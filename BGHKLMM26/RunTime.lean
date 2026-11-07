module

public import BGHKLMM26.PolyTime
public import BGHKLMM26.Assembly
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# The running time of the algorithm

The algorithm reads at most `coinLen x = n T` coins (`BGHKLMM26.Alg.alg_eq_algN`). As for [BBKS24]
in this repository, it first turns the coins into numbers and keeps the first `coinLen x` of them,
in time linear in the input with the coins plus a polynomial in the instance
(`Turing.MultiTapeTM.ComputableInO.take'`), then runs `BGHKLMM26.Alg.algN` on the result, in time
polynomial in the instance alone: the solver's budget `(|P| + 2)³` is computed from the encoded
problem. So it runs within `c ((|x| + 2)^d + |(x, r)| + 1)` steps and cells
(`BGHKLMM26.Alg.exists_runsInTime`).
-/

@[expose] public section

namespace BGHKLMM26.Alg

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS SoS.Solver SoS.PolyTime

/-! ### Reading the needed coins -/

/-- The number of coins the algorithm reads, at most: `n T`. -/
def coinLen (Q₀ : ℕ) (I : Instance) : ℕ := I.1 * tPar Q₀ I

/-- **The algorithm, for coins given as numbers.** -/
def algN (Q₀ : ℕ) (y : Instance × List ℕ) : List Bool :=
  run Q₀ ((y.1, y.2.map fun c ↦ decide (c = 1)), budget (solverInput Q₀ y.1))

theorem getD_coins {L i : ℕ} (r : List Bool) (hi : i < L) :
    (((r.map Bool.toNat).take L).map fun c ↦ decide (c = 1)).getD i false = r.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_take_of_lt hi, List.getElem?_map]
  cases r[i]? with
  | none => simp
  | some x => cases x <;> simp

/-- **The algorithm reads at most `coinLen x` coins.** -/
theorem alg_eq_algN (Q₀ : ℕ) (x : Instance × List Bool) :
    alg Q₀ x = algN Q₀ (x.1, (x.2.map Bool.toNat).take (coinLen Q₀ x.1)) := by
  change algC Q₀ x.1 (cellOfCoins (tPar Q₀ x.1) x.2) = algC Q₀ x.1 (cellOfCoins (tPar Q₀ x.1)
    (((x.2.map Bool.toNat).take (coinLen Q₀ x.1)).map fun c ↦ decide (c = 1)))
  refine algC_congr fun k hk ↦ ?_
  unfold cellOfCoins
  congr 1
  refine List.map_congr_left fun i hi ↦ ?_
  have hi' := List.mem_range.1 hi
  have hlt : k * tPar Q₀ x.1 + i < coinLen Q₀ x.1 := by
    unfold coinLen
    calc k * tPar Q₀ x.1 + i < k * tPar Q₀ x.1 + tPar Q₀ x.1 := by omega
      _ = (k + 1) * tPar Q₀ x.1 := by ring
      _ ≤ x.1.1 * tPar Q₀ x.1 := Nat.mul_le_mul_right _ hk
  rw [getD_coins _ hlt]

/-! ### Certificates -/

variable {α : Type} {input : α ↪ List Bool}

theorem coinLen_polytime (Q₀ : ℕ) : ComputableInPolyTime (coinLen Q₀) encInstance encUnary := by
  rw [encInstance_eq]
  unfold coinLen
  have := tPar' Q₀ (id' (encIn := encI))
  fun_prop

@[fun_prop]
theorem budget' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ budget (solverInput Q₀ (f a))) input encUnary := by
  have hl : ComputableInPolyTime (fun a ↦ (encProblemM (SDP.problem (f a))).length) input
      encUnary := (encoding_length encProblemM).comp (problem' hf)
  have e : (fun a ↦ budget (solverInput Q₀ (f a))) =
      fun a ↦ ((encProblemM (SDP.problem (f a))).length + 2) ^ 3 := rfl
  rw [e]
  fun_prop

/-- Coins as unary numbers. -/
abbrev encVs : List ℕ ↪ List Bool := encList encUnary

theorem algN_polytime (Q₀ : ℕ) :
    ComputableInPolyTime (algN Q₀) (encPair encInstance encVs) encBits := by
  rw [encInstance_eq]
  unfold algN
  have hI : ComputableInPolyTime (fun y : Instance × List ℕ ↦ y.1) (encPair encI encVs) encI :=
    by fun_prop
  have hc : ComputableInPolyTime (fun y : Instance × List ℕ ↦ y.2.map fun c ↦ decide (c = 1))
      (encPair encI encVs) (encList encBool) :=
    mapWithInput (f := fun _ (c : ℕ) ↦ decide (c = 1)) (by fun_prop) (by fun_prop)
  have hb : ComputableInPolyTime (fun y : Instance × List ℕ ↦ y.2.map fun c ↦ decide (c = 1))
      (encPair encI encVs) encBits :=
    .of_tidy (ComputableTidilyInPolyTime.listToBits.comp hc.tidy)
  have hin : ComputableInPolyTime (fun y : Instance × List ℕ ↦
      ((y.1, y.2.map fun c ↦ decide (c = 1)), budget (solverInput Q₀ y.1)))
      (encPair encI encVs) encRunIn :=
    (hI.prod hb).prod (budget' Q₀ hI)
  exact (run_polytime Q₀).comp hin

/-! ### The bound -/

/-- The constant of the coin count. -/
def coinC (Q₀ : ℕ) : ℕ := 4 ^ (Q₀ + 1) + 4 * (Q₀ + 1) ^ 2 + 8

theorem tPar_le (Q₀ : ℕ) (I : Instance) :
    tPar Q₀ I ≤ coinC Q₀ * ((encInstance I).length + 2) ^ 4 := by
  obtain ⟨N, hN⟩ : ∃ N, N = (encInstance I).length + 2 := ⟨_, rfl⟩
  rw [← hN]
  have hZ : zPar I ≤ N := hN ▸ zPar_le_length I
  have hN1 : 1 ≤ N := by omega
  have h2 : 1 ≤ 2 ^ Q₀ := Nat.one_le_two_pow
  have hR : rPar Q₀ I ≤ N ^ 2 * 2 ^ Q₀ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hZ 2)
  have hN2 : 1 ≤ N ^ 2 * 2 ^ Q₀ := Nat.mul_le_mul (Nat.one_le_pow _ _ hN1) h2
  have hR1 : (rPar Q₀ I + 1) ^ 2 ≤ 4 ^ (Q₀ + 1) * N ^ 4 :=
    calc (rPar Q₀ I + 1) ^ 2 ≤ (2 * (N ^ 2 * 2 ^ Q₀)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 ^ (Q₀ + 1) * N ^ 4 := by
        rw [pow_succ 4 Q₀, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
  have hp : pPar Q₀ I ≤ 4 * (Q₀ + 1) ^ 2 * N ^ 4 := by
    unfold pPar
    have : zPar I + Q₀ ≤ (Q₀ + 1) * N := by nlinarith
    calc 4 * (zPar I + Q₀) ^ 2 ≤ 4 * ((Q₀ + 1) * N) ^ 2 := by gcongr
      _ = 4 * (Q₀ + 1) ^ 2 * N ^ 2 := by ring
      _ ≤ 4 * (Q₀ + 1) ^ 2 * N ^ 4 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 (by norm_num))
  have h8 : 8 ≤ 8 * N ^ 4 := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hN1)
  unfold tPar coinC
  nlinarith

theorem coinLen_le (Q₀ : ℕ) (I : Instance) :
    coinLen Q₀ I ≤ coinC Q₀ * ((encInstance I).length + 2) ^ 5 := by
  have hn : I.1 ≤ (encInstance I).length + 2 :=
    ((n_lt_zPar I).le).trans (zPar_le_length I)
  have hT := tPar_le Q₀ I
  unfold coinLen
  calc I.1 * tPar Q₀ I ≤ ((encInstance I).length + 2) *
        (coinC Q₀ * ((encInstance I).length + 2) ^ 4) := Nat.mul_le_mul hn hT
    _ = coinC Q₀ * ((encInstance I).length + 2) ^ 5 := by ring

theorem length_encList_unary_le {l : List ℕ} (h : ∀ c ∈ l, c ≤ 1) :
    (encList encUnary l).length ≤ 3 * l.length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons c l ih =>
    have hc := h c List.mem_cons_self
    have := ih fun d hd ↦ h d (List.mem_cons_of_mem _ hd)
    simp only [List.map_cons, List.sum_cons, List.length_cons, encUnary_apply,
      List.length_replicate] at this ⊢
    omega

theorem eBit_le_one (b : Bool) : Universal.eBit b ≤ 1 := by
  cases b <;> decide

/-- The arithmetic of the bound. -/
theorem bound_arith {A X L Y R E TLv TCv cL dL cC dC D K cM : ℕ}
    (hR : R ≤ A) (hE : E ≤ 3 * A) (hL : L ≤ cM * (X + 2) ^ 5) (hY : Y ≤ 2 * X + 1 + 3 * L)
    (hTL : TLv ≤ cL * (X + 1) ^ dL) (hTC : TCv ≤ cC * (Y + 1) ^ dC)
    (hD1 : dL ≤ D) (hD2 : 5 * dC ≤ D) (hD3 : 5 ≤ D)
    (hK : 14 + cL + 3 * cM + cC * (3 * cM + 2) ^ dC ≤ K) :
    A + (A + R + (A + TLv) + (2 * E + 1 + L)) + TCv ≤ K * ((X + 2) ^ D + A + 1) := by
  obtain ⟨N, hN⟩ : ∃ N, N = X + 2 := ⟨_, rfl⟩
  rw [← hN] at hL ⊢
  have hN1 : 1 ≤ N := by omega
  have p1 : (X + 1) ^ dL ≤ N ^ D :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hN1 hD1)
  have p5 : N ^ 5 ≤ N ^ D := Nat.pow_le_pow_right hN1 hD3
  have hN5 : N ≤ N ^ 5 := Nat.le_self_pow (by norm_num) _
  have hY1 : Y + 1 ≤ (3 * cM + 2) * N ^ 5 := by nlinarith
  have p2 : (Y + 1) ^ dC ≤ (3 * cM + 2) ^ dC * N ^ D :=
    calc (Y + 1) ^ dC ≤ ((3 * cM + 2) * N ^ 5) ^ dC := Nat.pow_le_pow_left hY1 _
      _ = (3 * cM + 2) ^ dC * N ^ (5 * dC) := by rw [mul_pow, ← pow_mul]
      _ ≤ (3 * cM + 2) ^ dC * N ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 hD2)
  obtain ⟨P, hP⟩ : ∃ P, P = N ^ D := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cC * (3 * cM + 2) ^ dC := ⟨_, rfl⟩
  rw [← hP] at p1 p2 p5
  have h1 : TLv ≤ cL * P := hTL.trans (Nat.mul_le_mul_left _ p1)
  have h2 : TCv ≤ Q * P := by
    rw [hQ, mul_assoc]
    exact hTC.trans (Nat.mul_le_mul_left _ p2)
  have h3 : L ≤ cM * P := hL.trans (Nat.mul_le_mul_left _ p5)
  rw [← hP]
  have h4 : A + (A + R + (A + TLv) + (2 * E + 1 + L)) + TCv ≤
      (14 + cL + 3 * cM + Q) * (P + A + 1) := by
    have := Nat.zero_le (cL * A)
    have := Nat.zero_le (Q * A)
    have := Nat.zero_le (cM * A)
    have := Nat.zero_le cL
    have := Nat.zero_le Q
    have := Nat.zero_le cM
    nlinarith
  exact h4.trans (Nat.mul_le_mul_right _ (hQ ▸ hK))

theorem exists_le_pow {β : Type} {size u : β → ℕ} (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hb, hu⟩ := h
  obtain ⟨c, d, hcd⟩ := Cslib.polynomiallyBounded_iff_le.1 hb
  exact ⟨c, d, fun a ↦ (hu a).trans (hcd _)⟩

/-- **The algorithm runs in polynomial time**: within `c ((|x| + 2)^d + |(x, r)| + 1)` steps and
cells, for every precision constant `Q₀` and some `d`, which may be taken at least any `e`. -/
theorem exists_runsInTime (Q₀ e : ℕ) :
    ∃ d, e ≤ d ∧ 5 ≤ d ∧ RunsInTime (alg Q₀) (fun N ↦ (N + 2) ^ d) := by
  obtain ⟨TL, SL, hTL, hSL, hL⟩ := (coinLen_polytime Q₀).exists_computableInO
  obtain ⟨TC, SC, hTC, hSC, hC⟩ := (algN_polytime Q₀).exists_computableInO
  obtain ⟨cTL, dTL, hTL'⟩ := exists_le_pow hTL
  obtain ⟨cSL, dSL, hSL'⟩ := exists_le_pow hSL
  obtain ⟨cTC, dTC, hTC'⟩ := exists_le_pow hTC
  obtain ⟨cSC, dSC, hSC'⟩ := exists_le_pow hSC
  have hfst := ComputableInO.fst encInstance encBits
  have hsnd := ComputableInO.snd encInstance encBits
  have hmap := (Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO).comp' hsnd
  have hlen := hL.comp' hfst
  have htake := ComputableInO.take' hmap hlen
  have htr := ComputableInO.prod hfst htake
  have hall := hC.comp' htr
  have halg : (fun a : Instance × List Bool ↦
      algN Q₀ (a.1, List.take (coinLen Q₀ a.1) (List.map (⇑Universal.eBit) a.2))) = alg Q₀ :=
    funext fun a ↦ (alg_eq_algN Q₀ a).symm
  rw [halg] at hall
  set cM := coinC Q₀
  obtain ⟨D, hD⟩ : ∃ D, D = dTL + dSL + 5 * (dTC + dSC) + 5 + e := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 14 + (cTL + cSL) + 3 * cM + (cTC + cSC) * (3 * cM + 2) ^ (dTC + dSC) :=
    ⟨_, rfl⟩
  have hK1 : 14 + cTL + 3 * cM + cTC * (3 * cM + 2) ^ dTC ≤ K := by
    have : cTC * (3 * cM + 2) ^ dTC ≤ (cTC + cSC) * (3 * cM + 2) ^ (dTC + dSC) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  have hK2 : 14 + cSL + 3 * cM + cSC * (3 * cM + 2) ^ dSC ≤ K := by
    have : cSC * (3 * cM + 2) ^ dSC ≤ (cTC + cSC) * (3 * cM + 2) ^ (dTC + dSC) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) (by omega))
    omega
  -- The lengths.
  have hlens : ∀ a : Instance × List Bool,
      (encBits a.2).length ≤ (encPair encInstance encBits a).length ∧
      (encList encUnary (List.map (⇑Universal.eBit) a.2)).length ≤
        3 * (encPair encInstance encBits a).length ∧
      (encPair (encList encUnary) encUnary
          (List.map (⇑Universal.eBit) a.2, coinLen Q₀ a.1)).length =
        2 * (encList encUnary (List.map (⇑Universal.eBit) a.2)).length + 1 + coinLen Q₀ a.1 ∧
      (encPair encInstance (encList encUnary)
          (a.1, List.take (coinLen Q₀ a.1) (List.map (⇑Universal.eBit) a.2))).length ≤
        2 * (encInstance a.1).length + 1 + 3 * coinLen Q₀ a.1 := by
    intro a
    have hA := length_encPair (enc₁ := encInstance) (enc₂ := encBits) a
    have hm : (encList encUnary (List.map (⇑Universal.eBit) a.2)).length ≤
        3 * (List.map (⇑Universal.eBit) a.2).length :=
      length_encList_unary_le fun c hc ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
        exact eBit_le_one b
    have ht : (encList encUnary
        (List.take (coinLen Q₀ a.1) (List.map (⇑Universal.eBit) a.2))).length ≤
        3 * (List.take (coinLen Q₀ a.1) (List.map (⇑Universal.eBit) a.2)).length :=
      length_encList_unary_le fun c hc ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hc)
        exact eBit_le_one b
    have hlt := List.length_take_le (coinLen Q₀ a.1) (List.map (⇑Universal.eBit) a.2)
    rw [List.length_map] at hm
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have : a.2.length = (encBits a.2).length := rfl
      omega
    · rw [length_encPair, encUnary_apply, List.length_replicate]
    · simp only [length_encPair]
      omega
  refine ⟨D, by omega, by omega, ?_⟩
  obtain ⟨c, hc, -⟩ := hall.mono (T' := fun a ↦ ((encInstance a.1).length + 2) ^ D +
      (encPair encInstance encBits a).length)
    (S' := fun a ↦ ((encInstance a.1).length + 2) ^ D + (encPair encInstance encBits a).length) K
    (fun a ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := hlens a
      rw [h3]
      exact bound_arith h1 h2 (coinLen_le Q₀ a.1) h4 (hTL' a.1) (hTC' _) (by omega) (by omega)
        (by omega) hK1)
    (fun a ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := hlens a
      rw [h3]
      exact bound_arith h1 h2 (coinLen_le Q₀ a.1) h4 (hSL' a.1) (hSC' _) (by omega) (by omega)
        (by omega) hK2)
  exact ⟨c, hc⟩

end BGHKLMM26.Alg
