module

public import BBKS24.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# The running time of the algorithm

The algorithm reads at most `coinLen x = n² b` coins (`BBKS24.Alg.alg_eq_algN`). It first turns
the coins into numbers and keeps the first `coinLen x` of them, in time linear in the input with
the coins plus a polynomial in the input (`Turing.MultiTapeTM.ComputableInO.take'`), then runs
`BBKS24.Alg.algN` on the result, in time polynomial in the input alone. So it runs within
`c ((|x| + 2)^d + |(x, r)|)` steps and cells (`BBKS24.Alg.exists_runsInTime`).
-/

@[expose] public section

namespace BBKS24.Alg

open Turing.MultiTapeTM

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

theorem length_input_ge (x : Input) : x.2.2.length ≤ (encInput x).length := by
  change x.2.2.length ≤ (Encoding.frame (Encoding.encNat x.1) ++
    (Encoding.frame (Encoding.encNat x.2.1) ++ x.2.2)).length
  simp only [List.length_append]
  omega

theorem coinLen_le (x : Input) : coinLen x ≤ 3 * ((encInput x).length + 2) ^ 3 := by
  have h0 := length_input_ge x
  have h1 : numV x ≤ (encInput x).length + 1 := by
    unfold numV
    omega
  have h2 : nBits (numV x) ≤ 3 * ((encInput x).length + 2) := by
    unfold nBits logN
    have := Nat.log_le_self 2 (numV x)
    omega
  unfold coinLen
  obtain ⟨X, hX⟩ : ∃ X, X = (encInput x).length := ⟨_, rfl⟩
  rw [← hX] at h1 h2 ⊢
  calc numV x * numV x * nBits (numV x) ≤ (X + 2) * (X + 2) * (3 * (X + 2)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) h2
    _ = 3 * (X + 2) ^ 3 := by ring

/-- The arithmetic of the bound. -/
theorem bound_arith {A X L Y R E TLv TCv cL dL cC dC D K : ℕ}
    (hR : R ≤ A) (hE : E ≤ 3 * A) (hL : L ≤ 3 * (X + 2) ^ 3) (hY : Y ≤ 2 * X + 1 + 3 * L)
    (hTL : TLv ≤ cL * (X + 1) ^ dL) (hTC : TCv ≤ cC * (Y + 1) ^ dC)
    (hD1 : dL ≤ D) (hD2 : 3 * dC ≤ D) (hD3 : 3 ≤ D) (hK : 14 + cL + cC * 12 ^ dC ≤ K) :
    A + (A + R + (A + TLv) + (2 * E + 1 + L)) + TCv ≤ K * ((X + 2) ^ D + A + 1) := by
  obtain ⟨N, hN⟩ : ∃ N, N = X + 2 := ⟨_, rfl⟩
  rw [← hN] at hL ⊢
  have hN1 : 1 ≤ N := by omega
  have p1 : (X + 1) ^ dL ≤ N ^ D :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hN1 hD1)
  have p3 : N ^ 3 ≤ N ^ D := Nat.pow_le_pow_right hN1 hD3
  have hN3 : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) _
  have hY1 : Y + 1 ≤ 12 * N ^ 3 := by omega
  have p2 : (Y + 1) ^ dC ≤ 12 ^ dC * N ^ D :=
    calc (Y + 1) ^ dC ≤ (12 * N ^ 3) ^ dC := Nat.pow_le_pow_left hY1 _
      _ = 12 ^ dC * N ^ (3 * dC) := by rw [mul_pow, ← pow_mul]
      _ ≤ 12 ^ dC * N ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hN1 hD2)
  obtain ⟨P, hP⟩ : ∃ P, P = N ^ D := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cC * 12 ^ dC := ⟨_, rfl⟩
  rw [← hP] at p1 p2 p3
  have h1 : TLv ≤ cL * P := hTL.trans (Nat.mul_le_mul_left _ p1)
  have h2 : TCv ≤ Q * P := by
    rw [hQ, mul_assoc]
    exact hTC.trans (Nat.mul_le_mul_left _ p2)
  have h3 : L ≤ 3 * P := by omega
  rw [← hP]
  have h4 : A + (A + R + (A + TLv) + (2 * E + 1 + L)) + TCv ≤ (14 + cL + Q) * (P + A + 1) := by
    have := Nat.zero_le (cL * A)
    have := Nat.zero_le (Q * A)
    have := Nat.zero_le cL
    have := Nat.zero_le Q
    nlinarith
  exact h4.trans (Nat.mul_le_mul_right _ (hQ ▸ hK))

theorem exists_le_pow {β : Type} {size u : β → ℕ} (h : PolyBounded size u) :
    ∃ c d, ∀ a, u a ≤ c * (size a + 1) ^ d := by
  obtain ⟨bound, hb, hu⟩ := h
  obtain ⟨c, d, hcd⟩ := Cslib.polynomiallyBounded_iff_le.1 hb
  exact ⟨c, d, fun a ↦ (hu a).trans (hcd _)⟩

/-- **The algorithm runs in polynomial time**: within `c ((|x| + 2)^d + |(x, r)| + 1)` steps and
cells, for some `d ≥ 2`. -/
theorem exists_runsInTime : ∃ d, 2 ≤ d ∧ RunsInTime alg (fun N ↦ (N + 2) ^ d) := by
  obtain ⟨TL, SL, hTL, hSL, hL⟩ := coinLen_polytime.exists_computableInO
  obtain ⟨TC, SC, hTC, hSC, hC⟩ := algN_polytime.exists_computableInO
  obtain ⟨cTL, dTL, hTL'⟩ := exists_le_pow hTL
  obtain ⟨cSL, dSL, hSL'⟩ := exists_le_pow hSL
  obtain ⟨cTC, dTC, hTC'⟩ := exists_le_pow hTC
  obtain ⟨cSC, dSC, hSC'⟩ := exists_le_pow hSC
  have hfst := ComputableInO.fst encInput encBits
  have hsnd := ComputableInO.snd encInput encBits
  have hmap := (Universal.computableTidilyInDegree_map_eBit.inO_one.computableInO).comp' hsnd
  have hlen := hL.comp' hfst
  have htake := ComputableInO.take' hmap hlen
  have htr := ComputableInO.prod hfst htake
  have hall := hC.comp' htr
  have halg : (fun a : Input × List Bool ↦
      algN (a.1, List.take (coinLen a.1) (List.map (⇑Universal.eBit) a.2))) = alg :=
    funext fun a ↦ (alg_eq_algN a).symm
  rw [halg] at hall
  obtain ⟨D, hD⟩ : ∃ D, D = dTL + dSL + 3 * (dTC + dSC) + 3 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = 14 + (cTL + cSL) + (cTC + cSC) * 12 ^ (dTC + dSC) := ⟨_, rfl⟩
  have hK1 : 14 + cTL + cTC * 12 ^ dTC ≤ K := by
    have : cTC * 12 ^ dTC ≤ (cTC + cSC) * 12 ^ (dTC + dSC) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  have hK2 : 14 + cSL + cSC * 12 ^ dSC ≤ K := by
    have : cSC * 12 ^ dSC ≤ (cTC + cSC) * 12 ^ (dTC + dSC) :=
      Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega
  -- The lengths.
  have hlens : ∀ a : Input × List Bool,
      (encBits a.2).length ≤ (encPair encInput encBits a).length ∧
      (encList encUnary (List.map (⇑Universal.eBit) a.2)).length ≤
        3 * (encPair encInput encBits a).length ∧
      (encPair (encList encUnary) encUnary
          (List.map (⇑Universal.eBit) a.2, coinLen a.1)).length =
        2 * (encList encUnary (List.map (⇑Universal.eBit) a.2)).length + 1 + coinLen a.1 ∧
      (encPair encInput (encList encUnary)
          (a.1, List.take (coinLen a.1) (List.map (⇑Universal.eBit) a.2))).length ≤
        2 * (encInput a.1).length + 1 + 3 * coinLen a.1 := by
    intro a
    have hA := length_encPair (enc₁ := encInput) (enc₂ := encBits) a
    have hm : (encList encUnary (List.map (⇑Universal.eBit) a.2)).length ≤
        3 * (List.map (⇑Universal.eBit) a.2).length :=
      length_encList_unary_le fun c hc ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 hc
        exact eBit_le_one b
    have ht : (encList encUnary (List.take (coinLen a.1) (List.map (⇑Universal.eBit) a.2))).length
        ≤ 3 * (List.take (coinLen a.1) (List.map (⇑Universal.eBit) a.2)).length :=
      length_encList_unary_le fun c hc ↦ by
        obtain ⟨b, -, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hc)
        exact eBit_le_one b
    have hlt := List.length_take_le (coinLen a.1) (List.map (⇑Universal.eBit) a.2)
    rw [List.length_map] at hm
    refine ⟨by omega, ?_, ?_, ?_⟩
    · have : a.2.length = (encBits a.2).length := rfl
      omega
    · rw [length_encPair, encUnary_apply, List.length_replicate]
    · simp only [length_encPair]
      omega
  refine ⟨D, by omega, ?_⟩
  obtain ⟨c, hc, -⟩ := hall.mono (T' := fun a ↦ ((encInput a.1).length + 2) ^ D +
      (encPair encInput encBits a).length)
    (S' := fun a ↦ ((encInput a.1).length + 2) ^ D + (encPair encInput encBits a).length) K
    (fun a ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := hlens a
      rw [h3]
      exact bound_arith h1 h2 (coinLen_le a.1) h4 (hTL' a.1) (hTC' _) (by omega) (by omega)
        (by omega) hK1)
    (fun a ↦ by
      obtain ⟨h1, h2, h3, h4⟩ := hlens a
      rw [h3]
      exact bound_arith h1 h2 (coinLen_le a.1) h4 (hSL' a.1) (hSC' _) (by omega) (by omega)
        (by omega) hK2)
  exact ⟨c, hc⟩

end BBKS24.Alg
