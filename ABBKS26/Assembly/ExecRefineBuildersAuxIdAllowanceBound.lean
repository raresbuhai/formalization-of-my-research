module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdRawBits
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdAllowance

/-! The sparse SUB payload fits a dimension-quadratic rounder allowance. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdAllowanceBound

open Common Rounding _root_.ABBKS26.Tree Sources Builders
open _root_.ABBKS26.Schedule.EncodingBounds
open SoS.Solver (encProblem encRawPoly)
open Turing.MultiTapeTM
open scoped BigOperators

noncomputable section

theorem sparse (d t B : ℕ) (hB : 100 ≤ B) (ht : 3 ≤ t ∧ t ≤ B) :
    sparseBound d (8 * t) (2 * t + 1) ((d + 2) ^ (16 * t)) (B ^ 22 * (d + 2)) ≤
      B ^ 100 * (d + 2) ^ (400 * t) := by
  let z := d + 2
  have hz : 2 ≤ z := by omega
  have hm : 2 * t + 1 + 2 ≤ B ^ 2 := by nlinarith only [hB, ht.2]
  have hs : z ^ (16 * t) + 2 ≤ z ^ (16 * t + 2) := by
    have h1 : 1 ≤ z ^ (16 * t) := one_le_pow₀ (by omega)
    have h2 : 4 ≤ z ^ 2 := by nlinarith only [hz]
    rw [pow_add]
    nlinarith only [h1, Nat.mul_le_mul_left (z ^ (16 * t)) h2]
  have hb : B ^ 22 * z + 8 * t + 2 ≤ B ^ 23 * z := by
    have hB : B ≤ B ^ 22 := le_self_pow₀ (by omega) (by norm_num)
    have h1 : 1 ≤ B ^ 22 * z := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
    have hBP : B ≤ B ^ 22 * z := hB.trans (Nat.le_mul_of_pos_right _ (by omega))
    have hpow : 100 * B ^ 22 * z ≤ B ^ 23 * z :=
      Nat.mul_le_mul_right _ (IdBits.hundred_pow B 22 (by omega))
    nlinarith only [hBP, h1, ht.2, hpow]
  unfold sparseBound
  apply (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
    (Nat.pow_le_pow_left hm 4) (Nat.pow_le_pow_left hs 4))
      (Nat.pow_le_pow_left hb 4)) le_rfl).trans
  simp only [mul_pow, ← pow_mul]
  calc
    _ = (B ^ (2 * 4) * B ^ (23 * 4)) *
        (z ^ ((16 * t + 2) * 4) * z ^ 4 * z ^ (32 * (8 * t + 1))) := by ring
    _ = B ^ 100 * z ^ (320 * t + 44) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 2; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

theorem zeroObjective_length (P : SoS.Solver.Problem) :
    (encProblem (SpecSolver.zeroObjective P)).length ≤ (encProblem P).length := by
  have hnil : (encRawPoly []).length = 0 := rfl
  have hnil' : (Encoding.encList encRawPoly []).length = 0 := rfl
  simp only [SpecSolver.zeroObjective, SoS.Solver.Problem.numVars,
    SoS.Solver.Problem.degree, encProblem, RawAux.length_pair, hnil, hnil']
  omega

theorem round_bound (I : RoundInput) (B t : ℕ) (hB : 100 ≤ B) (ht : 3 ≤ t)
    (hproblem : (encProblem I.problem).length ≤ B ^ 100 * (I.ambient + 2) ^ (400 * t))
    (hdegree : I.problem.degree ≤ 25 * t) (hrank : I.rankBound ≤ B)
    (hcap : rankCap I.radius I.rankBound ≤ B)
    (hradius : (Encoding.encRat I.radius).length ≤ B ^ 22 * (I.ambient + 2))
    (hnorm : (Encoding.encRat I.normBound).length ≤ B ^ 22 * (I.ambient + 2)) :
    roundFuel I ≤ B ^ (1000000000 * (solverConstant + 1) * t ^ 2) *
      (I.ambient + 2) ^ (1000000000 * (solverConstant + 1) * t ^ 2) := by
  let z := I.ambient + 2
  let C := solverConstant + 1
  let E := 2600 * C * t
  let Q := B ^ 100 * z ^ (400 * t)
  have hz : 2 ≤ z := by omega
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hzpow : z ≤ z ^ (400 * t) := le_self_pow₀ (by omega) (by omega)
  have hBpow : B ≤ B ^ 100 := le_self_pow₀ (by omega) (by norm_num)
  have hB22 : B ^ 22 ≤ B ^ 100 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hbits : B ^ 22 * z ≤ Q := Nat.mul_le_mul hB22 hzpow
  have hdim : I.ambient ≤ Q := (by omega : I.ambient ≤ z).trans
    (hzpow.trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))))
  have hrank' : I.rankBound ≤ Q := hrank.trans (hBpow.trans
    (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))))
  have hQ : 1 ≤ Q := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have hsize : (encProblem I.problem).length + I.ambient + I.rankBound +
      (Encoding.encRat I.radius).length + (Encoding.encRat I.normBound).length + 2 ≤
        B ^ 102 * z ^ (400 * t) := by
    have hp : 100 * B ^ 100 ≤ B ^ 101 := IdBits.hundred_pow B 100 hB
    have hp' : B ^ 101 ≤ B ^ 102 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hm := Nat.mul_le_mul_right (z ^ (400 * t)) (hp.trans hp')
    have hP : (encProblem I.problem).length ≤ Q := hproblem
    have hr := hradius.trans hbits
    have hn := hnorm.trans hbits
    calc
      _ ≤ 8 * Q := by omega
      _ ≤ 100 * Q := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ _ := by simpa only [Q, Nat.mul_assoc] using hm
  have he : 100 * (solverConstant + 1) * (I.problem.degree + 1) ≤ E := by
    dsimp only [E, C]
    nlinarith only [Nat.mul_le_mul_left (100 * (solverConstant + 1)) hdegree,
      Nat.mul_le_mul_left (100 * (solverConstant + 1)) (show 1 ≤ t by omega)]
  have hpack : rankCap I.radius I.rankBound + 2 ≤ B ^ 2 := by
    nlinarith only [hcap, hB]
  have hmain : ((encProblem I.problem).length + I.ambient + I.rankBound +
      (Encoding.encRat I.radius).length + (Encoding.encRat I.normBound).length + 2) ^
        (100 * (solverConstant + 1) * (I.problem.degree + 1)) ≤
          (B ^ 102 * z ^ (400 * t)) ^ E := by
    exact (Nat.pow_le_pow_left hsize _).trans (Nat.pow_le_pow_right (by positivity) he)
  have hE1 : 102 * E + 200 ≤ 1000000000 * C * t ^ 2 := by
    have ht2 : t ≤ t ^ 2 := le_self_pow₀ (by omega) (by norm_num)
    have hh := Nat.mul_le_mul_left C ht2
    have h1 : 1 ≤ C * t ^ 2 := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    dsimp only [E]
    nlinarith only [hh, h1]
  have hE2 : 400 * t * E ≤ 1000000000 * C * t ^ 2 := by
    dsimp only [E]
    nlinarith only [Nat.zero_le (C * t ^ 2)]
  unfold roundFuel
  apply (Nat.mul_le_mul hmain (Nat.pow_le_pow_left hpack 100)).trans
  simp only [mul_pow, ← pow_mul]
  calc
    _ = B ^ (102 * E + 200) * z ^ (400 * t * E) := by
      rw [pow_add]
      ring
    _ ≤ _ := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hE1)
      (Nat.pow_le_pow_right (by omega) hE2)


theorem rat_bits (B d e : ℕ) (q : ℚ) (hB : 100 ≤ B)
    (hq : RatBound (B ^ e * (d + 2)) q) :
    (Encoding.encRat q).length ≤ B ^ (e + 1) * (d + 2) := by
  have h1 : 1 ≤ B ^ e * (d + 2) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  apply hq.bits.trans
  apply le_trans _ (Nat.mul_le_mul_right (d + 2) (IdBits.hundred_pow B e hB))
  nlinarith only [h1]

theorem reserve_le (k : ℕ) (ps : ℕ → StepParams) (h : ℕ) (hh : h < k - 1) :
    idReserve k (ps h) ≤ idReserves k ps + 2 := by
  let xs := (List.range (k - 1)).map fun j ↦ idReserve k (ps j) + 2
  have hall : ∀ a ∈ xs, 1 ≤ a := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    omega
  have hm : idReserve k (ps h) + 2 ∈ xs :=
    List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩
  have hp := List.single_le_prod hall _ hm
  change idReserve k (ps h) ≤ xs.prod + 2 + 2
  omega

theorem reserve_fuel {n k d : ℕ} (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1) :
    let a := (args k ps x h P, fuel)
    let B := idReserve k (ps h)
    let e := 1000000000 * (solverConstant + 1) * IdInput.degree a ^ 2
    B ^ e * (d + 2) ^ e ≤ fuel := by
  let a := (args k ps x h P, fuel)
  let e := 1000000000 * (solverConstant + 1) * IdInput.degree a ^ 2
  have ht := (IdReify.fields k ps x fuel h P (by omega)).1
  have ht0 := IdInput.prepared_degree ps M ε w η Δ D ω r hp h hh
  have he : logInv (ps 0).w + 3 = IdInput.degree a := by
    rw [ht, ht0]
    rfl
  apply le_trans _ hf
  unfold localBudget
  rw [ite_eq_right (by decide : Mode.identical ≠ .centered), he]
  change idReserve k (ps h) ^ e * (d + 2) ^ e ≤ _
  calc
    _ ≤ (idReserves k ps + 2) ^ e * (d + 2) ^ e :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (reserve_le k ps h hh) e)
    _ = (d + 2) ^ e * (idReserves k ps + 2) ^ e := Nat.mul_comm _ _
    _ ≤ _ := Nat.le_mul_of_pos_left _ (Nat.mul_pos
      (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega)))

/-- The actual rounded sparse system, its norm, and its rank cap fit the local reserve. -/
theorem prepared (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) : IdAllowance.Prepared MC NC := by
  intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP
  let a := (args k ps x h P, fuel)
  let B := idReserve k (ps h)
  let t := IdInput.degree a
  let z := d + 2
  let bits := B ^ 22 * z
  let support := z ^ (16 * t)
  let A := IdReify.system MC a
  let J := IdSolver.query d (8 * t) A (IdPayload.tolerance a) (IdNorms.ballInput a) fuel
  let P₀ := IdProgram.problem MC NC a
  let RI := RoundProgram.input (IdCoverage.call (IdProgram.problem MC NC) IdNorms.normInput a)
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hβp : 0 ≤ (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 :=
    ⟨hs.2.2.1.le, hs.2.2.2.1.trans (by norm_num)⟩
  obtain ⟨hB, htB, hA, hβ, hden, hpack⟩ := IdBits.inputs k ps x fuel h P (by omega) hβp
  have ht3 : 3 ≤ t := by unfold t IdInput.degree IdCov.tDegree; omega
  have htfield := (IdReify.fields k ps x fuel h P (by omega)).1
  change t = IdCov.tDegree (ps h).w at htfield
  have hraw := IdRawBits.prepared MC ps x fuel h P M ε w η Δ D ω r hp hf hh
  have hε := IdBits.tolerance a B hB hβ hden
  have hball := IdBits.ballInput a B hB htB hA hβ hden
  have hnorm := IdBits.normInput a B hB htB hA hβ hden
  have hbits {q : ℚ} (hq : RatBound (B ^ 20 * z) q) :
      (Encoding.encRat q).length ≤ bits :=
    (rat_bits B d 20 q hB hq).trans (Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by omega) (by norm_num)))
  have hεbits : (Encoding.encRat (IdPayload.tolerance a)).length ≤ bits :=
    hbits (hε.mono (IdBits.power_linear B d 2 20 (by omega) (by norm_num)))
  have hballbits := hbits hball
  have hnormbits := hbits hnorm
  have hlen : A.length ≤ 2 * t + 1 := IdReify.length_system MC a
  have hlayout : IdSolver.layoutFuel d (8 * t) A ≤ fuel := by
    rw [htfield]
    exact IdPrepared.layout ps fuel h M ε w η Δ D ω r hp hf hh A
      (by rwa [← htfield])
  obtain ⟨S, hframe, Q, hJ, hthin⟩ := IdInput.prepared_subspace MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hfamily := IdReify.prepared_family MC hMC ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP
  have hvalid : (plainSystem (A.map fun p ↦ SoS.toReal (p.toPoly d))).Valid (8 * t) := by
    rw [hfamily, htfield]
    exact hJ.1
  have hplain : ∀ p ∈ A, p.length ≤ support ∧ ∀ q ∈ p,
      q.1.length ≤ d ∧ q.1.sum ≤ 8 * t ∧ (Encoding.encRat q.2).length ≤ bits := by
    intro p hp'
    refine ⟨(hraw p hp').length, ?_⟩
    intro q hq
    obtain ⟨hlen, hsum, hb⟩ := (hraw p hp').terms q hq
    exact ⟨hlen, hsum, (rat_bits B d 14 q.2 hB hb).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by norm_num)))⟩
  have hsize := IdSolver.sparse_bound NC hNC d (8 * t) A (IdPayload.tolerance a)
    (IdNorms.ballInput a) fuel support bits hvalid hlayout hplain hεbits hballbits
  have hproblem : (encProblem P₀).length ≤ B ^ 100 * z ^ (400 * t) := by
    apply (zeroObjective_length (NC.build J)).trans
    apply hsize.trans
    apply le_trans _ (sparse d t B hB ⟨ht3, htB⟩)
    unfold sparseBound
    gcongr
  have hrep := IdReify.prepared_rep MC hMC NC hNC (IdNorms.ballInput a)
    ps x fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hdegree : P₀.degree ≤ 25 * t := by
    have he : P₀.degree = solverDegree
        (plainSystem (A.map fun p ↦ SoS.toReal (p.toPoly d))) (8 * t) := hrep.2.1
    rw [he]
    simp only [solverDegree, outerDegree, plainSystem, List.map_nil, List.foldl_nil]
    omega
  have hβf : IdFuel.accuracy a = (ps h).subspaceAccuracy :=
    IdFuel.fields k ps x fuel h P (by omega)
  obtain ⟨hk, _, _, _⟩ := IdFuel.caps ps x fuel h P hf hh
    ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hrank : IdFuel.rank a = k := min_eq_right hk
  have hkB : k ≤ B := (SpecFuel.rank_le_cap (IdFuel.accuracy a) k
    (by rw [hβf]; exact hs.2.2.1)).trans hpack
  have hcap : rankCap RI.radius RI.rankBound ≤ B := by
    change rankCap (IdFuel.accuracy a) (IdFuel.rank a) ≤ B
    rw [hrank]
    exact hpack
  have hβb : RatBound B (field a 10) :=
    ⟨(by rw [abs_of_nonneg hβ.1]; exact hβ.2.trans (one_le_pow₀ (by norm_num))),
      hden.trans (Nat.lt_two_pow_self (n := B)).le⟩
  have hradius : (Encoding.encRat RI.radius).length ≤ B ^ 22 * (d + 2) :=
    hbits (hβb.mono (by
      simpa only [pow_one] using IdBits.power_linear B d 1 20 (by omega) (by norm_num)))
  exact (round_bound RI B t hB ht3 hproblem hdegree
    (by change IdFuel.rank a ≤ B; rw [hrank]; exact hkB) hcap hradius hnormbits).trans
      (reserve_fuel ps x fuel h P M ε w η Δ D ω r hp hf hh)


end

end ABBKS26.Assembly.Exec.RefineSynth.IdAllowanceBound
