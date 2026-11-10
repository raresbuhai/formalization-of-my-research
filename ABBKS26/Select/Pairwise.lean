module

public import ABBKS26.Select.PairwiseAuxMatrix

/-!
# Rational pairwise tests and population error

Rational spectral, quadratic and mean tests, including variance-dependent rounding margins.
-/

@[expose] public section

namespace ABBKS26.Select

noncomputable section


open Matrix

open Common _root_.ABBKS26.Tree MeasureTheory
open scoped Topology
variable {k d : ℕ}

structure PairTest (d : ℕ) where
  statistic : Statistic d
  threshold : ℚ
  firstOnLeft : Bool

def PairTest.first (T : PairTest d) (x : Fin d → ℚ) : Bool :=
  if T.statistic.evalQ x ≤ T.threshold then T.firstOnLeft else !T.firstOnLeft


abbrev TestBuilder := {d : ℕ} → Mode → ℚ → Robust.Estimate d →
  Robust.Estimate d → ℕ → PairTest d

def pairError (mode : Mode) (Δ : ℝ) : ℝ :=
  match mode with
  | .centered => 16 * Δ ^ (- (1 / 8 : ℝ))
  | .identical => 8 * Δ ^ (- (2 : ℝ))

def PairTest.expanded (T : PairTest d) (margin : ℝ) (x : Vec d) : Prop :=
  if T.firstOnLeft then T.statistic.eval x ≤ T.threshold + margin
  else T.threshold - margin < T.statistic.eval x

def PairTest.contracted (T : PairTest d) (margin : ℝ) (x : Vec d) : Prop :=
  if T.firstOnLeft then T.statistic.eval x ≤ T.threshold - margin
  else T.threshold + margin < T.statistic.eval x

def TestSpec (build : TestBuilder) : Prop :=
  ∀ {k d} mode (M : Mixture k d) (a b : Fin k) (A B : Robust.Estimate d) (Δ : ℚ) fuel,
    M.Valid → mode.Condition M → mode.Separated M Δ → a ≠ b →
    Robust.Accurate M a A → Robust.Accurate M b B → (2 : ℝ) ^ 40 ≤ Δ →
    ∀ w η : ℝ, 0 < w → (∀ j, w ≤ M.w j) →
      0 ≤ η → η ≤ w ^ 2 / (10000 * k ^ 2 * Δ) →
    let T := build mode Δ A B fuel
    let ν := fun j ↦ ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
    let margin := fun j ↦ 2 * η * Real.sqrt
      (ProbabilityTheory.variance (fun y ↦ T.statistic.eval y.ofLp) (ν j))
    (ν a).real {y | ¬ T.contracted (margin a) y.ofLp} ≤ pairError mode Δ ∧
    (ν b).real {y | T.expanded (margin b) y.ofLp} ≤ pairError mode Δ


private theorem projection_error (S : Mat d) (hS : S.PosDef) (e v : Vec d) :
    (e ⬝ᵥ v) ^ 2 ≤ sqNormIn S e * qform S v := by
  have hinv : S * S⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have h := hS.star_dotProduct_mulVec_mul_le v (S⁻¹ *ᵥ e)
  simp only [star_trivial, mulVec_mulVec, hinv, one_mulVec] at h
  simpa only [qform, sqNormIn, dotProduct_comm, pow_two, mul_comm] using h

private def meanDirection (A B : Robust.Estimate d) : Fin d → ℚ :=
  A.cov⁻¹ *ᵥ (A.mean - B.mean)

private theorem meanDirection_solves (A B : Robust.Estimate d)
    (hA : (A.cov.map (algebraMap ℚ ℝ)).PosDef) :
    A.cov.map (algebraMap ℚ ℝ) *ᵥ (fun i ↦ (meanDirection A B i : ℝ)) =
      fun i ↦ (A.mean i : ℝ) - B.mean i := by
  have hdet : A.cov.det ≠ 0 := by
    intro hz
    have hh : (A.cov.map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) A.cov.det := ((algebraMap ℚ ℝ).map_det A.cov).symm
    rw [hz, map_zero] at hh
    exact hA.det_pos.ne' hh
  have h : A.cov *ᵥ meanDirection A B = A.mean - B.mean := by
    rw [meanDirection, mulVec_mulVec,
      mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  funext i
  have hi := congrArg (fun f : Fin d → ℚ ↦ (f i : ℝ)) h
  simpa only [mulVec, dotProduct, map_apply, Rat.cast_sum, Rat.cast_mul,
    Pi.sub_apply, Rat.cast_sub, eq_ratCast] using hi

private theorem meanDirection_gap (M : Mixture k d) (a b : Fin k)
    (A B : Robust.Estimate d) (Δ : ℝ) (hM : M.Valid)
    (hcov : M.S a = M.S b) (hsep : MeanSeparated Δ (M.μ a) (M.μ b) (M.S a))
    (ha : Robust.Accurate M a A) (hb : Robust.Accurate M b B) (hΔ : 1 ≤ Δ) :
    let u : Vec d := fun i ↦ (meanDirection A B i : ℝ)
    let V := qform (A.cov.map (algebraMap ℚ ℝ)) u
    Δ ^ 2 < V ∧ qform (M.S a) u ≤ (10 / 9 : ℝ) * V ∧
      |((fun i ↦ (A.mean i : ℝ)) - M.μ a) ⬝ᵥ u| ≤ V / 100 ∧
      |((fun i ↦ (B.mean i : ℝ)) - M.μ b) ⬝ᵥ u| ≤ V / 100 := by
  let E := A.cov.map (algebraMap ℚ ℝ)
  let u : Vec d := fun i ↦ (meanDirection A B i : ℝ)
  let δ : Vec d := fun i ↦ (A.mean i : ℝ) - B.mean i
  let ea : Vec d := (fun i ↦ (A.mean i : ℝ)) - M.μ a
  let eb : Vec d := (fun i ↦ (B.mean i : ℝ)) - M.μ b
  let V := qform E u
  have hsol : E *ᵥ u = δ := meanDirection_solves A B ha.1
  have hea : sqNormIn (M.S a) ea ≤ 1 / 10000000 := ha.2.2.2.2
  have heb : sqNormIn (M.S a) eb ≤ 1 / 10000000 := by
    rw [hcov]
    exact hb.2.2.2.2
  have herr (e : Vec d) (he : sqNormIn (M.S a) e ≤ 1 / 10000000) (v : Vec d) :
      (e ⬝ᵥ v) ^ 2 ≤ qform (M.S a) v / 10000000 := by
    have hv : 0 ≤ qform (M.S a) v := by
      simpa only [qform, star_trivial] using (hM.posDef a).posSemidef.dotProduct_mulVec_nonneg v
    exact (projection_error _ (hM.posDef a) e v).trans
      (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using
        mul_le_mul_of_nonneg_right he hv)
  have hδ (v : Vec d) : (δ ⬝ᵥ v) ^ 2 ≤ V * qform E v := by
    have h := ha.1.star_dotProduct_mulVec_mul_le v u
    simp only [star_trivial] at h
    change (v ⬝ᵥ (E *ᵥ u)) * (v ⬝ᵥ (E *ᵥ u)) ≤ qform E v * V at h
    rw [hsol] at h
    simpa only [V, qform, dotProduct_comm, pow_two, mul_comm] using h
  have hupper (v : Vec d) : qform E v ≤ (11 / 10 : ℝ) * qform (M.S a) v := by
    have hh := ha.2.2.1 v
    change qform E v ≤ qform ((1.1 : ℝ) • M.S a) v at hh
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh ⊢
    norm_num at hh ⊢
    exact hh
  have hV : Δ ^ 2 < V := by
    obtain ⟨v, hv⟩ := hsep
    have hv0 : v ≠ 0 := by
      intro hz
      simp [hz] at hv
    have hQ : 0 < qform (M.S a) v := by
      simpa only [qform, star_trivial] using (hM.posDef a).dotProduct_mulVec_pos hv0
    have hnoise : ((ea - eb) ⬝ᵥ v) ^ 2 ≤ qform (M.S a) v / 1000000 := by
      rw [sub_dotProduct]
      nlinarith [herr ea hea v, herr eb heb v, sq_nonneg (ea ⬝ᵥ v + eb ⬝ᵥ v)]
    have heq : M.μ a - M.μ b = δ - (ea - eb) := by
      ext i
      simp only [δ, ea, eb, Pi.sub_apply]
      ring
    rw [heq, sub_dotProduct] at hv
    have hsignal : ((δ - (ea - eb)) ⬝ᵥ v) ^ 2 ≤
        (3 / 2 : ℝ) * (δ ⬝ᵥ v) ^ 2 + 3 * ((ea - eb) ⬝ᵥ v) ^ 2 := by
      rw [sub_dotProduct]
      nlinarith only [sq_nonneg (δ ⬝ᵥ v + 2 * ((ea - eb) ⬝ᵥ v))]
    rw [sub_dotProduct] at hsignal
    have hV0 : 0 ≤ V := by
      simpa only [V, qform, star_trivial] using ha.1.posSemidef.dotProduct_mulVec_nonneg u
    have hh := (hδ v).trans (mul_le_mul_of_nonneg_left (hupper v) hV0)
    by_contra h
    have hle : V ≤ Δ ^ 2 := le_of_not_gt h
    have hnum : (3 / 2 : ℝ) * V * (11 / 10) + 3 / 1000000 ≤ 2 * Δ ^ 2 := by
      nlinarith only [hle, hΔ, sq_nonneg (Δ - 1)]
    have hprod := mul_le_mul_of_nonneg_right hnum hQ.le
    change 2 * Δ ^ 2 * qform (M.S a) v < _ at hv
    nlinarith only [hv, hsignal, hnoise, hh, hprod]
  have hlow : qform (M.S a) u ≤ (10 / 9 : ℝ) * V := by
    have hh := ha.2.1 u
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
    change (0.9 : ℝ) * qform (M.S a) u ≤ V at hh
    linarith only [hh]
  refine ⟨hV, hlow, ?_, ?_⟩
  all_goals
    have hV1 : 1 ≤ V := by nlinarith only [hV, hΔ, sq_nonneg (Δ - 1)]
    have hVsq : V ≤ V ^ 2 := by nlinarith only [hV1]
  · have hh := herr ea hea u
    change |ea ⬝ᵥ u| ≤ V / 100
    rw [abs_le]
    constructor <;> nlinarith only [hh, hlow, hVsq, hV1]
  · have hh := herr eb heb u
    change |eb ⬝ᵥ u| ≤ V / 100
    rw [abs_le]
    constructor <;> nlinarith only [hh, hlow, hVsq, hV1]

private def PairSpec (mode : Mode) (Δ : ℚ) (A B : Robust.Estimate d)
    (T : PairTest d) : Prop :=
  ∀ {k} (M : Mixture k d) (a b : Fin k),
    M.Valid → mode.Condition M → mode.Separated M Δ → a ≠ b →
    Robust.Accurate M a A → Robust.Accurate M b B → (2 : ℝ) ^ 40 ≤ Δ →
    ∀ w η : ℝ, 0 < w → (∀ j, w ≤ M.w j) →
      0 ≤ η → η ≤ w ^ 2 / (10000 * k ^ 2 * Δ) →
    let ν := fun j ↦ ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
    let margin := fun j ↦ 2 * η * Real.sqrt
      (ProbabilityTheory.variance (fun y ↦ T.statistic.eval y.ofLp) (ν j))
    (ν a).real {y | ¬ T.contracted (margin a) y.ofLp} ≤ pairError mode Δ ∧
    (ν b).real {y | T.expanded (margin b) y.ofLp} ≤ pairError mode Δ

private def meanTest (A B : Robust.Estimate d) : PairTest d :=
  { statistic := ⟨0, meanDirection A B, 0⟩
    threshold := (meanDirection A B ⬝ᵥ A.mean + meanDirection A B ⬝ᵥ B.mean) / 2
    firstOnLeft := false }

private theorem meanTest_spec (A B : Robust.Estimate d) (Δ : ℚ) :
    PairSpec .identical Δ A B (meanTest A B) := by
  intro k M a b hM hcov hsep hab ha hb hΔ w η hw hweights hη0 hη
  have hΔ1 : (1 : ℝ) ≤ Δ := (by norm_num : (1 : ℝ) ≤ 2 ^ 40).trans hΔ
  have hΔpos : (0 : ℝ) < Δ := by linarith only [hΔ1]
  have hη1 : η ≤ 1 / 100 := by
    have hw1 : w ≤ 1 := by
      apply (hweights a).trans
      rw [← hM.sum_w]
      exact Finset.single_le_sum (fun j _ ↦ hM.nonneg_w j) (Finset.mem_univ a)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk1]
    have hden : (10000 : ℝ) ≤ 10000 * k ^ 2 * Δ := by
      nlinarith only [mul_le_mul hk2 hΔ1 (by norm_num) (sq_nonneg (k : ℝ))]
    have hdenpos : 0 < (10000 : ℝ) * k ^ 2 * Δ := by linarith only [hden]
    apply hη.trans
    rw [div_le_iff₀ hdenpos]
    nlinarith only [hden, hw1, hw]
  have hcovab : M.S a = M.S b := hcov a b
  obtain ⟨hV, hvarbound, hmea, hmeb⟩ :=
    meanDirection_gap M a b A B Δ hM hcovab (hsep a b hab) ha hb hΔ1
  let T := meanTest A B
  let u : Vec d := fun i ↦ (meanDirection A B i : ℝ)
  let V := qform (A.cov.map (algebraMap ℚ ℝ)) u
  let Q := qform (M.S a) u
  let ν := fun j ↦ ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
  let f := fun y : EuclideanSpace ℝ (Fin d) ↦ T.statistic.eval y.ofLp
  change (Δ : ℝ) ^ 2 < V at hV
  change Q ≤ (10 / 9 : ℝ) * V at hvarbound
  have hV1 : 1 ≤ V := by nlinarith only [hV, hΔ1, sq_nonneg ((Δ : ℝ) - 1)]
  have hVpos : 0 < V := by linarith only [hV1]
  have heval (x : Vec d) : T.statistic.eval x = u ⬝ᵥ x := by
    have hz : (0 : Matrix (Fin d) (Fin d) ℚ).map (algebraMap ℚ ℝ) = 0 := by
      ext i j
      exact map_zero (algebraMap ℚ ℝ)
    change qform ((0 : Matrix (Fin d) (Fin d) ℚ).map (algebraMap ℚ ℝ)) x +
      u ⬝ᵥ x + (0 : ℚ) = u ⬝ᵥ x
    rw [hz]
    simp only [qform, zero_mulVec, dotProduct_zero, Rat.cast_zero, zero_add, add_zero]
  have hc (j : Fin k) : ∫ y, f y ∂ν j = u ⬝ᵥ M.μ j := by
    simp only [f, heval]
    exact Population.integral_dotProduct_multivariateGaussian u
  have hv (j : Fin k) : ProbabilityTheory.variance f (ν j) = qform (M.S j) u := by
    simp only [f, heval]
    exact Population.variance_dotProduct_multivariateGaussian (hM.posDef j).posSemidef u
  have hvb : ProbabilityTheory.variance f (ν b) = Q := by rw [hv, ← hcovab]
  have hQa : ProbabilityTheory.variance f (ν a) = Q := hv a
  have hQ0 : 0 ≤ Q := by rw [← hQa]; exact ProbabilityTheory.variance_nonneg _ _
  have hsqrt : Real.sqrt Q ≤ 2 * V := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    nlinarith only [hvarbound, hV1]
  have hmargin : 2 * η * Real.sqrt Q ≤ V / 25 := by
    calc
      _ ≤ 2 * η * (2 * V) := mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ V / 25 := by nlinarith only [hη1, hVpos]
  have hsol := meanDirection_solves A B ha.1
  have hgap : V = u ⬝ᵥ (fun i ↦ (A.mean i : ℝ)) -
      u ⬝ᵥ (fun i ↦ (B.mean i : ℝ)) := by
    change u ⬝ᵥ (A.cov.map (algebraMap ℚ ℝ) *ᵥ u) = _
    rw [hsol]
    exact dotProduct_sub _ _ _
  have hthreshold : (T.threshold : ℝ) =
      (u ⬝ᵥ (fun i ↦ (A.mean i : ℝ)) + u ⬝ᵥ (fun i ↦ (B.mean i : ℝ))) / 2 := by
    simp only [T, meanTest, dotProduct, Rat.cast_div, Rat.cast_add, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_ofNat, u]
  have hca : (2 / 5 : ℝ) * V ≤
      u ⬝ᵥ M.μ a - ((T.threshold : ℝ) + 2 * η * Real.sqrt Q) := by
    change |((fun i ↦ (A.mean i : ℝ)) - M.μ a) ⬝ᵥ u| ≤ V / 100 at hmea
    rw [sub_dotProduct, dotProduct_comm _ u, dotProduct_comm (M.μ a) u] at hmea
    rw [hthreshold]
    linarith only [hgap, (abs_le.mp hmea).2, hmargin, hVpos]
  have hcb : (2 / 5 : ℝ) * V ≤
      ((T.threshold : ℝ) - 2 * η * Real.sqrt Q) - u ⬝ᵥ M.μ b := by
    change |((fun i ↦ (B.mean i : ℝ)) - M.μ b) ⬝ᵥ u| ≤ V / 100 at hmeb
    rw [sub_dotProduct, dotProduct_comm _ u, dotProduct_comm (M.μ b) u] at hmeb
    rw [hthreshold]
    linarith only [hgap, (abs_le.mp hmeb).1, hmargin, hVpos]
  have hbound : Q / ((2 / 5 : ℝ) * V) ^ 2 ≤ 8 / (Δ : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hΔpos)]
    have hh := mul_le_mul_of_nonneg_right hvarbound (sq_nonneg (Δ : ℝ))
    have hmul := mul_le_mul_of_nonneg_left hV.le hVpos.le
    nlinarith only [hh, hmul, sq_nonneg V]
  have hLp (j : Fin k) : MemLp f 2 (ν j) := CompleteAux.statistic_memLp T.statistic _ _
  have hprob (j : Fin k) : IsProbabilityMeasure (ν j) := by
    dsimp only [ν]
    infer_instance
  have herror : pairError .identical Δ = 8 / (Δ : ℝ) ^ 2 := by
    simp only [pairError, Real.rpow_neg hΔpos.le, Real.rpow_two, div_eq_mul_inv]
  rw [herror]
  constructor
  · change (ν a).real {y | ¬ T.contracted _ y.ofLp} ≤ _
    have := hprob a
    refine (Population.measureReal_le_of_subset_dev (hLp a)
      (by positivity : 0 < (2 / 5 : ℝ) * V) (s := {y | ¬ T.contracted _ y.ofLp}) ?_).trans
      (by rw [hQa]; exact hbound)
    intro y hy
    change ¬ ((T.threshold : ℝ) + 2 * η * Real.sqrt (ProbabilityTheory.variance f (ν a)) <
      f y) at hy
    rw [hQa] at hy
    rw [hc]
    exact le_trans (by linarith only [hca, le_of_not_gt hy] :
      (2 / 5 : ℝ) * V ≤ -(f y - u ⬝ᵥ M.μ a)) (neg_le_abs _)
  · change (ν b).real {y | T.expanded _ y.ofLp} ≤ _
    have := hprob b
    refine (Population.measureReal_le_of_subset_dev (hLp b)
      (by positivity : 0 < (2 / 5 : ℝ) * V) (s := {y | T.expanded _ y.ofLp}) ?_).trans
      (by rw [hvb]; exact hbound)
    intro y hy
    change (T.threshold : ℝ) - 2 * η * Real.sqrt (ProbabilityTheory.variance f (ν b)) <
      f y at hy
    rw [hvb] at hy
    rw [hc]
    exact le_trans (by linarith only [hcb, hy] :
      (2 / 5 : ℝ) * V ≤ f y - u ⬝ᵥ M.μ b) (le_abs_self _)

private def squareStatistic (u : Fin d → ℚ) : Statistic d :=
  ⟨vecMulVec u u, 0, 0⟩

private theorem squareStatistic_eval (u : Fin d → ℚ) (x : Vec d) :
    (squareStatistic u).eval x = ((fun i ↦ (u i : ℝ)) ⬝ᵥ x) ^ 2 := by
  have hmap : (vecMulVec u u).map (algebraMap ℚ ℝ) =
      vecMulVec (fun i ↦ (u i : ℝ)) (fun i ↦ (u i : ℝ)) := by
    ext i j
    exact Rat.cast_mul _ _
  simp [Statistic.eval, squareStatistic, hmap, qform, vecMulVec_mulVec,
    op_smul_eq_smul, dotProduct_comm, pow_two]

private theorem squareStatistic_variance (u : Fin d → ℚ) (S : Mat d)
    (hS : S.PosSemidef) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (squareStatistic u).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) =
        2 * qform S (fun i ↦ (u i : ℝ)) ^ 2 := by
  let v : Vec d := fun i ↦ (u i : ℝ)
  have hA : (vecMulVec v v).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, star_trivial, vecMulVec_apply]
    exact mul_comm _ _
  have heval (y : EuclideanSpace ℝ (Fin d)) :
      (squareStatistic u).eval y.ofLp = Population.quadStat (vecMulVec v v) 0 0 y := by
    rw [squareStatistic_eval]
    simp [Population.quadStat, vecMulVec_mulVec, op_smul_eq_smul, dotProduct_comm,
      pow_two, v]
  simp_rw [heval]
  rw [Population.variance_quadStat_multivariateGaussian hS hA]
  simp [vecMulVec_mul, vecMul_vecMulVec, trace_vecMulVec, qform, v,
    dotProduct_mulVec, dotProduct_comm, pow_two]

/-- The spectral threshold remains valid after enlarging both wrong-outcome regions. -/
private theorem spectral_margin_bound (va vb τ r η ma mb : ℝ)
    (ha : 0 < va) (hb : 0 < vb) (hr : 2 ≤ r) (_hη : 0 ≤ η)
    (hηr : η * r ^ 2 ≤ 1 / 100)
    (hτa : τ * r ^ 2 ≤ (11 / 10 : ℝ) * va)
    (hτb : (9 / 5 : ℝ) * r ^ 2 * vb ≤ τ)
    (hma : ma ≤ 4 * η * va) (hmb : mb ≤ 4 * η * vb) :
    (ProbabilityTheory.gaussianReal 0 va.toNNReal).real {x | x ^ 2 ≤ τ + ma} ≤ 2 / r ∧
    (ProbabilityTheory.gaussianReal 0 vb.toNNReal).real {x | τ - mb < x ^ 2} ≤ 2 / r := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr2 : 4 ≤ r ^ 2 := by nlinarith only [hr]
  have hηsmall : η ≤ 1 / 100 := by nlinarith only [hηr, hr2, _hη]
  have hlarge : (τ + ma) * r ^ 2 ≤ 4 * va := by
    have hmul := mul_le_mul_of_nonneg_right hma (sq_nonneg r)
    have he := mul_le_mul_of_nonneg_right hηr (by positivity : 0 ≤ 4 * va)
    nlinarith only [hτa, hmul, he, ha]
  have hsmall : r ^ 2 * vb ≤ τ - mb := by
    have he := mul_le_mul_of_nonneg_right hηsmall (by positivity : 0 ≤ 4 * vb)
    nlinarith only [hτb, hmb, he, hr2, hb]
  have hsqa := Real.sq_sqrt ha.le
  have hsqb := Real.sq_sqrt hb.le
  constructor
  · have hv : va.toNNReal ≠ 0 := by
      exact ne_of_gt (Real.toNNReal_pos.mpr ha)
    have hbound := Population.gaussianReal_zero_abs_le_le hv
      (by positivity : 0 ≤ 2 * Real.sqrt va / r)
    refine (measureReal_mono (μ := ProbabilityTheory.gaussianReal 0 va.toNNReal)
      (fun x hx ↦ ?_) (measure_ne_top _ _)).trans (hbound.trans ?_)
    · change |x| ≤ 2 * Real.sqrt va / r
      change x ^ 2 ≤ τ + ma at hx
      apply (sq_le_sq₀ (abs_nonneg x) (by positivity)).mp
      rw [sq_abs, div_pow, mul_pow, hsqa, le_div_iff₀ (sq_pos_of_pos hr0)]
      norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
      exact (mul_le_mul_of_nonneg_right hx (sq_nonneg r)).trans hlarge
    · rw [Real.coe_toNNReal _ ha.le]
      have he : 2 * Real.sqrt va / r / Real.sqrt va = 2 / r := by
        field_simp
      exact he.le
  · have hbound := Population.gaussianReal_zero_abs_ge_le vb.toNNReal
      (by positivity : 0 < r * Real.sqrt vb)
    refine (measureReal_mono (μ := ProbabilityTheory.gaussianReal 0 vb.toNNReal)
      (fun x hx ↦ ?_) (measure_ne_top _ _)).trans (hbound.trans ?_)
    · change r * Real.sqrt vb ≤ |x|
      change τ - mb < x ^ 2 at hx
      apply (sq_le_sq₀ (by positivity) (abs_nonneg x)).mp
      rw [sq_abs, mul_pow, hsqb]
      exact hsmall.trans hx.le
    · rw [Real.coe_toNNReal _ hb.le, mul_pow, hsqb,
        div_mul_cancel_right₀ hb.ne']
      rw [← one_div]
      rw [div_le_div_iff₀ (sq_pos_of_pos hr0) hr0]
      nlinarith only [hr]

private theorem test_parameters (M : Mixture k d) (a : Fin k) (Δ w η : ℝ)
    (hM : M.Valid) (hΔ : 2 ^ 40 ≤ Δ) (hw : 0 < w) (hweights : ∀ j, w ≤ M.w j)
    (hη0 : 0 ≤ η) (hη : η ≤ w ^ 2 / (10000 * k ^ 2 * Δ)) :
    2 ≤ Δ ^ (1 / 8 : ℝ) ∧ η * (Δ ^ (1 / 8 : ℝ)) ^ 2 ≤ 1 / 100 := by
  have hΔ1 : 1 ≤ Δ := (by norm_num : (1 : ℝ) ≤ 2 ^ 40).trans hΔ
  have hΔ0 : 0 < Δ := by linarith only [hΔ1]
  let r := Δ ^ (1 / 8 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hΔ0.le _
  have hr8 : r ^ 8 = Δ := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ0.le]
    norm_num
  have hr2 : 2 ≤ r := by
    by_contra h
    have hp := pow_lt_pow_left₀ (lt_of_not_ge h) hr0 (by norm_num : 8 ≠ 0)
    rw [hr8] at hp
    norm_num at hp
    linarith only [hp, hΔ]
  have hw1 : w ≤ 1 := by
    apply (hweights a).trans
    rw [← hM.sum_w]
    exact Finset.single_le_sum (fun j _ ↦ hM.nonneg_w j) (Finset.mem_univ a)
  have hk1 : (1 : ℝ) ≤ k := by
    have hak := a.isLt
    exact_mod_cast (by omega : 1 ≤ k)
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk1]
  have hden : 0 < (10000 : ℝ) * k ^ 2 * Δ := by positivity
  have hηmul := (le_div_iff₀ hden).mp hη
  have hηΔ : η * Δ ≤ 1 / 10000 := by
    have hprod := mul_le_mul_of_nonneg_left hk2
      (by positivity : 0 ≤ 10000 * η * Δ)
    nlinarith only [hηmul, hprod, hw, hw1]
  have hpow : r ^ 2 ≤ Δ := by
    rw [← hr8]
    exact pow_le_pow_right₀ (by linarith only [hr2] : 1 ≤ r) (by norm_num : 2 ≤ 8)
  exact ⟨hr2, (mul_le_mul_of_nonneg_left hpow hη0).trans
    (hηΔ.trans (by norm_num))⟩


private def spectralPair (u : Fin d → ℚ) (τ : ℚ) : PairTest d :=
  ⟨squareStatistic u, τ, false⟩


private def PairTest.flip (T : PairTest d) : PairTest d :=
  ⟨T.statistic, T.threshold, !T.firstOnLeft⟩

private theorem PairSpec.flip {mode : Mode} {Δ : ℚ} {A B : Robust.Estimate d}
    {T : PairTest d} (h : PairSpec mode Δ A B T) : PairSpec mode Δ B A T.flip := by
  intro k M a b hM hmode hsep hab ha hb hΔ w η hw hweights hη0 hη
  have hh := h M b a hM hmode hsep (Ne.symm hab) hb ha hΔ w η hw hweights hη0 hη
  cases hb : T.firstOnLeft <;>
    simpa only [PairTest.flip, PairTest.contracted, PairTest.expanded, hb,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte, not_lt, not_le]
      using hh.symm


private def quadraticPair (A B : Robust.Estimate d)
    (Q : Matrix (Fin d) (Fin d) ℚ) : PairTest d :=
  ⟨⟨Q, 0, 0⟩, ((Q * A.cov).trace + (Q * B.cov).trace) / 2, true⟩

private theorem quadraticPair_spec (A B : Robust.Estimate d) (Δ : ℚ)
    (Q : Matrix (Fin d) (Fin d) ℚ)
    (hQt : (Q.map (algebraMap ℚ ℝ))ᵀ = Q.map (algebraMap ℚ ℝ))
    (hgap : let R := Q.map (algebraMap ℚ ℝ)
      let E := A.cov.map (algebraMap ℚ ℝ) + B.cov.map (algebraMap ℚ ℝ)
      (R * (B.cov.map (algebraMap ℚ ℝ) - A.cov.map (algebraMap ℚ ℝ))).trace =
        (R * E * R * E).trace)
    (hsize : let R := Q.map (algebraMap ℚ ℝ)
      let E := A.cov.map (algebraMap ℚ ℝ) + B.cov.map (algebraMap ℚ ℝ)
      2 * (Δ : ℝ) ^ (1 / 8 : ℝ) ≤ (R * E * R * E).trace) :
    PairSpec .centered Δ A B (quadraticPair A B Q) := by
  intro k M a b hM hcenter _ _ ha hb hΔ w η hw hweights hη0 hη
  let R := Q.map (algebraMap ℚ ℝ)
  let EA := A.cov.map (algebraMap ℚ ℝ)
  let EB := B.cov.map (algebraMap ℚ ℝ)
  let E := EA + EB
  let V := (R * E * R * E).trace
  let r := (Δ : ℝ) ^ (1 / 8 : ℝ)
  let T := quadraticPair A B Q
  let ν := fun j ↦ ProbabilityTheory.multivariateGaussian
    (WithLp.toLp 2 (M.μ j)) (M.S j)
  let f := fun y : EuclideanSpace ℝ (Fin d) ↦ T.statistic.eval y.ofLp
  let margin := fun j ↦ 2 * η * Real.sqrt (ProbabilityTheory.variance f (ν j))
  obtain ⟨hr, hηr⟩ := test_parameters M a Δ w η hM hΔ hw hweights hη0 hη
  have hr0 : 0 < r := by linarith only [hr]
  have hV1 : 1 ≤ V := by linarith only [hr, hsize]
  have hV0 : 0 < V := by linarith only [hV1]
  have hE : E.PosSemidef := ha.1.posSemidef.add hb.1.posSemidef
  have hupper : ∀ j ∈ ({a, b} : Finset (Fin k)), LE (M.S j) ((10 / 9 : ℝ) • E) := by
    intro j hj v
    have hqa : 0 ≤ qform EA v := by
      simpa only [qform, star_trivial] using ha.1.posSemidef.dotProduct_mulVec_nonneg v
    have hqb : 0 ≤ qform EB v := by
      simpa only [qform, star_trivial] using hb.1.posSemidef.dotProduct_mulVec_nonneg v
    have he : qform E v = qform EA v + qform EB v := by
      simp only [E, qform, add_mulVec, dotProduct_add]
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
    change qform (M.S j) v ≤ (10 / 9 : ℝ) * qform E v
    rw [he]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with hj | hj
    · rw [hj]
      have hh := ha.2.1 v
      simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
      change (0.9 : ℝ) * qform (M.S a) v ≤ qform EA v at hh
      linarith only [hh, hqb]
    · rw [hj]
      have hh := hb.2.1 v
      simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
      change (0.9 : ℝ) * qform (M.S b) v ≤ qform EB v at hh
      linarith only [hh, hqa]
  have hquad (j : Fin k) (hj : j ∈ ({a, b} : Finset (Fin k))) :
      (R * M.S j * R * M.S j).trace ≤ (100 / 81 : ℝ) * V := by
    have hh := PairwiseAux.trace_quad_mono R (M.S j) ((10 / 9 : ℝ) • E)
      hQt (hM.posDef j).posSemidef (hE.smul (by norm_num)) (hupper j hj)
    rw [PairwiseAux.trace_quad_smul] at hh
    norm_num at hh
    exact hh
  have hν (j : Fin k) : ν j = ProbabilityTheory.multivariateGaussian 0 (M.S j) := by
    simp only [ν, show M.μ j = 0 from hcenter j, WithLp.toLp_zero]
  have heval : f = Population.quadStat R 0 0 := by
    ext y
    simp [f, T, quadraticPair, Statistic.eval, Population.quadStat, qform, R]
  have hRH : R.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hQt
  have hc (j : Fin k) : ∫ y, f y ∂ν j = (R * M.S j).trace := by
    rw [hν, heval, Population.integral_quadStat_multivariateGaussian
      (hM.posDef j).posSemidef hRH]
    exact add_zero _
  have hv (j : Fin k) : ProbabilityTheory.variance f (ν j) =
      2 * (R * M.S j * R * M.S j).trace := by
    rw [hν, heval, Population.variance_quadStat_multivariateGaussian
      (hM.posDef j).posSemidef hRH]
    simp only [zero_dotProduct, add_zero, mul_assoc]
  have hvar (j : Fin k) (hj : j ∈ ({a, b} : Finset (Fin k))) :
      ProbabilityTheory.variance f (ν j) ≤ 3 * V := by
    rw [hv]
    nlinarith only [hquad j hj, hV1]
  have herrors : |(R * EA).trace - (R * M.S a).trace| ≤ V / 8 ∧
      |(R * EB).trace - (R * M.S b).trace| ≤ V / 8 := by
    have hVa := PairwiseAux.center_error_sq EA (M.S a) R
      (hM.posDef a) hQt ha.2.2.2.1
    have hVb := PairwiseAux.center_error_sq EB (M.S b) R
      (hM.posDef b) hQt hb.2.2.2.1
    simp only [mul_sub, trace_sub] at hVa hVb
    have hqa := hquad a (by simp)
    have hqb := hquad b (by simp)
    have hVsq : V ≤ V ^ 2 := by nlinarith only [hV1]
    constructor
    · rw [abs_le]
      constructor <;> nlinarith only [hVa, hqa, hV1, hVsq]
    · rw [abs_le]
      constructor <;> nlinarith only [hVb, hqb, hV1, hVsq]
  have hη1 : η ≤ 1 / 100 := by
    have hr2 : 4 ≤ r ^ 2 := by nlinarith only [hr]
    nlinarith only [hηr, hr2, hη0]
  have hmarg (j : Fin k) (hj : j ∈ ({a, b} : Finset (Fin k))) : margin j ≤ V / 25 := by
    have hs : Real.sqrt (ProbabilityTheory.variance f (ν j)) ≤ 2 * V := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity, by nlinarith only [hvar j hj, hV1]⟩
    calc
      _ ≤ 2 * η * (2 * V) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ V / 25 := by nlinarith only [hη1, hV0]
  have hmid : (T.threshold : ℝ) = ((R * EA).trace + (R * EB).trace) / 2 := by
    simp only [T, quadraticPair, trace, diag, Matrix.mul_apply, Rat.cast_div,
      Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, R, EA, EB, map_apply]
    rfl
  have hg : (R * EB).trace - (R * EA).trace = V := by
    simpa only [mul_sub, trace_sub] using hgap
  have hga : V / 3 ≤ (T.threshold : ℝ) - margin a - (R * M.S a).trace := by
    rw [hmid]
    linarith only [hg, (abs_le.mp herrors.1).1, hmarg a (by simp), hV0]
  have hgb : V / 3 ≤ (R * M.S b).trace - ((T.threshold : ℝ) + margin b) := by
    rw [hmid]
    linarith only [hg, (abs_le.mp herrors.2).2, hmarg b (by simp), hV0]
  have herror : 3 * V / (V / 3) ^ 2 ≤ pairError .centered Δ := by
    have hΔ0 : (0 : ℝ) < Δ := lt_of_lt_of_le (by norm_num) hΔ
    simp only [pairError, Real.rpow_neg hΔ0.le]
    change 3 * V / (V / 3) ^ 2 ≤ 16 * r⁻¹
    rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hr0]
    have hm := mul_le_mul_of_nonneg_left hsize hV0.le
    nlinarith only [hm, hV0]
  have hLp (j : Fin k) : MemLp f 2 (ν j) := CompleteAux.statistic_memLp T.statistic _ _
  have hprob (j : Fin k) : IsProbabilityMeasure (ν j) := by dsimp only [ν]; infer_instance
  constructor
  · change (ν a).real {y | ¬ T.contracted (margin a) y.ofLp} ≤ _
    have := hprob a
    refine (Population.measureReal_le_of_subset_dev (hLp a)
      (by positivity : 0 < V / 3) (s := {y | ¬ T.contracted (margin a) y.ofLp}) ?_).trans
      ((div_le_div_of_nonneg_right (hvar a (by simp)) (sq_nonneg _)).trans herror)
    intro y hy
    change ¬ f y ≤ (T.threshold : ℝ) - margin a at hy
    rw [hc]
    exact (by linarith only [hga, lt_of_not_ge hy] :
      V / 3 ≤ f y - (R * M.S a).trace).trans (le_abs_self _)
  · change (ν b).real {y | T.expanded (margin b) y.ofLp} ≤ _
    have := hprob b
    refine (Population.measureReal_le_of_subset_dev (hLp b)
      (by positivity : 0 < V / 3) (s := {y | T.expanded (margin b) y.ofLp}) ?_).trans
      ((div_le_div_of_nonneg_right (hvar b (by simp)) (sq_nonneg _)).trans herror)
    intro y hy
    change f y ≤ (T.threshold : ℝ) + margin b at hy
    rw [hc]
    exact (by linarith only [hgb, hy] :
      V / 3 ≤ -(f y - (R * M.S b).trace)).trans (neg_le_abs _)

private theorem eighth_root_bounds (Δ : ℝ) (hΔ : 2 ^ 40 ≤ Δ) :
    32 ≤ Δ ^ (1 / 8 : ℝ) ∧ (Δ ^ (1 / 8 : ℝ)) ^ 8 = Δ := by
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (by norm_num) hΔ
  let r := Δ ^ (1 / 8 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hΔ0.le _
  have hr8 : r ^ 8 = Δ := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ0.le]
    norm_num
  refine ⟨?_, hr8⟩
  by_contra h
  have hp := pow_lt_pow_left₀ (lt_of_not_ge h) hr0 (by norm_num : 8 ≠ 0)
  rw [hr8] at hp
  norm_num at hp hΔ
  exact (not_lt_of_ge hΔ) hp

end

end ABBKS26.Select
