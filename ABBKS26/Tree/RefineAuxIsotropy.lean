module

public import ABBKS26.Tree.RefineAuxPopulation

/-! Population isotropy in an affine empirical frame. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix MvPolynomial
open scoped BigOperators

variable {n k d : ℕ}

private theorem projected_second (R : Robust.Reference n k d) (θ : ℝ)
    (hres : R.Resilient 4 θ) (i : Fin d) (u a : Vec d) (j : Fin k) :
    let Cj := R.reference.filter (fun l ↦ R.label l = j)
    |(Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (R.clean l - a)) ^ 2 -
      ((u ⬝ᵥ (R.model.mean j - a)) ^ 2 + qform (R.model.cov j) u)| ≤
      (θ / (d + 1 : ℝ) ^ 8) *
        (1 + |u ⬝ᵥ (R.model.mean j - a)| + |qform (R.model.cov j) u|) ^ 2 := by
  let Cj := R.reference.filter (fun l ↦ R.label l = j)
  have h := hres (vecMulVec (Pi.single i 1) u) a j 2 (by omega)
  dsimp only at h ⊢
  simp only [Robust.FilterAux.lin_projection, Robust.FilterAux.quad_projection] at h
  have he : (C (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (C (u ⬝ᵥ (R.clean l - a)) * X i) ^ 2) -
      IdCov.hmom 2 (C (u ⬝ᵥ (R.model.mean j - a)) * X i)
        (C (qform (R.model.cov j) u) * X i ^ 2) =
      C ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (R.clean l - a)) ^ 2 -
        ((u ⬝ᵥ (R.model.mean j - a)) ^ 2 + qform (R.model.cov j) u)) *
          (X i : RPoly d) ^ 2 := by
    rw [Robust.FilterAux.hmom_monomial, Robust.FilterAux.hmom_two]
    simp only [mul_pow, ← map_pow, ← Finset.sum_mul, ← map_sum]
    rw [← mul_assoc, ← C_mul, ← sub_mul, ← C_sub]
  change SoS.coeffNorm1 ((C (Cj.card : ℝ)⁻¹ *
    ∑ l ∈ Cj, (C (u ⬝ᵥ (R.clean l - a)) * X i) ^ 2) - _) ≤ _ at h
  rw [he] at h
  simpa only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, X_pow_eq_monomial,
    SoS.coeffNorm1_monomial, abs_one, mul_one] using h

/-- The second moment error is relative to the full second moment about any origin. -/
theorem component_second_error (R : Robust.Reference n k d) (θ : ℝ)
    (hcov : ∀ j, (R.model.cov j).PosDef) (hθ : 0 ≤ θ) (hres : R.Resilient 4 θ)
    (u a : Vec d) (j : Fin k) :
    let Cj := R.reference.filter (fun l ↦ R.label l = j)
    let m := (u ⬝ᵥ (R.model.mean j - a)) ^ 2 + qform (R.model.cov j) u
    |(Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (R.clean l - a)) ^ 2 - m| ≤ 9 * θ * m := by
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let μ := u ⬝ᵥ (R.model.mean j - a)
  let S := qform (R.model.cov j) u
  let m := μ ^ 2 + S
  let c := (Real.sqrt m)⁻¹
  let δ := θ / (d + 1 : ℝ) ^ 8
  have hS : 0 < S := by
    simpa only [S, qform, star_trivial] using (hcov j).dotProduct_mulVec_pos hu
  have hm : 0 < m := add_pos_of_nonneg_of_pos (sq_nonneg μ) hS
  have hroot : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hc : 0 < c := inv_pos.mpr hroot
  have hcm : c ^ 2 * m = 1 := by
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt hm.le]
    exact inv_mul_cancel₀ hm.ne'
  have hnorm : (c * μ) ^ 2 + c ^ 2 * S = 1 := by
    change c ^ 2 * (μ ^ 2 + S) = 1 at hcm
    nlinarith only [hcm]
  have hcs : 0 ≤ c ^ 2 * S := by positivity
  have hμ : |c * μ| ≤ 1 := by
    nlinarith only [hnorm, hcs, sq_abs (c * μ), abs_nonneg (c * μ)]
  have hsmall : (1 + |c * μ| + |c ^ 2 * S|) ^ 2 ≤ 9 := by
    rw [abs_of_nonneg hcs]
    nlinarith only [hnorm, hμ, hcs, sq_nonneg (c * μ), abs_nonneg (c * μ)]
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hδθ : δ ≤ θ := div_le_self hθ
    (one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) d]))
  have h := projected_second R θ hres i (c • u) a j
  dsimp only at h
  simp only [smul_dotProduct, smul_eq_mul, mul_pow, ← Finset.mul_sum,
    qform, mulVec_smul, dotProduct_smul] at h
  change |((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    (c ^ 2 * ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
      (u ⬝ᵥ (R.clean l - a)) ^ 2) - (c ^ 2 * μ ^ 2 + c * (c * S))| ≤
    δ * (1 + |c * μ| + |c * (c * S)|) ^ 2 at h
  have he : c * (c * S) = c ^ 2 * S := by ring
  rw [he] at h
  have hb : δ * (1 + |c * μ| + |c ^ 2 * S|) ^ 2 ≤ 9 * δ := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hδ]
  have heq : ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
      (c ^ 2 * ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
        (u ⬝ᵥ (R.clean l - a)) ^ 2) - (c ^ 2 * μ ^ 2 + c ^ 2 * S) =
      c ^ 2 * (((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
          (u ⬝ᵥ (R.clean l - a)) ^ 2 - m) := by dsimp only [m]; ring
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg c)] at h
  have hh := mul_le_mul_of_nonneg_right (h.trans hb) hm.le
  dsimp only
  change |((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
      (u ⬝ᵥ (R.clean l - a)) ^ 2 - m| ≤ 9 * θ * m
  have hδm := mul_le_mul_of_nonneg_right hδθ hm.le
  have hcancel (x : ℝ) : c ^ 2 * x * m = x := by
    calc
      _ = (c ^ 2 * m) * x := by ring
      _ = x := by rw [hcm, one_mul]
  rw [hcancel] at hh
  linarith only [hh, hδm]

private theorem reference_partition (R : Robust.Reference n k d) (w : ℝ)
    (hR : R.Valid w) (f : Fin n → ℝ) :
    (∑ j, R.model.weight j *
      ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), f l) =
      (R.reference.card : ℝ)⁻¹ * ∑ l ∈ R.reference, f l := by
  classical
  have he (j : Fin k) : R.model.weight j *
      ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ =
      (R.reference.card : ℝ)⁻¹ := by
    have hw : 0 < R.model.weight j := hR.1.1.trans_le (hR.1.2.1 j)
    have hc : ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ) ≠ 0 := by
      intro hc
      rw [hR.2.2.2.2.2.2 j, hc, zero_div] at hw
      exact (lt_irrefl 0) hw
    rw [hR.2.2.2.2.2.2 j, div_eq_mul_inv]
    field_simp
  simp only [he, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

private theorem covariance_raw_second (R : Robust.Reference n k d) (w : ℝ)
    (hR : R.Valid w) (u : Vec d) :
    qform R.cov u = (R.reference.card : ℝ)⁻¹ *
      ∑ l ∈ R.reference, (u ⬝ᵥ R.clean l) ^ 2 - (u ⬝ᵥ R.mean) ^ 2 := by
  have hn : (R.reference.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hR.2.2.2.2.1).ne'
  have hmean : (R.reference.card : ℝ)⁻¹ *
      ∑ l ∈ R.reference, u ⬝ᵥ R.clean l = u ⬝ᵥ R.mean := by
    simp only [Robust.Reference.mean, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  have he (l : Fin n) : (u ⬝ᵥ (R.clean l - R.mean)) ^ 2 =
      (u ⬝ᵥ R.clean l) ^ 2 - 2 * (u ⬝ᵥ R.clean l) * (u ⬝ᵥ R.mean) +
        (u ⬝ᵥ R.mean) ^ 2 := by rw [dotProduct_sub]; ring
  simp only [Robust.Reference.cov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
    dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  simp_rw [dotProduct_comm (R.clean _ - R.mean) u, ← pow_two, he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, mul_add, mul_sub]
  rw [show (R.reference.card : ℝ)⁻¹ *
      (2 * (∑ l ∈ R.reference, u ⬝ᵥ R.clean l) * (u ⬝ᵥ R.mean)) =
      2 * (u ⬝ᵥ R.mean) ^ 2 by rw [← hmean]; ring]
  field_simp
  ring

/-- Empirical and population raw second moments agree up to relative resilience error. -/
theorem second_moment_comparison (R : Robust.Reference n k d) (w θ : ℝ)
    (hR : R.Valid w) (hθ : 0 ≤ θ) (hres : R.Resilient 4 θ) (u : Vec d) :
    |qform R.cov u + (u ⬝ᵥ R.mean) ^ 2 - qform R.model.second u| ≤
      9 * θ * qform R.model.second u := by
  let m := fun j ↦ (u ⬝ᵥ R.model.mean j) ^ 2 + qform (R.model.cov j) u
  let s := fun j ↦ ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), (u ⬝ᵥ R.clean l) ^ 2
  have hcomponent (j) : |s j - m j| ≤ 9 * θ * m j := by
    simpa only [sub_zero] using
      component_second_error R θ hR.1.2.2.2 hθ hres u 0 j
  have hw (j : Fin k) : 0 ≤ R.model.weight j := hR.1.1.le.trans (hR.1.2.1 j)
  have hpop : (∑ j, R.model.weight j * m j) = qform R.model.second u := by
    simp only [m, FrameModel.second, qform, sum_mulVec, dotProduct_sum,
      smul_mulVec, dotProduct_smul, smul_eq_mul, add_mulVec, dotProduct_add,
      vecMulVec_mulVec, op_smul_eq_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [dotProduct_comm (R.model.mean j) u]
    ring
  have hemp : (∑ j, R.model.weight j * s j) =
      qform R.cov u + (u ⬝ᵥ R.mean) ^ 2 := by
    simp only [s, ← mul_assoc]
    rw [reference_partition R w hR, covariance_raw_second R w hR]
    ring
  rw [← hemp, ← hpop, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |R.model.weight j * s j - R.model.weight j * m j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, R.model.weight j * |s j - m j| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw j)]
    _ ≤ ∑ j, R.model.weight j * (9 * θ * m j) :=
      Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcomponent j) (hw j)
    _ = _ := by rw [Finset.mul_sum]; congr 1; funext j; ring

/-- The error includes the squared empirical mean in the chosen affine coordinates. -/
theorem affine_isotropic_of_empirical (R : Robust.Reference n k d) (w θ e b : ℝ)
    (hR : R.Valid w) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : R.Resilient 4 θ)
    (he : 0 ≤ e ∧ e ≤ 1 / 100) (hb : 0 ≤ b ∧ b ≤ 1 / 100)
    (hC : frobSq (R.cov - 1) ≤ e ^ 2) (hmean : sqnorm R.mean ≤ b) :
    R.model.Isotropic (2 * e + 2 * b + 40 * θ) := by
  have hsecond (v : Vec d) : 0 ≤ qform R.model.second v := by
    simp only [FrameModel.second, qform, sum_mulVec, dotProduct_sum, smul_mulVec,
      dotProduct_smul, smul_eq_mul, add_mulVec, dotProduct_add, vecMulVec_mulVec,
      op_smul_eq_smul]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hR.1.1.le.trans (hR.1.2.1 j))
    rw [dotProduct_comm (R.model.mean j) v]
    exact add_nonneg ((hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v)
      (mul_self_nonneg _)
  have hbnd (v : Vec d) :
      (1 - (2 * e + 2 * b + 40 * θ)) * sqnorm v ≤ qform R.model.second v ∧
        qform R.model.second v ≤ (1 + (2 * e + 2 * b + 40 * θ)) * sqnorm v := by
    have hn := Rounding.DetRoundAux.sqnorm_nonneg v
    have hv := hsecond v
    have hm : (v ⬝ᵥ R.mean) ^ 2 ≤ b * sqnorm v := by
      have hh : (v ⬝ᵥ R.mean) ^ 2 ≤ sqnorm v * sqnorm R.mean := by
        simpa only [sqnorm, dotProduct, pow_two] using
          Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) v R.mean
      exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hmean hn])
    have hc := abs_le.mp (Rounding.DetRoundAux.abs_qform_le (R.cov - 1) e he.1 hC v)
    have hq : qform (R.cov - 1) v = qform R.cov v - sqnorm v := by
      simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub, sqnorm]
    rw [hq] at hc
    have hs := abs_le.mp (second_moment_comparison R w θ hR hθ.1 hres v)
    have hθv := mul_le_mul_of_nonneg_right hθ.2 hv
    have hen := mul_le_mul_of_nonneg_right he.2 hn
    have hbn := mul_le_mul_of_nonneg_right hb.2 hn
    have htwo : qform R.model.second v ≤ 2 * sqnorm v := by
      nlinarith only [hs.1, hc.2, hm, hθv, hen, hbn, hn]
    have hθtwo := mul_le_mul_of_nonneg_left htwo hθ.1
    constructor <;> nlinarith only [hs.1, hs.2, hc.1, hc.2, hm, hθtwo,
      mul_nonneg he.1 hn, mul_nonneg hb.1 hn, mul_nonneg hθ.1 hn,
      sq_nonneg (v ⬝ᵥ R.mean)]
  refine ⟨by linarith only [he.1, hb.1, hθ.1], ?_, ?_⟩
  · intro v
    simpa only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm]
      using (hbnd v).1
  · intro v
    simpa only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm]
      using (hbnd v).2

end

end ABBKS26.RefineAux
