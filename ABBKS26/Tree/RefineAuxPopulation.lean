module

public import ABBKS26.Tree.RefineAuxAffine

/-! Population second moments in a centered empirical frame. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix MvPolynomial
open scoped BigOperators

variable {n k d : ℕ}

private theorem projected_moment (R : Robust.Reference n k d) (θ : ℝ)
    (hres : R.Resilient 4 θ) (i : Fin d) (u a : Vec d) (j : Fin k)
    (r : ℕ) (hr : r ≤ 4) :
    let Cj := R.reference.filter (fun l ↦ R.label l = j)
    |(Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (R.clean l - a)) ^ r -
      IdCov.hmom r (u ⬝ᵥ (R.model.mean j - a)) (qform (R.model.cov j) u)| ≤
      (θ / (d + 1 : ℝ) ^ 8) *
        (1 + |u ⬝ᵥ (R.model.mean j - a)| + |qform (R.model.cov j) u|) ^ r := by
  let Cj := R.reference.filter (fun l ↦ R.label l = j)
  have h := hres (vecMulVec (Pi.single i 1) u) a j r hr
  dsimp only at h ⊢
  simp only [Robust.FilterAux.lin_projection, Robust.FilterAux.quad_projection] at h
  have he : (C (Cj.card : ℝ)⁻¹ *
      ∑ l ∈ Cj, (C (u ⬝ᵥ (R.clean l - a)) * X i) ^ r) -
      IdCov.hmom r (C (u ⬝ᵥ (R.model.mean j - a)) * X i)
        (C (qform (R.model.cov j) u) * X i ^ 2) =
      C ((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ (R.clean l - a)) ^ r -
        IdCov.hmom r (u ⬝ᵥ (R.model.mean j - a)) (qform (R.model.cov j) u)) *
          (X i : RPoly d) ^ r := by
    rw [Robust.FilterAux.hmom_monomial]
    simp only [mul_pow, ← map_pow, ← Finset.sum_mul, ← map_sum]
    rw [← mul_assoc, ← C_mul, ← sub_mul, ← C_sub]
  change SoS.coeffNorm1 ((C (Cj.card : ℝ)⁻¹ *
    ∑ l ∈ Cj, (C (u ⬝ᵥ (R.clean l - a)) * X i) ^ r) - _) ≤ _ at h
  rw [he] at h
  simpa only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, X_pow_eq_monomial,
    SoS.coeffNorm1_monomial, abs_one, mul_one] using h

/-- Rescaling the resilience inequality gives relative first and second moment errors. -/
theorem centered_component_moments (R : Robust.Reference n k d) (θ : ℝ)
    (hcov : ∀ j, (R.model.cov j).PosDef) (hcen : ∀ j, R.model.mean j = 0)
    (hres : R.Resilient 4 θ) (u : Vec d) (j : Fin k) :
    let Cj := R.reference.filter (fun l ↦ R.label l = j)
    let δ := θ / (d + 1 : ℝ) ^ 8
    (((Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, u ⬝ᵥ R.clean l) ^ 2 ≤
      4 * δ ^ 2 * qform (R.model.cov j) u) ∧
    |(Cj.card : ℝ)⁻¹ * ∑ l ∈ Cj, (u ⬝ᵥ R.clean l) ^ 2 -
      qform (R.model.cov j) u| ≤ 4 * δ * qform (R.model.cov j) u := by
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let V := qform (R.model.cov j) u
  let s := Real.sqrt V
  let c := s⁻¹
  have hV : 0 < V := by
    simpa only [V, qform, star_trivial] using (hcov j).dotProduct_mulVec_pos hu
  have hs : 0 < s := Real.sqrt_pos.mpr hV
  have hs2 : s ^ 2 = V := Real.sq_sqrt hV.le
  have hc : 0 < c := inv_pos.mpr hs
  have hcV : qform (R.model.cov j) (c • u) = 1 := by
    simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    change c * (c * V) = 1
    dsimp only [c]
    rw [← hs2]
    field_simp
  have h1 := projected_moment R θ hres i (c • u) 0 j 1 (by omega)
  have h2 := projected_moment R θ hres i (c • u) 0 j 2 (by omega)
  simp only [hcen, sub_self, sub_zero, dotProduct_zero, hcV, IdCov.hmom,
    IdCov.hermCoeff] at h1 h2
  norm_num [Finset.sum_range_succ] at h1 h2
  simp only [mul_pow, ← Finset.mul_sum] at h1 h2
  dsimp only
  constructor
  · have hh := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, sq_abs] at hh
    have hm := mul_le_mul_of_nonneg_right hh hV.le
    have he : ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
        (c * ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), u ⬝ᵥ R.clean l) =
        c * (((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
          ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), u ⬝ᵥ R.clean l) := by ring
    rw [← mul_pow, he, mul_pow] at hm
    have hec : c ^ 2 * V = 1 := by dsimp only [c]; rw [← hs2]; field_simp
    nlinarith only [hm, hec]
  · have hm := mul_le_mul_of_nonneg_right h2 hV.le
    have hec : c ^ 2 * V = 1 := by dsimp only [c]; rw [← hs2]; field_simp
    have he : (((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
        (c ^ 2 * ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
          (u ⬝ᵥ R.clean l) ^ 2) - 1) * V =
        ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
          ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
            (u ⬝ᵥ R.clean l) ^ 2 - V := by
      calc _ = (c ^ 2 * V) *
            (((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
              ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
                (u ⬝ᵥ R.clean l) ^ 2) - V := by ring
        _ = _ := by rw [hec, one_mul]
    rw [← abs_of_pos hV, ← abs_mul, he, abs_of_pos hV] at hm
    simpa only [mul_comm (θ / (d + 1 : ℝ) ^ 8) 4] using hm

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

/-- The empirical covariance of centered components approximates their population second moment. -/
theorem centered_covariance_comparison (R : Robust.Reference n k d) (w θ : ℝ)
    (hR : R.Valid w) (hcen : ∀ j, R.model.mean j = 0)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : R.Resilient 4 θ) (u : Vec d) :
    (1 - 5 * θ) * qform R.model.second u ≤ qform R.cov u ∧
      qform R.cov u ≤ (1 + 4 * θ) * qform R.model.second u := by
  let δ := θ / (d + 1 : ℝ) ^ 8
  let m := fun j ↦ ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), u ⬝ᵥ R.clean l
  let s := fun j ↦ ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), (u ⬝ᵥ R.clean l) ^ 2
  let V := qform R.model.second u
  let E := (R.reference.card : ℝ)⁻¹ * ∑ l ∈ R.reference, (u ⬝ᵥ R.clean l) ^ 2
  let μ := u ⬝ᵥ R.mean
  have hδ0 : 0 ≤ δ := div_nonneg hθ.1 (by positivity)
  have hd : (1 : ℝ) ≤ d + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hδθ : δ ≤ θ := div_le_self hθ.1 (one_le_pow₀ hd)
  have hδ : δ ≤ 1 / 100 := hδθ.trans hθ.2
  have hw (j : Fin k) : 0 ≤ R.model.weight j := hR.1.1.le.trans (hR.1.2.1 j)
  have hVj (j : Fin k) : 0 ≤ qform (R.model.cov j) u := by
    simpa only [qform, star_trivial] using
      (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u
  have hVeq : (∑ j, R.model.weight j * qform (R.model.cov j) u) = V := by
    simp only [V, FrameModel.second, hcen, vecMulVec_zero, add_zero, qform,
      sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hV : 0 ≤ V := hVeq ▸ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (hVj j)
  have hsum_m : (∑ j, R.model.weight j * m j) = μ := by
    simp only [m, ← mul_assoc]
    rw [reference_partition R w hR]
    simp only [μ, Robust.Reference.mean, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  have hsum_s : (∑ j, R.model.weight j * s j) = E := by
    simp only [s, ← mul_assoc]
    exact reference_partition R w hR _
  have hcomponent := centered_component_moments R θ hR.1.2.2.2 hcen hres u
  have hmsq : (∑ j, R.model.weight j * m j ^ 2) ≤ 4 * δ ^ 2 * V := by
    calc
      _ ≤ ∑ j, R.model.weight j * (4 * δ ^ 2 * qform (R.model.cov j) u) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcomponent j).1 (hw j)
      _ = _ := by rw [← hVeq, Finset.mul_sum]; congr 1; funext j; ring
  have hμsq : μ ^ 2 ≤ 4 * δ ^ 2 * V := by
    apply le_trans _ hmsq
    have hh : 0 ≤ ∑ j, R.model.weight j * (m j - μ) ^ 2 :=
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (sq_nonneg _)
    have he : (∑ j, R.model.weight j * (m j - μ) ^ 2) =
        (∑ j, R.model.weight j * m j ^ 2) - μ ^ 2 := by
      simp_rw [sub_sq, mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [show ∀ j, R.model.weight j * (2 * m j * μ) =
        2 * μ * (R.model.weight j * m j) by intro j; ring]
      rw [← Finset.mul_sum, hsum_m, ← Finset.sum_mul, hR.1.2.2.1]
      ring
    rw [he] at hh
    linarith only [hh]
  have hE : (1 - 4 * δ) * V ≤ E ∧ E ≤ (1 + 4 * δ) * V := by
    have hl (j : Fin k) := (abs_le.mp (hcomponent j).2).1
    have hu (j : Fin k) := (abs_le.mp (hcomponent j).2).2
    constructor
    · calc
        _ = ∑ j, R.model.weight j * ((1 - 4 * δ) * qform (R.model.cov j) u) := by
          rw [← hVeq, Finset.mul_sum]; congr 1; funext j; ring
        _ ≤ ∑ j, R.model.weight j * s j := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hw j)
          linarith only [hl j]
        _ = E := hsum_s
    · calc
        E = ∑ j, R.model.weight j * s j := hsum_s.symm
        _ ≤ ∑ j, R.model.weight j * ((1 + 4 * δ) * qform (R.model.cov j) u) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hw j)
          linarith only [hu j]
        _ = _ := by rw [← hVeq, Finset.mul_sum]; congr 1; funext j; ring
  have hC : qform R.cov u = E - μ ^ 2 := covariance_raw_second R w hR u
  have hδV := mul_le_mul_of_nonneg_right hδθ hV
  have hsδ : 4 * δ ^ 2 ≤ δ := by nlinarith only [hδ0, hδ]
  have hsδV := mul_le_mul_of_nonneg_right hsδ hV
  constructor <;> nlinarith only [hC, hE.1, hE.2, hμsq, hδV, hsδV, sq_nonneg μ]

/-- Small empirical normalization error transfers to population isotropy in the centered case. -/
theorem centered_isotropic_of_empirical (R : Robust.Reference n k d) (w θ e : ℝ)
    (hR : R.Valid w) (hcen : ∀ j, R.model.mean j = 0)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : R.Resilient 4 θ)
    (he : 0 ≤ e ∧ e ≤ 1 / 100) (hC : frobSq (R.cov - 1) ≤ e ^ 2) :
    R.model.Isotropic (2 * e + 20 * θ) := by
  have hsecond (v : Vec d) : 0 ≤ qform R.model.second v := by
    simp only [FrameModel.second, hcen, vecMulVec_zero, add_zero, qform,
      sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact Finset.sum_nonneg fun j _ ↦ mul_nonneg
      (hR.1.1.le.trans (hR.1.2.1 j))
      ((hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg v)
  have hb (v : Vec d) :
      (1 - (2 * e + 20 * θ)) * sqnorm v ≤ qform R.model.second v ∧
        qform R.model.second v ≤ (1 + (2 * e + 20 * θ)) * sqnorm v := by
    have hn := Rounding.DetRoundAux.sqnorm_nonneg v
    have hv := hsecond v
    obtain ⟨hl, hu⟩ := centered_covariance_comparison R w θ hR hcen hθ hres v
    have hc := abs_le.mp (Rounding.DetRoundAux.abs_qform_le (R.cov - 1) e he.1 hC v)
    have hq : qform (R.cov - 1) v = qform R.cov v - sqnorm v := by
      simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub, sqnorm]
    rw [hq] at hc
    have hθv := mul_le_mul_of_nonneg_right hθ.2 hv
    have hen := mul_le_mul_of_nonneg_right he.2 hn
    have htwo : qform R.model.second v ≤ 2 * sqnorm v := by
      nlinarith only [hl, hc.2, hθv, hen, hn]
    have hθtwo := mul_le_mul_of_nonneg_left htwo hθ.1
    have hen0 := mul_nonneg he.1 hn
    constructor <;> nlinarith only [hl, hu, hc.1, hc.2, hθtwo, hen0,
      mul_nonneg hθ.1 hn]
  refine ⟨add_nonneg (mul_nonneg (by norm_num) he.1)
    (mul_nonneg (by norm_num) hθ.1), ?_, ?_⟩
  · intro v
    simpa only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm]
      using (hb v).1
  · intro v
    simpa only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm]
      using (hb v).2

theorem isotropic_mono (F : FrameModel k d) (γ Γ : ℝ) (hF : F.Isotropic γ) (hle : γ ≤ Γ) :
    F.Isotropic Γ := by
  refine ⟨hF.1.trans hle, ?_, ?_⟩
  · intro v
    have h := hF.2.1 v
    have hn := Rounding.DetRoundAux.sqnorm_nonneg v
    have hh := mul_le_mul_of_nonneg_right hle hn
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      at h ⊢
    change (1 - γ) * sqnorm v ≤ qform F.second v at h
    change (1 - Γ) * sqnorm v ≤ qform F.second v
    linarith only [h, hh]
  · intro v
    have h := hF.2.2 v
    have hn := Rounding.DetRoundAux.sqnorm_nonneg v
    have hh := mul_le_mul_of_nonneg_right hle hn
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      at h ⊢
    change qform F.second v ≤ (1 + γ) * sqnorm v at h
    change qform F.second v ≤ (1 + Γ) * sqnorm v
    linarith only [h, hh]

/-- Every component mean is bounded in an empirical frame, relative to the reference mean. -/
theorem population_component_mean_sq (R : Robust.Reference n k d) (T : Mat d) (w θ : ℝ)
    (hR : R.Valid w) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : R.Resilient 4 θ)
    (hcov : LE (T * R.cov * Tᵀ) ((1.01 : ℝ) • (1 : Mat d))) (j : Fin k) :
    sqnorm (T *ᵥ (R.model.mean j - R.mean)) ≤ 1.1 / w := by
  let μ := T *ᵥ (R.model.mean j - R.mean)
  have hn := Rounding.DetRoundAux.sqnorm_nonneg μ
  by_cases hz : sqnorm μ = 0
  · change sqnorm μ ≤ _
    rw [hz]
    exact div_nonneg (by norm_num) hR.1.1.le
  have hpos : 0 < sqnorm μ := lt_of_le_of_ne hn (Ne.symm hz)
  have hp := population_component_second_le R w θ hR
    ⟨hθ.1, hθ.2.trans (by norm_num)⟩ hres (Tᵀ *ᵥ μ) j
  have hq : 0 ≤ qform (R.model.cov j) (Tᵀ *ᵥ μ) :=
    (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg _
  have hw : 0 ≤ R.model.weight j := hR.1.1.le.trans (hR.1.2.1 j)
  have hdot : (Tᵀ *ᵥ μ) ⬝ᵥ (R.model.mean j - R.mean) = sqnorm μ := by
    change _ = μ ⬝ᵥ (T *ᵥ (R.model.mean j - R.mean))
    rw [dotProduct_mulVec, ← mulVec_transpose]
  rw [hdot, ← Robust.RBAux.qform_conjugate T R.cov] at hp
  have hc := hcov μ
  change qform (T * R.cov * Tᵀ) μ ≤ qform ((1.01 : ℝ) • (1 : Mat d)) μ at hc
  simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hc
  change qform (T * R.cov * Tᵀ) μ ≤ 1.01 * sqnorm μ at hc
  have hθn := mul_le_mul_of_nonneg_right hθ.2 hn
  have hc' := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ 1 + θ by linarith only [hθ.1])
  have hm : R.model.weight j * sqnorm μ ^ 2 ≤ 1.1 * sqnorm μ := by
    nlinarith only [hp, hc', hθn, hn, mul_nonneg hw hq]
  have hwμ := mul_le_mul_of_nonneg_right (hR.1.2.1 j) (sq_nonneg (sqnorm μ))
  change sqnorm μ ≤ _
  rw [le_div_iff₀ hR.1.1]
  have hh : (w * sqnorm μ) * sqnorm μ ≤ 1.1 * sqnorm μ := by
    nlinarith only [hm, hwμ]
  exact (mul_le_mul_iff_left₀ hpos).mp (by nlinarith only [hh])

private theorem sqnorm_sub_le (u v : Vec d) :
    sqnorm (u - v) ≤ (3 / 2 : ℝ) * sqnorm u + 3 * sqnorm v := by
  have hh := Rounding.DetRoundAux.sqnorm_nonneg (u + 2 • v)
  simp only [two_smul, sqnorm, add_dotProduct, dotProduct_add, sub_dotProduct,
    dotProduct_sub] at hh ⊢
  rw [dotProduct_comm v u] at hh ⊢
  nlinarith only [hh]

/-- A center close to the reference mean meets the robust moment procedure's mean bound. -/
theorem population_component_mean_bound (R : Robust.Reference n k d) (T : Mat d)
    (a : Vec d) (w θ : ℝ) (hR : R.Valid w) (hw : w ≤ 1)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : R.Resilient 4 θ)
    (hcov : LE (T * R.cov * Tᵀ) ((1.01 : ℝ) • (1 : Mat d)))
    (ha : sqnorm (T *ᵥ (a - R.mean)) ≤ 1 / 100) (j : Fin k) :
    sqnorm (T *ᵥ (R.model.mean j - a)) ≤ 2 / w := by
  have hm := population_component_mean_sq R T w θ hR hθ hres hcov j
  have he : T *ᵥ (R.model.mean j - a) =
      T *ᵥ (R.model.mean j - R.mean) - T *ᵥ (a - R.mean) := by
    rw [← mulVec_sub]
    congr 1
    abel
  rw [he]
  apply (sqnorm_sub_le _ _).trans
  have hm' := (le_div_iff₀ hR.1.1).mp hm
  rw [le_div_iff₀ hR.1.1]
  have ha' := mul_le_mul_of_nonneg_right ha hR.1.1.le
  nlinarith only [hm', ha', hw]

end

end ABBKS26.RefineAux
