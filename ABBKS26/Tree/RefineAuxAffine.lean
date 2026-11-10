module

public import ABBKS26.Tree.RefineAuxRobust

/-! Affine changes of coordinates for the rounded node reference. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix
open scoped BigOperators

variable {n k d : ℕ}

/-- Change the coordinates of both the population model and the finite reference. -/
def affineReference (R : Robust.Reference n k d) (T : Mat d) (a : Vec d) :
    Robust.Reference n k d where
  model :=
    { weight := R.model.weight
      mean := fun j ↦ T *ᵥ (R.model.mean j - a)
      cov := fun j ↦ T * R.model.cov j * Tᵀ }
  label := R.label
  reference := R.reference
  good := R.good
  block := R.block
  clean := fun l ↦ T *ᵥ (R.clean l - a)
  observed := fun l ↦ T *ᵥ (R.observed l - a)


private theorem reference_component_pos (R : Robust.Reference n k d) (w : ℝ)
    (hR : R.Valid w) (j : Fin k) :
    0 < (R.reference.filter (fun l ↦ R.label l = j)).card := by
  have hw : 0 < R.model.weight j := hR.1.1.trans_le (hR.1.2.1 j)
  rw [hR.2.2.2.2.2.2 j] at hw
  by_contra hn
  have he : (R.reference.filter (fun l ↦ R.label l = j)).card = 0 := by omega
  simp [he] at hw

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
    rw [hR.2.2.2.2.2.2 j, div_eq_mul_inv]
    have hc : ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (reference_component_pos R w hR j).ne'
    field_simp
  simp only [he, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

private theorem component_second_le (R : Robust.Reference n k d) (w : ℝ)
    (hR : R.Valid w) (u : Vec d) (j : Fin k) :
    R.model.weight j *
      (((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j),
          (u ⬝ᵥ (R.clean l - R.mean)) ^ 2) ≤ qform R.cov u := by
  have he : qform R.cov u = (R.reference.card : ℝ)⁻¹ *
      ∑ l ∈ R.reference, (u ⬝ᵥ (R.clean l - R.mean)) ^ 2 := by
    simp only [Robust.Reference.cov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
      dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul, pow_two,
      dotProduct_comm]
  rw [he, ← reference_partition R w hR, ← mul_assoc]
  apply Finset.single_le_sum _ (Finset.mem_univ j)
  intro i _
  exact mul_nonneg (mul_nonneg (hR.1.1.le.trans (hR.1.2.1 i)) (by positivity))
    (Finset.sum_nonneg fun l _ ↦ sq_nonneg _)

/-- The component's population second moment is bounded by the actual reference covariance. -/
theorem population_component_second_le (R : Robust.Reference n k d) (w θ : ℝ)
    (hR : R.Valid w) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100)
    (hres : R.Resilient 4 θ) (u : Vec d) (j : Fin k) :
    R.model.weight j * ((u ⬝ᵥ (R.model.mean j - R.mean)) ^ 2 +
      qform (R.model.cov j) u) ≤ (1 + θ) * qform R.cov u := by
  by_cases hu : u = 0
  · subst u
    simp [qform]
  obtain ⟨i, _⟩ := Function.ne_iff.mp hu
  let δ := θ / (d + 1 : ℝ) ^ 8
  let m := (u ⬝ᵥ (R.model.mean j - R.mean)) ^ 2 + qform (R.model.cov j) u
  have hd : (2 : ℝ) ≤ d + 1 := by
    exact_mod_cast (show 2 ≤ d + 1 by have hi := i.isLt; omega)
  have hpow : (256 : ℝ) ≤ (d + 1 : ℝ) ^ 8 := by
    simpa only [show (2 : ℝ) ^ 8 = 256 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hd 8
  have hδ0 : 0 ≤ δ := div_nonneg hθ.1 (by positivity)
  have hδ : δ ≤ θ / 256 := div_le_div_of_nonneg_left hθ.1 (by norm_num) hpow
  have hw : 0 ≤ R.model.weight j := hR.1.1.le.trans (hR.1.2.1 j)
  have hm : 0 ≤ m := add_nonneg (sq_nonneg _) (by
    simpa only [qform, star_trivial] using
      (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u)
  have hprod : 1 ≤ (1 + θ) * (1 - 9 * δ) := by
    nlinarith only [hδ0, hδ, hθ.1,
      mul_nonneg (sub_nonneg.mpr hθ.2) hδ0]
  have he := (component_moments R θ hR.1.2.2.2 hθ.1 hres i u R.mean hu j).1
  have he' : (1 - 9 * δ) * (R.model.weight j * m) ≤ qform R.cov u := by
    have hh := mul_le_mul_of_nonneg_left he hw
    have hb := component_second_le R w hR u j
    dsimp only [δ, m]
    nlinarith only [hh, hb]
  calc
    _ ≤ (1 + θ) * (1 - 9 * δ) * (R.model.weight j * m) :=
      le_mul_of_one_le_left (mul_nonneg hw hm) hprod
    _ = (1 + θ) * ((1 - 9 * δ) * (R.model.weight j * m)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he' (by linarith only [hθ.1])

/-- A nearly normalized empirical frame bounds every transformed population covariance. -/
theorem population_component_cov_bound (R : Robust.Reference n k d) (T : Mat d) (w θ : ℝ)
    (hR : R.Valid w) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : R.Resilient 4 θ)
    (hcov : LE (T * R.cov * Tᵀ) ((1.01 : ℝ) • (1 : Mat d))) (j : Fin k) :
    LE (T * R.model.cov j * Tᵀ) ((1.1 / w) • (1 : Mat d)) := by
  intro v
  have hp := population_component_second_le R w θ hR
    ⟨hθ.1, hθ.2.trans (by norm_num)⟩ hres (Tᵀ *ᵥ v) j
  have hq : 0 ≤ qform (R.model.cov j) (Tᵀ *ᵥ v) := by
    simpa only [qform, star_trivial] using
      (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg (Tᵀ *ᵥ v)
  have hn := Rounding.DetRoundAux.sqnorm_nonneg v
  have hw := mul_le_mul_of_nonneg_right (hR.1.2.1 j) hq
  have hc := hcov v
  change qform (T * R.cov * Tᵀ) v ≤ qform ((1.01 : ℝ) • (1 : Mat d)) v at hc
  rw [Robust.RBAux.qform_conjugate] at hc
  have he (c : ℝ) : qform (c • (1 : Mat d)) v = c * sqnorm v := by
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm]
  rw [he] at hc
  have hbound : w * qform (R.model.cov j) (Tᵀ *ᵥ v) ≤ 1.1 * sqnorm v := by
    have hsq := mul_nonneg (hR.1.1.le.trans (hR.1.2.1 j))
      (sq_nonneg ((Tᵀ *ᵥ v) ⬝ᵥ (R.model.mean j - R.mean)))
    have hθn := mul_le_mul_of_nonneg_right hθ.2 hn
    nlinarith only [hp, hw, hc, hsq, hθ.1, hn, hθn]
  change qform (T * R.model.cov j * Tᵀ) v ≤ qform ((1.1 / w) • (1 : Mat d)) v
  rw [Robust.RBAux.qform_conjugate, he, div_mul_eq_mul_div]
  exact (le_div_iff₀ hR.1.1).mpr (by simpa only [mul_comm] using hbound)

/-- A small Frobenius normalization error certifies the frame's invertibility. -/
theorem empirical_frame_bounds (S T : Mat d) (hS : S.PosSemidef)
    (he : frobSq (T * S * Tᵀ - 1) ≤ (1 / 100 : ℝ) ^ 2) :
    T.det ≠ 0 ∧ LE (T * S * Tᵀ) ((1.01 : ℝ) • (1 : Mat d)) := by
  have hbound (v : Vec d) :=
    Rounding.DetRoundAux.abs_qform_le (T * S * Tᵀ - 1) (1 / 100) (by norm_num) he v
  have hq (v : Vec d) : qform (T * S * Tᵀ - 1) v =
      qform (T * S * Tᵀ) v - sqnorm v := by
    simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub, sqnorm]
  have hpsd : (T * S * Tᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hS.mul_mul_conjTranspose_same T
  have hpd : (T * S * Tᵀ).PosDef := by
    apply PosDef.of_dotProduct_mulVec_pos hpsd.1
    intro v hv
    have hn : 0 < sqnorm v := by
      apply lt_of_le_of_ne (Rounding.DetRoundAux.sqnorm_nonneg v)
      exact Ne.symm (fun h ↦ hv (dotProduct_self_eq_zero.mp h))
    have hh := (abs_le.mp (hbound v)).1
    rw [hq] at hh
    change 0 < qform (T * S * Tᵀ) v
    linarith only [hh, hn]
  constructor
  · intro hz
    have hdet := hpd.det_pos
    rw [det_mul, det_mul, hz, zero_mul, zero_mul] at hdet
    exact (lt_irrefl 0) hdet
  · intro v
    have hh := (abs_le.mp (hbound v)).2
    rw [hq] at hh
    change qform (T * S * Tᵀ) v ≤ qform ((1.01 : ℝ) • (1 : Mat d)) v
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    change qform (T * S * Tᵀ) v ≤ 1.01 * sqnorm v
    linarith only [hh]

theorem affineReference_mean (R : Robust.Reference n k d) (T : Mat d) (a : Vec d)
    (hne : R.reference.Nonempty) :
    (affineReference R T a).mean = T *ᵥ (R.mean - a) := by
  have hn : (R.reference.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hne).ne'
  change (R.reference.card : ℝ)⁻¹ •
    ∑ l ∈ R.reference, T *ᵥ (R.clean l - a) = _
  simp only [mulVec_sub, Finset.sum_sub_distrib, ← mulVec_sum, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul ℝ, ← mulVec_smul, smul_sub, smul_smul]
  rw [inv_mul_cancel₀ hn, one_smul]
  rfl

theorem affineReference_cov (R : Robust.Reference n k d) (T : Mat d) (a : Vec d)
    (hne : R.reference.Nonempty) :
    (affineReference R T a).cov = T * R.cov * Tᵀ := by
  have he (l : Fin n) :
      T *ᵥ (R.clean l - a) - T *ᵥ (R.mean - a) = T *ᵥ (R.clean l - R.mean) := by
    rw [← mulVec_sub]
    congr 1
    abel
  unfold Robust.Reference.cov
  rw [affineReference_mean R T a hne]
  change (R.reference.card : ℝ)⁻¹ •
    ∑ l ∈ R.reference,
      vecMulVec (T *ᵥ (R.clean l - a) - T *ᵥ (R.mean - a))
        (T *ᵥ (R.clean l - a) - T *ᵥ (R.mean - a)) = _
  simp only [he]
  simpa only [one_smul] using (Robust.FilterAux.covariance_conjugate R.reference
    (fun _ ↦ 1) (fun l ↦ R.clean l - R.mean) R.reference.card T).symm

private theorem transpose_mulVec_ne_zero (T : Mat d) (hT : T.det ≠ 0)
    (v : Vec d) (hv : v ≠ 0) : Tᵀ *ᵥ v ≠ 0 := by
  intro hz
  apply hv
  have h := congrArg (fun u ↦ Tᵀ⁻¹ *ᵥ u) hz
  rw [mulVec_mulVec, nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (by simpa only [det_transpose] using hT)), one_mulVec,
    mulVec_zero] at h
  exact h

private theorem posDef_conjugate (S T : Mat d) (hS : S.PosDef) (hT : T.det ≠ 0) :
    (T * S * Tᵀ).PosDef := by
  have hpsd : (T * S * Tᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hS.posSemidef.mul_mul_conjTranspose_same T
  apply PosDef.of_dotProduct_mulVec_pos hpsd.1
  intro v hv
  change 0 < qform (T * S * Tᵀ) v
  rw [Robust.RBAux.qform_conjugate]
  simpa only [star_trivial, qform] using
    hS.dotProduct_mulVec_pos (transpose_mulVec_ne_zero T hT v hv)

theorem affineReference_valid (R : Robust.Reference n k d) (T : Mat d) (a : Vec d)
    (w : ℝ) (hR : R.Valid w) (hT : T.det ≠ 0) :
    (affineReference R T a).Valid w := by
  refine ⟨⟨hR.1.1, hR.1.2.1, hR.1.2.2.1, ?_⟩, hR.2.1, hR.2.2.1,
    ?_, hR.2.2.2.2.1, ?_, hR.2.2.2.2.2.2⟩
  · intro j
    exact posDef_conjugate _ _ (hR.1.2.2.2 j) hT
  · intro l hl
    change T *ᵥ (R.observed l - a) = T *ᵥ (R.clean l - a)
    rw [hR.2.2.2.1 l hl]
  · rw [affineReference_cov R T a hR.2.2.2.2.1]
    exact posDef_conjugate _ _ hR.2.2.2.2.2.1 hT

/-- Resilience is preserved without any loss in degree or tolerance. -/
theorem affineReference_resilient (R : Robust.Reference n k d) (T : Mat d) (a : Vec d)
    (s : ℕ) (θ : ℝ) (hT : T.det ≠ 0) (hR : R.Resilient s θ) :
    (affineReference R T a).Resilient s θ := by
  have hTi : T * T⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hT)
  intro U b j q hq
  have he (v : Vec d) :
      U *ᵥ (T *ᵥ (v - a) - b) = (U * T) *ᵥ (v - (a + T⁻¹ *ᵥ b)) := by
    have hh : T *ᵥ ((v - a) - T⁻¹ *ᵥ b) = T *ᵥ (v - a) - b := by
      rw [mulVec_sub, mulVec_mulVec, hTi, one_mulVec]
    rw [← hh, mulVec_mulVec]
    exact congrArg ((U * T) *ᵥ ·) (by abel)
  have hc : U * (T * R.model.cov j * Tᵀ) * Uᵀ =
      (U * T) * R.model.cov j * (U * T)ᵀ := by
    simp only [transpose_mul, mul_assoc]
  dsimp only [affineReference]
  simp only [he, hc]
  exact hR (U * T) (a + T⁻¹ *ᵥ b) j q hq

/-- The rational input to the moment procedure in the selected affine coordinates. -/
def affinePoints (x : Fin n → Fin d → ℚ) (T : Matrix (Fin d) (Fin d) ℚ)
    (a : Fin d → ℚ) : Fin n → Fin d → ℚ := fun l ↦ T *ᵥ (x l - a)

theorem affineReference_observed (R : Robust.Reference n k d)
    (x : Fin n → Fin d → ℚ) (T : Matrix (Fin d) (Fin d) ℚ) (a : Fin d → ℚ)
    (hx : ∀ l i, R.observed l i = (x l i : ℝ)) :
    ∀ l i, (affineReference R (T.map (algebraMap ℚ ℝ))
      (fun j ↦ (a j : ℝ))).observed l i = (affinePoints x T a l i : ℝ) := by
  intro l i
  simp only [affineReference, affinePoints, mulVec, dotProduct, Pi.sub_apply,
    Matrix.map_apply, hx, Rat.cast_sum, Rat.cast_mul, Rat.cast_sub]
  rfl


/-- The centered schedule pays for the weight floor used by the robust moment call. -/
theorem centered_moment_budget (p : Tree.StepParams) (η : ℝ)
    (hw : 0 < p.w) (hη : 0 ≤ η ∧ η ≤ 1 / 100)
    (hηc : 8 * η ≤ p.contamination)
    (hc : p.contamination ≤ p.momentError / (10000 * (2 * (80 / p.w) ^ 4))) :
    250 * (p.contamination : ℝ) * Robust.momentBudget (((p.w / 2 : ℚ) : ℝ)) 4 +
      3 * (η / 10 ^ 8) ^ 2 * Robust.momentBudget (((p.w / 2 : ℚ) : ℝ)) 4 ≤
        p.momentError := by
  let B : ℝ := 2 * (80 / (p.w : ℝ)) ^ 4
  have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw
  have hB : 0 < B := by dsimp only [B]; positivity
  have hb : Robust.momentBudget (((p.w / 2 : ℚ) : ℝ)) 4 = 16 * B := by
    unfold Robust.momentBudget B
    push_cast
    field_simp
    ring
  have hc' : (p.contamination : ℝ) ≤ (p.momentError : ℝ) / (10000 * B) := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr hc
    push_cast at hh
    exact hh
  have hbudget := (le_div_iff₀ (by positivity : 0 < 10000 * B)).mp hc'
  have hc0 : (0 : ℝ) ≤ p.contamination :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hη.1).trans hηc
  have hηsq : η ^ 2 ≤ η := by nlinarith only [hη.1, hη.2]
  have hθ : 3 * (η / 10 ^ 8) ^ 2 ≤ (p.contamination : ℝ) := by
    nlinarith only [hηsq, hη.1, hηc]
  rw [hb]
  have hθB := mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ 16 * B)
  have hcB := mul_nonneg hc0 hB.le
  nlinarith only [hbudget, hθB, hcB]

end

end ABBKS26.RefineAux
