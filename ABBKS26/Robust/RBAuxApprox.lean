module

public import ABBKS26.Robust.MomentSDP

/-! Rational approximation for the robust wrapper. -/

@[expose] public section

namespace ABBKS26.Robust.RBAux

noncomputable section

open Common Matrix MvPolynomial
open scoped BigOperators MatrixOrder Topology

variable {d : ℕ}


theorem sqrt_properties (S : Mat d) (hS : S.PosDef) :
    (CFC.sqrt S)ᵀ = CFC.sqrt S ∧ (CFC.sqrt S).det ≠ 0 ∧
      CFC.sqrt S * CFC.sqrt S = S := by
  have hsq : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  refine ⟨?_, ?_, hsq⟩
  · simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg S).posSemidef.isHermitian
  · intro hz
    have hh := congrArg Matrix.det hsq
    rw [Matrix.det_mul, hz, zero_mul] at hh
    exact hS.det_pos.ne' hh.symm

theorem qform_conjugate (T A : Mat d) (v : Vec d) :
    qform (T * A * Tᵀ) v = qform A (Tᵀ *ᵥ v) := by
  simp only [qform, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

theorem relative_bounds (S A : Mat d) (hS : S.PosDef) (hA : Aᵀ = A)
    (herr : frobSq ((CFC.sqrt S)⁻¹ * A * (CFC.sqrt S)⁻¹ - 1) ≤ 1 / 100) :
    A.PosDef ∧ LE ((0.9 : ℝ) • S) A ∧ LE A ((1.1 : ℝ) • S) := by
  let B := CFC.sqrt S
  let E := B⁻¹ * A * B⁻¹ - 1
  obtain ⟨hBt, hdet, hBB⟩ := sqrt_properties S hS
  change Bᵀ = B at hBt
  change B * B = S at hBB
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hdet
  have hconj : B * E * Bᵀ = A - S := by
    change B * (B⁻¹ * A * B⁻¹ - 1) * Bᵀ = A - S
    rw [hBt, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    have hp : B * (B⁻¹ * A * B⁻¹) * B = A := by
      calc
        _ = (B * B⁻¹) * A * (B⁻¹ * B) := by simp only [Matrix.mul_assoc]
        _ = A := by rw [Matrix.mul_nonsing_inv _ hB, Matrix.nonsing_inv_mul _ hB,
          one_mul, Matrix.mul_one]
    rw [hp, hBB]
  have hnorm (v : Vec d) : sqnorm (Bᵀ *ᵥ v) = qform S v := by
    simpa only [qform, sqnorm, one_mulVec, Matrix.mul_one, hBt, hBB] using
      (qform_conjugate B 1 v).symm
  have he (v : Vec d) : |qform A v - qform S v| ≤ (1 / 10) * qform S v := by
    have hh := Rounding.DetRoundAux.abs_qform_le E (1 / 10) (by norm_num)
      (by convert herr using 1; norm_num) (Bᵀ *ᵥ v)
    rw [hnorm, ← qform_conjugate, hconj] at hh
    simpa only [qform, sub_mulVec, dotProduct_sub] using hh
  have hl : LE ((0.9 : ℝ) • S) A := by
    intro v
    have hh := (abs_le.mp (he v)).1
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
    change (0.9 : ℝ) * qform S v ≤ qform A v
    linarith only [hh]
  have hu : LE A ((1.1 : ℝ) • S) := by
    intro v
    have hh := (abs_le.mp (he v)).2
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
    change qform A v ≤ (1.1 : ℝ) * qform S v
    linarith only [hh]
  refine ⟨PosDef.of_dotProduct_mulVec_pos ?_ ?_, hl, hu⟩
  · simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA
  · intro v hv
    have hpos : 0 < qform S v := by
      simpa only [qform, star_trivial] using hS.dotProduct_mulVec_pos hv
    have hh := hl v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
    change (0.9 : ℝ) * qform S v ≤ qform A v at hh
    simpa only [qform, star_trivial] using (show 0 < qform A v by linarith only [hh, hpos])


end

end ABBKS26.Robust.RBAux
