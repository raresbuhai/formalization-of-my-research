module

public import ABBKS26.Tree.CompleteAuxNet
public import ABBKS26.Linalg.Separation

/-! Homogeneity and the thin-direction contradiction. -/

@[expose] public section

namespace ABBKS26.Tree.CompleteAux

noncomputable section

open Matrix Common
open scoped BigOperators

variable {d : ℕ}

theorem sqnorm_smul (t : ℝ) (v : Vec d) : sqnorm (t • v) = t ^ 2 * sqnorm v := by
  simp only [sqnorm, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem qform_smul (A : Mat d) (t : ℝ) (v : Vec d) :
    qform A (t • v) = t ^ 2 * qform A v := by
  simp only [qform, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem lower_of_unit (A : Mat d) (c : ℝ)
    (h : ∀ v, sqnorm v = 1 → c ≤ qform A v) (v : Vec d) :
    c * sqnorm v ≤ qform A v := by
  have hn : 0 ≤ sqnorm v := by simpa [sqnorm] using dotProduct_self_star_nonneg v
  by_cases hz : sqnorm v = 0
  · have hv : v = 0 := dotProduct_self_eq_zero.mp hz
    simp [hv, sqnorm, qform]
  have ht : 0 < Real.sqrt (sqnorm v) := Real.sqrt_pos.mpr (lt_of_le_of_ne hn (Ne.symm hz))
  have ht2 := Real.sq_sqrt hn
  have hu : sqnorm ((Real.sqrt (sqnorm v))⁻¹ • v) = 1 := by
    rw [sqnorm_smul, inv_pow, ht2, inv_mul_cancel₀ hz]
  have hh := mul_le_mul_of_nonneg_left (h _ hu) hn
  rw [qform_smul] at hh
  have he : sqnorm v * ((Real.sqrt (sqnorm v))⁻¹ ^ 2 * qform A v) = qform A v := by
    rw [inv_pow, ht2]
    field_simp
  rw [he] at hh
  simpa only [mul_comm] using hh

theorem trace_sq (A : Mat d) (hA : A.IsHermitian) :
    (A * A).trace = frobSq A := by
  have hs : Aᵀ = A := by simpa using hA.eq
  calc (A * A).trace = (Aᵀ * A).trace := by rw [hs]
    _ = frobSq A := by
      simp only [trace, diag, Matrix.mul_apply, transpose_apply, frobSq, pow_two]
      exact Finset.sum_comm

end

end ABBKS26.Tree.CompleteAux
