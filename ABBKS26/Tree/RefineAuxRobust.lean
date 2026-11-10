module

public import ABBKS26.Tree.RefineAuxReference
public import ABBKS26.Tree.RefineAuxResilienceBudget

/-! Robust frame scale and contamination bounds. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix

variable {n k d : ℕ}


theorem contamination_nonneg (R : Robust.Reference n k d) : 0 ≤ R.contamination := by
  unfold Robust.Reference.contamination
  positivity

theorem sigmaSq_one_le (p : Tree.StepParams) (hw : 0 < p.w) (hw2 : p.w ≤ 1 / 2)
    (hσ : p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2) : (1 : ℚ) ≤ p.sigmaSq := by
  have hπ0 : 0 < p.w / 2 := by positivity
  have hπ1 : p.w / 2 ≤ 1 := by linarith only [hw2]
  have hsq := pow_le_one₀ hπ0.le hπ1 (n := 2)
  have h600 : (600 : ℚ) ≤ 600 / (p.w / 2) ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hπ0)]
    linarith only [hsq]
  rw [hσ]
  nlinarith only [h600, sq_nonneg p.R]

theorem frame_sigmaSq (p : Tree.StepParams)
    (hσ : p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2) :
    Robust.sigmaSq ((p.w / 2 : ℚ) : ℝ) (|p.R| : ℚ) = p.sigmaSq := by
  unfold Robust.sigmaSq
  push_cast
  rw [sq_abs]
  have he := congrArg (fun q : ℚ ↦ (q : ℝ)) hσ
  push_cast at he
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using he.symm


/-- Increasing the error tolerance preserves resilience without changing the reference. -/
theorem resilient_tolerance_mono (R : Robust.Reference n k d) (s : ℕ) (θ φ : ℝ)
    (hres : R.Resilient s θ) (hle : θ ≤ φ) : R.Resilient s φ := by
  intro T a j q hq
  apply (hres T a j q hq).trans
  apply mul_le_mul_of_nonneg_right
  · exact div_le_div_of_nonneg_right hle (by positivity)
  · exact pow_nonneg (add_nonneg
      (add_nonneg zero_le_one (SoS.coeffNorm1_nonneg _)) (SoS.coeffNorm1_nonneg _)) q

end

end ABBKS26.RefineAux
