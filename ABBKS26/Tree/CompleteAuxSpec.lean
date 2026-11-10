module

public import ABBKS26.Tree.CompleteAuxFrob
public import ABBKS26.Tree.CompleteAuxThin
public import ABBKS26.IdCov.Params

/-! A multiplicative variance gap and Gaussian square tails. -/

@[expose] public section

namespace ABBKS26.Tree.CompleteAux

noncomputable section

open Matrix Common MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {k d : ℕ}

theorem multiplicative_gap (I : Finset (Fin k)) (σ : Fin k → ℝ) (Q : ℝ)
    (hQ : 1 < Q) (hσ : ∀ j ∈ I, 0 < σ j) (hk : 2 ≤ k)
    (a b : Fin k) (ha : a ∈ I) (hb : b ∈ I) (hab : Q * σ a < σ b) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧ lo ∈ I.image σ ∧ hi ∈ I.image σ ∧
      Q ^ (1 / ((k : ℝ) - 1)) * lo < hi ∧
      ∀ j ∈ I, σ j ≤ lo ∨ hi ≤ σ j := by
  classical
  let s := I.image (fun j ↦ Real.log (σ j))
  have hsk : (s.card : ℝ) ≤ k := by
    have hcard : s.card ≤ I.card := Finset.card_image_le
    exact_mod_cast hcard.trans (show I.card ≤ k by simpa using Finset.card_le_univ I)
  have hk' : 0 < (k : ℝ) - 1 := by exact_mod_cast (by omega : 0 < (k : ℤ) - 1)
  have hQ0 : 0 < Q := by linarith
  have hlog : 0 < Real.log Q := Real.log_pos hQ
  have hspread : Real.log Q < Real.log (σ b) - Real.log (σ a) := by
    have hh := (Real.log_lt_log_iff (mul_pos hQ0 (hσ a ha)) (hσ b hb)).mpr hab
    rw [Real.log_mul hQ0.ne' (hσ a ha).ne'] at hh
    linarith
  have hbound : ((s.card : ℝ) - 1) * (Real.log Q / ((k : ℝ) - 1)) <
      Real.log (σ b) - Real.log (σ a) := by
    have hh := mul_le_mul_of_nonneg_right (by linarith : (s.card : ℝ) - 1 ≤ k - 1)
      (div_nonneg hlog.le hk'.le)
    have he : ((k : ℝ) - 1) * (Real.log Q / ((k : ℝ) - 1)) = Real.log Q := by
      field_simp
    rw [he] at hh
    exact hh.trans_lt hspread
  obtain ⟨l, hl, u, hu, hgap, hside⟩ := expectation_gap
    (Finset.mem_image.mpr ⟨a, ha, rfl⟩ : Real.log (σ a) ∈ s)
    (Finset.mem_image.mpr ⟨b, hb, rfl⟩ : Real.log (σ b) ∈ s) hbound
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
  refine ⟨σ i, σ j, hσ i hi, hσ j hj,
    Finset.mem_image.mpr ⟨i, hi, rfl⟩, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_, ?_⟩
  · apply (Real.log_lt_log_iff
      (mul_pos (Real.rpow_pos_of_pos hQ0 _) (hσ i hi)) (hσ j hj)).mp
    rw [Real.log_mul (Real.rpow_pos_of_pos hQ0 _).ne' (hσ i hi).ne',
      Real.log_rpow hQ0]
    convert hgap using 1
    ring
  · intro t ht
    rcases hside (Real.log (σ t)) (Finset.mem_image.mpr ⟨t, ht, rfl⟩) with h | h
    · exact Or.inl ((Real.log_le_log_iff (hσ t ht) (hσ i hi)).mp h)
    · exact Or.inr ((Real.log_le_log_iff (hσ j hj) (hσ t ht)).mp h)

theorem square_small (S : Mat d) (hS : S.PosSemidef) (z : Vec d)
    (a R : ℝ) (ha : 0 < a) (hR : 1 ≤ R) (hv : qform S z ≤ (a / R) ^ 2) :
    (multivariateGaussian 0 S).real {y | a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2} ≤ 1 / R := by
  have hR0 : 0 < R := by linarith
  have ht := Population.multivariateGaussian_abs_ge_le_of_le hS z ha
    (by norm_num : (0 : ℝ) < 1) hR0 hv
  simp only [div_one] at ht
  have hsub : {y : EuclideanSpace ℝ (Fin d) | a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2} ⊆
      {y | a ≤ |z ⬝ᵥ y.ofLp|} := by
    intro y hy
    change a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2 at hy
    exact (pow_le_pow_iff_left₀ ha.le (abs_nonneg _) two_ne_zero).mp
      (hy.trans_eq (sq_abs _).symm)
  refine (measureReal_mono hsub).trans (ht.trans ?_)
  exact sq_le (by positivity) ((div_le_one hR0).mpr hR)


end

end ABBKS26.Tree.CompleteAux
