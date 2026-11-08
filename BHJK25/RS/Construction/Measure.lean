module

public import BHJK25.RS.Defs

/-!
# The planted and uniform distributions as finite averages

The expectations of the planted distribution (`BHJK25.RS.planted`) are averages over the pairs
(sample, permutation) (`BHJK25.RS.ConsAux.integral_planted`); the uniform distribution
(`BHJK25.uniformTensor`) is a probability distribution whose expectations are averages over all
tensors (`BHJK25.RS.ConsAux.integral_uniformTensor`).
-/

@[expose] public section

namespace BHJK25.RS.ConsAux

open MeasureTheory

variable {k T n : ℕ}

theorem card_sample_mul_ne_zero :
    (Fintype.card (Sample k T n) * n.factorial : ENNReal) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (Nat.cast_ne_zero.2 n.factorial_ne_zero)

theorem card_sample_mul_ne_top :
    (Fintype.card (Sample k T n) * n.factorial : ENNReal) ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _)

theorem card_tensor : Fintype.card (Tensor k n) = 2 ^ Fintype.card (KSet k n) := by
  simp [Tensor]

instance isProbabilityMeasure_uniformTensor : IsProbabilityMeasure (uniformTensor k n) := by
  constructor
  rw [uniformTensor, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (Nat.cast_ne_zero.2 Finset.univ_nonempty.card_pos.ne')
    (ENNReal.natCast_ne_top _)

theorem uniformTensor_singleton (M : Tensor k n) :
    uniformTensor k n {M} = ((Finset.univ : Finset (Tensor k n)).card : ENNReal)⁻¹ := by
  rw [uniformTensor, Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ M)]

theorem integral_planted (h : 2 * (k - 1) * ell k T n < n) (g : Tensor k n → ℝ) :
    ∫ M, g M ∂planted k T n = ((Fintype.card (Sample k T n) : ℝ) * n.factorial)⁻¹ *
      ∑ ω : Sample k T n, ∑ σ : Equiv.Perm (Fin n), g (relabel σ (encode h ω)) := by
  unfold planted
  rw [dite_eq_left h, integral_smul_measure, integral_finsetSum_measure fun ω _ ↦
    integrable_finsetSum_measure.2 fun σ _ ↦ Integrable.of_finite]
  have hω (ω : Sample k T n) : ∫ M, g M ∂(∑ σ : Equiv.Perm (Fin n),
      Measure.dirac (relabel σ (encode h ω))) = ∑ σ, g (relabel σ (encode h ω)) := by
    rw [integral_finsetSum_measure fun σ _ ↦ Integrable.of_finite]
    simp_rw [integral_dirac]
  simp_rw [hω]
  rw [smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]

theorem integral_uniformTensor (g : Tensor k n → ℝ) :
    ∫ M, g M ∂uniformTensor k n = ((2 : ℝ) ^ Fintype.card (KSet k n))⁻¹ * ∑ M, g M := by
  rw [integral_fintype Integrable.of_finite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun M _ ↦ ?_
  rw [measureReal_def, uniformTensor_singleton, Finset.card_univ, card_tensor, smul_eq_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  push_cast
  rfl

end BHJK25.RS.ConsAux
