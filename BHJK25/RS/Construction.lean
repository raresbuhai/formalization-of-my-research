module

public import BHJK25.RS.Defs
public import BHJK25.RS.Construction.Uniform

/-!
# The planted distribution of Theorem 2.1

`BHJK25.RS.planted` is a probability distribution, invariant under relabelling (it is averaged
over all permutations), and agrees with the uniform distribution on every polynomial of degree at
most `m ≥ n^(1 - 1/T)` in the entries: every set of at most `m` entries is uniformly distributed
[BHJK25, Lemma 2.10]. The values `α_v` are uniform, the padding bits are uniform, and, given `α`,
any `m` of the `β_v` are uniform: the `β_v` at unique `α_v` are values of a uniformly random
polynomial with `m` coefficients at distinct points (Vandermonde), the others are independent.

The proofs are in `BHJK25/RS/Construction/`: the bits of field elements (`Field`), flipping one
entry of a set of at most `m` entries by an injective map of the randomness (`Flip`), the counting
argument that turns flips into uniformity (`Count`), the two distributions as finite averages
(`Measure`), and the uniformity of the entries (`Uniform`). They use the shared facts of
`BHJK25/RS/Basic/`: the cells of the hidden layout and the planted bits (`Cells`), relabelling and
the planted distribution on a tensor (`Relabel`), and `m ≥ n^(1 - 1/T)` (`Params`).
-/

@[expose] public section

namespace BHJK25.RS

open MeasureTheory

theorem isProbabilityMeasure_planted (k T n : ℕ) : IsProbabilityMeasure (planted k T n) := by
  by_cases h : 2 * (k - 1) * ell k T n < n
  · constructor
    unfold planted
    rw [dite_eq_left h, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
    simp only [Measure.finsetSum_apply, measure_univ, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact ENNReal.inv_mul_cancel ConsAux.card_sample_mul_ne_zero
      ConsAux.card_sample_mul_ne_top
  · unfold planted
    rw [dite_eq_right h]
    infer_instance

theorem snInvariant_planted (k T n : ℕ) : SnInvariant (planted k T n) := by
  intro τ M
  by_cases h : 2 * (k - 1) * ell k T n < n
  · rw [planted_singleton h, planted_singleton h]
    congr 1
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [← Equiv.sum_comp (Equiv.mulLeft τ)]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    simp only [Equiv.coe_mulLeft, relabel_mul, (relabel_injective τ).eq_iff]
  · unfold planted
    rw [dite_eq_right h, ConsAux.uniformTensor_singleton, ConsAux.uniformTensor_singleton]

/-- **`m`-wise uniformity** [BHJK25, Lemma 2.10]: the planted distribution has degree-`D`
advantage `0` over the uniform distribution for `D ≤ n^(1 - 1/T)`. -/
theorem planted_uniform {k T : ℕ} (hk : 2 ≤ k) (hT : 1 ≤ T) (n : ℕ) {D : ℝ}
    (hD : D ≤ (n : ℝ) ^ (1 - 1 / (T : ℝ))) :
    AdvantageAtMost entryBits D (planted k T n) (uniformTensor k n) 0 := by
  have := isProbabilityMeasure_planted k T n
  intro f hf
  refine ⟨Integrable.of_finite, MemLp.of_discrete, ?_⟩
  rw [zero_mul, sub_nonpos]
  refine le_of_eq ?_
  by_cases h : 2 * (k - 1) * ell k T n < n
  · have hfm : f.totalDegree ≤ mdeg T n := by
      have h1 := hf.trans (hD.trans (rpow_le_mdeg hT n))
      exact_mod_cast h1
    have hP (g : Tensor k n → ℝ) : ∫ M, g M ∂planted k T n =
        ((Fintype.card (Sample k T n) : ℝ) * n.factorial)⁻¹ *
          ∑ p : Sample k T n × Equiv.Perm (Fin n), g (relabel p.2 (encode h p.1)) := by
      rw [ConsAux.integral_planted h]
      congr 1
      exact (Fintype.sum_prod_type fun p : Sample k T n × Equiv.Perm (Fin n) ↦
        g (relabel p.2 (encode h p.1))).symm
    rw [hP, ConsAux.integral_uniformTensor,
      ConsAux.avg_eval _ _ (mdeg T n) (fun A hA ↦ ?_) f hfm]
    · exact (ConsAux.avg_eval (fun M ↦ M) _ (mdeg T n) (fun A _ ↦ ConsAux.uniform_ones A) f
        hfm).symm
    · rw [← ConsAux.planted_ones hk h A hA]
      congr 1
      exact Fintype.sum_prod_type _
  · unfold planted
    rw [dite_eq_right h]

end BHJK25.RS
