module

public import BHJK25.Spectral.Tail.Asymp
public import BHJK25.Spectral.Tail.Cross
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The noisy planted matrix has a large eigenvalue

[BHJK25, Lemma 3.7]: for `ε ∈ [0, 1)`, the noisy matrix `(1 - ε) M₁ + ε M₀` has, with probability
`1 - n^(-e)` for every `e` and all large enough `n`, a vector `v` with `vᵀ M v > 3 ‖v‖²`: the spike
vector `u` of `M₁` itself, since `uᵀ M u ≥ (1 - ε) λ* ‖u‖⁴ - ∑ⱼ |λⱼ| ⟨uⱼ, u⟩²`, `‖u‖² ≥ n/2`, and,
conditionally on `u`, `⟨uⱼ, u⟩ / ‖u‖` are independent standard Gaussians.

The proof is split into:

* `BHJK25/Spectral/Tail/Law.lean`: the noisy matrix as a function of independent components (the
  spike column, the other columns of `M₁` with their eigenvalues, and those of `M₀`);
* `BHJK25/Spectral/Tail/Event.lean`: the deterministic bound on `uᵀ M u`;
* `BHJK25/Spectral/Tail/Gauss.lean`: exponential moments of Gaussians, and
  `P(‖u‖² < n / 2) ≤ (e^(1/4) / √2)^n`;
* `BHJK25/Spectral/Tail/Cross.lean`: `P(S ≥ ‖u‖² T) ≤ exp(γ n - T / 4)` for the cross terms `S`;
* `BHJK25/Spectral/Tail/Asymp.lean`: the inequalities in `n`.
-/

@[expose] public section

namespace BHJK25.Spectral

open MeasureTheory ProbabilityTheory Matrix Filter

namespace TailAux

/-- [BHJK25, Lemma 3.7] for `n = k + 1`, given the inequalities in `n`: the spike column `u` has
`uᵀ M u > 3 ‖u‖²` unless `‖u‖² < n / 2` (probability at most `(e^(1/4) / √2)^n`) or the cross terms
are at least `‖u‖² T` (probability at most `exp(γ n - T / 4)`), with `T = (1 - ε) λ* n / 4`. -/
theorem prob_good {k : ℕ} {γ ε spike δ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (hspike : 0 ≤ spike)
    (hnorm : (Real.exp (1 / 4) / √2) ^ (k + 1) ≤ δ / 2)
    (hcross : Real.exp (γ * ((k : ℝ) + 1) - (1 - ε) * spike * ((k : ℝ) + 1) / 4 / 4) ≤ δ / 2)
    (hbig : 3 < (1 - ε) * spike * ((k : ℝ) + 1) / 4) :
    ProbAtLeast (noisyLaw ε (plantedLaw γ (k + 1) spike (k + 1)) (nullLaw γ (k + 1) (k + 1)))
      (1 - δ) fun M ↦ Mᵀ = M ∧ ∃ v, 3 * (v ⬝ᵥ v) < v ⬝ᵥ (M *ᵥ v) := by
  have := isProbabilityMeasure_eigLaw h0 h1
  refine ⟨goodSet (k + 1), measurableSet_goodSet _, ?_, fun M hM ↦ hM⟩
  rw [noisyLaw_eq, Measure.map_apply (measurable_noisyMat ε spike) (measurableSet_goodSet _)]
  set μ := sampleLaw γ k
  set G := noisyMat ε spike ⁻¹' goodSet (k + 1)
  set T := (1 - ε) * spike * ((k : ℝ) + 1) / 4
  set B₁ := {ω : Sample k | ω.1.1 ⬝ᵥ ω.1.1 < ((k + 1 : ℕ) : ℝ) / 2}
  set B₂ := {ω : Sample k | T / 4 ≤ crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1))}
  have hsub : Gᶜ ⊆ B₁ ∪ B₂ := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, not_or, B₁, B₂, Set.mem_ofPred_eq, not_lt, not_le] at hcon
    apply hω
    have hs : ((k : ℝ) + 1) / 2 ≤ ω.1.1 ⬝ᵥ ω.1.1 := by exact_mod_cast hcon.1
    have hs0 : 0 < ω.1.1 ⬝ᵥ ω.1.1 := lt_of_lt_of_le (by positivity) hs
    have hS : crossSum ω < (ω.1.1 ⬝ᵥ ω.1.1) * T := by
      have := hcon.2
      rw [div_lt_iff₀ (by positivity)] at this
      linarith
    exact good_of hε0 hε1 hspike ω hs hS hbig
  have hB₁ : μ B₁ ≤ ENNReal.ofReal ((Real.exp (1 / 4) / √2) ^ (k + 1)) := by
    have : B₁ = ({u | u ⬝ᵥ u < ((k + 1 : ℕ) : ℝ) / 2} ×ˢ Set.univ) ×ˢ Set.univ := by
      ext ω
      simp [B₁]
    rw [this, show μ = sampleLaw γ k from rfl, sampleLaw, Measure.prod_prod, Measure.prod_prod,
      measure_univ, measure_univ, mul_one, mul_one]
    exact gaussVec_norm_lt (k + 1)
  have hδ : 0 ≤ δ / 2 := le_trans (by positivity) hnorm
  have hbad : μ Gᶜ ≤ ENNReal.ofReal δ :=
    calc μ Gᶜ ≤ μ (B₁ ∪ B₂) := measure_mono hsub
      _ ≤ μ B₁ + μ B₂ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) :=
        add_le_add (hB₁.trans (ENNReal.ofReal_le_ofReal hnorm))
          ((sampleLaw_crossSum_le h0 h1 k T).trans (ENNReal.ofReal_le_ofReal hcross))
      _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add hδ hδ, add_halves]
  have hGm : MeasurableSet G := measurable_noisyMat ε spike (measurableSet_goodSet _)
  have hG : μ G = 1 - μ Gᶜ := by rw [← prob_compl_eq_one_sub hGm.compl, compl_compl]
  rw [hG, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
  linarith [ENNReal.toReal_le_of_le_ofReal (by linarith) hbad]

end TailAux

open TailAux in
/-- [BHJK25, Lemma 3.7]: for `0 ≤ ε < 1`, the noisy matrix `(1 - ε) M₁ + ε M₀` is symmetric and
has a vector `v` with `vᵀ M v > 3 ‖v‖²` with probability at least `1 - n^(-e)`, for all large
`n`. -/
theorem noisy_spike {C : ℝ} (hC : 0 < C) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, ProbAtLeast (noisyLaw ε (plantedAt C n) (nullAt C n))
      (1 - 1 / (n : ℝ) ^ e) fun M ↦ Mᵀ = M ∧ ∃ v, 3 * (v ⬝ᵥ v) < v ⬝ᵥ (M *ᵥ v) := by
  filter_upwards [eventually_sparsity_eq hC, eventually_norm_bound e,
    eventually_cross_bound hC hε1 e, eventually_ge_atTop 1] with n hγ hnorm hcross hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set L := Real.log ((k + 1 : ℕ) : ℝ)
  have hk : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hγn : sparsity C (k + 1) * ((k : ℝ) + 1) = C * L ^ 2 := by
    rw [hγ, hk]
    field_simp
  have hspike : (1 - ε) * (sparsity C (k + 1) * L) * ((k : ℝ) + 1) = (1 - ε) * C * L ^ 3 := by
    calc (1 - ε) * (sparsity C (k + 1) * L) * ((k : ℝ) + 1)
        = (1 - ε) * L * (sparsity C (k + 1) * ((k : ℝ) + 1)) := by ring
      _ = (1 - ε) * C * L ^ 3 := by rw [hγn]; ring
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 k)
  refine prob_good (sparsity_nonneg hC.le _) (sparsity_le_one _ _) hε0 hε1
    (mul_nonneg (sparsity_nonneg hC.le _) hL) hnorm ?_ ?_
  · rw [hγn, hspike]
    convert hcross.1 using 3
    ring
  · rw [hspike]
    exact hcross.2

end BHJK25.Spectral
