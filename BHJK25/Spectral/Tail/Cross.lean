module

public import BHJK25.Spectral.Tail.Gauss
public import BHJK25.Spectral.Tail.Event

/-!
# The cross terms are small

The probabilistic heart of the proof of [BHJK25, Lemma 3.7] (`BHJK25.Spectral.noisy_spike`). For
the spike column `u` and the cross terms `S = ∑ⱼ |λⱼ| ⟨uⱼ, u⟩² + ∑ⱼ |λ'ⱼ| ⟨u'ⱼ, u⟩²`
(`BHJK25.Spectral.TailAux.crossSum`), conditionally on `u` the `2k + 1` terms are independent, and
each has `E exp(|λ| ⟨v, u⟩² / (4 ‖u‖²)) ≤ 1 + γ / 2`. So

  `E exp(S / (4 ‖u‖²)) ≤ (1 + γ / 2)^(2k + 1) ≤ exp(γ (k + 1))`,

and by Markov's inequality `S / (4 ‖u‖²) ≥ T / 4` with probability at most `exp(γ (k + 1) - T / 4)`.
-/

@[expose] public section

namespace BHJK25.Spectral.TailAux

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

/-- The factor `exp(|λ| ⟨v, u⟩² / (4 ‖u‖²))` of the exponential moment of the cross terms for one
component `(λ, v)`. -/
noncomputable def crossFactor {n : ℕ} (u : Fin n → ℝ) (p : ℝ × (Fin n → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (|p.1| * (p.2 ⬝ᵥ u) ^ 2 / (4 * (u ⬝ᵥ u))))

theorem exp_crossSum {k : ℕ} (ω : Sample k) :
    ENNReal.ofReal (Real.exp (crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1)))) =
      (∏ j, crossFactor ω.1.1 (ω.1.2 j)) * ∏ j, crossFactor ω.1.1 (ω.2 j) := by
  rw [crossSum, add_div, Finset.sum_div, Finset.sum_div, Real.exp_add, Real.exp_sum,
    Real.exp_sum, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le,
    ENNReal.ofReal_prod_of_nonneg fun _ _ ↦ (Real.exp_pos _).le]
  rfl

/-- `E exp(S / (4 ‖u‖²)) ≤ (1 + γ / 2)^(2k + 1)`. -/
theorem lintegral_exp_crossSum_le {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1)))) ∂(sampleLaw γ k) ≤
      ENNReal.ofReal (1 + γ / 2) ^ (2 * k + 1) := by
  have := isProbabilityMeasure_eigLaw h0 h1
  set c := ENNReal.ofReal (1 + γ / 2)
  have hfac : ∀ u : Fin (k + 1) → ℝ, ∫⁻ p, crossFactor u p ∂(compLaw γ (k + 1)) ≤ c :=
    fun u ↦ lintegral_comp_le h0 h1 u
  have hm : ∀ u : Fin (k + 1) → ℝ, Measurable (crossFactor u) := fun u ↦ by
    unfold crossFactor; fun_prop
  simp_rw [exp_crossSum]
  rw [sampleLaw, lintegral_prod _ (by unfold crossFactor; fun_prop)]
  calc _ ≤ ∫⁻ x, (∏ j, crossFactor x.1 (x.2 j)) * c ^ (k + 1)
          ∂((gaussVec (k + 1)).prod (Measure.pi fun _ : Fin k ↦ compLaw γ (k + 1))) := by
        refine lintegral_mono fun x ↦ ?_
        dsimp only
        rw [lintegral_const_mul _ (by unfold crossFactor; fun_prop),
          lintegral_pi_prod _ (hm x.1), Fintype.card_fin]
        gcongr
        exact hfac x.1
    _ = (∫⁻ x, ∏ j, crossFactor x.1 (x.2 j)
          ∂((gaussVec (k + 1)).prod (Measure.pi fun _ : Fin k ↦ compLaw γ (k + 1)))) *
          c ^ (k + 1) :=
        lintegral_mul_const _ (by unfold crossFactor; fun_prop)
    _ ≤ c ^ k * c ^ (k + 1) := by
        gcongr
        rw [lintegral_prod _ (by unfold crossFactor; fun_prop)]
        calc _ ≤ ∫⁻ _, c ^ k ∂(gaussVec (k + 1)) := lintegral_mono fun u ↦ by
              rw [lintegral_pi_prod _ (hm u), Fintype.card_fin]
              gcongr
              exact hfac u
          _ = c ^ k := by rw [lintegral_const, measure_univ, mul_one]
    _ = c ^ (2 * k + 1) := by ring

/-- Markov's inequality for the cross terms: `S / (4 ‖u‖²) ≥ T / 4` with probability at most
`exp(γ (k + 1) - T / 4)`. -/
theorem sampleLaw_crossSum_le {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (k : ℕ) (T : ℝ) :
    sampleLaw γ k {ω | T / 4 ≤ crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1))} ≤
      ENNReal.ofReal (Real.exp (γ * ((k : ℝ) + 1) - T / 4)) := by
  have hM := mul_meas_ge_le_lintegral₀
    (f := fun ω ↦ ENNReal.ofReal (Real.exp (crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1)))))
    (μ := sampleLaw γ k) (by unfold crossSum; fun_prop) (ENNReal.ofReal (Real.exp (T / 4)))
  have hsub : {ω : Sample k | T / 4 ≤ crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1))} ⊆
      {ω | ENNReal.ofReal (Real.exp (T / 4)) ≤
        ENNReal.ofReal (Real.exp (crossSum ω / (4 * (ω.1.1 ⬝ᵥ ω.1.1))))} :=
    fun ω hω ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 hω)
  have hle := (hM.trans (lintegral_exp_crossSum_le h0 h1 k))
  rw [← ENNReal.ofReal_pow (by positivity)] at hle
  refine (measure_mono hsub).trans ((measure_le_of_mul_le (Real.exp_pos _) hle).trans
    (ENNReal.ofReal_le_ofReal ?_))
  rw [Real.exp_sub]
  gcongr
  calc (1 + γ / 2) ^ (2 * k + 1) ≤ Real.exp (γ / 2) ^ (2 * k + 1) := by
        gcongr
        linarith [Real.add_one_le_exp (γ / 2)]
    _ = Real.exp (((2 * k + 1 : ℕ) : ℝ) * (γ / 2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (γ * ((k : ℝ) + 1)) := Real.exp_le_exp.2 (by push_cast; nlinarith)

end BHJK25.Spectral.TailAux
