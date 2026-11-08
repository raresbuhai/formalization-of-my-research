module

public import BHJK25.Spectral.LDA.Chain
public import BHJK25.Spectral.LDA.Params
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The low-degree advantage of the spectral distributions

[BHJK25, Lemmas 3.8–3.10]: for every `b` there is an `a` such that, for all large enough `n`, the
planted distribution has degree-`n^(1/3)/log^a n` advantage at most `1/log^b n` over the null
distribution.

The bound for general parameters is `BHJK25.Spectral.LDAAux.advantage_spectral`
(`BHJK25/Spectral/LDA/Chain.lean`): advantage at most `(1/√(1 - γ) + 10 D³ λ*/√γ)/√m`. With
`m = n`, `γ = C log² n/n`, `λ* = γ log n` and `a = b + 1`, this is at most `1/log^b n` for large
`n` (`BHJK25.Spectral.LDAAux.params_eventually`, `BHJK25/Spectral/LDA/Params.lean`).
-/

@[expose] public section

namespace BHJK25.Spectral

open MeasureTheory ProbabilityTheory Filter

/-- A bound on the advantage is also a larger bound. -/
theorem LDAAux.advantageAtMost_mono {Ω ι : Type} [MeasurableSpace Ω] {x : Ω → ι → ℝ} {D : ℝ}
    {P Q : Measure Ω} {δ δ' : ℝ} (h : AdvantageAtMost x D P Q δ) (hδ : δ ≤ δ') :
    AdvantageAtMost x D P Q δ' := fun f hf ↦
  let ⟨h1, h2, h3⟩ := h f hf
  ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg _))⟩

/-- **The low-degree advantage of the spectral distributions** [BHJK25, Lemmas 3.8–3.10]: for
every `b` there is an `a` (namely `b + 1`) such that, for all large enough `n`, the planted
distribution has degree-`n^(1/3)/log^a n` advantage at most `1/log^b n` over the null
distribution. -/
theorem lda {C : ℝ} (hC : 0 < C) (b : ℕ) : ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
    AdvantageAtMost entries ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ a) (plantedAt C n)
      (nullAt C n) (1 / Real.log n ^ b) := by
  refine ⟨b + 1, ?_⟩
  filter_upwards [LDAAux.params_eventually hC b] with n ⟨hn, hγ0, hγ1, ht0, htD, hδ⟩
  exact LDAAux.advantageAtMost_mono (LDAAux.advantage_spectral hγ0 hγ1 hn ht0 htD n) hδ

end BHJK25.Spectral
