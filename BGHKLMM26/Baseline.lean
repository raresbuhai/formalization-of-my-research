module

public import BGHKLMM26.GW
public import Background.Gaussian

/-!
# The Goemans–Williamson baseline

[BGHKLMM26, Lemma 3.3 and the GW analysis]: hyperplane rounding `xᵢ = [0 ≤ ⟨vᵢ, g⟩]` satisfies a
constraint `xᵢ xⱼ = b` (in `±1` terms) with probability `1/2 + arcsin ρ / π`, where
`ρ = b ⟨vᵢ, vⱼ⟩`. Its ratio to the constraint's SDP contribution `(1 + ρ) / 2` is
`gwRatio (-ρ)`, so it is at least `α_GW`, and at least `α_GW + κ` outside the window
`ρ ∈ (1/2, 4/5)`.
-/

@[expose] public section

namespace BGHKLMM26.GW

open Real Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- `±1` for a right-hand side: `1` for `b = true`, `-1` for `b = false`. -/
def bsign (b : Bool) : ℝ := if b then 1 else -1

/-- The probability of satisfying a constraint, in terms of `θ = arccos (-ρ)`. -/
theorem half_add_arcsin_div_pi (ρ : ℝ) : 1 / 2 + arcsin ρ / π = arccos (-ρ) / π := by
  rw [arccos_neg, arccos_eq_pi_div_two_sub_arcsin]
  have := pi_pos
  field_simp
  ring

/-- **The GW ratio, per constraint**: for `ρ ∈ [-1, 1]`, `1/2 + arcsin ρ / π ≥ α_GW (1 + ρ) / 2`. -/
theorem alphaGW_mul_le {ρ : ℝ} (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) :
    alphaGW * ((1 + ρ) / 2) ≤ 1 / 2 + arcsin ρ / π := by
  rw [half_add_arcsin_div_pi]
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · simp [arccos_one]
  · have hσ : -ρ ∈ Ico (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := isGWMinimizer_rhoStar.2 (-ρ) hσ
    rw [← alphaGW_eq, gwRatio, le_div_iff₀ (by linarith)] at h
    rw [sub_neg_eq_add] at h
    linarith

/-- **The gap outside the window** [BGHKLMM26, Lemma 3.3]: for one `κ > 0`, every `ρ ∈ [-1, 1]`
with `ρ ≤ 1/2` or `4/5 ≤ ρ` has `1/2 + arcsin ρ / π ≥ (α_GW + κ) (1 + ρ) / 2`. -/
theorem exists_gap_mul : ∃ κ : ℝ, 0 < κ ∧ ∀ ρ : ℝ, -1 ≤ ρ → ρ ≤ 1 → ρ ≤ 1 / 2 ∨ 4 / 5 ≤ ρ →
    (alphaGW + κ) * ((1 + ρ) / 2) ≤ 1 / 2 + arcsin ρ / π := by
  obtain ⟨κ, hκ, hgap⟩ := exists_gap
  refine ⟨κ, hκ, fun ρ h1 h2 hout ↦ ?_⟩
  rw [half_add_arcsin_div_pi]
  rcases eq_or_lt_of_le h1 with rfl | h1'
  · simp [arccos_one]
  · have hσ : -ρ ∈ Ico (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have h := hgap (-ρ) hσ (by rcases hout with h | h <;> [right; left] <;> linarith)
    rw [gwRatio, le_div_iff₀ (by linarith), sub_neg_eq_add] at h
    linarith

/-- **Hyperplane rounding**: for unit vectors `u, v`, the rounding `[0 ≤ ⟨u, g⟩]`,
`[0 ≤ ⟨v, g⟩]` satisfies a constraint with right-hand side `b` (agreement for `b = true`,
disagreement for `b = false`) with probability `1/2 + arcsin (b ⟨u, v⟩) / π`. -/
theorem prob_satisfied {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (b : Bool) {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).real {g | (decide (0 ≤ ⟪u, g⟫) = decide (0 ≤ ⟪v, g⟫)) = b} =
      1 / 2 + arcsin (bsign b * ⟪u, v⟫) / π := by
  have hagree := Gaussian.prob_sign_agree hu hv
  have hS : MeasurableSet {g : E | (0 ≤ ⟪u, g⟫ ↔ 0 ≤ ⟪v, g⟫)} :=
    measurableSet_setOfPred.2 (by fun_prop)
  cases b
  · -- Disagreement: the complement.
    have : {g : E | (decide (0 ≤ ⟪u, g⟫) = decide (0 ≤ ⟪v, g⟫)) = false} =
        {g | (0 ≤ ⟪u, g⟫ ↔ 0 ≤ ⟪v, g⟫)}ᶜ := by
      ext g
      simp
    rw [this, probReal_compl_eq_one_sub hS, hagree]
    simp only [bsign, Bool.false_eq_true, ite_false, neg_one_mul, arcsin_neg]
    ring
  · have : {g : E | (decide (0 ≤ ⟪u, g⟫) = decide (0 ≤ ⟪v, g⟫)) = true} =
        {g | (0 ≤ ⟪u, g⟫ ↔ 0 ≤ ⟪v, g⟫)} := by
      ext g
      simp
    rw [this, hagree]
    simp [bsign]

end BGHKLMM26.GW
