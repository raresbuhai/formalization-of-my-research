module

public import BS23.Common.GoodProb

/-!
# From a good set of samples to the success probability

`BS23.successProb` is a lower integral over the sample (the rounding need not be measurable), so a
lower bound on it only needs a measurable set `G` of samples on which the probability over the
coins is at least `p`: then `successProb ≥ p · P(G)` (`BS23.le_successProb`), by monotonicity of
the lower integral applied to `p · 1_G`. With `G` the good event of `BS23.GoodNoise`, whose failure
probability is bounded in `BS23.sampleLaw_not_goodNoise_le`, this gives
`BS23.le_successProb_of_goodNoise`. For deterministic steps, `BS23.coinProb_of_forall` says that
a property of every coin string has coin probability `1`.
-/

@[expose] public section

namespace BS23

open MeasureTheory

variable {k d : ℕ}

/-! ### Coin probabilities -/

theorem coinProb_nonneg (m : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb m P := by
  unfold coinProb
  positivity

theorem coinProb_le_one (m : ℕ) (P : List Bool → Prop) : coinProb m P ≤ 1 := by
  classical
  unfold coinProb
  rw [div_le_one (by positivity)]
  have h := Fintype.card_subtype_le (fun r : Fin m → Bool ↦ P (List.ofFn r))
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- A property of every coin string has coin probability `1`. -/
theorem coinProb_of_forall {m : ℕ} {P : List Bool → Prop} (h : ∀ c, P c) :
    coinProb m (fun c ↦ P c) = 1 := by
  classical
  unfold coinProb
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv fun r ↦ h (List.ofFn r)), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  push_cast
  exact div_self (by positivity)

/-! ### Lower bounds on the success probability -/

/-- **Success from a good set of samples.** If on a measurable set `G` of samples the algorithm
succeeds with probability at least `p` over its coins, then its success probability is at least
`p · P(G)`. -/
theorem le_successProb {α β : Type} {M : Mixture k d} (hM : M.Valid) (hw : ∀ i, 0 ≤ M.w i)
    {n : ℕ} (r : Rounding k d) (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) {G : Set (Fin n → Fin k × EuclideanSpace ℝ (Fin d))}
    (hG : MeasurableSet G) {p : ℝ}
    (hpG : ∀ ω ∈ G, p ≤ coinProb (T (input (roundedSample r ω)))
      (fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c)))) :
    p * (M.sampleLaw n G).toReal ≤ successProb M n r input A T Good := by
  rcases lt_or_ge p 0 with hp | hp
  · exact (mul_nonpos_of_nonpos_of_nonneg hp.le ENNReal.toReal_nonneg).trans
      ENNReal.toReal_nonneg
  have := M.isProbabilityMeasure_sampleLaw hM hw n
  set F : (Fin n → Fin k × EuclideanSpace ℝ (Fin d)) → ENNReal := fun ω ↦
    ENNReal.ofReal (coinProb (T (input (roundedSample r ω)))
      fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c))) with hF
  have hle : G.indicator (fun _ ↦ ENNReal.ofReal p) ≤ F := fun ω ↦ by
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω]
      exact ENNReal.ofReal_le_ofReal (hpG ω hω)
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hlint := lintegral_mono (μ := M.sampleLaw n) hle
  rw [lintegral_indicator_const hG] at hlint
  have hF1 : ∫⁻ ω, F ω ∂(M.sampleLaw n) ≤ 1 :=
    calc ∫⁻ ω, F ω ∂(M.sampleLaw n) ≤ ∫⁻ _, 1 ∂(M.sampleLaw n) :=
          lintegral_mono fun ω ↦ ENNReal.ofReal_le_one.2 (coinProb_le_one _ _)
      _ = 1 := by simp
  calc p * (M.sampleLaw n G).toReal = (ENNReal.ofReal p * M.sampleLaw n G).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp]
    _ ≤ (∫⁻ ω, F ω ∂(M.sampleLaw n)).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hF1) hlint
    _ = successProb M n r input A T Good := rfl

/-- **Success from a likely good set of samples.** As `BS23.le_successProb`, when the complement
of `G` has probability at most `δ`: the success probability is at least `p (1 - δ)`. -/
theorem mul_one_sub_le_successProb {α β : Type} {M : Mixture k d} (hM : M.Valid)
    (hw : ∀ i, 0 ≤ M.w i) {n : ℕ} (r : Rounding k d) (input : Points → α)
    (A : α × List Bool → β) (T : α → ℕ) (Good : (Fin n → Fin k) → β → Prop)
    {G : Set (Fin n → Fin k × EuclideanSpace ℝ (Fin d))} (hG : MeasurableSet G) {p δ : ℝ}
    (hp : 0 ≤ p)
    (hpG : ∀ ω ∈ G, p ≤ coinProb (T (input (roundedSample r ω)))
      (fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c))))
    (hδ : (M.sampleLaw n Gᶜ).toReal ≤ δ) :
    p * (1 - δ) ≤ successProb M n r input A T Good := by
  have := M.isProbabilityMeasure_sampleLaw hM hw n
  have h1 : (M.sampleLaw n G).toReal = 1 - (M.sampleLaw n Gᶜ).toReal := by
    rw [← measureReal_def, ← measureReal_def, probReal_compl_eq_one_sub hG]
    ring
  refine le_trans ?_ (le_successProb hM hw r input A T Good hG hpG)
  rw [h1]
  exact mul_le_mul_of_nonneg_left (by linarith) hp

/-- **Success from the good event.** For a valid mixture with weights at least `wmin > 0`, if on
every sample in the good event `GoodNoise M.w η D` the algorithm succeeds with probability at
least `p ≥ 0` over its coins, then its success probability is at least
`p (1 - k / (n η²) · (1 / wmin + (d + 1)^D (2D)^D))`. -/
theorem le_successProb_of_goodNoise {α β : Type} {M : Mixture k d} (hM : M.Valid) {wmin η : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) (hη : 0 < η) {n : ℕ} (hn : 0 < n) (D : ℕ)
    (r : Rounding k d) (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) {p : ℝ} (hp : 0 ≤ p)
    (hpG : ∀ ω, GoodNoise M.w η D (labels ω) (stdNoise M ω) →
      p ≤ coinProb (T (input (roundedSample r ω)))
        (fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c)))) :
    p * (1 - k / (n * η ^ 2) * (1 / wmin + (d + 1) ^ D * (2 * D) ^ D)) ≤
      successProb M n r input A T Good :=
  mul_one_sub_le_successProb hM (fun i ↦ hwmin.le.trans (hw i)) r input A T Good
    (measurableSet_goodNoise_sample M n η D) hp hpG
    (sampleLaw_not_goodNoise_le hM hwmin hw hη hn D)

end BS23
