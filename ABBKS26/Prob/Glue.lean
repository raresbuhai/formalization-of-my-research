module

public import ABBKS26.Prob.Basic

/-!
# From a good set of samples to the success probability

`ABBKS26.successProb` is a lower integral over the sample (the rounding need not be measurable),
so a lower bound on it only needs a measurable set `G` of samples on which the probability over
the coins is at least `p`: then `successProb ≥ p · P(G)`, by monotonicity of the lower integral
applied to `p · 1_G`. The set `G` should only be about the labels, the clean points and the
corruption pattern `{j | zⱼ ≠ yⱼ}` (then it is measurable), and the bound on the coin probability
must hold for the given rounding `r` (for instance for every rounding with `IsRounding`).

* `ABBKS26.coinProb_nonneg`, `ABBKS26.coinProb_le_one`, `ABBKS26.coinProb_of_forall`: coin
  probabilities lie in `[0, 1]`, and a property of every coin string has probability `1`.
* `ABBKS26.le_successProb`: `p · P^n(G) ≤ successProb`.
* `ABBKS26.one_sub_mul_le_successProb`: `(1 - β) p ≤ successProb` when `P^n(Gᶜ) ≤ β`.
* `ABBKS26.one_sub_le_successProb`: the same with `p = 1`, for an algorithm that succeeds for
  every coin string on `G`.
* `ABBKS26.Glue.measureReal_compl_inter_le`: `μ(A ∩ B)ᶜ ≤ μ Aᶜ + μ Bᶜ`, to combine good events.
-/

@[expose] public section

namespace ABBKS26

open MeasureTheory

variable {k d : ℕ}

/-! ### Coin probabilities -/

theorem coinProb_nonneg (m : ℕ) (Q : List Bool → Prop) : 0 ≤ coinProb m Q := by
  unfold coinProb
  positivity

theorem coinProb_le_one (m : ℕ) (Q : List Bool → Prop) : coinProb m Q ≤ 1 := by
  classical
  unfold coinProb
  rw [div_le_one (by positivity)]
  have h := Fintype.card_subtype_le (fun r : Fin m → Bool ↦ Q (List.ofFn r))
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- A property of every coin string has coin probability `1`. -/
theorem coinProb_of_forall {m : ℕ} {Q : List Bool → Prop} (h : ∀ c, Q c) :
    coinProb m (fun c ↦ Q c) = 1 := by
  classical
  unfold coinProb
  rw [Fintype.card_congr (Equiv.subtypeUnivEquiv fun r ↦ h (List.ofFn r)), Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin]
  push_cast
  exact div_self (by positivity)

/-- Coin probabilities are monotone in the property. -/
theorem coinProb_mono {m : ℕ} {Q Q' : List Bool → Prop} (h : ∀ c, Q c → Q' c) :
    coinProb m Q ≤ coinProb m Q' := by
  classical
  unfold coinProb
  gcongr
  exact_mod_cast Fintype.card_subtype_mono _ _ fun r ↦ h (List.ofFn r)

/-! ### Lower bounds on the success probability -/

/-- `μ (A ∩ B)ᶜ ≤ μ Aᶜ + μ Bᶜ`. -/
theorem Glue.measureReal_compl_inter_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (A B : Set α) : μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

variable {P : Measure (Triple k d)}

/-- **Success from a good set of samples.** If on a measurable set `G` of samples the algorithm
succeeds with probability at least `p` over its coins, then its success probability is at least
`p · P^n(G)`. -/
theorem le_successProb [IsProbabilityMeasure P] {α β : Type} {n : ℕ} (r : Rounding k d)
    (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) {G : Set (Fin n → Triple k d)}
    (hG : MeasurableSet G) {p : ℝ}
    (hpG : ∀ ω ∈ G, p ≤ coinProb (T (input (roundedSample r ω)))
      (fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c)))) :
    p * (Measure.pi fun _ : Fin n ↦ P).real G ≤ successProb P n r input A T Good := by
  rcases lt_or_ge p 0 with hp | hp
  · exact (mul_nonpos_of_nonpos_of_nonneg hp.le measureReal_nonneg).trans
      ENNReal.toReal_nonneg
  set μ := Measure.pi fun _ : Fin n ↦ P with hμ
  set F : (Fin n → Triple k d) → ENNReal := fun ω ↦
    ENNReal.ofReal (coinProb (T (input (roundedSample r ω)))
      fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c))) with hF
  have hle : G.indicator (fun _ ↦ ENNReal.ofReal p) ≤ F := fun ω ↦ by
    by_cases hω : ω ∈ G
    · rw [Set.indicator_of_mem hω]
      exact ENNReal.ofReal_le_ofReal (hpG ω hω)
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hlint := lintegral_mono (μ := μ) hle
  rw [lintegral_indicator_const hG] at hlint
  have hF1 : ∫⁻ ω, F ω ∂μ ≤ 1 :=
    calc ∫⁻ ω, F ω ∂μ ≤ ∫⁻ _, 1 ∂μ :=
          lintegral_mono fun ω ↦ ENNReal.ofReal_le_one.2 (coinProb_le_one _ _)
      _ = 1 := by simp
  calc p * μ.real G = (ENNReal.ofReal p * μ G).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hp, measureReal_def]
    _ ≤ (∫⁻ ω, F ω ∂μ).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hF1) hlint
    _ = successProb P n r input A T Good := rfl

/-- **Success from a likely good set of samples.** If the algorithm succeeds with coin
probability at least `p ≥ 0` on every sample in a measurable set `G` whose complement has
probability at most `β`, then its success probability is at least `(1 - β) p`. -/
theorem one_sub_mul_le_successProb [IsProbabilityMeasure P] {α β : Type} {n : ℕ}
    (r : Rounding k d) (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) {G : Set (Fin n → Triple k d)}
    (hG : MeasurableSet G) {p b : ℝ} (hp : 0 ≤ p)
    (hGc : (Measure.pi fun _ : Fin n ↦ P).real Gᶜ ≤ b)
    (hpG : ∀ ω ∈ G, p ≤ coinProb (T (input (roundedSample r ω)))
      (fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c)))) :
    (1 - b) * p ≤ successProb P n r input A T Good := by
  have h1 : (Measure.pi fun _ : Fin n ↦ P).real G =
      1 - (Measure.pi fun _ : Fin n ↦ P).real Gᶜ := by
    rw [probReal_compl_eq_one_sub hG]
    ring
  refine le_trans ?_ (le_successProb r input A T Good hG hpG)
  rw [h1, mul_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) hp

/-- **Deterministic success on a likely good set of samples.** If the algorithm succeeds for
every coin string on every sample in a measurable set `G` whose complement has probability at most
`β`, then its success probability is at least `1 - β`. -/
theorem one_sub_le_successProb [IsProbabilityMeasure P] {α β : Type} {n : ℕ}
    (r : Rounding k d) (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) {G : Set (Fin n → Triple k d)}
    (hG : MeasurableSet G) {b : ℝ}
    (hGc : (Measure.pi fun _ : Fin n ↦ P).real Gᶜ ≤ b)
    (hpG : ∀ ω ∈ G, ∀ c, Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c))) :
    1 - b ≤ successProb P n r input A T Good := by
  have h := one_sub_mul_le_successProb r input A T Good hG zero_le_one hGc fun ω hω ↦
    (coinProb_of_forall (m := T (input (roundedSample r ω))) (hpG ω hω)).ge
  rwa [mul_one] at h

end ABBKS26
