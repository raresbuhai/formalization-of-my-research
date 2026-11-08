module

public import BMW26.Spec.Paper
public import BMW26.Prob.Percolation

/-!
# Lemma 5.1, as stated in `Challenge.lean`

`BMW26.spectral_concentration_of_parts`: `BMW26.spectral_paper_whp` for the coins of
`BMW26.coinMeasure`, read on `Q_d(p)`:

* the probability of an event under `Q_d(p)` (`BMW26.percProb`) is that of the event for
  `coinGraph ω` (`BMW26.sum_percolationProb_eq`);
* the Laplacian form of a subgraph of `Q_d` is its energy with indicator weights
  (`BMW26.lapForm_eq_energy`: each edge `{x, flip x i}` counted once at its lower endpoint), and
  the energy of `coinGraph ω` is that of the coin weights, which agree at lower endpoints
  (`BMW26.graphW_coinGraph`).
-/

@[expose] public section

namespace BMW26

/-- The Laplacian form of a subgraph of the hypercube is its energy with indicator weights. -/
theorem lapForm_eq_energy {d : ℕ} {H : SimpleGraph (Cube d)} (hH : H ≤ cube d)
    (g : Cube d → ℝ) : lapForm H g = energy (graphW H) g := by
  classical
  -- the neighbours of `x` in `H` are among its flips
  have hx : ∀ x, (∑ y, if H.Adj x y then (g x - g y) ^ 2 else 0) =
      ∑ i, if H.Adj x (flip x i) then (g x - g (flip x i)) ^ 2 else 0 := by
    intro x
    have hinj : Set.InjOn (fun i ↦ flip x i) (Finset.univ : Finset (Fin d)) :=
      fun i _ j _ h ↦ (Perc.flip_eq_flip_iff x).1 h
    rw [← Finset.sum_image (f := fun y ↦ if H.Adj x y then (g x - g y) ^ 2 else 0) hinj]
    refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy ↦ ?_).symm
    refine ite_eq_right fun hadj ↦ ?_
    obtain ⟨i, rfl⟩ := cube_adj_iff.1 (hH hadj)
    exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) hy
  unfold lapForm energy
  rw [Finset.sum_congr rfl fun x _ ↦ hx x, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Cube.sum_filter_false_eq_half i]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    unfold graphW
    by_cases h : H.Adj x (flip x i) <;> simp [h]
  · intro x
    rw [flip_flip]
    by_cases h : H.Adj x (flip x i)
    · rw [ite_eq_left h, ite_eq_left h.symm]; ring
    · rw [ite_eq_right h, ite_eq_right fun h' ↦ h h'.symm]

/-- **[BMW26, Lemma 5.1]**, the statement of `Challenge.lean`. -/
theorem spectral_concentration_of_parts :
    ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ p : ℝ,
      C * Real.log d / d ≤ p → p ≤ 1 →
        1 - 1 / (d : ℝ) ^ C₁ ≤ percProb d p fun H ↦ ∃ R : Finset (Cube d),
          (R.card : ℝ) ≤ 2 ^ d / (d : ℝ) ^ C₂ ∧ ∀ g : Cube d → ℝ,
            |lapForm H g - p * lapForm (cube d) g| ≤
              ε * p * lapForm (cube d) g +
                (d : ℝ) ^ 2 * ∑ x ∈ R, (g x - (∑ y, g y) / 2 ^ d) ^ 2 := by
  intro ε hε C₁ C₂
  obtain ⟨C, hC, m₀, hmain⟩ := spectral_paper_whp hε C₁ C₂
  refine ⟨C, hC, m₀, fun d hd p hpC hp1 ↦ ?_⟩
  have hp : 0 ≤ p :=
    le_trans (div_nonneg (mul_nonneg hC.le (Real.log_natCast_nonneg d)) (Nat.cast_nonneg d)) hpC
  have hcoins := isCoins_coinMeasure d hp hp1
  have := hcoins.isProb
  have key := hmain d hd p hpC hp1 (coinMeasure d p hp hp1) (fun e ω ↦ ω e) hcoins
  set P : SimpleGraph (Cube d) → Prop := fun H ↦ ∃ R : Finset (Cube d),
    (R.card : ℝ) ≤ 2 ^ d / (d : ℝ) ^ C₂ ∧ ∀ g : Cube d → ℝ,
      |lapForm H g - p * lapForm (cube d) g| ≤
        ε * p * lapForm (cube d) g + (d : ℝ) ^ 2 * ∑ x ∈ R, (g x - (∑ y, g y) / 2 ^ d) ^ 2
    with hPdef
  have hpp : percProb d p P =
      (coinMeasure d p hp hp1).real {ω | coinGraph ω ∈ {H | P H}} :=
    sum_percolationProb_eq d hp hp1 {H | P H}
  rw [hpp]
  refine key.trans (MeasureTheory.measureReal_mono ?_)
  rintro ω ⟨R, hR, hineq⟩
  refine ⟨R, hR, fun g ↦ ?_⟩
  have e1 : lapForm (coinGraph ω) g = energy (coinW (fun e ω ↦ ω e) ω) g := by
    rw [lapForm_eq_energy (coinGraph_le ω)]
    exact Perc.energy_congr (fun j x hx ↦ graphW_coinGraph ω j hx) g
  have e2 : lapForm (cube d) g = energy 1 g := by
    rw [lapForm_eq_energy le_rfl]
    refine Perc.energy_congr (fun j x _ ↦ ?_) g
    unfold graphW
    rw [ite_eq_left (cube_adj_iff.2 ⟨j, rfl⟩)]
    rfl
  rw [e1, e2]
  exact hineq g

end BMW26
