module

public import BB20.Basic
public import BB20.Prediction.Sample

/-!
# Theorem 12: prediction error of the regression step

Fix a variable `u` and its features on `V = nb u`. The proof (in `BB20/Prediction/`) compares the
population risk `L(w) = E[l(X_u (w · z))]` of the logistic loss with its empirical version `L̂`:

* `BB20/Prediction/Logistic.lean`: Pinsker's inequality and smoothness for the Bernoulli
  divergences that make up the excess risk.
* `BB20/Prediction/Risk.lean`: the prediction error is at most half the excess risk
  `L(w) - L*`; the weights `w̄_T = 2 f̂(T ∪ {u})` lie in the `ℓ₁` ball of radius `2γ` and have
  excess risk at most `ε / 2` (this uses the hypothesis on `ζ`); so if `L ≤ L̂ + ε/8` on the ball
  and `L̂(w̄) ≤ L(w̄) + ε/8`, every near-minimizer has error at most `ε`.
* `BB20/Prediction/Contraction.lean`, `BB20/Prediction/Deviation.lean`,
  `BB20/Prediction/Sample.lean`: these deviations fail with probability at most
  `4 · 2^D exp(-M ε² / (2048 γ²))` (symmetrization, contraction, Massart's lemma, Chernoff).

With `C = 2048` and `M ≥ C γ² log(8 n 2^D / δ) / ε²`, this is at most `δ / (2n)` for each
variable (`BB20.Prediction.prob_not_good_le`), and a union bound over the `n` variables finishes
the proof. Width `γ = 0` is separate: the local fields vanish, and so do the weights of the
subsets of `V` for every `w` in the ball, so the error is `0`.
-/

@[expose] public section

namespace BB20.Prediction

open Finset Real

/-- With width `0`, every weight in the ball predicts exactly. -/
theorem predError_eq_zero_of_width_zero {n m : ℕ} (R : RBM n m) (hW : R.WidthLE 0) (u : Fin n)
    (V : Finset (Fin n)) (w : Finset (Fin n) → ℝ) (hw : l1Norm V w ≤ 2 * 0) :
    R.predError u V w = 0 := by
  have hw0 : ∀ T ∈ V.powerset, w T = 0 := by
    have h0 : ∑ T ∈ V.powerset, |w T| = 0 :=
      le_antisymm (by simpa [l1Norm] using hw) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    intro T hT
    exact abs_eq_zero.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ abs_nonneg _).1 h0 T hT)
  have hs : ∀ x, score V w x = 0 := fun x ↦
    Finset.sum_eq_zero fun T hT ↦ by rw [hw0 T hT, zero_mul]
  have hf : ∀ x, R.field u x = 0 := fun x ↦ abs_nonpos_iff.1 (R.abs_field_le hW u x)
  unfold RBM.predError
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  rw [R.condProb_eq, hf, hs]
  simp

/-- For one variable `u`: the probability that some near-minimizer has prediction error larger
than `ε` is at most `δ / (2n)`. -/
theorem prob_not_good_le {n m : ℕ} (R : RBM n m) {γ : ℝ} {d D : ℕ} {ζ ε δ : ℝ}
    (hW : R.WidthLE γ) (hd : R.LatentDegreeLE d) (hD : R.DegreeLE D) (hζ0 : 0 < ζ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hζ : ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))))
    {u : Fin n} {V : Finset (Fin n)} (hu : u ∉ V) (hV : V.card ≤ D)
    (hstrong : R.strongNbhd ζ u ⊆ V) {M : ℕ}
    (hM : 2048 * γ ^ 2 * Real.log (8 * n * 2 ^ D / δ) / ε ^ 2 ≤ M) :
    R.sampleProb M (fun X ↦ ¬ ∀ w, IsNearMinimizer γ (ε / 4) u V X w → R.predError u V w ≤ ε) ≤
      δ / (2 * n) := by
  have hn : (1 : ℝ) ≤ n := by
    have : 0 < n := Fin.pos u
    exact_mod_cast this
  have hγ0 : 0 ≤ γ := le_trans (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (hW u)
  rcases hγ0.eq_or_lt with hγ | hγ
  · -- width `0`: the event never happens
    subst hγ
    have hgood : ∀ (X : Fin M → Config n) (w : Finset (Fin n) → ℝ),
        IsNearMinimizer 0 (ε / 4) u V X w → R.predError u V w ≤ ε := fun X w hw ↦ by
      rw [predError_eq_zero_of_width_zero R hW u V w hw.1]
      exact hε.le
    unfold RBM.sampleProb
    refine le_trans (le_of_eq (Finset.sum_eq_zero fun X _ ↦ ?_)) (by positivity)
    simp only [ite_eq_right_iff]
    exact fun h ↦ absurd (hgood X) h
  have h2D : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
  have hpos : 0 < 8 * (n : ℝ) * 2 ^ D / δ := by positivity
  have hL : 0 < Real.log (8 * n * 2 ^ D / δ) := by
    apply Real.log_pos
    rw [one_lt_div hδ]
    nlinarith
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
    exact_mod_cast this
  have hLM : Real.log (8 * n * 2 ^ D / δ) ≤ M * ε ^ 2 / (2048 * γ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hM
    linarith
  calc _ ≤ R.sampleProb M (fun X ↦ ¬ ((∀ w, l1Norm V w ≤ 2 * γ →
          popRisk R u V w ≤ empRisk u V X w + ε / 8) ∧
          empRisk u V X (wbar R u) ≤ popRisk R u V (wbar R u) + ε / 8)) :=
        sampleProb_mono R M fun X hX hdev ↦ hX fun w hw ↦
          predError_le_of_dev R hW hd hD hζ0 hε hζ hu hstrong X hdev.1 hdev.2 w hw
    _ ≤ 4 * 2 ^ V.card * exp (-(M * ε ^ 2 / (2048 * γ ^ 2))) :=
        prob_not_dev_le R hγ hW hu hε hMpos
    _ ≤ 4 * 2 ^ D * exp (-Real.log (8 * n * 2 ^ D / δ)) := by
        gcongr
        norm_num
    _ = δ / (2 * n) := by
        rw [Real.exp_neg, Real.exp_log hpos]
        field_simp
        ring

/-- **Theorem 12** of [BB20]. -/
theorem predictionError :
    ∃ C : ℝ, ∀ (n m : ℕ) (R : RBM n m) (γ : ℝ) (d D : ℕ) (ζ ε δ : ℝ),
      R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → 0 < ζ → 0 < ε → 0 < δ →
      ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))) →
      ∀ nb : Fin n → Finset (Fin n),
        (∀ u, u ∉ nb u ∧ (nb u).card ≤ D ∧ R.strongNbhd ζ u ⊆ nb u) →
      ∀ M : ℕ, C * γ ^ 2 * Real.log (8 * n * 2 ^ D / δ) / ε ^ 2 ≤ M →
        1 - δ ≤ R.sampleProb M fun X ↦ ∀ (u : Fin n) (w : Finset (Fin n) → ℝ),
          IsNearMinimizer γ (ε / 4) u (nb u) X w → R.predError u (nb u) w ≤ ε := by
  refine ⟨2048, fun n m R γ d D ζ ε δ hW hd hD hζ0 hε hδ hζ nb hnb M hM ↦ ?_⟩
  rcases lt_or_ge 1 δ with hδ1 | hδ1
  · have := sampleProb_nonneg R M fun X ↦ ∀ (u : Fin n) (w : Finset (Fin n) → ℝ),
      IsNearMinimizer γ (ε / 4) u (nb u) X w → R.predError u (nb u) w ≤ ε
    linarith
  have hsum : ∑ u : Fin n, R.sampleProb M (fun X ↦ ¬ ∀ w,
      IsNearMinimizer γ (ε / 4) u (nb u) X w → R.predError u (nb u) w ≤ ε) ≤ δ := by
    calc _ ≤ ∑ _u : Fin n, δ / (2 * n) := Finset.sum_le_sum fun u _ ↦
          prob_not_good_le R hW hd hD hζ0 hε hδ hδ1 hζ (hnb u).1 (hnb u).2.1 (hnb u).2.2 hM
      _ = n * (δ / (2 * n)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ δ := by
          rcases Nat.eq_zero_or_pos n with h | h
          · simp [h, hδ.le]
          · have : (0 : ℝ) < n := Nat.cast_pos.2 h
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            nlinarith
  have := one_sub_sum_le_sampleProb_forall R M fun u X ↦ ∀ w,
    IsNearMinimizer γ (ε / 4) u (nb u) X w → R.predError u (nb u) w ≤ ε
  linarith

end BB20.Prediction
