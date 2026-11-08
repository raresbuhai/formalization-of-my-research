module

public import BB20.Prediction.Risk
public import BB20.Prediction.Deviation

/-!
# Concentration of the empirical risk

The probability of events of `M` independent samples (`BB20.RBM.sampleProb`): monotonicity, union
bounds, complements. Then, for a variable `u`, features on `V ∌ u` and `γ > 0`, the deviation
bound of `BB20/Prediction/Deviation.lean` applied to the logistic losses of weights in the `ℓ₁`
ball of radius `2γ`: the losses shifted by `l(0) = log 2` are contractions of the scores
(`BB20.Prediction.prob_exists_dev_le`). This gives, with probability at least
`1 - 4 · 2^{|V|} exp(-M ε² / (2048 γ²))`, both `L(w) ≤ L̂(w) + ε/8` for every `w` in the ball and
`L̂(w̄) ≤ L(w̄) + ε/8` (`BB20.Prediction.prob_not_dev_le`). The bound for every `w` of the ball
follows from the bound for finitely many: the sample space is finite, so the weights that witness
a large deviation for some sample form a finite family.
-/

@[expose] public section

namespace BB20.Prediction

open Finset Real

variable {n m : ℕ}

theorem sampleProb_nonneg (R : RBM n m) (M : ℕ) (P : (Fin M → Config n) → Prop) :
    0 ≤ R.sampleProb M P := by
  unfold RBM.sampleProb
  refine Finset.sum_nonneg fun X _ ↦ ?_
  split_ifs
  · exact prod_weight_nonneg (fun x ↦ (R.obsProb_pos x).le) X
  · exact le_rfl

theorem sampleProb_mono (R : RBM n m) (M : ℕ) {P Q : (Fin M → Config n) → Prop}
    (h : ∀ X, P X → Q X) : R.sampleProb M P ≤ R.sampleProb M Q := by
  unfold RBM.sampleProb
  refine Finset.sum_le_sum fun X _ ↦ ?_
  have := prod_weight_nonneg (fun x ↦ (R.obsProb_pos x).le) X
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (h X h1) h2
  · exact this
  · exact le_rfl

theorem sampleProb_or_le (R : RBM n m) (M : ℕ) (P Q : (Fin M → Config n) → Prop) :
    R.sampleProb M (fun X ↦ P X ∨ Q X) ≤ R.sampleProb M P + R.sampleProb M Q := by
  unfold RBM.sampleProb
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun X _ ↦ ?_
  have := prod_weight_nonneg (fun x ↦ (R.obsProb_pos x).le) X
  by_cases hP : P X <;> by_cases hQ : Q X <;> simp [hP, hQ, this]

theorem sampleProb_add_not (R : RBM n m) (M : ℕ) (P : (Fin M → Config n) → Prop) :
    R.sampleProb M P + R.sampleProb M (fun X ↦ ¬ P X) = 1 := by
  unfold RBM.sampleProb
  rw [← Finset.sum_add_distrib, ← sum_prod_weight R.sum_obsProb M]
  refine Finset.sum_congr rfl fun X _ ↦ ?_
  by_cases h : P X <;> simp [h]

/-- The union bound, for the complement of an intersection. -/
theorem one_sub_sum_le_sampleProb_forall (R : RBM n m) (M : ℕ) {ι : Type*} [Fintype ι]
    (G : ι → (Fin M → Config n) → Prop) :
    1 - ∑ i, R.sampleProb M (fun X ↦ ¬ G i X) ≤ R.sampleProb M (fun X ↦ ∀ i, G i X) := by
  classical
  have h1 := sampleProb_add_not R M (fun X ↦ ∀ i, G i X)
  have h2 : R.sampleProb M (fun X ↦ ¬ ∀ i, G i X) ≤ ∑ i, R.sampleProb M (fun X ↦ ¬ G i X) := by
    unfold RBM.sampleProb
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun X _ ↦ ?_
    have hw := prod_weight_nonneg (fun x ↦ (R.obsProb_pos x).le) X
    split_ifs with h
    · obtain ⟨i, hi⟩ := not_forall.1 h
      refine le_trans ?_ (Finset.single_le_sum (fun j _ ↦ ?_) (Finset.mem_univ i))
      · simp [hi]
      · split_ifs
        · exact hw
        · exact le_rfl
    · exact Finset.sum_nonneg fun j _ ↦ by
        split_ifs
        · exact hw
        · exact le_rfl
  linarith

/-- **Uniform deviation of the empirical risk** over a family of weights in the `ℓ₁` ball:
`P(∃ i, σ (L(Wᵢ) - L̂(Wᵢ)) > η) ≤ 2 · 2^{|V|} exp(-M η² / (8 (2γ)²))` for `σ = ±1`. -/
theorem prob_exists_dev_le (R : RBM n m) (u : Fin n) (V : Finset (Fin n)) {ι : Type*}
    [Finite ι] [Nonempty ι] (W : ι → Finset (Fin n) → ℝ) {γ : ℝ} (hγ : 0 < γ)
    (hW : ∀ i, l1Norm V (W i) ≤ 2 * γ) {σ : ℝ} (hσ : |σ| = 1) {M : ℕ} (hM : 0 < M) {η : ℝ}
    (hη : 0 < η) :
    R.sampleProb M (fun X ↦ ∃ i, η < σ * (popRisk R u V (W i) - empRisk u V X (W i))) ≤
      2 * 2 ^ V.card * exp (-(M * η ^ 2 / (8 * (2 * γ) ^ 2))) := by
  classical
  set f : ι → Config n → ℝ :=
    fun i x ↦ σ * (logLoss (spin (x u) * score V (W i) x) - Real.log 2) with hf
  have hf1 : ∀ i i' x, |f i x - f i' x| ≤
      |∑ j ∈ V.powerset, W i j * chi j x - ∑ j ∈ V.powerset, W i' j * chi j x| := by
    intro i i' x
    have h := abs_logLoss_sub_le (spin (x u) * score V (W i) x) (spin (x u) * score V (W i') x)
    rw [← mul_sub, abs_mul, abs_spin, one_mul] at h
    have e : f i x - f i' x = σ * (logLoss (spin (x u) * score V (W i) x) -
        logLoss (spin (x u) * score V (W i') x)) := by
      simp only [hf]
      ring
    rw [e, abs_mul, hσ, one_mul]
    exact h
  have hf2 : ∀ i x, |f i x| ≤ |∑ j ∈ V.powerset, W i j * chi j x| := by
    intro i x
    have h := abs_logLoss_sub_le (spin (x u) * score V (W i) x) 0
    rw [logLoss_zero, sub_zero, abs_mul, abs_spin, one_mul] at h
    simp only [hf]
    rw [abs_mul, hσ, one_mul]
    exact h
  have key := prob_sup_dev_le (μ := R.obsProb) (fun x ↦ (R.obsProb_pos x).le) R.sum_obsProb
    V.powerset ⟨∅, Finset.empty_mem_powerset V⟩ chi (fun j _ x ↦ (abs_chi j x).le) W
    (by linarith : (0 : ℝ) < 2 * γ) hW f hf1 hf2 M hη
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hsum : ∀ i (X : Fin M → Config n), ∑ k, ((∑ x, R.obsProb x * f i x) - f i (X k)) =
      M * (σ * (popRisk R u V (W i) - empRisk u V X (W i))) := by
    intro i X
    have h1 : ∑ x, R.obsProb x * f i x = σ * (popRisk R u V (W i) - Real.log 2) := by
      calc ∑ x, R.obsProb x * f i x
          = ∑ x, (σ * (R.obsProb x * logLoss (spin (x u) * score V (W i) x)) -
              σ * Real.log 2 * R.obsProb x) := by
            refine Finset.sum_congr rfl fun x _ ↦ ?_
            simp only [hf]
            ring
        _ = σ * popRisk R u V (W i) - σ * Real.log 2 * ∑ x, R.obsProb x := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, popRisk]
        _ = σ * (popRisk R u V (W i) - Real.log 2) := by
            rw [R.sum_obsProb]
            ring
    have h2 : ∑ k, logLoss (spin (X k u) * score V (W i) (X k)) = M * empRisk u V X (W i) := by
      unfold empRisk
      field_simp
    rw [h1]
    calc ∑ k, (σ * (popRisk R u V (W i) - Real.log 2) - f i (X k))
        = ∑ k, (σ * popRisk R u V (W i) - σ * logLoss (spin (X k u) * score V (W i) (X k))) := by
          refine Finset.sum_congr rfl fun k _ ↦ ?_
          simp only [hf]
          ring
      _ = M * (σ * popRisk R u V (W i)) -
            σ * ∑ k, logLoss (spin (X k u) * score V (W i) (X k)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Finset.mul_sum]
      _ = M * (σ * (popRisk R u V (W i) - empRisk u V X (W i))) := by
          rw [h2]
          ring
  calc R.sampleProb M (fun X ↦ ∃ i, η < σ * (popRisk R u V (W i) - empRisk u V X (W i)))
      ≤ ∑ X : Fin M → Config n, (if ∃ i, M * η < ∑ k, ((∑ x, R.obsProb x * f i x) - f i (X k))
          then ∏ k, R.obsProb (X k) else 0) := by
        unfold RBM.sampleProb
        refine Finset.sum_le_sum fun X _ ↦ ?_
        have hw := prod_weight_nonneg (fun x ↦ (R.obsProb_pos x).le) X
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          apply h2
          obtain ⟨i, hi⟩ := h1
          exact ⟨i, by rw [hsum i X]; exact mul_lt_mul_of_pos_left hi hMpos⟩
        · exact hw
        · exact le_rfl
    _ ≤ 2 * (V.powerset.card : ℝ) * exp (-(M * η ^ 2 / (8 * (2 * γ) ^ 2))) := by
        convert key
    _ = 2 * 2 ^ V.card * exp (-(M * η ^ 2 / (8 * (2 * γ) ^ 2))) := by
        rw [Finset.card_powerset]
        push_cast
        ring

/-- With probability at least `1 - 4 · 2^{|V|} exp(-M ε² / (2048 γ²))`, the empirical risk is at
least the population risk minus `ε/8` on the ball, and at most the population risk plus `ε/8` at
`w̄`. -/
theorem prob_not_dev_le (R : RBM n m) {γ : ℝ} (hγ : 0 < γ) (hW : R.WidthLE γ) {u : Fin n}
    {V : Finset (Fin n)} (hu : u ∉ V) {ε : ℝ} (hε : 0 < ε) {M : ℕ} (hM : 0 < M) :
    R.sampleProb M (fun X ↦ ¬ ((∀ w, l1Norm V w ≤ 2 * γ →
        popRisk R u V w ≤ empRisk u V X w + ε / 8) ∧
        empRisk u V X (wbar R u) ≤ popRisk R u V (wbar R u) + ε / 8)) ≤
      4 * 2 ^ V.card * exp (-(M * ε ^ 2 / (2048 * γ ^ 2))) := by
  classical
  let wit : (Fin M → Config n) → Finset (Fin n) → ℝ := fun X ↦
    if h : ∃ w, l1Norm V w ≤ 2 * γ ∧ empRisk u V X w + ε / 8 < popRisk R u V w then h.choose
    else 0
  have hwit : ∀ X, l1Norm V (wit X) ≤ 2 * γ := by
    intro X
    simp only [wit]
    split_ifs with h
    · exact h.choose_spec.1
    · simp only [l1Norm, Pi.zero_apply, abs_zero, Finset.sum_const_zero]
      linarith
  have h1 := prob_exists_dev_le R u V wit hγ hwit (σ := 1) (by simp) hM (η := ε / 8)
    (by positivity)
  have h2 := prob_exists_dev_le R u V (fun _ : Unit ↦ wbar R u) hγ
    (fun _ ↦ l1Norm_wbar_le R hW hu) (σ := -1) (by simp) hM (η := ε / 8) (by positivity)
  have hexp : (M : ℝ) * (ε / 8) ^ 2 / (8 * (2 * γ) ^ 2) = M * ε ^ 2 / (2048 * γ ^ 2) := by
    field_simp
    ring
  rw [hexp] at h1 h2
  calc _ ≤ R.sampleProb M (fun X ↦
          (∃ i, ε / 8 < 1 * (popRisk R u V (wit i) - empRisk u V X (wit i))) ∨
          ∃ _i : Unit, ε / 8 < -1 * (popRisk R u V (wbar R u) - empRisk u V X (wbar R u))) := by
        apply sampleProb_mono
        intro X hX
        by_cases hA : ∀ w, l1Norm V w ≤ 2 * γ → popRisk R u V w ≤ empRisk u V X w + ε / 8
        · right
          refine ⟨(), ?_⟩
          have hB : ¬ empRisk u V X (wbar R u) ≤ popRisk R u V (wbar R u) + ε / 8 :=
            fun h ↦ hX ⟨hA, h⟩
          push Not at hB
          linarith
        · left
          refine ⟨X, ?_⟩
          have hex : ∃ w, l1Norm V w ≤ 2 * γ ∧ empRisk u V X w + ε / 8 < popRisk R u V w := by
            push Not at hA
            exact hA
          have hspec := hex.choose_spec
          simp only [wit, dite_eq_left hex]
          linarith [hspec.2]
    _ ≤ _ := sampleProb_or_le R M _ _
    _ ≤ 2 * 2 ^ V.card * exp (-(M * ε ^ 2 / (2048 * γ ^ 2))) +
          2 * 2 ^ V.card * exp (-(M * ε ^ 2 / (2048 * γ ^ 2))) := add_le_add h1 h2
    _ = 4 * 2 ^ V.card * exp (-(M * ε ^ 2 / (2048 * γ ^ 2))) := by ring

end BB20.Prediction
