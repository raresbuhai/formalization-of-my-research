module

public import B25.Basic

/-!
# Deterministic facts about the Lasso

For `y = Xβ + w` and a Lasso estimate `b` of radius `‖β‖₁`, with `Δ = b - β` and `T = supp β`:

* `B25.exists_isLasso`: a Lasso estimate exists (a continuous function on the compact `ℓ₁`-ball,
  `IsCompact.exists_isMinOn`).
* The **basic inequality** [Wainwright, Equation (7.28)]: comparing with the feasible `β`,
  `‖XΔ‖₂² ≤ 2 ⟨w, XΔ⟩`. Then Cauchy–Schwarz gives `‖XΔ‖₂² ≤ 4 ‖w‖₂²` (`B25.lasso_le_noise`), the
  trivial bound of [B25, proof of Corollary 1.6].
* The **fast rate** (`B25.lasso_fast`) [B25, proof of Corollary 1.6, after Wainwright, Theorem
  7.20b]: `‖b‖₁ ≤ ‖β‖₁` puts `Δ` in the cone `C(T)`, so `‖Δ‖₁ ≤ 2 ‖Δ_T‖₁ ≤ 2 √|T| ‖Δ_T‖₂`. If every
  column has `|⟨Xⱼ, w⟩| ≤ t`, Hölder gives `⟨w, XΔ⟩ ≤ t ‖Δ‖₁`, and `γ_T(X) ‖Δ_T‖₂² ≤ ‖XΔ‖₂²/n`
  (`B25.reConst_le_reRatio`), so `γ_T(X) ‖XΔ‖₂² ≤ 16 |T| t² / n`. (If `Δ_T = 0`, the cone forces
  `Δ = 0`.)
-/

@[expose] public section

namespace B25

open Matrix

namespace LS

/-- The objective `‖y - Xb‖₂²` of the Lasso is continuous in `b`. -/
theorem continuous_lassoObjQuokka {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) :
    Continuous fun b : Fin d → ℝ ↦ (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b) := by
  have h : Continuous fun b : Fin d → ℝ ↦ y - X *ᵥ b :=
    continuous_const.sub (continuous_const.matrix_mulVec continuous_id)
  exact h.dotProduct h

/-- The `ℓ₁`-ball `{b | ‖b‖₁ ≤ r}` is compact. -/
theorem isCompact_l1BallQuokka {d : ℕ} (r : ℝ) : IsCompact {b : Fin d → ℝ | l1 b ≤ r} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).abs)
      continuous_const
  · refine isBounded_iff_forall_norm_le.2 ⟨max r 0, fun b hb ↦ ?_⟩
    refine (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun i ↦ ?_
    rw [Real.norm_eq_abs]
    exact ((Finset.single_le_sum (fun j _ ↦ abs_nonneg (b j)) (Finset.mem_univ i)).trans
      hb).trans (le_max_left _ _)

/-- `x ⬝ᵥ x ≥ 0`. -/
theorem dot_self_nonnegQuokka {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)

/-- The basic inequality `‖XΔ‖₂² ≤ 2 ⟨w, XΔ⟩` for a Lasso estimate `b` of radius `‖β‖₁`,
`Δ = b - β`. -/
theorem basic_ineqQuokka {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {β : Fin d → ℝ}
    {w : Fin n → ℝ} {b : Fin d → ℝ} (hb : IsLasso X (X *ᵥ β + w) (l1 β) b) :
    (X *ᵥ (b - β)) ⬝ᵥ (X *ᵥ (b - β)) ≤ 2 * (w ⬝ᵥ (X *ᵥ (b - β))) := by
  have h := hb.2 β le_rfl
  have e1 : X *ᵥ β + w - X *ᵥ b = w - X *ᵥ (b - β) := by
    rw [Matrix.mulVec_sub]; abel
  have e2 : X *ᵥ β + w - X *ᵥ β = w := by abel
  rw [e1, e2] at h
  simp only [sub_dotProduct, dotProduct_sub] at h
  rw [dotProduct_comm (X *ᵥ (b - β)) w] at h
  linarith

/-- `‖b‖₁ ≤ ‖β‖₁` puts `Δ = b - β` in the cone `C(supp β)`. -/
theorem mem_cone_suppQuokka {d : ℕ} {β b : Fin d → ℝ} (h : l1 b ≤ l1 β) :
    b - β ∈ cone (supp β) := by
  have hoff : ∀ j ∈ (supp β)ᶜ, β j = 0 := fun j hj ↦ by simpa [supp] using hj
  have h1 : l1 b = ∑ j ∈ supp β, |b j| + ∑ j ∈ (supp β)ᶜ, |b j| :=
    (Finset.sum_add_sum_compl _ _).symm
  have h2 : l1 β = ∑ j ∈ supp β, |β j| := by
    rw [l1, ← Finset.sum_add_sum_compl (supp β),
      Finset.sum_eq_zero (s := (supp β)ᶜ) fun j hj ↦ by rw [hoff j hj, abs_zero], add_zero]
  change ∑ j ∈ (supp β)ᶜ, |(b - β) j| ≤ ∑ j ∈ supp β, |(b - β) j|
  have h3 : ∑ j ∈ (supp β)ᶜ, |(b - β) j| = ∑ j ∈ (supp β)ᶜ, |b j| :=
    Finset.sum_congr rfl fun j hj ↦ by rw [Pi.sub_apply, hoff j hj, sub_zero]
  have h4 : ∑ j ∈ supp β, (|β j| - |b j|) ≤ ∑ j ∈ supp β, |(b - β) j| :=
    Finset.sum_le_sum fun j _ ↦ by
      rw [Pi.sub_apply, abs_sub_comm]; exact abs_sub_abs_le_abs_sub _ _
  rw [Finset.sum_sub_distrib] at h4
  linarith

/-- Hölder: `⟨w, XΔ⟩ ≤ t ‖Δ‖₁` when every column has `|⟨Xⱼ, w⟩| ≤ t`. -/
theorem dot_mulVec_leQuokka {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {w : Fin n → ℝ} {t : ℝ}
    (ht : ∀ j, |∑ i, X i j * w i| ≤ t) (Δ : Fin d → ℝ) :
    w ⬝ᵥ (X *ᵥ Δ) ≤ t * l1 Δ := by
  rw [Matrix.dotProduct_mulVec, l1, Finset.mul_sum]
  change ∑ j, (w ᵥ* X) j * Δ j ≤ _
  refine Finset.sum_le_sum fun j _ ↦ ?_
  have hj : (w ᵥ* X) j = ∑ i, X i j * w i := by
    simp only [Matrix.vecMul, dotProduct, mul_comm]
  calc (w ᵥ* X) j * Δ j ≤ |(w ᵥ* X) j * Δ j| := le_abs_self _
    _ = |(w ᵥ* X) j| * |Δ j| := abs_mul _ _
    _ ≤ t * |Δ j| := by rw [hj]; exact mul_le_mul_of_nonneg_right (ht j) (abs_nonneg _)

end LS

/-- A Lasso estimate exists. -/
theorem exists_isLasso {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) {r : ℝ}
    (hr : 0 ≤ r) : ∃ b, IsLasso X y r b := by
  obtain ⟨b, hb, hmin⟩ := (LS.isCompact_l1BallQuokka (d := d) r).exists_isMinOn
    ⟨0, by simp [l1, hr]⟩ (LS.continuous_lassoObjQuokka X y).continuousOn
  exact ⟨b, hb, fun b' hb' ↦ isMinOn_iff.1 hmin b' hb'⟩

/-- The trivial bound `‖X(b - β)‖₂² ≤ 4 ‖w‖₂²` for a Lasso estimate `b` of radius `‖β‖₁`. -/
theorem lasso_le_noise {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {β : Fin d → ℝ} {w : Fin n → ℝ}
    {b : Fin d → ℝ} (hb : IsLasso X (X *ᵥ β + w) (l1 β) b) :
    (X *ᵥ (b - β)) ⬝ᵥ (X *ᵥ (b - β)) ≤ 4 * (w ⬝ᵥ w) := by
  set v := X *ᵥ (b - β)
  have h : v ⬝ᵥ v ≤ 2 * (w ⬝ᵥ v) := LS.basic_ineqQuokka hb
  have hcs : (w ⬝ᵥ v) ^ 2 ≤ (w ⬝ᵥ w) * (v ⬝ᵥ v) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w v
    simpa only [dotProduct, sq] using this
  have hv := LS.dot_self_nonnegQuokka v
  have hw := LS.dot_self_nonnegQuokka w
  rcases eq_or_lt_of_le hv with h0 | hpos
  · rw [← h0]; linarith
  · have h1 : (v ⬝ᵥ v) ^ 2 ≤ 4 * (w ⬝ᵥ v) ^ 2 := by nlinarith
    nlinarith

/-- The fast rate: `γ_T(X) ‖X(b - β)‖₂² ≤ 16 |T| t² / n` for `T = supp β` when every column has
`|⟨Xⱼ, w⟩| ≤ t`. -/
theorem lasso_fast {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {β : Fin d → ℝ} {w : Fin n → ℝ}
    {b : Fin d → ℝ} (hb : IsLasso X (X *ᵥ β + w) (l1 β) b) {t : ℝ}
    (ht : ∀ j, |∑ i, X i j * w i| ≤ t) :
    reConst X (supp β) * ((X *ᵥ (b - β)) ⬝ᵥ (X *ᵥ (b - β))) ≤
      16 * (supp β).card * t ^ 2 / n := by
  have hbasic := LS.basic_ineqQuokka hb
  have hcone := LS.mem_cone_suppQuokka hb.1
  set T := supp β
  set Δ := b - β
  set Q := (X *ᵥ Δ) ⬝ᵥ (X *ᵥ Δ)
  have hQ0 : 0 ≤ Q := LS.dot_self_nonnegQuokka _
  have hRHS : 0 ≤ 16 * (T.card : ℝ) * t ^ 2 / n := by positivity
  have hcone' : ∑ j ∈ Tᶜ, |Δ j| ≤ ∑ j ∈ T, |Δ j| := hcone
  by_cases hne : ∃ j ∈ T, Δ j ≠ 0
  swap
  · push Not at hne
    have hoff : ∑ j ∈ Tᶜ, |Δ j| = 0 := by
      refine le_antisymm ?_ (Finset.sum_nonneg fun j _ ↦ abs_nonneg _)
      rwa [Finset.sum_eq_zero (s := T) fun j hj ↦ by rw [hne j hj, abs_zero]] at hcone'
    have hΔ : Δ = 0 := by
      funext j
      by_cases hj : j ∈ T
      · exact hne j hj
      · have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ abs_nonneg (Δ j))).1 hoff j
          (Finset.mem_compl.2 hj)
        simpa using this
    have hQz : Q = 0 := by simp [Q, hΔ]
    rw [hQz, mul_zero]; exact hRHS
  obtain ⟨j₀, hj₀T, hj₀⟩ := hne
  have ht0 : 0 ≤ t := (abs_nonneg _).trans (ht j₀)
  have hγ0 : 0 ≤ reConst X T := reConst_nonneg X T
  set A := ∑ j ∈ T, Δ j ^ 2
  have hγ : reConst X T ≤ Q / n / A := reConst_le_reRatio X hcone ⟨j₀, hj₀T, hj₀⟩
  have hA : 0 < A :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun j _ ↦ sq_nonneg (Δ j)) hj₀T)
  have hγA : reConst X T * A ≤ Q / n := (le_div_iff₀ hA).1 hγ
  set s := ∑ j ∈ T, |Δ j|
  have hl1 : l1 Δ ≤ 2 * s := by
    rw [l1, ← Finset.sum_add_sum_compl T]; linarith
  have hs : s ^ 2 ≤ T.card * A := by
    have := Finset.sum_mul_sq_le_sq_mul_sq T (fun _ ↦ (1 : ℝ)) fun j ↦ |Δ j|
    simpa only [one_mul, one_pow, sq_abs, Finset.sum_const, nsmul_eq_mul, mul_one] using this
  have hQ : Q ≤ 4 * t * s := by
    have h1 := LS.dot_mulVec_leQuokka ht Δ
    have h2 := mul_le_mul_of_nonneg_left hl1 ht0
    linarith
  have hQ2 : Q ^ 2 ≤ 16 * t ^ 2 * (T.card * A) := by
    have h1 : Q ^ 2 ≤ (4 * t * s) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
    have h2 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 16 * t ^ 2)
    nlinarith
  rcases eq_or_lt_of_le hQ0 with hQz | hQp
  · rw [← hQz, mul_zero]; exact hRHS
  have key : reConst X T * Q * Q ≤ 16 * T.card * t ^ 2 / n * Q := by
    calc reConst X T * Q * Q = reConst X T * Q ^ 2 := by ring
      _ ≤ reConst X T * (16 * t ^ 2 * (T.card * A)) := mul_le_mul_of_nonneg_left hQ2 hγ0
      _ = 16 * t ^ 2 * T.card * (reConst X T * A) := by ring
      _ ≤ 16 * t ^ 2 * T.card * (Q / n) := mul_le_mul_of_nonneg_left hγA (by positivity)
      _ = 16 * T.card * t ^ 2 / n * Q := by ring
  exact le_of_mul_le_mul_right key hQp

end B25
