module

public import BHSV25.Spectral.Basic

/-!
# Spectral facts for the hardness reductions

* **Models are negative semidefinite off the stationary direction**
  (`BHSV25.Hard.model_quad_nonpos`): for a model `M` with stationary distribution `π`, the
  symmetric matrix `M_ab / π_b` has `∑_{a,b} Y_a (M_ab / π_b) Y_b ≤ 0` whenever `∑_a Y_a = 0`.
  The matrix `√π_a M_ab / √π_b` is symmetric, has the characteristic polynomial of `M`, so at
  most one positive eigenvalue, and fixes `√π`; its quadratic form is therefore at most `0` on the
  vectors orthogonal to `√π`.
* **Counting large eigenvalues against a planted form** (`BHSV25.Hard.numEigGT_le_of_quad`,
  `BHSV25.Hard.card_eig_lt_neg_le`): if the quadratic form of the normalized adjacency matrix is
  at most `Q x + e ‖x‖²` and `Q` is at most `0` on the vectors orthogonal to `t` given vectors,
  at most `t` eigenvalues exceed `e`; if it is at least `-e ‖x‖²` on the vectors orthogonal to `t`
  given vectors, at most `t` eigenvalues are below `-e`. Both are the counting form of the
  Courant–Fischer theorem (`BHSV25.Spectral.card_le_of_inEigSpan`).
-/

@[expose] public section

namespace BHSV25.Hard

open Matrix Finset

/-! ### Models -/

section Model

variable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ}

/-- The symmetrization `√π_a M_ab / √π_b` of a reversible matrix. -/
noncomputable def symOf (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun a b ↦ Real.sqrt (π a) * M a b / Real.sqrt (π b)

theorem symOf_isHermitian {π : Fin k → ℝ} (hπ : IsStationary M π) :
    (symOf M π).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b ↦ ?_
  simp only [symOf, star_trivial]
  have ha := Real.sqrt_pos.2 (hπ.1 a)
  have hb := Real.sqrt_pos.2 (hπ.1 b)
  have hd := hπ.2.2 a b
  rw [div_eq_div_iff ha.ne' hb.ne']
  have e1 : Real.sqrt (π a) * Real.sqrt (π a) = π a := Real.mul_self_sqrt (hπ.1 a).le
  have e2 : Real.sqrt (π b) * Real.sqrt (π b) = π b := Real.mul_self_sqrt (hπ.1 b).le
  calc Real.sqrt (π b) * M b a * Real.sqrt (π b) = (Real.sqrt (π b) * Real.sqrt (π b)) * M b a := by
        ring
    _ = π a * M a b := by rw [e2, hd]
    _ = Real.sqrt (π a) * M a b * Real.sqrt (π a) := by rw [mul_right_comm, e1]

theorem charpoly_symOf {π : Fin k → ℝ} (hπ : IsStationary M π) :
    (symOf M π).charpoly = M.charpoly := by
  have hsq : ∀ a, Real.sqrt (π a) ≠ 0 := fun a ↦ (Real.sqrt_pos.2 (hπ.1 a)).ne'
  have hS : symOf M π = diagonal (fun a ↦ Real.sqrt (π a)) *
      (M * diagonal (fun b ↦ (Real.sqrt (π b))⁻¹)) := by
    ext a b
    simp [symOf, diagonal_mul, mul_diagonal, div_eq_mul_inv, mul_assoc]
  rw [hS, charpoly_mul_comm, mul_assoc, diagonal_mul_diagonal]
  have : (diagonal fun b ↦ (Real.sqrt (π b))⁻¹ * Real.sqrt (π b)) = 1 := by
    rw [← diagonal_one]
    congr 1
    funext b
    exact inv_mul_cancel₀ (hsq b)
  rw [this, mul_one]

/-- A model has at most one positive eigenvalue: for its symmetrization, two indices with
positive eigenvalues coincide. -/
theorem eig_pos_unique (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π) {i j : Fin k}
    (hi : 0 < (symOf_isHermitian hπ).eigenvalues i)
    (hj : 0 < (symOf_isHermitian hπ).eigenvalues j) : i = j := by
  have hcard := hM.secondEig
  rw [← charpoly_symOf hπ, (symOf_isHermitian hπ).roots_charpoly_eq_eigenvalues,
    Multiset.filter_map, Multiset.card_map] at hcard
  have h2 : (Finset.univ.filter fun i ↦ 0 < (symOf_isHermitian hπ).eigenvalues i).card ≤ 1 := by
    refine le_trans (le_of_eq ?_) hcard
    rw [Finset.card_def, Finset.filter_val]
    congr 1
  exact Finset.card_le_one.1 h2 i (by simpa using hi) j (by simpa using hj)

theorem symOf_mulVec_sqrt (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π) :
    symOf M π *ᵥ (fun a ↦ Real.sqrt (π a)) = fun a ↦ Real.sqrt (π a) := by
  funext a
  have hsq : ∀ b, Real.sqrt (π b) ≠ 0 := fun b ↦ (Real.sqrt_pos.2 (hπ.1 b)).ne'
  simp only [mulVec, dotProduct, symOf]
  have : ∀ b, Real.sqrt (π a) * M a b / Real.sqrt (π b) * Real.sqrt (π b) =
      Real.sqrt (π a) * M a b := fun b ↦ div_mul_cancel₀ _ (hsq b)
  simp_rw [this, ← mul_sum, hM.rowSum a, mul_one]

/-- **A model is negative semidefinite off the stationary direction**: for `∑ Y = 0`,
`∑_{a,b} Y_a (M_ab / π_b) Y_b ≤ 0`. -/
theorem model_quad_nonpos (hM : IsModel M) {π : Fin k → ℝ} (hπ : IsStationary M π)
    (Y : Fin k → ℝ) (hY : ∑ a, Y a = 0) :
    ∑ a, ∑ b, Y a * (M a b / π b) * Y b ≤ 0 := by
  set hS := symOf_isHermitian hπ
  set u : Fin k → ℝ := fun a ↦ Real.sqrt (π a)
  set v : Fin k → ℝ := fun a ↦ Y a / Real.sqrt (π a)
  have hsq : ∀ a, Real.sqrt (π a) ≠ 0 := fun a ↦ (Real.sqrt_pos.2 (hπ.1 a)).ne'
  have hsq2 : ∀ a, Real.sqrt (π a) * Real.sqrt (π a) = π a :=
    fun a ↦ Real.mul_self_sqrt (hπ.1 a).le
  -- the quadratic form of the symmetrization at `v`
  have hquad : v ⬝ᵥ (symOf M π *ᵥ v) = ∑ a, ∑ b, Y a * (M a b / π b) * Y b := by
    simp only [dotProduct, mulVec, symOf, v, mul_sum]
    refine sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ ?_
    conv_rhs => rw [← hsq2 b]
    field_simp [hsq a, hsq b]
  -- `u` is a fixed vector, so its coefficients live on eigenvalue `1`
  have hu : ∀ i, Spectral.coeff hS i u ≠ 0 → hS.eigenvalues i = 1 := by
    intro i hi
    have h := Spectral.coeff_mulVec hS i u
    rw [symOf_mulVec_sqrt hM hπ] at h
    have : (hS.eigenvalues i - 1) * Spectral.coeff hS i u = 0 := by rw [sub_mul, ← h]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 hi
  have huv : u ⬝ᵥ v = 0 := by
    simp only [dotProduct, u, v]
    rw [← hY]
    exact sum_congr rfl fun a _ ↦ by field_simp [hsq a]
  rw [← hquad, Spectral.quad_eq hS]
  by_cases hex : ∃ i₀, Spectral.coeff hS i₀ u ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hex
    have hpos₀ : 0 < hS.eigenvalues i₀ := by rw [hu i₀ hi₀]; exact one_pos
    -- every other coefficient of `u` vanishes
    have hother : ∀ i, i ≠ i₀ → Spectral.coeff hS i u = 0 := by
      intro i hi
      by_contra h
      have := hu i h
      exact hi (eig_pos_unique hM hπ (by rw [this]; exact one_pos) hpos₀)
    have hv₀ : Spectral.coeff hS i₀ v = 0 := by
      have h := Spectral.dotProduct_eq_sum_coeff hS u v
      rw [huv, Finset.sum_eq_single i₀ (fun i _ hi ↦ by rw [hother i hi, zero_mul])
        (by simp)] at h
      exact (mul_eq_zero.1 h.symm).resolve_left hi₀
    refine sum_nonpos fun i _ ↦ ?_
    by_cases hi : i = i₀
    · rw [hi, hv₀]; simp
    · have : hS.eigenvalues i ≤ 0 := by
        by_contra hc
        exact hi (eig_pos_unique hM hπ (lt_of_not_ge hc) hpos₀)
      exact mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _)
  · -- `u = 0` is impossible
    simp only [not_exists, not_not] at hex
    have h0 := Spectral.sum_coeff_sq hS u
    simp only [hex, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sum_const_zero] at h0
    exfalso
    cases k with
    | zero => exact absurd hπ.2.1 (by simp)
    | succ k =>
      have : 0 < u ⬝ᵥ u := by
        refine lt_of_lt_of_le ?_ (single_le_sum (f := fun a ↦ u a * u a)
          (fun a _ ↦ mul_self_nonneg _) (mem_univ 0))
        exact mul_self_pos.2 (hsq 0)
      simp only [dotProduct] at this h0
      linarith

end Model

/-! ### Counting eigenvalues -/

section Count

variable (G : Graph)

theorem quad_lt_of_inEigSpan {τ : ℝ} {x : Fin G.1 → ℝ}
    (h : Spectral.InEigSpan G.normAdj_isHermitian (· < τ) x) (hx : x ≠ 0) :
    x ⬝ᵥ (G.normAdj *ᵥ x) < τ * (x ⬝ᵥ x) := by
  set hA := G.normAdj_isHermitian
  rw [Spectral.quad_eq hA, ← Spectral.sum_coeff_sq hA, mul_sum]
  have hne : ∃ i, Spectral.coeff hA i x ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hx (Spectral.eq_of_coeff_eq hA fun i ↦ by
      rw [hc i]; simp [Spectral.coeff])
  obtain ⟨i₀, hi₀⟩ := hne
  have hle : ∀ i, hA.eigenvalues i * Spectral.coeff hA i x ^ 2 ≤
      τ * Spectral.coeff hA i x ^ 2 := by
    intro i
    by_cases hi : hA.eigenvalues i < τ
    · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
    · rw [h i hi]; simp
  refine sum_lt_sum (fun i _ ↦ hle i) ⟨i₀, mem_univ _, ?_⟩
  have hi : hA.eigenvalues i₀ < τ := by
    by_contra hc
    exact hi₀ (h i₀ hc)
  exact mul_lt_mul_of_pos_right hi (by positivity)

/-- **At most `t` eigenvalues above `e`**, if the quadratic form is at most `Q x + e ‖x‖²` with
`Q ≤ 0` off `t` given vectors. -/
theorem numEigGT_le_of_quad {t : ℕ} (w : Fin t → Fin G.1 → ℝ)
    (Q : (Fin G.1 → ℝ) → ℝ) (e : ℝ)
    (hup : ∀ x, x ⬝ᵥ (G.normAdj *ᵥ x) ≤ Q x + e * (x ⬝ᵥ x))
    (hQ : ∀ x, (∀ j, w j ⬝ᵥ x = 0) → Q x ≤ 0) : G.numEigGT e ≤ t := by
  unfold Graph.numEigGT Graph.eig
  refine Spectral.card_le_of_inEigSpan G.normAdj_isHermitian (e < ·) w fun x hx hw ↦ ?_
  by_contra hne
  have h1 := Spectral.quad_gt_of_inEigSpan G.normAdj_isHermitian hx hne
  have h2 := hup x
  have h3 := hQ x hw
  linarith

/-- **At most `t` eigenvalues below `-e`**, if the quadratic form is at least `-e ‖x‖²` off `t`
given vectors. -/
theorem card_eig_lt_neg_le {t : ℕ} (w : Fin t → Fin G.1 → ℝ) (e : ℝ)
    (hlow : ∀ x, (∀ j, w j ⬝ᵥ x = 0) → -e * (x ⬝ᵥ x) ≤ x ⬝ᵥ (G.normAdj *ᵥ x)) :
    (univ.filter fun i ↦ G.eig i < -e).card ≤ t := by
  unfold Graph.eig
  refine Spectral.card_le_of_inEigSpan G.normAdj_isHermitian (· < -e) w fun x hx hw ↦ ?_
  by_contra hne
  have h1 := quad_lt_of_inEigSpan G hx hne
  have h2 := hlow x hw
  linarith

/-- The eigenvalues larger than `e` in absolute value are those above `e` and those below `-e`. -/
theorem card_abs_eig_le (e : ℝ) :
    (univ.filter fun i ↦ e < |G.eig i|).card ≤
      G.numEigGT e + (univ.filter fun i ↦ G.eig i < -e).card := by
  unfold Graph.numEigGT
  refine (card_le_card fun i hi ↦ ?_).trans (card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union] at hi ⊢
  rcases lt_abs.1 hi with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

end Count

end BHSV25.Hard
