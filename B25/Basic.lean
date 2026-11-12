module

public import B25.Model

/-!
# Basic facts

* Euclidean norms and correlations: the triangle inequality, scaling, and the bound
  `‖u + v‖₂² ≥ (1 - ε) ‖u‖₂²` when `|corr u v| ≤ ε` [B25, proof of Proposition 1.10].
* Signed tuples of coordinates (`B25.tupleVec`): the vectors `∑ₜ ±e_{aₜ}` that Maurey's empirical
  method produces.
* The restricted eigenvalue constant as an infimum of ratios (`B25.reRatio`): it is nonnegative,
  at most every admissible ratio, at least any lower bound of them, and at most `1` for columns
  of norm `√n`; and the constant of `X_S` in terms of vectors of `ℝ^d` supported on `S`.
* Rotated designs: `[X_S, R X_{Sᶜ}] α = Xα` for `α` supported on `S`, and `= R (Xα)` for `α`
  supported on `Sᶜ`.
-/

@[expose] public section

namespace B25

open Matrix

/-! ### Norms and correlations -/

/-- `‖x‖₂` is the norm of `x` seen in `EuclideanSpace ℝ (Fin n)`. -/
theorem BS.l2_eq_normQx {n : ℕ} (x : Fin n → ℝ) :
    l2 x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq, l2]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, sq]

/-- `x ⬝ᵥ y` is the inner product of `x` and `y` seen in `EuclideanSpace ℝ (Fin n)`. -/
theorem BS.dot_eq_innerQx {n : ℕ} (x y : Fin n → ℝ) :
    x ⬝ᵥ y = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct_comm]

/-- `x ⬝ᵥ x ≥ 0`. -/
theorem BS.dot_self_nonnegQx {n : ℕ} (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)

theorem l2_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ l2 x :=
  Real.sqrt_nonneg _

theorem l2_sq {n : ℕ} (x : Fin n → ℝ) : l2 x ^ 2 = x ⬝ᵥ x :=
  Real.sq_sqrt (BS.dot_self_nonnegQx x)

/-- The triangle inequality for the Euclidean norm. -/
theorem l2_add_le {n : ℕ} (x y : Fin n → ℝ) : l2 (x + y) ≤ l2 x + l2 y := by
  simp only [BS.l2_eq_normQx, WithLp.toLp_add]
  exact norm_add_le _ _

theorem l2_smul {n : ℕ} (c : ℝ) (x : Fin n → ℝ) : l2 (c • x) = |c| * l2 x := by
  simp only [BS.l2_eq_normQx, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

/-- The Cauchy–Schwarz inequality `|x ⬝ᵥ y| ≤ ‖x‖₂ ‖y‖₂`. -/
theorem BS.abs_dot_le_l2Qx {n : ℕ} (x y : Fin n → ℝ) : |x ⬝ᵥ y| ≤ l2 x * l2 y := by
  rw [BS.dot_eq_innerQx, BS.l2_eq_normQx, BS.l2_eq_normQx]
  exact abs_real_inner_le_norm _ _

/-- Correlations do not change when a vector is scaled by a positive number. -/
theorem corr_smul_left {n : ℕ} {c : ℝ} (hc : 0 < c) (u v : Fin n → ℝ) :
    corr (c • u) v = corr u v := by
  rw [corr, corr, l2_smul, abs_of_pos hc, smul_dotProduct, smul_eq_mul, mul_assoc]
  exact mul_div_mul_left _ _ hc.ne'

/-- Correlations do not change when a vector is scaled by a positive number. -/
theorem corr_smul_right {n : ℕ} {c : ℝ} (hc : 0 < c) (u v : Fin n → ℝ) :
    corr u (c • v) = corr u v := by
  rw [corr, corr, l2_smul, abs_of_pos hc, dotProduct_smul, smul_eq_mul, mul_left_comm]
  exact mul_div_mul_left _ _ hc.ne'

/-- Scaling by nonnegative numbers can only make a correlation smaller in absolute value (it is
`0` when a factor is `0`). -/
theorem abs_corr_smul_le {n : ℕ} {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c') (u v : Fin n → ℝ) :
    |corr (c • u) (c' • v)| ≤ |corr u v| := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [corr]
  rcases hc'.eq_or_lt with rfl | hc'
  · simp [corr]
  rw [corr_smul_left hc, corr_smul_right hc']

/-- If `|corr u v| ≤ ε`, then `|u ⬝ᵥ v| ≤ ε ‖u‖₂ ‖v‖₂` (also when `u = 0` or `v = 0`). -/
theorem BS.abs_dot_le_epsQx {n : ℕ} {u v : Fin n → ℝ} {ε : ℝ} (h : |corr u v| ≤ ε) :
    |u ⬝ᵥ v| ≤ ε * (l2 u * l2 v) := by
  have hab : 0 ≤ l2 u * l2 v := mul_nonneg (l2_nonneg u) (l2_nonneg v)
  rcases hab.eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]
    exact (BS.abs_dot_le_l2Qx u v).trans h0.ge
  · rw [corr, abs_div, abs_of_pos hpos, div_le_iff₀ hpos] at h
    exact h

/-- [B25, proof of Proposition 1.10]: if `|corr u v| ≤ ε ≤ 1`, then
`‖u + v‖₂² ≥ (1 - ε)(‖u‖₂² + ‖v‖₂²) ≥ (1 - ε) ‖u‖₂²`. -/
theorem one_sub_mul_le_dot_add {n : ℕ} {u v : Fin n → ℝ} {ε : ℝ} (hε : ε ≤ 1)
    (h : |corr u v| ≤ ε) : (1 - ε) * (u ⬝ᵥ u) ≤ (u + v) ⬝ᵥ (u + v) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans h
  have hd := BS.abs_dot_le_epsQx h
  have hexp : (u + v) ⬝ᵥ (u + v) = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm v u]
    ring
  rw [hexp, ← l2_sq u, ← l2_sq v]
  have hneg := neg_abs_le (u ⬝ᵥ v)
  have ha := l2_nonneg u
  have hb := l2_nonneg v
  nlinarith [sq_nonneg (l2 u - l2 v), mul_nonneg hε0 (sq_nonneg (l2 u - l2 v)),
    mul_nonneg (sub_nonneg.2 hε) (sq_nonneg (l2 v))]

/-! ### Signed tuples -/

/-- The vector `∑ₜ ±e_{aₜ}` of a tuple of signed coordinates: `aₜ = (j, true)` contributes `e_j`
and `aₜ = (j, false)` contributes `-e_j`. -/
noncomputable def tupleVec {d s : ℕ} (a : Fin s → Fin d × Bool) : Fin d → ℝ :=
  ∑ t, (if (a t).2 then (1 : ℝ) else -1) • Pi.single (a t).1 (1 : ℝ)

/-- A tuple of coordinates in `T` gives a vector supported on `T`. -/
theorem tupleVec_eq_zero {d s : ℕ} {a : Fin s → Fin d × Bool} {T : Finset (Fin d)}
    (ha : ∀ t, (a t).1 ∈ T) {j : Fin d} (hj : j ∉ T) : tupleVec a j = 0 := by
  simp only [tupleVec, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_eq_zero fun t _ ↦ ?_
  have hne : j ≠ (a t).1 := fun h ↦ hj (h ▸ ha t)
  simp [hne]

/-! ### The restricted eigenvalue constant -/

/-- The ratio `(1/n) ‖Xβ‖₂² / ‖β_S‖₂²`, whose infimum over the cone is the restricted eigenvalue
constant. -/
noncomputable def reRatio {n : ℕ} {ι : Type*} [Fintype ι] (X : Matrix (Fin n) ι ℝ)
    (S : Finset ι) (β : ι → ℝ) : ℝ :=
  ((X *ᵥ β) ⬝ᵥ (X *ᵥ β) / n) / ∑ j ∈ S, β j ^ 2

theorem reConst_eq_iInf {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι ℝ) (S : Finset ι) :
    reConst X S = ⨅ β : {β : ι → ℝ // β ∈ cone S ∧ ∃ j ∈ S, β j ≠ 0}, reRatio X S β.1 :=
  rfl

theorem reRatio_nonneg {n : ℕ} {ι : Type*} [Fintype ι] (X : Matrix (Fin n) ι ℝ)
    (S : Finset ι) (β : ι → ℝ) : 0 ≤ reRatio X S β :=
  div_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _) (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem reConst_nonneg {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι ℝ) (S : Finset ι) : 0 ≤ reConst X S := by
  rw [reConst_eq_iInf]
  exact Real.iInf_nonneg fun β ↦ reRatio_nonneg X S β.1

theorem reConst_empty {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι ℝ) : reConst X ∅ = 0 := by
  have : IsEmpty {β : ι → ℝ // β ∈ cone (∅ : Finset ι) ∧ ∃ j ∈ (∅ : Finset ι), β j ≠ 0} :=
    ⟨fun β ↦ by simpa using β.2.2⟩
  exact Real.iInf_of_isEmpty _

/-- The constant is at most the ratio of every admissible vector. -/
theorem reConst_le_reRatio {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι ℝ) {S : Finset ι} {β : ι → ℝ} (hβ : β ∈ cone S)
    (hne : ∃ j ∈ S, β j ≠ 0) : reConst X S ≤ reRatio X S β := by
  rw [reConst_eq_iInf]
  refine ciInf_le ⟨0, ?_⟩ (⟨β, hβ, hne⟩ : {β : ι → ℝ // β ∈ cone S ∧ ∃ j ∈ S, β j ≠ 0})
  rintro _ ⟨γ, rfl⟩
  exact reRatio_nonneg X S γ.1

/-- A coordinate vector of `S` is in the cone of `S`. -/
theorem BS.single_mem_coneQx {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Finset ι} {j : ι}
    (hj : j ∈ S) : (Pi.single j (1 : ℝ) : ι → ℝ) ∈ cone S := by
  have h0 : ∑ i ∈ Sᶜ, |(Pi.single j (1 : ℝ) : ι → ℝ) i| = 0 := by
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hne : i ≠ j := fun h ↦ (Finset.mem_compl.1 hi) (h ▸ hj)
    simp [hne]
  rw [cone, Set.mem_ofPred_eq, h0]
  exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _

/-- A lower bound on the ratios of all admissible vectors is a lower bound on the constant. -/
theorem le_reConst {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix (Fin n) ι ℝ)
    {S : Finset ι} (hS : S.Nonempty) {g : ℝ}
    (h : ∀ β ∈ cone S, (∃ j ∈ S, β j ≠ 0) → g ≤ reRatio X S β) : g ≤ reConst X S := by
  obtain ⟨j, hj⟩ := hS
  have : Nonempty {β : ι → ℝ // β ∈ cone S ∧ ∃ j ∈ S, β j ≠ 0} :=
    ⟨⟨Pi.single j 1, BS.single_mem_coneQx hj, j, hj, by simp⟩⟩
  rw [reConst_eq_iInf]
  exact le_ciInf fun β ↦ h β.1 β.2.1 β.2.2

/-- For columns of norm `√n` in `S`, the constant is at most `1` (the ratio of a coordinate vector
of `S`). -/
theorem reConst_le_one {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι ℝ) {S : Finset ι} (hn : 0 < n) (hS : S.Nonempty)
    (hX : ∀ j ∈ S, ∑ i, X i j ^ 2 = n) : reConst X S ≤ 1 := by
  obtain ⟨j, hj⟩ := hS
  refine (reConst_le_reRatio X (BS.single_mem_coneQx hj) ⟨j, hj, by simp⟩).trans_eq ?_
  have hsum : ∑ i ∈ S, (Pi.single j (1 : ℝ) : ι → ℝ) i ^ 2 = 1 := by
    rw [Finset.sum_eq_single_of_mem j hj fun i _ hi ↦ by simp [Pi.single_eq_of_ne hi]]
    simp
  have hcol : (X *ᵥ Pi.single j 1) ⬝ᵥ (X *ᵥ Pi.single j 1) = n := by
    rw [mulVec_single_one, ← hX j hj]
    simp [dotProduct, sq]
  rw [reRatio, hsum, hcol, div_one, div_self (Nat.cast_pos.2 hn).ne']

/-- A sum over the subtype `S` of a function vanishing off `S` is the sum over all indices. -/
theorem BS.sum_coe_eq_sumQx {d : ℕ} {S : Finset (Fin d)} {g : Fin d → ℝ}
    (hg : ∀ j ∉ S, g j = 0) : ∑ j : S, g j.1 = ∑ j, g j := by
  rw [Finset.sum_coe_sort S g]
  exact Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ hg j hj

/-- The sum over `S'.subtype (· ∈ S)` is the sum over `S'` when `S' ⊆ S`. -/
theorem BS.sum_subtype_eq_sumQx {d : ℕ} {S S' : Finset (Fin d)} (hS' : S' ⊆ S)
    (g : Fin d → ℝ) : ∑ j ∈ S'.subtype (· ∈ S), g j.1 = ∑ j ∈ S', g j := by
  rw [Finset.sum_subtype_eq_sum_filter, Finset.filter_true_of_mem fun j hj ↦ hS' hj]

/-- `γ_{S'}(X_S)` is at most the ratio of every admissible vector of `ℝ^d` supported on `S`. -/
theorem reConst_cols_le {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) {S S' : Finset (Fin d)}
    (hS' : S' ⊆ S) {α : Fin d → ℝ} (hα : ∀ j ∉ S, α j = 0) (hcone : α ∈ cone S')
    (hne : ∃ j ∈ S', α j ≠ 0) :
    reConst (cols X S) (S'.subtype (· ∈ S)) ≤ reRatio X S' α := by
  set α' : S → ℝ := fun j ↦ α j.1
  have hmul : cols X S *ᵥ α' = X *ᵥ α := by
    ext i
    exact BS.sum_coe_eq_sumQx (g := fun j ↦ X i j * α j) fun j hj ↦ by simp [hα j hj]
  have habs : ∑ j : S, |α' j| = ∑ j, |α j| :=
    BS.sum_coe_eq_sumQx (g := fun j ↦ |α j|) fun j hj ↦ by simp [hα j hj]
  have hT : ∑ j ∈ S'.subtype (· ∈ S), |α' j| = ∑ j ∈ S', |α j| :=
    BS.sum_subtype_eq_sumQx hS' fun j ↦ |α j|
  have hcone' : α' ∈ cone (S'.subtype (· ∈ S)) := by
    have h1 := Finset.sum_compl_add_sum (S'.subtype (· ∈ S)) fun j ↦ |α' j|
    have h2 := Finset.sum_compl_add_sum S' fun j ↦ |α j|
    have hc : ∑ j ∈ S'ᶜ, |α j| ≤ ∑ j ∈ S', |α j| := hcone
    rw [cone, Set.mem_ofPred_eq]
    linarith
  obtain ⟨j, hj, hj0⟩ := hne
  refine (reConst_le_reRatio _ hcone' ⟨⟨j, hS' hj⟩, Finset.mem_subtype.2 hj, hj0⟩).trans_eq ?_
  rw [reRatio, reRatio, hmul, BS.sum_subtype_eq_sumQx hS' fun j ↦ α j ^ 2]

/-- For columns of norm `√n`, `γ_{S'}(X_S) ≤ 1` for nonempty `S' ⊆ S`. -/
theorem reConst_cols_le_one {n d : ℕ} {X : Matrix (Fin n) (Fin d) ℝ} {S S' : Finset (Fin d)}
    (hn : 0 < n) (hX : HasNormalizedColumns X) (hS' : S' ⊆ S) (hne : S'.Nonempty) :
    reConst (cols X S) (S'.subtype (· ∈ S)) ≤ 1 := by
  obtain ⟨j, hj⟩ := hne
  exact reConst_le_one _ hn ⟨⟨j, hS' hj⟩, Finset.mem_subtype.2 hj⟩ fun j _ ↦ hX j.1

/-! ### Rotated designs -/

theorem rotateCols_mulVec_of_mem {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (R : Matrix (Fin n) (Fin n) ℝ) {α : Fin d → ℝ} (hα : ∀ j ∉ S, α j = 0) :
    rotateCols X S R *ᵥ α = X *ᵥ α := by
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ S
  · simp [rotateCols, hj]
  · simp [hα j hj]

theorem rotateCols_mulVec_of_not_mem {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ)
    (S : Finset (Fin d)) (R : Matrix (Fin n) (Fin n) ℝ) {β : Fin d → ℝ}
    (hβ : ∀ j ∈ S, β j = 0) : rotateCols X S R *ᵥ β = R *ᵥ (X *ᵥ β) := by
  rw [mulVec_mulVec]
  ext i
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ S
  · simp [hβ j hj]
  · simp [rotateCols, hj]

end B25
