module

public import BHSV25.Planted.Net

/-!
# The threshold rank after planting

[BHSV25, Lemma 7.16]: removing the edges inside the color classes keeps the threshold rank low.
For a symmetric matrix `X` and a partition `χ` of its indices into `k` parts, let `Q` be `X` without
the entries inside the parts (`Q = X - X_F`, with `X_F` block-diagonal). If at most `t₁` eigenvalues
of `X` are at least `r₁` and at most `t₂` are at most `-r₂`, then at most `t₁ + k t₂` eigenvalues of
`Q` are at least `r₁ + r₂` (`BHSV25.Planted.card_ge_le_of_remove`) and at most `k t₁ + t₂` are at
most `-(r₁ + r₂)` (`BHSV25.Planted.card_le_neg_le_of_remove`).

The paper applies Cauchy's interlacing theorem to the blocks of `X_F` and Weyl's inequalities to
`X - X_F`. Here both steps are one count of subspaces (Courant–Fischer,
`BHSV25.Spectral.card_le_of_inEigSpan`): a vector `x` of the top eigenspace of `Q` orthogonal to
the top eigenvectors of `X` and whose restrictions `P_a x` to the parts are orthogonal to the
bottom eigenvectors of `X` has `xᵀ Q x = xᵀ X x - ∑_a (P_a x)ᵀ X (P_a x) < (r₁ + r₂) ‖x‖²`, so it
is `0`; that is `t₁ + k t₂` linear conditions.

For a regular host `H` of degree `d ≥ 1` and the planted graph `G`, `X = A_H / d` and
`Q = A_G / d` (`BHSV25.Planted.adjDiv_plant`), and the eigenvalues of `Q` at least `r₁ + r₂` in
absolute value number at most `(k + 1) (t₁ + t₂)` (`BHSV25.Planted.card_abs_ge_plant_le`).
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Matrix Finset Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-! ### Counting with a family of conditions -/

open Classical in
/-- **Courant–Fischer** with conditions indexed by any finite type. -/
theorem card_le_of_inEigSpan' (hA : A.IsHermitian) (S : ℝ → Prop) {κ : Type*} [Fintype κ]
    (w : κ → ι → ℝ) (h : ∀ x, InEigSpan hA S x → (∀ j, w j ⬝ᵥ x = 0) → x = 0) :
    (univ.filter fun i ↦ S (hA.eigenvalues i)).card ≤ Fintype.card κ := by
  set e := Fintype.equivFin κ
  exact card_le_of_inEigSpan hA S (fun j ↦ w (e.symm j))
    (fun x hx hw ↦ h x hx fun j ↦ by simpa using hw (e j))

theorem quad_lt_of_inEigSpan (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (· < τ) x) (hx : x ≠ 0) : x ⬝ᵥ (A *ᵥ x) < τ * (x ⬝ᵥ x) := by
  rw [quad_eq hA, ← sum_coeff_sq hA, Finset.mul_sum]
  obtain ⟨i₀, hi₀⟩ := Impl.exists_coeff_ne_zero hA hx
  have hle : ∀ i, hA.eigenvalues i * coeff hA i x ^ 2 ≤ τ * coeff hA i x ^ 2 := by
    intro i
    by_cases hi : hA.eigenvalues i < τ
    · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
    · rw [h i hi]
      simp
  refine Finset.sum_lt_sum (fun i _ ↦ hle i) ⟨i₀, Finset.mem_univ _, ?_⟩
  have hi₀' : coeff hA i₀ x ≠ 0 := hi₀
  have hμ : hA.eigenvalues i₀ < τ := by
    by_contra hμ
    exact hi₀' (h i₀ hμ)
  exact mul_lt_mul_of_pos_right hμ (by positivity)

theorem quad_ge_of_inEigSpan (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (τ < ·) x) : τ * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
  rw [quad_eq hA, ← sum_coeff_sq hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : τ < hA.eigenvalues i
  · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
  · rw [h i hi]
    simp

theorem quad_le_of_inEigSpan (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (· < τ) x) : x ⬝ᵥ (A *ᵥ x) ≤ τ * (x ⬝ᵥ x) := by
  rw [quad_eq hA, ← sum_coeff_sq hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : hA.eigenvalues i < τ
  · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
  · rw [h i hi]
    simp

theorem quad_gt_of_inEigSpan' (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (τ < ·) x) (hx : x ≠ 0) : τ * (x ⬝ᵥ x) < x ⬝ᵥ (A *ᵥ x) :=
  quad_gt_of_inEigSpan hA h hx

/-- The vectors orthogonal to the eigenvectors whose eigenvalues satisfy `S` lie in the span of
the others. -/
theorem inEigSpan_of_orth (hA : A.IsHermitian) (S : ℝ → Prop) {x : ι → ℝ}
    (h : ∀ i, S (hA.eigenvalues i) → ⇑(hA.eigenvectorBasis i) ⬝ᵥ x = 0) :
    InEigSpan hA (fun μ ↦ ¬ S μ) x := fun i hi ↦ h i (not_not.1 hi)

/-! ### Removing the entries inside the parts -/

variable {k : ℕ}

/-- The restriction `P_a x` of `x` to the part `a`. -/
def restr (χ : ι → Fin k) (a : Fin k) (x : ι → ℝ) : ι → ℝ := fun u ↦ if χ u = a then x u else 0

omit [DecidableEq ι] in
theorem restr_dotProduct (χ : ι → Fin k) (a : Fin k) (v x : ι → ℝ) :
    restr χ a v ⬝ᵥ x = v ⬝ᵥ restr χ a x := by
  simp only [restr, dotProduct]
  exact sum_congr rfl fun u _ ↦ by split_ifs <;> simp

omit [DecidableEq ι] in
theorem sum_restr_dotProduct_self (χ : ι → Fin k) (x : ι → ℝ) :
    ∑ a, restr χ a x ⬝ᵥ restr χ a x = x ⬝ᵥ x := by
  simp only [restr, dotProduct]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [sum_eq_single (χ u) (fun a _ ha ↦ by simp [Ne.symm ha]) (by simp)]
  simp

omit [DecidableEq ι] in
/-- `xᵀ Q x = xᵀ X x - ∑_a (P_a x)ᵀ X (P_a x)` when `Q` is `X` without the entries inside the
parts. -/
theorem quad_remove (χ : ι → Fin k) {X Q : Matrix ι ι ℝ}
    (hQ : ∀ u v, Q u v = if χ u = χ v then 0 else X u v) (x : ι → ℝ) :
    x ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (X *ᵥ x) - ∑ a, restr χ a x ⬝ᵥ (X *ᵥ restr χ a x) := by
  have hpt : ∀ u v, ∑ a, restr χ a x u * (X u v * restr χ a x v) =
      if χ u = χ v then x u * (X u v * x v) else 0 := by
    intro u v
    simp only [restr]
    rw [sum_eq_single (χ u) (fun a _ ha ↦ by simp [Ne.symm ha]) (by simp)]
    by_cases h : χ u = χ v
    · simp [h]
    · simp [h, Ne.symm h]
  simp only [dotProduct, mulVec, mul_sum]
  rw [Finset.sum_comm (f := fun a u ↦ ∑ v, restr χ a x u * (X u v * restr χ a x v))]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [Finset.sum_comm, ← sum_sub_distrib]
  refine sum_congr rfl fun v _ ↦ ?_
  rw [hpt, hQ]
  split_ifs <;> ring

/-- **The top threshold rank after removing the parts** [BHSV25, Lemma 7.16]. -/
theorem card_ge_le_of_remove (χ : ι → Fin k) {X Q : Matrix ι ι ℝ} (hX : X.IsHermitian)
    (hQh : Q.IsHermitian) (hQ : ∀ u v, Q u v = if χ u = χ v then 0 else X u v) {r₁ r₂ : ℝ} :
    (univ.filter fun i ↦ r₁ + r₂ ≤ hQh.eigenvalues i).card ≤
      (univ.filter fun i ↦ r₁ ≤ hX.eigenvalues i).card +
        k * (univ.filter fun i ↦ hX.eigenvalues i ≤ -r₂).card := by
  classical
  set T₁ := univ.filter fun i ↦ r₁ ≤ hX.eigenvalues i
  set T₂ := univ.filter fun i ↦ hX.eigenvalues i ≤ -r₂
  let w : T₁ ⊕ (Fin k × T₂) → ι → ℝ := fun j ↦ match j with
    | Sum.inl i => ⇑(hX.eigenvectorBasis i.1)
    | Sum.inr (a, i) => restr χ a ⇑(hX.eigenvectorBasis i.1)
  have hcard : Fintype.card (T₁ ⊕ (Fin k × T₂)) = T₁.card + k * T₂.card := by
    simp
  rw [← hcard]
  refine card_le_of_inEigSpan' hQh (r₁ + r₂ ≤ ·) w fun x hx hw ↦ ?_
  by_contra hx0
  -- `x` is orthogonal to the top eigenvectors of `X`
  have h1 : InEigSpan hX (· < r₁) x := by
    intro i hi
    have hi' : r₁ ≤ hX.eigenvalues i := not_lt.1 hi
    exact hw (Sum.inl ⟨i, by simp [T₁, hi']⟩)
  -- the restrictions are orthogonal to the bottom eigenvectors of `X`
  have h2 : ∀ a, InEigSpan hX (-r₂ < ·) (restr χ a x) := by
    intro a i hi
    have hi' : hX.eigenvalues i ≤ -r₂ := not_lt.1 hi
    have := hw (Sum.inr (a, ⟨i, by simp [T₂, hi']⟩))
    simp only [w] at this
    rw [restr_dotProduct] at this
    exact this
  have hQx : (r₁ + r₂) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (Q *ᵥ x) := by
    rw [quad_eq hQh, ← sum_coeff_sq hQh, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : r₁ + r₂ ≤ hQh.eigenvalues i
    · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
    · rw [hx i hi]
      simp
  have hXx := quad_lt_of_inEigSpan hX h1 hx0
  have hXa : ∀ a, -r₂ * (restr χ a x ⬝ᵥ restr χ a x) ≤
      restr χ a x ⬝ᵥ (X *ᵥ restr χ a x) := fun a ↦ quad_ge_of_inEigSpan hX (h2 a)
  have hsum := sum_le_sum fun a (_ : a ∈ univ) ↦ hXa a
  rw [← mul_sum, sum_restr_dotProduct_self] at hsum
  rw [quad_remove χ hQ] at hQx
  nlinarith

/-- **The bottom threshold rank after removing the parts** [BHSV25, Lemma 7.16]. -/
theorem card_le_neg_le_of_remove (χ : ι → Fin k) {X Q : Matrix ι ι ℝ} (hX : X.IsHermitian)
    (hQh : Q.IsHermitian) (hQ : ∀ u v, Q u v = if χ u = χ v then 0 else X u v) {r₁ r₂ : ℝ} :
    (univ.filter fun i ↦ hQh.eigenvalues i ≤ -(r₁ + r₂)).card ≤
      k * (univ.filter fun i ↦ r₁ ≤ hX.eigenvalues i).card +
        (univ.filter fun i ↦ hX.eigenvalues i ≤ -r₂).card := by
  classical
  set T₁ := univ.filter fun i ↦ r₁ ≤ hX.eigenvalues i
  set T₂ := univ.filter fun i ↦ hX.eigenvalues i ≤ -r₂
  let w : (Fin k × T₁) ⊕ T₂ → ι → ℝ := fun j ↦ match j with
    | Sum.inl (a, i) => restr χ a ⇑(hX.eigenvectorBasis i.1)
    | Sum.inr i => ⇑(hX.eigenvectorBasis i.1)
  have hcard : Fintype.card ((Fin k × T₁) ⊕ T₂) = k * T₁.card + T₂.card := by
    simp
  rw [← hcard]
  refine card_le_of_inEigSpan' hQh (· ≤ -(r₁ + r₂)) w fun x hx hw ↦ ?_
  by_contra hx0
  -- `x` is orthogonal to the bottom eigenvectors of `X`
  have h1 : InEigSpan hX (-r₂ < ·) x := by
    intro i hi
    have hi' : hX.eigenvalues i ≤ -r₂ := not_lt.1 hi
    exact hw (Sum.inr ⟨i, by simp [T₂, hi']⟩)
  -- the restrictions are orthogonal to the top eigenvectors of `X`
  have h2 : ∀ a, InEigSpan hX (· < r₁) (restr χ a x) := by
    intro a i hi
    have hi' : r₁ ≤ hX.eigenvalues i := not_lt.1 hi
    have := hw (Sum.inl (a, ⟨i, by simp [T₁, hi']⟩))
    simp only [w] at this
    rw [restr_dotProduct] at this
    exact this
  have hQx : x ⬝ᵥ (Q *ᵥ x) ≤ -(r₁ + r₂) * (x ⬝ᵥ x) := by
    rw [quad_eq hQh, ← sum_coeff_sq hQh, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    by_cases hi : hQh.eigenvalues i ≤ -(r₁ + r₂)
    · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
    · rw [hx i hi]
      simp
  have hXx := quad_gt_of_inEigSpan hX h1 hx0
  have hXa : ∀ a, restr χ a x ⬝ᵥ (X *ᵥ restr χ a x) ≤
      r₁ * (restr χ a x ⬝ᵥ restr χ a x) := fun a ↦ quad_le_of_inEigSpan hX (h2 a)
  have hsum := sum_le_sum fun a (_ : a ∈ univ) ↦ hXa a
  rw [← mul_sum, sum_restr_dotProduct_self] at hsum
  rw [quad_remove χ hQ] at hQx
  nlinarith

/-! ### The planted graph -/

open Classical in
/-- `A_G / d` for the planted graph is `A_H / d` without the entries inside the color classes. -/
theorem adjDiv_plant (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (χ : Fin H.1 → Fin k)
    (u v : Fin H.1) :
    adjDiv (H.plant χ) d u v = if χ u = χ v then 0 else H.normAdj u v := by
  rw [H.normAdj_of_isRegularOfDegree hreg]
  unfold adjDiv
  by_cases h : χ u = χ v
  · simp [h, Graph.plant]
  · simp [h, Graph.plant]

open Classical in
/-- **Few eigenvalues of `A_G / d` are large in absolute value**: if at most `t₁` eigenvalues of the
host are at least `r₁` and at most `t₂` are at most `-r₂`, at most `(k + 1) (t₁ + t₂)` eigenvalues
of `A_G / d` are at least `r₁ + r₂` in absolute value. -/
theorem card_abs_ge_plant_le (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    (χ : Fin H.1 → Fin k) {r₁ r₂ : ℝ} {t₁ t₂ : ℕ}
    (ht₁ : (univ.filter fun i ↦ r₁ ≤ H.eig i).card ≤ t₁)
    (ht₂ : (univ.filter fun i ↦ H.eig i ≤ -r₂).card ≤ t₂) :
    (univ.filter fun i ↦ r₁ + r₂ ≤
        |(adjDiv_isHermitian (H.plant χ) d).eigenvalues i|).card ≤ (k + 1) * (t₁ + t₂) := by
  classical
  set hQh := adjDiv_isHermitian (H.plant χ) d
  have hQ := adjDiv_plant H hreg χ
  have htop : (univ.filter fun i ↦ r₁ + r₂ ≤ hQh.eigenvalues i).card ≤
      (univ.filter fun i ↦ r₁ ≤ H.eig i).card + k * (univ.filter fun i ↦ H.eig i ≤ -r₂).card :=
    card_ge_le_of_remove χ H.normAdj_isHermitian hQh hQ
  have hbot : (univ.filter fun i ↦ hQh.eigenvalues i ≤ -(r₁ + r₂)).card ≤
      k * (univ.filter fun i ↦ r₁ ≤ H.eig i).card + (univ.filter fun i ↦ H.eig i ≤ -r₂).card :=
    card_le_neg_le_of_remove χ H.normAdj_isHermitian hQh hQ
  have hsub : (univ.filter fun i ↦ r₁ + r₂ ≤ |hQh.eigenvalues i|) ⊆
      (univ.filter fun i ↦ r₁ + r₂ ≤ hQh.eigenvalues i) ∪
        univ.filter fun i ↦ hQh.eigenvalues i ≤ -(r₁ + r₂) := by
    intro i hi
    rw [mem_filter] at hi
    rw [mem_union, mem_filter, mem_filter]
    rcases le_abs'.1 hi.2 with h | h
    · exact Or.inr ⟨mem_univ _, h⟩
    · exact Or.inl ⟨mem_univ _, h⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have h1 : k * (univ.filter fun i ↦ H.eig i ≤ -r₂).card ≤ k * t₂ := Nat.mul_le_mul_left k ht₂
  have h2 : k * (univ.filter fun i ↦ r₁ ≤ H.eig i).card ≤ k * t₁ := Nat.mul_le_mul_left k ht₁
  nlinarith

end Planted

end BHSV25
