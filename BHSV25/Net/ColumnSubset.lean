module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Column subset selection

Among finitely many vectors `m 0, …, m (n - 1)` of `ℝ^ι`, some `k ≤ |ι|` of them span all the
others with coefficients at most `1` in absolute value (`BHSV25.Net.exists_column_subset`).

The proof takes `k` as the largest size of a linearly independent subfamily and, among the
families of `k` vectors, one whose Gram determinant is largest in absolute value. Replacing its
`j`-th vector by `m u = ∑ αₗ m (g l)` multiplies the Gram matrix by the matrix `E` on both sides,
the identity with its `j`-th column replaced by `α`, so the Gram determinant gets multiplied by
`(det E)² = α_j²`; maximality gives `|α_j| ≤ 1`. (This is the argument behind Auerbach's lemma.)
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The matrix whose columns are the vectors `m (g 0), …, m (g (k - 1))`. -/
def colMat {k : ℕ} (m : Fin n → ι → ℝ) (g : Fin k → Fin n) : Matrix ι (Fin k) ℝ :=
  Matrix.of fun i a ↦ m (g a) i

/-- The Gram matrix of the vectors `m (g 0), …, m (g (k - 1))`. -/
def gram {k : ℕ} (m : Fin n → ι → ℝ) (g : Fin k → Fin n) : Matrix (Fin k) (Fin k) ℝ :=
  (colMat m g)ᵀ * colMat m g

omit [Fintype ι] in
theorem colMat_mulVec {k : ℕ} (m : Fin n → ι → ℝ) (g : Fin k → Fin n) (c : Fin k → ℝ) :
    colMat m g *ᵥ c = ∑ a, c a • m (g a) := by
  ext i
  simp only [mulVec, dotProduct, colMat, of_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm]

/-- If `Mᵀ M c = 0` then `M c = 0`. -/
theorem mulVec_eq_zero_of_transpose_mul {k : ℕ} (M : Matrix ι (Fin k) ℝ) {c : Fin k → ℝ}
    (h : (Mᵀ * M) *ᵥ c = 0) : M *ᵥ c = 0 := by
  have h1 : (M *ᵥ c) ⬝ᵥ (M *ᵥ c) = 0 := by
    have h2 : c ⬝ᵥ ((Mᵀ * M) *ᵥ c) = 0 := by rw [h, dotProduct_zero]
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at h2
    exact h2
  exact dotProduct_self_eq_zero.1 h1

theorem gram_det_ne_zero {k : ℕ} {m : Fin n → ι → ℝ} {g : Fin k → Fin n}
    (h : LinearIndependent ℝ (m ∘ g)) : (gram m g).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc, hzero⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have h0 : colMat m g *ᵥ c = 0 := mulVec_eq_zero_of_transpose_mul _ hzero
  rw [colMat_mulVec] at h0
  exact hc (funext (Fintype.linearIndependent_iff.1 h c h0))

theorem linearIndependent_of_gram_det_ne_zero {k : ℕ} {m : Fin n → ι → ℝ} {g : Fin k → Fin n}
    (h : (gram m g).det ≠ 0) : LinearIndependent ℝ (m ∘ g) := by
  refine Fintype.linearIndependent_iff.2 fun c hc ↦ ?_
  by_contra hne
  push Not at hne
  obtain ⟨a, ha⟩ := hne
  have hc0 : c ≠ 0 := fun h0 ↦ ha (by rw [h0]; rfl)
  have hM : colMat m g *ᵥ c = 0 := by rw [colMat_mulVec]; exact hc
  have : (gram m g) *ᵥ c = 0 := by rw [gram, ← mulVec_mulVec, hM, mulVec_zero]
  exact h (Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, this⟩)

/-- The determinant of the identity with one column replaced by `c` is the entry of `c` on the
diagonal. -/
theorem det_updateCol_one {k : ℕ} (j : Fin k) (c : Fin k → ℝ) :
    ((1 : Matrix (Fin k) (Fin k) ℝ).updateCol j c).det = c j := by
  rw [← cramer_apply, cramer_one]
  rfl

/-- **Replacing one vector** of a family by a combination of the family multiplies the Gram
determinant by the square of the coefficient of the replaced vector. -/
theorem gram_det_update {k : ℕ} (m : Fin n → ι → ℝ) (g : Fin k → Fin n) (u : Fin n) (j : Fin k)
    (α : Fin k → ℝ) (hu : m u = ∑ l, α l • m (g l)) :
    (gram m (Function.update g j u)).det = α j ^ 2 * (gram m g).det := by
  classical
  set E : Matrix (Fin k) (Fin k) ℝ := (1 : Matrix (Fin k) (Fin k) ℝ).updateCol j α
  have hcol : colMat m (Function.update g j u) = colMat m g * E := by
    ext i a
    rw [Matrix.mul_apply]
    simp only [colMat, of_apply, E, updateCol_apply]
    by_cases ha : a = j
    · subst ha
      simp only [Function.update_self, ite_true, hu, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul, mul_comm]
    · simp only [Function.update_of_ne ha, ha, ite_false, Matrix.one_apply, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hdet : E.det = α j := det_updateCol_one j α
  have hG : gram m (Function.update g j u) = Eᵀ * gram m g * E := by
    rw [gram, gram, hcol, transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [hG, det_mul, det_mul, det_transpose, hdet]
  ring

/-- **Column subset selection.** Among `n` vectors of `ℝ^ι`, some `k ≤ |ι|` of them,
`m (g 0), …, m (g (k - 1))`, span all the others with coefficients at most `1` in absolute
value. -/
theorem exists_column_subset (m : Fin n → ι → ℝ) :
    ∃ k ≤ Fintype.card ι, ∃ g : Fin k → Fin n, ∃ α : Fin n → Fin k → ℝ,
      (∀ u, m u = ∑ j, α u j • m (g j)) ∧ ∀ u j, |α u j| ≤ 1 := by
  classical
  let Pk : ℕ → Prop := fun k ↦ ∃ g : Fin k → Fin n, LinearIndependent ℝ (m ∘ g)
  set k := Nat.findGreatest Pk (Fintype.card ι) with hkdef
  have hk : Pk k :=
    Nat.findGreatest_spec (m := 0) (Nat.zero_le _) ⟨Fin.elim0, linearIndependent_empty_type⟩
  have hkle : k ≤ Fintype.card ι := Nat.findGreatest_le _
  obtain ⟨g₀, hg₀⟩ := hk
  obtain ⟨g, -, hg⟩ := Finset.exists_max_image Finset.univ
    (fun g : Fin k → Fin n ↦ |(gram m g).det|) ⟨g₀, Finset.mem_univ _⟩
  have hpos : 0 < |(gram m g).det| :=
    lt_of_lt_of_le (abs_pos.2 (gram_det_ne_zero hg₀)) (hg g₀ (Finset.mem_univ _))
  have hgLI : LinearIndependent ℝ (m ∘ g) :=
    linearIndependent_of_gram_det_ne_zero (abs_pos.1 hpos)
  have hspan : ∀ u, m u ∈ Submodule.span ℝ (Set.range (m ∘ g)) := by
    intro u
    by_contra h
    have hLI : LinearIndependent ℝ (Fin.cons (m u) (m ∘ g) : Fin (k + 1) → ι → ℝ) :=
      linearIndependent_finCons.2 ⟨hgLI, h⟩
    have h1 : k + 1 ≤ Fintype.card ι := by
      have := hLI.fintype_card_le_finrank
      simpa using this
    have h2 : Pk (k + 1) := by
      refine ⟨Fin.cons u g, ?_⟩
      convert hLI using 1
      ext j : 1
      refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
    have := Nat.le_findGreatest h1 h2
    omega
  choose α hα using fun u ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan u)
  refine ⟨k, hkle, g, α, fun u ↦ (hα u).symm, fun u j ↦ ?_⟩
  have hrep := gram_det_update m g u j (α u) (hα u).symm
  have hle := hg (Function.update g j u) (Finset.mem_univ _)
  rw [hrep, abs_mul, abs_of_nonneg (sq_nonneg _)] at hle
  have h1 : α u j ^ 2 ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon hpos
    linarith
  have h2 : |α u j| ^ 2 ≤ 1 := by rw [sq_abs]; exact h1
  nlinarith [abs_nonneg (α u j)]

/-- **Column subset selection with exactly `T` columns**, for `T ≥ |ι|` and `n > 0`: the family
of `exists_column_subset`, padded with copies of the vector `m 0` that get coefficient `0`. -/
theorem exists_column_subset_fin (m : Fin n → ι → ℝ) {T : ℕ} (hT : Fintype.card ι ≤ T)
    (hn : 0 < n) :
    ∃ g : Fin T → Fin n, ∃ α : Fin n → Fin T → ℝ,
      (∀ u, m u = ∑ j, α u j • m (g j)) ∧ ∀ u j, |α u j| ≤ 1 := by
  obtain ⟨k, hk, g, α, hα, hα1⟩ := exists_column_subset m
  have hkT : k ≤ T := hk.trans hT
  refine ⟨fun j ↦ if h : (j : ℕ) < k then g ⟨j, h⟩ else ⟨0, hn⟩,
    fun u j ↦ if h : (j : ℕ) < k then α u ⟨j, h⟩ else 0, fun u ↦ ?_, fun u j ↦ ?_⟩
  · rw [hα u]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb hkT))),
      Finset.sum_map]
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp [Fin.castLEEmb, j.2]
    · intro j _ hj
      have : ¬ (j : ℕ) < k := by
        intro h
        exact hj (Finset.mem_map.2 ⟨⟨j, h⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      simp [this]
  · change |(if h : (j : ℕ) < k then α u ⟨j, h⟩ else 0)| ≤ 1
    split_ifs
    · exact hα1 _ _
    · simp

end Net

end BHSV25
