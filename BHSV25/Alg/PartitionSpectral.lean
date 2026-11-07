module

public import BHSV25.Spectral.Basic

/-!
# Spectral lemmas for recovering partitions

Facts about a symmetric real matrix `A` and its orthonormal eigenvectors `v_i` with eigenvalues
`μ_i` (Mathlib's `Matrix.IsHermitian.eigenvectorBasis`), used by the partition recovery of
[BHSV25, Theorem 5.1].

* `⟨v_i, v_j⟩ = [i = j]` and `μ_i = ⟨v_i, A v_i⟩`.
* **Eigenspace closeness** ([BHSV25, Lemmas 5.2 and 5.5], in the form used here,
  `BHSV25.Alg.dist_proj_le`): if `|μ| ≥ θ + η` with `η > 0`, the component of a vector `u` on the
  eigenvectors with `|μ_i| < θ` has squared norm at most `‖A u - μ u‖² / η²`. So an approximate
  eigenvector of `A` with eigenvalue `μ` is close to the span of the eigenvectors with `|μ_i| ≥ θ`.
* **Separation by large eigenvalues** ([BHSV25, Lemmas 5.3 and 5.7], in the form used here,
  `BHSV25.Alg.exists_coeff_sq_ge`): if all `|μ_i| ≤ 1`, `‖A x‖² ≥ α² > 0`, `‖x‖² ≤ K` and
  `τ² K ≤ α² / 2`, then some eigenvector with `|μ_i| ≥ τ` has `⟨v_i, x⟩² ≥ α² / (4 N)`, where `N` is
  the dimension. (The paper bounds `|μ_i|` by the norm of the model; for the symmetrized model of a
  regular graph the eigenvalues lie in `[-1, 1]`.)
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Matrix Finset Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

theorem dotProduct_eigenvectorBasis (hA : A.IsHermitian) (i j : ι) :
    ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis j) = if i = j then 1 else 0 := by
  have h := hA.eigenvectorBasis.inner_eq_ite i j
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

theorem coeff_single (hA : A.IsHermitian) (i a : ι) :
    coeff hA i (Pi.single a 1) = hA.eigenvectorBasis i a := by
  simp [coeff, dotProduct_single]

theorem eigenvalues_eq_dotProduct (hA : A.IsHermitian) (i : ι) :
    hA.eigenvalues i = ⇑(hA.eigenvectorBasis i) ⬝ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis i)) := by
  rw [hA.mulVec_eigenvectorBasis i, dotProduct_smul, dotProduct_eigenvectorBasis, ite_eq_left rfl,
    smul_eq_mul, mul_one]

theorem coeff_sub' (hA : A.IsHermitian) (i : ι) (x y : ι → ℝ) :
    coeff hA i (x - y) = coeff hA i x - coeff hA i y :=
  dotProduct_sub _ _ _

theorem coeff_smul' (hA : A.IsHermitian) (i : ι) (c : ℝ) (x : ι → ℝ) :
    coeff hA i (c • x) = c * coeff hA i x := by
  simp [coeff, dotProduct_smul]

/-- A projection onto a span of eigenvectors does not increase the norm. -/
theorem proj_dotProduct_le (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) :
    proj hA S x ⬝ᵥ proj hA S x ≤ x ⬝ᵥ x := by
  classical
  rw [← sum_coeff_sq hA (proj hA S x), ← sum_coeff_sq hA x]
  refine sum_le_sum fun i _ ↦ ?_
  rw [coeff_proj]
  split_ifs
  · exact le_rfl
  · rw [sq, zero_mul]
    exact sq_nonneg _

/-- **Eigenspace closeness**: if `|μ| ≥ θ + η` with `η > 0`, the component of `u` on the
eigenvectors with `|μ_i| < θ` has squared norm at most `‖A u - μ u‖² / η²`. -/
theorem dist_proj_le (hA : A.IsHermitian) {θ η μ : ℝ} (hη : 0 < η) (hμ : θ + η ≤ |μ|)
    (u : ι → ℝ) :
    η ^ 2 * ((u - proj hA (fun t ↦ θ ≤ |t|) u) ⬝ᵥ (u - proj hA (fun t ↦ θ ≤ |t|) u)) ≤
      (A *ᵥ u - μ • u) ⬝ᵥ (A *ᵥ u - μ • u) := by
  classical
  rw [← sum_coeff_sq hA (u - proj hA _ u), ← sum_coeff_sq hA (A *ᵥ u - μ • u), mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  rw [coeff_sub', coeff_proj, coeff_sub', coeff_mulVec, coeff_smul']
  split_ifs with h
  · rw [sub_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact sq_nonneg _
  · rw [sub_zero, ← sub_mul, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h1 : η ≤ |hA.eigenvalues i - μ| := by
      have := abs_sub_abs_le_abs_sub μ (hA.eigenvalues i)
      rw [abs_sub_comm] at this
      push Not at h
      linarith
    calc η ^ 2 ≤ |hA.eigenvalues i - μ| ^ 2 := pow_le_pow_left₀ hη.le h1 2
      _ = (hA.eigenvalues i - μ) ^ 2 := sq_abs _

/-- **Separation by large eigenvalues**: if all `|μ_i| ≤ 1`, `‖A x‖² ≥ α² > 0`, `‖x‖² ≤ K` and
`τ² K ≤ α² / 2`, then some eigenvector with `|μ_i| ≥ τ` has `⟨v_i, x⟩² ≥ α² / (4 N)`. -/
theorem exists_coeff_sq_ge (hA : A.IsHermitian) (habs : ∀ i, |hA.eigenvalues i| ≤ 1)
    {x : ι → ℝ} {α τ K : ℝ} (hα : 0 < α) (hAx : α ^ 2 ≤ (A *ᵥ x) ⬝ᵥ (A *ᵥ x))
    (hx : x ⬝ᵥ x ≤ K) (hτ : τ ^ 2 * K ≤ α ^ 2 / 2) :
    ∃ i, τ ≤ |hA.eigenvalues i| ∧ α ^ 2 / (4 * Fintype.card ι) ≤ coeff hA i x ^ 2 := by
  classical
  by_contra hcon
  push Not at hcon
  have hN : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hterm : ∀ i, hA.eigenvalues i ^ 2 * coeff hA i x ^ 2 ≤
      α ^ 2 / (4 * Fintype.card ι) + τ ^ 2 * coeff hA i x ^ 2 := by
    intro i
    have hc := sq_nonneg (coeff hA i x)
    have hsq : hA.eigenvalues i ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) (habs i)
    by_cases hbig : τ ≤ |hA.eigenvalues i|
    · have h1 := (hcon i hbig).le
      have h2 : hA.eigenvalues i ^ 2 * coeff hA i x ^ 2 ≤ coeff hA i x ^ 2 := by nlinarith
      nlinarith [sq_nonneg τ]
    · push Not at hbig
      have h3 : hA.eigenvalues i ^ 2 ≤ τ ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hbig.le 2
      have : 0 ≤ α ^ 2 / (4 * Fintype.card ι) := by positivity
      nlinarith
  have hsum : (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i ^ 2 * coeff hA i x ^ 2 := by
    rw [← sum_coeff_sq hA (A *ᵥ x)]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [coeff_mulVec, mul_pow]
  have hbound : ∑ i, hA.eigenvalues i ^ 2 * coeff hA i x ^ 2 ≤ α ^ 2 / 4 + τ ^ 2 * K := by
    calc ∑ i, hA.eigenvalues i ^ 2 * coeff hA i x ^ 2
        ≤ ∑ i, (α ^ 2 / (4 * Fintype.card ι) + τ ^ 2 * coeff hA i x ^ 2) :=
          sum_le_sum fun i _ ↦ hterm i
      _ = Fintype.card ι * (α ^ 2 / (4 * Fintype.card ι)) + τ ^ 2 * (x ⬝ᵥ x) := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, sum_coeff_sq]
      _ ≤ α ^ 2 / 4 + τ ^ 2 * K := by
          have hτK : τ ^ 2 * (x ⬝ᵥ x) ≤ τ ^ 2 * K := mul_le_mul_of_nonneg_left hx (sq_nonneg τ)
          have hN4 : (Fintype.card ι : ℝ) * (α ^ 2 / (4 * Fintype.card ι)) ≤ α ^ 2 / 4 := by
            rcases hN.lt_or_eq with hpos | h0
            · apply le_of_eq
              field_simp
            · rw [← h0, zero_mul]
              positivity
          linarith
  have : α ^ 2 ≤ α ^ 2 / 4 + α ^ 2 / 2 := by linarith
  nlinarith [sq_pos_of_pos hα]

end Alg

end BHSV25
