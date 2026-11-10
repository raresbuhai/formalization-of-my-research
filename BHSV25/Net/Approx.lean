module

public import BHSV25.Spectral.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Coefficients in an eigenbasis

Facts about the coefficients `cᵢ(x) = uᵢ ⬝ x` of vectors on the orthonormal eigenvectors `uᵢ` of a
symmetric matrix `A`, used by the greedy net (`BHSV25/Net/GSCorrect.lean`): linearity, the
coefficients of the eigenvectors, powers of a filter (`BHSV25.Net.coeff_pow_mulVec`: if `B`
multiplies the `i`-th coefficient by `c`, then `B^k` multiplies it by `c^k`), and the preimage
`x = ∑ᵢ (cᵢ(w) / φᵢ) uᵢ` of a vector `w` under a filter acting on the eigenbasis by numbers `φᵢ`
(`BHSV25.Net.preimage`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix Spectral

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-! ### Coefficients are linear -/

theorem coeff_sub (hA : A.IsHermitian) (i : Fin n) (x y : Fin n → ℝ) :
    coeff hA i (x - y) = coeff hA i x - coeff hA i y := by
  simp only [coeff, dotProduct_sub]

theorem coeff_smul (hA : A.IsHermitian) (i : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    coeff hA i (c • x) = c * coeff hA i x := by
  simp only [coeff, dotProduct_smul, smul_eq_mul]

theorem coeff_sum (hA : A.IsHermitian) (i : Fin n) {κ : Type*} (s : Finset κ)
    (x : κ → Fin n → ℝ) : coeff hA i (∑ j ∈ s, x j) = ∑ j ∈ s, coeff hA i (x j) := by
  simp only [coeff, dotProduct_sum]

/-- The eigenvectors are orthonormal. -/
theorem coeff_eigenvector (hA : A.IsHermitian) (l i : Fin n) :
    coeff hA l ⇑(hA.eigenvectorBasis i) = if l = i then 1 else 0 := by
  have h := orthonormal_iff_ite.1 hA.eigenvectorBasis.orthonormal l i
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [coeff, dotProduct_comm]
  simpa using h

/-- **Powers of a filter**: if `B` multiplies the `i`-th coefficient by `c`, then `B^k`
multiplies it by `c^k`. -/
theorem coeff_pow_mulVec (hA : A.IsHermitian) {B : Matrix (Fin n) (Fin n) ℝ} {i : Fin n} {c : ℝ}
    (hB : ∀ x, coeff hA i (B *ᵥ x) = c * coeff hA i x) (k : ℕ) (x : Fin n → ℝ) :
    coeff hA i ((B ^ k) *ᵥ x) = c ^ k * coeff hA i x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, hB, pow_succ]
    ring

/-! ### Sparse vectors -/

/-! ### The approximation -/

/-- The vector with coefficients `cᵢ(w) / φᵢ` in the eigenbasis. -/
noncomputable def preimage (hA : A.IsHermitian) (φ : Fin n → ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, (coeff hA i w / φ i) • ⇑(hA.eigenvectorBasis i)

theorem coeff_preimage (hA : A.IsHermitian) (φ : Fin n → ℝ) (w : Fin n → ℝ) (l : Fin n) :
    coeff hA l (preimage hA φ w) = coeff hA l w / φ l := by
  classical
  rw [preimage, coeff_sum]
  simp only [coeff_smul, coeff_eigenvector, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

end Net

end BHSV25
