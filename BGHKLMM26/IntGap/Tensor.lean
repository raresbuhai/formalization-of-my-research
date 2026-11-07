module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order

/-!
# Tensor powers and Gram vectors

Two pieces of linear algebra for the SDP solution of Theorem 1.4.

* `BGHKLMM26.IntGap.tpow s v`: the `s`-th tensor power of `v ∈ ℝ^I`, a vector of `ℝ^(Fin s → I)`
  with `⟪tpow s v, tpow s w⟫ = ⟪v, w⟫ ^ s` (`BGHKLMM26.IntGap.inner_tpow`).
* `BGHKLMM26.IntGap.exists_gram_vectors`: a positive semidefinite `n × n` matrix is the Gram matrix
  of `n` vectors of `ℝⁿ` (the columns of a factor `M = Aᴴ A`).
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open scoped RealInnerProductSpace

variable {I : Type} [Fintype I]

/-- The `s`-th tensor power of a vector: the coordinate at `ι : Fin s → I` is `∏ₘ v (ι m)`. -/
noncomputable def tpow (s : ℕ) (v : EuclideanSpace ℝ I) : EuclideanSpace ℝ (Fin s → I) :=
  WithLp.toLp 2 fun ι ↦ ∏ m, v (ι m)

/-- **Inner products of tensor powers** are powers of inner products. -/
theorem inner_tpow (s : ℕ) (v w : EuclideanSpace ℝ I) :
    ⟪tpow s v, tpow s w⟫ = ⟪v, w⟫ ^ s := by
  simp only [tpow, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ← Finset.prod_mul_distrib]
  rw [← Fin.prod_const, Fintype.prod_sum]

open scoped MatrixOrder in
/-- **Gram vectors**: a positive semidefinite real `n × n` matrix is the Gram matrix of `n` vectors
of `ℝⁿ`. -/
theorem exists_gram_vectors {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n), ∀ i j, ⟪v i, v j⟫ = M i j := by
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  refine ⟨fun i ↦ WithLp.toLp 2 fun k ↦ a k i, fun i j ↦ ?_⟩
  simp [PiLp.inner_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose, mul_comm]

end BGHKLMM26.IntGap
