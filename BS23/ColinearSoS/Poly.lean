module

public import BS23.Separating.MomentClose
public import BS23.Colinear.Direction

/-!
# Directional moment polynomials

The polynomials in the direction `v ∈ ℝ^d` that the analysis of the sum-of-squares algorithm for
[BS23, Theorem 1.2] compares (with `lin u = ∑ᵢ uᵢ vᵢ`, `BS23.Separating.lin`):

* `BS23.ColinearSoS.quadPoly S = vᵀ S v`;
* `BS23.ColinearSoS.empPoly X r = (1/n) ∑ⱼ ⟨X j, v⟩^r`, the empirical moment polynomial of the
  points `X`;
* `BS23.ColinearSoS.popPoly w a u S r = ∑_c w_c hmom r (a_c ⟨u, v⟩) (vᵀ S v)`, the moment
  polynomial of the mixture `∑_c w_c N(a_c u, S)`: its value at `v` is `E ⟨x, v⟩^r` for `x` drawn
  from that mixture.

Their values at a point: `BS23.ColinearSoS.eval_quadPoly`, `BS23.ColinearSoS.eval_lin`,
`BS23.ColinearSoS.eval_empPoly`, `BS23.ColinearSoS.eval_popPoly`.
-/

@[expose] public section

namespace BS23.ColinearSoS

open MvPolynomial

variable {k d n : ℕ}

/-- The quadratic form `vᵀ S v` as a polynomial. -/
noncomputable def quadPoly (S : Matrix (Fin d) (Fin d) ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ a, ∑ b, C (S a b) * X a * X b

/-- The empirical moment polynomial `(1/n) ∑ⱼ ⟨X j, v⟩^r`. -/
noncomputable def empPoly (X : Fin n → Fin d → ℝ) (r : ℕ) : MvPolynomial (Fin d) ℝ :=
  (n : ℝ)⁻¹ • ∑ j, Separating.lin (X j) ^ r

/-- The moment polynomial `∑_c w_c hmom r (a_c ⟨u, v⟩) (vᵀ S v)` of the mixture
`∑_c w_c N(a_c u, S)`. -/
noncomputable def popPoly (w a : Fin k → ℝ) (u : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (r : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ c, C (w c) * hmom r (C (a c) * Separating.lin u) (quadPoly S)

theorem eval_lin (u v : Fin d → ℝ) : eval v (Separating.lin u) = u ⬝ᵥ v := by
  simp [Separating.lin, dotProduct]

theorem eval_quadPoly (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    eval v (quadPoly S) = Colinear.quad S v := by
  simp only [quadPoly, map_sum, map_mul, eval_C, eval_X, Colinear.quad, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

theorem eval_empPoly (X : Fin n → Fin d → ℝ) (r : ℕ) (v : Fin d → ℝ) :
    eval v (empPoly X r) = (n : ℝ)⁻¹ * ∑ j, (X j ⬝ᵥ v) ^ r := by
  simp only [empPoly, smul_eq_C_mul, map_mul, eval_C, map_sum, map_pow]
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by rw [eval_lin]

/-- A ring homomorphism commutes with `hmom`. -/
theorem map_hmom' {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (r : ℕ) (a v : K) :
    f (hmom r a v) = hmom r (f a) (f v) := by
  simp [hmom, map_sum, map_mul, map_pow, map_natCast]

theorem eval_popPoly (w a : Fin k → ℝ) (u : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) (r : ℕ)
    (v : Fin d → ℝ) :
    eval v (popPoly w a u S r) = ∑ c, w c * hmom r (a c * (u ⬝ᵥ v)) (Colinear.quad S v) := by
  simp only [popPoly, map_sum, map_mul, eval_C]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [show eval v (hmom r (C (a c) * Separating.lin u) (quadPoly S)) =
      (eval v) (hmom r (C (a c) * Separating.lin u) (quadPoly S)) from rfl, map_hmom',
    map_mul, eval_C, eval_lin, eval_quadPoly]

end BS23.ColinearSoS
