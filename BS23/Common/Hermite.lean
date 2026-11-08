module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Basic

/-!
# Hermite polynomials with a variance parameter

`BS23.hermite m x q` is the probabilists' Hermite polynomial of degree `m` for the variance `q`,
`∑_{i ≤ m/2} (-1)^i C(m, 2i) (2i-1)‼ x^(m-2i) q^i`; its generating function is
`exp (λ x - λ² q / 2)`, and `hermite m x 1` is the usual `He_m x`.

`BS23.hmom r a v = ∑_{i ≤ r/2} C(r, 2i) (2i-1)‼ a^(r-2i) v^i` is the `r`-th moment of a Gaussian
with mean `a` and variance `v` (`E (a + √v Z)^r`), written out as a polynomial; note
`hermite m x q = hmom m x (-q)`.

Both are defined over any commutative ring, so that the algorithms can evaluate them on rationals
and the analysis on reals.
-/

@[expose] public section

namespace BS23

/-- The coefficient `C(m, 2i) (2i-1)‼ = m! / (i! (m-2i)! 2^i)`. -/
def hermCoeff (m i : ℕ) : ℕ := m.choose (2 * i) * Nat.doubleFactorial (2 * i - 1)

variable {K : Type*} [CommRing K]

/-- The Hermite polynomial of degree `m` for the variance `q`, evaluated at `x`. -/
def hermite (m : ℕ) (x q : K) : K :=
  ∑ i ∈ Finset.range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : K) * x ^ (m - 2 * i) * q ^ i

/-- The `r`-th moment of a Gaussian of mean `a` and variance `v`, as a polynomial in `a, v`. -/
def hmom (r : ℕ) (a v : K) : K :=
  ∑ i ∈ Finset.range (r / 2 + 1), (hermCoeff r i : K) * a ^ (r - 2 * i) * v ^ i

end BS23
