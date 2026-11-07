module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.Analysis.Real.Sqrt

/-!
# Polynomials, sums of squares and coefficient sizes

Notions used throughout the library. Polynomials have coefficients in a field `K` that sits inside
`ℝ`: usually `ℝ` itself, or `ℚ` for the input of an algorithm.

* `SoS.toReal p`: `p` as a real polynomial.
* `SoS.IsSOS p`: `p` is a sum of squares of real polynomials.
* `SoS.CoeffsLE p M`: every coefficient of `p` is at most `M` in absolute value. The bit
  complexity of sum-of-squares proofs is measured this way, as in [RW17]: a proof has bit
  complexity at most `B` when all its coefficients are at most `2^B` in absolute value. This is
  what approximate soundness needs. Rationality and bit lengths only matter for the input and
  output of algorithms.
* `SoS.coeffNorm p`: the Euclidean norm `‖p‖₂` of the coefficient vector of a real polynomial.

References:
* [BKS23] R.-D. Buhai, P. K. Kothari, D. Steurer, *Algorithms approaching the threshold for
  semi-random planted clique*, STOC 2023, arXiv:2212.05619. Section 3.1.
* [RW17] P. Raghavendra, B. Weitz, *On the bit complexity of sum-of-squares proofs*, ICALP 2017,
  arXiv:1702.05139.
-/

@[expose] public section

namespace SoS

open MvPolynomial

variable {σ K : Type*} [Field K] [Algebra K ℝ]

/-- A polynomial with coefficients in `K` as a real polynomial. -/
noncomputable def toReal (p : MvPolynomial σ K) : MvPolynomial σ ℝ :=
  map (algebraMap K ℝ) p

/-- `p` is a sum of squares of real polynomials. -/
def IsSOS (p : MvPolynomial σ K) : Prop :=
  IsSumSq (toReal p)

/-- Every coefficient of `p` is at most `M` in absolute value. -/
def CoeffsLE (p : MvPolynomial σ K) (M : ℝ) : Prop :=
  ∀ m, |algebraMap K ℝ (p.coeff m)| ≤ M

/-- The Euclidean norm of the coefficient vector of a real polynomial. -/
noncomputable def coeffNorm (p : MvPolynomial σ ℝ) : ℝ :=
  Real.sqrt (∑ m ∈ p.support, p.coeff m ^ 2)

end SoS
