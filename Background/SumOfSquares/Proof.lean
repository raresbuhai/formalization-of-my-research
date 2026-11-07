module

public import Background.SumOfSquares.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sum-of-squares proofs

A *system* is a list of polynomials `f₀, …, fₘ₋₁`, read as the constraints `fᵢ ≥ 0`. An equality
`h = 0` is written, as in [BKS23], as the two constraints `h ≥ 0` and `-h ≥ 0`.

A degree-`k` *sum-of-squares proof* that `A` implies `g ≥ 0` [BKS23, §3.1 and Definition 3.5] is a
family of sum-of-squares polynomials `p S`, one for each set `S` of constraints, such that
`g = ∑ S, p S * ∏ i ∈ S, fᵢ` and `deg (p S) + ∑ i ∈ S, deg fᵢ ≤ k` for every nonzero `p S`.

* `SoS.Proof A g k`: such a proof, as data.
* `A ⊢[k] g`: such a proof exists.
* `A ⊢[k, B] g`: such a proof exists with bit complexity at most `B`: every coefficient of the
  constraints, of `g` and of the multipliers is at most `2^B` in absolute value [RW17]. [BKS23,
  Definition 3.5] instead counts the bits of rational coefficients; that count bounds the
  logarithm of every coefficient, so the paper's bounds imply these.
* `A.Entails B k`: every constraint of the system `B` has a degree-`k` proof from `A`.

The indeterminates of a proof are the variables `σ` of its polynomials. A fact stated for
indeterminates, such as `(∑ fᵢ)²ᵗ ≤ r²ᵗ⁻¹ ∑ fᵢ²ᵗ`, is a proof in the variables `fᵢ`; it is used
by substituting polynomials for them.
-/

@[expose] public section

namespace SoS

open MvPolynomial

variable {σ K : Type*} [Field K] [Algebra K ℝ]

/-- A system of polynomial constraints: each polynomial `f` in the list is the constraint
`f ≥ 0`. -/
abbrev System (σ K : Type*) [CommSemiring K] := List (MvPolynomial σ K)

namespace System

variable (A : System σ K)

/-- The product `∏ i ∈ S, fᵢ` of the constraints in `S`. -/
noncomputable def prod (S : Finset (Fin A.length)) : MvPolynomial σ K :=
  ∏ i ∈ S, A.get i

/-- The sum `∑ i ∈ S, deg fᵢ` of the degrees of the constraints in `S`. -/
def degree (S : Finset (Fin A.length)) : ℕ :=
  ∑ i ∈ S, (A.get i).totalDegree

end System

/-- A degree-`k` sum-of-squares proof that the constraints `A` imply `g ≥ 0`. -/
structure Proof (A : System σ K) (g : MvPolynomial σ K) (k : ℕ) where
  /-- The multiplier `p S` of the product of the constraints in `S`. -/
  mult : Finset (Fin A.length) → MvPolynomial σ K
  /-- Every multiplier is a sum of squares. -/
  isSOS_mult : ∀ S, IsSOS (mult S)
  /-- `deg (p S) + ∑ i ∈ S, deg fᵢ ≤ k` for every nonzero multiplier. (A zero multiplier
  contributes nothing, whatever the degree of the product of its constraints.) -/
  degree_le : ∀ S, mult S ≠ 0 → (mult S).totalDegree + A.degree S ≤ k
  /-- `g = ∑ S, p S * ∏ i ∈ S, fᵢ`. -/
  eq_sum : g = ∑ S, mult S * A.prod S

/-- There is a degree-`k` sum-of-squares proof that the constraints `A` imply `g ≥ 0`. -/
def Derives (A : System σ K) (k : ℕ) (g : MvPolynomial σ K) : Prop :=
  Nonempty (Proof A g k)

/-- The proof has bit complexity at most `B`: every coefficient of the constraints, of `g` and of
the multipliers is at most `2^B` in absolute value. -/
def Proof.BitComplexityLE {A : System σ K} {g : MvPolynomial σ K} {k : ℕ} (P : Proof A g k)
    (B : ℝ) : Prop :=
  (∀ f ∈ A, CoeffsLE f (2 ^ B)) ∧ CoeffsLE g (2 ^ B) ∧ ∀ S, CoeffsLE (P.mult S) (2 ^ B)

/-- There is a degree-`k` sum-of-squares proof that `A` implies `g ≥ 0` with bit complexity at
most `B`. -/
def DerivesWithin (A : System σ K) (k : ℕ) (B : ℝ) (g : MvPolynomial σ K) : Prop :=
  ∃ P : Proof A g k, P.BitComplexityLE B

/-- Every constraint of the system `B` has a degree-`k` sum-of-squares proof from `A`. -/
def System.Entails (A B : System σ K) (k : ℕ) : Prop :=
  ∀ g ∈ B, Derives A k g

@[inherit_doc] scoped notation:50 A:51 " ⊢[" k "] " g:51 => SoS.Derives A k g

@[inherit_doc] scoped notation:50 A:51 " ⊢[" k ", " B "] " g:51 => SoS.DerivesWithin A k B g

end SoS
