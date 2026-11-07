module

public import Background.SumOfSquares.PseudoExpectation
public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# The sum-of-squares algorithm

The specification of the algorithm that finds pseudo-distributions, [BKS23, Fact 3.6], stated
for multitape Turing machines (CSLib's `Turing.MultiTapeTM.ComputableInTimeAndSpace`). The theorem,
`SoS.Solver.exists_solver`, is stated and proved in
`Background/SumOfSquares/Algorithm/Correct.lean`, after the algorithm; algorithms built on the
sum-of-squares method use it from there.

## What it computes

The input is a problem `(n, ℓ, A, (q₀, [q₁, …, qₛ]))` and accuracies `η, γ > 0`. The problem
asks for a degree-`ℓ` pseudo-expectation `Ẽ` in `n` variables that satisfies the constraints
`f ≥ 0` (`f ∈ A`) and minimizes `Ẽ[q₀] + ∑ⱼ Ẽ[qⱼ]²`. This objective covers linear objectives
(only `q₀`) and objectives like `‖Ẽ[x]‖²` used by list-decoding algorithms such as [BKS23,
Algorithm 5.2]. The output is the pseudo-moments `Ẽ[xᵅ]`, `|α| ≤ ℓ`, as the rational polynomial
`∑ α, Ẽ[xᵅ] xᵅ`.

The guarantee (`SoS.Solver.Correct`): the output is the pseudo-moments of an exact degree-`ℓ`
pseudo-expectation that

* satisfies the constraints `(η + γ)`-approximately, at degree `0` (the paper's "satisfies `A`
  `η`-approximately", `SoS.PseudoExpectation.ApproxSatisfies`), and
* has objective at most `γ` more than every pseudo-expectation that satisfies them
  `η`-approximately.

The two accuracies make approximate optimality usable. A convex combination of the output with a
true solution satisfies the constraints `(1 - λ)(η + γ)`-approximately, which is at most `η` when
`λ ≥ γ / (η + γ)`; so it is a valid competitor, as arguments like [BKS23, Lemma 5.3] need.

## On which problems

`SoS.Solver.Problem.Valid`: `ℓ` is even and at least `2`, the objective has degree at most `ℓ`,
the constraints are satisfied by some real point, and one of them is an explicit bound
`B - ∑ i, xᵢ² ≥ 0` (the paper's "explicitly bounded"). Without such conditions the objective can be
unbounded below on the competitors, and no output is correct.

## Running time

`(|P| + 2)^(C (ℓ + 1)) (|η, γ| + 2)^C`, where `|P|` and `|η, γ|` are the encoded lengths of the
problem and of the accuracies: `n^O(ℓ)`, polynomial in the bits of the problem, and
polylogarithmic in `1/η` and `1/γ`. [BKS23, Fact 3.6] states `(n + m)^O(ℓ) polylog(1/η)` and
omits the bits of the problem.

## Encodings

Polynomials are lists of terms (`SoS.Solver.RawPoly`), with no canonical form; their meaning is
`SoS.Solver.RawPoly.toPoly`. Numbers and lists use `Background/Encoding.lean`.
-/

@[expose] public section

namespace SoS.Solver

open MvPolynomial Encoding

/-- A polynomial with rational coefficients, as a list of terms `(e, c)`: `c` times the monomial
with exponent `e[i]` on the variable `i`. Missing exponents are `0`, exponents past the number of
variables are ignored, and a monomial may appear in several terms. -/
abbrev RawPoly := List (List ℕ × ℚ)

def encRawPoly : RawPoly ↪ List Bool := encList (encPair (encList encNat) encRat)

/-- The polynomial in the variables `Fin n` that a list of terms stands for. -/
noncomputable def RawPoly.toPoly (n : ℕ) (p : RawPoly) : MvPolynomial (Fin n) ℚ :=
  (p.map fun t ↦ C t.2 * ∏ i : Fin n, X i ^ t.1.getD i 0).sum

/-- A problem `(n, ℓ, A, (q₀, [q₁, …, qₛ]))`: the number of variables, the degree, the constraints
`f ≥ 0` for `f ∈ A`, and the objective `Ẽ[q₀] + ∑ⱼ Ẽ[qⱼ]²` to minimize. -/
abbrev Problem := ℕ × ℕ × List RawPoly × (RawPoly × List RawPoly)

def encProblem : Problem ↪ List Bool :=
  encPair encNat
    (encPair encNat (encPair (encList encRawPoly) (encPair encRawPoly (encList encRawPoly))))

/-- An input: a problem and the accuracies `(η, γ)`. -/
abbrev Input := Problem × (ℚ × ℚ)

def encInput : Input ↪ List Bool := encPair encProblem (encPair encRat encRat)

/-- An output: the pseudo-moments, as the polynomial `∑ α, Ẽ[xᵅ] xᵅ`. -/
abbrev Output := RawPoly

def encOutput : Output ↪ List Bool := encRawPoly

namespace Problem

variable (P : Problem)

/-- The number of variables. -/
abbrev numVars : ℕ := P.1

/-- The degree. -/
abbrev degree : ℕ := P.2.1

/-- The constraints, as a system. -/
noncomputable def system : System (Fin P.numVars) ℚ := P.2.2.1.map (RawPoly.toPoly P.numVars)

/-- The objective `Ẽ[q₀] + ∑ⱼ Ẽ[qⱼ]²` at a pseudo-expectation `Ẽ`. -/
noncomputable def objective {ℓ : ℕ} (E : PseudoExpectation (Fin P.numVars) ℓ) : ℝ :=
  E (toReal (P.2.2.2.1.toPoly P.numVars)) +
    (P.2.2.2.2.map fun q ↦ E (toReal (q.toPoly P.numVars)) ^ 2).sum

/-- The problems the algorithm is specified on: the degree is even and at least `2`, the objective
has degree at most `ℓ`, the constraints are satisfied by some real point, and one of them is an
explicit bound `B - ∑ i, xᵢ² ≥ 0`. -/
def Valid : Prop :=
  Even P.degree ∧ 2 ≤ P.degree ∧
    (∀ q ∈ P.2.2.2.1 :: P.2.2.2.2, (q.toPoly P.numVars).totalDegree ≤ P.degree) ∧
    (∃ B : ℚ, (C B - ∑ i : Fin P.numVars, X i ^ 2) ∈ P.system) ∧
    ∃ y : Fin P.numVars → ℝ, ∀ f ∈ P.system, 0 ≤ eval y (toReal f)

end Problem

/-- `M` lists the pseudo-moments of `E` up to degree `ℓ`: its coefficient of `xᵅ` is `Ẽ[xᵅ]`. -/
def HasMoments {n ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) (M : MvPolynomial (Fin n) ℚ) : Prop :=
  ∀ α : Fin n →₀ ℕ, α.degree ≤ ℓ → E (monomial α 1) = (M.coeff α : ℝ)

/-- The output `out` is correct for the problem `P` with accuracies `η, γ`: it lists the
pseudo-moments of a degree-`ℓ` pseudo-expectation that satisfies the constraints
`(η + γ)`-approximately, and whose objective is at most `γ` more than that of every
pseudo-expectation satisfying them `η`-approximately. -/
def Correct (P : Problem) (η γ : ℚ) (out : Output) : Prop :=
  ∃ E : PseudoExpectation (Fin P.numVars) P.degree,
    HasMoments E (out.toPoly P.numVars) ∧
    E.ApproxSatisfies P.system ((η : ℝ) + γ) 0 ∧
    ∀ E' : PseudoExpectation (Fin P.numVars) P.degree, E'.ApproxSatisfies P.system η 0 →
      P.objective E ≤ P.objective E' + γ

/-- The running time `(|P| + 2)^(C (ℓ + 1)) (|η, γ| + 2)^C`. -/
def timeBound (C : ℕ) (x : Input) : ℕ :=
  ((encProblem x.1).length + 2) ^ (C * (x.1.degree + 1)) *
    ((encPair encRat encRat x.2).length + 2) ^ C

end SoS.Solver
