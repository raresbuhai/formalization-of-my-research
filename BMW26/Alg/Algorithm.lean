module

public import BMW26.Alg.Program
public import BMW26.Round.Function
public import Background.SumOfSquares.Algorithm.Correct

/-!
# The algorithm

The algorithm of [BMW26, Theorem 1.2] with parameter `c` (the exponent of the error `d^(-c)`), as a
function on the encoded input (`BMW26.Alg.runAlg`), with a budget `L` for the solver:

1. Read `n` (capped by the length of the adjacency table, `BMW26.Alg.numV`), `d = ⌊log₂ n⌋`, and
   the edge list of the graph.
2. Build the degree-`4` program ([Program.lean](Program.lean)) with slack `δ = 1 / d^(c+7)` and
   run the sum-of-squares solver `SoS.Core.core` with the accuracies `η = γ = 2^-(n² + 10)`.
3. Round its second moments ([../Round/Function.lean](../Round/Function.lean)).

The coins are not used. With the budget `L = SoS.Solver.budget` of the solver's input
(`BMW26.Alg.alg`), nothing is cut short, and the output is that of a correct solver
(`BMW26.Alg.alg_spec`).
-/

@[expose] public section

namespace BMW26.Alg

open SoS MvPolynomial

/-- The number of vertices, capped by the length of the adjacency table (which is `n²` for the
encoding of a graph on `n` vertices). -/
def numV (n : ℕ) (adj : List Bool) : ℕ := min n adj.length

/-- The dimension `d = ⌊log₂ n⌋`. -/
def dimOf (n : ℕ) : ℕ := Nat.log 2 n

/-- The slack `δ = 1 / d^(c+7)` of the cut constraint. -/
def slack (c d : ℕ) : ℚ := 1 / (d : ℚ) ^ (c + 7)

/-- The accuracy `η = γ = 2^-(n² + 10)` of the solver. -/
def acc (n : ℕ) : ℚ := 1 / 2 ^ (n ^ 2 + 10)

/-- The input of the solver: the program and the accuracies. -/
def solverInputOf (c : ℕ) (x : ℕ × List Bool) : Solver.Input :=
  let n := numV x.1 x.2
  (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n x.2), acc n, acc n)

/-- **The algorithm** with parameter `c`, on the number of vertices and the adjacency table, with
budget `L` for the solver. -/
def runAlg (c : ℕ) (x : (ℕ × List Bool) × ℕ) : Output :=
  let n := numV x.1.1 x.1.2
  Round.roundOut n (dimOf n) c (momentTable n (SoS.Core.core (solverInputOf c x.1, x.2)))
    (edgeList n x.1.2)

/-- **The algorithm** with parameter `c`, on a graph and coins (which it does not use), with the
solver's budget. -/
noncomputable def alg (c : ℕ) (xr : Graph × List Bool) : Output :=
  runAlg c ((xr.1.1, adjTable xr.1), Solver.budget (solverInputOf c (xr.1.1, adjTable xr.1)))

/-- The number of vertices read from the encoding of a graph on `n` vertices is `n`. -/
theorem numV_adjTable {n : ℕ} (G : SimpleGraph (Fin n)) : numV n (adjTable ⟨n, G⟩) = n := by
  rw [numV, adjTable, List.length_ofFn]
  exact min_eq_left (Nat.le_mul_self n)

/-- **Correctness of the algorithm relative to the solver.** On a graph `G` on `n` vertices whose
program is valid, there are a pseudo-expectation `Ẽ` satisfying the program up to `2η` whose
objective is within `η` of that of every pseudo-expectation satisfying it up to `η`, and a
moment table listing its second moments, such that the output is the rounding of that table. -/
theorem alg_spec (c : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (r : List Bool)
    (hvalid : (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).Valid) :
    ∃ (E : PseudoExpectation (Fin n) 4) (Mt : List (List ℚ)),
      E.ApproxSatisfies
        (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).system
        (2 * (acc n : ℝ)) 0 ∧
      (∀ E' : PseudoExpectation (Fin n) 4,
        E'.ApproxSatisfies
          (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).system
          (acc n : ℝ) 0 →
        ∑ u, ∑ v, E (X u * X v) ^ 2 ≤ ∑ u, ∑ v, E' (X u * X v) ^ 2 + acc n) ∧
      (∀ u v : Fin n, (Round.entry Mt u v : ℝ) = E (X u * X v)) ∧
      alg c (⟨n, G⟩, r) = Round.roundOut n (dimOf n) c Mt (edgeList n (adjTable ⟨n, G⟩)) := by
  have hη : (0 : ℚ) < acc n := by
    unfold acc
    positivity
  obtain ⟨E, hM, hA, hopt⟩ : ∃ E : PseudoExpectation (Fin n) 4,
      Solver.HasMoments E ((SoS.Core.core
        ((problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩)), acc n, acc n),
          Solver.budget (problemOf n (dimOf n) (slack c (dimOf n))
            (edgeList n (adjTable ⟨n, G⟩)), acc n, acc n))).toPoly n) ∧
      E.ApproxSatisfies
        (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).system
        ((acc n : ℝ) + (acc n : ℝ)) 0 ∧
      ∀ E' : PseudoExpectation (Fin n) 4,
        E'.ApproxSatisfies
          (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).system
          (acc n : ℝ) 0 →
        (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).objective E ≤
          (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩))).objective E' +
            (acc n : ℝ) :=
    SoS.Correct.core_correct _ hvalid (acc n) (acc n) hη hη
  have hsi : solverInputOf c (n, adjTable ⟨n, G⟩) =
      (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩)), acc n, acc n) := by
    simp only [solverInputOf, numV_adjTable]
  refine ⟨E, momentTable n (SoS.Core.core
    ((problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩)), acc n, acc n),
      Solver.budget
        (problemOf n (dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩)), acc n, acc n))),
    ?_, fun E' hE' ↦ ?_, fun u v ↦ ?_, ?_⟩
  · rwa [← two_mul] at hA
  · have h1 := objective_eq (d := dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩)) E
    have h2 := objective_eq (d := dimOf n) (slack c (dimOf n)) (edgeList n (adjTable ⟨n, G⟩)) E'
    calc _ = _ := h1.symm
      _ ≤ _ := hopt E' hE'
      _ = _ := congrArg (· + ((acc n : ℚ) : ℝ)) h2
  · rw [Round.entry, entry_momentTable, ← hM _ (by simp), X, X, monomial_mul_monomial, mul_one]
  · simp only [alg, runAlg, hsi, numV_adjTable]

end BMW26.Alg
