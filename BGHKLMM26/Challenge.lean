module

public import BGHKLMM26.Model

/-!
# Main results: statements

The main results of [BGHKLMM26], with proofs `sorry`. `lake comparator` checks that
`Solution.lean` proves exactly these statements using only the axioms listed in `comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BGHKLMM26/Model.lean` (Max 2-LIN(2), Max-Cut, its SDP relaxation, randomized algorithms,
encodings), the encodings in `Background/Encoding.lean`, the Unique Games Conjecture in
`Background/UniqueGames.lean`, CSLib's multitape Turing machines, complexitylib's classes `NP`,
`BPP` and `PromiseBPP` and its gap problems, and Mathlib.

## Theorem 1.1

[BGHKLMM26, Theorem 1.1] (in the form of Theorem 3.1): there is a randomized polynomial-time
algorithm that takes a weighted Max 2-LIN(2) instance `I` whose variables each appear in at most
`d` constraints and outputs an assignment of expected value at least
`(α_GW + Ω(1/(d log d))) opt(I)`.

Formally (`BGHKLMM26.max2lin_approximation`):

* **Instances** (`BGHKLMM26.Instance`, `BGHKLMM26.Valid`): constraints `xᵢ xⱼ = ±1` on distinct
  pairs of variables (the edges of a graph, as in the paper), with nonnegative rational weights.
  The value is the satisfied weight, not normalized by the total weight, so the inequality also
  makes sense when all weights are `0`.
* **`d`** is any bound `d ≥ 2` on the number of constraints containing a variable, and may grow
  with the instance; `Ω(1/(d log d))` is `c / (d log d)` for one constant `c > 0`.
* **Running time.** The algorithm runs in time `O((N + 2)^k)` on instances of encoded length `N`
  (`BGHKLMM26.RunsInTime`): polynomial in the number `n` of variables, which is encoded in unary
  as in the paper's "time polynomial in `n`", and in the bits of the constraints, weights
  included. As in [BKS23] and [BBKS24] in this repository, the bound is an explicit polynomial,
  which is also the number of coins the expectation is over.

## Theorem 1.2

[BGHKLMM26, Theorem 1.2]: assuming the Unique Games Conjecture and `NP ⊄ BPP`, for every large
enough `d`, no polynomial-time algorithm distinguishes graphs of maximum degree at most `d` with
Max-Cut value at least `c* - O(1/d)` from those with value at most `s* + O(log² d / d)`. Here
`c* = (1 - ρ*) / 2` and `s* = arccos ρ* / π` for the minimizer `ρ*` of the Goemans–Williamson ratio.
The formal statement is this one, with `O(log² d / d)`.

Formally (`BGHKLMM26.maxCut_hardness`):

* **The Unique Games Conjecture** is a hypothesis, `UniqueGames.UGC`, in the form of the paper's
  Conjecture 4.10: there is `ε₀ ∈ (0, 1/2]` such that for every `ε ∈ (0, ε₀]` there is a number
  `R` of labels for which it is NP-hard to tell simple bi-regular bipartite Unique Games instances
  with `R` labels and value at least `1 - ε` from those with value at most `ε`. The only change is
  that Conjecture 4.10 asks for hardness for every `R` larger than some `R(ε)`, and this asks for
  one `R`. That is weaker, and enough: the proof needs `R` large, and replacing each constraint
  `π` by `π × id` on `[R] × [k]` keeps the hardness with `kR` labels. A proof of
  `UniqueGames.UGC` makes the theorem unconditional.
* **The conclusion** is the paper's "unless `NP ⊆ BPP`": if the gap problem
  `BGHKLMM26.maxCutGap d c s` can be solved by a polynomial-time algorithm with bounded error
  (complexitylib's `PromiseBPP`), then `NP ⊆ BPP` for every encoding of instances. So it rules
  out bounded-error randomized polynomial-time algorithms, not only deterministic ones.
* **Graphs** are simple and unweighted, encoded by their number of vertices and adjacency table
  (`BGHKLMM26.encGraph`). The Max-Cut value is the largest fraction of edges crossing a cut.
* **Constants.** One `C` and one `d₀` serve every `d ≥ d₀`: the yes-instances have value at least
  `c* - C/d` and the no-instances at most `s* + C log² d / d` (natural logarithm). The paper
  proves this through the robust inverse of Borell's theorem by Heilman; the formal proof uses
  Eldan's published estimate (Invent. Math. 2015) instead, with the multiscale union bound of
  Lemma 6.6 starting at the scale `K log² d / d`.
* **`ρ*`.** The statement holds for every minimizer `ρ` of `gwRatio` on `[-1, 1)`;
  `BGHKLMM26.exists_unique_isGWMinimizer` shows that there is exactly one.

## Corollary 1.3

[BGHKLMM26, Corollary 1.3]: assuming the Unique Games Conjecture, no polynomial-time algorithm
approximates Max-Cut within `α_GW + Ω(log² d / d)` in graphs of maximum degree `d`, unless
`NP ⊆ BPP`. The formal statement has the paper's `log² d`, as Theorem 1.2.

Formally (`BGHKLMM26.maxCut_inapproximability`):

* **Algorithms and their guarantee** are those of Theorem 1.1: a machine running in time
  `O((N + 2)^k)` that outputs an assignment, and the expected value of that assignment over
  `(N + 2)^k` coins. Graphs are given as Max 2-LIN(2) instances whose constraints are all
  `xᵢ xⱼ = -1` with weight `1` (`BGHKLMM26.IsMaxCutInstance`), so an assignment is a cut and its
  value is the number of edges it cuts. The corollary is then the converse of Theorem 1.1: its
  gain `c / (d log d)` cannot be raised to `C log² d / d`, even on unweighted graphs.
* **Constants.** One `C` and one `d₀` serve every `d ≥ d₀`, and the algorithm may depend on `d`:
  for each such `d`, an algorithm with expected value at least `(α_GW + C log² d / d) opt` on all
  graphs of maximum degree at most `d` puts `NP` in `BPP`.
* **Other readings.** An algorithm that reaches the ratio with probability `2/3` gives one with
  the expected guarantee for a slightly smaller ratio, by repeating it and keeping the best cut, so
  it is ruled out too with a larger `C`. Algorithms that only estimate the Max-Cut value are ruled
  out by Theorem 1.2.
* **The conclusion** is that of Theorem 1.2. The proof goes through Theorem 1.2: on the yes
  instances such an algorithm finds, with probability bounded below for fixed `d`, a cut larger
  than any cut of a no instance; repeating it a number of times depending on `d` decides the gap
  problem with bounded error.

## Theorem 1.4

[BGHKLMM26, Theorem 1.4]: for every large enough `d` there is a graph of maximum degree at most
`d` whose Goemans–Williamson SDP with triangle inequalities has value at least `c* - O(1/d)` and
whose Max-Cut value is at most `s* + O(log² d / d)`; consequently the integrality gap of the SDP is
at most `α_GW + O(log² d / d)`. This is unconditional.

Formally (`BGHKLMM26.maxCut_integrality_gap`):

* **The SDP** is the one displayed in [BGHKLMM26, Section 3], for Max-Cut: unit vectors
  `vᵢ ∈ ℝⁿ` with the triangle inequalities (`BGHKLMM26.IsSDPSolution`), of value the average over
  the edges of `‖vᵢ - vⱼ‖² / 4 = (1 - ⟨vᵢ, vⱼ⟩) / 2` (`BGHKLMM26.sdpValue`), normalized like the
  Max-Cut value. "The optimal SDP value is at least `c* - C/d`" is stated by exhibiting a solution
  with that value.
* **The integrality gap.** The last clause, `MaxCut(H) ≤ (α_GW + C log² d / d) · SDP`, is the
  paper's "consequently"; it follows from the other two.
* **Constants** as in Theorem 1.2, with the paper's `log² d`: the soundness is that of the
  reduction of Theorem 1.2, applied to the Unique Games integrality gap instances of Khot and
  Vishnoi [KV15] instead of to the instances of the Unique Games Conjecture.
-/

public section

namespace BGHKLMM26

open UniqueGames

open Cslib.Complexity

/-- The Goemans–Williamson ratio has exactly one minimizer `ρ*` on `[-1, 1)`. -/
theorem exists_unique_isGWMinimizer : ∃! ρ : ℝ, IsGWMinimizer ρ :=
  sorry

/-- **Theorem 1.1** of [BGHKLMM26]: a randomized polynomial-time algorithm for weighted
Max 2-LIN(2) whose expected value is at least `(α_GW + c/(d log d))` times the optimum on
instances where every variable appears in at most `d` constraints. -/
theorem max2lin_approximation :
    ∃ (A : Instance × List Bool → List Bool) (k : ℕ),
      RunsInTime A (fun N ↦ (N + 2) ^ k) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ I : Instance, Valid I → MaxDegreeLE I d →
        (alphaGW + c / (d * Real.log d)) * opt I ≤
          coinMean (((encInstance I).length + 2) ^ k) fun r ↦ outputWeight I (A (I, r)) :=
  sorry

/-- **Theorem 1.2** of [BGHKLMM26]: assuming the Unique Games Conjecture, for every large enough
`d`, no polynomial-time algorithm tells graphs of maximum degree at most `d` with Max-Cut value at
least `c* - C/d` from those with value at most `s* + C log² d / d` with bounded error, unless
`NP ⊆ BPP`. -/
theorem maxCut_hardness (hUGC : UGC) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      maxCutGap d ((1 - ρ) / 2 - C / d) (Real.arccos ρ / Real.pi + C * Real.log d ^ 2 / d) ∈
        PromiseBPP encGraph →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc :=
  sorry

/-- **Corollary 1.3** of [BGHKLMM26]: assuming the Unique Games Conjecture, for every large enough
`d`, a randomized polynomial-time algorithm whose expected cut is at least `(α_GW + C log² d / d)`
times the maximum cut on graphs of maximum degree at most `d` puts `NP` in `BPP`. -/
theorem maxCut_inapproximability (hUGC : UGC) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
      ∀ (A : Instance × List Bool → List Bool) (k : ℕ), RunsInTime A (fun N ↦ (N + 2) ^ k) →
      (∀ I : Instance, Valid I → IsMaxCutInstance I → MaxDegreeLE I d →
        (alphaGW + C * Real.log d ^ 2 / d) * opt I ≤
          coinMean (((encInstance I).length + 2) ^ k) fun r ↦ outputWeight I (A (I, r))) →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc :=
  sorry

/-- **Theorem 1.4** of [BGHKLMM26]: for every large enough `d` there is a graph of maximum degree
at most `d` with a solution of the Goemans–Williamson SDP with triangle inequalities of value at
least `c* - C/d` and Max-Cut value at most `s* + C log² d / d`, so that the integrality gap is at
most `α_GW + C log² d / d`. -/
theorem maxCut_integrality_gap :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      ∃ (H : Graph) (v : Fin H.1 → EuclideanSpace ℝ (Fin H.1)),
        MaxDegreeAtMost H d ∧ IsSDPSolution H.1 v ∧
        (1 - ρ) / 2 - C / d ≤ sdpValue H v ∧
        maxCutValue H ≤ Real.arccos ρ / Real.pi + C * Real.log d ^ 2 / d ∧
        maxCutValue H ≤ (alphaGW + C * Real.log d ^ 2 / d) * sdpValue H v :=
  sorry

end BGHKLMM26
