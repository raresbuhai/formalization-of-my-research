module

public import BHSV25.Model

/-!
# Main results: statements

The main results of [BHSV25], with proofs `sorry`. The algorithms are stated in the full versions
of Section 7 (Theorems 7.1, 7.9, 7.17 and 7.20, Corollaries 7.2 and 7.21, and Theorem 7.12 with
an additional error `ε`), with their errors and running times, and Corollaries 1.2 and 1.4 with the
running times that these give. The
hardness results are Theorems 1.5, 1.6, 1.8 (2) and 1.9 (2), as NP-hardness of gap problems, and
the spectral results are Theorems 1.7 and 4.1. `lake comparator`
checks that `Solution.lean` proves exactly these statements using only the axioms listed in
`comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BHSV25/Model.lean` (graphs and their encoding, spectra, colorings, models, random planting,
running times), the
Unique Games Conjecture in `Background/UniqueGames.lean`, the encodings in
`Background/Encoding.lean`, CSLib's multitape Turing machines, complexitylib's polynomial time,
`P`, `NP` and NP-hardness of promise problems, and Mathlib.

Numbers refer to the arXiv version (v2), whose counters are shared within each section.

## Conventions

* **Graphs** are simple, on `n` vertices, encoded by their adjacency tables. All graphs in the
  algorithmic and hardness results are **regular**, as in the paper, except the planted graphs of
  Theorems 7.12 and 7.17, whose host graphs are regular. The spectrum is that of the
  normalized adjacency matrix (`A / d` for a `d`-regular graph), and a **`λ`-one-sided expander**
  has second largest eigenvalue at most `λ` (`BHSV25.Graph.IsOneSidedExpander`). Lean reserves
  `λ`, so it is written `lam`.
* **Running times** (`BHSV25.RunsInTime A encGraph enc K C`): a deterministic multitape Turing
  machine computes `A` in at most `K (m + 1)^C` steps on graphs whose encoding has length `m`
  (about `n²` for `n` vertices), in polynomial space. A running time `n^{O(1)} · g(p)` of the
  paper, for parameters `p`, is stated as: there is `C`, fixed before all parameters, such that for
  all values of `p` some algorithm runs in time `K · m^C`, where `K` is any number depending on
  `p` (the paper's `O_p(1)`).
* **Running times in the number `t` of eigenvalues** (Theorems 7.12 and 7.20, Corollary 7.21,
  `BHSV25.RunsInTimeWith A encGraph enc K C`): one machine computes `A` in at most
  `K G (m + 1)^C` steps on every graph `G`, for a factor `K G` that depends on the graph, and
  `K G ≤ g(t)` on the graphs with at most `t` eigenvalues beyond the threshold, for every `t`. The
  algorithm does not know `t`: it finds the number of eigenvectors it needs itself. Here `g(t)` is
  the paper's `(γ / (1 - λ))^{-O(t)}` (Theorem 7.20, Corollary 7.21), or `(O_{k,ε}(1))^t`
  (Theorem 7.12).
* **Algorithms depend on the parameters**, as in the paper's theorems: for all values of `δ`, `γ`,
  `λ` and `c` there is an algorithm, which in Theorems 7.12 and 7.20 and Corollary 7.21 is the
  same for all `t`. They are not given the promised independent sets or colorings.
* **Constants**: an `O(·)` is a constant fixed before the parameters it does not depend on, and
  "for `δ, γ, λ` small enough" is `δ, γ, λ < c₀` for some `c₀ > 0`. In Theorem 7.1 and
  Corollary 7.2 both depend on the model `M` (the paper's `O_M`).
* **`o_{λ→0}(1)`** (in Corollary 1.4) is a function `f` with `f λ → 0` as `λ → 0⁺`.
* **Outputs**: an independent set or a vertex cover is a list of membership bits, one per vertex
  (`BHSV25.Graph.vertexSet`); a coloring is a list of colors, one per vertex, with colors `≥ k`
  read as "uncolored" (`BHSV25.Graph.color`). "`k` independent sets covering all but a `δ`
  fraction of the vertices" is a `(k, δ)`-coloring (`BHSV25.Graph.IsColoring`).
* **Hardness** ("assuming the Unique Games Conjecture, it is NP-hard to find a `(k, δ)`-coloring
  of a graph with property `P`") is stated as: assuming the Unique Games Conjecture
  (`UniqueGames.KhotUGC`), the gap problem `BHSV25.coloringGap P k δ` is NP-hard
  (`Cslib.Complexity.PromiseProblem.NPHard`: every problem in `NP`, with any encoding of its
  instances, reduces to it by a deterministic polynomial-time map). Its yes-instances are the
  graphs with property `P` that have a `(k, δ)`-coloring, and its no-instances the graphs that
  have none.
  * This is how the paper's reductions show the problems of finding colorings hard: an algorithm
    finding `(k, δ')`-colorings of the graphs with property `P`, for some `δ' < δ`, solves the gap
    problem by checking its output, so it gives `NP ⊆ P`. complexitylib has no search problems
    or reductions to them, so these problems are stated through their gap problems.
  * The property `P` (regularity, the spectral bounds, the promised coloring) is required on the
    yes-instances only, as search hardness needs: the statements do not assert that the
    no-instances are regular or spectrally bounded.
  * For `ε ≤ δ`, every graph with property `P` has a `(k, δ)`-coloring, so the yes-instances are
    the graphs with property `P`; larger `ε` makes `P` weaker and the theorem stronger.
    "`γ` small enough" is `γ < 1/2`, `γ < 2/9` and `γ < α` in Theorems 1.5, 1.6 and 1.9 (2): the
    colorings sought leave a positive fraction `δ` of the vertices uncolored.
  * `UniqueGames.KhotUGC` is the conjecture in its usual form on graphs: for every small `ε > 0`,
    some number of labels makes it NP-hard to tell simple instances on graphs of value at least
    `1 - ε` from those of value at most `ε`. Khot's form, with completeness `1 - η` and soundness
    `ζ` for all small `η, ζ`, implies it, and so does the bipartite form, Khot's Unique Label
    Cover, since bipartite instances are instances on graphs.
  * The paper's reductions start from Fact 8.1, the hardness of almost-bipartite independent set
    that Bansal and Khot derive from the conjecture (with maximum degree `o(n)`, as in Bafna,
    Hsieh and Kothari). The proofs here derive Fact 8.1 from `UniqueGames.KhotUGC` too, through
    the bipartite double cover and Khot and Regev's regularization to left-regular instances.
  * The reductions are deterministic, so the proofs replace the random biregular graphs of the
    paper's reductions by explicit ones.

## Theorem 7.20

For every constant `c > 0` and all `λ ∈ (0, 1)` and `γ ∈ (0, 1/4)`: an algorithm that, on regular
graphs with an independent set of `(1/2 - γ) n` vertices, outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices, and runs in time `poly(n) · (γ / (1 - λ))^{-O(t)}`
on the regular graphs with at most `t` eigenvalues at most `-λ`, for every `t`
(`BHSV25.independentSet_bottomRank`).

* The degree of `poly(n)` is independent of all parameters, and the constant in `O(t)` depends
  only on `c`. The factor is written `(D / (1 - λ))^D (D (1 + (1 - λ) / γ))^{D (t + 1)}`: the
  `1 +` keeps the second factor at least `1` when `γ > 1 - λ`, where the bound on the output is
  negative anyway.
* The first factor `(D / (1 - λ))^D`, which does not depend on `t`, is not in the paper: the
  algorithm finds the number of eigenvectors with eigenvalue at most `-λ` itself, which needs `λ`
  to precision `c (1 - λ)`, and a Turing machine reads a description of such a `λ`. The paper
  computes with `λ` exactly.
* The output is an independent set on every regular graph, and the bound on its size holds on
  every regular graph with the promised independent set, whatever the number of eigenvalues at
  most `-λ`.

## Theorem 1.1 (Corollary 7.21)

For every constant `c > 0` and all `λ ∈ (0, 1/2)` and `γ ∈ (0, 1/4)`: an algorithm that, on
regular graphs with an independent set of `(1/2 - γ) n` vertices, outputs an independent set of at
least `(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n` vertices, and runs in time
`poly(n) · (γ / (1 - √(2λ)))^{-O(t/λ²)}` on the regular graphs with at most `t` eigenvalues
larger than `λ`, for every `t` (`BHSV25.independentSet_approximation`).

* Theorem 1.1 is the case `t = 1`, of `λ`-one-sided expanders (`BHSV25.Graph.IsOneSidedExpander`
  is `numEigGT λ ≤ 1`), with `γ ≤ 1/10`: the loss `γ + (4 + c) γ / (1 - √(2λ))` is
  `(5 + o_{λ→0}(1)) γ` for small `c`. Larger `t` is the paper's remark that the algorithm
  extends to bounded threshold rank.
* `λ < 1/2`, so that `√(2λ) < 1`.
* "Larger than `λ`" is strict (`BHSV25.Graph.numEigGT`), which makes the hypothesis weaker:
  Corollary 7.21 counts the eigenvalues at least `λ`. Corollary 4.2 for a threshold slightly above
  `λ` still bounds the number of eigenvalues at most `-√(2λ)` by `t / λ²`.
* As in Theorem 7.20, the factor is
  `(D / (1 - √(2λ)))^D (D (1 + (1 - √(2λ)) / γ))^{D (⌈t / λ²⌉ + 1)}`, and the guarantee holds on
  every regular graph with the promised independent set.

## Corollary 1.2

For every `ε > 0` there are `λ₀ > 0` and a polynomial-time algorithm that, on every regular
`λ₀`-one-sided expander, outputs a vertex cover of size at most `(5/3 + ε)` times the minimum
(`BHSV25.vertexCover_approximation`). The paper's `1.6667` is `5/3 + 1/30000`. The paper states
polynomial time; the running time `K · m^C` with `C` independent of `ε` is what Corollary 7.21
gives, run for finitely many values of `γ`.

## Theorem 1.3 (Theorem 7.9)

For `δ ∈ [0, c₀)` and `γ, λ ∈ (0, c₀)`: an algorithm running in time `n^{O(1)} · O_{δ,γ,λ}(1)`
that, on regular `λ`-one-sided expanders with a partition into `3` parts of at most `(1/2 - γ) n`
vertices each whose inside edges are covered by `δ n` vertices (`BHSV25.Graph.IsAlmostProper`),
outputs `3` independent sets covering all but `O(λ / γ⁸ + δ / (λ γ⁸)) n` vertices
(`BHSV25.threeColoring_balanced`).

* Theorem 7.9 takes `λ` to be the second eigenvalue; here `λ` is any upper bound on it, which is
  stronger, as the variance bound (Lemma 6.1) only needs an upper bound. It gives the
  introduction's Theorem 1.3, also for almost `3`-colorable graphs: if the inside edges are
  covered by `λ n` vertices and the second eigenvalue is at most `λ`, take the upper bound `√λ`
  and `γ = λ^{1/18}`, for an error `O(λ^{1/18})`.
* `δ = 0`, of proper `3`-colorings, is allowed.

## Corollary 1.4

For every `λ > 0` there is a polynomial-time algorithm that, given a regular `λ`-one-sided
expander with `3` independent sets covering all but `λ n` vertices, outputs `3` independent sets
of which one has at least `(1/2 - f λ) n` vertices or which together cover all but `f λ · n`
vertices, where `f λ → 0` (`BHSV25.threeColoring_independentSet_or_coloring`).

* The introduction asks for `3`-colorable graphs; the paper notes that its algorithms for
  `3`-colorable one-sided expanders handle almost `3`-colorable ones too, and so does this
  statement.
* The paper states polynomial time and gives no explicit `f`. The running time `K · m^C` with `C`
  independent of `λ` is what Theorem 7.9 and Corollary 7.21 give, with parameters depending only
  on `λ`: if every class has at most `(1/2 - g λ) n` vertices, Theorem 7.9 covers all but `g λ · n`
  vertices; otherwise the largest class is an independent set of more than `(1/2 - g λ) n`
  vertices, and Corollary 7.21 with `γ = g λ` finds one of `(1/2 - O(g λ)) n`.

## Theorems 7.12 and 7.17 (random planting)

A `k`-coloring is **randomly planted** in a host graph `H` (`BHSV25.Graph.plant`, Definition 7.11)
by giving every vertex one of `k` colors, independently and uniformly, and removing the edges whose
endpoints get the same color; the algorithm sees only the planted graph `G`, not `H` or the
colors. **With high probability** is with probability at least `1 - P/n` over the colors
(`BHSV25.Graph.plantProb`), for a constant `P` depending only on `k`, on every host graph.

* **Theorem 7.12, with an additional error `ε`** (`BHSV25.plantedColoring_partial`): for `k ≥ 3`
  there are `λ₀ > 0` and constants such that, for every `ε > 0`, there is an algorithm that, on
  the graph planted in any `d`-regular host with at most `t` eigenvalues at least `λ₀`, for every
  `t`, with high probability runs in time `n^{O(1)} · (O_{k,ε}(1))^t` and outputs a
  `(k, O_k(1/(d + 1)^γ) + ε)`-coloring. The degree of `n^{O(1)}` and the exponent `γ > 0` are
  universal.
* The running time is stated with high probability, like the output: the algorithm does not
  know the degree `d` of the host, and finds the number of eigenvectors it needs at the scale of
  the average degree of the planted graph, which is within a factor `2` of `d` with high
  probability.
* This is weaker than the paper's Theorem 7.12, which states the error `O_k(1/d^{Ω(1)})` in time
  `n^{O(1)} · (O_k(1))^t`. Here the algorithm and the base of the exponential depend on `ε`, so the
  error guaranteed for any one algorithm tends to `ε`, not to `0`, as `d` grows. The paper's time
  does not follow from its proof: the proof applies Theorem 5.1, which enumerates a net of
  `(δ k/λ²)^{-O(t)}` vectors and the `k`-tuples of them, so `(δ k/λ²)^{-O(t k)}` candidates, for
  the closeness `δ` of the planted graph to its model. Here `δ = O_k(1/d^{Ω(1)})`, so the number of
  candidates grows with `d`, like `d^{O_k(t)}`, which `n^{O(1)} · (O_k(1))^t` does not bound when
  both `d` and `t` grow. A net of
  fixed precision gives the extra error `ε` and the `ε`-dependent time of this statement.
* **Theorem 7.17** (`BHSV25.plantedColoring_full`): for `k ≥ 3` there are `λ₀ > 0` and `d₀` such
  that an algorithm running in time `n^{O(1)} · O_k(1)` outputs with high probability a proper
  `k`-coloring (a `(k, 0)`-coloring) of the graph planted in any `d`-regular `λ₀`-one-sided
  expander with `d ≥ d₀`. The degree of `n^{O(1)}` is universal.
* "For `λ` small enough" is `λ ≤ λ₀`: the hypotheses are stated at `λ₀`, which they imply for every
  smaller `λ`, and the algorithms do not depend on `λ`. "`d` at least a large enough constant
  compared to `k`" is `d ≥ d₀(k)`.
* `k ≥ 3`, as the paper's proofs use.

## Theorem 1.5 (Corollary 8.4)

Assuming the Unique Games Conjecture, for all `ε > 0` and `γ ∈ (0, 1/2)`, it is NP-hard to find
`3` independent sets covering at least `(1/2 + γ) n` vertices in a regular graph on `n` vertices
with `λ₂ = o(1)` and `3` independent sets covering `(1 - ε) n` vertices
(`BHSV25.threeColoring_unbalanced_hardness`).

* `λ₂ = o(1)` is: there is `f` with `f n → 0` such that the graphs are `f n`-one-sided expanders.
  `f` depends on `ε` and `γ`, which are fixed first, as in Corollary 8.4.
* The introduction's statement, for `ε`-one-sided expanders with `ε = γ`, follows, since
  `f n ≤ ε` for large `n`.

## Theorem 1.6 (Theorem 8.6)

Assuming the Unique Games Conjecture, for every `ε > 0` there is `R` such that, for every
`γ ∈ (0, 2/9)`, there is `f` with `f n → 0` such that it is NP-hard to find `3` independent sets
covering at least `(7/9 + γ) n` vertices in a regular graph on `n` vertices with
1. `3` independent sets of the same size covering `(1 - ε) n` vertices, a `(3, ε)`-coloring with
   identical color class sizes as in Theorem 8.6,
2. at most two eigenvalues larger than `f n`: `λ₃ = o(1)`,
3. at most `R` eigenvalues larger than `f n` in absolute value

(`BHSV25.threeColoring_lowRank_hardness`).

* Condition 3 is not in Theorem 8.6; the construction gives it with `R = 7`.
* Condition 1 gives the introduction's three disjoint independent sets of at least
  `(1/3 - ε) n` vertices each, and `f n ≤ ε` for large `n`, so this implies the introduction's
  statement, whose coverage `0.9` is the case `γ = 11/90`.

## Theorems 1.7 and 4.1

For every graph and all `τ ≥ 0` and `τ' < τ²`, the number of eigenvalues at most `-τ` and the
number of eigenvalues at least `τ'` satisfy
`((τ² - τ') / (1 - τ'))² · #{eigenvalues ≤ -τ} ≤ #{eigenvalues ≥ τ'}`
(`BHSV25.thresholdRank_graph`, Theorem 1.7, stated there for `τ > 0`). Theorem 4.1, the full
version, is for every symmetric matrix with nonnegative entries and eigenvalues in `[-1, 1]`, in
the parameters `λ ≥ 0` and `σ ∈ (0, 1)`:
`σ² · #{eigenvalues ≤ -λ} ≤ #{eigenvalues ≥ (λ² - σ) / (1 - σ)}` (`BHSV25.thresholdRank`). The
paper states it as: if at least `t` eigenvalues are at most `-λ`, at least `σ² t` are at least
`(λ² - σ) / (1 - σ)`, which is the same. For `λ < 1`, `τ = λ` and `σ = (τ² - τ') / (1 - τ')`
translate between the two.

## Theorems 1.8 (1) and 1.9 (1) (Corollary 7.2 and Theorem 7.1)

Let `M` be a model (`BHSV25.IsModel`): a reversible row-stochastic matrix with zero diagonal and
second largest eigenvalue at most `0`, with stationary distribution `π`, and let
`α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)` (`BHSV25.alpha`). For `δ ∈ [0, c₀)` and
`λ ∈ (0, c₀)`: an algorithm running in time `n^{O(1)} · O_{δ,λ,M}(1)` that, on regular
`λ`-one-sided expanders with an `(M, δ)`-coloring (`BHSV25.Graph.MColorable`), outputs a
`(k', α + O_M(√δ + λ + δ/λ))`-coloring, where `k'` is the number of distinct rows of `M`
(`BHSV25.expanderColoring_algorithm`). If `M` has no repeated rows, `k' = k` and `α = 0`
(`BHSV25.expanderColoring_distinctRows`, Corollary 7.2).

* The degree of `n^{O(1)}` is independent of `M`; the constants `B` and `c₀` depend on it.
* `k'` is `Nat.card (Set.range M)`, the number of distinct rows. Theorem 7.1's uncovered fraction
  is `1 - ∑ p_i + …`, and `1 - ∑ p_i = α`.
* As in Theorem 7.9, `λ` is any upper bound on the second eigenvalue. With `λ = √δ` the error is
  `α + O_M(√δ)`, which gives the introduction's `M`-expander-coloring and
  `(M, α)`-expander-coloring, with an algorithm for each `ε`.
* **Reversibility** is with respect to a positive `π`: `π_a M_ab = π_b M_ba` with every `π_a > 0`.
  The paper's printed definition (Section 3) asks only for `π ≥ 0`, but then every matrix would
  be reversible (take `π = 0`); the paper's proofs use a positive `π` (Lemma 7.3). **`π`** is the
  unique stationary distribution of a model; the theorem is stated for every positive `π` summing
  to `1` in detailed balance with `M` (`BHSV25.IsStationary`).

## Theorems 1.8 (2) and 1.9 (2) (Corollary 8.3 and Theorem 8.2)

Let `M` be a model with stationary distribution `π`.
1. If `M` has repeated rows then, assuming the Unique Games Conjecture, there is `δ > 0` such
   that for all `ε, λ > 0` it is NP-hard to find a `(k, δ)`-coloring of a regular `λ`-one-sided
   expander with an `(M, ε)`-coloring (`BHSV25.expanderColoring_repeatedRows_hardness`). This is
   Corollary 8.3, the introduction's "`M`-expander-coloring is NP-hard".
2. Assuming the Unique Games Conjecture, for all `ε, λ > 0` and `γ ∈ (0, α)`, it is NP-hard to
   find a `(k, α - γ)`-coloring of a regular `λ`-one-sided expander with an `(M, ε)`-coloring
   (`BHSV25.expanderColoring_hardness`). This is Theorem 8.2, the introduction's
   "`(M, α - γ)`-expander-coloring is NP-hard".
-/

public section

namespace BHSV25

open Filter Topology Turing.MultiTapeTM UniqueGames Cslib.Complexity

/-! ### Independent sets and vertex covers -/

/-- **Theorem 7.20** of [BHSV25]: for every `c > 0`, `λ ∈ (0, 1)` and `γ ∈ (0, 1/4)`, one
algorithm that, on regular graphs with an independent set of `(1/2 - γ) n` vertices, outputs an
independent set of at least `(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices, running in time
`poly(n) · (1 - λ)^{-O(1)} · (γ / (1 - λ))^{-O(t)}` on regular graphs with at most `t` eigenvalues
at most `-λ`, for every `t`. -/
theorem independentSet_bottomRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 →
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool, ∃ K : Graph → ℝ,
          RunsInTimeWith A encGraph Encoding.encBits K C ∧
          ∀ G : Graph, G.IsRegular →
            (∀ t : ℕ, (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
              K G ≤ ((D : ℝ) / (1 - lam)) ^ D * ((D : ℝ) * (1 + (1 - lam) / γ)) ^ (D * (t + 1))) ∧
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ (G.vertexSet (A G)).card) :=
  sorry

/-- **Theorem 1.1** of [BHSV25], full version (Corollary 7.21): for every `c > 0`,
`λ ∈ (0, 1/2)` and `γ ∈ (0, 1/4)`, one algorithm that, on regular graphs with an independent set
of `(1/2 - γ) n` vertices, outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n` vertices, running in time
`poly(n) · (1 - √(2λ))^{-O(1)} · (γ / (1 - √(2λ)))^{-O(t/λ²)}` on regular graphs with at most `t`
eigenvalues larger than `λ` (`λ`-one-sided expanders for `t = 1`), for every `t`. -/
theorem independentSet_approximation :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 / 2 →
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool, ∃ K : Graph → ℝ,
          RunsInTimeWith A encGraph Encoding.encBits K C ∧
          ∀ G : Graph, G.IsRegular →
            (∀ t : ℕ, G.numEigGT lam ≤ t →
              K G ≤ ((D : ℝ) / (1 - Real.sqrt (2 * lam))) ^ D *
                ((D : ℝ) * (1 + (1 - Real.sqrt (2 * lam)) / γ)) ^
                  (D * (⌈(t : ℝ) / lam ^ 2⌉₊ + 1))) ∧
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - Real.sqrt (2 * lam))) * G.1 ≤
                (G.vertexSet (A G)).card) :=
  sorry

/-- **Corollary 1.2** of [BHSV25]: for every `ε > 0`, a `(5/3 + ε)`-approximation algorithm for
vertex cover on regular `λ₀`-one-sided expanders, for some `λ₀ > 0`, running in time `K · m^C`
with `C` independent of `ε`. -/
theorem vertexCover_approximation :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ K : ℝ,
      ∃ A : Graph → List Bool, RunsInTime A encGraph Encoding.encBits K C ∧
        ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam₀ →
          G.IsVertexCover (G.vertexSet (A G)) ∧
          ((G.vertexSet (A G)).card : ℝ) ≤ (5 / 3 + ε) * G.vertexCoverNumber :=
  sorry

/-! ### Algorithms for 3-colorable one-sided expanders -/

/-- **Theorem 1.3** of [BHSV25], full version (Theorem 7.9): for `δ ∈ [0, c₀)` and
`γ, λ ∈ (0, c₀)`, an algorithm running in time `n^{O(1)} · O_{δ,γ,λ}(1)` that, on regular
`λ`-one-sided expanders with a partition into `3` parts of at most `(1/2 - γ) n` vertices each
whose inside edges are covered by `δ n` vertices, outputs `3` independent sets covering all but
`O(λ / γ⁸ + δ / (λ γ⁸)) n` vertices. -/
theorem threeColoring_balanced :
    ∃ C : ℕ, ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ γ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < γ → γ < c₀ →
      0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
            (∃ χ : Fin G.1 → Fin 3, G.IsAlmostProper χ δ ∧
              ∀ a, ((Finset.univ.filter (χ · = a)).card : ℝ) ≤ (1 / 2 - γ) * G.1) →
            G.IsColoring 3 (B * (lam + δ / lam) / γ ^ 8) (A G) :=
  sorry

/-- **Corollary 1.4** of [BHSV25]: for every `λ > 0`, an algorithm running in time `K · m^C`, with
`C` independent of `λ`, that, on regular `λ`-one-sided expanders with `3` independent sets
covering all but `λ n` vertices, outputs `3` independent sets of which one has at least
`(1/2 - f λ) n` vertices or which cover all but `f λ · n` vertices, where `f λ → 0` as
`λ → 0`. -/
theorem threeColoring_independentSet_or_coloring :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧ ∃ C : ℕ,
      ∀ lam : ℝ, 0 < lam → ∃ K : ℝ,
        ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 lam →
            G.IsPartialColoring 3 (A G) ∧
            ((∃ a < 3, (1 / 2 - f lam) * G.1 ≤ G.classSize 3 (A G) a) ∨
              (1 - f lam) * G.1 ≤ G.numColored 3 (A G)) :=
  sorry

/-! ### Random planting -/

open Classical in
/-- **Theorem 7.12** of [BHSV25] (random planting, partial recovery), with an additional error `ε`:
for `k ≥ 3` and every `ε > 0`, one algorithm that, on the graph obtained by randomly planting a
`k`-coloring in a `d`-regular graph with at most `t` eigenvalues at least `λ₀`, for every `t`,
with probability at least `1 - O_k(1/n)` runs in time `n^{O(1)} · (O_{k,ε}(1))^t` and outputs a
`(k, O_k(1/(d + 1)^γ) + ε)`-coloring. The paper's theorem has the error `O_k(1/d^{Ω(1)})`, without
`ε`, in time `n^{O(1)} · (O_k(1))^t`; see the module doc. -/
theorem plantedColoring_partial :
    ∃ C : ℕ, ∃ γ : ℝ, 0 < γ ∧ ∀ k : ℕ, 3 ≤ k → ∃ lam₀ B P : ℝ, 0 < lam₀ ∧
      ∀ ε : ℝ, 0 < ε → ∃ D : ℕ, ∃ A : Graph → List ℕ, ∃ K : Graph → ℝ,
        RunsInTimeWith A encGraph encColoring K C ∧
        ∀ (H : Graph) (d : ℕ), H.2.IsRegularOfDegree d → ∀ t : ℕ,
          (Finset.univ.filter fun i ↦ lam₀ ≤ H.eig i).card ≤ t →
          1 - P / H.1 ≤ H.plantProb k fun G ↦ K G ≤ (D : ℝ) ^ (t + 1) ∧
            G.IsColoring k (B / ((d : ℝ) + 1) ^ γ + ε) (A G) :=
  sorry

open Classical in
/-- **Theorem 7.17** of [BHSV25] (random planting, full recovery): for `k ≥ 3`, an algorithm
running in time `n^{O(1)} · O_k(1)` that, on the graph obtained by randomly planting a
`k`-coloring in a `d`-regular `λ₀`-one-sided expander with `d ≥ d₀`, outputs with probability at
least `1 - O_k(1/n)` a proper `k`-coloring. -/
theorem plantedColoring_full :
    ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ lam₀ P : ℝ, 0 < lam₀ ∧ ∃ d₀ : ℕ, ∃ K : ℝ,
      ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
        ∀ (H : Graph) (d : ℕ), H.2.IsRegularOfDegree d → d₀ ≤ d →
          H.IsOneSidedExpander lam₀ →
          1 - P / H.1 ≤ H.plantProb k fun G ↦ G.IsColoring k 0 (A G) :=
  sorry

/-! ### Hardness for almost 3-colorable graphs -/

/-- **Theorem 1.5** of [BHSV25] (Corollary 8.4): assuming the Unique Games Conjecture, for all
`ε > 0` and `γ ∈ (0, 1/2)` there is `f` with `f n → 0` such that it is NP-hard to find `3`
independent sets covering `(1/2 + γ) n` vertices in a regular graph on `n` vertices with second
eigenvalue at most `f n` and `3` independent sets covering `(1 - ε) n` vertices. -/
theorem threeColoring_unbalanced_hardness (hUGC : KhotUGC) :
    ∀ ε γ : ℝ, 0 < ε → 0 < γ → γ < 1 / 2 →
      ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
        PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
          G.IsOneSidedExpander (f G.1) ∧ G.HasColoring 3 ε) 3 (1 / 2 - γ)) :=
  sorry

/-- **Theorem 1.6** of [BHSV25] (Theorem 8.6): assuming the Unique Games Conjecture, for every
`ε > 0` there is `R` such that for every `γ ∈ (0, 2/9)` there is `f` with `f n → 0` such that it is
NP-hard to find `3` independent sets covering `(7/9 + γ) n` vertices in a regular graph on `n`
vertices with `3` independent sets of the same size covering `(1 - ε) n` vertices, third
eigenvalue at most `f n` and at most `R` eigenvalues larger than `f n` in absolute value. -/
theorem threeColoring_lowRank_hardness (hUGC : KhotUGC) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ γ : ℝ, 0 < γ → γ < 2 / 9 →
      ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
        PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
          (∃ c, G.IsColoring 3 ε c ∧ ∀ a < 3, G.classSize 3 c a = G.classSize 3 c 0) ∧
          G.numEigGT (f G.1) ≤ 2 ∧ (Finset.univ.filter fun i ↦ f G.1 < |G.eig i|).card ≤ R) 3
            (2 / 9 - γ)) :=
  sorry

/-! ### Threshold ranks -/

/-- **Theorem 4.1** of [BHSV25]: for a symmetric matrix with nonnegative entries and eigenvalues
in `[-1, 1]`, `λ ≥ 0` and `σ ∈ (0, 1)`,
`σ² · #{eigenvalues ≤ -λ} ≤ #{eigenvalues ≥ (λ² - σ) / (1 - σ)}`. -/
theorem thresholdRank {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) (hnorm : ∀ i, |hA.eigenvalues i| ≤ 1)
    (lam σ : ℝ) (hlam : 0 ≤ lam) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    σ ^ 2 * ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -lam).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ (lam ^ 2 - σ) / (1 - σ) ≤ hA.eigenvalues i).card :=
  sorry

/-- **Theorem 1.7** of [BHSV25]: for every graph and all `τ ≥ 0` and `τ' < τ²`, the spectrum `σ(G)`
of its normalized adjacency matrix satisfies
`((τ² - τ') / (1 - τ'))² · |σ(G) ∩ (-∞, -τ]| ≤ |σ(G) ∩ [τ', ∞)|`. -/
theorem thresholdRank_graph (G : Graph) (τ τ' : ℝ) (hτ : 0 ≤ τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card :=
  sorry

/-! ### The meta-theorems -/

/-- **Theorem 1.8 (1)** of [BHSV25], full version (Corollary 7.2): for every model `M` without
repeated rows, `δ ∈ [0, c₀)` and `λ ∈ (0, c₀)`, an algorithm running in time
`n^{O(1)} · O_{δ,λ,M}(1)` that, on regular `λ`-one-sided expanders with an `(M, δ)`-coloring,
outputs a `(k, O_M(√δ + λ + δ/λ))`-coloring. -/
theorem expanderColoring_distinctRows :
    ∃ C : ℕ, ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ), IsModel M → Function.Injective M →
      ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
            G.IsColoring k (B * (Real.sqrt δ + lam + δ / lam)) (A G) :=
  sorry

/-- **Theorem 1.8 (2)** of [BHSV25] (Corollary 8.3): assuming the Unique Games Conjecture, for
every model `M` with repeated rows there is `δ > 0` such that, for all `ε, λ > 0`, it is NP-hard to
find a `(k, δ)`-coloring of a regular `λ`-one-sided expander with an `(M, ε)`-coloring. -/
theorem expanderColoring_repeatedRows_hardness (hUGC : KhotUGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (hrows : ¬ Function.Injective M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε lam : ℝ, 0 < ε → 0 < lam →
      PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
        G.IsOneSidedExpander lam ∧ G.MColorable M ε) k δ) :=
  sorry

/-- **Theorem 1.9 (1)** of [BHSV25], full version (Theorem 7.1): for every model `M` with
stationary distribution `π`, `δ ∈ [0, c₀)` and `λ ∈ (0, c₀)`, an algorithm running in time
`n^{O(1)} · O_{δ,λ,M}(1)` that, on regular `λ`-one-sided expanders with an `(M, δ)`-coloring,
outputs a `(k', α + O_M(√δ + λ + δ/λ))`-coloring, where `k'` is the number of distinct rows of
`M` and `α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)`. -/
theorem expanderColoring_algorithm :
    ∃ C : ℕ, ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ), IsModel M →
      IsStationary M π →
      ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
            G.IsColoring (Nat.card (Set.range M))
              (alpha M π + B * (Real.sqrt δ + lam + δ / lam)) (A G) :=
  sorry

/-- **Theorem 1.9 (2)** of [BHSV25] (Theorem 8.2): assuming the Unique Games Conjecture, for
every model `M` with stationary distribution `π`, all `ε, λ > 0` and `γ ∈ (0, α)`, it is NP-hard to
find a `(k, α - γ)`-coloring of a regular `λ`-one-sided expander with an `(M, ε)`-coloring. -/
theorem expanderColoring_hardness (hUGC : KhotUGC) {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : IsModel M) (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∀ γ ε lam : ℝ, 0 < γ → γ < alpha M π → 0 < ε → 0 < lam →
      PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
        G.IsOneSidedExpander lam ∧ G.MColorable M ε) k (alpha M π - γ)) :=
  sorry

end BHSV25
