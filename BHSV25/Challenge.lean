module

public import BHSV25.Model

/-!
# Main results: statements

The main results of [BHSV25], Theorems 1.1 to 1.9 (Corollaries 1.2 and 1.4 included), with proofs
`sorry`. `lake comparator` checks that `Solution.lean` proves exactly these statements using only
the axioms listed in `comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BHSV25/Model.lean` (graphs and their encoding, spectra, colorings, models), the Unique Games
Conjecture in `Background/UniqueGames.lean`, the encodings in `Background/Encoding.lean`, CSLib's
multitape Turing machines, complexitylib's polynomial time, `P`, `NP` and NP-hardness of promise
problems, and Mathlib.

Numbers refer to the arXiv version (v2), whose counters are shared within each section.

## Conventions

* **Graphs** are simple, on `n` vertices, encoded by their adjacency tables. All graphs in the
  algorithmic and hardness results are **regular**, as in the paper. The spectrum is that of the
  normalized adjacency matrix (`A / d` for a `d`-regular graph), and a **`λ`-one-sided expander**
  has second largest eigenvalue at most `λ` (`BHSV25.Graph.IsOneSidedExpander`). Lean reserves
  `λ`, so it is written `lam`.
* **Algorithms** are deterministic multitape Turing machines running in time polynomial in the
  length of the encoded graph, so in `n` (complexitylib's
  `Turing.MultiTapeTM.ComputableInPolyTime`). "For every `λ` there is a polynomial-time
  algorithm" lets the algorithm, and the degree of the polynomial, depend on `λ`. The algorithms
  are not given the promised independent sets or colorings, nor their parameters.
* **`o_{λ→0}(1)`** is a function `f` with `f λ → 0` as `λ → 0⁺`, one for all `λ`.
* **Outputs**: an independent set or a vertex cover is a list of membership bits, one per vertex
  (`BHSV25.Graph.vertexSet`); a coloring is a list of colors, one per vertex, with colors `≥ k`
  read as "uncolored" (`BHSV25.Graph.color`). "`k` independent sets covering all but a `δ`
  fraction of the vertices" is a `(k, δ)`-coloring (`BHSV25.Graph.IsColoring`).
* **Hardness** ("NP-hard assuming the Unique Games Conjecture") is stated as: assuming the
  Unique Games Conjecture (`UniqueGames.UGC`), if some polynomial-time algorithm solves the
  problem on every instance satisfying the promise, then `NP ⊆ P` (`BHSV25.NPSubsetP`). This is
  the consequence of NP-hardness that matters for algorithms. It is weaker than NP-hardness of
  the corresponding gap problems (`Cslib.Complexity.PromiseProblem.NPHard`): a proof need not
  exhibit a reduction.
  * `UniqueGames.UGC` is the form used for [BGHKLMM26] in this repository: for every small
    `ε > 0`, some number of labels makes it NP-hard to tell simple bi-regular bipartite instances
    of value at least `1 - ε` from those of value at most `ε`. It implies Khot's form.
  * The paper's reductions start from Fact 8.1, the hardness of almost-bipartite independent set
    that Bansal and Khot derive from the conjecture (with maximum degree `o(n)`, as in Bafna,
    Hsieh and Kothari). The proofs here derive Fact 8.1 from `UniqueGames.UGC` too.
  * The conclusion is `NP ⊆ P`, not `NP ⊆ BPP`, so the proofs replace the random biregular
    graphs of the paper's reductions by explicit ones.
* Where the body has a stronger version of a statement of the introduction, the stronger version
  is stated, and the introduction's follows from it as explained below. Algorithms keep the
  introduction's qualitative form: errors are functions tending to `0`, and running times are
  polynomial, without the body's explicit dependence on the parameters.

## Theorem 1.1 (and Corollary 7.21)

For every `λ ∈ (0, 1)` and every `t` there is a polynomial-time algorithm that, given a regular
graph with at most `t` eigenvalues larger than `λ` and an independent set of at least
`(1/2 - γ) n` vertices for some `γ ∈ [0, 1/10]`, outputs an independent set of at least
`(1/2 - (5 + f λ) γ) n` vertices, where `f λ → 0` (`BHSV25.independentSet_approximation`).

* Theorem 1.1 is the case `t = 1`, of `λ`-one-sided expanders
  (`BHSV25.Graph.IsOneSidedExpander` is `numEigGT λ ≤ 1`). Corollary 7.21, the full version,
  allows any `t`, which only changes the running time; so does the paper's remark that the
  algorithm extends to bounded threshold rank.
* `λ` ranges over `(0, 1)`: the guarantee concerns `λ → 0`, and for `λ ≥ 1` every regular graph
  has at most one eigenvalue larger than `λ`. For `λ < 1`, Corollary 4.2 with `σ = λ` bounds the
  number of eigenvalues below `-√(2λ - λ²)`, a threshold `< 1`, which is what the proof uses.
* The guarantee holds for every `γ ∈ [0, 1/10]` for which the graph has an independent set of
  `(1/2 - γ) n` vertices; the algorithm does not know `γ`.
* "Larger than `λ`" is strict (`BHSV25.Graph.numEigGT`), which makes the hypothesis weaker:
  Corollary 7.21 counts the eigenvalues at least `λ`, so the proof applies it to some
  `λ' ∈ (λ, 1)` with `λ' → 0` as `λ → 0`, such as `λ (3 - λ) / 2`.

## Corollary 1.2

For every `ε > 0` there are `λ₀ > 0` and a polynomial-time algorithm that, on every regular
`λ₀`-one-sided expander, outputs a vertex cover of size at most `(5/3 + ε)` times the minimum
(`BHSV25.vertexCover_approximation`). The paper's `1.6667` is `5/3 + 1/30000`.

## Theorem 1.3 (Theorem 7.9)

For every `λ > 0` there is a polynomial-time algorithm that, given a regular `λ`-one-sided
expander with `3` independent sets of at most `(1/2 - f λ) n` vertices each that cover all but
`λ n` vertices, outputs `3` independent sets covering all but `f λ · n` vertices, where
`f λ → 0` (`BHSV25.threeColoring_balanced`). One function `f` serves for both `o_{λ→0}(1)`.

* The introduction asks for a proper `3`-coloring. Theorem 7.9, the paper's full version, allows
  a `3`-partition whose monochromatic edges are covered by `δ n` vertices; removing them leaves
  `3` independent sets covering all but `δ n` vertices (and conversely, the uncovered vertices can
  join the smallest class). This is stated in qualitative form, without Theorem 7.9's explicit
  error and running time. In that form, taking `δ = λ` loses nothing, as both hypotheses get
  weaker when their parameter grows.
* Theorem 7.9's error is `O(λ + δ/λ)` times a power of `1/γ`, for `λ` the second eigenvalue.
  With `δ = λ`, the proof uses `√λ` instead, as an upper bound on the second eigenvalue; the
  variance bound (Lemma 6.1) only needs an upper bound.

## Corollary 1.4

For every `λ > 0` there is a polynomial-time algorithm that, given a regular `λ`-one-sided
expander with `3` independent sets covering all but `λ n` vertices, outputs `3` independent sets
of which one has at least `(1/2 - f λ) n` vertices or which together cover all but `f λ · n`
vertices, where `f λ → 0` (`BHSV25.threeColoring_independentSet_or_coloring`).

* The introduction asks for `3`-colorable graphs; the paper notes that its algorithms for
  `3`-colorable one-sided expanders handle almost `3`-colorable ones too, and so does the proof
  here. Let `g` be the function of Theorem 1.3. If every class has at most `(1/2 - g λ) n`
  vertices, Theorem 1.3 covers all but `g λ · n` vertices. Otherwise the largest class is an
  independent set of more than `(1/2 - g λ) n` vertices, and Theorem 1.1 finds one of
  `(1/2 - (5 + o(1)) g λ) n`. So `f` is larger than `g`, about `6 g`.

## Theorem 1.5 (Corollary 8.4)

Assuming the Unique Games Conjecture, for all `ε, γ, λ > 0`, no polynomial-time algorithm finds `3`
independent sets covering at least `(1/2 + γ) n` vertices in every regular `λ`-one-sided expander
with `3` independent sets covering `(1 - ε) n` vertices, unless `NP ⊆ P`
(`BHSV25.threeColoring_unbalanced_hardness`). This is Corollary 8.4, the full version; the
introduction's statement is the case `ε = γ = λ`.

## Theorem 1.6 (Theorem 8.6)

Assuming the Unique Games Conjecture, for every `ε > 0` there is `R` such that, for every
`γ > 0`, no polynomial-time algorithm finds `3` independent sets covering at least `(7/9 + γ) n`
vertices in every regular graph with
1. `3` disjoint independent sets of at least `(1/3 - ε) n` vertices each,
2. at most two eigenvalues larger than `ε`,
3. at most `R` eigenvalues larger than `ε` in absolute value,

unless `NP ⊆ P` (`BHSV25.threeColoring_lowRank_hardness`). The introduction's statement asks for
coverage `0.9`, the case `γ = 11/90`; the coverage `7/9 + γ` is that of Theorem 8.6, the full
version, whose hypothesis `λ₃ = o(1)` gives conditions 2 and 3 by Theorem 1.7.

## Theorem 1.7 (Theorem 4.1)

For all `τ > 0` and `τ' < τ²`, the number of eigenvalues at most `-τ` and the number of
eigenvalues at least `τ'` satisfy
`((τ² - τ') / (1 - τ'))² · #{eigenvalues ≤ -τ} ≤ #{eigenvalues ≥ τ'}`.
It is stated for every graph (`BHSV25.thresholdRank_graph`), as in the introduction, and for
every symmetric matrix with nonnegative entries and eigenvalues in `[-1, 1]`
(`BHSV25.thresholdRank`), as in Theorem 4.1, the full version, whose parameter `σ` is
`(τ² - τ') / (1 - τ')`.

## Theorem 1.8 (Corollaries 7.2 and 8.3)

Let `M` be a model (`BHSV25.IsModel`): a reversible row-stochastic matrix with zero diagonal and
second largest eigenvalue at most `0`.
1. If `M` has no repeated rows, a polynomial-time algorithm solves `M`-expander-coloring
   (`BHSV25.expanderColoring_distinctRows`).
2. If `M` has repeated rows then, assuming the Unique Games Conjecture, there is `δ > 0` such
   that for all `ε, λ > 0` no polynomial-time algorithm finds a `(k, δ)`-coloring of every
   regular `λ`-one-sided expander with an `(M, ε)`-coloring, unless `NP ⊆ P`
   (`BHSV25.expanderColoring_repeatedRows_hardness`). This is Corollary 8.3. It gives the
   introduction's "`M`-expander-coloring is NP-hard" in the form of hardness used here (an
   algorithm solving it gives `NP ⊆ P`): take `ε = δ/2` in the definition of
   `BHSV25.SolvesExpanderColoring`, and its `δ'` as both `ε` and `λ` here.

## Theorem 1.9 (Theorems 7.1 and 8.2)

Let `M` be a model with stationary distribution `π`, and
`α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)` (`BHSV25.alpha`).
1. A polynomial-time algorithm solves `(M, α)`-expander-coloring
   (`BHSV25.expanderColoring_algorithm`).
2. Assuming the Unique Games Conjecture, for all `γ, ε, λ > 0`, no polynomial-time algorithm finds a
   `(k, α - γ)`-coloring of every regular `λ`-one-sided expander with an `(M, ε)`-coloring, unless
   `NP ⊆ P` (`BHSV25.expanderColoring_hardness`). This is Theorem 8.2; it gives the
   introduction's "`(M, α - γ)`-expander-coloring is NP-hard", in the same form, as for
   Theorem 1.8.

Details:
* **Reversibility** is with respect to a positive `π`, as Lemma 7.3 uses.
* **`π`** is the unique stationary distribution of a model; the theorem is stated for every
  positive `π` summing to `1` in detailed balance with `M` (`BHSV25.IsStationary`).
* **One algorithm for every `ε`**, as in the paper's definition of `(M, α)`-expander-coloring.
  Theorem 7.1's algorithm depends on `δ` and `λ`, but it enumerates a net of a subspace of
  dimension `O_M(1)`; a net of precision `1/poly(n)` takes polynomial time and serves every `δ`
  at once. The guarantee holds at every size: on the graphs that are `(M, δ)`-colorable
  `δ`-one-sided expanders for all `δ > 0`, the algorithm leaves at most `α n` vertices uncovered.
* `(k', ·)`-colorings with `k' ≤ k` (Theorem 7.1) are `(k, ·)`-colorings with empty classes.
-/

public section

namespace BHSV25

open Filter Topology Turing.MultiTapeTM UniqueGames

/-! ### Independent sets and vertex covers -/

/-- **Theorem 1.1** of [BHSV25] (Corollary 7.21): for every `λ ∈ (0, 1)` and every `t`, a
polynomial-time algorithm that, on regular graphs with at most `t` eigenvalues larger than `λ`
(`λ`-one-sided expanders for `t = 1`) and an independent set of `(1/2 - γ) n` vertices for some
`γ ∈ [0, 1/10]`, outputs an independent set of at least `(1/2 - (5 + f λ) γ) n` vertices, where
`f λ → 0` as `λ → 0`. -/
theorem independentSet_approximation :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ t : ℕ,
        ∃ A : Graph → List Bool, ComputableInPolyTime A encGraph Encoding.encBits ∧
          ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 / 10 → G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - (5 + f lam) * γ) * G.1 ≤ (G.vertexSet (A G)).card :=
  sorry

/-- **Corollary 1.2** of [BHSV25]: for every `ε > 0`, a polynomial-time `(5/3 + ε)`-approximation
algorithm for vertex cover on regular `λ₀`-one-sided expanders, for some `λ₀ > 0`. -/
theorem vertexCover_approximation :
    ∀ ε : ℝ, 0 < ε → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ A : Graph → List Bool, ComputableInPolyTime A encGraph Encoding.encBits ∧
        ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam₀ →
          G.IsVertexCover (G.vertexSet (A G)) ∧
          ((G.vertexSet (A G)).card : ℝ) ≤ (5 / 3 + ε) * G.vertexCoverNumber :=
  sorry

/-! ### Algorithms for 3-colorable one-sided expanders -/

/-- **Theorem 1.3** of [BHSV25] (Theorem 7.9): for every `λ > 0`, a polynomial-time algorithm that,
on regular `λ`-one-sided expanders with `3` independent sets of at most `(1/2 - f λ) n` vertices
each that cover all but `λ n` vertices, outputs `3` independent sets covering all but `f λ · n`
vertices, where `f λ → 0` as `λ → 0`. -/
theorem threeColoring_balanced :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
            (∃ c, G.IsColoring 3 lam c ∧
              ∀ a < 3, (G.classSize 3 c a : ℝ) ≤ (1 / 2 - f lam) * G.1) →
            G.IsColoring 3 (f lam) (A G) :=
  sorry

/-- **Corollary 1.4** of [BHSV25]: for every `λ > 0`, a polynomial-time algorithm that, on regular
`λ`-one-sided expanders with `3` independent sets covering all but `λ n` vertices, outputs `3`
independent sets of which one has at least `(1/2 - f λ) n` vertices or which cover all but
`f λ · n` vertices, where `f λ → 0` as `λ → 0`. -/
theorem threeColoring_independentSet_or_coloring :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 lam →
            G.IsPartialColoring 3 (A G) ∧
            ((∃ a < 3, (1 / 2 - f lam) * G.1 ≤ G.classSize 3 (A G) a) ∨
              (1 - f lam) * G.1 ≤ G.numColored 3 (A G)) :=
  sorry

/-! ### Hardness for almost 3-colorable graphs -/

/-- **Theorem 1.5** of [BHSV25] (Corollary 8.4): assuming the Unique Games
Conjecture, for all `ε, γ, λ > 0`, no polynomial-time algorithm finds `3` independent sets
covering `(1/2 + γ) n` vertices in every regular `λ`-one-sided expander with `3` independent sets
covering `(1 - ε) n` vertices, unless `NP ⊆ P`. -/
theorem threeColoring_unbalanced_hardness (hUGC : UGC) :
    ∀ ε γ lam : ℝ, 0 < ε → 0 < γ → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 ε →
          G.IsColoring 3 (1 / 2 - γ) (A G)) →
        NPSubsetP :=
  sorry

/-- **Theorem 1.6** of [BHSV25] (Theorem 8.6): assuming the Unique Games
Conjecture, for every `ε > 0` there is `R` such that for every `γ > 0` no polynomial-time
algorithm finds `3` independent sets covering `(7/9 + γ) n` vertices in every regular graph with
`3` disjoint independent sets of `(1/3 - ε) n` vertices each, at most two eigenvalues larger than
`ε` and at most `R` eigenvalues larger than `ε` in absolute value, unless `NP ⊆ P`. -/
theorem threeColoring_lowRank_hardness (hUGC : UGC) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ γ : ℝ, 0 < γ →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular →
          (∃ c, G.IsPartialColoring 3 c ∧ ∀ a < 3, (1 / 3 - ε) * G.1 ≤ G.classSize 3 c a) →
          G.numEigGT ε ≤ 2 →
          (Finset.univ.filter fun i ↦ ε < |G.eig i|).card ≤ R →
          G.IsColoring 3 (2 / 9 - γ) (A G)) →
        NPSubsetP :=
  sorry

/-! ### Threshold ranks -/

/-- **Theorem 4.1** of [BHSV25], in the parameters of Theorem 1.7: for a symmetric matrix with
nonnegative entries and eigenvalues in `[-1, 1]`, and all `τ > 0` and `τ' < τ²`,
`((τ² - τ') / (1 - τ'))² · #{eigenvalues ≤ -τ} ≤ #{eigenvalues ≥ τ'}`. -/
theorem thresholdRank {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) (hnorm : ∀ i, |hA.eigenvalues i| ≤ 1)
    (τ τ' : ℝ) (hτ : 0 < τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 *
        ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ hA.eigenvalues i).card :=
  sorry

/-- **Theorem 1.7** of [BHSV25]: for every graph and all `τ > 0` and `τ' < τ²`, the spectrum `σ(G)`
of its normalized adjacency matrix satisfies
`((τ² - τ') / (1 - τ'))² · |σ(G) ∩ (-∞, -τ]| ≤ |σ(G) ∩ [τ', ∞)|`. -/
theorem thresholdRank_graph (G : Graph) (τ τ' : ℝ) (hτ : 0 < τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card :=
  sorry

/-! ### The meta-theorems -/

/-- **Theorem 1.8 (1)** of [BHSV25] (Corollary 7.2): for every model `M` without repeated rows, a
polynomial-time algorithm solves `M`-expander-coloring. -/
theorem expanderColoring_distinctRows {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M)
    (hrows : Function.Injective M) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M 0 A :=
  sorry

/-- **Theorem 1.8 (2)** of [BHSV25] (Corollary 8.3): assuming the Unique Games
Conjecture, for every model `M` with repeated rows there is `δ > 0` such that, for all
`ε, λ > 0`, no polynomial-time algorithm finds a `(k, δ)`-coloring of every regular `λ`-one-sided
expander with an `(M, ε)`-coloring, unless `NP ⊆ P`. -/
theorem expanderColoring_repeatedRows_hardness (hUGC : UGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (hrows : ¬ Function.Injective M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε lam : ℝ, 0 < ε → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M ε →
          G.IsColoring k δ (A G)) →
        NPSubsetP :=
  sorry

/-- **Theorem 1.9 (1)** of [BHSV25] (Theorem 7.1): for every model `M` with stationary
distribution `π`, a polynomial-time algorithm solves `(M, α)`-expander-coloring, where
`α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)`. -/
theorem expanderColoring_algorithm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M)
    (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M (alpha M π) A :=
  sorry

/-- **Theorem 1.9 (2)** of [BHSV25] (Theorem 8.2): assuming the Unique Games
Conjecture, for every model `M` with stationary distribution `π` and all `γ, ε, λ > 0`, no
polynomial-time algorithm finds a `(k, α - γ)`-coloring of every regular `λ`-one-sided expander
with an `(M, ε)`-coloring, unless `NP ⊆ P`. -/
theorem expanderColoring_hardness (hUGC : UGC) {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : IsModel M) (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∀ γ ε lam : ℝ, 0 < γ → 0 < ε → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M ε →
          G.IsColoring k (alpha M π - γ) (A G)) →
        NPSubsetP :=
  sorry

end BHSV25
