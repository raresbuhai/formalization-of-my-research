module

public import BHSV25.Model

/-!
# Main results: statements

The main results of [BHSV25], with proofs `sorry`. The algorithms are stated in the full versions
of Section 7 (Theorems 7.1, 7.9 and 7.20, Corollaries 7.2 and 7.21), with their errors and running
times, and Corollaries 1.2 and 1.4 with the running times that these give. The hardness results are
Theorems 1.5, 1.6, 1.8 (2) and 1.9 (2), and the spectral result is Theorem 1.7. `lake comparator`
checks that `Solution.lean` proves exactly these statements using only the axioms listed in
`comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BHSV25/Model.lean` (graphs and their encoding, spectra, colorings, models, running times), the
Unique Games Conjecture in `Background/UniqueGames.lean`, the encodings in
`Background/Encoding.lean`, CSLib's multitape Turing machines, complexitylib's polynomial time,
`P`, `NP` and NP-hardness of promise problems, and Mathlib.

Numbers refer to the arXiv version (v2), whose counters are shared within each section.

## Conventions

* **Graphs** are simple, on `n` vertices, encoded by their adjacency tables. All graphs in the
  algorithmic and hardness results are **regular**, as in the paper. The spectrum is that of the
  normalized adjacency matrix (`A / d` for a `d`-regular graph), and a **`λ`-one-sided expander**
  has second largest eigenvalue at most `λ` (`BHSV25.Graph.IsOneSidedExpander`). Lean reserves
  `λ`, so it is written `lam`.
* **Running times** (`BHSV25.RunsInTime A encGraph enc K C`): a deterministic multitape Turing
  machine computes `A` in at most `K (m + 1)^C` steps on graphs whose encoding has length `m`
  (about `n²` for `n` vertices), in polynomial space. A running time `n^{O(1)} · g(p)` of the
  paper, for parameters `p`, is stated as: there is `C`, fixed before all parameters, such that for
  all values of `p` some algorithm runs in time `K · m^C`. Here `K` is the paper's `g(p)` where it
  is explicit (Theorem 7.20, Corollary 7.21), and otherwise any number depending on `p` (the
  paper's `O_p(1)`).
* **Algorithms depend on the parameters**, as in the paper's theorems: for all values of `δ`, `γ`,
  `λ`, `t` and `c` there is an algorithm. They are not given the promised independent sets or
  colorings.
* **Constants**: an `O(·)` is a constant fixed before the parameters it does not depend on, and
  "for `δ, γ, λ` small enough" is `δ, γ, λ < c₀` for some `c₀ > 0`. In Theorem 7.1 and
  Corollary 7.2 both depend on the model `M` (the paper's `O_M`).
* **`o_{λ→0}(1)`** (in Corollary 1.4) is a function `f` with `f λ → 0` as `λ → 0⁺`.
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

## Theorem 7.20

For every constant `c > 0`, all `λ ∈ (0, 1)`, `t` and `γ ∈ (0, 1/4)`: an algorithm running in time
`poly(n) · (γ / (1 - λ))^{-O(t)}` that, on regular graphs with at most `t` eigenvalues at most
`-λ` and an independent set of `(1/2 - γ) n` vertices, outputs an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices (`BHSV25.independentSet_bottomRank`).

* The degree of `poly(n)` is independent of all parameters, and the constant in `O(t)` depends
  only on `c`. The factor is written `(D (1 + (1 - λ) / γ))^{D (t + 1)}`: the `1 +` keeps it at
  least `1` when `γ > 1 - λ`, where the bound on the output is negative anyway.
* The output is an independent set on every regular graph with at most `t` eigenvalues at most
  `-λ`, whether or not it has the promised one.

## Theorem 1.1 (Corollary 7.21)

For every constant `c > 0`, all `λ ∈ (0, 1/2)`, `t` and `γ ∈ (0, 1/4)`: an algorithm running in
time `poly(n) · (γ / (1 - √(2λ)))^{-O(t/λ²)}` that, on regular graphs with at most `t` eigenvalues
larger than `λ` and an independent set of `(1/2 - γ) n` vertices, outputs an independent set of at
least `(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n` vertices (`BHSV25.independentSet_approximation`).

* Theorem 1.1 is the case `t = 1`, of `λ`-one-sided expanders (`BHSV25.Graph.IsOneSidedExpander`
  is `numEigGT λ ≤ 1`), with `γ ≤ 1/10`: the loss `γ + (4 + c) γ / (1 - √(2λ))` is
  `(5 + o_{λ→0}(1)) γ` for small `c`. Larger `t` is the paper's remark that the algorithm
  extends to bounded threshold rank.
* `λ < 1/2`, so that `√(2λ) < 1`.
* "Larger than `λ`" is strict (`BHSV25.Graph.numEigGT`), which makes the hypothesis weaker:
  Corollary 7.21 counts the eigenvalues at least `λ`. Corollary 4.2 for a threshold slightly above
  `λ` still bounds the number of eigenvalues at most `-√(2λ)` by `t / λ²`.
* As in Theorem 7.20, the factor is `(D (1 + (1 - √(2λ)) / γ))^{D (⌈t / λ²⌉ + 1)}`, and the
  output is always an independent set.

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
   that for all `ε, λ > 0` no polynomial-time algorithm finds a `(k, δ)`-coloring of every
   regular `λ`-one-sided expander with an `(M, ε)`-coloring, unless `NP ⊆ P`
   (`BHSV25.expanderColoring_repeatedRows_hardness`). This is Corollary 8.3, which gives the
   introduction's "`M`-expander-coloring is NP-hard" in the form of hardness used here.
2. Assuming the Unique Games Conjecture, for all `γ, ε, λ > 0`, no polynomial-time algorithm finds a
   `(k, α - γ)`-coloring of every regular `λ`-one-sided expander with an `(M, ε)`-coloring, unless
   `NP ⊆ P` (`BHSV25.expanderColoring_hardness`). This is Theorem 8.2; it gives the
   introduction's "`(M, α - γ)`-expander-coloring is NP-hard" in the same form.
-/

public section

namespace BHSV25

open Filter Topology Turing.MultiTapeTM UniqueGames

/-! ### Independent sets and vertex covers -/

/-- **Theorem 7.20** of [BHSV25]: for every `c > 0`, `λ ∈ (0, 1)`, `t` and `γ ∈ (0, 1/4)`, an
algorithm running in time `poly(n) · (γ / (1 - λ))^{-O(t)}` that, on regular graphs with at most
`t` eigenvalues at most `-λ` and an independent set of `(1/2 - γ) n` vertices, outputs an
independent set of at least `(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices. -/
theorem independentSet_bottomRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ t : ℕ,
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool,
          RunsInTime A encGraph Encoding.encBits
            (((D : ℝ) * (1 + (1 - lam) / γ)) ^ (D * (t + 1))) C ∧
          ∀ G : Graph, G.IsRegular → (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ (G.vertexSet (A G)).card) :=
  sorry

/-- **Theorem 1.1** of [BHSV25], full version (Corollary 7.21): for every `c > 0`,
`λ ∈ (0, 1/2)`, `t` and `γ ∈ (0, 1/4)`, an algorithm running in time
`poly(n) · (γ / (1 - √(2λ)))^{-O(t/λ²)}` that, on regular graphs with at most `t` eigenvalues
larger than `λ` (`λ`-one-sided expanders for `t = 1`) and an independent set of `(1/2 - γ) n`
vertices, outputs an independent set of at least `(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n`
vertices. -/
theorem independentSet_approximation :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 / 2 → ∀ t : ℕ,
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool,
          RunsInTime A encGraph Encoding.encBits
            (((D : ℝ) * (1 + (1 - Real.sqrt (2 * lam)) / γ)) ^
              (D * (⌈(t : ℝ) / lam ^ 2⌉₊ + 1))) C ∧
          ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
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
