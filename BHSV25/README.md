# BHSV25: Finding colorings in one-sided expanders

The results are [BHSV25]'s algorithms in the full versions of Section 7, with their explicit
errors and running times (Theorems 7.1, 7.9, 7.17 and 7.20, Corollaries 7.2 and 7.21, and
Theorem 7.12 with an additional error `ε`), Corollaries 1.2 and 1.4 with the running times these
give, the hardness results (Theorems 1.5, 1.6, 1.8 (2) and 1.9 (2)) and Theorems 1.7 and 4.1, stated in
[Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them. The
hardness results assume the Unique Games Conjecture on graphs (`UniqueGames.KhotUGC`), and the proof
derives from it the paper's starting point, Bansal and Khot's hardness of almost-bipartite
independent set [BHSV25, Fact 8.1], including Khot and Regev's regularization of Unique Games
instances and Mossel, O'Donnell and Oleszkiewicz's "It Ain't Over Till It's Over".

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v2).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 7.20 | `independentSet_bottomRank` | On regular graphs with an independent set of `(1/2 - γ) n` vertices: one of `(1/2 - γ - (4 + c) γ/(1 - λ)) n`, by one algorithm for all `t`, in time `poly(n) · (1 - λ)^{-O(1)} · (γ/(1 - λ))^{-O(t)}` on the graphs with at most `t` eigenvalues at most `-λ`. |
| Theorem 1.1 (Cor. 7.21) | `independentSet_approximation` | The same for `λ < 1/2`: `(1/2 - γ - (4 + c) γ/(1 - √(2λ))) n`, in time `poly(n) · (1 - √(2λ))^{-O(1)} · (γ/(1 - √(2λ)))^{-O(t/λ²)}` on the graphs with at most `t` eigenvalues above `λ`. |
| Corollary 1.2 | `vertexCover_approximation` | A `(5/3 + ε)`-approximation of vertex cover on regular `λ₀`-one-sided expanders, in time `n^{O(1)} · O_ε(1)`. |
| Theorem 1.3 (Thm. 7.9) | `threeColoring_balanced` | On regular `λ`-one-sided expanders with a partition into `3` parts of at most `(1/2 - γ) n` vertices, proper up to `δ n` vertices: `3` independent sets covering all but `O(λ/γ⁸ + δ/(λ γ⁸)) n`, in time `n^{O(1)} · O_{δ,γ,λ}(1)`. |
| Theorem 7.12 | `plantedColoring_partial` | For `k ≥ 3` and `ε > 0`, one algorithm for all `t` that, on the graph obtained by planting a random `k`-coloring in a `d`-regular graph with at most `t` eigenvalues at least `λ₀`, with probability `1 - O_k(1/n)` runs in time `n^{O(1)} · (O_{k,ε}(1))^t` and outputs a `(k, O_k(1/(d + 1)^γ) + ε)`-coloring. |
| Theorem 7.17 | `plantedColoring_full` | For `k ≥ 3`, on the graph obtained by planting a random `k`-coloring in a `d`-regular `λ₀`-one-sided expander with `d ≥ d₀(k)`: a proper `k`-coloring with probability `1 - O_k(1/n)`, in time `n^{O(1)} · O_k(1)`. |
| Corollary 1.4 | `threeColoring_independentSet_or_coloring` | On regular `λ`-one-sided expanders with `3` independent sets covering all but `λ n` vertices: an independent set of `(1/2 - o_λ(1)) n` vertices or `3` covering all but `o_λ(1) n`, in time `n^{O(1)} · O_λ(1)`. |
| Theorem 1.5 (Cor. 8.4) | `threeColoring_unbalanced_hardness` | Covering `(1/2 + γ) n` vertices of almost `3`-colorable regular graphs with `λ₂ = o(1)` is hard. |
| Theorem 1.6 (Thm. 8.6) | `threeColoring_lowRank_hardness` | Covering `(7/9 + γ) n` vertices is hard with balanced almost-`3`-colorings and `λ₃ = o(1)`. |
| Theorems 1.7 and 4.1 | `thresholdRank_graph`, `thresholdRank` | `((τ² - τ')/(1 - τ'))² #{eig ≤ -τ} ≤ #{eig ≥ τ'}` for graphs, `τ ≥ 0`; `σ² #{eig ≤ -λ} ≤ #{eig ≥ (λ² - σ)/(1 - σ)}` for nonnegative symmetric matrices of norm at most `1`, `λ ≥ 0`, `σ ∈ (0, 1)`. |
| Theorem 1.8 (Cor. 7.2, 8.3) | `expanderColoring_distinctRows`, `expanderColoring_repeatedRows_hardness` | Without repeated rows: a `(k, O_M(√δ + λ + δ/λ))`-coloring of `(M, δ)`-colorable `λ`-one-sided expanders in time `n^{O(1)} · O_{δ,λ,M}(1)`; with repeated rows, `M`-expander-coloring is hard. |
| Theorem 1.9 (Thm. 7.1, 8.2) | `expanderColoring_algorithm`, `expanderColoring_hardness` | A `(k', α + O_M(√δ + λ + δ/λ))`-coloring, `k'` the number of distinct rows of `M`, in time `n^{O(1)} · O_{δ,λ,M}(1)`; `(M, α - γ)`-expander-coloring is hard. |

* **Graphs** are simple and given by their adjacency tables; the spectrum is that of
  `D^(-1/2) A D^(-1/2)`, and a `λ`-one-sided expander has at most one eigenvalue above `λ`.
* **Running times** are those of deterministic multitape Turing machines (`BHSV25.RunsInTime`):
  a time `n^{O(1)} · g(p)` for parameters `p` is a degree `C`, fixed before all parameters, and for
  all values of `p` an algorithm running in time `g(p) · m^C` on inputs of length `m`. As in
  Section 7, the algorithms depend on the parameters. Where the time depends on the number `t` of
  eigenvalues beyond a threshold (Theorems 7.12 and 7.20, Corollary 7.21), one algorithm serves
  all `t`: it runs in time `K G · m^C` on every graph `G`, with `K G ≤ g(t)` on the graphs with at
  most `t` such eigenvalues (`BHSV25.RunsInTimeWith`), and `g` is the paper's explicit factor.
  Theorem 7.20 and Corollary 7.21 have the additional factor `(1 - λ)^{-O(1)}`, independent of
  `t`: the algorithm finds the number of eigenvalues itself, which needs `λ` to precision
  `c (1 - λ)`.
* **Errors** are the body's, with their constants as `∃` quantifiers (`O_M` for constants depending
  on the model). In Theorems 7.1 and 7.9, `λ` is any upper bound on the second eigenvalue, as the
  variance bound (Lemma 6.1) needs only an upper bound.
* **Random planting** (Theorems 7.12 and 7.17) gives every vertex of the host one of `k` colors,
  independently and uniformly, and removes the edges inside the color classes
  (`BHSV25.Graph.plant`); "with high probability" is with probability at least `1 - P/n` over the
  colors (`BHSV25.Graph.plantProb`), with `P` depending only on `k`, on every host. Theorem 7.12
  carries an accuracy `ε`: the algorithm and the base of its running time depend on `ε`, where
  the paper states the time `n^{O(1)} · (O_k(1))^t` without `ε`. That time does not follow from
  the paper's proof, whose net has `d^{O_k(t)}` candidates. Its running time holds with high
  probability, like its output: the algorithm does not know the degree of the host and uses the
  average degree of the planted graph.
* **Hardness** assumes the Unique Games Conjecture in its usual form on graphs
  (`UniqueGames.KhotUGC` in [../Background/UniqueGames.lean](../Background/UniqueGames.lean):
  simple instances on graphs, gap `(1 - ε, ε)` for small `ε`) and concludes NP-hardness
  (`PromiseProblem.NPHard`) of gap problems of colorings, `BHSV25.coloringGap P k δ`: graphs with
  the promised property `P` and a `(k, δ)`-coloring against graphs with none. complexitylib has
  no search problems, so "it is NP-hard to find a `(k, δ)`-coloring" is stated through this gap
  problem; it rules out polynomial-time algorithms finding `(k, δ')`-colorings, `δ' < δ`, unless
  `NP ⊆ P` (`BHSV25.Hard.npSubsetP_of_npHard`). Theorems 1.5 and 1.6 have the body's spectral
  promises `λ₂ = o(1)` and `λ₃ = o(1)`: some `f` with `f n → 0` bounds the second, respectively
  third, eigenvalue of the graphs on `n` vertices. Theorem 1.6 has the body's promise of `3` classes
  of the same size covering `(1 - ε) n` vertices, which gives the introduction's.
* **Models** (`BHSV25.IsModel`) are row-stochastic matrices with zero diagonal, in detailed balance
  with a positive vector, and with at most one positive eigenvalue; `α` is `BHSV25.alpha`, with the
  inner sum over `π_b`. The vector must be positive. The paper's printed definition (Section 3)
  allows `π ≥ 0`, but then every matrix would be reversible (take `π = 0`); the paper's proofs use
  a positive `π` (Lemma 7.3).

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### Running times

Each algorithm is one deterministic machine that reads its parameters in unary together with the
graph, certified with complexitylib's polynomial-time calculus. Fixing the parameters then gives
the running time `K · m^C`, with `C` the degree of that one machine and `K` polynomial in the
length of the parameters ([Time.lean](Time.lean), `BHSV25.runsInTime_graph_fix`).

The algorithms of Theorems 7.12 and 7.20 enumerate a net whose size depends on the number `T` of
rounds of the greedy selection, which they find themselves. Their machines read, with the
parameters and the graph, unary paddings `2^F` for exponents `F` computed from the graph in
polynomial time (`F = ⌈log₂(3 + 12 K)⌉ T` for the net): computing the paddings by doubling, then
running the machine, takes `c (|p| + 1)^C (2^F + 1)^C · m^C` steps
([TimePad.lean](TimePad.lean), `BHSV25.runsInTimeWith_graph_fix_pad`, with complexitylib's
explicit-time combinators). For Theorem 7.20 the parameters have length `O_c((1 + (1 - λ)/γ)/(1 - λ))`
and `T ≤ t`, and for Theorem 7.12 `T ≤ O_k(t)`, which give the stated factors.

### Nets of eigenspaces

A Turing machine cannot compute eigenvectors, so the algorithms enumerate a net of a
low-dimensional eigenspace instead of the paper's random points (Lemma 5.6). The greedy net
([Net/](Net/)) computes the exact integer powers `(dI - A)^E` and `A^(2E)` of the adjacency
matrix, the filters `((I - Ã)/2)^E` and `Ã^(2E)` up to a scalar; chooses `T` of their rows by
pivoted Gram–Schmidt, comparing Gram determinants; and takes the combinations of the
Gram–Schmidt vectors with coordinates `m_l / N` for the integer points `∑ m_l² ≤ N²` of a ball.
After `T` rounds every row has residual at most `2^(T+1) ℓ` when the filter is at most `ℓ` outside
`T` eigenvalues, so every unit vector of the eigenspace is within `2 √T / N + √n 2^(T+1) ℓ/h` of
a candidate (`BHSV25.Net.netGS_bottom_correct`, `BHSV25.Net.netGS_abs_correct`). The ball has at
most `(3 + 12 K)^T` integer points for `N = (⌊√T⌋ + 1) K` (`BHSV25.Net.ballBudget_sqrt`),
exponential in `T` where the cube `(2N + 1)^T` would be `T^{Θ(T)}`.

The number of rounds is the first after which every row has residual at most a threshold `τ`,
tested by comparing Gram determinants ([Net/Stop.lean](Net/Stop.lean), `BHSV25.Net.stopZ`). If
`τ ≥ 2^(t+1) ℓ`, the residuals are below `τ` after `t` rounds, so the stopping round is at most
`t`; and after the stopping round the candidates are within `2 √T / N + √n τ/h` of the
eigenspace (`BHSV25.Net.exists_cand_near_stop`). The filter makes the gap between `ℓ` and `h` so
large that a threshold fits between them.

### Independent sets: Theorem 7.20 and Corollary 7.21

The algorithm is the paper's: round every vector of the net of the bottom eigenspace to an
independent set and keep the largest (Lemmas 7.22 to 7.24). The net has precision `4/K` with
`K ≈ √((1 - λ)/(c γ))`, which costs `(c/2) γ n/(1 - λ)` vertices. The filter is applied at the
threshold `min(λ, 1 - 1/(4n⁴))` with the power `a n⁵`, which separates the eigenvalues for every
`λ < 1`: on a regular graph every eigenvalue is `-1` or at least `-1 + 1/(2n⁴)`
([Alg/EigGap.lean](Alg/EigGap.lean), `BHSV25.Alg.eig_eq_neg_one_or_ge`), by walks of both
parities from a vertex of large weight, or the sign vector of a bipartite component. Corollary
7.21 follows by Corollary 4.2: at most `t` eigenvalues above `λ` leave at most `t/λ²` at most
`-√(2λ)`.

The algorithm finds the number of rounds itself ([Alg/IndepSetStop.lean](Alg/IndepSetStop.lean),
[Alg/IndepSetStopCorrect.lean](Alg/IndepSetStopCorrect.lean)), with the threshold `ψ^E` for
`ψ = 1 - (1 - 1/β) g/2`, where `c' = min(c, 1)/32`, `β = ⌈4/c'⌉` and `g = max(1 - λ', 1/(4n⁴))`.
The filter makes the noise, the eigenvalues above `-(1 - g)`, at most `(1 - g/2)^E`, and the
target, the eigenvalues at most `-(1 - (1 - c') g)`, at least `(1 - (1 - c') g/2)^E`. Here `λ'`
is a fraction within `c' (1 - λ)` above `λ`, which the machine reads with denominator about
`1/(c' (1 - λ))`. The guarantee holds on every regular graph, and the stopping round is at most
the number of eigenvalues at most `-λ` ([Alg/IndepSetUnif.lean](Alg/IndepSetUnif.lean)).

### Colorings: Theorems 7.1 and 7.9 and Corollary 7.2

The algorithm is the net of the eigenvalues large in absolute value followed by the clustering of
Lemma 5.4 with a grid of centers, one cluster per group of equal rows of the model, each cluster
rounded to an independent set. The analysis follows Theorem 5.1 (Lemmas 5.2 to 5.4), with Lemma
6.1 applied at the upper bound `λ` on the second eigenvalue (error `O_M(δ/λ + λ)`), the part sizes
of Lemma 7.3 (error `O_M(δ)`), and a net whose cost `512 m² η²/α²` is at most `λ`. For
Theorem 7.9 the rows of the model are `γ/2` apart when `8 δ ≤ γ²` (the claim in its proof), and
the threshold is `γ^{3/2}/8`; when `8 δ > γ²` or `λ ≥ γ³/512` the bound `B (λ + δ/λ)/γ⁸` is at
least `1`.

### Random planting: Theorems 7.12 and 7.17

The algorithm of Theorem 7.12 is that of Theorem 7.1 with `k` clusters, which finds the number of
rounds of its net itself ([Planted/Stop.lean](Planted/Stop.lean)): the net needs no degree, but
the threshold of the stopping round is taken at the scale of the average degree of the planted
graph, which is between `d/2` and `d` on the good colorings
([Planted/StopCorrect.lean](Planted/StopCorrect.lean)). The analysis is Theorem 5.1 for the matrix
`A_G / d` of the planted graph ([Planted/Recovery.lean](Planted/Recovery.lean), with the closeness
to the model a hypothesis, as in the paper). The paper normalizes by the expected degree
`(k - 1) d / k`; normalizing by `d` keeps `|xᵀ (A_G / d) x| ≤ ‖x‖²` exact. The ingredients:

* **Concentration** (Lemmas 7.13 to 7.15, [Planted/Conc.lean](Planted/Conc.lean)): complexitylib's
  McDiarmid inequality in counting form for uniform colorings
  ([Planted/Prob.lean](Planted/Prob.lean)), with the deviation `n^{3/4}` in place of
  `√(n log n)`, so that the errors are powers of `n ≥ d + 1`; the averages by resampling one color
  at a time. The dispersion around `1/k` bounds the dispersion around the model, as the mean
  minimizes the sum of squares.
* **The threshold rank after planting** (Lemma 7.16, [Planted/Rank.lean](Planted/Rank.lean)): one
  Courant–Fischer count in place of interlacing and Weyl's inequalities, with Corollary 4.2 for the
  bottom of the host's spectrum.
* **The net** for `A_G / d` ([Planted/Net.lean](Planted/Net.lean)); the planted coloring is proper,
  so the rounding loses at most twice the misclustered vertices.

With `γ = 1/4` and `λ₀ = 1/(8192 k⁴)`, the net of precision `4/K`, `K = ⌈65536 k⁴/ε⌉ + 1`,
stops after at most `(k + 1)(1 + 2²⁶ k⁸) t` rounds: at most that many eigenvalues of `A_G / d`
are at least `1/(48 k²)` in absolute value ([Planted/Partial.lean](Planted/Partial.lean),
[Planted/StopCorrect.lean](Planted/StopCorrect.lean), [Planted/PartialThm.lean](Planted/PartialThm.lean)).

The algorithm of Theorem 7.17 ([Planted/FullAlg.lean](Planted/FullAlg.lean)) is the paper's: the
list of the clusters of Theorem 7.12 before the rounding (Theorem B.1), uncoloring
(Algorithm 2) for every degree `d' ≤ n` (the algorithm does not know the host's), safe recoloring
(Algorithm 3), and brute force on the components of the uncolored vertices; each result is rounded
and the one with the most colored vertices is kept. Uncoloring and recoloring run in rounds that
treat all vertices at once, which reach the same end: uncoloring only removes neighbors, and
recoloring only gives correct colors. The brute force tries at most `n²` colorings of a component,
enough for the components with `k^|C| ≤ n²`, which keeps the degree of the polynomial independent
of `k`. The analysis:

* **Expanders** (Lemmas 7.18, B.19 and 7.19, [Planted/Expander.lean](Planted/Expander.lean)); for
  Lemma B.19 a largest set with the right density, in place of the removal process.
* **Statistically bad vertices** (Lemma B.14, [Planted/StatBad.lean](Planted/StatBad.lean)):
  Hoeffding's inequality for one vertex, then Markov's inequality when `(d + 1)⁴ > n` and
  McDiarmid's inequality otherwise.
* **Uncoloring and recoloring** (Lemmas B.20 and B.21, [Planted/Uncolor.lean](Planted/Uncolor.lean),
  [Planted/Recolor.lean](Planted/Recolor.lean)).
* **Small components** (Lemma B.21, [Planted/Comp.lean](Planted/Comp.lean)): every component of the
  uncolored vertices is *stuck* (each of its vertices misses a color other than its own among its
  neighbors outside it); a connected set `S` is stuck with probability at most
  `(k - 1)^|S| ((k - 1)/k)^|∂S|`, and the sum over the connected sets through a vertex is bounded by
  `∑_S p^|S| q^|∂S| ≤ 1` for `p + q = 1`, the probability that `S` is the component of the vertex
  in a random set, in place of the count of Lemma B.23 of David and Feige. With the vertex
  expansion `|∂S| ≥ 4 k⁶ |S|`, no component has `k^|C| > n²`, except on `k^n / n⁵` colorings.
* **Brute force and the assembly** ([Planted/Brute.lean](Planted/Brute.lean),
  [Planted/FullCorrect.lean](Planted/FullCorrect.lean),
  [Planted/FullThm.lean](Planted/FullThm.lean)), and the machine
  ([Planted/FullPolyTime.lean](Planted/FullPolyTime.lean)).

### Corollaries 1.2 and 1.4

Each is one machine reading the parameters of the algorithms it combines. Corollary 1.2 runs
Corollary 7.21 for `γ` on a grid up to `1/10`, keeps the largest independent set and outputs its
complement. Corollary 1.4 runs Theorem 7.9 (with `δ = λ`, `γ = λ^{1/18}/2` and the bound `√λ` on the
second eigenvalue) and Corollary 7.21 (with `γ = λ^{1/18}`), and outputs the coloring if it colors
at least twice as many vertices as the independent set has, and the independent set otherwise,
for `f λ = O(λ^{1/18})`.

### Hardness

The reductions are deterministic: explicit pseudo-random graphs instead of random biregular
Ramanujan graphs, blow-ups made exactly regular by absorbers, integral sizes and degrees from
dyadic designs, and eigenvalue counts proved directly (Theorem 1.6 needs no Theorem 4.1). For the
vanishing spectral bounds of Theorems 1.5 and 1.6 the precision of the pseudo-random sets grows with
the input, `a = a₀ + ⌈log₂ n⌉`, so that the template has polynomially many cells, its error is of
order `2^{-a} ≤ 1/n`, and its degree, at least `2^a`, also makes the error from the input graph
vanish; the template is computed by the machine from the cell numbers. For Theorem 1.5 the weights
of the model are exact, so no rounding error remains. Fact 8.1
is proved from the conjecture on graphs: the bipartite double cover and Khot and Regev's
regularization give hardness on left-regular instances whose parallel constraints agree, which is
all that Bansal and Khot's long code test with one free bit needs (as described by Manurangsi,
arXiv:1705.03581, §4.2); [BK/README.md](BK/README.md) explains both. "It Ain't Over
Till It's Over" is proved without Gaussian space: the invariance principle compares two discrete
ensembles, and reverse hypercontractivity on the cube replaces the Gaussian isoperimetric
argument.

## Map of the files

| Files | Content |
| --- | --- |
| [Time.lean](Time.lean) | Running times `K · m^C` from one polynomial-time machine that reads its parameters with the graph. |
| [TimePad.lean](TimePad.lean) | Running times `K G · m^C` from one polynomial-time machine that reads unary paddings computed from the graph. |
| [Spectral/Basic.lean](Spectral/Basic.lean), [Spectral/Eigen.lean](Spectral/Eigen.lean), [Spectral/GraphFacts.lean](Spectral/GraphFacts.lean) | Coordinates in an eigenbasis, spans of eigenvectors and their projections, counting eigenvalues by subspaces (Courant–Fischer); the normalized adjacency matrix: nonnegative, eigenvalues in `[-1, 1]`, `A/d` for `d`-regular graphs, and `xᵀ Ã x ≤ (∑ x)²/n + L(‖x‖² - (∑ x)²/n)` when at most one eigenvalue exceeds `L`. |
| [Spectral/ThresholdRank.lean](Spectral/ThresholdRank.lean) | Theorem 4.1 for every `τ ≥ 0` and `τ' < τ²`: the witness of Lemma 4.4 from the vectors `wᵢ ⊗ wᵢ / ‖wᵢ‖` of the bottom eigenvectors, and the Barak–Raghavendra–Steurer bound (Lemma 4.3); in the paper's parameters `λ, σ` (at `λ = 1`, a threshold between `1` and the eigenvalues below it); the graph version, and Corollary 4.2. |
| [Net/Machine.lean](Net/Machine.lean), [Net/PolyTime.lean](Net/PolyTime.lean), [Net/Correct.lean](Net/Correct.lean), [Net/Approx.lean](Net/Approx.lean), [Net/Spec.lean](Net/Spec.lean) | Integer matrices on lists of numbers, their products and powers in polynomial time with bounds on the entries; the two filters on the input of a graph; coefficients in an eigenbasis. |
| [Net/Resid.lean](Net/Resid.lean), [Net/Greedy.lean](Net/Greedy.lean), [Net/GSGrid.lean](Net/GSGrid.lean), [Net/Ball.lean](Net/Ball.lean) | Residuals and Gram determinants; the greedy selection and its residual bound `(2^(T+1) - 1) ℓ` by back substitution; Gram–Schmidt coordinates and the grid point in the ball; the integer points of a ball, cut at a budget, and their number. |
| [Net/GSMachine.lean](Net/GSMachine.lean), [Net/GSCorrect.lean](Net/GSCorrect.lean), [Net/BallPolyTime.lean](Net/BallPolyTime.lean), [Net/GSPolyTime.lean](Net/GSPolyTime.lean) | The greedy net on lists (Gram–Schmidt by Cramer's rule with complexitylib's determinant), its correctness for the two filters, and its polynomial-time certificate. |
| [Net/Stop.lean](Net/Stop.lean), [Net/StopCorrect.lean](Net/StopCorrect.lean) | The stopping round of the greedy selection, in polynomial time, and the net at the stopping round. |
| [Alg/GraphMachine.lean](Alg/GraphMachine.lean), [Alg/Rounding.lean](Alg/Rounding.lean) | Graphs as machine inputs; rounding a vertex set to an independent set by removing both ends of a greedy maximal matching (Lemma 7.24). |
| [Alg/IndepSetSpectral.lean](Alg/IndepSetSpectral.lean), [Alg/IndepSet.lean](Alg/IndepSet.lean), [Alg/EigGap.lean](Alg/EigGap.lean) | Lemmas 7.22 and 7.23; rounding a net to the largest independent set; the spectral gap at `-1`. |
| [Alg/IndepSetGS.lean](Alg/IndepSetGS.lean), [Alg/IndepSetFull.lean](Alg/IndepSetFull.lean) | The algorithm of Theorem 7.20 with a given number of rounds, its guarantee and parameters, for the corollaries. |
| [Alg/IndepSetStop.lean](Alg/IndepSetStop.lean), [Alg/IndepSetStopCorrect.lean](Alg/IndepSetStopCorrect.lean), [Alg/IndepSetUnif.lean](Alg/IndepSetUnif.lean) | Theorem 7.20 and Corollary 7.21: the algorithm that finds the number of rounds, its guarantee, the parameters and the running time. |
| [Alg/VertexCover.lean](Alg/VertexCover.lean), [Alg/VertexCoverFull.lean](Alg/VertexCoverFull.lean) | Complements and vertex covers; Corollary 1.2. |
| [Alg/Variance.lean](Alg/Variance.lean) | Partitions, their models, Lemma 6.1 with any upper bound `L` on the second eigenvalue, and Lemma 7.4. |
| [Alg/PartitionSpectral.lean](Alg/PartitionSpectral.lean), [Alg/Partition.lean](Alg/Partition.lean) | Theorem 5.1, spectral part: eigenspace closeness (Lemma 5.2) and coordinate separation through the eigenvectors of the symmetrized model `B^(1/2) M B^(-1/2)`, whose eigenvalues lie in `[-1, 1]` (Lemma 5.3). |
| [Alg/Cluster.lean](Alg/Cluster.lean), [Alg/ClusterPolyTime.lean](Alg/ClusterPolyTime.lean), [Alg/GridCluster.lean](Alg/GridCluster.lean), [Alg/GridPartition.lean](Alg/GridPartition.lean), [Alg/GridPolyTime.lean](Alg/GridPolyTime.lean) | The clustering with a grid of centers (Lemma 5.4), the rounding of the clusters and the best coloring, its analysis (Theorem 5.1), and its polynomial-time certificate. |
| [Alg/ModelFacts.lean](Alg/ModelFacts.lean), [Alg/ExpanderContract.lean](Alg/ExpanderContract.lean), [Alg/ExpanderAccount.lean](Alg/ExpanderAccount.lean) | Lemma 7.3 (class sizes near `π`, through the symmetrized model and its characteristic polynomial), groups of equal rows, the contracted partition, and the comparison with `α`. |
| [Alg/ExpanderGrid.lean](Alg/ExpanderGrid.lean), [Alg/ExpanderFull.lean](Alg/ExpanderFull.lean) | Theorem 7.1 and Corollary 7.2: the analysis, the algorithm, its parameters and running time. |
| [Alg/ColoringAnalysis.lean](Alg/ColoringAnalysis.lean), [Alg/ColoringFull.lean](Alg/ColoringFull.lean) | Partitions into three parts and their separated rows; Theorem 7.9. |
| [Alg/Coloring.lean](Alg/Coloring.lean), [Alg/ColoringOrFull.lean](Alg/ColoringOrFull.lean) | The combination of a coloring and an independent set; Corollary 1.4. |
| [Planted/Lift.lean](Planted/Lift.lean), [Planted/Recovery.lean](Planted/Recovery.lean) | Theorem 5.1 with a grid of centers for any symmetric matrix `Q` with `|xᵀ Q x| ≤ ‖x‖²` and dispersions at most `Δ n`: the lift, the symmetrized model, Lemmas 5.2, 5.3 and 7.4. |
| [Planted/Net.lean](Planted/Net.lean), [Planted/Rank.lean](Planted/Rank.lean) | The net and the rounding of Theorem 7.1 analysed with `A_G / d`; Lemma 7.16 (the threshold rank after planting). |
| [Planted/Prob.lean](Planted/Prob.lean), [Planted/Conc.lean](Planted/Conc.lean) | Uniform colorings: McDiarmid's inequality in counting form, resampling one color; Lemmas 7.13 to 7.15 and the bad colorings. |
| [Planted/Partial.lean](Planted/Partial.lean), [Planted/Stop.lean](Planted/Stop.lean), [Planted/StopCorrect.lean](Planted/StopCorrect.lean), [Planted/PartialThm.lean](Planted/PartialThm.lean) | Theorem 7.12: the good candidate of the list (Theorem B.1), the algorithm that finds the number of rounds, one good coloring, the probability and the running time. |
| [Planted/Expander.lean](Planted/Expander.lean), [Planted/StatBad.lean](Planted/StatBad.lean), [Planted/Comp.lean](Planted/Comp.lean) | Lemmas 7.18, B.19 and 7.19; statistically bad vertices (Lemma B.14); stuck sets and the components of the uncolored vertices (Lemma B.21). |
| [Planted/FullAlg.lean](Planted/FullAlg.lean), [Planted/Uncolor.lean](Planted/Uncolor.lean), [Planted/Recolor.lean](Planted/Recolor.lean), [Planted/Brute.lean](Planted/Brute.lean) | The algorithm of Theorem 7.17 and its steps: uncoloring (Lemma B.20), safe recoloring, closures of the uncolored vertices and the brute force. |
| [Planted/FullCorrect.lean](Planted/FullCorrect.lean), [Planted/FullPolyTime.lean](Planted/FullPolyTime.lean), [Planted/FullThm.lean](Planted/FullThm.lean) | Theorem 7.17: one good coloring, the polynomial-time certificate, the probability and the theorem. |
| [Hard/Glue.lean](Hard/Glue.lean) | A reduction from Fact 8.1's gap problem proves NP-hardness (the graph without vertices first replaced by two isolated vertices); a polynomial-time checker of partial colorings with enough colored vertices, by which NP-hardness of a gap problem of colorings and an algorithm give `NP ⊆ P`. |
| [Hard/Blowup.lean](Hard/Blowup.lean), [Hard/Coloring.lean](Hard/Coloring.lean), [Hard/Machine.lean](Hard/Machine.lean) | Blow-ups `T ⊗ J + W ⊗ A_G` of a template on finitely many cells, exactly regular because `W` has zero row sums ("absorber" cells join copies of `G` by its complement); the bilinear-form comparison with the planted matrix, the colorings in the yes and no cases, and the blow-up in polynomial time. |
| [Hard/Cayley.lean](Hard/Cayley.lean), [Hard/Dyadic.lean](Hard/Dyadic.lean), [Hard/Design.lean](Hard/Design.lean), [Hard/Pipeline.lean](Hard/Pipeline.lean) | Explicit pseudo-random graphs in place of random biregular graphs: Cayley sum graphs on `(𝔽₂^(2a+1))^r` from the bent function `w₀ + ⟨w₁, w₂⟩`, with sets of every dyadic density; templates from finite designs, their regularity and eigenvalue counts. |
| [Hard/Spectral.lean](Hard/Spectral.lean) | The planted matrix `M_ab / π_b` is at most `0` on vectors of sum `0`, from the characteristic polynomial of the symmetrized model; eigenvalue counting. |
| [Hard/Formula.lean](Hard/Formula.lean), [Hard/MachineA.lean](Hard/MachineA.lean), [Hard/Rate.lean](Hard/Rate.lean) | Templates of growing precision: the template computed from cell numbers (digits in base `2 · 4^a`, the bent function of a sum by parity of bit counts); the blow-up by the template of precision `a₀ + ⌈log₂ n⌉` in polynomial time; spectral bounds `c / 2^a ≤ c (b / N)^{1/e}` in terms of the output size `N`. |
| [Hard/LowRankDesign.lean](Hard/LowRankDesign.lean), [Hard/LowRankFacts.lean](Hard/LowRankFacts.lean), [Hard/LowRank.lean](Hard/LowRank.lean) | Theorem 1.6 (Theorem 8.6): five groups, a complete join and a tripartite part of densities `3/4, 1/2, 1/2`; at most two eigenvalues above the threshold `73 / 2^a` and five below minus it, so `R = 7`; the color classes trimmed to the same size. |
| [Hard/ModelUnits.lean](Hard/ModelUnits.lean), [Hard/ModelDesign.lean](Hard/ModelDesign.lean), [Hard/ModelCount.lean](Hard/ModelCount.lean), [Hard/ModelEst.lean](Hard/ModelEst.lean), [Hard/ModelYes.lean](Hard/ModelYes.lean), [Hard/ModelNo.lean](Hard/ModelNo.lean), [Hard/Model.lean](Hard/Model.lean) | Theorem 1.9 (2) (Theorem 8.2): one group per color, with densities `∝ ⌊D π_i M_ij⌋ / (s_i s_j)` (symmetric by detailed balance, so the template is exactly regular); color units colored along the distribution of the classes and paired with their half shift, which accounts for the fraction `1 - α`; absorbers in the partner group. |
| [Hard/Corollaries.lean](Hard/Corollaries.lean), [Hard/Unbalanced.lean](Hard/Unbalanced.lean) | Theorem 1.8 (2) from Theorem 1.9 (2) with `δ = α/2`; Theorem 1.5 by the reduction of Theorem 1.9 (2) for the model `[[0, ½, ½], [1, 0, 0], [1, 0, 0]]` (`α = 1/2`), whose weights are exact at a precision `4c`, with the precision of the template growing with the input. |
| [BansalKhot.lean](BansalKhot.lean) | Fact 8.1, with maximum degree at most `η n` for every `η > 0` (`BHSV25.BansalKhot`), from the conjecture (`BHSV25.bansalKhot`). |
| [UG/Value.lean](UG/Value.lean), [UG/Cover.lean](UG/Cover.lean), [UG/Regular.lean](UG/Regular.lean), [UG/Machine.lean](UG/Machine.lean), [UG/Bridge.lean](UG/Bridge.lean) | From the conjecture on graphs to left-regular bipartite instances whose parallel constraints agree: the double cover (value at most doubled, by mixing the two labelings over all `2^n` choices) and Khot and Regev's regularization (value within `1/ℓ`), in polynomial time. |
| [BK/Basic.lean](BK/Basic.lean), [BK/Graph.lean](BK/Graph.lean), [BK/Vertices.lean](BK/Vertices.lean), [BK/Copies.lean](BK/Copies.lean), [BK/Complete.lean](BK/Complete.lean), [BK/Sound.lean](BK/Sound.lean), [BK/Machine.lean](BK/Machine.lean), [BK/Main.lean](BK/Main.lean) | The reduction: long codes, influences and the decoding of labels (from BGHKLMM26); one vertex per random string of the test, adjacent when they demand incompatible values of a folded long code; completeness, soundness through the averaged long codes, maximum degree `≤ η n` by disjoint copies, polynomial time, and the assembly. |
| [BK/AintOver.lean](BK/AintOver.lean), [BK/Ensemble.lean](BK/Ensemble.lean), [BK/Invariance*.lean](BK/Invariance.lean), [BK/HyperReverse.lean](BK/HyperReverse.lean), [BK/AintProof.lean](BK/AintProof.lean) | "It Ain't Over Till It's Over" [MOO10, Theorem 4.9]: the average on a random subcube is a multilinear polynomial in a three-valued ensemble; an invariance principle between that ensemble and uniform signs (adapted from BGHKLMM26/RobustMIS), and reverse hypercontractivity on the cube, `E[f · T_r h] ≥ (E f)^k (E h)^k` for `r ≤ 1 - 1/k`, proved by induction from a two-point inequality. |

*Formalized by [Claude Code](https://claude.com/claude-code).*
