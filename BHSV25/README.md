# BHSV25: Finding colorings in one-sided expanders

The results are [BHSV25]'s algorithms in the full versions of Section 7, with their explicit
errors and running times (Theorems 7.1, 7.9 and 7.20, Corollaries 7.2 and 7.21), Corollaries 1.2
and 1.4 with the running times these give, the hardness results (Theorems 1.5, 1.6, 1.8 (2) and
1.9 (2)) and Theorem 1.7, stated in [Challenge.lean](Challenge.lean) with the definitions of
[Model.lean](Model.lean) and proved in [Solution.lean](Solution.lean), with only the standard
axioms; `lake comparator` checks them. The hardness results assume the Unique Games Conjecture
(`UniqueGames.UGC`), and the proof derives from it the paper's starting point, Bansal and Khot's
hardness of almost-bipartite independent set [BHSV25, Fact 8.1], including Mossel, O'Donnell and
Oleszkiewicz's "It Ain't Over Till It's Over".

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v2).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 7.20 | `independentSet_bottomRank` | On regular graphs with at most `t` eigenvalues at most `-λ` and an independent set of `(1/2 - γ) n` vertices: one of `(1/2 - γ - (4 + c) γ/(1 - λ)) n`, in time `poly(n) · (γ/(1 - λ))^{-O(t)}`. |
| Theorem 1.1 (Cor. 7.21) | `independentSet_approximation` | The same with at most `t` eigenvalues above `λ < 1/2`: `(1/2 - γ - (4 + c) γ/(1 - √(2λ))) n` in time `poly(n) · (γ/(1 - √(2λ)))^{-O(t/λ²)}`. |
| Corollary 1.2 | `vertexCover_approximation` | A `(5/3 + ε)`-approximation of vertex cover on regular `λ₀`-one-sided expanders, in time `n^{O(1)} · O_ε(1)`. |
| Theorem 1.3 (Thm. 7.9) | `threeColoring_balanced` | On regular `λ`-one-sided expanders with a partition into `3` parts of at most `(1/2 - γ) n` vertices, proper up to `δ n` vertices: `3` independent sets covering all but `O(λ/γ⁸ + δ/(λ γ⁸)) n`, in time `n^{O(1)} · O_{δ,γ,λ}(1)`. |
| Corollary 1.4 | `threeColoring_independentSet_or_coloring` | On regular `λ`-one-sided expanders with `3` independent sets covering all but `λ n` vertices: an independent set of `(1/2 - o_λ(1)) n` vertices or `3` covering all but `o_λ(1) n`, in time `n^{O(1)} · O_λ(1)`. |
| Theorem 1.5 (Cor. 8.4) | `threeColoring_unbalanced_hardness` | Covering `(1/2 + γ) n` vertices of almost `3`-colorable one-sided expanders is hard. |
| Theorem 1.6 (Thm. 8.6) | `threeColoring_lowRank_hardness` | Covering `(7/9 + γ) n` vertices is hard with balanced almost-`3`-colorings and only two eigenvalues above `ε`. |
| Theorem 1.7 (Thm. 4.1) | `thresholdRank_graph`, `thresholdRank` | `((τ² - τ')/(1 - τ'))² #{eig ≤ -τ} ≤ #{eig ≥ τ'}`, for graphs and for nonnegative symmetric matrices of norm at most `1`. |
| Theorem 1.8 (Cor. 7.2, 8.3) | `expanderColoring_distinctRows`, `expanderColoring_repeatedRows_hardness` | Without repeated rows: a `(k, O_M(√δ + λ + δ/λ))`-coloring of `(M, δ)`-colorable `λ`-one-sided expanders in time `n^{O(1)} · O_{δ,λ,M}(1)`; with repeated rows, `M`-expander-coloring is hard. |
| Theorem 1.9 (Thm. 7.1, 8.2) | `expanderColoring_algorithm`, `expanderColoring_hardness` | A `(k', α + O_M(√δ + λ + δ/λ))`-coloring, `k'` the number of distinct rows of `M`, in time `n^{O(1)} · O_{δ,λ,M}(1)`; `(M, α - γ)`-expander-coloring is hard. |

* **Graphs** are simple and given by their adjacency tables; the spectrum is that of
  `D^(-1/2) A D^(-1/2)`, and a `λ`-one-sided expander has at most one eigenvalue above `λ`.
* **Running times** are those of deterministic multitape Turing machines (`BHSV25.RunsInTime`):
  a time `n^{O(1)} · g(p)` for parameters `p` is a degree `C`, fixed before all parameters, and for
  all values of `p` an algorithm running in time `g(p) · m^C` on inputs of length `m`. The factor
  `g` is explicit where the paper gives it (Theorem 7.20, Corollary 7.21). As in Section 7, the
  algorithms depend on the parameters.
* **Errors** are the body's, with their constants as `∃` quantifiers (`O_M` for constants depending
  on the model). In Theorems 7.1 and 7.9, `λ` is any upper bound on the second eigenvalue, as the
  variance bound (Lemma 6.1) needs only an upper bound.
* **Hardness** assumes the Unique Games Conjecture (`UniqueGames.UGC` in
  [../Background/UniqueGames.lean](../Background/UniqueGames.lean), the form used for BGHKLMM26:
  simple bi-regular bipartite instances, gap `(1 - ε, ε)`) and concludes `NP ⊆ P` from a
  polynomial-time algorithm. This is weaker than NP-hardness of gap problems
  (`PromiseProblem.NPHard`): a proof need not exhibit a reduction. The hardness theorems are the
  body's fixed-parameter versions, which imply the introduction's in this form.
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
length of the parameters ([Time.lean](Time.lean), `BHSV25.runsInTime_graph_fix`). For
Theorem 7.20 the parameters have length `(D (1 + (1 - λ)/γ))^{O(t)}`, which gives the stated
factor.

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

### Colorings: Theorems 7.1 and 7.9 and Corollary 7.2

The algorithm is the net of the eigenvalues large in absolute value followed by the clustering of
Lemma 5.4 with a grid of centers, one cluster per group of equal rows of the model, each cluster
rounded to an independent set. The analysis follows Theorem 5.1 (Lemmas 5.2 to 5.4), with Lemma
6.1 applied at the upper bound `λ` on the second eigenvalue (error `O_M(δ/λ + λ)`), the part sizes
of Lemma 7.3 (error `O_M(δ)`), and a net whose cost `512 m² η²/α²` is at most `λ`. For
Theorem 7.9 the rows of the model are `γ/2` apart when `8 δ ≤ γ²` (the claim in its proof), and
the threshold is `γ^{3/2}/8`; when `8 δ > γ²` or `λ ≥ γ³/512` the bound `B (λ + δ/λ)/γ⁸` is at
least `1`.

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
dyadic designs, and eigenvalue counts proved directly (Theorem 1.6 needs no Theorem 4.1). Fact 8.1
is proved from the conjecture by Bansal and Khot's long code test with one free bit, as described
by Manurangsi (arXiv:1705.03581, §4.2); [BK/README.md](BK/README.md) explains it. "It Ain't Over
Till It's Over" is proved without Gaussian space: the invariance principle compares two discrete
ensembles, and reverse hypercontractivity on the cube replaces the Gaussian isoperimetric
argument.

## Map of the files

| Files | Content |
| --- | --- |
| [Time.lean](Time.lean) | Running times `K · m^C` from one polynomial-time machine that reads its parameters with the graph. |
| [Spectral/Basic.lean](Spectral/Basic.lean), [Spectral/Eigen.lean](Spectral/Eigen.lean), [Spectral/GraphFacts.lean](Spectral/GraphFacts.lean) | Coordinates in an eigenbasis, spans of eigenvectors and their projections, counting eigenvalues by subspaces (Courant–Fischer); the normalized adjacency matrix: nonnegative, eigenvalues in `[-1, 1]`, `A/d` for `d`-regular graphs, and `xᵀ Ã x ≤ (∑ x)²/n + L(‖x‖² - (∑ x)²/n)` when at most one eigenvalue exceeds `L`. |
| [Spectral/ThresholdRank.lean](Spectral/ThresholdRank.lean) | Theorem 4.1 for every `τ > 0` and `τ' < τ²`: the witness of Lemma 4.4 from the vectors `wᵢ ⊗ wᵢ / ‖wᵢ‖` of the bottom eigenvectors, and the Barak–Raghavendra–Steurer bound (Lemma 4.3); the graph version, and Corollary 4.2. |
| [Net/Machine.lean](Net/Machine.lean), [Net/PolyTime.lean](Net/PolyTime.lean), [Net/Correct.lean](Net/Correct.lean), [Net/Approx.lean](Net/Approx.lean), [Net/Spec.lean](Net/Spec.lean) | Integer matrices on lists of numbers, their products and powers in polynomial time with bounds on the entries; the two filters on the input of a graph; coefficients in an eigenbasis. |
| [Net/Resid.lean](Net/Resid.lean), [Net/Greedy.lean](Net/Greedy.lean), [Net/GSGrid.lean](Net/GSGrid.lean), [Net/Ball.lean](Net/Ball.lean) | Residuals and Gram determinants; the greedy selection and its residual bound `(2^(T+1) - 1) ℓ` by back substitution; Gram–Schmidt coordinates and the grid point in the ball; the integer points of a ball, cut at a budget, and their number. |
| [Net/GSMachine.lean](Net/GSMachine.lean), [Net/GSCorrect.lean](Net/GSCorrect.lean), [Net/BallPolyTime.lean](Net/BallPolyTime.lean), [Net/GSPolyTime.lean](Net/GSPolyTime.lean) | The greedy net on lists (Gram–Schmidt by Cramer's rule with complexitylib's determinant), its correctness for the two filters, and its polynomial-time certificate. |
| [Alg/GraphMachine.lean](Alg/GraphMachine.lean), [Alg/Rounding.lean](Alg/Rounding.lean) | Graphs as machine inputs; rounding a vertex set to an independent set by removing both ends of a greedy maximal matching (Lemma 7.24). |
| [Alg/IndepSetSpectral.lean](Alg/IndepSetSpectral.lean), [Alg/IndepSet.lean](Alg/IndepSet.lean), [Alg/EigGap.lean](Alg/EigGap.lean) | Lemmas 7.22 and 7.23; rounding a net to the largest independent set; the spectral gap at `-1`. |
| [Alg/IndepSetGS.lean](Alg/IndepSetGS.lean), [Alg/IndepSetFull.lean](Alg/IndepSetFull.lean) | Theorem 7.20 and Corollary 7.21: the algorithm with the greedy net, its guarantee, the parameters and the running time. |
| [Alg/VertexCover.lean](Alg/VertexCover.lean), [Alg/VertexCoverFull.lean](Alg/VertexCoverFull.lean) | Complements and vertex covers; Corollary 1.2. |
| [Alg/Variance.lean](Alg/Variance.lean) | Partitions, their models, Lemma 6.1 with any upper bound `L` on the second eigenvalue, and Lemma 7.4. |
| [Alg/PartitionSpectral.lean](Alg/PartitionSpectral.lean), [Alg/Partition.lean](Alg/Partition.lean) | Theorem 5.1, spectral part: eigenspace closeness (Lemma 5.2) and coordinate separation through the eigenvectors of the symmetrized model `B^(1/2) M B^(-1/2)`, whose eigenvalues lie in `[-1, 1]` (Lemma 5.3). |
| [Alg/Cluster.lean](Alg/Cluster.lean), [Alg/ClusterPolyTime.lean](Alg/ClusterPolyTime.lean), [Alg/GridCluster.lean](Alg/GridCluster.lean), [Alg/GridPartition.lean](Alg/GridPartition.lean), [Alg/GridPolyTime.lean](Alg/GridPolyTime.lean) | The clustering with a grid of centers (Lemma 5.4), the rounding of the clusters and the best coloring, its analysis (Theorem 5.1), and its polynomial-time certificate. |
| [Alg/ModelFacts.lean](Alg/ModelFacts.lean), [Alg/ExpanderContract.lean](Alg/ExpanderContract.lean), [Alg/ExpanderAccount.lean](Alg/ExpanderAccount.lean) | Lemma 7.3 (class sizes near `π`, through the symmetrized model and its characteristic polynomial), groups of equal rows, the contracted partition, and the comparison with `α`. |
| [Alg/ExpanderGrid.lean](Alg/ExpanderGrid.lean), [Alg/ExpanderFull.lean](Alg/ExpanderFull.lean) | Theorem 7.1 and Corollary 7.2: the analysis, the algorithm, its parameters and running time. |
| [Alg/ColoringAnalysis.lean](Alg/ColoringAnalysis.lean), [Alg/ColoringFull.lean](Alg/ColoringFull.lean) | Partitions into three parts and their separated rows; Theorem 7.9. |
| [Alg/Coloring.lean](Alg/Coloring.lean), [Alg/ColoringOrFull.lean](Alg/ColoringOrFull.lean) | The combination of a coloring and an independent set; Corollary 1.4. |
| [Hard/Glue.lean](Hard/Glue.lean) | A polynomial-time checker of partial colorings with enough colored vertices; a reduction and an algorithm put Fact 8.1's gap problem in `PromiseP`, hence `NP ⊆ P`. |
| [Hard/Blowup.lean](Hard/Blowup.lean), [Hard/Coloring.lean](Hard/Coloring.lean), [Hard/Machine.lean](Hard/Machine.lean) | Blow-ups `T ⊗ J + W ⊗ A_G` of a template on finitely many cells, exactly regular because `W` has zero row sums ("absorber" cells join copies of `G` by its complement); the bilinear-form comparison with the planted matrix, the colorings in the yes and no cases, and the blow-up in polynomial time. |
| [Hard/Cayley.lean](Hard/Cayley.lean), [Hard/Dyadic.lean](Hard/Dyadic.lean), [Hard/Design.lean](Hard/Design.lean), [Hard/Pipeline.lean](Hard/Pipeline.lean) | Explicit pseudo-random graphs in place of random biregular graphs: Cayley sum graphs on `(𝔽₂^(2a+1))^r` from the bent function `w₀ + ⟨w₁, w₂⟩`, with sets of every dyadic density; templates from finite designs, their regularity and eigenvalue counts. |
| [Hard/Spectral.lean](Hard/Spectral.lean) | The planted matrix `M_ab / π_b` is at most `0` on vectors of sum `0`, from the characteristic polynomial of the symmetrized model; eigenvalue counting. |
| [Hard/LowRankDesign.lean](Hard/LowRankDesign.lean), [Hard/LowRankFacts.lean](Hard/LowRankFacts.lean), [Hard/LowRank.lean](Hard/LowRank.lean) | Theorem 1.6 (Theorem 8.6): five groups, a complete join and a tripartite part of densities `3/4, 1/2, 1/2`; at most two eigenvalues above `ε` and five below `-ε`, so `R = 7`. |
| [Hard/ModelUnits.lean](Hard/ModelUnits.lean), [Hard/ModelDesign.lean](Hard/ModelDesign.lean), [Hard/ModelCount.lean](Hard/ModelCount.lean), [Hard/ModelEst.lean](Hard/ModelEst.lean), [Hard/ModelYes.lean](Hard/ModelYes.lean), [Hard/ModelNo.lean](Hard/ModelNo.lean), [Hard/Model.lean](Hard/Model.lean) | Theorem 1.9 (2) (Theorem 8.2): one group per color, with densities `∝ ⌊D π_i M_ij⌋ / (s_i s_j)` (symmetric by detailed balance, so the template is exactly regular); color units colored along the distribution of the classes and paired with their half shift, which accounts for the fraction `1 - α`; absorbers in the partner group. |
| [Hard/Corollaries.lean](Hard/Corollaries.lean) | Theorems 1.5 and 1.8 (2) from Theorem 1.9 (2): the model `[[0, ½, ½], [1, 0, 0], [1, 0, 0]]` with `α = 1/2`, and `δ = α/2`. |
| [BansalKhot.lean](BansalKhot.lean) | Fact 8.1, with maximum degree at most `η n` for every `η > 0` (`BHSV25.BansalKhot`), from the conjecture (`BHSV25.bansalKhot`). |
| [BK/Basic.lean](BK/Basic.lean), [BK/Graph.lean](BK/Graph.lean), [BK/Vertices.lean](BK/Vertices.lean), [BK/Copies.lean](BK/Copies.lean), [BK/Complete.lean](BK/Complete.lean), [BK/Sound.lean](BK/Sound.lean), [BK/Machine.lean](BK/Machine.lean), [BK/Main.lean](BK/Main.lean) | The reduction: long codes, influences and the decoding of labels (from BGHKLMM26); one vertex per random string of the test, adjacent when they demand incompatible values of a folded long code; completeness, soundness through the averaged long codes, maximum degree `≤ η n` by disjoint copies, polynomial time, and the assembly. |
| [BK/AintOver.lean](BK/AintOver.lean), [BK/Ensemble.lean](BK/Ensemble.lean), [BK/Invariance*.lean](BK/Invariance.lean), [BK/HyperReverse.lean](BK/HyperReverse.lean), [BK/AintProof.lean](BK/AintProof.lean) | "It Ain't Over Till It's Over" [MOO10, Theorem 4.9]: the average on a random subcube is a multilinear polynomial in a three-valued ensemble; an invariance principle between that ensemble and uniform signs (adapted from BGHKLMM26/RobustMIS), and reverse hypercontractivity on the cube, `E[f · T_r h] ≥ (E f)^k (E h)^k` for `r ≤ 1 - 1/k`, proved by induction from a two-point inequality. |

*Formalized by [Claude Code](https://claude.com/claude-code).*
