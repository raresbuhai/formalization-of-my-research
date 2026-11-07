# BHSV25: Finding colorings in one-sided expanders

The main results are [BHSV25, Theorems 1.1 to 1.9] (Corollaries 1.2 and 1.4 included), stated in
[Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them. The
hardness results assume the Unique Games Conjecture (`UniqueGames.UGC`), and the proof derives
from it the paper's starting point, Bansal and Khot's hardness of almost-bipartite independent set
[BHSV25, Fact 8.1], including Mossel, O'Donnell and Oleszkiewicz's "It Ain't Over Till It's Over".

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v2), whose counters are shared within each section. The paper
has no venue yet, so the key uses the arXiv year.

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 1.1 (Cor. 7.21) | `independentSet_approximation` | For `λ ∈ (0, 1)` and every `t`: an independent set of `(1/2 - (5 + o_λ(1)) γ) n` vertices in regular graphs with at most `t` eigenvalues above `λ` and one of `(1/2 - γ) n`, `γ ≤ 1/10`. |
| Corollary 1.2 | `vertexCover_approximation` | A `(5/3 + ε)`-approximation of vertex cover on regular `λ₀`-one-sided expanders. |
| Theorem 1.3 (Thm. 7.9) | `threeColoring_balanced` | `3` independent sets covering all but `o_λ(1) n` vertices, if `3` of at most `(1/2 - o_λ(1)) n` vertices each cover all but `λ n`. |
| Corollary 1.4 | `threeColoring_independentSet_or_coloring` | On regular `λ`-one-sided expanders with `3` independent sets covering all but `λ n` vertices: an independent set of `(1/2 - o_λ(1)) n` vertices or `3` covering all but `o_λ(1) n`. |
| Theorem 1.5 (Cor. 8.4) | `threeColoring_unbalanced_hardness` | Covering `(1/2 + γ) n` vertices of almost `3`-colorable one-sided expanders is hard. |
| Theorem 1.6 (Thm. 8.6) | `threeColoring_lowRank_hardness` | Covering `(7/9 + γ) n` vertices is hard with balanced almost-`3`-colorings and only two eigenvalues above `ε`. |
| Theorem 1.7 (Thm. 4.1) | `thresholdRank_graph`, `thresholdRank` | `((τ² - τ')/(1 - τ'))² #{eig ≤ -τ} ≤ #{eig ≥ τ'}`, for graphs and for nonnegative symmetric matrices of norm at most `1`. |
| Theorem 1.8 (Cor. 7.2, 8.3) | `expanderColoring_distinctRows`, `expanderColoring_repeatedRows_hardness` | `M`-expander-coloring is easy without repeated rows and hard with them. |
| Theorem 1.9 (Thm. 7.1, 8.2) | `expanderColoring_algorithm`, `expanderColoring_hardness` | `(M, α)`-expander-coloring is easy and `(M, α - γ)`-expander-coloring hard. |

* **Graphs** are simple and given by their adjacency tables; the spectrum is that of
  `D^(-1/2) A D^(-1/2)`, and a `λ`-one-sided expander has at most one eigenvalue above `λ`.
* **Algorithms** are deterministic multitape Turing machines running in polynomial time
  (complexitylib's `ComputableInPolyTime`); for each `λ` the algorithm, and the degree of its
  running time, may depend on `λ`. Theorem 1.1 is stated for `λ ∈ (0, 1)` and for graphs with at
  most `t` eigenvalues above `λ` (Corollary 7.21); Theorems 1.3 and 1.4 accept `3` independent
  sets covering all but `λ n` vertices (almost `3`-colorable inputs, as in Theorem 7.9).
* **Hardness** assumes the Unique Games Conjecture (`UniqueGames.UGC` in
  [../Background/UniqueGames.lean](../Background/UniqueGames.lean), the form used for BGHKLMM26:
  simple bi-regular bipartite instances, gap `(1 - ε, ε)`) and concludes `NP ⊆ P` from a
  polynomial-time algorithm. This is weaker than NP-hardness of gap problems
  (`PromiseProblem.NPHard`): a proof need not exhibit a reduction. The hardness theorems are the
  body's fixed-parameter versions, which imply the introduction's in this form.
* **Models** (`BHSV25.IsModel`) are row-stochastic matrices with zero diagonal, in detailed balance
  with a positive vector, and with at most one positive eigenvalue; `α` is `BHSV25.alpha`, with the
  inner sum over `π_b`.
* **Body versions** are stated where they are stronger than the introduction's, keeping the
  introduction's qualitative form for algorithms (errors tending to `0`, polynomial time).

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## Map of the proof

### Spectral facts and Theorem 1.7

| Files | Content |
| --- | --- |
| [Spectral/Basic.lean](Spectral/Basic.lean), [Spectral/Eigen.lean](Spectral/Eigen.lean), [Spectral/GraphFacts.lean](Spectral/GraphFacts.lean) | Coordinates in an eigenbasis, spans of eigenvectors and their projections, counting eigenvalues by subspaces (Courant–Fischer) and Weyl's inequality; the normalized adjacency matrix: nonnegative, eigenvalues in `[-1, 1]`, `A/d` for `d`-regular graphs, and `xᵀ Ã x ≤ (∑ x)²/n + L(‖x‖² - (∑ x)²/n)` when at most one eigenvalue exceeds `L`. |
| [Spectral/ThresholdRank.lean](Spectral/ThresholdRank.lean) | Theorem 4.1 (`BHSV25.Spectral.thresholdRank`) for every `τ > 0` and `τ' < τ²`: the witness of Lemma 4.4 from the vectors `wᵢ ⊗ wᵢ / ‖wᵢ‖` of the bottom eigenvectors, and the Barak–Raghavendra–Steurer bound (Lemma 4.3) with the factor `(1 - 1/C)²`; the graph version, and Corollary 4.2 (`BHSV25.Graph.card_eig_le_neg_le`). |

### Nets of eigenspaces

The algorithms enumerate vectors near an eigenspace of bounded dimension (Lemmas 5.2 and 7.22).
[Net/Spec.lean](Net/Spec.lean) states what they use: for fixed rational thresholds and a bound
`T`, a polynomial-time map from a graph to a list of rational vectors containing one within `κ/n`
of every vector of norm at most `1` in the span of the eigenvectors with eigenvalue at most `-θ`
(`BHSV25.Net.exists_bottomNet`), or at least `θ` in absolute value (`BHSV25.Net.exists_absNet`),
on regular graphs with at most `T` eigenvalues beyond `θ'`.

| Files | Content |
| --- | --- |
| [Net/Machine.lean](Net/Machine.lean), [Net/PolyTime.lean](Net/PolyTime.lean) | The machine: the exact integer powers `(dI - A)^m` and `A^(2m)`, `m = O(log n)`, of the adjacency matrix, divided by `(2d)^m` and `d^(2m)`: the filters `((I - Ã)/2)^m` and `Ã^(2m)`; the candidates `∑ⱼ zⱼ · (column vⱼ)` over all `T`-tuples of columns and coefficients on a polynomial-size grid. The only loop is the matrix power, certified with a bound on the entries. |
| [Net/ColumnSubset.lean](Net/ColumnSubset.lean), [Net/Approx.lean](Net/Approx.lean), [Net/Correct.lean](Net/Correct.lean) | Correctness: among the columns' coordinates on the large eigenvalues, `T` of maximal Gram determinant span the others with coefficients at most `1` (Auerbach's argument); a target `w` is `P x` with `‖x‖ ≤ 1/h^m`, and the filter shrinks the other eigenvalues by `(ℓ/h)^m ≤ 2^(-a)/n²`. |

### Independent sets: Theorem 1.1 and Corollary 1.2

| Files | Content |
| --- | --- |
| [Alg/GraphMachine.lean](Alg/GraphMachine.lean), [Alg/Rounding.lean](Alg/Rounding.lean) | Graphs as machine inputs; rounding a vertex set to an independent set by removing both ends of a greedy maximal matching, losing at most `|S \ I|` vertices of every independent `I` (Lemma 7.24). |
| [Alg/IndepSetSpectral.lean](Alg/IndepSetSpectral.lean), [Alg/IndepSetParams.lean](Alg/IndepSetParams.lean) | Lemmas 7.22 and 7.23: the `±1/√n` vector of `I` is within `4γ/(1 - θ)` of the bottom eigenspace, and thresholding a nearby vector misclassifies at most `n ‖w - u‖²` vertices; the thresholds from Corollary 4.2 and the function `f` of Theorem 1.1. |
| [Alg/IndepSet.lean](Alg/IndepSet.lean), [Alg/VertexCover.lean](Alg/VertexCover.lean) | The algorithm (the best rounding over the net and the set of all vertices) and Theorem 1.1, for all `γ` at once: sizes are integers, so either `|I| = n/2` and `I` is recovered exactly, or `n/2 - |I| ≥ 1/2` absorbs the net's error. Corollary 1.2 from the same algorithm. |

### Colorings: Theorems 1.3, 1.9 (1), 1.8 (1) and Corollary 1.4

| Files | Content |
| --- | --- |
| [Alg/Variance.lean](Alg/Variance.lean) | Partitions, their models, Lemma 6.1 with any upper bound `L` on the second eigenvalue, and Lemma 7.4. |
| [Alg/PartitionSpectral.lean](Alg/PartitionSpectral.lean), [Alg/Partition.lean](Alg/Partition.lean) | Theorem 5.1 for regular graphs: eigenspace closeness (Lemma 5.2), coordinate separation through the eigenvectors of the symmetrized model `B^(1/2) M B^(-1/2)`, whose eigenvalues lie in `[-1, 1]` (Lemma 5.3), and clustering (Lemma 5.4). |
| [Alg/Cluster.lean](Alg/Cluster.lean), [Alg/ClusterPolyTime.lean](Alg/ClusterPolyTime.lean) | The clustering algorithm: for every tuple of net vectors and of representative vertices, assign each vertex to the nearest representative, round each cluster, and keep the coloring with the most colored vertices. |
| [Alg/ModelFacts.lean](Alg/ModelFacts.lean), [Alg/ExpanderContract.lean](Alg/ExpanderContract.lean), [Alg/ExpanderAccount.lean](Alg/ExpanderAccount.lean), [Alg/Expander.lean](Alg/Expander.lean) | Lemma 7.3 (class sizes near `π`, through the symmetrized model and its characteristic polynomial), groups of equal rows, the contracted partition `χ'`, the removal count per group and its comparison with `α`; Theorems 1.9 (1) and 1.8 (1). |
| [Alg/ColoringAnalysis.lean](Alg/ColoringAnalysis.lean), [Alg/ColoringPolyTime.lean](Alg/ColoringPolyTime.lean), [Alg/Coloring.lean](Alg/Coloring.lean) | Theorem 1.3 with `f(λ) = 32 λ^(1/16)`, the rows of the model of a balanced almost-`3`-coloring being `Ω(γ)` apart; Corollary 1.4, comparing the clustering coloring with Theorem 1.1's independent set. |

### Hardness: Theorems 1.5, 1.6, 1.8 (2) and 1.9 (2)

| Files | Content |
| --- | --- |
| [Hard/Glue.lean](Hard/Glue.lean) | A polynomial-time checker of partial colorings with enough colored vertices; a reduction and an algorithm put Fact 8.1's gap problem in `PromiseP`, hence `NP ⊆ P`. |
| [Hard/Blowup.lean](Hard/Blowup.lean), [Hard/Coloring.lean](Hard/Coloring.lean), [Hard/Machine.lean](Hard/Machine.lean) | Blow-ups `T ⊗ J + W ⊗ A_G` of a template on finitely many cells, exactly regular because `W` has zero row sums ("absorber" cells join copies of `G` by its complement); the bilinear-form comparison with the planted matrix, the colorings in the yes and no cases, and the blow-up in polynomial time. |
| [Hard/Cayley.lean](Hard/Cayley.lean), [Hard/Dyadic.lean](Hard/Dyadic.lean), [Hard/Design.lean](Hard/Design.lean), [Hard/Pipeline.lean](Hard/Pipeline.lean) | Explicit pseudo-random graphs in place of random biregular graphs: Cayley sum graphs on `(𝔽₂^(2a+1))^r` from the bent function `w₀ + ⟨w₁, w₂⟩`, with sets of every dyadic density; templates from finite designs, their regularity and eigenvalue counts. |
| [Hard/Spectral.lean](Hard/Spectral.lean) | The planted matrix `M_ab / π_b` is at most `0` on vectors of sum `0`, from the characteristic polynomial of the symmetrized model; eigenvalue counting. |
| [Hard/LowRankDesign.lean](Hard/LowRankDesign.lean), [Hard/LowRankFacts.lean](Hard/LowRankFacts.lean), [Hard/LowRank.lean](Hard/LowRank.lean) | Theorem 1.6 (Theorem 8.6): five groups, a complete join and a tripartite part of densities `3/4, 1/2, 1/2`; at most two eigenvalues above `ε` and five below `-ε`, so `R = 7`. |
| [Hard/ModelUnits.lean](Hard/ModelUnits.lean), [Hard/ModelDesign.lean](Hard/ModelDesign.lean), [Hard/ModelCount.lean](Hard/ModelCount.lean), [Hard/ModelEst.lean](Hard/ModelEst.lean), [Hard/ModelYes.lean](Hard/ModelYes.lean), [Hard/ModelNo.lean](Hard/ModelNo.lean), [Hard/Model.lean](Hard/Model.lean) | Theorem 1.9 (2) (Theorem 8.2): one group per color, with densities `∝ ⌊D π_i M_ij⌋ / (s_i s_j)` (symmetric by detailed balance, so the template is exactly regular); color units colored along the distribution of the classes and paired with their half shift, giving copies of the input graph when the two colors differ and independent types otherwise, which accounts for the fraction `1 - α`; absorbers in the partner group. |
| [Hard/Corollaries.lean](Hard/Corollaries.lean) | Theorems 1.5 and 1.8 (2) from Theorem 1.9 (2): the model `[[0, ½, ½], [1, 0, 0], [1, 0, 0]]` with `α = 1/2`, and `δ = α/2`. |

### Fact 8.1 from the Unique Games Conjecture

[BansalKhot.lean](BansalKhot.lean) states Fact 8.1 (`BHSV25.BansalKhot`, with maximum degree at
most `η n` for every `η > 0`) and proves it from the conjecture (`BHSV25.bansalKhot`). The
reduction follows Bansal and Khot's long code test with one free bit, as described by Manurangsi
(arXiv:1705.03581, §4.2); [BK/README.md](BK/README.md) explains it.

| Files | Content |
| --- | --- |
| [BK/Basic.lean](BK/Basic.lean) | Long codes, influences and the decoding of labels, from BGHKLMM26. |
| [BK/Graph.lean](BK/Graph.lean), [BK/Vertices.lean](BK/Vertices.lean), [BK/Copies.lean](BK/Copies.lean), [BK/Complete.lean](BK/Complete.lean), [BK/Sound.lean](BK/Sound.lean), [BK/Machine.lean](BK/Machine.lean), [BK/Main.lean](BK/Main.lean) | The reduction: one vertex per random string of the test, adjacent when they demand incompatible values of a folded long code; completeness, soundness through the averaged long codes, maximum degree `≤ η n` by disjoint copies, polynomial time, and the assembly. |
| [BK/AintOver.lean](BK/AintOver.lean), [BK/Ensemble.lean](BK/Ensemble.lean), [BK/Invariance*.lean](BK/Invariance.lean), [BK/HyperReverse.lean](BK/HyperReverse.lean), [BK/AintProof.lean](BK/AintProof.lean) | "It Ain't Over Till It's Over" [MOO10, Theorem 4.9]: the average on a random subcube is a multilinear polynomial in a three-valued ensemble; an invariance principle between that ensemble and uniform signs (adapted from BGHKLMM26/RobustMIS), and reverse hypercontractivity on the cube, `E[f · T_r h] ≥ (E f)^k (E h)^k` for `r ≤ 1 - 1/k`, proved by induction from a two-point inequality. |

## How the proof is implemented

* **Nets** are computed deterministically from exact matrix powers and a grid of coefficients on
  few columns, in place of exact eigenvectors and random points (Lemma 5.6).
* **Clustering** guesses one representative vertex per cluster instead of a grid of centers, and
  separates coordinates through the eigenvectors of the symmetrized model. The net's precision
  `κ/n` is a constant depending only on the model small enough that it moves no vertex, so one
  algorithm serves every `ε` and every number of vertices (the definition of
  `(M, α)`-expander-coloring).
* **Lemma 6.1** is applied with an upper bound `L` on the second eigenvalue (such as `√λ`), so
  that the error `L/c + δ/(Lc)` tends to `0` for almost-colorings.
* **Hardness reductions** are deterministic: explicit pseudo-random graphs instead of random
  biregular Ramanujan graphs, blow-ups made exactly regular by absorbers, integral sizes and
  degrees from dyadic designs, and eigenvalue counts proved directly (Theorem 1.6 needs no
  Theorem 4.1).
* **"It Ain't Over Till It's Over"** is proved without Gaussian space: the invariance principle
  compares two discrete ensembles, and reverse hypercontractivity on the cube replaces the
  Gaussian isoperimetric argument.

*Formalized by [Claude Code](https://claude.com/claude-code).*
