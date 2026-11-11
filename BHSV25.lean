module

public import BHSV25.Model
public import BHSV25.Time
public import BHSV25.TimePad
public import BHSV25.Spectral.ThresholdRank
public import BHSV25.Net.Spec
public import BHSV25.Net.GSCorrect
public import BHSV25.Net.GSPolyTime
public import BHSV25.Alg.GridPartition
public import BHSV25.Alg.GridPolyTime
public import BHSV25.Alg.IndepSetUnif
public import BHSV25.Alg.ExpanderFull
public import BHSV25.Alg.ColoringFull
public import BHSV25.Alg.VertexCoverFull
public import BHSV25.Alg.ColoringOrFull
public import BHSV25.Alg.VertexCover
public import BHSV25.Alg.Coloring
public import BHSV25.Planted.PartialThm
public import BHSV25.Planted.FullThm
public import BHSV25.BansalKhot
public import BHSV25.Hard.LowRank
public import BHSV25.Hard.Corollaries
public import BHSV25.Hard.Unbalanced

/-!
# Finding colorings in one-sided expanders

Formalization of R.-D. Buhai, Y. Hua, D. Steurer and A. Vári-Kakas, *Finding Colorings in
One-Sided Expanders*, [arXiv:2508.02825](https://arxiv.org/abs/2508.02825).

* `BHSV25/Challenge.lean`: the main results, stated without proof, with the algorithms in the full
  versions of Section 7 (explicit errors and running times), including random planting. This
  file and what it imports are all a reader needs to check.
* `BHSV25/Model.lean`: the definitions they are stated in.
* `BHSV25/Solution.lean`: the same statements, all proved.
* `BHSV25/comparator.json`: tells `lake comparator` which theorems to compare.
* `BHSV25/README.md`: the map of the proof.
* `BHSV25/Time.lean`: running times `n^{O(1)} · g(p)`, by fixing the parameter `p` of one
  polynomial-time machine; `BHSV25/TimePad.lean`: running times `n^{O(1)} · g(t)` for a number
  `t` the algorithm finds itself, with a padding computed from the input.
* `BHSV25/Spectral/`: eigenbases, eigenvalue counting, the normalized adjacency matrix, and
  Theorem 1.7 (Theorem 4.1 and Corollary 4.2).
* `BHSV25/Net/`: nets of eigenspaces computed in polynomial time, in place of exact
  eigenvectors: the greedy net, from exact integer powers of the adjacency matrix, greedy
  Gram–Schmidt on their rows and the integer points of a ball, with constant precision and a
  number of candidates independent of the graph; the number of rounds of the greedy selection,
  found from the residuals of the rows.
* `BHSV25/Alg/`: the algorithms and their analysis: Theorem 7.20 and Corollary 7.21 (rounding the
  net of the bottom eigenspace, with the spectral gap of regular graphs at `-1`, for all numbers
  of eigenvalues at once), Theorems 7.1
  and 7.9 and Corollary 7.2 (the net of large eigenvalues in absolute value and the clustering
  with a grid of centers), and Corollaries 1.2 and 1.4, which combine these algorithms.
* `BHSV25/Planted/`: random planting, Theorems 7.12 and 7.17: Theorem 5.1 for the adjacency
  matrix of the planted graph, concentration by McDiarmid's inequality, the threshold rank after
  planting, and the uncoloring, safe recoloring and brute force of the full recovery.
* `BHSV25/UG/`: from the Unique Games Conjecture on graphs to hardness on left-regular bipartite
  instances: the double cover and Khot and Regev's regularization.
* `BHSV25/BansalKhot.lean`, `BHSV25/BK/`: the paper's Fact 8.1, the starting point of its
  hardness reductions, from the Unique Games Conjecture (Bansal and Khot's reduction and "It Ain't
  Over Till It's Over").
* `BHSV25/Hard/`: the hardness reductions: Theorems 1.5, 1.6, 1.8 (2), 1.9 (2).

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
