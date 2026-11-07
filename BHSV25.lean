module

public import BHSV25.Model
public import BHSV25.Spectral.ThresholdRank
public import BHSV25.Net.Spec
public import BHSV25.Alg.VertexCover
public import BHSV25.Alg.Coloring
public import BHSV25.Alg.Expander
public import BHSV25.BansalKhot
public import BHSV25.Hard.LowRank
public import BHSV25.Hard.Corollaries

/-!
# Finding colorings in one-sided expanders

Formalization of R.-D. Buhai, Y. Hua, D. Steurer and A. Vári-Kakas, *Finding Colorings in
One-Sided Expanders*, [arXiv:2508.02825](https://arxiv.org/abs/2508.02825).

* `BHSV25/Challenge.lean`: the main results, Theorems 1.1 to 1.9, stated without proof. This
  file and what it imports are all a reader needs to check.
* `BHSV25/Model.lean`: the definitions they are stated in.
* `BHSV25/Solution.lean`: the same statements, proved.
* `BHSV25/comparator.json`: tells `lake comparator` which theorems to compare.
* `BHSV25/README.md`: the map of the proof.
* `BHSV25/Spectral/`: eigenbases, eigenvalue counting, the normalized adjacency matrix, and
  Theorem 1.7 (Theorem 4.1 and Corollary 4.2).
* `BHSV25/Net/`: nets of eigenspaces computed in polynomial time, in place of exact
  eigenvectors.
* `BHSV25/Alg/`: the algorithms and their analysis: Theorems 1.1, 1.3, 1.8 (1), 1.9 (1),
  Corollaries 1.2 and 1.4.
* `BHSV25/BansalKhot.lean`, `BHSV25/BK/`: the paper's Fact 8.1, the starting point of its
  hardness reductions, from the Unique Games Conjecture (Bansal and Khot's reduction and "It Ain't
  Over Till It's Over").
* `BHSV25/Hard/`: the hardness reductions: Theorems 1.5, 1.6, 1.8 (2), 1.9 (2).

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
