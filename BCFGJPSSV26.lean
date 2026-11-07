module

public import BCFGJPSSV26.Model
public import BCFGJPSSV26.Combine
public import BCFGJPSSV26.Basic.Metric
public import BCFGJPSSV26.Basic.Raw
public import BCFGJPSSV26.Stable.Main
public import BCFGJPSSV26.Greedy.Main
public import BCFGJPSSV26.FL.Main

/-!
# A better-than-2 approximation for k-median

Formalization of R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte,
M. R. Pittu, M. Stouras, O. Svensson and L. Vogl, *A Better-than-2 Approximation for k-Median*,
Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144), and
Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172).

* `BCFGJPSSV26/Challenge.lean`: the main results, stated without proof. This file and what it
  imports are all a reader needs to check.
* `BCFGJPSSV26/Model.lean`: the definitions they are stated in.
* `BCFGJPSSV26/Solution.lean`: the same statements, proved.
* `BCFGJPSSV26/Combine.lean`: Theorem 1.1 from Theorems 1.2 and 1.3
  (`BCFGJPSSV26.Combine.thm11_of`).
* `BCFGJPSSV26/Greedy/Main.lean`, `BCFGJPSSV26/Stable/Main.lean`, `BCFGJPSSV26/FL/Main.lean`:
  Theorems 1.2, 1.3 and 1.4 (`BCFGJPSSV26.Greedy.greedy_main`, `BCFGJPSSV26.Stable.stable_main`,
  `BCFGJPSSV26.FL.fl_main`).
* `BCFGJPSSV26/comparator.json`: tells `lake comparator` which theorems to compare.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
