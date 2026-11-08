module

public import BS23.Model
public import BS23.Separating.Main
public import BS23.Colinear.Main
public import BS23.ColinearSoS.Main
public import BS23.SmallRadius.Main

/-!
# Beyond parallel pancakes: quasi-polynomial time guarantees for non-spherical Gaussian mixtures

Formalization of R.-D. Buhai and D. Steurer, *Beyond Parallel Pancakes: Quasi-Polynomial Time
Guarantees for Non-Spherical Gaussian Mixtures*, COLT 2023,
[arXiv:2112.05445](https://arxiv.org/abs/2112.05445).

* `BS23/Challenge.lean`: finite-precision variants of the main results, Theorems 1.1, 1.2 and 1.3
  (in their full versions, Theorems 4.2, 6.1 and 7.1), stated without proof. This file and what
  it imports are all a reader needs to check.
* `BS23/Model.lean`: the definitions they are stated in.
* `BS23/Common/`: the good event of a sample and its probability, Gaussian moments, Hermite
  polynomials with a variance parameter, the one-dimensional moment mismatch, and the passage from
  a sample to the algorithm's input.
* `BS23/ColinearSoS/`: Theorem 1.2, by the sum-of-squares programs that maximize or minimize a
  directional moment, a direction rounded from their pseudo-moments, and a clustering on a line.
* `BS23/Colinear/`: the clustering on a line and the covariance comparison used for Theorem 1.2,
  and a second proof of Theorem 1.2, by a polynomial-time algorithm from empirical Hermite
  moments.
* `BS23/Separating/`: Theorem 1.1, by the separating polynomial of a sum-of-squares program and a
  random pivot.
* `BS23/SmallRadius/`: Theorem 1.3, by `k` rounds of sum-of-squares clustering.
* `BS23/Solution.lean`: the same statements, proved.
* `BS23/comparator.json`: tells `lake comparator` which theorems to compare.
* `BS23/README.md`: how the proof is implemented.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
