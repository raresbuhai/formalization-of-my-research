module

public import ABBKS26.Model
public import ABBKS26.Assembly.Main

/-!
# Dimension reduction via sum-of-squares and clustering of non-spherical mixtures

Formalization of P. Anderson, M. Bafna, R.-D. Buhai, P. K. Kothari and D. Steurer, *Dimension
Reduction via Sum-of-Squares and Improved Clustering Algorithms for Non-Spherical Mixtures*,
COLT 2026, [arXiv:2411.12438](https://arxiv.org/abs/2411.12438).

* `ABBKS26/Challenge.lean`: finite-precision variants of the main results, Theorems 1.1 and 1.2
  (in their full versions, Theorems 5.2 and 6.2), stated without proof. This file and what it
  imports are all a reader needs to check.
* `ABBKS26/Model.lean`: the definitions they are stated in.
* `ABBKS26/Common/`, `ABBKS26/SoS/`: shared definitions, Gram factors, and normed sum-of-squares
  inequalities.
* `ABBKS26/Rounding/`: the paper's Section 4, deterministic subspace rounding (Algorithm 1,
  Theorem 4.1) and the orthogonal-complement system (Lemma 4.3, Theorem 4.2).
* `ABBKS26/Centered/`: Section 5.1, the centered constraint system and the subspace theorem for
  centered mixtures (Theorem 5.6).
* `ABBKS26/IdCov/`: Section 6.1, the moment system and the subspace theorem for a common
  covariance (Theorem 6.5).
* `ABBKS26/Robust/`: the robust subroutines, a quadratic filter and certified moments.
* `ABBKS26/Prob/`, `ABBKS26/Split/`, `ABBKS26/Linalg/`: the good event of a sample and its
  probability, window counts of Gaussians, and separation of covariances.
* `ABBKS26/Tree/`: splits, the refinement step and the refinement tree (Algorithms 2–5).
* `ABBKS26/Select/`: learning of every candidate, selection and reclustering (Appendix A).
* `ABBKS26/Assembly/`: the schedule of parameters, the list programs, the running time and the
  main theorems.
* `ABBKS26/Solution.lean`: the same statements, proved.
* `ABBKS26/comparator.json`: tells `lake comparator` which theorems to compare.
* `ABBKS26/README.md`: how the proof is implemented.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
