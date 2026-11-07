module

public import BKS23.Certificate
public import BKS23.RandomCut
public import BKS23.Rounding
public import BKS23.Cleanup
public import BKS23.AlgorithmPolyTime
public import BKS23.Assembly
public import BKS23.Algorithm1PolyTime
public import BKS23.Assembly1

/-!
# Algorithms approaching the threshold for semi-random planted clique

Formalization of R.-D. Buhai, P. K. Kothari and D. Steurer, *Algorithms approaching the threshold
for semi-random planted clique*, STOC 2023, [arXiv:2212.05619](https://arxiv.org/abs/2212.05619).

* `BKS23/Challenge.lean`: the main results, stated without proof. This file and what it imports
  are all a reader needs to check.
* `BKS23/Solution.lean`: the same statements, proved.
* `BKS23/comparator.json`: tells `lake comparator` which theorems to compare.
* `BKS23/README.md`: the plan of the proof.
* `BKS23/Biclique.lean`, `BKS23/Certificate.lean`: the biclique certificates of §4, for any
  bipartite graph with balanced characters and bounded degrees.
* `BKS23/Random.lean`, `BKS23/RandomCut.lean`: the random graph `G(n, p)` (Mathlib's
  `SimpleGraph.binomialRandom`) and the properties of its cuts: balancedness, bounded degrees,
  no large bicliques, and the reduction of `p ≤ 1/2` to `p = 1/2`.
* `BKS23/CliqueProgram.lean`, `BKS23/Rounding.lean`: the clique program as a solver input, and
  the rounding of the solver's output to the planted clique.
* `BKS23/Cleanup.lean`: the cleanup, its correctness and the list size.
* `BKS23/Algorithm.lean`, `BKS23/AlgorithmPolyTime.lean`: the algorithm as a function on the
  encoded input, its correctness, and its running time on Turing machines.
* `BKS23/Assembly.lean`: the parameters, the asymptotics and the success probability, from which
  `Solution.lean` proves Theorem 5.6 (2).
* Theorem 5.6 (1): `BKS23/SpectralDefs.lean`, `BKS23/SpectralWalks.lean`,
  `BKS23/SpectralNorm.lean` (the norm of the cut of `G(n, q)`, by the moment method),
  `BKS23/SpectralCertificate.lean` (the degree-6 spectral certificate),
  `BKS23/Rounding1.lean`, `BKS23/Refine.lean`, `BKS23/NonNeighbors.lean` (rounding to a nearby
  set and refining it), `BKS23/Algorithm1.lean`, `BKS23/Algorithm1PolyTime.lean` (the
  algorithm), and `BKS23/Size1.lean`, `BKS23/Assembly1.lean` (the assembly).

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
