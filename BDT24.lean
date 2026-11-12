module

public import BDT24.Model
public import BDT24.Main
public import BDT24.LowDeg.Main
public import BDT24.SQ.Main

/-!
# Computational-statistical gaps for improper learning in sparse linear regression

Formalization of R.-D. Buhai, J. Ding and S. Tiegel, *Computational-Statistical Gaps for Improper
Learning in Sparse Linear Regression*, COLT 2024,
[arXiv:2402.14103](https://arxiv.org/abs/2402.14103).

* `BDT24/Challenge.lean`: a finite-precision variant of the reduction from negative sparse PCA to
  sparse linear regression, Theorem 3.1, stated without proof: both algorithms read their samples
  to a given number of bits, the PCA algorithm to more bits than it gives the regression
  algorithm. Also the low-degree and statistical-query lower bounds for negative sparse PCA,
  Theorems B.4 and C.6. This file and what it imports are all a reader needs to check.
* `BDT24/Model.lean`: the definitions it is stated in.
* `BDT24/Alg/`: the reduction's algorithm (`Defs.lean`), the numerics for drawing Gaussians from
  coins (`Numerics.lean`, copied from BGHKLMM26), its polynomial-time pieces and running time, and
  its coins.
* `BDT24/Prob/`: the regression instances of the reduction [BDT24, Fact 2.1], Gaussian tail
  bounds, and the exchangeability argument of [BDT24, Lemma 4.1].
* `BDT24/Analysis/`: what the algorithm computes on quantized samples, the paired test, the good
  events, and the planted and null cases.
* `BDT24/Main.lean`: Theorem 3.1.
* `BDT24/LowDeg/`: Theorem B.4, through the Hermite expansion of the low-degree norm and the
  moments of the overlap of two spikes [BDT24, Lemma B.5].
* `BDT24/SQ/`: Theorem C.6, through the density of a planted point, the closed form of the
  correlations, and Hölder's inequality.
* `BDT24/Solution.lean`: the statements of `Challenge.lean`, proved.
* `BDT24/comparator.json`: tells `lake comparator` which theorems to compare.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
