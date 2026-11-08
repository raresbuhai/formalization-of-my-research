module

public import BMW26.Model
public import BMW26.Assembly
public import BMW26.Paper.FKN
public import BMW26.Paper.Spectral

/-!
# Efficient recovery of latent coordinate structure from sparse observations of the hypercube

Formalization of R.-D. Buhai, D. Mazzali and W. Wrzos-Kaminska, *Efficient Recovery of Latent
Coordinate Structure from Sparse Observations of the Hypercube*,
[arXiv:2610.11741](https://arxiv.org/abs/2610.11741).

* `BMW26/Challenge.lean`: the results, Theorem 1.2, Theorem 4.1 and Lemma 5.1, stated without
  proof. This file and what it imports are all a reader needs to check.
* `BMW26/Model.lean`: the definitions they are stated in.
* `BMW26/Cube/`, `BMW26/Prob/`: Fourier analysis on the hypercube, independent coins, and the
  percolated hypercube as coins.
* `BMW26/Spec/`: spectral concentration (Lemma 5.1 and its lemmas).
* `BMW26/SoS/`: the sum-of-squares FKN theorem (Theorem 4.1) and the certificate of Section 6.
* `BMW26/Round/`, `BMW26/Alg/`: the rounding, the algorithm, its correctness and running time.
* `BMW26/Assembly.lean`, `BMW26/Paper/`: the results from the parts.
* `BMW26/Solution.lean`: the same statements, proved.
* `BMW26/comparator.json`: tells `lake comparator` which theorems to compare.
* `BMW26/README.md`: how the proof is implemented.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
