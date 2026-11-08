module

public import BHJK25.Model
public import BHJK25.RS.Main
public import BHJK25.Spectral.Main

/-!
# The quasi-polynomial low-degree conjecture is false

Formalization of R.-D. Buhai, J.-T. Hsieh, A. Jain and P. K. Kothari, *The Quasi-Polynomial
Low-Degree Conjecture is False*, FOCS 2025, [arXiv:2505.17360](https://arxiv.org/abs/2505.17360).

* `BHJK25/Challenge.lean`: the two counterexamples, Theorems 2.1 and 3.1 (Theorems 1.3 and 1.6 in
  the introduction), stated without proof; Theorem 3.1 with an algorithm that reads rational
  approximations of the matrix. This file and what it imports are all a reader needs to check.
* `BHJK25/Model.lean`: the definitions they are stated in.
* `BHJK25/RS/`: Theorem 2.1: the Reed–Solomon construction, its uniformity, the null and planted
  bounds, Sudan's list decoder with Roth–Ruckenstein root finding, the search over guesses and its
  running time.
* `BHJK25/Spectral/`: Theorem 3.1: the Gaussian facts, the Legendre inequality, the low-degree
  bound, the eigenvalue of the noisy planted matrix, and the algorithm.
* `BHJK25/Machine/`: loops whose running time is linear in the number of rounds (from BB20).
* `BHJK25/Solution.lean`: the same statements, proved.
* `BHJK25/comparator.json`: tells `lake comparator` which theorems to compare.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
