module

public import BBKS24.Model
public import BBKS24.SparseNorm
public import BBKS24.Statistic
public import BBKS24.Events
public import BBKS24.Recovery
public import BBKS24.GraphList
public import BBKS24.Algorithm
public import BBKS24.Assembly
public import BBKS24.PolyTime
public import BBKS24.RunTime

/-!
# Semirandom planted clique and the restricted isometry property

Formalization of J. Błasiok, R.-D. Buhai, P. K. Kothari and D. Steurer, *Semirandom planted clique
and the restricted isometry property*, FOCS 2024,
[arXiv:2404.14159](https://arxiv.org/abs/2404.14159).

* `BBKS24/Challenge.lean`: the main result, stated without proof. This file and what it imports
  are all a reader needs to check.
* `BBKS24/Model.lean`: the definitions it is stated in.
* `BBKS24/SparseNorm.lean`: sparse operator norms of random matrices, and few large correlations
  (Lemma 3.3).
* `BBKS24/Statistic.lean`: the algorithm's statistic, and recovery from a good cut.
* `BBKS24/Events.lean`: the probability that the cut is good.
* `BBKS24/Recovery.lean`: recovery with probability `1 - 1/400` for all large `n`.
* `BBKS24/GraphList.lean`, `BBKS24/Algorithm.lean`: the algorithm on lists, and what it outputs.
* `BBKS24/Assembly.lean`: the success probability, for all large `n` and every `0 ≤ p < 1`.
* `BBKS24/PolyTime.lean`, `BBKS24/RunTime.lean`: the algorithm runs in polynomial time on
  multitape Turing machines.
* `BBKS24/Solution.lean`: the same statement, proved.
* `BBKS24/comparator.json`: tells `lake comparator` which theorems to compare.
* `BBKS24/README.md`: the plan of the proof.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
