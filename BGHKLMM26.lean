module

public import BGHKLMM26.Model
public import BGHKLMM26.GW
public import BGHKLMM26.Baseline
public import BGHKLMM26.Energy
public import BGHKLMM26.Strip
public import BGHKLMM26.Gain
public import BGHKLMM26.Ideal
public import BGHKLMM26.Opt
public import BGHKLMM26.Numerics
public import BGHKLMM26.SDP
public import BGHKLMM26.Factor
public import BGHKLMM26.Robust
public import BGHKLMM26.Algorithm
public import BGHKLMM26.Exact
public import BGHKLMM26.Accuracy
public import BGHKLMM26.Assembly
public import BGHKLMM26.Run
public import BGHKLMM26.PolyTime
public import BGHKLMM26.RunTime
public import BGHKLMM26.Stablest
public import BGHKLMM26.Hardness.Main
public import BGHKLMM26.RobustMIS.Final
public import BGHKLMM26.Inapprox
public import BGHKLMM26.IntGap.Main

/-!
# Optimal algorithms and hardness for Max-Cut in bounded degree graphs

Formalization of R.-D. Buhai, S. Ghoshal, N. Huang, P. K. Kothari, E. Lee, K. Makarychev and
Y. Makarychev, *Optimal Algorithms and Hardness for Max-Cut in Bounded Degree Graphs*,
SODA 2027, [arXiv:2610.27216](https://arxiv.org/abs/2610.27216).

* `BGHKLMM26/Challenge.lean`: the main results, stated without proof. This file and what it
  imports are all a reader needs to check.
* `BGHKLMM26/Model.lean`: the definitions they are stated in.
* `BGHKLMM26/Solution.lean`: the same statements, proved.
* `BGHKLMM26/comparator.json`: tells `lake comparator` which theorems to compare.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
