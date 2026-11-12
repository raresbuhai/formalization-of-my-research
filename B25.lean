module

public import B25.Model
public import B25.RE.Main
public import B25.Lasso.Main
public import B25.Rot.Sphere
public import B25.Rot.SubGauss

/-!
# Lasso and partially-rotated designs

Formalization of R.-D. Buhai, *Lasso and Partially-Rotated Designs*,
[arXiv:2505.11093](https://arxiv.org/abs/2505.11093).

* `B25/Challenge.lean`: Theorem 1.5 (partially-rotated designs have restricted eigenvalue
  constants independent of the columns outside `S`), Corollary 1.6 (the prediction error of the
  Lasso), and Lemmas 1.3 and 1.4 (two families of partially-rotated designs), stated without
  proof. This file and what it imports are all a reader needs to check.
* `B25/Model.lean`: the definitions they are stated in.
* `B25/Basic.lean`: norms, correlations, signed tuples of coordinates, the restricted eigenvalue
  constant as an infimum, rotated designs.
* `B25/RE/`: Theorem 1.5: Maurey's sparsification [B25, Lemma 2.1], RNO on signed tuples implies
  RE [B25, Proposition 1.10], and the union bound.
* `B25/Lasso/`: Corollary 1.6: the Lasso's basic inequality and fast rate, and the Gaussian noise.
* `B25/Rot/`: Lemmas 1.3 and 1.4: rotations that map unit vectors to uniform points of the sphere,
  and sub-Gaussian rotations.
* `B25/Solution.lean`: the same statements, proved.
* `B25/comparator.json`: tells `lake comparator` which theorems to compare.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
