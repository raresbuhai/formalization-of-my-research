module

public import BB20.Model
public import BB20.Basic
public import BB20.Structural
public import BB20.LowerBound
public import BB20.Prediction
public import BB20.Learning.Correct
public import BB20.Machine.Threshold
public import BB20.Machine.Time

/-!
# Learning restricted Boltzmann machines with sparse latent variables

Formalization of G. Bresler and R.-D. Buhai, *Learning Restricted Boltzmann Machines with Sparse
Latent Variables*, NeurIPS 2020, [arXiv:2006.04166](https://arxiv.org/abs/2006.04166).

* `BB20/Challenge.lean`: the main results, Theorems 4, 6, 11 and 12, stated without proof. This
  file and what it imports are all a reader needs to check.
* `BB20/Model.lean`: the definitions they are stated in.
* `BB20/Basic.lean`, `BB20/Basic/`: the observed law, Walsh inversion, the local field, the
  Markov property.
* `BB20/Structural.lean`, `BB20/Structural/`: Theorem 4.
* `BB20/LowerBound.lean`, `BB20/LowerBound/`: the lower bound on the proxy `ν`.
* `BB20/Learning/`: the algorithms of Theorems 6 and 11 and their correctness.
* `BB20/Machine/`: their thresholds and running time on multitape Turing machines.
* `BB20/Prediction.lean`, `BB20/Prediction/`: Theorem 12.
* `BB20/Solution.lean`: the same statements, proved.
* `BB20/comparator.json`: tells `lake comparator` which theorems to compare.
* `BB20/README.md`: how the proof is implemented.

This root module imports the development. It must not import both `Challenge` and `Solution`:
they declare the same names.
-/
