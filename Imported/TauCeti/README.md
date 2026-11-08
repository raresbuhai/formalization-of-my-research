# Files from TauCeti

These files are copied from [TauCeti](https://github.com/TauCetiProject/TauCeti) (Apache-2.0, see
[LICENSE](LICENSE)), with their paths, module names and copyright headers unchanged. TauCeti is on
our Lean version but a slightly newer Mathlib, so it cannot be a dependency here; when it shares our
Mathlib, this folder can be replaced by it.

The files are the import closures of two modules:

* `TauCeti.Probability.Distributions.Gaussian.OwensT`, at commit
  `385ec2ddd8ddf8cc779b78c176308cb9c6b55499`: the error function, the Gaussian distribution function
  `Φ`, and Owen's `T` function.
* `TauCeti.Probability.Moments.Bernstein`, at commit `e583e15d3be177d86491854d1db508f6edfe5ee7`:
  Bernstein's inequality for sums of independent bounded random variables, with its imports
  `TauCeti.Probability.Moments.Basic`, `TauCeti.MeasureTheory.Measure.Tail` and
  `TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound`. These four files are unchanged.

Changes for our Mathlib:

* `TauCeti/MeasureTheory/Measure/Real.lean`: `_root_.add_apply` (from a newer Mathlib) is
  `Measure.add_apply`.
