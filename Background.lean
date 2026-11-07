module

public import Background.Ellipsoid
public import Background.PolyTime.Rat
public import Background.Encoding
public import Background.RandomGraph
public import Background.Pruning
public import Background.Sampling
public import Background.Gaussian
public import Background.GaussianCalculus
public import Background.ArcsinSeries
public import Background.GaussianCoins
public import Background.PhiSeries
public import Background.BlackBox
public import Background.Tuples
public import Background.UniqueGames
public import Background.SumOfSquares

/-!
# Background

Material that more than one paper needs and that doesn't belong to any single paper, including
the sum-of-squares method (`Background/SumOfSquares/`, see its `README.md`). Modules live under
`Background/` and import only Mathlib, CSLib, complexitylib, the libraries in `Imported/` and
other `Background` modules, never a paper. When something in a paper turns out to be needed by
another paper, move it here.

Add a `public import` here for every module under `Background/`, so that `lake build` checks it.
-/
