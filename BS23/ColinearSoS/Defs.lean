module

public import BS23.Common.Hermite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The moments along the line of means

Definitions shared by the analysis of the sum-of-squares algorithm for [BS23, Theorem 1.2]. In the
whitened frame of the mixture, its points are `aᵢ ŭ + (Gaussian noise)`, with the noise of variance
`σ²` along the unit direction `ŭ` of the means. The one-dimensional mixture along `ŭ` is
`∑_c w_c N(a_c, σ²)`.

* `BS23.ColinearSoS.lineMom w a σ2 l = ∑_c w_c hmom (2l) a_c σ²`: its moment `M_{2l}` of order
  `2l`.
* `BS23.ColinearSoS.nbeta w a σ2 m l = (2m-1)‼ M_{2l} / (2l-1)‼`: the normalized coefficient of
  `⟨ŭ, v⟩^{2l} ‖v_⊥‖^{2(m-l)}` in the directional moment of order `2m` (see
  `BS23/ColinearSoS/Bernstein.lean`). For `l = m` it is `M_{2m}`, the moment along `ŭ` itself.
-/

@[expose] public section

namespace BS23.ColinearSoS

/-- The moment `M_{2l} = ∑_c w_c hmom (2l) a_c σ²` of order `2l` of the one-dimensional mixture
`∑_c w_c N(a_c, σ²)`. -/
noncomputable def lineMom {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) (l : ℕ) : ℝ :=
  ∑ c, w c * hmom (2 * l) (a c) σ2

/-- The normalized coefficient `β_l = (2m-1)‼ M_{2l} / (2l-1)‼`. -/
noncomputable def nbeta {k : ℕ} (w a : Fin k → ℝ) (σ2 : ℝ) (m l : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * m - 1) : ℝ) * lineMom w a σ2 l / (Nat.doubleFactorial (2 * l - 1) : ℝ)

end BS23.ColinearSoS
