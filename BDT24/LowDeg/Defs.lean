module

public import BDT24.Model
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Definitions for the low-degree and statistical-query bounds

* **Multivariate Hermite polynomials** (`BDT24.LowDeg.hermiteMv`): `H_α = ∏ᵢ He_{αᵢ}(Xᵢ)` for a
  multi-index `α : ι → ℕ`, with `α! = ∏ᵢ αᵢ!` (`BDT24.LowDeg.multiFact`) and the multi-indices of
  total degree at most `D` (`BDT24.LowDeg.degSet`). Under independent standard Gaussians they
  are orthogonal with `E H_α² = α!`, and the polynomials of degree at most `D` are their
  combinations with `|α| ≤ D`.
* **Hermite coefficients of a planted point** (`BDT24.LowDeg.hermCoef`): for a unit spike `x`,
  `E_{N(0, I - θ x xᵀ)} H_a = (-θ)^m (2m - 1)!! x^a` when `|a| = 2m`, and `0` when `|a|` is odd.
* **The overlap of two spikes** (`BDT24.LowDeg.spikeIP`) and its moments under two independent
  uniform sign patterns (`BDT24.LowDeg.overlapMoment`) [BDT24, Lemma B.5].
-/

@[expose] public section

namespace BDT24.LowDeg

/-- The multivariate Hermite polynomial `H_α = ∏ᵢ He_{αᵢ}(Xᵢ)` (probabilists' Hermite
polynomials, Mathlib's `Polynomial.hermite`). -/
noncomputable def hermiteMv {ι : Type*} [Fintype ι] (α : ι → ℕ) : MvPolynomial ι ℝ :=
  ∏ i, Polynomial.aeval (MvPolynomial.X i : MvPolynomial ι ℝ) (Polynomial.hermite (α i))

/-- `α! = ∏ᵢ αᵢ!`. -/
def multiFact {ι : Type*} [Fintype ι] (α : ι → ℕ) : ℝ := ∏ i, ((α i).factorial : ℝ)

/-- The multi-indices of total degree at most `D`. -/
def degSet (ι : Type*) [Fintype ι] [DecidableEq ι] (D : ℕ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ Finset.range (D + 1)).filter fun α ↦ ∑ i, α i ≤ D

/-- The Hermite coefficient `E_{N(0, I - θ x xᵀ)} H_a` of a unit spike `x`: `(-θ)^m (2m - 1)!! x^a`
when `|a| = 2m`, and `0` when `|a|` is odd. -/
noncomputable def hermCoef {m : ℕ} (θ : ℝ) (x : Fin m → ℝ) (a : Fin m → ℕ) : ℝ :=
  if Even (∑ j, a j) then
    (-θ) ^ ((∑ j, a j) / 2) * ((∑ j, a j) - 1).doubleFactorial * ∏ j, x j ^ a j
  else 0

/-- The overlap `⟨x_u, x_v⟩` of the spikes of two sign patterns. -/
noncomputable def spikeIP {d : ℕ} (k : ℕ) (u v : Fin d → SignType) : ℝ :=
  ∑ j, spikeVector k u j * spikeVector k v j

/-- The moment `E ⟨x_u, x_v⟩^(2L)` for two independent uniform sign patterns. -/
noncomputable def overlapMoment (d k L : ℕ) : ℝ :=
  (∑ u ∈ spikeSigns d k, ∑ v ∈ spikeSigns d k, spikeIP k u v ^ (2 * L)) /
    ((spikeSigns d k).card : ℝ) ^ 2

end BDT24.LowDeg
