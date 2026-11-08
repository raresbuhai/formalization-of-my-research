module

public import BS23.Model

/-!
# The good event of a sample

All probability in the proofs of BS23 enters through one event on the sample: the cluster sizes
are close to their expectations, and the low-degree empirical moments of the standardized noise
of each cluster are close to those of a standard Gaussian. Everything else is deterministic on
this event.

* `BS23.gaussMom p`: `E Z^p` for a standard Gaussian `Z`, `(p-1)‼` for even `p` and `0` for odd.
* `BS23.gaussMomMulti α`: `E ∏ᵢ Gᵢ^αᵢ` for a standard Gaussian vector `G`.
* `BS23.stdNoise M ω j`: the standardized noise `Σ^{-1/2} (y_j - μ_{ℓ_j})` of the `j`-th point,
  with Mathlib's square root `CFC.sqrt Σ` (the one `multivariateGaussian` uses).
* `BS23.GoodNoise w η D ℓ g`: cluster fractions within a factor `1 ± η` of the weights, and the
  empirical moments `(1/n) ∑_{j ∈ S_c} g_j^α` within `η` of `(|S_c|/n) · gaussMomMulti α` for all
  multi-indices of total degree at most `D`.
-/

@[expose] public section

namespace BS23

open Matrix
open scoped MatrixOrder

/-- `E Z^p` for a standard Gaussian: `(p-1)‼` for even `p`, `0` for odd `p`. -/
def gaussMom (p : ℕ) : ℕ := if Even p then Nat.doubleFactorial (p - 1) else 0

/-- `E ∏ᵢ Gᵢ^αᵢ` for a standard Gaussian vector `G`. -/
def gaussMomMulti {d : ℕ} (α : Fin d → ℕ) : ℕ := ∏ i, gaussMom (α i)

variable {k d : ℕ}

/-- The standardized noise `Σ^{-1/2} (y_j - μ_{ℓ_j})` of the `j`-th point of a sample. -/
noncomputable def stdNoise (M : Mixture k d) {n : ℕ} (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d))
    (j : Fin n) : Fin d → ℝ :=
  (CFC.sqrt M.S)⁻¹ *ᵥ (fun i ↦ (ω j).2 i - M.μ (ω j).1 i)

/-- The labels of a sample. -/
def labels {n : ℕ} (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : Fin n → Fin k :=
  fun j ↦ (ω j).1

/-- The good event: cluster fractions within `1 ± η` of the weights, and empirical moments of
degree at most `D` of the standardized noise of each cluster within `η` of the Gaussian ones. -/
def GoodNoise {n : ℕ} (w : Fin k → ℝ) (η : ℝ) (D : ℕ) (ℓ : Fin n → Fin k)
    (g : Fin n → Fin d → ℝ) : Prop :=
  (∀ c, |((cluster ℓ c).card : ℝ) / n - w c| ≤ η * w c) ∧
    ∀ c, ∀ α : Fin d → ℕ, ∑ i, α i ≤ D →
      |(∑ j ∈ cluster ℓ c, ∏ i, g j i ^ α i) / n -
          ((cluster ℓ c).card : ℝ) / n * (gaussMomMulti α : ℝ)| ≤ η

end BS23
