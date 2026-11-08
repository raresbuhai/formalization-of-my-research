module

public import BS23.Common.Good

/-!
# The good event in uniform form

`BS23.UniformNoise S η D ℓ ν` says that for every cluster `c`, every degree `p ≤ D` and every
direction `λ`, the empirical `p`-th moment of `⟨ν_j, λ⟩` over the cluster (normalized by `n`) is
within `η (λᵀSλ)^{p/2}` of `(|S_c|/n) · E Z^p · (λᵀSλ)^{p/2}`, as for Gaussian noise of
covariance `S`. It follows from `BS23.GoodNoise` for `ν_j = B g_j` with `S = B Bᵀ`, and it is the
form the deterministic analysis uses.
-/

@[expose] public section

namespace BS23

open Matrix

variable {k d : ℕ}

/-- The noise `ν` of a labelled sample has, cluster by cluster, the low-degree directional
moments of Gaussian noise of covariance `S`, up to `η (λᵀSλ)^{p/2}`. -/
def UniformNoise {n : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (D : ℕ) (ℓ : Fin n → Fin k)
    (ν : Fin n → Fin d → ℝ) : Prop :=
  ∀ c, ∀ p ≤ D, ∀ v : Fin d → ℝ,
    |(∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ v) ^ p) / n -
        ((cluster ℓ c).card : ℝ) / n * (gaussMom p : ℝ) * Real.sqrt (v ⬝ᵥ (S *ᵥ v)) ^ p| ≤
      η * Real.sqrt (v ⬝ᵥ (S *ᵥ v)) ^ p

end BS23
