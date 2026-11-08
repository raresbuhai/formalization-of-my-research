module

public import BS23.Model
import BS23.Separating.Main
import BS23.ColinearSoS.Main
import BS23.SmallRadius.Main

/-!
# Main results: proofs

Restates each theorem of `Challenge.lean` with the same name and statement, and proves it from the
development in this folder. Don't import `Challenge` here: the names would clash.

* Theorem 1.1: `BS23.Separating.separating_bipartition_main` in `BS23/Separating/Main.lean`.
* Theorem 1.2: `BS23.ColinearSoS.colinear_clustering_main` in `BS23/ColinearSoS/Main.lean`.
* Theorem 1.3: `BS23.SmallRadius.small_radius_clustering_main` in `BS23/SmallRadius/Main.lean`.
-/

public section

namespace BS23

open Matrix

/-- **Theorem 1.1** of [BS23] (full version: Theorem 4.2): if some two components of a mixture of
Gaussians with a common covariance are separated by `C ⌈1/δ⌉^C log (1/wmin)` in the geometry of
the covariance, then from a quasi-polynomial number of rounded samples one algorithm, given the
failure probability `δ > 0`, computes in time `poly(|x|) · d^O(δ^(-O(1)) log (1/wmin))`, with
probability `1 - δ`, a bipartition of the sample each side of which contains `99%` of the points
of some component. -/
theorem separating_bipartition :
    ∃ (A : BipartitionInput × List Bool → Output) (C : ℕ),
      RunsInTime encBipartitionInput encOutput A (bipartitionTime C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin δ : ℚ), M.Valid → 0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) →
        0 < δ →
        (∃ a b, a ≠ b ∧ C * ⌈1 / δ⌉₊ ^ C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) →
        ∀ n : ℕ, ((d + 1) / (wmin : ℝ)) ^ (C * ⌈1 / δ⌉₊ ^ C * (Real.log (1 / wmin) + 1)) ≤ n →
        ∀ r : Rounding k d, IsRounding M.S (1 / n) r →
          1 - (δ : ℝ) ≤ successProb M n r (fun pts ↦ ⟨δ, wmin, pts⟩) A (bipartitionTime C)
            IsSeparatingBipartition :=
  Separating.separating_bipartition_main

/-- **Theorem 1.2** of [BS23] (full version: Theorem 6.1): a mixture of Gaussians with a common
covariance, pairwise separated by `C log (1/wmin)` in the geometry of the covariance and with
colinear means, can be clustered from rounded samples in time `|x|^O(log (1/wmin))` with error
`(wmin / k)^c` and probability `1 - (wmin / k)^c`, for every `c`. -/
theorem colinear_clustering :
    ∀ c : ℕ, ∃ (A : ColinearInput × List Bool → Output) (C : ℕ),
      RunsInTime encColinearInput encOutput A (colinearTime C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin : ℚ), M.Valid → 0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) →
        (∀ a b, a ≠ b → C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) →
        ∀ base u : Fin d → ℝ, u ≠ 0 → (∀ i, ∃ t : ℝ, M.μ i = base + t • u) →
        ∀ lo hi : ℝ, 0 < lo → (∀ v, lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M.cov *ᵥ v)) →
          (∀ v, v ⬝ᵥ (M.cov *ᵥ v) ≤ hi * (v ⬝ᵥ v)) →
        ∀ n : ℕ, (hi / (lo * M.sigmaSq u)) ^ C *
            ((d + 1) / (wmin : ℝ)) ^ (C * (Real.log (1 / wmin) + 1)) ≤ n →
        ∀ r : Rounding k d, IsRounding M.S (1 / n) r →
          1 - ((wmin : ℝ) / k) ^ c ≤ successProb M n r (fun pts ↦ ⟨k, wmin, pts⟩) A
            (colinearTime C) (ClustersWithin (((wmin : ℝ) / k) ^ c)) :=
  ColinearSoS.colinear_clustering_main

/-- **Theorem 1.3** of [BS23] (full version: Theorem 7.1): a mixture of Gaussians with a common
covariance, pairwise separated by `C log (1/wmin)` in the geometry of the covariance and with means
of length at most `R` in that geometry, can be clustered from rounded samples in time
`|x|^O(R² + log (1/wmin))` with error `(wmin / k)^c` and probability `1 - (wmin / k)^c`, for every
`c`. -/
theorem small_radius_clustering :
    ∀ c : ℕ, ∃ (A : RadiusInput × List Bool → Output) (C : ℕ),
      RunsInTime encRadiusInput encOutput A (radiusTime C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin : ℚ), M.Valid → 0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) →
        (∀ a b, a ≠ b → C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) →
        ∀ R : ℚ, (∀ i, sqNormIn M.S (M.μ i) ≤ (R : ℝ) ^ 2) →
        ∀ n : ℕ, ((d + 1) / (wmin : ℝ)) ^ (C * ((R : ℝ) ^ 2 + Real.log (1 / wmin) + 1)) ≤ n →
        ∀ r : Rounding k d, IsRounding M.S (1 / n) r →
          1 - ((wmin : ℝ) / k) ^ c ≤ successProb M n r (fun pts ↦ ⟨k, wmin, R, pts⟩) A
            (radiusTime C) (ClustersWithin (((wmin : ℝ) / k) ^ c)) :=
  SmallRadius.small_radius_clustering_main

end BS23
