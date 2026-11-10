module

public import ABBKS26.Model
import ABBKS26.Assembly.Main

/-!
# Main results: proofs

Restates each theorem of `Challenge.lean` with the same name and statement, and proves it from the
development in this folder. Don't import `Challenge` here: the names would clash.

* Theorem 1.1 (Theorem 5.2): `ABBKS26.Main.centered_clustering_main` in
  `ABBKS26/Assembly/Main.lean`.
* Theorem 1.2 (Theorem 6.2): `ABBKS26.Main.identical_covariance_clustering_main` in
  `ABBKS26/Assembly/Main.lean`.
-/

public section

namespace ABBKS26

open MeasureTheory

/-- **Theorem 1.1** of [ABBKS26] (full version: Theorem 5.2): a mixture of centered Gaussians
whose components are pairwise `Δ`-separated, observed through an `ε`-corruption, can be clustered
from rounded samples, `poly(d, 1/wmin, Δ, 1/δ)` of them, in time `g(1/wmin, Δ) · poly(|x|)`, with
probability `1 - δ` for a `δ > 0` given to the algorithm, misclassifying in each component at most a
`C k / wmin · max ε (Δ^(-1/(C k)))` fraction of its points, provided `Δ` and `1/ε` are at least
`f(1/wmin)`. -/
theorem centered_clustering :
    ∃ (A : Input × List Bool → Output) (C : ℕ) (g : ℕ → ℕ → ℕ) (f : ℝ → ℝ),
      1 ≤ C ∧ (∀ x, 1 ≤ f x) ∧ Computable₂ g ∧
      RunsInTime encInput encOutput A (centeredTime g C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin Δ δ : ℚ), M.Valid → M.IsCentered →
        0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) → f (1 / wmin) ≤ Δ →
        (∀ a b, a ≠ b → CenteredSeparated Δ (M.S a) (M.S b)) → 0 < δ →
        ∀ (ε : ℝ) (P : Measure (Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))),
          0 ≤ ε → ε ≤ 1 / f (1 / wmin) → IsCorruption M ε P →
        ∀ n : ℕ, ((d + 1) * (Δ + 1) / ((wmin : ℝ) * δ)) ^ C ≤ n →
        ∀ r : Rounding k d, IsRounding M (1 / n) r →
          1 - δ ≤ successProb P n r (fun pts ↦ ⟨k, wmin, Δ, δ, pts⟩) A (centeredTime g C)
            (RecoversClusters (C * k / wmin * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))) :=
  Main.centered_clustering_main

/-- **Theorem 1.2** of [ABBKS26] (full version: Theorem 6.2): a mixture of Gaussians with one
common covariance whose components are pairwise `Δ`-separated, observed through an
`ε`-corruption, can be clustered from rounded samples,
`((d + 1) / wmin)^O(log (1/wmin)) poly(Δ, 1/δ)` of them, in time
`g(1/wmin, Δ) · poly(|x|) · d^O(log² (1/wmin))`, with probability `1 - δ` for a `δ > 0` given to
the algorithm, misclassifying in each component at most a `C k / wmin · max ε (Δ^(-1/(C k)))`
fraction of its points, provided `Δ` and `1/ε` are at least `f(1/wmin)`. -/
theorem identical_covariance_clustering :
    ∃ (A : Input × List Bool → Output) (C : ℕ) (g : ℕ → ℕ → ℕ) (f : ℝ → ℝ),
      1 ≤ C ∧ (∀ x, 1 ≤ f x) ∧ Computable₂ g ∧
      RunsInTime encInput encOutput A (identicalCovTime g C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin Δ δ : ℚ), M.Valid → M.HasIdenticalCovariances →
        0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) → f (1 / wmin) ≤ Δ →
        (∀ a b, a ≠ b → MeanSeparated Δ (M.μ a) (M.μ b) (M.S a)) → 0 < δ →
        ∀ (ε : ℝ) (P : Measure (Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))),
          0 ≤ ε → ε ≤ 1 / f (1 / wmin) → IsCorruption M ε P →
        ∀ n : ℕ,
          ((d + 1) / (wmin : ℝ)) ^ (C * (Real.log (1 / wmin) + 1)) * ((Δ + 1) / (δ : ℝ)) ^ C ≤ n →
        ∀ r : Rounding k d, IsRounding M (1 / n) r →
          1 - δ ≤ successProb P n r (fun pts ↦ ⟨k, wmin, Δ, δ, pts⟩) A (identicalCovTime g C)
            (RecoversClusters (C * k / wmin * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))) :=
  Main.identical_covariance_clustering_main

end ABBKS26
