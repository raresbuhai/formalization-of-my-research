module

public import BDT24.Model
import BDT24.Main
import BDT24.LowDeg.Main
import BDT24.SQ.Main

/-!
# Main results: proofs

Restates the theorems of `Challenge.lean` with the same names and statements, and proves them from
the development in this folder: Theorem 3.1 by `BDT24.Main.negSPCA_of_sparse_regression_main`
(`BDT24/Main.lean`), Theorem B.4 by `BDT24.LowDeg.lowDegree_negSPCA_main` (`BDT24/LowDeg/Main.lean`)
and Theorem C.6 by `BDT24.SQ.sq_negSPCA_main` (`BDT24/SQ/Main.lean`). Don't import `Challenge`
here: the names would clash.
-/

public section

namespace BDT24

/-- **Theorem 3.1** of [BDT24]: an efficient algorithm that achieves prediction error `0.01` for
sparse linear regression with Gaussian design and noise variance `1` with probability `1 - δ`,
reading its sample to `p` bits, gives an algorithm running in time `O(1 + δ^(-1/2)) · poly(|x|)`
that solves negative sparse PCA with `θ = (k+1)/(k+2)` from the same number of samples, read to
polynomially many more bits, with probability `1 - √(2δ) - exp(-Ω(n))`. -/
theorem negSPCA_of_sparse_regression :
    ∃ c C : ℝ, 0 < c ∧
      ∀ (A : SLRInput × List Bool → Estimate) (e : ℕ),
        RunsInTime encSLRInput encEstimate A (slrTime e) →
      ∃ (B : SPCAInput × List Bool → Bool) (e' E : ℕ),
        RunsInTime encSPCAInput Encoding.encBool B (spcaTime e') ∧
        ∀ δ : ℚ, 0 < δ → ∀ n d k p : ℕ, k ≤ d →
          SolvesSLR A (slrTime e) n (2 * d) k p δ →
          ∀ q : ℕ, (n + d + p + 2) ^ E ≤ q →
            SolvesNegSPCA B (spcaTime e') δ p q n d k (√(2 * δ) + C * Real.exp (-c * n)) :=
  Main.negSPCA_of_sparse_regression_main

/-- **Theorem B.4** of [BDT24]: for `δ ∈ (0, 0.1]` and `n = o(min(d, k^(2-δ)))`, polynomials of
degree `k^δ` in the coordinates of `n` points have advantage `o(1)` in telling the planted law
of negative sparse PCA from the null law. -/
theorem lowDegree_negSPCA :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ k₀ : ℕ,
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ n d k : ℕ, k₀ ≤ k → k ≤ d →
        (n : ℝ) ≤ η * min (d : ℝ) ((k : ℝ) ^ (2 - δ)) →
        AdvantageAtMost sampleCoords ((k : ℝ) ^ δ) (plantedSample n d k θ) (nullSample n d) ε :=
  LowDeg.lowDegree_negSPCA_main

/-- **Theorem C.6** of [BDT24]: for `δ ∈ (0, 0.1]` and `n = o(min(d/k^δ, k^(2-2δ)))`, the
statistical dimension of negative sparse PCA at VSTAT parameter `n` is at least `2^(k^δ)`,
uniformly for `θ ≤ (k+1)/(k+2)`. -/
theorem sq_negSPCA :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∃ η : ℝ, 0 < η ∧ ∃ k₀ : ℕ,
      ∀ n d k : ℕ, k₀ ≤ k → k ≤ d → 0 < n →
        (n : ℝ) ≤ η * min ((d : ℝ) / (k : ℝ) ^ δ) ((k : ℝ) ^ (2 - 2 * δ)) →
        ∀ θ : ℝ, 0 < θ → θ ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) →
          SDAAtLeast d k θ n ⌈(2 : ℝ) ^ ((k : ℝ) ^ δ)⌉₊ :=
  SQ.sq_negSPCA_main

end BDT24
