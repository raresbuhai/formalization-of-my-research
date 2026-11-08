module

public import BS23.Model

/-!
# Main results: statements

Finite-precision variants of the main results of [BS23], Theorems 1.1, 1.2 and 1.3, in the full
versions of the paper's later sections (Theorems 4.2, 6.1 and 7.1), with proofs `sorry`: the
algorithms read rational approximations of the sample points instead of the real points. Numbers
are those of the arXiv version (v2).

What a reader has to trust is this file and what it imports: the definitions in `BS23/Model.lean`
(mixtures, samples, rounding, randomized algorithms, inputs and outputs), the encodings in
`Background/Encoding.lean`, CSLib's multitape Turing machines, and Mathlib.

## Conventions of all three theorems

* **The model.** The sample is `n` independent labelled points from a mixture `M` of `k` Gaussians
  `N(μᵢ, Σ)` in `ℝ^d` with nonnegative weights `wᵢ` summing to `1` and a positive definite
  covariance `Σ` shared by all components (`BS23.Mixture.Valid`, `BS23.Mixture.sampleLaw`). The
  labels are the paper's true clustering `S₁, …, S_k`.
* **The input: rational approximations.** The paper's algorithms read real numbers; here the
  algorithm reads rational vectors. A rounding `r` (`BS23.Rounding`) maps each labelled point to a
  rational vector within `1/n` of it in the geometry of the components,
  `‖Σ^{-1/2} (r (i, y) - y)‖ ≤ 1/n` (`BS23.IsRounding`), and the algorithm reads the rounded points
  (`BS23.roundedSample`). The guarantee holds for **every** such rounding:
  * it may be any function, measurable or not, may use the label of the point, and may depend on
    `M` and `n`; it is applied to each point separately, so it does not depend on the other points
    of the sample, nor on the algorithm's coins.
  * The tolerance is measured with `Σ`, so, like the model, it is invariant under affine maps of
    `ℝ^d`. An absolute tolerance `‖r (i, y) - y‖ ≤ δ` would make the theorems false for any `δ`
    depending only on `n, d, k` and the weights: their hypotheses do not change when the whole
    mixture is shrunk, and once all points lie within `δ` of `0` the rounding may map them all
    to `0`.
  * The tolerance is explicit, so short roundings exist. Rounding every coordinate to a multiple
    of a power of two `h ≤ min (1, 2 √λ_min(Σ) / (n √d))` stays within it, since the error is then
    at most `√d h / 2` in Euclidean norm. As `h ≤ 1`, a coordinate `y_j` then takes
    `O(log (2 + |y_j| / h) + log (2 + 1 / h))` bits. That count grows with the ratio of the
    coordinates to the smallest standard deviation `√λ_min(Σ)` of the components and with
    `log (n d)`. (A much smaller tolerance would force longer inputs, and the running times,
    which grow with the length of the input, would grow with it.)
  * This goes beyond the paper, whose analysis is for the exact points. A proof also has to show
    that the paper's arguments survive moving each point by `1/n` in the geometry of `Σ`. That
    includes the empirical moments, the sum-of-squares bounds built on them, the whitening, and
    the margins of the final clustering steps.
* **The weight bound.** The algorithm is given a rational `wmin` with `0 < wmin ≤ wᵢ` for all `i`,
  which takes the place of the paper's minimum weight `p_min` in every bound: the separation, the
  sample size and the running time. Taking `wmin = p_min` gives the paper's statements; when
  `p_min` is irrational, a rational `wmin ∈ [p_min / 2, p_min]` changes only constants, since
  `log (1/wmin) ≤ 2 log (1/p_min)` when `p_min ≤ 1/2` (that is, `k ≥ 2`). Logarithms are natural;
  the base only changes constants.
* **Constants.** One natural number `C` stands for all the paper's `O(·)`s and for "`C_sep` larger
  than some universal constant": the separation is at least `C log (1/wmin)` (in Theorem 1.1,
  `C ⌈1/δ⌉^C log (1/wmin)`), and `C` appears in the sample sizes and in the exponents of the
  running times. One constant serves for all, since each statement only gets weaker as `C` grows.
* **Sample sizes.** `(p_min⁻¹ d)^O(log p_min⁻¹)` is `((d + 1) / wmin)^(C (log (1/wmin) + 1))`; the
  `+ 1`s keep it at least `1` and meaningful for `d = 0` or `wmin = 1`.
* **Running times** are in the length `|x|` of the encoded input, which counts every bit of the
  rounded sample: the paper's `n^O(log p_min⁻¹)` is `|x|^O(log (1/wmin))`, and so on. The time
  bounds are explicit functions of the input (`BS23.bipartitionTime`, `BS23.colinearTime`,
  `BS23.radiusTime`), not any functions bounded by them: the algorithm is given exactly `T x`
  coins and may read them all, so the length of its coin string tells it `T x`, which for an
  arbitrary `T` could be advice no machine computes.
* **Probability** (`BS23.successProb`) is over the sample and the algorithm's coins.
* **Uniformity.** One algorithm and one constant serve all `k`, `d`, mixtures and sample sizes,
  and in Theorem 1.1 all failure probabilities (they depend only on the error exponent `c` in
  Theorems 1.2 and 1.3).
  The algorithm is given the rounded sample and `wmin` (and the failure probability `δ` in
  Theorem 1.1, and `k` and `R` where the paper's algorithm needs them), but not the weights, the
  means, `Σ`, the labels or the rounding.

## Theorem 1.1 (Theorem 4.2)

[BS23, Theorem 4.2]: consider a mixture with `‖Σ^{-1/2} (μₐ - μ_b)‖² ≥ C_sep log p_min⁻¹` for some
`a, b`, with `C_sep` larger than some universal constant. Given a sample of size
`n ≥ (p_min⁻¹ d)^O(log p_min⁻¹)`, there is an algorithm that runs in time
`n · d^O(log p_min⁻¹)` and returns with probability `0.99` a partition of `[n]` into two sets
`C₁, C₂` such that `maxᵢ |C₁ ∩ Sᵢ| / |Sᵢ| ≥ 0.99` and `maxᵢ |C₂ ∩ Sᵢ| / |Sᵢ| ≥ 0.99`.
[BS23, Theorem 1.1] is the case `p_min ≥ 1/k^100`.

Formally (`BS23.separating_bipartition`):

* **The output** is a list of `n` numbers, one per sample point; the points numbered `0` form
  `C₁`, the others `C₂` (`BS23.IsSeparatingBipartition`).
* **Running time `poly(|x|) · d^O(δ^(-O(1)) log (1/wmin))`** (`BS23.bipartitionTime`). This is
  weaker than the paper's `n · d^O(log p_min⁻¹)`, which counts arithmetic operations on real
  numbers. Here the factor in the length of the input may be any polynomial, not one linear in
  `n`. Since `n ≥ d^Ω(log (1/wmin))`, the second factor does not absorb the difference. What the
  bound keeps is that the exponent of `|x|` grows neither with `log (1/wmin)`, unlike in Theorems
  1.2 and 1.3, nor with `1/δ`. (A bound linear in `n` would need exact-degree time bounds for
  Turing machines.)
* **Probability `1 - δ`** for every failure probability `δ > 0`, which is part of the input
  (`BS23.BipartitionInput`): one algorithm and one `C` serve all `δ`. The factor `⌈1/δ⌉^C` in the
  separation, in the exponent of the sample size and in the exponent of the running time comes
  from the proof, not from the paper's statement, which is the case `δ = 1/100`. More samples
  alone would not lower the failure probability. The paper's algorithm fails when it builds the
  bipartition around an atypical sample point, and the probability of that is set by the
  separation and the degree of the moments, not by `n`. Repeating does not help either: two good
  bipartitions may split the components differently, so the algorithm cannot keep the one that
  most runs agree on. Taking the separation and the degree `δ^(-O(1))` times larger makes the
  failure probability `δ`; the degree enters the sample size and the running time through their
  exponents.
* The algorithm is given `δ` and `wmin` but not `k`; the paper's algorithm does not use `k`
  either.

## Theorem 1.2 (Theorem 6.1)

[BS23, Theorem 6.1]: consider a mixture with `‖Σ^{-1/2} (μᵢ - μⱼ)‖² ≥ C_sep log p_min⁻¹` for all
`i ≠ j`, with `C_sep` larger than some universal constant, whose means are colinear: `μᵢ` lies on a
line `μ_base + ℝ u` for a unit vector `u`. Let `σ² = (uᵀ cov⁻¹ u) / (uᵀ Σ⁻¹ u)`, where `cov` is the
covariance of the mixture. Given a sample of size
`n ≥ (σ⁻² ‖cov‖ ‖cov⁻¹‖)^O(1) (p_min⁻¹ d)^O(log p_min⁻¹)`, there is an algorithm that runs in time
`n^O(log p_min⁻¹)` and returns with high probability a partition of `[n]` into `k` sets
`C₁, …, C_k` such that, for some permutation `π` of `[k]`,
`1 - (1/n) ∑ᵢ |Cᵢ ∩ S_{π(i)}| ≤ (p_min / k)^O(1)`. [BS23, Theorem 1.2] is the case
`p_min ≥ 1/k^100` with the eigenvalues of `Σ` and `cov` polynomially bounded in `k` and `d`.

Formally (`BS23.colinear_clustering`):

* **The line.** The means lie on `base + ℝ u` for some `u ≠ 0` (`u` need not be a unit vector:
  `σ²` does not depend on its length, `BS23.Mixture.sigmaSq`). For `k ≥ 2` the separation makes
  the means distinct, so the line is unique; the sample size is asked for every line through the
  means, which matters only for `k = 1`.
* **`‖cov‖ ‖cov⁻¹‖`** is `hi / lo` for any bounds `lo > 0` and `hi` on the eigenvalues of `cov`
  (`BS23.Mixture.cov`), given as `lo ‖v‖² ≤ vᵀ cov v ≤ hi ‖v‖²` for all `v`; the best bounds are
  the extreme eigenvalues.
* **`(p_min / k)^O(1)`** is `(wmin / k)^c` for every exponent `c`, with the algorithm and `C`
  depending on `c`: the separation constant controls the exponent.
* **"With high probability"** is probability at least `1 - (wmin / k)^c`, with the same `c` as
  the error, at the paper's sample size. This is the order of failure probability the paper's
  proof gives. The rounding step it takes from Hopkins and Li fails with probability of the order
  of the clustering error. Its finite-sample lemmas fail with probability `δ` at sample sizes
  polynomial in `1/δ`, and the sample size leaves room for `δ = (wmin / k)^c`.
* **Running time `|x|^O(log (1/wmin))`** (`BS23.colinearTime`). The algorithm is given `k`.
* **The output** is a list of `n` numbers, one per sample point, its cluster, which must be one of
  `0, …, k - 1`; so the output is a partition of the sample into `k` sets
  (`BS23.ClustersWithin`).

## Theorem 1.3 (Theorem 7.1)

[BS23, Theorem 7.1]: consider a mixture with `‖Σ^{-1/2} (μᵢ - μⱼ)‖² ≥ C_sep log p_min⁻¹` for all
`i ≠ j`, with `C_sep` larger than some universal constant, and `‖Σ^{-1/2} μᵢ‖ ≤ R` for all `i`.
Given a sample of size `n ≥ (p_min⁻¹ d)^O(R² + log p_min⁻¹)`, there is an algorithm that runs in
time `n^O(R² + log p_min⁻¹)` and returns with high probability a partition of `[n]` into `k` sets
`C₁, …, C_k` such that, for some permutation `π` of `[k]`,
`1 - (1/n) ∑ᵢ |Cᵢ ∩ S_{π(i)}| ≤ (p_min / k)^O(1)`. [BS23, Theorem 1.3] is the case
`p_min ≥ 1/k^100`.

Formally (`BS23.small_radius_clustering`):

* **The radius** `R` is a rational number given to the algorithm, with `‖Σ^{-1/2} μᵢ‖² ≤ R²` for
  all `i`; the paper's algorithm uses moments of order `Ω(R²)`.
* **Running time `|x|^O(R² + log (1/wmin))`** (`BS23.radiusTime`). The algorithm is given `k`.
* `(p_min / k)^O(1)`, "with high probability" and the output are as in Theorem 1.2.
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
  sorry

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
  sorry

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
  sorry

end BS23
