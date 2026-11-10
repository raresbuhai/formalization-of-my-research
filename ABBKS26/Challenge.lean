module

public import ABBKS26.Model

/-!
# Main results: statements

Finite-precision variants of the main results of [ABBKS26], Theorems 1.1 and 1.2, in the full
versions of the paper's later sections (Theorems 5.2 and 6.2), with proofs `sorry`: the algorithms
read rational approximations of the sample points instead of the real points. Numbers are those of
the arXiv version (v2); they are the same in v1.

What a reader has to trust is this file and what it imports: the definitions in
`ABBKS26/Model.lean` (mixtures, separation, corruptions, rounding, randomized algorithms, inputs
and outputs), the encodings in `Background/Encoding.lean`, CSLib's multitape Turing machines, and
Mathlib.

## Conventions of both theorems

* **The model.** A mixture `M` of `k` Gaussians `N(μᵢ, Σᵢ)` in `ℝ^d` with nonnegative weights
  `wᵢ` summing to `1` and positive definite covariances (`ABBKS26.Mixture.Valid`). Theorem 1.1 is
  about centered mixtures, `μᵢ = 0` (`ABBKS26.Mixture.IsCentered`), Theorem 1.2 about mixtures
  whose components share one covariance `Σ` (`ABBKS26.Mixture.HasIdenticalCovariances`).
* **Corruptions.** The paper's sample consists of `n` independent points from a distribution `M'`
  with `d_TV(M', M) ≤ ε`, and its guarantee refers to "the set `Sᵢ` of samples generated according
  to the `i`-th component". Here each sample point is a triple `(i, y, z)` drawn from an
  `ε`-corruption `P` of `M` (`ABBKS26.IsCorruption`): `(i, y)` is a labelled point of `M`, `z` is
  the observed point, and `z ≠ y` with probability at most `ε`. The law of `z` is then such an
  `M'`, and every such `M'` arises this way. The guarantee is asked for **every** `ε`-corruption,
  so for every way of attaching the labels to the points of `M'`; `Sᵢ` is the set of sample points
  with label `i`, corrupted ones included. (That corrupted points count under their original
  labels is a convention; leaving them out of the `Sᵢ` instead changes each by about an `ε / wmin`
  fraction, within the error bound up to the constant.) Since the triples are independent, the
  corruption of a point may depend on its label and its point, but not on the other points (an
  oblivious adversary; [ABBKS26, Remarks 5.3 and 6.3] on adaptive adversaries are not
  formalized).
* **The input: rational approximations.** The paper analyzes its algorithms on real numbers and
  omits numerical precision, noting that they "can be implemented to give guarantees in the
  standard bit complexity model" [ABBKS26, §3]. Here the algorithm reads rational vectors, which
  makes that claim precise. A rounding `r` (`ABBKS26.Rounding`) maps each observed point
  `z`, together with its label `i`, to a rational vector within `1/n` of it in the geometry of the
  `i`-th component, `‖Σᵢ^{-1/2} (r (i, z) - z)‖ ≤ 1/n` (`ABBKS26.IsRounding`), and the algorithm
  reads the rounded points (`ABBKS26.roundedSample`). The guarantee holds for **every** such
  rounding, as in [BS23]:
  * it may be any function, measurable or not, may use the label of the point, and may depend on
    `M`, `n` and the corruption; it is applied to each point separately, so it does not depend on
    the other points of the sample, nor on the algorithm's coins.
  * The tolerance is measured with the covariance of the point's own component, so the condition
    is invariant, like the model, under invertible linear maps of `ℝ^d` (and, for Theorem 1.2,
    affine ones); that the rounded points are rational is preserved only by rational maps. A
    tolerance measured with a fixed matrix fails for the same reason an absolute one would:
    shrinking a thin component makes any fixed tolerance as large as the component.
  * Rounding every coordinate of a point of component `i` to a multiple of a power of two
    `h ≤ min(1, 2 √λ_min(Σᵢ) / (n √d))` stays within the tolerance; a coordinate `z_j` then takes
    `O(log (2 + |z_j| / h) + log (2 + 1 / h))` bits.
  * The paper states the bit-complexity claim without proof; its analysis is for the exact
    points. A proof also has to show that the paper's arguments survive moving each point by `1/n`
    in the geometry of its component. This does not reduce to the corruptions: the rounded points
    are rational, so their law is at total variation distance `1` from the mixture; the moment
    estimates, whitening, candidate selection and final classification each have to tolerate
    the perturbation. When the paper whitens a part `S` of the sample by the
    covariance of the components it contains, which is at least `wmin Σᵢ` for each of them, this
    moves each of their points by at most `1/(n √wmin)`; points of other components count as
    corruptions there.
* **The weight bound.** The algorithm is given a rational `wmin` with `0 < wmin ≤ wᵢ` for all `i`,
  which takes the place of the paper's minimum weight `w_min` in every bound. Logarithms are
  natural; the base only changes constants.
* **The separation parameter** `Δ` is a rational number given to the algorithm, as in the paper's
  algorithms (Algorithms 2 and 4), with every two components `Δ`-separated.
* **"`Δ, 1/ε ≥ f(1/w_min)` for some function `f`"** is `∃ f : ℝ → ℝ` with `f ≥ 1` everywhere,
  `f (1/wmin) ≤ Δ` and `ε ≤ 1 / f (1/wmin)`, for a corruption level `ε ≥ 0`. So `Δ ≥ 1` and
  `0 ≤ ε ≤ 1`. The bound `f ≥ 1` costs nothing (replace `f` by `max f 1`), but it is needed: for a
  negative `f` the hypothesis `0 ≤ ε ≤ 1 / f (1/wmin)` would be unsatisfiable. The function `f`
  occurs only in hypotheses, so it need not be computable. It may grow arbitrarily fast, so the
  sample sizes below, polynomial in `Δ`, may depend on `wmin` in any way, as in the paper.
* **The error** `O(k w_min⁻¹ max{ε, Δ^(-Ω(1/k))})` is `C k / wmin · max ε (Δ^(-1/(C k)))`. The
  output is a list of `n` numbers, one per sample point, its cluster, which must be one of
  `0, …, k - 1`; so the output is a partition of the sample into `k` sets `Ŝ₀, …, Ŝ_{k-1}`, and for
  some permutation `π`, `|Ŝᵢ ∩ S_{π(i)}| ≥ (1 - error) |S_{π(i)}|` for every `i`
  (`ABBKS26.RecoversClusters`).
* **Constants.** One natural number `C ≥ 1` stands for all the paper's `O(·)` and `Ω(·)`: the
  constant factor of the error, the exponent `1/(C k)` of `Δ` in it, and the degrees of the
  polynomial sample sizes and running times. One constant serves for all: a larger `C` only weakens
  the error, sample and time bounds (as `Δ ≥ 1`), and, although it also gives the algorithm more
  coins, an algorithm for a smaller `C` can be run on the first coins it needs, with `g` enlarged
  to pay for computing their number. So `C ≥ 1` costs nothing, and only rules out reading the
  degenerate `C = 0` (which would ask for exact recovery).
* **Running times** are in the length `|x|` of the encoded input, which counts every bit of the
  rounded sample. The paper's `g(w_min⁻¹, Δ) · poly(d)` is `g(⌈1/wmin⌉, ⌈Δ⌉) · (|x| + 2)^C`
  (`ABBKS26.centeredTime`): reading the sample takes time `|x|`, and the paper's sample sizes are
  polynomial in `d` for fixed `wmin` and `Δ`; what the bound keeps is that the degree of the
  polynomial does not grow with `k`, `wmin` or `Δ`. The function `g : ℕ → ℕ → ℕ` is existential,
  as in the paper, but must be **computable** (Mathlib's `Computable₂`): the algorithm is given
  exactly `T x` coins and may read them all, so the length of its coin string tells it `T x`, and
  for an arbitrary `g` that would be advice no machine computes. (For a computable `g` the
  algorithm gains nothing: it could compute `g` itself, within a larger computable time bound.)
* **Explicit `f` and `g`.** Footnotes to Theorems 5.2 and 6.2 add that `f(x) = exp(exp(Õ(x²)))`
  and `g(x, y) = exp(exp(exp(exp(Õ(min(x, y)²)))))` suffice. These refinements are not
  formalized; the theorems themselves say "for some function". The bound on `g` also does not fit
  the algorithms as written: with `min(x, y)` it stops growing with `Δ` once `Δ ≥ 1/w_min`, while
  the refinement steps (Algorithms 3 and 5) try every guess of `ε ≥ 1/Δ` at precision `2^(-Δ)`,
  a number of guesses exponential in `Δ`.
* **Probability** (`ABBKS26.successProb`) is over the sample and the algorithm's coins. The
  paper's "with high probability" is probability at least `1 - δ` for a rational `δ > 0` that the
  algorithm is given, from a sample whose size is also polynomial in `1/δ`; the algorithm, `C`,
  `f` and `g` do not depend on `δ`. The paper does not say how its resources depend on the failure
  probability, so this dependence is not taken from its statements but from its proof, in which
  everything that can fail fails less often with more samples or more repetitions:
  * the properties of the sample that the analysis uses hold with probability tending to `1` as
    the sample grows;
  * the randomized steps succeed with probability at least `2^(-O(·))` each and can be repeated
    more often;
  * the final selection among candidate clusterings ([ABBKS26, Theorem A.1], through the robust
    tournament of Fact 3.23) can use more fresh samples.

  A polynomial dependence on `1/δ` is weaker than the usual `log (1/δ)`; it is what these
  arguments give most directly, for instance with second-moment bounds. A logarithmic dependence
  is likely derivable as well, from exponential tail bounds or from weaker guarantees by repetition
  on independent parts of the sample and robust aggregation, but it is not claimed here. The
  running times need no term for `δ`: they are polynomial in `|x|`, which is at least the sample
  size, so at least `1/δ` (for `δ < 1`; for `δ ≥ 1` there is nothing to show).
* **Uniformity.** One algorithm, one constant and one pair of functions `f`, `g` serve all `k`, `d`,
  mixtures, `wmin`, `Δ`, failure probabilities `δ`, corruption levels `ε` and sample sizes. The
  algorithm is given `k`, `wmin`, `Δ`, `δ` and the rounded sample, but not `ε`, the weights, the
  means, the covariances, the labels, the corruption or the rounding.

## Theorem 1.1 (Theorem 5.2)

[ABBKS26, Theorem 5.2]: let `M = ∑ᵢ wᵢ N(0, Σᵢ)` be a mixture of `k` centered Gaussians in `ℝ^d`
with `Σᵢ ≻ 0` and `w_min = minᵢ wᵢ`, all of whose components are pairwise `Δ`-separated, and let
`M'` satisfy `d_TV(M', M) ≤ ε`, with `Δ, 1/ε ≥ f(1/w_min)` for some function `f`. Then, given
`poly(d, 1/w_min, Δ)` independent samples from `M'`, there is an algorithm that runs in time
`g(1/w_min, Δ) · poly(d)` for some function `g` and outputs with high probability a partition
`Ŝ₁, …, Ŝ_k` of the samples with, up to a permutation,
`minᵢ |Ŝᵢ ∩ Sᵢ| / |Sᵢ| ≥ 1 - O(k w_min⁻¹ max{ε, Δ^(-Ω(1/k))})`.

Formally (`ABBKS26.centered_clustering`):

* **Separation** (`ABBKS26.CenteredSeparated`, [ABBKS26, Definition 5.1]): for every two
  components, in one order or the other, either some direction `v` has `vᵀ Σᵢ v > Δ² vᵀ Σⱼ v`
  (`ABBKS26.SpectrallySeparated`), or
  `‖Σᵢ^{-1/2} Σⱼ Σᵢ^{-1/2} - I‖_F² > Δ² ‖Σᵢ^{-1/2} Σⱼ Σᵢ^{-1/2}‖²` with the spectral norm on the
  right (`ABBKS26.FrobeniusSeparated`, which states it without matrix square roots and explains
  why that is the same).
* **Sample size** `poly(d, 1/w_min, Δ)` is `((d + 1) (Δ + 1) / (wmin δ))^C`, with the factor
  `1/δ` for the failure probability.
* **Running time** `g(⌈1/wmin⌉, ⌈Δ⌉) · (|x| + 2)^C` (`ABBKS26.centeredTime`).

## Theorem 1.2 (Theorem 6.2)

[ABBKS26, Theorem 6.2]: let `M = ∑ᵢ wᵢ N(μᵢ, Σ)` be a mixture of `k` Gaussians in `ℝ^d` with
`Σ ≻ 0` and `w_min = minᵢ wᵢ`, all of whose components are pairwise `Δ`-separated, and let `M'`
satisfy `d_TV(M', M) ≤ ε`, with `Δ, 1/ε ≥ f(1/w_min)` for some function `f`. Then, given
`poly(d^(log w_min⁻¹), (w_min⁻¹)^(log w_min⁻¹), Δ)` independent samples from `M'`, there is an
algorithm that runs in time `g(1/w_min, Δ) · poly(d^(log² w_min⁻¹))` for some function `g` and
outputs with high probability a partition `Ŝ₁, …, Ŝ_k` of the samples with, up to a permutation,
`minᵢ |Ŝᵢ ∩ Sᵢ| / |Sᵢ| ≥ 1 - O(k w_min⁻¹ max{ε, Δ^(-Ω(1/k))})`.

Formally (`ABBKS26.identical_covariance_clustering`):

* **Separation** (`ABBKS26.MeanSeparated`, [ABBKS26, Definition 6.1]): for every two components,
  some direction `v` has `⟨μᵢ - μⱼ, v⟩² > 2 Δ² vᵀ Σ v`.
* **Sample size** `poly(d^(log w_min⁻¹), (w_min⁻¹)^(log w_min⁻¹), Δ)` is
  `((d + 1) / wmin)^(C (log (1/wmin) + 1)) ((Δ + 1) / δ)^C`, with the factor `1/δ` for the failure
  probability; the `+ 1`s keep it meaningful for `d = 0` or `wmin = 1`.
* **Running time** `g(⌈1/wmin⌉, ⌈Δ⌉) · (|x| + 2)^C · (d + 2)^(C (L² + 1))` with
  `L = logInv wmin ≈ log₂ (1/wmin)` (`ABBKS26.identicalCovTime`). As in Theorem 1.1, the factor
  `(|x| + 2)^C` pays for reading the sample, whose size the paper's bound
  `poly(d^(log² w_min⁻¹))` absorbs; its degree does not grow with `wmin`, so the exponent of `d`
  stays `O(log² (1/wmin))`.

Reference: [BS23] R.-D. Buhai, D. Steurer, *Beyond parallel pancakes: quasi-polynomial time
guarantees for non-spherical Gaussian mixtures*, COLT 2023, arXiv:2112.05445.
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
  sorry

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
  sorry

end ABBKS26
