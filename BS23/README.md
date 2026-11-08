# BS23: Beyond parallel pancakes: quasi-polynomial time guarantees for non-spherical Gaussian mixtures

The results are finite-precision variants of [BS23, Theorems 1.1, 1.2 and 1.3], in their full
versions (Theorems 4.2, 6.1 and 7.1), stated in [Challenge.lean](Challenge.lean) with the
definitions of [Model.lean](Model.lean) and proved in [Solution.lean](Solution.lean), with only the
standard axioms; `lake comparator` checks them. The algorithms read rational approximations of the
sample points, and the guarantees hold for every such approximation. Theorem 1.1's running time,
`poly(|x|) · d^O(δ^(-O(1)) log (1/wmin))` for the failure probability `δ`, is polynomial rather
than linear in `n` (the paper has `n · d^O(log (1/wmin))` for `δ = 1/100`). This is due to the
machine model: the paper counts unit-cost arithmetic operations in a RAM model, while the theorems
here are about multitape Turing machines, which simulate a word RAM only with polynomial overhead.

The formal proofs follow the paper's sum-of-squares algorithms in outline, though some of their
steps take a different route (see [below](#how-the-proof-is-implemented)). In addition to the
proof of Theorem 1.2 that follows the paper, which is the one [Solution.lean](Solution.lean) uses,
the formalization contains a second, independent proof of Theorem 1.2 with a different algorithm,
which uses no sum-of-squares and runs in polynomial time
(see [below](#theorem-12-a-second-proof-polynomial-time)).

Numbers refer to the arXiv version (v2).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 1.1 (Thm. 4.2) | `separating_bipartition` | There are `C` and an algorithm, given the failure probability `δ > 0`, running in time `poly(\|x\|) · d^O(⌈1/δ⌉^C log (1/wmin))` that, if some two components have `‖Σ^(-1/2) (μₐ - μ_b)‖² ≥ C ⌈1/δ⌉^C log (1/wmin)`, returns from `n ≥ ((d + 1)/wmin)^(C ⌈1/δ⌉^C (log (1/wmin) + 1))` rounded samples, with probability `1 - δ`, a bipartition each side of which contains `99%` of the points of some component. |
| Theorem 1.2 (Thm. 6.1) | `colinear_clustering` | For every `c` there are `C` and an algorithm running in time `\|x\|^O(log (1/wmin))` that, if the means lie on a line and all pairs have `‖Σ^(-1/2) (μₐ - μ_b)‖² ≥ C log (1/wmin)`, clusters `n ≥ (hi / (lo σ²))^C ((d + 1)/wmin)^(C (log (1/wmin) + 1))` rounded samples into `k` sets with error `(wmin/k)^c`, with probability `1 - (wmin/k)^c`. |
| Theorem 1.3 (Thm. 7.1) | `small_radius_clustering` | For every `c` there are `C` and an algorithm running in time `\|x\|^O(R² + log (1/wmin))` that, if all pairs have `‖Σ^(-1/2) (μₐ - μ_b)‖² ≥ C log (1/wmin)` and all means `‖Σ^(-1/2) μᵢ‖ ≤ R`, clusters `n ≥ ((d + 1)/wmin)^(C (R² + log (1/wmin) + 1))` rounded samples into `k` sets with error `(wmin/k)^c`, with probability `1 - (wmin/k)^c`. |

* **The model** ([Model.lean](Model.lean)): `k` Gaussians `N(μᵢ, Σ)` in `ℝ^d` with one positive
  definite covariance `Σ` and nonnegative weights `wᵢ` summing to `1`. The sample is `n`
  independent labelled points, and the labels are the true clustering.
* **Rounded samples** (`BS23.IsRounding`): the algorithm reads, for each point `y` with label `i`,
  a rational vector `r (i, y)` with `‖Σ^(-1/2) (r (i, y) - y)‖ ≤ 1/n`. The guarantees hold for
  every such rounding `r`. It is applied to each point separately, may use the label and depend on
  the mixture and on `n`, and need not be measurable. The paper's analysis is for the exact
  points.
* **The weight bound**: the algorithm is given a rational `wmin` with `0 < wmin ≤ wᵢ`, which
  replaces the paper's `p_min` in every bound. One natural number `C` stands for all the `O(·)`s
  and for the separation constant.
* **Algorithms** are multitape Turing machines with coins, running within explicit time bounds
  (`BS23.bipartitionTime`, `BS23.colinearTime`, `BS23.radiusTime`) in the length `|x|` of the
  encoded input. They are given the rounded sample and `wmin` (and the failure probability `δ` in
  Theorem 1.1, `k` in Theorems 1.2 and 1.3, `R` in Theorem 1.3), but not the weights, the means,
  `Σ`, the labels or the rounding. The probability (`BS23.successProb`) is over the sample and the
  coins; it is a lower integral, since the rounding need not be measurable.
* **Theorem 1.1** holds with probability `1 - δ` for every failure probability `δ > 0`, which is
  part of the input; one algorithm and one `C` serve all `δ`. The paper's statement is the case
  `δ = 1/100`; the factor `⌈1/δ⌉^C` in the separation and in the exponents of the sample size and
  the running time comes from the proof. Its running time is discussed above.
* **Theorems 1.2 and 1.3**: the error `(p_min/k)^O(1)` is `(wmin/k)^c` for every `c`, with the
  algorithm and `C` depending on `c`, and "with high probability" is probability
  `1 - (wmin/k)^c` at the paper's sample size. Every label is one of `0, …, k - 1`. In Theorem 1.2,
  `‖cov‖ ‖cov⁻¹‖` is `hi/lo` for any bounds `lo > 0` and `hi` on the eigenvalues of the covariance
  `cov` of the mixture, and `σ² = (uᵀ cov⁻¹ u) / (uᵀ Σ⁻¹ u)` for the direction `u` of the line.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### Common structure

* **One good event.** All probability enters through one event on the sample
  ([Common/Good.lean](Common/Good.lean), `BS23.GoodNoise`): the cluster sizes are within `1 ± η`
  of their expectations, and the empirical moments of degree at most `D` of the standardized noise
  `Σ^(-1/2) (yⱼ - μ_ℓⱼ)` of each cluster are within `η` of those of a standard Gaussian.
  Chebyshev's inequality (TauCeti's weak law) and a union bound over the labels and the
  multi-indices bound its failure probability by `k/(n η²) · (1/wmin + (d + 1)^D (2D)^D)`
  ([Common/GoodProb.lean](Common/GoodProb.lean)). A lower bound over the coins on every good
  sample gives a lower bound on `successProb` by monotonicity of the lower integral
  ([Common/Glue.lean](Common/Glue.lean)).
* **Everything else is deterministic** on the good event, for every rounding, including the
  rounding itself: it moves each point by at most `1/n` in the geometry of `Σ`, and every step of
  the analyses carries this perturbation. Only the pivots of Theorems 1.1 and 1.3 use coins.
* [Common/UniformProof.lean](Common/UniformProof.lean) puts the good event in uniform directional
  form (`BS23.UniformNoise`, [Common/Uniform.lean](Common/Uniform.lean)): along every direction
  `λ`, the empirical `p`-th moments of the noise are those of `N(0, λᵀΣλ)` up to
  `η (d + 1)^D (λᵀΣλ)^(p/2)`, by the multinomial theorem.
* [Common/Input.lean](Common/Input.lean) transports the input of the algorithms, the rounded sample
  as lists of rationals, to the points `j ↦ r (ωⱼ)` indexed by `Fin n` and `Fin d`.
* [Common/Hermite.lean](Common/Hermite.lean), [Common/HermiteFacts.lean](Common/HermiteFacts.lean)
  and [Common/Gaussian.lean](Common/Gaussian.lean): Hermite polynomials `He_m(x; q)` with a
  variance parameter (homogeneity, the heat identity, inversion, derivatives) and the moments of
  standard Gaussian vectors.

### Theorem 1.2: colinear means

The algorithm ([ColinearSoS/Alg.lean](ColinearSoS/Alg.lean)) follows the paper's: approximate
isotropic position, sum-of-squares programs over directions `v` that maximize the `2s`-th or
minimize the `2t`-th directional moment, a direction rounded from `Ẽ[vvᵀ]`, and a clustering of
the projections on a line. With `s = logInv wmin + 1` and `t = 256 s`:

1. the points are whitened with rational arithmetic as for Theorem 1.1, `Xⱼ = W (Yⱼ - ȳ)`, so
   that their empirical covariance is `D = diag κ` with `κᵢ ∈ (1/2, 2]`; the unit sphere of the
   empirical covariance is `vᵀDv = 1`;
2. program U ([ColinearSoS/Program.lean](ColinearSoS/Program.lean)) maximizes `Ẽ Φ̂_{2s}` over
   degree-`2s` pseudo-distributions on `{vᵀDv = 1, ‖v‖² ≤ 256}`, for the empirical moment
   polynomial `Φ̂_r = (1/n) ∑ⱼ ⟨Xⱼ, v⟩^r`; if the optimum is at least `(5s)^s`, its
   pseudo-expectation is used, otherwise that of program L, which minimizes `Ẽ Φ̂_{2t}` at
   degree `2t`;
3. the direction is the column `â` of the pseudo-moment matrix `Ẽ[vvᵀ]` at its largest diagonal
   entry, mapped back to the original coordinates, `a = Wᵀ â`;
4. the projections `⟨a, Yⱼ⟩` are clustered on the line
   ([Colinear/OneDim.lean](Colinear/OneDim.lean)): at the smallest scale `h` of a geometric grid at
   which the cells `[p h, (p + 1) h)` holding at least `θ n` points (the heavy cells) cover all but
   an `ε` fraction of the points, the `k - 1` largest gaps between consecutive heavy cells separate
   the clusters.

The solver optimizes the moments directly, where the paper searches for thresholds; the choice
between the two programs is a test on the optimum of program U, so the algorithm does not need
`σ²`; the direction is rounded with a column of `Ẽ[vvᵀ]` instead of its top eigenvector, which is
irrational; and the line clustering replaces Hopkins and Li's.

The analysis is deterministic on the good event:

* **The frame** ([ColinearSoS/Frame.lean](ColinearSoS/Frame.lean)). In the whitened coordinates,
  with `cov_W = W cov Wᵀ`, the centered means are `a_c ŭ` for the direction `ŭ ∝ W u₀`
  normalized by `ŭᵀ cov_W⁻¹ ŭ = 1`, the noise covariance is `G + σ² ŭŭᵀ` with
  `G = cov_W - ŭŭᵀ ⪰ 0`, and `σ² = M.sigmaSq u₀`. The Fisher ratio
  `⟨a, u₀⟩² / (aᵀΣa · u₀ᵀΣ⁻¹u₀)` of `a = Wᵀ â` is `σ² ⟨ŭ, â⟩² / (âᵀGâ + σ² ⟨ŭ, â⟩²)`.
* **Moment equality** ([ColinearSoS/Bernstein.lean](ColinearSoS/Bernstein.lean)). With
  `x = ⟨ŭ, v⟩` and `y = vᵀGv`, the population moment polynomial of degree `2m` is
  `∑_l C(2m, 2l) (2m - 2l - 1)‼ M_{2l} x^{2l} y^{m-l}`, where `M_{2l}` are the moments of the
  one-dimensional mixture `∑_c w_c N(a_c, σ²)` along the line (the paper's moment equality,
  regrouped). The coefficients are nonnegative and every `x^{2l} y^{m-l}` is a sum of squares, so
  a pseudo-expectation on the sphere `vᵀ cov_W v = 1` induces a probability distribution
  `π_l ∝ C(m, l) Ẽ[x^{2l} y^{m-l}]` on `{0, …, m}`, with
  `Ẽ Φ_{2m} = (2m - 1)‼ ∑_l π_l M_{2l} / (2l - 1)‼` and `Ẽ y ≤ 1 - π_m`. Identifiability is then a
  comparison of the one-dimensional ratios `r_l = M_{2l} / (2l - 1)‼`.
* **The ratios** ([ColinearSoS/Ratios.lean](ColinearSoS/Ratios.lean)). If `M_{2s} ≥ (4s)^s`,
  then `r_l ≤ r_s / 2^(s-l)` (by log-convexity of the moments, from their form as Gaussian
  integrals), so a near-maximal `Ẽ` has `π_s ≈ 1`: case U, where the means dominate. If all
  `a_c² ≤ A²`, `σ² ≤ 1/16` and `t ≥ 5 A² + 8`, then `r_l ≥ 2 r_t` for `l < t` (by Stein's
  recurrence for Gaussian moments), so a near-minimal `Ẽ` has `π_t ≈ 1`: case L, where the means
  are bounded and the noise along the line is small.
* **The test.** `OPT_U ≥ (5s)^s` forces `M_{2s} ≥ (4s)^s`. Otherwise `M_{2s} ≤ 3 (5s)^s`, so all
  `a_c² ≤ 20 s` since the weights are at least `wmin`, and the separation forces `σ² ≤ 1/16`;
  case L applies with `t = 256 s`.
* **The pseudo-expectation analysis**
  ([ColinearSoS/PseudoAnalysis.lean](ColinearSoS/PseudoAnalysis.lean)) puts this together with
  explicit errors: the equality `vᵀDv = 1` with sum-of-squares multipliers, the bound
  `|Ẽ f| ≤ ‖f‖₁ 258^m` from the ball, the comparison of `D` with `cov_W`, and near-optimality
  against the point `v* ∝ cov_W⁻¹ ŭ`. The defect `Ẽ[vᵀGv]` is at most a multiple of the
  finite-sample and solver errors.
* **Rounding** ([ColinearSoS/Rounding.lean](ColinearSoS/Rounding.lean)). For `M = Ẽ[vvᵀ] ⪰ 0`
  with `tr(GM) ≤ δ'` and `ŭᵀMŭ ≥ 1/2`, the column `â` at the largest diagonal entry has
  `âᵀGâ ≤ 3σ² ⟨ŭ, â⟩²` once `δ' ≤ min(1/(10⁴ d), 3σ²/8)`, so its Fisher ratio is at least `1/4`,
  and the projected means are `Ω(√(C log (1/wmin)))` apart in units of `√(aᵀΣa)`.
* **Finite-sample transfer** ([ColinearSoS/MomentPoly.lean](ColinearSoS/MomentPoly.lean)). On the
  good event, `‖Φ̂_{2m} - Φ_{2m}‖₁ ≤ (2η/wmin + 1/n) (10⁶ (d + 1)⁶ (m + 1) / wmin)^(4m + 2)`, from
  the per-cluster moment closeness of Theorem 1.1 and a bound on the shift `ȳ - μ̄`.
* **The line** ([Colinear/OneDimCorrect.lean](Colinear/OneDimCorrect.lean),
  [Colinear/OneDimApply.lean](Colinear/OneDimApply.lean)): the clustering on the line is correct
  when few points of each cluster are far from its center and some scale of the grid lies between
  the spread and a twentieth of the gaps. The tails come from Markov's inequality on the empirical
  moments of order `2 (logInv wmin + 4)`, and the error is `(wmin/k)^c` for the separation
  constant `4 · 10⁸ · 4^c`.
* **Correctness** ([ColinearSoS/Correct.lean](ColinearSoS/Correct.lean)) chains these with the
  covariance comparison of [Colinear/Moments.lean](Colinear/Moments.lean) (`Ĉ` is close to the
  covariance `cov` of the mixture).
* **The running time** `|x|^O(log (1/wmin))` ([ColinearSoS/PolyTime.lean](ColinearSoS/PolyTime.lean),
  [ColinearSoS/RunTime.lean](ColinearSoS/RunTime.lean)): the machine writes the solver's budget
  `(d + 5)^(2t + 1)` in unary and runs a list program that is polynomial-time in the input and the
  budget. The algorithm ignores its coins.

[ColinearSoS/Main.lean](ColinearSoS/Main.lean) puts the parts together. The proof needs
`n ≥ σ⁻⁴ ((d + 1)/wmin)^(2c + 109000 (logInv wmin + 1))` samples, with no dependence on `hi/lo`:
the algorithm only uses the geometry of `Ĉ`.

### Theorem 1.2, a second proof: polynomial time

[Colinear/](Colinear/) also proves Theorem 1.2 (`BS23.Colinear.colinear_clustering_main`), with an
algorithm ([Colinear/Alg.lean](Colinear/Alg.lean)) that uses no sum-of-squares and runs in
polynomial time; `Solution.lean` uses the proof above. The algorithm:

1. the empirical mean `ȳ` and covariance `Ĉ`, and a `Ĉ`-orthogonal basis `λ₁, …, λ_d`: `λᵢ` is a
   column of the adjugate of the leading `(i + 1) × (i + 1)` block of `Ĉ`;
2. for every degree `3 ≤ m ≤ M = 40 (logInv wmin + 1)` and basis vector `λ`, the empirical Hermite
   moment `P̂_m(λ) = (1/n) ∑ⱼ He_m(⟨λ, yⱼ - ȳ⟩; λᵀĈλ)` and the score `P̂_m(λ)² / (λᵀĈλ)^m`; the
   pair `(m, λᵢ)` of best score;
3. the direction `a = Ĉ⁻¹ ∇P̂_m(λᵢ)`;
4. the projections `⟨a, yⱼ⟩`, clustered on the line as above.

The analysis ([Colinear/Correct.lean](Colinear/Correct.lean), `BS23.Colinear.alg_correct`) is
deterministic on the good event:

* **Moments.** Along every direction, the empirical moments of the rounded points are close to the
  mixture's ([Colinear/Moments.lean](Colinear/Moments.lean)). So `Ĉ` is close to the covariance
  `cov` of the mixture, and `P̂_m`, a Lipschitz polynomial in the raw moments
  ([Colinear/HermiteScore.lean](Colinear/HermiteScore.lean)), is close to its population value. By
  the heat identity, that value is a rank-one form `h̃_m ⟨u₀, v⟩^m` along the direction `u₀` of
  the means, with `h̃_m = ∑_c w_c He_m(t_c - t̄; τ²)` for the positions `t_c` of the means on the
  line ([Colinear/Population.lean](Colinear/Population.lean)).
* **The mismatch lemma** ([Common/Mismatch.lean](Common/Mismatch.lean)): a discrete distribution
  `V` on the line whose atoms have weight at least `w` has, for `t ≥ 10` and `t ≥ 10 ln (1/w)`,
  some `1 ≤ m ≤ 4t` with `|E He_m(V; E V²)| ≥ (E V²)^(2t) / (4 · 16^t)`. Otherwise its moments of
  orders `2t` and `4t` would be within a factor `1 ± 1/2` of the Gaussian ones, whereas
  `w² E V^(4t) ≤ (E V^(2t))²` and `(4t - 1)‼ ≥ 2^t ((2t - 1)‼)²`. Hence some `h̃_m` with
  `3 ≤ m ≤ M` is large (`h̃_1 = h̃_2 = 0`).
* **The direction.** Some basis vector has `⟨λᵢ, u₀⟩² / λᵢᵀĈλᵢ ≥ u₀ᵀĈ⁻¹u₀ / d`, so the selected
  pair has a large score ([Colinear/Basis.lean](Colinear/Basis.lean)). The gradient of `P̂_m`,
  which is determined by its values at `m + 1` points of a line
  ([Colinear/Line.lean](Colinear/Line.lean)), is then `c u₀ + E` with `E` small
  ([Colinear/Gradient.lean](Colinear/Gradient.lean)), and `a = Ĉ⁻¹ ∇P̂_m` has Fisher ratio
  `⟨a, u₀⟩² / (aᵀΣa · u₀ᵀΣ⁻¹u₀) ≥ 1/4` ([Colinear/Direction.lean](Colinear/Direction.lean)); the
  optimal direction `cov⁻¹ u₀`, a multiple of `Σ⁻¹ u₀`, has ratio `1`. So the projected means are
  `Ω(√(C log (1/wmin)))` apart in units of `√(aᵀΣa)`.
* **Exact arithmetic.** The algorithm is written over any linearly ordered field with a floor: the
  machine runs it over `ℚ`, the analysis over `ℝ`, and the two agree on rational points
  ([Colinear/Cast.lean](Colinear/Cast.lean)). It ignores its coins, and every number it computes is
  a closed-form expression of polynomial size (sums over the points, determinants, Hermite
  polynomials of degree at most `M`), so complexitylib's polynomial-time calculus certifies it
  ([Colinear/PolyTime.lean](Colinear/PolyTime.lean), with `PolyTimeBasic`, `PolyTimeLinAlg`,
  `PolyTimeScore` and `PolyTimeOneDim`).

[Colinear/Main.lean](Colinear/Main.lean) puts the parts together; this proof needs
`n ≥ σ⁻⁴ ((d + 1)/wmin)^(2c + 8200 (logInv wmin + 1))` samples.

### Theorem 1.1: separating bipartition

The algorithm ([Separating/Alg.lean](Separating/Alg.lean)) is the paper's, with `s = logInv wmin + 1`
and `t = r s`:

1. the points are centered and whitened with rational arithmetic
   ([Separating/Whiten.lean](Separating/Whiten.lean)): the rows of the whitening matrix are the
   `Ĉ`-orthogonal basis vectors of [Colinear/Basis.lean](Colinear/Basis.lean) divided by powers of
   two, so the whitened points `xⱼ` have a diagonal covariance with entries in `(1/2, 2]`, and the
   explicit ball constraint that the solver needs is the paper's bound on the covariance norm of
   `v`, up to constants;
2. the solver of [../Background/SumOfSquares](../Background/SumOfSquares/README.md) finds a
   degree-`2t` pseudo-expectation `Ẽ` over `v ∈ ℝ^d` with `‖v‖² ≤ 256`, `F_{2s}(v) ≥ 1` and
   `F_{2t}(v) ≤ 1024^t`, for the pair moments `F_p(v) = n⁻² ∑_{i,j} ⟨xᵢ - xⱼ, v⟩^p`
   ([Separating/Program.lean](Separating/Program.lean));
3. a pivot `p` is read from the coins ([Separating/Coins.lean](Separating/Coins.lean)), and the
   points `j` with `q(x_p - xⱼ) ≤ τ = 1/(4 · 64^s)` form one side, for the separating polynomial
   `q(u) = Ẽ ⟨u, v⟩^(2s)`.

The analysis:

* **Feasibility** ([Separating/Feasible.lean](Separating/Feasible.lean)): on the good event, the
  point `v ∝ Σ⁻¹ (μₐ - μ_b)` for the two farthest components, in the whitened coordinates,
  satisfies the constraints, so the program is valid.
* **The pseudo-expectation** ([Separating/PseudoAnalysis.lean](Separating/PseudoAnalysis.lean)) is
  analyzed with its exact positivity on squares (only the constraints are satisfied
  approximately), each constraint on its own, the bound `|Ẽ f| ≤ ‖f‖₁ 258^t` from the ball, the
  weak triangle inequality `Ẽ (A + B)^(2s) ≤ 2^(2s-1) (Ẽ A^(2s) + Ẽ B^(2s))` and Jensen's
  inequality for powers of a sum of squares
  ([../Background/SumOfSquares/PseudoBounds.lean](../Background/SumOfSquares/PseudoBounds.lean)),
  with no sum-of-squares proofs from the constraints. The same-cluster terms of `F_{2t}`, compared
  with Gaussian moments, bound `Ẽ N^t` for the noise form `N(v) = vᵀ W Σ Wᵀ v`, Jensen bounds
  `Ẽ N^s`, and then `Ẽ F_{2s} ≥ 1/2` makes `q` large on the difference of the whitened means of
  two distinct clusters. The empirical moments enter as polynomials close to the Gaussian ones in
  coefficient norm ([Separating/MomentClose.lean](Separating/MomentClose.lean)), and
  [Separating/Setup.lean](Separating/Setup.lean) compares `Ĉ` with `Σ`.
* **Markov over pairs of sample points**: at most a `δ₁` fraction of the pairs within a cluster
  have `q(xᵢ - xⱼ) > τ`, and at most a `δ₁` fraction of the pairs between those two clusters have
  `q(xᵢ - xⱼ) < 16^(-s)/2`. These count pairs of the sample itself, so they are deterministic, and
  that `q` depends on the sample does not matter; the paper bounds `q` on fresh samples from the
  components instead.
* **The bipartition** ([Separating/Rounding.lean](Separating/Rounding.lean)) is combinatorial: by
  the weak triangle inequality for `q`, all pivots but `100 δ₁ n` give a separating bipartition,
  and the pivot, read from `⌈log₂ n⌉ + Kc` coins, avoids them with probability at least
  `1 - 100 δ₁ - n / 2^(⌈log₂ n⌉ + Kc)`. The probability `1 - δ` comes from the degree ratio
  `r = t / s = 2^41 R`, `R = max ⌈1/δ⌉ 100`, with `Kc = ⌈log₂ (4R)⌉`, and a separation growing
  with it: the analysis needs the separation `Cs log (1/wmin)` and the sample size
  `((d + 1)/wmin)^(Cs (log (1/wmin) + 1))` for some `Cs = O(R²)`, which `C ⌈1/δ⌉^C` covers for
  `C ≥ 2^106`.
* **The running time** `poly(|x|) · d^O(⌈1/δ⌉ log (1/wmin))`
  ([Separating/PolyTime.lean](Separating/PolyTime.lean),
  [Separating/RunTime.lean](Separating/RunTime.lean)): the solver is run with the budget
  `(d + 5)^(2t + 1) (|P| + 2)³` rather than its default `(|P| + 2)^(2t + 1)`, which would give
  `|x|^O(log (1/wmin))`. Its correctness is proved for every budget that suffices
  (`SoS.Correct.core_correct_of_budget` in
  [../Background/SumOfSquares/Algorithm/Correct.lean](../Background/SumOfSquares/Algorithm/Correct.lean)),
  and the powers `⟨u, v⟩^p` in the program are cut at the budget. One machine serves all `δ`: it
  computes `R` from `δ` and writes it and the budget in unary, and the list program takes `r` and
  `Kc` as part of its input, so the degree of its polynomial time bound does not depend on `δ`.
  For `δ ≤ 0` it outputs nothing.

[Separating/Main.lean](Separating/Main.lean) puts the parts together.

### Theorem 1.3: small radius

The algorithm ([SmallRadius/Alg.lean](SmallRadius/Alg.lean)) is a sum-of-squares clustering in the
style of Hopkins and Li, with the paper's estimate of the covariance scale in the moment
constraint. Its parameters ([SmallRadius/Params.lean](SmallRadius/Params.lean)) are two degrees,
powers of `2`: `s` of order `log (1/wmin)` (`logInv wmin + 8 ≤ s ≤ 2 (logInv wmin + 8)`) and a
multiple `t ≥ 4 ⌈R²⌉ + 4` of `s`.

1. A guard checks the sample size and that the leading principal minors of the second moment
   `Ĉ₀ = (1/n) ∑ⱼ Yⱼ Yⱼᵀ` are positive; if it fails (in particular for `k = 1`), all labels are `0`.
2. The points are whitened with rational arithmetic (`A Ĉ₀ Aᵀ` diagonal with entries in `[1, 4)`)
   and re-rounded to multiples of `2^(-p)`, so that the programs have coefficients of polynomial
   size ([SmallRadius/Whiten.lean](SmallRadius/Whiten.lean)). The scale estimate is the data's
   `2t`-th moment form `B̃(v) = (n t^t)⁻¹ ∑ⱼ ⟨zⱼ, v⟩^(2t)`.
3. `k` rounds of peeling. Round `r` solves, on the remaining points `zᵢ`, a program of degree
   `64 t` in Boolean variables `wᵢ`, a mean `μ` and auxiliary variables
   ([SmallRadius/Program.lean](SmallRadius/Program.lean)): maximize `∑ᵢ wᵢ` subject to
   `(∑ᵢ wᵢ ⟨zᵢ - μ, v⟩^(2s))^(t/s) ≤ K (∑ᵢ wᵢ)^(t/s) B̃(v)` for all `v`, `K = (256 s)^t`, where
   "for all `v`" is a set of coefficient equalities with a Gram factor among the variables. It
   picks a pivot `i₀` with probability proportional to `max (Ẽ wᵢ₀) 0`, from its own block of
   `n + 8` coins ([SmallRadius/Coins.lean](SmallRadius/Coins.lean)), and gives label `r` to the
   points `i` with `Ẽ wᵢ₀ ≤ 2 Ẽ[wᵢ₀ wᵢ]`, which it removes.

Maximizing `∑ᵢ wᵢ` in every round means that the cluster sizes need not be known. The analysis:

* **The standard frame** ([SmallRadius/Frame.lean](SmallRadius/Frame.lean),
  `BS23.SmallRadius.frame_of_model`): on the good event of every degree `r ≤ 2t`
  ([SmallRadius/GoodProb.lean](SmallRadius/GoodProb.lean)), the data are `zⱼ = G ζⱼ` for standard
  points `ζⱼ = m_ℓⱼ + gⱼ + eⱼ`: the means and the noise in the geometry of `Σ`, and errors
  `‖eⱼ‖² ≤ 4/n²` from both roundings, with `G` well conditioned. There
  ([SmallRadius/MomentSoS.lean](SmallRadius/MomentSoS.lean)), as sums of squares in `v`, each
  cluster has `∑_{j ∈ S_c} ⟨gⱼ + eⱼ, v⟩^(2s) ≤ |S_c| (8s)^s ‖v‖^(2s)`, and
  `16^(-t) (vᵀΣ'v)^t ≤ B̃(v) ≤ 32^t (vᵀΣ'v)^t` for the covariance `Σ' = G Gᵀ` of the components in
  the data frame; both bounds use `t ≥ 4R²` to control the means' contribution to `B̃`.
* **Two degrees.** The moment constraint compares the moments of degree `2s`, raised to the power
  `t/s`, with the scale `B̃` of degree `2t`. Identifiability uses only the moments of degree `2s`,
  so it works with the separation `C log (1/wmin)` even when `R² ≫ log (1/wmin)`, while `t` serves
  the covariance scale.
* **Feasibility** ([SmallRadius/Feasible.lean](SmallRadius/Feasible.lean)): the remaining part of
  a cluster that keeps at least half of its points is a feasible point. The moment inequality is a
  sum of squares by the bounds above, the spectral theorem turns it into a Gram factor, and
  interpolation on a grid bounds that factor by the ball of the program.
  [SmallRadius/RawAlg.lean](SmallRadius/RawAlg.lean) reads the program's polynomials in two blocks
  of variables, and [SmallRadius/MomentAxiom.lean](SmallRadius/MomentAxiom.lean) turns the
  coefficient equalities back into the moment inequality, for every `v` that is a polynomial of
  degree at most `1` in the program variables, as a sum of squares plus an explicit combination of
  the equalities.
* **Identifiability** ([SmallRadius/Ident.lean](SmallRadius/Ident.lean), with `IdentCore`,
  `IdentCross` and `IdentRules`). For a cluster `j`, let `p_j` be the weight on its remaining points
  and `D_j = ‖G⁻¹μ - m_j‖²`. A sum of squares plus an explicit combination of the equality
  constraints, with bounded norms, proves `p_j^(2t) D_j^(2t) ≤ c p_j^(2t-m) D_j^t`, `m = t/s`, from
  the moment constraint, the scale bound and the cluster bound, by power means and Hölder's
  inequality for Boolean variables. These certificates are built with
  [../Background/SumOfSquares/IdealSOS.lean](../Background/SumOfSquares/IdealSOS.lean), whose
  products do not double the degree, and
  [../Background/SumOfSquares/PowerSOS.lean](../Background/SumOfSquares/PowerSOS.lean). Roots are
  taken only of values of the pseudo-expectation, by log-convexity of its even moments
  ([../Background/SumOfSquares/Holder.lean](../Background/SumOfSquares/Holder.lean)): the cross
  mass is `Ẽ[p_j p_l] ≤ 2 n² (2^18 s / ‖m_j - m_l‖²)^s + 1` for `j ≠ l`.
* **Rounding** ([SmallRadius/RoundTable.lean](SmallRadius/RoundTable.lean),
  [SmallRadius/RoundStep.lean](SmallRadius/RoundStep.lean)) is arithmetic on the tables `Ẽ wᵢ` and
  `Ẽ[wᵢ wᵢ']`: near-optimality against the feasible cluster, `(∑ Ẽ wᵢ)² ≤ ∑ Ẽ[wᵢ wᵢ']`,
  Booleanity up to `2^(-n)` and the cross mass make the extracted set close to the remaining part
  of the pivot's cluster, for all pivots but a small weight.
* **Peeling** ([SmallRadius/Peel.lean](SmallRadius/Peel.lean)): after successful rounds, a cluster
  with the most remaining points has not been extracted and keeps at least half of its points, so
  each round succeeds with probability `1 - δ'/(2k)` over its block of coins, whatever the earlier
  blocks. A sequential union bound gives error `δ' = (wmin/k)^(c+2)` with probability
  `1 - δ'/2`.
* **The budget** ([SmallRadius/Budget.lean](SmallRadius/Budget.lean)): on the guard every program
  has length at most `n^6`, so the unary budget `radiusTime 2^14 x` cuts nothing and suffices for
  the solver; the running time is `|x|^O(R² + log (1/wmin))`
  ([SmallRadius/PolyTime.lean](SmallRadius/PolyTime.lean), with `PolyTimeProg`, and
  [SmallRadius/RunTime.lean](SmallRadius/RunTime.lean)).

[SmallRadius/Main.lean](SmallRadius/Main.lean) puts the parts together.

## Map of the files

| Files | Content |
| --- | --- |
| [Common/](Common/) | The good event and its probability (`Good`, `GoodProb`, `Glue`), its uniform form (`Uniform`, `UniformProof`), Gaussian moments, Hermite polynomials, the mismatch lemma, and the input of the algorithms. |
| [ColinearSoS/](ColinearSoS/) | Theorem 1.2: the programs and the algorithm (`Program`, `Alg`), the analysis (`Defs`, `Poly`, `Frame`, `Bernstein`, `Ratios`, `MomentPoly`, `PseudoAnalysis`, `Rounding`, `Correct`), the running time (`PolyTime`, `RunTime`) and `Main`. |
| [Colinear/](Colinear/) | The line clustering (`OneDim`, `OneDimCorrect`, `OneDimApply`) and the covariance comparison (`Moments`) used for Theorem 1.2, the basis used for the whitening of Theorems 1.1 and 1.2 (`Basis`), and the second proof of Theorem 1.2: the algorithm (`Alg`), its analysis (`HermiteScore`, `Population`, `Line`, `Gradient`, `Direction`, `Cast`, `Correct`), its running time (`PolyTime*`) and `Main`. |
| [Separating/](Separating/) | Theorem 1.1: whitening and the model quantities (`Whiten`, `Setup`, `MomentClose`), the program and the algorithm (`Program`, `Alg`), the analysis (`Feasible`, `PseudoAnalysis`, `Rounding`, `Coins`), the running time (`PolyTime`, `RunTime`) and `Main`. |
| [SmallRadius/](SmallRadius/) | Theorem 1.3: parameters and the standard frame (`Params`, `Frame`, `GoodProb`, `Whiten`, `MomentSoS`), the program (`Program`, `RawAlg`, `MomentAxiom`, `Feasible`), identifiability (`Ident*`), rounding and peeling (`RoundTable`, `RoundStep`, `Coins`, `Alg`, `Peel`), the running time (`Budget`, `PolyTime*`, `RunTime`) and `Main`. |
| [Solution.lean](Solution.lean) | The three theorems from the `Main` files. |

*Formalized by [Claude Code](https://claude.com/claude-code).*
