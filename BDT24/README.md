# BDT24: Computational-statistical gaps for improper learning in sparse linear regression

The results are the reduction of [BDT24], Theorem 3.1, and the low-degree and statistical-query
lower bounds for negative sparse PCA, Theorems B.4 and C.6. They are stated in
[Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them.

* **Theorem 3.1.** A polynomial-time algorithm that achieves prediction error `0.01` for sparse
  linear regression with Gaussian design and noise variance `1`, with probability `1 - δ`, gives
  an algorithm that solves negative sparse PCA with `θ = (k+1)/(k+2)` from the same number of
  samples, with probability `1 - √(2δ) - exp(-Ω(n))`. Both algorithms are Turing machines that
  read their samples to a given number of bits. The PCA algorithm reads polynomially many more
  bits than it gives the regression algorithm, and runs in time `O(1 + δ^(-1/2))` times a
  polynomial in its input. The regression algorithm is only asked to succeed on instances with
  `I/(k+2) ⪯ Σ ⪯ I` and `‖x*‖² ≤ k`, which contain those of the reduction.
* **Theorem B.4.** For `δ ≤ 0.1` and `n = o(min(d, k^(2-δ)))`, polynomials of degree `k^δ` in
  the coordinates of `n` points have advantage `o(1)` in telling planted points of negative sparse
  PCA from null ones, for every `θ ∈ (0, 1)`. The paper bounds the normalized ratio by
  `1 + o(1)`; its proof gives `o(1)`.
* **Theorem C.6.** For `δ ≤ 0.1` and `n = o(min(d/k^δ, k^(2-2δ)))`, the statistical dimension of
  negative sparse PCA at VSTAT parameter `n` is at least `2^(k^δ)`, uniformly in
  `θ ≤ (k+1)/(k+2)`. This contains every fixed `θ < 1` and the `θ` of the reduction.
  Statistical-query algorithms themselves are not formalized.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v2).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 3.1 | `negSPCA_of_sparse_regression` | There are constants `c > 0` and `C` such that for every regression algorithm `A` running in time `(|x| + 2)^e` there are a PCA algorithm `B` running in time `(⌊√⌈1/δ⌉⌋ + 1)(|x| + 2)^(e')` and an exponent `E` such that, for every rational `δ > 0` and all `n`, `k ≤ d` and `p`: if `A` achieves prediction error `0.01` with probability `1 - δ` on `n` samples in dimension `2d` with sparsity `k`, read to `p` bits, on every bounded instance, then `B`, given `δ` and `p`, tells `n` points of `N(0, I_{d+1})` from `n` points of `N(0, I - θ x xᵀ)` (for a random spike `x`), read to any `q ≥ (n + d + p + 2)^E` bits, with probability `1 - √(2δ) - C exp(-c n)` on each side. |
| Theorem B.4 | `lowDegree_negSPCA` | For every `δ ∈ (0, 1/10]` and `ε > 0` there are `η > 0` and `k₀` such that for every `θ ∈ (0, 1)` and all `n` and `k₀ ≤ k ≤ d` with `n ≤ η min(d, k^(2-δ))`, every polynomial `f` of total degree at most `k^δ` in the `n(d+1)` coordinates of `n` points has `E_P f - E_Q f ≤ ε √(Var_Q f)`, for the planted law `P` (one random spike shared by the `n` points) and the null law `Q`. |
| Theorem C.6 | `sq_negSPCA` | For every `δ ∈ (0, 1/10]` there are `η > 0` and `k₀` such that for all `n ≥ 1` and `k₀ ≤ k ≤ d` with `n ≤ η min(d/k^δ, k^(2-2δ))` and every `θ ∈ (0, (k+1)/(k+2)]`, the statistical dimension at VSTAT parameter `n` is at least `q = ⌈2^(k^δ)⌉`: on every set of pairs `(u, v)` of sign patterns of probability at least `1/q²`, the average of `|⟨D̄_u, D̄_v⟩ - 1|` is at most `1/n`. |

For Theorem 3.1:

* **Inputs.** Each algorithm reads every number `t` of its sample as the integer `⌊2^p t⌋` and is
  given `p` in unary; nothing quantifies over roundings. An algorithm on quantized samples can be
  run on the real ones.
* **The regression problem** (Model 1.1) keeps the paper's prediction loss
  `(1/n) ‖X x̂ - X x*‖² ≤ 0.01` on the real design. Its instances are those with
  `I/(k+2) ⪯ Σ ⪯ I` and a `k`-sparse `x*` with `‖x*‖² ≤ k`; asking the regression algorithm to
  succeed on fewer instances only strengthens the theorem, and these contain the reduction's
  instances. The bounds fix the scale, so that a fixed number of bits means the same precision on
  every instance.
* **Negative sparse PCA** (Model 1.3): the spike has first coordinate `-1/√(k+1)` and the other
  coordinates a uniformly random vector in `{±1/√(k+1), 0}^d` with exactly `k` nonzero entries.
  The PCA points are in `ℝ^{d+1}`, so the regression algorithm is used in dimension `2d`.
* **Two precisions.** The PCA algorithm needs more bits than it gives the regression algorithm, a
  number that depends on the regression algorithm's running time. The paper does not bound the
  precision.
* **Pointwise in the parameters.** The hypothesis is only used at the sizes, the precision and the
  failure probability of the conclusion, so the theorem applies to algorithms that work only in
  some range of parameters, as in Theorem 1.5, and to `δ` that depend on `n`, `d` and `k`.
* **Running times** are in the length `|x|` of the encoded input. The factor
  `⌊√⌈1/δ⌉⌋ + 1` is the `O(1/√δ)` repetitions of Lemma 4.1; for this, the PCA algorithm is given
  `δ`. It is polynomial in `|x|` when `1/δ` is polynomially bounded.

For Theorems B.4 and C.6:

* **The advantage** (`AdvantageAtMost`, as in BHJK25) is `E_P f - E_Q f ≤ ε √(Var_Q f)` for every
  polynomial `f` of degree at most `k^δ`; for `E_Q f = 0` it bounds the paper's ratio
  `E_P f / √(E_Q f²)` by `ε`.
* **`o(·)`** is written with quantifiers: the bounds hold once `n / min(d, k^(2-δ))` (or
  `n / min(d/k^δ, k^(2-2δ))`) is at most `η` and `k ≥ k₀`.
* **The statistical dimension** (Definition C.2, `SDAAtLeast`) is written with the relative
  densities `D̄_v = dP_v/dQ` of one planted point (Mathlib's Radon–Nikodym derivative) and their
  correlations `⟨D̄_u, D̄_v⟩ = E_Q [D̄_u D̄_v]`. The prior is uniform on sign patterns, so an event
  is a set of pairs and a conditional expectation an average. `n` is the parameter of the VSTAT
  oracle; the oracle and the theorem that statistical-query algorithms need about `SDA(S, n)`
  queries (Theorem C.3) are not formalized.
* **`θ` in Theorem C.6** ranges over `(0, (k+1)/(k+2)]` with one `η` and one `k₀`. The paper does
  not say whether `θ` may vary with `n`, `d` and `k`. This range contains every fixed `θ < 1` once
  `k` is large, where it is the paper's statement, and the `θ` of the reduction, which varies with
  `k`. Some bound in terms of `k` is needed: the correlation `(1 - θ²)^(-1/2)` of a spike with
  itself is unbounded as `θ → 1`, so for `θ` close enough to `1` the statistical dimension is not
  even `1`.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

The first six subsections are Theorem 3.1; the last two are Theorems B.4 and C.6.

### The algorithm

The PCA algorithm ([Alg/Defs.lean](Alg/Defs.lean)) is the paper's reduction, from negative sparse
PCA to its paired version (Lemma 4.1) and from the paired version to regression (the proof of
Theorem 3.1). It repeats a round `M = min(⌊√⌊1/(2δ)⌋⌋, 2^⌊n / 2^24⌋)` times and says "planted"
when every round passes. Lemma 4.1 takes `M ≈ 1/√(2δ)`; the cap `2^⌊n / 2^24⌋` keeps the
exponentially small errors of the rounds, added over all of them, within `exp(-Ω(n))` when `δ` is
tiny.

In a round, the algorithm draws its own null sample from coins: each coordinate is the cell
`⌊2^B Φ(g)⌋` of `B` coins, turned into a Gaussian by bisection on the series of `Φ` and quantized
to the input's precision ([Alg/Numerics.lean](Alg/Numerics.lean), copied from BGHKLMM26). It
runs the paired test on (input, own sample) and on (own sample, input), each with its own coins,
and the round passes when the input is said to be planted in the first and the own sample not in
the second.

The paired test builds the regression instance whose design is coordinates `2, …, d+1` of both
points and whose response is `√(2/3)` times the sum of their first coordinates. The factor
rescales the paper's noise variance `3/2` to `1`. The algorithm coarsens the design to `p` bits
and computes the response's `p`-bit value exactly with integer square roots. It runs the
regression algorithm, predicts with the `q`-bit design, and compares the residuals against
`√(2/3)` times the first coordinates of the two samples.

### Running time

The pieces are polynomial-time ([Alg/PolyTime.lean](Alg/PolyTime.lean) and
[Alg/PolyTime/](Alg/PolyTime)), with the regression algorithm as a black box. The number of
rounds can be exponential in the input, so the algorithm is written as a fold over its coin bits
that fills a block, runs the round, and shrinks to a one-bit state after the last round
([Alg/RunTime.lean](Alg/RunTime.lean)). With complexitylib's streaming fold, the time is the sum
of the costs of the steps: polynomial in `|x|` for each of the `M` blocks' coins and constant for
the remaining ones.

### Fact 2.1

A planted point `z` and a null point `g` give a regression point whose law is that of sparse linear
regression with design covariance `diag(I - v vᵀ/(k+2), I)` and secret `(v/√6, 0)`, where `v` is
the sign pattern of the spike ([Prob/Gauss.lean](Prob/Gauss.lean)). The two Gaussian laws are
compared through all their one-dimensional projections (Cramér–Wold), whose variances agree. The
same file gives the bounded instance and the laws of the statistics of the test.

### The planted case

On planted input the algorithm fails only if a round fails, so with probability at most `M`
times the probability that one round fails (`1 - p^M ≤ M (1 - p)`)
([Analysis/Planted.lean](Analysis/Planted.lean)). A round fails only if one of its tests does.
On a good pair of samples ([Analysis/Good.lean](Analysis/Good.lean)), three things hold:

* the own sample is the quantization of a null sample ([Analysis/Exact.lean](Analysis/Exact.lean));
* the regression input is exactly the `p`-bit input of the regression point, which needs the `q`-bit
  values and a response away from multiples of `2^(-p)`;
* the regression algorithm's output, being no longer than its running time, has coordinates small
  enough for the `q`-bit design.

Then the test is right whenever the regression algorithm predicts well
([Analysis/Test.lean](Analysis/Test.lean)): with the residual of the planted sample at most
`0.51 n` and the other difference at least `0.98 n` in squared norm, the predictions are within
`0.69 √n` of the planted sample's coordinates and at least `0.70 √n` from the null sample's.
Through Fact 2.1, the regression algorithm predicts well with probability at least `1 - δ`, so a
round fails with probability at most `2 (δ + P(not good))`.

### The null case

On null input the own sample has, on a good own sample, exactly the law of the input
([Analysis/Null.lean](Analysis/Null.lean)). The probability of saying "planted" is then at most
`1/(M+1)` by the exchangeability argument of Lemma 4.1 ([Prob/Exch.lean](Prob/Exch.lean)), plus
`M` times the probability of a bad own sample. The formal argument gives each ordered pair of
`M + 1` independent samples its own coins. The events that a sample beats all others are then
pairwise disjoint, since two of them disagree on the test of their pair, and they are equally
likely by symmetry. This replaces the paper's conditioning on the regression algorithm's
randomness.

### Probabilities

The squared norms of the statistics concentrate by Chernoff bounds with the moment generating
function of `X²` ([Prob/Tail.lean](Prob/Tail.lean)). The coordinates have Gaussian tails, and a
Gaussian lands near a multiple of `2^(-q)` with small probability, which covers the own samples
and the responses. The coin probabilities of the algorithm are turned into integrals over
Gaussians through the cells of `Φ` ([Alg/Coins.lean](Alg/Coins.lean)). The error bound
`√(2δ) + C exp(-c n)` with `c = log 2 / 2^24` is assembled in [Main.lean](Main.lean).

### Theorem B.4

The proof follows the paper ([LowDeg/](LowDeg)). The polynomials of degree at most `D` are the
combinations of the multivariate Hermite polynomials `H_α = ∏ᵢ He_{αᵢ}` with `|α| ≤ D`, which are
orthogonal under the null law with `E H_α² = α!`. So the advantage is at most the square root of
`∑_{0 < |α| ≤ D} (E_P H_α)² / α!` ([LowDeg/Hermite.lean](LowDeg/Hermite.lean), with the
one-dimensional orthogonality of TauCeti). Given the spike `x`, a planted point has
`E H_a = (-θ)^m (2m - 1)!! x^a` when `|a| = 2m` and `0` when `|a|` is odd
([LowDeg/Spike.lean](LowDeg/Spike.lean), [LowDeg/Spike/](LowDeg/Spike)), by induction on `|a|`
with Gaussian integration by parts, `E z_j f(z) = ∑_l Σ_jl E ∂_l f(z)` for `z ~ N(0, Σ)`, and
`He_{m+1}(t) = t He_m(t) - He_m'(t)`. The points are independent given the spike, so by the
multinomial theorem the sum is at most `∑_{L=1}^{D/2} (n + L)^L / L! · E ⟨x_u, x_v⟩^(2L)` over two
independent spikes ([LowDeg/Norm.lean](LowDeg/Norm.lean)).

Lemma B.5 bounds these moments by `(C L)^L (1/d + L/k²)^L` with `C = 8e²`
([LowDeg/Overlap.lean](LowDeg/Overlap.lean)). As in the paper, `(k+1) ⟨x_u, x_v⟩ - 1` is, given
the supports, a sum `R` of independent signs over their intersection, and the intersection is
dominated by a binomial `Bin(k, k/d)`: a set `T` of coordinates lies in a random support with
probability at most `(k/d)^|T|`. The moments of `R` are bounded through its moment generating
function, `E e^(tR) ≤ exp((cosh t - 1) k²/d)`, instead of by counting pairings. With
`D = ⌊k^δ⌋`, each term of the series is at most `r^L` for `r = e C (n + D)(1/d + D/k²)`, and `r`
is small when `n ≤ η min(d, k^(2-δ))` and `k` is large ([LowDeg/Main.lean](LowDeg/Main.lean)).

### Theorem C.6

The paper derives Theorem C.6 from the low-degree bound, through the almost-equivalence of
statistical-query and low-degree bounds of Brennan et al. and a bound on the high-degree part of
the likelihood ratio (Lemma C.7). At the core of the almost-equivalence is Hölder's inequality: if
`E |⟨D̄_u, D̄_v⟩ - 1|^p ≤ M` for two independent spikes, then on every event of probability at
least `1/q²` the average of `|⟨D̄_u, D̄_v⟩ - 1|` is at most `(q² M)^(1/p)`
([SQ/Holder.lean](SQ/Holder.lean)). The formal proof applies this with `p = ⌈k^δ⌉`, and bounds the
moments through the closed form of the correlations and Lemma B.5 rather than through the
low-degree norm and the high-degree part:

* a planted point has density `(1 - θ)^(-1/2) exp(-θ ⟨x, z⟩² / (2(1 - θ)))` with respect to
  `N(0, I)` ([SQ/Density.lean](SQ/Density.lean)). A standard Gaussian is `s x + w` with
  `s ~ N(0, 1)` and `w ~ N(0, I - x xᵀ)` independent, and a planted point is `√(1 - θ) s x + w`
  (Cramér–Wold);
* so `⟨D̄_u, D̄_v⟩ = E_{P_u} D̄_v = (1 - θ² ⟨x_u, x_v⟩²)^(-1/2)`, a one-dimensional Gaussian
  integral ([SQ/Corr.lean](SQ/Corr.lean));
* with `τ = ⟨x_u, x_v⟩`, `0 ≤ ⟨D̄_u, D̄_v⟩ - 1 ≤ 2τ² + (k + 2)(2τ)^10`, since `θ ≤ (k+1)/(k+2)`
  keeps `1 - θ² τ² ≥ 1/(k+2)`. Lemma B.5 at `L = p` and `L = 5p` bounds the `p`-th moment by
  `B^p`, and with `q = ⌈2^(k^δ)⌉ ≤ 2^(p+1)` the average is at most `16 B ≤ 1/n`
  ([SQ/Main.lean](SQ/Main.lean), [SQ/Main/Bounds.lean](SQ/Main/Bounds.lean)).

## Map of the files

| Files | Content |
| --- | --- |
| [Model.lean](Model.lean), [Challenge.lean](Challenge.lean) | the models, quantized inputs, machines, and the statement |
| [Alg/Defs.lean](Alg/Defs.lean) | the algorithm: paired test, own samples, rounds, the fold over the coins |
| [Alg/Numerics.lean](Alg/Numerics.lean) | `π`, `Φ` and Gaussians from cells, with error bounds (from BGHKLMM26) |
| [Alg/PolyTime.lean](Alg/PolyTime.lean), [Alg/PolyTime/](Alg/PolyTime) | the pieces in polynomial time |
| [Alg/RunTime.lean](Alg/RunTime.lean) | the running time of the fold |
| [Alg/Coins.lean](Alg/Coins.lean), [Alg/Coins/](Alg/Coins) | rounds as independent blocks of coins; own samples from Gaussians |
| [Prob/Gauss.lean](Prob/Gauss.lean), [Prob/Gauss/](Prob/Gauss) | Fact 2.1, the bounded instances, the laws of the statistics |
| [Prob/Tail.lean](Prob/Tail.lean), [Prob/Tail/](Prob/Tail) | squared-norm concentration, tails, anti-concentration near a grid |
| [Prob/Exch.lean](Prob/Exch.lean) | the exchangeability argument of Lemma 4.1 |
| [Analysis/Exact.lean](Analysis/Exact.lean) | what the algorithm computes on quantized samples |
| [Analysis/Test.lean](Analysis/Test.lean) | the paired test is right on good samples |
| [Analysis/Good.lean](Analysis/Good.lean) | the good events and their probabilities |
| [Analysis/Planted.lean](Analysis/Planted.lean), [Analysis/Null.lean](Analysis/Null.lean) | the planted and the null case |
| [Main.lean](Main.lean) | the error bound of Theorem 3.1 |
| [LowDeg/Defs.lean](LowDeg/Defs.lean) | multivariate Hermite polynomials, the planted Hermite coefficients, the overlap moments |
| [LowDeg/Hermite.lean](LowDeg/Hermite.lean) | the Hermite basis and the advantage bound |
| [LowDeg/Spike.lean](LowDeg/Spike.lean), [LowDeg/Spike/](LowDeg/Spike) | the laws of the samples and the Hermite coefficients of a planted point |
| [LowDeg/Norm.lean](LowDeg/Norm.lean) | the low-degree norm through the overlap moments |
| [LowDeg/Overlap.lean](LowDeg/Overlap.lean) | Lemma B.5 |
| [LowDeg/Main.lean](LowDeg/Main.lean) | Theorem B.4 |
| [SQ/Density.lean](SQ/Density.lean), [SQ/Corr.lean](SQ/Corr.lean) | the density of a planted point and the correlations |
| [SQ/Holder.lean](SQ/Holder.lean) | the statistical dimension from the moments of the correlations |
| [SQ/Main.lean](SQ/Main.lean), [SQ/Main/](SQ/Main) | Theorem C.6 |
| [Solution.lean](Solution.lean) | the three theorems |

*Formalized by [Claude Code](https://claude.com/claude-code).*
