module

public import BDT24.Model

/-!
# Main results: statements

Three results of [BDT24], with proofs `sorry`: a finite-precision variant of the reduction,
Theorem 3.1, in which both algorithms read their sample points to a given number of bits instead
of the real points; the low-degree lower bound for negative sparse PCA, Theorem B.4; and its
statistical-query lower bound, Theorem C.6, a bound on the statistical dimension. Numbers are those
of the arXiv version (v2). The paper's hardness assumption (Assumption 1.4), its main result for
learners running in time `d^(k^o(1))` (Theorem 1.5) and statistical-query algorithms themselves
are not formalized.

What a reader has to trust is this file and what it imports: the definitions in
`BDT24/Model.lean` (the two models, quantized samples, randomized algorithms, inputs and outputs,
low-degree polynomials, the statistical dimension), the encodings in `Background/Encoding.lean`,
CSLib's multitape Turing machines, and Mathlib.

## Theorem 3.1

[BDT24, Theorem 3.1]: let `d, k, n ∈ ℕ` with `d ≥ k`. Assume there exists an efficient algorithm
that, given `n` samples from the sparse linear regression model with noise variance `σ² = 1`,
achieves prediction error `(1/n) ‖A x̂ - A x*‖² ≤ 0.01` with probability `1 - δ`. Then there exists
an efficient algorithm that solves `NegSPCA_θ` for `θ = (k+1)/(k+2)` with probability
`1 - √(2δ) - exp(-Ω(n))`.

Formally (`BDT24.negSPCA_of_sparse_regression`): there are constants `c > 0` and `C` such that for
every regression algorithm `A` running in polynomial time there are a PCA algorithm `B` running in
time `O(1 + δ^(-1/2))` times a polynomial in its input length, and an exponent `E`, such that, for
every rational `δ > 0` and all `n`, `k ≤ d` and `p`, if `A` solves sparse linear regression with
`n` samples in dimension `2d` with sparsity `k`, read to `p` bits, with failure probability `δ`
(`BDT24.SolvesSLR`), then `B`, given `δ` and `p`, solves `NegSPCA_θ` with `n` samples in dimension
`d + 1`, read to any `q ≥ (n + d + p + 2)^E` bits, with probability `1 - √(2δ) - C exp(-c n)`
(`BDT24.SolvesNegSPCA`).

## Conventions of Theorem 3.1

* **The models.** Sparse linear regression [BDT24, Model 1.1]: `n` independent points `(a, y)` with
  `a ~ N(0, Σ)` in `ℝ^D`, `y = ⟨a, x*⟩ + w` and `w ~ N(0, 1)` independent of `a`
  (`BDT24.slrLaw`); the algorithm is given `k`. Negative sparse PCA [BDT24, Model 1.3]: `n`
  independent points from `N(0, I_{d+1})` (null) or, for one spike `x` drawn first, from
  `N(0, I_{d+1} - θ x xᵀ)` (planted), where `x₁ = -1/√(k+1)` and the other coordinates are a
  uniformly random vector in `{±1/√(k+1), 0}^d` with exactly `k` nonzero entries
  (`BDT24.spikeSigns`, `BDT24.spikeVector`; exactly `k`, since `x` is a unit vector); the algorithm
  is given `k`, so it knows `θ`.
* **The regression instances** are those with `I/(k+2) ⪯ Σ ⪯ I` and a `k`-sparse `x*` with
  `‖x*‖² ≤ k` (`BDT24.IsBoundedInstance`), not every positive semidefinite `Σ` and every `k`-sparse
  `x*` as in the paper's model. Asking `A` to succeed on fewer instances only strengthens the
  theorem, and these contain every instance the reduction builds: after the response is scaled to
  noise variance `1`, the design covariance has spectrum in `[2/(k+2), 1]` and the secret has `k`
  entries `±1/√6`. The bounds fix the scale, so that `p` bits mean the same precision on every
  instance; without them, scaling the design down and `x*` up leaves the model unchanged but makes
  any fixed precision too coarse.
* **The input: quantized samples.** The paper's algorithms read real numbers. Here each algorithm
  reads every number `t` of its sample to a given number of bits after the binary point, as the
  integer `⌊2^p t⌋` (`BDT24.quantize`), and is given that number of bits in unary, so that its
  input is at least as long as one number at that precision. There is no quantification over
  roundings: each side reads one fixed quantization of its real sample. `A` reads its sample to `p`
  bits (`BDT24.slrInput`), `B` reads its sample to `q` bits (`BDT24.spcaInput`). An algorithm that
  reads quantized samples can also be run on the real samples, so the conclusion bears on the
  hardness of `NegSPCA_θ` [BDT24, Assumption 1.4] as the paper states it, with the precisions and
  `δ` chosen as described under **Efficient** below.
* **The prediction error is the paper's**, `(1/n) ‖X x̂ - X x*‖² ≤ 0.01` on the real design `X`
  (`BDT24.PredictsWell`). The algorithm need not be able to evaluate it, just as it does not know
  `x*`.
* **The two precisions.** The theorem holds at every `p`, and asks of `B`'s input
  `q ≥ (n + d + p + 2)^E` bits, where the exponent `E` depends on `A` (through its running time).
  The reduction needs more bits than it gives `A`, for two reasons.
  * `B` decides by comparing `X x̂` with two columns of its sample, and only knows its design to
    `q` bits. Since `A` runs in time `(|x| + 2)^e`, its output has length at most a polynomial in
    its input, so every coordinate of `x̂` has absolute value at most `2^H` for some `H` polynomial
    in `n`, `d` and `p` (except on an exponentially unlikely sample), and the `q`-bit design gives
    `X x̂` to within `O(d 2^(H - q))` per point. This works because `A` sees only `p` bits, whatever
    `q` is: given all `q` bits, its output could outgrow them.
  * `B` must give `A` exactly the `p`-bit input of a genuine regression sample. The design
    coordinates are coordinates of `B`'s points, and their `p`-bit values follow from the `q`-bit
    ones. The response is `√(2/3)` times the sum of two coordinates, one from a point of `B`'s
    input and one from a point that `B` draws; `B` knows it to within `O(2^(-q))`, so its `p`-bit
    value is wrong only near a multiple of `2^(-p)`, which over the sample has probability
    `O(n 2^(p - q))`. So `q - p` must be of order `n`.

  The paper does not bound the precision; any polynomial one is efficient.
* **Dimensions.** The PCA points are in `ℝ^{d+1}`. The reduction pairs two of them and deletes the
  first coordinate of each, so `A` is used in dimension `2d`, at the same `n` and `k`.
* **A reduction, pointwise in the parameters.** The hypothesis is asked only at the sizes
  `(n, 2d, k)`, the precision `p` and the failure probability `δ` of the conclusion. So the
  theorem applies to algorithms that work only in some range of parameters, as in [BDT24, Theorem
  1.5], and to `δ` that depend on `n`, `d` and `k`.
* **Efficient** means running time polynomial in the length `|x|` of the encoded input, which
  counts every bit. The precision is written once, in unary, and each number in binary, so `|x|` is
  at least the precision and at least the number of numbers, not their product (a number close to
  `0` takes few bits). `A` runs in time `(|x| + 2)^e` for some `e` (`BDT24.slrTime`).
  * `B` runs in time `O(1 + δ^(-1/2)) (|x| + 2)^(e')` (`BDT24.spcaTime`), where `e'` depends on `A`
    but not on `δ`: this is the time `O((T_sample + T_dist)/√δ)` of the reduction from `NegSPCA_θ`
    to its paired version [BDT24, Lemma 4.1], which repeats the paired test about `1/√(2δ)` times.
    For that, `B` is given `δ` (`BDT24.SPCAInput`); `A` is not. This is polynomial in `|x|` when
    `1/δ` is polynomially bounded, but not for every `δ` written in binary: `δ = 2^(-2L)` takes
    about `2L` bits and allows time `2^L`. The factor is needed for error `√(2δ)`.
  * The input contains `q` in unary and `δ` in binary, so polynomial in `|x|` is polynomial in `n`,
    `d` and `k` only when these are: with `p` and `q = (n + d + p + 2)^E` polynomial in `n`, `d`
    and `k`, `1/δ` polynomially bounded and `δ` of polynomial bit length, `B` runs in time
    polynomial in `n`, `d` and `k` except on exponentially unlikely samples (with huge
    coordinates). The bit length is a separate condition: `δ = (2^N + 1)/2^(N + 4)` has
    `1/δ < 16` but takes about `2N` bits.
  * `B` draws its own null points in the format of its input, `q` bits. It cannot draw them exactly
    from the law of a quantized Gaussian, which takes infinitely many values, with finitely many
    coins; it draws them from an approximation. So the exchangeability argument of Lemma 4.1 holds
    for the input and `B`'s own points only up to the approximation error, which must be
    exponentially small in `n`; and the number of repetitions must stay at most exponential in `n`,
    so that these errors, added over the repetitions, stay `exp(-Ω(n))` even for tiny `δ`.
  * The time bounds are explicit functions of the input, not any functions bounded by them: an
    algorithm is given exactly `T x` coins and may read them all, so the length of its coin string
    tells it `T x`, which for an arbitrary `T` could be advice that no machine computes.
* **`exp(-Ω(n))`** is `C exp(-c n)` for constants `c > 0` and `C` that depend on nothing.
* **Correctness** of `B` is asked in both cases (`BDT24.SolvesNegSPCA`): it outputs `false` on the
  null law and `true` on the planted law, each with probability at least `1 - √(2δ) - C exp(-c n)`
  over the sample, the spike and the coins. `A`'s guarantee is over the sample and its coins.
* **Uniformity.** The constants `c` and `C` serve all algorithms; one `B`, one exponent `e'` and
  one exponent `E` serve all `δ`, `n`, `d`, `k`, `p` and `q`. `B` is given `δ`, `p`, `k`, `q` and
  the quantized points, but not the spike.

## Theorem B.4

[BDT24, Theorem B.4]: fix `δ ∈ (0, 0.1]` and suppose `n = o(min(d, k^(2-δ)))`. For the planted
law `P_n` and the null law `Q_n` of `n` points of `NegSPCA_θ`, every polynomial `f(z₁, …, z_n)` of
degree `k^δ` with `E_{Q_n} f = 0` has `E_{P_n} f / √(E_{Q_n} f²) ≤ 1 + o(1)`.

Formally (`BDT24.lowDegree_negSPCA`): for every `δ ∈ (0, 1/10]` and `ε > 0` there are `η > 0` and
`k₀` such that for every `θ ∈ (0, 1)` and all `n` and `k₀ ≤ k ≤ d` with
`n ≤ η min(d, k^(2-δ))`, the planted law has degree-`k^δ` advantage at most `ε` over the null law.

* **The advantage** (`BDT24.AdvantageAtMost`): every polynomial `f` of total degree at most `k^δ`
  in the `n (d + 1)` coordinates of the points (`BDT24.sampleCoords`) has
  `E_P f - E_Q f ≤ ε √(Var_Q f)`; for `E_Q f = 0` this bounds the paper's ratio by `ε`. So the
  ratio is asked to be `o(1)` rather than `1 + o(1)`, which is what the paper's proof gives: it
  bounds the squared norm of the degree-`k^δ` likelihood ratio `L^{≤D}` by `1 + o(1)`, and for
  `E_Q f = 0`, `E_P f = ⟨L^{≤D} - 1, f⟩ ≤ √(‖L^{≤D}‖² - 1) ‖f‖`. The paper writes the
  polynomials on `ℝ^{n×d}`; the points are in `ℝ^{d+1}`.
* **`o(·)`** is written with quantifiers: for every `ε` the advantage is at most `ε` once
  `n / min(d, k^(2-δ)) ≤ η` and `k ≥ k₀`. The paper's asymptotics are as `n → ∞`, and then
  `n = o(k^(2-δ))` makes `k → ∞`; so this is the paper's statement along every such sequence of
  parameters.
* **The laws** (`BDT24.plantedSample`, `BDT24.nullSample`): the planted law draws one spike, with
  its sign pattern uniform, shared by all `n` points, as in [BDT24, Model 1.3].
* **`θ`.** One `η` and one `k₀` serve every `θ ∈ (0, 1)`.
* The low-degree bound is evidence for the hardness of `NegSPCA_θ` through the low-degree
  conjecture [BDT24, Conjecture B.3], which is not formalized.

## Theorem C.6

[BDT24, Theorem C.6]: consider `NegSPCA_θ` and let `0 < δ ≤ 0.1`. Then for
`n = o(min(d/k^δ, k^(2-2δ)))`, the statistical dimension satisfies `SDA(S, n) ≥ 2^(k^δ)`, where
`S` is the family of planted laws `N(0, I - θ x xᵀ)` of one point, with the prior of the spike.

Formally (`BDT24.sq_negSPCA`): for every `δ ∈ (0, 1/10]` there are `η > 0` and `k₀` such that for
all `n ≥ 1` and `k₀ ≤ k ≤ d` with `n ≤ η min(d/k^δ, k^(2-2δ))`, and every
`θ ∈ (0, (k+1)/(k+2)]`, the statistical dimension at VSTAT parameter `n` is at least
`⌈2^(k^δ)⌉`.

* **The statistical dimension** [BDT24, Definition C.2] (`BDT24.SDAAtLeast`) is written with the
  relative densities `D̄_v = dP_v/dQ` of one planted point (`BDT24.relDensity`, Mathlib's
  Radon–Nikodym derivative) and their correlations `⟨D̄_u, D̄_v⟩ = E_Q [D̄_u D̄_v]`
  (`BDT24.pairCorr`). The prior is uniform on a finite set of sign patterns, so an event is a set
  of pairs of sign patterns and a conditional expectation an average. For `q ≥ 1` the defining
  condition only gets harder as `q` grows, so "the statistical dimension is at least `q`" is the
  condition at `q`. For `0 < θ < 1` the relative densities are bounded, so the correlations are
  finite, `(1 - θ² ⟨x_u, x_v⟩²)^(-1/2)`.
* **`n`** is the parameter of the VSTAT oracle [BDT24, Definition C.1], not a number of samples.
  The oracle, statistical-query algorithms, and the theorem that they need about `SDA(S, n)`
  queries to `VSTAT(n/3)` [BDT24, Theorem C.3, from Feldman et al.] are not formalized;
  Theorem C.6 is the bound on the statistical dimension.
* **`o(·)`** is written with quantifiers, as in Theorem B.4: the bound holds once
  `n / min(d/k^δ, k^(2-2δ)) ≤ η` and `k ≥ k₀`.
* **`θ`, uniformly.** The paper takes `θ ∈ (0, 1)` and calls `δ` an absolute constant, but does
  not say whether `θ` may vary with `n`, `d` and `k`. Here one `η` and one `k₀` serve every
  `θ ∈ (0, (k+1)/(k+2)]`. For each fixed `θ < 1` this is the paper's asymptotic statement, since
  `θ ≤ (k+1)/(k+2)` once `k` is large. It also covers the `θ = (k+1)/(k+2)` of the reduction
  (Theorem 3.1), which varies with `k`. It does not cover `θ` tending to `1` faster, and no
  statement can: for fixed `n`, `d` and `k` the correlation of a spike with itself,
  `(1 - θ²)^(-1/2)`, is unbounded as `θ → 1`, and the event of all pairs already has average at
  least `((1 - θ²)^(-1/2) - 1)/N`, with `N` the number of sign patterns, so the statistical
  dimension is not even `1` once this exceeds `1/n`.

Reference: [BDT24] R.-D. Buhai, J. Ding, S. Tiegel, *Computational-statistical gaps for improper
learning in sparse linear regression*, COLT 2024, arXiv:2402.14103.
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
  sorry


/-- **Theorem B.4** of [BDT24]: for `δ ∈ (0, 0.1]` and `n = o(min(d, k^(2-δ)))`, polynomials of
degree `k^δ` in the coordinates of `n` points have advantage `o(1)` in telling the planted law
of negative sparse PCA from the null law. -/
theorem lowDegree_negSPCA :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ k₀ : ℕ,
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ n d k : ℕ, k₀ ≤ k → k ≤ d →
        (n : ℝ) ≤ η * min (d : ℝ) ((k : ℝ) ^ (2 - δ)) →
        AdvantageAtMost sampleCoords ((k : ℝ) ^ δ) (plantedSample n d k θ) (nullSample n d) ε :=
  sorry

/-- **Theorem C.6** of [BDT24]: for `δ ∈ (0, 0.1]` and `n = o(min(d/k^δ, k^(2-2δ)))`, the
statistical dimension of negative sparse PCA at VSTAT parameter `n` is at least `2^(k^δ)`,
uniformly for `θ ≤ (k+1)/(k+2)`. -/
theorem sq_negSPCA :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∃ η : ℝ, 0 < η ∧ ∃ k₀ : ℕ,
      ∀ n d k : ℕ, k₀ ≤ k → k ≤ d → 0 < n →
        (n : ℝ) ≤ η * min ((d : ℝ) / (k : ℝ) ^ δ) ((k : ℝ) ^ (2 - 2 * δ)) →
        ∀ θ : ℝ, 0 < θ → θ ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2) →
          SDAAtLeast d k θ n ⌈(2 : ℝ) ^ ((k : ℝ) ^ δ)⌉₊ :=
  sorry

end BDT24
