# BGHKLMM26: Optimal algorithms and hardness for Max-Cut in bounded degree graphs

The main results are [BGHKLMM26, Theorem 1.1] and [BGHKLMM26, Theorem 1.2], stated in
[Challenge.lean](Challenge.lean) as `BGHKLMM26.max2lin_approximation` and
`BGHKLMM26.maxCut_hardness`. Theorem 1.1 is a randomized polynomial-time algorithm for weighted
Max 2-LIN(2) whose expected value is at least `(α_GW + c/(d log d))` times the optimum when every
variable appears in at most `d` constraints. Theorem 1.2 says that, assuming the Unique Games
Conjecture, telling graphs of maximum degree `d` with Max-Cut value at least `c* - C/d` from those
with value at most `s* + C log² d / d` with bounded error in polynomial time would put `NP` in
`BPP`; it is formalized with `C log d / d` in place of `C log² d / d`. Both are proved in
[Solution.lean](Solution.lean), with only the standard axioms, and `lake comparator` checks
them.

[BGHKLMM26, Corollary 1.3] is `BGHKLMM26.maxCut_inapproximability`: assuming the Unique Games
Conjecture, a randomized polynomial-time algorithm whose expected cut is at least
`(α_GW + C log d / d)` times the maximum on graphs of maximum degree `d` would put `NP` in `BPP`.
It is proved from Theorem 1.2 and checked by `lake comparator` too.

[BGHKLMM26, Theorem 1.4] is `BGHKLMM26.maxCut_integrality_gap`: for every large `d`, some graph
of maximum degree `d` has Goemans–Williamson SDP value with triangle inequalities at least
`c* - C/d` and Max-Cut value at most `s* + C log d / d`. It is unconditional, proved from
Theorem 7.1, and checked by `lake comparator` too.

Theorems 1.2 and 1.4 and Corollary 1.3 are stated with `log d / d`, one logarithm better than
the paper's `log² d / d`. The robust Majority is Stablest theorem behind them (Theorem 7.1) rests
on the Gaussian lemma with the error `C √Δ` (Lemma 7.4), which the paper takes from Heilman's
robust Borell inequality. Here it is proved from scratch, in two steps: Eldan's published estimate
of the Gaussian noise stability deficit (Invent. Math. 2015) brings the function close to the
halfspace, and a local spectral argument at the halfspace gives the error `C √Δ`. With that error,
the multiscale union bound of Lemma 6.6 starts at the scale `K log d / d`.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route.

Numbers refer to the arXiv version (v2), whose counters are shared within each section.

## The statements

* **Max 2-LIN(2)** ([Model.lean](Model.lean)): `n` variables in `{±1}`, constraints `xᵢ xⱼ = b`
  with rational weights `w ≥ 0` on distinct pairs; `n` is in unary, so that the algorithm can
  output an assignment.
* **Randomized algorithms** (`BGHKLMM26.RunsInTime`): a multitape Turing machine reading the
  instance and `T |x| = (|x| + 2)^k` coin flips; the expectation is over the coins
  (`BGHKLMM26.coinMean`).
* **Max-Cut** (`BGHKLMM26.maxCutGap`): simple graphs encoded by their adjacency tables; the gap
  problem restricted to maximum degree at most `d`. `c* = (1 - ρ*)/2` and `s* = arccos ρ* / π` for
  the minimizer `ρ*` of the Goemans–Williamson ratio (`BGHKLMM26.exists_unique_isGWMinimizer`).
* **The Unique Games Conjecture** (`UniqueGames.UGC`, shared with the other papers in
  `Background/UniqueGames.lean`) is a hypothesis, in the form of Conjecture 4.10 (simple
  bi-regular bipartite instances), except that it asks for one number of labels rather than all
  large ones (weaker, and enough).
* **The conclusion** of Theorem 1.2 is that the gap problem in complexitylib's `PromiseBPP` implies
  `NP ⊆ BPP` for every encoding: it rules out bounded-error randomized algorithms.
* **Constants.** In Theorem 1.1, one `c > 0` for all `d ≥ 2`; in Theorem 1.2, Corollary 1.3 and
  Theorem 1.4, one `C` and one `d₀` for all `d ≥ d₀`.
* **Corollary 1.3** uses the algorithms and the guarantee of Theorem 1.1 (expected value over the
  coins), on Max 2-LIN(2) instances that are unweighted graphs (`BGHKLMM26.IsMaxCutInstance`), so
  it is the converse of Theorem 1.1. The algorithm may depend on `d`.
* **The SDP** of Theorem 1.4 (`BGHKLMM26.IsSDPSolution`, `BGHKLMM26.sdpValue`): unit vectors in
  `ℝⁿ` with the triangle inequalities of Section 3, valued by the average of `‖vᵢ - vⱼ‖² / 4` over
  the edges. The theorem exhibits a solution, and also states the integrality gap
  `MaxCut ≤ (α_GW + C log d / d) · SDP` that follows. Theorem 1.4 is unconditional.

## Map of the proof

### Theorem 1.1

| Files | Content |
| --- | --- |
| [GW.lean](GW.lean), [Baseline.lean](Baseline.lean) | The Goemans–Williamson ratio: its unique minimizer `ρ* ∈ (-4/5, -1/2)`, `0 < α_GW < 1`, the gap `κ` outside a rational window, and hyperplane rounding (Lemma 3.3). |
| [../Background/Gaussian.lean](../Background/Gaussian.lean), [../Background/GaussianCalculus.lean](../Background/GaussianCalculus.lean), [../Background/ArcsinSeries.lean](../Background/ArcsinSeries.lean) | Sheppard's formula through Owen's `T` function (TauCeti), Gaussian calculus, the smoothed correlations (Fact 3.9). |
| [Energy.lean](Energy.lean), [Strip.lean](Strip.lean), [Gain.lean](Gain.lean), [Ideal.lean](Ideal.lean) | Section 3: votes and energy (Lemmas 3.10, 3.12), strips (3.13–3.15), the gain (3.16–3.20, Theorem 3.2), the two roundings (3.4, 3.5). |
| [SDP.lean](SDP.lean), [Factor.lean](Factor.lean), [Numerics.lean](Numerics.lean), [Algorithm.lean](Algorithm.lean) | The machine: the SDP by the sum-of-squares solver, the vectors from a positive definiteness test, Gaussians from coins through `Φ`, projections rounded to `2^-p`. |
| [Exact.lean](Exact.lean), [Accuracy.lean](Accuracy.lean), [Robust.lean](Robust.lean), [Opt.lean](Opt.lean), [Assembly.lean](Assembly.lean) | Exactness of the machine's choices, accuracy of its projections, robustness of the signs, `opt ≥ W/2`, and the mean value (`BGHKLMM26.Alg.alg_mean`). |
| [Run.lean](Run.lean), [PolyTime.lean](PolyTime.lean), [RunTime.lean](RunTime.lean) | Polynomial-time certificates and the running time (`BGHKLMM26.Alg.exists_runsInTime`). |

### Theorem 1.2

Assuming Theorem 7.1 (`BGHKLMM26.Hard.RobustMIS`, robust Majority is Stablest with the error
`C √η`), [Hardness/Main.lean](Hardness/Main.lean) proves the theorem
(`BGHKLMM26.Hard.maxCut_hardness_of_robustMIS`); [RobustMIS/Final.lean](RobustMIS/Final.lean)
proves Theorem 7.1 (`BGHKLMM26.RobustMIS.robustMIS`).

| Files | Content |
| --- | --- |
| [Hardness/Defs.lean](Hardness/Defs.lean) | The reduction: the KKMO graph (Figure 5.1) without noise, LTFs, `Cut_ρ`, the statement of Theorem 7.1, and the machine (edges decoded from blocks of coins, greedy simplification with degree cap `d`). |
| [Hardness/TwoSided.lean](Hardness/TwoSided.lean), [Hardness/Enlarge.lean](Hardness/Enlarge.lean) | `PromiseBPP` is closed under randomized reductions with two-sided error; the alphabet enlargement `π ↦ π × id`. |
| [../Imported/OAI](../Imported/OAI), [Stablest.lean](Stablest.lean), [Hardness/KKMO.lean](Hardness/KKMO.lean) | Majority is Stablest (from OpenAI's library), its cut form for `ρ < 0` (Corollary 4.3), and the KKMO completeness and soundness (Lemmas 5.1, 5.2, 5.4), with low-degree influences. |
| [Hardness/LTF.lean](Hardness/LTF.lean), [Hardness/KKMORobust.lean](Hardness/KKMORobust.lean) | LTFs: at most `(2^R + 1)^(R+1)` of them (Chow's theorem), Corollary 4.6, Claim 4.7, Lemma 4.8; the robust inverse of soundness (Lemma 5.3) from Theorem 7.1. |
| [Hardness/Decoder.lean](Hardness/Decoder.lean), [Hardness/Coins.lean](Hardness/Coins.lean), [Hardness/Glue.lean](Hardness/Glue.lean) | The law of a decoded edge against the KKMO graph; the coins as independent blocks. |
| [Hardness/Concentration.lean](Hardness/Concentration.lean), [Hardness/SparsifyMain.lean](Hardness/SparsifyMain.lean) | Hoeffding, Bernstein, binomial tails, Hamming balls; the sparsification (Section 6) for an abstract law. |
| [Hardness/Machine.lean](Hardness/Machine.lean), [Hardness/Main.lean](Hardness/Main.lean) | The reduction in polynomial time; completeness and soundness of the reduction and the assembly. |
| [RobustMIS/](RobustMIS) (see its [README](RobustMIS/README.md)) | Theorem 7.1. The Gaussian lemma (Lemma 7.4) in two steps: Eldan's estimate, with the error `C √(Δ log(e/Δ))`, by Eldan's argument in analytic form (the heat flow, the deficit and drift identities, the static Gaussian bounds, the bootstrap); then the error `C √Δ` by a local spectral argument at the halfspace (the Mehler kernel along its normal, and the spectral gap of the noise operator from TauCeti's Hermite basis). The transfer to the cube by an invariance principle for pairs of polynomials (Bonami, Lindeberg, mollification), in place of the anti-concentration of regular forms and Mossel–Neeman's Lemma 7.3; the truncation; and the smoothing removal, with a bound for regular LTFs in place of Peres's bound. |

How the reduction is implemented:

* **Correlation and constraints.** The machine samples pairs with a dyadic correlation `ρ_d` close
  to `ρ*`, with the cut value Lipschitz in `ρ` and Theorem 7.1 applied at `ρ*`, and reads the
  index of a constraint modulo the number of constraints from enough coins.
* **The dense graph** has no noise `μ`: Majority is Stablest with low-degree influences gives its
  soundness, and the robust inverse is applied to the smoothed `T_{1-γ} g_u`.
* **The sparsification** succeeds with probability `9/10` on each side, so that it composes with
  a bounded-error algorithm (`BGHKLMM26.Hard.RandReducible`).
* **The multiscale union bound** (Lemma 6.6) starts at the scale `λ = K log D / D`
  (`BGHKLMM26.Hard.lam`), at which Bernstein's bound beats the Hamming balls of radius `C₁ √η`
  (`BGHKLMM26.Hard.radius_entropy_le`). The union over the tuples of LTFs is bounded by
  `exp(n / A(d))`, with the number of labels `R` large depending on `d` through the alphabet
  enlargement.

### Corollary 1.3

[Inapprox.lean](Inapprox.lean) (`BGHKLMM26.Inapprox.of_hardness`): a graph becomes a Max-Cut
instance in polynomial time, with one constraint per edge; the algorithm is run a number of times
depending on `d`, accepting if one of its cuts crosses more than a rational fraction between
`s` and `α c` of the edges. No-instances are never accepted, and by Markov's inequality each run
accepts a yes-instance with probability bounded below, so this solves Theorem 1.2's gap problem in
`PromiseBPP`.

### Theorem 1.4

[IntGap/Main.lean](IntGap/Main.lean) (`BGHKLMM26.IntGap.integrality_gap`): the reduction of
Theorem 1.2 applied to a Unique Games integrality gap instance. With probability `9/10` its output
is a no-instance, and with probability `9/10` an SDP solution for all its vertices keeps its value
on the sampled edges; some output does both.

| Files | Content |
| --- | --- |
| [IntGap/Cube.lean](IntGap/Cube.lean), [IntGap/Instance.lean](IntGap/Instance.lean) | Khot and Vishnoi's instance (KV15, Section 3) in a bipartite form: right vertices are Boolean functions on `{0,1}^k` modulo characters, left vertices a class and a set `Z` of `z` points, one constraint for each function vanishing outside `Z`. It is simple and bi-regular, and its tuples `T_{P,s}` (tensor squares of truth tables) are within `1 - 4z/2^k` along two constraints at one left vertex. |
| [IntGap/Sound.lean](IntGap/Sound.lean) | Its value is at most `2^{-kz/(8·2^k)}`: the label-extended graph and hypercontractivity on the cube of truth tables. |
| [IntGap/Tensor.lean](IntGap/Tensor.lean), [IntGap/KS.lean](IntGap/KS.lean), [IntGap/Mix.lean](IntGap/Mix.lean) | The long-code kernel (scales of tensor powers of the tuples) and Khot and Saket's local argument (FOCS 2009) for three points: at each scale, single-linkage clusters at radius `2^{-(i+1)T}` and labels matched through the clusters give correlations with the signed triangle inequalities, within `4/Δ + 2^{-T}` of the kernel. Mixing with the identity, `(1-δ) K + δ I`, makes them exact; vectors from a factorization of the Gram matrix. |
| [IntGap/Dense.lean](IntGap/Dense.lean) | The kernel on the dense graph of the reduction: at most `ρ (1 - 4zs/2^k)`, so SDP value at least `(1 - ρ)/2` up to `δ` and `4zs/2^k`. |
| [IntGap/Sample.lean](IntGap/Sample.lean), [IntGap/SoundAt.lean](IntGap/SoundAt.lean) | The completeness of the sparsification for an edge score in `[0, 1]`, applied to the SDP value; the soundness of Theorem 1.2 for a given instance with enough labels and small value. |

*Formalized by [Claude Code](https://claude.com/claude-code).*
