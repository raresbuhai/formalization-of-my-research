# BCFGJPSSV26: A better-than-2 approximation for k-median

The main results are [BCFGJPSSV26a, Theorems 1.1, 1.2, 1.3 and 1.4], stated in
[Challenge.lean](Challenge.lean) as `BCFGJPSSV26.kMedian_approximation`,
`BCFGJPSSV26.kMedian_pseudoApproximation`, `BCFGJPSSV26.stable_kMedian_approximation` and
`BCFGJPSSV26.facilityLocation_lmp`. Theorem 1.1 is a randomized polynomial-time
`1.95`-approximation algorithm for k-median. Theorem 1.2 is a polynomial-time algorithm that opens
`k + O(log n / ε²)` centers at cost `(1.9499 + ε) opt`. Theorem 1.3, which is Theorem 1.1 of
Part II [BCFGJPSSV26b], is a `(1.89 + O(ε))`-approximation for `β`-stable instances in time
`exp(O(β⁻¹ poly(1/ε))) n^poly(1/ε)`. Theorem 1.4 is a polynomial-time `1.9499`-LMP approximation
algorithm for facility location. All four are proved in [Solution.lean](Solution.lean), with only
the standard axioms, and `lake comparator` checks them. Theorem 1.1 is proved from Theorems 1.2 and
1.3 (`BCFGJPSSV26.Combine.thm11_of`).

* [BCFGJPSSV26a] R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte,
  M. R. Pittu, M. Stouras, O. Svensson, L. Vogl, *A Better-than-2 Approximation for k-Median,
  Part I: The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144).
* [BCFGJPSSV26b] the same authors, *A Better-than-2 Approximation for k-Median, Part II: Stable
  Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172).
* [CGLSS25] V. Cohen-Addad, F. Grandoni, E. Lee, C. Schwiegelshohn, O. Svensson, *A
  (2+ε)-Approximation Algorithm for Metric k-Median*, STOC 2025,
  [arXiv:2503.10972](https://arxiv.org/abs/2503.10972).

The two parts have the same authors and are formalized together. Theorem numbers refer to Part I
unless stated otherwise; counters are shared within each section in both papers. Numbers in
[CGLSS25] refer to its arXiv version.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route.

## The statements

* **Instances** ([Model.lean](Model.lean)): `n` clients and `m ≥ 1` facilities with rational
  distances forming a pseudometric, and `k ≥ 1`. A point that is both a client and a facility is
  two points at distance `0`. Instances are encoded by `n`, `m`, `k` and the table of distances,
  so polynomial time is polynomial in `n + m` and the bits of the distances.
* **Costs.** `opt ℓ` is the least cost of a nonempty set of at most `ℓ` facilities. Outputs are
  lists of distinct facilities.
* **Theorem 1.1** (`BCFGJPSSV26.kMedian_approximation`): always at most `k` facilities, and with
  probability at least `2/3` cost at most `1.95 opt k`. The paper does not fix the probability.
* **Theorem 1.2** (`BCFGJPSSV26.kMedian_pseudoApproximation`): deterministic, as in the paper; one
  constant `C` for every `ε > 0`, at most `k + C log n / ε²` facilities, where `n` is the number
  of clients. Large `ε` use local search with `k` centers.
* **Theorem 1.3** (`BCFGJPSSV26.stable_kMedian_approximation`): one algorithm that is given the
  instance, a number `L ≥ 1/β` in unary and the accuracy `ε` as a rational number in binary, runs
  in time `O(2^(e L) (N + 2)^e + N + L + |ε|)` with `e = a (⌈1/ε⌉ + 1)^b`, where `N` is the
  encoded length of the instance and `|ε|` that of `ε`, and always outputs exactly `k` facilities
  (for `k ≤ m`); for `ε ∈ (0, 1/200)`, with probability at least `1 - ε` their cost is at most
  `(1.89 + C ε) opt k`. The machine, its constant factor and the constants `a`, `b`, `C` are
  absolute. Stability is `opt (k - 1) ≥ (1 + β) opt k` for `k ≥ 2`; every instance with `k = 1`
  is stable, as in the paper, where `opt 0 = ∞`.
* **Theorem 1.4** (`BCFGJPSSV26.facilityLocation_lmp`): deterministic polynomial time; given a
  valid instance with at least one client (its `k` plays no role) and an opening cost `f ≥ 0`, a
  nonempty set `S` of distinct facilities with `cost S ≤ 1.9499 (OPT_f - f |S|)`, where `OPT_f`
  is the least `cost S' + f |S'|` over nonempty `S'`.

Randomized algorithms are Turing machines that read the instance and a string of coin flips, as
in [BGHKLMM26](../BGHKLMM26); the time bound is explicit and is also the number of coins.

## Map of the proof

### Theorem 1.1

[Combine.lean](Combine.lean) (`BCFGJPSSV26.Combine.thm11_of`) proves Theorem 1.1 from the
statements of Theorems 1.2 and 1.3 by the argument of [BCFGJPSSV26a, Section 1.1, step (ii)]. With
`k₀ = min(k, m)` and `c - 1` a bound on the extra centers of Theorem 1.2, the algorithm runs the
algorithm of Theorem 1.2 with `k₀ - c` centers and the algorithm of Theorem 1.3, with a fixed
accuracy, with `k₀ - j` centers for every `j < min(c, k₀)`, each on its own block of coins, and
outputs the cheapest valid
output. Either `opt (k₀ - c)` is within a factor `1 + 10⁻⁵` of `opt k₀`, or some `k₀ - j` is
`1/L`-stable for `L = 100001 c` with `opt (k₀ - j)` within that factor of `opt k₀`, and
`opt k₀ ≤ opt k`.

| Files | Content |
| --- | --- |
| [Combine/Algorithm.lean](Combine/Algorithm.lean) | The combined algorithm: the runs, their blocks of coins, exact costs, the cheapest valid output. |
| [Combine/Analysis.lean](Combine/Analysis.lean) | `opt (min(k, m)) ≤ opt k`; a stable number of centers; events on one block of coins. |
| [Combine/PolyTime.lean](Combine/PolyTime.lean), [../Background/BlackBox.lean](../Background/BlackBox.lean) | Polynomial time, with the algorithms of Theorems 1.2 and 1.3 given only as machines; reading a prefix of the coins. |
| [Combine.lean](Combine.lean) | The statements of Theorems 1.1–1.3 and the assembly. |

### Theorem 1.2

[Greedy/](Greedy) (see its [README](Greedy/README.md)) proves it as
`BCFGJPSSV26.Greedy.greedy_main`, with `C = 10¹⁰`. The algorithm is deterministic: the
log-adaptive greedy of [BCFGJPSSV26a, Section 5 and Appendices D and E] with the bids
`[α - 1.224 d]⁺`. The type-2 openability test uses bids of the form `F_i(T)` and the least such
`T`, computed exactly. Distances are scaled by guessing the scale among the client–facility
distances, and the solutions for two opening costs are merged after [CGLSS25, Section 3.5]. The
guarantee comes from the bound on the factor-revealing program in [KMedian195](../Imported/KMedian195).
For `ε ≥ 4` the algorithm is the local search of Part II.

| Files | Content |
| --- | --- |
| [Greedy/Bid.lean](Greedy/Bid.lean), [Greedy/Space.lean](Greedy/Space.lean), [Greedy/Openable.lean](Greedy/Openable.lean), [Greedy/Valid.lean](Greedy/Valid.lean), [Greedy/Structure.lean](Greedy/Structure.lean) | The bid, the parameters, openability and the exact tests, valid solutions, the structure lemma. |
| [Greedy/Trace.lean](Greedy/Trace.lean), [Greedy/FRP.lean](Greedy/FRP.lean), [Greedy/Embed.lean](Greedy/Embed.lean), [Greedy/LMP.lean](Greedy/LMP.lean) | The robust LMP guarantee (`BCFGJPSSV26.Greedy.robust_lmp`), through the factor-revealing program. |
| [Greedy/Alg/](Greedy/Alg) | The core: CompleteSolution, the bisection on the opening cost and the merge; at most `k + 6R` facilities of cost at most `(ρ + 10δ) opt`. |
| [Greedy/Reduction/](Greedy/Reduction), [Greedy/Algorithm.lean](Greedy/Algorithm.lean), [Greedy/Constants.lean](Greedy/Constants.lean), [Greedy/Main.lean](Greedy/Main.lean) | The trivial solution, the scaled distances, the local search for large `ε`, the constants, Theorem 1.2. |
| [Greedy/PolyTime/](Greedy/PolyTime) | Polynomial time. |

### Theorem 1.3

[Stable/](Stable) (see its [README](Stable/README.md)) proves it as
`BCFGJPSSV26.Stable.stable_main`, with `b = 2` and `C = 1000`. One machine serves all `ε`: it
computes `N`, a power of two with `1/N < ε` (for `ε > 0`) and `N ≤ 256 (⌈1/ε⌉ + 1)`, from the
numbers of binary digits of the numerator and the denominator of `ε`, in time linear in the
encoding of `ε`; then it takes the accuracy `1/N` and reads a budget in unary. The local search
reaches an approximate local optimum. Fewer than `632/(εβ)` optimal clusters are unsynced, so the
algorithm uses `s = 632 N L`. The client and cluster sampling are state machines reading chunks
of coins, and the radii of the cluster-sampling dummies of one leader are made distinct by a small
shift. After color coding, the submodular step uses a sequential greedy reaching
`1 - (1 + 1/N)^(-N)` of the optimum. The trials are repeated, and the final output is sanitized
to exactly `k` facilities.

| Files | Content |
| --- | --- |
| [Stable/Main.lean](Stable/Main.lean), [Stable/Params.lean](Stable/Params.lean), [Stable/Hyp.lean](Stable/Hyp.lean), [Stable/Alg/Main.lean](Stable/Alg/Main.lean), [Stable/Alg/Trial.lean](Stable/Alg/Trial.lean) | The theorem, with `N` computed from `ε`; the parameters and the standing hypotheses; the algorithm, its validity and its success probability; one trial. |
| [Stable/Alg/LocalSearch.lean](Stable/Alg/LocalSearch.lean), [Stable/LocalSearch/](Stable/LocalSearch) | The local search and its termination; swap families on star forests ([BCFGJPSSV26b, Lemma 6.2]), the refined local-search bound (Theorem 3.6), and `cost ≤ 4 opt` (Corollary 1.5). |
| [Stable/Percentile.lean](Stable/Percentile.lean), [Stable/Kappa.lean](Stable/Kappa.lean), [Stable/Dummy.lean](Stable/Dummy.lean), [Stable/Stability/](Stable/Stability) | Percentiles, `κ`, dummies; synced and close clusters ([BCFGJPSSV26b, Section 4.1]). |
| [Stable/Structure/](Stable/Structure), [Stable/LSBound/NiceMaps.lean](Stable/LSBound/NiceMaps.lean) | Satellites, the good outcomes of the two samplings, the structural theorem (Theorems 3.1 and 3.2); the nuanced local-search bound (Theorem 3.8). |
| [Stable/Alg/Coins.lean](Stable/Alg/Coins.lean), [Stable/Alg/Mixed.lean](Stable/Alg/Mixed.lean), [Stable/Alg/ClientSampling.lean](Stable/Alg/ClientSampling.lean), [`Stable/Alg/ClusterSampling*.lean`](Stable/Alg) | Coins in chunks and the counting lemmas; exact dummies and mixed sets; the client and cluster sampling (Algorithms 1 and 2) and their analyses. |
| [Stable/Submod/](Stable/Submod), [Stable/Alg/Submod.lean](Stable/Alg/Submod.lean), [Stable/Alg/Coloring.lean](Stable/Alg/Coloring.lean) | Color coding and the submodular step ([BCFGJPSSV26b, Section 5], Theorem 3.4). |
| [Stable/WinWin.lean](Stable/WinWin.lean), [Stable/Final/Combine.lean](Stable/Final/Combine.lean) | The win-win combination (Lemma 3.9). |
| [Stable/Time/](Stable/Time) | `N` from `ε`; the budget and the running time, with one degree for every `N`. |

### Theorem 1.4

[FL/](FL) (see its [README](FL/README.md)) proves it as `BCFGJPSSV26.FL.fl_main`. The algorithm
runs the log-adaptive greedy of Part I once, at one opening cost, with no slack (`η = 0`), on the
distances shifted and scaled, and bounds it by `BCFGJPSSV26.Greedy.robust_lmp`. The output is the
candidate with the least `cost S + 1.9499 f |S|`, among the greedy run and the nearest facilities
of the clients.

| Files | Content |
| --- | --- |
| [FL/Algorithm.lean](FL/Algorithm.lean), [FL/Run.lean](FL/Run.lean) | The scale, the parameters and the greedy run; its LMP bound. |
| [FL/Select.lean](FL/Select.lean), [FL/Main.lean](FL/Main.lean) | The choice of the output, and Theorem 1.4. |
| [FL/PolyTimeCtx.lean](FL/PolyTimeCtx.lean), [FL/PolyTime.lean](FL/PolyTime.lean) | Polynomial time. |

### Shared material

| Files | Content |
| --- | --- |
| [Basic/Metric.lean](Basic/Metric.lean) | Distances to sets of facilities, costs, optimal sets, nearest centers and clusters, over the reals. |
| [Basic/Raw.lean](Basic/Raw.lean) | Instances as the algorithms read them, exact costs and nearest centers, and lists of exactly `k` facilities (`BCFGJPSSV26.sanitizeK`). |
| [../Background/Tuples.lean](../Background/Tuples.lean), [../Background/TuplesPolyTime.lean](../Background/TuplesPolyTime.lean) | Tuples cut at a budget, as in [BKS23](../BKS23), and their certificate. |
| [../Background/PolyTime/Lists.lean](../Background/PolyTime/Lists.lean) | More list operations in polynomial time. |

### The factor-revealing program

The bound on the factor-revealing program [BCFGJPSSV26a, Theorem 4.4] is
`KMedian195.originalPrimalUpperBound_exact`: for `γ ∈ [1, 1.224]`, the program of
[BCFGJPSSV26a, Definition 4.1] with the bid `[α - γ d]⁺` has value at most `2 - (γ - 1)²`.
[Greedy/FRP.lean](Greedy/FRP.lean) applies it with `γ = 1.224`, so `2 - 0.224² = 1.949824`. The
library [KMedian195](../Imported/KMedian195) is copied from the project `bound-195` of
[`epfl-thl2/project-k-median`](https://github.com/epfl-thl2/project-k-median), at commit
`d87e2a20376896ab72fe005a493b3af970a0f82d`. All of its code was written by Codex; its
[README](../Imported/KMedian195/README.md) lists the changes made for our Lean and Mathlib.

*Formalized by [Claude Code](https://claude.com/claude-code).*
