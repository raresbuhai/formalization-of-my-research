# Stable instances

[BCFGJPSSV26b, Theorem 1.1], which is [BCFGJPSSV26a, Theorem 1.3], is
`BCFGJPSSV26.Stable.stable_main : BCFGJPSSV26.Combine.Thm13` ([Main.lean](Main.lean); the
statement is `BCFGJPSSV26.stable_kMedian_approximation` in [../Challenge.lean](../Challenge.lean)):
one algorithm is given a valid instance with `k ≤ m`, a number `L` in unary and the accuracy `ε`
as a rational number in binary, runs in time `O(2^(e L) (|I| + 2)^e + |I| + L + |ε|)` with
`e = a (⌈1/ε⌉ + 1)²`, where `|I|` is the encoded length of the instance and `|ε|` that of `ε`, and
always outputs exactly `k` distinct facilities; for `ε ∈ (0, 1/200)`, on a `β`-stable instance
with `L ≥ 1/β` it outputs, with probability at least `1 - ε`, facilities of cost at most
`(1.89 + 1000 ε) opt k`. The constants are `a = d' (10⁶ · 2¹⁶ + 1)`, `b = 2` and `C = 1000`,
where `d'` bounds the degrees of the polynomial-time certificates of the steps of the algorithm,
the same for every `ε`.

The algorithm takes the accuracy `1/N` for `N = 2^(g + 8)`, where `g` is computed from the
numbers of binary digits of the numerator and the denominator of `ε`, in time linear in the
encoding of `ε` ([Time/Accuracy.lean](Time/Accuracy.lean)): `N ≥ 256`, `1/N < ε` for `ε > 0`, and
`N ≤ 256 (⌈1/ε⌉ + 1)`, so `ε/512 ≤ 1/N < ε` for `ε ∈ (0, 1/200)`. Its parameters are explicit
functions of `N`, `L` and the instance ([Params.lean](Params.lean)); the bound on the special
clusters is `s = 632 N L`.

## The route

1. **One algorithm for all accuracies** (`BCFGJPSSV26.Stable.coreAlg`,
   `BCFGJPSSV26.Stable.alg`). The core reads `N`, the instance, `L`, the coins and a budget `B`,
   with `N`, `L` and `B` in unary, and cuts every loop and enumeration at `B`; so one polynomial
   bound serves every `N`. Given `N` in unary with the instance and `L`
   (`BCFGJPSSV26.Stable.algN`), the machine writes `B = 2^(e₁ L) (|I| + 2)^(e₁)`, `e₁ = 10⁶ N²`,
   keeps the coins the core reads, and runs the core, in time `O(stableTime (d e₁ + d))` plus the
   length of the input, for one `d` and every `N` (`BCFGJPSSV26.Stable.exists_algN_inO`). The
   machine of the theorem (`BCFGJPSSV26.Stable.algQ`) first computes `N` from `ε`
   (`BCFGJPSSV26.Stable.exists_accN_inO`); since `N ≤ 256 (⌈1/ε⌉ + 1)`, it runs in time
   `O(stableTime (a (⌈1/ε⌉ + 1)²))` plus the length of the input
   (`BCFGJPSSV26.Stable.exists_runsInTime`).
2. **Local search** (`BCFGJPSSV26.Stable.localSearch`, `BCFGJPSSV26.Stable.isALO_localSearch`).
   From the facilities `0, …, k - 1`, apply the first swap of at most `24 N` facilities that lowers
   the exact cost below `(1 - 1/(N k))` times the current one. It stops within
   `2 N k |enc I| + 2` improvements, since `Q · cost` is a natural number for the product `Q` of
   the denominators of the table, and its output is an approximate local optimum. Swap families on
   star forests (`BCFGJPSSV26.Stable.BiGraph.exists_swap_families`, a variant of
   [BCFGJPSSV26b, Lemma 6.2]) give the refined local-search bound
   ([BCFGJPSSV26b, Theorem 3.6], `BCFGJPSSV26.Stable.refined_ls`) and the bound
   `(3 + 100/N) opt ≤ 4 opt` ([BCFGJPSSV26b, Corollary 1.5],
   `BCFGJPSSV26.Stable.costF_le_three_add`).
3. **Stability** (`BCFGJPSSV26.Stable.Hyp.card_unsynced_lt`). Fewer than `632/(εβ)` optimal
   clusters are unsynced ([BCFGJPSSV26b, Lemma 4.2] with this bound; of the local search, the
   proof uses only `cost(S) ≤ 4 opt`), so `s = 632 N L ≥ 632/(εβ)` bounds the special clusters.
   Synced and close clusters have substitutes in the local search ([BCFGJPSSV26b, Propositions
   4.3 and 4.4], `BCFGJPSSV26.Stable.Hyp.syncSub`, `BCFGJPSSV26.Stable.Hyp.closeSub`).
4. **Sampling from coin chunks.** All randomness comes from chunks of `|enc I| + 7 N` coins: fair
   bits, uniform choices and weighted samples, with lower bounds on the number of chunks giving
   each outcome. The client sampling and the cluster sampling ([BCFGJPSSV26b, Algorithms 1 and
   2]) are state machines reading three chunks per iteration, resp. one chunk per step
   (`BCFGJPSSV26.Stable.csRun`, `BCFGJPSSV26.Stable.ksRun`). Their analyses are process lemmas
   (`BCFGJPSSV26.Stable.Hyp.card_clientWitness`, `BCFGJPSSV26.Stable.Hyp.card_clusterWitness`):
   from every state satisfying an invariant, a fraction `1/(440 N⁸)`, resp. `1/(12 N³)`, of the
   next chunks keeps it (`BCFGJPSSV26.Stable.guided_count`), and the invariant at the end is a
   good outcome of the client-sampling and cluster-sampling theorems ([BCFGJPSSV26b, Sections 4.2
   and 4.4]). In the cluster sampling, the radius of the `t`-th dummy is a grid point shifted by
   `t r₀/(N⁴ (2s + 2))`, less than the spacing of the grid, so that the dummies of one
   leader are distinct (`BCFGJPSSV26.Stable.ksRad`); a skipped iteration leaves the state
   unchanged, so the cost condition that made it skip persists; and every run ends within
   `20 s + 20` steps (`BCFGJPSSV26.Stable.ksRun_phase`).
5. **The structural theorem** ([BCFGJPSSV26b, Theorems 3.1 and 3.2],
   `BCFGJPSSV26.Stable.Hyp.exists_partition`): the optimal centers split into those with
   substitutes, dummies, backups and satellites, with the bounds of the theorems. With the
   cross-free maps of [BCFGJPSSV26b, Lemma 3.7] and the refined bound, the local search costs at
   most `Ψ_LS + 150 ε opt` ([BCFGJPSSV26b, Theorem 3.8],
   `BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS`).
6. **The submodular step** ([BCFGJPSSV26b, Section 5], `BCFGJPSSV26.Stable.candidate`). For each
   guess `p' ≤ s`, the kept centers are colored by coins (color coding; the good event has
   probability at least `4^(-s)`, `BCFGJPSSV26.Stable.Partition.card_colorEvent`), and
   `f = g(∅) - g` is monotone and submodular (`BCFGJPSSV26.Stable.gfun_isSubmod`). The
   maximization of `f` with one element in each ball of a dummy and `p'` more facilities uses a
   deterministic sequential greedy with `N` rounds (`BCFGJPSSV26.Stable.seqGreedy_bound`), which
   reaches `1 - (1 + 1/N)^(-N)` of the optimum; its sums over `[N]^ρ`, `ρ ≤ s`, are enumerated
   within the budget. The candidate of the guess `|O_P|` costs at most `Ψ_T + 60 ε opt`
   ([BCFGJPSSV26b, Theorem 3.4], `BCFGJPSSV26.Stable.Partition.costF_candidate_le`).
7. **Win-win** ([BCFGJPSSV26b, Lemma 3.9 and Table 1], `BCFGJPSSV26.Stable.Partition.psi_combo`).
   With `κ` given explicitly by `1 + κ = (89 - 12 t)/(65 t)` (`BCFGJPSSV26.Stable.kappa`), the
   `(3/25, 22/25)` combination of the two rows of every optimal cluster is at most
   `1 + η + O(ε)`, so the local search or the candidate costs at most `(1.89 + 100 ε) opt`
   (`BCFGJPSSV26.Stable.Partition.min_le_bound`). For `k = 1` or `opt = 0` the local search alone
   suffices (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`).
8. **Repetition and output** (`BCFGJPSSV26.Stable.success_prob`, `BCFGJPSSV26.Stable.alg_valid`).
   Each of the `R = N^(200 s + 1)` trials reads its own block of chunks and is good with
   probability at least `q = N^(-200 s)` (`BCFGJPSSV26.Stable.Hyp.card_trialGood`), so some trial
   is good with probability at least `1 - (1 - q)^R ≥ 1 - 1/N`. The output is the cheapest of the
   local search and all candidates, each made into exactly `k` distinct facilities by
   `BCFGJPSSV26.sanitizeK` ([../Basic/Raw.lean](../Basic/Raw.lean)), so it is valid for every
   instance with `k ≤ m`, every `L` and every coin string.

## Files

| Files | Content |
| --- | --- |
| [Main.lean](Main.lean), [Params.lean](Params.lean), [Hyp.lean](Hyp.lean) | The theorem, from the algorithm for `N` computed from `ε`; the parameters; the context and the standing hypotheses of the analysis. |
| [Alg/Main.lean](Alg/Main.lean), [Alg/Trial.lean](Alg/Trial.lean) | The core and the algorithm for one `N`: validity, comparison with the candidates, the success probability; one trial and its probability of being good. |
| [Alg/LocalSearch.lean](Alg/LocalSearch.lean), [LocalSearch/Defs.lean](LocalSearch/Defs.lean) | The local search, its termination and its output; approximate local optima. |
| [LocalSearch/StarForestAux.lean](LocalSearch/StarForestAux.lean), [LocalSearch/StarForest.lean](LocalSearch/StarForest.lean), [LocalSearch/Refined.lean](LocalSearch/Refined.lean), [LocalSearch/ThreeApprox.lean](LocalSearch/ThreeApprox.lean) | Swap families on star forests (Lemma 6.2) and their combinatorics; the refined local-search bound (Theorem 3.6); the `(3 + 100/N)`-approximation (Corollary 1.5). |
| [Percentile.lean](Percentile.lean), [Kappa.lean](Kappa.lean), [Dummy.lean](Dummy.lean) | Percentiles and cores; the parameter `κ` and the technical condition of Lemma 3.9; dummies and mixed sets. |
| [Stability/Defs.lean](Stability/Defs.lean), [Stability/FewNotInSync.lean](Stability/FewNotInSync.lean), [Stability/SyncSub.lean](Stability/SyncSub.lean) | Synced and close clusters and the first consequences of stability; fewer than `632/(εβ)` unsynced clusters (Lemma 4.2); substitutes for synced and close clusters (Propositions 4.3, 4.4). |
| [Structure/Satellites.lean](Structure/Satellites.lean), [Structure/ClientWitness.lean](Structure/ClientWitness.lean), [Structure/ClusterWitness.lean](Structure/ClusterWitness.lean), [Structure/Partition.lean](Structure/Partition.lean) | Satellites (Lemma 4.5, comparable percentiles); the good outcomes of the two samplings and the cost bounds of Section 4.7; the structural theorem (Theorems 3.1, 3.2). |
| [Alg/Coins.lean](Alg/Coins.lean), [Alg/Mixed.lean](Alg/Mixed.lean) | Chunks of coins, their primitives and the counting lemmas; exact dummies, mixed sets and the radius grid. |
| [Alg/ClientSampling.lean](Alg/ClientSampling.lean) | The client sampling (Algorithm 1) and its process lemma. |
| [Alg/ClusterSampling.lean](Alg/ClusterSampling.lean), [Alg/ClusterSamplingGhost.lean](Alg/ClusterSamplingGhost.lean), [Alg/ClusterSamplingBridge.lean](Alg/ClusterSamplingBridge.lean), [Alg/ClusterSamplingStep.lean](Alg/ClusterSamplingStep.lean), [Alg/ClusterSamplingDensity.lean](Alg/ClusterSamplingDensity.lean), [Alg/ClusterSamplingAnalysis.lean](Alg/ClusterSamplingAnalysis.lean) | The cluster sampling (Algorithm 2) as a state machine, and its termination; the ghost matching and the invariant; exact weights and counting; one step, mode by mode; the densities of good chunks; the process lemma. |
| [LSBound/NiceMaps.lean](LSBound/NiceMaps.lean) | The nuanced local-search bound (Theorem 3.8), from the cross-free maps of Lemma 3.7, Claim A.1 and Lemmas A.2, A.3. |
| [Submod/Supermodular.lean](Submod/Supermodular.lean), [Submod/SeqGreedy.lean](Submod/SeqGreedy.lean), [Submod/Candidate.lean](Submod/Candidate.lean) | Submodularity of minimum-type functions (Claim B.1, sums of the smallest values); the sequential greedy; the bounds on the candidate (Lemmas 5.2–5.4, Theorem 3.4). |
| [Alg/Submod.lean](Alg/Submod.lean), [Alg/Coloring.lean](Alg/Coloring.lean) | The submodular step in exact arithmetic and its specification; color coding. |
| [WinWin.lean](WinWin.lean), [Final/Combine.lean](Final/Combine.lean) | The rows of Lemma 3.9; the win-win combination and the degenerate cases `k = 1`, `opt = 0`. |
| [Time/Budget.lean](Time/Budget.lean), [Time/PolyTimeRaw.lean](Time/PolyTimeRaw.lean), [Time/PolyTimeCoins.lean](Time/PolyTimeCoins.lean), [Time/PolyTimeKS.lean](Time/PolyTimeKS.lean), [Time/PolyTimeSubmod.lean](Time/PolyTimeSubmod.lean), [Time/PolyTimeLS.lean](Time/PolyTimeLS.lean), [Time/PolyTimeTrial.lean](Time/PolyTimeTrial.lean), [Time/PolyTimeCore.lean](Time/PolyTimeCore.lean), [Time/Accuracy.lean](Time/Accuracy.lean), [Time/RunTime.lean](Time/RunTime.lean) | The budget and the number of trials; polynomial-time certificates for the exact computations, the samplings, the submodular step, the local search, a trial and the core, with one degree for every `N`; `N` from `ε`; the running time. |

The local search, with a fixed `N = 201` and a polynomial budget, also serves Part I for large
`ε` (`BCFGJPSSV26.Stable.costF_localSearch_le`, `BCFGJPSSV26.Stable.localSearch_polytime'`).
