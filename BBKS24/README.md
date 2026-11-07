# BBKS24: Semirandom planted clique and the restricted isometry property

The main result is [BBKS24, Theorem 4.1], stated in [Challenge.lean](Challenge.lean) as
`BBKS24.semirandom_planted_clique`, with the running time formalized as polynomial rather than
the paper's specific `O(n^(ω + 1/2))` (see [Running time](#the-statement) below). In the
semirandom model `SRPC(n, k, p)` of
[Charikar, Steinhardt and Valiant](https://arxiv.org/abs/1611.02315), a simple greedy algorithm
lists at most `(1 + o(1)) n / k` cliques of size `k`, one of them the planted one, with probability
at least `0.99`, whenever `k ≥ O(√n log² n · max(1, (p/(1-p))⁴))`. The theorem is proved in
[Solution.lean](Solution.lean), with only the standard axioms, and `lake comparator` checks it.

Its case `p = 1/2` is [BBKS24, Theorem 1.2 (= Theorem 3.1)], the main result of the
introduction.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route.

## The statement

* **The model** ([Model.lean](Model.lean), `BBKS24.Adversary`): the planted set `S*` is an
  arbitrary `k`-set and the theorem holds for every one; the edges between `S*` and the rest are
  random and cannot be deleted (unlike in [BKS23](../BKS23)); the rest of the graph is adaptive and
  adversarial. The probability is over the random edges and the coins.
* **`p` is real and not given.** The algorithm's input is `n`, `k` and the adjacency bits, as in
  [BKS23](../BKS23); the guarantee holds for every real `0 ≤ p < 1`. The paper's algorithm uses
  `p`; ours tries a grid of guesses for it. `p = 0` is included.
* **Running time.** The paper's `O(n^(ω + 1/2))` is a word-RAM bound with fast matrix
  multiplication. On multitape Turing machines the theorem asks for polynomial time,
  `O((N + 2)^d)` on inputs of length `N`, with the explicit polynomial `T N = (N + 2)^d` as the
  number of coins (as in [BKS23](../BKS23), to rule out advice through the coin string's length).
* **Uniformity.** One `C`, one `δ` and one threshold for "large enough `n`" serve every `p`,
  every `k`, every `S*` and every adversary, so `p` may be any function of `n`.

## Map of the proof

| Files | Content |
| --- | --- |
| [Model.lean](Model.lean), [Challenge.lean](Challenge.lean) | The model `SRPC(n, k, p)`, randomized algorithms on Turing machines, and the statement. |
| [SparseNorm.lean](SparseNorm.lean), [SparseNorm/](SparseNorm) | The sparse operator norm bound for independent rows of a bounded orthonormal system (`sparse_norm_bound`), following Haviv–Regev: tail bounds (`Tail`), Maurey's sampling (`Maurey`), the scales (`Levels`), the Chernoff event and the union bound over nets (`Core`), the parameters (`Params`). Lemma 3.3 (`card_lt_of_sparseNormLE`, `few_large_correlations`). |
| [Statistic.lean](Statistic.lean) | The statistic, the selected and refined sets, and recovery from a good cut, deterministically (`exists_refine_eq`: Lemmas 3.2, 3.5, 3.6, 4.2–4.4). |
| [Events.lean](Events.lean) | The probability that the cut is good (`prob_goodCut`). |
| [Recovery.lean](Recovery.lean) | Recovery with probability `1 - 1/400` for all large `n` (`eventually_recovers`). |
| [../Background/RandomGraph.lean](../Background/RandomGraph.lean), [../Background/Pruning.lean](../Background/Pruning.lean), [../Background/Sampling.lean](../Background/Sampling.lean) | Shared with [BKS23](../BKS23): `G(V, p)` as coins on the pairs, the cut and its law, characters, total variation (`abs_binomialRandom_sub_le`), bicliques (`prob_not_noBiclique`); the pruning and Corrádi's bound; chunks of coins and the law of the augmented graph (`sum_mass_coins_sup`). |
| [GraphList.lean](GraphList.lean), [Algorithm.lean](Algorithm.lean) | The algorithm on lists (`Alg.alg`) and what it outputs (`Alg.alg_spec`). |
| [PolyTime.lean](PolyTime.lean), [RunTime.lean](RunTime.lean) | Polynomial-time certificates (`Alg.algN_polytime`) and the running time (`Alg.exists_runsInTime`). |
| [Assembly.lean](Assembly.lean), [Solution.lean](Solution.lean) | The success probability (`Asm.le_successProb`, `Asm.eventually_le_successProb`) and the theorem, checked by `lake comparator` ([comparator.json](comparator.json)). |

*Formalized by [Claude Code](https://claude.com/claude-code).*
