# BKS23: Algorithms approaching the threshold for semi-random planted clique

The main results are the two parts of [BKS23, Theorem 5.6]. Part (2) is stated in
[Challenge.lean](Challenge.lean) as `BKS23.semirandom_planted_clique`. For every `0 < ε ≤ 1/10`
there is an algorithm running in time `O((N + 2)^d)`, `d ≤ C/ε`, on inputs of length `N`, that,
given `n`, `k` and a graph from `FK(n, k, p)` with `k ≥ n^(1/2+ε) / (1 - p)^(1/ε)`, but not `p`,
lists at most `(1 + o(1)) n / k` cliques of size `k`, one of them the planted one, with
probability at least `0.99`, for every planted set.

The main result of the introduction, [BKS23, Theorem 1.2], follows from the case `p = 1/2` with
`ε/2` in place of `ε`. The sum-of-squares algorithm it uses, [BKS23, Fact 3.6], is proved too, in
[SumOfSquares](../Background/SumOfSquares/README.md) (`SoS.Solver.exists_solver`).

Part (1) is stated as `BKS23.semirandom_planted_clique_two_thirds`. It gives one polynomial-time
algorithm, not given `p`, with the same guarantee for every `p ∈ [0, 1)` and
`k ≥ 32 max{n^(2/3) p^(1/3) / (1 - p)^(2/3), √n log n}`. Part (2) does not imply it: there
`1 - p ≥ n^(-1/20)`, and the time is `n^O(1/ε)` for `k ≥ n^(1/2+ε)`.
[Challenge.lean](Challenge.lean) explains how the statement differs from the paper's: it has no
`ε`, and the algorithm is not given `p`.

Both theorems are proved in [Solution.lean](Solution.lean), with only the standard axioms, and
`lake comparator` checks them.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route.

## The statement

* **The model** ([Model.lean](Model.lean), `BKS23.Adversary`): the Feige–Kilian semi-random model.
  A `k`-set `S*` gets a clique, added to `G(n, p)`; an adaptive adversary then deletes any edges
  between `S*` and the rest and replaces the graph on the other vertices. The planted set is an
  arbitrary `k`-set, and the theorem holds for every one. The probability is over the random
  graph and the coins.
* **`p` is real and not given.** The algorithm's input is `n`, `k` and the adjacency bits; the
  guarantee holds for every real `0 ≤ p < 1`.
* **Running time.** `O((N + 2)^d)` on inputs of length `N`: for part (1) with one `d`, for part
  (2) with `1 ≤ d ≤ C/ε` for one constant `C` and every `ε`. The input of a graph on `n` vertices
  has length `n (n - 1) / 2 + O(log n)`, so this is `n^O(1)` and `n^O(1/ε)`. The explicit
  polynomial `T N = (N + 2)^d` is also the number of coins, which rules out advice through the
  coin string's length.
* **Uniformity.** For part (1), and for part (2) for each `ε`, one algorithm, one `δ` and one
  threshold for "large enough `n`" serve every `p`, every `k`, every `S*` and every adversary, so
  `p` may be any function of `n`.

## Map of the proof

| Files | Content |
| --- | --- |
| [Model.lean](Model.lean), [Challenge.lean](Challenge.lean) | The Feige–Kilian semi-random model `FK(n, k, p)`, randomized algorithms on Turing machines, and the statement. |
| [Random.lean](Random.lean), [../Background/RandomGraph.lean](../Background/RandomGraph.lean) | **Probability in the model**, on Mathlib's `G(V, p)` (`SimpleGraph.binomialRandom`). `G(V, p)` is the graph of independent coins on the pairs; `erdosRenyiProb` is its mass function, so `successProb` is an integral (`Random.successProb_eq`). Monotonicity in `p` by the coupling through uniform variables (`binomialRandom_le_of_antitone`). The law of the cut: independent blocks of independent coins (`map_cut_binomialRandom`). The first moment of `lem:clique-intersection` (`prob_not_noBiclique`). Hoeffding is Mathlib's (`measure_sum_ge_le_of_iIndepFun` with Hoeffding's lemma). The generic parts are in `Background/` and exported as `BKS23.Random.*`. |
| [../Background/SumOfSquares/Normed.lean](../Background/SumOfSquares/Normed.lean), [../Background/SumOfSquares/Boolean.lean](../Background/SumOfSquares/Boolean.lean) | **SoS facts with norms.** Proofs with bounded multipliers and equalities; Boolean identities, `x_S ≥ 0`, `x_S x_T ≥ 0`, and the expansion `(∑ xᵢ)^t = ∑_m a(t, m) e_m`; fourth-power Jensen (`isSOS_jensen`). |
| [Biclique.lean](Biclique.lean) | **Biclique certificates, deterministic**: the key lemma, the lower-bound trick, cancellation for `t = 2` (an identity, inside `Axioms.vertex`), and the certificate `e_m⁴ \|y\| ≤ \|V\| (Γ/λ)⁴` at each level, for characters `u_S(v)` with diagonal sums `≤ Γ`, balancedness `≤ Δ` and degree bound `d`. |
| [Certificate.lean](Certificate.lean) | `\|x\|^(4t) \|y\| ≤ F_t⁴ \|V\| c⁴` in degree `8t + 6` (`Axioms.certificate`), and its instance for `p`-biased characters (`Axioms.certificate_pBiased`), which leaves only balancedness and the degree bound to the random graph. |
| [RandomCut.lean](RandomCut.lean) | **The certificates' hypotheses for random graphs.** For every fixed planted set `U`, the cut of `G(V, p)` is balanced with `Δ_m = M^m √(2 \|V\| log(t \|U\|^(2m) / δ))` (`prob_not_balanced`) and has degrees at most `\|U\| p + √(2 \|U\| log(\|V\| / δ))` (`prob_not_degreeLE`), each failing with probability at most `δ`. For `p ≤ 1/2`, `G(V, p)` lies inside a graph whose cut is good for `p = 1/2` (`prob_not_le_good_half`). |
| [CliqueProgram.lean](CliqueProgram.lean), [Rounding.lean](Rounding.lean) | **Rounding with an approximate pseudo-distribution.** The clique program as a solver input: valid, with the planted point, and containing the biclique axioms of every graph containing the cut (`Clique.axioms`), so the certificate is a proof from the solver's system. Approximate soundness for proofs with bounded multipliers (`SoS.DerivesN.approx_ge`); maximal coverage by mixing with the planted point (`SoS.PseudoExpectation.mix`); `Ẽ[s^T] ≥ Ẽ[s]^T - errH` for every `T` by the tangent line (`Rounding.holder`); and averaging: some `T`-tuple `Q` has `S_Q = S*` exactly (`Rounding.exists_round_eq`), with threshold `1/2`. |
| [Cleanup.lean](Cleanup.lean), [../Background/Pruning.lean](../Background/Pruning.lean) | **Cleanup.** Keep the `k`-cliques, prune greedily with threshold `Δ`. The planted clique survives when every other `k`-clique meets it in fewer than `Δ` vertices, which `NoBiclique` gives (`card_inter_lt`, `mem_cleanup`). The list has at most `(n/k)(1 + 2nΔ/k²)` sets (`length_cleanup_le`), by Corrádi's lemma. |
| [Algorithm.lean](Algorithm.lean), [AlgorithmPolyTime.lean](AlgorithmPolyTime.lean) | **The algorithm on Turing machines.** Read the non-edges from the adjacency bits; build the clique program of degree `8t + 6` on vertex numbers (`Algorithm.problemN`, equal to `Clique.problem`); run `SoS.Core.core` with `η = 2^-e`, `γ = 2^-2e`, `e = (n + 2)^4 (t + 1)`; read `Ẽ[w_Q]` and `Ẽ[w_Q wᵢ]` from the moments for all `n^(4t)` tuples `Q`; form `S_Q`; clean up on lists with `Δ = ⌈n^(1/(2t))⌉`. Correctness (`Algorithm.alg_spec`): the output's `k`-cliques, membership of every surviving `S_Q`, and the list size, with the solver's `Ẽ`. Polynomial time uniformly in `t` and the budget (`Algorithm.run_polytime`), and time `c_t ((N + 2)^(E (t + 1)) + \|(x, r)\|)` with the solver's budget (`Algorithm.exists_alg_inO`). |
| [SpectralDefs.lean](SpectralDefs.lean), [SpectralWalks.lean](SpectralWalks.lean), [SpectralNorm.lean](SpectralNorm.lean) | **The norm of the cut** [BKS23, Fact 3.14], for part (1). The centred cut matrix `M_uv = 𝟙[u ∼ v] - q` of `G(n, q)` has `‖M‖² ≤ 18 n q (1 - q)` except with probability `n / 2^r`, when `charMax q (2r + 1)⁴ ≤ n` for `r = 2^ℓ` (`Spectral.prob_not_normLE`). The proof is the moment method. `‖X y‖^(2r) ≤ ‖y‖^(2r) tr(X^(2r))` for the symmetric matrix of characters, by iterated Cauchy–Schwarz (`Spectral.pow_dotProduct_le`). By independence, the mean of the product along a closed walk vanishes unless every edge is traversed at least twice (`Spectral.integral_walkProd`). Counting such walks with weighted step types and a potential on the open edges gives `E tr(X^(2r)) ≤ n (9n)^r` (`Spectral.Walk.bound_le`). Markov finishes. |
| [SpectralCertificate.lean](SpectralCertificate.lean) | **The spectral certificate** [BKS23, Lemma 4.13]: from `‖M‖² ≤ Λ`, the clique program proves `\|x\| \|y\| ≤ Λ / (1 - q)²` in degree `6` (`Spectral.certificate_spectral`). The ingredients are the edge axioms (`xᵀ M y = (1 - q) \|x\| \|y\|`), Lagrange's identity, the positive semidefinite form `Λ ‖y‖² - ‖M y‖²` as a sum of squares (`Spectral.isSOS_of_sum_sq_le`), Booleanity, and cancellation. |
| [Rounding1.lean](Rounding1.lean), [Refine.lean](Refine.lean), [NonNeighbors.lean](NonNeighbors.lean) | **Rounding near the planted clique, and refinement** [BKS23, Theorem 5.1 with `δ = (1 - p)/24`, Claim 5.9]. Some `S_i = {j \| Ẽ[wᵢ] ≤ 2 Ẽ[wᵢ wⱼ]}` differs from `S*` in at most `8 ω (n/k²)` vertices, plus errors (`Rounding.exists_round_near_eq`). If every vertex outside `S*` has more non-neighbours in `S*` than that, the vertices with at least `τ` neighbours in `S_i` are `S*` for some `τ` (`Refine.exists_threshold`). The random graph gives at least `(1 - q) k / 2` non-neighbours, by the Chernoff bound for the lower tail (`Random.prob_not_nonNbrGE`); Hoeffding is too weak when `1 - q` is near `n^(-1/2)`. |
| [Algorithm1.lean](Algorithm1.lean), [Algorithm1PolyTime.lean](Algorithm1PolyTime.lean) | **The algorithm of part (1).** The clique program of degree `6`; the `n` sets `S_i`; their refinements at every threshold `τ ≤ n`; and the cleanup with `Δ = ⌊k² / (n (log₂ n + 1))⌋ + 1`. Correctness (`Algorithm.alg1_spec`) and polynomial time (`Algorithm.exists_alg1_inO`, with the threshold in binary). |
| [Size1.lean](Size1.lean), [Assembly1.lean](Assembly1.lean) | **Assembly of part (1).** The graph is analysed at `q = max(p, 1/√n)`: for `p < 1/√n`, `G(n, p)` lies inside `G(n, q)` by the coupling (`Assembly1.prob_not_exists_le`), and the size condition still holds at `q` by `k ≥ 32 √n log n`. At `q`, the characters are at most `√n` (`Size1.charMax_le`) and `(1 - q) k ≥ √n / 2` (`Size1.q_facts`). The algorithm succeeds on a good cut for every coin string (`Assembly1.succeeds1_of_good`). The conditions on `n` alone (`Size1.Large`) hold for all large `n` (`Size1.eventually_large`). The failure probabilities, from the norm, the non-neighbours and the bicliques, add to `1/100` (`Assembly1.le_successProb1`). |
| [Assembly.lean](Assembly.lean), [Solution.lean](Solution.lean) | **Assembly of part (2).** The parameters (`t = ⌊3/(8ε) - 1/2⌋ + 1`, `Assembly.tOf_spec`). Deterministically, on a good cut and with the numerical conditions, the algorithm succeeds for every coin string (`Assembly.succeeds_of_good`); the conditions reduce to conditions on `n` alone, uniformly in `p` and `k` (`Assembly.Large`, `Assembly.succeeds_of_large`), which hold for all large `n` (`Assembly.eventually_large`). The failure probabilities add to `1/100` (`Assembly.le_successProb_of_large`). The running time is `Algorithm.exists_alg_inO` with `d = E (t + 1) + 1 ≤ (E + 1)/ε`. Both theorems are checked by `lake comparator` ([comparator.json](comparator.json)). |

*Formalized by [Claude Code](https://claude.com/claude-code).*
