module

public import BBKS24.Model

/-!
# Main result: statement

The main result of [BBKS24], with proof `sorry`. `lake comparator` checks that `Solution.lean`
proves exactly this statement using only the axioms listed in `comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BBKS24/Model.lean` (the semirandom model, randomized algorithms, inputs and outputs), the
encodings in `Background/Encoding.lean`, CSLib's multitape Turing machines, and Mathlib.

## Theorem 4.1, and Theorem 1.2

Numbers are those of the arXiv version (v2).

[BBKS24, Theorem 4.1]: there is an `O(n^(ω + 1/2))`-time algorithm that takes as input a graph `G`
generated according to `SRPC(n, k, p)` for any `k ≥ O(√n log² n · max(1, (p/(1 - p))⁴))` and with
probability at least `0.99` outputs a list of size `(1 + o(1)) n / k` of `k`-cliques containing the
planted clique in `G`.

The main result as stated in the introduction, [BBKS24, Theorem 1.2] (= Theorem 3.1), is the case
`p = 1/2`, where the condition is `k ≥ O(√n log² n)`.

Formally (`BBKS24.semirandom_planted_clique`):

* **The model.** `SRPC(n, k, p)` (`BBKS24.Adversary`): the planted set `S*` is an arbitrary
  `k`-set, and the statement holds for every one; the edges between `S*` and the other vertices
  are random, and the adversary may not delete them; the graph on the other vertices is chosen by
  an adaptive adversary.
* **The edge probability.** `p` is any real number with `0 ≤ p < 1`, and the algorithm is not
  given it: its input is `n`, `k` and the adjacency bits of `G` (`BBKS24.input`), as in [BKS23].
  * This is stronger than the paper, whose algorithm uses `p`: to rescale the adjacency matrix to
    the `p`-biased characters, in its threshold, and in its final cleanup. Not knowing `p` also
    avoids any question of how a real `p` would be given to a Turing machine.
  * `p = 0` is allowed; the paper's characters need `0 < p`.
  * `p` may depend on `n`: one algorithm, one `C`, one `δ` and one threshold for "large enough
    `n`" serve every `p`, so `p` may be any function of `n`.
* **`k ≥ O(√n log² n · max(1, (p/(1 - p))⁴))`**: there is a constant `C` such that the guarantee
  holds whenever `C √n (log n)² max(1, (p/(1 - p))⁴) ≤ k ≤ n`, for all large enough `n`.
  Logarithms are natural; the base only changes `C`. For `p = 1/2` the condition is
  `C √n (log n)² ≤ k ≤ n`, which is Theorem 1.2.
* **Running time.** The paper's `O(n^(ω + 1/2))` is a bound in the word RAM with fast matrix
  multiplication (`ω ≤ 2.372`); multitape Turing machines do not multiply matrices in that time, so
  the formal statement asks for polynomial time: `A` runs in time `O((N + 2)^d)` on inputs of
  encoded length `N` (`BBKS24.RunsInTime` with `T N = (N + 2)^d`), for some natural number
  `d ≥ 1`. The input of a graph on `n` vertices with `k ≤ n` has length `n (n - 1) / 2 + O(log n)`.
  * The time bound is an explicit polynomial, not any function bounded by one: the algorithm is
    given exactly `T N` coins and may read them all, so the length of its coin string would pass
    it `T N`, which for an arbitrary `T` could be advice no machine computes.
* The algorithm needs `k`: it looks for cliques of size `k`, and so does the paper's algorithm.
* `o(1)` is a function `δ` of `n` tending to `0`.
* "With probability at least `0.99`" is for all large enough `n`, every real `p ∈ [0, 1)`, every
  `k` in the range, every planted `k`-set `S*` and every adversary. The probability is over the
  random edges and the algorithm's coins (`BBKS24.successProb`).
-/

public section

namespace BBKS24

open Filter Topology

/-- **Theorem 4.1** of [BBKS24], which contains **Theorem 1.2** (Theorem 3.1) as the case
`p = 1/2`: semirandom planted clique can be solved, in the list-decoding sense, in polynomial time
for cliques of size `k ≥ O(√n log² n · max(1, (p/(1 - p))⁴))`, by an algorithm that is not given
the edge probability `p`. -/
theorem semirandom_planted_clique :
    ∃ (A : Input × List Bool → Output) (d : ℕ),
      1 ≤ d ∧ RunsInTime A (fun N ↦ (N + 2) ^ d) ∧
      ∃ C : ℝ, ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
          C * √(n : ℝ) * Real.log n ^ 2 * max 1 ((p / (1 - p)) ^ 4) ≤ k → k ≤ n →
          ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
            0.99 ≤ successProb n k p S Adv A (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) :=
  sorry

end BBKS24
