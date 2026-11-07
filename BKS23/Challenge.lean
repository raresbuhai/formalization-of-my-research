module

public import BKS23.Model

/-!
# Main results: statements

The main results of [BKS23], with proofs `sorry`. `lake comparator` checks that `Solution.lean`
proves exactly the statements listed in `comparator.json`, using only the axioms listed there.

What a reader has to trust is this file and what it imports: the definitions in
`BKS23/Model.lean` (the semi-random model, randomized algorithms, inputs and outputs), the
encodings in `Background/Encoding.lean`, CSLib's multitape Turing machines, and Mathlib.

Both parts of [BKS23, Theorem 5.6] are stated here. Numbers are those of the arXiv version (v2).
`Solution.lean` proves both, and `lake comparator` checks them (`comparator.json`).

## Conventions of both parts

* **The planted set is arbitrary.** In [BKS23, Definition 1.1] the planted set `S*` is a uniformly
  random `k`-set; here the guarantee holds for every `k`-set `S*`, which is stronger: averaging
  over `S*` gives the paper's statement. (The proofs use only the randomness of the edges between
  `S*` and the other vertices.)
* **The edge probability.** The graph is drawn from `FK(n, k, p)` for a real `p ∈ [0, 1)`. The
  algorithm is given `n`, `k` and the adjacency bits of `G` (`BKS23.input`), but not `p`. This is
  stronger than the paper, whose algorithms use `p` (see each part).
  * `p` may depend on `n`: one algorithm, one `δ` and one threshold for "large enough `n`" serve
    every `p`, so `p` may be any function of `n`.
* **Running time.** The algorithm `A` runs in time `O((N + 2)^d)` on inputs of encoded length `N`
  (`BKS23.RunsInTime` with `T N = (N + 2)^d`), for a natural number `d ≥ 1`. The input of a graph
  on `n` vertices with `k ≤ n` has length `n (n - 1) / 2 + O(log n)`, so this is `n^O(d)`.
  * The time bound is an explicit polynomial, not any function bounded by one: the algorithm is
    given exactly `T N` coins and may read them all, so the length of its coin string would pass
    it `T N`, which for an arbitrary `T` could be advice no machine computes.
* The algorithm needs `k`: it looks for cliques of size `k`, and so do the paper's algorithms.
* `o(1)` is a function `δ` of `n` tending to `0`.
* "With probability at least `0.99`" is for all large enough `n`, every real `p ∈ [0, 1)`, every
  `k` with the size condition and `k ≤ n`, every planted `k`-set `S*` and every adversary. The
  probability is over the random graph and the algorithm's coins (`BKS23.successProb`).

## Theorem 5.6 (1)

[BKS23, Theorem 5.6 (1)]: for every `ε > 0` and `p, 1 - p ≥ n^(-(1 - ε))`, there is an algorithm
that, given a graph `G` on `n` vertices, runs in polynomial time, such that if `G` is drawn from
`FK(n, k, p)` with `k ≥ max{O(n^(2/3) p^(1/3) / (1 - p)^(2/3)), Õ(n^(1/2))}`, then with
probability at least `0.99` it outputs a list of at most `(1 + o(1)) n / k` cliques of size `k`,
one of which is the planted clique. Its proof uses the degree-4 spectral certificate of
[BKS23, Lemma 4.13] where part (2) uses certificates of degree `O(1/ε)`, and refines the rounded
sets [BKS23, Claim 5.9] before the cleanup.

It does not follow from part (2). There, `k ≤ n` and `k ≥ n^(1/2 + ε) / (1 - p)^(1/ε)` with
`ε ≤ 1/10` force `1 - p ≥ n^(-1/20)`, and `k` near `√n` needs a small `ε`, hence time `n^O(1/ε)`
with a large exponent. Here `1 - p` may be as small as order `n^(-1/2)`, and one polynomial serves
`k` down to `C √n log n` when `p` is at most about `(log n)³ / √n`.

Formally (`BKS23.semirandom_planted_clique_two_thirds`):

* **The size condition** is `C max{n^(2/3) p^(1/3) / (1 - p)^(2/3), √n log n} ≤ k ≤ n` for a
  constant `C`. The polylogarithmic factor of `Õ(n^(1/2))` is one factor `log n`, which the
  cleanup needs: [BKS23, Lemma 5.8] bounds the list by `(1 + 2nΔ/k²) n / k`, with a threshold `Δ`
  of order `log n` when `p ≤ 1/2`. Logarithms are natural; the base only changes `C`.
* **No `ε`**: the guarantee holds for every real `p ∈ [0, 1)`. This is stronger than the paper,
  whose proof uses `p, 1 - p ≥ n^(-(1 - ε))` to bound the entries of the `p`-biased adjacency
  matrix of the cut of `S*` by `n^(1/2 - ε/2)`, for the spectral norm bound [BKS23, Fact 3.14].
  The hypothesis is not needed, and the entries are `O(n^(1/4))` in every case:
  * the size condition gives `(1 - p)² ≥ C³ n² p / k³`, so when `p ≥ 1/2`,
    `1 - p ≥ C^(3/2) n / (√2 k^(3/2)) ≥ C^(3/2) / √(2n)`;
  * `p < n^(-1/2)` reduces to `p = n^(-1/2)`, for which the size condition follows from
    `k ≥ C √n log n` for large `n`: `G(n, p)` lies inside `G(n, n^(-1/2))` under the monotone
    coupling, and edges between `S*` and the other vertices may be deleted anyway. (Part (2)
    reduces `p ≤ 1/2` to `p = 1/2` in the same way.)
* **`p` is not given.** The paper's algorithm uses `p` in its rounding threshold `1 - 2δ` with
  `δ = (1 - p)/24`, in its refinement threshold `(1 - (1 - p)/6) k - 1` (after
  [BKS23, Claim 5.9]), and in its cleanup threshold `O(log n / log(1/p))`. None is needed: round at
  threshold `1/2`; refine to the `k` vertices with the most neighbors in the rounded set (on the
  good event, every vertex of `S*` has more than every other vertex); and clean up with a
  threshold `O(log n · (1 + k^(3/2) / n))`, which exceeds `3 log n / log(1/p)` for every
  admissible `p` by the bound on `1 - p` above.
* **Polynomial time**: one exponent `d` serves every `p` and `k`.

## Theorem 5.6 (2)

[BKS23, Theorem 5.6 (2)]: for every small enough `ε > 0` there is an algorithm that, given a graph
`G` on `n` vertices, runs in time `n^O(1/ε)`, such that if `G` is drawn from `FK(n, k, p)` with
`k ≥ n^(1/2 + ε) / (1 - p)^(1/ε)`, then with probability at least `0.99` it outputs a list of at
most `(1 + o(1)) n / k` cliques of size `k`, one of which is the planted clique. The main result
as stated in the introduction, [BKS23, Theorem 1.2], follows from the case `p = 1/2` with `ε/2`
in place of `ε`, since `n^(1/2 + ε) ≥ 2^(2/ε) n^(1/2 + ε/2)` for large `n`.

Formally (`BKS23.semirandom_planted_clique`):

* **`ε ≤ 1/10`.** The paper's "small enough": its proof takes `ε ≤ 0.1`.
* **The size condition** `n^(1/2 + ε) / (1 - p)^(1/ε) ≤ k ≤ n` is the paper's, in terms of `p`.
* **`p` is not given.** The paper's algorithm uses `p` only in its final cleanup: two candidate
  cliques sharing more than `O(log n / log(1/p))` vertices are not both kept. Knowing `p` is not
  needed there: `k ≤ n` and the size condition give `1 - p ≥ n^(-ε (1/2 - ε))`, so a threshold
  depending on `n` and `ε` alone works for every admissible `p`.
* **Running time `n^O(1/ε)`**: the exponent satisfies `d ≤ C / ε` for one constant `C` and every
  `ε`: it is uniformly `O(1/ε)`, and the constant factor may depend on `ε`.
* `δ` and the threshold for "large enough `n`" may depend on `ε`.

-/

public section

namespace BKS23

open Filter Topology

/-- **Theorem 5.6 (1)** of [BKS23]: semi-random planted clique can be solved in polynomial time,
in the list-decoding sense, for cliques of size `k ≥ O(n^(2/3) p^(1/3) / (1 - p)^(2/3))` and
`k ≥ O(√n log n)`, by an algorithm that is not given the edge probability `p`. -/
theorem semirandom_planted_clique_two_thirds :
    ∃ (A : Input × List Bool → Output) (d : ℕ),
      1 ≤ d ∧ RunsInTime A (fun N ↦ (N + 2) ^ d) ∧
      ∃ C : ℝ, ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
          C * max ((n : ℝ) ^ (2 / 3 : ℝ) * p ^ (1 / 3 : ℝ) / (1 - p) ^ (2 / 3 : ℝ))
            (√(n : ℝ) * Real.log n) ≤ k → k ≤ n →
          ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
            0.99 ≤ successProb n k p S Adv A (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) :=
  sorry

/-- **Theorem 5.6 (2)** of [BKS23]: semi-random planted clique can be solved, in the list-decoding
sense, for cliques of size approaching `√n`. -/
theorem semirandom_planted_clique :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
      ∃ (A : Input × List Bool → Output) (d : ℕ),
        1 ≤ d ∧ (d : ℝ) ≤ C / ε ∧ RunsInTime A (fun N ↦ (N + 2) ^ d) ∧
        ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
          ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
            (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k → k ≤ n →
            ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
              0.99 ≤ successProb n k p S Adv A (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) :=
  sorry

end BKS23
