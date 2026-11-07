# Files from project-k-median

These files are copied from the project `bound-195` of
[`epfl-thl2/project-k-median`](https://github.com/epfl-thl2/project-k-median), at commit
`d87e2a20376896ab72fe005a493b3af970a0f82d`. All of their code was written by Codex. Like the rest
of this repository, they are released under Apache-2.0 (see [LICENSE](../../LICENSE)). That
repository is on Lean and Mathlib 4.30.0-rc1, so it cannot be a dependency here.

They prove the bound on the factor-revealing program in *A Better-than-2 Approximation for
k-Median*, Part I: *The Power of General Bids*
([arXiv:2610.18144](https://arxiv.org/abs/2610.18144)). This is Theorem 4.4: for every `γ ∈ [1, 1.224]`, the program of Definition 4.1 with the bid
`β_γ(α, d) = [α - γ d]^+` has value at most `2 - (γ - 1)^2` in every dimension `n ≥ 1`.

```lean
theorem KMedian195.originalPrimalUpperBound_exact
    (gamma : ℝ) (hγlo : 1 ≤ gamma) (hγhi : gamma ≤ (153 : ℝ) / 125) :
    OriginalPrimalUpperBound gamma (2 - (gamma - 1) ^ 2)
```

`KMedian195.originalPrimalUpperBound_195` is the case `γ = 1.224`, with the bound
`2 - 0.224^2 = 1.949824` rounded up to `1.95`. [`Program.lean`](Program.lean) defines the program
(`KMedian195.OriginalPrimalSolution`, with `Feasible` and `objective`) and the statement
`OriginalPrimalUpperBound`, and explains how its indices match the paper's.
[`Main.lean`](Main.lean) contains the two theorems. For `1 < γ ≤ 1.224` the proof is by dual
fitting. The case `γ = 1` follows by continuity in `γ`.

The module names and the namespace `KMedian195` are the source's. Each file starts with a comment
giving its source and its changes. In short:

* `Program.lean` is the source's `Challenge.lean`, the statements that its comparator checks,
  without the two theorems. The source defines these declarations twice: there and in the
  development. Here they are defined only once, and `Basic.lean` and `FactorRevealingPrimal.lean`
  import them.
* `Main.lean` holds the last three theorems of `FactorRevealingPrimal.lean`, including the two of
  the source's `Challenge.lean` and `Solution.lean`.
* Changes for our Lean and Mathlib:
  * Deprecated and renamed lemmas: `if_pos`, `if_neg`, `dif_pos`, `dif_neg`, `if_true`,
    `Set.mem_setOf_eq`, `continuous_finset_sum` and similar. The case of `Nat.strong_induction_on`
    is now called `ind`.
  * In 69 places, `simpa ... using e` is changed to `simpa ... using! e`. Our Lean's
    `simpa using` compares the simplified `e` with the goal up to reducible unfolding only.
    `using!` compares them the way it did before.
  * A few local repairs in `GoodAdvice.lean` and `UpperBound.lean`: two `erw`, an implicit
    argument given explicitly, a `simp only` followed by `exact`, and one more `simp` lemma.
* All files: module headers (`module`, `public import`, `@[expose] public section`). The imports
  are the source's own imports of parts of Mathlib, with `Mathlib.Data.Real.Basic` replaced by
  `Mathlib.Basic.Real.Basic`.

The library's entry in `lakefile.toml` keeps the source's auto-bound implicit arguments
(`autoImplicit = true`). It also turns off the linter for overlapping instance arguments, which
flags 124 declarations in `GoodAdvice.lean` that take `[NeZero n]` both from a `variable` and
from their own binders.
