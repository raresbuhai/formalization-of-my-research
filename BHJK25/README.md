# BHJK25: The quasi-polynomial low-degree conjecture is false

The results are the two counterexamples of [BHJK25]: Theorem 2.1 (Theorem 1.3 in the
introduction), a permutation-invariant distribution on Boolean tensors with vanishing low-degree
advantage that a quasi-polynomial-time algorithm tells apart from uniform after noise, and
Theorem 3.1 (Theorem 1.6), rotation-invariant distributions on matrices with small low-degree
advantage that the top eigenvalue tells apart after noise. They are stated in
[Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them.
Theorem 3.1 is stated for an algorithm that reads rational approximations of the matrix, and for
the paper's explicit distributions rather than "there exist".

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v1). The paper appeared at FOCS 2025, hence the key.

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 2.1 | `reed_solomon_counterexample` | For every `k ≥ 2` and small enough `ε > 0` there is an `S_n`-invariant distribution `P_n` on symmetric `k`-tensors with entries in `{0, 1}` that agrees with the uniform distribution `Q_n` on every polynomial of degree at most `n^(1 - 6ε)`, while an algorithm running in time `n^O(log^(1/(k-1)) n)` answers `0` on `Q_n` and `1` on `T_ε P_n`, each with probability `1 - exp(-n^(1 - O(ε)))`. |
| Theorem 3.1 | `top_eigenvalue_counterexample` | The null and planted distributions `U diag(λ) Uᵀ` of the paper (with `m = n`, `γ = C log² n / n`, `λ* = γ log n`, every `C > 0`) are rotation-invariant probability distributions; for every `b` the advantage at degree `n^(1/3) / log^a n` is at most `1 / log^b n` for some `a`; and a polynomial-time algorithm that reads any rational matrix within `1/n` of the real one in every entry answers `0` on the null distribution with probability `1`, and `1` on the noisy matrix `(1 - ε) M₁ + ε M₀` with probability `1 - n^(-e)` for every `e`. |

* **The low-degree advantage** (`BHJK25.AdvantageAtMost`) is Definition 1.1 as an inequality,
  `E_P f - E_Q f ≤ δ √(Var_Q f)` for every polynomial `f` of degree at most `D`, with the
  expectations finite; Theorem 2.1 is the case `δ = 0`.
* **Algorithms** are deterministic multitape Turing machines (`BHJK25.RunsInTime`).
* **Theorem 2.1** keeps the paper's existential `P_n` and its degree `n^(1 - 6ε)`. "Small enough
  `ε`" and `n^(1 - O(ε))` are `ε ≤ ε₀` and `n^(1 - Kε)` for absolute constants, and the exponent
  of the running time does not depend on `ε`. The noise `T_ε` replaces each entry by a uniformly
  random bit with probability `ε`.
* **Theorem 3.1** names the distributions, with the parameters of the paper's proof; `γ` is capped
  at `1`, which matters only for small `n`. The guarantee holds for every rational
  approximation: with the stated probability, the algorithm is correct on every rational matrix
  within `1/n` of the real one in each entry. The algorithm is the same for every `C` and `ε`.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### Theorem 2.1: the construction

The proof chooses `P_n` ([RS/Defs.lean](RS/Defs.lean)) with `T = ⌈1/(6ε)⌉`, `K = 6` and
`ε₀ = 1/30`. Field elements have `r = c + ⌈c/(2T)⌉ + 4` bits (`c = ⌈log₂ n⌉`), so the field has
`q ≥ 16 n^(1 + 1/(2T))` elements, and the hidden polynomial has `m = 2^⌈(1 - 1/T) c⌉ ≥ n^(1 - 1/T)`
coefficients. The field is `F₂[U]/(f)` for the first monic `f` of degree `r` whose quotient has
no zero divisors, with complexitylib's arithmetic on coefficient lists; the existence of such an
`f` comes from the Galois field of order `2^r`. A field element is written on `r` cells of a grid
of `ℓ^(k-1)` cells, as in Definition 2.13; every vertex outside the `2(k - 1)ℓ` row vertices is a
column.

The construction is a probability distribution and invariant under relabelling
([RS/Construction.lean](RS/Construction.lean)). Every set of at most `m` entries is uniformly
distributed (Lemma 2.10), which gives the vanishing advantage. The proof counts with flips: for
every such set, some entry can be toggled by an injective map that fixes the others. For a `β`
value at a unique `α`, the map adds to the hidden polynomial one that vanishes at the other
columns concerned.

### Theorem 2.1: the bounds

Acceptance (`BHJK25.RS.Accept`) asks for a valid guess and a polynomial of degree `< m` agreeing
with the read pairs at `W + 1` distinct values, `W = ⌊√(2nm)⌋ + 1`.

* **Uniform tensors** ([RS/Null.lean](RS/Null.lean)): union bound over the guesses, the
  polynomials and the sets of `W + 1` columns; for a fixed guess, the cells of distinct columns
  are distinct entries.
* **Noisy planted tensors** ([RS/Planted.lean](RS/Planted.lean)): acceptance and the noise
  commute with relabelling, so the relabelling drops out. The true polynomial agrees with every
  column whose `2r` bits escape the noise and whose `α` is unique. The number of clean columns is
  bounded below by expanding a product over columns, since different columns use disjoint
  entries. Repeated values are counted as columns that repeat an earlier one, which the field
  size makes rare. These replace the paper's McDiarmid and binomial tail bounds.

### Theorem 2.1: the algorithm

The algorithm ([RS/Alg.lean](RS/Alg.lean)) runs through all `n^(2(k-1)ℓ)` guesses. For each, it
reads the column pairs from the input table and runs a per-guess decoder
([RS/Decode.lean](RS/Decode.lean)) on coefficient lists:

* Sudan's interpolation: a nonzero `Q(X, Y)` of weighted degree at most `W` vanishing at the
  points, found by fraction-free Gaussian elimination;
* the roots `Y = p(X)` of degree `< m` by Roth–Ruckenstein, with roots of univariate polynomials
  found by trying every field element. A Taylor-expansion argument bounds the `Y`-degree of each
  child by the multiplicity of its root, so each level has at most `W + 1` nodes. The program
  truncates to that many and keeps every polynomial in a fixed window, and the proof shows
  nothing is lost;
* a check of the agreement of each root.

The proof uses Sudan's algorithm, not Guruswami–Sudan; the parameters leave room for it.

The running time is certified with complexitylib's polynomial-time calculus. The guesses are
iterated with the loop theorem of [Machine/](Machine/), copied from BB20, whose cost is linear in
the number of rounds. The parameter `T` is given to the machine in unary, so the exponent does not
depend on `ε`.

### Theorem 3.1

* **The distributions** ([Spectral/Basic.lean](Spectral/Basic.lean),
  [Spectral/Prob.lean](Spectral/Prob.lean)) are probability measures. The Gaussian matrix is
  invariant under column permutations and under orthogonal maps (Mathlib's standard Gaussian),
  and null matrices are negative semidefinite.
* **The low-degree bound** ([Spectral/LDA.lean](Spectral/LDA.lean)) does not expand symmetric
  polynomials in an orthogonal basis, as Lemma 3.9 does. For a polynomial `f` of the entries, the
  projection on one eigenvalue, `Gᵢ(x) = E[f | λᵢ = x]`, is a polynomial of degree at most
  `deg f`. The projections satisfy `Σᵢ Var Gᵢ ≤ Var f` ([Spectral/Proj.lean](Spectral/Proj.lean))
  and are all equal, by the column symmetry. So `E_P f - E_Q f = G(λ*) - E G` is bounded by a
  univariate inequality for `μ_γ` ([Spectral/Legendre.lean](Spectral/Legendre.lean)). That
  inequality is proved with shifted Legendre polynomials: their orthogonality comes from
  Rodrigues' formula and the Beta integral.
* **The noisy planted matrix** ([Spectral/Tail.lean](Spectral/Tail.lean)) has `vᵀ M v > 3 ‖v‖²`
  for `v` the spike column `u`. Conditionally on `u`, the cross terms `⟨uⱼ, u⟩ / ‖u‖` are
  independent standard Gaussians; a moment generating function bound controls their weighted sum,
  in place of the Hanson–Wright inequality.
* **The algorithm** ([Spectral/Alg.lean](Spectral/Alg.lean)) tests whether
  `2I - (X + Xᵀ)/2` is positive definite. It uses the exact test of
  [../Background/SumOfSquares](../Background/SumOfSquares/README.md), which runs in polynomial
  time. Entrywise error `1/n` moves the quadratic form by at most `‖v‖²`.

## Map of the files

| Files | Content |
| --- | --- |
| [RS/Defs.lean](RS/Defs.lean) | Parameters, the field and its bits, guesses, cells, acceptance, the planted distribution. |
| [RS/Basic/](RS/Basic/) | Facts shared by the parts: parameter bounds, cells and the hidden layout, relabelling, list helpers. |
| [RS/Construction/](RS/Construction/), [RS/Construction.lean](RS/Construction.lean) | Probability, invariance and uniformity of the planted distribution (Lemma 2.10). |
| [RS/Null/](RS/Null/), [RS/Null.lean](RS/Null.lean) | Uniform tensors are rejected: counting, union bound, asymptotics. |
| [RS/Planted/](RS/Planted/), [RS/Planted.lean](RS/Planted.lean) | Noisy planted tensors are accepted: relabelling, noise, collisions, tails. |
| [RS/Decode/](RS/Decode/), [RS/Decode.lean](RS/Decode.lean) | The per-guess decoder: Sudan's lemma, elimination, Roth–Ruckenstein, its correctness and running time. |
| [RS/Alg/](RS/Alg/), [RS/Alg.lean](RS/Alg.lean) | The search over guesses, its correctness, and its running time. |
| [Machine/](Machine/) | Loops whose running time is linear in the number of rounds (from BB20). |
| [Spectral/Basic.lean](Spectral/Basic.lean), [Spectral/Prob.lean](Spectral/Prob.lean) | Gaussian facts; probability and rotation invariance of the distributions. |
| [Spectral/Legendre/](Spectral/Legendre/), [Spectral/Legendre.lean](Spectral/Legendre.lean) | Shifted Legendre polynomials and the univariate inequality. |
| [Spectral/Proj.lean](Spectral/Proj.lean), [Spectral/LDA/](Spectral/LDA/), [Spectral/LDA.lean](Spectral/LDA.lean) | Projections on one coordinate; moments, symmetry and the low-degree bound. |
| [Spectral/Tail/](Spectral/Tail/), [Spectral/Tail.lean](Spectral/Tail.lean) | The eigenvalue of the noisy planted matrix. |
| [Spectral/Alg.lean](Spectral/Alg.lean) | The algorithm of Theorem 3.1 and its running time. |
| [RS/Main.lean](RS/Main.lean), [Spectral/Main.lean](Spectral/Main.lean) | Theorems 2.1 and 3.1 from the parts. |

*Formalized by [Claude Code](https://claude.com/claude-code).*
