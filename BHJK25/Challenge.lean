module

public import BHJK25.Model

/-!
# Main results: statements

The two counterexamples of [BHJK25], Theorems 2.1 and 3.1 (in the introduction, Theorems 1.3 and
1.6), with proofs `sorry`. Numbers are those of the arXiv version (v1).

What a reader has to trust is this file and what it imports: the definitions in
`BHJK25/Model.lean` (the low-degree advantage, Boolean tensors and their noise, the spiked
spectral distributions, rational approximations, algorithms), the encodings in
`Background/Encoding.lean`, CSLib's multitape Turing machines, and Mathlib.

## Conventions of both theorems

* **The low-degree advantage** is the paper's Definition 1.1, as an inequality
  (`BHJK25.AdvantageAtMost`): `LDA_D(P, Q) ≤ δ` says that `E_P f - E_Q f ≤ δ √(Var_Q f)` for every
  polynomial `f` of degree at most `D` in the coordinates, and that these expectations are
  finite. `LDA_D(P, Q) = 0` is the case `δ = 0`: `P` and `Q` give every such polynomial the same
  expectation. The degree bound `D` is a real number, so `n^(1 - 6ε)` needs no rounding.
* **Algorithms** are deterministic multitape Turing machines that output a bit
  (`BHJK25.RunsInTime`). Both of the paper's distinguishers are deterministic, and a deterministic
  algorithm is a special case of a randomized one. Without coins the time bound cannot pass advice
  to the machine, so it may be any explicit function.
* `n` is the dimension: tensors are indexed by `{0, …, n - 1}` and matrices are `n × n`. "For all
  large enough `n`" is `∀ᶠ n in atTop`. Logarithms are natural; the base only changes constants.

## Theorem 2.1

[BHJK25, Theorem 2.1]: fix any integer `k ≥ 2` and small enough `ε > 0`. Let `Q_n` be the uniform
distribution over symmetric `k`-tensors in `({0,1}^n)^⊗k`. Then there exists an `S_n`-symmetric
distribution `P_n` over symmetric `k`-tensors in `({0,1}^n)^⊗k` such that
`LDA_D(P_n, Q_n) = 0` for `D = n^(1 - 6ε)`, and there is an algorithm `A` that runs in time
`n^O(log^(1/(k-1)) n)` such that `Pr_{M ∼ Q_n}[A(M) = 0]` and `Pr_{M ∼ T_ε P_n}[A(M) = 1]` are at
least `1 - exp(-n^(1 - O(ε)))`. [BHJK25, Theorem 1.3] is the form given in the introduction, with
`D = n^(1 - O(ε))` and success probability `1 - o(1)`: a counterexample to the low-degree
conjecture (Conjecture 1.2).

Formally (`BHJK25.reed_solomon_counterexample`):

* **Tensors** are functions from the `k`-element subsets of `{0, …, n - 1}` to bits
  (`BHJK25.Tensor`). These are the paper's symmetric tensors, determined by their entries
  `M_{i₁ … i_k}` with `i₁ < ⋯ < i_k`, which are the coordinates of `{0,1}^(n choose k)` and the
  variables of the polynomials (`BHJK25.entryBits`). `Q_n` is uniform (`BHJK25.uniformTensor`).
* **`P_n` is existential**, as in the paper: any probability distributions with the stated
  properties will do, so the reader need not check the construction (noisy evaluations of a
  random polynomial over a finite field, written in binary and hidden among random bits).
  `S_n`-invariance (`BHJK25.SnInvariant`) and the noise make the statement non-trivial: without
  them, the uniform distribution on a linear code with large dual distance would already give
  advantage `0` and a fast distinguisher (testing membership in the code).
* **The noise** `T_ε` replaces each entry, independently, by a uniformly random bit with
  probability `ε` (`BHJK25.noisyProb`), as in Section 2 and Conjecture 1.2.
* **"Small enough `ε`"** is `0 < ε ≤ ε₀`, and **`n^(1 - O(ε))`** is `n^(1 - K ε)`; `ε₀ > 0` and
  `K` are absolute constants, the same for every `k`. Theorem 1.3 is phrased for every `ε > 0`;
  its precise form, Theorem 2.1, is for small enough `ε`, and so is this statement.
* **The running time `n^O(log^(1/(k-1)) n)`** is `(n + 2)^(C ((log (n + 2))^(1/(k-1)) + 1))`
  (`BHJK25.tensorTime`), with a constant `C` that depends on `k` but not on `ε`. The input
  (`BHJK25.encTensor`) is `n` followed by the tensor as a table of `n^k` bits, one for each index
  tuple, with `0` where two indices coincide: the tensor as an element of `({0,1}^n)^⊗k`, as in
  the paper. For fixed `k` its length is polynomial in `n`.
* **The probabilities** are bounded for all large enough `n` (depending on `k` and `ε`). `P_n` and
  the algorithm may depend on `k` and `ε`. The algorithm is given only the tensor.

## Theorem 3.1

[BHJK25, Theorem 3.1]: there exist rotational invariant distributions `Q_n` and `P_n` over
symmetric matrices in `ℝ^(n × n)` such that `LDA_D(P_n, Q_n) ≤ 1/polylog(n)` for
`D = n^(1/3)/polylog(n)`, and such that, for any fixed `ε ∈ [0, 1)` and `M' = (1 - ε) M₁ + ε M₀`
with `M₁ ∼ P_n` and `M₀ ∼ Q_n`, there is a polynomial-time algorithm `A` with
`Pr_{M ∼ Q_n}[A(M) = 0] = 1` and `Pr[A(M') = 1] ≥ 1 - 1/poly(n)`. [BHJK25, Theorem 1.6] is the
informal version.

Formally (`BHJK25.top_eigenvalue_counterexample`):

* **The distributions are the paper's** (Definitions 3.2–3.4), with the parameters of its proof
  (Section 3.3). `Q_n` is the law of `U diag(λ) Uᵀ`, where `U` is an `n × n` matrix of independent
  standard Gaussians and `λ₁, …, λ_n` are independent, each uniform on `[-1, 0]` with probability
  `γ = C log² n / n` and `0` otherwise (`BHJK25.nullAt`). `P_n` is the same with `λ_n = γ log n`
  (`BHJK25.plantedAt`). The paper's `m = Θ(n)` eigenvalues are `m = n`, and its "some large
  constant `C`" is every `C > 0`. `γ` is capped at `1` (`BHJK25.sparsity`), which changes only the
  finitely many `n` with `C log² n > n` and makes `μ_γ` a distribution for every `n`. Naming the
  distributions is stronger than "there exist" and shows which ones they are. `Q_n` is not a
  product distribution, so this theorem does not refute Conjecture 1.2.
* **Rotation-invariant probability distributions**: for every `n`, both laws are probability
  measures, and `O M Oᵀ` has the same law as `M` for every orthogonal `O`
  (`BHJK25.RotationInvariant`). The laws are images of measures under maps, which are continuous,
  hence measurable (`BHJK25.measurable_spectral`, `BHJK25.measurable_noisy`,
  `BHJK25.measurable_conj`, proved in `BHJK25/Model.lean`), so `Measure.map` gives the intended
  distributions. (For a map that is not almost everywhere measurable with respect to the source
  measure, Mathlib's `Measure.map` is an arbitrary Dirac mass, and the statement would say
  something else.)
* **`D = n^(1/3)/polylog(n)` and `1/polylog(n)`**: for every `b` there is an `a` such that for all
  large enough `n`, the advantage at degree `n^(1/3) / log^a n` is at most `1 / log^b n`. The
  coordinates are the `n²` entries of the matrix (`BHJK25.entries`).
* **The noisy matrix** `(1 - ε) M₁ + ε M₀` (`BHJK25.noisyLaw`) is the paper's.
* **Rational input.** The paper's algorithm reads the real matrix and tests whether it has a
  positive eigenvalue. Here the algorithm reads a rational matrix `X` whose entries are within
  `1/n` of those of the real matrix (`BHJK25.Approximates`), and the guarantee is that with the
  stated probability it answers correctly on **every** such `X` (`BHJK25.ProbAtLeast`).
  * So the approximation may be chosen by an adversary who sees the drawn matrix. It need not be
    symmetric, and it need not come from a measurable rounding: the probability is that of a
    measurable event on which the algorithm answers correctly on every approximation.
  * The sign of the top eigenvalue is not robust, so the proof uses a threshold. `X - M` has
    operator norm at most `1`, the null matrices are negative semidefinite, and the planted top
    eigenvalue is of order `(1 - ε) C log³ n`.
  * The tolerance is absolute: unlike the Gaussian mixtures of [BS23], these distributions have a
    fixed scale. Rounding every entry to a multiple of `1/n` gives an approximation whose entries
    have `O(log n + log (2 + |M_ij|))` bits.
* **`1 - 1/poly(n)`** is `1 - 1/n^e` for every `e`, for all large enough `n` (depending on `C`,
  `ε` and `e`); the paper's proof gives this. Probability `1` for the null distribution is kept,
  for every `n`.
* **Polynomial time**: `A` runs in time `O((|x| + 2)^c)` on inputs of encoded length `|x|`
  (`BHJK25.encRatMatrix`: `n` and the rows of `X`). An adversary may give a needlessly long
  approximation; the algorithm must still answer correctly, and may take time polynomial in its
  length, as reading it already does.
* **One algorithm** serves every `C`, `ε` and `n`, where the paper allows it to depend on `ε`.
  It is given only `X`.
-/

public section

namespace BHJK25

open Encoding Filter MeasureTheory

/-- **Theorem 2.1** of [BHJK25] (Theorem 1.3 in the introduction): for every `k ≥ 2` and small
enough `ε > 0` there is an `S_n`-invariant distribution `P_n` on symmetric `k`-tensors with entries
in `{0, 1}` whose degree-`n^(1 - 6ε)` advantage over the uniform distribution `Q_n` is `0`, while an
algorithm running in time `n^O(log^(1/(k-1)) n)` tells `T_ε P_n` from `Q_n` with probability
`1 - exp(-n^(1 - O(ε)))` on each side. -/
theorem reed_solomon_counterexample :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ k : ℕ, 2 ≤ k → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (P : (n : ℕ) → Measure (Tensor k n)) (A : TensorInput k → Bool),
        (∀ n, IsProbabilityMeasure (P n) ∧ SnInvariant (P n) ∧
          AdvantageAtMost entryBits ((n : ℝ) ^ (1 - 6 * ε)) (P n) (uniformTensor k n) 0) ∧
        RunsInTime (encTensor k) encBool A (tensorTime k C) ∧
        ∀ᶠ n : ℕ in atTop,
          1 - Real.exp (-(n : ℝ) ^ (1 - K * ε)) ≤ uniformProb k n (fun M ↦ A ⟨n, M⟩ = false) ∧
          1 - Real.exp (-(n : ℝ) ^ (1 - K * ε)) ≤ noisyProb ε (P n) (fun M ↦ A ⟨n, M⟩ = true) :=
  sorry

/-- **Theorem 3.1** of [BHJK25] (Theorem 1.6 in the introduction): the rotation-invariant null and
planted distributions `U diag(λ) Uᵀ` of the paper have advantage at most `1/polylog(n)` at degree
`n^(1/3)/polylog(n)`, while a polynomial-time algorithm reading any entrywise `1/n`-approximation
of the matrix answers `0` on the null distribution with probability `1`, and `1` on the noisy
planted matrix `(1 - ε) M₁ + ε M₀` with probability `1 - 1/n^e` for every `e`. -/
theorem top_eigenvalue_counterexample :
    ∃ (A : RatMatrix → Bool) (c : ℕ),
      RunsInTime encRatMatrix encBool A (fun x ↦ ((encRatMatrix x).length + 2) ^ c) ∧
      ∀ C : ℝ, 0 < C →
        (∀ n, IsProbabilityMeasure (nullAt C n) ∧ IsProbabilityMeasure (plantedAt C n) ∧
          RotationInvariant (nullAt C n) ∧ RotationInvariant (plantedAt C n)) ∧
        (∀ b : ℕ, ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
          AdvantageAtMost entries ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ a) (plantedAt C n)
            (nullAt C n) (1 / Real.log n ^ b)) ∧
        (∀ n, ProbAtLeast (nullAt C n) 1 fun M ↦ ∀ X, Approximates X M → A ⟨n, X⟩ = false) ∧
        ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∀ e : ℕ, ∀ᶠ n : ℕ in atTop,
          ProbAtLeast (noisyLaw ε (plantedAt C n) (nullAt C n)) (1 - 1 / (n : ℝ) ^ e) fun M ↦
            ∀ X, Approximates X M → A ⟨n, X⟩ = true :=
  sorry

end BHJK25
