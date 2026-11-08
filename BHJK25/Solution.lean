module

public import BHJK25.Model
import BHJK25.RS.Main
import BHJK25.Spectral.Main

/-!
# Main results: proofs

Restates each theorem of `Challenge.lean` with the same name and statement, and proves it from the
development in this folder. Don't import `Challenge` here: the names would clash.

* Theorem 2.1: `BHJK25.reed_solomon_main` in `BHJK25/RS/Main.lean`.
* Theorem 3.1: `BHJK25.top_eigenvalue_main` in `BHJK25/Spectral/Main.lean`.
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
  reed_solomon_main

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
  top_eigenvalue_main

end BHJK25
