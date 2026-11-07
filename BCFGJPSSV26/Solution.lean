module

public import BCFGJPSSV26.Model
import BCFGJPSSV26.Combine
import BCFGJPSSV26.Greedy.Main
import BCFGJPSSV26.Stable.Main
import BCFGJPSSV26.FL.Main

/-!
# Main results: proofs

Restates the theorems of `Challenge.lean` with the same names and statements, and proves them from
the development in this folder. Don't import `Challenge` here: the names would clash.

* `BCFGJPSSV26.kMedian_approximation` follows from the other two by the paper's combination
  argument, `BCFGJPSSV26.Combine.thm11_of` (`BCFGJPSSV26/Combine.lean`).
* `BCFGJPSSV26.kMedian_pseudoApproximation`: `BCFGJPSSV26.Greedy.greedy_main`
  (`BCFGJPSSV26/Greedy/Main.lean`).
* `BCFGJPSSV26.stable_kMedian_approximation`: `BCFGJPSSV26.Stable.stable_main`
  (`BCFGJPSSV26/Stable/Main.lean`).
* `BCFGJPSSV26.facilityLocation_lmp`: `BCFGJPSSV26.FL.fl_main` (`BCFGJPSSV26/FL/Main.lean`).
-/

public section

namespace BCFGJPSSV26

open Encoding

/-- **Theorem 1.2** of [BCFGJPSSV26a]: for every `ε > 0`, a polynomial-time algorithm that
outputs at most `k + C log n / ε²` distinct facilities, of cost at most `(1.9499 + ε)` times the
optimum with `k` facilities. -/
theorem kMedian_pseudoApproximation :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ A : Instance → List ℕ, Turing.MultiTapeTM.ComputableInPolyTime A encInstance encCenters ∧
        ∀ I : Instance, I.Valid →
          I.IsCenterList (A I) ∧ ((A I).length : ℝ) ≤ I.k + C * Real.log I.n / ε ^ 2 ∧
          I.cost (I.centers (A I)) ≤ (1.9499 + ε) * I.opt I.k :=
  Greedy.greedy_main

/-- **Theorem 1.3** of [BCFGJPSSV26a], **Theorem 1.1** of [BCFGJPSSV26b]: an algorithm that,
given an instance, a number `L` and a rational accuracy `ε`, runs in time
`O(2^(e L) (N + 2)^e + N + L + |ε|)` with `e = a (⌈1/ε⌉ + 1)^b`, where `N` is the encoded length
of the instance and `|ε|` that of `ε` (not its absolute value), always outputs exactly `k`
distinct facilities, and, if `ε ∈ (0, 1/200)` and the instance is `β`-stable with `L ≥ 1/β`, with
probability at least `1 - ε` outputs facilities of cost at most `(1.89 + C ε)` times the
optimum. -/
theorem stable_kMedian_approximation :
    ∃ (A : ((Instance × ℕ) × ℚ) × List Bool → List ℕ) (a b : ℕ) (C : ℝ),
      RunsInTime (encPair (encPair encInstance encUnary) encRat) encCenters A
        (stableTimeOf a b) ∧
      ∀ I : Instance, I.Valid → I.k ≤ I.m → ∀ (L : ℕ) (ε : ℚ),
        (∀ r, I.IsCenterList (A (((I, L), ε), r)) ∧ (A (((I, L), ε), r)).length = I.k) ∧
        (0 < ε → ε < 1 / 200 → ∀ β : ℝ, 0 < β → I.IsStable β → 1 / β ≤ L →
          1 - (ε : ℝ) ≤ coinProb (stableTimeOf a b ((I, L), ε))
            fun r ↦ I.cost (I.centers (A (((I, L), ε), r))) ≤
              (1.89 + C * ε) * I.opt I.k) :=
  Stable.stable_main

/-- **Theorem 1.1** of [BCFGJPSSV26a]: a randomized polynomial-time `1.95`-approximation algorithm
for k-median. It always outputs at most `k` distinct facilities, and with probability at least
`2/3` their cost is at most `1.95` times the optimum. -/
theorem kMedian_approximation :
    ∃ (A : Instance × List Bool → List ℕ) (e : ℕ),
      RunsInTime encInstance encCenters A (fun I ↦ ((encInstance I).length + 2) ^ e) ∧
      ∀ I : Instance, I.Valid →
        (∀ r, I.IsCenterList (A (I, r)) ∧ (A (I, r)).length ≤ I.k) ∧
        2 / 3 ≤ coinProb (((encInstance I).length + 2) ^ e)
          fun r ↦ I.cost (I.centers (A (I, r))) ≤ 1.95 * I.opt I.k :=
  Combine.thm11_of kMedian_pseudoApproximation stable_kMedian_approximation


/-- **Theorem 1.4** of [BCFGJPSSV26a] (Theorem 4.3 in full): a polynomial-time `1.9499`-LMP
approximation algorithm for uncapacitated facility location. Given an instance with at least one
client and an opening cost `f ≥ 0`, it outputs a nonempty set `S` of distinct facilities with
`cost S ≤ 1.9499 (OPT_f - f |S|)`. -/
theorem facilityLocation_lmp :
    ∃ A : Instance × ℚ → List ℕ,
      Turing.MultiTapeTM.ComputableInPolyTime A (encPair encInstance encRat) encCenters ∧
      ∀ I : Instance, I.Valid → 0 < I.n → ∀ f : ℚ, 0 ≤ f →
        I.IsCenterList (A (I, f)) ∧
        I.cost (I.centers (A (I, f))) ≤
          1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (A (I, f)).length) :=
  FL.fl_main

end BCFGJPSSV26
