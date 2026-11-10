module

public import BGHKLMM26.Model
public import BGHKLMM26.Boolean
import BGHKLMM26.GW
import BGHKLMM26.Assembly
import BGHKLMM26.RunTime
import BGHKLMM26.Hardness.Main
import BGHKLMM26.RobustMIS.Final
import BGHKLMM26.Inapprox
import BGHKLMM26.IntGap.Main
import BGHKLMM26.RobustMIS.Statement

/-!
# Main results: proofs

Restates the theorems of `Challenge.lean` with the same names and statements, and proves them from
the development in this folder. Don't import `Challenge` here: the names would clash.

* `BGHKLMM26.exists_unique_isGWMinimizer` (`BGHKLMM26/GW.lean`).
* `BGHKLMM26.max2lin_approximation`: the algorithm is `BGHKLMM26.Alg.alg` with a precision
  constant `Q₀`, its mean value is `BGHKLMM26.Alg.alg_mean` and its running time
  `BGHKLMM26.Alg.exists_runsInTime`.
* `BGHKLMM26.maxCut_hardness`: `BGHKLMM26.Hard.maxCut_hardness_of_robustMIS`
  (`BGHKLMM26/Hardness/Main.lean`) from Theorem 7.1, `BGHKLMM26.RobustMIS.robustMIS`
  (`BGHKLMM26/RobustMIS/Final.lean`).
* `BGHKLMM26.maxCut_inapproximability`: `BGHKLMM26.Inapprox.of_hardness`
  (`BGHKLMM26/Inapprox.lean`) from Theorem 1.2.
* `BGHKLMM26.maxCut_integrality_gap`: `BGHKLMM26.IntGap.integrality_gap`
  (`BGHKLMM26/IntGap/Main.lean`) from Theorem 7.1.
* `BGHKLMM26.robust_majority_is_stablest`:
  `BGHKLMM26.RobustMIS.Statement.robust_majority_is_stablest_cube`
  (`BGHKLMM26/RobustMIS/Statement.lean`), which restates `BGHKLMM26.RobustMIS.robustMIS` in the
  definitions of `BGHKLMM26/Boolean.lean`.
-/

public section

namespace BGHKLMM26

open UniqueGames

/-- The Goemans–Williamson ratio has exactly one minimizer `ρ*` on `[-1, 1)`. -/
theorem exists_unique_isGWMinimizer : ∃! ρ : ℝ, IsGWMinimizer ρ :=
  GW.exists_unique_isGWMinimizer

/-- **Theorem 1.1** of [BGHKLMM26]: a randomized polynomial-time algorithm for weighted
Max 2-LIN(2) whose expected value is at least `(α_GW + c/(d log d))` times the optimum on
instances where every variable appears in at most `d` constraints. -/
theorem max2lin_approximation :
    ∃ (A : Instance × List Bool → List Bool) (k : ℕ),
      RunsInTime A (fun N ↦ (N + 2) ^ k) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d → ∀ I : Instance, Valid I → MaxDegreeLE I d →
        (alphaGW + c / (d * Real.log d)) * opt I ≤
          coinMean (((encInstance I).length + 2) ^ k) fun r ↦ outputWeight I (A (I, r)) := by
  -- The precision constant.
  have hm : 0 < min kappa 1 := lt_min kappa_pos one_pos
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt ((54 * 84 * 10 ^ 6 : ℝ) / min kappa 1)
    (by norm_num : (1 : ℝ) < 2)
  set Q₀ := max 10 q
  have hQ : 10 ≤ Q₀ := le_max_left _ _
  have hQ' : (54 * 84 * 10 ^ 6 : ℝ) ≤ min kappa 1 * 2 ^ Q₀ := by
    have h1 : (2 : ℝ) ^ q ≤ 2 ^ Q₀ := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    rw [div_lt_iff₀ hm] at hq
    nlinarith
  -- The running time, with enough coins.
  obtain ⟨k, hk, hk5, hrun⟩ := Alg.exists_runsInTime Q₀ (Alg.coinC Q₀ + 5)
  refine ⟨Alg.alg Q₀, k, hrun, min kappa 1 / (252 * 10 ^ 6), by positivity, ?_⟩
  intro d hd I hI hdeg
  refine Alg.alg_mean hQ hQ' ?_ hI hd hdeg
  -- `n T ≤ (|I| + 2)^k`.
  obtain ⟨N, hN⟩ : ∃ N, N = (encInstance I).length + 2 := ⟨_, rfl⟩
  have hc := Alg.coinLen_le Q₀ I
  rw [← hN] at hc ⊢
  have hN2 : 2 ≤ N := by omega
  have h1 : Alg.coinC Q₀ ≤ 2 ^ (k - 5) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : 2 ^ (k - 5) ≤ N ^ (k - 5) := Nat.pow_le_pow_left hN2 _
  calc I.1 * Alg.tPar Q₀ I = Alg.coinLen Q₀ I := rfl
    _ ≤ Alg.coinC Q₀ * N ^ 5 := hc
    _ ≤ N ^ (k - 5) * N ^ 5 := Nat.mul_le_mul_right _ (h1.trans h2)
    _ = N ^ k := by rw [← pow_add, Nat.sub_add_cancel hk5]

open Cslib.Complexity in
/-- **Theorem 1.2** of [BGHKLMM26]: assuming the Unique Games Conjecture, for every large enough
`d`, no polynomial-time algorithm tells graphs of maximum degree at most `d` with Max-Cut value at
least `c* - C/d` from those with value at most `s* + C log d / d` with bounded error, unless
`NP ⊆ BPP`. -/
theorem maxCut_hardness (hUGC : UGC) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      maxCutGap d ((1 - ρ) / 2 - C / d) (Real.arccos ρ / Real.pi + C * Real.log d / d) ∈
        PromiseBPP encGraph →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc :=
  Hard.maxCut_hardness_of_robustMIS RobustMIS.robustMIS hUGC

open Cslib.Complexity in
/-- **Corollary 1.3** of [BGHKLMM26]: assuming the Unique Games Conjecture, for every large enough
`d`, a randomized polynomial-time algorithm whose expected cut is at least `(α_GW + C log d / d)`
times the maximum cut on graphs of maximum degree at most `d` puts `NP` in `BPP`. -/
theorem maxCut_inapproximability (hUGC : UGC) :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d →
      ∀ (A : Instance × List Bool → List Bool) (k : ℕ), RunsInTime A (fun N ↦ (N + 2) ^ k) →
      (∀ I : Instance, Valid I → IsMaxCutInstance I → MaxDegreeLE I d →
        (alphaGW + C * Real.log d / d) * opt I ≤
          coinMean (((encInstance I).length + 2) ^ k) fun r ↦ outputWeight I (A (I, r))) →
      ∀ (α : Type) (enc : α ↪ List Bool), NP enc ⊆ BPP enc :=
  Inapprox.of_hardness (maxCut_hardness hUGC)

/-- **Theorem 1.4** of [BGHKLMM26]: for every large enough `d` there is a graph of maximum degree
at most `d` with a solution of the Goemans–Williamson SDP with triangle inequalities of value at
least `c* - C/d` and Max-Cut value at most `s* + C log d / d`, so that the integrality gap is at
most `α_GW + C log d / d`. -/
theorem maxCut_integrality_gap :
    ∃ (C : ℝ) (d₀ : ℕ), ∀ d : ℕ, d₀ ≤ d → ∀ ρ : ℝ, IsGWMinimizer ρ →
      ∃ (H : Graph) (v : Fin H.1 → EuclideanSpace ℝ (Fin H.1)),
        MaxDegreeAtMost H d ∧ IsSDPSolution H.1 v ∧
        (1 - ρ) / 2 - C / d ≤ sdpValue H v ∧
        maxCutValue H ≤ Real.arccos ρ / Real.pi + C * Real.log d / d ∧
        maxCutValue H ≤ (alphaGW + C * Real.log d / d) * sdpValue H v :=
  IntGap.integrality_gap RobustMIS.robustMIS

/-- **Theorem 7.1** of [BGHKLMM26], robust Majority is Stablest: for `ρ ∈ (-1, 0)` there are a
constant `C` and a function `h` with `h(τ) → 0` as `τ ↓ 0` such that every `f : {0,1}^R → [0,1]`
with influences at most `τ` and `Cut_ρ(f) ≥ arccos ρ / π - η` is within `L¹` distance
`C √η + h(τ)` of a linear threshold function. -/
theorem robust_majority_is_stablest :
    ∀ ρ : ℝ, -1 < ρ → ρ < 0 →
      ∃ (C : ℝ) (h : ℝ → ℝ), (∀ τ ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ h τ) ∧
        Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ (R : ℕ) (f : (Fin R → Bool) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
          ∀ τ ∈ Set.Ioc (0 : ℝ) 1, (∀ i, cubeInfluence f i ≤ τ) →
          ∀ η : ℝ, 0 ≤ η → Real.arccos ρ / Real.pi - η ≤ cubeCut ρ f →
            ∃ L, IsCubeLTF L ∧ cubeL1 f L ≤ C * Real.sqrt η + h τ :=
  RobustMIS.Statement.robust_majority_is_stablest_cube

end BGHKLMM26
