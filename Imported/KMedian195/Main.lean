/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`, the last three theorems of
`bound-195/KMedian195/FactorRevealingPrimal.lean`. The first and last are the two theorems of
`bound-195/Challenge.lean`, which the source checks with the comparator.
Changes: module header (`module`, `public import`, `@[expose] public section`) and a module
docstring; the theorems are moved here from `Imported/KMedian195/FactorRevealingPrimal.lean`.
-/
module

public import KMedian195.FactorRevealingPrimal

/-!
# The 1.95 bound on the factor-revealing program

Theorem 4.4 of *A Better-than-2 Approximation for k-Median*, Part I
(arXiv:2610.18144): for `γ ∈ [1, 1.224]`, every feasible solution of the factor-revealing program
of Definition 4.1 (`KMedian195.OriginalPrimalSolution.Feasible`, in
`Imported/KMedian195/Program.lean`) with the bid `β_γ(α, d) = [α - γ d]^+` has objective value at most
`2 - (γ - 1)^2`, in every dimension `n ≥ 1`.
-/

@[expose] public section

namespace KMedian195

noncomputable section

/-- The exact factor-revealing bound throughout the closed parameter interval `[1, 1.224]`. -/
theorem originalPrimalUpperBound_exact
    (gamma : ℝ) (hγlo : 1 ≤ gamma) (hγhi : gamma ≤ (153 : ℝ) / 125) :
    OriginalPrimalUpperBound gamma (2 - (gamma - 1) ^ 2) := by
  rcases eq_or_lt_of_le hγlo with hγ | hγ
  · subst gamma
    simpa using originalPrimalUpperBound_one
  · exact originalPrimalUpperBound_exact_of_one_lt hγ hγhi

theorem originalPrimalUpperBound_153_div_125_exact :
    OriginalPrimalUpperBound ((153 : ℝ) / 125)
      (2 - (((153 : ℝ) / 125) - 1) ^ 2) := by
  exact originalPrimalUpperBound_exact _ (by norm_num) le_rfl

theorem originalPrimalUpperBound_195 :
    OriginalPrimalUpperBound ((153 : ℝ) / 125) ((39 : ℝ) / 20) := by
  intro n hn x hx
  have hExact := originalPrimalUpperBound_153_div_125_exact n hn x hx
  have hbound : 2 - (((153 : ℝ) / 125) - 1) ^ 2 ≤ (39 : ℝ) / 20 := by
    norm_num
  exact le_trans hExact hbound

end

end KMedian195
