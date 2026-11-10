module

public import ABBKS26.Assembly.Det
public import ABBKS26.Assembly.RunTimeAuxBudget

/-!
# Running time

The list program runs on a multitape Turing machine in time `g(⌈1/wmin⌉, ⌈Δ⌉) · (|x| + 2)^C`
(times `(d + 2)^(C (L² + 1))` for identical covariances), with a computable, constructible
`g`.
-/

@[expose] public section

namespace ABBKS26.Assembly

noncomputable section


open Matrix

open Common

def time (mode : Mode) (g : ℕ → ℕ → ℕ) (C : ℕ) : Input → ℕ :=
  match mode with
  | .centered => centeredTime g C
  | .identical => identicalCovTime g C


/-- Writing a unary budget and running the padded program fits the frozen time bound. -/
theorem exists_runtime
    (mode : Mode) : ∃ (budget : Input → ℕ) (Ct : ℕ) (g : ℕ → ℕ → ℕ),
      Computable₂ g ∧
      RunsInTime encInput encOutput (algorithm mode budget) (time mode g Ct) ∧
      (∀ x, WellFormed x → budgetNeed mode x ≤ budget x) := by
  obtain ⟨clock, hclock, E, hbudget⟩ := RunTimeAuxBudget.exists_budget_constructor mode
  let budget := RunTimeAuxBudget.budget clock mode
  obtain ⟨D, hD⟩ := RunTimeAuxPadding.padded_runtime (program mode).raw budget
    (program_spec mode).2.2.2.1 E hbudget
  obtain ⟨g, C, hg, hbound⟩ := RunTimeAuxBudget.budget_power_absorption clock hclock mode D
  refine ⟨budget, C, g, hg, RunTimeAuxPadding.runtime_of_le hD hbound, ?_⟩
  intro x hx
  exact RunTimeAuxBudget.budget_sufficient clock mode x hx

/-- Increasing the absolute polynomial exponent preserves the time certificate. -/
theorem runtime_mono
    (mode : Mode) (A : Input × List Bool → Output) (g : ℕ → ℕ → ℕ)
    (C C' : ℕ) (hC : C ≤ C') (h : RunsInTime encInput encOutput A (time mode g C)) :
    RunsInTime encInput encOutput A (time mode g C') := by
  have ht (x : Input) : time mode g C x ≤ time mode g C' x := by
    have hp : ((encInput x).length + 2) ^ C ≤ ((encInput x).length + 2) ^ C' :=
      Nat.pow_le_pow_right (by omega) hC
    cases mode with
    | centered => exact Nat.mul_le_mul_left _ hp
    | identical =>
      exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hp)
        (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ hC))
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩
  all_goals exact Nat.mul_le_mul_left c (Nat.add_le_add_right
    (Nat.add_le_add_right (ht xr.1) _) 1)


end

end ABBKS26.Assembly
