module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdDirection
public import Mathlib.Data.Set.Finite.List
public import Mathlib.Order.Interval.Set.Infinite

/-! Encoding-sensitive sufficient rounder allowances for the SUB branch. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdAllowance

open Common Rounding
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)

noncomputable section


/-- The exact bit-sensitive execution premise still needed by the prepared SUB net. -/
def Prepared (MC : MomentCode) (NC : NestedCode) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      _root_.ABBKS26.Tree.Prepared .identical M ε w η Δ D ω r ps →
      localBudget .identical k n d ps ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
      roundFuel (RoundProgram.input
        (IdCoverage.call (IdProgram.problem MC NC) IdNorms.normInput
          (args k ps x h P, fuel))) ≤ fuel

end

end ABBKS26.Assembly.Exec.RefineSynth.IdAllowance
