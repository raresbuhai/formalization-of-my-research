module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdSolver
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdInput

/-! The actual plain rounded SUB representation supplied to RC2. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdNested

open Common Matrix MvPolynomial Rounding
open SoS.Solver (RawPoly Problem)

noncomputable section

variable {d : ℕ}


/-- The executable plain-system representation supplies an encoded RC2 call.
Ball, norm, and layout bounds remain independent machine obligations. -/
def encoding (J : ComplementInput d) (A : List RawPoly) (Bd : ℚ) (fuel : ℕ)
    (hA : plainSystem (A.map fun p ↦ SoS.toReal (p.toPoly d)) = J.system)
    (hvalid : J.system.Valid J.degree)
    (hball : ballBound J.system J.degree J.tolerance J.M₁ J.X ≤ (Bd : ℝ))
    (hf : IdSolver.layoutFuel d J.degree A ≤ fuel)
    (NC : NestedCode) (hNC : NestedSpec NC) (B : ℚ) (hB : 1 ≤ B)
    (hbound : nestedNorm J.system J.degree J.tolerance J.M₂ ≤ (B : ℝ)) :
    RCEncoding J where
  raw := nestedInput (IdSolver.query d J.degree A J.tolerance Bd fuel)
  problem := SpecSolver.zeroObjective
    (NC.build (IdSolver.query d J.degree A J.tolerance Bd fuel))
  normBound := B
  dimension_eq := rfl
  system_eq := (IdSolver.family_real d J.degree A J.tolerance Bd fuel).trans hA
  degree_eq := rfl
  tolerance_eq := rfl
  represents := IdSolver.represents NC hNC d J.degree A J.tolerance Bd fuel
    (hA.symm ▸ hvalid) hf
  objective_degree := by
    intro f hf
    change f ∈ [[]] at hf
    rw [List.mem_singleton.mp hf]
    simp [SoS.Solver.RawPoly.toPoly]
  ball_le := hball
  norm_one_le := hB
  norm_le := hbound

end

end ABBKS26.Assembly.Exec.RefineSynth.IdNested
