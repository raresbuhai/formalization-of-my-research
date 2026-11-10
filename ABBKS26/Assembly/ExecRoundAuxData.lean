module

public import ABBKS26.Assembly.ExecNested

/-! Shared interfaces for the executable rounder, moved unchanged from `ExecRound`. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common Rounding
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

abbrev RoundArgs := SoS.Solver.Problem × ℕ × ℚ × ℕ × ℚ
abbrev encRoundArgs := encPair SoS.Solver.encProblem
  (encPair encUnary (encPair encRat (encPair encUnary encRat)))

def roundArgs (I : RoundInput) : RoundArgs :=
  (I.problem, I.ambient, I.radius, I.rankBound, I.normBound)

structure RoundCode where
  step : (RoundArgs × ℕ) × Points → Option Vector

/-- A failed call stops growing the basis; every later iteration preserves it. -/
def roundStep (R : RoundCode) (q : RoundArgs × ℕ) (state : Bool × Points) : Bool × Points :=
  if state.1 then state else
  match R.step (q, state.2) with
  | none => (true, state.2)
  | some v =>
    let next := state.2 ++ [v]
    if (encPoints next).length ≤ q.2 then (false, next) else (true, state.2)

/-- The entire greedy/packing loop is explicit and bounded by unary fuel. -/
def roundL (R : RoundCode) (q : RoundArgs × ℕ) : Points :=
  (((roundStep R q)^[q.2]) (false, [])).2

noncomputable def roundFuel (I : RoundInput) : ℕ :=
  ((SoS.Solver.encProblem I.problem).length + I.ambient + I.rankBound +
    (encRat I.radius).length + (encRat I.normBound).length + 2) ^
      (100 * (solverConstant + 1) * (I.problem.degree + 1)) *
        (rankCap I.radius I.rankBound + 2) ^ 100

structure RoundSpecL (R : RoundCode) : Prop where
  step_polytime : ComputableInPolyTime R.step
    (encPair (encPair encRoundArgs encUnary) encPoints) (encOption encVector)
  polytime : ComputableInPolyTime (roundL R) (encPair encRoundArgs encUnary) encPoints
  semantic : ∃ run : (I : RoundInput) → RoundOutput I.ambient, RoundSpec run ∧
      ∀ I fuel, roundFuel I ≤ fuel →
        roundL R (roundArgs I, fuel) = (run I).basis.map (fun v ↦ List.ofFn v)

end ABBKS26.Assembly.Exec
