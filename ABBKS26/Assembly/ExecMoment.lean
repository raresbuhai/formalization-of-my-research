module

public import ABBKS26.Assembly.ExecMomentProgram

/-!
# Degree-two moment SDP as a budgeted list program

Problem construction and moment recovery are separate from the already certified Background
solver. Sample-dependent coefficient bits are allowed here: this SDP has degree two.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Robust
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

structure MomentSpec (M : MomentCode) : Prop where
  prepare_polytime : ComputableInPolyTime M.prepare encMomentInput
    (encPair SoS.Solver.encInput encUnary)
  recover_polytime : ComputableInPolyTime M.recover
    (encPair encMomentInput SoS.Solver.encOutput) (encList SoS.Solver.encRawPoly)
  degree_two : ∀ q, (M.prepare q).1.1.degree ≤ 2
  contract : MomentContract (momentProc M)
  adequate : MomentAdequate (momentProc M)

/-- Construct the weight/Gram SDP and recover its clipped, rounded rational moments. -/
theorem exists_moment_code : ∃ M : MomentCode, MomentSpec M := by
  refine ⟨MomentProgram.code, ⟨MomentProgram.prepare_polytime,
    MomentProgram.recover_polytime, ?_, MomentProgram.contract, MomentProgram.adequate⟩⟩
  intro q
  exact (MomentProgram.degree_two q).le

theorem moment_polytime (M : MomentCode) (hM : MomentSpec M) :
    ComputableInPolyTime (momentL M) encMomentInput (encList SoS.Solver.encRawPoly) := by
  exact hM.recover_polytime.comp
    (id'.prod (SoS.PolyTime.core_polytime.comp hM.prepare_polytime))


end ABBKS26.Assembly.Exec
