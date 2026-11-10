module

public import ABBKS26.Assembly.ExecNestedProgram

/-!
# Guarded sparse nested reification and the second solver call

The concrete list constructor and its correctness proofs are in `ExecNestedProgram`.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly Problem encRawPoly encProblem)

/-- Construct the sparse witness, rather than choosing an arbitrary `NestedRawSpec` witness. -/
theorem exists_nested_code : ∃ N : NestedCode, NestedSpec N := by
  refine ⟨NestedProgram.code, ?_⟩
  exact ⟨NestedProgram.build_polytime, NestedProgram.build_represents,
    NestedProgram.build_sparse_plain⟩


end ABBKS26.Assembly.Exec
