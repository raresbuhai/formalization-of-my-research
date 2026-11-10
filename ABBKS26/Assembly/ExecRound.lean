module

public import ABBKS26.Assembly.ExecRoundCertificates

/-!
# Deterministic, fuelled rounding

Each step solves a rounded objective, reads quadratic pseudo-moments, and either appends a
new grid vector or stops. The stored basis is size-capped after every step; the cap is tested
on junk inputs too. The semantic witness may be replaced, as permitted by `ProgramSpec`.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common Rounding
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- Grid objectives and the prescribed solver accuracy realize deterministic rounding. -/
theorem exists_round_code (N : NestedCode) (hN : NestedSpec N) :
    ∃ R : RoundCode, RoundSpecL R := by
  refine ⟨RoundCertificates.code, ?_⟩
  exact ⟨RoundCertificates.step_polytime, RoundCertificates.loop_polytime,
    RoundCertificates.semantic N hN⟩


end ABBKS26.Assembly.Exec
