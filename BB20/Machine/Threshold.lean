module

public import BB20.Learning.Algorithm
public import BB20.Machine.ThrPolyTime
public import BB20.Machine.ThrSpec
public import Background.PolyTime.Rat
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# The thresholds, computed in polynomial time

Threshold functions for the algorithms of Theorems 6 and 11 that meet their specifications
(`BB20.ThrSpec6`, `BB20.ThrSpec11`) and are computable in polynomial time.

The thresholds are `BB20.Machine.thr6` and `BB20.Machine.thr11` (`BB20/Machine/ThrDef.lean`),
rational approximations from below of `τ'` within a factor `0.9`. Their specifications are proved
in `BB20/Machine/ThrSpec.lean`, their polynomial-time certificates in
`BB20/Machine/ThrPolyTime.lean`.
-/

@[expose] public section

namespace BB20.Machine

open Turing.MultiTapeTM

/-- **A threshold function for Theorem 6.** -/
theorem exists_thr6 : ∃ thr : Input → Option ℚ, ThrSpec6 thr ∧
    ComputableInPolyTime thr encInput (encOption Encoding.encRat) :=
  ⟨thr6, Thr.thr6_spec, Thr.thr6_polytime⟩

/-- **A threshold function for Theorem 11.** -/
theorem exists_thr11 : ∃ thr : Input → Option (ℚ × ℚ), ThrSpec11 thr ∧
    ComputableInPolyTime thr encInput (encOption (encPair Encoding.encRat Encoding.encRat)) :=
  ⟨thr11, Thr.thr11_spec, Thr.thr11_polytime⟩

end BB20.Machine
