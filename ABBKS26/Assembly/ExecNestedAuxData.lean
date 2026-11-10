module

public import ABBKS26.Assembly.ExecData

/-!
# Guarded sparse nested reification and the second solver call

The high-degree solver sees locally rounded and magnitude-checked moments. It does not see
the global sample budget as a binary payload. `NestedArgs` contains only the local fuel.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly Problem encRawPoly encProblem)

abbrev NestedArgs := ℕ × ℕ × List RawPoly × List RawPoly × List ℕ × ℚ × ℚ
abbrev encNestedArgs := encPair encUnary (encPair encUnary
  (encPair (encList encRawPoly) (encPair (encList encRawPoly)
    (encPair encIndices (encPair encRat encRat)))))

def nestedInput (q : NestedArgs × ℕ) : Rounding.RawInput :=
  ⟨⟨q.1.1, q.1.2.2.1, q.1.2.2.2.1, q.1.2.2.2.2.1⟩,
    q.1.2.1, q.1.2.2.2.2.2.1, q.1.2.2.2.2.2.2, q.2⟩

structure NestedCode where
  build : NestedArgs × ℕ → Problem


/-- Sparse storage bound: linear degree in the dimension exponent, before solving. -/
def sparseBound (d K m support bits : ℕ) : ℕ :=
  (m + 2) ^ 4 * (support + 2) ^ 4 * (bits + K + 2) ^ 4 * (d + 2) ^ (32 * (K + 1))

structure NestedSpec (N : NestedCode) : Prop where
  polytime : ComputableInPolyTime N.build (encPair encNestedArgs encUnary) encProblem
  represents : ∀ q, (nestedInput q).family.real.Valid (nestedInput q).degree →
    (Rounding.nestedVars (nestedInput q).family.real (nestedInput q).degree + 2) ^
      (2 * (nestedInput q).degree + 2) ≤ q.2 →
    Rounding.RawRep (nestedInput q) (N.build q)
  sparse_plain : ∀ q support bits,
    q.1.2.2.2.1 = [] → q.1.2.2.2.2.1 = [] →
    (nestedInput q).family.real.Valid (nestedInput q).degree →
    (Rounding.nestedVars (nestedInput q).family.real (nestedInput q).degree + 2) ^
      (2 * (nestedInput q).degree + 2) ≤ q.2 →
    (∀ p ∈ q.1.2.2.1, p.length ≤ support ∧
      ∀ t ∈ p, t.1.length ≤ q.1.1 ∧ t.1.sum ≤ q.1.2.1 ∧
        (encRat t.2).length ≤ bits) →
    (encRat q.1.2.2.2.2.2.1).length ≤ bits →
    (encRat q.1.2.2.2.2.2.2).length ≤ bits →
    (encProblem (N.build q)).length ≤
      sparseBound q.1.1 q.1.2.1 q.1.2.2.1.length support bits


end ABBKS26.Assembly.Exec
