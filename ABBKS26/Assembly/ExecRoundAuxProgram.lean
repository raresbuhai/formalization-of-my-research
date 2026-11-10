module

public import ABBKS26.Assembly.ExecRoundAuxLoop
public import ABBKS26.Assembly.ExecFrameAuxLinear

/-!
# A capped rational planner for deterministic rounding

The planner carries one basis across solver rounds and PD-test greedy blocks. The public
one-vector step replays this plan. Recomputing a plan costs another polynomial factor in
unary fuel and avoids adding a hidden solver state to the public `RoundCode` interface.

All matrix operations below are on rational lists. Precision depends on the local rounding
parameters. The solver receives its own capped problem budget, rather than the caller's
entire fuel as a payload. No hidden projection or analytic `detRound` witness is evaluated.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundProgram

open Common Rounding
open FrameAux.Linear
open Cslib.Circuits.Rational (detRows)

/-- Decode the public tuple without introducing any new information. -/
def input (a : RoundArgs) : RoundInput :=
  ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩

/-- A square table with explicit unary dimension. -/
def table (d : ℕ) (f : ℕ → ℕ → ℚ) : MatrixL :=
  (List.range d).map fun i ↦ (List.range d).map (f i)

def identity (d : ℕ) : MatrixL := table d fun i j ↦ if i = j then 1 else 0

def subtract (d : ℕ) (A B : MatrixL) : MatrixL :=
  table d fun i j ↦ ent A i j - ent B i j

def multiply (d : ℕ) (A B : MatrixL) : MatrixL :=
  table d fun i j ↦ ((List.range d).map fun k ↦ ent A i k * ent B k j).sum

def trace (d : ℕ) (A : MatrixL) : ℚ :=
  ((List.range d).map fun i ↦ ent A i i).sum

/-- Rational determinants use the existing polynomial-time integer determinant. -/
def determinant (A : MatrixL) : ℚ :=
  (detRows (SoS.PDTestRat.scale A) : ℚ) /
    (SoS.PDTestRat.commonDen A : ℚ) ^ A.length

def replaceRow (A : MatrixL) (i j : ℕ) : MatrixL :=
  table A.length fun r c ↦ if r = i then (if c = j then 1 else 0) else ent A r c

/-- Cramer's rule, total also at a singular Gram matrix. -/
def inverse (A : MatrixL) : MatrixL :=
  table A.length fun i j ↦ determinant (replaceRow A j i) / determinant A

def gram (d : ℕ) (B : Points) : MatrixL :=
  table B.length fun i j ↦ dotL d (B.getD i []) (B.getD j [])

/-- Exact rational `B (Bᵀ B)⁻¹ Bᵀ`, with basis vectors stored as rows. -/
def projection (d : ℕ) (B : Points) : MatrixL :=
  let G := inverse (gram d B)
  table d fun a b ↦ ((List.range B.length).map fun i ↦
    ((List.range B.length).map fun j ↦ ent B i a * ent G i j * ent B j b).sum).sum

def complement (d : ℕ) (B : Points) : MatrixL :=
  subtract d (identity d) (projection d B)

/-- Prescribed objective grid; the extra factor four pays for the Frobenius norm. -/
def objectivePrecision (a : RoundArgs) : ℕ :=
  Nat.clog 2 ⌈1024 * (a.2.1 + 1 : ℚ) / a.2.2.1 ^ 2⌉₊

def greedyPrecision (a : RoundArgs) : ℕ :=
  Nat.clog 2 ⌈120 * (a.2.1 + 1 : ℚ) / greedyThreshold a.2.2.1 a.2.2.2.1⌉₊ + 2

def roundedProjection (a : RoundArgs) (B : Points) : MatrixL :=
  (projection a.2.1 B).map fun row ↦ row.map (roundRat (objectivePrecision a))

/-- The raw quadratic objective uses precisely the public pair-exponent convention. -/
def objective (a : RoundArgs) (Q : MatrixL) : SoS.Solver.Problem :=
  (a.1.numVars, a.1.degree, a.1.2.2.1,
    ((List.range a.2.1).flatMap (fun i ↦ (List.range a.2.1).map fun j ↦
      (pairExponent a.1.numVars i j, ent Q i j)), []))

def accuracy (a : RoundArgs) (P : SoS.Solver.Problem) : ℚ :=
  1 / (2 : ℚ) ^ (2 * (SoS.Solver.encProblem P).length +
    Nat.clog 2 ⌈a.2.2.2.2⌉₊ + 4 * Nat.clog 2 ⌈1 / a.2.2.1⌉₊ +
      Nat.clog 2 (a.2.1 + 2) + 24)

/-- Both the exponent and the resulting unary budget are capped before solving.
At sufficient fuel this is the solver's prescribed problem-only budget. -/
def solverFuel (P : SoS.Solver.Problem) (fuel : ℕ) : ℕ :=
  min fuel (((SoS.Solver.encProblem P).length + 2) ^ (min fuel (P.degree + 1)))

def solve (a : RoundArgs) (fuel : ℕ) (Q : MatrixL) : SoS.Solver.Output :=
  let P := objective a Q
  let η := accuracy a P
  SoS.Core.core ((P, η, η), solverFuel P fuel)

def moments (a : RoundArgs) (out : SoS.Solver.Output) : MatrixL :=
  table a.2.1 fun i j ↦ SoS.Poly.coeff a.1.numVars out (pairExponent a.1.numVars i j)

/-- One PD witness is projected, scaled into the half-unit annulus, and rounded. -/
def candidate (a : RoundArgs) (B : Points) (y : List ℤ) : Vector :=
  let x := mulVecL a.2.1 (complement a.2.1 B) (y.map fun (z : ℤ) ↦ (z : ℚ))
  let scale := scaleL (dotL a.2.1 x x) / 2
  x.map fun q ↦ roundRat (greedyPrecision a) (scale * q)

/-- Reject malformed or ill-conditioned candidates even when solver correctness is absent. -/
def acceptable (a : RoundArgs) (B : Points) (v : Vector) : Prop :=
  v.length = a.2.1 ∧ (∀ q ∈ v, -1 ≤ q ∧ q ≤ 1) ∧
    let z := mulVecL a.2.1 (complement a.2.1 B) v
    9 / 64 ≤ dotL a.2.1 z z ∧ dotL a.2.1 z z ≤ 81 / 64

instance (a : RoundArgs) (B : Points) (v : Vector) : Decidable (acceptable a B v) := by
  unfold acceptable
  infer_instance

/-- The same stop bit and encoded-size check used in the public loop guard every append. -/
def greedyStep (a : RoundArgs) (fuel : ℕ) (M : MatrixL)
    (s : Bool × Points) : Bool × Points :=
  if s.1 then s else
  if s.2.length ≥ rankCap a.2.2.1 a.2.2.2.1 then (true, s.2) else
  let C := complement a.2.1 s.2
  let A := table a.2.1 fun i j ↦
    (if i = j then greedyThreshold a.2.2.1 a.2.2.2.1 else 0) -
      ent (multiply a.2.1 (multiply a.2.1 C M) C) i j
  match SoS.PDTestRat.test A with
  | none => (true, s.2)
  | some y =>
    let v := candidate a s.2 y
    if acceptable a s.2 v ∧ (encPoints (s.2 ++ [v])).length ≤ fuel
    then (false, s.2 ++ [v]) else (true, s.2)

def greedy (a : RoundArgs) (fuel : ℕ) (M : MatrixL) (B : Points) : Points :=
  (((greedyStep a fuel M)^[min fuel (greedyCap a.2.2.1 a.2.2.2.1)]) (false, B)).2

/-- One outer solve, followed by a persistent-basis greedy block when it continues. -/
def outerStep (a : RoundArgs) (fuel : ℕ) (s : Bool × Points) : Bool × Points :=
  if s.1 then s else
  let Q := roundedProjection a s.2
  let M := moments a (solve a fuel Q)
  if |trace a.2.1 M - 1| > 1 / 4 then (true, s.2) else
  if 1 - a.2.2.1 ^ 2 / 4 ≤ trace a.2.1 (multiply a.2.1 Q M) then (true, s.2) else
  let B := greedy a fuel M s.2
  if B.length = s.2.length then (true, s.2) else (false, B)

/-- Reject a numerically huge junk variable count before enumerating exponent vectors.
An explicit ball constraint on a valid input pays at least one encoded term per variable. -/
def plan (q : RoundArgs × ℕ) : Points :=
  if q.1.1.numVars ≤ (SoS.Solver.encProblem q.1.1).length then
    (((outerStep q.1 q.2)^[min q.2 (packCount q.1.2.2.1 q.1.2.2.2.1 + 1)])
      (false, [])).2
  else []

/-- Replaying uses only a list index; no semantic witness is consulted by the machine. -/
def code : RoundCode := ⟨fun p ↦ (plan p.1)[p.2.length]?⟩

/-- The analytic decoder is used only in theorem statements. -/
def output (a : RoundArgs) (B : Points) : RoundOutput a.2.1 :=
  ⟨B.map (vectorOf a.2.1)⟩

end ABBKS26.Assembly.Exec.RoundProgram
