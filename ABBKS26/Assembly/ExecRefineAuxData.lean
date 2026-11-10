module

public import ABBKS26.Assembly.ExecFrame
public import ABBKS26.Assembly.ExecMoment
public import ABBKS26.Assembly.ExecRound

/-! Shared refiner interfaces, moved unchanged from `ExecRefine`. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- Dimension, component count, schedule, sample, depth, parent block. -/
abbrev BlockArgs := ℕ × ℕ × Points × Points × ℕ × List ℕ
abbrev encBlockArgs := encPair encUnary (encPair encNat (encPair encPoints
  (encPair encPoints (encPair encNat encIndices))))
abbrev RefineArgs := ℕ × ℕ × Points × Points × CandidateL
abbrev encRefineArgs := encPair encUnary (encPair encNat
  (encPair encPoints (encPair encPoints encCandidate)))

/-- A quadratic evaluation with dimension in unary. -/
def evalL (d : ℕ) (q : StatisticL) (x : Vector) : ℚ :=
  ((List.range d).map fun i ↦
    ((List.range d).map fun j ↦
      x.getD i 0 * (q.1.getD i []).getD j 0 * x.getD j 0).sum).sum +
    ((List.range d).map fun i ↦ q.2.1.getD i 0 * x.getD i 0).sum + q.2.2

def leftL (d : ℕ) (pts : Points) (e : EdgeL) : List ℕ :=
  e.2.1.filter fun l ↦ evalL d e.2.2.1 (pts.getD l []) ≤ e.2.2.2.2.1

def replaceL (d : ℕ) (pts : Points) (C : CandidateL) (j : ℕ) (e : EdgeL) : CandidateL :=
  let L := leftL d pts e
  let R := e.2.1.filter fun l ↦ l ∉ L
  (C.1.take j ++ [L, R] ++ C.1.drop (j + 1), C.2 ++ [e])

structure RefineCode where
  ref : Refiner
  block : Mode → BlockArgs × ℕ → List EdgeL

/-- Unary fuel caps the scan, each returned block list, and the final candidate list. -/
def refineL (B : RefineCode) (mode : Mode) (q : RefineArgs × ℕ) : List CandidateL :=
  let d := q.1.1
  let k := q.1.2.1
  let ps := q.1.2.2.1
  let pts := q.1.2.2.2.1
  let C := q.1.2.2.2.2
  if C.1.length < k ∧ C.2.length + 1 = C.1.length then
    (((List.range (min C.1.length q.2)).flatMap fun j ↦
      ((B.block mode ((d, k, ps, pts, C.2.length, C.1.getD j []), q.2)).take q.2).map
        (replaceL d pts C j)).take q.2)
  else []

structure RefineSpecL (B : RefineCode) : Prop where
  contract : RefineSpec B.ref
  block_polytime : ∀ mode, ComputableInPolyTime (B.block mode)
    (encPair encBlockArgs encUnary) (encList encEdge)
  polytime : ∀ mode, ComputableInPolyTime (refineL B mode)
    (encPair encRefineArgs encUnary) (encList encCandidate)
  agrees : ∀ mode x fuel, Valid x → need mode x ≤ fuel →
    let ps := Schedule.params mode x.wmin x.k
    let pts := fun l : Fin x.points.length ↦
      fun i : Fin (dim x.points) ↦ (x.points[l]).getD i.val 0
    ∀ C, refineL B mode
      ((dim x.points, x.k, (List.range x.k).map (fun h ↦ paramsList (ps h)),
        x.points, candidateList C), fuel) =
      (B.ref mode x.k ps pts fuel C).map candidateList
  levels_size : ∀ mode x fuel, Valid x → need mode x ≤ fuel →
    let ps := Schedule.params mode x.wmin x.k
    let pts := fun l : Fin x.points.length ↦
      fun i : Fin (dim x.points) ↦ (x.points[l]).getD i.val 0
    ∀ h, h ≤ x.k - 1 →
      (encList encCandidate ((levels B.ref mode x.k ps pts fuel h).map candidateList)).length ≤
        fuel

end ABBKS26.Assembly.Exec
