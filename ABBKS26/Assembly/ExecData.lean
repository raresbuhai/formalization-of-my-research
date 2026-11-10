module

public import ABBKS26.Assembly.Schedule
public import Background.PolyTime.Lists
public import Background.SumOfSquares.Algorithm.PolyTime

/-!
# List representations used by the executable layer

The records below contain only rational numbers, natural numbers and lists. In particular,
no population, real spectral decomposition, or hidden clean subset is an executable input.
The typed decoders are used only in agreement statements.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Select
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

abbrev Vector := List ℚ
abbrev MatrixL := List Vector
abbrev StatisticL := MatrixL × Vector × ℚ
abbrev EstimateL := Vector × MatrixL
abbrev EdgeL := ℕ × List ℕ × StatisticL × ℕ × ℚ × ℚ × ℚ
abbrev CandidateL := List (List ℕ) × List EdgeL
abbrev LearnedL := CandidateL × List (Option EstimateL)
abbrev TestL := StatisticL × ℚ × Bool

abbrev encVector := encList encRat
abbrev encMatrix := encList encVector
abbrev encStatistic := encPair encMatrix (encPair encVector encRat)
abbrev encEstimate := encPair encVector encMatrix
abbrev encIndices := encList encNat
abbrev encEdge := encPair encNat (encPair encIndices (encPair encStatistic
  (encPair encNat (encPair encRat (encPair encRat encRat)))))
abbrev encCandidate := encPair (encList encIndices) (encList encEdge)
abbrev encLearned := encPair encCandidate (encList (Turing.MultiTapeTM.encOption encEstimate))
abbrev encTest := encPair encStatistic (encPair encRat Turing.MultiTapeTM.encBool)
abbrev encPadded := Encoding.encPair encInput Encoding.encUnary

def pointsOf {n d : ℕ} (x : Fin n → Fin d → ℚ) : Points :=
  List.ofFn fun l ↦ List.ofFn (x l)

def inputPoints (x : Input) : Fin x.points.length → Fin (dim x.points) → ℚ :=
  fun l i ↦ (x.points[l]).getD i.val 0

def vectorOf (d : ℕ) (v : Vector) : Fin d → ℚ := fun i ↦ v.getD i.val 0

def matrixOf (d : ℕ) (A : MatrixL) : Matrix (Fin d) (Fin d) ℚ :=
  fun i j ↦ (A.getD i.val []).getD j.val 0

def statisticOf (d : ℕ) (q : StatisticL) : Statistic d :=
  ⟨matrixOf d q.1, vectorOf d q.2.1, q.2.2⟩

def estimateOf (d : ℕ) (E : EstimateL) : Robust.Estimate d :=
  ⟨vectorOf d E.1, matrixOf d E.2⟩


def indexList {n : ℕ} (N : Finset (Fin n)) : List ℕ :=
  (N.sort (· ≤ ·)).map Fin.val

def statisticList {d : ℕ} (q : Statistic d) : StatisticL :=
  (List.ofFn fun i ↦ List.ofFn (q.A i), List.ofFn q.b, q.c)

def estimateList {d : ℕ} (E : Robust.Estimate d) : EstimateL :=
  (List.ofFn E.mean, List.ofFn fun i ↦ List.ofFn (E.cov i))

def edgeList {n d : ℕ} (e : Edge n d) : EdgeL :=
  (e.depth, indexList e.parent, statisticList e.statistic,
    match e.kind with | .spectral => 0 | .frobenius => 1 | .mean => 2,
    e.threshold, e.lower, e.upper)

def candidateList {n d : ℕ} (C : Candidate n d) : CandidateL :=
  (C.blocks.map indexList, C.path.map edgeList)

def learnedList {n d : ℕ} (L : Learned n d) : LearnedL :=
  (candidateList L.candidate, L.estimates.map (Option.map estimateList))

def testList {d : ℕ} (T : PairTest d) : TestL :=
  (statisticList T.statistic, T.threshold, T.firstOnLeft)

def testOf (d : ℕ) (T : TestL) : PairTest d :=
  ⟨statisticOf d T.1, T.2.1, T.2.2⟩

def paramsList (p : StepParams) : List ℚ :=
  [p.w, p.straddle, p.windowMass, p.verifyMass, p.tail, p.K, p.WF, p.DF, p.R,
    p.sigmaSq, p.subspaceAccuracy, p.isotropy, p.momentError, p.frameAccuracy,
    p.contamination, p.leakage, p.separation]

/-- This is definitionally the validation predicate in `Alg`, without an import cycle. -/
def Valid (x : Input) : Prop :=
  0 < x.wmin ∧ x.wmin ≤ 1 ∧ (x.k : ℚ) * x.wmin ≤ 1 ∧ 1 ≤ x.k ∧
    0 < x.δ ∧ ∀ row ∈ x.points, row.length = dim x.points

instance (x : Input) : Decidable (Valid x) := by
  unfold Valid
  infer_instance

/-- The frozen budget, repeated here so component files need not import `Alg`. -/
noncomputable def need (mode : Mode) (x : Input) : ℕ :=
  if x.k ≤ 1 then ((encInput x).length + 2) ^ 100 else
  (Schedule.ledger mode x.wmin x.k + 2) *
    localBudget mode x.k x.points.length (dim x.points) (Schedule.params mode x.wmin x.k) *
      ((encInput x).length + 2) ^ 100

/-- Every intermediate stored object is checked before the next loop iteration. -/
def cap {α : Type} (enc : α ↪ List Bool) (fuel : ℕ) (fallback a : α) : α :=
  if (enc a).length ≤ fuel then a else fallback

theorem cap_eq {α : Type} (enc : α ↪ List Bool) (fuel : ℕ) (fallback a : α)
    (h : (enc a).length ≤ fuel) : cap enc fuel fallback a = a := by
  simp [cap, h]

theorem pointsOf_get {n d : ℕ} (x : Fin n → Fin d → ℚ) (l : Fin n) (i : Fin d) :
    ((pointsOf x).getD l.val []).getD i.val 0 = x l i := by
  simp [pointsOf, List.getD_eq_getElem?_getD]

@[simp] theorem vector_roundtrip {d : ℕ} (v : Fin d → ℚ) :
    vectorOf d (List.ofFn v) = v := by
  funext i
  simp [vectorOf, List.getD_eq_getElem?_getD]

@[simp] theorem matrix_roundtrip {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :
    matrixOf d (List.ofFn fun i ↦ List.ofFn (A i)) = A := by
  funext i j
  simp [matrixOf, List.getD_eq_getElem?_getD]

theorem estimate_roundtrip {d : ℕ} (E : Robust.Estimate d) :
    estimateOf d (estimateList E) = E := by
  cases E
  simp [estimateOf, estimateList]

theorem statistic_roundtrip {d : ℕ} (q : Statistic d) :
    statisticOf d (statisticList q) = q := by
  cases q
  simp [statisticOf, statisticList]


/-- The point projection uses the existing binary input encoding. -/
theorem points_polytime : ComputableInPolyTime Input.points encInput encPoints := by
  have h : ComputableInPolyTime
      (fun x : Input ↦ (x.k, x.wmin, x.Δ, x.δ, x.points)) encInput
      (encPair encNat (encPair encRat (encPair encRat (encPair encRat encPoints)))) :=
    of_eq fun _ ↦ rfl
  exact (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp h)))

theorem k_polytime : ComputableInPolyTime Input.k encInput encNat := by
  have h : ComputableInPolyTime
      (fun x : Input ↦ (x.k, x.wmin, x.Δ, x.δ, x.points)) encInput
      (encPair encNat (encPair encRat (encPair encRat (encPair encRat encPoints)))) :=
    of_eq fun _ ↦ rfl
  exact (fst _ _).comp h

theorem zero_labels_polytime : ComputableInPolyTime
    (fun x : Input ↦ List.replicate x.points.length 0) encInput encOutput := by
  exact replicate ((length_list _).comp points_polytime) (const 0)

end ABBKS26.Assembly.Exec
