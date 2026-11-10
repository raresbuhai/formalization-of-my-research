module

public import ABBKS26.Assembly.ExecRefineKernelsAuxThresholds
public import ABBKS26.Assembly.ExecRefineAuxKernel

/-!
# Sources and compilers for local refinement lists

A source returns rational certificates, or two lists to be crossed. The compilers below
own the node metadata and the RB3 loop. A source's typed procedure is a compatible new
witness; none of these interfaces require equality to a classical subspace choice.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.Sources

open Common _root_.ABBKS26.Tree
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

abbrev NodeProc (α : ℕ → Type) := {n d : ℕ} → ℕ → (ℕ → StepParams) →
  (Fin n → Fin d → ℚ) → ℕ → ℕ → Finset (Fin n) → α d

def args {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (h : ℕ) (N : Finset (Fin n)) : BlockArgs :=
  (d, k, (List.range k).map (fun j ↦ paramsList (ps j)), pointsOf x, h, indexList N)

/-- The list representation of a rectangular input is recovered without changing indices. -/
theorem points_input (x : Input) (hx : Valid x) : pointsOf (inputPoints x) = x.points := by
  unfold inputPoints
  apply List.ext_getElem
  · simp [pointsOf]
  · intro i hi hi'
    simp only [pointsOf, List.getElem_ofFn]
    have hr := hx.2.2.2.2.2 _ (List.getElem_mem hi')
    apply List.ext_getElem
    · simpa using hr.symm
    · intro j hj hj'
      simp [List.getD_eq_getElem?_getD, hj']

theorem points_decode {n d : ℕ} (x : Fin n → Fin d → ℚ) :
    (fun l ↦ vectorOf d ((pointsOf x).getD l.val [])) = x := by
  funext l i
  exact pointsOf_get x l i

/-- Binary depth lookup is total even for an absent or malformed schedule row. -/
def field (q : BlockArgs × ℕ) (j : ℕ) : ℚ :=
  ((q.1.2.2.1).getD q.1.2.2.2.2.1 []).getD j 0

theorem field_args {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n)) (hh : h < k) (j : ℕ) :
    field (args k ps x h N, fuel) j = (paramsList (ps h)).getD j 0 := by
  unfold field args
  rw [FrameAux.Linear.getD_map_range _ _ hh]

theorem field_polytime (j : ℕ) : ComputableInPolyTime (fun q ↦ field q j)
    (encPair encBlockArgs encUnary) encRat := by
  have hp : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.2.2.1)
      (encPair encBlockArgs encUnary) encPoints := by fun_prop
  have hh : ComputableInPolyTime (fun q : BlockArgs × ℕ ↦ q.1.2.2.2.2.1)
      (encPair encBlockArgs encUnary) encNat := by fun_prop
  have hr : ComputableInPolyTime
      (fun q : BlockArgs × ℕ ↦ q.1.2.2.1.getD q.1.2.2.2.2.1 [])
      (encPair encBlockArgs encUnary) encVector := .of_tidy
    (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector)
      [] hp.tidy hh.tidy)
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encL := encVector) 0
    hr.tidy (const j).tidy)

structure FrobSource where
  pool : NodeProc (fun d ↦ List (Statistic d × Bool))
  code : BlockArgs × ℕ → List (StatisticL × Bool)
  bits : Input → ℕ

def frobRaw (P : FrobSource) : {n d : ℕ} → ℕ → (ℕ → StepParams) →
    (Fin n → Fin d → ℚ) → ℕ → ℕ → Finset (Fin n) → List (Edge n d) :=
  fun k ps x fuel h N ↦ Thresholds.pool (pointsOf x) h N (P.pool k ps x fuel h N) (ps h).WF

/-- Only RB3 verifies and merges. The source's flags stay attached to their certificates. -/
def frobKernel (P : FrobSource) : Kernel where
  run _ k ps x fuel h N := frobSplits (ps h) k x (frobRaw P k ps x fuel h N)
  block _ q := RB3.run q.1.1 q.1.2.2.2.1.length (field q 0) (field q 3)
    q.1.2.2.2.1 q.1.2.1
    (Thresholds.poolL q.1.1 q.1.2.2.2.1 q.1.2.2.2.2.1 q.1.2.2.2.2.2
      (P.code q) (field q 6))
  bits := P.bits

/-- Source storage pays for raw records, so the packing compiler can only decrease it.
The envelope is independent of global fuel and covers every parent subset. -/
structure FrobCertificate (P : FrobSource) : Prop where
  polytime : ComputableInPolyTime P.code (encPair encBlockArgs encUnary)
    (encList (encPair encStatistic encBool))
  agrees : ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    P.code (args k ps x h N, fuel) =
      (P.pool k ps x fuel h N).map (fun q ↦ (statisticList q.1, q.2))
  edge_size : ∀ x fuel, Valid x → need .centered x ≤ fuel →
    ∀ h, h < x.k - 1 → ∀ N e,
      e ∈ frobRaw P x.k (Schedule.params .centered x.wmin x.k) (inputPoints x) fuel h N →
      (encEdge (edgeList e)).length ≤ P.bits x
  storage : ∀ x, Valid x → levelBits x.points.length x.k
    (branchCap .centered x.k (Schedule.params .centered x.wmin x.k)) (P.bits x) ≤
      need .centered x

/-- These are obligations on eligible statistics, before scanning thresholds or packing. -/
def FrobGeometry (F : FrameCode) (P : FrobSource) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .centered M ε w η Δ D ω r ps →
      localBudget .centered k n d ps ≤ fuel → h < k - 1 →
      ∀ (hI : I.Nonempty), leakage ω N I ≤ leakageBudget ps η h → w * n / 4 ≤ N.card →
      (∀ q, (q, true) ∈ P.pool k ps x fuel h N → ∀ j ∈ I, ProbabilityTheory.variance
        (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
        (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
          (40 / ((ps h).w : ℝ)) ^ 2) ∧
      (2 ≤ I.card → centeredFar F M ω r (ps h) fuel N I hI →
        ∃ q, (q, true) ∈ P.pool k ps x fuel h N ∧ ∃ t,
          Verify (ps h) x (Thresholds.typedEdge h N q (ps h).WF t))

abbrev Window := ℚ × ℚ × ℚ
abbrev encWindow := encPair encRat (encPair encRat encRat)
abbrev PairData (d : ℕ) := List (Statistic d) × List Window
abbrev PairDataL := List StatisticL × List Window
abbrev encPairData := encPair (encList encStatistic) (encList encWindow)

def pairDataList {d : ℕ} (p : PairData d) : PairDataL := (p.1.map statisticList, p.2)

def pairEdge {n d : ℕ} (mode : Mode) (h : ℕ) (N : Finset (Fin n))
    (q : Statistic d) (t : Window) : Edge n d :=
  ⟨h, N, q, (match mode with | .centered => .spectral | .identical => .mean),
    t.1, t.2.1, t.2.2⟩

def pairEdgeL (mode : Mode) (h : ℕ) (N : List ℕ) (q : StatisticL)
    (t : Window) : EdgeL :=
  (h, N, q, (match mode with | .centered => 0 | .identical => 2), t.1, t.2.1, t.2.2)

/-- The Cartesian product is appended verbatim, including unsuccessful window pairs. -/
def pairs {n d : ℕ} (mode : Mode) (h : ℕ) (N : Finset (Fin n))
    (p : PairData d) : List (Edge n d) :=
  p.1.flatMap fun q ↦ p.2.map (pairEdge mode h N q)

def pairsL (mode : Mode) (h : ℕ) (N : List ℕ) (p : PairDataL) : List EdgeL :=
  p.1.flatMap fun q ↦ p.2.map (pairEdgeL mode h N q)

structure PairSource where
  data : NodeProc PairData
  code : BlockArgs × ℕ → PairDataL
  bits : Input → ℕ

def pairKernel (mode : Mode) (P : PairSource) : Kernel where
  run _ k ps x fuel h N := pairs mode h N (P.data k ps x fuel h N)
  block _ q := pairsL mode q.1.2.2.2.2.1 q.1.2.2.2.2.2 (P.code q)
  bits := P.bits

structure PairCertificate (mode : Mode) (P : PairSource) : Prop where
  polytime : ComputableInPolyTime P.code (encPair encBlockArgs encUnary) encPairData
  agrees : ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    P.code (args k ps x h N, fuel) = pairDataList (P.data k ps x fuel h N)
  edge_size : ∀ x fuel, Valid x → need mode x ≤ fuel →
    ∀ h, h < x.k - 1 → ∀ N e,
      e ∈ pairs mode h N
        (P.data x.k (Schedule.params mode x.wmin x.k) (inputPoints x) fuel h N) →
      (encEdge (edgeList e)).length ≤ P.bits x
  storage : ∀ x, Valid x → levelBits x.points.length x.k
    (branchCap mode x.k (Schedule.params mode x.wmin x.k)) (P.bits x) ≤ need mode x

/-- The branch allowance bounds the product, not either factor separately. -/
def PairCount (mode : Mode) (P : PairSource) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    let p := P.data k ps x fuel h N
    p.1.length * p.2.length ≤
      if mode = .centered then centeredStageCap false k (ps h)
      else stepBranchCap .identical k (ps h)

/-- Population validity applies to every retained pair; completeness only needs one pair. -/
def PairGeometry (mode : Mode) (F : FrameCode) (P : PairSource) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared mode M ε w η Δ D ω r ps →
      localBudget mode k n d ps ≤ fuel → h < k - 1 →
      ∀ (hI : I.Nonempty), leakage ω N I ≤ leakageBudget ps η h → w * n / 4 ≤ N.card →
      (∀ q ∈ (P.data k ps x fuel h N).1, ∀ t ∈ (P.data k ps x fuel h N).2,
        ScaleValid M I (ps h) (pairEdge mode h N q t)) ∧
      (2 ≤ I.card →
        (mode = .centered → ¬ centeredFar F M ω r (ps h) fuel N I hI) →
        ∃ q ∈ (P.data k ps x fuel h N).1, ∃ t ∈ (P.data k ps x fuel h N).2,
          Verify (ps h) x (pairEdge mode h N q t))

end ABBKS26.Assembly.Exec.RefineSynth.Sources
