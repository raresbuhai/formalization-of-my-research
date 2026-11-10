module

public import ABBKS26.Tree.Good
public import ABBKS26.Split.Population

/-!
# Splits and partial clusterings

Stored splits of a node into two parts by a window on a statistic, and their partial
clusterings ([ABBKS26, Definitions 3.26 and 3.27]).
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section


open Matrix

open Common Matrix
open scoped BigOperators
variable {n d : ℕ}

structure Statistic (d : ℕ) where
  A : Matrix (Fin d) (Fin d) ℚ
  b : Fin d → ℚ
  c : ℚ

def Statistic.evalQ (q : Statistic d) (x : Fin d → ℚ) : ℚ :=
  x ⬝ᵥ (q.A *ᵥ x) + q.b ⬝ᵥ x + q.c

def Statistic.eval (q : Statistic d) (x : Vec d) : ℝ :=
  qform (q.A.map (algebraMap ℚ ℝ)) x + (fun i ↦ (q.b i : ℝ)) ⬝ᵥ x + q.c

inductive SplitKind where
  | spectral
  | frobenius
  | mean
  deriving DecidableEq

structure StepParams where
  w : ℚ
  straddle : ℚ
  windowMass : ℚ
  verifyMass : ℚ
  tail : ℚ
  K : ℚ
  WF : ℚ
  DF : ℚ
  R : ℚ
  sigmaSq : ℚ
  subspaceAccuracy : ℚ
  isotropy : ℚ
  momentError : ℚ
  frameAccuracy : ℚ
  contamination : ℚ
  leakage : ℚ
  separation : ℚ

structure Edge (n d : ℕ) where
  depth : ℕ
  parent : Finset (Fin n)
  statistic : Statistic d
  kind : SplitKind
  threshold : ℚ
  lower : ℚ
  upper : ℚ

def Edge.left (e : Edge n d) (x : Fin n → Fin d → ℚ) : Finset (Fin n) :=
  e.parent.filter (fun l ↦ e.statistic.evalQ (x l) ≤ e.threshold)

def Edge.right (e : Edge n d) (x : Fin n → Fin d → ℚ) : Finset (Fin n) :=
  e.parent \ e.left x

def Edge.windowCount (e : Edge n d) (x : Fin n → Fin d → ℚ) : ℕ :=
  (e.parent.filter (fun l ↦ e.lower ≤ e.statistic.evalQ (x l) ∧
    e.statistic.evalQ (x l) ≤ e.upper)).card

def Verify (p : StepParams) (x : Fin n → Fin d → ℚ) (e : Edge n d) : Prop :=
  e.windowCount x ≤ (p.verifyMass : ℚ) * e.parent.card ∧
    p.w * n / 4 ≤ (e.left x).card ∧ p.w * n / 4 ≤ (e.right x).card

instance decidableVerify (p : StepParams) (x : Fin n → Fin d → ℚ) (e : Edge n d) :
    Decidable (Verify p x e) := by
  unfold Verify
  infer_instance

structure Candidate (n d : ℕ) where
  blocks : List (Finset (Fin n))
  path : List (Edge n d)

def root (n d : ℕ) : Candidate n d := ⟨[Finset.univ], []⟩

def replaceBlock (x : Fin n → Fin d → ℚ) (C : Candidate n d)
    (j : ℕ) (e : Edge n d) : Candidate n d :=
  ⟨C.blocks.take j ++ [e.left x, e.right x] ++ C.blocks.drop (j + 1), C.path ++ [e]⟩

def Replays (x : Fin n → Fin d → ℚ) (C : Candidate n d) : Prop :=
  ∃ states : Fin (C.path.length + 1) → Candidate n d,
    states 0 = root n d ∧ states (Fin.last C.path.length) = C ∧
    ∀ h : Fin C.path.length, ∃ j : Fin (states h.castSucc).blocks.length,
      (C.path[h]).parent = (states h.castSucc).blocks[j] ∧
      (C.path[h]).depth = h ∧
      states h.succ = replaceBlock x (states h.castSucc) j C.path[h]

def Accepted (params : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (C : Candidate n d) : Prop := ∀ e ∈ C.path, Verify (params e.depth) x e

/-- Unordered empirical split distance, used only inside RB3. -/
def splitDistance (N A B : Finset (Fin n)) : ℕ :=
  min ((A \ B) ∪ (B \ A)).card ((A \ (N \ B)) ∪ ((N \ B) \ A)).card

/-- Every stored split partitions its parent, with the closed-window tie rule. -/
theorem split_partition
    (e : Edge n d) (x : Fin n → Fin d → ℚ) :
    Disjoint (e.left x) (e.right x) ∧ e.left x ∪ e.right x = e.parent := by
  constructor
  · exact Finset.disjoint_sdiff
  · exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

end

end ABBKS26.Tree
