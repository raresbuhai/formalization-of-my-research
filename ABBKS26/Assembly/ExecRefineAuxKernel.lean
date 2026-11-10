module

public import ABBKS26.Assembly.ExecRefineAuxData

/-!
# Local kernel obligations

A kernel contains a typed block procedure and its rational list implementation. The typed
procedure is a new witness: it need not equal the classical `Tree.refine` or its block code.
The bit envelope below is a bound on individual returned edges, independent of global fuel.
It pays for every weak-partition block and persistent history in a complete tree level.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime

/-- An upper bound on the binary encoding of any subset of `Fin n`. -/
def indexBits (n : ℕ) : ℕ := n * (2 * (Nat.log2 n + 1) + 1)

/-- At most `k` blocks and `k` persistent edges, including every framing bit. -/
def candidateBits (n k bits : ℕ) : ℕ :=
  2 * (k * (2 * indexBits n + 1)) + 1 + k * (2 * bits + 1)

/-- The branch count is a parameter factor; sample bits enter only the edge envelope. -/
def levelBits (n k branches bits : ℕ) : ℕ :=
  branches ^ (k - 1) * (2 * candidateBits n k bits + 1)

structure Kernel where
  run : BlockRefiner
  block : Mode → BlockArgs × ℕ → List EdgeL
  bits : Input → ℕ

/-- A single mode of the existing block contract, with no additional acceptance test. -/
def BlockContract (mode : Mode) (run : BlockRefiner) : Prop :=
  ∀ {n d} k params (x : Fin n → Fin d → ℚ) fuel h N,
    (run mode k params x fuel h N).length ≤ stepBranchCap mode k (params h) ∧
    (∀ e ∈ run mode k params x fuel h N, e.parent = N ∧ e.depth = h) ∧
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared mode M ε w η Δ D ω r params →
      localBudget mode k n d params ≤ fuel → h < k - 1 →
      I.Nonempty → leakage ω N I ≤ leakageBudget params η h → w * n / 4 ≤ N.card →
      (∀ e ∈ run mode k params x fuel h N, ScaleValid M I (params h) e) ∧
      (2 ≤ I.card → ∃ e ∈ run mode k params x fuel h N, Verify (params h) x e)

/-- Agreement is required on every parent subset, including junk nodes. The semantic
contract supplies analytic correctness separately, only under its prepared-node hypotheses. -/
structure KernelRepresentation (mode : Mode) (K : Kernel) : Prop where
  polytime : ComputableInPolyTime (K.block mode)
    (encPair encBlockArgs encUnary) (encList encEdge)
  agrees : ∀ x fuel, Valid x → need mode x ≤ fuel →
    let ps := Schedule.params mode x.wmin x.k
    ∀ h, h < x.k - 1 → ∀ N : Finset (Fin x.points.length),
      K.block mode ((dim x.points, x.k,
        (List.range x.k).map (fun j ↦ paramsList (ps j)), x.points, h, indexList N), fuel) =
      (K.run mode x.k ps (inputPoints x) fuel h N).map edgeList
  edge_size : ∀ x fuel, Valid x → need mode x ≤ fuel →
    let ps := Schedule.params mode x.wmin x.k
    ∀ h, h < x.k - 1 → ∀ N e,
      e ∈ K.run mode x.k ps (inputPoints x) fuel h N →
        (encEdge (edgeList e)).length ≤ K.bits x
  storage : ∀ x, Valid x →
    levelBits x.points.length x.k
      (branchCap mode x.k (Schedule.params mode x.wmin x.k)) (K.bits x) ≤ need mode x

/-- The analytic contract and the machine certificate concern the same local witness. -/
structure KernelSpec (mode : Mode) (K : Kernel) : Prop
    extends KernelRepresentation mode K where
  contract : BlockContract mode K.run

/-- Both centered stages refer to the very same effective P1 call. FAR is only an analytic
case split in the completeness proof; it is not an extra construction-stage window test. -/
def centeredFar (F : FrameCode) {n k d : ℕ} (M : Mixture k d)
    (ω : Fin n → Triple k d) (r : Rounding k d) (p : StepParams)
    (fuel : ℕ) (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) : Prop :=
  Robust.Far (ABBKS26.RefineAux.roundedReference M ω r N I hI)
    (frameProc F d ((N.sort (· ≤ ·)).map fun l ↦ List.ofFn fun i ↦
      r ((ω l).1, (ω l).2.2) i) .centered (p.w / 2) |p.R| p.frameAccuracy fuel)
    (|p.R| : ℚ) (20 / ((p.w / 2 : ℚ) : ℝ))

/-- RB3 consumes the Frobenius cap; the unfiltered spectral list consumes its complement. -/
def centeredStageCap (far : Bool) (k : ℕ) (p : StepParams) : ℕ :=
  if far then frobCap k else stepBranchCap .centered k p - frobCap k

/-- Each centered stage supplies valid scales on every prepared node. RB3 supplies a verified
split in the FAR case, and the spectral net supplies one in the complementary case. -/
def CenteredStageContract (F : FrameCode) (far : Bool) (run : BlockRefiner) : Prop :=
  ∀ {n d} k params (x : Fin n → Fin d → ℚ) fuel h N,
    (run .centered k params x fuel h N).length ≤ centeredStageCap far k (params h) ∧
    (∀ e ∈ run .centered k params x fuel h N, e.parent = N ∧ e.depth = h) ∧
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .centered M ε w η Δ D ω r params →
      localBudget .centered k n d params ≤ fuel → h < k - 1 →
      ∀ (hI : I.Nonempty), leakage ω N I ≤ leakageBudget params η h →
      w * n / 4 ≤ N.card →
      (∀ e ∈ run .centered k params x fuel h N, ScaleValid M I (params h) e) ∧
      (2 ≤ I.card →
        (if far then centeredFar F M ω r (params h) fuel N I hI else
          ¬ centeredFar F M ω r (params h) fuel N I hI) →
        ∃ e ∈ run .centered k params x fuel h N, Verify (params h) x e)

structure CenteredStageSpec (F : FrameCode) (far : Bool) (K : Kernel) : Prop
    extends KernelRepresentation .centered K where
  contract : CenteredStageContract F far K.run

/-- Only RB3's subkernel verifies and merges; the spectral subkernel is appended as is. -/
def centeredKernel (A S : Kernel) : Kernel where
  run mode := match mode with
    | .centered => fun k ps x fuel h N ↦
        A.run .centered k ps x fuel h N ++ S.run .centered k ps x fuel h N
    | .identical => fun _ _ _ _ _ _ ↦ []
  block mode := match mode with
    | .centered => fun q ↦ A.block .centered q ++ S.block .centered q
    | .identical => fun _ ↦ []
  bits x := max (A.bits x) (S.bits x)

/-- The mode switch is outside the block scan, so one block's failure cannot erase another. -/
def jointRun (C I : Kernel) : BlockRefiner :=
  fun mode ↦ match mode with
    | .centered => C.run .centered
    | .identical => I.run .identical

def jointCode (C I : Kernel) : RefineCode where
  ref := refinerFromBlocks (jointRun C I)
  block mode := match mode with
    | .centered => C.block .centered
    | .identical => I.block .identical

end ABBKS26.Assembly.Exec.RefineSynth
