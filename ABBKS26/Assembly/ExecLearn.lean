module

public import ABBKS26.Assembly.ExecFrame
public import ABBKS26.Assembly.ExecLearnAux

/-! # Single-component learning and the per-candidate map -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Select
open Turing.MultiTapeTM ComputableInPolyTime

abbrev LearnArgs := ℕ × Points × List ℕ
abbrev encLearnArgs := encPair encUnary (encPair encPoints encIndices)

structure LearnCode where
  learn : Learner
  run : Mode → LearnArgs × ℕ → Option EstimateL

structure LearnSpecL (L : LearnCode) : Prop where
  contract : LearnerSpec L.learn
  polytime : ∀ mode, ComputableInPolyTime (L.run mode)
    (encPair encLearnArgs encUnary) (encOption encEstimate)
  agrees : ∀ {n d} mode (x : Fin n → Fin d → ℚ) N fuel,
    L.run mode ((d, pointsOf x, indexList N), fuel) =
      (L.learn mode x N fuel).map estimateList

/-- Replace the semantic resilient-subset learner by the single-component P1 procedure. -/
theorem exists_learn_code (F : FrameCode) (hF : FrameSpec F) :
    ∃ L : LearnCode, LearnSpecL L := by
  have _ := hF
  let L : LearnCode :=
    { learn := fun {_ d} _ x N fuel ↦
        (LearnAux.run ((d, pointsOf x, indexList N), fuel)).map (estimateOf d)
      run := fun _ ↦ LearnAux.run }
  refine ⟨L, ?_, fun _ ↦ LearnAux.run_polytime, ?_⟩
  · intro n k d mode M ε w η Δ D ω r params fuel hp hf N j hl hN
    exact LearnAux.run_accurate mode M ε w η Δ D ω r params fuel hp hf N j hl hN
  · intro n d mode x N fuel
    change LearnAux.run ((d, pointsOf x, indexList N), fuel) =
      ((LearnAux.run ((d, pointsOf x, indexList N), fuel)).map (estimateOf d)).map
        estimateList
    rw [Option.map_map]
    exact (LearnAux.run_canonical _).symm

/-- Learning precedes final path acceptance, including for candidates on junk branches. -/
def learnAllL (L : LearnCode) (mode : Mode) (d : ℕ) (pts : Points) (fuel : ℕ)
    (Cs : List CandidateL) : List LearnedL :=
  Cs.map fun C ↦ (C, C.1.map fun N ↦ L.run mode ((d, pts, N), fuel))

theorem learn_all_agrees (L : LearnCode) (hL : LearnSpecL L) {n d : ℕ}
    (mode : Mode) (x : Fin n → Fin d → ℚ) (fuel : ℕ) (Cs : List (Candidate n d)) :
    learnAllL L mode d (pointsOf x) fuel (Cs.map candidateList) =
      (learnAll L.learn mode x fuel Cs).map learnedList := by
  simp only [learnAllL, learnAll, List.map_map, Function.comp_def, learnedList, candidateList]
  congr 1
  funext C
  simp only [Prod.mk.injEq, true_and]
  congr 1
  funext N
  exact hL.agrees mode x N fuel

end ABBKS26.Assembly.Exec
