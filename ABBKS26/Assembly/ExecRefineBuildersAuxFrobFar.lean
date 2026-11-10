module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobVariance
public import ABBKS26.Assembly.ExecRefineSourcesAuxBuilders

/-! A FAR certificate of an arbitrary specified frame gives a verified threshold. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobFar

open Common _root_.ABBKS26.Tree Matrix Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

variable {n k d : ℕ}


/-- The executable call selects the parent rows and uses the shared centered parameters. -/
def callArgs (a : Args) : FrameArgs × ℕ :=
  ((a.1.1, a.1.2.2.2.2.2.map (fun i ↦ a.1.2.2.2.1.getD i []),
    field a 0 / 2, |field a 8|, field a 13), a.2)

theorem callArgs_polytime : ComputableInPolyTime callArgs encArgs
    (encPair encFrameArgs encUnary) := by
  have hp : ComputableInPolyTime (fun a : Args ↦ a.1.2.2.2.1) encArgs encPoints := by
    fun_prop
  have hn : ComputableInPolyTime (fun a : Args ↦ a.1.2.2.2.2.2) encArgs encIndices := by
    fun_prop
  have hs : ComputableInPolyTime
      (fun a : Args ↦ a.1.2.2.2.2.2.map (fun i ↦ a.1.2.2.2.1.getD i []))
      encArgs encPoints := by
    apply mapWithInput (encB := encVector) hn
    exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector)
      [] (hp.comp (fst _ _)).tidy (snd _ _).tidy)
  have hd : ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary := by fun_prop
  exact (hd.prod (hs.prod ((rat_div' (field_polytime 0) (const 2)).prod
    ((rat_abs' (field_polytime 8)).prod (field_polytime 13))))).prod (by fun_prop)

/-- The paired rational frame pool before coefficient rounding and the scanned-edge guard. -/
def run (F : FrameCode) (a : Args) : PoolL := FramePool.run F (callArgs a)

theorem run_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (run F) encArgs encPool :=
  (FramePool.run_polytime F hF).comp callArgs_polytime

theorem callArgs_agrees (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (N : Finset (Fin n)) (hh : h < k) :
    callArgs (args k ps x h N, fuel) = ((d,
      (N.sort (· ≤ ·)).map (fun l ↦ List.ofFn (x l)),
      (ps h).w / 2, |(ps h).R|, (ps h).frameAccuracy), fuel) := by
  simp only [callArgs, field_args k ps x fuel h N hh]
  simp [paramsList, args, indexList, List.map_map, pointsOf,
    List.getD_eq_getElem?_getD]

/-- The typed paired pool for the exact call used by `centeredFar`. -/
def pool (F : FrameCode) (p : StepParams) (x : Fin n → Fin d → ℚ)
    (fuel : ℕ) (N : Finset (Fin n)) : List (Statistic d × Bool) :=
  FramePool.typed d (F.run .centered ((d,
    (N.sort (· ≤ ·)).map (fun l ↦ List.ofFn (x l)),
    p.w / 2, |p.R|, p.frameAccuracy), fuel))

theorem run_agrees (F : FrameCode) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n)) (hh : h < k) :
    run F (args k ps x h N, fuel) =
      (pool F (ps h) x fuel N).map (fun q ↦ (statisticList q.1, q.2)) := by
  unfold run
  rw [callArgs_agrees k ps x fuel h N hh]
  exact FramePool.paired_agrees _ _


end ABBKS26.Assembly.Exec.RefineSynth.FrobFar
