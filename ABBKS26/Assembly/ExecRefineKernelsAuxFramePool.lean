module

public import ABBKS26.Assembly.ExecRefineKernelsAuxSources

/-!
# Canonical paired P1 certificates

This is the executable starting pool, before any coefficient-size repair. Missing flags
cannot make a certificate eligible, and surplus flags cannot introduce a certificate.
Canonicalization fixes list shapes, without asserting symmetry or a bound on bit lengths.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FramePool

open Common _root_.ABBKS26.Tree FrameAux.Linear FrameAux.Features
open Turing.MultiTapeTM ComputableInPolyTime

def canonical (d : ℕ) (q : StatisticL) : StatisticL :=
  (table d d (fun i j ↦ (q.1.getD i []).getD j 0),
    (List.range d).map (fun i ↦ q.2.1.getD i 0), q.2.2)

/-- Shape normalization preserves the entire decoded quadratic, including its constant. -/
theorem canonical_agrees (d : ℕ) (q : StatisticL) :
    canonical d q = statisticList (statisticOf d q) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [canonical, table, statisticList]
    · intro i hi hi'
      simp only [canonical, table, statisticList, List.getElem_map, List.getElem_range,
        List.getElem_ofFn]
      apply List.ext_getElem
      · simp
      · intro j hj hj'
        simp [statisticOf, matrixOf]
  · apply Prod.ext
    · apply List.ext_getElem
      · simp [canonical, statisticList]
      · intro i hi hi'
        simp [canonical, statisticList, statisticOf, vectorOf]
    · rfl

theorem canonical_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {q : α → StatisticL}
    (hd : ComputableInPolyTime d input encUnary)
    (hq : ComputableInPolyTime q input encStatistic) :
    ComputableInPolyTime (fun x ↦ canonical (d x) (q x)) input encStatistic := by
  unfold canonical
  apply ComputableInPolyTime.prod
  · apply table_polytime hd hd
    fun_prop
  · apply ComputableInPolyTime.prod
    · apply mapWithInput (range.comp hd)
      fun_prop
    · fun_prop

def typed (d : ℕ) (f : FrameData) : List (Statistic d × Bool) :=
  (f.2.2.2.2.1.zip f.2.2.2.2.2).map (fun q ↦ (statisticOf d q.1, q.2))

def list (d : ℕ) (f : FrameData) : List (StatisticL × Bool) :=
  (f.2.2.2.2.1.zip f.2.2.2.2.2).map (fun q ↦ (canonical d q.1, q.2))

/-- Flags are paired by their original index, never by separate filtering of two lists. -/
theorem paired_agrees (d : ℕ) (f : FrameData) :
    list d f = (typed d f).map (fun q ↦ (statisticList q.1, q.2)) := by
  simp only [list, typed, List.map_map, canonical_agrees]
  rfl

theorem paired_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {f : α → FrameData}
    (hd : ComputableInPolyTime d input encUnary)
    (hf : ComputableInPolyTime f input encFrameData) :
    ComputableInPolyTime (fun x ↦ list (d x) (f x)) input
      (encList (encPair encStatistic encBool)) := by
  unfold list
  have hqs : ComputableInPolyTime (fun x ↦ (f x).2.2.2.2.1)
      input (encList encStatistic) := by fun_prop
  have hflags : ComputableInPolyTime (fun x ↦ (f x).2.2.2.2.2)
      input (encList encBool) := by fun_prop
  apply mapWithInput ((ComputableInPolyTime.zip encStatistic encBool).comp
    (hqs.prod hflags))
  exact (canonical_polytime (hd.comp (fst _ _)) (by fun_prop)).prod (by fun_prop)

/-- The concrete P1 call already supplies a polynomial-time paired pool on junk inputs. -/
def run (F : FrameCode) (q : FrameArgs × ℕ) : List (StatisticL × Bool) :=
  list q.1.1 (F.run .centered q)

theorem run_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (run F) (encPair encFrameArgs encUnary)
      (encList (encPair encStatistic encBool)) :=
  paired_polytime (by fun_prop) (hF.polytime .centered)


end ABBKS26.Assembly.Exec.RefineSynth.FramePool
