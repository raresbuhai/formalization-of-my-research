module

public import ABBKS26.Assembly.ExecRefineAuxData

/-! Polynomial-time certificates for the refiner's fixed list wrapper. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree FrameAux.Features
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

@[fun_prop] theorem eval_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {q : α → StatisticL} {v : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hq : ComputableInPolyTime q input encStatistic)
    (hv : ComputableInPolyTime v input encVector) :
    ComputableInPolyTime (fun x ↦ evalL (d x) (q x) (v x)) input encRat := by
  unfold evalL
  apply rat_add'
  · apply rat_add'
    · apply sum_polytime hd
      apply sum_polytime (hd.comp (fst _ _))
      fun_prop
    · apply sum_polytime hd
      fun_prop
  · fun_prop

@[fun_prop] theorem left_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {e : α → EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime pts input encPoints)
    (he : ComputableInPolyTime e input encEdge) :
    ComputableInPolyTime (fun x ↦ leftL (d x) (pts x) (e x)) input encIndices := by
  unfold leftL
  apply filterWithInput (by fun_prop)
  apply rat_le' (eval_polytime (hd.comp (fst _ _)) (by fun_prop) ?_) (by fun_prop)
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector) []
    (hp.comp (fst _ _)).tidy (snd _ _).tidy)

@[fun_prop] theorem replace_polytime {α : Type} {input : α ↪ List Bool}
    {d j : α → ℕ} {pts : α → Points} {C : α → CandidateL} {e : α → EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime pts input encPoints)
    (hC : ComputableInPolyTime C input encCandidate)
    (hj : ComputableInPolyTime j input encUnary)
    (he : ComputableInPolyTime e input encEdge) :
    ComputableInPolyTime (fun x ↦ replaceL (d x) (pts x) (C x) (j x) (e x))
      input encCandidate := by
  have hl := left_polytime hd hp he
  have hr : ComputableInPolyTime
      (fun x ↦ (e x).2.1.filter fun l ↦ l ∉ leftL (d x) (pts x) (e x))
      input encIndices := by
    apply filterWithInput (by fun_prop)
    exact bool_not.comp (decide_mem (hl.comp (fst _ _)) (snd _ _))
  unfold replaceL
  fun_prop

/-- The wrapper is polynomial on all lists, including noncanonical indices and junk states.
Its polynomial exponent is absolute once the supplied block program is fixed. -/
theorem refine_polytime (B : RefineCode) (mode : Mode)
    (hb : ComputableInPolyTime (B.block mode)
      (encPair encBlockArgs encUnary) (encList encEdge)) :
    ComputableInPolyTime (refineL B mode)
      (encPair encRefineArgs encUnary) (encList encCandidate) := by
  let E := encPair encRefineArgs encUnary
  have hq : ComputableInPolyTime (fun q : RefineArgs × ℕ ↦ q.1) E encRefineArgs :=
    fst _ _
  have hf : ComputableInPolyTime (fun q : RefineArgs × ℕ ↦ q.2) E encUnary := snd _ _
  have hd := (fst _ _).comp hq
  have hk := (fst _ _).comp ((snd _ _).comp hq)
  have hps := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hq))
  have hp := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hq)))
  have hC := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hq)))
  have hlen := (length_list encIndices).comp ((fst _ _).comp hC)
  have hdepth := (length_list encEdge).comp ((snd _ _).comp hC)
  have hg : ComputableInPolyTime (fun q : RefineArgs × ℕ ↦
      decide (q.1.2.2.2.2.1.length < q.1.2.1 ∧
        q.1.2.2.2.2.2.length + 1 = q.1.2.2.2.2.1.length)) E encBool := by
    apply bool_and'
    · exact binary_lt' (unary_to_binary.comp hlen) hk
    · exact .of_tidy (ComputableTidilyInPolyTime.unary_beq
        (unary_add' hdepth (const 1)).tidy hlen.tidy)
  have hcount := (ComputableInPolyTime.of_tidy
    ComputableTidilyInPolyTime.unary_min).comp (hlen.prod hf)
  have hb' : ComputableInPolyTime
      (fun p : (RefineArgs × ℕ) × ℕ ↦
        B.block mode ((p.1.1.1, p.1.1.2.1, p.1.1.2.2.1, p.1.1.2.2.2.1,
          p.1.1.2.2.2.2.2.length, p.1.1.2.2.2.2.1.getD p.2 []), p.1.2))
      (encPair E encUnary) (encList encEdge) := by
    apply hb.comp
    exact ((hd.comp (fst _ _)).prod ((hk.comp (fst _ _)).prod
      ((hps.comp (fst _ _)).prod ((hp.comp (fst _ _)).prod
        ((unary_to_binary.comp (hdepth.comp (fst _ _))).prod
          (listGetDWithInput (((fst _ _).comp hC).comp (fst _ _)) (snd _ _) [])))))).prod
      (hf.comp (fst _ _))
  have hbody : ComputableInPolyTime
      (fun q : RefineArgs × ℕ ↦
        ((List.range (min q.1.2.2.2.2.1.length q.2)).flatMap fun j ↦
          ((B.block mode ((q.1.1, q.1.2.1, q.1.2.2.1, q.1.2.2.2.1,
            q.1.2.2.2.2.2.length, q.1.2.2.2.2.1.getD j []), q.2)).take q.2).map
              (replaceL q.1.1 q.1.2.2.2.1 q.1.2.2.2.2 j)).take q.2)
      E (encList encCandidate) := by
    apply ComputableInPolyTime.of_tidy
    apply ComputableTidilyInPolyTime.listTakeWithInput ?_ hf.tidy
    apply ComputableInPolyTime.tidy
    apply flatMapWithInput (range.comp hcount)
    apply mapWithInput (.of_tidy
      (ComputableTidilyInPolyTime.listTakeWithInput hb'.tidy (hf.comp (fst _ _)).tidy))
    have hbase := (fst E encUnary).comp (fst _ encEdge)
    exact replace_polytime (hd.comp hbase) (hp.comp hbase) (hC.comp hbase)
      ((snd _ _).comp (fst _ _)) (snd _ _)
  exact ite_decide hg hbody (const [])

end ABBKS26.Assembly.Exec.RefineSynth
