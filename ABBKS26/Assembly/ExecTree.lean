module

public import ABBKS26.Assembly.ExecSchedule
public import ABBKS26.Assembly.ExecTests
public import ABBKS26.Assembly.ExecLearn

/-! # Capped traversal and final stored-parent path checks -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Select
open Turing.MultiTapeTM ComputableInPolyTime

/-- A tree iteration stores at most fuel bits, including all persistent path records. -/
def treeStep (B : RefineCode) (mode : Mode) (q : Input × ℕ) (ps : Points)
    (Cs : List CandidateL) : List CandidateL :=
  cap (encList encCandidate) q.2 []
    ((Cs.flatMap fun C ↦
      if C.1.length < q.1.k then
        refineL B mode ((dim q.1.points, q.1.k, ps, q.1.points, C), q.2)
      else []).take q.2)

/-- No intermediate acceptance check: traverse the unfiltered lists to depth k-1. -/
def treeL (B : RefineCode) (mode : Mode) (q : Input × ℕ) (ps : Points) : List CandidateL :=
  (((treeStep B mode q ps)^[min (q.1.k - 1) q.2])
    [([List.range q.1.points.length], [])]).filter fun C ↦ C.1.length = q.1.k

/-- The weak partition check evaluates the recorded statistic on its recorded parent. -/
def verifyL (n d : ℕ) (p : List ℚ) (pts : Points) (e : EdgeL) : Bool :=
  let values := e.2.1.map fun l ↦ evalL d e.2.2.1 (pts.getD l [])
  let lo := e.2.2.2.2.2.1
  let hi := e.2.2.2.2.2.2
  let window := (values.filter fun v ↦ lo ≤ v ∧ v ≤ hi).length
  let L := (leftL d pts e).length
  decide ((window : ℚ) ≤ p.getD 3 0 * e.2.1.length ∧
    p.getD 0 0 * n / 4 ≤ L ∧ p.getD 0 0 * n / 4 ≤ e.2.1.length - L)

/-- Learning is already finished when this first-accepted search begins. -/
def selectL (n d : ℕ) (ps pts : Points) (Cs : List LearnedL) : Option LearnedL :=
  Cs.find? fun C ↦ C.1.2.all fun e ↦ verifyL n d (ps.getD e.1 []) pts e

/-- The cap never truncates a generated level at a sufficient global budget. -/
theorem tree_agrees (B : RefineCode) (hB : RefineSpecL B)
    (S : ScheduleCode) (hS : ScheduleSpec S) (mode : Mode) (x : Input) (fuel : ℕ)
    (hx : Valid x) (hf : need mode x ≤ fuel) :
    treeL B mode (x, fuel) (S.run mode (x, fuel)) =
      (leaves B.ref mode x.k (Schedule.params mode x.wmin x.k)
        (inputPoints x) fuel).map candidateList := by
  let ps := (List.range x.k).map
    (fun h ↦ paramsList (Schedule.params mode x.wmin x.k h))
  let pts := inputPoints x
  let params := Schedule.params mode x.wmin x.k
  have hlevels : ∀ h, h ≤ x.k - 1 →
      ((treeStep B mode (x, fuel) ps)^[h]) [([List.range x.points.length], [])] =
        (levels B.ref mode x.k params pts fuel h).map candidateList := by
    intro h
    induction h with
    | zero =>
      intro _
      simp [levels, root, candidateList, indexList, Fin.sort_univ,
        List.map_coe_finRange_eq_range]
    | succ h ih =>
      intro hh
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hm : ((levels B.ref mode x.k params pts fuel h).map candidateList).flatMap
          (fun C ↦ if C.1.length < x.k then
            refineL B mode ((dim x.points, x.k, ps, x.points, C), fuel) else []) =
          (levels B.ref mode x.k params pts fuel (h + 1)).map candidateList := by
        rw [levels, List.map_flatMap, List.flatMap_map]
        apply List.flatMap_congr
        intro C _
        simp only [candidateList, List.length_map]
        split_ifs
        · exact hB.agrees mode x fuel hx hf C
        · rfl
      have hs := hB.levels_size mode x fuel hx hf (h + 1) hh
      have hc := Rounding.RawAux.length_count encCandidate
        ((levels B.ref mode x.k params pts fuel (h + 1)).map candidateList)
      dsimp only [treeStep]
      rw [hm, List.take_of_length_le (hc.trans hs)]
      exact cap_eq _ fuel [] _ hs
  unfold treeL
  rw [hS.agrees mode x fuel hx hf, min_eq_left (hS.count_le mode x fuel hx hf)]
  rw [hlevels _ le_rfl]
  simp only [leaves, List.filter_map, Function.comp_def, candidateList, List.length_map]
  rfl

private theorem treeStep_polytime (B : RefineCode) (hB : RefineSpecL B)
    (S : ScheduleCode) (hS : ScheduleSpec S) (mode : Mode) :
    ComputableInPolyTime (fun p : (Input × ℕ) × List CandidateL ↦
      treeStep B mode p.1 (S.run mode p.1) p.2)
      (encPair encPadded (encList encCandidate)) (encList encCandidate) := by
  let E := encPair encPadded (encList encCandidate)
  have hq : ComputableInPolyTime (fun p : (Input × ℕ) × List CandidateL ↦ p.1)
      E encPadded := fst _ _
  have hx := hq.fst'
  have hf := hq.snd'
  have hd := dim_polytime.comp hx
  have hk := k_polytime.comp hx
  have hp := points_polytime.comp hx
  have hps := (hS.polytime mode).comp hq
  have hrun : ComputableInPolyTime
      (fun p : ((Input × ℕ) × List CandidateL) × CandidateL ↦
        refineL B mode ((dim p.1.1.1.points, p.1.1.1.k, S.run mode p.1.1,
          p.1.1.1.points, p.2), p.1.1.2))
      (encPair E encCandidate) (encList encCandidate) :=
    (hB.polytime mode).comp
      (((hd.comp (fst _ _)).prod ((hk.comp (fst _ _)).prod
        ((hps.comp (fst _ _)).prod ((hp.comp (fst _ _)).prod (snd _ _))))).prod
          (hf.comp (fst _ _)))
  have hg : ComputableInPolyTime
      (fun p : ((Input × ℕ) × List CandidateL) × CandidateL ↦
        decide (p.2.1.length < p.1.1.1.k)) (encPair E encCandidate) encBool :=
    binary_lt' (unary_to_binary.comp ((length_list encIndices).comp (snd _ _).fst'))
      (hk.comp (fst _ _))
  have hm : ComputableInPolyTime
      (fun p : (Input × ℕ) × List CandidateL ↦ p.2.flatMap fun C ↦
        if C.1.length < p.1.1.k then
          refineL B mode ((dim p.1.1.points, p.1.1.k, S.run mode p.1,
            p.1.1.points, C), p.1.2) else []) E (encList encCandidate) :=
    flatMapWithInput (snd _ _) (ite_decide hg hrun (const []))
  have ht := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listTakeWithInput hm.tidy hf.tidy)
  unfold treeStep cap
  apply ite_decide ?_ ht (const [])
  exact .of_tidy (ComputableTidilyInPolyTime.unary_le'
    ((ComputableTidilyInPolyTime.encoding_length (encList encCandidate)).comp ht.tidy)
    hf.tidy)

theorem tree_polytime (B : RefineCode) (hB : RefineSpecL B)
    (S : ScheduleCode) (hS : ScheduleSpec S) (mode : Mode) :
    ComputableInPolyTime (fun q ↦ treeL B mode q (S.run mode q))
      encPadded (encList encCandidate) := by
  have hx : ComputableInPolyTime (fun q : Input × ℕ ↦ q.1) encPadded encInput := fst _ _
  have hf : ComputableInPolyTime (fun q : Input × ℕ ↦ q.2) encPadded encUnary := snd _ _
  have hk := k_polytime.comp hx
  have hc : ComputableInPolyTime (fun q : Input × ℕ ↦ min (q.1.k - 1) q.2)
      encPadded encUnary :=
    (binary_min_unary' hf (binary_sub' hk (const 1))).of_enc_eq fun q ↦ by
      rw [Nat.min_comm]
      rfl
  have hindices : ComputableInPolyTime (fun q : Input × ℕ ↦ List.range q.1.points.length)
      encPadded encIndices := by
    have hr := mapWithInput (f := fun (_ : Input × ℕ) (i : ℕ) ↦ i)
      (range.comp ((length_list encVector).comp (points_polytime.comp hx)))
      (unary_to_binary.comp (snd _ _))
    exact hr.of_enc_eq fun q ↦ by
      change encIndices (List.range q.1.points.length) =
        encIndices ((List.range q.1.points.length).map fun i ↦ i)
      rw [List.map_id']
  have hroot : ComputableInPolyTime
      (fun q : Input × ℕ ↦ [([List.range q.1.points.length], [])])
      encPadded (encList encCandidate) :=
    cons' ((cons' hindices (const [])).prod (const [])) (const [])
  have hit := ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    (step := fun q Cs ↦ treeStep B mode q (S.run mode q) Cs)
    ComputableTidilyInPolyTime.id' hc.tidy hroot.tidy
    (treeStep_polytime B hB S hS mode).tidy hf.tidy.polyBounded
    (fun q Cs ↦ by
      have hs : (encList encCandidate
          (treeStep B mode q (S.run mode q) Cs)).length ≤ q.2 := by
        unfold treeStep cap
        split
        · assumption
        · exact Nat.zero_le _
      exact hs.trans (Nat.le_add_left _ _))
  unfold treeL
  apply filterWithInput (ComputableInPolyTime.of_tidy hit)
  exact .of_tidy (ComputableTidilyInPolyTime.decide_eq'
    (unary_to_binary.comp ((length_list encIndices).comp (snd _ _).fst')).tidy
    (hk.comp (fst _ _)).tidy)

private theorem verify_agrees {n d : ℕ} (p : StepParams)
    (x : Fin n → Fin d → ℚ) (e : Edge n d) :
    verifyL n d (paramsList p) (pointsOf x) (edgeList e) = decide (Verify p x e) := by
  have hx : (fun l : Fin n ↦ vectorOf d ((pointsOf x).getD l.val [])) = x := by
    funext l i
    exact pointsOf_get x l i
  have hw := RefineSynth.RB3.window_agrees (pointsOf x) e
  have hl := RefineSynth.left_agrees (pointsOf x) e
  rw [hx] at hw hl
  have hc : (e.left x).card ≤ e.parent.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hr : (e.right x).card = e.parent.card - (e.left x).card :=
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  unfold verifyL
  simp only [edgeList, List.filter_map, List.length_map]
  change decide ((RefineSynth.RB3.windowL d (pointsOf x) (edgeList e)).length ≤
      p.verifyMass * (indexList e.parent).length ∧
    p.w * n / 4 ≤ (leftL d (pointsOf x) (edgeList e)).length ∧
    p.w * n / 4 ≤ (indexList e.parent).length -
      (leftL d (pointsOf x) (edgeList e)).length) = _
  rw [hw, hl]
  simp only [indexList, List.length_map, Finset.length_sort, Verify, hr, Nat.cast_sub hc]

theorem select_agrees {n d : ℕ} (params : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (Cs : List (Learned n d)) (ps : Points)
    (hps : ∀ L ∈ Cs, ∀ e ∈ L.candidate.path,
      ps.getD e.depth [] = paramsList (params e.depth)) :
    selectL n d ps (pointsOf x) (Cs.map learnedList) =
      (select params x Cs).map learnedList := by
  have htest (L : Learned n d) (hL : L ∈ Cs) :
      (learnedList L).1.2.all (fun e ↦ verifyL n d (ps.getD e.1 []) (pointsOf x) e) =
        L.candidate.path.all (fun e ↦ decide (Verify (params e.depth) x e)) := by
    simp only [learnedList, candidateList, List.all_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true]
    apply forall₂_congr
    intro e he
    change verifyL n d (ps.getD (edgeList e).1 []) (pointsOf x) (edgeList e) = true ↔ _
    rw [show ps.getD (edgeList e).1 [] = paramsList (params e.depth) from hps L hL e he,
      verify_agrees]
  unfold selectL select
  induction Cs with
  | nil => rfl
  | cons L Cs ih =>
    rw [List.map_cons, List.find?_cons, List.find?_cons, htest L List.mem_cons_self]
    split
    · rfl
    · exact ih (fun C hC ↦ hps C (List.mem_cons_of_mem _ hC))
        (fun C hC ↦ htest C (List.mem_cons_of_mem _ hC))

/-- Mapping the learner over all stored candidates has polynomial total cost. -/
theorem learn_all_polytime (L : LearnCode) (hL : LearnSpecL L) (mode : Mode) :
    ComputableInPolyTime
      (fun q : ((ℕ × Points) × ℕ) × List CandidateL ↦
        learnAllL L mode q.1.1.1 q.1.1.2 q.1.2 q.2)
      (encPair (encPair (encPair encUnary encPoints) encUnary) (encList encCandidate))
      (encList encLearned) := by
  let Q := ((ℕ × Points) × ℕ) × List CandidateL
  let E := encPair (encPair (encPair encUnary encPoints) encUnary) (encList encCandidate)
  let D := encPair E encCandidate
  let R := encPair D encIndices
  have hq : ComputableInPolyTime (fun p : (Q × CandidateL) × List ℕ ↦ p.1.1) R E :=
    (fst _ _).comp (fst _ _)
  have hm := (fst _ _).comp hq
  have hdp := (fst _ _).comp hm
  have hd := (fst _ _).comp hdp
  have hp := (snd _ _).comp hdp
  have hf := (snd _ _).comp hm
  have hn : ComputableInPolyTime (fun p : (Q × CandidateL) × List ℕ ↦ p.2)
      R encIndices := snd _ _
  have hrun := (hL.polytime mode).comp ((hd.prod (hp.prod hn)).prod hf)
  have hC : ComputableInPolyTime (fun p : Q × CandidateL ↦ p.2) D encCandidate := snd _ _
  have hblocks := (fst _ _).comp hC
  have hmap := mapWithInput
    (f := fun (p : Q × CandidateL) (N : List ℕ) ↦
      L.run mode ((p.1.1.1.1, p.1.1.1.2, N), p.1.1.2)) hblocks hrun
  have hstep := hC.prod hmap
  have hcs : ComputableInPolyTime (fun q : Q ↦ q.2) E (encList encCandidate) := snd _ _
  exact (mapWithInput
    (f := fun (q : Q) (C : CandidateL) ↦
      (C, C.1.map fun N ↦ L.run mode ((q.1.1.1, q.1.1.2, N), q.1.2)))
    hcs hstep).of_enc_eq fun q ↦ rfl

private theorem verify_polytime {α : Type} {enc : α ↪ List Bool} {n d : α → ℕ}
    {p : α → Vector} {pts : α → Points} {e : α → EdgeL}
    (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encVector)
    (hpts : ComputableInPolyTime pts enc encPoints)
    (he : ComputableInPolyTime e enc encEdge) :
    ComputableInPolyTime (fun a ↦ verifyL (n a) (d a) (p a) (pts a) (e a))
      enc encBool := by
  have hv : ComputableInPolyTime (fun q : α × ℕ ↦ (pts q.1).getD q.2 [])
      (encPair enc encNat) encVector := .of_tidy
    (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector) []
      (hpts.comp (fst _ _)).tidy (snd _ _).tidy)
  have hvalue := RefineSynth.eval_polytime (hd.comp (fst _ _))
    (he.snd'.snd'.fst'.comp (fst _ _)) hv
  have hvalues : ComputableInPolyTime
      (fun a ↦ (e a).2.1.map fun l ↦ evalL (d a) (e a).2.2.1 ((pts a).getD l []))
      enc encVector := mapWithInput he.snd'.fst' hvalue
  have hwindow : ComputableInPolyTime
      (fun a ↦ ((e a).2.1.map fun l ↦ evalL (d a) (e a).2.2.1
        ((pts a).getD l [])).filter fun v ↦ (e a).2.2.2.2.2.1 ≤ v ∧
          v ≤ (e a).2.2.2.2.2.2) enc encVector :=
    filterWithInput hvalues (bool_and'
      (rat_le' (by fun_prop) (snd _ _)) (rat_le' (snd _ _) (by fun_prop)))
  have hleft := RefineSynth.left_polytime hd hpts he
  unfold verifyL
  apply bool_and'
  · apply rat_le' <;> fun_prop
  · apply bool_and'
    · apply rat_le' <;> fun_prop
    · apply rat_le' <;> fun_prop

theorem select_polytime : ComputableInPolyTime
    (fun q : (ℕ × ℕ × Points × Points) × List LearnedL ↦
      selectL q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
    (encPair (encPair encUnary (encPair encUnary (encPair encPoints encPoints)))
      (encList encLearned)) (encOption encLearned) := by
  let Q := (ℕ × ℕ × Points × Points) × List LearnedL
  let E := encPair (encPair encUnary (encPair encUnary (encPair encPoints encPoints)))
    (encList encLearned)
  let R := encPair (encPair E encLearned) encEdge
  have hq : ComputableInPolyTime (fun p : (Q × LearnedL) × EdgeL ↦ p.1.1) R E :=
    (fst _ _).comp (fst _ _)
  have hn := hq.fst'.fst'
  have hd := hq.fst'.snd'.fst'
  have hps := hq.fst'.snd'.snd'.fst'
  have hpts := hq.fst'.snd'.snd'.snd'
  have he : ComputableInPolyTime (fun p : (Q × LearnedL) × EdgeL ↦ p.2)
      R encEdge := snd _ _
  have hp : ComputableInPolyTime
      (fun p : (Q × LearnedL) × EdgeL ↦ p.1.1.1.2.2.1.getD p.2.1 [])
      R encVector := ComputableInPolyTime.of_tidy
    (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector) []
      hps.tidy he.fst'.tidy)
  unfold selectL
  apply findWithInput (show ComputableInPolyTime (fun q : Q ↦ q.2)
    E (encList encLearned) from snd _ _)
  apply allWithInput (show ComputableInPolyTime (fun p : Q × LearnedL ↦ p.2.1.2)
    (encPair E encLearned) (encList encEdge) from (snd _ _).fst'.snd')
  exact verify_polytime hn hd hp hpts he

end ABBKS26.Assembly.Exec
