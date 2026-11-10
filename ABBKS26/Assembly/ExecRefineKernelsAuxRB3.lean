module

public import ABBKS26.Assembly.ExecRefineAuxAgreement
public import ABBKS26.Assembly.ExecRefineAuxPoly

/-! Rational-list verification and the internal RB3 packing loop. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.RB3

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

def rightL (d : ℕ) (pts : Points) (e : EdgeL) : List ℕ :=
  e.2.1.filter fun l ↦ l ∉ leftL d pts e

def windowL (d : ℕ) (pts : Points) (e : EdgeL) : List ℕ :=
  e.2.1.filter fun l ↦
    e.2.2.2.2.2.1 ≤ evalL d e.2.2.1 (pts.getD l []) ∧
      evalL d e.2.2.1 (pts.getD l []) ≤ e.2.2.2.2.2.2

def verifyL (d n : ℕ) (w mass : ℚ) (pts : Points) (e : EdgeL) : Bool :=
  decide ((windowL d pts e).length ≤ mass * e.2.1.length ∧
    w * n / 4 ≤ (leftL d pts e).length ∧ w * n / 4 ≤ (rightL d pts e).length)

private theorem index_filter {n : ℕ} (s : Finset (Fin n))
    (p : ℕ → Prop) [DecidablePred p] :
    (indexList s).filter p = indexList (s.filter fun i ↦ p i.val) := by
  have hsort {α : Type} [LinearOrder α] (t : Finset α)
      (q : α → Prop) [DecidablePred q] :
      (t.sort (· ≤ ·)).filter q = (t.filter q).sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise'
      ((t.pairwise_sort (· ≤ ·)).filter _) ((t.filter q).pairwise_sort (· ≤ ·))
    apply (List.perm_ext_iff_of_nodup ((t.sort_nodup _).filter _)
      ((t.filter q).sort_nodup _)).mpr
    intro a
    simp
  simp only [indexList, List.filter_map]
  rw [← hsort]
  rfl

theorem right_agrees {n d : ℕ} (pts : Points) (e : Edge n d) :
    rightL d pts (edgeList e) =
      indexList (e.right fun l ↦ vectorOf d (pts.getD l.val [])) := by
  simp only [rightL, left_agrees]
  change (indexList e.parent).filter _ = _
  rw [index_filter]
  congr 1
  ext i
  simp [Edge.right, indexList, Fin.val_injective.eq_iff]

theorem window_agrees {n d : ℕ} (pts : Points) (e : Edge n d) :
    (windowL d pts (edgeList e)).length =
      e.windowCount (fun l ↦ vectorOf d (pts.getD l.val [])) := by
  simp only [windowL, edgeList, eval_agrees]
  rw [index_filter]
  simp only [indexList, List.length_map, Finset.length_sort, Edge.windowCount]

theorem verify_agrees {n d : ℕ} (p : StepParams) (pts : Points) (e : Edge n d) :
    verifyL d n p.w p.verifyMass pts (edgeList e) =
      decide (Verify p (fun l ↦ vectorOf d (pts.getD l.val [])) e) := by
  unfold verifyL
  rw [window_agrees, left_agrees, right_agrees]
  simp only [edgeList, indexList, List.length_map, Finset.length_sort, Verify]

@[fun_prop] theorem right_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {e : α → EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime pts input encPoints)
    (he : ComputableInPolyTime e input encEdge) :
    ComputableInPolyTime (fun x ↦ rightL (d x) (pts x) (e x)) input encIndices := by
  unfold rightL
  apply filterWithInput (by fun_prop)
  exact bool_not.comp (decide_mem
    ((left_polytime hd hp he).comp (fst _ _)) (snd _ _))

@[fun_prop] theorem window_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {e : α → EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime pts input encPoints)
    (he : ComputableInPolyTime e input encEdge) :
    ComputableInPolyTime (fun x ↦ windowL (d x) (pts x) (e x)) input encIndices := by
  have hv : ComputableInPolyTime (fun q : α × ℕ ↦ (pts q.1).getD q.2 [])
      (encPair input encNat) encVector :=
    .of_tidy (ComputableTidilyInPolyTime.listGetD_binary (encL := encList encVector) []
      (hp.comp (fst _ _)).tidy (snd _ _).tidy)
  have hstat : ComputableInPolyTime (fun q : α × ℕ ↦ (e q.1).2.2.1)
      (encPair input encNat) encStatistic := by fun_prop
  have hvalue := eval_polytime (hd.comp (fst _ _)) hstat hv
  unfold windowL
  apply filterWithInput (by fun_prop)
  apply bool_and'
  · exact rat_le' (by fun_prop) hvalue
  · exact rat_le' hvalue (by fun_prop)

@[fun_prop] theorem verify_polytime {α : Type} {input : α ↪ List Bool}
    {d n : α → ℕ} {w mass : α → ℚ} {pts : α → Points} {e : α → EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hn : ComputableInPolyTime n input encNat)
    (hw : ComputableInPolyTime w input encRat)
    (hm : ComputableInPolyTime mass input encRat)
    (hp : ComputableInPolyTime pts input encPoints)
    (he : ComputableInPolyTime e input encEdge) :
    ComputableInPolyTime (fun x ↦ verifyL (d x) (n x) (w x) (mass x) (pts x) (e x))
      input encBool := by
  have hwindow := window_polytime hd hp he
  have hleft := left_polytime hd hp he
  have hright := right_polytime hd hp he
  unfold verifyL
  apply bool_and'
  · apply rat_le' <;> fun_prop
  · apply bool_and'
    · apply rat_le' <;> fun_prop
    · apply rat_le' <;> fun_prop

def differenceL (A B : List ℕ) : List ℕ := A.filter fun i ↦ i ∉ B

def symmetricCountL (A B : List ℕ) : ℕ :=
  (differenceL A B).length + (differenceL B A).length

def distanceL (N A B : List ℕ) : ℕ :=
  min (symmetricCountL A B) (symmetricCountL A (differenceL N B))

private theorem difference_agrees {n : ℕ} (A B : Finset (Fin n)) :
    differenceL (indexList A) (indexList B) = indexList (A \ B) := by
  unfold differenceL
  rw [index_filter]
  congr 1
  ext i
  simp [indexList, Fin.val_injective.eq_iff]

private theorem symmetricCount_agrees {n : ℕ} (A B : Finset (Fin n)) :
    symmetricCountL (indexList A) (indexList B) = ((A \ B) ∪ (B \ A)).card := by
  unfold symmetricCountL
  rw [difference_agrees, difference_agrees]
  simp only [indexList, List.length_map, Finset.length_sort]
  rw [Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr fun (i : Fin n) hi hj ↦
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1

theorem distance_agrees {n : ℕ} (N A B : Finset (Fin n)) :
    distanceL (indexList N) (indexList A) (indexList B) = splitDistance N A B := by
  simp only [distanceL, difference_agrees, symmetricCount_agrees, splitDistance]

@[fun_prop] theorem difference_polytime {α : Type} {input : α ↪ List Bool}
    {A B : α → List ℕ}
    (hA : ComputableInPolyTime A input encIndices)
    (hB : ComputableInPolyTime B input encIndices) :
    ComputableInPolyTime (fun x ↦ differenceL (A x) (B x)) input encIndices := by
  unfold differenceL
  exact filterWithInput hA
    (bool_not.comp (decide_mem (hB.comp (fst _ _)) (snd _ _)))

@[fun_prop] theorem symmetricCount_polytime {α : Type} {input : α ↪ List Bool}
    {A B : α → List ℕ}
    (hA : ComputableInPolyTime A input encIndices)
    (hB : ComputableInPolyTime B input encIndices) :
    ComputableInPolyTime (fun x ↦ symmetricCountL (A x) (B x)) input encUnary := by
  unfold symmetricCountL
  exact unary_add' ((length_list _).comp (difference_polytime hA hB))
    ((length_list _).comp (difference_polytime hB hA))

@[fun_prop] theorem distance_polytime {α : Type} {input : α ↪ List Bool}
    {N A B : α → List ℕ}
    (hN : ComputableInPolyTime N input encIndices)
    (hA : ComputableInPolyTime A input encIndices)
    (hB : ComputableInPolyTime B input encIndices) :
    ComputableInPolyTime (fun x ↦ distanceL (N x) (A x) (B x)) input encUnary := by
  unfold distanceL
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_min).comp
    ((symmetricCount_polytime hA hB).prod
      (symmetricCount_polytime hA (difference_polytime hN hB)))

def packStep (d n : ℕ) (w mass : ℚ) (pts : Points) (cap : ℕ)
    (out : List EdgeL) (e : EdgeL) : List EdgeL :=
  if verifyL d n w mass pts e then
    if out.any (fun e' ↦
      (distanceL e.2.1 (leftL d pts e) (leftL d pts e') : ℚ) < w * n / 8) then out
    else if out.length < cap then out ++ [e] else out
  else out

/-- The cap is compared in binary; no loop enumerates the cap. -/
def packL (d n : ℕ) (w mass : ℚ) (pts : Points) (cap : ℕ)
    (raw : List EdgeL) : List EdgeL :=
  raw.foldl (packStep d n w mass pts cap) []

private theorem step_agrees {n d : ℕ} (p : StepParams) (pts : Points) (k : ℕ)
    (out : List (Edge n d)) (e : Edge n d) :
    packStep d n p.w p.verifyMass pts (frobCap k) (out.map edgeList) (edgeList e) =
      (if Verify p (fun l ↦ vectorOf d (pts.getD l.val [])) e then
        if out.any (fun e' ↦ (splitDistance e.parent
          (e.left fun l ↦ vectorOf d (pts.getD l.val []))
          (e'.left fun l ↦ vectorOf d (pts.getD l.val [])) : ℚ) < p.w * n / 8) then out
        else if out.length < frobCap k then out ++ [e] else out
      else out).map edgeList := by
  have ha : (out.map edgeList).any (fun e' ↦
      (distanceL (edgeList e).2.1 (leftL d pts (edgeList e)) (leftL d pts e') : ℚ) <
        p.w * n / 8) =
      out.any (fun e' ↦ (splitDistance e.parent
        (e.left fun l ↦ vectorOf d (pts.getD l.val []))
        (e'.left fun l ↦ vectorOf d (pts.getD l.val [])) : ℚ) < p.w * n / 8) := by
    rw [List.any_map]
    congr 1
    funext e'
    dsimp only [Function.comp_apply]
    rw [left_agrees, left_agrees]
    change decide ((distanceL (indexList e.parent) _ _ : ℚ) < _) = _
    rw [distance_agrees]
  unfold packStep
  rw [verify_agrees, ha]
  simp only [decide_eq_true_eq, List.length_map]
  split_ifs <;> simp only [List.map_append, List.map_cons, List.map_nil]

/-- The list machine performs precisely the typed RB3 verification and merging loop. -/
theorem pack_agrees {n d : ℕ} (p : StepParams) (pts : Points) (k : ℕ)
    (raw : List (Edge n d)) :
    packL d n p.w p.verifyMass pts (frobCap k) (raw.map edgeList) =
      (frobSplits p k (fun l ↦ vectorOf d (pts.getD l.val [])) raw).map edgeList := by
  have hfold (es out : List (Edge n d)) :
      (es.map edgeList).foldl (packStep d n p.w p.verifyMass pts (frobCap k))
        (out.map edgeList) =
      (es.foldl (fun out e ↦
        if Verify p (fun l ↦ vectorOf d (pts.getD l.val [])) e then
          if out.any (fun e' ↦ (splitDistance e.parent
            (e.left fun l ↦ vectorOf d (pts.getD l.val []))
            (e'.left fun l ↦ vectorOf d (pts.getD l.val [])) : ℚ) < p.w * n / 8) then out
          else if out.length < frobCap k then out ++ [e] else out
        else out) out).map edgeList := by
    induction es generalizing out with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons, List.foldl_cons, step_agrees]
      exact ih _
  exact hfold raw []


@[fun_prop] theorem packStep_polytime {α : Type} {input : α ↪ List Bool}
    {d n cap : α → ℕ} {w mass : α → ℚ} {pts : α → Points}
    {out : α → List EdgeL} {e : α → EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hn : ComputableInPolyTime n input encNat)
    (hc : ComputableInPolyTime cap input encNat)
    (hw : ComputableInPolyTime w input encRat)
    (hm : ComputableInPolyTime mass input encRat)
    (hp : ComputableInPolyTime pts input encPoints)
    (ho : ComputableInPolyTime out input (encList encEdge))
    (he : ComputableInPolyTime e input encEdge) :
    ComputableInPolyTime (fun x ↦
      packStep (d x) (n x) (w x) (mass x) (pts x) (cap x) (out x) (e x))
      input (encList encEdge) := by
  have hl := left_polytime hd hp he
  have hmrg : ComputableInPolyTime (fun x ↦ (out x).any fun e' ↦
      (distanceL (e x).2.1 (leftL (d x) (pts x) (e x)) (leftL (d x) (pts x) e') : ℚ) <
        w x * n x / 8) input encBool := by
    apply anyWithInput ho
    have hl' := left_polytime (hd.comp (fst _ _)) (hp.comp (fst _ _)) (snd _ _)
    have hdis := distance_polytime
      (((fst _ _).comp ((snd _ _).comp he)).comp (fst _ _)) (hl.comp (fst _ _)) hl'
    apply rat_lt' (rat_natCast' (unary_to_binary.comp hdis))
    fun_prop
  have hlen := binary_lt' (unary_to_binary.comp ((length_list encEdge).comp ho)) hc
  have hverify := verify_polytime hd hn hw hm hp he
  unfold packStep
  exact ite_decide hverify (ite_decide hmrg ho (ite_decide hlen
    (listAppend' ho (by fun_prop)) ho)) ho

/-- The streaming merge costs polynomial time even when the supplied cap is enormous. -/
theorem pack_polytime {α : Type} {input : α ↪ List Bool}
    {d n cap : α → ℕ} {w mass : α → ℚ} {pts : α → Points}
    {raw : α → List EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hn : ComputableInPolyTime n input encNat)
    (hc : ComputableInPolyTime cap input encNat)
    (hw : ComputableInPolyTime w input encRat)
    (hm : ComputableInPolyTime mass input encRat)
    (hp : ComputableInPolyTime pts input encPoints)
    (hr : ComputableInPolyTime raw input (encList encEdge)) :
    ComputableInPolyTime (fun x ↦ packL (d x) (n x) (w x) (mass x) (pts x) (cap x)
      (raw x)) input (encList encEdge) := by
  unfold packL
  refine foldlWith_of_bounded_growth (encA := encEdge) (encL := encList encEdge)
    (par := fun x ↦ x)
    (list := raw) (init := fun _ ↦ [])
    (step := fun x out e ↦ packStep (d x) (n x) (w x) (mass x) (pts x) (cap x) out e)
    id' hr (const []) ?_
    (growth := fun x ↦ 2 * (encList encEdge (raw x)).length + 1)
    (((PolyBounded.const 2).mul hr.polyBounded_length).add (.const 1)) ?_
  · have hbase := (fst input (encList encEdge)).comp (fst _ encEdge)
    exact packStep_polytime (hd.comp hbase) (hn.comp hbase) (hc.comp hbase)
      (hw.comp hbase) (hm.comp hbase) (hp.comp hbase)
      ((snd _ _).comp (fst _ _)) (snd _ _)
  · intro x out e he
    have hs := SizedListEncoding.length_elem_le (encA := encEdge)
      (encL := encList encEdge) (raw x) e he
    unfold packStep
    split_ifs
    · omega
    · simp only [encList_append, List.length_append, encList_cons, encList_nil,
        List.length_nil, length_frame]
      omega
    · omega
    · omega

private theorem step_length (d n : ℕ) (w mass : ℚ) (pts : Points) (cap : ℕ)
    (out : List EdgeL) (e : EdgeL) :
    (packStep d n w mass pts cap out e).length ≤ out.length + 1 := by
  unfold packStep
  split_ifs <;> simp

private theorem pack_caps_eq (d n : ℕ) (w mass : ℚ) (pts : Points)
    (a b : ℕ) (raw : List EdgeL) (ha : raw.length ≤ a) (hb : raw.length ≤ b) :
    packL d n w mass pts a raw = packL d n w mass pts b raw := by
  have hfold (es out : List EdgeL) (hs : out.length + es.length ≤ raw.length) :
      es.foldl (packStep d n w mass pts a) out =
        es.foldl (packStep d n w mass pts b) out := by
    induction es generalizing out with
    | nil => rfl
    | cons e es ih =>
      have hla : out.length < a := by simp only [List.length_cons] at hs; omega
      have hlb : out.length < b := by simp only [List.length_cons] at hs; omega
      have hstep : packStep d n w mass pts a out e =
          packStep d n w mass pts b out e := by
        simp only [packStep, hla, hlb, ite_true]
      simp only [List.foldl_cons, hstep]
      apply ih
      have hg := step_length d n w mass pts b out e
      simp only [List.length_cons] at hs
      omega
  exact hfold raw [] (by simp)

/-- Saturating the exponent avoids constructing an exponentially long cap from binary `k`.
The saturated cap still admits every raw record when saturation occurs. -/
def run (d n : ℕ) (w mass : ℚ) (pts : Points) (k : ℕ)
    (raw : List EdgeL) : List EdgeL :=
  packL d n w mass pts (2 ^ min raw.length (k - 1)) raw

private theorem run_eq_pack (d n : ℕ) (w mass : ℚ) (pts : Points) (k : ℕ)
    (raw : List EdgeL) :
    run d n w mass pts k raw = packL d n w mass pts (frobCap k) raw := by
  unfold run
  by_cases hk : k - 1 ≤ raw.length
  · rw [min_eq_right hk]
    rfl
  · rw [min_eq_left (by omega)]
    have hl : raw.length ≤ 2 ^ raw.length := Nat.le_of_lt (Nat.lt_two_pow_self (n := _))
    exact pack_caps_eq d n w mass pts _ _ raw hl
      (hl.trans (Nat.pow_le_pow_right (by omega) (by omega)))

theorem run_agrees {n d : ℕ} (p : StepParams) (pts : Points) (k : ℕ)
    (raw : List (Edge n d)) :
    run d n p.w p.verifyMass pts k (raw.map edgeList) =
      (frobSplits p k (fun l ↦ vectorOf d (pts.getD l.val [])) raw).map edgeList := by
  rw [run_eq_pack, pack_agrees]


@[fun_prop] theorem run_polytime {α : Type} {input : α ↪ List Bool}
    {d n k : α → ℕ} {w mass : α → ℚ} {pts : α → Points}
    {raw : α → List EdgeL}
    (hd : ComputableInPolyTime d input encUnary)
    (hn : ComputableInPolyTime n input encNat)
    (hk : ComputableInPolyTime k input encNat)
    (hw : ComputableInPolyTime w input encRat)
    (hm : ComputableInPolyTime mass input encRat)
    (hp : ComputableInPolyTime pts input encPoints)
    (hr : ComputableInPolyTime raw input (encList encEdge)) :
    ComputableInPolyTime (fun x ↦ run (d x) (n x) (w x) (mass x) (pts x) (k x)
      (raw x)) input (encList encEdge) := by
  unfold run
  apply pack_polytime hd hn _ hw hm hp hr
  exact binary_two_pow.comp
    (binary_min_unary' ((length_list encEdge).comp hr) (binary_sub' hk (const 1)))

end ABBKS26.Assembly.Exec.RefineSynth.RB3
