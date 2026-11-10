module

public import ABBKS26.Assembly.ExecTree
public import ABBKS26.Assembly.ExecOutput

/-!
# Assembly of the executable stages

The two public existence theorems use this composition layer. Each stage is proved at its own
interface; this file does not posit a joint implementation witness.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Select
open Turing.MultiTapeTM ComputableInPolyTime

/-- The selected learned candidate, still in list representation. -/
def frontL (S : ScheduleCode) (B : RefineCode) (L : LearnCode) (mode : Mode)
    (q : Input × ℕ) : Option LearnedL :=
  let ps := S.run mode q
  selectL q.1.points.length (dim q.1.points) ps q.1.points
    (learnAllL L mode (dim q.1.points) q.1.points q.2 (treeL B mode q ps))

theorem learned_polytime (S : ScheduleCode) (hS : ScheduleSpec S)
    (B : RefineCode) (hB : RefineSpecL B) (L : LearnCode) (hL : LearnSpecL L)
    (mode : Mode) : ComputableInPolyTime
      (fun q : Input × ℕ ↦ learnAllL L mode (dim q.1.points) q.1.points q.2
        (treeL B mode q (S.run mode q))) encPadded (encList encLearned) := by
  have hx : ComputableInPolyTime (fun q : Input × ℕ ↦ q.1) encPadded encInput := fst _ _
  have hf : ComputableInPolyTime (fun q : Input × ℕ ↦ q.2) encPadded encUnary := snd _ _
  have hd := dim_polytime.comp hx
  have hp := points_polytime.comp hx
  have ht := tree_polytime B hB S hS mode
  exact (learn_all_polytime L hL mode).comp (((hd.prod hp).prod hf).prod ht)

theorem front_polytime (S : ScheduleCode) (hS : ScheduleSpec S)
    (B : RefineCode) (hB : RefineSpecL B) (L : LearnCode) (hL : LearnSpecL L)
    (mode : Mode) : ComputableInPolyTime (frontL S B L mode) encPadded
      (encOption encLearned) := by
  have hx : ComputableInPolyTime (fun q : Input × ℕ ↦ q.1) encPadded encInput := fst _ _
  have hd := dim_polytime.comp hx
  have hp := points_polytime.comp hx
  have hn := (length_list _).comp hp
  have hl := learned_polytime S hS B hB L hL mode
  have h := select_polytime.comp ((hn.prod (hd.prod ((hS.polytime mode).prod hp))).prod hl)
  exact h.of_enc_eq fun q ↦ rfl

/-- Rectangular input lists are recovered exactly by the typed sample function. -/
theorem pointsOf_input (x : Input) (hx : Valid x) :
    pointsOf (inputPoints x) = x.points := by
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

/-- Replay provenance places every stored edge inside the finite schedule. -/
theorem leaf_depth_lt (B : RefineCode) (hB : RefineSpecL B) {n d : ℕ}
    (mode : Mode) (k : ℕ) (params : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel : ℕ) (C : Candidate n d) (hC : C ∈ leaves B.ref mode k params x fuel)
    (e : Edge n d) (he : e ∈ C.path) : e.depth < k := by
  obtain ⟨_, ⟨states, _, _, hsteps⟩, hlen⟩ := leaf_history B.ref hB.contract
    mode k params x fuel C hC
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp he
  obtain ⟨_, _, hd, _⟩ := hsteps i
  change (C.path.get i).depth = i.val at hd
  rw [hi] at hd
  have := i.isLt
  omega

/-- Tree traversal, learning and first-accepted search preserve the typed enumeration. -/
theorem front_agrees (S : ScheduleCode) (hS : ScheduleSpec S)
    (B : RefineCode) (hB : RefineSpecL B) (L : LearnCode) (hL : LearnSpecL L)
    (mode : Mode) (x : Input) (fuel : ℕ) (hx : Valid x) (hf : need mode x ≤ fuel) :
    frontL S B L mode (x, fuel) =
      (select (Schedule.params mode x.wmin x.k)
        (inputPoints x)
        (learnAll L.learn mode (inputPoints x) fuel
          (leaves B.ref mode x.k (Schedule.params mode x.wmin x.k)
            (inputPoints x) fuel))).map learnedList := by
  dsimp only [frontL]
  rw [tree_agrees B hB S hS mode x fuel hx hf]
  have hl := learn_all_agrees L hL mode (inputPoints x) fuel
    (leaves B.ref mode x.k (Schedule.params mode x.wmin x.k) (inputPoints x) fuel)
  rw [pointsOf_input x hx] at hl
  rw [hl]
  have hs := select_agrees (Schedule.params mode x.wmin x.k) (inputPoints x)
    (learnAll L.learn mode (inputPoints x) fuel
      (leaves B.ref mode x.k (Schedule.params mode x.wmin x.k) (inputPoints x) fuel))
    (S.run mode (x, fuel))
  rw [pointsOf_input x hx] at hs
  apply hs
  intro learned hlearned e he
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hlearned
  have hd := leaf_depth_lt B hB mode x.k (Schedule.params mode x.wmin x.k)
    (inputPoints x) fuel C hC e he
  rw [hS.agrees mode x fuel hx hf]
  simp [List.getD_eq_getElem?_getD, hd]

/-- A typed expression definitionally identical to `execute` in `Alg`. -/
noncomputable def pipeline (ref : Refiner) (learn : Learner) (tests : TestBuilder)
    (mode : Mode) (x : Input) (fuel : ℕ) : Output :=
  let pts := inputPoints x
  if x.k ≤ 1 then List.replicate x.points.length 0 else
  let params := Schedule.params mode x.wmin x.k
  let Cs := leaves ref mode x.k params pts fuel
  let learned := learnAll learn mode pts fuel Cs
  match select params pts learned with
  | none => List.replicate x.points.length 0
  | some L => finish tests mode x.k x.Δ pts fuel L.estimates

/-- Junk inputs abort before evaluating a binary-count schedule or tree. -/
def runL (S : ScheduleCode) (B : RefineCode) (L : LearnCode) (T : TestCode)
    (mode : Mode) (q : Input × ℕ) : Output :=
  if q.1.k ≤ 1 then List.replicate q.1.points.length 0 else
  if Valid q.1 then
    let selected := frontL S B L mode q
    if selected.isNone then List.replicate q.1.points.length 0 else
      finishL T mode (dim q.1.points) q.1.k q.1.Δ q.1.points q.2
        (selected.getD (([], []), [])).2
  else List.replicate q.1.points.length 0

/-- All branches, including exhausted or malformed inputs, have polynomial cost. -/
theorem run_polytime (S : ScheduleCode) (hS : ScheduleSpec S)
    (B : RefineCode) (hB : RefineSpecL B) (L : LearnCode) (hL : LearnSpecL L)
    (T : TestCode) (hT : TestSpecL T) (mode : Mode) :
    ComputableInPolyTime (runL S B L T mode) encPadded encOutput := by
  have hx : ComputableInPolyTime (fun q : Input × ℕ ↦ q.1) encPadded encInput := fst _ _
  have hf : ComputableInPolyTime (fun q : Input × ℕ ↦ q.2) encPadded encUnary := snd _ _
  have hk := k_polytime.comp hx
  have hd := dim_polytime.comp hx
  have hp := points_polytime.comp hx
  have hΔ := separation_polytime.comp hx
  have hz := zero_labels_polytime.comp hx
  have hs := front_polytime S hS B hB L hL mode
  have hsel := (optionGetD encLearned).comp (hs.prod (const (([], []), [])))
  have he := (snd _ _).comp hsel
  have hout := (finish_polytime T hT mode).comp
    ((hd.prod (hk.prod (hΔ.prod (hp.prod he)))).prod hf)
  have hnone : ComputableInPolyTime (fun q ↦ (frontL S B L mode q).isNone)
      encPadded encBool := (bool_not.comp (optionIsSome hs)).of_enc_eq fun q ↦ by
    dsimp only [Function.comp_apply]
    cases frontL S B L mode q <;> rfl
  exact SoS.PolyTime.ite_prop (.of_tidy
      (ComputableTidilyInPolyTime.binary_le' hk.tidy (ComputableTidilyInPolyTime.const 1))) hz
    (SoS.PolyTime.ite_prop (valid_polytime.comp hx)
      (ite' hnone hz hout) hz)

theorem run_zero (S : ScheduleCode) (B : RefineCode) (L : LearnCode) (T : TestCode)
    (mode : Mode) (x : Input) (fuel : ℕ) (hk : x.k ≤ 1) :
    runL S B L T mode (x, fuel) = List.replicate x.points.length 0 := by
  simp [runL, hk]

/-- Sufficient fuel removes every implementation guard in the composed program. -/
theorem run_agrees (S : ScheduleCode) (hS : ScheduleSpec S)
    (B : RefineCode) (hB : RefineSpecL B) (L : LearnCode) (hL : LearnSpecL L)
    (T : TestCode) (hT : TestSpecL T) (mode : Mode) (x : Input) (fuel : ℕ)
    (hx : Valid x) (hf : need mode x ≤ fuel) :
    runL S B L T mode (x, fuel) = pipeline B.ref L.learn T.tests mode x fuel := by
  by_cases hk : x.k ≤ 1
  · simp [runL, pipeline, hk]
  · let selected := select (Schedule.params mode x.wmin x.k) (inputPoints x)
      (learnAll L.learn mode (inputPoints x) fuel
        (leaves B.ref mode x.k (Schedule.params mode x.wmin x.k) (inputPoints x) fuel))
    have ha : frontL S B L mode (x, fuel) = selected.map learnedList :=
      front_agrees S hS B hB L hL mode x fuel hx hf
    dsimp only [pipeline]
    change runL S B L T mode (x, fuel) =
      (if x.k ≤ 1 then List.replicate x.points.length 0 else
        match selected with
        | none => List.replicate x.points.length 0
        | some learned => finish T.tests mode x.k x.Δ (inputPoints x) fuel learned.estimates)
    simp only [runL, ite_eq_right hk, ite_eq_left hx, ha]
    cases selected with
    | none => rfl
    | some learned =>
      simp only [Option.map_some, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
        Option.getD_some, learnedList]
      have h := finish_agrees T hT mode x.k x.Δ (inputPoints x) fuel learned.estimates
      rw [pointsOf_input x hx] at h
      exact h

end ABBKS26.Assembly.Exec
