module

public import ABBKS26.Assembly.ExecScheduleAux

/-! # Fuelled rational schedule evaluation and input validation -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime

structure ScheduleCode where
  run : Mode → Input × ℕ → Points

structure ScheduleSpec (S : ScheduleCode) : Prop where
  polytime : ∀ mode, ComputableInPolyTime (S.run mode) encPadded encPoints
  agrees : ∀ mode x fuel, Valid x → need mode x ≤ fuel →
    S.run mode (x, fuel) =
      (List.range x.k).map (fun h ↦ paramsList (Schedule.params mode x.wmin x.k h))
  count_le : ∀ mode x fuel, Valid x → need mode x ≤ fuel → x.k - 1 ≤ fuel

/-- Evaluate the backward rational schedule with fuel checks on loops and integer exponents. -/
theorem exists_schedule_code : ∃ S : ScheduleCode, ScheduleSpec S := by
  refine ⟨⟨ScheduleAux.run⟩, ?_⟩
  constructor
  · exact ScheduleAux.run_polytime
  · intro mode x fuel _ hf
    exact ScheduleAux.run_agrees mode x fuel hf
  · intro mode x fuel _ hf
    exact (Nat.sub_le x.k 1).trans ((ScheduleAux.k_le_need mode x).trans hf)

theorem dim_polytime : ComputableInPolyTime (fun x : Input ↦ dim x.points)
    encInput encUnary := by
  exact (length_list _).comp (.of_tidy
    (ComputableTidilyInPolyTime.listHeadDWithInput [] points_polytime.tidy))

theorem separation_polytime : ComputableInPolyTime Input.Δ encInput Encoding.encRat := by
  have h : ComputableInPolyTime
      (fun x : Input ↦ (x.k, x.wmin, x.Δ, x.δ, x.points)) encInput
      (encPair encNat (encPair Encoding.encRat
        (encPair Encoding.encRat (encPair Encoding.encRat encPoints)))) := of_eq fun _ ↦ rfl
  exact (fst _ _).comp ((snd _ _).comp ((snd _ _).comp h))

/-- Validation is polynomial before any parameter-count loop is initiated. -/
theorem valid_polytime : ComputableInPolyTime (fun x : Input ↦ decide (Valid x))
    encInput encBool := by
  have ht : ComputableInPolyTime
      (fun x : Input ↦ (x.k, x.wmin, x.Δ, x.δ, x.points)) encInput
      (encPair encNat (encPair Encoding.encRat
        (encPair Encoding.encRat (encPair Encoding.encRat encPoints)))) := of_eq fun _ ↦ rfl
  have hw := (fst _ _).comp ((snd _ _).comp ht)
  have he := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp ht)))
  have hrow : ComputableInPolyTime
      (fun p : Input × Vector ↦ decide (p.2.length = dim p.1.points))
      (encPair encInput encVector) encBool := .of_tidy
    (ComputableTidilyInPolyTime.decide_eq'
      ((length_list Encoding.encRat).comp (snd _ _)).tidy
      (dim_polytime.comp (fst _ _)).tidy)
  have hall := allWithInput
    (test := fun (x : Input) (row : Vector) ↦ decide (row.length = dim x.points))
    points_polytime hrow
  have h1 := (rat_lt' (const 0) hw).tidy
  have h2 := (rat_le' hw (const 1)).tidy
  have h3 := (rat_le' (rat_mul' (rat_natCast' k_polytime) hw) (const 1)).tidy
  have h4 := ComputableTidilyInPolyTime.binary_le'
    (ComputableTidilyInPolyTime.const 1) k_polytime.tidy
  have h5 := (rat_lt' (const 0) he).tidy
  have h := ComputableTidilyInPolyTime.bool_and' h1
    (ComputableTidilyInPolyTime.bool_and' h2
      (ComputableTidilyInPolyTime.bool_and' h3
        (ComputableTidilyInPolyTime.bool_and' h4
          (ComputableTidilyInPolyTime.bool_and' h5 hall.tidy))))
  refine (ComputableInPolyTime.of_tidy h).of_enc_eq fun x ↦ ?_
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp [Valid, List.all_eq_true, Function.comp_def]

end ABBKS26.Assembly.Exec
