module

public import ABBKS26.Assembly.ExecRoundAuxData

/-! Size, stopping, and machine certificates for the unchanged capped round loop. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundAux

open Common Rounding
open Turing.MultiTapeTM ComputableInPolyTime

abbrev encState := encPair encBool encPoints
abbrev encArgsFuel := encPair encRoundArgs encUnary

/-- The empty encoding has length zero, so the invariant also covers zero fuel. -/
theorem step_size (R : RoundCode) (q : RoundArgs × ℕ) (s : Bool × Points)
    (hs : (encPoints s.2).length ≤ q.2) :
    (encPoints (roundStep R q s).2).length ≤ q.2 := by
  unfold roundStep
  split
  · exact hs
  · split
    · exact hs
    · dsimp only
      split
      · assumption
      · exact hs

/-- Every intermediate basis, on junk inputs too, fits in the original unary fuel. -/
theorem iterate_size (R : RoundCode) (q : RoundArgs × ℕ) (i : ℕ) :
    (encPoints (((roundStep R q)^[i]) (false, [])).2).length ≤ q.2 := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact step_size R q _ ih


/-- Adding the cap test and the absorbing stop bit preserves a joint step certificate. -/
theorem step_polytime (R : RoundCode)
    (hR : ComputableInPolyTime R.step
      (encPair encArgsFuel encPoints) (encOption encVector)) :
    ComputableInPolyTime (fun p : (RoundArgs × ℕ) × (Bool × Points) ↦
      roundStep R p.1 p.2) (encPair encArgsFuel encState) encState := by
  have hq := fst encArgsFuel encState
  have hs := snd encArgsFuel encState
  have hb := (snd encBool encPoints).comp hs
  have hv := hR.comp (hq.prod hb)
  have hn := listAppend' hb (cons' ((optionGetD encVector).comp
    (hv.prod (const []))) (const []))
  have he : ComputableInPolyTime (fun B : Points ↦ encPoints B) encPoints encBits :=
    of_eq fun _ ↦ rfl
  have hcap := unary_le' (length_bits.comp (he.comp hn)) ((snd _ _).comp hq)
  unfold roundStep
  have hsome : ComputableInPolyTime
      (fun p : (RoundArgs × ℕ) × (Bool × Points) ↦
        if (encPoints (p.2.2 ++ [(R.step (p.1, p.2.2)).getD []])).length ≤ p.1.2
        then (false, p.2.2 ++ [(R.step (p.1, p.2.2)).getD []]) else (true, p.2.2))
      (encPair encArgsFuel encState) encState :=
    ite_decide hcap ((const false).prod hn) ((const true).prod hb)
  have hm := ite' (optionIsSome hv) hsome ((const true).prod hb)
  convert ite' ((fst encBool encPoints).comp hs) hs hm using 1
  funext p
  rcases p with ⟨q, b, B⟩
  dsimp only [Function.comp_apply]
  have hh (o : Option Vector) :
      (match o with
      | none => (true, B)
      | some v => if (encPoints (B ++ [v])).length ≤ q.2
          then (false, B ++ [v]) else (true, B)) =
        if o.isSome then
          if (encPoints (B ++ [o.getD []])).length ≤ q.2
          then (false, B ++ [o.getD []]) else (true, B)
        else (true, B) := by
    cases o <;> rfl
  cases b
  · exact hh _
  · rfl

/-- Unary iteration with the encoded basis cap gives one absolute polynomial degree.
The bound is on all intermediate states, not merely on the eventual output. -/
theorem loop_polytime (R : RoundCode)
    (hR : ComputableInPolyTime R.step
      (encPair encArgsFuel encPoints) (encOption encVector)) :
    ComputableInPolyTime (roundL R) encArgsFuel encPoints := by
  have hf := snd encRoundArgs encUnary
  have hi : ComputableInPolyTime (fun _ : RoundArgs × ℕ ↦ (false, []))
      encArgsFuel encState := (const false).prod (const [])
  have hbound : PolyBounded (fun q : RoundArgs × ℕ ↦ (encArgsFuel q).length)
      (fun q ↦ 2 * q.2 + 4) :=
    ((PolyBounded.const 2).mul hf.tidy.polyBounded).add (.const 4)
  have hit := ComputableTidilyInPolyTime.iterateWith
    ComputableTidilyInPolyTime.id' hf.tidy hi.tidy (step_polytime R hR).tidy hbound
    (fun q i _ ↦ by
      have h := iterate_size R q i
      simp only [encState, length_encPair]
      have hb (b : Bool) : (encBool b).length = 1 := rfl
      rw [hb]
      omega)
  exact (snd encBool encPoints).comp (ComputableInPolyTime.of_tidy hit)

/-- Framed encodings of prefixes cannot be longer than the whole basis encoding. -/
theorem take_size (B : Points) (i : ℕ) :
    (encPoints (B.take i)).length ≤ (encPoints B).length := by
  have h : (encPoints (B.take i ++ B.drop i)).length =
      (encPoints (B.take i)).length + (encPoints (B.drop i)).length := by
    change (encList encVector _).length = (encList encVector _).length +
      (encList encVector _).length
    simp only [length_encList, List.map_append, List.sum_append]
  rw [List.take_append_drop] at h
  omega

/-- Replaying a fixed capped plan produces its successive prefixes and eventually stops. -/
theorem replay_trace (R : RoundCode) (q : RoundArgs × ℕ) (B : Points)
    (hstep : ∀ S, R.step (q, S) = B[S.length]?)
    (hcap : (encPoints B).length ≤ q.2) (i : ℕ) :
    (((roundStep R q)^[i]) (false, [])).2 = B.take i ∧
      ((((roundStep R q)^[i]) (false, [])).1 = true → B.length ≤ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    generalize hs : ((roundStep R q)^[i]) (false, []) = s at *
    rcases s with ⟨b, S⟩
    rcases ih with ⟨hS, hb⟩
    dsimp only at hS hb ⊢
    subst S
    cases b
    · by_cases hi : i < B.length
      · have hc := (take_size B (i + 1)).trans hcap
        simp [roundStep, hstep, List.length_take, Nat.min_eq_left hi.le, hi, hc,
          List.take_append_getElem hi]
      · have hle : B.length ≤ i := by omega
        simp [roundStep, hstep, List.take_of_length_le hle,
          List.take_of_length_le (hle.trans (Nat.le_succ _)), hle.trans (Nat.le_succ _)]
    · have hle := hb rfl
      simp [roundStep, List.take_of_length_le hle,
        List.take_of_length_le (hle.trans (Nat.le_succ _)), hle.trans (Nat.le_succ _)]

/-- The public fuelled loop returns the whole plan as soon as its encoding fits. -/
theorem replay_eq (R : RoundCode) (q : RoundArgs × ℕ) (B : Points)
    (hstep : ∀ S, R.step (q, S) = B[S.length]?)
    (hcap : (encPoints B).length ≤ q.2) : roundL R q = B := by
  have hlen : B.length ≤ q.2 :=
    (length_le_length_encList encVector B).trans hcap
  exact (replay_trace R q B hstep hcap q.2).1.trans (List.take_of_length_le hlen)

end ABBKS26.Assembly.Exec.RoundAux
