module

public import BB20.Machine.EffNu
public import Background.PolyTime.Lists
public import Background.PolyTime.Rat

/-!
# The empirical proxy in polynomial time

A certificate (`Turing.MultiTapeTM.ComputableInPolyTime`) for `BB20.Machine.Run.effNu`, in the
composable form `BB20.Machine.Run.PT.effNu'`: the samples as lists of bits, the numbers `n`, `u`
and the elements of `I` and `S` in unary.
-/

@[expose] public section

namespace BB20.Machine.Run.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- A natural number in unary, as a rational. -/
theorem rat_ofUnary' {k : α → ℕ} (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a => (k a : ℚ)) input encRat :=
  rat_natCast' (unary_to_binary.comp hk)

/-- A case distinction on a decidable proposition. -/
theorem ite_prop' {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a => decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a => if p a then f a else g a) input encB :=
  ite_decide hp hf hg

theorem agreeAt' {u : α → ℕ} {L : α → List ℕ} {x : α → List Bool} {b : α → Bool}
    {y : α → List Bool} (hu : ComputableInPolyTime u input encUnary)
    (hL : ComputableInPolyTime L input (encList encUnary))
    (hx : ComputableInPolyTime x input encBits) (hb : ComputableInPolyTime b input encBool)
    (hy : ComputableInPolyTime y input encBits) :
    ComputableInPolyTime (fun a => agreeAt (u a) (L a) (x a) (b a) (y a)) input encBool := by
  unfold agreeAt
  have htest : ComputableInPolyTime (fun p : α × ℕ => (y p.1).getD p.2 false ==
      if p.2 = u p.1 then b p.1 else (x p.1).getD p.2 false) (encPair input encUnary) encBool :=
    beq (bitsGetDWithInput (hy.comp (fst _ _)) (snd _ _) false)
      (ite_prop' (decide_eq' (snd _ _) (hu.comp (fst _ _))) (hb.comp (fst _ _))
        (bitsGetDWithInput (hx.comp (fst _ _)) (snd _ _) false))
  exact allWithInput (test := fun a i => (y a).getD i false ==
      if i = u a then b a else (x a).getD i false) hL htest

theorem cntL' {smp : α → List (List Bool)} {u : α → ℕ} {L : α → List ℕ} {x : α → List Bool}
    {b : α → Bool} (hs : ComputableInPolyTime smp input (encList encBits))
    (hu : ComputableInPolyTime u input encUnary)
    (hL : ComputableInPolyTime L input (encList encUnary))
    (hx : ComputableInPolyTime x input encBits) (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime (fun a => cntL (smp a) (u a) (L a) (x a) (b a)) input encUnary := by
  unfold cntL
  exact countPWithInput (test := fun a y => agreeAt (u a) (L a) (x a) (b a) y) hs
    (agreeAt' (hu.comp (fst _ _)) (hL.comp (fst _ _)) (hx.comp (fst _ _)) (hb.comp (fst _ _))
      (snd _ _))

theorem margL' {smp : α → List (List Bool)} {u : α → ℕ} {L : α → List ℕ} {x : α → List Bool}
    {b : α → Bool} (hs : ComputableInPolyTime smp input (encList encBits))
    (hu : ComputableInPolyTime u input encUnary)
    (hL : ComputableInPolyTime L input (encList encUnary))
    (hx : ComputableInPolyTime x input encBits) (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime (fun a => margL (smp a) (u a) (L a) (x a) (b a)) input encRat := by
  unfold margL
  exact rat_div' (rat_ofUnary' (cntL' hs hu hL hx hb))
    (rat_ofUnary' ((length_list encBits).comp hs))

theorem termL' {smp : α → List (List Bool)} {u : α → ℕ} {I S : α → List ℕ} {x : α → List Bool}
    {b : α → Bool} (hs : ComputableInPolyTime smp input (encList encBits))
    (hu : ComputableInPolyTime u input encUnary)
    (hI : ComputableInPolyTime I input (encList encUnary))
    (hS : ComputableInPolyTime S input (encList encUnary))
    (hx : ComputableInPolyTime x input encBits) (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime (fun a => termL (smp a) (u a) (I a) (S a) (x a) (b a)) input encRat := by
  unfold termL
  have hIS := listAppend' hI hS
  have h := rat_div' (rat_abs' (rat_sub' (margL' hs hu (cons' hu hIS) hx hb)
    (rat_div' (rat_mul' (margL' hs hu (cons' hu hS) hx hb) (margL' hs hu hIS hx hb))
      (margL' hs hu hS hx hb)))) (rat_ofUnary' (cntL' hs hu hIS hx hb))
  exact h

/-- **The empirical proxy is computable in polynomial time.** -/
theorem effNu' {smp : α → List (List Bool)} {n u : α → ℕ} {I S : α → List ℕ}
    (hs : ComputableInPolyTime smp input (encList encBits))
    (hn : ComputableInPolyTime n input encUnary) (hu : ComputableInPolyTime u input encUnary)
    (hI : ComputableInPolyTime I input (encList encUnary))
    (hS : ComputableInPolyTime S input (encList encUnary)) :
    ComputableInPolyTime (fun a => effNu (smp a) (n a) (u a) (I a) (S a)) input encRat := by
  unfold effNu
  have hterm : ComputableInPolyTime (fun p : α × List Bool =>
      termL (smp p.1) (u p.1) (I p.1) (S p.1) p.2 true +
        termL (smp p.1) (u p.1) (I p.1) (S p.1) p.2 false) (encPair input encBits) encRat :=
    rat_add' (termL' (hs.comp (fst _ _)) (hu.comp (fst _ _)) (hI.comp (fst _ _))
        (hS.comp (fst _ _)) (snd _ _) (const true))
      (termL' (hs.comp (fst _ _)) (hu.comp (fst _ _)) (hI.comp (fst _ _))
        (hS.comp (fst _ _)) (snd _ _) (const false))
  have hsum := rat_sum' (mapWithInput (f := fun a x =>
    termL (smp a) (u a) (I a) (S a) x true + termL (smp a) (u a) (I a) (S a) x false) hs hterm)
  have hlI := (length_list encUnary).comp hI
  have hlS := (length_list encUnary).comp hS
  have h := rat_div' (rat_mul' hsum (rat_two_pow' (unary_sub' hn
    (unary_add' (unary_add' hlI hlS) (const 1))))) (rat_two_pow' (unary_sub' hn hlS))
  exact h

end BB20.Machine.Run.PT
