module

public import BB20.Machine.Flat
public import BB20.Machine.NuPolyTime

/-!
# A round of the loop in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the functions of a round of the loop
(`BB20.Machine.Run.fstep`), ending with `BB20.Machine.Run.PT.fstep_polytime`. Numbers below `n`
and `n` itself are in unary, the round `j` and the number `K` of rounds of a phase in binary.
-/

@[expose] public section

namespace BB20.Machine.Run

/-- The successor of a word, without recursion: the leading digits `≥ n` become `0`, and the first
digit `< n` is increased. -/
theorem incr_eq (n : ℕ) (t : List ℕ) :
    incr n t = (t.takeWhile fun d => !decide (d < n)).map (fun _ => 0) ++
      ((((t.dropWhile fun d => !decide (d < n)).take 1).map (· + 1)) ++
        (t.dropWhile fun d => !decide (d < n)).tail) := by
  induction t with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : d < n
    · simp [incr, h]
    · simp [incr, h, ih]

/-- `List.erase`, without recursion. -/
theorem erase_eq (l : List ℕ) (a : ℕ) :
    l.erase a = l.takeWhile (· != a) ++ (l.dropWhile (· != a)).tail := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : b = a
    · subst h
      simp
    · simp [h, ih]

end BB20.Machine.Run

namespace BB20.Machine.Run.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- Lists of numbers, in unary. -/
abbrev encL : List ℕ ↪ List Bool := encList encUnary

/-! ### Lists -/

theorem incr' {n : α → ℕ} {t : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (ht : ComputableInPolyTime t input encL) :
    ComputableInPolyTime (fun a => incr (n a) (t a)) input encL := by
  have htest : ComputableInPolyTime (fun p : α × ℕ => !decide (p.2 < n p.1))
      (encPair input encUnary) encBool :=
    bool_not.comp' (unary_lt' (snd _ _) (hn.comp' (fst _ _)))
  have htw := listTakeWhile (test := fun a d => !decide (d < n a)) ht htest
  have hdw := listDropWhile (test := fun a d => !decide (d < n a)) ht htest
  have h1 := mapWithInput (f := fun _ (_ : ℕ) => (0 : ℕ)) htw (const (encOut := encUnary) 0)
  have h2 := mapWithInput (f := fun _ (d : ℕ) => d + 1) (listTakeBin hdw (const 1))
    (unary_add' (snd _ _) (const 1))
  have h3 := (tail (encA := encUnary)).comp' hdw
  have h := listAppend' h1 (listAppend' h2 h3)
  refine h.of_enc_eq fun a => ?_
  rw [incr_eq]

theorem erase' {l : α → List ℕ} {i : α → ℕ} (hl : ComputableInPolyTime l input encL)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (l a).erase (i a)) input encL := by
  have htest : ComputableInPolyTime (fun p : α × ℕ => p.2 != i p.1) (encPair input encUnary)
      encBool := bool_not.comp' (beq (snd _ _) (hi.comp' (fst _ _)))
  have h := listAppend' (listTakeWhile (test := fun a d => d != i a) hl htest)
    ((tail (encA := encUnary)).comp' (listDropWhile (test := fun a d => d != i a) hl htest))
  refine h.of_enc_eq fun a => ?_
  rw [erase_eq]

theorem candOf' {n : α → ℕ} {t : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (ht : ComputableInPolyTime t input encL) :
    ComputableInPolyTime (fun a => candOf (n a) (t a)) input encL := by
  unfold candOf
  exact filterWithInput (test := fun a i => decide (i ∈ t a)) (unary_range' hn)
    (decide_mem (ht.comp' (fst _ _)) (snd _ _))

theorem code' {I : α → List ℕ} (hI : ComputableInPolyTime I input encL) :
    ComputableInPolyTime (fun a => code (I a)) input encNat := by
  unfold code
  have hm := mapWithInput (f := fun _ (i : ℕ) => 2 ^ i) hI (binary_two_pow.comp' (snd _ _))
  exact (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp' hm

theorem okCand' {u : α → ℕ} {S I : α → List ℕ} (hu : ComputableInPolyTime u input encUnary)
    (hS : ComputableInPolyTime S input encL) (hI : ComputableInPolyTime I input encL) :
    ComputableInPolyTime (fun a => okCand (u a) (S a) (I a)) input encBool := by
  unfold okCand
  have he := bool_not.comp'
    ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listIsEmpty' encUnary)).comp' hI)
  have hm := bool_not.comp' (decide_mem hI hu)
  have ha := allWithInput (test := fun a i => !decide (i ∈ S a)) hI
    (bool_not.comp' (decide_mem (hS.comp' (fst _ _)) (snd _ _)))
  exact bool_and' (bool_and' he hm) ha

theorem better' {I : α → List ℕ} {b : α → Option (List ℕ)} (hI : ComputableInPolyTime I input encL)
    (hb : ComputableInPolyTime b input (encOption encL)) :
    ComputableInPolyTime (fun a => better (I a) (b a)) input encBool := by
  unfold better
  exact optionElimWithInput (body := fun a J => decide (code (I a) < code J)) hb (const true)
    (binary_lt' (code' (hI.comp' (fst _ _))) (code' (snd _ _)))

theorem nuOK' {smp : α → List (List Bool)} {n u : α → ℕ} {t : α → ℚ} {S I : α → List ℕ}
    (hs : ComputableInPolyTime smp input (encList encBits))
    (hn : ComputableInPolyTime n input encUnary) (hu : ComputableInPolyTime u input encUnary)
    (ht : ComputableInPolyTime t input encRat) (hS : ComputableInPolyTime S input encL)
    (hI : ComputableInPolyTime I input encL) :
    ComputableInPolyTime (fun a => nuOK (smp a) (n a) (u a) (t a) (S a) (I a)) input encBool := by
  unfold nuOK
  exact bool_and' (okCand' hu hS hI) (rat_lt' ht (effNu' hs hn hu hI hS))

theorem upd' {smp : α → List (List Bool)} {n u : α → ℕ} {t : α → ℚ} {S I : α → List ℕ}
    {b : α → Option (List ℕ)} (hs : ComputableInPolyTime smp input (encList encBits))
    (hn : ComputableInPolyTime n input encUnary) (hu : ComputableInPolyTime u input encUnary)
    (ht : ComputableInPolyTime t input encRat) (hS : ComputableInPolyTime S input encL)
    (hb : ComputableInPolyTime b input (encOption encL)) (hI : ComputableInPolyTime I input encL) :
    ComputableInPolyTime (fun a => upd (smp a) (n a) (u a) (t a) (S a) (b a) (I a)) input
      (encOption encL) := by
  unfold upd
  exact ite' (bool_and' (nuOK' hs hn hu ht hS hI) (better' hI hb)) ((optionSome encL).comp' hI)
    hb

theorem sstep' {smp : α → List (List Bool)} {n u : α → ℕ} {t : α → ℚ} {S : α → List ℕ}
    {q : α → List ℕ × Option (List ℕ)} (hs : ComputableInPolyTime smp input (encList encBits))
    (hn : ComputableInPolyTime n input encUnary) (hu : ComputableInPolyTime u input encUnary)
    (ht : ComputableInPolyTime t input encRat) (hS : ComputableInPolyTime S input encL)
    (hq : ComputableInPolyTime q input (encPair encL (encOption encL))) :
    ComputableInPolyTime (fun a => sstep (smp a) (n a) (u a) (t a) (S a) (q a)) input
      (encPair encL (encOption encL)) := by
  unfold sstep
  have h1 := (fst _ _).comp' hq
  have h2 := (snd _ _).comp' hq
  exact (incr' hn h1).prod (upd' hs hn hu ht hS h2 (candOf' hn h1))

/-! ### The state of the loop -/

/-- The encoding of the data of a run. -/
abbrev encDat : Dat ↪ List Bool :=
  encPair (encList encBits) (encPair encUnary (encPair encUnary (encPair encNat
    (encPair encRat (encPair encRat encBool)))))

/-- The encoding of the state between phases. -/
abbrev encMac : Mac ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encL (encPair encL (encList encL))))

/-- The encoding of the state within a phase. -/
abbrev encInn : Inn ↪ List Bool := encPair encNat (encPair encL (encOption encL))

/-- The encoding of the state of the loop. -/
abbrev encSt : St ↪ List Bool := encPair encDat (encPair encMac encInn)

section Fields

variable {d : α → Dat} (hd : ComputableInPolyTime d input encDat)
  {m : α → Mac} (hm : ComputableInPolyTime m input encMac)
include hd

theorem dat_smp : ComputableInPolyTime (fun a => (d a).1) input (encList encBits) :=
  (fst _ _).comp' hd

theorem dat_n : ComputableInPolyTime (fun a => (d a).2.1) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' hd)

theorem dat_k : ComputableInPolyTime (fun a => (d a).2.2.1) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hd))

theorem dat_K : ComputableInPolyTime (fun a => (d a).2.2.2.1) input encNat :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hd)))

theorem dat_t₂ : ComputableInPolyTime (fun a => (d a).2.2.2.2.1) input encRat :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hd))))

theorem dat_t₃ : ComputableInPolyTime (fun a => (d a).2.2.2.2.2.1) input encRat :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    ((snd _ _).comp' hd)))))

theorem dat_mode : ComputableInPolyTime (fun a => (d a).2.2.2.2.2.2) input encBool :=
  (snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    ((snd _ _).comp' hd)))))

omit hd
include hm

theorem mac_u : ComputableInPolyTime (fun a => (m a).1) input encUnary := (fst _ _).comp' hm

theorem mac_ph : ComputableInPolyTime (fun a => (m a).2.1) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' hm)

theorem mac_S : ComputableInPolyTime (fun a => (m a).2.2.1) input encL :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hm))

theorem mac_P : ComputableInPolyTime (fun a => (m a).2.2.2.1) input encL :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hm)))

theorem mac_acc : ComputableInPolyTime (fun a => (m a).2.2.2.2) input (encList encL) :=
  (snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hm)))

end Fields

/-! ### The end of a phase -/

theorem curS' {n ph : α → ℕ} {S : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hph : ComputableInPolyTime ph input encUnary) (hS : ComputableInPolyTime S input encL) :
    ComputableInPolyTime (fun a => curS (n a) (ph a) (S a)) input encL := by
  unfold curS
  exact ite_prop' (unary_lt' hph hn) hS (erase' hS (unary_sub' hph hn))

theorem curT' {n ph : α → ℕ} {t₂ t₃ : α → ℚ} (hn : ComputableInPolyTime n input encUnary)
    (hph : ComputableInPolyTime ph input encUnary) (h₂ : ComputableInPolyTime t₂ input encRat)
    (h₃ : ComputableInPolyTime t₃ input encRat) :
    ComputableInPolyTime (fun a => curT (n a) (ph a) (t₂ a) (t₃ a)) input encRat := by
  unfold curT
  exact ite_prop' (unary_lt' hph hn) h₂ h₃

theorem keep' {smp : α → List (List Bool)} {n u i : α → ℕ} {t₃ : α → ℚ} {mode : α → Bool}
    {S : α → List ℕ} {r : α → Option (List ℕ)}
    (hs : ComputableInPolyTime smp input (encList encBits))
    (hn : ComputableInPolyTime n input encUnary) (hu : ComputableInPolyTime u input encUnary)
    (ht : ComputableInPolyTime t₃ input encRat) (hmode : ComputableInPolyTime mode input encBool)
    (hS : ComputableInPolyTime S input encL) (hi : ComputableInPolyTime i input encUnary)
    (hr : ComputableInPolyTime r input (encOption encL)) :
    ComputableInPolyTime (fun a => keep (smp a) (n a) (u a) (t₃ a) (mode a) (S a) (i a) (r a))
      input encBool := by
  unfold keep
  exact bool_and' (decide_mem hS hi) (ite' hmode (optionIsSome hr)
    (rat_lt' ht (effNu' hs hn hu (cons' hi (const [])) (erase' hS hi))))

theorem newP' {d : α → Dat} {m : α → Mac} {r : α → Option (List ℕ)}
    (hd : ComputableInPolyTime d input encDat) (hm : ComputableInPolyTime m input encMac)
    (hr : ComputableInPolyTime r input (encOption encL)) :
    ComputableInPolyTime (fun a => newP (d a) (m a) (r a)) input encL := by
  unfold newP
  have hi := unary_sub' (mac_ph hm) (dat_n hd)
  exact listAppend' (mac_P hm) (ite' (keep' (dat_smp hd) (dat_n hd) (mac_u hm) (dat_t₃ hd)
    (dat_mode hd) (mac_S hm) hi hr) (cons' hi (const [])) (const []))

theorem trans' {d : α → Dat} {m : α → Mac} {r : α → Option (List ℕ)}
    (hd : ComputableInPolyTime d input encDat) (hm : ComputableInPolyTime m input encMac)
    (hr : ComputableInPolyTime r input (encOption encL)) :
    ComputableInPolyTime (fun a => trans (d a) (m a) (r a)) input encMac := by
  unfold trans
  have hP := newP' hd hm hr
  have hph1 := unary_add' (mac_ph hm) (const 1)
  have hgreedy : ComputableInPolyTime (fun a => ((m a).1, (m a).2.1 + 1,
      (m a).2.2.1 ++ (r a).getD [], (m a).2.2.2)) input encMac :=
    (mac_u hm).prod (hph1.prod ((listAppend' (mac_S hm)
      ((optionGetD encL).comp' (hr.prod (const [])))).prod
      ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' hm)))))
  have hprune : ComputableInPolyTime (fun a => ((m a).1, (m a).2.1 + 1, (m a).2.2.1,
      newP (d a) (m a) (r a), (m a).2.2.2.2)) input encMac :=
    (mac_u hm).prod (hph1.prod ((mac_S hm).prod (hP.prod (mac_acc hm))))
  have hnext : ComputableInPolyTime (fun a => ((m a).1 + 1, 0, ([] : List ℕ), ([] : List ℕ),
      (m a).2.2.2.2 ++ [newP (d a) (m a) (r a)])) input encMac :=
    (unary_add' (mac_u hm) (const 1)).prod ((const 0).prod ((const []).prod ((const []).prod
      (listAppend' (mac_acc hm) (cons' hP (const []))))))
  exact ite_prop' (unary_lt' (mac_ph hm) (dat_n hd)) hgreedy
    (ite_prop' (unary_lt' hph1 (unary_mul' (const 2) (dat_n hd))) hprune hnext)

theorem sstepAt' {d : α → Dat} {m : α → Mac} {q : α → List ℕ × Option (List ℕ)}
    (hd : ComputableInPolyTime d input encDat) (hm : ComputableInPolyTime m input encMac)
    (hq : ComputableInPolyTime q input (encPair encL (encOption encL))) :
    ComputableInPolyTime (fun a => sstepAt (d a) (m a) (q a)) input
      (encPair encL (encOption encL)) := by
  unfold sstepAt
  exact sstep' (dat_smp hd) (dat_n hd) (mac_u hm)
    (curT' (dat_n hd) (mac_ph hm) (dat_t₂ hd) (dat_t₃ hd))
    (curS' (dat_n hd) (mac_ph hm) (mac_S hm)) hq

/-- **A round of the loop is computable in polynomial time.** -/
theorem fstep_polytime : ComputableInPolyTime fstep encSt encSt := by
  unfold fstep
  have hd : ComputableInPolyTime (fun s : St => s.1) encSt encDat := fst _ _
  have hm : ComputableInPolyTime (fun s : St => s.2.1) encSt encMac :=
    (fst _ _).comp' (snd _ _)
  have hj : ComputableInPolyTime (fun s : St => s.2.2.1) encSt encNat :=
    (fst _ _).comp' ((snd _ _).comp' (snd _ _))
  have hq : ComputableInPolyTime (fun s : St => s.2.2.2) encSt (encPair encL (encOption encL)) :=
    (snd _ _).comp' ((snd _ _).comp' (snd _ _))
  have hsq := sstepAt' hd hm hq
  have hj1 := binary_add.comp' (hj.prod (const 1))
  have hadv : ComputableInPolyTime (fun s : St => (s.1, s.2.1, s.2.2.1 + 1,
      sstepAt s.1 s.2.1 s.2.2.2)) encSt encSt :=
    hd.prod (hm.prod (hj1.prod hsq))
  have hend : ComputableInPolyTime (fun s : St => (s.1, trans s.1 s.2.1
      (sstepAt s.1 s.2.1 s.2.2.2).2, 0, List.replicate s.1.2.2.1 0, none)) encSt encSt :=
    hd.prod ((trans' hd hm ((snd _ _).comp' hsq)).prod ((const 0).prod
      ((replicate (dat_k hd) (const 0)).prod (const none))))
  exact ite_prop' (unary_lt' (mac_u hm) (dat_n hd))
    (ite_prop' (binary_lt' hj1 (dat_K hd)) hadv hend) id'

end BB20.Machine.Run.PT
