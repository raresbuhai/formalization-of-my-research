module

public import BBKS24.Algorithm
public import Complexity.Tactic.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The algorithm runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for every function of the algorithm, with
the coins as a list of numbers `0, 1` (`BBKS24.Alg.algN`), ending with
`BBKS24.Alg.algN_polytime`.

Encodings: vertex numbers, grid points and counts are unary (all at most polynomial in the input:
the grid has `M ≤ 8 n³` points); `k`, the pruning threshold and the integer test are binary, since
`k` is given in binary and may be large.
-/

@[expose] public section

namespace BBKS24.Alg

open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Pairs of vertex numbers, in unary. -/
abbrev encE2 : List (ℕ × ℕ) ↪ List Bool := encList (encPair encUnary encUnary)

/-- Lists of vertex numbers, in unary. -/
abbrev encVs : List ℕ ↪ List Bool := encList encUnary

/-- A case distinction on a decidable proposition. -/
theorem ite_prop {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a => decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a => if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

/-- A unary natural, in binary. -/
theorem toBinary' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

/-! ### Reading the input -/

theorem numV_polytime : ComputableInPolyTime numV encInput encUnary := by
  have h : numV = fun x : Input ↦ min (x.2.2.length + 1) x.1 := funext fun x ↦ min_comm _ _
  rw [h]
  exact binary_min_unary' (by fun_prop) (by fun_prop)

@[fun_prop]
theorem numV' {f : α → Input} (hf : ComputableInPolyTime f input encInput) :
    ComputableInPolyTime (fun a ↦ numV (f a)) input encUnary :=
  numV_polytime.comp hf

theorem pairs_polytime : ComputableInPolyTime pairs encUnary encE2 := by
  unfold pairs
  exact flatMapWithInput (by fun_prop)
    (mapWithInput (filterWithInput (by fun_prop) (unary_lt' (by fun_prop) (by fun_prop)))
      (by fun_prop))

@[fun_prop]
theorem pairs' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ pairs (f a)) input encE2 :=
  pairs_polytime.comp hf

theorem nonEdges_polytime : ComputableInPolyTime (fun p : ℕ × List Bool ↦ nonEdges p.1 p.2)
    (encPair encUnary encBits) encE2 := by
  unfold nonEdges
  have hbits : ComputableInPolyTime (fun p : ℕ × List Bool ↦ p.2) (encPair encUnary encBits)
      (encList encBool) := (bits_encList_polyTime encBool).1.comp (snd _ _)
  have hzip : ComputableInPolyTime (fun p : ℕ × List Bool ↦ (pairs p.1).zip p.2)
      (encPair encUnary encBits) (encList (encPair (encPair encUnary encUnary) encBool)) :=
    (zip _ _).comp (g := fun p : ℕ × List Bool ↦ (pairs p.1, p.2)) ((pairs' (fst _ _)).prod hbits)
  have hf : ComputableInPolyTime (fun p : ℕ × List Bool ↦
      ((pairs p.1).zip p.2).filter fun q ↦ !q.2) (encPair encUnary encBits)
      (encList (encPair (encPair encUnary encUnary) encBool)) :=
    filterWithInput hzip (by fun_prop)
  exact mapWithInput hf (by fun_prop)

@[fun_prop]
theorem nonEdges' {f : α → ℕ} {g : α → List Bool} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encBits) :
    ComputableInPolyTime (fun a ↦ nonEdges (f a) (g a)) input encE2 :=
  nonEdges_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-! ### The cleanup -/

theorem decide_eq_binary {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ decide (f a = g a)) input encBool := by
  have h : (fun a ↦ decide (f a = g a)) = fun a ↦ (decide (f a ≤ g a) && decide (g a ≤ f a)) :=
    funext fun a ↦ by
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
        decide_eq_true_eq]
      omega
  rw [h]
  exact bool_and' (binary_le' hf hg) (binary_le' hg hf)

theorem isCliqueL_polytime : ComputableInPolyTime
    (fun x : ℕ × List (ℕ × ℕ) × List ℕ ↦ isCliqueL x.1 x.2.1 x.2.2)
    (encPair encNat (encPair encE2 encVs)) encBool := by
  unfold isCliqueL
  have hlen : ComputableInPolyTime (fun x : ℕ × List (ℕ × ℕ) × List ℕ ↦ decide (x.2.2.length = x.1))
      (encPair encNat (encPair encE2 encVs)) encBool :=
    decide_eq_binary (toBinary' (by fun_prop)) (by fun_prop)
  have hall : ComputableInPolyTime (fun x : ℕ × List (ℕ × ℕ) × List ℕ ↦
      x.2.2.all fun i ↦ x.2.2.all fun j ↦ !(decide (i < j) && decide ((i, j) ∈ x.2.1)))
      (encPair encNat (encPair encE2 encVs)) encBool :=
    allWithInput (by fun_prop) (allWithInput (by fun_prop)
      (bool_not.comp (bool_and' (unary_lt' (by fun_prop) (by fun_prop))
        (decide_mem (by fun_prop) (by fun_prop)))))
  exact bool_and' hlen hall

@[fun_prop]
theorem isCliqueL' {f : α → ℕ} {g : α → List (ℕ × ℕ)} {h : α → List ℕ}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encE2)
    (hh : ComputableInPolyTime h input encVs) :
    ComputableInPolyTime (fun a ↦ isCliqueL (f a) (g a) (h a)) input encBool :=
  isCliqueL_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem interCount_polytime : ComputableInPolyTime (fun x : List ℕ × List ℕ ↦ interCount x.1 x.2)
    (encPair encVs encVs) encUnary := by
  unfold interCount
  have h : ComputableInPolyTime (fun x : List ℕ × List ℕ ↦ x.1.filter fun a ↦ decide (a ∈ x.2))
      (encPair encVs encVs) encVs :=
    filterWithInput (by fun_prop) (decide_mem (by fun_prop) (by fun_prop))
  fun_prop

@[fun_prop]
theorem interCount' {f g : α → List ℕ} (hf : ComputableInPolyTime f input encVs)
    (hg : ComputableInPolyTime g input encVs) :
    ComputableInPolyTime (fun a ↦ interCount (f a) (g a)) input encUnary :=
  interCount_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-- One pruning step, with the threshold `Δ` in binary. -/
theorem pruneStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × List (List ℕ)) × List ℕ ↦ pruneStep p.1.1 p.1.2 p.2)
    (encPair (encPair encNat (encList encVs)) encVs) (encList encVs) := by
  unfold pruneStep
  exact ite' (allWithInput (by fun_prop)
    (binary_lt' (toBinary' (by fun_prop)) (by fun_prop))) (by fun_prop) (by fun_prop)

theorem length_encList_append_singleton {β : Type} (e : β ↪ List Bool) (l : List β) (a : β) :
    (encList e (l ++ [a])).length = (encList e l).length + (2 * (e a).length + 1) := by
  rw [length_encList, length_encList, List.map_append, List.sum_append]
  simp

/-- The cleanup, with the threshold `Δ` in binary. -/
theorem cleanupL_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦ cleanupL x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encNat (encPair encNat (encPair encE2 (encList encVs)))) (encList encVs) := by
  have h := funext fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦
    cleanupL_eq x.1 x.2.1 x.2.2.1 x.2.2.2
  rw [h]
  set enc := encPair encNat (encPair encNat (encPair encE2 (encList encVs)))
  have hl : ComputableInPolyTime (fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦
      x.2.2.2.filter (isCliqueL x.1 x.2.2.1)) enc (encList encVs) :=
    filterWithInput (by fun_prop) (by fun_prop)
  refine foldlWith_of_bounded_growth (par := fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦ x.2.1)
    (by fun_prop) hl (const []) pruneStep_polytime
    (growth := fun x ↦ 2 * (enc x).length + 1) ?_ ?_
  · exact ((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)
  · intro x state value hv
    have hv' : value ∈ x.2.2.2 := (List.mem_filter.1 hv).1
    have h1 : (encVs value).length ≤ (enc x).length := by
      refine (SizedListEncoding.length_elem_le (encA := encVs) (encL := encList encVs) _ _
        hv').trans ?_
      simp only [enc, length_encPair]
      omega
    unfold pruneStep
    split_ifs
    · rw [length_encList_append_singleton]
      omega
    · omega

@[fun_prop]
theorem cleanupL' {f g : α → ℕ} {h : α → List (ℕ × ℕ)} {l : α → List (List ℕ)}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encNat)
    (hh : ComputableInPolyTime h input encE2) (hl : ComputableInPolyTime l input (encList encVs)) :
    ComputableInPolyTime (fun a ↦ cleanupL (f a) (g a) (h a) (l a)) input (encList encVs) :=
  cleanupL_polytime.comp (g := fun a ↦ (f a, g a, h a, l a)) (hf.prod (hg.prod (hh.prod hl)))

theorem toBinaryLists : ComputableInPolyTime (fun l : List (List ℕ) ↦ l) (encList encVs)
    (encList (encList encNat)) := by
  have h : ComputableInPolyTime (fun l : List (List ℕ) ↦ l.map fun q ↦ q.map fun i ↦ i)
      (encList encVs) (encList (encList encNat)) :=
    mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (toBinary' (by fun_prop)))
  simpa only [List.map_id'] using h

/-! ### Binary arithmetic -/

theorem bAdd {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hf.tidy hg.tidy)

theorem bMul {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a * g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_mul' hf.tidy hg.tidy)

theorem bDiv {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a / g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_div' hf.tidy hg.tidy)

theorem bLe {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ decide (f a ≤ g a)) input encBool :=
  .of_tidy (ComputableTidilyInPolyTime.binary_le' hf.tidy hg.tidy)

theorem bPow {f : α → ℕ} (hf : ComputableInPolyTime f input encNat) (e : ℕ) :
    ComputableInPolyTime (fun a ↦ f a ^ e) input encNat :=
  binary_pow' hf (const e)

theorem bool_or' {f g : α → Bool} (hf : ComputableInPolyTime f input encBool)
    (hg : ComputableInPolyTime g input encBool) :
    ComputableInPolyTime (fun a ↦ f a || g a) input encBool := by
  have h := bool_not.comp (bool_and' (bool_not.comp hf) (bool_not.comp hg))
  convert h using 1
  funext a
  simp only [Function.comp_apply]
  cases f a <;> cases g a <;> rfl

/-! ### The statistic -/

@[fun_prop]
theorem radjL' {E : α → List (ℕ × ℕ)} {u v : α → ℕ} (hE : ComputableInPolyTime E input encE2)
    (hu : ComputableInPolyTime u input encUnary) (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a ↦ radjL (E a) (u a) (v a)) input encBool := by
  unfold radjL
  have hmm : ComputableInPolyTime (fun a ↦ (min (u a) (v a), max (u a) (v a))) input
      (encPair encUnary encUnary) := by fun_prop
  exact bool_or' (unary_eq' hu hv) (bool_not.comp (decide_mem hE hmm))

@[fun_prop]
theorem headCount' {E : α → List (ℕ × ℕ)} {l : α → List ℕ} {i : α → ℕ}
    (hE : ComputableInPolyTime E input encE2) (hl : ComputableInPolyTime l input encVs)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ headCount (E a) (l a) (i a)) input encUnary := by
  unfold headCount
  exact countPWithInput hl (radjL' (hE.comp (fst _ _)) (snd _ _) (hi.comp (fst _ _)))

@[fun_prop]
theorem levelCount' {n e : α → ℕ} {E : α → List (ℕ × ℕ)} {l : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hE : ComputableInPolyTime E input encE2)
    (hl : ComputableInPolyTime l input encVs) (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ levelCount (n a) (E a) (l a) (e a)) input encUnary := by
  unfold levelCount
  exact countPWithInput (by fun_prop)
    (unary_eq' (headCount' (hE.comp (fst _ _)) (hl.comp (fst _ _)) (snd _ _)) (he.comp (fst _ _)))

@[fun_prop]
theorem selTest' {n M j k : α → ℕ} {E : α → List (ℕ × ℕ)} {l : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hM : ComputableInPolyTime M input encUnary)
    (hj : ComputableInPolyTime j input encUnary) (hk : ComputableInPolyTime k input encNat)
    (hE : ComputableInPolyTime E input encE2) (hl : ComputableInPolyTime l input encVs) :
    ComputableInPolyTime (fun a ↦ selTest (n a) (M a) (j a) (k a) (E a) (l a)) input encBool := by
  unfold selTest
  have hc : ∀ e : ℕ, ComputableInPolyTime (fun a ↦ levelCount (n a) (E a) (l a) e) input encNat :=
    fun e ↦ toBinary' (levelCount' hn hE hl (const e))
  have hw : ComputableInPolyTime (fun a ↦ M a - j a) input encNat := toBinary' (unary_sub' hM hj)
  have hjB := toBinary' hj
  exact bLe
    (bAdd (bMul (const 2) (bAdd (bMul (bMul (hc 3) (bPow hw 3)) hjB)
      (bMul (bMul (hc 1) hw) (bPow hjB 3)))) (bMul hk (bPow hw 4)))
    (bMul (const 2) (bAdd (bAdd (bMul (hc 4) (bPow hw 4)) (bMul (bMul (hc 2) (bPow hw 2))
      (bPow hjB 2))) (bMul (hc 0) (bPow hjB 4))))

@[fun_prop]
theorem selectedL' {n M j k : α → ℕ} {E : α → List (ℕ × ℕ)} {l : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hM : ComputableInPolyTime M input encUnary)
    (hj : ComputableInPolyTime j input encUnary) (hk : ComputableInPolyTime k input encNat)
    (hE : ComputableInPolyTime E input encE2) (hl : ComputableInPolyTime l input encVs) :
    ComputableInPolyTime (fun a ↦ selectedL (n a) (M a) (j a) (k a) (E a) (l a)) input encVs := by
  unfold selectedL
  have hcons : ComputableInPolyTime (fun p : α × ℕ ↦ p.2 :: l p.1) (encPair input encUnary)
      encVs := by fun_prop
  exact filterWithInput (by fun_prop) (selTest' (hn.comp (fst _ _)) (hM.comp (fst _ _))
    (hj.comp (fst _ _)) (hk.comp (fst _ _)) (hE.comp (fst _ _)) hcons)

@[fun_prop]
theorem adjL' {E : α → List (ℕ × ℕ)} {u v : α → ℕ} (hE : ComputableInPolyTime E input encE2)
    (hu : ComputableInPolyTime u input encUnary) (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a ↦ adjL (E a) (u a) (v a)) input encBool := by
  have h : (fun a ↦ adjL (E a) (u a) (v a)) =
      fun a ↦ (!decide (u a = v a)) && !decide ((min (u a) (v a), max (u a) (v a)) ∈ E a) :=
    funext fun a ↦ by simp only [adjL, _root_.decide_not]
  rw [h]
  have hmm : ComputableInPolyTime (fun a ↦ (min (u a) (v a), max (u a) (v a))) input
      (encPair encUnary encUnary) := by fun_prop
  exact bool_and' (bool_not.comp (unary_eq' hu hv)) (bool_not.comp (decide_mem hE hmm))

@[fun_prop]
theorem refineL' {k : α → ℕ} {E : α → List (ℕ × ℕ)} {T : α → List ℕ}
    (hk : ComputableInPolyTime k input encNat) (hE : ComputableInPolyTime E input encE2)
    (hT : ComputableInPolyTime T input encVs) :
    ComputableInPolyTime (fun a ↦ refineL (k a) (E a) (T a)) input encVs := by
  unfold refineL
  have hcnt : ComputableInPolyTime (fun p : α × ℕ ↦ (T p.1).countP fun w ↦ adjL (E p.1) p.2 w)
      (encPair input encUnary) encUnary :=
    countPWithInput (hT.comp (fst _ _))
      (adjL' (hE.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _)) (snd _ _))
  exact filterWithInput hT
    (bLe (binary_sub' (hk.comp (fst _ _)) (const 1)) (toBinary' hcnt))

theorem triples_polytime : ComputableInPolyTime triples encUnary (encList encVs) := by
  unfold triples
  exact flatMapWithInput (by fun_prop)
    (flatMapWithInput (filterWithInput (by fun_prop) (unary_lt' (by fun_prop) (by fun_prop)))
      (mapWithInput (filterWithInput (by fun_prop) (unary_lt' (by fun_prop) (by fun_prop)))
        (by fun_prop)))

@[fun_prop]
theorem triples' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ triples (f a)) input (encList encVs) :=
  triples_polytime.comp hf

/-! ### The grid -/

theorem logN_eq_clog (n : ℕ) : logN n = Nat.clog 2 (n + 1 + (1 - n)) := by
  refine le_antisymm ?_ ?_
  · rw [logN, Nat.add_one_le_iff, Nat.lt_clog_iff_pow_lt (by norm_num)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.pow_log_le_self 2 hn.ne'
      omega
  · rw [Nat.clog_le_iff_le_pow (by norm_num), logN]
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
    have h2 : 2 ≤ 2 ^ (Nat.log 2 n + 1) :=
      le_self_pow₀ (by norm_num) (by omega)
    omega

theorem gridM_eq (n : ℕ) : gridM n = 8 ^ Nat.clog 2 (n + 1 + (1 - n)) := by
  rw [gridM, nBits, ← logN_eq_clog, pow_mul]
  norm_num

@[fun_prop]
theorem logN' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ logN (f a)) input encUnary := by
  unfold logN
  exact unary_add' (binary_log_two.comp (toBinary' hf)) (const 1)

@[fun_prop]
theorem nBits' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ nBits (f a)) input encUnary := by
  unfold nBits
  exact unary_mul' (const 3) (logN' hf)

@[fun_prop]
theorem gridM' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ gridM (f a)) input encUnary := by
  simp only [gridM_eq]
  exact unary_pow_clog_const (unary_add' (unary_add' hf (const 1)) (unary_sub' (const 1) hf)) 8 2

@[fun_prop]
theorem delta' {n k : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hk : ComputableInPolyTime k input encNat) :
    ComputableInPolyTime (fun a ↦ delta (n a) (k a)) input encNat := by
  unfold delta
  exact bAdd (bDiv (bPow hk 2) (bMul (toBinary' hn) (bPow (toBinary' (logN' hn)) 3))) (const 1)

@[fun_prop]
theorem candHigh' {n k M : α → ℕ} {E : α → List (ℕ × ℕ)}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encNat)
    (hM : ComputableInPolyTime M input encUnary) (hE : ComputableInPolyTime E input encE2) :
    ComputableInPolyTime (fun a ↦ candHigh (n a) (k a) (M a) (E a)) input (encList encVs) := by
  unfold candHigh
  have hM2 : ComputableInPolyTime (fun a ↦ M a / 2) input encUnary :=
    (unary_div_const 2).comp hM
  have hgrid : ComputableInPolyTime (fun a ↦ (List.range (M a)).filter fun j ↦ decide (M a / 2 ≤ j))
      input encVs :=
    filterWithInput (by fun_prop) (unary_le' (hM2.comp (fst _ _)) (snd _ _))
  refine flatMapWithInput hgrid (mapWithInput (triples' (hn.comp (fst _ _))) ?_)
  exact refineL' (hk.comp ((fst _ _).comp (fst _ _))) (hE.comp ((fst _ _).comp (fst _ _)))
    (selectedL' (hn.comp ((fst _ _).comp (fst _ _))) (hM.comp ((fst _ _).comp (fst _ _)))
      ((snd _ _).comp (fst _ _)) (hk.comp ((fst _ _).comp (fst _ _)))
      (hE.comp ((fst _ _).comp (fst _ _))) (snd _ _))

/-! ### The coins as numbers -/

/-- `Sampling.chunkVal`, for coins given as numbers (`1` for heads). -/
def chunkValN (b : ℕ) (c : List ℕ) (e : ℕ) : ℕ :=
  ((List.range b).map fun t ↦ if c.getD (e * b + t) 0 = 1 then 2 ^ t else 0).sum

/-- `nonEdgesAug`, for coins given as numbers. -/
def nonEdgesAugN (n b j : ℕ) (a : List Bool) (c : List ℕ) : List (ℕ × ℕ) :=
  ((((pairs n).zip a).zip (List.range (pairs n).length)).filter fun p ↦
    !p.1.2 && !decide (chunkValN b c p.2 < j)).map fun p ↦ p.1.1

/-- `candLow`, for coins given as numbers. -/
def candLowN (n k b M : ℕ) (a : List Bool) (c : List ℕ) : List (List ℕ) :=
  (List.range (M / 2 + 1)).flatMap fun j ↦
    (triples n).map fun t ↦
      refineL k (nonEdgesAugN n b j a c) (selectedL n M (M / 2) k (nonEdgesAugN n b j a c) t)

/-- **The algorithm, for coins given as numbers.** -/
def algN (y : Input × List ℕ) : Output :=
  cleanupL y.1.2.1 (delta (numV y.1) y.1.2.1) (nonEdges (numV y.1) y.1.2.2)
    (candHigh (numV y.1) y.1.2.1 (gridM (numV y.1)) (nonEdges (numV y.1) y.1.2.2) ++
      candLowN (numV y.1) y.1.2.1 (nBits (numV y.1)) (gridM (numV y.1)) y.1.2.2 y.2)

/-- The number of coins the algorithm reads, at most: `n² b`. -/
def coinLen (x : Input) : ℕ := numV x * numV x * nBits (numV x)

theorem list_sum_range (f : ℕ → ℕ) (b : ℕ) :
    ((List.range b).map f).sum = ∑ t ∈ Finset.range b, f t := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem getD_take_map_toNat {L i : ℕ} (r : List Bool) (hi : i < L) :
    ((r.map Bool.toNat).take L).getD i 0 = 1 ↔ r.getD i false = true := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
    List.getElem?_map]
  cases r[i]? with
  | none => simp
  | some x => cases x <;> simp

theorem chunkValN_eq {b L e : ℕ} (r : List Bool) (h : e * b + b ≤ L) :
    chunkValN b ((r.map Bool.toNat).take L) e = Sampling.chunkVal b r e := by
  rw [chunkValN, Sampling.chunkVal, list_sum_range]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [Finset.mem_range] at ht
  by_cases hr : r.getD (e * b + t) false = true
  · rw [ite_eq_left_iff.2 fun h' ↦ absurd hr h',
      ite_eq_left_iff.2 fun h' ↦ absurd ((getD_take_map_toNat r (by omega)).2 hr) h']
  · rw [ite_eq_right_iff.2 fun h' ↦ absurd h' hr,
      ite_eq_right_iff.2 fun h' ↦ absurd ((getD_take_map_toNat r (by omega)).1 h') hr]

theorem nonEdgesAugN_eq {n b j L : ℕ} (a r : List Bool) (h : (pairs n).length * b ≤ L) :
    nonEdgesAugN n b j a ((r.map Bool.toNat).take L) = nonEdgesAug n b j a r := by
  unfold nonEdgesAugN nonEdgesAug
  congr 1
  refine List.filter_congr fun p hp ↦ ?_
  have h2 : p.2 + 1 ≤ (pairs n).length := List.mem_range.1 (List.of_mem_zip hp).2
  have h3 : p.2 * b + b ≤ L :=
    calc p.2 * b + b = (p.2 + 1) * b := by ring
      _ ≤ (pairs n).length * b := Nat.mul_le_mul_right _ h2
      _ ≤ L := h
  rw [chunkValN_eq r h3]

theorem candLowN_eq {n k b M L : ℕ} (a r : List Bool) (h : (pairs n).length * b ≤ L) :
    candLowN n k b M a ((r.map Bool.toNat).take L) = candLow n k b M a r := by
  unfold candLowN candLow
  simp only [nonEdgesAugN_eq a r h]

theorem length_pairs_le (n : ℕ) : (pairs n).length ≤ n * n := by
  rw [pairs_eq, List.length_map, Sampling.length_pairsF, Nat.choose_two_right]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

/-- **The algorithm reads at most `coinLen x` coins.** -/
theorem alg_eq_algN (xr : Input × List Bool) :
    alg xr = algN (xr.1, (xr.2.map Bool.toNat).take (coinLen xr.1)) := by
  unfold alg algN coinLen
  dsimp only
  rw [candLowN_eq _ _ (Nat.mul_le_mul_right _ (length_pairs_le _))]

/-! ### Certificates for the coins -/

@[fun_prop]
theorem chunkValN' {b e : α → ℕ} {c : α → List ℕ} (hb : ComputableInPolyTime b input encUnary)
    (hc : ComputableInPolyTime c input encVs) (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ chunkValN (b a) (c a) (e a)) input encNat := by
  unfold chunkValN
  have hidx : ComputableInPolyTime (fun p : α × ℕ ↦ e p.1 * b p.1 + p.2) (encPair input encUnary)
      encUnary := unary_add' (unary_mul' (he.comp (fst _ _)) (hb.comp (fst _ _))) (snd _ _)
  have hterm : ComputableInPolyTime (fun p : α × ℕ ↦
      if (c p.1).getD (e p.1 * b p.1 + p.2) 0 = 1 then 2 ^ p.2 else 0)
      (encPair input encUnary) encNat :=
    ite_prop (unary_eq' (listGetDWithInput (hc.comp (fst _ _)) hidx 0) (const 1))
      (binary_two_pow.comp (snd _ _)) (const 0)
  have hmap := mapWithInput (f := fun a t ↦ if (c a).getD (e a * b a + t) 0 = 1 then 2 ^ t else 0)
    (by fun_prop : ComputableInPolyTime (fun a ↦ List.range (b a)) input encVs) hterm
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp hmap.tidy)

@[fun_prop]
theorem nonEdgesAugN' {n b j : α → ℕ} {a : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hb : ComputableInPolyTime b input encUnary)
    (hj : ComputableInPolyTime j input encUnary) (ha : ComputableInPolyTime a input encBits)
    (hc : ComputableInPolyTime c input encVs) :
    ComputableInPolyTime (fun x ↦ nonEdgesAugN (n x) (b x) (j x) (a x) (c x)) input encE2 := by
  unfold nonEdgesAugN
  have hbits : ComputableInPolyTime a input (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp ha
  have hz1 : ComputableInPolyTime (fun x ↦ (pairs (n x)).zip (a x)) input
      (encList (encPair (encPair encUnary encUnary) encBool)) :=
    (zip _ _).comp (g := fun x ↦ (pairs (n x), a x)) ((pairs' hn).prod hbits)
  have hlen : ComputableInPolyTime (fun x ↦ List.range (pairs (n x)).length) input encVs := by
    fun_prop
  have hz2 : ComputableInPolyTime (fun x ↦ ((pairs (n x)).zip (a x)).zip
      (List.range (pairs (n x)).length)) input
      (encList (encPair (encPair (encPair encUnary encUnary) encBool) encUnary)) :=
    (zip _ _).comp (g := fun x ↦ ((pairs (n x)).zip (a x), List.range (pairs (n x)).length))
      (hz1.prod hlen)
  have hf : ComputableInPolyTime (fun x ↦ (((pairs (n x)).zip (a x)).zip
      (List.range (pairs (n x)).length)).filter fun p ↦
        !p.1.2 && !decide (chunkValN (b x) (c x) p.2 < j x)) input
      (encList (encPair (encPair (encPair encUnary encUnary) encBool) encUnary)) :=
    filterWithInput hz2 (bool_and' (by fun_prop) (bool_not.comp (binary_lt'
      (chunkValN' (hb.comp (fst _ _)) (hc.comp (fst _ _)) (by fun_prop))
      (toBinary' (hj.comp (fst _ _))))))
  exact mapWithInput hf (by fun_prop)

@[fun_prop]
theorem candLowN' {n k b M : α → ℕ} {a : α → List Bool} {c : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hk : ComputableInPolyTime k input encNat)
    (hb : ComputableInPolyTime b input encUnary) (hM : ComputableInPolyTime M input encUnary)
    (ha : ComputableInPolyTime a input encBits) (hc : ComputableInPolyTime c input encVs) :
    ComputableInPolyTime (fun x ↦ candLowN (n x) (k x) (b x) (M x) (a x) (c x)) input
      (encList encVs) := by
  unfold candLowN
  have hM2 : ComputableInPolyTime (fun x ↦ M x / 2) input encUnary := (unary_div_const 2).comp hM
  have hr : ComputableInPolyTime (fun x ↦ List.range (M x / 2 + 1)) input encVs := by fun_prop
  refine flatMapWithInput hr (mapWithInput (triples' (hn.comp (fst _ _))) ?_)
  have f1 {β : Type} {e : β ↪ List Bool} {g : α → β} (hg : ComputableInPolyTime g input e) :
      ComputableInPolyTime (fun p : (α × ℕ) × List ℕ ↦ g p.1.1)
        (encPair (encPair input encUnary) encVs) e := hg.comp ((fst _ _).comp (fst _ _))
  have hE := nonEdgesAugN' (f1 hn) (f1 hb) ((snd _ _).comp (fst _ _)) (f1 ha) (f1 hc)
  exact refineL' (f1 hk) hE
    (selectedL' (f1 hn) (f1 hM) (f1 hM2) (f1 hk) hE (snd _ _))

/-- **The algorithm runs in polynomial time**, with the coins as numbers. -/
theorem algN_polytime : ComputableInPolyTime algN (encPair encInput encVs) encOutput := by
  have hx : ComputableInPolyTime (fun y : Input × List ℕ ↦ y.1) (encPair encInput encVs)
      encInput := fst _ _
  have hn : ComputableInPolyTime (fun y : Input × List ℕ ↦ numV y.1) (encPair encInput encVs)
      encUnary := numV' hx
  have hk : ComputableInPolyTime (fun y : Input × List ℕ ↦ y.1.2.1) (encPair encInput encVs)
      encNat := by fun_prop
  have ha : ComputableInPolyTime (fun y : Input × List ℕ ↦ y.1.2.2) (encPair encInput encVs)
      encBits := by fun_prop
  have hc : ComputableInPolyTime (fun y : Input × List ℕ ↦ y.2) (encPair encInput encVs)
      encVs := snd _ _
  have hE := nonEdges' hn ha
  unfold algN
  exact toBinaryLists.comp (cleanupL' hk (delta' hn hk) hE (listAppend'
    (candHigh' hn hk (gridM' hn) hE) (candLowN' hn hk (nBits' hn) (gridM' hn) ha hc)))

theorem coinLen_polytime : ComputableInPolyTime coinLen encInput encUnary := by
  unfold coinLen
  exact unary_mul' (unary_mul' (numV' id') (numV' id')) (nBits' (numV' id'))

end BBKS24.Alg
