module

public import ABBKS26.Assembly.ExecRoundAuxPoly

/-! Compilation of the capped planner, with bounds on every intermediate state. -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace ABBKS26.Assembly.Exec.RoundCertificates.Compile

open Common Rounding RoundProgram FrameAux.Linear
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

@[local fun_prop]
private theorem binary_of_unary {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) : ComputableInPolyTime n enc encNat :=
  unary_to_binary.comp hn

private theorem binary_add' {m n : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun x ↦ m x + n x) enc encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hm.tidy hn.tidy)

private theorem problem_bits {P : α → SoS.Solver.Problem}
    (hP : ComputableInPolyTime P enc SoS.Solver.encProblem) :
    ComputableInPolyTime (fun x ↦ (SoS.Solver.encProblem (P x)).length) enc encUnary :=
  length_bits.comp ((of_eq fun _ ↦ rfl).comp hP)

private theorem pairExponent_time {n i j : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary)
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun x ↦ pairExponent (n x) (i x) (j x))
      enc (encList encNat) := by
  unfold pairExponent
  apply mapWithInput (range.comp hn)
  apply binary_add'
  · exact ite_prop (by fun_prop) (const 1) (const 0)
  · exact ite_prop (by fun_prop) (const 1) (const 0)

private theorem objective_time {a : α → RoundArgs} {Q : α → MatrixL}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hn : ComputableInPolyTime (fun x ↦ (a x).1.numVars) enc encUnary)
    (hQ : ComputableInPolyTime Q enc encMatrix) :
    ComputableInPolyTime (fun x ↦ objective (a x) (Q x)) enc SoS.Solver.encProblem := by
  have hd : ComputableInPolyTime (fun x ↦ (a x).2.1) enc encUnary := by fun_prop
  have ht : ComputableInPolyTime (fun x ↦
      (List.range (a x).2.1).flatMap fun i ↦ (List.range (a x).2.1).map fun j ↦
        (pairExponent (a x).1.numVars i j, ent (Q x) i j))
      enc SoS.Solver.encRawPoly := by
    apply flatMapWithInput (range.comp hd)
    apply mapWithInput (range.comp (hd.comp (fst _ _)))
    exact (pairExponent_time (hn.comp ((fst _ _).comp (fst _ _)))
      ((snd _ _).comp (fst _ _)) (snd _ _)).prod (by fun_prop)
  change ComputableInPolyTime _ _ (encPair encNat
    (encPair encNat (encPair (encList SoS.Solver.encRawPoly)
      (encPair SoS.Solver.encRawPoly (encList SoS.Solver.encRawPoly)))))
  apply ComputableInPolyTime.prod (by fun_prop)
  apply ComputableInPolyTime.prod (by fun_prop)
  apply ComputableInPolyTime.prod (by fun_prop)
  exact ht.prod (const [])

private theorem accuracy_time {a : α → RoundArgs} {P : α → SoS.Solver.Problem}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hP : ComputableInPolyTime P enc SoS.Solver.encProblem) :
    ComputableInPolyTime (fun x ↦ accuracy (a x) (P x)) enc encRat := by
  unfold accuracy
  apply rat_div' (const 1)
  apply rat_two_pow'
  apply unary_add' _ (const 24)
  apply unary_add'
  · apply unary_add'
    · exact unary_add' (unary_mul' (const 2) (problem_bits hP))
        (binary_clog_two.comp (rat_natCeil' (by fun_prop)))
    · exact unary_mul' (const 4)
        (binary_clog_two.comp (rat_natCeil' (rat_div' (const 1) (by fun_prop))))
  · exact (binary_clog_two.comp (binary_of_unary (unary_add' (by fun_prop) (const 2))))

private theorem solverFuel_time {P : α → SoS.Solver.Problem} {fuel : α → ℕ}
    (hP : ComputableInPolyTime P enc SoS.Solver.encProblem)
    (hf : ComputableInPolyTime fuel enc encUnary) :
    ComputableInPolyTime (fun x ↦ solverFuel (P x) (fuel x)) enc encUnary := by
  have hd : ComputableInPolyTime (fun x ↦ (P x).degree) enc encNat := by fun_prop
  have he := binary_min_unary' hf (binary_add' hd (const 1))
  exact binary_min_unary' hf (binary_pow'
    (binary_of_unary (unary_add' (problem_bits hP) (const 2))) he)

private theorem solve_time {a : α → RoundArgs} {fuel : α → ℕ} {Q : α → MatrixL}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hn : ComputableInPolyTime (fun x ↦ (a x).1.numVars) enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hQ : ComputableInPolyTime Q enc encMatrix) :
    ComputableInPolyTime (fun x ↦ solve (a x) (fuel x) (Q x))
      enc SoS.Solver.encOutput := by
  have hP := objective_time ha hn hQ
  have hη := accuracy_time ha hP
  exact SoS.PolyTime.core_polytime.comp
    ((hP.prod (hη.prod hη)).prod (solverFuel_time hP hf))

private theorem moments_time {a : α → RoundArgs} {out : α → SoS.Solver.Output}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hn : ComputableInPolyTime (fun x ↦ (a x).1.numVars) enc encUnary)
    (ho : ComputableInPolyTime out enc SoS.Solver.encOutput) :
    ComputableInPolyTime (fun x ↦ moments (a x) (out x)) enc encMatrix := by
  unfold moments
  apply table_polytime (by fun_prop)
  exact SoS.Poly.coeff' (hn.comp (fst _ _)) (ho.comp (fst _ _))
    (pairExponent_time (hn.comp (fst _ _))
      ((fst _ _).comp (snd _ _)) ((snd _ _).comp (snd _ _)))

private theorem points_bits {B : α → Points}
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun x ↦ (encPoints (B x)).length) enc encUnary :=
  length_bits.comp ((of_eq fun _ ↦ rfl).comp hB)

private theorem radiusRank_time : ComputableInPolyTime
    (fun a : RoundArgs ↦ (a.2.2.1, a.2.2.2.1)) encRoundArgs
      (encPair encRat encUnary) := by fun_prop

private def greedyMatrix (a : RoundArgs) (M : MatrixL) (B : Points) : MatrixL :=
  let C := complement a.2.1 B
  table a.2.1 fun i j ↦ (if i = j then greedyThreshold a.2.2.1 a.2.2.2.1 else 0) -
    ent (multiply a.2.1 (multiply a.2.1 C M) C) i j

private theorem greedyMatrix_time {a : α → RoundArgs} {M B : α → MatrixL}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hM : ComputableInPolyTime M enc encMatrix)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun x ↦ greedyMatrix (a x) (M x) (B x)) enc encMatrix := by
  have hd : ComputableInPolyTime (fun x ↦ (a x).2.1) enc encUnary := by fun_prop
  have ht := threshold_polytime.comp (radiusRank_time.comp ha)
  have hC := complement_polytime hd hB
  have hCMC := multiply_polytime hd (multiply_polytime hd hC hM) hC
  unfold greedyMatrix
  apply table_polytime hd
  apply rat_sub'
  · exact ite_prop (by fun_prop) (ht.comp (fst _ _)) (const 0)
  · exact ent' (hCMC.comp (fst _ _))
      ((fst _ _).comp (snd _ _)) ((snd _ _).comp (snd _ _))

private theorem option_guard_eq {β : Type} (o : Option (List ℤ)) (stop : β)
    (next : List ℤ → β) (p q : List ℤ → Prop) [DecidablePred p] [DecidablePred q] :
    (match o with
    | none => stop
    | some y => if p y ∧ q y then next y else stop) =
      if o.isSome then
        if p (o.getD []) then (if q (o.getD []) then next (o.getD []) else stop)
        else stop
      else stop := by
  cases o with
  | none => rfl
  | some y =>
    dsimp only [Option.isSome, Option.getD]
    by_cases hp : p y <;> simp [hp]

private theorem greedyStep_time : ComputableInPolyTime
    (fun p : (RoundArgs × ℕ × MatrixL) × (Bool × Points) ↦
      greedyStep p.1.1 p.1.2.1 p.1.2.2 p.2)
    (encPair (encPair encRoundArgs (encPair encUnary encMatrix)) RoundAux.encState)
    RoundAux.encState := by
  let encP := encPair encRoundArgs (encPair encUnary encMatrix)
  have ha : ComputableInPolyTime (fun p : (RoundArgs × ℕ × MatrixL) × (Bool × Points) ↦
      p.1.1) (encPair encP RoundAux.encState) encRoundArgs := by fun_prop
  have hB := (snd encBool encPoints).comp (snd encP RoundAux.encState)
  have hf := ((fst encUnary encMatrix).comp (snd encRoundArgs _)).comp
    (fst encP RoundAux.encState)
  have hM : ComputableInPolyTime (fun p : (RoundArgs × ℕ × MatrixL) × (Bool × Points) ↦
      p.1.2.2) (encPair encP RoundAux.encState) encMatrix := by fun_prop
  have hA := greedyMatrix_time ha hM hB
  have hy := SoS.PDTestRat.test_polytime.comp hA
  have hv := candidate_polytime ha hB ((optionGetD (encList encIntBin)).comp
    (hy.prod (const [])))
  have hnext := listAppend' hB (cons' hv (const []))
  have hok := acceptable_polytime ha hB hv
  have happend := ite_decide (unary_le' (points_bits hnext) hf)
    ((const (encOut := encBool) false).prod hnext) ((const (encOut := encBool) true).prod hB)
  have hguard := ite' hok happend ((const (encOut := encBool) true).prod hB)
  have htest := ite' (optionIsSome hy) hguard ((const (encOut := encBool) true).prod hB)
  have hr := rankCap_polytime.comp (radiusRank_time.comp ha)
  have hcap := binary_le' hr (binary_of_unary ((length_list encVector).comp hB))
  have h := ite' ((fst encBool encPoints).comp (snd encP RoundAux.encState))
    (snd _ _) (ite_decide hcap ((const (encOut := encBool) true).prod hB) htest)
  convert h using 1
  funext p
  dsimp only [Function.comp_apply, greedyMatrix, decide_eq_true_eq]
  unfold greedyStep
  split
  · rfl
  · split
    · rfl
    · dsimp only
      simp only [decide_eq_true_eq]
      exact option_guard_eq (SoS.PDTestRat.test (greedyMatrix p.1.1 p.1.2.2 p.2.2))
        (true, p.2.2) (fun y ↦ (false, p.2.2 ++ [candidate p.1.1 p.2.2 y]))
        (fun y ↦ acceptable p.1.1 p.2.2 (candidate p.1.1 p.2.2 y))
        (fun y ↦ (encPoints (p.2.2 ++ [candidate p.1.1 p.2.2 y])).length ≤ p.1.2.1)

private theorem greedyStep_size (a : RoundArgs) (fuel : ℕ) (M : MatrixL)
    (s : Bool × Points) (bound : ℕ) (hs : (encPoints s.2).length ≤ bound)
    (hf : fuel ≤ bound) : (encPoints (greedyStep a fuel M s).2).length ≤ bound := by
  unfold greedyStep
  split
  · exact hs
  · split
    · exact hs
    · dsimp only
      split
      · exact hs
      · split
        · rename_i h
          exact h.2.trans hf
        · exact hs

private theorem greedy_iterate_size (a : RoundArgs) (fuel : ℕ) (M : MatrixL)
    (B : Points) (i : ℕ) :
    (encPoints (((greedyStep a fuel M)^[i]) (false, B)).2).length ≤
      (encPoints B).length + fuel :=
  iterate_preserves _ (fun s : Bool × Points ↦ (encPoints s.2).length ≤
    (encPoints B).length + fuel)
    (fun _ hs ↦ greedyStep_size _ _ _ _ _ hs (Nat.le_add_left _ _))
    (false, B) (Nat.le_add_right _ _) i

private theorem state_size (s : Bool × Points) :
    (RoundAux.encState s).length = 2 * (encBool s.1).length + 1 +
      (encPoints s.2).length := length_encPair s

private abbrev GreedyPar := RoundArgs × ℕ × MatrixL
private abbrev encGreedyPar := encPair encRoundArgs (encPair encUnary encMatrix)
private abbrev encGreedyInput := encPair encGreedyPar encPoints

private theorem greedyCap_args : ComputableInPolyTime
    (fun a : RoundArgs ↦ greedyCap a.2.2.1 a.2.2.2.1) encRoundArgs encNat := by
  have h := greedyCap_polytime.comp radiusRank_time
  exact h.of_enc_eq fun _ ↦ rfl

private theorem greedy_count_par : ComputableInPolyTime
    (fun p : GreedyPar ↦ min p.2.1 (greedyCap p.1.2.2.1 p.1.2.2.2.1))
    encGreedyPar encUnary := by
  have hf := (fst encUnary encMatrix).comp (snd encRoundArgs _)
  have hc := greedyCap_args.comp (fst encRoundArgs (encPair encUnary encMatrix))
  exact binary_min_unary' hf hc

private theorem greedy_count_time : ComputableInPolyTime
    (fun p : GreedyPar × Points ↦ min p.1.2.1 (greedyCap p.1.1.2.2.1 p.1.1.2.2.2.1))
    encGreedyInput encUnary :=
  greedy_count_par.comp (fst encGreedyPar encPoints)

private theorem greedy_bound_poly : PolyBounded
    (fun p : GreedyPar × Points ↦ (encGreedyInput p).length)
    (fun p ↦ (encPoints p.2).length + p.1.2.1 + 3) := by
  have hf := ((fst encUnary encMatrix).comp (snd encRoundArgs _)).comp
    (fst encGreedyPar encPoints)
  exact ((points_bits (snd encGreedyPar encPoints)).tidy.polyBounded.add
    hf.tidy.polyBounded).add (.const 3)

private theorem greedy_states (p : GreedyPar × Points) (i : ℕ) :
    (RoundAux.encState (((greedyStep p.1.1 p.1.2.1 p.1.2.2)^[i]) (false, p.2))).length ≤
      (encPoints p.2).length + p.1.2.1 + 3 := by
  have hs := greedy_iterate_size p.1.1 p.1.2.1 p.1.2.2 p.2 i
  rw [state_size]
  have hb (b : Bool) : (encBool b).length = 1 := rfl
  rw [hb]
  simpa only [Nat.mul_one, Nat.reduceAdd, Nat.add_comm] using Nat.add_le_add_right hs 3

private def greedyParStep (p : GreedyPar) (s : Bool × Points) : Bool × Points :=
  greedyStep p.1 p.2.1 p.2.2 s

private def greedyParCount (p : GreedyPar × Points) : ℕ :=
  min p.1.2.1 (greedyCap p.1.1.2.2.1 p.1.1.2.2.2.1)

private theorem greedyParStep_time : ComputableTidilyInPolyTime
    (fun p : GreedyPar × (Bool × Points) ↦ greedyParStep p.1 p.2)
    (encPair encGreedyPar RoundAux.encState) RoundAux.encState := by
  exact greedyStep_time.tidy.of_enc_eq fun _ ↦ rfl

private theorem greedyParCount_time : ComputableTidilyInPolyTime greedyParCount
    encGreedyInput encUnary := by
  exact greedy_count_time.tidy.of_enc_eq fun _ ↦ rfl

private theorem greedy_iter_time : ComputableTidilyInPolyTime
    (fun p : GreedyPar × Points ↦
      (greedyParStep p.1)^[greedyParCount p] (false, p.2))
    encGreedyInput RoundAux.encState := by
  have hi : ComputableTidilyInPolyTime (fun p : GreedyPar × Points ↦ (false, p.2))
      encGreedyInput RoundAux.encState := (const false).tidy.prod (snd _ _).tidy
  exact ComputableTidilyInPolyTime.iterateWith (par := Prod.fst)
    (step := greedyParStep) (fst encGreedyPar encPoints).tidy
    greedyParCount_time hi greedyParStep_time greedy_bound_poly
    (fun p i _ ↦ greedy_states p i)

private theorem greedy_time : ComputableInPolyTime
    (fun p : GreedyPar × Points ↦ greedy p.1.1 p.1.2.1 p.1.2.2 p.2)
    encGreedyInput encPoints := by
  have h := (snd encBool encPoints).comp (.of_tidy greedy_iter_time)
  exact h.of_enc_eq fun _ ↦ rfl

private theorem outerStep_time {a : α → RoundArgs} {fuel : α → ℕ}
    {s : α → Bool × Points}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hn : ComputableInPolyTime (fun x ↦ (a x).1.numVars) enc encUnary)
    (hf : ComputableInPolyTime fuel enc encUnary)
    (hs : ComputableInPolyTime s enc RoundAux.encState) :
    ComputableInPolyTime (fun x ↦ outerStep (a x) (fuel x) (s x)) enc
      RoundAux.encState := by
  have hB := (snd encBool encPoints).comp hs
  have hd := ((fst _ _).comp (snd _ _)).comp ha
  have hQ := roundedProjection_polytime ha hB
  have hM := moments_time ha hn (solve_time ha hn hf hQ)
  have ht := trace_polytime hd hM
  have hstop := rat_lt' (const (1 / 4)) (rat_abs' (rat_sub' ht (const 1)))
  have hγ : ComputableInPolyTime (fun x ↦ (a x).2.2.1) enc encRat := by fun_prop
  have hstop' := rat_le'
    (rat_sub' (const 1) (rat_div' (rat_pow' hγ (const 2)) (const 4)))
    (trace_polytime hd (multiply_polytime hd hQ hM))
  have hgreedy := greedy_time.comp ((ha.prod (hf.prod hM)).prod hB)
  have hsame := unary_eq' ((length_list encVector).comp hgreedy)
    ((length_list encVector).comp hB)
  exact ite' ((fst encBool encPoints).comp hs) hs
    (ite_decide hstop ((const (encOut := encBool) true).prod hB)
      (ite_decide hstop' ((const (encOut := encBool) true).prod hB)
        (ite_decide hsame ((const (encOut := encBool) true).prod hB)
          ((const (encOut := encBool) false).prod hgreedy))))

private def boundedArgs (a : RoundArgs) : RoundArgs :=
  ((min (SoS.Solver.encProblem a.1).length a.1.numVars, a.1.2), a.2)

private theorem boundedArgs_count : ComputableInPolyTime
    (fun a ↦ (boundedArgs a).1.numVars) encRoundArgs encUnary :=
  binary_min_unary' (problem_bits (fst _ _)) (by fun_prop)

private theorem boundedArgs_time : ComputableInPolyTime boundedArgs encRoundArgs
    encRoundArgs := by
  exact ((binary_of_unary boundedArgs_count).prod (by fun_prop)).prod (snd _ _)

private theorem outerStep_size (a : RoundArgs) (fuel : ℕ) (s : Bool × Points)
    (hs : (encPoints s.2).length ≤ fuel) :
    (encPoints (outerStep a fuel s).2).length ≤ fuel := by
  unfold outerStep
  split
  · exact hs
  · dsimp only
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · exact iterate_preserves _
            (fun t : Bool × Points ↦ (encPoints t.2).length ≤ fuel)
            (fun t ht ↦ greedyStep_size _ _ _ t fuel ht le_rfl) (false, s.2) hs _

theorem plan_time : ComputableInPolyTime plan RoundAux.encArgsFuel encPoints := by
  let a : RoundArgs × ℕ → RoundArgs := fun q ↦ boundedArgs q.1
  have ha : ComputableInPolyTime a RoundAux.encArgsFuel encRoundArgs :=
    boundedArgs_time.comp (fst _ _)
  have hf := snd encRoundArgs encUnary
  have hpack := packCount_polytime.comp (radiusRank_time.comp ha)
  have hcount := binary_min_unary' hf (binary_add' hpack (const 1))
  have hstep := outerStep_time (ha.comp (fst _ _))
    (boundedArgs_count.comp ((fst _ _).comp (fst _ _)))
    (hf.comp (fst _ _)) (snd _ _)
  have hbound : PolyBounded (fun q : RoundArgs × ℕ ↦ (RoundAux.encArgsFuel q).length)
      (fun q ↦ q.2 + 3) := hf.tidy.polyBounded.add (.const 3)
  have hit := ComputableTidilyInPolyTime.iterateWith
    (step := fun q s ↦ outerStep (a q) q.2 s) ComputableTidilyInPolyTime.id'
    hcount.tidy ((const (encOut := encBool) false).prod (const [])).tidy hstep.tidy hbound
    (fun q i _ ↦ by
      have hb := iterate_preserves (outerStep (a q) q.2)
        (fun s : Bool × Points ↦ (encPoints s.2).length ≤ q.2)
        (outerStep_size _ _) (false, []) (Nat.zero_le _) i
      rw [state_size]
      have he (b : Bool) : (encBool b).length = 1 := rfl
      rw [he]
      simpa only [Nat.mul_one, Nat.reduceAdd, Nat.add_comm] using
        Nat.add_le_add_right hb 3)
  have hloop := (snd encBool encPoints).comp (.of_tidy hit)
  have hP := (fst SoS.Solver.encProblem _).comp (fst encRoundArgs encUnary)
  have hn : ComputableInPolyTime (fun q : RoundArgs × ℕ ↦ q.1.1.numVars)
      RoundAux.encArgsFuel encNat := by fun_prop
  have hguard := binary_le' hn (binary_of_unary (problem_bits hP))
  convert ite_decide hguard hloop (const []) using 1
  funext q
  unfold plan
  split
  · rename_i h
    have he : a q = q.1 := by
      dsimp [a, boundedArgs]
      rw [min_eq_right h]
    simp only [Function.comp_apply, he, ite_eq_left h]
  · rename_i h
    simp only [Function.comp_apply, ite_eq_right h]

end ABBKS26.Assembly.Exec.RoundCertificates.Compile
