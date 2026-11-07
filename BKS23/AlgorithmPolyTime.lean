module

public import BKS23.Algorithm
public import Background.SumOfSquares.Algorithm.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# The algorithm runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for every function of
`BKS23.Algorithm.run`, ending with `BKS23.Algorithm.run_polytime`: one certificate for every
parameter `t` and budget `L`, both in unary.

Encodings: vertex numbers are unary inside the algorithm, exponents binary (as in the solver),
and the output lists binary vertex numbers (`BKS23.encOutput`).
-/

@[expose] public section

namespace BKS23.Algorithm

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS SoS.Solver SoS.Poly SoS.PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Pairs of vertex numbers, in unary. -/
abbrev encE2 : List (ℕ × ℕ) ↪ List Bool := encList (encPair encUnary encUnary)

/-- Lists of vertex numbers, in unary. -/
abbrev encVs : List ℕ ↪ List Bool := encList encUnary

/-! ### Reading the input -/

theorem numV_polytime : ComputableInPolyTime numV encInput encUnary := by
  have h : numV = fun x : Input ↦ min (x.2.2.length + 1) x.1 := funext fun x ↦ min_comm _ _
  rw [h]
  exact binary_min_unary' (by fun_prop) (by fun_prop)

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

/-! ### The clique program -/

theorem singleN_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ singleN x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encNat)) (encList encNat) := by
  unfold singleN
  exact mapWithInput (by fun_prop)
    (ite_prop (p := fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.2 = q.1.2.1) (by fun_prop) (by fun_prop) (const 0))

@[fun_prop]
theorem singleN' {f g : α → ℕ} {h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encNat) :
    ComputableInPolyTime (fun a ↦ singleN (f a) (g a) (h a)) input (encList encNat) :=
  singleN_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem pairN_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ pairN x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList encNat) := by
  unfold pairN
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ decide (p.2 = p.1.2.1 ∨ p.2 = p.1.2.2))
      (encPair (encPair encUnary (encPair encUnary encUnary)) encUnary) encBool := by
    have h' : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × ℕ ↦
        (decide (p.2 = p.1.2.1) || decide (p.2 = p.1.2.2)))
        (encPair (encPair encUnary (encPair encUnary encUnary)) encUnary) encBool := by
      fun_prop
    have heq : (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ decide (p.2 = p.1.2.1 ∨ p.2 = p.1.2.2)) =
        fun p ↦ (decide (p.2 = p.1.2.1) || decide (p.2 = p.1.2.2)) :=
      funext fun p ↦ Bool.decide_or _ _
    rw [heq]
    exact h'
  exact mapWithInput (by fun_prop) (ite_prop h (const 1) (const 0))

@[fun_prop]
theorem pairN' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ pairN (f a) (g a) (h a)) input (encList encNat) :=
  pairN_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem neg_polytime : ComputableInPolyTime Clique.neg encRaw encRaw := by
  unfold Clique.neg
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem neg' {f : α → RawPoly} (hf : ComputableInPolyTime f input encRaw) :
    ComputableInPolyTime (fun a ↦ Clique.neg (f a)) input encRaw :=
  neg_polytime.comp hf

@[fun_prop]
theorem boolPolyN' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ boolPolyN (f a) (g a)) input encRaw := by
  unfold boolPolyN
  fun_prop

@[fun_prop]
theorem cardPolyN' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ cardPolyN (f a) (g a)) input encRaw := by
  unfold cardPolyN
  have h : ComputableInPolyTime
      (fun a ↦ (List.range (f a)).map fun i ↦ (singleN (f a) i 1, (1 : ℚ))) input encRaw :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem edgePolyN' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ edgePolyN (f a) (g a) (h a)) input encRaw := by
  unfold edgePolyN
  fun_prop

@[fun_prop]
theorem boundPolyN' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ boundPolyN (f a) (g a)) input encRaw := by
  unfold boundPolyN
  have h : ComputableInPolyTime
      (fun a ↦ (List.range (f a)).map fun i ↦ (singleN (f a) i 2, (-1 : ℚ))) input encRaw :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

theorem constraintsN_polytime :
    ComputableInPolyTime (fun x : ℕ × ℕ × List (ℕ × ℕ) ↦ constraintsN x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encNat encE2)) (encList encRaw) := by
  unfold constraintsN
  have h1 : ComputableInPolyTime (fun x : ℕ × ℕ × List (ℕ × ℕ) ↦
      (List.range x.1).flatMap fun i ↦ [boolPolyN x.1 i, Clique.neg (boolPolyN x.1 i)])
      (encPair encUnary (encPair encNat encE2)) (encList encRaw) :=
    flatMapWithInput (by fun_prop) (by fun_prop)
  have h2 : ComputableInPolyTime (fun x : ℕ × ℕ × List (ℕ × ℕ) ↦
      x.2.2.flatMap fun e ↦ [edgePolyN x.1 e.1 e.2, Clique.neg (edgePolyN x.1 e.1 e.2)])
      (encPair encUnary (encPair encNat encE2)) (encList encRaw) :=
    flatMapWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem constraintsN' {f g : α → ℕ} {h : α → List (ℕ × ℕ)}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encNat)
    (hh : ComputableInPolyTime h input encE2) :
    ComputableInPolyTime (fun a ↦ constraintsN (f a) (g a) (h a)) input (encList encRaw) :=
  constraintsN_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

@[fun_prop]
theorem objectiveN' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ objectiveN (f a)) input (encPair encRaw (encList encRaw)) := by
  unfold objectiveN
  have h : ComputableInPolyTime (fun a ↦ (List.range (f a)).map fun i ↦
      ([(singleN (f a) i 1, (1 : ℚ))] : RawPoly)) input (encList encRaw) :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

/-! ### The solver's input -/

theorem solverInput_polytime : ComputableInPolyTime (fun x : Input × ℕ ↦ solverInput x.1 x.2)
    (encPair encInput encUnary) SoS.Solver.encInput := by
  have hn : ComputableInPolyTime (fun x : Input × ℕ ↦ numV x.1) (encPair encInput encUnary)
      encUnary := numV_polytime.comp (fst _ _)
  have hk : ComputableInPolyTime (fun x : Input × ℕ ↦ x.1.2.1) (encPair encInput encUnary)
      encNat := by fun_prop
  have hb : ComputableInPolyTime (fun x : Input × ℕ ↦ x.1.2.2) (encPair encInput encUnary)
      encBits := by fun_prop
  have he : ComputableInPolyTime (fun x : Input × ℕ ↦ accExp (numV x.1) x.2)
      (encPair encInput encUnary) encUnary := by
    unfold accExp
    fun_prop
  have hP : ComputableInPolyTime (fun x : Input × ℕ ↦
      problemN (numV x.1) x.1.2.1 (deg x.2) (nonEdges (numV x.1) x.1.2.2))
      (encPair encInput encUnary) encProblem := by
    unfold problemN deg
    have hnB : ComputableInPolyTime (fun x : Input × ℕ ↦ numV x.1) (encPair encInput encUnary)
        encNat := toBinary' hn
    have hdB : ComputableInPolyTime (fun x : Input × ℕ ↦ 8 * x.2 + 6) (encPair encInput encUnary)
        encNat := toBinary' (by fun_prop)
    exact hnB.prod (hdB.prod ((constraintsN' hn hk (nonEdges' hn hb)).prod (objectiveN' hn)))
  unfold solverInput accη accγ
  fun_prop

/-! ### The solver -/

theorem core_run_polytime : ComputableInPolyTime
    (fun p : (Input × ℕ) × ℕ ↦ SoS.Core.core (solverInput p.1.1 p.1.2, p.2))
    (encPair (encPair encInput encUnary) encUnary) encRaw :=
  core_polytime.comp (g := fun p : (Input × ℕ) × ℕ ↦ (solverInput p.1.1 p.1.2, p.2))
    ((solverInput_polytime.comp (fst _ _)).prod (snd _ _))

/-! ### Tuples -/

theorem tupleStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List (List ℕ) ↦ tupleStep p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encUnary) (encList encVs)) (encList encVs) := by
  unfold tupleStep
  have h : ComputableInPolyTime (fun p : (ℕ × ℕ) × List (List ℕ) ↦
      p.2.flatMap fun q ↦ (List.range p.1.2).map (· :: q))
      (encPair (encPair encUnary encUnary) (encList encVs)) (encList encVs) :=
    flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))
  fun_prop

/-- The states of the tuple loop: at most `L + 1` tuples, of at most `i` vertices below `n`. -/
theorem tuples_iter_small (L n i : ℕ) :
    (∀ q ∈ (tupleStep L n)^[i] [[]], q.length ≤ i ∧ ∀ a ∈ q, a < n) ∧
      ((tupleStep L n)^[i] [[]]).length ≤ L + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · have hq' := List.mem_of_mem_take hq
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq'
      obtain ⟨q', hq', a, ha, rfl⟩ := hq'
      obtain ⟨h1, h2⟩ := ih.1 q' hq'
      refine ⟨by simp; omega, fun b hb ↦ ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ha
      · exact h2 b hb
    · rw [tupleStep, List.length_take]
      omega

theorem tuples_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ tuples x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList encVs) := by
  unfold tuples
  refine iterateWith (par := fun x : ℕ × ℕ × ℕ ↦ (x.1, x.2.1)) (count := fun x ↦ x.2.2)
    (init := fun _ ↦ [[]]) (step := fun p l ↦ tupleStep p.1 p.2 l) (by fun_prop) (by fun_prop)
    (by fun_prop) tupleStep_polytime
    (bound := fun x ↦ (x.1 + 1) * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1)) ?_ ?_
  · refine PolyBounded.of_forall_le 7 3 fun x ↦ ?_
    set s := (encPair encUnary (encPair encUnary encUnary) x).length
    have hs : x.1 + x.2.1 + x.2.2 ≤ s := by
      simp only [s, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have h1 : x.1 + 1 ≤ s + 1 := by omega
    have h2 : x.2.2 ≤ s + 1 := by omega
    have h3 : 2 * x.2.1 + 1 ≤ 2 * (s + 1) := by omega
    calc (x.1 + 1) * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1)
        ≤ (s + 1) * (2 * ((s + 1) * (2 * (s + 1))) + 1 * (s + 1) * (s + 1)) := by
          gcongr
          nlinarith
      _ = 5 * (s + 1) ^ 3 := by ring
      _ ≤ 7 * (s + 1) ^ 3 := by gcongr; norm_num
  · intro x i hi
    obtain ⟨hsmall, hlen⟩ := tuples_iter_small x.1 x.2.1 i
    have helem : ∀ q ∈ (tupleStep x.1 x.2.1)^[i] [[]], (encVs q).length ≤
        x.2.2 * (2 * x.2.1 + 1) := by
      intro q hq
      obtain ⟨h1, h2⟩ := hsmall q hq
      refine (length_encList_le encUnary q (b := x.2.1) fun a ha ↦ ?_).trans
        (Nat.mul_le_mul_right _ (h1.trans hi))
      simpa [encUnary_apply] using (h2 a ha).le
    calc (encList encVs ((tupleStep x.1 x.2.1)^[i] [[]])).length
        ≤ ((tupleStep x.1 x.2.1)^[i] [[]]).length * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1) :=
          length_encList_le _ _ helem
      _ ≤ (x.1 + 1) * (2 * (x.2.2 * (2 * x.2.1 + 1)) + 1) := Nat.mul_le_mul_right _ hlen

@[fun_prop]
theorem tuples' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ tuples (f a) (g a) (h a)) input (encList encVs) :=
  tuples_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

/-! ### The rounding -/

theorem countVec_polytime : ComputableInPolyTime (fun x : ℕ × List ℕ ↦ countVec x.1 x.2)
    (encPair encUnary encVs) (encList encNat) := by
  unfold countVec
  have h : ComputableInPolyTime (fun p : (ℕ × List ℕ) × ℕ ↦ p.1.2.countP fun a ↦ a == p.2)
      (encPair (encPair encUnary encVs) encUnary) encUnary :=
    countPWithInput (by fun_prop) (unary_beq' (by fun_prop) (by fun_prop))
  exact mapWithInput (by fun_prop) (toBinary' h)

@[fun_prop]
theorem countVec' {f : α → ℕ} {g : α → List ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encVs) :
    ComputableInPolyTime (fun a ↦ countVec (f a) (g a)) input (encList encNat) :=
  countVec_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

theorem roundSet_polytime : ComputableInPolyTime
    (fun x : ℕ × RawPoly × List ℕ ↦ roundSet x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encRaw encVs)) encVs := by
  unfold roundSet
  exact filterWithInput (by fun_prop) (rat_le' (by fun_prop) (by fun_prop))

@[fun_prop]
theorem roundSet' {f : α → ℕ} {g : α → RawPoly} {h : α → List ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encRaw)
    (hh : ComputableInPolyTime h input encVs) :
    ComputableInPolyTime (fun a ↦ roundSet (f a) (g a) (h a)) input encVs :=
  roundSet_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

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

theorem pruneStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × List (List ℕ)) × List ℕ ↦ pruneStep p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary (encList encVs)) encVs) (encList encVs) := by
  unfold pruneStep
  exact ite' (allWithInput (by fun_prop) (unary_lt' (by fun_prop) (by fun_prop))) (by fun_prop)
    (by fun_prop)

theorem length_encList_append_singleton {β : Type} (e : β ↪ List Bool) (l : List β) (a : β) :
    (encList e (l ++ [a])).length = (encList e l).length + (2 * (e a).length + 1) := by
  rw [length_encList, length_encList, List.map_append, List.sum_append]
  simp

theorem cleanupL_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦ cleanupL x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encNat (encPair encUnary (encPair encE2 (encList encVs)))) (encList encVs) := by
  have h := funext fun x : ℕ × ℕ × List (ℕ × ℕ) × List (List ℕ) ↦
    cleanupL_eq x.1 x.2.1 x.2.2.1 x.2.2.2
  rw [h]
  set enc := encPair encNat (encPair encUnary (encPair encE2 (encList encVs)))
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
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encUnary)
    (hh : ComputableInPolyTime h input encE2) (hl : ComputableInPolyTime l input (encList encVs)) :
    ComputableInPolyTime (fun a ↦ cleanupL (f a) (g a) (h a) (l a)) input (encList encVs) :=
  cleanupL_polytime.comp (g := fun a ↦ (f a, g a, h a, l a)) (hf.prod (hg.prod (hh.prod hl)))

theorem rootCeil_polytime : ComputableInPolyTime (fun x : ℕ × ℕ ↦ rootCeil x.1 x.2)
    (encPair encUnary encUnary) encUnary := by
  unfold rootCeil
  have h : ComputableInPolyTime (fun x : ℕ × ℕ ↦
      (List.range (x.1 + 1)).filter fun d ↦ decide (d ^ x.2 < x.1))
      (encPair encUnary encUnary) encVs :=
    filterWithInput (by fun_prop)
      (binary_lt' (binary_pow' (toBinary' (by fun_prop)) (by fun_prop)) (toBinary' (by fun_prop)))
  fun_prop

@[fun_prop]
theorem rootCeil' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ rootCeil (f a) (g a)) input encUnary :=
  rootCeil_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-! ### The algorithm -/

theorem toBinaryLists : ComputableInPolyTime (fun l : List (List ℕ) ↦ l) (encList encVs)
    (encList (encList encNat)) := by
  have h : ComputableInPolyTime (fun l : List (List ℕ) ↦ l.map fun q ↦ q.map fun i ↦ i)
      (encList encVs) (encList (encList encNat)) :=
    mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (toBinary' (by fun_prop)))
  simpa only [List.map_id'] using h

/-- **The algorithm runs in polynomial time** in the input, the parameter `t` and the budget `L`,
both in unary. -/
theorem run_polytime : ComputableInPolyTime run (encPair (encPair encInput encUnary) encUnary)
    encOutput := by
  set enc := encPair (encPair encInput encUnary) encUnary
  have hn : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ numV p.1.1) enc encUnary :=
    numV_polytime.comp (g := fun p : (Input × ℕ) × ℕ ↦ p.1.1) (by fun_prop)
  have hb : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ p.1.1.2.2) enc encBits := by fun_prop
  have hk : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦ p.1.1.2.1) enc encNat := by fun_prop
  have hout := core_run_polytime
  have hC : ComputableInPolyTime (fun p : (Input × ℕ) × ℕ ↦
      (tuples p.2 (numV p.1.1) (4 * p.1.2)).map
        (roundSet (numV p.1.1) (SoS.Core.core (solverInput p.1.1 p.1.2, p.2))))
      enc (encList encVs) :=
    mapWithInput (by fun_prop) (roundSet' (hn.comp (fst _ _)) (hout.comp (fst _ _)) (snd _ _))
  exact toBinaryLists.comp (cleanupL' hk (rootCeil' hn (by fun_prop)) (nonEdges' hn hb) hC)

/-! ### Padding -/

theorem problem_polytime : ComputableInPolyTime (fun x : Input × ℕ ↦ (solverInput x.1 x.2).1)
    (encPair encInput encUnary) encProblem :=
  (fst _ _).comp solverInput_polytime

theorem length_encPair_input_unary (x : Input) (t : ℕ) :
    (encPair encInput encUnary (x, t)).length = 2 * (encInput x).length + 1 + t := by
  rw [length_encPair, encUnary_apply, List.length_replicate]

/-- The arithmetic of the padding: every term of the pipeline's bound is at most a constant times
`(N + 2)^(8 (e + 1) G (t + 1))`, or linear in the length `R` of the input with the coins. -/
theorem pad_arith {c cP K dP D dr eP t G N R Pl T : ℕ} (hG : G = max dP (max D dr))
    (hR : 2 * N + 1 ≤ R) (hPl : Pl ≤ cP * (2 * N + 1 + t + 1) ^ eP)
    (hT : T ≤ R + R + (R + R + (2 * N + 1 + t + 1) ^ dP + K * ((Pl + 2) ^ (8 * t + 6 + 2)) ^ D) +
      (2 * (2 * N + 1 + t) + 1 + (Pl + 2) ^ (8 * t + 6 + 1) + 1) ^ dr) :
    c * (T + 1) ≤ c * (5 + (1 + K + 3 ^ dr) * (cP * (2 * t + 2) ^ eP + 2 * t + 8) ^
      ((8 * t + 8) * G)) * ((N + 2) ^ (8 * (eP + 1) * G * (t + 1)) + R) := by
  rw [show 8 * t + 6 + 2 = 8 * t + 8 by ring, show 8 * t + 6 + 1 = 8 * t + 7 by ring] at hT
  set A := cP * (2 * t + 2) ^ eP + 2 * t + 8 with hA
  set W := A * (N + 2) ^ (eP + 1) with hW
  have hN1 : 1 ≤ (N + 2) ^ (eP + 1) := Nat.one_le_pow _ _ (by omega)
  have hW1 : 1 ≤ W := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hNW : (2 * t + 8) * (N + 2) ≤ W :=
    Nat.mul_le_mul (by omega) (Nat.le_self_pow (by omega) _)
  have hlin : 2 * N + 1 + t + 1 ≤ (2 * t + 2) * (N + 2) := by nlinarith
  have hPlen : Pl + 2 ≤ W := by
    have h' : (2 * N + 1 + t + 1) ^ eP ≤ (2 * t + 2) ^ eP * (N + 2) ^ (eP + 1) :=
      calc (2 * N + 1 + t + 1) ^ eP ≤ ((2 * t + 2) * (N + 2)) ^ eP := Nat.pow_le_pow_left hlin _
        _ = (2 * t + 2) ^ eP * (N + 2) ^ eP := mul_pow _ _ _
        _ ≤ (2 * t + 2) ^ eP * (N + 2) ^ (eP + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : Pl ≤ cP * (2 * t + 2) ^ eP * (N + 2) ^ (eP + 1) := by
      calc Pl ≤ cP * (2 * N + 1 + t + 1) ^ eP := hPl
        _ ≤ cP * ((2 * t + 2) ^ eP * (N + 2) ^ (eP + 1)) := Nat.mul_le_mul_left _ h'
        _ = _ := by ring
    have h3 : 2 ≤ 2 * (N + 2) ^ (eP + 1) := by omega
    calc Pl + 2 ≤ cP * (2 * t + 2) ^ eP * (N + 2) ^ (eP + 1) + 2 * (N + 2) ^ (eP + 1) := by
          omega
      _ ≤ (cP * (2 * t + 2) ^ eP + 2) * (N + 2) ^ (eP + 1) := by ring_nf; omega
      _ ≤ W := Nat.mul_le_mul_right _ (by omega)
  have hW8 : W ≤ W ^ (8 * t + 8) := Nat.le_self_pow (by omega) _
  have hpad : (Pl + 2) ^ (8 * t + 8) ≤ W ^ (8 * t + 8) := Nat.pow_le_pow_left hPlen _
  have hL : (Pl + 2) ^ (8 * t + 7) ≤ W ^ (8 * t + 8) :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hpad
  set M := W ^ ((8 * t + 8) * G) with hM
  have hpowM : ∀ X d, X ≤ W ^ (8 * t + 8) → d ≤ G → X ^ d ≤ M := fun X d hX hd ↦
    calc X ^ d ≤ (W ^ (8 * t + 8)) ^ d := Nat.pow_le_pow_left hX d
      _ = W ^ ((8 * t + 8) * d) := (pow_mul _ _ _).symm
      _ ≤ M := Nat.pow_le_pow_right hW1 (Nat.mul_le_mul_left _ hd)
  have hdP : dP ≤ G := hG ▸ le_max_left _ _
  have hD : D ≤ G := hG ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hdr : dr ≤ G := hG ▸ (le_max_right _ _).trans (le_max_right _ _)
  have t1 : (2 * N + 1 + t + 1) ^ dP ≤ M := hpowM _ _ (by nlinarith) hdP
  have t2 : ((Pl + 2) ^ (8 * t + 8)) ^ D ≤ M := hpowM _ _ hpad hD
  have t3 : 2 * (2 * N + 1 + t) + 1 + (Pl + 2) ^ (8 * t + 7) + 1 ≤ 3 * W ^ (8 * t + 8) := by
    nlinarith
  have t3' : (2 * (2 * N + 1 + t) + 1 + (Pl + 2) ^ (8 * t + 7) + 1) ^ dr ≤ 3 ^ dr * M :=
    calc _ ≤ (3 * W ^ (8 * t + 8)) ^ dr := Nat.pow_le_pow_left t3 _
      _ = 3 ^ dr * (W ^ (8 * t + 8)) ^ dr := mul_pow _ _ _
      _ ≤ 3 ^ dr * M := Nat.mul_le_mul_left _ (hpowM _ _ le_rfl hdr)
  have hMeq : M = A ^ ((8 * t + 8) * G) * (N + 2) ^ (8 * (eP + 1) * G * (t + 1)) := by
    rw [hM, hW, mul_pow, ← pow_mul]
    congr 2
    ring
  set Y := (N + 2) ^ (8 * (eP + 1) * G * (t + 1))
  set Z := A ^ ((8 * t + 8) * G)
  have hsum : T + 1 ≤ 5 * R + (1 + K + 3 ^ dr) * M := by
    have h2 := Nat.mul_le_mul_left K t2
    have e : (1 + K + 3 ^ dr) * M = M + K * M + 3 ^ dr * M := by ring
    rw [e]
    linarith
  have hfin : 5 * R + (1 + K + 3 ^ dr) * M ≤ (5 + (1 + K + 3 ^ dr) * Z) * (Y + R) := by
    rw [hMeq]
    have e : (5 + (1 + K + 3 ^ dr) * Z) * (Y + R) =
        5 * R + (1 + K + 3 ^ dr) * (Z * Y) + (5 * Y + (1 + K + 3 ^ dr) * Z * R) := by ring
    rw [e]
    exact Nat.le_add_right _ _
  calc c * (T + 1) ≤ c * (5 * R + (1 + K + 3 ^ dr) * M) := Nat.mul_le_mul_left _ hsum
    _ ≤ c * ((5 + (1 + K + 3 ^ dr) * Z) * (Y + R)) := Nat.mul_le_mul_left _ hfin
    _ = _ := by ring

/-- **The algorithm with parameter `t` runs in time `n^O(t)`**: within
`c_t ((|x| + 2)^(E (t + 1)) + |(x, r)|)` steps and cells, for one exponent `E` and every `t`. The
coins are read but not used. -/
theorem exists_alg_inO : ∃ E : ℕ, ∀ t : ℕ, ∃ c : ℕ,
    ComputableInTimeAndSpace (alg t) (encPair encInput encBits) encOutput
      (fun xr ↦ c * (((encInput xr.1).length + 2) ^ (E * (t + 1)) +
        (encPair encInput encBits xr).length))
      (fun xr ↦ c * (((encInput xr.1).length + 2) ^ (E * (t + 1)) +
        (encPair encInput encBits xr).length)) := by
  obtain ⟨dP, eP, hP⟩ := problem_polytime.tidy.exists_degree
  obtain ⟨cP, hcP⟩ := hP.2
  obtain ⟨K, D, hbud⟩ := exists_budget_inO
  obtain ⟨dr, er, hr⟩ := run_polytime.tidy.exists_degree
  set G := max dP (max D dr) with hG
  refine ⟨8 * (eP + 1) * G, fun t ↦ ?_⟩
  set encXR := encPair encInput encBits
  -- The pipeline: `(x, t)`, the problem, the budget, and the algorithm.
  have h1 : ComputableTidilyInO (fun xr : Input × List Bool ↦ (xr.1, t)) encXR
      (encPair encInput encUnary) (fun xr ↦ (encXR xr).length + (encXR xr).length)
      (fun xr ↦ (encXR xr).length + (encXR xr).length) :=
    (ComputableTidilyInO.fst encInput encBits).prod (ComputableTidilyInO.const t)
  have h2 := hP.inO.comp h1
  have h3 := hbud.comp h2
  have h4 := h1.prod h3
  have h5 := hr.inO.comp h4
  obtain ⟨c, hc, -⟩ := h5.computableInO
  -- The algorithm is this pipeline.
  replace hc : ComputableInTimeAndSpace (alg t) encXR encOutput _ _ := hc
  -- The bounds.
  refine ⟨c * (5 + (1 + K + 3 ^ dr) * (cP * (2 * t + 2) ^ eP + 2 * t + 8) ^ ((8 * t + 8) * G)),
    hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩
  all_goals
    have hR : 2 * (encInput xr.1).length + 1 ≤ (encXR xr).length := by
      simp only [encXR, length_encPair]
      omega
    have hPl := hcP (xr.1, t)
    simp only [length_encPair_input_unary] at hPl
    have hdeg : (solverInput xr.1 t).1.degree = 8 * t + 6 := rfl
    refine pad_arith hG hR hPl (le_of_eq ?_)
    simp only [Function.comp_apply, padMeasure, hdeg, length_encPair, encUnary_apply,
      List.length_replicate]

end BKS23.Algorithm
