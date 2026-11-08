module

public import BMW26.Alg.Algorithm
public import Background.SumOfSquares.Algorithm.PolyTime
public import Background.PolyTime.Rat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-!
# The algorithm runs in polynomial time

`BMW26.Alg.alg_runsInTime`: for every `c`, the algorithm runs in time `O((N + 2)^k)` on inputs of
encoded length `N`, for some `k`. As in [BKS23] in this repository:

* Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`, complexitylib's `fun_prop` calculus)
  for every function of `BMW26.Alg.runAlg`, ending with `BMW26.Alg.PT.runAlg_polytime`: polynomial
  time in the input `(n, adj)` and the budget, in unary. Vertex numbers are unary (the vertex count
  `BMW26.Alg.numV` is at most the length of the adjacency table), exponents binary (as in the
  solver), bit vectors lists of bits.
* **The budget.** The program has the fixed degree `4`, so the budget
  `SoS.Solver.budget = (|P| + 2)^5` is polynomial in the input, and it is computed in unary
  (`BMW26.Alg.PT.budget_polytime`); no padding is needed. So `(n, adj) ↦ runAlg c ((n, adj), L)`
  with that budget runs in polynomial time (`BMW26.Alg.PT.runBudget_polytime`).
* **The input.** The encoded graph is the encoding of `(n, adjTable G)`, the first frame of the
  input with the coins: reading it takes linear time, so the algorithm runs within
  `O((N + 1)^k + |(x, r)|)` steps and cells.
-/

@[expose] public section

namespace BMW26.Alg.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS SoS.Poly SoS.PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- The input `(n, adj)`, as in `BMW26.encGraph`. -/
abbrev encX : ℕ × List Bool ↪ List Bool := encPair encNat encBits

/-- The input with the budget, in unary. -/
abbrev encY : (ℕ × List Bool) × ℕ ↪ List Bool := encPair encX encUnary

/-- Edge lists, with vertex numbers in unary. -/
abbrev encE2 : List (ℕ × ℕ) ↪ List Bool := encList (encPair encUnary encUnary)

/-! ### Reading the input -/

theorem numV_polytime : ComputableInPolyTime (fun x : ℕ × List Bool ↦ numV x.1 x.2) encX
    encUnary := by
  have h : (fun x : ℕ × List Bool ↦ numV x.1 x.2) = fun x ↦ min x.2.length x.1 :=
    funext fun x ↦ min_comm _ _
  rw [h]
  exact binary_min_unary' (by fun_prop) (by fun_prop)

@[fun_prop]
theorem dimOf' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ dimOf (f a)) input encUnary :=
  binary_log_two.comp (toBinary' hf)

theorem edgeList_polytime : ComputableInPolyTime (fun x : ℕ × List Bool ↦ edgeList x.1 x.2)
    (encPair encUnary encBits) encE2 := by
  unfold edgeList
  exact flatMapWithInput (by fun_prop)
    (mapWithInput (filterWithInput (by fun_prop) (bool_and' (by fun_prop) (by fun_prop)))
      (by fun_prop))

@[fun_prop]
theorem edgeList' {f : α → ℕ} {g : α → List Bool} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encBits) :
    ComputableInPolyTime (fun a ↦ edgeList (f a) (g a)) input encE2 :=
  edgeList_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-! ### The program -/

/-- The sum of two binary numbers. -/
theorem binAdd' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  binary_add.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

theorem expo1_polytime : ComputableInPolyTime (fun x : ℕ × ℕ ↦ expo1 x.1 x.2)
    (encPair encUnary encUnary) encE := by
  unfold expo1
  exact mapWithInput (by fun_prop)
    (ite_prop (p := fun q : (ℕ × ℕ) × ℕ ↦ q.2 = q.1.2) (by fun_prop) (const 1) (const 0))

@[fun_prop]
theorem expo1' {f g : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ expo1 (f a) (g a)) input encE :=
  expo1_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

theorem expo2_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ expo2 x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encE := by
  unfold expo2
  exact mapWithInput (by fun_prop) (binAdd'
    (ite_prop (p := fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.2 = q.1.2.1) (by fun_prop) (const 1) (const 0))
    (ite_prop (p := fun q : (ℕ × ℕ × ℕ) × ℕ ↦ q.2 = q.1.2.2) (by fun_prop) (const 1) (const 0)))

@[fun_prop]
theorem expo2' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ expo2 (f a) (g a) (h a)) input encE :=
  expo2_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

/-- A unary number, as a rational. -/
theorem rat_ofUnary {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ (f a : ℚ)) input encRat :=
  rat_natCast' (toBinary' hf)

/-- A fixed power of a rational. -/
theorem rat_pow_const (k : ℕ) {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ f a ^ k) input encRat := by
  induction k with
  | zero => simpa only [pow_zero] using (const 1 : ComputableInPolyTime (fun _ : α ↦ (1 : ℚ))
      input encRat)
  | succ k ih => simpa only [pow_succ] using rat_mul' ih hf

theorem boundC_polytime : ComputableInPolyTime boundC encUnary encRaw := by
  unfold boundC
  exact cons' ((const []).prod (rat_ofUnary id')) (mapWithInput (by fun_prop) (by fun_prop))

theorem boolC_polytime : ComputableInPolyTime (fun x : ℕ × ℕ ↦ boolC x.1 x.2)
    (encPair encUnary encUnary) (encList encRaw) := by
  unfold boolC
  fun_prop

theorem balC_polytime : ComputableInPolyTime balC encUnary (encList encRaw) := by
  unfold balC
  exact cons' (mapWithInput (by fun_prop) (by fun_prop))
    (cons' (mapWithInput (by fun_prop) (by fun_prop)) (const []))

theorem cutC_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ cutC x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encRat encE2))) encRaw := by
  unfold cutC
  have hd : ComputableInPolyTime (fun p : (ℕ × ℕ × ℚ × List (ℕ × ℕ)) × (ℕ × ℕ) ↦
      (p.1.2.1 : ℚ)) (encPair (encPair encUnary (encPair encUnary (encPair encRat encE2)))
      (encPair encUnary encUnary)) encRat := rat_ofUnary (by fun_prop)
  have hl : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ (x.2.2.2.length : ℚ))
      (encPair encUnary (encPair encUnary (encPair encRat encE2))) encRat :=
    rat_ofUnary (by fun_prop)
  exact cons' ((const []).prod (rat_mul' (rat_mul' (rat_add' (const 2) (by fun_prop)) (const 2))
    hl)) (flatMapWithInput (by fun_prop)
      (cons' (ComputableInPolyTime.prod (by fun_prop) (rat_neg' hd))
      (cons' (ComputableInPolyTime.prod (by fun_prop) (rat_neg' hd))
        (cons' (ComputableInPolyTime.prod (by fun_prop) (rat_mul' (const 2) hd)) (const [])))))

theorem objective_polytime : ComputableInPolyTime objective encUnary
    (encPair encRaw (encList encRaw)) := by
  unfold objective
  exact (const []).prod (flatMapWithInput (by fun_prop)
    (mapWithInput (by fun_prop) (cons' (ComputableInPolyTime.prod (by fun_prop) (const 1))
      (const []))))

theorem problemOf_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ problemOf x.1 x.2.1 x.2.2.1 x.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encRat encE2))) encProblemM := by
  unfold problemOf
  set enc := encPair encUnary (encPair encUnary (encPair encRat encE2))
  have hn : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ x.1) enc encUnary :=
    fst _ _
  have hb : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ boundC x.1) enc encRaw :=
    boundC_polytime.comp hn
  have hbo : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦
      (List.range x.1).flatMap (boolC x.1)) enc (encList encRaw) :=
    flatMapWithInput (by fun_prop) (boolC_polytime.comp (g := fun p : (ℕ × ℕ × ℚ × List (ℕ × ℕ))
      × ℕ ↦ (p.1.1, p.2)) (by fun_prop))
  have hba : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ balC x.1) enc
      (encList encRaw) := balC_polytime.comp hn
  have hc : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦
      cutC x.1 x.2.1 x.2.2.1 x.2.2.2) enc encRaw := cutC_polytime
  have ho : ComputableInPolyTime (fun x : ℕ × ℕ × ℚ × List (ℕ × ℕ) ↦ objective x.1) enc
      (encPair encRaw (encList encRaw)) := objective_polytime.comp hn
  exact (toBinary' hn).prod ((const 4).prod ((cons' hb (listAppend' (listAppend' hbo hba)
    (cons' hc (const [])))).prod ho))

@[fun_prop]
theorem problemOf' {f g : α → ℕ} {h : α → ℚ} {k : α → List (ℕ × ℕ)}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encUnary)
    (hh : ComputableInPolyTime h input encRat) (hk : ComputableInPolyTime k input encE2) :
    ComputableInPolyTime (fun a ↦ problemOf (f a) (g a) (h a) (k a)) input encProblemM :=
  problemOf_polytime.comp (g := fun a ↦ (f a, g a, h a, k a)) (hf.prod (hg.prod (hh.prod hk)))

@[fun_prop]
theorem slack' (c : ℕ) {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ slack c (f a)) input encRat := by
  unfold slack
  exact rat_div' (const 1) (rat_pow_const _ (rat_ofUnary hf))

@[fun_prop]
theorem acc' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ acc (f a)) input encRat := by
  unfold acc
  exact rat_div' (const 1) (rat_two_pow' (unary_add' ((unary_pow 2).comp hf) (const 10)))

/-! ### The solver's input and the budget -/

theorem solverInputOf_polytime (c : ℕ) : ComputableInPolyTime (solverInputOf c) encX
    encInputM := by
  unfold solverInputOf
  have hn := numV_polytime
  have hb : ComputableInPolyTime (fun x : ℕ × List Bool ↦ x.2) encX encBits := snd _ _
  exact (problemOf' hn (dimOf' hn) (slack' c (dimOf' hn)) (edgeList' hn hb)).prod
    ((acc' hn).prod (acc' hn))

theorem problem_polytime (c : ℕ) : ComputableInPolyTime (fun x ↦ (solverInputOf c x).1) encX
    encProblemM :=
  (fst _ _).comp (solverInputOf_polytime c)

theorem degree_solverInputOf (c : ℕ) (x : ℕ × List Bool) :
    (solverInputOf c x).1.degree = 4 := rfl

/-- **The budget**, in unary: `(|P| + 2)^5`, polynomial in the input since the degree is `4`. -/
theorem budget_polytime (c : ℕ) : ComputableInPolyTime
    (fun x ↦ Solver.budget (solverInputOf c x)) encX encUnary := by
  have h : ComputableInPolyTime (fun x ↦ ((encProblemM (solverInputOf c x).1).length + 2) ^ 5)
      encX encUnary :=
    (unary_pow 5).comp (unary_add' ((encoding_length encProblemM).comp (problem_polytime c))
      (const 2))
  exact h

/-! ### The solver and the moment table -/

theorem core_run_polytime (c : ℕ) : ComputableInPolyTime
    (fun y : (ℕ × List Bool) × ℕ ↦ SoS.Core.core (solverInputOf c y.1, y.2)) encY encRaw :=
  core_polytime'.comp (g := fun y : (ℕ × List Bool) × ℕ ↦ (solverInputOf c y.1, y.2))
    (((solverInputOf_polytime c).comp (fst _ _)).prod (snd _ _))

theorem coeffAt_polytime : ComputableInPolyTime
    (fun x : ℕ × Solver.RawPoly × List ℕ ↦ coeffAt x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encRaw encE)) encRat := by
  unfold coeffAt
  exact rat_sum' (mapWithInput (filterWithInput (by fun_prop)
    (allWithInput (by fun_prop) (beq (listGetDWithInput (by fun_prop) (by fun_prop) 0)
      (listGetDWithInput (by fun_prop) (by fun_prop) 0)))) (by fun_prop))

@[fun_prop]
theorem coeffAt' {f : α → ℕ} {g : α → Solver.RawPoly} {h : α → List ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encRaw)
    (hh : ComputableInPolyTime h input encE) :
    ComputableInPolyTime (fun a ↦ coeffAt (f a) (g a) (h a)) input encRat :=
  coeffAt_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem momentTable_polytime : ComputableInPolyTime
    (fun x : ℕ × Solver.RawPoly ↦ momentTable x.1 x.2) (encPair encUnary encRaw)
    (encList encPt) := by
  unfold momentTable
  exact mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

@[fun_prop]
theorem momentTable' {f : α → ℕ} {g : α → Solver.RawPoly}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encRaw) :
    ComputableInPolyTime (fun a ↦ momentTable (f a) (g a)) input (encList encPt) :=
  momentTable_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-! ### The rounding -/

/-- Bit vectors, as lists of bits. -/
abbrev encVec : List Bool ↪ List Bool := encList encBool

theorem hamm_eq (a b : List Bool) : Round.hamm a b = (a.zip b).countP fun p ↦ p.1 != p.2 := by
  rw [Round.hamm, List.count_eq_countP, ← List.map_uncurry_zip_eq_zipWith, List.countP_map]
  rfl

theorem hamm_polytime : ComputableInPolyTime (fun x : List Bool × List Bool ↦ Round.hamm x.1 x.2)
    (encPair encVec encVec) encUnary := by
  have h : ComputableInPolyTime (fun x : List Bool × List Bool ↦
      (x.1.zip x.2).countP fun p ↦ p.1 != p.2) (encPair encVec encVec) encUnary :=
    countPWithInput (zip _ _) (bool_not.comp (beq (by fun_prop) (by fun_prop)))
  simpa only [hamm_eq] using h

@[fun_prop]
theorem hamm' {f g : α → List Bool} (hf : ComputableInPolyTime f input encVec)
    (hg : ComputableInPolyTime g input encVec) :
    ComputableInPolyTime (fun a ↦ Round.hamm (f a) (g a)) input encUnary :=
  hamm_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

@[fun_prop]
theorem hammPM' {f : α → ℕ} {g h : α → List Bool} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encVec) (hh : ComputableInPolyTime h input encVec) :
    ComputableInPolyTime (fun a ↦ Round.hammPM (f a) (g a) (h a)) input encUnary := by
  unfold Round.hammPM
  exact binary_min_unary' (hamm' hg hh) (toBinary' (unary_sub' hf (hamm' hg hh)))

@[fun_prop]
theorem entry' {M : α → List (List ℚ)} {u v : α → ℕ}
    (hM : ComputableInPolyTime M input (encList encPt)) (hu : ComputableInPolyTime u input encUnary)
    (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a ↦ Round.entry (M a) (u a) (v a)) input encRat := by
  unfold Round.entry
  exact listGetDWithInput (listGetDWithInput hM hu []) hv 0

theorem edgeVec_polytime : ComputableInPolyTime
    (fun x : ℕ × List (List ℚ) × (ℕ × ℕ) ↦ Round.edgeVec x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair (encList encPt) (encPair encUnary encUnary))) encVec := by
  unfold Round.edgeVec
  exact mapWithInput (by fun_prop) (rat_lt' (by fun_prop) (by fun_prop))

@[fun_prop]
theorem edgeVec' {f : α → ℕ} {g : α → List (List ℚ)} {h : α → ℕ × ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input (encList encPt))
    (hh : ComputableInPolyTime h input (encPair encUnary encUnary)) :
    ComputableInPolyTime (fun a ↦ Round.edgeVec (f a) (g a) (h a)) input encVec :=
  edgeVec_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

@[fun_prop]
theorem heavy' {n T m : α → ℕ} {vs : α → List (List Bool)} {a : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hT : ComputableInPolyTime T input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hvs : ComputableInPolyTime vs input (encList encVec))
    (ha : ComputableInPolyTime a input encVec) :
    ComputableInPolyTime (fun x ↦ Round.heavy (n x) (T x) (m x) (vs x) (a x)) input encBool := by
  unfold Round.heavy
  exact unary_le' hm ((length_list encVec).comp (filterWithInput hvs
    (unary_le' (by fun_prop) (unary_mul' (const 2) (by fun_prop)))))

/-- The parameters `(n, T, mth, vs)` of the greedy clustering. -/
abbrev encGP : ℕ × ℕ × ℕ × List (List Bool) ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encList encVec)))

theorem greedyStep_polytime : ComputableInPolyTime
    (fun p : ((ℕ × ℕ × ℕ × List (List Bool)) × List (List Bool)) × List Bool ↦
      Round.greedyStep p.1.1.1 p.1.1.2.1 p.1.1.2.2.1 p.1.1.2.2.2 p.1.2 p.2)
    (encPair (encPair encGP (encList encVec)) encVec) (encList encVec) := by
  unfold Round.greedyStep
  exact ite' (bool_and' (by fun_prop) (allWithInput (by fun_prop)
    (unary_lt' ((unary_div_const 4).comp (by fun_prop)) (by fun_prop))))
    (listAppend' (by fun_prop) (cons' (by fun_prop) (const []))) (by fun_prop)

theorem length_encList_append_singleton {β : Type} (e : β ↪ List Bool) (l : List β) (a : β) :
    (encList e (l ++ [a])).length = (encList e l).length + (2 * (e a).length + 1) := by
  rw [length_encList, length_encList, List.map_append, List.sum_append]
  simp

theorem greedy_polytime : ComputableInPolyTime
    (fun x : ℕ × ℕ × ℕ × List (List Bool) ↦ Round.greedy x.1 x.2.1 x.2.2.1 x.2.2.2) encGP
    (encList encVec) := by
  unfold Round.greedy
  refine foldlWith_of_bounded_growth (par := fun x : ℕ × ℕ × ℕ × List (List Bool) ↦ x)
    (step := fun p kept a ↦ Round.greedyStep p.1 p.2.1 p.2.2.1 p.2.2.2 kept a)
    id' (by fun_prop) (const []) greedyStep_polytime
    (growth := fun x ↦ 2 * (encGP x).length + 1) ?_ ?_
  · exact ((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)
  · intro x state value hv
    have h1 : (encVec value).length ≤ (encGP x).length := by
      refine (SizedListEncoding.length_elem_le (encA := encVec) (encL := encList encVec) _ _
        hv).trans ?_
      simp only [encGP, length_encPair]
      omega
    unfold Round.greedyStep
    split_ifs
    · rw [length_encList_append_singleton]
      omega
    · omega

@[fun_prop]
theorem greedy' {n T m : α → ℕ} {vs : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary) (hT : ComputableInPolyTime T input encUnary)
    (hm : ComputableInPolyTime m input encUnary)
    (hvs : ComputableInPolyTime vs input (encList encVec)) :
    ComputableInPolyTime (fun x ↦ Round.greedy (n x) (T x) (m x) (vs x)) input (encList encVec) :=
  greedy_polytime.comp (g := fun x ↦ (n x, T x, m x, vs x)) (hn.prod (hT.prod (hm.prod hvs)))

/-- Bit vectors, converted to raw bit strings. -/
theorem vecToBits {f : α → List Bool} (hf : ComputableInPolyTime f input encVec) :
    ComputableInPolyTime f input encBits :=
  (bits_encList_polyTime encBool).2.comp hf

theorem roundOut_polytime (c : ℕ) : ComputableInPolyTime
    (fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦ Round.roundOut x.1 x.2.1 c x.2.2.1 x.2.2.2)
    (encPair encUnary (encPair encUnary (encPair (encList encPt) encE2))) encOutput := by
  set enc := encPair encUnary (encPair encUnary (encPair (encList encPt) encE2))
  have hvs : ComputableInPolyTime (fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦
      x.2.2.2.map (Round.edgeVec x.1 x.2.2.1)) enc (encList encVec) :=
    mapWithInput (by fun_prop) (by fun_prop)
  have hT : ComputableInPolyTime (fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦
      x.1 / x.2.1 ^ (c + 2)) enc encUnary :=
    unary_div.comp (g := fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦ (x.1, x.2.1 ^ (c + 2)))
      ((fst _ _).prod ((unary_pow (c + 2)).comp (by fun_prop)))
  have hm : ComputableInPolyTime (fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦
      x.2.2.2.length / (4 * x.2.1)) enc encUnary :=
    unary_div.comp (g := fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦
      (x.2.2.2.length, 4 * x.2.1)) ((by fun_prop : ComputableInPolyTime _ enc encUnary).prod
        (unary_mul' (const 4) (by fun_prop)))
  have hk : ComputableInPolyTime (fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦
      (Round.greedy x.1 (x.1 / x.2.1 ^ (c + 2)) (x.2.2.2.length / (4 * x.2.1))
        (x.2.2.2.map (Round.edgeVec x.1 x.2.2.1))).take x.2.1) enc (encList encVec) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput (greedy' (fst _ _) hT hm hvs).tidy
      (by fun_prop : ComputableInPolyTime _ enc encUnary).tidy)
  have h : ComputableInPolyTime (fun x : ℕ × ℕ × List (List ℚ) × List (ℕ × ℕ) ↦
      (List.range x.1).map fun v ↦ ((Round.greedy x.1 (x.1 / x.2.1 ^ (c + 2))
        (x.2.2.2.length / (4 * x.2.1)) (x.2.2.2.map (Round.edgeVec x.1 x.2.2.1))).take
          x.2.1).map fun a ↦ a.getD v false) enc (encList encBits) :=
    mapWithInput (by fun_prop) (vecToBits (mapWithInput (hk.comp (fst _ _))
      (listGetDWithInput (by fun_prop) (by fun_prop) false)))
  exact h

/-! ### The algorithm -/

/-- **The algorithm runs in polynomial time** in the input and the budget, in unary. -/
theorem runAlg_polytime (c : ℕ) : ComputableInPolyTime (runAlg c) encY encOutput := by
  have hn : ComputableInPolyTime (fun y : (ℕ × List Bool) × ℕ ↦ numV y.1.1 y.1.2) encY
      encUnary :=
    numV_polytime.comp (fst _ _)
  have hb : ComputableInPolyTime (fun y : (ℕ × List Bool) × ℕ ↦ y.1.2) encY encBits := by
    fun_prop
  have h : ComputableInPolyTime (fun y : (ℕ × List Bool) × ℕ ↦
      Round.roundOut (numV y.1.1 y.1.2) (dimOf (numV y.1.1 y.1.2)) c
        (momentTable (numV y.1.1 y.1.2) (SoS.Core.core (solverInputOf c y.1, y.2)))
        (edgeList (numV y.1.1 y.1.2) y.1.2)) encY encOutput :=
    (roundOut_polytime c).comp (g := fun y : (ℕ × List Bool) × ℕ ↦
      (numV y.1.1 y.1.2, dimOf (numV y.1.1 y.1.2),
        momentTable (numV y.1.1 y.1.2) (SoS.Core.core (solverInputOf c y.1, y.2)),
        edgeList (numV y.1.1 y.1.2) y.1.2))
      (hn.prod ((dimOf' hn).prod ((momentTable' hn (core_run_polytime c)).prod
        (edgeList' hn hb))))
  exact h

/-- **The algorithm with the solver's budget runs in polynomial time** in the input `(n, adj)`. -/
theorem runBudget_polytime (c : ℕ) : ComputableInPolyTime
    (fun y : ℕ × List Bool ↦ runAlg c (y, Solver.budget (solverInputOf c y))) encX encOutput :=
  (runAlg_polytime c).comp (g := fun y : ℕ × List Bool ↦ (y, Solver.budget (solverInputOf c y)))
    (id'.prod (budget_polytime c))

end BMW26.Alg.PT

namespace BMW26.Alg

open Turing.MultiTapeTM

/-- **The algorithm runs in polynomial time.** -/
theorem alg_runsInTime (c : ℕ) : ∃ k : ℕ, RunsInTime (alg c) (fun N ↦ (N + 2) ^ k) := by
  obtain ⟨d, e, hd⟩ := (PT.runBudget_polytime c).tidy.exists_degree
  -- Reading `(n, adjTable G)` from the input: the encoded graph is its encoding.
  have h1 : ComputableTidilyInO (fun xr : Graph × List Bool ↦ (xr.1.1, adjTable xr.1))
      (encPair encGraph encBits) PT.encX
      (fun xr ↦ (encPair encGraph encBits xr).length)
      (fun xr ↦ (encPair encGraph encBits xr).length) :=
    (ComputableTidilyInO.fst encGraph encBits).of_enc_eq fun _ ↦ rfl
  obtain ⟨C, hC, -⟩ := (hd.inO.comp h1).computableInO
  replace hC : ComputableInTimeAndSpace (alg c) (encPair encGraph encBits) encOutput _ _ := hC
  refine ⟨d, C, hC.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩
  all_goals
    refine Nat.mul_le_mul_left C ?_
    have h : (PT.encX (xr.1.1, adjTable xr.1)).length + 1 ≤ (encGraph xr.1).length + 2 := by
      have : (PT.encX (xr.1.1, adjTable xr.1)).length = (encGraph xr.1).length := rfl
      omega
    have h2 := Nat.pow_le_pow_left h d
    have hk : (Encoding.encPair encGraph Encoding.encBits xr).length =
        (encPair encGraph encBits xr).length := rfl
    beta_reduce
    omega

end BMW26.Alg
