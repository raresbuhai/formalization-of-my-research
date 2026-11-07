module

public import BGHKLMM26.Run
public import Background.SumOfSquares.Algorithm.PolyTime
public import Background.PolyTime.Rat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial

/-!
# The algorithm runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the functions of
`BGHKLMM26.Alg.run`, ending with `BGHKLMM26.Alg.run_polytime`: the algorithm with the solver's
budget as a unary input runs in polynomial time, for every precision constant `Q₀`.

Encodings: an instance is its number of variables in unary and its constraints with binary
variable numbers (`BGHKLMM26.encInstance`); rationals in lowest terms; the solver's output as in
the solver; the coins and the output as bit strings.
-/

@[expose] public section

namespace BGHKLMM26.Alg

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS SoS.Solver SoS.Poly SoS.PolyTime SoS.Loop

/-- A constraint. -/
abbrev encC : Constraint ↪ List Bool := encPair (encPair encNat encNat) (encPair encBool encRat)

/-- An instance. -/
abbrev encI : Instance ↪ List Bool := encPair encUnary (encList encC)

theorem encInstance_eq : encInstance = encI := rfl

variable {α : Type} {input : α ↪ List Bool}

/-! ### Parameters -/

theorem foldl_max_eq_foldr (l : List ℕ) (a : ℕ) : l.foldl max a = l.foldr max a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons, List.foldr_cons, ih]
    clear ih
    induction l with
    | nil => simp [max_comm]
    | cons y l ih2 => simp only [List.foldr_cons]; rw [ih2]; omega

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

theorem decide_eq_unary_binary {f : α → ℕ} {g : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ decide (f a = g a)) input encBool :=
  decide_eq_binary hf (toBinary' hg)

theorem degree_polytime : ComputableInPolyTime (fun p : Instance × ℕ ↦ degree p.1 p.2)
    (encPair encI encUnary) encUnary := by
  unfold degree
  have h : ComputableInPolyTime (fun p : (Instance × ℕ) × Constraint ↦
      decide (p.2.1.1 = p.1.2 ∨ p.2.1.2 = p.1.2))
      (encPair (encPair encI encUnary) encC) encBool :=
    decide_or (decide_eq_unary_binary (by fun_prop) (by fun_prop))
      (decide_eq_unary_binary (by fun_prop) (by fun_prop))
  have hl : ComputableInPolyTime (fun p : Instance × ℕ ↦ p.1.2) (encPair encI encUnary)
      (encList encC) := by fun_prop
  have hf := filterWithInput (test := fun (p : Instance × ℕ) (c : Constraint) ↦
    decide (c.1.1 = p.2 ∨ c.1.2 = p.2)) hl h
  exact (length_list encC).comp hf

@[fun_prop]
theorem degree' {f : α → Instance} {g : α → ℕ} (hf : ComputableInPolyTime f input encI)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ degree (f a) (g a)) input encUnary :=
  degree_polytime.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

/-- The largest of a computed list of unary numbers. -/
theorem foldl_max_unary {f : α → List ℕ} (hf : ComputableInPolyTime f input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ (f a).foldl max 0) input encUnary := by
  have hstep : ComputableTidilyInPolyTime (fun p : (Bool × ℕ) × ℕ ↦ max p.1.2 p.2)
      (encPair (encPair encBool encUnary) encUnary) encUnary :=
    ComputableTidilyInPolyTime.unary_max.comp
      ((ComputableTidilyInPolyTime.fst _ _).snd'.prod (ComputableTidilyInPolyTime.snd _ _))
  refine .of_tidy (ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (par := fun _ ↦ false) (step := fun _ s v ↦ max s v) (encA := encUnary)
    (encL := encList encUnary) (ComputableTidilyInPolyTime.const false) hf.tidy
    (ComputableTidilyInPolyTime.const 0) hstep
    (growth := fun a ↦ (encList encUnary (f a)).length) hf.tidy.polyBounded_length ?_)
  intro a s v hv
  have h := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary)
    (f a) v hv
  simp only [encUnary_apply, List.length_replicate] at h ⊢
  omega

theorem maxDeg_polytime : ComputableInPolyTime maxDeg encI encUnary := by
  have e : maxDeg = fun I ↦ ((List.range I.1).map (degree I)).foldl max 0 :=
    funext fun I ↦ (foldl_max_eq_foldr _ _).symm
  rw [e]
  have hlist : ComputableInPolyTime (fun I : Instance ↦ (List.range I.1).map (degree I)) encI
      (encList encUnary) :=
    mapWithInput (f := fun (I : Instance) (v : ℕ) ↦ degree I v) (by fun_prop) (by fun_prop)
  exact foldl_max_unary hlist

@[fun_prop]
theorem maxDeg' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ maxDeg (f a)) input encUnary := maxDeg_polytime.comp hf

@[fun_prop]
theorem dPar' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ dPar (f a)) input encUnary := by
  unfold dPar; fun_prop

@[fun_prop]
theorem lPar' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ lPar (f a)) input encNat := by
  unfold lPar
  exact binary_clog_two_nat' (toBinary' (dPar' hf))

@[fun_prop]
theorem kPar' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ kPar (f a)) input encNat := by
  unfold kPar
  fun_prop

@[fun_prop]
theorem etaQ' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ etaQ (f a)) input encRat := by
  unfold etaQ; fun_prop

@[fun_prop]
theorem ratioQ' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ ratioQ (f a)) input encRat := by
  unfold ratioQ; fun_prop

@[fun_prop]
theorem tQ' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ tQ (f a)) input encRat := by
  unfold tQ; fun_prop

@[fun_prop]
theorem epsQ' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ epsQ (f a)) input encRat := by
  unfold epsQ; fun_prop

@[fun_prop]
theorem zPar' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ zPar (f a)) input encUnary := by
  unfold zPar; fun_prop

@[fun_prop]
theorem qPar' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ qPar Q₀ (f a)) input encUnary := by
  unfold qPar; fun_prop

@[fun_prop]
theorem pPar' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ pPar Q₀ (f a)) input encUnary := by
  unfold pPar; fun_prop

@[fun_prop]
theorem rPar' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ rPar Q₀ (f a)) input encUnary := by
  unfold rPar; fun_prop

@[fun_prop]
theorem tPar' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ tPar Q₀ (f a)) input encUnary := by
  unfold tPar; fun_prop

@[fun_prop]
theorem nSer' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ nSer Q₀ (f a)) input encUnary := by
  unfold nSer; fun_prop

@[fun_prop]
theorem kBis' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ kBis Q₀ (f a)) input encUnary := by
  unfold kBis; fun_prop

@[fun_prop]
theorem clampPar' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ clampPar Q₀ (f a)) input encRat := by
  unfold clampPar; exact rat_two_pow' (pPar' Q₀ hf)

@[fun_prop]
theorem wTot' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ wTot (f a)) input encRat := by
  unfold wTot
  have h : ComputableInPolyTime (fun a ↦ (f a).2.map fun c ↦ c.2.2) input (encList encRat) :=
    mapWithInput (f := fun _ (c : Constraint) ↦ c.2.2) (by fun_prop) (by fun_prop)
  exact rat_sum' h

@[fun_prop]
theorem etaS' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ etaS Q₀ (f a)) input encRat := by
  unfold etaS
  exact rat_div' (const 1) (rat_two_pow' (qPar' Q₀ hf))

@[fun_prop]
theorem tauS' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ tauS Q₀ (f a)) input encRat := by
  unfold tauS
  exact rat_div' (const 1) (rat_two_pow' (qPar' Q₀ hf))

theorem decide_rat_eq {f g : α → ℚ} (hf : ComputableInPolyTime f input encRat)
    (hg : ComputableInPolyTime g input encRat) :
    ComputableInPolyTime (fun a ↦ decide (f a = g a)) input encBool := by
  have h : (fun a ↦ decide (f a = g a)) = fun a ↦ (decide (f a ≤ g a) && decide (g a ≤ f a)) :=
    funext fun a ↦ by
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
        decide_eq_true_eq]
      exact ⟨fun h ↦ ⟨h.le, h.ge⟩, fun h ↦ le_antisymm h.1 h.2⟩
  rw [h]
  exact bool_and' (rat_le' hf hg) (rat_le' hg hf)

@[fun_prop]
theorem gammaS' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ gammaS Q₀ (f a)) input encRat := by
  unfold gammaS
  refine rat_div' (ite_prop (decide_rat_eq (wTot' hf) (const 0)) (const 1)
    (rat_min' (wTot' hf) (const 1))) (rat_two_pow' (qPar' Q₀ hf))

/-! ### The SDP -/

theorem decide_eq_unary_binary' {f : α → ℕ} {g : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ decide (f a = g a)) input encBool :=
  decide_eq_binary (toBinary' hf) hg

theorem pairExp_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ ↦ SDP.pairExp x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encNat encNat)) (encList encNat) := by
  unfold SDP.pairExp
  have h1 : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ decide (p.2 = p.1.2.1))
      (encPair (encPair encUnary (encPair encNat encNat)) encUnary) encBool :=
    decide_eq_unary_binary' (by fun_prop) (by fun_prop)
  have h2 : ComputableInPolyTime (fun p : (ℕ × ℕ × ℕ) × ℕ ↦ decide (p.2 = p.1.2.2))
      (encPair (encPair encUnary (encPair encNat encNat)) encUnary) encBool :=
    decide_eq_unary_binary' (by fun_prop) (by fun_prop)
  exact mapWithInput (f := fun (x : ℕ × ℕ × ℕ) (l : ℕ) ↦
      (if l = x.2.1 then 1 else 0) + (if l = x.2.2 then 1 else 0)) (by fun_prop)
    (.of_tidy (ComputableTidilyInPolyTime.binary_add' (ite_prop h1 (const 1) (const 0)).tidy
      (ite_prop h2 (const 1) (const 0)).tidy))

@[fun_prop]
theorem pairExp' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encNat) (hh : ComputableInPolyTime h input encNat) :
    ComputableInPolyTime (fun a ↦ SDP.pairExp (f a) (g a) (h a)) input (encList encNat) :=
  pairExp_polytime.comp (g := fun a ↦ (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem pairExpU' {f g h : α → ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary) :
    ComputableInPolyTime (fun a ↦ SDP.pairExp (f a) (g a) (h a)) input (encList encNat) :=
  pairExp' hf (toBinary' hg) (toBinary' hh)

@[fun_prop]
theorem ballC' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ SDP.ballC (f a)) input encRaw := by
  unfold SDP.ballC
  have h : ComputableInPolyTime (fun a ↦ (List.range (f a)).map fun i ↦
      (SDP.pairExp (f a) i i, (-1 : ℚ))) input encRaw :=
    mapWithInput (f := fun a (i : ℕ) ↦ (SDP.pairExp (f a) i i, (-1 : ℚ))) (by fun_prop)
      ((pairExpU' (by fun_prop) (by fun_prop) (by fun_prop)).prod (const _))
  have hn : ComputableInPolyTime (fun a ↦ ((f a : ℕ) : ℚ)) input encRat :=
    rat_natCast' (toBinary' hf)
  fun_prop

@[fun_prop]
theorem sqC' {f g : α → ℕ} {s : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hs : ComputableInPolyTime s input encRat) :
    ComputableInPolyTime (fun a ↦ SDP.sqC (f a) (g a) (s a)) input encRaw := by
  unfold SDP.sqC
  have h := pairExpU' hf hg hg
  fun_prop

@[fun_prop]
theorem triC' {f g h k : α → ℕ} {b b' : α → ℚ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input encUnary) (hh : ComputableInPolyTime h input encUnary)
    (hk : ComputableInPolyTime k input encUnary) (hb : ComputableInPolyTime b input encRat)
    (hb' : ComputableInPolyTime b' input encRat) :
    ComputableInPolyTime (fun a ↦ SDP.triC (f a) (g a) (h a) (k a) (b a) (b' a)) input encRaw := by
  unfold SDP.triC
  have h1 := pairExpU' hf hg hh
  have h2 := pairExpU' hf hg hk
  have h3 := pairExpU' hf hh hk
  fun_prop

/-- Triples, with unary entries. -/
abbrev encT : ℕ × ℕ × ℕ ↪ List Bool := encPair encUnary (encPair encUnary encUnary)

theorem triples_polytime : ComputableInPolyTime SDP.triples encUnary (encList encT) := by
  unfold SDP.triples
  have hk : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ ↦
      ((List.range p.1.1).filter fun k ↦ p.1.2 ≠ p.2 ∧ p.1.2 ≠ k ∧ p.2 ≠ k).map
        fun k ↦ (p.1.2, p.2, k))
      (encPair (encPair encUnary encUnary) encUnary) (encList encT) := by
    have htest : ComputableInPolyTime (fun q : ((ℕ × ℕ) × ℕ) × ℕ ↦
        decide (q.1.1.2 ≠ q.1.2 ∧ q.1.1.2 ≠ q.2 ∧ q.1.2 ≠ q.2))
        (encPair (encPair (encPair encUnary encUnary) encUnary) encUnary) encBool := by
      fun_prop
    have hf := filterWithInput (list := fun p : (ℕ × ℕ) × ℕ ↦ List.range p.1.1)
      (test := fun p k ↦ decide (p.1.2 ≠ p.2 ∧ p.1.2 ≠ k ∧ p.2 ≠ k)) (by fun_prop) htest
    exact mapWithInput (f := fun (p : (ℕ × ℕ) × ℕ) (k : ℕ) ↦ (p.1.2, p.2, k)) hf (by fun_prop)
  have hj : ComputableInPolyTime (fun p : ℕ × ℕ ↦ (List.range p.1).flatMap fun j ↦
      ((List.range p.1).filter fun k ↦ p.2 ≠ j ∧ p.2 ≠ k ∧ j ≠ k).map fun k ↦ (p.2, j, k))
      (encPair encUnary encUnary) (encList encT) :=
    flatMapWithInput (f := fun (p : ℕ × ℕ) (j : ℕ) ↦
      ((List.range p.1).filter fun k ↦ p.2 ≠ j ∧ p.2 ≠ k ∧ j ≠ k).map fun k ↦ (p.2, j, k))
      (by fun_prop) hk
  exact flatMapWithInput (f := fun (n : ℕ) (i : ℕ) ↦ (List.range n).flatMap fun j ↦
      ((List.range n).filter fun k ↦ i ≠ j ∧ i ≠ k ∧ j ≠ k).map fun k ↦ (i, j, k))
    (by fun_prop) hj

theorem constraints_polytime : ComputableInPolyTime SDP.constraints encUnary (encList encRaw) := by
  unfold SDP.constraints
  have h1 : ComputableInPolyTime (fun n : ℕ ↦ (List.range n).flatMap fun i ↦
      [SDP.sqC n i 1, SDP.sqC n i (-1)]) encUnary (encList encRaw) :=
    flatMapWithInput (f := fun (n : ℕ) (i : ℕ) ↦ [SDP.sqC n i 1, SDP.sqC n i (-1)])
      (by fun_prop) (by fun_prop)
  have ht : ComputableInPolyTime (fun p : ℕ × (ℕ × ℕ × ℕ) ↦
      [SDP.triC p.1 p.2.1 p.2.2.1 p.2.2.2 1 1, SDP.triC p.1 p.2.1 p.2.2.1 p.2.2.2 1 (-1),
        SDP.triC p.1 p.2.1 p.2.2.1 p.2.2.2 (-1) 1, SDP.triC p.1 p.2.1 p.2.2.1 p.2.2.2 (-1) (-1)])
      (encPair encUnary encT) (encList encRaw) := by
    fun_prop
  have h2 : ComputableInPolyTime (fun n : ℕ ↦ (SDP.triples n).flatMap fun t ↦
      [SDP.triC n t.1 t.2.1 t.2.2 1 1, SDP.triC n t.1 t.2.1 t.2.2 1 (-1),
        SDP.triC n t.1 t.2.1 t.2.2 (-1) 1, SDP.triC n t.1 t.2.1 t.2.2 (-1) (-1)])
      encUnary (encList encRaw) :=
    flatMapWithInput (f := fun (n : ℕ) (t : ℕ × ℕ × ℕ) ↦
      [SDP.triC n t.1 t.2.1 t.2.2 1 1, SDP.triC n t.1 t.2.1 t.2.2 1 (-1),
        SDP.triC n t.1 t.2.1 t.2.2 (-1) 1, SDP.triC n t.1 t.2.1 t.2.2 (-1) (-1)])
      triples_polytime ht
  fun_prop

@[fun_prop]
theorem constraints' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a ↦ SDP.constraints (f a)) input (encList encRaw) :=
  constraints_polytime.comp hf

theorem bsignQ_polytime : ComputableInPolyTime SDP.objective.bsignQ encBool encRat :=
  of_finite _

@[fun_prop]
theorem bsignQ' {f : α → Bool} (hf : ComputableInPolyTime f input encBool) :
    ComputableInPolyTime (fun a ↦ SDP.objective.bsignQ (f a)) input encRat :=
  bsignQ_polytime.comp hf

@[fun_prop]
theorem objective' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ SDP.objective (f a)) input encRaw := by
  unfold SDP.objective
  have hn : ComputableInPolyTime (fun a ↦ (f a).1) input encUnary := by fun_prop
  have h : ComputableInPolyTime (fun p : α × Constraint ↦
      ([([], -(p.2.2.2 / 2)), (SDP.pairExp (f p.1).1 p.2.1.1 p.2.1.2,
        -(p.2.2.2 * SDP.objective.bsignQ p.2.2.1 / 2))] : RawPoly))
      (encPair input encC) encRaw := by
    have hp : ComputableInPolyTime (fun p : α × Constraint ↦
        SDP.pairExp (f p.1).1 p.2.1.1 p.2.1.2) (encPair input encC) (encList encNat) :=
      pairExp' (hn.comp (fst _ _)) (by fun_prop) (by fun_prop)
    fun_prop
  exact flatMapWithInput (f := fun a (c : Constraint) ↦ ([([], -(c.2.2 / 2)),
      (SDP.pairExp (f a).1 c.1.1 c.1.2, -(c.2.2 * SDP.objective.bsignQ c.2.1 / 2))] : RawPoly))
    (by fun_prop) h

@[fun_prop]
theorem problem' {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ SDP.problem (f a)) input encProblemM := by
  unfold SDP.problem
  have hn : ComputableInPolyTime (fun a ↦ (f a).1) input encUnary := by fun_prop
  have := toBinary' hn
  fun_prop

@[fun_prop]
theorem solverInput' (Q₀ : ℕ) {f : α → Instance} (hf : ComputableInPolyTime f input encI) :
    ComputableInPolyTime (fun a ↦ solverInput Q₀ (f a)) input encInputM := by
  unfold solverInput
  fun_prop

/-! ### The solver's output and the rescaled moments -/

@[fun_prop]
theorem core' {f : α → SoS.Solver.Input} {g : α → ℕ} (hf : ComputableInPolyTime f input encInputM)
    (hg : ComputableInPolyTime g input encUnary) :
    ComputableInPolyTime (fun a ↦ SoS.Core.core (f a, g a)) input encRaw :=
  core_polytime'.comp (g := fun a ↦ (f a, g a)) (hf.prod hg)

@[fun_prop]
theorem momentsOf' {f : α → ℕ} {o : α → RawPoly} {g h : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) (ho : ComputableInPolyTime o input encRaw)
    (hg : ComputableInPolyTime g input encNat) (hh : ComputableInPolyTime h input encNat) :
    ComputableInPolyTime (fun a ↦ SDP.momentsOf (f a) (o a) (g a) (h a)) input encRat := by
  unfold SDP.momentsOf
  exact coeff' hf ho (pairExp' hf hg hh)

theorem foldl_max_eq_foldr_rat (l : List ℚ) (a : ℚ) : l.foldl max a = l.foldr max a := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons, List.foldr_cons, ih]
    clear ih
    induction l with
    | nil => simp [max_comm]
    | cons y l ih2 =>
      simp only [List.foldr_cons]; rw [ih2, max_left_comm]

/-- The largest of a computed list of rationals and `0`. -/
theorem foldl_max_rat {f : α → List ℚ} (hf : ComputableInPolyTime f input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ (f a).foldl max 0) input encRat := by
  have hstep : ComputableTidilyInPolyTime (fun p : (Bool × ℚ) × ℚ ↦ max p.1.2 p.2)
      (encPair (encPair encBool encRat) encRat) encRat :=
    (rat_max' (by fun_prop) (by fun_prop)).tidy
  refine .of_tidy (ComputableTidilyInPolyTime.foldlWith_of_bounded_growth
    (par := fun _ ↦ false) (step := fun _ s v ↦ max s v) (encA := encRat)
    (encL := encList encRat) (ComputableTidilyInPolyTime.const false) hf.tidy
    (ComputableTidilyInPolyTime.const 0) hstep
    (growth := fun a ↦ (encList encRat (f a)).length) hf.tidy.polyBounded_length ?_)
  intro a s v hv
  have h := SizedListEncoding.length_elem_le (encA := encRat) (encL := encList encRat) (f a) v hv
  rcases le_total s v with hsv | hsv
  · rw [max_eq_right hsv]; omega
  · rw [max_eq_left hsv]; omega

@[fun_prop]
theorem smax' {f : α → ℕ} {o : α → RawPoly} (hf : ComputableInPolyTime f input encUnary)
    (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ Factor.smax (f a) (SDP.momentsOf (f a) (o a))) input encRat := by
  have e : (fun a ↦ Factor.smax (f a) (SDP.momentsOf (f a) (o a))) =
      fun a ↦ ((List.range (f a)).map fun i ↦ SDP.momentsOf (f a) (o a) i i).foldl max 0 :=
    funext fun a ↦ (foldl_max_eq_foldr_rat _ _).symm
  rw [e]
  refine foldl_max_rat ?_
  exact mapWithInput (f := fun a (i : ℕ) ↦ SDP.momentsOf (f a) (o a) i i) (by fun_prop)
    (momentsOf' (by fun_prop) (by fun_prop) (toBinary' (by fun_prop)) (toBinary' (by fun_prop)))

@[fun_prop]
theorem aQ' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {g h : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hg : ComputableInPolyTime g input encNat) (hh : ComputableInPolyTime h input encNat) :
    ComputableInPolyTime (fun a ↦ O.aQ Q₀ (f a) (o a) (g a) (h a)) input encRat := by
  unfold O.aQ Factor.rescaled
  have hn : ComputableInPolyTime (fun a ↦ (f a).1) input encUnary := by fun_prop
  exact ite_prop (decide_eq_binary hg hh) (const 1)
    (rat_div' (momentsOf' hn ho hg hh) (rat_add' (smax' hn ho) (tauS' Q₀ hf)))

@[fun_prop]
theorem rhoQ' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {c : α → Constraint}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hc : ComputableInPolyTime c input encC) :
    ComputableInPolyTime (fun a ↦ O.rhoQ Q₀ (f a) (o a) (c a)) input encRat := by
  unfold O.rhoQ
  exact rat_mul' (bsignQ' (by fun_prop)) (aQ' Q₀ hf ho (by fun_prop) (by fun_prop))

@[fun_prop]
theorem inWin' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {c : α → Constraint}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hc : ComputableInPolyTime c input encC) :
    ComputableInPolyTime (fun a ↦ O.inWin Q₀ (f a) (o a) (c a)) input encBool := by
  unfold O.inWin
  have h := rhoQ' Q₀ hf ho hc
  exact .of_tidy (ComputableTidilyInPolyTime.decide_and (rat_lt' (const _) h).tidy
    (rat_lt' h (const _)).tidy)

@[fun_prop]
theorem winList' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ O.winList Q₀ (f a) (o a)) input (encList encC) := by
  unfold O.winList
  exact filterWithInput (test := fun a c ↦ O.inWin Q₀ (f a) (o a) c) (by fun_prop)
    (inWin' Q₀ (hf.comp (fst _ _)) (ho.comp (fst _ _)) (snd _ _))

@[fun_prop]
theorem sdpQ' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ O.sdpQ Q₀ (f a) (o a)) input encRat := by
  unfold O.sdpQ
  have hr := rhoQ' Q₀ (hf.comp (fst _ _)) (ho.comp (fst _ _)) (snd input encC)
  refine rat_sum' (mapWithInput (f := fun a (c : Constraint) ↦
    c.2.2 * ((1 + O.rhoQ Q₀ (f a) (o a) c) / 2)) (by fun_prop) ?_)
  fun_prop

@[fun_prop]
theorem sdpOutQ' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ O.sdpOutQ Q₀ (f a) (o a)) input encRat := by
  unfold O.sdpOutQ
  have hr := rhoQ' Q₀ (hf.comp (fst _ _)) (ho.comp (fst _ _)) (snd input encC)
  have hw := inWin' Q₀ (hf.comp (fst _ _)) (ho.comp (fst _ _)) (snd input encC)
  refine rat_sum' (mapWithInput (f := fun a (c : Constraint) ↦
    if O.inWin Q₀ (f a) (o a) c then 0 else c.2.2 * ((1 + O.rhoQ Q₀ (f a) (o a) c) / 2))
    (by fun_prop) ?_)
  exact ite' hw (const 0) (by fun_prop)

@[fun_prop]
theorem branch0' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ O.branch0 Q₀ (f a) (o a)) input encBool := by
  unfold O.branch0
  exact rat_le' (rat_mul' (epsQ' hf) (sdpQ' Q₀ hf ho)) (sdpOutQ' Q₀ hf ho)

@[fun_prop]
theorem rowsQ' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ O.rowsQ Q₀ (f a) (o a)) input
      (SoS.PDTestRat.encRatRows) := by
  unfold O.rowsQ
  have hn : ComputableInPolyTime (fun a ↦ (f a).1) input encUnary := by fun_prop
  refine mapWithInput (f := fun a (i : ℕ) ↦ (List.range (f a).1).map fun j ↦
    O.aQ Q₀ (f a) (o a) i j) (by fun_prop) ?_
  have hl : ComputableInPolyTime (fun p : α × ℕ ↦ List.range (f p.1).1) (encPair input encUnary)
      (encList encUnary) := by fun_prop
  refine mapWithInput (f := fun (p : α × ℕ) (j : ℕ) ↦ O.aQ Q₀ (f p.1) (o p.1) p.2 j) hl ?_
  exact aQ' Q₀ (hf.comp ((fst _ _).comp (fst _ _))) (ho.comp ((fst _ _).comp (fst _ _)))
    (toBinary' ((snd _ _).comp (fst _ _))) (toBinary' (snd _ _))

@[fun_prop]
theorem zRows' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw) :
    ComputableInPolyTime (fun a ↦ O.zRows Q₀ (f a) (o a)) input SoS.PDTestRows.encRows := by
  unfold O.zRows
  exact SoS.PDTestRat.scale_polytime.comp (rowsQ' Q₀ hf ho)

@[fun_prop]
theorem detB' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {k : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ O.detB Q₀ (f a) (o a) (k a)) input encIntBin := by
  unfold O.detB
  exact SoS.PDTestRows.detRows' (SoS.PDTestRows.block_polytime.comp
    (g := fun a ↦ (O.zRows Q₀ (f a) (o a), k a)) ((zRows' Q₀ hf ho).prod hk))

@[fun_prop]
theorem coefL' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {k : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ O.coefL Q₀ (f a) (o a) (k a)) input (encList encRat) := by
  unfold O.coefL
  have hc : ComputableInPolyTime (fun a ↦ SoS.PDTestRows.cof (O.zRows Q₀ (f a) (o a)) (k a))
      input (encList encIntBin) := SoS.PDTestRows.cof_polytime.comp
    (g := fun a ↦ (O.zRows Q₀ (f a) (o a), k a)) ((zRows' Q₀ hf ho).prod hk)
  have hd := detB' Q₀ hf ho hk
  exact mapWithInput (f := fun a (u : ℤ) ↦ (u : ℚ) / O.detB Q₀ (f a) (o a) (k a)) hc
    (rat_div' (rat_intCast' (snd _ _)) (rat_intCast' (hd.comp (fst _ _))))

@[fun_prop]
theorem diagL' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {k : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ O.diagL Q₀ (f a) (o a) (k a)) input encRat := by
  unfold O.diagL
  have hs : ComputableInPolyTime (fun a ↦ SoS.PDTestRows.schur (O.zRows Q₀ (f a) (o a)) (k a))
      input encIntBin := SoS.PDTestRows.schur_polytime.comp
    (g := fun a ↦ (O.zRows Q₀ (f a) (o a), k a)) ((zRows' Q₀ hf ho).prod hk)
  have hd := detB' Q₀ hf ho hk
  have hc : ComputableInPolyTime (fun a ↦ SoS.PDTestRat.commonDen (O.rowsQ Q₀ (f a) (o a)))
      input encIntBin := SoS.PDTestRat.commonDen_polytime.comp (rowsQ' Q₀ hf ho)
  exact rat_div' (rat_intCast' hs) (rat_mul' (rat_intCast' hd) (rat_intCast' hc))

/-! ### Numerics -/

theorem rat_pow' {f : α → ℚ} {k : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ^ k a) input encRat := by
  have e : (fun a ↦ f a ^ k a) = fun a ↦ (List.replicate (k a) (f a)).prod :=
    funext fun a ↦ (List.prod_replicate _ _).symm
  rw [e]
  exact rat_prod' (replicate hk hf)

@[fun_prop]
theorem phiTermQ' {f : α → ℚ} {m : α → ℕ} (hf : ComputableInPolyTime f input encRat)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun a ↦ Num.phiTermQ (f a) (m a)) input encRat := by
  unfold Num.phiTermQ
  have h1 := rat_pow' (const (-1 : ℚ)) hm
  have h2 := rat_pow' hf (show ComputableInPolyTime (fun a ↦ 2 * m a + 1) input encUnary by
    fun_prop)
  have h3 : ComputableInPolyTime (fun a ↦ ((m a).factorial : ℚ)) input encRat :=
    rat_natCast' (binary_factorial.comp hm)
  have h4 : ComputableInPolyTime (fun a ↦ ((m a : ℕ) : ℚ)) input encRat :=
    rat_natCast' (toBinary' hm)
  have h5 := rat_two_pow' hm
  exact rat_div' (rat_mul' h1 h2) (rat_mul' (rat_mul' h5 h3)
    (rat_add' (rat_mul' (const 2) h4) (const 1)))

@[fun_prop]
theorem phiSumQ' {N : α → ℕ} {f : α → ℚ} (hN : ComputableInPolyTime N input encUnary)
    (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ Num.phiSumQ (N a) (f a)) input encRat := by
  unfold Num.phiSumQ
  exact rat_sum' (mapWithInput (f := fun a (m : ℕ) ↦ Num.phiTermQ (f a) m) (by fun_prop)
    (phiTermQ' (hf.comp (fst _ _)) (snd _ _)))

theorem nestQ_eq_iterate (p n : ℕ) :
    Num.nestQ p n = (fun y ↦ sqrtP p (2 + y))^[n] 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ← ih]; rfl

theorem small_nestQ (p n : ℕ) : Small p 1 (Num.nestQ p n) := by
  rcases n with _ | n
  · exact small_zero p 1
  · have h0 : (0 : ℚ) ≤ 2 + Num.nestQ p n := by have := Num.nestQ_nonneg p n; linarith
    refine ⟨?_, ?_⟩
    · rw [Num.nestQ, abs_of_nonneg (Num.sqrtP_nonneg _ _), pow_one]
      have h1 := Num.sqrtP_le_sqrt p h0
      have h2 := (Num.nestQ_spec p n).1
      have h3 := Real.sqrtTwoAddSeries_lt_two n
      have h4 : √((2 + Num.nestQ p n : ℚ) : ℝ) ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; push_cast; linarith
      exact_mod_cast h1.trans h4
    · refine ⟨Nat.sqrt (⌊(2 + Num.nestQ p n) * 4 ^ p⌋.natAbs), ?_⟩
      rw [Num.nestQ, sqrtP]
      field_simp
      push_cast
      ring

@[fun_prop]
theorem nestQ' {p n : α → ℕ} (hp : ComputableInPolyTime p input encUnary)
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ Num.nestQ (p a) (n a)) input encRat := by
  have e : (fun a ↦ Num.nestQ (p a) (n a)) =
      fun a ↦ ((fun (q : ℕ) (y : ℚ) ↦ sqrtP q (2 + y)) (p a))^[n a] 0 :=
    funext fun a ↦ nestQ_eq_iterate _ _
  rw [e]
  have hstep : ComputableInPolyTime (fun q : ℕ × ℚ ↦ sqrtP q.1 (2 + q.2))
      (encPair encUnary encRat) encRat := sqrtP' (by fun_prop) (by fun_prop)
  refine iterateWith (par := p) (count := n) (init := fun _ ↦ (0 : ℚ))
    (step := fun (q : ℕ) (y : ℚ) ↦ sqrtP q (2 + y)) hp hn (const 0) hstep
    (bound := fun a ↦ 3 * (1 + p a) + 6)
    (by have := hp.polyBounded; exact ((PolyBounded.const 3).mul ((PolyBounded.const 1).add
      this)).add (.const 6)) fun a i _ ↦ ?_
  rw [← nestQ_eq_iterate]
  exact length_encRat_le_of_small (small_nestQ _ _)

@[fun_prop]
theorem piQ' {n : α → ℕ} (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ Num.piQ (n a)) input encRat := by
  unfold Num.piQ
  have h4 : ComputableInPolyTime (fun a ↦ 4 * n a + 3) input encUnary := by fun_prop
  have := nestQ' h4 hn
  have := sqrtP' h4 (rat_sub' (const 2) this)
  have := rat_two_pow' (show ComputableInPolyTime (fun a ↦ n a + 1) input encUnary by fun_prop)
  fun_prop

@[fun_prop]
theorem phiQ' {n N : α → ℕ} {f : α → ℚ} (hn : ComputableInPolyTime n input encUnary)
    (hN : ComputableInPolyTime N input encUnary) (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ Num.phiQ (n a) (N a) (f a)) input encRat := by
  unfold Num.phiQ Num.invSqrt2piQ
  have := sqrtP' hn (rat_mul' (const 2) (piQ' hn))
  have := phiSumQ' hN hf
  fun_prop

/-! ### Bisection and the Gaussians -/

/-- The bisection's endpoints are multiples of `2^-i` after `i` steps. -/
theorem bisect_dyadic (f : ℚ → ℚ) (u X : ℚ) (hX : ∃ z : ℤ, X = z) (i : ℕ) :
    (∃ z : ℤ, (Num.bisect f u X i).1 * 2 ^ i = z) ∧
      ∃ z : ℤ, (Num.bisect f u X i).2 * 2 ^ i = z := by
  obtain ⟨x, rfl⟩ := hX
  induction i with
  | zero => exact ⟨⟨-x, by simp [Num.bisect]⟩, ⟨x, by simp [Num.bisect]⟩⟩
  | succ i ih =>
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
    have hs : Num.bisect f u x (i + 1) = Num.bisectStep f u (Num.bisect f u x i) := by
      simp only [Num.bisect, Function.iterate_succ_apply']
    rw [hs]
    unfold Num.bisectStep
    have hm : ((Num.bisect f u x i).1 + (Num.bisect f u x i).2) / 2 * 2 ^ (i + 1) = a + b := by
      rw [← ha, ← hb, pow_succ]; ring
    have hlo : (Num.bisect f u x i).1 * 2 ^ (i + 1) = (2 * a : ℤ) := by
      push_cast; rw [← ha, pow_succ]; ring
    have hhi : (Num.bisect f u x i).2 * 2 ^ (i + 1) = (2 * b : ℤ) := by
      push_cast; rw [← hb, pow_succ]; ring
    split_ifs
    · exact ⟨⟨a + b, by rw [hm]; push_cast; ring⟩, ⟨2 * b, hhi⟩⟩
    · exact ⟨⟨2 * a, hlo⟩, ⟨a + b, by rw [hm]; push_cast; ring⟩⟩

theorem small_bisect (f : ℚ → ℚ) (u : ℚ) (R K i : ℕ) (hi : i ≤ K) :
    Small K (R + 1) (Num.bisect f u ((R : ℚ) + 1) i).1 ∧
      Small K (R + 1) (Num.bisect f u ((R : ℚ) + 1) i).2 := by
  have hX : (0 : ℚ) ≤ (R : ℚ) + 1 := by positivity
  obtain ⟨h0, h1, h5, -, -, -⟩ := Num.bisect_spec f u hX i
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := bisect_dyadic f u ((R : ℚ) + 1) ⟨R + 1, by push_cast; ring⟩ i
  have hR : (R : ℚ) + 1 ≤ 2 ^ (R + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := R + 1)).le
  have hK : (2 : ℚ) ^ K = 2 ^ i * 2 ^ (K - i) := by rw [← pow_add, Nat.add_sub_cancel' hi]
  refine ⟨⟨abs_le.2 ⟨by linarith, by linarith⟩, a * 2 ^ (K - i), ?_⟩,
    ⟨abs_le.2 ⟨by linarith, by linarith⟩, b * 2 ^ (K - i), ?_⟩⟩
  · rw [hK, ← mul_assoc, ha]; push_cast; ring
  · rw [hK, ← mul_assoc, hb]; push_cast; ring

/-- Pairs of rationals. -/
abbrev encQQ : ℚ × ℚ ↪ List Bool := encPair encRat encRat

theorem bisectStep_polytime : ComputableInPolyTime
    (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ Num.bisectStep (Num.phiQ q.1.1 q.1.2.1) q.1.2.2 q.2)
    (encPair (encPair encUnary (encPair encUnary encRat)) encQQ) encQQ := by
  unfold Num.bisectStep
  have hm : ComputableInPolyTime (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ (q.2.1 + q.2.2) / 2)
      (encPair (encPair encUnary (encPair encUnary encRat)) encQQ) encRat := by fun_prop
  have hc := rat_lt' (phiQ' (n := fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ q.1.1)
    (N := fun q ↦ q.1.2.1) (by fun_prop) (by fun_prop) hm)
    (show ComputableInPolyTime (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ q.1.2.2) _ encRat by fun_prop)
  exact ite' hc (hm.prod (by fun_prop)) ((by fun_prop : ComputableInPolyTime
    (fun q : (ℕ × ℕ × ℚ) × (ℚ × ℚ) ↦ q.2.1) _ encRat).prod hm)

@[fun_prop]
theorem cellInv' {n N K B R j : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hN : ComputableInPolyTime N input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hB : ComputableInPolyTime B input encUnary) (hR : ComputableInPolyTime R input encUnary)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ Num.cellInv (n a) (N a) (K a) (B a) ((R a : ℚ) + 1) (j a))
      input encRat := by
  unfold Num.cellInv Num.bisect
  have hu : ComputableInPolyTime (fun a ↦ ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1))) input encRat := by
    have := rat_natCast' hj
    have := rat_two_pow' (show ComputableInPolyTime (fun a ↦ B a + 1) input encUnary by fun_prop)
    fun_prop
  have hX : ComputableInPolyTime (fun a ↦ ((R a : ℚ) + 1)) input encRat := by
    have := rat_natCast' (toBinary' hR)
    fun_prop
  have hit := iterateWith (par := fun a ↦ (n a, N a, (2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)))
    (count := K) (init := fun a ↦ (-((R a : ℚ) + 1), (R a : ℚ) + 1))
    (step := fun (q : ℕ × ℕ × ℚ) (s : ℚ × ℚ) ↦ Num.bisectStep (Num.phiQ q.1 q.2.1) q.2.2 s)
    (hn.prod (hN.prod hu)) hK ((rat_neg' hX).prod hX) bisectStep_polytime
    (bound := fun a ↦ 9 * (R a + 1 + K a) + 19)
    (by
      have h1 := hR.polyBounded
      have h2 := hK.polyBounded
      exact ((PolyBounded.const 9).mul ((h1.add (.const 1)).add h2)).add (.const 19))
    (fun a i hi ↦ by
      obtain ⟨h1, h2⟩ := small_bisect (Num.phiQ (n a) (N a))
        ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)) (R a) (K a) i hi
      have l1 := length_encRat_le_of_small h1
      have l2 := length_encRat_le_of_small h2
      have : ((Num.bisectStep (Num.phiQ (n a) (N a)) ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)))^[i]
          (-((R a : ℚ) + 1), (R a : ℚ) + 1)) = Num.bisect (Num.phiQ (n a) (N a))
          ((2 * (j a : ℚ) + 1) / 2 ^ (B a + 1)) ((R a : ℚ) + 1) i := rfl
      rw [this, length_encPair]
      omega)
  exact hit.fst'

@[fun_prop]
theorem cellOfCoins' {B k : α → ℕ} {r : α → List Bool}
    (hB : ComputableInPolyTime B input encUnary) (hr : ComputableInPolyTime r input encBits)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ cellOfCoins (B a) (r a) (k a)) input encNat := by
  unfold cellOfCoins
  have hidx : ComputableInPolyTime (fun p : α × ℕ ↦ k p.1 * B p.1 + p.2)
      (encPair input encUnary) encUnary := by fun_prop
  have hbit := bitsGetDWithInput (list := fun p : α × ℕ ↦ r p.1) (hr.comp (fst _ _)) hidx false
  have hpow : ComputableInPolyTime (fun p : α × ℕ ↦ 2 ^ p.2) (encPair input encUnary) encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_two_pow.comp (snd _ _).tidy)
  have hl : ComputableInPolyTime (fun a ↦ (List.range (B a)).map fun i ↦
      if (r a).getD (k a * B a + i) false then 2 ^ i else 0) input (encList encNat) :=
    mapWithInput (f := fun a (i : ℕ) ↦ if (r a).getD (k a * B a + i) false then 2 ^ i else 0)
      (by fun_prop) (ite' hbit hpow (const 0))
  exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp hl.tidy)

@[fun_prop]
theorem gHat' (Q₀ : ℕ) {f : α → Instance} {r : α → List Bool} {k : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (hr : ComputableInPolyTime r input encBits)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ gHat Q₀ (f a) (cellOfCoins (tPar Q₀ (f a)) (r a)) (k a))
      input encRat := by
  unfold gHat
  exact cellInv' (tPar' Q₀ hf) (nSer' Q₀ hf) (kBis' Q₀ hf) (tPar' Q₀ hf) (rPar' Q₀ hf)
    (cellOfCoins' (tPar' Q₀ hf) hr hk)

/-! ### The projections -/

/-- The data the projections are computed from: the instance, the solver's output and the
coins. -/
abbrev encCtx : Instance × RawPoly × List Bool ↪ List Bool := encPair encI (encPair encRaw encBits)

@[fun_prop]
theorem xiNext' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {r : α → List Bool}
    {acc : α → List ℚ} {k : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hr : ComputableInPolyTime r input encBits) (hacc : ComputableInPolyTime acc input encPt)
    (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ O.xiNext Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a))
      (acc a) (k a)) input encRat := by
  unfold O.xiNext
  have hd : ComputableInPolyTime (fun a ↦ ((O.coefL Q₀ (f a) (o a) (k a)).zipWith (· * ·)
      (acc a)).sum) input encRat := dotL' (coefL' Q₀ hf ho hk) hacc
  exact clamp' (clampPar' Q₀ hf) (roundP' (pPar' Q₀ hf) (rat_add' hd
    (rat_mul' (sqrtP' (pPar' Q₀ hf) (diagL' Q₀ hf ho hk)) (gHat' Q₀ hf hr hk))))

theorem xiStep_small (Q₀ : ℕ) (I : Instance) (out : RawPoly) (cells : ℕ → ℕ) (l : List ℕ)
    (acc : List ℚ) (hacc : ∀ q ∈ acc, Small (pPar Q₀ I) (pPar Q₀ I) q) :
    (l.foldl (O.xiStep Q₀ I out cells) acc).length = acc.length + l.length ∧
      ∀ q ∈ l.foldl (O.xiStep Q₀ I out cells) acc, Small (pPar Q₀ I) (pPar Q₀ I) q := by
  induction l generalizing acc with
  | nil => exact ⟨by simp, hacc⟩
  | cons k l ih =>
    simp only [List.foldl_cons, List.length_cons]
    refine (ih _ ?_).imp (fun h ↦ by rw [h]; simp [O.xiStep]; ring) id
    intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact hacc q hq
    · rw [List.mem_singleton.1 hq, O.xiNext, clampPar]
      exact small_clamp_roundP _ _ _

@[fun_prop]
theorem xiHat' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {r : α → List Bool}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a ↦ O.xiHat Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a)))
      input encPt := by
  unfold O.xiHat
  have hstep : ComputableInPolyTime (fun p : ((Instance × RawPoly × List Bool) × List ℚ) × ℕ ↦
      O.xiStep Q₀ p.1.1.1 p.1.1.2.1 (cellOfCoins (tPar Q₀ p.1.1.1) p.1.1.2.2) p.1.2 p.2)
      (encPair (encPair encCtx encPt) encUnary) encPt := by
    unfold O.xiStep
    have p1 : ComputableInPolyTime (fun p : ((Instance × RawPoly × List Bool) × List ℚ) × ℕ ↦
        p.1.1.1) (encPair (encPair encCtx encPt) encUnary) encI := by fun_prop
    have p2 : ComputableInPolyTime (fun p : ((Instance × RawPoly × List Bool) × List ℚ) × ℕ ↦
        p.1.1.2.1) (encPair (encPair encCtx encPt) encUnary) encRaw := by fun_prop
    have p3 : ComputableInPolyTime (fun p : ((Instance × RawPoly × List Bool) × List ℚ) × ℕ ↦
        p.1.1.2.2) (encPair (encPair encCtx encPt) encUnary) encBits := by fun_prop
    have p4 : ComputableInPolyTime (fun p : ((Instance × RawPoly × List Bool) × List ℚ) × ℕ ↦
        p.1.2) (encPair (encPair encCtx encPt) encUnary) encPt := by fun_prop
    have p5 : ComputableInPolyTime (fun p : ((Instance × RawPoly × List Bool) × List ℚ) × ℕ ↦
        p.2) (encPair (encPair encCtx encPt) encUnary) encUnary := by fun_prop
    have := xiNext' Q₀ p1 p2 p3 p4 p5
    exact listAppend' p4 (cons' this (const []))
  have hn : ComputableInPolyTime (fun a ↦ (f a).1) input encUnary := by fun_prop
  refine foldlWith (par := fun a ↦ (f a, o a, r a)) (list := fun a ↦ List.range (f a).1)
    (init := fun _ ↦ ([] : List ℚ))
    (step := fun (c : Instance × RawPoly × List Bool) acc k ↦
      O.xiStep Q₀ c.1 c.2.1 (cellOfCoins (tPar Q₀ c.1) c.2.2) acc k)
    (hf.prod (ho.prod hr)) (by fun_prop) (const _) hstep
    (B := fun a ↦ (f a).1 * (6 * (pPar Q₀ (f a) + pPar Q₀ (f a)) + 13))
    (by
      have h1 := hn.polyBounded
      have h2 := (pPar' Q₀ hf).polyBounded
      exact h1.mul (((PolyBounded.const 6).mul (h2.add h2)).add (.const 13))) ?_
  intro a i hi
  obtain ⟨hlen, hsm⟩ := xiStep_small Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a))
    ((List.range (f a).1).take i) [] (by simp)
  refine length_encPt_le ?_ hsm
  rw [hlen]
  simp

/-! ### The votes and the output -/

/-- Out-edges `(j, b, w)`, with binary `j`. -/
abbrev encE : ℕ × Bool × ℚ ↪ List Bool := encPair encNat (encPair encBool encRat)

theorem outEdges_eq (T : List Constraint) (i : ℕ) :
    outEdges T i = (T.filter fun c ↦ decide (c.1.1 = i ∨ c.1.2 = i)).map fun c ↦
      if c.1.1 = i then (c.1.2, c.2.1, c.2.2) else (c.1.1, c.2.1, c.2.2) := by
  induction T with
  | nil => rfl
  | cons c T ih =>
    simp only [outEdges, List.filterMap_cons] at ih ⊢
    by_cases h1 : c.1.1 = i
    · simp [h1, ih]
    · by_cases h2 : c.1.2 = i
      · simp [h1, h2, ih]
      · simp [h1, h2, ih]

@[fun_prop]
theorem outEdges' {T : α → List Constraint} {i : α → ℕ}
    (hT : ComputableInPolyTime T input (encList encC))
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ outEdges (T a) (i a)) input (encList encE) := by
  simp_rw [outEdges_eq]
  have h1 : ComputableInPolyTime (fun p : α × Constraint ↦ decide (p.2.1.1 = i p.1))
      (encPair input encC) encBool :=
    decide_eq_unary_binary (by fun_prop) (hi.comp (fst _ _))
  have h2 : ComputableInPolyTime (fun p : α × Constraint ↦ decide (p.2.1.2 = i p.1))
      (encPair input encC) encBool :=
    decide_eq_unary_binary (by fun_prop) (hi.comp (fst _ _))
  have hf := filterWithInput (test := fun a (c : Constraint) ↦ decide (c.1.1 = i a ∨ c.1.2 = i a))
    hT (decide_or h1 h2)
  exact mapWithInput (f := fun a (c : Constraint) ↦
      if c.1.1 = i a then (c.1.2, c.2.1, c.2.2) else (c.1.1, c.2.1, c.2.2)) hf
    (ite_prop h1 (by fun_prop) (by fun_prop))

@[fun_prop]
theorem hHat' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {xi : α → List ℚ} {i : α → ℕ}
    {e : α → ℕ × Bool × ℚ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hxi : ComputableInPolyTime xi input encPt) (hi : ComputableInPolyTime i input encUnary)
    (he : ComputableInPolyTime e input encE) :
    ComputableInPolyTime (fun a ↦ O.hHat Q₀ (f a) (o a) (xi a) (i a) (e a)) input encRat := by
  unfold O.hHat
  have hb : ComputableInPolyTime (fun a ↦ SDP.objective.bsignQ (e a).2.1) input encRat :=
    bsignQ' (by fun_prop)
  have hρ : ComputableInPolyTime (fun a ↦ SDP.objective.bsignQ (e a).2.1 *
      O.aQ Q₀ (f a) (o a) (i a) (e a).1) input encRat :=
    rat_mul' hb (aQ' Q₀ hf ho (toBinary' hi) (by fun_prop))
  have hj : ComputableInPolyTime (fun a ↦ (xi a).getD (e a).1 0) input encRat :=
    .of_tidy (ComputableTidilyInPolyTime.listGetD_binary 0 hxi.tidy (by fun_prop : 
      ComputableInPolyTime (fun a ↦ (e a).1) input encNat).tidy)
  have hii : ComputableInPolyTime (fun a ↦ (xi a).getD (i a) 0) input encRat :=
    listGetDWithInput hxi hi 0
  exact rat_div' (rat_sub' (rat_mul' hb hj) (rat_mul' hρ hii))
    (sqrtP' (pPar' Q₀ hf) (rat_sub' (const 1) (rat_sq' hρ)))

@[fun_prop]
theorem wDegQ' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {i : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ O.wDegQ Q₀ (f a) (o a) (i a)) input encRat := by
  unfold O.wDegQ
  exact rat_sum' (mapWithInput (f := fun _ (e : ℕ × Bool × ℚ) ↦ e.2.2)
    (outEdges' (winList' Q₀ hf ho) hi) (by fun_prop))

@[fun_prop]
theorem fHat' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {xi : α → List ℚ} {i : α → ℕ}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hxi : ComputableInPolyTime xi input encPt) (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ O.fHat Q₀ (f a) (o a) (xi a) (i a)) input encRat := by
  unfold O.fHat
  have hf1 := hf.comp (fst input encE)
  have ho1 := ho.comp (fst input encE)
  have hi1 := hi.comp (fst input encE)
  have hh := hHat' Q₀ hf1 ho1 (hxi.comp (fst input encE)) hi1 (snd input encE)
  have hw := wDegQ' Q₀ hf1 ho1 hi1
  have hp := phiQ' (tPar' Q₀ hf1) (nSer' Q₀ hf1) (rat_mul' (ratioQ' hf1) hh)
  refine rat_sum' (mapWithInput (f := fun a (e : ℕ × Bool × ℚ) ↦
      e.2.2 / O.wDegQ Q₀ (f a) (o a) (i a) *
      (2 * Num.phiQ (tPar Q₀ (f a)) (nSer Q₀ (f a))
        (ratioQ (f a) * O.hHat Q₀ (f a) (o a) (xi a) (i a) e) - 1))
    (outEdges' (winList' Q₀ hf ho) hi) ?_)
  exact rat_mul' (rat_div' (by fun_prop) hw) (rat_sub' (rat_mul' (const 2) hp) (const 1))

@[fun_prop]
theorem algC' (Q₀ : ℕ) {f : α → Instance} {o : α → RawPoly} {r : α → List Bool}
    (hf : ComputableInPolyTime f input encI) (ho : ComputableInPolyTime o input encRaw)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a ↦ O.algC Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a)))
      input (encList encBool) := by
  unfold O.algC
  have hx := xiHat' Q₀ hf ho hr
  have hx1 := hx.comp (fst input encUnary)
  have hget : ComputableInPolyTime (fun p : α × ℕ ↦
      (O.xiHat Q₀ (f p.1) (o p.1) (cellOfCoins (tPar Q₀ (f p.1)) (r p.1))).getD p.2 0)
      (encPair input encUnary) encRat := listGetDWithInput hx1 (snd _ _) 0
  have hfh := fHat' Q₀ (hf.comp (fst input encUnary)) (ho.comp (fst input encUnary)) hx1
    (snd input encUnary)
  have hn : ComputableInPolyTime (fun a ↦ List.range (f a).1) input (encList encUnary) := by
    fun_prop
  refine ite' (branch0' Q₀ hf ho) ?_ ?_
  · exact mapWithInput (f := fun a (i : ℕ) ↦ decide (0 ≤
      (O.xiHat Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a))).getD i 0)) hn
      (rat_le' (const 0) hget)
  · exact mapWithInput (f := fun a (i : ℕ) ↦ decide (0 ≤
      (O.xiHat Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a))).getD i 0 +
        tQ (f a) * O.fHat Q₀ (f a) (o a)
          (O.xiHat Q₀ (f a) (o a) (cellOfCoins (tPar Q₀ (f a)) (r a))) i)) hn
      (rat_le' (const 0) (rat_add' hget (rat_mul' (tQ' (hf.comp (fst _ _))) hfh)))

/-- The input of `BGHKLMM26.Alg.run`: an instance, coins, and a budget in unary. -/
abbrev encRunIn : (Instance × List Bool) × ℕ ↪ List Bool :=
  encPair (encPair encInstance encBits) encUnary

/-- **The algorithm with budget `L` runs in polynomial time** in the instance, the coins and
`L`, for every precision constant `Q₀`. -/
theorem run_polytime (Q₀ : ℕ) : ComputableInPolyTime (run Q₀) encRunIn encBits := by
  have hI : ComputableInPolyTime (fun x : (Instance × List Bool) × ℕ ↦ x.1.1) encRunIn encI :=
    by fun_prop
  have hr : ComputableInPolyTime (fun x : (Instance × List Bool) × ℕ ↦ x.1.2) encRunIn encBits :=
    by fun_prop
  have hL : ComputableInPolyTime (fun x : (Instance × List Bool) × ℕ ↦ x.2) encRunIn encUnary :=
    by fun_prop
  have ho := core' (solverInput' Q₀ hI) hL
  have h := algC' Q₀ hI ho hr
  exact .of_tidy (ComputableTidilyInPolyTime.listToBits.comp h.tidy)

end BGHKLMM26.Alg
