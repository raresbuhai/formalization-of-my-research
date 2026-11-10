module

public import ABBKS26.Assembly.ExecData

/-! Budgeted raw expansions for the explicit moment program. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.MomentExpansion

open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver SoS.Poly

/-- The empty product retains the short constant representation. -/
def tupleTerm (d : ℕ) (ts : RawPoly) : List ℕ × ℚ :=
  if ts = [] then ([], 1) else prodTerm d ts

theorem tupleTerm_append (d : ℕ) (ts : RawPoly) (t : List ℕ × ℚ) :
    tupleTerm d (ts ++ [t]) =
      (addE d (tupleTerm d ts).1 t.1, (tupleTerm d ts).2 * t.2) := by
  by_cases hs : ts = []
  · subst ts
    simp [tupleTerm, prodTerm, sumE, addE]
  · simp only [tupleTerm, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      ↓reduceIte, hs, prodTerm, List.map_append, List.prod_append,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    congr 1
    apply List.ext_getElem (by simp [sumE, addE])
    intro i hi hi'
    have hid : i < d := by simpa [sumE] using hi
    simp [sumE, addE, List.getD_eq_getElem?_getD, hid]

/-- The tuple enumerator bounds the number of products before multiplying coefficients. -/
def powerB (L d : ℕ) (p : RawPoly) (r : ℕ) : RawPoly :=
  (sectB (L + 1) (List.replicate r p)).map (tupleTerm d)

theorem powerB_eq (L d : ℕ) (p : RawPoly) (r : ℕ)
    (hL : (max 1 p.length) ^ r ≤ L + 1) :
    powerB L d p r = (fun q ↦ SoS.Coords.mulRaw d q p)^[r] [([], 1)] := by
  have h (s : ℕ) (hs : s ≤ r) :
      (sectB (L + 1) (List.replicate s p)).length = p.length ^ s ∧
      powerB L d p s = (fun q ↦ SoS.Coords.mulRaw d q p)^[s] [([], 1)] := by
    induction s with
    | zero => simp [powerB, sectB, tupleTerm]
    | succ s ih =>
      obtain ⟨hlen, heq⟩ := ih (by omega)
      have hbound : p.length ^ (s + 1) ≤ L + 1 := by
        calc
          _ ≤ (max 1 p.length) ^ (s + 1) := Nat.pow_le_pow_left (le_max_right _ _) _
          _ ≤ (max 1 p.length) ^ r := Nat.pow_le_pow_right (by omega) hs
          _ ≤ _ := hL
      have hstep : sectB (L + 1) (List.replicate (s + 1) p) =
          (sectB (L + 1) (List.replicate s p)).flatMap
            (fun ts ↦ p.map fun t ↦ ts ++ [t]) := by
        rw [List.replicate_succ', sectB, List.foldl_append]
        simp only [List.foldl_cons, List.foldl_nil, sectStep]
        apply List.take_of_length_le
        simp only [List.length_flatMap, List.length_map, List.map_const',
          List.sum_replicate, smul_eq_mul]
        change (sectB (L + 1) (List.replicate s p)).length * p.length ≤ L + 1
        rw [hlen, ← Nat.pow_succ]
        exact hbound
      constructor
      · rw [hstep]
        simp [hlen, List.length_flatMap, Nat.pow_succ]
      · rw [powerB, hstep, List.map_flatMap]
        rw [Function.iterate_succ_apply', ← heq, powerB, SoS.Coords.mulRaw,
          List.flatMap_map]
        congr 1
        funext ts
        simp only [List.map_map, Function.comp_def, tupleTerm_append]
  exact (h r le_rfl).2

theorem tupleTerm_polytime : ComputableInPolyTime
    (fun q : ℕ × RawPoly ↦ tupleTerm q.1 q.2)
    (encPair encUnary encRaw) encTerm := by
  unfold tupleTerm
  exact ite_decide (by fun_prop) (const ([], 1)) prodTerm_polytime

theorem powerB_polytime : ComputableInPolyTime
    (fun q : ℕ × ℕ × RawPoly × ℕ ↦ powerB q.1 q.2.1 q.2.2.1 q.2.2.2)
    (encPair encUnary (encPair encUnary (encPair encRaw encUnary))) encRaw := by
  unfold powerB
  apply mapWithInput
    (sectB_polytime encTerm |>.comp
      ((unary_add' (fst _ _) (const 1)).prod
        (replicate ((snd _ _).comp ((snd _ _).comp (snd _ _)))
          ((fst _ _).comp ((snd _ _).comp (snd _ _))))))
  exact tupleTerm_polytime.comp
    (((fst _ _).comp ((snd _ _).comp (fst _ _))).prod (snd _ _))

theorem maximum_polytime : ComputableInPolyTime
    (fun l : List ℕ ↦ l.foldr max 0) (encList encNat) encNat := by
  have hm : ComputableInPolyTime (fun p : ℕ × ℕ ↦ max p.1 p.2)
      (encPair encNat encNat) encNat := by
    have h := ite_decide (binary_le' (fst _ _) (snd _ _)) (snd _ _) (fst _ _)
    exact h.of_enc_eq fun p ↦ by simp only [max_def]
  refine foldrWithInput_of_bounded_growth id' (const 0)
    (hm.comp ((snd _ _).prod ((snd _ _).comp (fst _ _))))
    (growth := fun l ↦ (encList encNat l).length + 1)
    (PolyBounded.self.add (.const 1)) ?_
  intro l state value hv
  have hv' := SizedListEncoding.length_elem_le (encA := encNat)
    (encL := encList encNat) l value hv
  have hh := (Nat.size_le_size (show max value state ≤ value + state by omega)).trans
    (Nat.size_add_le value state)
  simp only [encNat_apply, Nat.size_eq_bits_len] at hv' ⊢
  omega

theorem allB_polytime : ComputableInPolyTime
    (fun q : ℕ × ℕ × ℕ ↦ SoS.Mono.allB q.1 q.2.1 q.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList (encList encNat)) := by
  have h : ComputableInPolyTime (fun l : List (List ℕ) ↦ l)
      (encList (encList encUnary)) (encList (encList encNat)) := by
    have hrow : ComputableInPolyTime (fun l : List ℕ ↦ l)
        (encList encUnary) (encList encNat) := by
      exact (ComputableInPolyTime.of_tidy
        (ComputableTidilyInPolyTime.map unary_to_binary.tidy)).of_enc_eq fun l ↦ by simp
    exact (ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.map hrow.tidy)).of_enc_eq fun l ↦ by simp
  exact h.comp SoS.Mono.allB_polytime

theorem rat_pow' {α : Type} {input : α ↪ List Bool} {f : α → ℚ} {e : α → ℕ}
    (hf : ComputableInPolyTime f input encRat)
    (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ f a ^ e a) input encRat :=
  rat_of_numDen (g := fun a ↦ ((f a).num ^ e a, (f a).den ^ e a))
    ((ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.intBin_pow' (rat_num' hf).tidy he.tidy)).prod
        (binary_pow' (rat_den' hf) he))
    fun a ↦ by rw [Rat.num_pow, Rat.den_pow]

theorem unary_sum : ComputableInPolyTime List.sum (encList encUnary) encUnary := by
  have h : ComputableInPolyTime
      (fun l : List ℕ ↦ l.flatMap fun n ↦ List.replicate n true)
      (encList encUnary) (encList encBool) :=
    flatMapWithInput id' (replicate (snd _ _) (const true))
  exact ((length_list encBool).comp h).of_enc_eq fun l ↦ by
    simp [List.length_flatMap]

end ABBKS26.Assembly.Exec.MomentExpansion
