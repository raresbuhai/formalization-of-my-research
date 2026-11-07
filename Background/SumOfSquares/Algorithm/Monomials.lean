module

public import Background.SumOfSquares.Moments
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.GetD
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Complexity.Tactic.PolyTime

/-!
# Listing monomials

The exponent vectors of length `n` and degree at most `D`, each once (`SoS.Mono.all`), built one
variable at a time: every vector `e` is kept with the degree `r = D - ∑ e` it has left, and is
extended by every exponent `a ≤ r` of a new first variable (`SoS.Mono.extend`).
-/

@[expose] public section

namespace SoS.Mono

/-- Extend every pair `(r, e)`, of an exponent vector `e` and the degree `r` it has left, by every
exponent `a ≤ r` of a new first variable. -/
def extend (acc : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  acc.flatMap fun p => (List.range (p.1 + 1)).map fun a => (p.1 - a, a :: p.2)

/-- The pairs `(D - ∑ e, e)` for the exponent vectors `e` of length `n` and degree at most `D`. -/
def pairs (n D : ℕ) : List (ℕ × List ℕ) := extend^[n] [(D, [])]

/-- The exponent vectors of length `n` and degree at most `D`. -/
def all (n D : ℕ) : List (List ℕ) := (pairs n D).map Prod.snd

theorem pairs_succ (n D : ℕ) : pairs (n + 1) D = extend (pairs n D) :=
  Function.iterate_succ_apply' _ _ _

theorem mem_extend {acc : List (ℕ × List ℕ)} {p : ℕ × List ℕ} :
    p ∈ extend acc ↔ ∃ q ∈ acc, ∃ a ≤ q.1, p = (q.1 - a, a :: q.2) := by
  simp only [extend, List.mem_flatMap, List.mem_map, List.mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨q, hq, a, ha, rfl⟩
    exact ⟨q, hq, a, ha, rfl⟩
  · rintro ⟨q, hq, a, ha, rfl⟩
    exact ⟨q, hq, a, ha, rfl⟩

theorem mem_pairs {n D : ℕ} {p : ℕ × List ℕ} :
    p ∈ pairs n D ↔ p.2.length = n ∧ p.2.sum ≤ D ∧ p.1 = D - p.2.sum := by
  induction n generalizing p with
  | zero =>
    simp only [pairs, Function.iterate_zero, id_eq, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨hl, -, h1⟩
      rw [List.length_eq_zero_iff] at hl
      obtain ⟨r, e⟩ := p
      simp_all
  | succ n ih =>
    rw [pairs_succ, mem_extend]
    constructor
    · rintro ⟨q, hq, a, ha, rfl⟩
      obtain ⟨hl, hs, h1⟩ := ih.1 hq
      simp only [List.length_cons, hl, List.sum_cons, true_and]
      omega
    · obtain ⟨r, e⟩ := p
      rintro ⟨hl, hs, h1⟩
      obtain ⟨a, e', rfl⟩ : ∃ a e', e = a :: e' := by
        cases e with
        | nil => simp at hl
        | cons a e' => exact ⟨a, e', rfl⟩
      simp only [List.length_cons, List.sum_cons] at hl hs h1 ⊢
      refine ⟨(D - e'.sum, e'), ih.2 ⟨by simpa using hl, show e'.sum ≤ D by omega, rfl⟩, a,
        show a ≤ D - e'.sum by omega, ?_⟩
      simp only [Prod.mk.injEq, and_true]
      omega

theorem mem_all {n D : ℕ} {e : List ℕ} : e ∈ all n D ↔ e.length = n ∧ e.sum ≤ D := by
  simp only [all, List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨(mem_pairs.1 hp).1, (mem_pairs.1 hp).2.1⟩
  · rintro ⟨hl, hs⟩
    exact ⟨(D - e.sum, e), mem_pairs.2 ⟨hl, hs, rfl⟩, rfl⟩

theorem nodup_pairs (n D : ℕ) : (pairs n D).Nodup := by
  induction n with
  | zero => simp [pairs]
  | succ n ih =>
    rw [pairs_succ, extend, List.nodup_flatMap]
    refine ⟨fun q _ => (List.nodup_range).map fun a b h => by
      simp only [Prod.mk.injEq, List.cons.injEq] at h
      exact h.2.1, ?_⟩
    refine ih.pairwise_of_forall_ne fun q hq q' hq' hne => ?_
    simp only [Function.onFun]
    rw [List.disjoint_iff_ne]
    rintro _ hx _ hy rfl
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, ha⟩ := hx
    obtain ⟨a', -, ha'⟩ := hy
    rw [← ha'] at ha
    simp only [Prod.mk.injEq, List.cons.injEq] at ha
    apply hne
    have h1 := (mem_pairs.1 hq).2.2
    have h2 := (mem_pairs.1 hq').2.2
    obtain ⟨r, e⟩ := q
    obtain ⟨r', e'⟩ := q'
    simp only at ha h1 h2
    obtain ⟨-, -, rfl⟩ := ha
    simp [h1, h2]

theorem nodup_all (n D : ℕ) : (all n D).Nodup := by
  refine (nodup_pairs n D).map_on fun p hp q hq h => ?_
  have h1 := (mem_pairs.1 hp).2.2
  have h2 := (mem_pairs.1 hq).2.2
  obtain ⟨r, e⟩ := p
  obtain ⟨r', e'⟩ := q
  simp only at h h1 h2
  subst h
  simp [h1, h2]

/-! ### How many there are -/

theorem sum_getD_eq_sum (e : List ℕ) : ∑ i : Fin e.length, e.getD i 0 = e.sum := by
  induction e with
  | nil => simp
  | cons a e ih =>
    rw [List.length_cons, Fin.sum_univ_succ, List.sum_cons]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ]
    rw [ih]

/-- The monomial with exponent vector `e`. -/
noncomputable def toFinsupp (n : ℕ) (e : List ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => e.getD i 0

@[simp] theorem toFinsupp_apply (n : ℕ) (e : List ℕ) (i : Fin n) :
    toFinsupp n e i = e.getD i 0 := by
  simp [toFinsupp]

theorem degree_toFinsupp {n : ℕ} {e : List ℕ} (he : e.length = n) :
    (toFinsupp n e).degree = e.sum := by
  subst he
  rw [Finsupp.degree_eq_sum]
  simp only [toFinsupp_apply]
  exact sum_getD_eq_sum e

theorem toFinsupp_inj {n : ℕ} {e e' : List ℕ} (he : e.length = n) (he' : e'.length = n)
    (h : toFinsupp n e = toFinsupp n e') : e = e' := by
  refine List.ext_getElem (he.trans he'.symm) fun i hi hi' => ?_
  have := congrArg (fun f => f ⟨i, he ▸ hi⟩) h
  simp only [toFinsupp_apply] at this
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] at this

/-- There are at most `(n + 1)^D` exponent vectors of length `n` and degree at most `D`. -/
theorem length_all_le (n D : ℕ) : (all n D).length ≤ (n + 1) ^ D := by
  classical
  have hinj : ∀ e ∈ all n D, ∀ e' ∈ all n D, toFinsupp n e = toFinsupp n e' → e = e' :=
    fun e he e' he' h => toFinsupp_inj (mem_all.1 he).1 (mem_all.1 he').1 h
  calc (all n D).length = ((all n D).map (toFinsupp n)).toFinset.card := by
        rw [List.toFinset_card_of_nodup ((nodup_all n D).map_on hinj), List.length_map]
    _ ≤ (monomialsLE (Fin n) D).card := by
        refine Finset.card_le_card fun m hm => ?_
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hm)
        rw [mem_monomialsLE, degree_toFinsupp (mem_all.1 he).1]
        exact (mem_all.1 he).2
    _ ≤ (Fintype.card (Fin n) + 1) ^ D := card_monomialsLE_le D
    _ = (n + 1) ^ D := by simp

theorem length_pairs_le (n D : ℕ) : (pairs n D).length ≤ (n + 1) ^ D := by
  simpa [all] using length_all_le n D

/-! ### With a budget -/

/-- One step of the budgeted enumeration: `SoS.Mono.extend`, cut at `L` pairs. -/
def extendB (L : ℕ) (acc : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  (extend acc).take L

/-- The budgeted enumeration: the degree is cut at `L`, and every step at `L` pairs. -/
def pairsB (L n D : ℕ) : List (ℕ × List ℕ) := (extendB L)^[n] [(min D L, [])]

/-- The exponent vectors of length `n` and degree at most `D`, within the budget `L`. -/
def allB (L n D : ℕ) : List (List ℕ) := (pairsB L n D).map Prod.snd

/-- With a large enough budget, nothing is cut. -/
theorem pairsB_eq {L n D : ℕ} (hD : D ≤ L) (hL : (n + 1) ^ D ≤ L) :
    pairsB L n D = pairs n D := by
  have key : ∀ k ≤ n, (extendB L)^[k] [(min D L, [])] = pairs k D := by
    intro k hk
    induction k with
    | zero => simp [pairs, Nat.min_eq_left hD]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega), extendB, List.take_of_length_le,
        pairs_succ]
      calc (extend (pairs k D)).length = (pairs (k + 1) D).length := by rw [pairs_succ]
        _ ≤ (k + 1 + 1) ^ D := length_pairs_le _ _
        _ ≤ (n + 1) ^ D := Nat.pow_le_pow_left (by omega) _
        _ ≤ L := hL
  exact key n le_rfl

theorem allB_eq {L n D : ℕ} (hD : D ≤ L) (hL : (n + 1) ^ D ≤ L) : allB L n D = all n D := by
  rw [allB, all, pairsB_eq hD hL]

/-- The budgeted states stay small: every degree and exponent is at most `L`, the vectors have at
most `i` entries after `i` steps, and there are at most `L + 1` pairs. -/
theorem pairsB_iter_small (L D i : ℕ) :
    (∀ q ∈ (extendB L)^[i] [(min D L, [])], q.1 ≤ L ∧ q.2.length ≤ i ∧ ∀ a ∈ q.2, a ≤ L) ∧
      ((extendB L)^[i] [(min D L, [])]).length ≤ L + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨fun q hq => ?_, ?_⟩
    · obtain ⟨p, hp, a, ha, rfl⟩ := mem_extend.1 (List.mem_of_mem_take hq)
      obtain ⟨h1, h2, h3⟩ := ih.1 p hp
      refine ⟨by simp; omega, by simp; omega, fun b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · omega
      · exact h3 b hb
    · rw [extendB, List.length_take]
      omega

section PolyTime

open Turing.MultiTapeTM ComputableInPolyTime

/-- Lists of pairs `(r, e)`, with unary entries. -/
abbrev encPairs : List (ℕ × List ℕ) ↪ List Bool := encList (encPair encUnary (encList encUnary))

theorem extendB_polytime : ComputableInPolyTime (fun p : ℕ × List (ℕ × List ℕ) => extendB p.1 p.2)
    (encPair encUnary encPairs) encPairs := by
  unfold extendB extend
  have h : ComputableInPolyTime (fun p : ℕ × List (ℕ × List ℕ) =>
      p.2.flatMap fun q => (List.range (q.1 + 1)).map fun a => (q.1 - a, a :: q.2))
      (encPair encUnary encPairs) encPairs :=
    flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))
  fun_prop

/-- **The budgeted enumeration runs in polynomial time**, in the budget, the number of variables and
the degree, all in unary. -/
theorem pairsB_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => pairsB x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) encPairs := by
  unfold pairsB
  refine iterateWith (par := fun x : ℕ × ℕ × ℕ => x.1) (count := fun x => x.2.1)
    (init := fun x => [(min x.2.2 x.1, [])]) (step := extendB) (by fun_prop) (by fun_prop)
    (by fun_prop) extendB_polytime
    (bound := fun x => (x.1 + 1) * (2 * ((x.2.1 + 1) * (2 * x.1 + 1)) + 1)) ?_ ?_
  · refine PolyBounded.of_forall_le 7 3 fun x => ?_
    set s := (encPair encUnary (encPair encUnary encUnary) x).length
    have hs : x.1 + x.2.1 ≤ s := by
      simp only [s, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have h1 : x.1 + 1 ≤ s + 1 := by omega
    have h2 : x.2.1 + 1 ≤ s + 1 := by omega
    have h3 : 2 * x.1 + 1 ≤ 2 * (s + 1) := by omega
    calc (x.1 + 1) * (2 * ((x.2.1 + 1) * (2 * x.1 + 1)) + 1)
        ≤ (s + 1) * (2 * ((s + 1) * (2 * (s + 1))) + 1 * (s + 1) * (s + 1)) := by
          gcongr
          nlinarith
      _ = 5 * (s + 1) ^ 3 := by ring
      _ ≤ 7 * (s + 1) ^ 3 := by gcongr; norm_num
  · intro x i hi
    obtain ⟨hsmall, hlen⟩ := pairsB_iter_small x.1 x.2.2 i
    have helem : ∀ q ∈ (extendB x.1)^[i] [(min x.2.2 x.1, [])],
        (encPair encUnary (encList encUnary) q).length ≤ (x.2.1 + 1) * (2 * x.1 + 1) := by
      intro q hq
      obtain ⟨h1, h2, h3⟩ := hsmall q hq
      have hl := length_encList_le encUnary q.2 (b := x.1) fun a ha => by
        simpa [encUnary_apply] using h3 a ha
      rw [length_encPair, encUnary_apply, List.length_replicate]
      have : q.2.length * (2 * x.1 + 1) ≤ x.2.1 * (2 * x.1 + 1) :=
        Nat.mul_le_mul_right _ (h2.trans hi)
      nlinarith
    calc (encPairs ((extendB x.1)^[i] [(min x.2.2 x.1, [])])).length
        ≤ ((extendB x.1)^[i] [(min x.2.2 x.1, [])]).length *
            (2 * ((x.2.1 + 1) * (2 * x.1 + 1)) + 1) := length_encList_le _ _ helem
      _ ≤ (x.1 + 1) * (2 * ((x.2.1 + 1) * (2 * x.1 + 1)) + 1) := Nat.mul_le_mul_right _ hlen

theorem allB_polytime : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => allB x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encUnary encUnary)) (encList (encList encUnary)) := by
  unfold allB
  have := pairsB_polytime
  fun_prop

end PolyTime

end SoS.Mono
