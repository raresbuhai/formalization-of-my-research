module

public import Background.SumOfSquares.Solver
public import Background.SumOfSquares.Algorithm.Monomials
public import Background.PolyTime.Rat

/-!
# Raw polynomials

The input polynomials (`SoS.Solver.RawPoly`) are lists of terms, with exponent lists of any length
and repeated monomials. This file reads their coefficients and degrees.

* `SoS.Poly.expo n e`: the exponent vector of a term, with exactly `n` entries.
* `SoS.Poly.coeff n p m`: the coefficient of the exponent vector `m`, summed over the terms with
  that exponent vector; it is the coefficient of `p.toPoly n` (`SoS.Poly.coeff_toPoly`).
* `SoS.Poly.degree n p`: the largest degree of an exponent vector of a term with a nonzero
  coefficient; it is the total degree of `p.toPoly n` (`SoS.Poly.degree_eq_totalDegree`).
-/

@[expose] public section

namespace SoS.Poly

open MvPolynomial SoS.Solver

/-- The exponent vector of a term, with exactly `n` entries: missing exponents are `0`, and
exponents past `n` are dropped. -/
def expo (n : ℕ) (e : List ℕ) : List ℕ := (List.range n).map fun i => e.getD i 0

@[simp] theorem length_expo (n : ℕ) (e : List ℕ) : (expo n e).length = n := by
  simp [expo]

theorem getD_expo {n : ℕ} (e : List ℕ) {i : ℕ} (hi : i < n) : (expo n e).getD i 0 = e.getD i 0 := by
  simp [expo, List.getD_eq_getElem?_getD, hi]

/-- The coefficient of the exponent vector `m`: the sum of the coefficients of the terms with that
exponent vector. -/
def coeff (n : ℕ) (p : RawPoly) (m : List ℕ) : ℚ :=
  ((p.filter fun t => expo n t.1 = m).map Prod.snd).sum

/-- A term `c x^e` is the monomial of its exponent vector. -/
theorem term_eq_monomial (n : ℕ) (t : List ℕ × ℚ) :
    C t.2 * ∏ i : Fin n, X i ^ t.1.getD i 0 = monomial (Mono.toFinsupp n (expo n t.1)) t.2 := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun i => by simp)]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Mono.toFinsupp_apply, getD_expo _ i.2]

theorem toPoly_eq_sum (n : ℕ) (p : RawPoly) :
    p.toPoly n = (p.map fun t => monomial (Mono.toFinsupp n (expo n t.1)) t.2).sum := by
  rw [RawPoly.toPoly]
  congr 1
  exact List.map_congr_left fun t _ => term_eq_monomial n t

/-- **The coefficients.** -/
theorem coeff_toPoly {n : ℕ} (p : RawPoly) {m : List ℕ} (hm : m.length = n) :
    (p.toPoly n).coeff (Mono.toFinsupp n m) = coeff n p m := by
  classical
  rw [toPoly_eq_sum, coeff]
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.map_cons, List.sum_cons]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    rw [ih, coeff_monomial, List.filter_cons]
    by_cases h : expo n t.1 = m
    · subst h
      simp
    · have : Mono.toFinsupp n (expo n t.1) ≠ Mono.toFinsupp n m :=
        fun h' => h (Mono.toFinsupp_inj (length_expo _ _) hm h')
      simp [h, this]

theorem toFinsupp_ofFn {n : ℕ} (s : Fin n →₀ ℕ) : Mono.toFinsupp n (List.ofFn s) = s := by
  ext i
  simp [Mono.toFinsupp_apply, List.getD_eq_getElem?_getD]

/-- Every monomial of the polynomial is the exponent vector of a term. -/
theorem mem_support_toPoly {n : ℕ} {p : RawPoly} {s : Fin n →₀ ℕ}
    (hs : s ∈ (p.toPoly n).support) : ∃ t ∈ p, expo n t.1 = List.ofFn s := by
  by_contra h
  push Not at h
  apply mem_support_iff.1 hs
  rw [← toFinsupp_ofFn s, coeff_toPoly p (by simp), coeff,
    List.filter_eq_nil_iff.2 fun t ht => by simpa using h t ht]
  simp

/-! ### Degrees -/

theorem foldl_max_le_iff {l : List ℕ} {a b : ℕ} :
    l.foldl max a ≤ b ↔ a ≤ b ∧ ∀ x ∈ l, x ≤ b := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih]
    simp only [max_le_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem le_foldl_max {l : List ℕ} {x : ℕ} (hx : x ∈ l) (a : ℕ) : x ≤ l.foldl max a := by
  have := (foldl_max_le_iff (l := l) (a := a) (b := l.foldl max a)).1 le_rfl
  exact this.2 x hx

/-- The total degree: the largest degree of an exponent vector of a term with a nonzero
coefficient, or `0`. -/
def degree (n : ℕ) (p : RawPoly) : ℕ :=
  ((p.filter fun t => decide (coeff n p (expo n t.1) ≠ 0)).map fun t => (expo n t.1).sum).foldl
    max 0

/-- **The degree** is the total degree. -/
theorem degree_eq_totalDegree (n : ℕ) (p : RawPoly) : degree n p = (p.toPoly n).totalDegree := by
  classical
  apply le_antisymm
  · rw [degree, foldl_max_le_iff]
    refine ⟨Nat.zero_le _, fun x hx => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    have hc : coeff n p (expo n t.1) ≠ 0 := by simpa using (List.mem_filter.1 ht).2
    have hmem : Mono.toFinsupp n (expo n t.1) ∈ (p.toPoly n).support := by
      rw [mem_support_iff, coeff_toPoly p (length_expo _ _)]
      exact_mod_cast hc
    have := le_totalDegree hmem
    change (Mono.toFinsupp n (expo n t.1)).degree ≤ _ at this
    rwa [Mono.degree_toFinsupp (length_expo _ _)] at this
  · refine Finset.sup_le fun s hs => ?_
    obtain ⟨t, ht, he⟩ := mem_support_toPoly hs
    have hc : coeff n p (expo n t.1) ≠ 0 := by
      rw [he, ← coeff_toPoly p (by simp), toFinsupp_ofFn]
      exact_mod_cast mem_support_iff.1 hs
    have hsum : s.degree = (expo n t.1).sum := by
      have := Mono.degree_toFinsupp (n := n) (e := List.ofFn s) (by simp)
      rw [toFinsupp_ofFn] at this
      rw [this, he]
    change s.degree ≤ _
    rw [hsum]
    rw [degree]
    exact le_foldl_max (List.mem_map_of_mem (f := fun t : List ℕ × ℚ => (expo n t.1).sum)
      (List.mem_filter.2 ⟨ht, decide_eq_true hc⟩)) 0

/-! ### Real coefficients and moments -/

theorem toFinsupp_expo (n : ℕ) (e : List ℕ) : Mono.toFinsupp n (expo n e) = Mono.toFinsupp n e := by
  ext i
  rw [Mono.toFinsupp_apply, Mono.toFinsupp_apply, getD_expo _ i.2]

/-- A term as a polynomial. -/
noncomputable def termPoly (n : ℕ) (t : List ℕ × ℚ) : MvPolynomial (Fin n) ℚ :=
  monomial (Mono.toFinsupp n t.1) t.2

theorem toPoly_eq_sum' (n : ℕ) (p : RawPoly) : p.toPoly n = (p.map (termPoly n)).sum := by
  rw [toPoly_eq_sum]
  congr 1
  exact List.map_congr_left fun t _ => by rw [termPoly, toFinsupp_expo]

theorem toPoly_append (n : ℕ) (p q : RawPoly) : (p ++ q).toPoly n = p.toPoly n + q.toPoly n := by
  rw [toPoly_eq_sum', toPoly_eq_sum', toPoly_eq_sum', List.map_append, List.sum_append]

theorem toReal_toPoly (n : ℕ) (p : RawPoly) :
    toReal (p.toPoly n) = (p.map fun t => monomial (Mono.toFinsupp n t.1) (t.2 : ℝ)).sum := by
  rw [toPoly_eq_sum', toReal, map_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => by simp [termPoly]

/-- **The Riesz functional of a raw polynomial**: `∑ c y(e)` over its terms `(e, c)`. -/
theorem riesz_toPoly (n : ℕ) (Y : (Fin n →₀ ℕ) → ℝ) (p : RawPoly) :
    riesz Y (toReal (p.toPoly n)) = (p.map fun t => (t.2 : ℝ) * Y (Mono.toFinsupp n t.1)).sum := by
  rw [toReal_toPoly, map_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => by simp

/-! ### The coefficient norm -/

/-- The squared Euclidean norm of the coefficients, computed term by term:
`∑ (e, c), c · coeff(e)`. -/
def normSq (n : ℕ) (p : RawPoly) : ℚ := (p.map fun t => t.2 * coeff n p (expo n t.1)).sum

theorem sum_coeff_sq (n : ℕ) (p : RawPoly) :
    ∑ m ∈ (p.toPoly n).support, (p.toPoly n).coeff m ^ 2 = normSq n p := by
  classical
  set P := p.toPoly n
  let Φ : MvPolynomial (Fin n) ℚ →ₗ[ℚ] ℚ := ∑ m ∈ P.support, P.coeff m • lcoeff ℚ m
  have hΦ : ∀ q, Φ q = ∑ m ∈ P.support, P.coeff m * q.coeff m := by
    intro q
    simp only [Φ, LinearMap.sum_apply, LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
  have hmono : ∀ s c, Φ (monomial s c) = c * P.coeff s := by
    intro s c
    rw [hΦ]
    simp only [coeff_monomial]
    rw [Finset.sum_eq_single s (fun b _ hb => by simp [Ne.symm hb])]
    · simp [mul_comm]
    · intro hs
      rw [notMem_support_iff.1 hs]
      simp
  have hP : Φ P = (p.map fun t => t.2 * coeff n p (expo n t.1)).sum := by
    have : P = (p.map (termPoly n)).sum := toPoly_eq_sum' n p
    rw [this, map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp, termPoly, hmono]
    rw [← toFinsupp_expo, coeff_toPoly p (length_expo _ _)]
  rw [normSq, ← hP, hΦ]
  simp [sq]

/-- **The coefficient norm** of a raw polynomial: its square is `SoS.Poly.normSq`. -/
theorem coeffNorm_toReal_sq (n : ℕ) (p : RawPoly) :
    coeffNorm (toReal (p.toPoly n)) ^ 2 = (normSq n p : ℝ) := by
  rw [coeffNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), ← sum_coeff_sq, toReal,
    support_map_of_injective _ (algebraMap ℚ ℝ).injective]
  push_cast
  simp [coeff_map]

/-! ### Shifts and products -/

/-- The exponent vector `a + b`, of length `n`. -/
def addE (n : ℕ) (a b : List ℕ) : List ℕ := (List.range n).map fun i => a.getD i 0 + b.getD i 0

@[simp] theorem length_addE (n : ℕ) (a b : List ℕ) : (addE n a b).length = n := by
  simp [addE]

theorem toFinsupp_addE (n : ℕ) (a b : List ℕ) :
    Mono.toFinsupp n (addE n a b) = Mono.toFinsupp n a + Mono.toFinsupp n b := by
  ext i
  simp [addE, List.getD_eq_getElem?_getD, i.2]

/-- `xᵐ p`. -/
def shift (n : ℕ) (m : List ℕ) (p : RawPoly) : RawPoly :=
  p.map fun t => (addE n m t.1, t.2)

theorem toPoly_shift (n : ℕ) (m : List ℕ) (p : RawPoly) :
    (shift n m p).toPoly n = monomial (Mono.toFinsupp n m) 1 * p.toPoly n := by
  rw [toPoly_eq_sum', toPoly_eq_sum', shift, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [termPoly, toFinsupp_addE, monomial_mul_monomial]

/-- The exponent vector of a product of terms: the sum of their exponent vectors. -/
def sumE (n : ℕ) (tup : List (List ℕ × ℚ)) : List ℕ :=
  (List.range n).map fun i => (tup.map fun t => t.1.getD i 0).sum

/-- The product of a list of terms, as a term. -/
def prodTerm (n : ℕ) (tup : List (List ℕ × ℚ)) : List ℕ × ℚ :=
  (sumE n tup, (tup.map Prod.snd).prod)

theorem termPoly_prodTerm (n : ℕ) (tup : List (List ℕ × ℚ)) :
    termPoly n (prodTerm n tup) = (tup.map (termPoly n)).prod := by
  induction tup with
  | nil =>
    have : Mono.toFinsupp n (sumE n []) = 0 := by
      ext i; simp [sumE, List.getD_eq_getElem?_getD, i.2]
    simp [termPoly, prodTerm, this]
  | cons t tup ih =>
    have : Mono.toFinsupp n (sumE n (t :: tup)) =
        Mono.toFinsupp n t.1 + Mono.toFinsupp n (sumE n tup) := by
      ext i
      simp [sumE, List.getD_eq_getElem?_getD, i.2]
    rw [List.map_cons, List.prod_cons, ← ih]
    simp only [termPoly, prodTerm, this, List.map_cons, List.prod_cons, monomial_mul_monomial]

/-- One step of the budgeted sections: every tuple is extended by every element of `l`, and the
first `L` tuples are kept. -/
def sectStep {α : Type} (L : ℕ) (acc : List (List α)) (l : List α) : List (List α) :=
  (acc.flatMap fun s => l.map fun a => s ++ [a]).take L

/-- The budgeted sections: the tuples with one element from each list, at most `L` of them. -/
def sectB {α : Type} (L : ℕ) (ls : List (List α)) : List (List α) := ls.foldl (sectStep L) [[]]

/-- Without cuts, a sum over the sections of products is the product of the sums. -/
theorem sum_foldl_sectStep {α R : Type} [CommSemiring R] (g : α → R) (L : ℕ) :
    ∀ (ls : List (List α)) (acc : List (List α)), (∀ l ∈ ls, l ≠ []) →
      acc.length * (ls.map List.length).prod ≤ L →
      ((ls.foldl (sectStep L) acc).map fun s => (s.map g).prod).sum =
        (acc.map fun s => (s.map g).prod).sum * (ls.map fun l => (l.map g).sum).prod
  | [], acc, _, _ => by simp
  | l :: ls, acc, hne, hL => by
    have hpos : 0 < (ls.map List.length).prod :=
      List.prod_pos fun k hk => by
        obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hk
        exact List.length_pos_iff.2 (hne l' (List.mem_cons_of_mem _ hl'))
    have hlen : (acc.flatMap fun s => l.map fun a => s ++ [a]).length = acc.length * l.length := by
      rw [List.length_flatMap]
      simp only [List.length_map, List.map_const', List.sum_replicate, smul_eq_mul]
    have hstep : sectStep L acc l = acc.flatMap fun s => l.map fun a => s ++ [a] := by
      rw [sectStep, List.take_of_length_le]
      rw [hlen]
      simp only [List.map_cons, List.prod_cons] at hL
      calc acc.length * l.length ≤ acc.length * (l.length * (ls.map List.length).prod) :=
            Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hpos)
        _ ≤ L := hL
    rw [List.foldl_cons, hstep, sum_foldl_sectStep g L ls _
      (fun l' hl' => hne l' (List.mem_cons_of_mem _ hl')) (by
        rw [hlen]
        simp only [List.map_cons, List.prod_cons] at hL
        calc acc.length * l.length * (ls.map List.length).prod
            = acc.length * (l.length * (ls.map List.length).prod) := by ring
          _ ≤ L := hL)]
    rw [List.map_cons, List.prod_cons, ← mul_assoc]
    congr 1
    rw [List.flatMap, List.map_flatten, List.sum_flatten, List.map_map, List.map_map,
      ← List.sum_map_mul_right]
    congr 1
    refine List.map_congr_left fun s _ => ?_
    simp only [Function.comp, List.map_map]
    rw [← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp [List.map_append]

/-- The product of raw polynomials, as the list of products of one term from each, within the
budget `L`. -/
def prodRaw (n L : ℕ) (fs : List RawPoly) : RawPoly := (sectB L fs).map (prodTerm n)

/-- **Products**: with a large enough budget, `prodRaw` is the product. -/
theorem toPoly_prodRaw {n L : ℕ} {fs : List RawPoly} (hne : ∀ f ∈ fs, f ≠ [])
    (hL : (fs.map List.length).prod ≤ L) :
    (prodRaw n L fs).toPoly n = (fs.map fun f => f.toPoly n).prod := by
  rw [toPoly_eq_sum', prodRaw, List.map_map]
  have := sum_foldl_sectStep (termPoly n) L fs [[]] hne (by simpa using hL)
  simp only [List.map_cons, List.map_nil, List.prod_nil, List.sum_cons, List.sum_nil, add_zero,
    one_mul] at this
  rw [sectB]
  have h2 : (fs.map fun f => f.toPoly n) = fs.map fun l => (l.map (termPoly n)).sum :=
    List.map_congr_left fun f _ => toPoly_eq_sum' n f
  rw [h2, ← this]
  congr 1
  exact List.map_congr_left fun tup _ => termPoly_prodTerm n tup

/-! ### Capped degrees -/

theorem foldl_max_eq_or_mem (l : List ℕ) (a : ℕ) : l.foldl max a = a ∨ l.foldl max a ∈ l := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons]
    rcases ih (max a x) with h | h
    · rw [h]
      rcases le_total a x with hax | hax
      · right; rw [max_eq_right hax]; exact List.mem_cons_self
      · left; exact max_eq_left hax
    · right; exact List.mem_cons_of_mem _ h

/-- The degree, capped at `c`. -/
def degCap (n c : ℕ) (p : RawPoly) : ℕ :=
  ((p.filter fun t => decide (coeff n p (expo n t.1) ≠ 0)).map fun t =>
    min c (expo n t.1).sum).foldl max 0

theorem degCap_eq (n c : ℕ) (p : RawPoly) : degCap n c p = min c (degree n p) := by
  apply le_antisymm
  · rw [degCap, foldl_max_le_iff]
    refine ⟨Nat.zero_le _, fun x hx => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    refine min_le_min le_rfl ?_
    rw [degree]
    exact le_foldl_max (List.mem_map_of_mem (f := fun t : List ℕ × ℚ => (expo n t.1).sum) ht) 0
  · rcases foldl_max_eq_or_mem ((p.filter fun t => decide (coeff n p (expo n t.1) ≠ 0)).map
      fun t => (expo n t.1).sum) 0 with h | h
    · rw [degree, h]
      exact (min_le_right _ _).trans (Nat.zero_le _)
    · obtain ⟨t, ht, he⟩ := List.mem_map.1 h
      rw [degree, ← he, degCap]
      exact le_foldl_max (List.mem_map_of_mem (f := fun t : List ℕ × ℚ => min c (expo n t.1).sum)
        ht) 0

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- Terms, with binary exponents. -/
abbrev encTerm : List ℕ × ℚ ↪ List Bool := encPair (encList encNat) encRat

/-- Raw polynomials, as in the input (`SoS.Solver.encRawPoly`). -/
abbrev encRaw : RawPoly ↪ List Bool := encList encTerm

theorem expo_polytime : ComputableInPolyTime (fun x : ℕ × List ℕ => expo x.1 x.2)
    (encPair encUnary (encList encNat)) (encList encNat) := by
  unfold expo
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem expo' {f : α → ℕ} {g : α → List ℕ} (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encNat)) :
    ComputableInPolyTime (fun a => expo (f a) (g a)) input (encList encNat) :=
  expo_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem coeff_polytime :
    ComputableInPolyTime (fun x : ℕ × RawPoly × List ℕ => coeff x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair encRaw (encList encNat))) encRat := by
  unfold coeff
  have h : ComputableInPolyTime (fun x : ℕ × RawPoly × List ℕ =>
      x.2.1.filter fun t => decide (expo x.1 t.1 = x.2.2))
      (encPair encUnary (encPair encRaw (encList encNat))) encRaw :=
    filterWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem coeff' {f : α → ℕ} {g : α → RawPoly} {h : α → List ℕ}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encRaw)
    (hh : ComputableInPolyTime h input (encList encNat)) :
    ComputableInPolyTime (fun a => coeff (f a) (g a) (h a)) input encRat :=
  coeff_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem normSq_polytime : ComputableInPolyTime (fun x : ℕ × RawPoly => normSq x.1 x.2)
    (encPair encUnary encRaw) encRat := by
  unfold normSq
  have h : ComputableInPolyTime (fun x : ℕ × RawPoly =>
      x.2.map fun t => t.2 * coeff x.1 x.2 (expo x.1 t.1))
      (encPair encUnary encRaw) (encList encRat) :=
    mapWithInput (by fun_prop) (by fun_prop)
  fun_prop

@[fun_prop]
theorem normSq' {f : α → ℕ} {g : α → RawPoly}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encRaw) :
    ComputableInPolyTime (fun a => normSq (f a) (g a)) input encRat :=
  normSq_polytime.comp (g := fun a => (f a, g a)) (hf.prod hg)

theorem addE_polytime : ComputableInPolyTime (fun x : ℕ × List ℕ × List ℕ => addE x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair (encList encNat) (encList encNat))) (encList encNat) := by
  unfold addE
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem addE' {f : α → ℕ} {g h : α → List ℕ}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encNat))
    (hh : ComputableInPolyTime h input (encList encNat)) :
    ComputableInPolyTime (fun a => addE (f a) (g a) (h a)) input (encList encNat) :=
  addE_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem shift_polytime :
    ComputableInPolyTime (fun x : ℕ × List ℕ × RawPoly => shift x.1 x.2.1 x.2.2)
    (encPair encUnary (encPair (encList encNat) encRaw)) encRaw := by
  unfold shift
  exact mapWithInput (by fun_prop) (by fun_prop)

@[fun_prop]
theorem shift' {f : α → ℕ} {g : α → List ℕ} {h : α → RawPoly}
    (hf : ComputableInPolyTime f input encUnary)
    (hg : ComputableInPolyTime g input (encList encNat))
    (hh : ComputableInPolyTime h input encRaw) :
    ComputableInPolyTime (fun a => shift (f a) (g a) (h a)) input encRaw :=
  shift_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem prodTerm_polytime : ComputableInPolyTime (fun x : ℕ × List (List ℕ × ℚ) => prodTerm x.1 x.2)
    (encPair encUnary encRaw) encTerm := by
  unfold prodTerm sumE
  have h1 : ComputableInPolyTime (fun x : ℕ × List (List ℕ × ℚ) =>
      (List.range x.1).map fun i => (x.2.map fun t => t.1.getD i 0).sum)
      (encPair encUnary encRaw) (encList encNat) := by
    refine mapWithInput (by fun_prop) ?_
    have : ComputableInPolyTime (fun p : (ℕ × List (List ℕ × ℚ)) × ℕ =>
        p.1.2.map fun t => t.1.getD p.2 0) (encPair (encPair encUnary encRaw) encUnary)
        (encList encNat) :=
      mapWithInput (by fun_prop) (by fun_prop)
    exact .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp this.tidy)
  have h2 : ComputableInPolyTime (fun x : ℕ × List (List ℕ × ℚ) => (x.2.map Prod.snd).prod)
      (encPair encUnary encRaw) encRat := by fun_prop
  exact h1.prod h2

theorem sectStep_polytime (e : α ↪ List Bool) :
    ComputableInPolyTime (fun p : (ℕ × List (List α)) × List α => sectStep p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary (encList (encList e))) (encList e)) (encList (encList e)) := by
  unfold sectStep
  have h : ComputableInPolyTime (fun p : (ℕ × List (List α)) × List α =>
      p.1.2.flatMap fun s => p.2.map fun a => s ++ [a])
      (encPair (encPair encUnary (encList (encList e))) (encList e)) (encList (encList e)) :=
    flatMapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))
  fun_prop

/-- **The budgeted sections run in polynomial time**: at most `L + 1` tuples, each of at most
as many elements of the input as there are lists. -/
theorem sectB_polytime (e : α ↪ List Bool) :
    ComputableInPolyTime (fun x : ℕ × List (List α) => sectB x.1 x.2)
      (encPair encUnary (encList (encList e))) (encList (encList e)) := by
  unfold sectB
  set enc := encPair encUnary (encList (encList e))
  -- Every tuple has at most as many elements as lists consumed, each from a consumed list.
  refine (foldlWith_spec (par := fun x : ℕ × List (List α) => x.1) (list := fun x => x.2)
    (init := fun _ => [[]]) (step := sectStep) (by fun_prop) (by fun_prop) (by fun_prop)
    (sectStep_polytime e)
    (fun x consumed state => state.length ≤ x.1 + 1 ∧
      ∀ s ∈ state, s.length ≤ consumed.length ∧ ∀ a ∈ s, ∃ l ∈ consumed, a ∈ l)
    (fun x => by simp) ?_ (size := fun x => ((enc x).length + 1) *
      (2 * ((enc x).length * (2 * (enc x).length + 1)) + 1)) ?_ ?_).1
  · intro x consumed state value _ ⟨hlen, hs⟩
    refine ⟨?_, fun s hs' => ?_⟩
    · rw [sectStep, List.length_take]
      omega
    · obtain ⟨s₀, hs₀, a, ha, rfl⟩ : ∃ s₀ ∈ state, ∃ a ∈ value, s₀ ++ [a] = s := by
        have := List.mem_of_mem_take hs'
        simp only [List.mem_flatMap, List.mem_map] at this
        exact this
      obtain ⟨h1, h2⟩ := hs s₀ hs₀
      refine ⟨by simp; omega, fun b hb => ?_⟩
      rcases List.mem_append.1 hb with hb | hb
      · obtain ⟨l, hl, hbl⟩ := h2 b hb
        exact ⟨l, List.mem_append_left _ hl, hbl⟩
      · rw [List.mem_singleton.1 hb]
        exact ⟨value, List.mem_append_right _ (List.mem_singleton_self value), ha⟩
  · have h := (PolyBounded.self (size := fun x : ℕ × List (List α) => (enc x).length))
    exact (h.add (.const 1)).mul ((PolyBounded.const 2).mul (h.mul ((((PolyBounded.const 2).mul
      h).add (.const 1)))) |>.add (.const 1))
  · intro x consumed state hpre ⟨hlen, hs⟩
    have hx1 : x.1 ≤ (enc x).length := by
      simp only [enc, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hls : (encList (encList e) x.2).length ≤ (enc x).length := by
      simp only [enc, length_encPair]
      omega
    have helem : ∀ a, (∃ l ∈ consumed, a ∈ l) → (e a).length ≤ (enc x).length := by
      rintro a ⟨l, hl, ha⟩
      have hl' : l ∈ x.2 := hpre.subset hl
      exact ((SizedListEncoding.length_elem_le (encA := e) (encL := encList e) l a ha).trans
        (SizedListEncoding.length_elem_le (encA := encList e) (encL := encList (encList e)) x.2 l
          hl')).trans hls
    have hcons : consumed.length ≤ (enc x).length :=
      (hpre.length_le.trans (SizedListEncoding.length_le (encA := encList e)
        (encL := encList (encList e)) x.2)).trans hls
    have htup : ∀ s ∈ state, (encList e s).length ≤ (enc x).length * (2 * (enc x).length + 1) :=
      fun s hs' => (length_encList_le e s fun a ha => helem a ((hs s hs').2 a ha)).trans
        (Nat.mul_le_mul_right _ (((hs s hs').1).trans hcons))
    exact (length_encList_le (encList e) state htup).trans
      (Nat.mul_le_mul_right _ (by omega))

@[fun_prop]
theorem sectB' (e : α ↪ List Bool) {β : Type} {encIn : β ↪ List Bool} {f : β → ℕ}
    {g : β → List (List α)} (hf : ComputableInPolyTime f encIn encUnary)
    (hg : ComputableInPolyTime g encIn (encList (encList e))) :
    ComputableInPolyTime (fun b => sectB (f b) (g b)) encIn (encList (encList e)) :=
  (sectB_polytime e).comp (g := fun b => (f b, g b)) (hf.prod hg)

theorem prodRaw_polytime :
    ComputableInPolyTime (fun x : ℕ × ℕ × List RawPoly => prodRaw x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encUnary (encList encRaw))) encRaw := by
  unfold prodRaw
  have h : ComputableInPolyTime (fun x : ℕ × ℕ × List RawPoly => sectB x.2.1 x.2.2)
      (encPair encUnary (encPair encUnary (encList encRaw))) (encList encRaw) :=
    sectB' encTerm (by fun_prop) (by fun_prop)
  exact mapWithInput h (prodTerm_polytime.comp (g := fun p : (ℕ × ℕ × List RawPoly) ×
    List (List ℕ × ℚ) => (p.1.1, p.2)) (by fun_prop))

@[fun_prop]
theorem prodRaw' {f g : α → ℕ} {h : α → List RawPoly}
    (hf : ComputableInPolyTime f input encUnary) (hg : ComputableInPolyTime g input encUnary)
    (hh : ComputableInPolyTime h input (encList encRaw)) :
    ComputableInPolyTime (fun a => prodRaw (f a) (g a) (h a)) input encRaw :=
  prodRaw_polytime.comp (g := fun a => (f a, g a, h a)) (hf.prod (hg.prod hh))

theorem degCap_polytime :
    ComputableInPolyTime (fun x : ℕ × ℕ × RawPoly => degCap x.1 x.2.1 x.2.2)
      (encPair encUnary (encPair encUnary encRaw)) encUnary := by
  unfold degCap
  have hf : ComputableInPolyTime (fun x : ℕ × ℕ × RawPoly =>
      x.2.2.filter fun t => decide (coeff x.1 x.2.2 (expo x.1 t.1) ≠ 0))
      (encPair encUnary (encPair encUnary encRaw)) encRaw :=
    filterWithInput (by fun_prop) (by fun_prop)
  have hl : ComputableInPolyTime (fun x : ℕ × ℕ × RawPoly =>
      (x.2.2.filter fun t => decide (coeff x.1 x.2.2 (expo x.1 t.1) ≠ 0)).map fun t =>
        min x.2.1 (expo x.1 t.1).sum) (encPair encUnary (encPair encUnary encRaw))
        (encList encUnary) := by
    refine mapWithInput hf ?_
    have : ComputableInPolyTime (fun p : (ℕ × ℕ × RawPoly) × (List ℕ × ℚ) =>
        (expo p.1.1 p.2.1).sum) (encPair (encPair encUnary (encPair encUnary encRaw)) encTerm)
        encNat :=
      .of_tidy (ComputableTidilyInPolyTime.binary_sum.comp (by fun_prop : ComputableInPolyTime
        (fun p : (ℕ × ℕ × RawPoly) × (List ℕ × ℚ) => expo p.1.1 p.2.1) _ _).tidy)
    fun_prop
  refine (foldl_spec (init := fun _ => 0) (step := max) hl (by fun_prop)
    (.of_tidy ComputableTidilyInPolyTime.unary_max)
    (fun x _ state => state ≤ x.2.1) (fun x => Nat.zero_le _) ?_
    (size := fun x => (encPair encUnary (encPair encUnary encRaw) x).length) PolyBounded.self ?_).1
  · intro x consumed state value hpre hs
    have hv : value ∈ (x.2.2.filter fun t => decide (coeff x.1 x.2.2 (expo x.1 t.1) ≠ 0)).map
        fun t => min x.2.1 (expo x.1 t.1).sum := hpre.subset (by simp)
    obtain ⟨t, -, rfl⟩ := List.mem_map.1 hv
    exact max_le hs (min_le_left _ _)
  · intro x consumed state _ hs
    simp only [encUnary_apply, List.length_replicate, length_encPair]
    omega

end PolyTime

end SoS.Poly
