module

public import Background.SumOfSquares.Algorithm.RawPoly

/-!
# Raw polynomials in two blocks of variables

Tools for building the sum-of-squares program of [BS23, Theorem 1.3]
([Program.lean](Program.lean)) as raw polynomials (`SoS.Solver.RawPoly`) and reading off what they
are.

* **Building blocks.** `RawAlg.unitExp n k e` is the exponent vector of `xₖ^e`, and
  `RawAlg.tm u α c` the term `c x^u v^α`; `RawAlg.neg` negates and `RawAlg.smul` scales.
  `SoS.Poly.prodRaw` multiplies, exactly (with no nonemptiness condition) as soon as the budget
  covers the product of the lengths (`RawAlg.toPoly_prodRaw'`). Every term of a product is the
  product of one term of each factor (`RawAlg.mem_prodRaw`).
* **Two blocks.** A raw polynomial `F` in `n + d` variables is read as a polynomial in program
  variables `x₀, …, xₙ₋₁` and auxiliary variables `v₀, …, v_{d-1}` (the last `d`). The `v`-part
  of an exponent vector is `RawAlg.vpart n d e`, and `RawAlg.coeffV n d F γ` keeps the terms whose
  `v`-part is `γ`: as a polynomial in `x`, it is the coefficient of `v^γ` in `F`.
* **The coefficient identity** (`RawAlg.aeval_append_eq_sum_coeffV`). If every `v`-part of a term
  of `F` lies in a duplicate-free list `Γ`, then substituting `ψ` for `x` and `φ` for `v`,
  `F(ψ, φ) = ∑_{γ ∈ Γ} φ^γ (coeffV F γ)(ψ)`, in every commutative `ℚ`-algebra. Its pointwise form
  (`RawAlg.eval_coeffV`): at a real point `y`, `(coeffV F γ)(y)` is the coefficient of `v^γ` in
  `F(y, v)`.
* **Degrees.** `RawAlg.udeg n e` is the degree of an exponent vector in the first `n` variables; a
  raw polynomial whose terms all have `udeg ≤ D` has total degree at most `D`
  (`RawAlg.totalDegree_toPoly_le`). Both `udeg` and the `v`-degree are additive over the terms of a
  product (`RawAlg.udeg_prodTerm`, `RawAlg.sum_vpart_prodTerm`).
* **Coefficients in one block** (`RawAlg.sum_coeff_mul_powE`): `∑_{γ ∈ Γ} coeff(p, γ) φ^γ = p(φ)`
  when `Γ` covers the exponent vectors of the terms of `p`.
-/

@[expose] public section

namespace BS23.SmallRadius.RawAlg

open MvPolynomial SoS SoS.Solver SoS.Poly

/-! ### Lists -/

theorem sum_range_map {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ i : Fin n, g i := by
  rw [← List.map_coe_finRange_eq_range, List.map_map, Fin.sum_univ_def]
  rfl

theorem list_sum_comm {α β M : Type*} [AddCommMonoid M] (l₁ : List α) (l₂ : List β)
    (f : α → β → M) :
    (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih => simp [List.sum_map_add, ih]

theorem sum_map_le {α : Type*} (l : List α) (f : α → ℕ) {D : ℕ} (h : ∀ x ∈ l, f x ≤ D) :
    (l.map f).sum ≤ l.length * D := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := h a List.mem_cons_self
    omega

/-- **Regrouping a sum by keys**: summing, over the keys `γ ∈ Γ`, the terms with key `γ` is
summing over all terms, when every key lies in the duplicate-free list `Γ`. -/
theorem sum_map_sum_filter {α β M : Type*} [AddCommMonoid M] [DecidableEq β] {Γ : List β}
    (hΓ : Γ.Nodup) (key : α → β) (g : β → α → M) :
    ∀ F : List α, (∀ t ∈ F, key t ∈ Γ) →
      (Γ.map fun γ => ((F.filter fun t => key t = γ).map (g γ)).sum).sum =
        (F.map fun t => g (key t) t).sum
  | [], _ => by simp
  | t :: F, hF => by
    have ih := sum_map_sum_filter hΓ key g F fun t' ht' => hF t' (List.mem_cons_of_mem _ ht')
    have h1 : ∀ γ, ((List.filter (fun t' => decide (key t' = γ)) (t :: F)).map (g γ)).sum =
        (if key t = γ then g γ t else 0) + ((F.filter fun t' => key t' = γ).map (g γ)).sum := by
      intro γ
      rw [List.filter_cons]
      by_cases h : key t = γ
      · simp [h]
      · simp [h]
    simp only [h1, List.sum_map_add, ih, List.map_cons, List.sum_cons]
    congr 1
    rw [← List.sum_toFinset _ hΓ, Finset.sum_ite_eq]
    simp [hF t List.mem_cons_self]

/-! ### Terms -/

theorem toPoly_nil (n : ℕ) : RawPoly.toPoly n [] = 0 := by simp [RawPoly.toPoly]

theorem toPoly_cons (n : ℕ) (t : List ℕ × ℚ) (p : RawPoly) :
    RawPoly.toPoly n (t :: p) = termPoly n t + p.toPoly n := by
  rw [toPoly_eq_sum', toPoly_eq_sum', List.map_cons, List.sum_cons]

theorem toPoly_flatMap {α : Type*} (n : ℕ) (l : List α) (g : α → RawPoly) :
    RawPoly.toPoly n (l.flatMap g) = (l.map fun a => (g a).toPoly n).sum := by
  induction l with
  | nil => simp [RawPoly.toPoly]
  | cons a l ih => rw [List.flatMap_cons, toPoly_append, ih, List.map_cons, List.sum_cons]

theorem toPoly_map {α : Type*} (n : ℕ) (l : List α) (f : α → List ℕ × ℚ) :
    RawPoly.toPoly n (l.map f) = (l.map fun a => termPoly n (f a)).sum := by
  rw [toPoly_eq_sum', List.map_map]
  rfl

/-- The negation of a raw polynomial. -/
def neg (p : RawPoly) : RawPoly := p.map fun t => (t.1, -t.2)

theorem toPoly_neg (n : ℕ) (p : RawPoly) : (neg p).toPoly n = -p.toPoly n := by
  induction p with
  | nil => simp [neg, toPoly_nil]
  | cons t p ih =>
    rw [neg, List.map_cons, toPoly_cons, ← neg, ih, toPoly_cons, neg_add]
    simp [termPoly]

/-- All coefficients multiplied by `c`. -/
def smul (c : ℚ) (p : RawPoly) : RawPoly := p.map fun t => (t.1, c * t.2)

theorem toPoly_smul (n : ℕ) (c : ℚ) (p : RawPoly) : (smul c p).toPoly n = C c * p.toPoly n := by
  rw [toPoly_eq_sum', toPoly_eq_sum', smul, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [termPoly, C_mul_monomial]

theorem mem_smul {c : ℚ} {p : RawPoly} {t : List ℕ × ℚ} (ht : t ∈ smul c p) :
    ∃ t' ∈ p, t.1 = t'.1 := by
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact ⟨t', ht', rfl⟩

theorem mem_neg {p : RawPoly} {t : List ℕ × ℚ} (ht : t ∈ neg p) : ∃ t' ∈ p, t.1 = t'.1 := by
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact ⟨t', ht', rfl⟩

/-- A term with exponents `u` in the first block and `α` in the second: `(u ++ α, c)`. -/
def tm (u α : List ℕ) (c : ℚ) : List ℕ × ℚ := (u ++ α, c)

/-- The exponent vector of `xₖ^e` in `n` variables. -/
def unitExp (n k e : ℕ) : List ℕ := (List.range n).map fun i => if i = k then e else 0

@[simp] theorem length_unitExp (n k e : ℕ) : (unitExp n k e).length = n := by simp [unitExp]

theorem getD_unitExp {n k e i : ℕ} (hi : i < n) :
    (unitExp n k e).getD i 0 = if i = k then e else 0 := by
  simp [unitExp, List.getD_eq_getElem?_getD, hi]

theorem toFinsupp_unitExp {n : ℕ} (k : Fin n) (e : ℕ) :
    Mono.toFinsupp n (unitExp n k e) = Finsupp.single k e := by
  ext i
  rw [Mono.toFinsupp_apply, getD_unitExp i.2, Finsupp.single_apply]
  by_cases h : i = k
  · subst h
    simp
  · have h' : (i : ℕ) ≠ k := fun h' => h (Fin.ext h')
    simp [h', Ne.symm h]

theorem sum_unitExp {n : ℕ} (k : Fin n) (e : ℕ) : (unitExp n k e).sum = e := by
  rw [← Mono.degree_toFinsupp (length_unitExp n k e), toFinsupp_unitExp, Finsupp.degree_single]

theorem toFinsupp_replicate (n : ℕ) : Mono.toFinsupp n (List.replicate n 0) = 0 := by
  ext i
  simp [Mono.toFinsupp_apply, List.getD_eq_getElem?_getD]

theorem toFinsupp_append {n : ℕ} {u : List ℕ} (hu : u.length = n) (α : List ℕ) :
    Mono.toFinsupp n (u ++ α) = Mono.toFinsupp n u := by
  ext i
  rw [Mono.toFinsupp_apply, Mono.toFinsupp_apply, List.getD_append _ _ _ _ (hu ▸ i.2)]

theorem termPoly_append {n : ℕ} {u : List ℕ} (hu : u.length = n) (α : List ℕ) (c : ℚ) :
    termPoly n (u ++ α, c) = termPoly n (u, c) := by
  rw [termPoly, termPoly, toFinsupp_append hu]

theorem termPoly_unitExp {n : ℕ} (k : Fin n) (e : ℕ) (c : ℚ) :
    termPoly n (unitExp n k e, c) = C c * X k ^ e := by
  rw [termPoly, toFinsupp_unitExp, C_mul_X_pow_eq_monomial]

theorem termPoly_replicate (n : ℕ) (c : ℚ) : termPoly n (List.replicate n 0, c) = C c := by
  rw [termPoly, toFinsupp_replicate, ← C_apply]

theorem termPoly_nil (n : ℕ) (c : ℚ) : termPoly n ([], c) = C c := by
  rw [termPoly]
  have : Mono.toFinsupp n [] = 0 := by
    ext i
    simp
  rw [this, ← C_apply]

/-! ### Products -/

section Products

variable {α : Type}

theorem foldl_sectStep_nil (L : ℕ) : ∀ ls : List (List α), ls.foldl (sectStep L) [] = []
  | [] => rfl
  | l :: ls => by
    rw [List.foldl_cons, show sectStep L ([] : List (List α)) l = [] by simp [sectStep]]
    exact foldl_sectStep_nil L ls

theorem foldl_sectStep_eq_nil (L : ℕ) :
    ∀ (ls : List (List α)) (acc : List (List α)), [] ∈ ls → ls.foldl (sectStep L) acc = []
  | [], _, h => by simp at h
  | l :: ls, acc, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with h | h
    · subst h
      rw [show sectStep L acc [] = [] by simp [sectStep]]
      exact foldl_sectStep_nil L ls
    · exact foldl_sectStep_eq_nil L ls _ h

theorem forall₂_foldl_sectStep (L : ℕ) :
    ∀ (ls acc pre : List (List α)), (∀ s ∈ acc, List.Forall₂ (· ∈ ·) s pre) →
      ∀ s ∈ ls.foldl (sectStep L) acc, List.Forall₂ (· ∈ ·) s (pre ++ ls)
  | [], acc, pre, h => by simpa using h
  | l :: ls, acc, pre, h => by
    intro s hs
    rw [List.foldl_cons] at hs
    have := forall₂_foldl_sectStep L ls (sectStep L acc l) (pre ++ [l]) ?_ s hs
    · simpa using this
    · intro s' hs'
      obtain ⟨s₀, hs₀, a, ha, rfl⟩ : ∃ s₀ ∈ acc, ∃ a ∈ l, s₀ ++ [a] = s' := by
        have := List.mem_of_mem_take hs'
        simp only [List.mem_flatMap, List.mem_map] at this
        exact this
      exact List.rel_append (h s₀ hs₀) (List.Forall₂.cons ha List.Forall₂.nil)

/-- Every tuple of the sections takes its `i`-th entry from the `i`-th list. -/
theorem forall₂_of_mem_sectB {L : ℕ} {ls : List (List α)} {s : List α} (hs : s ∈ sectB L ls) :
    List.Forall₂ (· ∈ ·) s ls := by
  simpa using forall₂_foldl_sectStep L ls [[]] [] (by simp) s hs

theorem forall₂_replicate {tup : List α} {f : List α} :
    ∀ {m : ℕ}, List.Forall₂ (· ∈ ·) tup (List.replicate m f) →
      tup.length = m ∧ ∀ t ∈ tup, t ∈ f
  | 0, h => by
    rw [List.replicate_zero, List.forall₂_nil_right_iff] at h
    subst h
    simp
  | m + 1, h => by
    rw [List.replicate_succ, List.forall₂_cons_right_iff] at h
    obtain ⟨a, u', ha, hu', rfl⟩ := h
    obtain ⟨h1, h2⟩ := forall₂_replicate hu'
    refine ⟨by simp [h1], fun t ht => ?_⟩
    rcases List.mem_cons.1 ht with rfl | ht
    · exact ha
    · exact h2 t ht

end Products

/-- Every term of a product is the product of one term of each factor. -/
theorem mem_prodRaw {n L : ℕ} {fs : List RawPoly} {t : List ℕ × ℚ} (ht : t ∈ prodRaw n L fs) :
    ∃ tup, List.Forall₂ (· ∈ ·) tup fs ∧ t = prodTerm n tup := by
  obtain ⟨tup, htup, rfl⟩ := List.mem_map.1 ht
  exact ⟨tup, forall₂_of_mem_sectB htup, rfl⟩

/-- **Products**, exact as soon as the budget covers the product of the lengths (an empty factor
gives the empty product, which is `0` on both sides). -/
theorem toPoly_prodRaw' {n L : ℕ} {fs : List RawPoly} (hL : (fs.map List.length).prod ≤ L) :
    (prodRaw n L fs).toPoly n = (fs.map fun f => f.toPoly n).prod := by
  by_cases h : [] ∈ fs
  · rw [prodRaw, sectB, foldl_sectStep_eq_nil L fs _ h, List.map_nil, toPoly_nil]
    exact (List.prod_eq_zero (List.mem_map.2 ⟨[], h, toPoly_nil n⟩)).symm
  · exact toPoly_prodRaw (fun f hf hf0 => h (hf0 ▸ hf)) hL

theorem toPoly_prodRaw_replicate {n L k : ℕ} {f : RawPoly} (hL : f.length ^ k ≤ L) :
    (prodRaw n L (List.replicate k f)).toPoly n = f.toPoly n ^ k := by
  rw [toPoly_prodRaw' (by rwa [List.map_replicate, List.prod_replicate]), List.map_replicate,
    List.prod_replicate]

theorem getD_sumE {n i : ℕ} (hi : i < n) (tup : List (List ℕ × ℚ)) :
    (sumE n tup).getD i 0 = (tup.map fun t => t.1.getD i 0).sum := by
  simp [sumE, List.getD_eq_getElem?_getD, hi]

/-- Sums of exponents over a set of indices are additive over the terms of a product. -/
theorem sum_getD_sumE {M : ℕ} (I : List ℕ) (hI : ∀ i ∈ I, i < M) (tup : List (List ℕ × ℚ)) :
    (I.map fun i => (sumE M tup).getD i 0).sum =
      (tup.map fun t => (I.map fun i => t.1.getD i 0).sum).sum := by
  rw [List.map_congr_left fun i hi => getD_sumE (hI i hi) tup]
  exact list_sum_comm I tup fun i t => t.1.getD i 0

/-! ### Degrees in the first block -/

/-- The degree of an exponent vector in the first `n` variables. -/
def udeg (n : ℕ) (e : List ℕ) : ℕ := ((List.range n).map fun i => e.getD i 0).sum

theorem udeg_prodTerm {n M : ℕ} (h : n ≤ M) (tup : List (List ℕ × ℚ)) :
    udeg n (prodTerm M tup).1 = (tup.map fun t => udeg n t.1).sum :=
  sum_getD_sumE (List.range n) (fun i hi => by simp at hi; omega) tup

theorem udeg_append {n : ℕ} {u : List ℕ} (hu : u.length = n) (α : List ℕ) :
    udeg n (u ++ α) = udeg n u := by
  unfold udeg
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [List.getD_append _ _ _ _ (by simp at hi; omega)]

theorem udeg_unitExp {n : ℕ} (k : Fin n) (e : ℕ) : udeg n (unitExp n k e) = e := by
  rw [udeg, sum_range_map]
  have : ∀ i : Fin n, (unitExp n k e).getD i 0 = if i = k then e else 0 := fun i => by
    rw [getD_unitExp i.2]
    simp [Fin.val_inj]
  simp_rw [this]
  simp

theorem udeg_replicate (n : ℕ) : udeg n (List.replicate n 0) = 0 := by
  simp [udeg, List.getD_eq_getElem?_getD]

theorem udeg_tm {n : ℕ} (k : Fin n) (e : ℕ) (α : List ℕ) (c : ℚ) :
    udeg n (tm (unitExp n k e) α c).1 = e := by
  rw [tm, udeg_append (length_unitExp n k e), udeg_unitExp]

theorem udeg_tm0 (n : ℕ) (α : List ℕ) (c : ℚ) : udeg n (tm (List.replicate n 0) α c).1 = 0 := by
  rw [tm, udeg_append (List.length_replicate ..), udeg_replicate]

theorem totalDegree_termPoly_le (n : ℕ) (t : List ℕ × ℚ) :
    (termPoly n t).totalDegree ≤ udeg n t.1 := by
  refine (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
  rw [udeg, sum_range_map]
  change (Mono.toFinsupp n t.1).degree = _
  rw [Finsupp.degree_eq_sum]
  simp [Mono.toFinsupp_apply]

/-- **The total degree** is at most the largest `udeg` of a term. -/
theorem totalDegree_toPoly_le {n D : ℕ} {p : RawPoly} (h : ∀ t ∈ p, udeg n t.1 ≤ D) :
    (p.toPoly n).totalDegree ≤ D := by
  induction p with
  | nil => simp [toPoly_nil]
  | cons t p ih =>
    rw [toPoly_cons]
    exact (totalDegree_add _ _).trans (max_le ((totalDegree_termPoly_le n t).trans
      (h t List.mem_cons_self)) (ih fun t' ht' => h t' (List.mem_cons_of_mem _ ht')))

/-! ### Two blocks of variables -/

/-- `φ^e = ∏ₐ φₐ^{eₐ}`. -/
def powE {S : Type*} [CommMonoid S] {d : ℕ} (φ : Fin d → S) (e : List ℕ) : S :=
  ∏ a : Fin d, φ a ^ e.getD a 0

theorem powE_nil {S : Type*} [CommMonoid S] {d : ℕ} (φ : Fin d → S) : powE φ [] = 1 := by
  simp [powE]

theorem powE_unitExp {S : Type*} [CommMonoid S] {d : ℕ} (φ : Fin d → S) (a : Fin d) :
    powE φ (unitExp d a 1) = φ a := by
  simp only [powE]
  rw [Finset.prod_eq_single a (fun b _ hb => by
    have : (b : ℕ) ≠ a := fun h => hb (Fin.ext h)
    rw [getD_unitExp b.2]
    simp [this]) (by simp)]
  rw [getD_unitExp a.2]
  simp

theorem powE_X_eq_monomial {R : Type*} [CommSemiring R] {d : ℕ} (e : List ℕ) :
    powE (X : Fin d → MvPolynomial (Fin d) R) e = monomial (Mono.toFinsupp d e) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp [powE, Mono.toFinsupp_apply]

/-- The exponents of the second block, `v₀, …, v_{d-1}` (the variables `n, …, n + d - 1`). -/
def vpart (n d : ℕ) (e : List ℕ) : List ℕ := (List.range d).map fun a => e.getD (n + a) 0

@[simp] theorem length_vpart (n d : ℕ) (e : List ℕ) : (vpart n d e).length = d := by
  simp [vpart]

theorem getD_vpart {n d a : ℕ} (ha : a < d) (e : List ℕ) :
    (vpart n d e).getD a 0 = e.getD (n + a) 0 := by
  simp [vpart, List.getD_eq_getElem?_getD, ha]

theorem powE_vpart {S : Type*} [CommMonoid S] {n d : ℕ} (φ : Fin d → S) (e : List ℕ) :
    powE φ (vpart n d e) = ∏ a : Fin d, φ a ^ e.getD (n + a) 0 := by
  simp only [powE, getD_vpart (Fin.isLt _)]

theorem powE_vpart_append {S : Type*} [CommMonoid S] {n d : ℕ} (φ : Fin d → S) {u : List ℕ}
    (hu : u.length = n) (α : List ℕ) : powE φ (vpart n d (u ++ α)) = powE φ α := by
  rw [powE_vpart]
  unfold powE
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [List.getD_append_right u α 0 (n + a) (by omega), hu, Nat.add_sub_cancel_left]

theorem powE_expo {S : Type*} [CommMonoid S] {d : ℕ} (φ : Fin d → S) (e : List ℕ) :
    powE φ (expo d e) = powE φ e := by
  unfold powE
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [getD_expo _ a.2]

theorem map_getD_range {d : ℕ} {α : List ℕ} (h : α.length = d) :
    (List.range d).map (fun a => α.getD a 0) = α := by
  subst h
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, h2]

theorem vpart_append {n d : ℕ} {u : List ℕ} (hu : u.length = n) (α : List ℕ) :
    vpart n d (u ++ α) = (List.range d).map fun a => α.getD a 0 := by
  unfold vpart
  refine List.map_congr_left fun a _ => ?_
  rw [List.getD_append_right u α 0 (n + a) (by omega), hu, Nat.add_sub_cancel_left]

theorem vpart_append_of_length {n d : ℕ} {u α : List ℕ} (hu : u.length = n)
    (hα : α.length = d) : vpart n d (u ++ α) = α := by
  rw [vpart_append hu, map_getD_range hα]

theorem sum_vpart_append {n d : ℕ} {u : List ℕ} (hu : u.length = n) (α : List ℕ) :
    (vpart n d (u ++ α)).sum = ∑ a : Fin d, α.getD a 0 := by
  rw [vpart_append hu, sum_range_map]

theorem sum_vpart_prodTerm (n d : ℕ) (tup : List (List ℕ × ℚ)) :
    (vpart n d (prodTerm (n + d) tup).1).sum = (tup.map fun t => (vpart n d t.1).sum).sum := by
  have h := sum_getD_sumE (M := n + d) ((List.range d).map (n + ·)) (fun i hi => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hi
    rw [List.mem_range] at ha
    omega) tup
  simp only [List.map_map, Function.comp_def] at h
  exact h

/-- The terms of `F` whose `v`-exponents are `γ`: the coefficient of `v^γ`, as a polynomial in the
first block. -/
def coeffV (n d : ℕ) (F : RawPoly) (γ : List ℕ) : RawPoly :=
  F.filter fun t => vpart n d t.1 = γ

theorem coeffV_sublist (n d : ℕ) (F : RawPoly) (γ : List ℕ) : coeffV n d F γ ⊆ F :=
  fun _ ht => List.mem_of_mem_filter ht

section Eval

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem aeval_termPoly {n : ℕ} (ψ : Fin n → S) (t : List ℕ × ℚ) :
    aeval ψ (termPoly n t) = algebraMap ℚ S t.2 * ∏ i : Fin n, ψ i ^ t.1.getD i 0 := by
  rw [termPoly, aeval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)]
  simp [Mono.toFinsupp_apply]

/-- A term in two blocks, evaluated: the first block at `ψ`, the second at `φ`. -/
theorem aeval_append_termPoly {n d : ℕ} (ψ : Fin n → S) (φ : Fin d → S) (t : List ℕ × ℚ) :
    aeval (Fin.append ψ φ) (termPoly (n + d) t) =
      aeval ψ (termPoly n t) * powE φ (vpart n d t.1) := by
  rw [aeval_termPoly, aeval_termPoly, Fin.prod_univ_add, powE_vpart]
  simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  ring

theorem aeval_append_toPoly {n d : ℕ} (ψ : Fin n → S) (φ : Fin d → S) (F : RawPoly) :
    aeval (Fin.append ψ φ) (F.toPoly (n + d)) =
      (F.map fun t => aeval ψ (termPoly n t) * powE φ (vpart n d t.1)).sum := by
  rw [toPoly_eq_sum', map_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun t _ => aeval_append_termPoly ψ φ t

/-- `c xₖ^e v^α`, evaluated. -/
theorem aeval_append_tm {n d : ℕ} (ψ : Fin n → S) (φ : Fin d → S) (k : Fin n) (e : ℕ)
    (α : List ℕ) (c : ℚ) :
    aeval (Fin.append ψ φ) (termPoly (n + d) (tm (unitExp n k e) α c)) =
      algebraMap ℚ S c * ψ k ^ e * powE φ α := by
  rw [aeval_append_termPoly, tm, termPoly_append (length_unitExp n k e), termPoly_unitExp,
    powE_vpart_append φ (length_unitExp n k e)]
  simp only [map_mul, map_pow, aeval_C, aeval_X]

/-- `c v^α`, evaluated. -/
theorem aeval_append_tm0 {n d : ℕ} (ψ : Fin n → S) (φ : Fin d → S) (α : List ℕ) (c : ℚ) :
    aeval (Fin.append ψ φ) (termPoly (n + d) (tm (List.replicate n 0) α c)) =
      algebraMap ℚ S c * powE φ α := by
  rw [aeval_append_termPoly, tm, termPoly_append (List.length_replicate ..), termPoly_replicate,
    aeval_C, powE_vpart_append φ (List.length_replicate ..)]

/-- **The coefficient identity.** If every `v`-part of a term of `F` lies in the duplicate-free
list `Γ`, then `F(ψ, φ) = ∑_{γ ∈ Γ} φ^γ (coeffV F γ)(ψ)`. -/
theorem aeval_append_eq_sum_coeffV {n d : ℕ} (ψ : Fin n → S) (φ : Fin d → S)
    {Γ : List (List ℕ)} (hΓ : Γ.Nodup) {F : RawPoly} (hF : ∀ t ∈ F, vpart n d t.1 ∈ Γ) :
    aeval (Fin.append ψ φ) (F.toPoly (n + d)) =
      (Γ.map fun γ => powE φ γ * aeval ψ ((coeffV n d F γ).toPoly n)).sum := by
  rw [aeval_append_toPoly]
  have : ∀ γ, powE φ γ * aeval ψ ((coeffV n d F γ).toPoly n) =
      ((F.filter fun t => vpart n d t.1 = γ).map
        fun t => powE φ γ * aeval ψ (termPoly n t)).sum := by
    intro γ
    rw [coeffV, toPoly_eq_sum', map_list_sum, List.map_map, ← List.sum_map_mul_left]
    rfl
  simp_rw [this]
  rw [sum_map_sum_filter hΓ (fun t => vpart n d t.1)
    (fun γ t => powE φ γ * aeval ψ (termPoly n t)) F hF]
  congr 1
  exact List.map_congr_left fun t _ => mul_comm _ _

/-- **Coefficients in one block**: `∑_{γ ∈ Γ} coeff(p, γ) φ^γ = p(φ)` when every exponent vector
of a term of `p` lies in the duplicate-free list `Γ`. -/
theorem sum_coeff_mul_powE {d : ℕ} (φ : Fin d → S) {Γ : List (List ℕ)} (hΓ : Γ.Nodup)
    {p : RawPoly} (hp : ∀ t ∈ p, expo d t.1 ∈ Γ) :
    (Γ.map fun γ => algebraMap ℚ S (SoS.Poly.coeff d p γ) * powE φ γ).sum =
      aeval φ (p.toPoly d) := by
  have : ∀ γ, algebraMap ℚ S (SoS.Poly.coeff d p γ) * powE φ γ =
      ((p.filter fun t => expo d t.1 = γ).map fun t => algebraMap ℚ S t.2 * powE φ γ).sum := by
    intro γ
    rw [SoS.Poly.coeff, map_list_sum, List.map_map, ← List.sum_map_mul_right]
    rfl
  simp_rw [this]
  rw [sum_map_sum_filter hΓ (fun t => expo d t.1) (fun γ t => algebraMap ℚ S t.2 * powE φ γ) p hp,
    toPoly_eq_sum', map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [Function.comp_apply, aeval_termPoly, powE_expo]
  rfl

end Eval

theorem aeval_X_eq_toReal {σ : Type*} (p : MvPolynomial σ ℚ) :
    aeval (X : σ → MvPolynomial σ ℝ) p = toReal p := by
  induction p using MvPolynomial.induction_on <;> simp_all [toReal]

theorem aeval_C_comp {n d : ℕ} (y : Fin n → ℝ) (p : MvPolynomial (Fin n) ℚ) :
    aeval (fun i => (C (y i) : MvPolynomial (Fin d) ℝ)) p = C (eval y (toReal p)) := by
  induction p using MvPolynomial.induction_on <;> simp_all [toReal]

/-- **The coefficient identity at a point**: `(coeffV F γ)(y)` is the coefficient of `v^γ` in
`F(y, v)`. -/
theorem eval_coeffV {n d : ℕ} (y : Fin n → ℝ) {Γ : List (List ℕ)} (hΓ : Γ.Nodup)
    (hlen : ∀ γ ∈ Γ, γ.length = d) {F : RawPoly} (hF : ∀ t ∈ F, vpart n d t.1 ∈ Γ) {γ : List ℕ}
    (hγ : γ ∈ Γ) :
    eval y (toReal ((coeffV n d F γ).toPoly n)) =
      (aeval (Fin.append (fun i => (C (y i) : MvPolynomial (Fin d) ℝ)) X)
        (F.toPoly (n + d))).coeff (Mono.toFinsupp d γ) := by
  classical
  rw [aeval_append_eq_sum_coeffV _ _ hΓ hF]
  have key : ∀ γ' : List ℕ, powE (X : Fin d → MvPolynomial (Fin d) ℝ) γ' *
      aeval (fun i => (C (y i) : MvPolynomial (Fin d) ℝ)) ((coeffV n d F γ').toPoly n) =
      monomial (Mono.toFinsupp d γ') (eval y (toReal ((coeffV n d F γ').toPoly n))) := by
    intro γ'
    rw [aeval_C_comp, powE_X_eq_monomial, mul_comm, C_mul_monomial, mul_one]
  simp_rw [key]
  rw [← List.sum_toFinset _ hΓ, coeff_sum, Finset.sum_eq_single γ]
  · simp [coeff_monomial]
  · intro γ' hγ' hne
    rw [coeff_monomial, ite_eq_right_iff]
    intro h
    exact absurd (Mono.toFinsupp_inj (hlen γ' (List.mem_toFinset.1 hγ')) (hlen γ hγ) h) hne
  · intro h
    exact absurd (List.mem_toFinset.2 hγ) h

end BS23.SmallRadius.RawAlg
