module

public import BMW26.Model
public import Background.SumOfSquares.Solver
public import Background.SumOfSquares.Algorithm.RawPoly
public import Background.SumOfSquares.Approximate

/-!
# The program, as an input of the solver

The degree-`4` sum-of-squares program of [BMW26, Section 6] for a graph on the vertices
`0, …, n - 1` with edge list `E`, as a `SoS.Solver.Problem` (`BMW26.Alg.problemOf`): variables
`f_0, …, f_{n-1}`, degree `4`, and the constraints

* the explicit bound `n - ∑ᵥ f_v² ≥ 0` (which the Boolean constraints imply; the solver needs it),
* `f_v² = 1` for every `v` (as `f_v² - 1 ≥ 0` and `1 - f_v² ≥ 0`),
* `∑ᵥ f_v = 0` (as two inequalities),
* the cut constraint `(2 + δ) · 2|E| - d ∑_{(u,v) ∈ E} (f_u - f_v)² ≥ 0`, which says
  `E_G(f)/p̂ ≤ (2 + δ) n` for the edge density `p̂ = 2|E| / (d n)`.

The objective is `∑_{u,v} Ẽ[f_u f_v]²` (`q₀ = 0`, `qⱼ = f_u f_v`), to minimize: it spreads the
pseudo-distribution over the coordinate cuts.

Also: the edge list of an adjacency table (`BMW26.Alg.edgeList`), the second-moment table of the
solver's output (`BMW26.Alg.momentTable`), and the facts about these the analysis needs.
-/

@[expose] public section

namespace BMW26.Alg

open SoS SoS.Solver MvPolynomial

/-! ### Polynomials as lists of terms -/

/-- The exponent list of the monomial `f_u` over `n` variables. -/
def expo1 (n u : ℕ) : List ℕ := (List.range n).map fun i ↦ if i = u then 1 else 0

/-- The exponent list of the monomial `f_u f_v` over `n` variables. -/
def expo2 (n u v : ℕ) : List ℕ :=
  (List.range n).map fun i ↦ (if i = u then 1 else 0) + (if i = v then 1 else 0)

/-- The explicit bound `n - ∑ᵥ f_v²`. -/
def boundC (n : ℕ) : RawPoly := ([], (n : ℚ)) :: (List.range n).map fun u ↦ (expo2 n u u, -1)

/-- The two Boolean constraints `f_u² - 1` and `1 - f_u²`. -/
def boolC (n u : ℕ) : List RawPoly :=
  [[(expo2 n u u, 1), ([], -1)], [(expo2 n u u, -1), ([], 1)]]

/-- The two balance constraints `∑ᵥ f_v` and `-∑ᵥ f_v`. -/
def balC (n : ℕ) : List RawPoly :=
  [(List.range n).map fun u ↦ (expo1 n u, 1), (List.range n).map fun u ↦ (expo1 n u, -1)]

/-- The cut constraint `(2 + δ) · 2|E| - d ∑_{(u,v) ∈ E} (f_u - f_v)²`. -/
def cutC (n d : ℕ) (δ : ℚ) (E : List (ℕ × ℕ)) : RawPoly :=
  ([], (2 + δ) * 2 * E.length) ::
    E.flatMap fun e ↦ [(expo2 n e.1 e.1, -(d : ℚ)), (expo2 n e.2 e.2, -(d : ℚ)),
      (expo2 n e.1 e.2, 2 * d)]

/-- The objective `∑_{u,v} Ẽ[f_u f_v]²`. -/
def objective (n : ℕ) : RawPoly × List RawPoly :=
  ([], (List.range n).flatMap fun u ↦ (List.range n).map fun v ↦ [(expo2 n u v, 1)])

/-- **The program** for `n` vertices, dimension `d`, slack `δ` and edge list `E`. -/
def problemOf (n d : ℕ) (δ : ℚ) (E : List (ℕ × ℕ)) : Problem :=
  (n, 4, boundC n :: ((List.range n).flatMap (boolC n) ++ balC n ++ [cutC n d δ E]), objective n)

/-- The edges `(u, v)`, `u < v < n`, of the graph with adjacency table `adj` (row by row). -/
def edgeList (n : ℕ) (adj : List Bool) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun u ↦
    ((List.range n).filter fun v ↦ decide (u < v) && adj.getD (u * n + v) false).map fun v ↦ (u, v)

/-- The coefficient of the monomial with exponent list `e` in a raw polynomial over `n` variables:
the sum of the coefficients of the terms whose exponents agree with `e` on `0, …, n - 1`. -/
def coeffAt (n : ℕ) (P : RawPoly) (e : List ℕ) : ℚ :=
  ((P.filter fun t ↦ (List.range n).all fun i ↦ t.1.getD i 0 == e.getD i 0).map Prod.snd).sum

/-- The second moments `Ẽ[f_u f_v]` listed by the solver's output, as a table of rows. -/
def momentTable (n : ℕ) (P : RawPoly) : List (List ℚ) :=
  (List.range n).map fun u ↦ (List.range n).map fun v ↦ coeffAt n P (expo2 n u v)

/-! ### What the analysis needs -/

/-- The cut constraint for a graph on `Fin n`, as a polynomial. -/
noncomputable def cutPolyFin {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (δ : ℚ) :
    MvPolynomial (Fin n) ℚ := by
  classical
  exact C ((2 + δ) * 2 * G.edgeFinset.card) -
    C (d : ℚ) * ∑ u, ∑ v, if u < v ∧ G.Adj u v then (X u - X v) ^ 2 else 0

/-! ### Helpers: list sums and polynomials of lists of terms -/

namespace Prog

theorem sum_range_map {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Fin.sum_univ_castSucc]
    simp

theorem sum_map_filter {α M : Type*} [AddCommMonoid M] (l : List α) (p : α → Bool) (f : α → M) :
    ((l.filter p).map f).sum = (l.map fun x ↦ if p x then f x else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

theorem sum_flatMap {α β M : Type*} [AddCommMonoid M] (l : List α) (g : α → List β)
    (f : β → M) : ((l.flatMap g).map f).sum = (l.map fun a ↦ ((g a).map f).sum).sum := by
  rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
  rfl

theorem toPoly_nil (n : ℕ) : RawPoly.toPoly n [] = 0 := by
  simp [RawPoly.toPoly]

theorem toPoly_cons (n : ℕ) (t : List ℕ × ℚ) (p : RawPoly) :
    RawPoly.toPoly n (t :: p) = C t.2 * ∏ i : Fin n, X i ^ t.1.getD i 0 + RawPoly.toPoly n p := by
  simp [RawPoly.toPoly]

theorem toPoly_append (n : ℕ) (p q : RawPoly) :
    RawPoly.toPoly n (p ++ q) = RawPoly.toPoly n p + RawPoly.toPoly n q := by
  simp [RawPoly.toPoly, List.sum_append]

theorem toPoly_flatMap {α : Type*} (n : ℕ) (l : List α) (g : α → RawPoly) :
    RawPoly.toPoly n (l.flatMap g) = (l.map fun a ↦ RawPoly.toPoly n (g a)).sum := by
  induction l with
  | nil => simp [toPoly_nil]
  | cons a l ih => rw [List.flatMap_cons, toPoly_append, ih, List.map_cons, List.sum_cons]

theorem toPoly_map {α : Type*} (n : ℕ) (l : List α) (g : α → List ℕ × ℚ) :
    RawPoly.toPoly n (l.map g) =
      (l.map fun a ↦ C (g a).2 * ∏ i : Fin n, X i ^ (g a).1.getD i 0).sum := by
  simp only [RawPoly.toPoly, List.map_map]
  rfl

theorem prod_pow_nil (n : ℕ) :
    ∏ i : Fin n, (X i : MvPolynomial (Fin n) ℚ) ^ ([] : List ℕ).getD i 0 = 1 := by
  simp

theorem prod_pow_ite {n u : ℕ} (hu : u < n) :
    ∏ i : Fin n, (X i : MvPolynomial (Fin n) ℚ) ^ (if (i : ℕ) = u then 1 else 0) =
      X ⟨u, hu⟩ := by
  rw [Finset.prod_eq_single ⟨u, hu⟩
    (fun b _ hb ↦ by
      have : (b : ℕ) ≠ u := fun h ↦ hb (Fin.ext h)
      simp [this]) (by simp)]
  simp

theorem getD_expo1 {n u i : ℕ} (hi : i < n) : (expo1 n u).getD i 0 = if i = u then 1 else 0 := by
  simp [expo1, List.getD_eq_getElem?_getD, hi]

theorem getD_expo2 {n u v i : ℕ} (hi : i < n) :
    (expo2 n u v).getD i 0 = (if i = u then 1 else 0) + (if i = v then 1 else 0) := by
  simp [expo2, List.getD_eq_getElem?_getD, hi]

theorem length_expo2 (n u v : ℕ) : (expo2 n u v).length = n := by
  simp [expo2]

theorem prod_expo1 {n u : ℕ} (hu : u < n) :
    ∏ i : Fin n, (X i : MvPolynomial (Fin n) ℚ) ^ (expo1 n u).getD i 0 = X ⟨u, hu⟩ := by
  rw [← prod_pow_ite hu]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [getD_expo1 i.2]

theorem prod_expo2 {n u v : ℕ} (hu : u < n) (hv : v < n) :
    ∏ i : Fin n, (X i : MvPolynomial (Fin n) ℚ) ^ (expo2 n u v).getD i 0 =
      X ⟨u, hu⟩ * X ⟨v, hv⟩ := by
  rw [← prod_pow_ite hu, ← prod_pow_ite hv, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [getD_expo2 i.2, pow_add]

/-! ### The edge list -/

theorem getD_adjTable_iff {n : ℕ} (G : SimpleGraph (Fin n)) {u v : ℕ} (hu : u < n)
    (hv : v < n) : (adjTable ⟨n, G⟩).getD (u * n + v) false = true ↔ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  have hk : u * n + v < n * n := by
    calc u * n + v < u * n + n := by omega
      _ = (u + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right _ hu
  have heq : finProdFinEquiv.symm (⟨u * n + v, hk⟩ : Fin (n * n)) = (⟨u, hu⟩, ⟨v, hv⟩) := by
    rw [Equiv.symm_apply_eq]
    ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [List.getD_eq_getElem _ _ (by simpa [adjTable] using hk)]
  simp only [adjTable, List.getElem_ofFn, decide_eq_true_eq]
  rw [heq]

theorem sum_map_edgeList {M : Type*} [AddCommMonoid M] (n : ℕ) (adj : List Bool)
    (g : ℕ × ℕ → M) :
    ((edgeList n adj).map g).sum = ∑ u : Fin n, ∑ v : Fin n,
      if (decide ((u : ℕ) < v) && adj.getD (u * n + v) false) = true then g (u, v) else 0 := by
  rw [edgeList, sum_flatMap, sum_range_map]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [List.map_map, sum_map_filter, sum_range_map]
  rfl

theorem length_edgeList_le (n : ℕ) (adj : List Bool) : (edgeList n adj).length ≤ n * n := by
  rw [edgeList, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ n fun x hx ↦ ?_).trans (by simp)
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hx
  simpa using List.length_filter_le _ (List.range n)

end Prog

open Prog

/-- The edge list of the adjacency table of a graph lists its edges `(u, v)`, `u < v`, each once. -/
theorem edgeList_adjTable {n : ℕ} (G : SimpleGraph (Fin n)) :
    (edgeList n (adjTable ⟨n, G⟩)).Nodup ∧
      ∀ u v : ℕ, (u, v) ∈ edgeList n (adjTable ⟨n, G⟩) ↔
        ∃ (hu : u < n) (hv : v < n), u < v ∧ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  refine ⟨?_, fun u v ↦ ?_⟩
  · rw [edgeList, List.nodup_flatMap]
    refine ⟨fun u _ ↦ (List.nodup_range.filter _).map fun a b h ↦ (Prod.mk.inj h).2, ?_⟩
    refine List.nodup_range.imp fun {a b} hab x hxa hxb ↦ hab ?_
    obtain ⟨a', -, rfl⟩ := List.mem_map.1 hxa
    obtain ⟨b', -, hb⟩ := List.mem_map.1 hxb
    exact (Prod.mk.inj hb).1.symm
  · simp only [edgeList, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, b, ⟨hb, hab, hadj⟩, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨ha, hb, hab, (getD_adjTable_iff G ha hb).1 hadj⟩
    · rintro ⟨hu, hv, huv, hadj⟩
      exact ⟨u, hu, v, ⟨hv, huv, (getD_adjTable_iff G hu hv).2 hadj⟩, rfl⟩

namespace Prog

theorem length_edgeList {n : ℕ} (G : SimpleGraph (Fin n)) [Fintype G.edgeSet] :
    (edgeList n (adjTable ⟨n, G⟩)).length = G.edgeFinset.card := by
  classical
  obtain ⟨hnd, hmem⟩ := edgeList_adjTable G
  rw [← List.toFinset_card_of_nodup hnd]
  have hb : ∀ p ∈ (edgeList n (adjTable ⟨n, G⟩)).toFinset, p.1 < n ∧ p.2 < n := fun p hp ↦ by
    obtain ⟨hu, hv, -⟩ := (hmem p.1 p.2).1 (List.mem_toFinset.1 hp)
    exact ⟨hu, hv⟩
  refine Finset.card_bij (fun p hp ↦ s(⟨p.1, (hb p hp).1⟩, ⟨p.2, (hb p hp).2⟩)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hu, hv, -, hadj⟩ := (hmem p.1 p.2).1 (List.mem_toFinset.1 hp)
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hadj
  · intro p hp q hq h
    obtain ⟨-, -, hp1, -⟩ := (hmem p.1 p.2).1 (List.mem_toFinset.1 hp)
    obtain ⟨-, -, hq1, -⟩ := (hmem q.1 q.2).1 (List.mem_toFinset.1 hq)
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext (congrArg Fin.val h1) (congrArg Fin.val h2)
    · have h1' := congrArg Fin.val h1
      have h2' := congrArg Fin.val h2
      simp only at h1' h2'
      omega
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rcases lt_or_gt_of_ne he.ne with h | h
      · exact ⟨((a : ℕ), (b : ℕ)), List.mem_toFinset.2 ((hmem _ _).2 ⟨a.2, b.2, h, he⟩), rfl⟩
      · exact ⟨((b : ℕ), (a : ℕ)), List.mem_toFinset.2 ((hmem _ _).2 ⟨b.2, a.2, h, he.symm⟩),
          Sym2.eq_swap⟩

theorem toPoly_boundC (n : ℕ) : (boundC n).toPoly n = C (n : ℚ) - ∑ v, X v ^ 2 := by
  rw [boundC, toPoly_cons, toPoly_map, sum_range_map, prod_pow_nil, mul_one, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [prod_expo2 u.2 u.2]
  simp [sq]

theorem toPoly_bool1 {n u : ℕ} (hu : u < n) :
    RawPoly.toPoly n [(expo2 n u u, 1), ([], -1)] = X ⟨u, hu⟩ ^ 2 - 1 := by
  rw [toPoly_cons, toPoly_cons, toPoly_nil, prod_expo2 hu hu, prod_pow_nil]
  simp only [map_one, map_neg, mul_one, add_zero]
  ring

theorem toPoly_bool2 {n u : ℕ} (hu : u < n) :
    RawPoly.toPoly n [(expo2 n u u, -1), ([], 1)] = 1 - X ⟨u, hu⟩ ^ 2 := by
  rw [toPoly_cons, toPoly_cons, toPoly_nil, prod_expo2 hu hu, prod_pow_nil]
  simp only [map_one, map_neg, mul_one, add_zero]
  ring

theorem toPoly_bal1 (n : ℕ) :
    RawPoly.toPoly n ((List.range n).map fun u ↦ (expo1 n u, (1 : ℚ))) = ∑ v, X v := by
  rw [toPoly_map, sum_range_map]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [prod_expo1 u.2]
  simp

theorem toPoly_bal2 (n : ℕ) :
    RawPoly.toPoly n ((List.range n).map fun u ↦ (expo1 n u, (-1 : ℚ))) = -∑ v, X v := by
  rw [toPoly_map, sum_range_map, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [prod_expo1 u.2]
  simp

theorem toPoly_cutTerm {n d u v : ℕ} (hu : u < n) (hv : v < n) :
    RawPoly.toPoly n [(expo2 n u u, -(d : ℚ)), (expo2 n v v, -(d : ℚ)), (expo2 n u v, 2 * d)] =
      -(C (d : ℚ) * (X ⟨u, hu⟩ - X ⟨v, hv⟩) ^ 2) := by
  rw [toPoly_cons, toPoly_cons, toPoly_cons, toPoly_nil, prod_expo2 hu hu, prod_expo2 hv hv,
    prod_expo2 hu hv]
  simp only [map_neg, map_mul, map_ofNat, add_zero]
  ring

theorem toPoly_cutC {n d : ℕ} (δ : ℚ) (G : SimpleGraph (Fin n)) :
    (cutC n d δ (edgeList n (adjTable ⟨n, G⟩))).toPoly n = cutPolyFin G d δ := by
  classical
  rw [cutC, toPoly_cons, toPoly_flatMap, sum_map_edgeList, cutPolyFin, prod_pow_nil, mul_one,
    sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  · rw [length_edgeList]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  have hc : (decide ((u : ℕ) < v) && (adjTable ⟨n, G⟩).getD (u * n + v) false) = true ↔
      u < v ∧ G.Adj u v := by
    rw [Bool.and_eq_true, decide_eq_true_eq, getD_adjTable_iff G u.2 v.2, Fin.lt_def]
  by_cases h : u < v ∧ G.Adj u v
  · simp only [hc.2 h, h, ↓reduceIte, and_self]
    rw [toPoly_cutTerm u.2 v.2]
  · have h' : ¬ (decide ((u : ℕ) < v) && (adjTable ⟨n, G⟩).getD (u * n + v) false) = true :=
      mt hc.1 h
    simp only [h', h, ↓reduceIte, Bool.false_eq_true, mul_zero, neg_zero]

theorem mem_constraints {n d : ℕ} {δ : ℚ} {E : List (ℕ × ℕ)} {p : RawPoly} :
    p ∈ (problemOf n d δ E).2.2.1 ↔ p = boundC n ∨
      (∃ u < n, p = [(expo2 n u u, 1), ([], -1)] ∨ p = [(expo2 n u u, -1), ([], 1)]) ∨
      p = (List.range n).map (fun u ↦ (expo1 n u, (1 : ℚ))) ∨
      p = (List.range n).map (fun u ↦ (expo1 n u, (-1 : ℚ))) ∨ p = cutC n d δ E := by
  simp only [problemOf, boolC, balC, List.mem_cons, List.mem_append, List.mem_flatMap,
    List.mem_range, List.not_mem_nil, or_false, or_assoc]

end Prog

/-- **The constraints of the program**, read as polynomials: each is the explicit bound, a
Boolean constraint, a balance constraint, or the cut constraint, and all of these occur. -/
theorem mem_system_iff {n d : ℕ} (δ : ℚ) (G : SimpleGraph (Fin n)) (f : MvPolynomial (Fin n) ℚ) :
    f ∈ (problemOf n d δ (edgeList n (adjTable ⟨n, G⟩))).system ↔
      f = C (n : ℚ) - ∑ v, X v ^ 2 ∨ (∃ v, f = X v ^ 2 - 1) ∨ (∃ v, f = 1 - X v ^ 2) ∨
        f = ∑ v, X v ∨ f = -∑ v, X v ∨ f = cutPolyFin G d δ := by
  change f ∈ List.map (RawPoly.toPoly n) (problemOf n d δ (edgeList n (adjTable ⟨n, G⟩))).2.2.1 ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases mem_constraints.1 hp with rfl | ⟨u, hu, rfl | rfl⟩ | rfl | rfl | rfl
    · exact Or.inl (toPoly_boundC n)
    · exact Or.inr (Or.inl ⟨⟨u, hu⟩, toPoly_bool1 hu⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨u, hu⟩, toPoly_bool2 hu⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (toPoly_bal1 n))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (toPoly_bal2 n)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (toPoly_cutC δ G)))))
  · rintro (rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | rfl | rfl | rfl)
    · exact ⟨_, mem_constraints.2 (Or.inl rfl), toPoly_boundC n⟩
    · exact ⟨_, mem_constraints.2 (Or.inr (Or.inl ⟨v, v.2, Or.inl rfl⟩)), toPoly_bool1 v.2⟩
    · exact ⟨_, mem_constraints.2 (Or.inr (Or.inl ⟨v, v.2, Or.inr rfl⟩)), toPoly_bool2 v.2⟩
    · exact ⟨_, mem_constraints.2 (Or.inr (Or.inr (Or.inl rfl))), toPoly_bal1 n⟩
    · exact ⟨_, mem_constraints.2 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), toPoly_bal2 n⟩
    · exact ⟨_, mem_constraints.2 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))), toPoly_cutC δ G⟩

/-- The number of constraints. -/
theorem length_system {n d : ℕ} (δ : ℚ) (E : List (ℕ × ℕ)) :
    (problemOf n d δ E).system.length = 2 * n + 4 := by
  simp [Problem.system, problemOf, boolC, balC, List.length_flatMap]
  ring

namespace Prog

theorem objective_aux (n : ℕ) {ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) :
    E (toReal ((objective n).1.toPoly n)) +
      ((objective n).2.map fun q ↦ E (toReal (q.toPoly n)) ^ 2).sum =
      ∑ u : Fin n, ∑ v : Fin n, E (X u * X v) ^ 2 := by
  simp only [objective]
  rw [toPoly_nil, sum_flatMap, sum_range_map]
  simp only [toReal, map_zero, zero_add]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [List.map_map, sum_range_map]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  simp only [Function.comp_apply, toPoly_cons, toPoly_nil, prod_expo2 u.2 v.2, map_one, one_mul,
    add_zero, map_mul, map_X]

end Prog

/-- The objective of the program at a pseudo-expectation. -/
theorem objective_eq {n d : ℕ} (δ : ℚ) (L : List (ℕ × ℕ)) {ℓ : ℕ}
    (E : PseudoExpectation (Fin (problemOf n d δ L).numVars) ℓ) :
    (problemOf n d δ L).objective E = ∑ u : Fin n, ∑ v : Fin n, E (X u * X v) ^ 2 := by
  exact objective_aux n E

/-- **Validity**: the program is valid as soon as some real point satisfies its constraints. -/
theorem valid_of_feasible {n d : ℕ} (δ : ℚ) (G : SimpleGraph (Fin n))
    (y : Fin n → ℝ) (hy : ∀ f ∈ (problemOf n d δ (edgeList n (adjTable ⟨n, G⟩))).system,
      0 ≤ eval y (toReal f)) :
    (problemOf n d δ (edgeList n (adjTable ⟨n, G⟩))).Valid := by
  refine ⟨⟨2, rfl⟩, show 2 ≤ 4 by norm_num, ?_,
    ⟨(n : ℚ), (mem_system_iff δ G _).2 (Or.inl rfl)⟩, y, hy⟩
  intro q hq
  change q ∈ (objective n).1 :: (objective n).2 at hq
  change (q.toPoly n).totalDegree ≤ 4
  rcases List.mem_cons.1 hq with rfl | hq
  · simp [objective, toPoly_nil]
  · simp only [objective, List.mem_flatMap, List.mem_map, List.mem_range] at hq
    obtain ⟨u, hu, v, hv, rfl⟩ := hq
    rw [toPoly_cons, toPoly_nil, prod_expo2 hu hv, map_one, one_mul, add_zero]
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_X])

namespace Prog

theorem expo_eq_iff {n : ℕ} {e m : List ℕ} (hm : m.length = n) :
    Poly.expo n e = m ↔ ∀ i < n, e.getD i 0 = m.getD i 0 := by
  constructor
  · rintro rfl i hi
    rw [Poly.getD_expo _ hi]
  · intro h
    refine List.ext_getElem (by simp [hm]) fun i h1 h2 ↦ ?_
    have hi : i < n := by simpa using h1
    have := h i hi
    rw [← Poly.getD_expo e hi, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    exact this

end Prog

/-- The entries of the moment table are the coefficients of the monomials `f_u f_v`. -/
theorem entry_momentTable {n : ℕ} (P : RawPoly) (u v : Fin n) :
    ((momentTable n P).getD u []).getD v 0 =
      (P.toPoly n).coeff (Finsupp.single u 1 + Finsupp.single v 1) := by
  have hm : ((momentTable n P).getD u []).getD v 0 = coeffAt n P (expo2 n u v) := by
    simp [momentTable, List.getD_eq_getElem?_getD]
  have hs : Finsupp.single u 1 + Finsupp.single v 1 = Mono.toFinsupp n (expo2 n u v) := by
    ext i
    rw [Finsupp.add_apply, Mono.toFinsupp_apply, getD_expo2 i.2]
    simp [Finsupp.single_apply, Fin.ext_iff, eq_comm]
  rw [hm, hs, Poly.coeff_toPoly P (length_expo2 n u v), Poly.coeff, coeffAt]
  congr 2
  refine List.filter_congr fun t _ ↦ ?_
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff, expo_eq_iff (length_expo2 n u v)]
  simp [List.mem_range]

namespace Prog

theorem coeffNorm_toReal_toPoly_le (n : ℕ) (p : RawPoly) :
    coeffNorm (toReal (p.toPoly n)) ≤ (p.map fun t ↦ |(t.2 : ℝ)|).sum := by
  induction p with
  | nil => simp [toPoly_nil, toReal]
  | cons t p ih =>
    rw [toPoly_cons, List.map_cons, List.sum_cons]
    simp only [toReal, map_add] at ih ⊢
    refine (coeffNorm_add_le _ _).trans (add_le_add ?_ ih)
    rw [Poly.term_eq_monomial, map_monomial, coeffNorm_monomial]
    simp

theorem sum_abs_le {p : RawPoly} {M : ℝ} (h : ∀ t ∈ p, |(t.2 : ℝ)| ≤ M) :
    (p.map fun t ↦ |(t.2 : ℝ)|).sum ≤ p.length * M := by
  have := List.sum_le_length_nsmul (p.map fun t ↦ |(t.2 : ℝ)|) M fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact h t ht
  simpa [nsmul_eq_mul] using this

theorem sum_abs_cutC_le {n d : ℕ} (hd : d ≤ n) {δ : ℚ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (adj : List Bool) :
    ((cutC n d δ (edgeList n adj)).map fun t ↦ |(t.2 : ℝ)|).sum ≤
      6 * ((n : ℝ) * n) + 6 * ((n : ℝ) * n) * n := by
  set E := edgeList n adj
  have hE : (E.length : ℝ) ≤ (n : ℝ) * n := by exact_mod_cast length_edgeList_le n adj
  have hδ' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hδ0 : (0 : ℝ) ≤ δ := by exact_mod_cast hδ
  have hdn : (d : ℝ) ≤ n := by exact_mod_cast hd
  rw [cutC, List.map_cons, List.sum_cons]
  have h1 : |((((2 + δ) * 2 * E.length : ℚ)) : ℝ)| ≤ 6 * ((n : ℝ) * n) := by
    push_cast
    rw [abs_of_nonneg (by positivity)]
    nlinarith [(Nat.cast_nonneg E.length : (0 : ℝ) ≤ E.length)]
  have hlen : (E.flatMap fun e ↦ [(expo2 n e.1 e.1, -(d : ℚ)), (expo2 n e.2 e.2, -(d : ℚ)),
      (expo2 n e.1 e.2, 2 * (d : ℚ))]).length = 3 * E.length := by
    simp [List.length_flatMap, mul_comm]
  have h2 := sum_abs_le (M := 2 * (n : ℝ)) (p := E.flatMap fun e ↦
    [(expo2 n e.1 e.1, -(d : ℚ)), (expo2 n e.2 e.2, -(d : ℚ)), (expo2 n e.1 e.2, 2 * (d : ℚ))])
    fun t ht ↦ by
      simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ht
      obtain ⟨e, -, rfl | rfl | rfl⟩ := ht <;> simp <;> linarith
  rw [hlen] at h2
  push_cast at h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem one_add_sum_abs_le {n d : ℕ} (hd : d ≤ n) {δ : ℚ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {adj : List Bool} {p : RawPoly} (hp : p ∈ (problemOf n d δ (edgeList n adj)).2.2.1) :
    1 + (p.map fun t ↦ |(t.2 : ℝ)|).sum ≤ ((n : ℝ) + 2) ^ 4 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h4 : ((n : ℝ) + 2) ^ 4 = n ^ 4 + 8 * n ^ 3 + 24 * n ^ 2 + 32 * n + 16 := by ring
  have hn3 : (0 : ℝ) ≤ n ^ 3 := pow_nonneg hn 3
  have hn4 : (0 : ℝ) ≤ n ^ 4 := pow_nonneg hn 4
  rw [h4]
  rcases mem_constraints.1 hp with rfl | ⟨u, -, rfl | rfl⟩ | rfl | rfl | rfl
  · rw [boundC, List.map_cons, List.sum_cons]
    have := sum_abs_le (M := 1) (p := (List.range n).map fun u ↦ (expo2 n u u, (-1 : ℚ)))
      fun t ht ↦ by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
        simp
    simp only [List.length_map, List.length_range, mul_one] at this
    simp only [Rat.cast_natCast, abs_of_nonneg hn]
    nlinarith
  · simp
    nlinarith
  · simp
    nlinarith
  · have := sum_abs_le (M := 1) (p := (List.range n).map fun u ↦ (expo1 n u, (1 : ℚ)))
      fun t ht ↦ by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
        simp
    simp only [List.length_map, List.length_range, mul_one] at this
    nlinarith
  · have := sum_abs_le (M := 1) (p := (List.range n).map fun u ↦ (expo1 n u, (-1 : ℚ)))
      fun t ht ↦ by
        obtain ⟨u, -, rfl⟩ := List.mem_map.1 ht
        simp
    simp only [List.length_map, List.length_range, mul_one] at this
    nlinarith
  · have := sum_abs_cutC_le hd hδ hδ1 adj
    nlinarith

end Prog

end BMW26.Alg
