module

public import BKS23.Biclique
public import Background.SumOfSquares.Solver
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The clique program

The sum-of-squares program of [BKS23, Algorithm 5.2], as an input of the solver
(`SoS.Solver.Problem`): variables `w₀, …, wₙ₋₁`, degree `ℓ`, and the constraints

* the explicit bound `k - ∑ᵢ wᵢ² ≥ 0` (which the others imply; the solver needs it written),
* `wᵢ² = wᵢ`, `∑ᵢ wᵢ = k`, and `wᵢ wⱼ = 0` for the listed non-edges `{i, j}`,

each equality as two inequalities. The objective is `∑ᵢ Ẽ[wᵢ]²` (`q₀ = 0`, `qᵢ = wᵢ`).

* `BKS23.Clique.problem n k ℓ L`: the problem, for a list `L` of non-edges.
* `BKS23.Clique.axioms`: its real system contains the biclique axioms of every bipartite graph
  between a set `U` and its complement that contains the edges of `G` across (so the
  certificates of `BKS23/Certificate.lean` are proofs from it).
* `BKS23.Clique.valid`: the problem is valid when `G` has a `k`-clique (the planted point
  satisfies the constraints) and `ℓ` is even and at least `2`.
* `BKS23.Clique.coeffNorm_le`: every constraint has `‖·‖₂ ≤ n + k + 2`.

Polynomials are lists of terms with exponent lists over `0, …, n-1` (`SoS.Solver.RawPoly`).
-/

@[expose] public section

namespace BKS23.Clique

open SoS SoS.Solver MvPolynomial Finset

/-! ### Raw polynomials -/

/-- The exponents of `xᵢ^a`. -/
def single (n : ℕ) (i : Fin n) (a : ℕ) : List ℕ :=
  (List.finRange n).map fun j ↦ if j = i then a else 0

/-- The exponents of `xᵢ xⱼ`, for vertex numbers `i ≠ j`. -/
def pair (n i j : ℕ) : List ℕ :=
  (List.finRange n).map fun l : Fin n ↦ if (l : ℕ) = i ∨ (l : ℕ) = j then 1 else 0

/-- The negation of a polynomial. -/
def neg (p : RawPoly) : RawPoly := p.map fun t ↦ (t.1, -t.2)

/-- `xᵢ² - xᵢ`. -/
def boolPoly (n : ℕ) (i : Fin n) : RawPoly := [(single n i 2, 1), (single n i 1, -1)]

/-- `∑ᵢ xᵢ - k`. -/
def cardPoly (n k : ℕ) : RawPoly :=
  (List.finRange n).map (fun i ↦ (single n i 1, 1)) ++ [([], -(k : ℚ))]

/-- `xᵢ xⱼ`. -/
def edgePoly (n i j : ℕ) : RawPoly := [(pair n i j, 1)]

/-- `k - ∑ᵢ xᵢ²`. -/
def boundPoly (n k : ℕ) : RawPoly :=
  ([], (k : ℚ)) :: (List.finRange n).map fun i ↦ (single n i 2, -1)

/-- The constraints, for the non-edges `L`. -/
def constraints (n k : ℕ) (L : List (ℕ × ℕ)) : List RawPoly :=
  boundPoly n k :: ((List.finRange n).flatMap fun i ↦ [boolPoly n i, neg (boolPoly n i)]) ++
    [cardPoly n k, neg (cardPoly n k)] ++
    L.flatMap fun e ↦ [edgePoly n e.1 e.2, neg (edgePoly n e.1 e.2)]

/-- The objective `∑ᵢ Ẽ[wᵢ]²`. -/
def objective (n : ℕ) : RawPoly × List RawPoly :=
  ([], (List.finRange n).map fun i ↦ [(single n i 1, 1)])

/-- **The clique program** for `n` vertices, clique size `k`, degree `ℓ` and non-edges `L`. -/
def problem (n k ℓ : ℕ) (L : List (ℕ × ℕ)) : Problem :=
  (n, ℓ, constraints n k L, objective n)

/-! ### The polynomials -/

section Poly

variable {n : ℕ}

theorem toPoly_nil : RawPoly.toPoly n [] = 0 := by simp [RawPoly.toPoly]

theorem toPoly_cons (t : List ℕ × ℚ) (p : RawPoly) :
    RawPoly.toPoly n (t :: p) = C t.2 * (∏ i : Fin n, X i ^ t.1.getD i 0) + RawPoly.toPoly n p := by
  simp [RawPoly.toPoly]

theorem toPoly_append (p q : RawPoly) :
    RawPoly.toPoly n (p ++ q) = RawPoly.toPoly n p + RawPoly.toPoly n q := by
  simp [RawPoly.toPoly]

theorem toPoly_neg (p : RawPoly) : RawPoly.toPoly n (neg p) = -RawPoly.toPoly n p := by
  induction p with
  | nil => simp [neg, toPoly_nil]
  | cons t p ih =>
    rw [neg, List.map_cons, toPoly_cons, ← neg, ih, toPoly_cons, map_neg]
    ring

theorem getD_finRange_map (f : Fin n → ℕ) (j : Fin n) :
    ((List.finRange n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD]

theorem prod_singleExp (i : Fin n) (a : ℕ) :
    ∏ j : Fin n, (X j : MvPolynomial (Fin n) ℚ) ^ (single n i a).getD j 0 = X i ^ a := by
  simp only [single, getD_finRange_map]
  rw [prod_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
  simp

theorem prod_nilExp :
    ∏ j : Fin n, (X j : MvPolynomial (Fin n) ℚ) ^ ([] : List ℕ).getD j 0 = 1 := by
  simp

theorem prod_pairExp {i j : Fin n} (hij : i ≠ j) :
    ∏ l : Fin n, (X l : MvPolynomial (Fin n) ℚ) ^ (pair n i j).getD l 0 = X i * X j := by
  have h : ∀ l : Fin n, (pair n i j).getD l 0 = if l = i ∨ l = j then 1 else 0 := fun l ↦ by
    rw [pair, getD_finRange_map]
    simp only [Fin.val_inj]
  simp_rw [h]
  rw [← prod_mul_prod_compl {i, j}, Finset.prod_pair hij, prod_eq_one fun l hl ↦ ?_]
  · simp
  · have : ¬ (l = i ∨ l = j) := by simpa [not_or] using hl
    simp [this]

theorem toPoly_unit (i : Fin n) : RawPoly.toPoly n [(single n i 1, 1)] = X i := by
  rw [toPoly_cons, prod_singleExp, toPoly_nil]
  simp

theorem toPoly_boolPoly (i : Fin n) : RawPoly.toPoly n (boolPoly n i) = X i ^ 2 - X i := by
  simp only [boolPoly, toPoly_cons, prod_singleExp, toPoly_nil]
  simp only [map_one, one_mul, pow_one, map_neg, neg_mul, add_zero]
  ring

theorem toPoly_cardPoly (k : ℕ) : RawPoly.toPoly n (cardPoly n k) = ∑ i, X i - C (k : ℚ) := by
  rw [cardPoly, toPoly_append, toPoly_cons, prod_nilExp, toPoly_nil]
  simp only [RawPoly.toPoly, List.map_map, Function.comp_def, prod_singleExp, map_one, one_mul,
    pow_one, mul_one, map_neg, add_zero]
  rw [← Fin.sum_univ_def]
  ring

theorem toPoly_edgePoly {i j : Fin n} (hij : i ≠ j) :
    RawPoly.toPoly n (edgePoly n i j) = X i * X j := by
  rw [edgePoly, toPoly_cons, prod_pairExp hij, toPoly_nil]
  simp

theorem toPoly_boundPoly (k : ℕ) :
    RawPoly.toPoly n (boundPoly n k) = C (k : ℚ) - ∑ i, X i ^ 2 := by
  rw [boundPoly, toPoly_cons, prod_nilExp]
  simp only [RawPoly.toPoly, List.map_map, Function.comp_def, prod_singleExp, map_neg, map_one,
    neg_mul, one_mul, mul_one]
  rw [← Fin.sum_univ_def, Finset.sum_neg_distrib]
  ring

end Poly

/-! ### The real system and the biclique axioms -/

variable {n k : ℕ} {L : List (ℕ × ℕ)}

/-- The constraints as real polynomials. -/
noncomputable abbrev realSystem (n k ℓ : ℕ) (L : List (ℕ × ℕ)) : System (Fin n) ℝ :=
  (problem n k ℓ L).system.map toReal

theorem mem_realSystem {ℓ : ℕ} {r : RawPoly} (hr : r ∈ constraints n k L) :
    toReal (RawPoly.toPoly n r) ∈ realSystem n k ℓ L := by
  simp only [realSystem, Problem.system, problem, List.map_map, List.mem_map, Function.comp_apply]
  exact ⟨r, hr, rfl⟩

theorem hasEq_of_mem {ℓ : ℕ} {r : RawPoly} (h₁ : r ∈ constraints n k L)
    (h₂ : neg r ∈ constraints n k L) :
    HasEq (realSystem n k ℓ L) (toReal (RawPoly.toPoly n r)) :=
  ⟨mem_realSystem h₁, by simpa [toPoly_neg, toReal, map_neg] using mem_realSystem (ℓ := ℓ) h₂⟩

theorem boolPoly_mem (i : Fin n) : boolPoly n i ∈ constraints n k L :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨i, List.mem_finRange i, by simp⟩)))

theorem neg_boolPoly_mem (i : Fin n) : neg (boolPoly n i) ∈ constraints n k L :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨i, List.mem_finRange i, by simp⟩)))

theorem cardPoly_mem : cardPoly n k ∈ constraints n k L :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))

theorem neg_cardPoly_mem : neg (cardPoly n k) ∈ constraints n k L :=
  List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))

theorem boundPoly_mem : boundPoly n k ∈ constraints n k L := List.mem_cons_self

theorem edgePoly_mem {e : ℕ × ℕ} (he : e ∈ L) : edgePoly n e.1 e.2 ∈ constraints n k L :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, by simp⟩))

theorem neg_edgePoly_mem {e : ℕ × ℕ} (he : e ∈ L) :
    neg (edgePoly n e.1 e.2) ∈ constraints n k L :=
  List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨e, he, by simp⟩))

theorem mem_constraints {r : RawPoly} :
    r ∈ constraints n k L ↔ r = boundPoly n k ∨ (∃ i, r = boolPoly n i) ∨
      (∃ i, r = neg (boolPoly n i)) ∨ r = cardPoly n k ∨ r = neg (cardPoly n k) ∨
      (∃ e ∈ L, r = edgePoly n e.1 e.2) ∨ (∃ e ∈ L, r = neg (edgePoly n e.1 e.2)) := by
  constructor
  · intro h
    simp only [constraints, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_finRange,
      true_and, List.not_mem_nil, or_false] at h
    rcases h with ((h | ⟨i, h | h⟩) | h | h) | ⟨e, he, h | h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨i, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨i, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, h⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, h⟩)))))
  · rintro (rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact boundPoly_mem
    · exact boolPoly_mem i
    · exact neg_boolPoly_mem i
    · exact cardPoly_mem
    · exact neg_cardPoly_mem
    · exact edgePoly_mem he
    · exact neg_edgePoly_mem he

/-- `L` lists every non-edge `{u, v}` of `G`, as `(u, v)` with `u < v`. -/
def ListsNonEdges (G : SimpleGraph (Fin n)) (L : List (ℕ × ℕ)) : Prop :=
  ∀ u v : Fin n, u < v → ¬ G.Adj u v → ((u : ℕ), (v : ℕ)) ∈ L

/-- **The clique program contains the biclique axioms** of every bipartite graph `adj` between
`U` and its complement that contains the edges of `G` across. -/
theorem axioms {ℓ : ℕ} {G : SimpleGraph (Fin n)} (hL : ListsNonEdges G L) {U : Finset (Fin n)}
    {adj : Fin n → Fin n → Prop} (hadj : ∀ u ∈ U, ∀ v ∈ Uᶜ, G.Adj u v → adj u v) :
    Biclique.Axioms (realSystem n k ℓ L) U adj k where
  bool i := by
    have := hasEq_of_mem (ℓ := ℓ) (boolPoly_mem (k := k) (L := L) i) (neg_boolPoly_mem i)
    simpa [toPoly_boolPoly, toReal] using this
  card := by
    have := hasEq_of_mem (ℓ := ℓ) (cardPoly_mem (n := n) (k := k) (L := L)) neg_cardPoly_mem
    simpa [toPoly_cardPoly, toReal] using this
  edge u hu v hv huv := by
    have hne : u ≠ v := fun h ↦ (mem_compl.1 hv) (h ▸ hu)
    have hG : ¬ G.Adj u v := fun h ↦ huv (hadj u hu v hv h)
    rcases lt_or_gt_of_ne hne with h | h
    · have := hasEq_of_mem (ℓ := ℓ) (edgePoly_mem (n := n) (k := k) (hL u v h hG))
        (neg_edgePoly_mem (hL u v h hG))
      simpa [toPoly_edgePoly hne, toReal] using this
    · have := hasEq_of_mem (ℓ := ℓ) (edgePoly_mem (n := n) (k := k)
        (hL v u h fun h' ↦ hG h'.symm)) (neg_edgePoly_mem (hL v u h fun h' ↦ hG h'.symm))
      simpa [toPoly_edgePoly hne.symm, toReal, mul_comm] using this

/-! ### Validity: the planted point -/

/-- `L` lists only non-edges of `G`, between distinct vertices. -/
def OnlyNonEdges (G : SimpleGraph (Fin n)) (L : List (ℕ × ℕ)) : Prop :=
  ∀ e ∈ L, ∃ u v : Fin n, (u : ℕ) = e.1 ∧ (v : ℕ) = e.2 ∧ u ≠ v ∧ ¬ G.Adj u v

theorem toReal_neg' (p : MvPolynomial (Fin n) ℚ) : toReal (-p) = -toReal p := map_neg _ _

/-- The indicator of `S`. -/
noncomputable def planted (S : Finset (Fin n)) : Fin n → ℝ := fun i ↦ if i ∈ S then 1 else 0

theorem planted_sq (S : Finset (Fin n)) (i : Fin n) : planted S i ^ 2 = planted S i := by
  unfold planted
  split_ifs <;> norm_num

theorem sum_planted (S : Finset (Fin n)) : ∑ i, planted S i = S.card := by
  simp [planted]

/-- The planted point satisfies every constraint with equality. -/
theorem eval_planted {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} (hS : G.IsNClique k S)
    (hL : OnlyNonEdges G L) {r : RawPoly} (hr : r ∈ constraints n k L) :
    eval (planted S) (toReal (RawPoly.toPoly n r)) = 0 := by
  have hcard : (S.card : ℝ) = k := by exact_mod_cast hS.card_eq
  have hbool : ∀ i, eval (planted S) (toReal (RawPoly.toPoly n (boolPoly n i))) = 0 := fun i ↦ by
    simp [toPoly_boolPoly, toReal, planted_sq]
  have hcardp : eval (planted S) (toReal (RawPoly.toPoly n (cardPoly n k))) = 0 := by
    simp [toPoly_cardPoly, toReal, sum_planted, hcard]
  rcases mem_constraints.1 hr with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl | ⟨e, he, rfl⟩ |
    ⟨e, he, rfl⟩
  · simp [toPoly_boundPoly, toReal, planted_sq, sum_planted, hcard]
  · exact hbool i
  · rw [toPoly_neg, toReal_neg', eval_neg, hbool i, neg_zero]
  · exact hcardp
  · rw [toPoly_neg, toReal_neg', eval_neg, hcardp, neg_zero]
  · obtain ⟨u, v, hu, hv, huv, hG⟩ := hL e he
    have hnot : ¬ (u ∈ S ∧ v ∈ S) := fun ⟨h₁, h₂⟩ ↦ hG (hS.isClique h₁ h₂ huv)
    rw [← hu, ← hv, toPoly_edgePoly huv]
    simp only [toReal, map_mul, map_X, eval_X, planted]
    split_ifs <;> simp_all
  · obtain ⟨u, v, hu, hv, huv, hG⟩ := hL e he
    have hnot : ¬ (u ∈ S ∧ v ∈ S) := fun ⟨h₁, h₂⟩ ↦ hG (hS.isClique h₁ h₂ huv)
    rw [← hu, ← hv, toPoly_neg, toPoly_edgePoly huv]
    simp only [toReal, map_neg, map_mul, map_X, eval_X, planted]
    split_ifs <;> simp_all

/-- **The clique program is valid** when `G` has a `k`-clique and `ℓ` is even and at least `2`. -/
theorem valid {ℓ : ℕ} (hℓ : Even ℓ) (hℓ2 : 2 ≤ ℓ) {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (hS : G.IsNClique k S) (hL : OnlyNonEdges G L) : (problem n k ℓ L).Valid := by
  refine ⟨hℓ, hℓ2, ?_, ⟨k, ?_⟩, planted S, ?_⟩
  · intro q hq
    simp only [problem, objective, List.mem_cons, List.mem_map, List.mem_finRange, true_and] at hq
    change _ ≤ ℓ
    rcases hq with rfl | ⟨i, rfl⟩
    · simp [toPoly_nil]
    · change (RawPoly.toPoly n [(single n i 1, 1)]).totalDegree ≤ ℓ
      rw [toPoly_unit, totalDegree_X]
      omega
  · exact List.mem_map.2 ⟨boundPoly n k, boundPoly_mem, toPoly_boundPoly k⟩
  · intro f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
    exact (eval_planted hS hL hr).ge

/-! ### Sizes of the constraints -/

theorem coeffNorm1_toPoly_le (r : RawPoly) :
    coeffNorm1 (toReal (RawPoly.toPoly n r)) ≤ (r.map fun t ↦ |(t.2 : ℝ)|).sum := by
  induction r with
  | nil => simp [toPoly_nil]
  | cons t r ih =>
    rw [toPoly_cons, toReal_add, List.map_cons, List.sum_cons]
    refine (coeffNorm1_add_le _ _).trans (add_le_add ?_ ih)
    rw [toReal_mul, toReal_prod]
    refine (coeffNorm1_mul_le _ _).trans ?_
    have h1 : coeffNorm1 (toReal (C t.2 : MvPolynomial (Fin n) ℚ)) = |(t.2 : ℝ)| := by
      simp [toReal, coeffNorm1_C]
    have h2 : coeffNorm1 (∏ i : Fin n, toReal ((X i : MvPolynomial (Fin n) ℚ) ^ t.1.getD i 0))
        ≤ 1 := by
      simp only [toReal_pow]
      refine (coeffNorm1_prod_le _ _).trans ?_
      refine (prod_le_prod₀ (g := fun _ ↦ (1 : ℝ)) (fun _ _ ↦ coeffNorm1_nonneg _)
        fun i _ ↦ ?_).trans (by simp)
      refine (coeffNorm1_pow_le _ _).trans ?_
      simp [toReal, coeffNorm1_X]
    rw [h1]
    exact (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)).trans (by rw [mul_one])

theorem sum_abs_neg (r : RawPoly) :
    ((neg r).map fun t ↦ |(t.2 : ℝ)|).sum = (r.map fun t ↦ |(t.2 : ℝ)|).sum := by
  simp [neg, Function.comp_def]

/-- **Every constraint has `‖·‖₂ ≤ n + k + 2`.** -/
theorem coeffNorm_le {r : RawPoly} (hr : r ∈ constraints n k L) :
    coeffNorm (toReal (RawPoly.toPoly n r)) ≤ n + k + 2 := by
  refine (coeffNorm_le_coeffNorm1 _).trans ((coeffNorm1_toPoly_le r).trans ?_)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rcases mem_constraints.1 hr with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ | rfl | rfl | ⟨e, -, rfl⟩ |
    ⟨e, -, rfl⟩
  · simp [boundPoly, List.map_map, Function.comp_def]; linarith
  · simp [boolPoly]; linarith
  · rw [sum_abs_neg]; simp [boolPoly]; linarith
  · simp [cardPoly, List.map_map, Function.comp_def]
  · rw [sum_abs_neg]; simp [cardPoly, List.map_map, Function.comp_def]
  · simp [edgePoly]; linarith
  · rw [sum_abs_neg]; simp [edgePoly]; linarith

theorem length_constraints : (constraints n k L).length = 2 * n + 3 + 2 * L.length := by
  simp [constraints, List.length_flatMap, List.map_const', List.sum_replicate]
  ring

/-! ### The objective -/

/-- The objective of the clique program is `∑ᵢ Ẽ[wᵢ]²`. -/
theorem objective_eq {ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) :
    (problem n k ℓ L).objective E = ∑ i, E (X i) ^ 2 := by
  change E (toReal (RawPoly.toPoly n [])) + (((List.finRange n).map fun i : Fin n ↦
    [(single n i 1, 1)]).map fun q ↦ E (toReal (RawPoly.toPoly n q)) ^ 2).sum = _
  rw [toPoly_nil, toReal_zero, PseudoExpectation.map_zero, zero_add, List.map_map,
    Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun i _ ↦ ?_
  simp only [Function.comp_apply, toPoly_unit]
  simp [toReal]

end BKS23.Clique
