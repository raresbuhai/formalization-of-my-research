module

public import BGHKLMM26.Ideal
public import BGHKLMM26.Opt
public import Background.SumOfSquares.Algorithm.Correct

/-!
# The SDP, through the sum-of-squares solver

[BGHKLMM26, Section 3]: the Goemans–Williamson SDP with triangle inequalities, as a degree-2
sum-of-squares problem in `n` variables (`BGHKLMM26.SDP.problem`): the constraints `xᵢ² = 1`, the
triangle inequalities `1 - b xᵢxⱼ - b' xᵢxₖ + b b' xⱼxₖ ≥ 0` for distinct `i, j, k`, and the
bound `n - ∑ xᵢ² ≥ 0`, minimizing `-∑ w (1 + b xᵢxⱼ)/2`.

From the solver's guarantee (`SoS.Solver.Correct`), the moments `Mᵢⱼ = Ẽ[xᵢ xⱼ]`
(`BGHKLMM26.SDP.momentsOf`) form a positive semidefinite matrix that satisfies the constraints up
to the solver's accuracy and has value at least `opt - γ`, since every assignment is a competitor
(`BGHKLMM26.SDP.correct_spec`).
-/

@[expose] public section

namespace BGHKLMM26.SDP

open SoS SoS.Solver MvPolynomial GW

/-! ### The problem -/

/-- The exponent vector of `xᵢ xⱼ` (of `xᵢ²` for `i = j`). -/
def pairExp (n i j : ℕ) : List ℕ :=
  (List.range n).map fun l ↦ (if l = i then 1 else 0) + (if l = j then 1 else 0)

/-- The bound `n - ∑ xᵢ² ≥ 0`. -/
def ballC (n : ℕ) : RawPoly := ([], (n : ℚ)) :: (List.range n).map fun i ↦ (pairExp n i i, -1)

/-- `s (xᵢ² - 1) ≥ 0`. -/
def sqC (n i : ℕ) (s : ℚ) : RawPoly := [(pairExp n i i, s), ([], -s)]

/-- The triangle inequality `1 - b xᵢxⱼ - b' xᵢxₖ + b b' xⱼxₖ ≥ 0`. -/
def triC (n i j k : ℕ) (b b' : ℚ) : RawPoly :=
  [([], 1), (pairExp n i j, -b), (pairExp n i k, -b'), (pairExp n j k, b * b')]

/-- The ordered triples of distinct indices below `n`. -/
def triples (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ (List.range n).flatMap fun j ↦ ((List.range n).filter
    fun k ↦ i ≠ j ∧ i ≠ k ∧ j ≠ k).map fun k ↦ (i, j, k)

/-- The constraints. -/
def constraints (n : ℕ) : List RawPoly :=
  ballC n :: ((List.range n).flatMap fun i ↦ [sqC n i 1, sqC n i (-1)]) ++
    (triples n).flatMap fun t ↦ [triC n t.1 t.2.1 t.2.2 1 1, triC n t.1 t.2.1 t.2.2 1 (-1),
      triC n t.1 t.2.1 t.2.2 (-1) 1, triC n t.1 t.2.1 t.2.2 (-1) (-1)]

/-- The objective `-∑ w (1 + b xᵢxⱼ) / 2`. -/
def objective (I : Instance) : RawPoly :=
  I.2.flatMap fun c ↦ [([], -(c.2.2 / 2)), (pairExp I.1 c.1.1 c.1.2, -(c.2.2 * bsignQ c.2.1 / 2))]
where
  /-- `±1` on rationals. -/
  bsignQ (b : Bool) : ℚ := if b then 1 else -1

/-- The SDP as a degree-2 sum-of-squares problem. -/
def problem (I : Instance) : Problem := (I.1, 2, constraints I.1, (objective I, []))

/-! ### The polynomials -/

theorem length_pairExp (n i j : ℕ) : (pairExp n i j).length = n := by simp [pairExp]

theorem expo_pairExp (n i j : ℕ) : Poly.expo n (pairExp n i j) = pairExp n i j := by
  unfold Poly.expo
  refine List.ext_getElem (by simp [pairExp]) fun l h1 h2 ↦ ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa [pairExp] using h2)]

theorem expo_nil (n : ℕ) : Poly.expo n [] = List.replicate n 0 := by
  simp [Poly.expo, List.map_const']

theorem toFinsupp_nil (n : ℕ) : Mono.toFinsupp n (Poly.expo n []) = 0 := by
  ext l
  simp [Mono.toFinsupp_apply, Poly.expo]

theorem toFinsupp_pairExp {n i j : ℕ} (hi : i < n) (hj : j < n) :
    Mono.toFinsupp n (Poly.expo n (pairExp n i j)) =
      Finsupp.single (⟨i, hi⟩ : Fin n) 1 + Finsupp.single (⟨j, hj⟩ : Fin n) 1 := by
  rw [expo_pairExp]
  ext l
  simp only [Mono.toFinsupp_apply, Finsupp.add_apply, Finsupp.single_apply, pairExp]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h1 : (l : ℕ) = i <;> by_cases h2 : (l : ℕ) = j <;>
    simp [h1, h2, Fin.ext_iff, eq_comm]

/-- The monomial `xᵢ xⱼ`. -/
noncomputable def xx (n i j : ℕ) : MvPolynomial (Fin n) ℝ :=
  if h : i < n ∧ j < n then X ⟨i, h.1⟩ * X ⟨j, h.2⟩ else 0

theorem monomial_pairExp {n i j : ℕ} (hi : i < n) (hj : j < n) (c : ℝ) :
    monomial (Mono.toFinsupp n (pairExp n i j)) c = C c * xx n i j := by
  rw [← expo_pairExp, toFinsupp_pairExp hi hj, xx, dite_eq_left ⟨hi, hj⟩, X, X,
    monomial_mul_monomial, one_mul, C_mul_monomial, mul_one]

theorem toFinsupp_nil' (n : ℕ) : Mono.toFinsupp n [] = 0 := by
  ext l
  simp [Mono.toFinsupp_apply]

/-- A pseudo-expectation of a raw polynomial, term by term. -/
theorem apply_toPoly {n ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) (p : RawPoly) :
    E (toReal (p.toPoly n)) =
      (p.map fun t ↦ (t.2 : ℝ) * E (monomial (Mono.toFinsupp n t.1) 1)).sum := by
  rw [Poly.toReal_toPoly, E.map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ ↦ ?_
  simp only [Function.comp_apply]
  rw [show monomial (Mono.toFinsupp n t.1) (t.2 : ℝ) = (t.2 : ℝ) • monomial (Mono.toFinsupp n t.1) 1
    by rw [smul_monomial, smul_eq_mul, mul_one]]
  simp

theorem apply_const {n ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) :
    E (monomial (Mono.toFinsupp n []) 1) = 1 := by
  rw [toFinsupp_nil', ← C_apply, map_one, E.map_one]

theorem apply_pair {n ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) {i j : ℕ} (hi : i < n)
    (hj : j < n) : E (monomial (Mono.toFinsupp n (pairExp n i j)) 1) = E (xx n i j) := by
  rw [monomial_pairExp hi hj, map_one, one_mul]

/-- Evaluation at a point, as a pseudo-expectation. -/
noncomputable def evalPE {n : ℕ} (ℓ : ℕ) (x : Fin n → ℝ) : PseudoExpectation (Fin n) ℓ where
  toLinearMap := (MvPolynomial.aeval x).toLinearMap
  map_one' := by simp
  map_mul_self_nonneg' f _ := by simp [mul_self_nonneg]

theorem evalPE_apply {n ℓ : ℕ} (x : Fin n → ℝ) (f : MvPolynomial (Fin n) ℝ) :
    evalPE ℓ x f = eval x f := by
  simp [evalPE]

theorem evalPE_xx {n ℓ : ℕ} (x : Fin n → ℝ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    evalPE ℓ x (xx n i j) = x ⟨i, hi⟩ * x ⟨j, hj⟩ := by
  rw [evalPE_apply, xx, dite_eq_left ⟨hi, hj⟩]
  simp

/-! ### The constraints at a pseudo-expectation -/

section Values

variable {n ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ)

theorem apply_sqC {i : ℕ} (hi : i < n) (s : ℚ) :
    E (toReal ((sqC n i s).toPoly n)) = s * E (xx n i i) - s := by
  rw [apply_toPoly]
  simp only [sqC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    apply_pair E hi hi, apply_const]
  push_cast
  ring

theorem apply_triC {i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) (b b' : ℚ) :
    E (toReal ((triC n i j k b b').toPoly n)) =
      1 - b * E (xx n i j) - b' * E (xx n i k) + b * b' * E (xx n j k) := by
  rw [apply_toPoly]
  simp only [triC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    apply_pair E hi hj, apply_pair E hi hk, apply_pair E hj hk, apply_const]
  push_cast
  ring

theorem apply_objective_aux (n : ℕ) (E : PseudoExpectation (Fin n) ℓ) (l : List Constraint)
    (hval : ∀ c ∈ l, c.1.1 < c.1.2 ∧ c.1.2 < n) :
    ((l.flatMap fun c ↦ [([], -(c.2.2 / 2)),
        (pairExp n c.1.1 c.1.2, -(c.2.2 * objective.bsignQ c.2.1 / 2))]).map
      fun t ↦ (t.2 : ℝ) * E (monomial (Mono.toFinsupp n t.1) 1)).sum =
      -(l.map fun c ↦ (c.2.2 : ℝ) * ((1 + bsign c.2.1 * E (xx n c.1.1 c.1.2)) / 2)).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rcases c with ⟨⟨i, j⟩, b, w⟩
    have hc' := hval ((i, j), b, w) List.mem_cons_self
    simp only at hc'
    obtain ⟨hij, hj⟩ := hc'
    have hi : i < n := hij.trans hj
    have ih' := ih fun c' hc'' ↦ hval c' (List.mem_cons_of_mem _ hc'')
    rw [List.flatMap_cons, List.map_append, List.sum_append, ih', List.map_cons, List.sum_cons]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      apply_pair E hi hj, apply_const]
    cases b <;> simp [objective.bsignQ, bsign] <;> ring

theorem apply_objective {I : Instance} (hI : Valid I) (E : PseudoExpectation (Fin I.1) ℓ) :
    E (toReal ((objective I).toPoly I.1)) =
      -(I.2.map fun c ↦ (c.2.2 : ℝ) * ((1 + bsign c.2.1 * E (xx I.1 c.1.1 c.1.2)) / 2)).sum := by
  rw [apply_toPoly, objective]
  exact apply_objective_aux I.1 E I.2 fun c hc ↦ by
    obtain ⟨h1, h2, -⟩ := hI.1 c hc
    exact ⟨h1, h2⟩

end Values

/-! ### Degrees and norms of raw polynomials -/

theorem list_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem totalDegree_toPoly_le {n d : ℕ} (p : RawPoly)
    (h : ∀ t ∈ p, (Mono.toFinsupp n t.1).degree ≤ d) : (p.toPoly n).totalDegree ≤ d := by
  rw [Poly.toPoly_eq_sum]
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.map_cons, List.sum_cons]
    refine (totalDegree_add _ _).trans
      (max_le ?_ (ih fun t' ht' ↦ h t' (List.mem_cons_of_mem _ ht')))
    refine (totalDegree_monomial_le _ _).trans ?_
    rw [Poly.toFinsupp_expo]
    exact (h t List.mem_cons_self)

theorem coeffNorm_toPoly_le (n : ℕ) (p : RawPoly) :
    coeffNorm (toReal (p.toPoly n)) ≤ (p.map fun t ↦ |(t.2 : ℝ)|).sum := by
  rw [Poly.toReal_toPoly]
  induction p with
  | nil => simp
  | cons t p ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
    exact (coeffNorm_add_le _ _).trans (add_le_add (by rw [coeffNorm_monomial]) ih)

theorem degree_pairExp_le (n i j : ℕ) : (Mono.toFinsupp n (pairExp n i j)).degree ≤ 2 := by
  rw [Mono.degree_toFinsupp (length_pairExp n i j), pairExp, List.sum_map_add, list_sum_range,
    list_sum_range, Finset.sum_ite_eq', Finset.sum_ite_eq']
  split_ifs <;> omega

theorem degree_nil (n : ℕ) : (Mono.toFinsupp n []).degree ≤ 2 := by
  rw [toFinsupp_nil']; simp

/-! ### Validity -/

theorem triples_mem {n : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ triples n) :
    t.1 < n ∧ t.2.1 < n ∧ t.2.2 < n ∧ t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 := by
  simp only [triples, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq] at ht
  obtain ⟨i, hi, j, hj, k, ⟨hk, hij, hik, hjk⟩, rfl⟩ := ht
  exact ⟨hi, hj, hk, hij, hik, hjk⟩

theorem mem_triples {n i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) : (i, j, k) ∈ triples n := by
  simp only [triples, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨i, hi, j, hj, k, ⟨hk, hij, hik, hjk⟩, rfl⟩

/-- Every constraint is `ballC`, an `sqC`, or a `triC` on a triple of distinct indices with signs
`±1`. -/
theorem mem_constraints {n : ℕ} {f : RawPoly} (hf : f ∈ constraints n) :
    f = ballC n ∨ (∃ i < n, ∃ s : ℚ, (s = 1 ∨ s = -1) ∧ f = sqC n i s) ∨
      ∃ t ∈ triples n, ∃ b b' : ℚ, (b = 1 ∨ b = -1) ∧ (b' = 1 ∨ b' = -1) ∧
        f = triC n t.1 t.2.1 t.2.2 b b' := by
  simp only [constraints, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | ⟨i, hi, h | h⟩) | ⟨t, ht, h | h | h | h⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨i, hi, 1, Or.inl rfl, h⟩)
  · exact Or.inr (Or.inl ⟨i, hi, -1, Or.inr rfl, h⟩)
  · exact Or.inr (Or.inr ⟨t, ht, 1, 1, Or.inl rfl, Or.inl rfl, h⟩)
  · exact Or.inr (Or.inr ⟨t, ht, 1, -1, Or.inl rfl, Or.inr rfl, h⟩)
  · exact Or.inr (Or.inr ⟨t, ht, -1, 1, Or.inr rfl, Or.inl rfl, h⟩)
  · exact Or.inr (Or.inr ⟨t, ht, -1, -1, Or.inr rfl, Or.inr rfl, h⟩)

theorem degree_constraints {n : ℕ} {f : RawPoly} (hf : f ∈ constraints n) :
    ∀ t ∈ f, (Mono.toFinsupp n t.1).degree ≤ 2 := by
  rcases mem_constraints hf with rfl | ⟨i, -, s, -, rfl⟩ | ⟨t, -, b, b', -, -, rfl⟩
  · intro t ht
    simp only [ballC, List.mem_cons, List.mem_map, List.mem_range] at ht
    rcases ht with rfl | ⟨i, -, rfl⟩
    · exact degree_nil n
    · exact degree_pairExp_le n i i
  · intro t ht
    simp only [sqC, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact degree_pairExp_le n i i
    · exact degree_nil n
  · intro t' ht
    simp only [triC, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact degree_nil n
    all_goals exact degree_pairExp_le n _ _

theorem ballC_toPoly (n : ℕ) :
    (ballC n).toPoly n = C (n : ℚ) - ∑ i : Fin n, X i ^ 2 := by
  rw [Poly.toPoly_eq_sum, ballC, List.map_cons, List.sum_cons, List.map_map, Poly.toFinsupp_expo,
    toFinsupp_nil', ← C_apply, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  rw [list_sum_range, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Function.comp_apply]
  rw [Poly.toFinsupp_expo, ← expo_pairExp, toFinsupp_pairExp i.2 i.2, X, sq,
    monomial_mul_monomial, mul_one]
  simp only [Fin.eta]
  rw [show (-1 : ℚ) = -(1 : ℚ) from rfl, map_neg]

theorem eval_nonneg_of_isSumSq {n : ℕ} (x : Fin n → ℝ) {h : MvPolynomial (Fin n) ℝ}
    (hh : IsSumSq h) : 0 ≤ eval x h := by
  induction hh with
  | zero => simp
  | sq_add a hs ih => rw [map_add, map_mul]; nlinarith [mul_self_nonneg (eval x a)]

/-- At a point with `±1` coordinates, every constraint holds. -/
theorem eval_constraints_nonneg {n : ℕ} {x : Fin n → ℝ} (hx : ∀ l, x l = 1 ∨ x l = -1)
    {f : RawPoly} (hf : f ∈ constraints n) : 0 ≤ eval x (toReal (f.toPoly n)) := by
  have hsq : ∀ l, x l * x l = 1 := fun l ↦ by rcases hx l with h | h <;> rw [h] <;> norm_num
  rw [← evalPE_apply (ℓ := 0)]
  rcases mem_constraints hf with rfl | ⟨i, hi, s, -, rfl⟩ | ⟨t, ht, b, b', hb, hb', rfl⟩
  · rw [evalPE_apply, ballC_toPoly]
    simp only [toReal, map_sub, map_C, map_sum, map_pow, map_X, eval_C, eval_X]
    have : ∑ i : Fin n, x i ^ 2 = n := by simp [sq, hsq]
    rw [this]
    simp
  · rw [apply_sqC _ hi, evalPE_xx _ hi hi, hsq]
    simp
  · obtain ⟨h1, h2, h3, -, -, -⟩ := triples_mem ht
    rw [apply_triC _ h1 h2 h3, evalPE_xx _ h1 h2, evalPE_xx _ h1 h3, evalPE_xx _ h2 h3]
    have hfac : 1 - (b : ℝ) * (x ⟨t.1, h1⟩ * x ⟨t.2.1, h2⟩) - b' * (x ⟨t.1, h1⟩ * x ⟨t.2.2, h3⟩) +
        b * b' * (x ⟨t.2.1, h2⟩ * x ⟨t.2.2, h3⟩) =
        (1 - b * (x ⟨t.1, h1⟩ * x ⟨t.2.1, h2⟩)) * (1 - b' * (x ⟨t.1, h1⟩ * x ⟨t.2.2, h3⟩)) := by
      have := hsq ⟨t.1, h1⟩
      linear_combination (-(b * b') * (x ⟨t.2.1, h2⟩ * x ⟨t.2.2, h3⟩)) * this
    rw [hfac]
    have hf1 : ∀ c : ℚ, (c = 1 ∨ c = -1) → ∀ y z : ℝ, (y = 1 ∨ y = -1) → (z = 1 ∨ z = -1) →
        0 ≤ 1 - (c : ℝ) * (y * z) := by
      intro c hc y z hy hz
      rcases hc with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        norm_num
    exact mul_nonneg (hf1 b hb _ _ (hx _) (hx _)) (hf1 b' hb' _ _ (hx _) (hx _))

/-- **The problem is valid**: degree `2`, an explicit bound, and the all-ones point. -/
theorem problem_valid (I : Instance) : (problem I).Valid := by
  refine ⟨⟨1, rfl⟩, le_rfl, ?_, ⟨I.1, ?_⟩, ⟨fun _ ↦ 1, ?_⟩⟩
  · intro q hq
    simp only [problem, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    refine totalDegree_toPoly_le _ fun t ht ↦ ?_
    simp only [objective, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at ht
    obtain ⟨c, -, rfl | rfl⟩ := ht
    · exact degree_nil _
    · exact degree_pairExp_le _ _ _
  · have hmem : (ballC I.1).toPoly I.1 ∈ (constraints I.1).map (RawPoly.toPoly I.1) :=
      List.mem_map_of_mem (List.mem_cons_self ..)
    rw [ballC_toPoly] at hmem
    exact hmem
  · intro f hf
    change f ∈ (constraints I.1).map (RawPoly.toPoly I.1) at hf
    obtain ⟨raw, hraw, rfl⟩ := List.mem_map.1 hf
    exact eval_constraints_nonneg (fun _ ↦ Or.inl rfl) hraw

/-! ### What the solver gives -/

/-- The moments `Mᵢⱼ = Ẽ[xᵢ xⱼ]`, read from the solver's output. -/
def momentsOf (n : ℕ) (out : RawPoly) (i j : ℕ) : ℚ := Poly.coeff n out (pairExp n i j)

theorem moment_eq {n ℓ : ℕ} {E : PseudoExpectation (Fin n) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly n)) (hℓ : 2 ≤ ℓ) {i j : ℕ} (hi : i < n) (hj : j < n) :
    E (xx n i j) = momentsOf n out i j := by
  rw [← apply_pair E hi hj, hM _ ((degree_pairExp_le n i j).trans hℓ),
    Poly.coeff_toPoly _ (length_pairExp n i j), momentsOf]

/-- Approximate satisfaction of one constraint. -/
theorem approx_mem {n ℓ : ℕ} {E : PseudoExpectation (Fin n) ℓ} {A : System (Fin n) ℚ} {e : ℝ}
    (hE : E.ApproxSatisfies A e 0) {f : MvPolynomial (Fin n) ℚ} (hf : f ∈ A)
    (hdeg : f.totalDegree ≤ ℓ) : -(e * coeffNorm (toReal f)) ≤ E (toReal f) := by
  obtain ⟨idx, rfl⟩ := List.mem_iff_get.1 hf
  have h := hE {idx} 1 IsSumSq.one (by simpa using hdeg)
  have h1 : coeffNorm (1 : MvPolynomial (Fin n) ℝ) = 1 := by rw [← C_1, coeffNorm_C, abs_one]
  simpa [System.prod, h1] using h

theorem mem_system {I : Instance} {f : RawPoly} (hf : f ∈ constraints I.1) :
    f.toPoly I.1 ∈ (problem I).system :=
  List.mem_map_of_mem hf

theorem sqC_mem {n i : ℕ} (hi : i < n) (s : ℚ) (hs : s = 1 ∨ s = -1) :
    sqC n i s ∈ constraints n := by
  simp only [constraints, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range]
  rcases hs with rfl | rfl
  · exact Or.inl (Or.inr ⟨i, hi, by simp⟩)
  · exact Or.inl (Or.inr ⟨i, hi, by simp⟩)

theorem triC_mem {n i j k : ℕ} (hi : i < n) (hj : j < n) (hk : k < n) (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (b b' : Bool) :
    triC n i j k (objective.bsignQ b) (objective.bsignQ b') ∈ constraints n := by
  simp only [constraints, List.mem_cons, List.mem_append, List.mem_flatMap]
  refine Or.inr ⟨(i, j, k), mem_triples hi hj hk hij hik hjk, ?_⟩
  cases b <;> cases b' <;> simp [objective.bsignQ]

theorem bsignQ_cast (b : Bool) : ((objective.bsignQ b : ℚ) : ℝ) = bsign b := by
  cases b <;> simp [objective.bsignQ, bsign]

/-- The satisfied weight of `y` is the SDP value of the `±1` point `bsign ∘ y`. -/
theorem satWeight_extend_eq {I : Instance} (hI : Valid I) (y : Fin I.1 → Bool) :
    satWeight I (BGHKLMM26.extend y) = (I.2.map fun c ↦ (c.2.2 : ℝ) *
      ((1 + bsign c.2.1 * (evalPE 2 (fun l ↦ bsign (y l)) (xx I.1 c.1.1 c.1.2))) / 2)).sum := by
  unfold satWeight
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  obtain ⟨hij, hj, -⟩ := hI.1 c hc
  have hi : c.1.1 < I.1 := hij.trans hj
  rw [evalPE_xx _ hi hj]
  simp only [BGHKLMM26.extend, dite_eq_left hi, dite_eq_left hj]
  cases y ⟨c.1.1, hi⟩ <;> cases y ⟨c.1.2, hj⟩ <;> cases c.2.1 <;> simp [bsign]

/-- **The solver's output** [BGHKLMM26, Section 3]: the moments form a positive semidefinite
matrix with diagonal within `2(η + γ)` of `1`, satisfying the triangle inequalities up to
`4(η + γ)`, with SDP value at least `opt - γ`. -/
theorem correct_spec {I : Instance} (hI : Valid I) {η γ : ℚ} (hη : 0 < η) (hγ : 0 < γ)
    {out : RawPoly} (hc : Correct (problem I) η γ out) :
    (∀ a : Fin I.1 → ℝ, 0 ≤ ∑ i, ∑ j, a i * a j * (momentsOf I.1 out i j : ℝ)) ∧
    (∀ i < I.1, |(momentsOf I.1 out i i : ℝ) - 1| ≤ 2 * ((η : ℝ) + γ)) ∧
    (∀ i j k, i < I.1 → j < I.1 → k < I.1 → i ≠ j → i ≠ k → j ≠ k → ∀ b b' : Bool,
      bsign b * (momentsOf I.1 out i j : ℝ) + bsign b' * momentsOf I.1 out i k - 1 -
        4 * ((η : ℝ) + γ) ≤ bsign b * bsign b' * momentsOf I.1 out j k) ∧
    opt I - γ ≤ (I.2.map fun c ↦ (c.2.2 : ℝ) *
      ((1 + bsign c.2.1 * momentsOf I.1 out c.1.1 c.1.2) / 2)).sum := by
  have hc' : ∃ E : PseudoExpectation (Fin I.1) 2, HasMoments E (out.toPoly I.1) ∧
      E.ApproxSatisfies ((constraints I.1).map (RawPoly.toPoly I.1)) ((η : ℝ) + γ) 0 ∧
      ∀ E' : PseudoExpectation (Fin I.1) 2,
        E'.ApproxSatisfies ((constraints I.1).map (RawPoly.toPoly I.1)) η 0 →
        E (toReal ((objective I).toPoly I.1)) ≤ E' (toReal ((objective I).toPoly I.1)) + γ := by
    obtain ⟨E, h1, h2, h3⟩ := hc
    refine ⟨E, h1, h2, fun E' hE' ↦ ?_⟩
    have := h3 E' hE'
    simp only [Problem.objective, problem, Problem.numVars, List.map_nil, List.sum_nil,
      add_zero] at this
    exact this
  clear hc
  obtain ⟨E, hM, happ, hopt⟩ := hc'
  have hm : ∀ {i j : ℕ}, i < I.1 → j < I.1 → E (xx I.1 i j) = momentsOf I.1 out i j :=
    fun hi hj ↦ moment_eq hM le_rfl hi hj
  set e : ℝ := (η : ℝ) + γ with hedef
  have he : 0 ≤ e := by positivity
  have happ' : ∀ f ∈ constraints I.1, -(e * coeffNorm (toReal (f.toPoly I.1))) ≤
      E (toReal (f.toPoly I.1)) := fun f hf ↦
    approx_mem happ (List.mem_map_of_mem hf) (totalDegree_toPoly_le f (degree_constraints hf))
  have hsm : ∀ (c : ℝ) (p : MvPolynomial (Fin I.1) ℝ), E (C c * p) = c * E p := fun c p ↦ by
    rw [C_mul', PseudoExpectation.coe_apply, LinearMap.map_smul, smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Positive semidefinite: `Ẽ[(∑ aᵢ xᵢ)²] ≥ 0`.
    intro a
    set f : MvPolynomial (Fin I.1) ℝ := ∑ i, C (a i) * X i
    have hdeg : 2 * f.totalDegree ≤ 2 := by
      have : f.totalDegree ≤ 1 := by
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ ↦ ?_)
        refine (totalDegree_mul _ _).trans ?_
        simp
      omega
    have h := E.map_mul_self_nonneg hdeg
    have hexp : f * f = ∑ i, ∑ j, C (a i * a j) * xx I.1 i j := by
      simp only [f, Finset.sum_mul, Finset.mul_sum, xx, Fin.is_lt, and_self, dite_true,
        Fin.eta, C_mul]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [hexp, E.map_sum] at h
    convert h using 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [E.map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hsm, hm i.2 j.2]
  · -- The diagonal.
    intro i hi
    have h1 := happ' _ (sqC_mem hi 1 (Or.inl rfl))
    have h2 := happ' _ (sqC_mem hi (-1) (Or.inr rfl))
    rw [apply_sqC _ hi, hm hi hi] at h1 h2
    have hn1 : coeffNorm (toReal ((sqC I.1 i 1).toPoly I.1)) ≤ 2 :=
      (coeffNorm_toPoly_le I.1 _).trans (by simp [sqC]; norm_num)
    have hn2 : coeffNorm (toReal ((sqC I.1 i (-1)).toPoly I.1)) ≤ 2 :=
      (coeffNorm_toPoly_le I.1 _).trans (by simp [sqC]; norm_num)
    have := mul_le_mul_of_nonneg_left hn1 he
    have := mul_le_mul_of_nonneg_left hn2 he
    push_cast at h1 h2
    rw [abs_le]
    constructor <;> linarith
  · -- The triangle inequalities.
    intro i j k hi hj hk hij hik hjk b b'
    have h := happ' _ (triC_mem hi hj hk hij hik hjk b b')
    rw [apply_triC _ hi hj hk, hm hi hj, hm hi hk, hm hj hk] at h
    have hn : coeffNorm (toReal ((triC I.1 i j k (objective.bsignQ b)
        (objective.bsignQ b')).toPoly I.1)) ≤ 4 :=
      (coeffNorm_toPoly_le I.1 _).trans (by
        cases b <;> cases b' <;> simp [triC, objective.bsignQ] <;> norm_num)
    have := mul_le_mul_of_nonneg_left hn he
    rw [bsignQ_cast, bsignQ_cast] at h
    linarith
  · -- The value: every assignment is a competitor.
    obtain ⟨y, hy⟩ := exists_eq_ciSup_of_finite (f := fun y : Fin I.1 → Bool ↦
      satWeight I (BGHKLMM26.extend y))
    set x : Fin I.1 → ℝ := fun l ↦ bsign (y l)
    have hx : ∀ l, x l = 1 ∨ x l = -1 := fun l ↦ bsign_cases (y l)
    set A := (constraints I.1).map (RawPoly.toPoly I.1)
    have hcomp : (evalPE 2 x).ApproxSatisfies A η 0 := by
      intro S h hh _
      have hnn : 0 ≤ evalPE 2 x (h * toReal (System.prod A S)) := by
        rw [evalPE_apply, map_mul]
        refine mul_nonneg (eval_nonneg_of_isSumSq x hh) ?_
        simp only [System.prod, toReal, map_prod]
        refine Finset.prod_nonneg fun idx _ ↦ ?_
        have hmem := List.get_mem A idx
        obtain ⟨raw, hraw, hreq⟩ := List.mem_map.1 hmem
        rw [← hreq]
        exact eval_constraints_nonneg hx hraw
      have : 0 ≤ (η : ℝ) * coeffNorm h * ∏ i ∈ S, coeffNorm (toReal (A.get i)) :=
        mul_nonneg (mul_nonneg (by positivity) (coeffNorm_nonneg _))
          (Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _)
      linarith
    have hle := hopt (evalPE 2 x) hcomp
    rw [apply_objective hI, apply_objective hI] at hle
    have hval : opt I = satWeight I (BGHKLMM26.extend y) := by rw [hy]; rfl
    rw [hval, satWeight_extend_eq hI y]
    have heq : (I.2.map fun c ↦ (c.2.2 : ℝ) * ((1 + bsign c.2.1 * E (xx I.1 c.1.1 c.1.2)) / 2)) =
        I.2.map fun c ↦ (c.2.2 : ℝ) * ((1 + bsign c.2.1 * momentsOf I.1 out c.1.1 c.1.2) / 2) :=
      List.map_congr_left fun c hc ↦ by
        obtain ⟨hij, hj, -⟩ := hI.1 c hc
        rw [hm (hij.trans hj) hj]
    rw [heq] at hle
    linarith

end BGHKLMM26.SDP
