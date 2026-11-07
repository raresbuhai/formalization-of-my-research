module

public import BKS23.Model
public import BKS23.Rounding
public import BKS23.Cleanup
public import Background.SumOfSquares.Algorithm.Correct

/-!
# The algorithm

The algorithm of [BKS23, Algorithm 5.2], as a function on the encoded input
(`BKS23.Algorithm.run`), with the parameter `t` and a budget `L`:

1. Read `n` (at most one more than the number of adjacency bits, `BKS23.Algorithm.numV`), `k`, and
   the non-edges of the graph (`BKS23.Algorithm.nonEdges`).
2. Build the clique program of degree `ℓ = 8t + 6` ([CliqueProgram.lean](CliqueProgram.lean)), on
   vertex numbers (`BKS23.Algorithm.problemN`), and run the sum-of-squares solver
   `SoS.Core.core` on it with the accuracies `η = 2^-e`, `γ = 2^-2e`, `e = (n + 2)^4 (t + 1)`.
3. For every `T`-tuple `Q` of vertices, `T = 4t` (`BKS23.Algorithm.tuples`), read `Ẽ[w_Q]` and
   `Ẽ[w_Q wᵢ]` from the solver's moments and form `S_Q = {i | Ẽ[w_Q] ≤ 2 Ẽ[w_Q wᵢ]}`
   (`BKS23.Algorithm.roundSet`).
4. Clean up (`BKS23.Algorithm.cleanupL`): keep the `S_Q` that are `k`-cliques, and prune greedily
   with the threshold `Δ = ⌈n^(1/(2t))⌉` (`BKS23.Algorithm.rootCeil`).

The coins are not used. With the budget `L = SoS.Solver.budget` of the solver's input
(`BKS23.Algorithm.alg`), nothing is cut short.

**Correctness** (`BKS23.Algorithm.alg_spec`): on the input of a graph `G` with a `k`-clique, there
is a pseudo-expectation `Ẽ` satisfying the clique program approximately and approximately optimal,
as `BKS23.Rounding.exists_round_eq` needs, such that the output consists of `k`-cliques of `G`, has
at most `(n/k)(1 + 2nΔ/k²)` entries, and contains every `S_Q` that is a `k`-clique meeting every
other `k`-clique of `G` in fewer than `Δ` vertices.
-/

@[expose] public section

namespace BKS23.Algorithm

open SoS SoS.Solver MvPolynomial Finset

/-! ### The clique program on vertex numbers -/

/-- `BKS23.Clique.single` on vertex numbers. -/
def singleN (n i a : ℕ) : List ℕ := (List.range n).map fun j ↦ if j = i then a else 0

/-- `BKS23.Clique.pair` on vertex numbers. -/
def pairN (n i j : ℕ) : List ℕ := (List.range n).map fun l ↦ if l = i ∨ l = j then 1 else 0

def boolPolyN (n i : ℕ) : RawPoly := [(singleN n i 2, 1), (singleN n i 1, -1)]

def cardPolyN (n k : ℕ) : RawPoly :=
  (List.range n).map (fun i ↦ (singleN n i 1, 1)) ++ [([], -(k : ℚ))]

def edgePolyN (n i j : ℕ) : RawPoly := [(pairN n i j, 1)]

def boundPolyN (n k : ℕ) : RawPoly :=
  ([], (k : ℚ)) :: (List.range n).map fun i ↦ (singleN n i 2, -1)

def constraintsN (n k : ℕ) (L : List (ℕ × ℕ)) : List RawPoly :=
  boundPolyN n k :: ((List.range n).flatMap fun i ↦ [boolPolyN n i, Clique.neg (boolPolyN n i)]) ++
    [cardPolyN n k, Clique.neg (cardPolyN n k)] ++
    L.flatMap fun e ↦ [edgePolyN n e.1 e.2, Clique.neg (edgePolyN n e.1 e.2)]

def objectiveN (n : ℕ) : RawPoly × List RawPoly :=
  ([], (List.range n).map fun i ↦ [(singleN n i 1, 1)])

/-- The clique program, on vertex numbers. -/
def problemN (n k ℓ : ℕ) (L : List (ℕ × ℕ)) : Problem :=
  (n, ℓ, constraintsN n k L, objectiveN n)

theorem range_eq_map_val (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem map_finRange_val {β : Type*} (n : ℕ) (f : ℕ → β) :
    (List.finRange n).map (fun i : Fin n ↦ f i) = (List.range n).map f := by
  rw [range_eq_map_val, List.map_map]
  rfl

theorem flatMap_finRange_val {β : Type*} (n : ℕ) (f : ℕ → List β) :
    (List.finRange n).flatMap (fun i : Fin n ↦ f i) = (List.range n).flatMap f := by
  rw [List.flatMap_def, List.flatMap_def, map_finRange_val]

theorem single_eq {n : ℕ} (i : Fin n) (a : ℕ) : Clique.single n i a = singleN n i a := by
  rw [Clique.single, singleN, ← map_finRange_val]
  simp only [Fin.val_inj]

theorem pair_eq (n i j : ℕ) : Clique.pair n i j = pairN n i j := by
  rw [Clique.pair, pairN, ← map_finRange_val]

theorem problemN_eq (n k ℓ : ℕ) (L : List (ℕ × ℕ)) : problemN n k ℓ L = Clique.problem n k ℓ L := by
  have hb : ∀ i : Fin n, Clique.boolPoly n i = boolPolyN n i := fun i ↦ by
    simp [Clique.boolPoly, boolPolyN, single_eq]
  have he : ∀ i j, Clique.edgePoly n i j = edgePolyN n i j := fun i j ↦ by
    simp [Clique.edgePoly, edgePolyN, pair_eq]
  simp only [problemN, Clique.problem, constraintsN, Clique.constraints, objectiveN,
    Clique.objective, boundPolyN, Clique.boundPoly, cardPolyN, Clique.cardPoly, hb, he,
    single_eq, flatMap_finRange_val (f := fun i ↦ [boolPolyN n i,
      Clique.neg (boolPolyN n i)]), map_finRange_val (f := fun i ↦ (singleN n i 1, (1 : ℚ))),
    map_finRange_val (f := fun i ↦ (singleN n i 2, (-1 : ℚ))),
    map_finRange_val (f := fun i ↦ ([(singleN n i 1, (1 : ℚ))] : RawPoly))]

/-! ### The non-edges -/

/-- The pairs `(i, j)`, `i < j < n`, in lexicographic order: the pairs of `BKS23.adjBits`. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ ((List.range n).filter fun j ↦ decide (i < j)).map fun j ↦ (i, j)

/-- The pairs whose adjacency bit is `false`. -/
def nonEdges (n : ℕ) (a : List Bool) : List (ℕ × ℕ) :=
  (((pairs n).zip a).filter fun p ↦ !p.2).map Prod.fst

/-- The pairs of `Fin n`, in the order of `BKS23.adjBits`. -/
def pairsF (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i ↦ ((List.finRange n).filter fun j ↦ decide (i < j)).map (i, ·)

theorem pairs_eq (n : ℕ) : pairs n = (pairsF n).map fun e ↦ ((e.1 : ℕ), (e.2 : ℕ)) := by
  rw [pairs, pairsF, List.map_flatMap, ← flatMap_finRange_val]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [range_eq_map_val, List.filter_map, List.map_map, List.map_map]
  rfl

open Classical in
theorem adjBits_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    adjBits G = (pairsF n).map fun e ↦ decide (G.Adj e.1 e.2) := by
  rw [adjBits, pairsF, List.map_flatMap]
  refine List.flatMap_congr fun i _ ↦ ?_
  rw [List.map_map]
  rfl

theorem mem_pairsF {n : ℕ} {e : Fin n × Fin n} : e ∈ pairsF n ↔ e.1 < e.2 := by
  simp only [pairsF, List.mem_flatMap, List.mem_finRange, List.mem_map, List.mem_filter,
    decide_eq_true_eq, true_and]
  constructor
  · rintro ⟨a, b, h, rfl⟩
    exact h
  · intro h
    exact ⟨e.1, e.2, h, rfl⟩

open Classical in
theorem nonEdges_eq {n : ℕ} (G : SimpleGraph (Fin n)) :
    nonEdges n (adjBits G) =
      ((pairsF n).filter fun e ↦ !decide (G.Adj e.1 e.2)).map fun e ↦ ((e.1 : ℕ), (e.2 : ℕ)) := by
  rw [nonEdges, pairs_eq, adjBits_eq, List.zip_map, List.zip_eq_zipWith, List.zipWith_self,
    List.map_map, List.filter_map, List.map_map]
  rfl

theorem mem_nonEdges {n : ℕ} (G : SimpleGraph (Fin n)) {e : ℕ × ℕ} :
    e ∈ nonEdges n (adjBits G) ↔
      ∃ u v : Fin n, (u : ℕ) = e.1 ∧ (v : ℕ) = e.2 ∧ u < v ∧ ¬ G.Adj u v := by
  classical
  rw [nonEdges_eq]
  simp only [List.mem_map, List.mem_filter, mem_pairsF, Bool.not_eq_true', decide_eq_false_iff_not,
    Prod.exists]
  constructor
  · rintro ⟨u, v, ⟨huv, hG⟩, rfl⟩
    exact ⟨u, v, rfl, rfl, huv, hG⟩
  · rintro ⟨u, v, h1, h2, huv, hG⟩
    exact ⟨u, v, ⟨huv, hG⟩, Prod.ext h1 h2⟩

theorem listsNonEdges {n : ℕ} (G : SimpleGraph (Fin n)) :
    Clique.ListsNonEdges G (nonEdges n (adjBits G)) :=
  fun u v huv hG ↦ (mem_nonEdges G).2 ⟨u, v, rfl, rfl, huv, hG⟩

theorem onlyNonEdges {n : ℕ} (G : SimpleGraph (Fin n)) :
    Clique.OnlyNonEdges G (nonEdges n (adjBits G)) := fun e he ↦ by
  obtain ⟨u, v, h1, h2, huv, hG⟩ := (mem_nonEdges G).1 he
  exact ⟨u, v, h1, h2, huv.ne, hG⟩

theorem length_pairs_ge (n : ℕ) : n ≤ (pairs n).length + 1 := by
  rcases n with _ | m
  · simp
  rw [pairs, List.range_succ_eq_map, List.flatMap_cons, List.length_append, List.length_map]
  have : ((0 :: (List.range m).map Nat.succ).filter fun j ↦ decide (0 < j)).length = m := by
    rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.2 (by simp)]
    simp
  omega

theorem length_adjBits_ge {n : ℕ} (G : SimpleGraph (Fin n)) : n ≤ (adjBits G).length + 1 := by
  have := length_pairs_ge n
  rw [pairs_eq, List.length_map] at this
  rwa [adjBits_eq, List.length_map]

/-! ### Tuples -/

/-- One more coordinate, for every tuple, cut at `L` tuples. -/
def tupleStep (L n : ℕ) (l : List (List ℕ)) : List (List ℕ) :=
  (l.flatMap fun q ↦ (List.range n).map (· :: q)).take L

/-- The `T`-tuples over `{0, …, n - 1}`, cut at `L` at every step: all of them if `n^T ≤ L`. -/
def tuples (L n T : ℕ) : List (List ℕ) := (tupleStep L n)^[T] [[]]

/-- One more coordinate, for every tuple. -/
def tupleStepFull (n : ℕ) (l : List (List ℕ)) : List (List ℕ) :=
  l.flatMap fun q ↦ (List.range n).map (· :: q)

theorem length_tupleStepFull (n : ℕ) (l : List (List ℕ)) :
    (tupleStepFull n l).length = n * l.length := by
  rw [tupleStepFull, List.length_flatMap]
  simp [mul_comm]

theorem length_iterate_tupleStepFull (n i : ℕ) : ((tupleStepFull n)^[i] [[]]).length = n ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', length_tupleStepFull, ih, pow_succ, mul_comm]

theorem mem_iterate_tupleStepFull {n : ℕ} : ∀ {i : ℕ} {q : List ℕ},
    q ∈ (tupleStepFull n)^[i] [[]] ↔ q.length = i ∧ ∀ x ∈ q, x < n
  | 0, q => by
    simp only [Function.iterate_zero, id, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, -⟩
      exact List.length_eq_zero_iff.1 h
  | i + 1, q => by
    rw [Function.iterate_succ_apply', tupleStepFull, List.mem_flatMap]
    constructor
    · rintro ⟨q', hq', hq⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      obtain ⟨h1, h2⟩ := mem_iterate_tupleStepFull.1 hq'
      refine ⟨by simp [h1], fun y hy ↦ ?_⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · exact List.mem_range.1 hx
      · exact h2 y hy
    · rintro ⟨h1, h2⟩
      obtain _ | ⟨x, q'⟩ := q
      · simp at h1
      refine ⟨q', mem_iterate_tupleStepFull.2 ⟨by simpa using h1, fun y hy ↦ h2 y (by simp [hy])⟩,
        List.mem_map.2 ⟨x, List.mem_range.2 (h2 x (by simp)), rfl⟩⟩

theorem tuples_eq {L n T : ℕ} (h : n ^ T ≤ L) : tuples L n T = (tupleStepFull n)^[T] [[]] := by
  suffices ∀ i ≤ T, (tupleStep L n)^[i] [[]] = (tupleStepFull n)^[i] [[]] from this T le_rfl
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega), tupleStep]
    refine List.take_of_length_le ?_
    change (tupleStepFull n _).length ≤ L
    rw [length_tupleStepFull, length_iterate_tupleStepFull, ← pow_succ']
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_le_pow_right hn hi).trans h

theorem ofFn_mem_tuples {L n T : ℕ} (h : n ^ T ≤ L) (Q : Fin T → Fin n) :
    List.ofFn (fun j ↦ (Q j : ℕ)) ∈ tuples L n T := by
  rw [tuples_eq h, mem_iterate_tupleStepFull]
  refine ⟨by simp, fun x hx ↦ ?_⟩
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  exact (Q j).2

/-! ### The rounding -/

/-- The exponent vector of `∏_{i ∈ q} xᵢ`: the number of times each vertex appears. -/
def countVec (n : ℕ) (q : List ℕ) : List ℕ := (List.range n).map fun i ↦ q.count i

/-- `S_Q = {i | Ẽ[w_Q] ≤ 2 Ẽ[w_Q wᵢ]}`, from the moments `out`. -/
def roundSet (n : ℕ) (out : RawPoly) (q : List ℕ) : List ℕ :=
  (List.range n).filter fun i ↦
    decide (Poly.coeff n out (countVec n q) ≤ 2 * Poly.coeff n out (countVec n (i :: q)))

/-- The variable of a vertex number (`1` past `n`). -/
noncomputable def xN (n i : ℕ) : MvPolynomial (Fin n) ℝ := if h : i < n then X ⟨i, h⟩ else 1

theorem toFinsupp_countVec_cons {n : ℕ} {i : ℕ} (hi : i < n) (q : List ℕ) :
    Mono.toFinsupp n (countVec n (i :: q)) =
      Finsupp.single ⟨i, hi⟩ 1 + Mono.toFinsupp n (countVec n q) := by
  ext j
  simp only [Mono.toFinsupp_apply, countVec, Finsupp.add_apply, Finsupp.single_apply,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2, Option.map_some,
    Option.getD_some, List.count_cons]
  by_cases h : (⟨i, hi⟩ : Fin n) = j
  · subst h
    simp
    omega
  · have : ¬ (i = (j : ℕ)) := fun h' ↦ h (Fin.ext h')
    simp [h, this]

theorem toFinsupp_countVec_nil (n : ℕ) : Mono.toFinsupp n (countVec n []) = 0 := by
  ext j
  simp [Mono.toFinsupp_apply, countVec, List.getD_eq_getElem?_getD]

/-- `∏_{i ∈ q} xᵢ` is the monomial of `countVec n q`. -/
theorem monomial_countVec {n : ℕ} : ∀ {q : List ℕ}, (∀ i ∈ q, i < n) →
    monomial (Mono.toFinsupp n (countVec n q)) (1 : ℝ) = (q.map (xN n)).prod
  | [], _ => by simp [toFinsupp_countVec_nil]
  | i :: q, h => by
    have hi : i < n := h i (by simp)
    rw [toFinsupp_countVec_cons hi, ← mul_one (1 : ℝ), ← monomial_mul_monomial,
      monomial_countVec fun j hj ↦ h j (by simp [hj]), List.map_cons, List.prod_cons]
    simp only [xN, hi, ↓reduceDIte]
    rfl

theorem degree_countVec_le {n : ℕ} {q : List ℕ} (h : ∀ i ∈ q, i < n) :
    (Mono.toFinsupp n (countVec n q)).degree ≤ q.length := by
  have h1 := monomial_countVec h
  have h2 : (monomial (Mono.toFinsupp n (countVec n q)) (1 : ℝ)).totalDegree =
      (Mono.toFinsupp n (countVec n q)).degree := by
    rw [totalDegree_monomial _ one_ne_zero, Finsupp.degree]
    rfl
  rw [← h2, h1]
  refine (totalDegree_list_prod _).trans ?_
  rw [List.map_map]
  calc ((q.map (totalDegree ∘ xN n)).sum) ≤ (q.map fun _ ↦ 1).sum := by
        refine List.sum_le_sum fun i _ ↦ ?_
        simp only [Function.comp_apply, xN]
        split_ifs
        · rw [totalDegree_X]
        · simp
    _ = q.length := by simp

theorem wQ_eq_prod {n T : ℕ} (Q : Fin T → Fin n) :
    Rounding.wQ Q = ((List.ofFn fun j ↦ (Q j : ℕ)).map (xN n)).prod := by
  rw [List.map_ofFn, List.prod_ofFn, Rounding.wQ]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp [xN]

theorem forall_lt_ofFn {n T : ℕ} (Q : Fin T → Fin n) :
    ∀ i ∈ List.ofFn (fun j ↦ (Q j : ℕ)), i < n := by
  intro i hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hi
  exact (Q j).2

/-- `Ẽ[∏_{i ∈ q} xᵢ]` is read from the moments. -/
theorem apply_prod_eq {n ℓ : ℕ} {E : PseudoExpectation (Fin n) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly n)) {q : List ℕ} (hq : ∀ i ∈ q, i < n) (hℓ : q.length ≤ ℓ) :
    E ((q.map (xN n)).prod) = (Poly.coeff n out (countVec n q) : ℝ) := by
  rw [← monomial_countVec hq, hM _ ((degree_countVec_le hq).trans hℓ),
    Poly.coeff_toPoly _ (by simp [countVec])]

theorem roundSet_eq {n ℓ T : ℕ} {E : PseudoExpectation (Fin n) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly n)) (hT : T + 1 ≤ ℓ) (Q : Fin T → Fin n) :
    vertexSet n (roundSet n out (List.ofFn fun j ↦ (Q j : ℕ))) =
      univ.filter fun i ↦ E (Rounding.wQ Q) ≤ 2 * E (Rounding.wQ Q * X i) := by
  classical
  ext i
  have hq := forall_lt_ofFn Q
  have h1 := apply_prod_eq hM hq (by simp; omega)
  have h2 := apply_prod_eq hM (q := (i : ℕ) :: List.ofFn fun j ↦ (Q j : ℕ))
    (fun j hj ↦ by rcases List.mem_cons.1 hj with rfl | hj; exacts [i.2, hq j hj]) (by simp; omega)
  rw [List.map_cons, List.prod_cons, mul_comm] at h2
  have hxi : xN n i = X i := by simp [xN]
  rw [← wQ_eq_prod] at h1 h2
  rw [hxi] at h2
  simp only [vertexSet, roundSet, mem_filter, mem_univ, true_and, List.mem_filter, List.mem_range,
    i.2, decide_eq_true_eq, h1, h2]
  exact_mod_cast Iff.rfl

theorem good_roundSet (n : ℕ) (out : RawPoly) (q : List ℕ) :
    (roundSet n out q).Nodup ∧ ∀ i ∈ roundSet n out q, i < n :=
  ⟨List.nodup_range.filter _, fun _ hi ↦ List.mem_range.1 (List.mem_filter.1 hi).1⟩

/-! ### The cleanup on lists -/

/-- Whether `S` has `k` entries and no non-edge (of the list `E`) inside it. -/
def isCliqueL (k : ℕ) (E : List (ℕ × ℕ)) (S : List ℕ) : Bool :=
  decide (S.length = k) && S.all fun i ↦ S.all fun j ↦ !(decide (i < j) && decide ((i, j) ∈ E))

/-- The number of entries of `y` that are in `x`. -/
def interCount (y x : List ℕ) : ℕ := (y.filter fun a ↦ decide (a ∈ x)).length

/-- `BKS23.Cleanup.cleanup` on lists. -/
def cleanupL (k Δ : ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) : List (List ℕ) :=
  Cleanup.prune (fun y x ↦ decide (interCount y x < Δ)) (C.filter (isCliqueL k E))

/-- A list of distinct vertex numbers below `n`. -/
def Good (n : ℕ) (S : List ℕ) : Prop := S.Nodup ∧ ∀ i ∈ S, i < n

theorem map_vertexSet {n : ℕ} (S : List ℕ) :
    (vertexSet n S).map Fin.valEmbedding = S.toFinset.filter (· < n) := by
  classical
  ext i
  simp only [vertexSet, mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
    List.mem_toFinset]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, j.2⟩
  · rintro ⟨hi, hin⟩
    exact ⟨⟨i, hin⟩, hi, rfl⟩

theorem card_vertexSet {n : ℕ} {S : List ℕ} (h : Good n S) : (vertexSet n S).card = S.length := by
  classical
  rw [← card_map Fin.valEmbedding, map_vertexSet, filter_true_of_mem fun i hi ↦
    h.2 i (List.mem_toFinset.1 hi), List.toFinset_card_of_nodup h.1]

theorem vertexSet_inter (n : ℕ) (y x : List ℕ) :
    vertexSet n y ∩ vertexSet n x = vertexSet n (y.filter fun a ↦ decide (a ∈ x)) := by
  classical
  ext i
  simp [vertexSet]

theorem card_inter_vertexSet {n : ℕ} {y : List ℕ} (h : Good n y) (x : List ℕ) :
    (vertexSet n y ∩ vertexSet n x).card = interCount y x := by
  rw [vertexSet_inter, card_vertexSet ⟨h.1.filter _, fun i hi ↦ h.2 i (List.mem_filter.1 hi).1⟩,
    interCount]

theorem isCliqueL_iff {n k : ℕ} (G : SimpleGraph (Fin n)) {S : List ℕ} (h : Good n S) :
    isCliqueL k (nonEdges n (adjBits G)) S = true ↔ G.IsNClique k (vertexSet n S) := by
  classical
  rw [SimpleGraph.isNClique_iff, card_vertexSet h, isCliqueL, Bool.and_eq_true, decide_eq_true_eq,
    and_comm]
  refine and_congr_left' ?_
  simp only [List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    not_lt, mem_nonEdges]
  constructor
  · intro hS u hu v hv huv
    simp only [vertexSet, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
    rcases lt_or_gt_of_ne huv with hlt | hlt
    · rcases hS u hu v hv with h' | h'
      · exact absurd (Fin.lt_def.1 hlt) (by omega)
      · by_contra hG
        exact h' ⟨u, v, rfl, rfl, hlt, hG⟩
    · rcases hS v hv u hu with h' | h'
      · exact absurd (Fin.lt_def.1 hlt) (by omega)
      · by_contra hG
        exact h' ⟨v, u, rfl, rfl, hlt, fun h'' ↦ hG h''.symm⟩
  · intro hS i hi j hj
    by_cases hij : j ≤ i
    · exact Or.inl hij
    refine Or.inr ?_
    rintro ⟨u, v, rfl, rfl, huv, hG⟩
    exact hG (hS (by simp [vertexSet, hi]) (by simp [vertexSet, hj]) huv.ne)

/-- `BKS23.Cleanup.cleanup` commutes with `vertexSet` on good lists. -/
theorem map_cleanupL {n k Δ : ℕ} (G : SimpleGraph (Fin n)) {C : List (List ℕ)}
    (hC : ∀ S ∈ C, Good n S) :
    (cleanupL k Δ (nonEdges n (adjBits G)) C).map (vertexSet n) =
      Cleanup.cleanup G k Δ (C.map (vertexSet n)) := by
  classical
  rw [cleanupL, Cleanup.cleanup, List.filter_map]
  have hf : C.filter ((fun S ↦ decide (G.IsNClique k S)) ∘ vertexSet n) =
      C.filter (isCliqueL k (nonEdges n (adjBits G))) := by
    refine List.filter_congr fun S hS ↦ ?_
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, isCliqueL_iff G (hC S hS), decide_eq_true_eq]
  rw [hf, Cleanup.prune, Cleanup.prune, ← List.map_nil (f := vertexSet n),
    Cleanup.pruneAux_map]
  intro y hy x hx
  simp only [List.nil_append] at hy hx
  rw [card_inter_vertexSet (hC y (List.mem_filter.1 hy).1)]

/-- The pruning step, for a fold. -/
def pruneStep (Δ : ℕ) (kept : List (List ℕ)) (x : List ℕ) : List (List ℕ) :=
  if kept.all (fun y ↦ decide (interCount y x < Δ)) then kept ++ [x] else kept

theorem pruneAux_eq_foldl {β : Type*} (ok : β → β → Bool) :
    ∀ (kept l : List β), Cleanup.pruneAux ok kept l =
      l.foldl (fun kept x ↦ if kept.all (ok · x) then kept ++ [x] else kept) kept
  | _, [] => rfl
  | kept, x :: xs => by rw [Cleanup.pruneAux, List.foldl_cons, pruneAux_eq_foldl]

theorem cleanupL_eq (k Δ : ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) :
    cleanupL k Δ E C = (C.filter (isCliqueL k E)).foldl (pruneStep Δ) [] := by
  rw [cleanupL, Cleanup.prune, pruneAux_eq_foldl]
  rfl

/-! ### The algorithm -/

/-- The number of vertices, capped at one more than the number of adjacency bits. -/
def numV (x : Input) : ℕ := min x.1 (x.2.2.length + 1)

/-- The accuracy exponent `e = (n + 2)^4 (t + 1)`. -/
def accExp (n t : ℕ) : ℕ := (n + 2) ^ 4 * (t + 1)

/-- The accuracy `η = 2^-e`. -/
def accη (n t : ℕ) : ℚ := 1 / 2 ^ accExp n t

/-- The accuracy `γ = 2^-2e`. -/
def accγ (n t : ℕ) : ℚ := 1 / 2 ^ (2 * accExp n t)

/-- The degree `ℓ = 8t + 6` of the clique program. -/
def deg (t : ℕ) : ℕ := 8 * t + 6

/-- `⌈n^(1/m)⌉`: the number of `d ≤ n` with `d^m < n`. -/
def rootCeil (n m : ℕ) : ℕ := ((List.range (n + 1)).filter fun d ↦ decide (d ^ m < n)).length

/-- The input of the solver: the clique program of degree `8t + 6` and the accuracies. -/
def solverInput (x : Input) (t : ℕ) : SoS.Solver.Input :=
  (problemN (numV x) x.2.1 (deg t) (nonEdges (numV x) x.2.2), accη (numV x) t, accγ (numV x) t)

/-- **The algorithm** with parameter `t` and budget `L`. -/
def run (p : (Input × ℕ) × ℕ) : Output :=
  cleanupL p.1.1.2.1 (rootCeil (numV p.1.1) (2 * p.1.2)) (nonEdges (numV p.1.1) p.1.1.2.2)
    ((tuples p.2 (numV p.1.1) (4 * p.1.2)).map
      (roundSet (numV p.1.1) (SoS.Core.core (solverInput p.1.1 p.1.2, p.2))))

/-- **The algorithm** with parameter `t`, with the solver's budget. It does not use its coins. -/
def alg (t : ℕ) (xr : Input × List Bool) : Output :=
  run ((xr.1, t), budget (solverInput xr.1 t))

theorem numV_input {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : numV (input G k) = n :=
  min_eq_left (length_adjBits_ge G)

/-- **Correctness of the algorithm.** On the input of a graph `G` with a `k`-clique there is a
pseudo-expectation `Ẽ` that satisfies the clique program `(η + γ)`-approximately and is
`γ`-optimal among those satisfying it `η`-approximately, such that the output consists of
`k`-cliques of `G`, contains every `S_Q` that is a `k`-clique meeting every other `k`-clique in
fewer than `Δ` vertices, and has at most `(n/k)(1 + 2nΔ/k²)` entries. -/
theorem alg_spec {n k t : ℕ} (G : SimpleGraph (Fin n)) {S : Finset (Fin n)} (hS : G.IsNClique k S)
    (r : List Bool) :
    ∃ E : PseudoExpectation (Fin n) (deg t),
      E.ApproxSatisfies (Clique.problem n k (deg t) (nonEdges n (adjBits G))).system
        ((accη n t : ℝ) + (accγ n t : ℝ)) 0 ∧
      (∀ E' : PseudoExpectation (Fin n) (deg t),
        E'.ApproxSatisfies (Clique.problem n k (deg t) (nonEdges n (adjBits G))).system
          (accη n t : ℝ) 0 →
        (Clique.problem n k (deg t) (nonEdges n (adjBits G))).objective E ≤
          (Clique.problem n k (deg t) (nonEdges n (adjBits G))).objective E' + (accγ n t : ℝ)) ∧
      (∀ l ∈ alg t (input G k, r), G.IsNClique k (vertexSet n l)) ∧
      (∀ (Q : Fin (4 * t) → Fin n) (U : Finset (Fin n)),
        (univ.filter fun i ↦ E (Rounding.wQ Q) ≤ 2 * E (Rounding.wQ Q * X i)) = U →
        G.IsNClique k U → (∀ S', G.IsNClique k S' → S' ≠ U → (S' ∩ U).card < rootCeil n (2 * t)) →
        U ∈ (alg t (input G k, r)).map (vertexSet n)) ∧
      (0 < k → rootCeil n (2 * t) ≤ k → 2 * n * rootCeil n (2 * t) ≤ k ^ 2 →
        ((alg t (input G k, r)).length : ℝ) ≤
          n / k * (1 + 2 * n * rootCeil n (2 * t) / (k : ℝ) ^ 2)) := by
  classical
  set L := nonEdges n (adjBits G)
  have hP := Clique.valid (k := k) (ℓ := deg t) (L := L) ⟨4 * t + 3, by simp [deg]; ring⟩
    (by simp [deg]) hS (onlyNonEdges G)
  have hη : (0 : ℚ) < accη n t := by unfold accη; positivity
  have hγ : (0 : ℚ) < accγ n t := by unfold accγ; positivity
  have hc := SoS.Correct.core_correct _ hP _ _ hη hγ
  have hsi : solverInput (input G k) t = (Clique.problem n k (deg t) L, accη n t, accγ n t) := by
    simp only [solverInput, numV_input, problemN_eq]
    rfl
  have he := SoS.Correct.enough hP (accη n t, accγ n t)
  set B := budget (Clique.problem n k (deg t) L, accη n t, accγ n t) with hB
  set out := SoS.Core.core ((Clique.problem n k (deg t) L, accη n t, accγ n t), B) with hout
  obtain ⟨E, hM, hA, hopt⟩ := hc
  -- The output.
  have hT : n ^ (4 * t) ≤ B := by
    calc n ^ (4 * t) ≤ (n + 1) ^ deg t :=
          (Nat.pow_le_pow_left (by omega) _).trans
            (Nat.pow_le_pow_right (by omega) (by simp only [deg]; omega))
      _ ≤ B := he.vars
  set C := (tuples B n (4 * t)).map (roundSet n out) with hC
  have hgood : ∀ S ∈ C, Good n S := by
    intro S hS'
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hS'
    exact good_roundSet n out q
  have halg : alg t (input G k, r) = cleanupL k (rootCeil n (2 * t)) L C := by
    simp only [alg, hsi, run, numV_input]
    rfl
  have hmap : (alg t (input G k, r)).map (vertexSet n) =
      Cleanup.cleanup G k (rootCeil n (2 * t)) (C.map (vertexSet n)) := by
    rw [halg]
    exact map_cleanupL G hgood
  refine ⟨E, hA, hopt, fun l hl ↦ ?_, fun Q U hQ hU hother ↦ ?_, fun hk hΔk h2 ↦ ?_⟩
  · have : vertexSet n l ∈ (alg t (input G k, r)).map (vertexSet n) := List.mem_map_of_mem hl
    rw [hmap] at this
    exact Cleanup.isNClique_of_mem_cleanup this
  · rw [hmap]
    refine Cleanup.mem_cleanup ?_ hU hother
    refine List.mem_map.2 ⟨roundSet n out (List.ofFn fun j ↦ (Q j : ℕ)),
      List.mem_map.2 ⟨_, ofFn_mem_tuples hT Q, rfl⟩, ?_⟩
    rw [← hQ]
    exact roundSet_eq hM (by change 4 * t + 1 ≤ 8 * t + 6; omega) Q
  · have := Cleanup.length_cleanup_le (G := G) (C := C.map (vertexSet n)) hk hΔk h2
    rwa [← hmap, List.length_map] at this

end BKS23.Algorithm
