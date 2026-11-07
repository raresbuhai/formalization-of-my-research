module

public import BKS23.Algorithm

/-!
# The algorithm of Theorem 5.6 (1)

The algorithm of [BKS23, Theorem 5.6 (1)], as a function on the encoded input
(`BKS23.Algorithm.run1`), with a budget `L`:

1. Read `n`, `k` and the non-edges, as in `BKS23.Algorithm.run`.
2. Run the sum-of-squares solver on the clique program of degree `6` (`solverInput x 0`).
3. For every vertex `i`, form `S_i = {j | Ẽ[wᵢ] ≤ 2 Ẽ[wᵢ wⱼ]}` (`BKS23.Algorithm.roundSet` with the
   tuple `[i]`), and for every threshold `τ ≤ n` the refinement
   `{v | v has at least τ neighbours in S_i}` (`BKS23.Algorithm.refineSet`).
4. Clean up with the threshold `Δ = ⌊k² / (n (log₂ n + 1))⌋ + 1` (`BKS23.Algorithm.delta1`).

The paper's algorithm knows `p` and refines `S_i` with a threshold depending on `p`
([BKS23, Claim 5.9]); trying every threshold needs no `p`.
-/

@[expose] public section

namespace BKS23.Algorithm

open SoS SoS.Solver MvPolynomial Finset

/-! ### The refinement -/

/-- Whether `u` and `v` are adjacent, given the list `E` of non-edges (as pairs `(i, j)`,
`i < j`): `u ≠ v`, and neither `(u, v)` nor `(v, u)` is a non-edge. -/
def adjL (E : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  !(u == v) && !decide ((u, v) ∈ E) && !decide ((v, u) ∈ E)

/-- The number of neighbours of `v` in `S`. -/
def nbrCount (E : List (ℕ × ℕ)) (S : List ℕ) (v : ℕ) : ℕ := S.countP fun u ↦ adjL E u v

/-- The refinement of `S` at threshold `τ`: the vertices with at least `τ` neighbours in `S`. -/
def refineSet (n : ℕ) (E : List (ℕ × ℕ)) (S : List ℕ) (τ : ℕ) : List ℕ :=
  (List.range n).filter fun v ↦ decide (τ ≤ nbrCount E S v)

/-- The candidates: every refinement of every `S_i`. -/
def candidates1 (n : ℕ) (E : List (ℕ × ℕ)) (out : RawPoly) : List (List ℕ) :=
  (List.range n).flatMap fun i ↦ (List.range (n + 1)).map (refineSet n E (roundSet n out [i]))

/-- The cleanup threshold `Δ = ⌊k² / (n (log₂ n + 1))⌋ + 1`. -/
def delta1 (n k : ℕ) : ℕ := k * k / (n * (Nat.log 2 n + 1)) + 1

/-! ### The algorithm -/

/-- **The algorithm of Theorem 5.6 (1)** with budget `L`. -/
def run1 (p : Input × ℕ) : Output :=
  cleanupL p.1.2.1 (delta1 (numV p.1) p.1.2.1) (nonEdges (numV p.1) p.1.2.2)
    (candidates1 (numV p.1) (nonEdges (numV p.1) p.1.2.2)
      (SoS.Core.core (solverInput p.1 0, p.2)))

/-- **The algorithm of Theorem 5.6 (1)**, with the solver's budget. It does not use its coins. -/
def alg1 (xr : Input × List Bool) : Output :=
  run1 (xr.1, budget (solverInput xr.1 0))

/-! ### Correctness -/

theorem mem_nonEdges_val {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    ((u : ℕ), (v : ℕ)) ∈ nonEdges n (adjBits G) ↔ u < v ∧ ¬ G.Adj u v := by
  rw [mem_nonEdges]
  constructor
  · rintro ⟨a, b, ha, hb, hab, hG⟩
    obtain rfl := Fin.ext ha
    obtain rfl := Fin.ext hb
    exact ⟨hab, hG⟩
  · rintro ⟨huv, hG⟩
    exact ⟨u, v, rfl, rfl, huv, hG⟩

/-- On the non-edges of `G`, `BKS23.Algorithm.adjL` is the adjacency of `G`. -/
theorem adjL_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    adjL (nonEdges n (adjBits G)) u v = true ↔ G.Adj u v := by
  simp only [adjL, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    decide_eq_false_iff_not, mem_nonEdges_val, ne_eq, Fin.val_inj]
  constructor
  · rintro ⟨⟨huv, h1⟩, h2⟩
    rcases lt_or_gt_of_ne huv with h | h
    · by_contra hG
      exact h1 ⟨h, hG⟩
    · by_contra hG
      exact h2 ⟨h, fun h' ↦ hG h'.symm⟩
  · intro hG
    exact ⟨⟨G.ne_of_adj hG, fun h ↦ h.2 hG⟩, fun h ↦ h.2 hG.symm⟩

theorem good_refineSet (n : ℕ) (E : List (ℕ × ℕ)) (S : List ℕ) (τ : ℕ) :
    Good n (refineSet n E S τ) :=
  ⟨List.nodup_range.filter _, fun _ hi ↦ List.mem_range.1 (List.mem_filter.1 hi).1⟩

open Classical in
/-- `BKS23.Algorithm.nbrCount` counts the neighbours in `G`. -/
theorem nbrCount_eq {n : ℕ} (G : SimpleGraph (Fin n)) {S : List ℕ} (hS : Good n S) (v : Fin n) :
    nbrCount (nonEdges n (adjBits G)) S v = ((vertexSet n S).filter fun u ↦ G.Adj u v).card := by
  have hf : Good n (S.filter fun u ↦ adjL (nonEdges n (adjBits G)) u v) :=
    ⟨hS.1.filter _, fun i hi ↦ hS.2 i (List.mem_filter.1 hi).1⟩
  rw [nbrCount, List.countP_eq_length_filter, ← card_vertexSet hf]
  congr 1
  ext u
  simp only [vertexSet, mem_filter, mem_univ, true_and, List.mem_filter, adjL_iff]

open Classical in
/-- The refinement `{v | τ ≤ |N(v) ∩ S|}`. -/
theorem vertexSet_refineSet {n : ℕ} (G : SimpleGraph (Fin n)) {S : List ℕ} (hS : Good n S)
    (τ : ℕ) :
    vertexSet n (refineSet n (nonEdges n (adjBits G)) S τ) =
      univ.filter fun v ↦ τ ≤ ((vertexSet n S).filter fun u ↦ G.Adj u v).card := by
  ext v
  simp only [mem_filter, mem_univ, true_and, ← nbrCount_eq G hS]
  simp [vertexSet, refineSet]

/-- `S_i = {j | Ẽ[wᵢ] ≤ 2 Ẽ[wᵢ wⱼ]}`, from the moments. -/
theorem roundSet_single {n : ℕ} {E : PseudoExpectation (Fin n) (deg 0)} {out : RawPoly}
    (hM : HasMoments E (out.toPoly n)) (i : Fin n) :
    vertexSet n (roundSet n out [(i : ℕ)]) =
      univ.filter fun j ↦ E (X i) ≤ 2 * E (X i * X j) := by
  have h := roundSet_eq hM (T := 1) (by simp [deg]) ![i]
  have hw : Rounding.wQ ![i] = X i := by simp [Rounding.wQ]
  have hl : (List.ofFn fun j : Fin 1 ↦ ((![i] j : Fin n) : ℕ)) = [(i : ℕ)] := by simp
  rw [hl, hw] at h
  exact h

theorem mem_candidates1 {n : ℕ} (E : List (ℕ × ℕ)) (out : RawPoly) {i τ : ℕ} (hi : i < n)
    (hτ : τ ≤ n) : refineSet n E (roundSet n out [i]) τ ∈ candidates1 n E out :=
  List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨τ, List.mem_range.2 (by omega), rfl⟩⟩

theorem good_of_mem_candidates1 {n : ℕ} {E : List (ℕ × ℕ)} {out : RawPoly} {S : List ℕ}
    (hS : S ∈ candidates1 n E out) : Good n S := by
  simp only [candidates1, List.mem_flatMap, List.mem_map] at hS
  obtain ⟨i, -, τ, -, rfl⟩ := hS
  exact good_refineSet _ _ _ _

open Classical in
/-- **Correctness of the algorithm.** On the input of a graph `G` with a `k`-clique there is a
pseudo-expectation `Ẽ` that satisfies the clique program of degree `6` `(η + γ)`-approximately and
is `γ`-optimal among those satisfying it `η`-approximately, such that the output consists of
`k`-cliques of `G`, contains every refinement `{v | τ ≤ |N(v) ∩ S_i|}` of every
`S_i = {j | Ẽ[wᵢ] ≤ 2 Ẽ[wᵢ wⱼ]}` that is a `k`-clique meeting every other `k`-clique in fewer
than `Δ` vertices, and has at most `(n/k)(1 + 2nΔ/k²)` entries. -/
theorem alg1_spec {n k : ℕ} (G : SimpleGraph (Fin n)) {S : Finset (Fin n)} (hS : G.IsNClique k S)
    (r : List Bool) :
    ∃ E : PseudoExpectation (Fin n) (deg 0),
      E.ApproxSatisfies (Clique.problem n k (deg 0) (nonEdges n (adjBits G))).system
        ((accη n 0 : ℝ) + (accγ n 0 : ℝ)) 0 ∧
      (∀ E' : PseudoExpectation (Fin n) (deg 0),
        E'.ApproxSatisfies (Clique.problem n k (deg 0) (nonEdges n (adjBits G))).system
          (accη n 0 : ℝ) 0 →
        (Clique.problem n k (deg 0) (nonEdges n (adjBits G))).objective E ≤
          (Clique.problem n k (deg 0) (nonEdges n (adjBits G))).objective E' + (accγ n 0 : ℝ)) ∧
      (∀ l ∈ alg1 (input G k, r), G.IsNClique k (vertexSet n l)) ∧
      (∀ (i : Fin n) (τ : ℕ) (U : Finset (Fin n)), τ ≤ n →
        (univ.filter fun v ↦ τ ≤ ((univ.filter fun j ↦ E (X i) ≤ 2 * E (X i * X j)).filter
          fun u ↦ G.Adj u v).card) = U →
        G.IsNClique k U → (∀ S', G.IsNClique k S' → S' ≠ U → (S' ∩ U).card < delta1 n k) →
        U ∈ (alg1 (input G k, r)).map (vertexSet n)) ∧
      (0 < k → delta1 n k ≤ k → 2 * n * delta1 n k ≤ k ^ 2 →
        ((alg1 (input G k, r)).length : ℝ) ≤ n / k * (1 + 2 * n * delta1 n k / (k : ℝ) ^ 2)) := by
  classical
  set L := nonEdges n (adjBits G)
  have hP := Clique.valid (k := k) (ℓ := deg 0) (L := L) ⟨3, by simp [deg]⟩ (by simp [deg]) hS
    (onlyNonEdges G)
  have hη : (0 : ℚ) < accη n 0 := by unfold accη; positivity
  have hγ : (0 : ℚ) < accγ n 0 := by unfold accγ; positivity
  have hc := SoS.Correct.core_correct _ hP _ _ hη hγ
  have hsi : solverInput (input G k) 0 = (Clique.problem n k (deg 0) L, accη n 0, accγ n 0) := by
    simp only [solverInput, numV_input, problemN_eq]
    rfl
  set B := budget (Clique.problem n k (deg 0) L, accη n 0, accγ n 0) with hB
  set out := SoS.Core.core ((Clique.problem n k (deg 0) L, accη n 0, accγ n 0), B) with hout
  obtain ⟨E, hM, hA, hopt⟩ := hc
  -- The output.
  set C := candidates1 n L out with hC
  have halg : alg1 (input G k, r) = cleanupL k (delta1 n k) L C := by
    simp only [alg1, hsi, run1, numV_input]
    rfl
  have hmap : (alg1 (input G k, r)).map (vertexSet n) =
      Cleanup.cleanup G k (delta1 n k) (C.map (vertexSet n)) := by
    rw [halg]
    exact map_cleanupL G fun S hS ↦ good_of_mem_candidates1 hS
  refine ⟨E, hA, hopt, fun l hl ↦ ?_, fun i τ U hτ hU hUc hother ↦ ?_, fun hk hΔk h2 ↦ ?_⟩
  · have : vertexSet n l ∈ (alg1 (input G k, r)).map (vertexSet n) := List.mem_map_of_mem hl
    rw [hmap] at this
    exact Cleanup.isNClique_of_mem_cleanup this
  · rw [hmap]
    refine Cleanup.mem_cleanup (List.mem_map.2 ⟨_, mem_candidates1 L out i.2 hτ, ?_⟩) hUc hother
    have hround := roundSet_single (n := n) (E := E) hM i
    rw [← hU, vertexSet_refineSet G (good_roundSet n out _), hround]
  · have := Cleanup.length_cleanup_le (G := G) (C := C.map (vertexSet n)) hk hΔk h2
    rwa [← hmap, List.length_map] at this

end BKS23.Algorithm
