module

public import BBKS24.Model
public import Background.Pruning
public import Background.Sampling

/-!
# Graphs as lists

The algorithm works on vertex numbers and lists. This file has the list versions of the graph
notions it uses, and their agreement with `SimpleGraph (Fin n)` and `Finset (Fin n)`:

* the pairs `i < j < n` (`BBKS24.Alg.pairs`, in the order of `BBKS24.adjBits` and of
  `Sampling.pairsF`), the non-edges of the input (`BBKS24.Alg.nonEdges`), and the non-edges after
  adding the pairs whose chunk of coins is below `j` (`BBKS24.Alg.nonEdgesAug`,
  `Sampling.chunkGraph`);
* the clique test and the cleanup on lists (`BBKS24.Alg.isCliqueL`, `BBKS24.Alg.cleanupL`), which
  agree with `Pruning.cleanup` (`BBKS24.Alg.map_cleanupL`).

The clique test and the cleanup are those of `BKS23/Algorithm.lean`, for BBKS24's `adjBits` and
`vertexSet`. (They could move to `Background/` once the papers' input conventions are shared.)
-/

@[expose] public section

open Finset Sampling

namespace BBKS24.Alg

/-! ### The pairs and the non-edges -/

/-- The pairs `(i, j)`, `i < j < n`, in lexicographic order: the pairs of `BBKS24.adjBits`. -/
def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i ↦ ((List.range n).filter fun j ↦ decide (i < j)).map fun j ↦ (i, j)

/-- The pairs whose adjacency bit is `false`. -/
def nonEdges (n : ℕ) (a : List Bool) : List (ℕ × ℕ) :=
  (((pairs n).zip a).filter fun p ↦ !p.2).map Prod.fst

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

/-! ### The augmented non-edges -/

/-- The non-edges of the input that stay non-edges after adding the pairs whose chunk of `b` bits
of `r` is below `j`: the `e`-th pair gets the `e`-th chunk. -/
def nonEdgesAug (n b j : ℕ) (a r : List Bool) : List (ℕ × ℕ) :=
  ((((pairs n).zip a).zip (List.range (pairs n).length)).filter fun p ↦
    !p.1.2 && !decide (chunkVal b r p.2 < j)).map fun p ↦ p.1.1

open Classical in
theorem mem_nonEdgesAug {n b j : ℕ} (G : SimpleGraph (Fin n)) (r : List Bool) {e : ℕ × ℕ} :
    e ∈ nonEdgesAug n b j (adjBits G) r ↔
      ∃ u v : Fin n, (u : ℕ) = e.1 ∧ (v : ℕ) = e.2 ∧ u < v ∧
        ¬ (G ⊔ chunkGraph n b j r).Adj u v := by
  classical
  have hlen : (pairs n).length = (pairsF n).length := by rw [pairs_eq, List.length_map]
  have hlenA : (adjBits G).length = (pairsF n).length := by rw [adjBits_eq, List.length_map]
  -- The chunk graph on the `i`-th pair.
  have hchunk : ∀ (i : ℕ) (hi : i < (pairsF n).length),
      (chunkGraph n b j r).Adj (pairsF n)[i].1 (pairsF n)[i].2 ↔ chunkVal b r i < j := by
    intro i hi
    have hlt := mem_pairsF.1 (List.getElem_mem hi)
    have hpe : (pairEquiv n).symm (toPair (pairsF n)[i] hlt) = ⟨i, hi⟩ := by
      rw [Equiv.symm_apply_eq]
      rfl
    simp only [chunkGraph, graphB, RandomGraph.graphOf_adj, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩
      have : (⟨s((pairsF n)[i].1, (pairsF n)[i].2), _⟩ : RandomGraph.Pair (Fin n)) =
          toPair (pairsF n)[i] hlt := rfl
      rw [this, hpe] at h
      exact h
    · intro h
      refine ⟨hlt.ne, ?_⟩
      have : (⟨s((pairsF n)[i].1, (pairsF n)[i].2), _⟩ : RandomGraph.Pair (Fin n)) =
          toPair (pairsF n)[i] hlt := rfl
      rw [this, hpe]
      exact h
  obtain ⟨e1, e2⟩ := e
  simp only [nonEdgesAug, List.mem_map, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨a, a', bit, i, ⟨hmem, hbit, hch⟩, rfl, rfl⟩
    obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.1 hmem
    simp only [List.length_zip, List.length_range, hlen, hlenA, min_self] at hk
    simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at hget
    obtain ⟨⟨he, hb⟩, hik⟩ := hget
    subst hik
    have hP : (pairs n)[k]'(by omega) = (((pairsF n)[k].1 : ℕ), ((pairsF n)[k].2 : ℕ)) := by
      simp [pairs_eq]
    have hA : (adjBits G)[k]'(by omega) = decide (G.Adj (pairsF n)[k].1 (pairsF n)[k].2) := by
      simp [adjBits_eq]
    rw [hP, Prod.mk.injEq] at he
    refine ⟨(pairsF n)[k].1, (pairsF n)[k].2, he.1, he.2,
      mem_pairsF.1 (List.getElem_mem _), ?_⟩
    rw [SimpleGraph.sup_adj, not_or, hchunk k (by omega), not_lt]
    refine ⟨?_, hch⟩
    rw [← hb, hA] at hbit
    simpa using hbit
  · rintro ⟨u, v, rfl, rfl, huv, hG⟩
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (mem_pairsF.2 (show (u, v).1 < (u, v).2 from huv))
    rw [SimpleGraph.sup_adj, not_or] at hG
    have hP : (pairs n)[i]'(by omega) = ((u : ℕ), (v : ℕ)) := by
      simp [pairs_eq, hget]
    have hA : (adjBits G)[i]'(by omega) = decide (G.Adj u v) := by
      simp [adjBits_eq, hget]
    refine ⟨(u : ℕ), (v : ℕ), decide (G.Adj u v), i, ⟨?_, by simpa using hG.1, ?_⟩, rfl, rfl⟩
    · refine List.mem_iff_getElem.2 ⟨i, by simp [hlen, hlenA, hi], ?_⟩
      simp only [List.getElem_zip, List.getElem_range, hP, hA]
    · have := hchunk i hi
      rw [hget] at this
      exact not_lt.1 (fun h ↦ hG.2 (this.2 h))

/-! ### The cleanup on lists -/

/-- Whether `S` has `k` entries and no non-edge (of the list `E`) inside it. -/
def isCliqueL (k : ℕ) (E : List (ℕ × ℕ)) (S : List ℕ) : Bool :=
  decide (S.length = k) && S.all fun i ↦ S.all fun j ↦ !(decide (i < j) && decide ((i, j) ∈ E))

/-- The number of entries of `y` that are in `x`. -/
def interCount (y x : List ℕ) : ℕ := (y.filter fun a ↦ decide (a ∈ x)).length

/-- `Pruning.cleanup` on lists. -/
def cleanupL (k Δ : ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) : List (List ℕ) :=
  Pruning.prune (fun y x ↦ decide (interCount y x < Δ)) (C.filter (isCliqueL k E))

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

/-- `Pruning.cleanup` commutes with `vertexSet` on good lists. -/
theorem map_cleanupL {n k Δ : ℕ} (G : SimpleGraph (Fin n)) {C : List (List ℕ)}
    (hC : ∀ S ∈ C, Good n S) :
    (cleanupL k Δ (nonEdges n (adjBits G)) C).map (vertexSet n) =
      Pruning.cleanup G k Δ (C.map (vertexSet n)) := by
  classical
  rw [cleanupL, Pruning.cleanup, List.filter_map]
  have hf : C.filter ((fun S ↦ decide (G.IsNClique k S)) ∘ vertexSet n) =
      C.filter (isCliqueL k (nonEdges n (adjBits G))) := by
    refine List.filter_congr fun S hS ↦ ?_
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, isCliqueL_iff G (hC S hS), decide_eq_true_eq]
  rw [hf, Pruning.prune, Pruning.prune, ← List.map_nil (f := vertexSet n),
    Pruning.pruneAux_map]
  intro y hy x hx
  simp only [List.nil_append] at hy hx
  rw [card_inter_vertexSet (hC y (List.mem_filter.1 hy).1)]

/-- The pruning step, for a fold. -/
def pruneStep (Δ : ℕ) (kept : List (List ℕ)) (x : List ℕ) : List (List ℕ) :=
  if kept.all (fun y ↦ decide (interCount y x < Δ)) then kept ++ [x] else kept

theorem pruneAux_eq_foldl {β : Type*} (ok : β → β → Bool) :
    ∀ (kept l : List β), Pruning.pruneAux ok kept l =
      l.foldl (fun kept x ↦ if kept.all (ok · x) then kept ++ [x] else kept) kept
  | _, [] => rfl
  | kept, x :: xs => by rw [Pruning.pruneAux, List.foldl_cons, pruneAux_eq_foldl]

theorem cleanupL_eq (k Δ : ℕ) (E : List (ℕ × ℕ)) (C : List (List ℕ)) :
    cleanupL k Δ E C = (C.filter (isCliqueL k E)).foldl (pruneStep Δ) [] := by
  rw [cleanupL, Pruning.prune, pruneAux_eq_foldl]
  rfl

end BBKS24.Alg
