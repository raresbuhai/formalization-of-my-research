module

public import BHSV25.Alg.IndepSetSpectral
public import BHSV25.Spectral.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Background.PolyTime.Rat

/-!
# Rounding a net to an independent set

The algorithm of [BHSV25, Theorem 7.20] for a given net (`BHSV25.Alg.indepAlg`): each vector `c` of
the net gives the candidate set `{x : c_x ≥ 0}` (`BHSV25.Alg.thrBits`), rounded to an independent
set by removing a greedy maximal matching (`BHSV25.Alg.roundIndep`); so does the set of all
vertices. The algorithm outputs the largest result (`BHSV25.Alg.bestOf`).

The output is an independent set (`BHSV25.Alg.isIndepSet_indepAlg`) at least as large as every
candidate (`BHSV25.Alg.card_cand_le_indepAlg`), and on graphs without edges it has all vertices
(`BHSV25.Alg.card_indepAlg_of_degree_zero`). It runs in polynomial time given a polynomial-time net
(`BHSV25.Alg.indepAlg_polytime`, and `BHSV25.Alg.bestOf'` for the selection).
-/

@[expose] public section

namespace BHSV25.Alg

open Filter Topology Turing.MultiTapeTM ComputableInPolyTime Matrix
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### The largest candidate -/

/-- Keep the larger of `acc` and `r`, by their numbers of members among the first `n`. -/
def bestStep (n : ℕ) (acc r : List Bool) : List Bool :=
  if numTrue n acc < numTrue n r then r else acc

/-- The candidate with the most members, among `init` and the list `L`. -/
def bestOf (n : ℕ) (init : List Bool) (L : List (List Bool)) : List Bool :=
  L.foldl (bestStep n) init

theorem le_numTrue_bestStep_left (n : ℕ) (acc r : List Bool) :
    numTrue n acc ≤ numTrue n (bestStep n acc r) := by
  unfold bestStep
  split_ifs with h
  · exact h.le
  · exact le_rfl

theorem le_numTrue_bestStep_right (n : ℕ) (acc r : List Bool) :
    numTrue n r ≤ numTrue n (bestStep n acc r) := by
  unfold bestStep
  split_ifs with h
  · exact le_rfl
  · exact not_lt.1 h

theorem bestOf_mem (n : ℕ) (init : List Bool) (L : List (List Bool)) :
    bestOf n init L = init ∨ bestOf n init L ∈ L := by
  induction L generalizing init with
  | nil => exact Or.inl rfl
  | cons e L ih =>
    unfold bestOf
    rw [List.foldl_cons]
    rcases ih (bestStep n init e) with h | h
    · unfold bestOf at h
      rw [h]
      unfold bestStep
      split_ifs
      · exact Or.inr List.mem_cons_self
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem le_numTrue_bestOf_init (n : ℕ) (init : List Bool) (L : List (List Bool)) :
    numTrue n init ≤ numTrue n (bestOf n init L) := by
  induction L generalizing init with
  | nil => exact le_rfl
  | cons e L ih =>
    unfold bestOf
    rw [List.foldl_cons]
    exact (le_numTrue_bestStep_left n init e).trans (ih _)

theorem le_numTrue_bestOf {n : ℕ} {init r : List Bool} {L : List (List Bool)} (hr : r ∈ L) :
    numTrue n r ≤ numTrue n (bestOf n init L) := by
  induction L generalizing init with
  | nil => simp at hr
  | cons e L ih =>
    unfold bestOf
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hr with rfl | hr
    · exact (le_numTrue_bestStep_right n init r).trans (le_numTrue_bestOf_init n _ L)
    · exact ih hr

/-! ### The algorithm -/

/-- **The algorithm** of [BHSV25, Theorem 7.20], for a net `net`: the largest of the roundings of
all vertices and of the sets `{x : c_x ≥ 0}` for the vectors `c` of the net. -/
def indepAlg (net : ℕ × List Bool → List (List ℚ)) (x : ℕ × List Bool) : List Bool :=
  bestOf (numV x) (roundIndep (numV x) x.2 (List.replicate (numV x) true))
    ((net x).map fun c ↦ roundIndep (numV x) x.2 (thrBits (numV x) c))

theorem isIndepSet_indepAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) :
    G.2.IsIndepSet (G.vertexSet (indepAlg net (G.1, adjTable G)) : Set (Fin G.1)) := by
  unfold indepAlg
  rw [numV_graph]
  rcases bestOf_mem G.1 (roundIndep G.1 (adjTable G) (List.replicate G.1 true))
    ((net (G.1, adjTable G)).map fun c ↦ roundIndep G.1 (adjTable G) (thrBits G.1 c)) with h | h
  · rw [h]
    exact isIndepSet_roundIndep G _
  · obtain ⟨c, -, hc⟩ := List.mem_map.1 h
    rw [← hc]
    exact isIndepSet_roundIndep G _

theorem card_init_le_indepAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) :
    (G.vertexSet (roundIndep G.1 (adjTable G) (List.replicate G.1 true))).card ≤
      (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  unfold indepAlg
  rw [numV_graph, card_vertexSet, card_vertexSet]
  exact le_numTrue_bestOf_init _ _ _

theorem card_cand_le_indepAlg (net : ℕ × List Bool → List (List ℚ)) (G : Graph) {c : List ℚ}
    (hc : c ∈ net (G.1, adjTable G)) :
    (G.vertexSet (roundIndep G.1 (adjTable G) (thrBits G.1 c))).card ≤
      (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  unfold indepAlg
  rw [numV_graph, card_vertexSet, card_vertexSet]
  exact le_numTrue_bestOf (List.mem_map.2 ⟨c, hc, rfl⟩)

/-! ### Polynomial time -/

theorem thrBits_polytime : ComputableInPolyTime (fun x : ℕ × List ℚ ↦ thrBits x.1 x.2)
    (encPair encUnary (encList encRat)) encBits := by
  unfold thrBits
  have h : ComputableInPolyTime
      (fun x : ℕ × List ℚ ↦ (List.range x.1).map fun i ↦ decide (0 ≤ x.2.getD i 0))
      (encPair encUnary (encList encRat)) (encList encBool) :=
    mapWithInput (by fun_prop)
      (rat_le' (const 0) (listGetDWithInput (by fun_prop) (by fun_prop) 0))
  exact (bits_encList_polyTime encBool).2.comp h

@[fun_prop]
theorem thrBits' {n : α → ℕ} {c : α → List ℚ} (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime c input (encList encRat)) :
    ComputableInPolyTime (fun x ↦ thrBits (n x) (c x)) input encBits :=
  thrBits_polytime.comp (g := fun x ↦ (n x, c x)) (hn.prod hc)

theorem bestStep_polytime : ComputableInPolyTime
    (fun p : (ℕ × List Bool) × List Bool ↦ bestStep p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encBits) encBits) encBits := by
  unfold bestStep
  exact ite_decide (unary_lt' (numTrue' ((fst _ _).comp (fst _ _)) ((snd _ _).comp (fst _ _)))
    (numTrue' ((fst _ _).comp (fst _ _)) (snd _ _))) (snd _ _) ((snd _ _).comp (fst _ _))

theorem bestOf' {n : α → ℕ} {init : α → List Bool} {L : α → List (List Bool)}
    (hn : ComputableInPolyTime n input encUnary) (hinit : ComputableInPolyTime init input encBits)
    (hL : ComputableInPolyTime L input (encList encBits)) :
    ComputableInPolyTime (fun x ↦ bestOf (n x) (init x) (L x)) input encBits := by
  unfold bestOf
  refine foldlWith_of_bounded_growth (par := n) (list := L) (init := init) (step := bestStep)
    hn hL hinit bestStep_polytime (growth := fun x ↦ (encList encBits (L x)).length)
    hL.polyBounded_length ?_
  intro x acc r hr
  have h := SizedListEncoding.length_elem_le (encA := encBits) (encL := encList encBits) _ _ hr
  unfold bestStep
  split_ifs <;> omega

/-! ### The size of the output -/

theorem vertexSet_replicate (G : Graph) : G.vertexSet (List.replicate G.1 true) = Finset.univ := by
  ext v
  simp [Graph.vertexSet, List.getD_eq_getElem?_getD]

open Classical in
/-- Without edges, the algorithm outputs all vertices. -/
theorem card_indepAlg_of_degree_zero (net : ℕ × List Bool → List (List ℚ)) (G : Graph)
    (hd : G.2.IsRegularOfDegree 0) : G.1 ≤ (G.vertexSet (indepAlg net (G.1, adjTable G))).card := by
  have hI : G.2.IsIndepSet ((Finset.univ : Finset (Fin G.1)) : Set (Fin G.1)) := by
    intro u _ v _ _ hadj
    have h := hd u
    rw [SimpleGraph.degree, Finset.card_eq_zero] at h
    have hv : v ∈ G.2.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
    rw [h] at hv
    exact Finset.notMem_empty v hv
  have h := card_inter_le_card_roundIndep G (List.replicate G.1 true) hI
  rw [vertexSet_replicate, Finset.inter_self, Finset.sdiff_self, Finset.card_empty, add_zero,
    Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (card_init_le_indepAlg net G)

/-! ### Theorem 1.1 -/

end BHSV25.Alg
