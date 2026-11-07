module

public import BHSV25.Alg.Cluster
public import Background.TuplesPolyTime
public import Background.PolyTime.Rat

/-!
# The clustering algorithm runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the clustering algorithm
`BHSV25.Alg.clusterAlg` of `BHSV25/Alg/Cluster.lean`, for every number `m` of clusters and every
uncolored mark `K`, given a polynomial-time net (`BHSV25.Alg.clusterAlg_polytime`), and on graphs
encoded by `BHSV25.encGraph` (`BHSV25.Alg.clusterAlg_graph_polytime`).

Encodings: inside the algorithm, the number of vertices, vertex numbers, cluster indices, colors,
the number of vectors of the net and the budget of the tuples are in unary (all are polynomial in
the input, since `m` is fixed), and vectors are lists of rationals (`Encoding.encRat`). The output
lists the colors in binary (`BHSV25.encColoring`).

The two loops are folds whose states stay small:

* the search for the nearest representative (`BHSV25.Alg.argminBelow`) keeps an index below the
  number of representatives (`BHSV25.Alg.argminBelow'`);
* the selection of the best candidate (`BHSV25.Alg.bestColoring`) keeps `[]` or one of the
  candidates
  (`BHSV25.Alg.bestColoring'`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Clustering -/

theorem sqDist_polytime : ComputableInPolyTime
    (fun x : List (List ℚ) × ℕ × ℕ ↦ sqDist x.1 x.2.1 x.2.2)
    (encPair (encList (encList encRat)) (encPair encUnary encUnary)) encRat := by
  unfold sqDist
  refine rat_sum' (mapWithInput (fst _ _) (rat_sq' (rat_sub' ?_ ?_)))
  · exact listGetDWithInput (snd _ _) (by fun_prop) 0
  · exact listGetDWithInput (snd _ _) (by fun_prop) 0

@[fun_prop]
theorem sqDist' {us : α → List (List ℚ)} {y z : α → ℕ}
    (hus : ComputableInPolyTime us input (encList (encList encRat)))
    (hy : ComputableInPolyTime y input encUnary) (hz : ComputableInPolyTime z input encUnary) :
    ComputableInPolyTime (fun a ↦ sqDist (us a) (y a) (z a)) input encRat :=
  sqDist_polytime.comp (g := fun a ↦ (us a, y a, z a)) (hus.prod (hy.prod hz))

/-- One step of the search for a minimizer of a function `f` that may depend on the input. -/
theorem argminStep_polytime {f : α → ℕ → ℚ}
    (hf : ComputableInPolyTime (fun p : α × ℕ ↦ f p.1 p.2) (encPair input encUnary) encRat) :
    ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ argminStep (f p.1.1) p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encUnary := by
  unfold argminStep
  have h1 : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ f p.1.1 p.2)
      (encPair (encPair input encUnary) encUnary) encRat :=
    hf.comp (g := fun p : (α × ℕ) × ℕ ↦ (p.1.1, p.2)) (((fst _ _).comp (fst _ _)).prod (snd _ _))
  have h2 : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ f p.1.1 p.1.2)
      (encPair (encPair input encUnary) encUnary) encRat :=
    hf.comp (g := fun p : (α × ℕ) × ℕ ↦ p.1) (fst _ _)
  have h3 : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ p.1.2)
      (encPair (encPair input encUnary) encUnary) encUnary :=
    (snd _ _).comp (fst _ _)
  exact ite_decide (rat_lt' h1 h2) (snd _ _) h3

/-- **The search for a minimizer** among `0, …, m - 1`: a fold whose state is an index below
`max m 1`. -/
theorem argminBelow' {f : α → ℕ → ℚ} {m : α → ℕ}
    (hf : ComputableInPolyTime (fun p : α × ℕ ↦ f p.1 p.2) (encPair input encUnary) encRat)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun a ↦ argminBelow (f a) (m a)) input encUnary := by
  unfold argminBelow
  refine foldlWithInput_of_bounded_growth (step := fun a b c ↦ argminStep (f a) b c) (const 0)
    ⟨unary_range' hm, argminStep_polytime hf, inferInstance, inferInstance⟩
    ⟨hm.polyBounded, fun a b c hc ↦ ?_⟩
  rw [List.mem_range] at hc
  simp only [encUnary_apply, List.length_replicate]
  unfold argminStep
  split_ifs <;> omega

theorem clusterIdx_polytime : ComputableInPolyTime
    (fun x : (List (List ℚ) × List ℕ) × ℕ ↦ clusterIdx x.1.1 x.1.2 x.2)
    (encPair (encPair (encList (encList encRat)) (encList encUnary)) encUnary) encUnary := by
  have h : ComputableInPolyTime
      (fun p : ((List (List ℚ) × List ℕ) × ℕ) × ℕ ↦ sqDist p.1.1.1 p.1.2 (p.1.1.2.getD p.2 0))
      (encPair (encPair (encPair (encList (encList encRat)) (encList encUnary)) encUnary)
        encUnary) encRat :=
    sqDist' (by fun_prop) (by fun_prop) (listGetDWithInput (by fun_prop) (snd _ _) 0)
  have hm : ComputableInPolyTime (fun x : (List (List ℚ) × List ℕ) × ℕ ↦ x.1.2.length)
      (encPair (encPair (encList (encList encRat)) (encList encUnary)) encUnary) encUnary :=
    (length_list encUnary).comp ((snd _ _).comp (fst _ _))
  have hc := argminBelow'
    (input := encPair (encPair (encList (encList encRat)) (encList encUnary)) encUnary)
    (f := fun (x : (List (List ℚ) × List ℕ) × ℕ) a ↦ sqDist x.1.1 x.2 (x.1.2.getD a 0))
    (m := fun x ↦ x.1.2.length) h hm
  unfold clusterIdx
  exact hc

@[fun_prop]
theorem clusters' {n : α → ℕ} {us : α → List (List ℚ)} {xs : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hus : ComputableInPolyTime us input (encList (encList encRat)))
    (hxs : ComputableInPolyTime xs input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ clusters (n a) (us a) (xs a)) input (encList encUnary) := by
  unfold clusters
  exact mapWithInput (unary_range' hn) (clusterIdx_polytime.comp
    (g := fun p : α × ℕ ↦ ((us p.1, xs p.1), p.2))
    (((hus.comp (fst _ _)).prod (hxs.comp (fst _ _))).prod (snd _ _)))

/-! ### Rounding the clusters -/

theorem classBits_polytime (m : ℕ) : ComputableInPolyTime
    (fun x : ℕ × List ℕ × ℕ ↦ classBits x.1 m x.2.1 x.2.2)
    (encPair encUnary (encPair (encList encUnary) encUnary)) encBits := by
  unfold classBits
  have h : ComputableInPolyTime (fun x : ℕ × List ℕ × ℕ ↦
      (List.range x.1).map fun y ↦ decide (x.2.1.getD y m = x.2.2))
      (encPair encUnary (encPair (encList encUnary) encUnary)) (encList encBool) :=
    mapWithInput (unary_range' (fst _ _))
      (unary_eq' (listGetDWithInput (by fun_prop) (snd _ _) m) (by fun_prop))
  exact (bits_encList_polyTime encBool).2.comp h

@[fun_prop]
theorem classBits' (m : ℕ) {n : α → ℕ} {p : α → List ℕ} {c : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hp : ComputableInPolyTime p input (encList encUnary))
    (hc : ComputableInPolyTime c input encUnary) :
    ComputableInPolyTime (fun a ↦ classBits (n a) m (p a) (c a)) input encBits :=
  (classBits_polytime m).comp (g := fun a ↦ (n a, p a, c a)) (hn.prod (hp.prod hc))

@[fun_prop]
theorem roundedClasses' (m : ℕ) {n : α → ℕ} {adj : α → List Bool} {p : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hp : ComputableInPolyTime p input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ roundedClasses (n a) m (adj a) (p a)) input
      (encList encBits) := by
  unfold roundedClasses
  exact mapWithInput (unary_range' (const m)) (roundIndep' (hn.comp (fst _ _))
    (hadj.comp (fst _ _)) (classBits' m (hn.comp (fst _ _)) (hp.comp (fst _ _)) (snd _ _)))

theorem colorWith_polytime (m K : ℕ) : ComputableInPolyTime
    (fun x : ℕ × List (List Bool) × List ℕ ↦ colorWith x.1 m K x.2.1 x.2.2)
    (encPair encUnary (encPair (encList encBits) (encList encUnary))) (encList encUnary) := by
  unfold colorWith
  have hpy : ComputableInPolyTime (fun q : (ℕ × List (List Bool) × List ℕ) × ℕ ↦ q.1.2.2.getD q.2 m)
      (encPair (encPair encUnary (encPair (encList encBits) (encList encUnary))) encUnary)
      encUnary :=
    listGetDWithInput (by fun_prop) (snd _ _) m
  have hc : ComputableInPolyTime (fun q : (ℕ × List (List Bool) × List ℕ) × ℕ ↦
      (q.1.2.1.getD (q.1.2.2.getD q.2 m) []).getD q.2 false)
      (encPair (encPair encUnary (encPair (encList encBits) (encList encUnary))) encUnary)
      encBool :=
    bitsGetDWithInput (listGetDWithInput (by fun_prop) hpy []) (snd _ _) false
  exact mapWithInput (unary_range' (fst _ _)) (ite' hc hpy (const K))

@[fun_prop]
theorem colorOf' (m K : ℕ) {n : α → ℕ} {adj : α → List Bool} {p : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hp : ComputableInPolyTime p input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ colorOf (n a) m K (adj a) (p a)) input (encList encUnary) := by
  unfold colorOf
  exact (colorWith_polytime m K).comp
    (g := fun a ↦ (n a, roundedClasses (n a) m (adj a) (p a), p a))
    (hn.prod ((roundedClasses' m hn hadj hp).prod hp))

/-! ### Choosing the best coloring -/

@[fun_prop]
theorem numCol' (K : ℕ) {n : α → ℕ} {c : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ numCol (n a) K (c a)) input encUnary := by
  unfold numCol
  exact (length_list encUnary).comp (filterWithInput (unary_range' hn)
    (unary_lt' (listGetDWithInput (hc.comp (fst _ _)) (snd _ _) K) (const K)))

theorem bestColorStep_polytime (K : ℕ) : ComputableInPolyTime
    (fun p : (ℕ × List ℕ) × List ℕ ↦ bestColorStep p.1.1 K p.1.2 p.2)
    (encPair (encPair encUnary (encList encUnary)) (encList encUnary)) (encList encUnary) := by
  unfold bestColorStep
  have hn : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ ↦ p.1.1)
      (encPair (encPair encUnary (encList encUnary)) (encList encUnary)) encUnary :=
    (fst _ _).comp (fst _ _)
  have hb : ComputableInPolyTime (fun p : (ℕ × List ℕ) × List ℕ ↦ p.1.2)
      (encPair (encPair encUnary (encList encUnary)) (encList encUnary)) (encList encUnary) :=
    (snd _ _).comp (fst _ _)
  exact ite_decide (unary_lt' (numCol' K hn hb) (numCol' K hn (snd _ _))) (snd _ _) hb

/-- **The selection of the best candidate**: a fold whose state is `[]` or one of the
candidates. -/
@[fun_prop]
theorem bestColoring' (K : ℕ) {n : α → ℕ} {cs : α → List (List ℕ)}
    (hn : ComputableInPolyTime n input encUnary)
    (hcs : ComputableInPolyTime cs input (encList (encList encUnary))) :
    ComputableInPolyTime (fun a ↦ bestColoring (n a) K (cs a)) input (encList encUnary) := by
  unfold bestColoring
  refine foldlWith_of_bounded_growth (par := n) (step := fun n b c ↦ bestColorStep n K b c) hn hcs
    (const []) (bestColorStep_polytime K) hcs.polyBounded_length ?_
  intro a b c hc
  unfold bestColorStep
  split_ifs
  · exact (SizedListEncoding.length_elem_le (encA := encList encUnary)
      (encL := encList (encList encUnary)) _ _ hc).trans (Nat.le_add_left _ _)
  · exact Nat.le_add_right _ _

/-! ### The candidates -/

@[fun_prop]
theorem clusterBudget' (m : ℕ) {n N : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hN : ComputableInPolyTime N input encUnary) :
    ComputableInPolyTime (fun a ↦ clusterBudget (n a) (N a) m) input encUnary := by
  unfold clusterBudget
  exact (unary_pow m).comp (unary_add' (unary_add' hn hN) (const 1))

/-- The tuples with all three numbers in unary, the entries in unary. -/
theorem tuplesUnary' {L n T : α → ℕ} (hL : ComputableInPolyTime L input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hT : ComputableInPolyTime T input encUnary) :
    ComputableInPolyTime (fun a ↦ Tuples.tuples (L a) (n a) (T a)) input
      (encList (encList encUnary)) :=
  Tuples.tuples_unary_polytime.comp (g := fun a ↦ (L a, n a, T a)) (hL.prod (hn.prod hT))

/-- One candidate: the rounded clusters of the vectors of `U` numbered `is` and the
representatives `xs`. -/
theorem candidate' (m K : ℕ) {n : α → ℕ} {adj : α → List Bool} {U : α → List (List ℚ)}
    {is xs : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hU : ComputableInPolyTime U input (encList (encList encRat)))
    (his : ComputableInPolyTime is input (encList encUnary))
    (hxs : ComputableInPolyTime xs input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦
      colorOf (n a) m K (adj a) (clusters (n a) ((is a).map fun i ↦ (U a).getD i []) (xs a)))
      input (encList encUnary) := by
  have hU1 : ComputableInPolyTime (fun p : α × ℕ ↦ U p.1) (encPair input encUnary)
      (encList (encList encRat)) := hU.comp (fst _ _)
  have hus : ComputableInPolyTime (fun a ↦ (is a).map fun i ↦ (U a).getD i []) input
      (encList (encList encRat)) :=
    mapWithInput his (listGetDWithInput hU1 (snd _ _) [])
  exact colorOf' m K hn hadj (clusters' hn hus hxs)

theorem candidates_polytime (m K : ℕ) : ComputableInPolyTime
    (fun x : ℕ × List Bool × List (List ℚ) ↦ candidates x.1 m K x.2.1 x.2.2)
    (encPair encUnary (encPair encBits (encList (encList encRat))))
    (encList (encList encUnary)) := by
  unfold candidates
  have hn : ComputableInPolyTime (fun x : ℕ × List Bool × List (List ℚ) ↦ x.1)
      (encPair encUnary (encPair encBits (encList (encList encRat)))) encUnary := fst _ _
  have hU : ComputableInPolyTime (fun x : ℕ × List Bool × List (List ℚ) ↦ x.2.2)
      (encPair encUnary (encPair encBits (encList (encList encRat))))
      (encList (encList encRat)) := (snd _ _).comp (snd _ _)
  have hN : ComputableInPolyTime (fun x : ℕ × List Bool × List (List ℚ) ↦ x.2.2.length)
      (encPair encUnary (encPair encBits (encList (encList encRat)))) encUnary :=
    (length_list _).comp hU
  have hL := clusterBudget' m hn hN
  -- The input with the tuple `is` of vectors.
  have hn1 : ComputableInPolyTime (fun p : (ℕ × List Bool × List (List ℚ)) × List ℕ ↦ p.1.1)
      (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) encUnary := hn.comp (fst _ _)
  have hL1 : ComputableInPolyTime (fun p : (ℕ × List Bool × List (List ℚ)) × List ℕ ↦
      clusterBudget p.1.1 p.1.2.2.length m)
      (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) encUnary := hL.comp (fst _ _)
  -- The input with the tuples `is` of vectors and `xs` of representatives.
  have hn2 : ComputableInPolyTime
      (fun q : ((ℕ × List Bool × List (List ℚ)) × List ℕ) × List ℕ ↦ q.1.1.1)
      (encPair (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) (encList encUnary)) encUnary := hn1.comp (fst _ _)
  have hadj2 : ComputableInPolyTime
      (fun q : ((ℕ × List Bool × List (List ℚ)) × List ℕ) × List ℕ ↦ q.1.1.2.1)
      (encPair (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) (encList encUnary)) encBits := by fun_prop
  have hU2 : ComputableInPolyTime
      (fun q : ((ℕ × List Bool × List (List ℚ)) × List ℕ) × List ℕ ↦ q.1.1.2.2)
      (encPair (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) (encList encUnary)) (encList (encList encRat)) := by fun_prop
  have his2 : ComputableInPolyTime
      (fun q : ((ℕ × List Bool × List (List ℚ)) × List ℕ) × List ℕ ↦ q.1.2)
      (encPair (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) (encList encUnary)) (encList encUnary) := by fun_prop
  have hin : ComputableInPolyTime (fun p : (ℕ × List Bool × List (List ℚ)) × List ℕ ↦
      (Tuples.tuples (clusterBudget p.1.1 p.1.2.2.length m) p.1.1 m).map fun xs ↦
        colorOf p.1.1 m K p.1.2.1 (clusters p.1.1 (p.2.map fun i ↦ p.1.2.2.getD i []) xs))
      (encPair (encPair encUnary (encPair encBits (encList (encList encRat))))
        (encList encUnary)) (encList (encList encUnary)) :=
    mapWithInput (tuplesUnary' hL1 hn1 (const m))
      (candidate' m K hn2 hadj2 hU2 his2 (snd _ _))
  exact flatMapWithInput (tuplesUnary' hL hN (const m)) hin

@[fun_prop]
theorem candidates' (m K : ℕ) {n : α → ℕ} {adj : α → List Bool} {U : α → List (List ℚ)}
    (hn : ComputableInPolyTime n input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hU : ComputableInPolyTime U input (encList (encList encRat))) :
    ComputableInPolyTime (fun a ↦ candidates (n a) m K (adj a) (U a)) input
      (encList (encList encUnary)) :=
  (candidates_polytime m K).comp (g := fun a ↦ (n a, adj a, U a)) (hn.prod (hadj.prod hU))

/-! ### The algorithm -/

/-- The algorithm, with the colors in unary. -/
theorem clusterAlg_unary (m K : ℕ) {net : ℕ × List Bool → List (List ℚ)}
    (hnet : ComputableInPolyTime net (encPair encNat encBits) (encList (encList encRat))) :
    ComputableInPolyTime (clusterAlg m K net) (encPair encNat encBits) (encList encUnary) :=
  bestColoring' K numV_polytime (candidates' m K numV_polytime (snd _ _) hnet)

/-- Lists of numbers from unary to binary. -/
theorem unaryList_to_binary :
    ComputableInPolyTime (fun l : List ℕ ↦ l) (encList encUnary) (encList encNat) := by
  have h : ComputableInPolyTime (fun l : List ℕ ↦ l.map fun i ↦ i) (encList encUnary)
      (encList encNat) :=
    mapWithInput id' (unary_to_binary.comp (snd _ _))
  simpa only [List.map_id'] using h

/-- **The clustering algorithm runs in polynomial time**, given a polynomial-time net. -/
theorem clusterAlg_polytime (m K : ℕ) {net : ℕ × List Bool → List (List ℚ)}
    (hnet : ComputableInPolyTime net (Encoding.encPair Encoding.encNat Encoding.encBits)
      (Encoding.encList (Encoding.encList Encoding.encRat))) :
    ComputableInPolyTime (clusterAlg m K net) (Encoding.encPair Encoding.encNat Encoding.encBits)
      encColoring :=
  unaryList_to_binary.comp (clusterAlg_unary m K hnet)

/-- The clustering algorithm on graphs, encoded by their adjacency tables. -/
theorem clusterAlg_graph_polytime (m K : ℕ) {net : ℕ × List Bool → List (List ℚ)}
    (hnet : ComputableInPolyTime net (Encoding.encPair Encoding.encNat Encoding.encBits)
      (Encoding.encList (Encoding.encList Encoding.encRat))) :
    ComputableInPolyTime (fun G : Graph ↦ clusterAlg m K net (G.1, adjTable G)) encGraph
      encColoring := by
  have he : ComputableInPolyTime (fun G : Graph ↦ (G.1, adjTable G)) encGraph
      (encPair encNat encBits) := of_eq fun _ ↦ rfl
  exact (clusterAlg_polytime m K hnet).comp he

end Alg

end BHSV25
