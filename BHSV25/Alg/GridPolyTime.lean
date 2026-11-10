module

public import BHSV25.Alg.GridCluster
public import BHSV25.Alg.ClusterPolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-!
# The grid clustering runs in polynomial time

`BHSV25.Alg.gridAlg_polytime`: the grid clustering algorithm, as one machine reading the number
`m` of clusters, the uncolored mark `K₀`, the scale `S`, the range `K` and the budget `B` in unary,
together with the list `U` of net vectors and the graph, runs in polynomial time. Unlike the
certificates of `BHSV25/Alg/ClusterPolyTime.lean`, which fix `m` and `K₀`, these read them from
the input, so that the degree of the polynomial does not depend on them (in Theorem 7.1, `m` is
the number of distinct rows of the model).

The loops are those of `BHSV25.Alg.clusterAlg` (the search for the nearest center and the selection
of the best candidate) and the tuples, cut at the budget.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Lookups with a default read from the input -/

/-- A unary natural, in binary. -/
theorem toBin' {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (g := f) hf.tidy)

theorem listGetDWithInput' {l : α → List ℕ} {i d : α → ℕ}
    (hl : ComputableInPolyTime l input (encList encUnary))
    (hi : ComputableInPolyTime i input encUnary) (hd : ComputableInPolyTime d input encUnary) :
    ComputableInPolyTime (fun a ↦ (l a).getD (i a) (d a)) input encUnary := by
  have hv : ComputableTidilyInPolyTime (fun a ↦ (l a)[i a]?) input (encOption encUnary) :=
    ComputableTidilyInPolyTime.getElem? hl.tidy hi.tidy
  have hb : ComputableTidilyInPolyTime (fun p : α × ℕ ↦ p.2) (encPair input encUnary) encUnary :=
    (snd input encUnary).tidy
  have key := ComputableTidilyInPolyTime.optionElimWithInput (value := fun a ↦ (l a)[i a]?)
    (fallback := d) (body := fun _ x ↦ x) hv hd.tidy hb
  have heq : (fun a ↦ (l a).getD (i a) (d a)) = fun a ↦ ((l a)[i a]?).elim (d a) fun x ↦ x := by
    funext a
    rw [List.getD_eq_getElem?_getD]
    cases (l a)[i a]? <;> rfl
  rw [heq]
  exact .of_tidy key

/-! ### Rounding, with `m` and `K₀` read from the input -/

theorem classBitsI_polytime : ComputableInPolyTime
    (fun x : ((ℕ × ℕ) × List ℕ) × ℕ ↦ classBits x.1.1.1 x.1.1.2 x.1.2 x.2)
    (encPair (encPair (encPair encUnary encUnary) (encList encUnary)) encUnary) encBits := by
  unfold classBits
  set E := encPair (encPair (encPair encUnary encUnary) (encList encUnary)) encUnary
  have hn : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List ℕ) × ℕ ↦ x.1.1.1) E encUnary :=
    (fst _ _).comp ((fst _ _).comp (fst _ _))
  have h1 : ComputableInPolyTime (fun q : (((ℕ × ℕ) × List ℕ) × ℕ) × ℕ ↦ q.1.1.2.getD q.2 q.1.1.1.2)
      (encPair E encUnary) encUnary :=
    listGetDWithInput' ((snd _ _).comp ((fst _ _).comp (fst _ _)))
      (snd _ _) ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp (fst _ _))))
  have h2 : ComputableInPolyTime (fun q : (((ℕ × ℕ) × List ℕ) × ℕ) × ℕ ↦ q.1.2)
      (encPair E encUnary) encUnary := (snd _ _).comp (fst _ _)
  have h : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List ℕ) × ℕ ↦
      (List.range x.1.1.1).map fun y ↦ decide (x.1.2.getD y x.1.1.2 = x.2)) E (encList encBool) :=
    mapWithInput (f := fun (x : ((ℕ × ℕ) × List ℕ) × ℕ) y ↦ decide (x.1.2.getD y x.1.1.2 = x.2))
      (unary_range' hn) (unary_eq' h1 h2)
  exact (bits_encList_polyTime encBool).2.comp h

theorem classBitsI' {n m : α → ℕ} {p : α → List ℕ} {c : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hp : ComputableInPolyTime p input (encList encUnary))
    (hc : ComputableInPolyTime c input encUnary) :
    ComputableInPolyTime (fun a ↦ classBits (n a) (m a) (p a) (c a)) input encBits := by
  have h := classBitsI_polytime.comp (((hn.prod hm).prod hp).prod hc)
  exact h

theorem roundedClassesI' {n m : α → ℕ} {adj : α → List Bool} {p : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hp : ComputableInPolyTime p input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ roundedClasses (n a) (m a) (adj a) (p a)) input
      (encList encBits) := by
  unfold roundedClasses
  have hb := classBitsI' (hn.comp (fst _ _)) (hm.comp (fst _ _)) (hp.comp (fst _ _))
    (snd input encUnary)
  have hr := roundIndep' (hn.comp (fst _ _)) (hadj.comp (fst _ _)) hb
  exact mapWithInput (f := fun a c ↦ roundIndep (n a) (adj a) (classBits (n a) (m a) (p a) c))
    (unary_range' hm) hr

theorem colorWithI_polytime : ComputableInPolyTime
    (fun x : ((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ ↦
      colorWith x.1.1.1 x.1.1.2.1 x.1.1.2.2 x.1.2 x.2)
    (encPair (encPair (encPair encUnary (encPair encUnary encUnary)) (encList encBits))
      (encList encUnary)) (encList encUnary) := by
  unfold colorWith
  set E := encPair (encPair (encPair encUnary (encPair encUnary encUnary)) (encList encBits))
    (encList encUnary)
  have hn : ComputableInPolyTime (fun x : ((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ ↦ x.1.1.1) E
      encUnary := (fst _ _).comp ((fst _ _).comp (fst _ _))
  set E2 := encPair E encUnary
  have hm : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ) × ℕ ↦
      q.1.1.1.2.1) E2 encUnary := (fst _ _).comp ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp
        (fst _ _))))
  have hK : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ) × ℕ ↦
      q.1.1.1.2.2) E2 encUnary := (snd _ _).comp ((snd _ _).comp ((fst _ _).comp ((fst _ _).comp
        (fst _ _))))
  have hrs : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ) × ℕ ↦
      q.1.1.2) E2 (encList encBits) := (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hp : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ) × ℕ ↦
      q.1.2) E2 (encList encUnary) := (snd _ _).comp (fst _ _)
  have hy : ComputableInPolyTime (fun q : (((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ) × ℕ ↦ q.2)
      E2 encUnary := snd _ _
  have hpy := listGetDWithInput' hp hy hm
  have hc := bitsGetDWithInput (listGetDWithInput hrs hpy []) hy false
  have hbody := ite' hc hpy hK
  exact mapWithInput (f := fun (x : ((ℕ × ℕ × ℕ) × List (List Bool)) × List ℕ) y ↦
    if (x.1.2.getD (x.2.getD y x.1.1.2.1) []).getD y false then x.2.getD y x.1.1.2.1
    else x.1.1.2.2) (unary_range' hn) hbody

theorem colorOfI' {n m K : α → ℕ} {adj : α → List Bool} {p : α → List ℕ}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hK : ComputableInPolyTime K input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hp : ComputableInPolyTime p input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ colorOf (n a) (m a) (K a) (adj a) (p a)) input
      (encList encUnary) := by
  unfold colorOf
  have h := colorWithI_polytime.comp (((hn.prod (hm.prod hK)).prod
    (roundedClassesI' hn hm hadj hp)).prod hp)
  exact h

/-! ### Selection, with `K₀` read from the input -/

theorem numColI' {n K : α → ℕ} {c : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hK : ComputableInPolyTime K input encUnary)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ numCol (n a) (K a) (c a)) input encUnary := by
  unfold numCol
  have hg := listGetDWithInput' (hc.comp (fst _ _)) (snd input encUnary) (hK.comp (fst _ _))
  have hlt0 := unary_lt' hg (hK.comp (fst _ _))
  have hlt : ComputableInPolyTime (fun p : α × ℕ ↦ decide ((c p.1).getD p.2 (K p.1) < K p.1))
      (encPair input encUnary) encBool := hlt0
  have hf := filterWithInput (test := fun a y ↦ decide ((c a).getD y (K a) < K a))
    (unary_range' hn) hlt
  exact (length_list encUnary).comp hf

theorem bestColorStepI_polytime : ComputableInPolyTime
    (fun p : ((ℕ × ℕ) × List ℕ) × List ℕ ↦ bestColorStep p.1.1.1 p.1.1.2 p.1.2 p.2)
    (encPair (encPair (encPair encUnary encUnary) (encList encUnary)) (encList encUnary))
    (encList encUnary) := by
  unfold bestColorStep
  set E := encPair (encPair (encPair encUnary encUnary) (encList encUnary)) (encList encUnary)
  have hn : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × List ℕ ↦ p.1.1.1) E encUnary :=
    (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hK : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × List ℕ ↦ p.1.1.2) E encUnary :=
    (snd _ _).comp ((fst _ _).comp (fst _ _))
  have hb : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × List ℕ ↦ p.1.2) E
      (encList encUnary) := (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun p : ((ℕ × ℕ) × List ℕ) × List ℕ ↦ p.2) E
      (encList encUnary) := snd _ _
  exact ite_decide (unary_lt' (numColI' hn hK hb) (numColI' hn hK hc)) hc hb

theorem bestColoringI' {n K : α → ℕ} {cs : α → List (List ℕ)}
    (hn : ComputableInPolyTime n input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hcs : ComputableInPolyTime cs input (encList (encList encUnary))) :
    ComputableInPolyTime (fun a ↦ bestColoring (n a) (K a) (cs a)) input (encList encUnary) := by
  unfold bestColoring
  refine foldlWith_of_bounded_growth (par := fun a ↦ (n a, K a))
    (step := fun q b c ↦ bestColorStep q.1 q.2 b c) (hn.prod hK) hcs (const [])
    bestColorStepI_polytime hcs.polyBounded_length ?_
  intro a b c hc
  unfold bestColorStep
  split_ifs
  · exact (SizedListEncoding.length_elem_le (encA := encList encUnary)
      (encL := encList (encList encUnary)) _ _ hc).trans (Nat.le_add_left _ _)
  · exact Nat.le_add_right _ _

/-! ### Clustering around centers -/

theorem sqDistC_polytime : ComputableInPolyTime
    (fun x : List (List ℚ) × ℕ × List ℚ ↦ sqDistC x.1 x.2.1 x.2.2)
    (encPair (encList (encList encRat)) (encPair encUnary (encList encRat))) encRat := by
  unfold sqDistC
  set E := encPair (encList (encList encRat)) (encPair encUnary (encList encRat))
  have hus : ComputableInPolyTime (fun x : List (List ℚ) × ℕ × List ℚ ↦ x.1) E
      (encList (encList encRat)) := fst _ _
  have hlen := (length_list (encList encRat)).comp hus
  have hu1 : ComputableInPolyTime (fun q : (List (List ℚ) × ℕ × List ℚ) × ℕ ↦
      (q.1.1.getD q.2 []).getD q.1.2.1 0) (encPair E encUnary) encRat :=
    listGetDWithInput (listGetDWithInput (hus.comp (fst _ _)) (snd _ _) [])
      ((fst _ _).comp ((snd _ _).comp (fst _ _))) 0
  have hc1 : ComputableInPolyTime (fun q : (List (List ℚ) × ℕ × List ℚ) × ℕ ↦
      q.1.2.2.getD q.2 0) (encPair E encUnary) encRat :=
    listGetDWithInput ((snd _ _).comp ((snd _ _).comp (fst _ _))) (snd _ _) 0
  have hbody := rat_sq' (rat_sub' hu1 hc1)
  have hmap := mapWithInput (f := fun (x : List (List ℚ) × ℕ × List ℚ) j ↦
    ((x.1.getD j []).getD x.2.1 0 - x.2.2.getD j 0) ^ 2) (unary_range' hlen) hbody
  exact rat_sum' hmap

theorem clusterIdxC_polytime : ComputableInPolyTime
    (fun x : (List (List ℚ) × List (List ℚ)) × ℕ ↦ clusterIdxC x.1.1 x.1.2 x.2)
    (encPair (encPair (encList (encList encRat)) (encList (encList encRat))) encUnary)
    encUnary := by
  set E := encPair (encPair (encList (encList encRat)) (encList (encList encRat))) encUnary
  have hus : ComputableInPolyTime (fun p : ((List (List ℚ) × List (List ℚ)) × ℕ) × ℕ ↦ p.1.1.1)
      (encPair E encUnary) (encList (encList encRat)) := (fst _ _).comp ((fst _ _).comp (fst _ _))
  have hy : ComputableInPolyTime (fun p : ((List (List ℚ) × List (List ℚ)) × ℕ) × ℕ ↦ p.1.2)
      (encPair E encUnary) encUnary := (snd _ _).comp (fst _ _)
  have hc : ComputableInPolyTime (fun p : ((List (List ℚ) × List (List ℚ)) × ℕ) × ℕ ↦
      p.1.1.2.getD p.2 []) (encPair E encUnary) (encList encRat) :=
    listGetDWithInput ((snd _ _).comp ((fst _ _).comp (fst _ _))) (snd _ _) []
  have h0 := sqDistC_polytime.comp (hus.prod (hy.prod hc))
  have h : ComputableInPolyTime (fun p : ((List (List ℚ) × List (List ℚ)) × ℕ) × ℕ ↦
      sqDistC p.1.1.1 p.1.2 (p.1.1.2.getD p.2 [])) (encPair E encUnary) encRat := h0
  have hm : ComputableInPolyTime (fun x : (List (List ℚ) × List (List ℚ)) × ℕ ↦ x.1.2.length) E
      encUnary := (length_list _).comp ((snd _ _).comp (fst _ _))
  have hcl := argminBelow' (input := E)
    (f := fun (x : (List (List ℚ) × List (List ℚ)) × ℕ) a ↦ sqDistC x.1.1 x.2 (x.1.2.getD a []))
    (m := fun x ↦ x.1.2.length) h hm
  unfold clusterIdxC
  exact hcl

theorem clustersC' {n : α → ℕ} {us cs : α → List (List ℚ)}
    (hn : ComputableInPolyTime n input encUnary)
    (hus : ComputableInPolyTime us input (encList (encList encRat)))
    (hcs : ComputableInPolyTime cs input (encList (encList encRat))) :
    ComputableInPolyTime (fun a ↦ clustersC (n a) (us a) (cs a)) input (encList encUnary) := by
  unfold clustersC
  have h := clusterIdxC_polytime.comp (((hus.comp (fst _ _)).prod (hcs.comp (fst _ _))).prod
    (snd input encUnary))
  exact mapWithInput (f := fun a y ↦ clusterIdxC (us a) (cs a) y) (unary_range' hn) h

/-- The grid centers, with `m`, `S`, `K` and the tuple in unary and `r` in binary. -/
theorem gridCenters' {m S K r : α → ℕ} {ts : α → List ℕ}
    (hm : ComputableInPolyTime m input encUnary) (hS : ComputableInPolyTime S input encUnary)
    (hK : ComputableInPolyTime K input encUnary) (hr : ComputableInPolyTime r input encNat)
    (hts : ComputableInPolyTime ts input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ gridCenters (m a) (S a) (K a) (r a) (ts a)) input
      (encList (encList encRat)) := by
  unfold gridCenters
  set E2 := encPair (encPair input encUnary) encUnary
  have hx : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.1.1) E2 input :=
    (fst _ _).comp (fst _ _)
  have ha : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.1.2) E2 encUnary :=
    (snd _ _).comp (fst _ _)
  have hj : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ q.2) E2 encUnary := snd _ _
  have hidx := unary_add' (unary_mul' ha (hm.comp hx)) hj
  have ht := listGetDWithInput (hts.comp hx) hidx 0
  have hnum := rat_sub' (rat_natCast' (toBin' ht)) (rat_natCast' (toBin' (hK.comp hx)))
  have hden := rat_mul' (rat_natCast' (toBin' (hS.comp hx))) (rat_natCast' (hr.comp hx))
  have hval := rat_div' hnum hden
  have hrow := mapWithInput (f := fun (p : α × ℕ) j ↦
    ((ts p.1).getD (p.2 * m p.1 + j) 0 - (K p.1 : ℚ)) / ((S p.1 : ℚ) * r p.1))
    (unary_range' (hm.comp (fst _ _))) hval
  exact mapWithInput (f := fun a i ↦ (List.range (m a)).map fun j ↦
    ((ts a).getD (i * m a + j) 0 - (K a : ℚ)) / ((S a : ℚ) * r a)) (unary_range' hm) hrow

/-! ### The candidates and the algorithm -/

/-- One candidate: the rounded clusters of the vectors of `U` numbered `is` around the grid
centers of `ts`. -/
theorem candG' {n m K₀ S K : α → ℕ} {adj : α → List Bool} {U : α → List (List ℚ)}
    {is ts : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hK₀ : ComputableInPolyTime K₀ input encUnary)
    (hS : ComputableInPolyTime S input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hU : ComputableInPolyTime U input (encList (encList encRat)))
    (his : ComputableInPolyTime is input (encList encUnary))
    (hts : ComputableInPolyTime ts input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ colorOf (n a) (m a) (K₀ a) (adj a) (clustersC (n a)
      ((is a).map fun i ↦ (U a).getD i []) (gridCenters (m a) (S a) (K a) (Nat.sqrt (n a))
        (ts a)))) input (encList encUnary) := by
  have hus := mapWithInput (f := fun a i ↦ (U a).getD i []) his
    (listGetDWithInput (hU.comp (fst _ _)) (snd input encUnary) [])
  have hr := binary_sqrt' (toBin' hn)
  have hcs := gridCenters' hm hS hK hr hts
  have hcl := clustersC' hn hus hcs
  exact colorOfI' hn hm hK₀ hadj hcl

/-- The candidates of one tuple `is` of vectors, for all grids of centers. -/
theorem innerG' {n m K₀ S K B : α → ℕ} {adj : α → List Bool} {U : α → List (List ℚ)}
    {is : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hK₀ : ComputableInPolyTime K₀ input encUnary)
    (hS : ComputableInPolyTime S input encUnary) (hK : ComputableInPolyTime K input encUnary)
    (hB : ComputableInPolyTime B input encUnary) (hadj : ComputableInPolyTime adj input encBits)
    (hU : ComputableInPolyTime U input (encList (encList encRat)))
    (his : ComputableInPolyTime is input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ (Tuples.tuples (B a) (2 * K a + 1) (m a * m a)).map fun ts ↦
      colorOf (n a) (m a) (K₀ a) (adj a) (clustersC (n a) ((is a).map fun i ↦ (U a).getD i [])
        (gridCenters (m a) (S a) (K a) (Nat.sqrt (n a)) ts))) input
      (encList (encList encUnary)) := by
  have hx := fst input (encList encUnary)
  have hc := candG' (hn.comp hx) (hm.comp hx) (hK₀.comp hx) (hS.comp hx) (hK.comp hx)
    (hadj.comp hx) (hU.comp hx) (his.comp hx) (snd input (encList encUnary))
  have h2K1 : ComputableInPolyTime (fun a ↦ 2 * K a + 1) input encUnary :=
    unary_add' (unary_mul' (const 2) hK) (const 1)
  have hmm : ComputableInPolyTime (fun a ↦ m a * m a) input encUnary := unary_mul' hm hm
  exact mapWithInput (f := fun a ts ↦ colorOf (n a) (m a) (K₀ a) (adj a) (clustersC (n a)
    ((is a).map fun i ↦ (U a).getD i []) (gridCenters (m a) (S a) (K a) (Nat.sqrt (n a)) ts)))
    (tuplesUnary' hB h2K1 hmm) hc

theorem candidatesG' {n m K₀ S K B : α → ℕ} {adj : α → List Bool} {U : α → List (List ℚ)}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hK₀ : ComputableInPolyTime K₀ input encUnary) (hS : ComputableInPolyTime S input encUnary)
    (hK : ComputableInPolyTime K input encUnary) (hB : ComputableInPolyTime B input encUnary)
    (hadj : ComputableInPolyTime adj input encBits)
    (hU : ComputableInPolyTime U input (encList (encList encRat))) :
    ComputableInPolyTime (fun a ↦ candidatesG (n a) (m a) (K₀ a) (S a) (K a) (B a) (adj a) (U a))
      input (encList (encList encUnary)) := by
  have hx := fst input (encList encUnary)
  have hin := innerG' (n := fun p : α × List ℕ ↦ n p.1) (m := fun p ↦ m p.1)
    (K₀ := fun p ↦ K₀ p.1) (S := fun p ↦ S p.1) (K := fun p ↦ K p.1) (B := fun p ↦ B p.1)
    (adj := fun p ↦ adj p.1) (U := fun p ↦ U p.1) (is := fun p ↦ p.2)
    (hn.comp hx) (hm.comp hx) (hK₀.comp hx) (hS.comp hx) (hK.comp hx)
    (hB.comp hx) (hadj.comp hx) (hU.comp hx) (snd input (encList encUnary))
  have hlenU : ComputableInPolyTime (fun a ↦ (U a).length) input encUnary :=
    (length_list (encList encRat)).comp hU
  have htup : ComputableInPolyTime (fun a ↦ Tuples.tuples (B a) (U a).length (m a)) input
      (encList (encList encUnary)) := tuplesUnary' hB hlenU hm
  have hin' : ComputableInPolyTime (fun p : α × List ℕ ↦
      (Tuples.tuples (B p.1) (2 * K p.1 + 1) (m p.1 * m p.1)).map fun ts ↦
        colorOf (n p.1) (m p.1) (K₀ p.1) (adj p.1) (clustersC (n p.1)
          (p.2.map fun i ↦ (U p.1).getD i []) (gridCenters (m p.1) (S p.1) (K p.1)
            (Nat.sqrt (n p.1)) ts))) (encPair input (encList encUnary))
      (encList (encList encUnary)) := hin
  unfold candidatesG
  exact flatMapWithInput htup hin'

/-- The parameters of the grid clustering: `m`, `K₀`, `S`, `K` and `B`, in unary. -/
abbrev encGridPar : ℕ × ℕ × ℕ × ℕ × ℕ ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))

/-- The grid clustering, with the colors in unary. -/
theorem gridAlg_unary : ComputableInPolyTime
    (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List (List ℚ)) × (ℕ × List Bool) ↦
      gridAlg z.1.1.1 z.1.1.2.1 z.1.1.2.2.1 z.1.1.2.2.2.1 z.1.1.2.2.2.2 z.1.2 z.2)
    (encPair (encPair encGridPar (encList (encList encRat))) (encPair encNat encBits))
    (encList encUnary) := by
  set E := encPair (encPair encGridPar (encList (encList encRat))) (encPair encNat encBits)
  have hp : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List (List ℚ)) × (ℕ × List Bool) ↦ z.1.1) E encGridPar :=
    (fst _ _).comp (fst _ _)
  have hU : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List (List ℚ)) × (ℕ × List Bool) ↦ z.1.2) E
      (encList (encList encRat)) := (snd _ _).comp (fst _ _)
  have hx : ComputableInPolyTime
      (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List (List ℚ)) × (ℕ × List Bool) ↦ z.2) E
      (encPair encNat encBits) := snd _ _
  have hm := (fst _ _).comp hp
  have hK₀ := (fst _ _).comp ((snd _ _).comp hp)
  have hS := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hp))
  have hK := (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
  have hB := (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
  have hn := numV_polytime.comp hx
  have hadj := (snd encNat encBits).comp hx
  have hc := candidatesG' hn hm hK₀ hS hK hB hadj hU
  have hbest := bestColoringI' hn hK₀ hc
  unfold gridAlg
  exact hbest

/-- **The grid clustering runs in polynomial time**, reading its parameters in unary with the
net vectors and the graph. -/
theorem gridAlg_polytime : ComputableInPolyTime
    (fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × List (List ℚ)) × (ℕ × List Bool) ↦
      gridAlg z.1.1.1 z.1.1.2.1 z.1.1.2.2.1 z.1.1.2.2.2.1 z.1.1.2.2.2.2 z.1.2 z.2)
    (encPair (encPair encGridPar (encList (encList encRat))) (encPair encNat encBits))
    encColoring := by
  have key := unaryList_to_binary.comp gridAlg_unary
  exact key

end Alg

end BHSV25
