module

public import BHSV25.Alg.Cluster
public import Background.TuplesPolyTime
public import Background.PolyTime.Rat

/-!
# The pieces of the clustering in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the pieces of
`BHSV25/Alg/Cluster.lean` that the machines of `BHSV25/Alg/GridPolyTime.lean` use: the search for
the first minimizer, a fold whose state stays below the number of candidates
(`BHSV25.Alg.argminBelow'`), the count of colored vertices (`BHSV25.Alg.numCol'`), the tuples with
all numbers in unary (`BHSV25.Alg.tuplesUnary'`), and lists of unary numbers in binary
(`BHSV25.Alg.unaryList_to_binary`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-! ### Clustering -/

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

/-! ### Rounding the clusters -/

/-! ### Choosing the best coloring -/

@[fun_prop]
theorem numCol' (K : ℕ) {n : α → ℕ} {c : α → List ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hc : ComputableInPolyTime c input (encList encUnary)) :
    ComputableInPolyTime (fun a ↦ numCol (n a) K (c a)) input encUnary := by
  unfold numCol
  exact (length_list encUnary).comp (filterWithInput (unary_range' hn)
    (unary_lt' (listGetDWithInput (hc.comp (fst _ _)) (snd _ _) K) (const K)))

/-! ### The candidates -/

/-- The tuples with all three numbers in unary, the entries in unary. -/
theorem tuplesUnary' {L n T : α → ℕ} (hL : ComputableInPolyTime L input encUnary)
    (hn : ComputableInPolyTime n input encUnary) (hT : ComputableInPolyTime T input encUnary) :
    ComputableInPolyTime (fun a ↦ Tuples.tuples (L a) (n a) (T a)) input
      (encList (encList encUnary)) :=
  Tuples.tuples_unary_polytime.comp (g := fun a ↦ (L a, n a, T a)) (hL.prod (hn.prod hT))

/-! ### The algorithm -/

/-- Lists of numbers from unary to binary. -/
theorem unaryList_to_binary :
    ComputableInPolyTime (fun l : List ℕ ↦ l) (encList encUnary) (encList encNat) := by
  have h : ComputableInPolyTime (fun l : List ℕ ↦ l.map fun i ↦ i) (encList encUnary)
      (encList encNat) :=
    mapWithInput id' (unary_to_binary.comp (snd _ _))
  simpa only [List.map_id'] using h

end Alg

end BHSV25
