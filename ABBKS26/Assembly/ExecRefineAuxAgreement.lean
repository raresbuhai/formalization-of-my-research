module

public import ABBKS26.Assembly.ExecRefineAuxData

/-! Canonical list representations commute with evaluation and weak block replacement. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree Matrix
open scoped BigOperators

/-- The two range sums use exactly the typed rational quadratic, including linear terms. -/
theorem eval_agrees {d : ℕ} (q : Statistic d) (v : Vector) :
    evalL d (statisticList q) v = q.evalQ (vectorOf d v) := by
  have hs := @FrameAux.Linear.sum_fin_eq_list ℚ _
  change evalL d (statisticList q) v =
    (∑ i, vectorOf d v i * ∑ j, q.A i j * vectorOf d v j) +
      (∑ i, q.b i * vectorOf d v i) + q.c
  unfold evalL
  congr 2
  · rw [hs (fun i ↦ vectorOf d v i * ∑ j, q.A i j * vectorOf d v j)
      (fun i ↦ ((List.range d).map fun j ↦
        v.getD i 0 * (((statisticList q).1).getD i []).getD j 0 * v.getD j 0).sum)]
    intro i
    rw [Finset.mul_sum]
    rw [hs (fun j ↦ vectorOf d v i * (q.A i j * vectorOf d v j))]
    intro j
    simp [statisticList, vectorOf, List.getD_eq_getElem?_getD, mul_assoc]
  · rw [hs (fun i ↦ q.b i * vectorOf d v i)]
    intro i
    simp [statisticList, vectorOf, List.getD_eq_getElem?_getD]

private theorem sort_filter {α : Type} [LinearOrder α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.sort (· ≤ ·)).filter p = (s.filter p).sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise'
    ((s.pairwise_sort (· ≤ ·)).filter _) ((s.filter p).pairwise_sort (· ≤ ·))
  apply (List.perm_ext_iff_of_nodup ((s.sort_nodup _).filter _)
    ((s.filter p).sort_nodup _)).mpr
  intro a
  simp

private theorem index_filter {n : ℕ} (s : Finset (Fin n))
    (p : ℕ → Prop) [DecidablePred p] :
    (indexList s).filter p = indexList (s.filter fun i ↦ p i.val) := by
  simp only [indexList, List.filter_map]
  rw [← sort_filter]
  rfl

/-- Filtering the canonical parent retains canonical increasing indices and the tie rule. -/
theorem left_agrees {n d : ℕ} (pts : Points) (e : Edge n d) :
    leftL d pts (edgeList e) = indexList (e.left fun l ↦ vectorOf d (pts.getD l.val [])) := by
  simp only [leftL, edgeList, eval_agrees, Edge.left]
  exact index_filter _ _

/-- Both children, empty slots, and the original parent record are preserved in order. -/
theorem replace_agrees {n d : ℕ} (pts : Points) (C : Candidate n d)
    (j : ℕ) (e : Edge n d) :
    replaceL d pts (candidateList C) j (edgeList e) =
      candidateList (replaceBlock (fun l ↦ vectorOf d (pts.getD l.val [])) C j e) := by
  have hr : (indexList e.parent).filter
      (fun l ↦ l ∉ indexList (e.left fun l ↦ vectorOf d (pts.getD l.val []))) =
        indexList (e.right fun l ↦ vectorOf d (pts.getD l.val [])) := by
    rw [index_filter]
    congr 1
    ext i
    simp [Edge.right, indexList, Fin.val_injective.eq_iff]
  simp only [replaceL, left_agrees]
  change ((C.blocks.map indexList).take j ++
      [indexList (e.left _), (indexList e.parent).filter
        (fun l ↦ l ∉ indexList (e.left _))] ++
      (C.blocks.map indexList).drop (j + 1), C.path.map edgeList ++ [edgeList e]) = _
  rw [hr]
  simp only [candidateList, replaceBlock,
    List.map_append, List.map_take, List.map_drop, List.map_cons, List.map_nil]

end ABBKS26.Assembly.Exec.RefineSynth
