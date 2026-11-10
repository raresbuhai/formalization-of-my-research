module

public import BHSV25.Alg.ColoringAnalysis
public import BHSV25.Alg.ClusterPolyTime
public import BHSV25.Alg.IndepSet

/-!
# The combination of a coloring and an independent set

The output rule of [BHSV25, Corollary 1.4] (`BHSV25.Alg.threeCombine`): given a partial
`3`-coloring `c` and an independent set `b`, output `c` if `c` colors at least `2 |b|` vertices,
and otherwise the coloring of `b` alone: color `0` on `b`, uncolored elsewhere
(`BHSV25.Alg.threeIndepColoring`). The comparison is between two counts of vertices, so it needs no
real thresholds. The coloring of an independent set is a partial `3`-coloring whose class `0` is
the set (`BHSV25.Alg.isPartialColoring_threeIndepColoring`,
`BHSV25.Alg.classSize_threeIndepColoring`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset

/-- The coloring of a set `b` of vertices: color `0` on its members among `0, …, n - 1`, and
uncolored (`3`) on the other vertices. -/
def threeIndepColoring (n : ℕ) (b : List Bool) : List ℕ :=
  (List.range n).map fun v ↦ if b.getD v false then 0 else 3

/-- **The combination**: the coloring `c` if it colors at least `2 |b|` vertices, and the coloring
of `b` otherwise. -/
def threeCombine (n : ℕ) (c : List ℕ) (b : List Bool) : List ℕ :=
  if numCol n 3 c < 2 * numTrue n b then threeIndepColoring n b else c

section Corollary

variable (G : Graph)

theorem color_threeIndepColoring (b : List Bool) (v : Fin G.1) :
    G.color 3 (threeIndepColoring G.1 b) v = if b.getD v false then 0 else 3 := by
  rw [Graph.color, threeIndepColoring, List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The coloring of an independent set is a partial `3`-coloring. -/
theorem isPartialColoring_threeIndepColoring {b : List Bool}
    (hb : G.2.IsIndepSet (G.vertexSet b : Set (Fin G.1))) :
    G.IsPartialColoring 3 (threeIndepColoring G.1 b) := by
  intro u v huv hu heq
  rw [color_threeIndepColoring] at hu heq
  rw [color_threeIndepColoring] at heq
  by_cases hbu : b.getD u false = true
  · by_cases hbv : b.getD v false = true
    · have hu' : u ∈ (G.vertexSet b : Set (Fin G.1)) := by
        rw [mem_coe, Graph.vertexSet, mem_filter]
        exact ⟨mem_univ _, hbu⟩
      have hv' : v ∈ (G.vertexSet b : Set (Fin G.1)) := by
        rw [mem_coe, Graph.vertexSet, mem_filter]
        exact ⟨mem_univ _, hbv⟩
      exact hb hu' hv' huv.ne huv
    · rw [ite_eq_left hbu, ite_eq_right hbv] at heq
      exact absurd heq (by norm_num)
  · rw [ite_eq_right hbu] at hu
    exact absurd hu (by norm_num)

/-- The class `0` of the coloring of `b` is `b`. -/
theorem classSize_threeIndepColoring (b : List Bool) :
    G.classSize 3 (threeIndepColoring G.1 b) 0 = numTrue G.1 b := by
  rw [← card_vertexSet, Graph.classSize]
  congr 1
  ext v
  rw [mem_filter, color_threeIndepColoring, Graph.vertexSet, mem_filter]
  by_cases h : b.getD v false = true
  · rw [ite_eq_left h]
    exact ⟨fun _ ↦ ⟨mem_univ _, h⟩, fun _ ↦ ⟨mem_univ _, rfl⟩⟩
  · rw [ite_eq_right h]
    exact ⟨fun h' ↦ absurd h'.2 (by norm_num), fun h' ↦ absurd h'.2 h⟩

end Corollary

end Alg

end BHSV25
