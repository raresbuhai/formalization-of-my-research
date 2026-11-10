module

public import BHSV25.Alg.Cluster
public import BHSV25.Net.Machine

/-!
# Clustering with a grid of centers

The clustering algorithm of [BHSV25, Lemma 5.4 and Algorithm 3] (`BHSV25.Alg.gridAlg`), given a
list `U` of rational vectors (a net of an eigenspace), a number `m` of clusters, the color
`K₀ ≥ m` that marks uncolored vertices, the scale `S` and range `K` of the grid, and a budget
`B` for the tuples:

1. **Candidates.** For every `m`-tuple of vectors `u₀, …, u_{m-1}` of `U` and every choice of `m`
   centers with `m` coordinates on the grid `{(t - K) / (S r) : 0 ≤ t ≤ 2K}`, `r = ⌊√n⌋`, put
   each vertex `y` in the cluster `a` of the nearest center `c_a`: `a` minimizes
   `∑_j (u_j[y] - c_(a,j))²` (`BHSV25.Alg.clustersC`).
2. **Rounding** and **selection** (`BHSV25/Alg/Cluster.lean`): round each cluster to an
   independent set and output the candidate with the most colored vertices.

The grid has `(2K + 1)^(m²)` points, independent of the number of vertices, and so has the list
of tuples of `U` when `U` has a size independent of it, as the greedy net of
`BHSV25/Net/GSMachine.lean` does.

The facts here are combinatorial (`BHSV25.Alg.gridAlg_spec`): the output is a partial
`K₀`-coloring that colors, for every candidate partition `R₀, …, R_(m-1)` and independent sets
`I₀, …, I_(m-1)`, at least `∑_a (|R_a ∩ I_a| - |R_a \ I_a|)` vertices. Which candidate is good is
the analysis of `BHSV25/Alg/GridPartition.lean`.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset

/-! ### Clustering around centers -/

/-- The squared distance `∑_j (u_j[y] - c_j)²` from the vertex `y` to a center `c`, in the
coordinates given by the vectors `us`. -/
def sqDistC (us : List (List ℚ)) (y : ℕ) (c : List ℚ) : ℚ :=
  ((List.range us.length).map fun j ↦ ((us.getD j []).getD y 0 - c.getD j 0) ^ 2).sum

/-- The cluster of the vertex `y`: the index of the nearest center of `cs`. -/
def clusterIdxC (us cs : List (List ℚ)) (y : ℕ) : ℕ :=
  argminBelow (fun a ↦ sqDistC us y (cs.getD a [])) cs.length

/-- The clusters of the vertices `0, …, n - 1`. -/
def clustersC (n : ℕ) (us cs : List (List ℚ)) : List ℕ := (List.range n).map (clusterIdxC us cs)

/-- The `m` centers with `m` coordinates of a tuple `ts` over `{0, …, 2K}`: the coordinate `j` of
the center `a` is `(t_(a m + j) - K) / (S r)`. -/
def gridCenters (m S K r : ℕ) (ts : List ℕ) : List (List ℚ) :=
  (List.range m).map fun a ↦ (List.range m).map fun j ↦
    ((ts.getD (a * m + j) 0 : ℚ) - K) / ((S : ℚ) * r)

/-- **The candidates**: for every `m`-tuple of vectors of `U` and every grid of centers, the
rounded clusters. -/
def candidatesG (n m K₀ S K B : ℕ) (adj : List Bool) (U : List (List ℚ)) : List (List ℕ) :=
  (Tuples.tuples B U.length m).flatMap fun is ↦
    (Tuples.tuples B (2 * K + 1) (m * m)).map fun ts ↦
      colorOf n m K₀ adj
        (clustersC n (is.map fun i ↦ U.getD i []) (gridCenters m S K (Nat.sqrt n) ts))

/-- **The grid clustering algorithm**: the best candidate. -/
def gridAlg (m K₀ S K B : ℕ) (U : List (List ℚ)) (x : ℕ × List Bool) : List ℕ :=
  bestColoring (numV x) K₀ (candidatesG (numV x) m K₀ S K B x.2 U)

/-! ### Facts -/

theorem length_gridCenters (m S K r : ℕ) (ts : List ℕ) : (gridCenters m S K r ts).length = m := by
  simp [gridCenters]

theorem clusterIdxC_lt (us cs : List (List ℚ)) (hcs : 0 < cs.length) (y : ℕ) :
    clusterIdxC us cs y < cs.length :=
  argminBelow_lt _ hcs

/-- A strict nearest center is the cluster. -/
theorem clusterIdxC_eq (us cs : List (List ℚ)) (y : ℕ) {a : ℕ} (ha : a < cs.length)
    (h : ∀ b < cs.length, b ≠ a → sqDistC us y (cs.getD a []) < sqDistC us y (cs.getD b [])) :
    clusterIdxC us cs y = a :=
  argminBelow_eq _ ha h

theorem getD_clustersC {n : ℕ} (us cs : List (List ℚ)) {y : ℕ} (hy : y < n) (d : ℕ) :
    (clustersC n us cs).getD y d = clusterIdxC us cs y := by
  rw [clustersC, Net.getD_map_range n _ _ hy]

/-- The coordinates of the grid centers. -/
theorem getD_gridCenters {m S K r : ℕ} (ts : List ℕ) {a j : ℕ} (ha : a < m) (hj : j < m) :
    ((gridCenters m S K r ts).getD a []).getD j 0 =
      ((ts.getD (a * m + j) 0 : ℚ) - K) / ((S : ℚ) * r) := by
  rw [gridCenters, Net.getD_map_range m _ _ ha, Net.getD_map_range m _ _ hj]

/-- The squared distance of the algorithm, for vectors given by a function, as a real sum. -/
theorem sqDistC_ofFn_cast {m n : ℕ} (us : Fin m → List ℚ) (y : Fin n) (c : List ℚ) :
    ((sqDistC (List.ofFn us) y c : ℚ) : ℝ) =
      ∑ j : Fin m, ((((us j).getD y 0 : ℚ) : ℝ) - ((c.getD j 0 : ℚ) : ℝ)) ^ 2 := by
  rw [sqDistC, List.length_ofFn, Net.sum_map_range]
  push_cast
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : (List.ofFn us).getD j [] = us j := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  rw [h]

theorem colorOf_mem_candidatesG (n m K₀ S K B : ℕ) (adj : List Bool) (U : List (List ℚ))
    (us : Fin m → List ℚ) (hus : ∀ j, us j ∈ U) (ts : Fin (m * m) → Fin (2 * K + 1))
    (hB1 : U.length ^ m ≤ B) (hB2 : (2 * K + 1) ^ (m * m) ≤ B) :
    colorOf n m K₀ adj (clustersC n (List.ofFn us)
        (gridCenters m S K (Nat.sqrt n) (List.ofFn fun k ↦ (ts k : ℕ)))) ∈
      candidatesG n m K₀ S K B adj U := by
  rw [candidatesG, List.mem_flatMap]
  have hU : ∀ j, U.idxOf (us j) < U.length := fun j ↦ List.idxOf_lt_length_of_mem (hus j)
  refine ⟨List.ofFn fun j ↦ ((⟨U.idxOf (us j), hU j⟩ : Fin U.length) : ℕ),
    Tuples.ofFn_mem_tuples hB1 _, List.mem_map.2 ⟨_, Tuples.ofFn_mem_tuples hB2 ts, ?_⟩⟩
  congr 3
  rw [List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (hU j), List.getElem_idxOf]

/-! ### The algorithm on a graph -/

variable (G : Graph)

/-- **The output is a partial `K₀`-coloring**, for `1 ≤ m ≤ K₀` and every budget. -/
theorem isPartialColoring_gridAlg {m K₀ : ℕ} (hm : 0 < m) (hmK : m ≤ K₀) (S K B : ℕ)
    (U : List (List ℚ)) : G.IsPartialColoring K₀ (gridAlg m K₀ S K B U (G.1, adjTable G)) := by
  have hp : ∀ (us cs : List (List ℚ)), cs.length = m → ∀ v : Fin G.1,
      (clustersC G.1 us cs).getD v m < m := by
    intro us cs hcs v
    rw [getD_clustersC _ _ v.2]
    exact hcs ▸ clusterIdxC_lt us cs (by omega) v
  have hrun : gridAlg m K₀ S K B U (G.1, adjTable G) =
      bestColoring G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U) := by
    rw [gridAlg, numV_graph]
  obtain ⟨hmem, -⟩ := bestColoring_spec G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U)
  rw [hrun]
  rcases hmem with h | h
  · generalize bestColoring G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U) = b at h ⊢
    rw [candidatesG, List.mem_flatMap] at h
    obtain ⟨is, -, h⟩ := h
    obtain ⟨ts', -, hc⟩ := List.mem_map.1 h
    rw [← hc]
    exact isPartialColoring_colorOf G hmK _ (hp _ _ (length_gridCenters m S K _ _))
  · rw [h]
    intro u v _ hu
    simp [Graph.color] at hu

/-- **What the algorithm guarantees**, for `1 ≤ m ≤ K₀` and a budget covering the tuples: a
partial `K₀`-coloring that, for every candidate (vectors `us` of `U` and grid indices `ts`) and
all independent sets `I_a`, colors at least `∑_a max(0, |R_a ∩ I_a| - |R_a \ I_a|)` vertices,
where `R_a` are the clusters. -/
theorem gridAlg_spec {m K₀ : ℕ} (hm : 0 < m) (hmK : m ≤ K₀) (S K B : ℕ) (U : List (List ℚ))
    (hB1 : U.length ^ m ≤ B) (hB2 : (2 * K + 1) ^ (m * m) ≤ B) :
    G.IsPartialColoring K₀ (gridAlg m K₀ S K B U (G.1, adjTable G)) ∧
      ∀ (us : Fin m → List ℚ), (∀ j, us j ∈ U) →
      ∀ (ts : Fin (m * m) → Fin (2 * K + 1)) (I : ℕ → Finset (Fin G.1)),
        (∀ a, G.2.IsIndepSet (I a : Set (Fin G.1))) →
        ∑ a ∈ range m, max 0
          (((classSet G m (clustersC G.1 (List.ofFn us)
              (gridCenters m S K (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ)))) a ∩
            I a).card : ℝ) -
          (classSet G m (clustersC G.1 (List.ofFn us)
              (gridCenters m S K (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ)))) a \
            I a).card) ≤
          G.numColored K₀ (gridAlg m K₀ S K B U (G.1, adjTable G)) := by
  have hp : ∀ (us cs : List (List ℚ)), cs.length = m → ∀ v : Fin G.1,
      (clustersC G.1 us cs).getD v m < m := by
    intro us cs hcs v
    rw [getD_clustersC _ _ v.2]
    exact hcs ▸ clusterIdxC_lt us cs (by omega) v
  have hrun : gridAlg m K₀ S K B U (G.1, adjTable G) =
      bestColoring G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U) := by
    rw [gridAlg, numV_graph]
  obtain ⟨hmem, hbest⟩ := bestColoring_spec G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U)
  rw [hrun]
  refine ⟨?_, fun us hus ts I hI ↦ ?_⟩
  · rcases hmem with h | h
    · generalize bestColoring G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U) = b at h ⊢
      rw [candidatesG, List.mem_flatMap] at h
      obtain ⟨is, -, h⟩ := h
      obtain ⟨ts', -, hc⟩ := List.mem_map.1 h
      rw [← hc]
      exact isPartialColoring_colorOf G hmK _ (hp _ _ (length_gridCenters m S K _ _))
    · rw [h]
      intro u v _ hu
      simp [Graph.color] at hu
  · have hc := colorOf_mem_candidatesG G.1 m K₀ S K B (adjTable G) U us hus ts hB1 hB2
    have h1 := sum_card_inter_le G hmK _ (hp (List.ofFn us)
      (gridCenters m S K (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ)))
      (length_gridCenters m S K (Nat.sqrt G.1) _)) I hI
    have h2 := hbest _ hc
    rw [← numColored_eq_numCol, ← numColored_eq_numCol] at h2
    have h2' : (G.numColored K₀ (colorOf G.1 m K₀ (adjTable G) (clustersC G.1 (List.ofFn us)
        (gridCenters m S K (Nat.sqrt G.1) (List.ofFn fun k ↦ (ts k : ℕ))))) : ℝ) ≤
        G.numColored K₀ (bestColoring G.1 K₀ (candidatesG G.1 m K₀ S K B (adjTable G) U)) := by
      exact_mod_cast h2
    linarith

end Alg

end BHSV25
