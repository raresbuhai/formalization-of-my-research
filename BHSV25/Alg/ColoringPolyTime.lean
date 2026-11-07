module

public import BHSV25.Alg.ClusterPolyTime
public import BHSV25.Alg.IndepSet

/-!
# Corollary 1.4: the combined algorithm

The algorithm of [BHSV25, Corollary 1.4] (`BHSV25.Alg.threeAlg`) runs two algorithms on the input
graph: the clustering algorithm with `3` clusters of Theorem 1.3 (`BHSV25.Alg.clusterAlg 3 3`),
which outputs a partial `3`-coloring `c`, and the independent-set algorithm of Theorem 1.1
(`BHSV25.Alg.indepAlg`), which outputs an independent set `b`. It outputs `c` if `c` colors at
least `2 |b|` vertices, and otherwise the coloring of `b` alone: color `0` on `b`, uncolored
elsewhere (`BHSV25.Alg.threeIndepColoring`). The comparison is between two counts of vertices, so
it needs no real thresholds.

`BHSV25.Alg.threeAlg_graph_polytime` certifies that it runs in polynomial time on graphs encoded
by `BHSV25.encGraph`, given polynomial-time nets for both algorithms. Inside, the counts and the
colors are in unary, as in `BHSV25/Alg/ClusterPolyTime.lean`.
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- The coloring of a set `b` of vertices: color `0` on its members among `0, …, n - 1`, and
uncolored (`3`) on the other vertices. -/
def threeIndepColoring (n : ℕ) (b : List Bool) : List ℕ :=
  (List.range n).map fun v ↦ if b.getD v false then 0 else 3

/-- **The combination**: the coloring `c` if it colors at least `2 |b|` vertices, and the coloring
of `b` otherwise. -/
def threeCombine (n : ℕ) (c : List ℕ) (b : List Bool) : List ℕ :=
  if numCol n 3 c < 2 * numTrue n b then threeIndepColoring n b else c

/-- **The algorithm of Corollary 1.4**, for the nets `net₁` of the clustering algorithm and
`net₂` of the independent-set algorithm. -/
def threeAlg (net₁ net₂ : ℕ × List Bool → List (List ℚ)) (x : ℕ × List Bool) : List ℕ :=
  threeCombine (numV x) (clusterAlg 3 3 net₁ x) (indepAlg net₂ x)

/-- The algorithm, with the colors in unary. -/
theorem threeAlg_unary {net₁ net₂ : ℕ × List Bool → List (List ℚ)}
    (h₁ : ComputableInPolyTime net₁ (encPair encNat encBits) (encList (encList encRat)))
    (h₂ : ComputableInPolyTime net₂ (encPair encNat encBits) (encList (encList encRat))) :
    ComputableInPolyTime (threeAlg net₁ net₂) (encPair encNat encBits) (encList encUnary) := by
  have hn := numV_polytime
  have hc := clusterAlg_unary 3 3 h₁
  have hb := indepAlg_polytime h₂
  have hind : ComputableInPolyTime
      (fun x : ℕ × List Bool ↦ threeIndepColoring (numV x) (indepAlg net₂ x))
      (encPair encNat encBits) (encList encUnary) := by
    unfold threeIndepColoring
    exact mapWithInput (unary_range' hn)
      (ite' (bitsGetDWithInput (hb.comp (fst _ _)) (snd _ _) false) (const 0) (const 3))
  unfold threeAlg threeCombine
  exact ite_decide (unary_lt' (numCol' 3 hn hc) (unary_mul' (const 2) (numTrue' hn hb))) hind hc

/-- **The algorithm of Corollary 1.4 runs in polynomial time**, on graphs encoded by their
adjacency tables, given polynomial-time nets. -/
theorem threeAlg_graph_polytime {net₁ net₂ : ℕ × List Bool → List (List ℚ)}
    (h₁ : ComputableInPolyTime net₁ (Encoding.encPair Encoding.encNat Encoding.encBits)
      (Encoding.encList (Encoding.encList Encoding.encRat)))
    (h₂ : ComputableInPolyTime net₂ (encPair encNat encBits) (encList (encList encRat))) :
    ComputableInPolyTime (fun G : Graph ↦ threeAlg net₁ net₂ (G.1, adjTable G)) encGraph
      encColoring := by
  have he : ComputableInPolyTime (fun G : Graph ↦ (G.1, adjTable G)) encGraph
      (encPair encNat encBits) := of_eq fun _ ↦ rfl
  exact (unaryList_to_binary.comp (threeAlg_unary h₁ h₂)).comp he

end Alg

end BHSV25
