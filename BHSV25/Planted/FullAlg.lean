module

public import BHSV25.Alg.ExpanderFull

/-!
# The algorithm of Theorem 7.17

The steps of [BHSV25, Theorem 7.17] on the input `(n, a)` of a graph, colorings being lists of
numbers (`k` or more means "uncolored"):

1. **The list** (`BHSV25.Planted.clusterList`): the clusters of Theorem 7.12 before the rounding,
   for every tuple of net vectors and every grid of centers (Theorem B.1: one of them agrees with
   the planted coloring on all but a few vertices).
2. **Uncoloring** [BHSV25, Algorithm 2] (`BHSV25.Planted.uncolor`): as long as some colored vertex
   has fewer than `d / (6k)` neighbors of some other color, uncolor it. The rounds uncolor all such
   vertices at once; uncoloring only removes neighbors, so a vertex that should be uncolored stays
   so, and `n + 1` rounds reach the end. The host degree `d` is not known: the algorithm tries
   every `d ≤ n`.
3. **Safe recoloring** [BHSV25, Algorithm 3] (`BHSV25.Planted.recolor`): as long as some uncolored
   vertex has colored neighbors of all colors but one, give it that color; in rounds, `n + 1` of
   them.
4. **Brute force** (`BHSV25.Planted.brute`): every uncolored vertex `y` computes the set `C_y` of
   the uncolored vertices it reaches through uncolored vertices (`BHSV25.Planted.closure`), tries
   the colorings of `C_y` in order (at most `n²` of them, `Tuples.tuples`), and takes its color in
   the first one that has no monochromatic edge (`BHSV25.Planted.validAssign`). The vertices of
   one component compute the same component and the same coloring.
5. **Selection**: each result is rounded to a partial coloring (`BHSV25.Alg.colorOf`, after
   sending the uncolored vertices to the color `0`) and the one with the most colored vertices is
   output (`BHSV25.Alg.bestColoring`).
-/

@[expose] public section

namespace BHSV25

namespace Planted

/-! ### The list -/

/-- The clusters of all candidates of the grid clustering, before the rounding. -/
def clusterList (n m S K B : ℕ) (U : List (List ℚ)) : List (List ℕ) :=
  (Tuples.tuples B U.length m).flatMap fun is ↦
    (Tuples.tuples B (2 * K + 1) (m * m)).map fun ts ↦
      Alg.clustersC n (is.map fun i ↦ U.getD i []) (Alg.gridCenters m S K (Nat.sqrt n) ts)

/-! ### Uncoloring -/

/-- The number of neighbors `z < n` of `y` with the color `a`. -/
def nbrCount (n k : ℕ) (adj : List Bool) (c : List ℕ) (y a : ℕ) : ℕ :=
  (List.range n).countP fun z ↦ Alg.adjBit n adj y z && decide (c.getD z k = a)

/-- `y` is colored and has fewer than `d / (6k)` neighbors of some other color. -/
def violates (n k d : ℕ) (adj : List Bool) (c : List ℕ) (y : ℕ) : Bool :=
  decide (c.getD y k < k) && (List.range k).any fun a ↦
    !decide (a = c.getD y k) && decide (6 * k * nbrCount n k adj c y a < d)

/-- One round of uncoloring. -/
def uncolorStep (n k d : ℕ) (adj : List Bool) (c : List ℕ) : List ℕ :=
  (List.range n).map fun y ↦ if violates n k d adj c y then k else c.getD y k

/-- **Uncoloring** [BHSV25, Algorithm 2], in `n + 1` rounds. -/
def uncolor (n k d : ℕ) (adj : List Bool) (c : List ℕ) : List ℕ :=
  (uncolorStep n k d adj)^[n + 1] c

/-! ### Safe recoloring -/

/-- The colors `a < k` that no neighbor of `y` has. -/
def missing (n k : ℕ) (adj : List Bool) (c : List ℕ) (y : ℕ) : List ℕ :=
  (List.range k).filter fun a ↦
    !(List.range n).any fun z ↦ Alg.adjBit n adj y z && decide (c.getD z k = a)

/-- One round of safe recoloring. -/
def recolorStep (n k : ℕ) (adj : List Bool) (c : List ℕ) : List ℕ :=
  (List.range n).map fun y ↦
    if decide (k ≤ c.getD y k) && decide ((missing n k adj c y).length = 1) then
      (missing n k adj c y).headD k
    else c.getD y k

/-- **Safe recoloring** [BHSV25, Algorithm 3], in `n + 1` rounds. -/
def recolor (n k : ℕ) (adj : List Bool) (c : List ℕ) : List ℕ :=
  (recolorStep n k adj)^[n + 1] c

/-! ### Brute force -/

/-- One step of the closure: add the uncolored neighbors of the set. -/
def closeStep (n k : ℕ) (adj : List Bool) (c : List ℕ) (s : List Bool) : List Bool :=
  (List.range n).map fun y ↦ s.getD y false ||
    (decide (c.getD y k = k) && (List.range n).any fun z ↦ s.getD z false && Alg.adjBit n adj z y)

/-- The uncolored vertices reached from `v` through uncolored vertices, as membership bits. -/
def closure (n k : ℕ) (adj : List Bool) (c : List ℕ) (v : ℕ) : List Bool :=
  (closeStep n k adj c)^[n] ((List.range n).map fun y ↦ decide (y = v))

/-- The color of `z` when the vertices of `C` get the colors `σ`, in order. -/
def assignAt (k : ℕ) (c C σ : List ℕ) (z : ℕ) : ℕ :=
  if z ∈ C then σ.getD (C.idxOf z) 0 else c.getD z k

/-- The coloring `σ` of `C` has no monochromatic edge at `C`. -/
def validAssign (n k : ℕ) (adj : List Bool) (c C σ : List ℕ) : Bool :=
  C.all fun u ↦ (List.range n).all fun w ↦
    !Alg.adjBit n adj u w || !decide (assignAt k c C σ u = assignAt k c C σ w)

/-- The color of the uncolored vertex `y`: its color in the first valid coloring of its set. -/
def bruteAt (n k : ℕ) (adj : List Bool) (c : List ℕ) (y : ℕ) : ℕ :=
  (((Tuples.tuples (n * n) k (Alg.bitsToList n (closure n k adj c y)).length).find?
    fun σ ↦ validAssign n k adj c (Alg.bitsToList n (closure n k adj c y)) σ).map
      fun σ ↦ σ.getD ((Alg.bitsToList n (closure n k adj c y)).idxOf y) 0).getD k

/-- **Brute force** on the sets of uncolored vertices. -/
def brute (n k : ℕ) (adj : List Bool) (c : List ℕ) : List ℕ :=
  (List.range n).map fun y ↦ if c.getD y k = k then bruteAt n k adj c y else c.getD y k

/-! ### The algorithm -/

/-- The uncolored vertices sent to the color `0`. -/
def clampK (n k : ℕ) (c : List ℕ) : List ℕ :=
  (List.range n).map fun y ↦ if c.getD y k < k then c.getD y k else 0

/-- The result of the steps 2–4 from the candidate `q` with the degree `d`, rounded. -/
def pipeline (n k d : ℕ) (adj : List Bool) (q : List ℕ) : List ℕ :=
  Alg.colorOf n k k adj (clampK n k (brute n k adj (recolor n k adj (uncolor n k d adj q))))

/-- **The algorithm** of [BHSV25, Theorem 7.17], with the parameters
`((k, K₀, S, K, B), (a, T, N, B'))` of the clustering and the net of Theorem 7.1. -/
def fullAlg (p : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) (x : ℕ × List Bool) : List ℕ :=
  Alg.bestColoring (Alg.numV x) p.1.1
    ((clusterList (Alg.numV x) p.1.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2 (Alg.expNet p.2 x)).flatMap
      fun q ↦ (List.range (Alg.numV x + 1)).map fun d ↦ pipeline (Alg.numV x) p.1.1 d x.2 q)

end Planted

end BHSV25
