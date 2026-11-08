module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max

/-!
# Clustering points on a line

The last step of the colinear algorithm clusters real (or rational) numbers `z₁, …, z_n` into `k`
groups, without knowing the spread of the groups:

* At a scale `h`, the line is cut into the cells `[p h, (p + 1) h)`, `p ∈ ℤ` (`BS23.OneDim.cell`).
  A cell is *heavy* when it holds at least `θ n` of the points, and the *coverage* is the fraction
  of points in heavy cells.
* Scales are `H / 2^ℓ` for `ℓ ≤ ℓmax`; the algorithm takes the smallest scale (largest `ℓ`) whose
  coverage is at least `1 - ε` (`BS23.OneDim.level`, `0` when there is none).
* Between consecutive heavy cells there are gaps; the `k - 1` largest (ties broken towards the
  left) are the boundaries between groups (`BS23.OneDim.boundaries`). A point gets the number of
  boundaries whose gap's midpoint lies to its left (`BS23.OneDim.label`).

Everything is stated over a linearly ordered field with a floor, so that the algorithm runs on
rationals and the analysis on reals.
-/

@[expose] public section

namespace BS23.OneDim

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The cell `⌊z / h⌋` of `z` at scale `h`. -/
def cell (h z : K) : ℤ := ⌊z / h⌋

variable {n : ℕ}

/-- The number of points in the cell `p`. -/
def cellCount (h : K) (z : Fin n → K) (p : ℤ) : ℕ :=
  (Finset.univ.filter fun j ↦ cell h (z j) = p).card

/-- The heavy cells: those holding at least `θ n` points. -/
def heavy (θ h : K) (z : Fin n → K) : Finset ℤ :=
  (Finset.univ.image fun j ↦ cell h (z j)).filter fun p ↦ θ * n ≤ (cellCount h z p : K)

/-- The fraction of points in heavy cells. -/
def coverage (θ h : K) (z : Fin n → K) : K :=
  ((Finset.univ.filter fun j ↦ cell h (z j) ∈ heavy θ h z).card : K) / n

/-- The scale `H / 2^ℓ`. -/
def scale (H : K) (ℓ : ℕ) : K := H / 2 ^ ℓ

/-- The chosen level: the largest `ℓ ≤ ℓmax` whose coverage is at least `1 - ε`, or `0`. -/
def level (θ ε H : K) (ℓmax : ℕ) (z : Fin n → K) : ℕ :=
  ((Finset.range (ℓmax + 1)).filter fun ℓ ↦ 1 - ε ≤ coverage θ (scale H ℓ) z).sup id

/-- The next heavy cell after `p`, if any. -/
def next (S : Finset ℤ) (p : ℤ) : Option ℤ :=
  if h : (S.filter fun q ↦ p < q).Nonempty then some ((S.filter fun q ↦ p < q).min' h) else none

/-- The gap after the heavy cell `p` (in cells), `0` for the last heavy cell. -/
def gap (S : Finset ℤ) (p : ℤ) : ℤ :=
  match next S p with
  | some q => q - p
  | none => 0

/-- The heavy cells followed by another one, with a larger gap, or an equal gap further left. -/
def before (S : Finset ℤ) (p : ℤ) : Finset ℤ :=
  S.filter fun q ↦ (next S q).isSome ∧ (gap S p < gap S q ∨ (gap S q = gap S p ∧ q < p))

/-- The boundaries: the `k - 1` heavy cells, followed by another heavy cell, with the largest
gaps after them (ties broken towards the left). -/
def boundaries (k : ℕ) (S : Finset ℤ) : Finset ℤ :=
  S.filter fun p ↦ (next S p).isSome ∧ (before S p).card < k - 1

/-- The label of a point in the cell `p`: the number of boundaries `b` whose gap midpoint
`(b + next b) / 2` lies to the left of `p` (`2 p > b + next b`). -/
def labelOfCell (k : ℕ) (S : Finset ℤ) (p : ℤ) : ℕ :=
  ((boundaries k S).filter fun b ↦ b + (b + gap S b) < 2 * p).card

/-- **The clustering on the line**: the label of every point, at the chosen level. -/
def cluster (k : ℕ) (θ ε H : K) (ℓmax : ℕ) (z : Fin n → K) (j : Fin n) : ℕ :=
  let h := scale H (level θ ε H ℓmax z)
  labelOfCell k (heavy θ h z) (cell h (z j))

end BS23.OneDim
