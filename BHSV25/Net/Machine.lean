module

public import Background.Tuples
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Integer matrices on lists of numbers

The list operations under the greedy net (`BHSV25/Net/GSMachine.lean`), on the input `(n, a)` of a
graph with adjacency matrix `A` and degree `d` (read off vertex `0`):

* the number of vertices, capped at the length of the table (`BHSV25.Net.numV`), so that every
  loop is polynomial in the length of the input, also on inputs that are not graphs; the adjacency
  bits (`BHSV25.Net.adjB`) and the degree (`BHSV25.Net.deg`);
* the integer matrix `M = d I - A` (bottom eigenspace) or `M = A` (`BHSV25.Net.baseMat`), with
  `M / D = (I - Ã) / 2` for `D = 2 d` or `M / D = Ã` for `D = d` (`BHSV25.Net.denBase`);
* products and powers of square tables (`BHSV25.Net.mulL`, `BHSV25.Net.powL`), which compute
  matrix products and powers (`BHSV25.Net.toMat_powL`).
-/

@[expose] public section

namespace BHSV25

namespace Net

/-- The eigenspace of a filter: the bottom one (`bottom = true`) or that of the eigenvalues large
in absolute value. -/
structure Params where
  bottom : Bool

/-! ### The operations -/

/-- The number of vertices, capped at the length of the table. -/
def numV (x : ℕ × List Bool) : ℕ := min x.2.length x.1

/-- The adjacency bit of `u` and `v`: `a[u N + v]`. -/
def adjB (N : ℕ) (tab : List Bool) (u v : ℕ) : Bool := tab.getD (u * N + v) false

/-- The degree of vertex `0`: the number of `v < N` with `a[v] = true`. -/
def deg (N : ℕ) (tab : List Bool) : ℕ := (List.range N).countP fun v ↦ tab.getD v false

/-- The entries of the integer matrix `M`: `d [u = v] - [u ~ v]` for the bottom eigenspace,
`[u ~ v]` for the absolute one. -/
def entry (bottom : Bool) (N d : ℕ) (tab : List Bool) (u v : ℕ) : ℤ :=
  if bottom then (if u = v then (d : ℤ) else 0) - (if adjB N tab u v then 1 else 0)
  else if adjB N tab u v then 1 else 0

/-- The integer matrix `M`, as a list of rows. -/
def baseMat (bottom : Bool) (N d : ℕ) (tab : List Bool) : List (List ℤ) :=
  (List.range N).map fun u ↦ (List.range N).map fun v ↦ entry bottom N d tab u v

/-- The product of two `N × N` matrices given as lists of rows (missing entries are `0`). -/
def mulL (N : ℕ) (X Y : List (List ℤ)) : List (List ℤ) :=
  (List.range N).map fun u ↦ (List.range N).map fun v ↦
    ((List.range N).map fun w ↦ (X.getD u []).getD w 0 * (Y.getD w []).getD v 0).sum

/-- The `N × N` identity matrix. -/
def idL (N : ℕ) : List (List ℤ) :=
  (List.range N).map fun u ↦ (List.range N).map fun v ↦ if u = v then 1 else 0

/-- The power `M^e`, by `e` multiplications. -/
def powL (N : ℕ) (M : List (List ℤ)) (e : ℕ) : List (List ℤ) :=
  (fun X ↦ mulL N X M)^[e] (idL N)

/-- The base `D` of the denominator `D^e`. -/
def denBase (p : Params) (d : ℕ) : ℕ := (if p.bottom then 2 else 1) * d

/-! ### Lists of rows as matrices -/

/-- An `N × N` matrix given as a list of rows (missing entries are `0`). -/
def toMat (N : ℕ) (X : List (List ℤ)) : Matrix (Fin N) (Fin N) ℤ :=
  fun u v ↦ (X.getD u []).getD v 0

theorem getD_map_range {β : Type*} (N : ℕ) (F : ℕ → β) (d : β) {u : ℕ} (hu : u < N) :
    ((List.range N).map F).getD u d = F u := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu), List.getElem_map, List.getElem_range]

theorem sum_map_range {β : Type*} [AddCommMonoid β] (N : ℕ) (F : ℕ → β) :
    ((List.range N).map F).sum = ∑ i : Fin N, F i := by
  rw [Fin.sum_univ_eq_sum_range F N]
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem toMat_map_range (N : ℕ) (F : ℕ → ℕ → ℤ) :
    toMat N ((List.range N).map fun u ↦ (List.range N).map fun v ↦ F u v) =
      fun u v : Fin N ↦ F u v := by
  funext u v
  rw [toMat, getD_map_range N _ _ u.2, getD_map_range N _ _ v.2]

theorem toMat_mulL (N : ℕ) (X Y : List (List ℤ)) :
    toMat N (mulL N X Y) = toMat N X * toMat N Y := by
  rw [mulL, toMat_map_range]
  funext u v
  rw [Matrix.mul_apply, sum_map_range]
  rfl

theorem toMat_idL (N : ℕ) : toMat N (idL N) = 1 := by
  rw [idL, toMat_map_range]
  funext u v
  rw [Matrix.one_apply]
  by_cases h : u = v
  · simp [h]
  · have h' : (u : ℕ) ≠ v := fun h' ↦ h (Fin.ext h')
    simp [h, h']

theorem toMat_powL (N : ℕ) (M : List (List ℤ)) (e : ℕ) :
    toMat N (powL N M e) = toMat N M ^ e := by
  induction e with
  | zero => rw [powL, Function.iterate_zero, id, toMat_idL, pow_zero]
  | succ e ih =>
    rw [powL, Function.iterate_succ_apply', toMat_mulL, ← powL, ih, pow_succ]

theorem toMat_baseMat (bottom : Bool) (N d : ℕ) (tab : List Bool) :
    toMat N (baseMat bottom N d tab) = fun u v : Fin N ↦ entry bottom N d tab u v := by
  rw [baseMat, toMat_map_range]

end Net

end BHSV25
