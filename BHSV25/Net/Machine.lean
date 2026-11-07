module

public import Background.Tuples
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Cast.Defs

/-!
# The nets on lists of numbers

The algorithm behind `BHSV25/Net/Spec.lean`, as a function on lists (`BHSV25.Net.netList`), with
fixed natural parameters (`BHSV25.Net.Params`). On the input `(n, a)` of a graph with adjacency
matrix `A` and degree `d` (read off vertex `0`), it

1. forms the integer matrix `M = d I - A` (for the bottom eigenspace) or `M = A` (for the
   absolute one), so that `M / D` is `(I - Ã) / 2` with `D = 2 d`, or `Ã` with `D = d`;
2. computes `Q = M^e` exactly, with `e = c (a + 2 ⌈log₂ (n + 1)⌉)` for the bottom eigenspace and
   twice that for the absolute one: `Q / D^e` is the filter `P` of `BHSV25/Net/Approx.lean`;
3. lists, for all `T`-tuples `v` of vertices and `z` of integers in `[0, 2 Z]`, the vector
   `∑ⱼ (zⱼ - Z) Q e_{vⱼ} / (S D^e)`, with `S = K n` and `Z = Z_c (n + 1)^{Z_e}`, together with the
   empty list (the zero vector).

The tuples are those of `Background/Tuples.lean`, cut at the budget `(n + 2 Z + 1)^T`, which cuts
nothing. The number of vertices is capped at the length of the table (`BHSV25.Net.numV`), so that
every loop is polynomial in the length of the input, also on inputs that are not graphs.

This file also proves that the list operations compute matrix products and powers
(`BHSV25.Net.toMat_powL`).
-/

@[expose] public section

namespace BHSV25

namespace Net

/-- The parameters of the algorithm: the eigenspace (`bottom`), the length `T` of the tuples, the
exponent `c (a + 2 ⌈log₂ (n + 1)⌉)`, the scale `S = K n` and the range `Z = Z_c (n + 1)^{Z_e}`. -/
structure Params where
  bottom : Bool
  T : ℕ
  c : ℕ
  a : ℕ
  K : ℕ
  Zc : ℕ
  Ze : ℕ

/-! ### The algorithm -/

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

/-- The exponent `e`. -/
def expo (p : Params) (N : ℕ) : ℕ := (if p.bottom then 1 else 2) * (p.c * (p.a + 2 * N.size))

/-- The base `D` of the denominator `D^e`. -/
def denBase (p : Params) (d : ℕ) : ℕ := (if p.bottom then 2 else 1) * d

/-- The range `Z` of the coefficients. -/
def zMax (p : Params) (N : ℕ) : ℕ := p.Zc * (N + 1) ^ p.Ze

/-- The budget of the tuples. -/
def budget (p : Params) (N : ℕ) : ℕ := (N + 2 * zMax p N + 1) ^ p.T

/-- The candidate `∑ⱼ (zⱼ - Z) Q e_{vⱼ} / q`, for the rows `vⱼ` of `Q`. -/
def cand (T N Z : ℕ) (q : ℚ) (Q : List (List ℤ)) (vs zs : List ℕ) : List ℚ :=
  (List.range N).map fun u ↦
    ((((List.range T).map fun j ↦
      ((zs.getD j 0 : ℤ) - Z) * (Q.getD (vs.getD j 0) []).getD u 0).sum : ℤ) : ℚ) / q

/-- What the candidates are made of: `N`, `Z`, `q = S D^e`, `Q = M^e` and the budget. -/
def ctx (p : Params) (x : ℕ × List Bool) : ℕ × ℕ × ℚ × List (List ℤ) × ℕ :=
  (numV x, zMax p (numV x),
    ((p.K * numV x * denBase p (deg (numV x) x.2) ^ expo p (numV x) : ℕ) : ℚ),
    powL (numV x) (baseMat p.bottom (numV x) (deg (numV x) x.2) x.2) (expo p (numV x)),
    budget p (numV x))

/-- All candidates. -/
def body (T : ℕ) (c : ℕ × ℕ × ℚ × List (List ℤ) × ℕ) : List (List ℚ) :=
  (Tuples.tuples c.2.2.2.2 c.1 T).flatMap fun vs ↦
    (Tuples.tuples c.2.2.2.2 (2 * c.2.1 + 1) T).map fun zs ↦
      cand T c.1 c.2.1 c.2.2.1 c.2.2.2.1 vs zs

/-- **The net**: the zero vector and all candidates. -/
def netList (p : Params) (x : ℕ × List Bool) : List (List ℚ) := [] :: body p.T (ctx p x)

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
