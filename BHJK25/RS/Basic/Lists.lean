module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.GetD

/-!
# Lists over `List.range`

The entries (`BHJK25.RS.getD_map_range`) and the sum (`BHJK25.RS.sum_map_range`) of a list
`(List.range n).map f`, as used by the list programs of the decoder and of the algorithm.
-/

@[expose] public section

namespace BHJK25.RS

/-- Entry `j` of `(List.range n).map f` is `f j` for `j < n`, and the default otherwise. -/
theorem getD_map_range {α : Type*} (n : ℕ) (f : ℕ → α) (d : α) (j : ℕ) :
    ((List.range n).map f).getD j d = if j < n then f j else d := by
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getElem_range]
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem getD_map_range_of_lt {α : Type*} {n j : ℕ} (f : ℕ → α) (d : α) (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [getD_map_range, ite_eq_left hj]

/-- The sum of `(List.range n).map f` is `Σ_{j < n} f j`. -/
theorem sum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, ih, Finset.sum_range_succ]

end BHJK25.RS
