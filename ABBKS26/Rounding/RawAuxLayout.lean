module

public import ABBKS26.Rounding.RawAux

/-! # Block indices and sparse presentations of the nested template -/

@[expose] public section

namespace ABBKS26.Rounding.RawAux

noncomputable section

open MvPolynomial Encoding SoS.Solver
open scoped BigOperators

variable {d : ℕ}

theorem prefix_block (f : ℕ → ℕ) {j m : ℕ} (hj : j < m) :
    ((List.range j).map f).sum + f j ≤ ((List.range m).map f).sum := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases h : j < m
    · exact (ih h).trans (Nat.le_add_right _ _)
    · have : j = m := by omega
      subst j
      rfl

theorem dimension_le_vars (A : FamilySystem d) (k : ℕ) : d ≤ nestedVars A k := by
  dsimp [nestedVars, slotOffset, plainOffset]
  omega

theorem plain_block (A : FamilySystem d) (k : ℕ) {j : ℕ}
    (hj : j < A.plain.length + 1) :
    plainOffset A k j + gramSize A k j ^ 2 ≤ nestedVars A k := by
  have := prefix_block (fun i ↦ gramSize A k i ^ 2) hj
  dsimp [nestedVars, slotOffset, plainOffset]
  omega

theorem slot_block (A : FamilySystem d) (k : ℕ) {a : ℕ}
    (ha : a < A.slots.length) :
    slotOffset A k a + familySize A k (A.slots[a]?.map Fin.val |>.getD 0) ^ 2 +
      d ^ 2 ≤ nestedVars A k := by
  have := prefix_block
    (fun i ↦ familySize A k (A.slots[i]?.map Fin.val |>.getD 0) ^ 2 + d ^ 2) ha
  dsimp [nestedVars, slotOffset]
  omega

theorem matrix_index {s n a c : ℕ} (ha : a < n) (hc : c < n) :
    s + a * n + c < s + n ^ 2 := by
  have := Nat.mul_le_mul_right n (show a + 1 ≤ n by omega)
  nlinarith


end

end ABBKS26.Rounding.RawAux
