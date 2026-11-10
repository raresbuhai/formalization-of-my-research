module

public import ABBKS26.Common.Gram
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Sparse presentations for the nested encoding

The outer exponents are discarded by coefficient extraction. Only the inner exponents
contribute to the final solver encoding.
-/

@[expose] public section

namespace ABBKS26.Rounding.RawAux

noncomputable section

open MvPolynomial Encoding SoS.Solver
open scoped BigOperators

variable {σ : Type}


theorem length_rat_neg (q : ℚ) : (encRat (-q)).length = (encRat q).length := by
  change (frame (decide ((-q).num < 0) :: encNat (-q).num.natAbs) ++
      encNat (-q).den).length =
    (frame (decide (q.num < 0) :: encNat q.num.natAbs) ++ encNat q.den).length
  simp [frame]


theorem length_pair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (p : α × β) : (encPair a b p).length = 2 * (a p.1).length + 1 + (b p.2).length := by
  change (frame (a p.1) ++ b p.2).length = _
  simp [frame]
  omega

theorem length_list_le {α : Type} (e : α ↪ List Bool) (l : List α) {b : ℕ}
    (hb : ∀ a ∈ l, (e a).length ≤ b) :
    (encList e l).length ≤ l.length * (2 * b + 1) := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    change (frame (e a) ++ encList e l).length ≤ _
    have := hb a (by simp)
    have := ih fun a ha ↦ hb a (by simp [ha])
    simp only [List.length_append, List.length_cons, Nat.add_mul]
    have hf : (frame (e a)).length = 2 * (e a).length + 1 := by simp [frame]; omega
    omega

theorem length_nat_le (n : ℕ) : (encNat n).length ≤ n := by
  change n.bits.length ≤ n
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le_self n


theorem length_list {α : Type} (e : α ↪ List Bool) (l : List α) :
    (encList e l).length = (l.map fun a ↦ 2 * (e a).length + 1).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change (frame (e a) ++ encList e l).length = _
    simp only [List.length_append, List.map_cons, List.sum_cons, ← ih]
    simp [frame]
    omega


theorem length_elem {α : Type} (e : α ↪ List Bool) (l : List α) (a : α)
    (ha : a ∈ l) : (e a).length ≤ (encList e l).length := by
  rw [length_list]
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · exact (ih ha).trans (Nat.le_add_left _ _)

theorem length_count {α : Type} (e : α ↪ List Bool) (l : List α) :
    l.length ≤ (encList e l).length := by
  rw [length_list]
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega


end

end ABBKS26.Rounding.RawAux
