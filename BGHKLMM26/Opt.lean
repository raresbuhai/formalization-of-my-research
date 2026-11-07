module

public import BGHKLMM26.Model
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators

/-!
# The optimum is at least half the total weight

A uniformly random assignment satisfies each constraint `xᵢ xⱼ = b` (on two distinct variables)
with probability `1/2`, so `opt ≥ W / 2` for the total weight `W` (`BGHKLMM26.opt_ge_half`). The
algorithm's additive losses are charged against this.
-/

@[expose] public section

namespace BGHKLMM26

open Finset

/-- An assignment of the variables `0, …, n - 1`, extended by `false`. -/
def extend {n : ℕ} (x : Fin n → Bool) (v : ℕ) : Bool := if h : v < n then x ⟨v, h⟩ else false

/-- The total weight of an instance. -/
def totalWeight (I : Instance) : ℝ := (I.2.map fun c ↦ (c.2.2 : ℝ)).sum

/-- Flipping one variable toggles every constraint on it: a constraint is satisfied by exactly
one of `x` and `x` with `xⱼ` flipped. -/
theorem sum_sat_flip {n : ℕ} (c : Constraint) (hc : c.1.1 < c.1.2 ∧ c.1.2 < n) :
    ∑ x : Fin n → Bool, (if decide (extend x c.1.1 = extend x c.1.2) = c.2.1 then
      (c.2.2 : ℝ) else 0) = 2 ^ n * ((c.2.2 : ℝ) / 2) := by
  set j : Fin n := ⟨c.1.2, hc.2⟩
  set f : (Fin n → Bool) → ℝ := fun x ↦
    if decide (extend x c.1.1 = extend x c.1.2) = c.2.1 then (c.2.2 : ℝ) else 0 with hfdef
  let flip : (Fin n → Bool) ≃ (Fin n → Bool) :=
    { toFun := fun x ↦ Function.update x j (!x j)
      invFun := fun x ↦ Function.update x j (!x j)
      left_inv := fun x ↦ by ext k; by_cases hk : k = j <;> simp [hk]
      right_inv := fun x ↦ by ext k; by_cases hk : k = j <;> simp [hk] }
  have hpair : ∀ x, f x + f (flip x) = c.2.2 := by
    intro x
    have hi : c.1.1 < n := hc.1.trans hc.2
    have hij : (⟨c.1.1, hi⟩ : Fin n) ≠ j := fun h ↦ by
      have := congrArg Fin.val h
      simp [j] at this
      omega
    simp only [hfdef, flip, Equiv.coe_fn_mk, extend, dite_eq_left hi, dite_eq_left hc.2,
      Function.update_of_ne hij]
    have hj : (⟨c.1.2, hc.2⟩ : Fin n) = j := rfl
    rw [hj]
    cases x ⟨c.1.1, hi⟩ <;> cases x j <;> cases c.2.1 <;> simp
  have hsum : ∑ x, f (flip x) = ∑ x, f x := Equiv.sum_comp flip f
  have h2 : 2 * ∑ x, f x = ∑ x : Fin n → Bool, (c.2.2 : ℝ) := by
    rw [two_mul]
    nth_rewrite 2 [← hsum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ ↦ hpair x
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    nsmul_eq_mul] at h2
  push_cast at h2
  linarith

theorem sum_satWeight_extend (n : ℕ) (l : List Constraint)
    (hval : ∀ c ∈ l, c.1.1 < c.1.2 ∧ c.1.2 < n) :
    ∑ x : Fin n → Bool, satWeight (n, l) (extend x) =
      2 ^ n * ((l.map fun c ↦ (c.2.2 : ℝ)).sum / 2) := by
  unfold satWeight
  induction l with
  | nil => simp
  | cons c l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib, sum_sat_flip c (hval c List.mem_cons_self),
      ih fun c' hc' ↦ hval c' (List.mem_cons_of_mem _ hc')]
    ring

/-- `opt ≥ W / 2`. -/
theorem opt_ge_half {I : Instance} (hI : Valid I) : totalWeight I / 2 ≤ opt I := by
  set n := I.1
  -- The average of the satisfied weight over all assignments is `W / 2`.
  have havg : ∑ x : Fin n → Bool, satWeight I (extend x) = 2 ^ n * (totalWeight I / 2) :=
    sum_satWeight_extend I.1 I.2 fun c hc ↦ ⟨(hI.1 c hc).1, (hI.1 c hc).2.1⟩
  -- Some assignment is at least the average.
  obtain ⟨x, -, hx⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    (f := fun _ : Fin n → Bool ↦ totalWeight I / 2)
    (g := fun x ↦ satWeight I (extend x)) Finset.univ_nonempty (by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, havg]
      push_cast
      rfl)
  have := le_ciSup (f := fun x : Fin n → Bool ↦ satWeight I (extend x))
    (Set.finite_range _).bddAbove x
  exact hx.trans this

end BGHKLMM26
