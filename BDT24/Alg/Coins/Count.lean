module

public import BDT24.Model

/-!
# Counting coin strings

Generalities on `BDT24.coinProb`, the probability of an event over a uniform string of coins,
following `BS23/SmallRadius/Coins.lean`: probabilities as sums, a string of `a + b` coins as a
string of `a` coins followed by one of `b` coins (`BDT24.Alg.CN.coinProb_split`), events on
disjoint blocks multiply (`BDT24.Alg.CN.coinProb_and`, `BDT24.Alg.CN.coinProb_blocks`), events on
a prefix or a later block (`BDT24.Alg.CN.coinProb_take`, `BDT24.Alg.CN.coinProb_drop`), the
union bound and complements.
-/

@[expose] public section

namespace BDT24.Alg.CN

open Finset

open Classical in
/-- A coin probability as an average of an indicator. -/
theorem coinProb_eq_sum (T : ℕ) (P : List Bool → Prop) :
    coinProb T P = (∑ c : Fin T → Bool, if P (List.ofFn c) then (1 : ℝ) else 0) / 2 ^ T := by
  unfold coinProb
  rw [Fintype.card_subtype, natCast_card_filter]

/-- Coin probabilities are nonnegative. -/
theorem coinProb_nonneg (T : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb T P := by
  unfold coinProb
  positivity

/-- Events that agree on strings of `T` coins have the same probability. -/
theorem coinProb_congr {T : ℕ} {P Q : List Bool → Prop}
    (h : ∀ c : Fin T → Bool, P (List.ofFn c) ↔ Q (List.ofFn c)) : coinProb T P = coinProb T Q := by
  classical
  rw [coinProb_eq_sum, coinProb_eq_sum]
  congr 1
  exact sum_congr rfl fun c _ ↦ if_congr (h c) rfl rfl

/-- Strings of `a + b` coins are a string of `a` coins followed by a string of `b` coins. -/
theorem sum_ofFn_append {a b : ℕ} (F : List Bool → ℝ) :
    ∑ c : Fin (a + b) → Bool, F (List.ofFn c) =
      ∑ p : Fin a → Bool, ∑ w : Fin b → Bool, F (List.ofFn p ++ List.ofFn w) := by
  rw [← (Fin.appendEquiv a b).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun p _ ↦ sum_congr rfl fun w _ ↦ ?_
  change F (List.ofFn (Fin.append p w)) = _
  rw [List.ofFn_fin_append]

/-- **Splitting the coins**: an event on the first `a` and the last `b` of `a + b` coins has the
average over the first `a` coins of its probability over the last `b`. -/
theorem coinProb_split (a b : ℕ) (P : List Bool → List Bool → Prop) :
    coinProb (a + b) (fun c ↦ P (c.take a) (c.drop a)) =
      (∑ p : Fin a → Bool, coinProb b (P (List.ofFn p))) / 2 ^ a := by
  classical
  rw [coinProb_eq_sum, sum_ofFn_append (fun l ↦ if P (l.take a) (l.drop a) then (1 : ℝ) else 0)]
  simp only [List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  simp only [coinProb_eq_sum, ← sum_div, pow_add, div_div, mul_comm ((2 : ℝ) ^ a)]

/-- **Disjoint blocks are independent**: an event on the first `a` coins and one on the last `b`
of `a + b` coins. -/
theorem coinProb_and (a b : ℕ) (P Q : List Bool → Prop) :
    coinProb (a + b) (fun c ↦ P (c.take a) ∧ Q (c.drop a)) = coinProb a P * coinProb b Q := by
  classical
  rw [coinProb_split a b (fun u w ↦ P u ∧ Q w), coinProb_eq_sum a P, div_mul_eq_mul_div,
    sum_mul]
  congr 1
  refine sum_congr rfl fun p _ ↦ ?_
  by_cases hp : P (List.ofFn p)
  · simp only [hp, true_and, ite_true, one_mul]
  · simp only [hp, false_and, ite_false, zero_mul]
    rw [coinProb_eq_sum]
    simp

/-- The event that always holds. -/
theorem coinProb_true (T : ℕ) : coinProb T (fun _ ↦ True) = 1 := by
  classical
  rw [coinProb_eq_sum]
  simp

/-- An event on the coins after the first `a` has its probability on the remaining `b` coins. -/
theorem coinProb_drop (a b : ℕ) (Q : List Bool → Prop) :
    coinProb (a + b) (fun c ↦ Q (c.drop a)) = coinProb b Q := by
  have h := coinProb_and a b (fun _ ↦ True) Q
  simp only [true_and, coinProb_true, one_mul] at h
  exact h

/-- An event on the first `T` of `L ≥ T` coins has its probability on `T` coins. -/
theorem coinProb_take (T L : ℕ) (hT : T ≤ L) (P : List Bool → Prop) :
    coinProb L (fun r ↦ P (r.take T)) = coinProb T P := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hT
  have h := coinProb_and T b P (fun _ ↦ True)
  simp only [and_true, coinProb_true, mul_one] at h
  exact h

/-- **The union bound.** -/
theorem coinProb_or_le (T : ℕ) (P Q : List Bool → Prop) :
    coinProb T (fun c ↦ P c ∨ Q c) ≤ coinProb T P + coinProb T Q := by
  classical
  simp only [coinProb_eq_sum, ← add_div, ← sum_add_distrib]
  gcongr with c
  by_cases hP : P (List.ofFn c) <;> by_cases hQ : Q (List.ofFn c) <;> simp [hP, hQ]

/-- An event and its complement. -/
theorem coinProb_add_not (T : ℕ) (P : List Bool → Prop) :
    coinProb T P + coinProb T (fun r ↦ ¬ P r) = 1 := by
  classical
  simp only [coinProb_eq_sum, ← add_div, ← sum_add_distrib]
  rw [div_eq_one_iff_eq (by positivity), sum_congr rfl (g := fun _ ↦ (1 : ℝ)) fun c _ ↦ by
    by_cases hP : P (List.ofFn c) <;> simp [hP]]
  simp

/-- **Independent blocks**: the probability that the same event holds on each of the first `R`
blocks of `L` coins of `T ≥ R L` coins is its probability on `L` coins, to the power `R`. -/
theorem coinProb_blocks (L : ℕ) (Q : List Bool → Prop) (R T : ℕ) (hT : R * L ≤ T) :
    coinProb T (fun c ↦ ∀ j < R, Q ((c.drop (j * L)).take L)) = coinProb L Q ^ R := by
  induction R generalizing T with
  | zero =>
    simp only [Nat.not_lt_zero, false_imp_iff, implies_true, pow_zero]
    exact coinProb_true T
  | succ R ih =>
    have hLT : L ≤ T := le_trans (by nlinarith) hT
    obtain ⟨T', rfl⟩ := Nat.exists_eq_add_of_le hLT
    have hT' : R * L ≤ T' := by nlinarith
    have hev : (fun c : List Bool ↦ ∀ j < R + 1, Q ((c.drop (j * L)).take L)) =
        fun c ↦ Q (c.take L) ∧ ∀ j < R, Q (((c.drop L).drop (j * L)).take L) := by
      funext c
      rw [Nat.forall_lt_succ_left, zero_mul, List.drop_zero]
      refine propext (and_congr Iff.rfl (forall₂_congr fun j _ ↦ ?_))
      rw [List.drop_drop, Nat.succ_mul, Nat.add_comm (j * L) L]
    have h := coinProb_and L T' Q (fun d ↦ ∀ j < R, Q ((d.drop (j * L)).take L))
    rw [ih T' hT'] at h
    rw [hev, h, pow_succ']

end BDT24.Alg.CN
