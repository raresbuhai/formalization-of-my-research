module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdPayload
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdSolver

/-! Prepared enumeration and nested-layout allowances for high-degree SUB. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdPrepared

open Common Rounding _root_.ABBKS26.Tree Sources Builders
open SoS.Solver (RawPoly)

noncomputable section

/-- The dimension factor of the public allowance pays for all local powers below this
explicit quadratic degree exponent. -/
theorem power_fuel {n k d : ℕ} (ps : ℕ → StepParams) (fuel h : ℕ)
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (e : ℕ) (he : e ≤ 1000 * (IdCov.tDegree (ps h).w) ^ 2) :
    (d + 2) ^ e ≤ fuel := by
  have ht := IdInput.prepared_degree ps M ε w η Δ D ω r hp h hh
  have hexp : e ≤ 1000000000 * (solverConstant + 1) * (IdCov.tDegree (ps 0).w) ^ 2 := by
    rw [ht] at he
    have hc : 1000 ≤ 1000000000 * (solverConstant + 1) := by omega
    exact he.trans (Nat.mul_le_mul_right _ hc)
  apply le_trans _ hf
  unfold localBudget
  rw [ite_eq_right (by decide : Mode.identical ≠ .centered)]
  apply (Nat.pow_le_pow_right (by omega : 1 ≤ d + 2) hexp).trans
  exact (Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))).trans
    (Nat.le_mul_of_pos_left _ (by positivity))

theorem enumeration {n k d : ℕ} (ps : ℕ → StepParams) (fuel h : ℕ)
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (q : ℕ) (hq : q ≤ 4 * IdCov.tDegree (ps h).w) :
    q ≤ fuel ∧ (d + 1) ^ q ≤ fuel := by
  have ht : 3 ≤ IdCov.tDegree (ps h).w := by unfold IdCov.tDegree; omega
  have he : q ≤ 1000 * (IdCov.tDegree (ps h).w) ^ 2 := by
    nlinarith only [hq, ht]
  have hb := power_fuel ps fuel h M ε w η Δ D ω r hp hf hh q he
  exact ⟨((Nat.lt_two_pow_self (n := q)).le.trans
    (Nat.pow_le_pow_left (by omega : 2 ≤ d + 2) q)).trans hb,
    (Nat.pow_le_pow_left (by omega : d + 1 ≤ d + 2) q).trans hb⟩

/-- A quadratic rounded moment raised to any needed order stays inside the enumeration
allowance. The extra term is the zero padding used by `IdSystem.power`. -/
theorem expansion {n k d : ℕ} (ps : ℕ → StepParams) (fuel h : ℕ)
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (s L : ℕ) (hs : s ≤ 2 * IdCov.tDegree (ps h).w) (hL : L ≤ (d + 1) ^ 2) :
    (L + 1) ^ s ≤ fuel := by
  have ht : 3 ≤ IdCov.tDegree (ps h).w := by unfold IdCov.tDegree; omega
  have hbase : L + 1 ≤ (d + 2) ^ 3 := by
    have hb : L + 1 ≤ (d + 2) ^ 2 := by nlinarith only [hL, Nat.zero_le d]
    exact hb.trans (Nat.pow_le_pow_right (by omega) (by norm_num : 2 ≤ 3))
  calc
    _ ≤ ((d + 2) ^ 3) ^ s := Nat.pow_le_pow_left hbase s
    _ = (d + 2) ^ (3 * s) := (pow_mul _ _ _).symm
    _ ≤ fuel := power_fuel ps fuel h M ε w η Δ D ω r hp hf hh _ (by
      nlinarith only [hs, ht])

/-- Plain SUB needs no matrix slots, so its local layout costs only a quadratic degree
exponent. Its coefficient bits do not enter this estimate. -/
theorem layout_bound (d t : ℕ) (A : List RawPoly) (ht : 3 ≤ t)
    (hA : A.length ≤ 2 * t + 1) :
    IdSolver.layoutFuel d (8 * t) A ≤ (d + 2) ^ (200 * t ^ 2) := by
  let b := d + 2
  have hb : 2 ≤ b := by omega
  have hf : A.length + 1 ≤ b ^ (t + 1) := by
    calc
      _ ≤ 2 * (t + 1) := by omega
      _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 (Nat.lt_two_pow_self (n := t))
      _ ≤ b * b ^ t := Nat.mul_le_mul hb (Nat.pow_le_pow_left hb t)
      _ = b ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]
  have hp : (A.length + 1) * (d + 1) ^ (8 * t) ≤ b ^ (9 * t + 1) := by
    calc
      _ ≤ b ^ (t + 1) * b ^ (8 * t) :=
        Nat.mul_le_mul hf (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hinner : d + (A.length + 1) * (d + 1) ^ (8 * t) + 2 ≤
      b ^ (9 * t + 2) := by
    have hdim : b ≤ b ^ (9 * t + 1) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ b)
        (show 1 ≤ 9 * t + 1 by omega)
    calc
      _ ≤ b ^ (9 * t + 1) + b ^ (9 * t + 1) := by omega
      _ = 2 * b ^ (9 * t + 1) := by omega
      _ ≤ b * b ^ (9 * t + 1) := Nat.mul_le_mul_right _ hb
      _ = _ := by
        rw [show 9 * t + 2 = (9 * t + 1) + 1 by omega, pow_succ]
        exact Nat.mul_comm _ _
  unfold IdSolver.layoutFuel
  apply (Nat.pow_le_pow_left hinner _).trans
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by omega : 1 ≤ b)
  nlinarith only [ht]

theorem layout {n k d : ℕ} (ps : ℕ → StepParams) (fuel h : ℕ)
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (A : List RawPoly) (hA : A.length ≤ 2 * IdCov.tDegree (ps h).w + 1) :
    IdSolver.layoutFuel d (8 * IdCov.tDegree (ps h).w) A ≤ fuel := by
  exact (layout_bound d _ A (by unfold IdCov.tDegree; omega) hA).trans
    (power_fuel ps fuel h M ε w η Δ D ω r hp hf hh _ (by omega))

end

end ABBKS26.Assembly.Exec.RefineSynth.IdPrepared
