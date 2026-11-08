module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Orthogonality of the shifted Legendre polynomials

The shifted Legendre polynomials `P_k` (`Polynomial.shiftedLegendre`, here with real coefficients,
`BHJK25.Spectral.LegendreAux.leg`) are orthogonal in `L²[0, 1]`, with
`∫₀¹ P_j P_k = δ_{jk} / (2k + 1)`. By Rodrigues' formula `k! P_k = D^k [X^k (1 - X)^k]` and `k`
integrations by parts, `P_k` is orthogonal to every polynomial of degree less than `k`, and
`∫₀¹ P_k² = C(2k, k) ∫₀¹ x^k (1 - x)^k dx = 1 / (2k + 1)` by the Beta integral.
-/

@[expose] public section

namespace BHJK25.Spectral.LegendreAux

open Polynomial intervalIntegral Nat

/-- The shifted Legendre polynomial `P_k` with real coefficients. -/
noncomputable def leg (k : ℕ) : ℝ[X] := (shiftedLegendre k).map (Int.castRingHom ℝ)

/-- The inner product of two polynomials in `L²[0, 1]`. -/
noncomputable def ip (f g : ℝ[X]) : ℝ := ∫ x in (0 : ℝ)..1, f.eval x * g.eval x

/-- The polynomial `X^k (1 - X)^k` of Rodrigues' formula. -/
noncomputable def rod (k : ℕ) : ℝ[X] := X ^ k * (1 - X) ^ k

theorem intervalIntegrable_eval_mul (f g : ℝ[X]) (a b : ℝ) :
    IntervalIntegrable (fun x ↦ f.eval x * g.eval x) MeasureTheory.volume a b :=
  (f.continuous.mul g.continuous).intervalIntegrable a b

theorem ip_comm (f g : ℝ[X]) : ip f g = ip g f := by
  simp only [ip, mul_comm]

theorem ip_smul_right (f g : ℝ[X]) (c : ℝ) : ip f (C c * g) = c * ip f g := by
  rw [ip, ip, ← integral_const_mul]
  congr 1
  ext x
  rw [eval_mul, eval_C]
  ring

theorem ip_natCast_mul_right (f g : ℝ[X]) (n : ℕ) : ip f (n * g) = n * ip f g := by
  rw [← C_eq_natCast, ip_smul_right]

theorem ip_zero_right (f : ℝ[X]) : ip f 0 = 0 := by
  simp [ip]

/-- The inner product is linear in its second argument. -/
theorem ip_sum_right (f : ℝ[X]) (s : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℝ[X]) :
    ip f (∑ k ∈ s, C (a k) * g k) = ∑ k ∈ s, a k * ip f (g k) := by
  have h : ∀ x, f.eval x * (∑ k ∈ s, C (a k) * g k).eval x =
      ∑ k ∈ s, a k * (f.eval x * (g k).eval x) := fun x ↦ by
    rw [eval_finsetSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [eval_mul, eval_C]
    ring
  simp only [ip, h]
  rw [integral_finsetSum fun k _ ↦ (intervalIntegrable_eval_mul f (g k) 0 1).const_mul (a k)]
  exact Finset.sum_congr rfl fun k _ ↦ integral_const_mul _ _

/-- The fundamental theorem of calculus for polynomials. -/
theorem integral_eval_derivative (p : ℝ[X]) (a b : ℝ) :
    ∫ x in a..b, (derivative p).eval x = p.eval b - p.eval a :=
  integral_eq_sub_of_hasDerivAt (fun x _ ↦ p.hasDerivAt x)
    (p.derivative.continuous.intervalIntegrable a b)

/-- Integration by parts on `[0, 1]`. -/
theorem ip_derivative (f g : ℝ[X]) :
    ip f (derivative g) = f.eval 1 * g.eval 1 - f.eval 0 * g.eval 0 - ip (derivative f) g := by
  have h := integral_eval_derivative (f * g) 0 1
  simp only [derivative_mul, eval_add, eval_mul] at h
  rw [integral_add (intervalIntegrable_eval_mul _ _ 0 1)
    (intervalIntegrable_eval_mul _ _ 0 1)] at h
  rw [ip, ip]
  linarith

/-- `m` integrations by parts on `[0, 1]`, against a polynomial whose derivatives of order less
than `m` vanish at `0` and `1`. -/
theorem ip_iterate_derivative (g : ℝ[X]) (m : ℕ)
    (hg : ∀ i < m, (derivative^[i] g).eval 0 = 0 ∧ (derivative^[i] g).eval 1 = 0) (f : ℝ[X]) :
    ip f (derivative^[m] g) = (-1) ^ m * ip (derivative^[m] f) g := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ip_derivative, (hg m (by lia)).1, (hg m (by lia)).2,
      ih (fun i hi ↦ hg i (by lia)), ← Function.iterate_succ_apply]
    ring

/-- The derivatives of order less than `k` of `X^k (1 - X)^k` vanish at `0` and `1`. -/
theorem iterate_derivative_rod_eval {k i : ℕ} (hi : i < k) :
    (derivative^[i] (rod k)).eval 0 = 0 ∧ (derivative^[i] (rod k)).eval 1 = 0 := by
  have hk : k - i ≠ 0 := by lia
  constructor
  · obtain ⟨c, hc⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd i
      (dvd_mul_right (X ^ k) ((1 - X : ℝ[X]) ^ k))
    rw [rod, hc, eval_mul, eval_pow, eval_X, zero_pow hk, zero_mul]
  · obtain ⟨c, hc⟩ := pow_sub_dvd_iterate_derivative_of_pow_dvd i
      (dvd_mul_left ((1 - X : ℝ[X]) ^ k) (X ^ k))
    rw [rod, hc, eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_self, zero_pow hk, zero_mul]

/-- Rodrigues' formula: `k! P_k = D^k [X^k (1 - X)^k]`. -/
theorem factorial_mul_leg (k : ℕ) : (k ! : ℝ[X]) * leg k = derivative^[k] (rod k) := by
  have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (factorial_mul_shiftedLegendre_eq k)
  rw [Polynomial.map_mul, ← iterate_derivative_map] at h
  simpa [leg, rod] using h

theorem natDegree_leg (k : ℕ) : (leg k).natDegree = k := by
  rw [leg, natDegree_map_eq_of_injective (RingHom.injective_int _), natDegree_shiftedLegendre]

theorem coeff_leg (k i : ℕ) :
    (leg k).coeff i = (-1) ^ i * k.choose i * (k + i).choose k := by
  simp [leg, coeff_shiftedLegendre]

/-- `P_k` is orthogonal to the polynomials of degree less than `k`. -/
theorem ip_leg_eq_zero (f : ℝ[X]) {k : ℕ} (hf : f.natDegree < k) : ip f (leg k) = 0 := by
  have h : ip f (derivative^[k] (rod k)) = 0 := by
    rw [ip_iterate_derivative _ _ (fun i hi ↦ iterate_derivative_rod_eval hi),
      iterate_derivative_eq_zero hf]
    simp [ip]
  rw [← factorial_mul_leg, ip_natCast_mul_right] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast factorial_ne_zero k)

/-- The `k`-th derivative of `P_k` is the constant `k! (-1)^k C(2k, k)`. -/
theorem iterate_derivative_leg (k : ℕ) :
    derivative^[k] (leg k) = C ((k ! : ℝ) * ((-1) ^ k * ((2 * k).choose k : ℝ))) := by
  have hdeg : (derivative^[k] (leg k)).natDegree ≤ 0 := by
    have := natDegree_iterate_derivative (leg k) k
    rw [natDegree_leg, Nat.sub_self] at this
    exact this
  rw [eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add, descFactorial_self,
    coeff_leg, choose_self, two_mul, nsmul_eq_mul]
  push_cast
  congr 1
  ring

/-- The Beta integral `∫₀¹ x^a (1 - x)^b dx = a! b! / (a + b + 1)!`. -/
theorem integral_pow_mul_one_sub_pow (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b = a ! * b ! / (a + b + 1 : ℕ)! := by
  induction b generalizing a with
  | zero =>
    simp only [pow_zero, mul_one, integral_pow, add_zero, factorial_succ]
    push_cast
    field_simp
    ring
  | succ b ih =>
    have key : ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1) =
        (b + 1) / (a + 1) * ∫ x in (0 : ℝ)..1, x ^ (a + 1) * (1 - x) ^ b := by
      have hu : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ ↦ (1 - x) ^ (b + 1))
          (-((b + 1) * (1 - x) ^ b)) x := fun x _ ↦ by
        refine (((hasDerivAt_id x).const_sub 1).pow (b + 1)).congr_deriv ?_
        rw [Nat.add_sub_cancel]
        push_cast
        simp only [id]
        ring
      have hv : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ ↦ x ^ (a + 1) / (a + 1))
          (x ^ a) x := fun x _ ↦ by
        refine ((hasDerivAt_pow (a + 1) x).div_const ((a : ℝ) + 1)).congr_deriv ?_
        rw [Nat.add_sub_cancel]
        push_cast
        field_simp
      have h := integral_mul_deriv_eq_deriv_mul hu hv
        (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _)
      simp only [one_pow, sub_self, zero_pow (succ_ne_zero _), zero_mul, sub_zero, zero_div,
        mul_zero, zero_sub] at h
      rw [← integral_const_mul]
      calc ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ (b + 1)
          = ∫ x in (0 : ℝ)..1, (1 - x) ^ (b + 1) * x ^ a := by simp only [mul_comm]
        _ = _ := by
          rw [h, ← integral_neg]
          congr 1
          ext x
          field_simp
    rw [key, ih (a + 1), show a + 1 + b + 1 = a + (b + 1) + 1 by ring]
    rw [factorial_succ a, factorial_succ b]
    push_cast
    field_simp

/-- `∫₀¹ P_k² = 1 / (2k + 1)`. -/
theorem ip_leg_self (k : ℕ) : ip (leg k) (leg k) = 1 / (2 * k + 1) := by
  have h : (k ! : ℝ) * ip (leg k) (leg k) =
      (-1) ^ k * ((k ! : ℝ) * ((-1) ^ k * ((2 * k).choose k : ℝ))) * ip 1 (rod k) := by
    rw [← ip_natCast_mul_right, factorial_mul_leg,
      ip_iterate_derivative _ _ (fun i hi ↦ iterate_derivative_rod_eval hi),
      iterate_derivative_leg, ip_comm, ← mul_one (C _), ip_smul_right, ip_comm]
    ring
  have hrod : ip 1 (rod k) = (k ! * k ! : ℝ) / (2 * k + 1 : ℕ)! := by
    rw [show 2 * k + 1 = k + k + 1 by ring, ← integral_pow_mul_one_sub_pow, ip]
    simp [rod]
  have hc : ((2 * k).choose k : ℝ) * k ! * k ! = (2 * k)! := by
    have := choose_mul_factorial_mul_factorial (by lia : k ≤ 2 * k)
    rw [show 2 * k - k = k by lia] at this
    exact_mod_cast this
  have h2 : ((2 * k + 1 : ℕ)! : ℝ) = (2 * k + 1) * (2 * k)! := by
    rw [factorial_succ]
    push_cast
    ring
  have h1 : ((-1 : ℝ) ^ k) * (-1) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  have hk : (k ! : ℝ) ≠ 0 := by exact_mod_cast factorial_ne_zero k
  have h2k : ((2 * k)! : ℝ) ≠ 0 := by exact_mod_cast factorial_ne_zero _
  apply mul_left_cancel₀ hk
  rw [h, hrod, h2]
  calc (-1) ^ k * ((k ! : ℝ) * ((-1) ^ k * ((2 * k).choose k : ℝ))) *
        (k ! * k ! / ((2 * k + 1) * (2 * k)!))
      = ((-1) ^ k * (-1) ^ k) * ((k ! : ℝ) * ((2 * k).choose k * k ! * k ! /
        ((2 * k + 1) * (2 * k)!))) := by ring
    _ = k ! * (1 / (2 * k + 1)) := by
      rw [h1, one_mul, hc]
      field_simp

/-- **Orthogonality** of the shifted Legendre polynomials: `∫₀¹ P_j P_k = δ_{jk} / (2k + 1)`. -/
theorem ip_leg_leg (j k : ℕ) :
    ip (leg j) (leg k) = if j = k then (1 / (2 * k + 1) : ℝ) else 0 := by
  split_ifs with h
  · rw [h, ip_leg_self]
  · rcases lt_or_gt_of_ne h with h | h
    · exact ip_leg_eq_zero _ (by rwa [natDegree_leg])
    · rw [ip_comm]
      exact ip_leg_eq_zero _ (by rwa [natDegree_leg])

end BHJK25.Spectral.LegendreAux
