module

public import BHJK25.Spectral.Legendre.Orthogonal

/-!
# Expansion in shifted Legendre polynomials

Every real polynomial `q` of degree at most `d` is a combination `∑_{k ≤ d} a_k P_k` of the shifted
Legendre polynomials, and `∫₀¹ q² = ∑_k a_k² / (2k + 1)` (Parseval). Since `P_k(0) = 1` and
`0 ≤ P_k(-t) - 1 ≤ 2k(k + 1)t` when `k(k + 1)t ≤ 1/2`, the Cauchy–Schwarz inequality gives
`|q(-t) - q(0)| ≤ 10 d³ t (∫₀¹ q²)^(1/2)` for `0 ≤ t ≤ 1 / (2d(d + 1))`.
-/

@[expose] public section

namespace BHJK25.Spectral.LegendreAux

open Polynomial Nat Finset

theorem leg_zero : leg 0 = 1 := by
  simp [leg, shiftedLegendre]

theorem coeff_leg_self_ne_zero (k : ℕ) : (leg k).coeff k ≠ 0 := by
  rw [coeff_leg, choose_self, cast_one, mul_one]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast (choose_pos (by lia)).ne')

/-- The shifted Legendre polynomials `P_0, …, P_d` span the polynomials of degree at most `d`. -/
theorem exists_leg_expansion {d : ℕ} (q : ℝ[X]) (hq : q.natDegree ≤ d) :
    ∃ a : ℕ → ℝ, q = ∑ k ∈ range (d + 1), C (a k) * leg k := by
  induction d generalizing q with
  | zero =>
    refine ⟨fun _ ↦ q.coeff 0, ?_⟩
    rw [sum_range_one, leg_zero, mul_one]
    exact eq_C_of_natDegree_le_zero hq
  | succ d ih =>
    set c := q.coeff (d + 1) / (leg (d + 1)).coeff (d + 1) with hc
    have hr : (q - C c * leg (d + 1)).natDegree ≤ d := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul]
      rcases (succ_le_of_lt hN).eq_or_lt with h | h
      · rw [← h, hc, div_mul_cancel₀ _ (coeff_leg_self_ne_zero _), sub_self]
      · rw [coeff_eq_zero_of_natDegree_lt (hq.trans_lt h),
          coeff_eq_zero_of_natDegree_lt ((natDegree_leg _).trans_lt h), mul_zero, sub_zero]
    obtain ⟨a, ha⟩ := ih _ hr
    refine ⟨Function.update a (d + 1) c, ?_⟩
    rw [sum_range_succ, Function.update_self]
    have hs : ∑ k ∈ range (d + 1), C (Function.update a (d + 1) c k) * leg k =
        ∑ k ∈ range (d + 1), C (a k) * leg k :=
      sum_congr rfl fun k hk ↦ by
        rw [Function.update_of_ne (by simp at hk; lia)]
    rw [hs, ← ha]
    ring

/-- The inner product of `P_j` with a combination of `P_0, …, P_d`, for `j ≤ d`. -/
theorem ip_leg_expansion {d j : ℕ} (a : ℕ → ℝ) (hj : j ≤ d) :
    ip (leg j) (∑ k ∈ range (d + 1), C (a k) * leg k) = a j / (2 * j + 1) := by
  rw [ip_sum_right]
  simp_rw [ip_leg_leg, mul_ite, mul_zero]
  have hjm : j ∈ range (d + 1) := mem_range.mpr (by lia)
  rw [sum_ite_eq]
  simp only [hjm, ↓reduceIte]
  ring

/-- **Parseval's identity** for an expansion in shifted Legendre polynomials. -/
theorem ip_self_expansion {d : ℕ} (a : ℕ → ℝ) :
    ip (∑ k ∈ range (d + 1), C (a k) * leg k) (∑ k ∈ range (d + 1), C (a k) * leg k) =
      ∑ k ∈ range (d + 1), a k ^ 2 / (2 * k + 1) := by
  rw [ip_sum_right]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [ip_comm, ip_leg_expansion a (by simp at hk; lia)]
  ring

theorem eval_leg_zero (k : ℕ) : (leg k).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_leg]
  simp

theorem eval_leg_neg (k : ℕ) (t : ℝ) :
    (leg k).eval (-t) = ∑ i ∈ range (k + 1), (k.choose i * (k + i).choose k : ℝ) * t ^ i := by
  rw [eval_eq_sum_range' (n := k + 1) (by rw [natDegree_leg]; lia)]
  refine sum_congr rfl fun i _ ↦ ?_
  have h : ((-1 : ℝ) ^ i) * (-1) ^ i = 1 := by
    rw [← mul_pow]
    norm_num
  rw [coeff_leg, neg_pow]
  linear_combination (k.choose i * (k + i).choose k * t ^ i : ℝ) * h

/-- `C(k, i) C(k + i, k) ≤ (k (k + 1))^i`. -/
theorem choose_mul_choose_le (k i : ℕ) :
    (k.choose i * (k + i).choose k : ℝ) ≤ (k * (k + 1)) ^ i := by
  rw [mul_pow]
  have h1 : (k.choose i : ℝ) ≤ (k : ℝ) ^ i := by exact_mod_cast choose_le_pow k i
  have h2 : ((k + i).choose k : ℝ) ≤ ((k : ℝ) + 1) ^ i := by
    rw [choose_symm_add]
    exact_mod_cast choose_add_le_add_one_pow k i
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/-- `∑_{i < n} x^(i+1) ≤ 2x` for `0 ≤ x ≤ 1/2`. -/
theorem sum_pow_succ_le {x : ℝ} (hx0 : 0 ≤ x) (hx : 2 * x ≤ 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ (i + 1) ≤ 2 * x := by
  induction n with
  | zero => simp [hx0]
  | succ n ih =>
    rw [sum_range_succ', zero_add, pow_one]
    have h : ∑ i ∈ range n, x ^ (i + 1 + 1) = x * ∑ i ∈ range n, x ^ (i + 1) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [h]
    nlinarith

/-- `0 ≤ P_k(-t) - 1 ≤ 2k(k + 1)t` for `0 ≤ t` and `2k(k + 1)t ≤ 1`. -/
theorem eval_leg_neg_sub_one {k : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : 2 * (k * (k + 1) * t) ≤ 1) :
    0 ≤ (leg k).eval (-t) - 1 ∧ (leg k).eval (-t) - 1 ≤ 2 * (k * (k + 1) * t) := by
  have h : (leg k).eval (-t) - 1 =
      ∑ i ∈ range k, (k.choose (i + 1) * (k + (i + 1)).choose k : ℝ) * t ^ (i + 1) := by
    rw [eval_leg_neg, sum_range_succ']
    simp
  rw [h]
  constructor
  · exact sum_nonneg fun i _ ↦ by positivity
  · calc ∑ i ∈ range k, (k.choose (i + 1) * (k + (i + 1)).choose k : ℝ) * t ^ (i + 1)
        ≤ ∑ i ∈ range k, (k * (k + 1) * t : ℝ) ^ (i + 1) := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [mul_pow _ t]
          exact mul_le_mul_of_nonneg_right (choose_mul_choose_le k (i + 1)) (by positivity)
      _ ≤ 2 * (k * (k + 1) * t) := sum_pow_succ_le (by positivity) ht k

/-- `∑_{k ≤ d} (2k + 1) (2k(k + 1))² ≤ 100 d⁶`. -/
theorem sum_weights_le (d : ℕ) :
    ∑ k ∈ range (d + 1), (2 * k + 1 : ℝ) * (2 * (k * (k + 1))) ^ 2 ≤ 100 * (d : ℝ) ^ 6 := by
  have hterm : ∀ k ∈ range (d + 1),
      (2 * k + 1 : ℝ) * (2 * (k * (k + 1))) ^ 2 ≤ (2 * d + 1) * (2 * (d * (d + 1))) ^ 2 :=
    fun k hk ↦ by
      have hkd : (k : ℝ) ≤ d := by exact_mod_cast (by simp at hk; lia : k ≤ d)
      have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
      have h1 : (2 * k + 1 : ℝ) ≤ 2 * d + 1 := by linarith
      have h2 : (2 * (k * (k + 1)) : ℝ) ≤ 2 * (d * (d + 1)) := by
        have := mul_le_mul hkd (by linarith : (k : ℝ) + 1 ≤ d + 1) (by linarith) (by linarith)
        linarith
      exact mul_le_mul h1 (pow_le_pow_left₀ (by positivity) h2 2) (by positivity) (by positivity)
  refine (sum_le_sum hterm).trans ?_
  rw [sum_const, card_range, nsmul_eq_mul]
  push_cast
  rcases d.eq_zero_or_pos with rfl | hd
  · norm_num
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    set x : ℝ := (d : ℝ)
    have hx0 : 0 ≤ x := by linarith
    calc (x + 1) * ((2 * x + 1) * (2 * (x * (x + 1))) ^ 2)
        = 4 * x ^ 2 * ((x + 1) ^ 3 * (2 * x + 1)) := by ring
      _ ≤ 4 * x ^ 2 * ((2 * x) ^ 3 * (3 * x)) := by
          gcongr
          · linarith
          · linarith
      _ = 96 * x ^ 6 := by ring
      _ ≤ 100 * x ^ 6 := by nlinarith [pow_nonneg hx0 6]

/-- For a polynomial `q` of degree at most `d` and `0 ≤ t ≤ 1 / (2d(d + 1))`,
`|q(-t) - q(0)| ≤ 10 d³ t (∫₀¹ q²)^(1/2)`. -/
theorem abs_eval_neg_sub_eval_zero_le {d : ℕ} (q : ℝ[X]) (hq : q.natDegree ≤ d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t * (2 * d * (d + 1)) ≤ 1) :
    |q.eval (-t) - q.eval 0| ≤ 10 * d ^ 3 * t * √(ip q q) := by
  obtain ⟨a, ha⟩ := exists_leg_expansion q hq
  set e : ℕ → ℝ := fun k ↦ (leg k).eval (-t) - 1 with he_def
  have hdiff : q.eval (-t) - q.eval 0 = ∑ k ∈ range (d + 1), a k * e k := by
    rw [ha, eval_finsetSum, eval_finsetSum, ← sum_sub_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [eval_mul, eval_C, eval_leg_zero, he_def]
    ring
  have hnorm : ip q q = ∑ k ∈ range (d + 1), a k ^ 2 / (2 * k + 1) := by
    rw [ha, ip_self_expansion]
  have he : ∀ k ∈ range (d + 1), 0 ≤ e k ∧ e k ≤ 2 * (k * (k + 1) * t) := fun k hk ↦ by
    have hkd : (k : ℝ) ≤ d := by exact_mod_cast (by simp at hk; lia : k ≤ d)
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have hkk : (k : ℝ) * (k + 1) ≤ d * (d + 1) :=
      mul_le_mul hkd (by linarith) (by linarith) (by linarith)
    refine eval_leg_neg_sub_one ht0 ?_
    nlinarith
  have hCS : (∑ k ∈ range (d + 1), a k * e k) ^ 2 ≤
      (∑ k ∈ range (d + 1), a k ^ 2 / (2 * k + 1)) *
        ∑ k ∈ range (d + 1), (2 * k + 1) * e k ^ 2 := by
    refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ ↦ by positivity)
      (fun k _ ↦ by positivity) fun k _ ↦ le_of_eq ?_
    have : (2 * k + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  have hw : ∑ k ∈ range (d + 1), (2 * k + 1) * e k ^ 2 ≤ (10 * d ^ 3 * t) ^ 2 := by
    calc ∑ k ∈ range (d + 1), (2 * k + 1) * e k ^ 2
        ≤ ∑ k ∈ range (d + 1), (2 * k + 1 : ℝ) * (2 * (k * (k + 1))) ^ 2 * t ^ 2 :=
          sum_le_sum fun k hk ↦ by
            have h := he k hk
            have h2 : e k ^ 2 ≤ (2 * (k * (k + 1) * t)) ^ 2 := pow_le_pow_left₀ h.1 h.2 2
            calc (2 * k + 1 : ℝ) * e k ^ 2 ≤ (2 * k + 1) * (2 * (k * (k + 1) * t)) ^ 2 :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = _ := by ring
      _ = (∑ k ∈ range (d + 1), (2 * k + 1 : ℝ) * (2 * (k * (k + 1))) ^ 2) * t ^ 2 := by
          rw [sum_mul]
      _ ≤ 100 * (d : ℝ) ^ 6 * t ^ 2 :=
          mul_le_mul_of_nonneg_right (sum_weights_le d) (by positivity)
      _ = (10 * d ^ 3 * t) ^ 2 := by ring
  rw [hdiff, ← Real.sqrt_sq_eq_abs, hnorm, mul_comm _ (√_)]
  calc √((∑ k ∈ range (d + 1), a k * e k) ^ 2)
      ≤ √((∑ k ∈ range (d + 1), a k ^ 2 / (2 * k + 1)) * (10 * d ^ 3 * t) ^ 2) := by
        refine Real.sqrt_le_sqrt (hCS.trans ?_)
        exact mul_le_mul_of_nonneg_left hw (sum_nonneg fun k _ ↦ by positivity)
    _ = √(∑ k ∈ range (d + 1), a k ^ 2 / (2 * k + 1)) * (10 * d ^ 3 * t) := by
        rw [Real.sqrt_mul (sum_nonneg fun k _ ↦ by positivity), Real.sqrt_sq (by positivity)]

end BHJK25.Spectral.LegendreAux
