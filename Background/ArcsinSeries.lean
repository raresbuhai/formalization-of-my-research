module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.RingTheory.Binomial

/-!
# The power series of `arcsin`

For `|x| < 1`, `arcsin x = ∑ₙ cₙ x^(2n+1)` with `cₙ = bₙ / (2n + 1)` and `bₙ = C(2n, n) / 4ⁿ`, the
coefficients of `(1 - y)^(-1/2)` (`ArcsinSeries.hasSum_arcsin`). The coefficients are positive,
at most `1`, and `bₙ ≥ 1 / (2 √n)` for `n ≥ 1` (`ArcsinSeries.b_ge`), so `cₙ ≳ n^(-3/2)`.

The coefficients `bₙ` are Mathlib's binomial coefficients `choose (n - 1/2) n`, from the binomial
series of `(1 - y)^(-1/2)` (`Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero`). The series of
`arcsin` follows by differentiating termwise: its derivative is `(1 - x²)^(-1/2) = arcsin' x`.
-/

@[expose] public section

namespace ArcsinSeries

open Real Set Filter Topology Polynomial

/-- `bₙ = C(2n, n) / 4ⁿ`, the coefficients of `(1 - y)^(-1/2)`, as `choose (n - 1/2) n`. -/
noncomputable def b (n : ℕ) : ℝ := Ring.choose ((1 / 2 : ℝ) + n - 1) n

/-- `cₙ = bₙ / (2n + 1)`, the coefficients of `arcsin`. -/
noncomputable def c (n : ℕ) : ℝ := b n / (2 * n + 1)

theorem b_eq (n : ℕ) : b n = (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / n.factorial := by
  rw [b, Ring.choose_eq_smul, descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval, show (1 / 2 : ℝ) + n - 1 - n + 1 = 1 / 2 by ring, smul_eq_mul]
  have := Nat.factorial_pos n
  field_simp

theorem b_zero : b 0 = 1 := by simp [b_eq]

theorem b_succ (n : ℕ) : b (n + 1) = b n * ((n + 1 / 2) / (n + 1)) := by
  rw [b_eq, b_eq, ascPochhammer_succ_eval, Nat.factorial_succ]
  have := Nat.factorial_pos n
  push_cast
  field_simp
  ring

theorem b_pos (n : ℕ) : 0 < b n := by
  induction n with
  | zero => rw [b_zero]; norm_num
  | succ n ih => rw [b_succ]; positivity

theorem b_le_one (n : ℕ) : b n ≤ 1 := by
  induction n with
  | zero => rw [b_zero]
  | succ n ih =>
    rw [b_succ]
    have h : (n + 1 / 2 : ℝ) / (n + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have := b_pos n
    calc b n * ((n + 1 / 2) / (n + 1)) ≤ 1 * 1 :=
          mul_le_mul ih h (by positivity) zero_le_one
      _ = 1 := one_mul 1

/-- **`C(2n, n) / 4ⁿ ≥ 1 / (2 √n)`** for `n ≥ 1`. -/
theorem b_ge {n : ℕ} (hn : 1 ≤ n) : 1 / (2 * √n) ≤ b n := by
  induction n, hn using Nat.le_induction with
  | base => rw [b_succ, b_zero]; norm_num
  | succ n hn ih =>
    rw [b_succ]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
    -- `(n + 1) √n ≤ (n + 1/2) √(n + 1)`, by comparing squares.
    have key : ((n : ℝ) + 1) * √n ≤ (n + 1 / 2) * √((n : ℝ) + 1) := by
      have h1 : ((n : ℝ) + 1) * √n = √(((n : ℝ) + 1) ^ 2 * n) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have h2 : ((n : ℝ) + 1 / 2) * √((n : ℝ) + 1) = √(((n : ℝ) + 1 / 2) ^ 2 * (n + 1)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      rw [h1, h2]
      exact Real.sqrt_le_sqrt (by nlinarith)
    have hs1 : 0 < √((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    push_cast
    calc 1 / (2 * √((n : ℝ) + 1)) ≤ 1 / (2 * √n) * ((n + 1 / 2) / (n + 1)) := by
          rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ ≤ b n * ((n + 1 / 2) / (n + 1)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)

theorem c_nonneg (n : ℕ) : 0 ≤ c n := div_nonneg (b_pos n).le (by positivity)

theorem c_le_one (n : ℕ) : c n ≤ 1 := by
  rw [c, div_le_one (by positivity)]
  have := b_le_one n
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **`(1 - y)^(-1/2) = ∑ bₙ yⁿ`** for `|y| < 1`. -/
theorem hasSum_b {y : ℝ} (hy : |y| < 1) : HasSum (fun n ↦ b n * y ^ n) (1 / √(1 - y)) := by
  have h := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2)
  have hy' : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, enorm_eq_nnnorm]
    exact_mod_cast (show ‖y‖₊ < 1 from by rw [← NNReal.coe_lt_coe]; simpa using hy)
  have := h.hasSum hy'
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at this
  rw [Real.sqrt_eq_rpow]
  exact this

/-- **The power series of `arcsin`**: `arcsin x = ∑ cₙ x^(2n+1)` for `|x| < 1`. -/
theorem hasSum_arcsin {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n ↦ c n * x ^ (2 * n + 1)) (arcsin x) := by
  obtain ⟨r, hxr, hr1⟩ := exists_between hx
  have hr0 : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  set t := Ioo (-r) r with htdef
  have ht : IsOpen t := isOpen_Ioo
  have hxt : x ∈ t := ⟨by linarith [neg_abs_le x], lt_of_le_of_lt (le_abs_self x) hxr⟩
  have h0t : (0 : ℝ) ∈ t := ⟨by linarith, hr0⟩
  -- The terms, their derivatives, and a summable bound on `t`.
  have hderiv : ∀ n (z : ℝ), HasDerivAt (fun z ↦ c n * z ^ (2 * n + 1)) (b n * z ^ (2 * n)) z := by
    intro n z
    have := ((hasDerivAt_pow (2 * n + 1) z).const_mul (c n))
    convert this using 1
    rw [c, Nat.add_sub_cancel]
    push_cast
    field_simp
  have hbound : ∀ n (z : ℝ), z ∈ t → ‖b n * z ^ (2 * n)‖ ≤ (r ^ 2) ^ n := by
    intro n z hz
    have hz' : |z| ≤ r := abs_le.2 ⟨hz.1.le, hz.2.le⟩
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (b_pos n), abs_pow, pow_mul]
    calc b n * (|z| ^ 2) ^ n ≤ 1 * (r ^ 2) ^ n := mul_le_mul (b_le_one n)
          (pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg z) hz' 2) n)
          (by positivity) zero_le_one
      _ = (r ^ 2) ^ n := one_mul _
  have hsum : Summable fun n : ℕ ↦ (r ^ 2) ^ n :=
    summable_geometric_of_lt_one (by positivity) (by nlinarith)
  -- The series `S` has derivative `(1 - z²)^(-1/2)` on `t`, like `arcsin`.
  set S : ℝ → ℝ := fun z ↦ ∑' n, c n * z ^ (2 * n + 1) with hS
  have hSderiv : ∀ z ∈ t, HasDerivAt S (1 / √(1 - z ^ 2)) z := by
    intro z hz
    have h := hasDerivAt_tsum_of_isPreconnected hsum ht isPreconnected_Ioo
      (fun n z _ ↦ hderiv n z) hbound h0t (by simp) hz
    have hz2 : |z ^ 2| < 1 := by
      rw [abs_pow]
      have : |z| < 1 := lt_of_le_of_lt (abs_le.2 ⟨hz.1.le, hz.2.le⟩) hr1
      nlinarith [abs_nonneg z]
    have := (hasSum_b hz2).tsum_eq
    simp_rw [← pow_mul] at this
    rw [this] at h
    exact h
  have hAderiv : ∀ z ∈ t, HasDerivAt arcsin (1 / √(1 - z ^ 2)) z := by
    intro z hz
    have : |z| < 1 := lt_of_le_of_lt (abs_le.2 ⟨hz.1.le, hz.2.le⟩) hr1
    exact hasDerivAt_arcsin (by intro h; rw [h] at this; norm_num at this)
      (by intro h; rw [h] at this; norm_num at this)
  -- `S - arcsin` is constant on `t`, and vanishes at `0`.
  have hd : ∀ z ∈ t, HasDerivAt (fun z ↦ S z - arcsin z)
      (1 / √(1 - z ^ 2) - 1 / √(1 - z ^ 2)) z := fun z hz ↦ (hSderiv z hz).sub (hAderiv z hz)
  have hx0 := ht.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (f := fun z ↦ S z - arcsin z)
    (fun z hz ↦ (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz ↦ by rw [(hd z hz).deriv, sub_self]; rfl) hxt h0t
  simp only [hS, arcsin_zero, sub_zero] at hx0
  have hS0 : ∑' n : ℕ, c n * (0 : ℝ) ^ (2 * n + 1) = 0 := by simp
  rw [hS0, sub_eq_zero] at hx0
  -- Summability at `x`.
  have hsx : Summable fun n ↦ c n * x ^ (2 * n + 1) := by
    refine Summable.of_norm_bounded (g := fun n : ℕ ↦ (r ^ 2) ^ n) hsum fun n ↦ ?_
    have hx' : |x| ≤ r := hxr.le
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (c_nonneg n), abs_pow,
      pow_succ, pow_mul]
    have h1 : |x| ≤ 1 := hx.le
    calc c n * ((|x| ^ 2) ^ n * |x|) ≤ 1 * ((r ^ 2) ^ n * 1) := by
          gcongr
          · exact c_le_one n
      _ = (r ^ 2) ^ n := by ring
  rw [← hx0]
  exact hsx.hasSum

end ArcsinSeries
