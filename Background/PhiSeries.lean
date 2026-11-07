module

public import Background.GaussianCoins
public import Background.GaussianCalculus
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The series of the Gaussian distribution function

`Φ(x) = 1/2 + T(x) / √(2π)` with `T(x) = ∑ₘ (-1)ᵐ x^(2m+1) / (2ᵐ m! (2m+1))`, the integral of
`e^(-t²/2)` from `0` (`Gaussian.Phi_eq`): `T` has derivative `e^(-x²/2)` term by term, as `Φ` has
derivative the Gaussian density. Truncating after `N ≥ 3x²` terms costs at most
`2 |x| (x²/2)^N / N! ≤ 2 |x| 2^-N` (`Gaussian.abs_phiSum_sub_le`), so `Φ` is computable to any
precision from rational arithmetic and an approximation of `π`.
-/

@[expose] public section

namespace Gaussian

open Real Set Filter Topology Nat ProbabilityTheory MeasureTheory

/-- The terms `(-1)ᵐ x^(2m+1) / (2ᵐ m! (2m+1))` of `T(x) = ∫₀ˣ e^(-t²/2) dt`. -/
noncomputable def phiTerm (x : ℝ) (m : ℕ) : ℝ :=
  (-1) ^ m * x ^ (2 * m + 1) / (2 ^ m * (m ! : ℝ) * (2 * m + 1))

/-- `T(x) = ∑ₘ phiTerm x m`. -/
noncomputable def phiSum (x : ℝ) : ℝ := ∑' m, phiTerm x m

theorem hasSum_exp_neg_sq (x : ℝ) :
    HasSum (fun m : ℕ ↦ (-1) ^ m * x ^ (2 * m) / (2 ^ m * (m ! : ℝ))) (rexp (-x ^ 2 / 2)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-x ^ 2 / 2)
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext m
  have : (-x ^ 2 / 2) ^ m = (-1) ^ m * x ^ (2 * m) / 2 ^ m := by
    rw [div_pow, neg_pow, ← pow_mul, mul_comm 2 m]
  rw [this]
  field_simp

theorem hasDerivAt_phiTerm (m : ℕ) (x : ℝ) :
    HasDerivAt (fun x ↦ phiTerm x m) ((-1) ^ m * x ^ (2 * m) / (2 ^ m * (m ! : ℝ))) x := by
  have h := ((hasDerivAt_pow (2 * m + 1) x).const_mul ((-1) ^ m)).div_const
    (2 ^ m * (m ! : ℝ) * (2 * m + 1))
  unfold phiTerm
  convert h using 1
  have : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have : ((m ! : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp

theorem abs_phiTerm_le (x : ℝ) (m : ℕ) :
    |phiTerm x m| ≤ |x| * ((x ^ 2 / 2) ^ m / (m ! : ℝ)) := by
  unfold phiTerm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m * (m ! : ℝ) * (2 * m + 1)), abs_pow,
    div_le_iff₀ (by positivity)]
  have h1 : |x| ^ (2 * m + 1) = |x| * (x ^ 2) ^ m := by
    rw [pow_succ, pow_mul, sq_abs, mul_comm]
  rw [h1, div_pow]
  have hm : (1 : ℝ) ≤ 2 * m + 1 := by have := (m.cast_nonneg : (0 : ℝ) ≤ m); linarith
  have hpos : 0 ≤ |x| * (x ^ 2) ^ m := by positivity
  calc |x| * (x ^ 2) ^ m = |x| * ((x ^ 2) ^ m / 2 ^ m / (m ! : ℝ)) * (2 ^ m * (m ! : ℝ) * 1) := by
        field_simp
    _ ≤ |x| * ((x ^ 2) ^ m / 2 ^ m / (m ! : ℝ)) * (2 ^ m * (m ! : ℝ) * (2 * m + 1)) := by
        gcongr

theorem summable_phiTerm (x : ℝ) : Summable (phiTerm x) :=
  Summable.of_norm_bounded ((Real.summable_pow_div_factorial (x ^ 2 / 2)).mul_left |x|)
    fun m ↦ by rw [Real.norm_eq_abs]; exact abs_phiTerm_le x m

/-- `T' = e^(-x²/2)`, term by term. -/
theorem hasDerivAt_phiSum (x : ℝ) : HasDerivAt phiSum (rexp (-x ^ 2 / 2)) x := by
  set R := |x| + 1
  have hR : 0 < R := by positivity
  have hbound : ∀ m (y : ℝ), y ∈ Ioo (-R) R →
      ‖(-1) ^ m * y ^ (2 * m) / (2 ^ m * (m ! : ℝ))‖ ≤ (R ^ 2 / 2) ^ m / (m ! : ℝ) := by
    intro m y hy
    have hy' : |y| ≤ R := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ m * (m ! : ℝ)), pow_mul, div_pow,
      div_div]
    gcongr
    have hy2 : y ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (sq_nonneg y) hy2 m
  have h := hasDerivAt_tsum_of_isPreconnected (Real.summable_pow_div_factorial (R ^ 2 / 2))
    isOpen_Ioo isPreconnected_Ioo (fun m y _ ↦ hasDerivAt_phiTerm m y) hbound
    (y₀ := 0) ⟨by linarith, hR⟩ (summable_phiTerm 0)
    (show x ∈ Ioo (-R) R from ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩)
  rw [(hasSum_exp_neg_sq x).tsum_eq] at h
  exact h

theorem phiSum_zero : phiSum 0 = 0 := by
  simp [phiSum, phiTerm]

/-- **`Φ(x) = 1/2 + T(x) / √(2π)`**. -/
theorem Phi_eq (x : ℝ) : Phi x = 1 / 2 + phiSum x / √(2 * π) := by
  have hd : ∀ y, HasDerivAt (fun y ↦ Phi y - phiSum y / √(2 * π)) 0 y := by
    intro y
    have h1 : HasDerivAt Phi (gaussianPDFReal 0 1 y) y :=
      TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero y
    have h2 := (hasDerivAt_phiSum y).div_const (√(2 * π))
    have h3 := h1.sub h2
    rw [show gaussianPDFReal 0 1 y = rexp (-y ^ 2 / 2) / √(2 * π) by
      simp [gaussianPDFReal, div_eq_inv_mul], sub_self] at h3
    exact h3
  have hc := is_const_of_deriv_eq_zero (f := fun y ↦ Phi y - phiSum y / √(2 * π))
    (fun y ↦ (hd y).differentiableAt) (fun y ↦ (hd y).deriv) x 0
  simp only [phiSum_zero, zero_div, sub_zero] at hc
  have h0 : Phi 0 = 1 / 2 := TauCeti.Probability.cdf_gaussianReal_self 0 one_ne_zero
  linarith

/-- `N^N / N! ≤ e^N`. -/
theorem pow_div_factorial_le_exp (y : ℝ) (hy : 0 ≤ y) (N : ℕ) : y ^ N / (N ! : ℝ) ≤ rexp y := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) y
  rw [← Real.exp_eq_exp_ℝ] at h
  exact le_hasSum h N fun j _ ↦ by positivity

/-- `y^N / N! ≤ 2^-N` once `N ≥ 6 y`. -/
theorem pow_div_factorial_le {y : ℝ} (hy : 0 ≤ y) {N : ℕ} (hN : 6 * y ≤ N) :
    y ^ N / (N ! : ℝ) ≤ (1 / 2) ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · simp
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have h := pow_div_factorial_le_exp N hN'.le N
  have he : rexp N ≤ 3 ^ N := by
    rw [← Real.exp_one_rpow, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le N
  have hyN : y / N ≤ 1 / 6 := by rw [div_le_iff₀ hN']; linarith
  calc y ^ N / (N ! : ℝ) = (y / N) ^ N * ((N : ℝ) ^ N / (N ! : ℝ)) := by
        rw [div_pow]; field_simp
    _ ≤ (1 / 6) ^ N * 3 ^ N := by
        gcongr
        exact h.trans he
    _ = (1 / 2) ^ N := by rw [← mul_pow]; norm_num

/-- **Truncating the series of `Φ`**: for `N ≥ 3 x²`, the first `N` terms are within
`2 |x| 2^-N` of `T(x)`. -/
theorem abs_phiSum_sub_le (x : ℝ) {N : ℕ} (hN : 3 * x ^ 2 ≤ N) :
    |phiSum x - ∑ m ∈ Finset.range N, phiTerm x m| ≤ 2 * |x| * (1 / 2) ^ N := by
  set y := x ^ 2 / 2 with hydef
  have hy : 0 ≤ y := by positivity
  have hyN : y ≤ (N + 1) / 2 := by rw [hydef]; nlinarith
  rw [phiSum, ← (summable_phiTerm x).sum_add_tsum_nat_add N, add_sub_cancel_left]
  -- `y^(N+j)/(N+j)! ≤ y^N/N! 2^-j`.
  have hratio : ∀ j : ℕ, y ^ (j + N) / ((j + N)! : ℝ) ≤ y ^ N / (N ! : ℝ) * (1 / 2) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hq : y / ((j + N + 1 : ℕ) : ℝ) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        push_cast
        nlinarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
      have key : y ^ (j + 1 + N) / ((j + 1 + N)! : ℝ) =
          y ^ (j + N) / ((j + N)! : ℝ) * (y / ((j + N + 1 : ℕ) : ℝ)) := by
        rw [show j + 1 + N = (j + N) + 1 by ring, pow_succ, Nat.factorial_succ]
        push_cast
        field_simp
      rw [key, pow_succ, ← mul_assoc]
      exact mul_le_mul ih hq (by positivity) (by positivity)
  have hterm : ∀ j : ℕ, |phiTerm x (j + N)| ≤ |x| * (y ^ N / (N ! : ℝ)) * (1 / 2) ^ j := by
    intro j
    refine (abs_phiTerm_le x (j + N)).trans ?_
    rw [← hydef, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hratio j) (abs_nonneg x)
  have hsum : Summable fun j : ℕ ↦ |x| * (y ^ N / (N ! : ℝ)) * (1 / 2) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hfac : y ^ N / (N ! : ℝ) ≤ (1 / 2) ^ N :=
    pow_div_factorial_le hy (by rw [hydef]; nlinarith)
  calc |∑' j, phiTerm x (j + N)| ≤ ∑' j, |x| * (y ^ N / (N ! : ℝ)) * (1 / 2) ^ j := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hsum.hasSum fun j ↦ by rw [Real.norm_eq_abs]; exact hterm j
    _ = 2 * |x| * (y ^ N / (N ! : ℝ)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        ring
    _ ≤ 2 * |x| * (1 / 2) ^ N := by gcongr

/-- **The smoothed sign through `Φ`**: `s_a(t) = 2 Φ(a t / √(1 - a²)) - 1` for `0 ≤ a < 1`. -/
theorem smoothSign_eq_Phi {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (t : ℝ) :
    smoothSign a t = 2 * Phi (a * t / √(1 - a ^ 2)) - 1 := by
  set σ := √(1 - a ^ 2) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by nlinarith)
  -- `sgn(a t + σ z) = 2 [z ≥ -a t/σ] - 1`.
  set c := -(a * t / σ) with hcdef
  have hpt : ∀ z : ℝ, sgn (a * t + σ * z) = 2 * (Set.Ici c).indicator 1 z - 1 := by
    intro z
    have : 0 ≤ a * t + σ * z ↔ c ≤ z := by
      rw [hcdef, neg_le, show -z = -(σ * z) / σ by field_simp, div_le_div_iff_of_pos_right hσ]
      constructor <;> intro h <;> linarith
    by_cases h : c ≤ z
    · simp [sgn, this.2 h, Set.indicator, h]; norm_num
    · simp [sgn, show ¬ 0 ≤ a * t + σ * z from fun h' ↦ h (this.1 h'), Set.indicator, h]
  unfold smoothSign
  simp_rw [← hσdef, hpt]
  have hI : Integrable (fun z ↦ 2 * (Ici c).indicator (1 : ℝ → ℝ) z) (gaussianReal 0 1) :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ici).const_mul 2
  rw [integral_sub hI (integrable_const 1), integral_const_mul,
    integral_indicator_one measurableSet_Ici,
    integral_const, probReal_univ, one_smul]
  -- `P(Z ≥ c) = 1 - Φ(c) = Φ(-c)`.
  have hcompl : (gaussianReal 0 1).real (Set.Ici c) = 1 - Phi c := by
    rw [← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
      measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real]
    rfl
  have hsym : Phi (-c) = 1 - Phi c := by
    rw [Phi, Phi, TauCeti.Probability.cdf_gaussianReal_zero_one,
      TauCeti.Probability.cdf_gaussianReal_zero_one, neg_div, TauCeti.Real.erf_neg]
    ring
  rw [hcompl, ← hsym, hcdef, neg_neg]

end Gaussian
