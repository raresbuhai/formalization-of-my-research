module

public import BGHKLMM26.RobustMIS.Defs
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# One-dimensional Gaussian integrals

The standard facts (S6) of `eldan-proof.tex` on `φ = npdf` and `Φ = Gaussian.Phi`, shared by
`Quantile.lean`, `Static1D.lean`, `QBath.lean` and `Gamma.lean`.

Material: Mathlib's `gaussianReal`, `gaussianPDFReal`, `integral_gaussianReal_eq_integral_smul`,
`integral_Ioi_of_hasDerivAt_of_tendsto'`; TauCeti's `cdf_gaussianReal_zero_one`,
`hasDerivAt_cdf_gaussianReal`, `integral_Iic_gaussianPDFReal`; the moment computations follow
OpenAI's `GaussianPropeller/OneCell.lean` (`tail_first_moment`, `tail_second_moment`;
Apache-2.0, openai/math 4eaee87).

Auxiliary facts in `BGHKLMM26.RobustMIS.Normal`: `npdf_eq` (the explicit formula), integrability
of `φ`, `x φ`, `x² φ`, the limits of `φ`, `x φ` at `±∞`, and `∫_a^∞ φ = 1 - Φ(a)`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open Gaussian

theorem npdf_pos (y : ℝ) : 0 < npdf y := gaussianPDFReal_pos _ _ _ one_ne_zero

namespace Normal

theorem npdf_eq (y : ℝ) : npdf y = (√(2 * π))⁻¹ * exp (-y ^ 2 / 2) := by
  simp [gaussianPDFReal]

theorem npdf_nonneg (y : ℝ) : 0 ≤ npdf y := (npdf_pos y).le

theorem integrable_npdf : Integrable npdf := integrable_gaussianPDFReal 0 1

theorem integrable_mul_npdf : Integrable (fun x : ℝ ↦ x * npdf x) := by
  have h := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).const_mul
    (√(2 * π))⁻¹
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [npdf_eq]
  ring_nf

theorem integrable_sq_mul_npdf : Integrable (fun x : ℝ ↦ x ^ 2 * npdf x) := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (-1:ℝ) < 2)).const_mul (√(2 * π))⁻¹
  refine h.congr (ae_of_all _ fun x ↦ ?_)
  simp only [npdf_eq, Real.rpow_two]
  ring_nf

theorem tendsto_npdf_atTop : Tendsto npdf atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ ↦ exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (by norm_num : (-(1/2:ℝ)) < 0) using 1
    ext x
    ring
  rw [show npdf = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) from funext npdf_eq]
  simpa using h.const_mul (√(2 * π))⁻¹

theorem tendsto_npdf_atBot : Tendsto npdf atBot (𝓝 0) := by
  have h : Tendsto (fun x : ℝ ↦ exp (-x ^ 2 / 2)) atBot (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    convert (tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (by norm_num : (-(1/2:ℝ)) < 0) |>.comp tendsto_neg_atBot_atTop using 1
    ext x
    simp only [Function.comp_apply]
    ring
  rw [show npdf = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) from funext npdf_eq]
  simpa using h.const_mul (√(2 * π))⁻¹

theorem tendsto_mul_npdf_atTop : Tendsto (fun x ↦ x * npdf x) atTop (𝓝 0) := by
  -- x e^{-x²/2} ≤ 2 e^{-x²/4} ... use x * exp(-x^2/2) = x * exp(-x^2/4) * exp(-x^2/4)
  have h1 : Tendsto (fun x : ℝ ↦ x * exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have := (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      ((tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num : (0 : ℝ) < 2))
    -- (x²/2) e^{-x²/2} → 0, so x e^{-x²/2} ≤ (x²/2) e^{-x²/2} * 2 / x
    apply squeeze_zero' (eventually_ge_atTop 0 |>.mono fun x hx ↦ by positivity)
      ((eventually_ge_atTop 1).mono fun x hx ↦ ?_) (by simpa using this.const_mul 2)
    show x * rexp (-x ^ 2 / 2) ≤ 2 * (x ^ 2 / 2 * rexp (-(x ^ 2 / 2)))
    have he := (exp_pos (-x ^ 2 / 2)).le
    rw [show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring] at he ⊢
    nlinarith [mul_le_mul_of_nonneg_right (show x ≤ x ^ 2 by nlinarith) he]
  rw [show (fun x ↦ x * npdf x) = fun x ↦ (√(2 * π))⁻¹ * (x * exp (-x ^ 2 / 2)) from
    funext fun x ↦ by rw [npdf_eq]; ring]
  simpa using h1.const_mul (√(2 * π))⁻¹

end Normal

open BGHKLMM26.RobustMIS.Normal

theorem npdf_neg (y : ℝ) : npdf (-y) = npdf y := by
  rw [npdf_eq, npdf_eq, neg_sq]

/-- `φ' = -y φ`. -/
theorem hasDerivAt_npdf (y : ℝ) : HasDerivAt npdf (-y * npdf y) y := by
  rw [show npdf = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) from funext npdf_eq]
  convert ((((hasDerivAt_pow 2 y).neg.div_const 2).exp).const_mul ((√(2 * π))⁻¹)) using 1
  simp only [Pi.neg_apply]
  push_cast
  ring

theorem npdf_le (y : ℝ) : npdf y ≤ (√(2 * π))⁻¹ := by
  rw [npdf_eq]
  exact mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 (by nlinarith [sq_nonneg y]))

/-- `sup |y| φ(y) = φ(1) < 1/4`. -/
theorem abs_mul_npdf_le (y : ℝ) : |y| * npdf y ≤ npdf 1 ∧ npdf 1 < 1 / 4 := by
  constructor
  · rw [npdf_eq, npdf_eq]
    have h1 : |y| ≤ 1 + (y ^ 2 - 1) / 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
    have h2 := add_one_le_exp ((y ^ 2 - 1) / 2)
    have h3 : exp (-y ^ 2 / 2) * exp ((y ^ 2 - 1) / 2) = exp (-1 ^ 2 / 2) := by
      rw [← exp_add]; congr 1; ring
    have h4 : |y| * exp (-y ^ 2 / 2) ≤ exp (-1 ^ 2 / 2) := by
      rw [← h3, mul_comm (exp _)]
      exact mul_le_mul_of_nonneg_right (h1.trans (by linarith)) (exp_pos _).le
    calc |y| * ((√(2 * π))⁻¹ * exp (-y ^ 2 / 2)) = (√(2 * π))⁻¹ * (|y| * exp (-y ^ 2 / 2)) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
  · rw [npdf_eq]
    have hs : (5 / 2 : ℝ) < √(2 * π) := by
      rw [Real.lt_sqrt (by norm_num)]; nlinarith [pi_gt_d2]
    have he : (13 / 8 : ℝ) ≤ exp (1 / 2) := by
      have := quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num); norm_num at this ⊢
      linarith
    have he' : exp (-1 ^ 2 / 2) = (exp (1 / 2))⁻¹ := by
      rw [← exp_neg]; congr 1; ring
    rw [he']
    have h1 : (√(2 * π))⁻¹ < 2 / 5 := by
      rw [inv_lt_comm₀ (by positivity) (by norm_num)]; linarith
    have h2 : (exp (1 / 2))⁻¹ ≤ 8 / 13 := by
      rw [inv_le_comm₀ (exp_pos _) (by norm_num)]; linarith
    calc (√(2 * π))⁻¹ * (exp (1 / 2))⁻¹ < 2 / 5 * (exp (1 / 2))⁻¹ :=
          mul_lt_mul_of_pos_right h1 (by positivity)
      _ ≤ 2 / 5 * (8 / 13) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ < 1 / 4 := by norm_num

/-- `sup y² φ(y) = 2 φ(√2) < 0.294`. -/
theorem sq_mul_npdf_le (y : ℝ) : y ^ 2 * npdf y ≤ 0.294 := by
  rw [npdf_eq]
  -- `t e^{-t} ≤ e^{-1}` with `t = y²/2`
  have h1 : y ^ 2 / 2 ≤ exp (y ^ 2 / 2 - 1) := by linarith [add_one_le_exp (y ^ 2 / 2 - 1)]
  have h2 : y ^ 2 * exp (-y ^ 2 / 2) ≤ 2 * exp (-1) := by
    have h3 : exp (y ^ 2 / 2 - 1) * exp (-y ^ 2 / 2) = exp (-1) := by
      rw [← exp_add]; congr 1; ring
    have := mul_le_mul_of_nonneg_right h1 (exp_pos (-y ^ 2 / 2)).le
    rw [h3] at this
    linarith
  have hs : (2.5066 : ℝ) < √(2 * π) := by
    rw [Real.lt_sqrt (by norm_num)]; nlinarith [pi_gt_d6]
  have he : exp (-1) < 1 / 2.7182818283 := by
    rw [exp_neg, inv_lt_comm₀ (exp_pos _) (by norm_num), one_div, inv_inv]
    exact exp_one_gt_d9
  have h4 : (√(2 * π))⁻¹ < 1 / 2.5066 := by
    rw [one_div, inv_lt_inv₀ (by positivity) (by norm_num)]; exact hs
  calc y ^ 2 * ((√(2 * π))⁻¹ * exp (-y ^ 2 / 2)) = (√(2 * π))⁻¹ * (y ^ 2 * exp (-y ^ 2 / 2)) := by
        ring
    _ ≤ (√(2 * π))⁻¹ * (2 * exp (-1)) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ 1 / 2.5066 * (2 * (1 / 2.7182818283)) := by
        apply mul_le_mul h4.le (by linarith) (by positivity) (by norm_num)
    _ ≤ 0.294 := by norm_num

theorem Phi_zero : Phi 0 = 1 / 2 :=
  TauCeti.Probability.cdf_gaussianReal_self 0 one_ne_zero

theorem Phi_neg (x : ℝ) : Phi (-x) = 1 - Phi x :=
  TauCeti.Probability.cdf_gaussianReal_zero_one_neg x

theorem hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (npdf x) x :=
  TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero x

theorem Phi_eq_integral (x : ℝ) : Phi x = ∫ y in Iic x, npdf y := by
  rw [Phi, TauCeti.Probability.cdf_gaussianReal_eq 0 one_ne_zero,
    TauCeti.Probability.integral_Iic_gaussianPDFReal 0 one_ne_zero]

/-- Integrals against `γ₁` are integrals against the density. -/
theorem integral_gaussianReal_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussianReal 0 1 = ∫ x, npdf x * f x := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  rfl

namespace Normal

theorem integral_Ioi_npdf (a : ℝ) : ∫ x in Ioi a, npdf x = 1 - Phi a := by
  rw [TauCeti.Probability.integral_Ioi_gaussianPDFReal_eq_cdf 0 one_ne_zero]
  simp only [NNReal.coe_one, Real.sqrt_one, div_one, zero_sub]
  exact Phi_neg a

end Normal

/-- `∫_a^∞ x φ(x) dx = φ(a)`. -/
theorem integral_Ici_mul_npdf (a : ℝ) : ∫ x in Ici a, x * npdf x = npdf a := by
  rw [integral_Ici_eq_integral_Ioi]
  have hd (x : ℝ) : HasDerivAt (fun x ↦ -npdf x) (x * npdf x) x := by
    convert (hasDerivAt_npdf x).neg using 1; ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := a) (fun x _ ↦ hd x)
    integrable_mul_npdf.integrableOn tendsto_npdf_atTop.neg
  rw [this]; ring

/-- `∫_{-∞}^c x φ(x) dx = -φ(c)`. -/
theorem integral_Iic_mul_npdf (c : ℝ) : ∫ x in Iic c, x * npdf x = -npdf c := by
  have hd (x : ℝ) : HasDerivAt (fun x ↦ -npdf x) (x * npdf x) x := by
    convert (hasDerivAt_npdf x).neg using 1; ring
  have := integral_Iic_of_hasDerivAt_of_tendsto' (a := c) (fun x _ ↦ hd x)
    integrable_mul_npdf.integrableOn tendsto_npdf_atBot.neg
  rw [this]; ring

/-- `∫_a^∞ (x² - 1) φ(x) dx = a φ(a)`. -/
theorem integral_Ici_sq_sub_one_mul_npdf (a : ℝ) :
    ∫ x in Ici a, (x ^ 2 - 1) * npdf x = a * npdf a := by
  rw [integral_Ici_eq_integral_Ioi]
  have hd (x : ℝ) : HasDerivAt (fun x ↦ -(x * npdf x)) ((x ^ 2 - 1) * npdf x) x := by
    convert ((hasDerivAt_id' x).mul (hasDerivAt_npdf x)).neg using 1; ring
  have hi : Integrable (fun x : ℝ ↦ (x ^ 2 - 1) * npdf x) := by
    refine (integrable_sq_mul_npdf.sub integrable_npdf).congr (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.sub_apply]; ring
  have := integral_Ioi_of_hasDerivAt_of_tendsto' (a := a) (fun x _ ↦ hd x)
    hi.integrableOn tendsto_mul_npdf_atTop.neg
  rw [this]; ring

/-- `∫_a^∞ x² φ(x) dx = a φ(a) + 1 - Φ(a)`. -/
theorem integral_Ici_sq_mul_npdf (a : ℝ) :
    ∫ x in Ici a, x ^ 2 * npdf x = a * npdf a + (1 - Phi a) := by
  have hi : Integrable (fun x : ℝ ↦ (x ^ 2 - 1) * npdf x) := by
    refine (integrable_sq_mul_npdf.sub integrable_npdf).congr (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.sub_apply]; ring
  have h1 := integral_Ici_sq_sub_one_mul_npdf a
  rw [← integral_Ioi_npdf, ← integral_Ici_eq_integral_Ioi, ← h1,
    ← integral_add hi.integrableOn integrable_npdf.integrableOn]
  congr 1; ext x; ring

/-- **Mills**: `1 - Φ(a) ≤ φ(a)/a` for `a > 0`. -/
theorem one_sub_Phi_le {a : ℝ} (ha : 0 < a) : 1 - Phi a ≤ npdf a / a := by
  rw [← integral_Ioi_npdf, ← integral_Ici_mul_npdf, integral_Ici_eq_integral_Ioi,
    ← integral_div]
  refine setIntegral_mono_on integrable_npdf.integrableOn
    (integrable_mul_npdf.div_const a).integrableOn measurableSet_Ioi fun x hx ↦ ?_
  rw [le_div_iff₀ ha]
  have hx : a < x := hx
  nlinarith [npdf_pos x]

/-- **Chernoff**: `Φ(y) ≤ e^{-y²/2}/2` for `y ≤ 0`. -/
theorem Phi_le_exp {y : ℝ} (hy : y ≤ 0) : Phi y ≤ exp (-y ^ 2 / 2) / 2 := by
  have hhalf : ∫ x in Iic y, gaussianPDFReal y 1 x = 1 / 2 := by
    rw [TauCeti.Probability.integral_Iic_gaussianPDFReal y one_ne_zero]
    simp
  rw [Phi_eq_integral, div_eq_mul_one_div _ 2, ← hhalf, ← integral_const_mul]
  refine setIntegral_mono_on integrable_npdf.integrableOn
    ((integrable_gaussianPDFReal y 1).const_mul _).integrableOn measurableSet_Iic fun x hx ↦ ?_
  have hx : x ≤ y := hx
  rw [npdf_eq, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one]
  rw [mul_left_comm, ← exp_add]
  refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by positivity)
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hy (sub_nonpos.2 hx)]

/-- `γ₁` of an interval of length `ℓ` is at most `ℓ/√(2π)`. -/
theorem gaussianReal_Icc_le {a b : ℝ} (hab : a ≤ b) :
    (gaussianReal 0 1).real (Icc a b) ≤ (b - a) / √(2 * π) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      fun x _ ↦ gaussianPDFReal_nonneg 0 1 x)]
  calc ∫ x in Icc a b, gaussianPDFReal 0 1 x
      ≤ ∫ x in Icc a b, (√(2 * π))⁻¹ :=
        setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc fun x _ ↦ npdf_le x
    _ = (b - a) / √(2 * π) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab, smul_eq_mul, div_eq_mul_inv]

end BGHKLMM26.RobustMIS
