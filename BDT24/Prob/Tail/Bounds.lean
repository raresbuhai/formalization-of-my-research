module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# One-dimensional Gaussian facts for the tail bounds of `BDT24.Prob.Tail`

* `BDT24.Prob.T.mgf_sq_gaussianReal`: `E exp(t X²) = (1 - 2 t v)^{-1/2}` for `X ~ N(0, v)` and
  `t v < 1/2`, from the Gaussian integral; `BDT24.Prob.T.mgf_sum_sq_pi`: the moment-generating
  function of `∑ xᵢ²` under a product of copies is its `n`-th power.
* `BDT24.Prob.T.gauss_tail_of_nonneg`: `P(|X| > T) ≤ 2 exp(-T²/4)` for `T ≥ 0` and `v ≤ 2`, by
  Chernoff's bound at `t = ±T/2` on both sides.
* `BDT24.Prob.T.gaussianReal_abs_sub_le_le`: `P(|X - c| ≤ t) ≤ t / √v`, as the density is at
  most `1 / √(2πv)` (copied from `ABBKS26.Population`).
-/

@[expose] public section

namespace BDT24.Prob.T

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

/-- `E exp(t X²) = (1 - 2 t v)^{-1/2}` for `X ~ N(0, v)` with `v > 0` and `t v < 1/2`. -/
theorem mgf_sq_gaussianReal {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : t * v < 1 / 2) :
    mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) t = (√(1 - 2 * t * v))⁻¹ := by
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  rw [mgf, integral_gaussianReal_eq_integral_smul hv]
  have h : ∀ x : ℝ, gaussianPDFReal 0 v x • exp (t * x ^ 2) =
      (√(2 * π * v))⁻¹ * exp (-(1 / (2 * v) - t) * x ^ 2) := by
    intro x
    rw [gaussianPDFReal_def, smul_eq_mul, mul_assoc, ← exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian]
  have hb : 0 < 1 - 2 * t * v := by linarith
  have h2 : π / (1 / (2 * v) - t) = 2 * π * v / (1 - 2 * t * v) := by
    have : (1 / (2 * v) - t : ℝ) = (1 - 2 * t * v) / (2 * v) := by field_simp
    rw [this]
    field_simp
  have hs : 0 < √(2 * π * v) := sqrt_pos.2 (by positivity)
  rw [h2, sqrt_div (by positivity)]
  field_simp

/-- The moment-generating function of `∑ xᵢ²` under `n` independent copies is the `n`-th power
of that of `x²`. -/
theorem mgf_sum_sq_pi (n : ℕ) (v : ℝ≥0) (t : ℝ) :
    mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2) (Measure.pi fun _ ↦ gaussianReal 0 v) t =
      mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) t ^ n := by
  simp only [mgf, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_pow (fun u : ℝ ↦ exp (t * u ^ 2)), Fintype.card_fin]

/-- Chernoff's bound for the upper tail of the squared norm, per coordinate: at `t v = 1/200`,
`exp(-(51/50) t v) (1 - 2 t v)^{-1/2} ≤ exp(-1/100000)`. -/
theorem upper_factor : exp (-(51 / 10000)) * (√(99 / 100))⁻¹ ≤ exp (-(1 / 100000)) := by
  have hs : 0 < √(99 / 100 : ℝ) := sqrt_pos.2 (by norm_num)
  rw [mul_inv_le_iff₀ hs]
  have he : exp (-(509 / 100000)) ≤ √(99 / 100) := by
    rw [le_sqrt' (exp_pos _), sq, ← exp_add]
    have h1 : exp (-(509 / 100000) + -(509 / 100000)) * exp (1018 / 100000) = 1 := by
      rw [← exp_add]; norm_num
    have h2 := add_one_le_exp (1018 / 100000 : ℝ)
    have h3 := exp_pos (-(509 / 100000) + -(509 / 100000) : ℝ)
    nlinarith
  calc exp (-(51 / 10000)) = exp (-(1 / 100000)) * exp (-(509 / 100000)) := by
        rw [← exp_add]; norm_num
    _ ≤ exp (-(1 / 100000)) * √(99 / 100) := by gcongr

/-- Chernoff's bound for the lower tail of the squared norm, per coordinate: at `t v = -1/200`,
`exp((49/50) |t| v) (1 + 2 |t| v)^{-1/2} ≤ exp(-1/100000)`. -/
theorem lower_factor : exp (49 / 10000) * (√(101 / 100))⁻¹ ≤ exp (-(1 / 100000)) := by
  have hs : 0 < √(101 / 100 : ℝ) := sqrt_pos.2 (by norm_num)
  rw [mul_inv_le_iff₀ hs]
  have he : exp (491 / 100000) ≤ √(101 / 100) := by
    rw [le_sqrt' (exp_pos _), sq, ← exp_add]
    refine (exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans ?_
    norm_num
  calc exp (49 / 10000) = exp (-(1 / 100000)) * exp (491 / 100000) := by
        rw [← exp_add]; norm_num
    _ ≤ exp (-(1 / 100000)) * √(101 / 100) := by gcongr

/-- **Gaussian tails**: `P(|X| > T) ≤ 2 exp(-T²/4)` for `X ~ N(0, v)` with `v ≤ 2` and `T ≥ 0`,
by Chernoff's bound at `t = ±T/2` on each side, as `E exp(s X) = exp(v s²/2) ≤ exp(s²)`. -/
theorem gauss_tail_of_nonneg (v : ℝ≥0) (hv : (v : ℝ) ≤ 2) {T : ℝ} (hT : 0 ≤ T) :
    (gaussianReal 0 v).real {x | T < |x|} ≤ 2 * exp (-T ^ 2 / 4) := by
  have hsub : {x : ℝ | T < |x|} ⊆ {x | T ≤ id x} ∪ {x | id x ≤ -T} := by
    intro x hx
    simp only [mem_ofPred_eq, mem_union, id] at hx ⊢
    rcases le_or_gt 0 x with h | h
    · left
      rw [abs_of_nonneg h] at hx
      exact hx.le
    · right
      rw [abs_of_neg h] at hx
      linarith
  have hmgf : ∀ s : ℝ, mgf id (gaussianReal 0 v) s ≤ exp (s ^ 2) := by
    intro s
    simp only [mgf_id_gaussianReal]
    exact exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hv (sq_nonneg s)])
  have h1 : (gaussianReal 0 v).real {x | T ≤ id x} ≤ exp (-T ^ 2 / 4) := by
    refine (measure_ge_le_exp_mul_mgf T (by linarith : (0 : ℝ) ≤ T / 2)
      (integrable_exp_mul_gaussianReal _)).trans ?_
    calc exp (-(T / 2) * T) * mgf id (gaussianReal 0 v) (T / 2)
        ≤ exp (-(T / 2) * T) * exp ((T / 2) ^ 2) := by gcongr; exact hmgf _
      _ = exp (-T ^ 2 / 4) := by rw [← exp_add]; ring_nf
  have h2 : (gaussianReal 0 v).real {x | id x ≤ -T} ≤ exp (-T ^ 2 / 4) := by
    refine (measure_le_le_exp_mul_mgf (-T) (by linarith : -(T / 2) ≤ 0)
      (integrable_exp_mul_gaussianReal _)).trans ?_
    calc exp (-(-(T / 2)) * -T) * mgf id (gaussianReal 0 v) (-(T / 2))
        ≤ exp (-(-(T / 2)) * -T) * exp ((-(T / 2)) ^ 2) := by gcongr; exact hmgf _
      _ = exp (-T ^ 2 / 4) := by rw [← exp_add]; ring_nf
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- `P(|X - a| ≤ t) ≤ t / √v` for `X ~ N(m, v)`, `v ≠ 0`: the density is at most `1/√(2πv)`
(copied from `ABBKS26.Population.gaussianReal_abs_sub_le_le`). -/
theorem gaussianReal_abs_sub_le_le (m a : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal m v).real {x | |x - a| ≤ t} ≤ t / √v := by
  have hS : {x : ℝ | |x - a| ≤ t} = Icc (a - t) (a + t) := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  have hsv : 0 < √(v : ℝ) := sqrt_pos.mpr hv0
  rw [hS, measureReal_def, gaussianReal_apply_eq_integral _ hv,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      fun x _ ↦ gaussianPDFReal_nonneg m v x)]
  have hpdf : ∀ x, gaussianPDFReal m v x ≤ (√(2 * π * v))⁻¹ := by
    intro x
    simp only [gaussianPDFReal]
    calc (√(2 * π * v))⁻¹ * rexp (-(x - m) ^ 2 / (2 * v)) ≤ (√(2 * π * v))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg
            (by nlinarith [sq_nonneg (x - m)]) (by positivity))) (by positivity)
      _ = _ := mul_one _
  have h2 : 2 ≤ √(2 * π) :=
    calc (2 : ℝ) = √(2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ √(2 * π) := Real.sqrt_le_sqrt (by nlinarith [two_le_pi])
  have hsplit : √(2 * π * v) = √(2 * π) * √(v : ℝ) := Real.sqrt_mul (by positivity) _
  calc ∫ x in Icc (a - t) (a + t), gaussianPDFReal m v x
      ≤ ∫ x in Icc (a - t) (a + t), (√(2 * π * v))⁻¹ :=
        setIntegral_mono_on (integrable_gaussianPDFReal m v).integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc fun x _ ↦ hpdf x
    _ = 2 * t / (√(2 * π) * √(v : ℝ)) := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul, hsplit]
        ring
    _ ≤ t / √(v : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hsv]
        have : 2 * t * √(v : ℝ) ≤ t * (√(2 * π) * √(v : ℝ)) := by
          rw [show t * (√(2 * π) * √(v : ℝ)) = √(2 * π) * (t * √(v : ℝ)) by ring,
            show 2 * t * √(v : ℝ) = 2 * (t * √(v : ℝ)) by ring]
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
        linarith

end BDT24.Prob.T
