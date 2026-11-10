module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Population facts behind window verification

One-dimensional facts about the law of a statistic of one Gaussian component, used to verify a
split `{s(x) ≤ τ}` by the mass of a window around the threshold `τ`.

## Additive windows (any statistic with a variance bound)

For a real random variable `X` with mean `m` and `Var X ≤ s²` on a probability space:

* `ABBKS26.Population.mul_sq_sub_le_variance`, `ABBKS26.Population.abs_sub_le_of_two_sided`:
  if `P(X ≤ τ) ≥ φ` and `P(X > τ) ≥ φ`, then `φ (m - τ)² ≤ Var X`, so `|m - τ| ≤ s / √φ`.
* `ABBKS26.Population.one_sub_le_measureReal_window`: if `|m - τ| ≤ D < W`, then
  `P(|X - τ| ≤ W) ≥ 1 - s² / (W - D)²`; with the two-sided hypothesis and `D = s / √φ` this is
  `ABBKS26.Population.one_sub_le_measureReal_window_of_two_sided`.
* `ABBKS26.Population.measureReal_window_le`: if `|m - τ| ≥ W' > W`, then
  `P(|X - τ| ≤ W) ≤ s² / (W' - W)²`.

## Logarithmic windows (centered Gaussians)

For `X ~ N(0, v)` (`gaussianReal 0 v`, standard deviation `σ = √v`):

* `ABBKS26.Population.gaussianReal_abs_ge_le`: `P(|X - m| ≥ t) ≤ v / t²` (any mean `m`).
* `ABBKS26.Population.gaussianReal_abs_sub_le_le`: `P(|X - a| ≤ t) ≤ t / √v` (any mean, any `a`).
  Centered versions: `ABBKS26.Population.gaussianReal_zero_abs_ge_le`,
  `ABBKS26.Population.gaussianReal_zero_abs_le_le`.
* `ABBKS26.Population.gaussianReal_window_ge`: if `P(|X| ≤ τ) ≥ φ` and `P(|X| > τ) ≥ φ`
  (`0 < φ ≤ 1`), then `P(τ/K ≤ |X| ≤ τK) ≥ 1 - 1/(φK) - 1/(φ²K²)`;
  `ABBKS26.Population.gaussianReal_window_ge_half`: at least `1/2` when `K ≥ 4/φ`.
* `ABBKS26.Population.gaussianReal_abs_ge_le_of_le`,
  `ABBKS26.Population.gaussianReal_abs_le_le_of_ge`: if `σ ≤ τ/K'` then
  `P(|X| ≥ τ/K) ≤ (K/K')²`; if `σ ≥ τK'` then `P(|X| ≤ τK) ≤ K/K'`.

## Statistics of a multivariate Gaussian

For `y ~ N(μ, S)` (`multivariateGaussian`) on `EuclideanSpace ℝ ι`:

* `ABBKS26.Population.map_dotProduct_multivariateGaussian`: `⟨v, y⟩ ~ N(⟨v, μ⟩, vᵀ S v)`, with
  `ABBKS26.Population.measureReal_dotProduct_multivariateGaussian` (probabilities of events
  `⟨v, y⟩ ∈ s`), and the mean, variance and square integrability of `⟨v, y⟩`
  (`ABBKS26.Population.integral_dotProduct_multivariateGaussian`, ...). The logarithmic window
  facts for `⟨v, y⟩` are `ABBKS26.Population.multivariateGaussian_window_ge`,
  `ABBKS26.Population.multivariateGaussian_abs_ge_le_of_le`,
  `ABBKS26.Population.multivariateGaussian_abs_le_le_of_ge`.
* Quadratic statistics `q(y) = yᵀ A y + ⟨b, y⟩ + c` for symmetric `A` and `y ~ N(0, S)`:
  `ABBKS26.Population.integral_quadStat_multivariateGaussian` (mean `tr (A S) + c`),
  `ABBKS26.Population.variance_quadStat_multivariateGaussian` (variance
  `2 tr ((A S)²) + bᵀ S b`), `ABBKS26.Population.memLp_quadStat_multivariateGaussian`.
-/

@[expose] public section

namespace ABBKS26

namespace Population

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

/-! ### Chebyshev -/

section General

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Two events covering the space have probabilities summing to at least `1`. -/
theorem one_le_measureReal_add [IsProbabilityMeasure P] {s t : Set Ω} (h : ∀ ω, ω ∈ s ∨ ω ∈ t) :
    1 ≤ P.real s + P.real t := by
  have hst : s ∪ t = univ := eq_univ_of_forall fun ω ↦ h ω
  calc (1 : ℝ) = P.real (s ∪ t) := by rw [hst, probReal_univ]
    _ ≤ P.real s + P.real t := measureReal_union_le s t

/-- **Chebyshev's inequality** for `measureReal`: `P(|X - E X| ≥ c) ≤ Var X / c²`. -/
theorem measureReal_abs_sub_ge_le [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {c : ℝ}
    (hc : 0 < c) : P.real {ω | c ≤ |X ω - P[X]|} ≤ Var[X; P] / c ^ 2 := by
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by have := variance_nonneg X P; positivity)
    (meas_ge_le_variance_div_sq hX hc)

/-- Chebyshev's inequality for an event inside a deviation event. -/
theorem measureReal_le_of_subset_dev [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {c : ℝ}
    (hc : 0 < c) {s : Set Ω} (hs : ∀ ω ∈ s, c ≤ |X ω - P[X]|) :
    P.real s ≤ Var[X; P] / c ^ 2 :=
  (measureReal_mono fun ω hω ↦ hs ω hω).trans (measureReal_abs_sub_ge_le hX hc)

/-! ### Additive windows -/

/-- **Two-sided splits have their threshold near the mean**: if `P(X ≤ τ) ≥ φ` and
`P(X > τ) ≥ φ`, then `φ (E X - τ)² ≤ Var X`. -/
theorem mul_sq_sub_le_variance [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) {φ τ : ℝ}
    (hle : φ ≤ P.real {ω | X ω ≤ τ}) (hgt : φ ≤ P.real {ω | τ < X ω}) :
    φ * (P[X] - τ) ^ 2 ≤ Var[X; P] := by
  rcases lt_trichotomy P[X] τ with h | h | h
  · have hc : 0 < τ - P[X] := sub_pos.mpr h
    have := measureReal_le_of_subset_dev hX hc (s := {ω | τ < X ω}) fun ω hω ↦ by
      simp only [mem_ofPred_eq] at hω
      rw [abs_of_pos (by linarith)]
      linarith
    have h2 := hgt.trans this
    rw [le_div_iff₀ (by positivity)] at h2
    rwa [show (P[X] - τ) ^ 2 = (τ - P[X]) ^ 2 by ring]
  · rw [h, sub_self]
    simp [variance_nonneg]
  · have hc : 0 < P[X] - τ := sub_pos.mpr h
    have := measureReal_le_of_subset_dev hX hc (s := {ω | X ω ≤ τ}) fun ω hω ↦ by
      simp only [mem_ofPred_eq] at hω
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    have h2 := hle.trans this
    rwa [le_div_iff₀ (by positivity)] at h2

/-- **Two-sided splits have their threshold near the mean**: if `P(X ≤ τ) ≥ φ > 0`,
`P(X > τ) ≥ φ` and `Var X ≤ s²`, then `|E X - τ| ≤ s / √φ`. -/
theorem abs_sub_le_of_two_sided [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    {φ τ s : ℝ} (hφ : 0 < φ) (hs : 0 ≤ s) (hvar : Var[X; P] ≤ s ^ 2)
    (hle : φ ≤ P.real {ω | X ω ≤ τ}) (hgt : φ ≤ P.real {ω | τ < X ω}) :
    |P[X] - τ| ≤ s / √φ := by
  have h := (mul_sq_sub_le_variance hX hle hgt).trans hvar
  have hsφ : 0 < √φ := sqrt_pos.mpr hφ
  rw [le_div_iff₀ hsφ]
  have h' : (|P[X] - τ| * √φ) ^ 2 ≤ s ^ 2 := by
    rw [mul_pow, sq_abs, sq_sqrt hφ.le, mul_comm]
    exact h
  exact (pow_le_pow_iff_left₀ (by positivity) hs two_ne_zero).mp h'

/-- **A window around a threshold near the mean is heavy**: if `|E X - τ| ≤ D < W` and
`Var X ≤ s²`, then `P(|X - τ| ≤ W) ≥ 1 - s² / (W - D)²`. -/
theorem one_sub_le_measureReal_window [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    {τ s D W : ℝ} (hvar : Var[X; P] ≤ s ^ 2) (hD : |P[X] - τ| ≤ D) (hDW : D < W) :
    1 - s ^ 2 / (W - D) ^ 2 ≤ P.real {ω | |X ω - τ| ≤ W} := by
  have hc : 0 < W - D := sub_pos.mpr hDW
  have hcov := one_le_measureReal_add (P := P) (s := {ω | |X ω - τ| ≤ W})
    (t := {ω | W < |X ω - τ|}) fun ω ↦ le_or_gt |X ω - τ| W
  have hdev := measureReal_le_of_subset_dev hX hc (s := {ω | W < |X ω - τ|}) fun ω hω ↦ by
    simp only [mem_ofPred_eq] at hω
    have := abs_sub_abs_le_abs_sub (X ω - τ) (P[X] - τ)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  have : Var[X; P] / (W - D) ^ 2 ≤ s ^ 2 / (W - D) ^ 2 :=
    div_le_div_of_nonneg_right hvar (by positivity)
  linarith

/-- **Two-sided splits put a heavy window around the threshold**: if `P(X ≤ τ) ≥ φ > 0`,
`P(X > τ) ≥ φ` and `Var X ≤ s²`, then for `W > s / √φ`,
`P(|X - τ| ≤ W) ≥ 1 - s² / (W - s / √φ)²`. -/
theorem one_sub_le_measureReal_window_of_two_sided [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : MemLp X 2 P) {φ τ s W : ℝ} (hφ : 0 < φ) (hs : 0 ≤ s) (hvar : Var[X; P] ≤ s ^ 2)
    (hle : φ ≤ P.real {ω | X ω ≤ τ}) (hgt : φ ≤ P.real {ω | τ < X ω}) (hW : s / √φ < W) :
    1 - s ^ 2 / (W - s / √φ) ^ 2 ≤ P.real {ω | |X ω - τ| ≤ W} :=
  one_sub_le_measureReal_window hX hvar (abs_sub_le_of_two_sided hX hφ hs hvar hle hgt) hW

/-- **A window far from the mean is light** (completeness): if `|E X - τ| ≥ W' > W` and
`Var X ≤ s²`, then `P(|X - τ| ≤ W) ≤ s² / (W' - W)²`. -/
theorem measureReal_window_le [IsFiniteMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    {τ s W W' : ℝ} (hvar : Var[X; P] ≤ s ^ 2) (hW' : W' ≤ |P[X] - τ|) (hWW : W < W') :
    P.real {ω | |X ω - τ| ≤ W} ≤ s ^ 2 / (W' - W) ^ 2 := by
  have hc : 0 < W' - W := sub_pos.mpr hWW
  refine (measureReal_le_of_subset_dev hX hc fun ω hω ↦ ?_).trans
    (div_le_div_of_nonneg_right hvar (by positivity))
  simp only [mem_ofPred_eq] at hω
  have := abs_sub_abs_le_abs_sub (P[X] - τ) (X ω - τ)
  rw [sub_sub_sub_cancel_right, abs_sub_comm (P[X]) (X ω)] at this
  linarith

end General

/-! ### Logarithmic windows for a centered Gaussian -/

section Gaussian

/-- **Chebyshev for a Gaussian**: `P(|X - m| ≥ t) ≤ v / t²` for `X ~ N(m, v)`. -/
theorem gaussianReal_abs_ge_le (m : ℝ) (v : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    (gaussianReal m v).real {x | t ≤ |x - m|} ≤ v / t ^ 2 := by
  have h := measureReal_abs_sub_ge_le (P := gaussianReal m v) (X := id)
    (memLp_id_gaussianReal 2) ht
  simpa only [id_eq, integral_id_gaussianReal, variance_id_gaussianReal] using h

/-- **Gaussian anticoncentration**: `P(|X - a| ≤ t) ≤ t / √v` for `X ~ N(m, v)`, `v ≠ 0`: the
density is at most `1 / √(2π v)` and `2 / √(2π) ≤ 1`. -/
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

/-- `gaussianReal_abs_ge_le` for a centered Gaussian: `P(|X| ≥ t) ≤ v / t²`. -/
theorem gaussianReal_zero_abs_ge_le (v : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    (gaussianReal 0 v).real {x | t ≤ |x|} ≤ v / t ^ 2 := by
  simpa only [sub_zero] using gaussianReal_abs_ge_le 0 v ht

/-- `gaussianReal_abs_sub_le_le` for a centered Gaussian: `P(|X| ≤ t) ≤ t / √v`. -/
theorem gaussianReal_zero_abs_le_le {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 v).real {x | |x| ≤ t} ≤ t / √v := by
  simpa only [sub_zero] using gaussianReal_abs_sub_le_le 0 0 hv ht

/-- **Two-sided splits of a centered Gaussian put a heavy logarithmic window around the
threshold**: if `X ~ N(0, v)`, `P(|X| ≤ τ) ≥ φ` and `P(|X| > τ) ≥ φ` with `0 < φ ≤ 1`, then
`P(τ/K ≤ |X| ≤ τK) ≥ 1 - 1/(φK) - 1/(φ²K²)` for every `K > 0`.

The hypotheses give `φ τ ≤ √v ≤ τ / φ` (anticoncentration and Chebyshev); then anticoncentration
bounds `P(|X| < τ/K)` and Chebyshev bounds `P(|X| > τK)`. -/
theorem gaussianReal_window_ge {v : ℝ≥0} {φ τ K : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hτ : 0 < τ)
    (hK : 0 < K) (hle : φ ≤ (gaussianReal 0 v).real {x | |x| ≤ τ})
    (hgt : φ ≤ (gaussianReal 0 v).real {x | τ < |x|}) :
    1 - 1 / (φ * K) - 1 / (φ ^ 2 * K ^ 2) ≤
      (gaussianReal 0 v).real {x | τ / K ≤ |x| ∧ |x| ≤ τ * K} := by
  -- the variance is positive
  have hv : v ≠ 0 := by
    rintro rfl
    have : (gaussianReal 0 0).real {x : ℝ | τ < |x|} = 0 := by
      rw [gaussianReal_zero_var, measureReal_def, Measure.dirac_apply' _
        (measurableSet_lt measurable_const continuous_abs.measurable)]
      simp [Set.indicator, hτ.not_gt]
    linarith
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.2 (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  set σ := √(v : ℝ) with hσdef
  have hσ : 0 < σ := sqrt_pos.mpr hv0
  have hσ2 : σ ^ 2 = v := sq_sqrt hv0.le
  have hsub : ∀ x : ℝ, |x| = |x - 0| := fun x ↦ by rw [sub_zero]
  -- `σ ≤ τ / φ`
  have hup : φ * σ ≤ τ := by
    have := gaussianReal_abs_sub_le_le 0 0 hv hτ.le
    simp only [sub_zero] at this
    have h := hle.trans this
    rwa [le_div_iff₀ hσ] at h
  -- `φ τ² ≤ σ²`, so `φ τ ≤ σ`
  have hlo : φ * τ ^ 2 ≤ σ ^ 2 := by
    have := gaussianReal_abs_ge_le 0 v hτ
    simp only [sub_zero] at this
    have h := (hgt.trans (measureReal_mono (show {x : ℝ | τ < |x|} ⊆ {x | τ ≤ |x|} from
      ofPred_subset_ofPred.2 fun _ hx ↦ le_of_lt hx))).trans this
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hlo' : φ * τ ≤ σ := by
    have : (φ * τ) ^ 2 ≤ σ ^ 2 := by
      have : φ ^ 2 ≤ φ := by nlinarith
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hσ.le two_ne_zero).mp this
  -- the lower tail
  have hlow : (gaussianReal 0 v).real {x | |x| < τ / K} ≤ 1 / (φ * K) := by
    have h := gaussianReal_abs_sub_le_le 0 0 hv (t := τ / K) (by positivity)
    simp only [sub_zero] at h
    refine (measureReal_mono (show {x : ℝ | |x| < τ / K} ⊆ {x | |x| ≤ τ / K} from
      ofPred_subset_ofPred.2 fun _ hx ↦ le_of_lt hx)).trans (h.trans ?_)
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  -- the upper tail
  have hhigh : (gaussianReal 0 v).real {x | τ * K < |x|} ≤ 1 / (φ ^ 2 * K ^ 2) := by
    have h := gaussianReal_abs_ge_le 0 v (t := τ * K) (by positivity)
    simp only [sub_zero] at h
    refine (measureReal_mono (show {x : ℝ | τ * K < |x|} ⊆ {x | τ * K ≤ |x|} from
      ofPred_subset_ofPred.2 fun _ hx ↦ le_of_lt hx)).trans (h.trans ?_)
    rw [← hσ2, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (φ * σ) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by positivity) hup 2
    nlinarith
  have hcov : 1 ≤ (gaussianReal 0 v).real {x | τ / K ≤ |x| ∧ |x| ≤ τ * K} +
      ((gaussianReal 0 v).real {x | |x| < τ / K} +
        (gaussianReal 0 v).real {x | τ * K < |x|}) := by
    refine (one_le_measureReal_add (P := gaussianReal 0 v) (s := {x | τ / K ≤ |x| ∧ |x| ≤ τ * K})
      (t := {x | |x| < τ / K} ∪ {x | τ * K < |x|}) fun x ↦ ?_).trans ?_
    · by_cases h1 : τ / K ≤ |x|
      · by_cases h2 : |x| ≤ τ * K
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inr (not_le.mp h2))
      · exact Or.inr (Or.inl (not_le.mp h1))
    · gcongr
      exact measureReal_union_le _ _
  linarith

/-- `gaussianReal_window_ge` with `K ≥ 4 / φ`: the window has probability at least `1/2`. -/
theorem gaussianReal_window_ge_half {v : ℝ≥0} {φ τ K : ℝ} (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hτ : 0 < τ) (hK : 4 / φ ≤ K) (hle : φ ≤ (gaussianReal 0 v).real {x | |x| ≤ τ})
    (hgt : φ ≤ (gaussianReal 0 v).real {x | τ < |x|}) :
    1 / 2 ≤ (gaussianReal 0 v).real {x | τ / K ≤ |x| ∧ |x| ≤ τ * K} := by
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  refine le_trans ?_ (gaussianReal_window_ge hφ hφ1 hτ hK0 hle hgt)
  have h4 : 4 ≤ φ * K := by rwa [div_le_iff₀ hφ, mul_comm] at hK
  have h1 : 1 / (φ * K) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
  have h2 : 1 / (φ ^ 2 * K ^ 2) ≤ 1 / 16 := by
    rw [show φ ^ 2 * K ^ 2 = (φ * K) ^ 2 by ring]
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  linarith

/-- **Completeness, small variance**: if `X ~ N(0, v)` with `√v ≤ τ / K'` (as
`v ≤ (τ / K')²`), then `P(|X| ≥ τ / K) ≤ (K / K')²`. -/
theorem gaussianReal_abs_ge_le_of_le {v : ℝ≥0} {τ K K' : ℝ} (hτ : 0 < τ) (hK : 0 < K)
    (hK' : 0 < K') (hv : (v : ℝ) ≤ (τ / K') ^ 2) :
    (gaussianReal 0 v).real {x | τ / K ≤ |x|} ≤ (K / K') ^ 2 := by
  have h := gaussianReal_abs_ge_le 0 v (t := τ / K) (by positivity)
  simp only [sub_zero] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by positivity)]
  calc (v : ℝ) ≤ (τ / K') ^ 2 := hv
    _ = (K / K') ^ 2 * (τ / K) ^ 2 := by field_simp

/-- **Completeness, large variance**: if `X ~ N(0, v)` with `√v ≥ τ K'` (as `(τ K')² ≤ v`),
then `P(|X| ≤ τ K) ≤ K / K'`. -/
theorem gaussianReal_abs_le_le_of_ge {v : ℝ≥0} {τ K K' : ℝ} (hτ : 0 < τ) (hK : 0 < K)
    (hK' : 0 < K') (hv : (τ * K') ^ 2 ≤ v) :
    (gaussianReal 0 v).real {x | |x| ≤ τ * K} ≤ K / K' := by
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le (by positivity) hv
  have hv' : v ≠ 0 := fun h ↦ by simp [h] at hv0
  have h := gaussianReal_abs_sub_le_le 0 0 hv' (t := τ * K) (by positivity)
  simp only [sub_zero] at h
  refine h.trans ?_
  have hs : τ * K' ≤ √(v : ℝ) := by
    rw [← sqrt_sq (by positivity : 0 ≤ τ * K')]
    exact sqrt_le_sqrt hv
  rw [div_le_div_iff₀ (sqrt_pos.mpr hv0) hK']
  calc τ * K * K' = K * (τ * K') := by ring
    _ ≤ K * √(v : ℝ) := mul_le_mul_of_nonneg_left hs hK.le

end Gaussian

/-! ### Linear statistics of a multivariate Gaussian -/

section Linear

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

open Matrix WithLp
open scoped RealInnerProductSpace

omit [DecidableEq ι] in
/-- `y ↦ v ⬝ᵥ y` is the continuous linear functional `⟪v, ·⟫`. -/
theorem dotProduct_eq_innerSL (v : ι → ℝ) :
    (fun y : EuclideanSpace ℝ ι ↦ v ⬝ᵥ y.ofLp) = ⇑(innerSL ℝ (toLp 2 v)) := by
  ext y
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

omit [DecidableEq ι] in
/-- A linear statistic is measurable. -/
theorem measurable_dotProduct (v : ι → ℝ) :
    Measurable fun y : EuclideanSpace ℝ ι ↦ v ⬝ᵥ y.ofLp := by
  rw [dotProduct_eq_innerSL]
  exact (innerSL ℝ (toLp 2 v)).continuous.measurable

/-- **The law of a linear statistic**: for `y ~ N(μ, S)`, `⟨v, y⟩ ~ N(⟨v, μ⟩, vᵀ S v)`. -/
theorem map_dotProduct_multivariateGaussian (hS : S.PosSemidef) (v : ι → ℝ) :
    (multivariateGaussian μ S).map (fun y ↦ v ⬝ᵥ y.ofLp) =
      gaussianReal (v ⬝ᵥ μ.ofLp) (v ⬝ᵥ (S *ᵥ v)).toNNReal := by
  rw [dotProduct_eq_innerSL, IsGaussian.map_eq_gaussianReal]
  congr 2
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  · change Var[fun u ↦ ⟪toLp 2 v, u⟫; multivariateGaussian μ S] = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS]

/-- Probabilities of events about a linear statistic of `y ~ N(μ, S)` are those of
`N(⟨v, μ⟩, vᵀ S v)`. -/
theorem measureReal_dotProduct_multivariateGaussian (hS : S.PosSemidef) (v : ι → ℝ)
    {p : ℝ → Prop} (hp : MeasurableSet {x | p x}) :
    (multivariateGaussian μ S).real {y | p (v ⬝ᵥ y.ofLp)} =
      (gaussianReal (v ⬝ᵥ μ.ofLp) (v ⬝ᵥ (S *ᵥ v)).toNNReal).real {x | p x} := by
  rw [← map_dotProduct_multivariateGaussian hS v, map_measureReal_apply (measurable_dotProduct v)
    hp]
  rfl

/-- A linear statistic of a multivariate Gaussian has all finite moments. -/
theorem memLp_dotProduct_multivariateGaussian (v : ι → ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun y ↦ v ⬝ᵥ y.ofLp) p (multivariateGaussian μ S) := by
  rw [dotProduct_eq_innerSL]
  exact (innerSL ℝ (toLp 2 v)).comp_memLp' (IsGaussian.memLp_id _ p hp)

/-- The mean of `⟨v, y⟩` for `y ~ N(μ, S)` is `⟨v, μ⟩`. -/
theorem integral_dotProduct_multivariateGaussian (v : ι → ℝ) :
    ∫ y, v ⬝ᵥ y.ofLp ∂(multivariateGaussian μ S) = v ⬝ᵥ μ.ofLp := by
  rw [show (∫ y, v ⬝ᵥ y.ofLp ∂(multivariateGaussian μ S)) =
      ∫ y, (innerSL ℝ (toLp 2 v)) y ∂(multivariateGaussian μ S) by
    rw [← dotProduct_eq_innerSL],
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- The variance of `⟨v, y⟩` for `y ~ N(μ, S)` is `vᵀ S v`. -/
theorem variance_dotProduct_multivariateGaussian (hS : S.PosSemidef) (v : ι → ℝ) :
    Var[fun y ↦ v ⬝ᵥ y.ofLp; multivariateGaussian μ S] = v ⬝ᵥ (S *ᵥ v) := by
  rw [dotProduct_eq_innerSL]
  change Var[fun u ↦ ⟪toLp 2 v, u⟫; multivariateGaussian μ S] = _
  rw [← covarianceBilin_self IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS]

/-- `gaussianReal_window_ge` for a linear statistic `⟨v, y⟩` of `y ~ N(0, S)`. -/
theorem multivariateGaussian_window_ge (hS : S.PosSemidef) (v : ι → ℝ) {φ τ K : ℝ}
    (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hτ : 0 < τ) (hK : 0 < K)
    (hle : φ ≤ (multivariateGaussian 0 S).real {y | |v ⬝ᵥ y.ofLp| ≤ τ})
    (hgt : φ ≤ (multivariateGaussian 0 S).real {y | τ < |v ⬝ᵥ y.ofLp|}) :
    1 - 1 / (φ * K) - 1 / (φ ^ 2 * K ^ 2) ≤
      (multivariateGaussian 0 S).real {y | τ / K ≤ |v ⬝ᵥ y.ofLp| ∧ |v ⬝ᵥ y.ofLp| ≤ τ * K} := by
  have h0 : v ⬝ᵥ (0 : EuclideanSpace ℝ ι).ofLp = 0 := by simp
  rw [measureReal_dotProduct_multivariateGaussian hS v (p := fun x ↦ |x| ≤ τ)
    (measurableSet_le continuous_abs.measurable measurable_const), h0] at hle
  rw [measureReal_dotProduct_multivariateGaussian hS v (p := fun x ↦ τ < |x|)
    (measurableSet_lt measurable_const continuous_abs.measurable), h0] at hgt
  rw [measureReal_dotProduct_multivariateGaussian hS v (p := fun x ↦ τ / K ≤ |x| ∧ |x| ≤ τ * K)
    ((measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const)), h0]
  exact gaussianReal_window_ge hφ hφ1 hτ hK hle hgt

/-- `gaussianReal_abs_ge_le_of_le` for a linear statistic `⟨v, y⟩` of `y ~ N(0, S)`:
if `vᵀ S v ≤ (τ / K')²` then `P(|⟨v, y⟩| ≥ τ / K) ≤ (K / K')²`. -/
theorem multivariateGaussian_abs_ge_le_of_le (hS : S.PosSemidef) (v : ι → ℝ) {τ K K' : ℝ}
    (hτ : 0 < τ) (hK : 0 < K) (hK' : 0 < K') (hv : v ⬝ᵥ (S *ᵥ v) ≤ (τ / K') ^ 2) :
    (multivariateGaussian 0 S).real {y | τ / K ≤ |v ⬝ᵥ y.ofLp|} ≤ (K / K') ^ 2 := by
  have h0 : v ⬝ᵥ (0 : EuclideanSpace ℝ ι).ofLp = 0 := by simp
  rw [measureReal_dotProduct_multivariateGaussian hS v (p := fun x ↦ τ / K ≤ |x|)
    (measurableSet_le measurable_const continuous_abs.measurable), h0]
  refine gaussianReal_abs_ge_le_of_le hτ hK hK' ?_
  rw [Real.coe_toNNReal _ (by simpa [star_trivial] using hS.dotProduct_mulVec_nonneg v)]
  exact hv

/-- `gaussianReal_abs_le_le_of_ge` for a linear statistic `⟨v, y⟩` of `y ~ N(0, S)`:
if `(τ K')² ≤ vᵀ S v` then `P(|⟨v, y⟩| ≤ τ K) ≤ K / K'`. -/
theorem multivariateGaussian_abs_le_le_of_ge (hS : S.PosSemidef) (v : ι → ℝ) {τ K K' : ℝ}
    (hτ : 0 < τ) (hK : 0 < K) (hK' : 0 < K') (hv : (τ * K') ^ 2 ≤ v ⬝ᵥ (S *ᵥ v)) :
    (multivariateGaussian 0 S).real {y | |v ⬝ᵥ y.ofLp| ≤ τ * K} ≤ K / K' := by
  have h0 : v ⬝ᵥ (0 : EuclideanSpace ℝ ι).ofLp = 0 := by simp
  rw [measureReal_dotProduct_multivariateGaussian hS v (p := fun x ↦ |x| ≤ τ * K)
    (measurableSet_le continuous_abs.measurable measurable_const), h0]
  refine gaussianReal_abs_le_le_of_ge hτ hK hK' ?_
  rw [Real.coe_toNNReal _ (by simpa [star_trivial] using hS.dotProduct_mulVec_nonneg v)]
  exact hv

end Linear

/-! ### Quadratic statistics of a centered multivariate Gaussian -/

section Quadratic

open Matrix WithLp

/-! #### One coordinate: `l t² + β t` for `t ~ N(0, 1)` -/

/-- `E t³ = 0` for `t ~ N(0, 1)`. -/
theorem integral_pow_three_gaussianReal : ∫ t, t ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have h := TauCeti.Probability.centralMoment_id_two_mul_add_one_gaussianReal 0 1 1
  simpa [centralMoment, integral_id_gaussianReal] using h

/-- `E t⁴ = 3` for `t ~ N(0, 1)`. -/
theorem integral_pow_four_gaussianReal : ∫ t, t ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 1 2
  simpa using h

/-- `l t² + β t` is square integrable for `t ~ N(0, 1)`. -/
theorem memLp_quad_gaussianReal (l β : ℝ) :
    MemLp (fun t : ℝ ↦ l * t ^ 2 + β * t) 2 (gaussianReal 0 1) := by
  have := TauCeti.memLp_two_eval_gaussianReal 0 1
    (Polynomial.C l * Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X)
  simpa using this

/-- `E [l t² + β t] = l` for `t ~ N(0, 1)`. -/
theorem integral_quad_gaussianReal (l β : ℝ) :
    ∫ t, (l * t ^ 2 + β * t) ∂(gaussianReal 0 1) = l := by
  have h2 := TauCeti.integrable_pow_gaussianReal 0 1 2
  have h1 := TauCeti.integrable_pow_gaussianReal 0 1 1
  simp only [pow_one] at h1
  rw [integral_add (h2.const_mul l) (h1.const_mul β), integral_const_mul, integral_const_mul,
    TauCeti.Probability.integral_sq_gaussianReal, integral_id_gaussianReal]
  simp

/-- `Var [l t² + β t] = 2 l² + β²` for `t ~ N(0, 1)` (`E t⁴ = 3`, `E t³ = 0`). -/
theorem variance_quad_gaussianReal (l β : ℝ) :
    Var[fun t ↦ l * t ^ 2 + β * t; gaussianReal 0 1] = 2 * l ^ 2 + β ^ 2 := by
  rw [variance_eq_sub (memLp_quad_gaussianReal l β), integral_quad_gaussianReal]
  have hfun : ((fun t : ℝ ↦ l * t ^ 2 + β * t) ^ 2) =
      fun t ↦ l ^ 2 * t ^ 4 + (2 * l * β) * t ^ 3 + β ^ 2 * t ^ 2 := by
    ext t
    simp only [Pi.pow_apply]
    ring
  have h4 := TauCeti.integrable_pow_gaussianReal 0 1 4
  have h3 := TauCeti.integrable_pow_gaussianReal 0 1 3
  have h2 := TauCeti.integrable_pow_gaussianReal 0 1 2
  have h43 : Integrable (fun x : ℝ ↦ l ^ 2 * x ^ 4 + 2 * l * β * x ^ 3) (gaussianReal 0 1) :=
    (h4.const_mul _).add (h3.const_mul _)
  have e1 : ∫ x, (l ^ 2 * x ^ 4 + 2 * l * β * x ^ 3 + β ^ 2 * x ^ 2) ∂(gaussianReal 0 1) =
      ∫ x, (l ^ 2 * x ^ 4 + 2 * l * β * x ^ 3) ∂(gaussianReal 0 1) +
        ∫ x, β ^ 2 * x ^ 2 ∂(gaussianReal 0 1) := integral_add h43 (h2.const_mul _)
  have e2 : ∫ x, (l ^ 2 * x ^ 4 + 2 * l * β * x ^ 3) ∂(gaussianReal 0 1) =
      ∫ x, l ^ 2 * x ^ 4 ∂(gaussianReal 0 1) + ∫ x, 2 * l * β * x ^ 3 ∂(gaussianReal 0 1) :=
    integral_add (h4.const_mul _) (h3.const_mul _)
  rw [hfun]
  beta_reduce
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_pow_four_gaussianReal, integral_pow_three_gaussianReal,
    TauCeti.Probability.integral_sq_gaussianReal]
  simp only [NNReal.coe_one]
  ring

/-! #### Sums over independent coordinates -/

variable {ι : Type*} [Fintype ι]

/-- `∑ᵢ (λᵢ xᵢ² + βᵢ xᵢ) + c` is square integrable for a standard Gaussian `x`. -/
theorem memLp_sumQuad_pi (lam β : ι → ℝ) (c : ℝ) :
    MemLp (fun x : ι → ℝ ↦ ∑ i, (lam i * x i ^ 2 + β i * x i) + c) 2
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) :=
  (memLp_finsetSum _ fun i _ ↦ (memLp_quad_gaussianReal (lam i) (β i)).comp_measurePreserving
    (measurePreserving_eval _ i)).add (memLp_const c)

/-- `E [∑ᵢ (λᵢ xᵢ² + βᵢ xᵢ) + c] = ∑ᵢ λᵢ + c` for a standard Gaussian `x`. -/
theorem integral_sumQuad_pi (lam β : ι → ℝ) (c : ℝ) :
    ∫ x, (∑ i, (lam i * x i ^ 2 + β i * x i) + c) ∂(Measure.pi fun _ : ι ↦ gaussianReal 0 1) =
      ∑ i, lam i + c := by
  have hi : ∀ i, Integrable (fun x : ι → ℝ ↦ lam i * x i ^ 2 + β i * x i)
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1) := fun i ↦
    ((memLp_quad_gaussianReal (lam i) (β i)).comp_measurePreserving
      (measurePreserving_eval _ i)).integrable one_le_two
  rw [integral_add (integrable_finsetSum _ fun i _ ↦ hi i) (integrable_const c),
    integral_finsetSum _ fun i _ ↦ hi i, integral_const]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact (integral_comp_eval (μ := fun _ : ι ↦ gaussianReal (0 : ℝ) 1) (i := i)
      (f := fun t : ℝ ↦ lam i * t ^ 2 + β i * t) (by fun_prop)).trans
      (integral_quad_gaussianReal _ _)
  · simp

/-- `Var [∑ᵢ (λᵢ xᵢ² + βᵢ xᵢ) + c] = ∑ᵢ (2 λᵢ² + βᵢ²)` for a standard Gaussian `x`: the
coordinates are independent. -/
theorem variance_sumQuad_pi (lam β : ι → ℝ) (c : ℝ) :
    Var[fun x : ι → ℝ ↦ ∑ i, (lam i * x i ^ 2 + β i * x i) + c;
      Measure.pi fun _ : ι ↦ gaussianReal 0 1] = ∑ i, (2 * lam i ^ 2 + β i ^ 2) := by
  have h := variance_sum_pi (μ := fun _ : ι ↦ gaussianReal 0 1)
    (X := fun i t ↦ lam i * t ^ 2 + β i * t) fun i ↦ memLp_quad_gaussianReal _ _
  have hfun : (fun x : ι → ℝ ↦ ∑ i, (lam i * x i ^ 2 + β i * x i) + c) =
      fun x ↦ (∑ i, fun ω : ι → ℝ ↦ lam i * ω i ^ 2 + β i * ω i) x + c := by
    ext x
    simp [Finset.sum_apply]
  rw [hfun, variance_add_const (Measurable.aestronglyMeasurable (by fun_prop)), h]
  simp [variance_quad_gaussianReal]

/-! #### The spectral reduction -/

variable [DecidableEq ι]

/-- The **quadratic statistic** `q(y) = yᵀ A y + ⟨b, y⟩ + c`. -/
def quadStat (A : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  y.ofLp ⬝ᵥ (A *ᵥ y.ofLp) + b ⬝ᵥ y.ofLp + c

omit [DecidableEq ι] in
/-- The quadratic statistic is continuous. -/
theorem continuous_quadStat (A : Matrix ι ι ℝ) (b : ι → ℝ) (c : ℝ) :
    Continuous (quadStat A b c) := by
  unfold quadStat
  fun_prop

omit [DecidableEq ι] in
/-- The quadratic form of `W x`. -/
theorem mulVec_dotProduct_mulVec (W M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (W *ᵥ x) ⬝ᵥ (M *ᵥ (W *ᵥ x)) = x ⬝ᵥ ((Wᵀ * M * W) *ᵥ x) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec x Wᵀ, vecMul_transpose]

/-- The coordinates of `∑ᵢ xᵢ eᵢ` in an orthonormal eigenbasis `e` are `U x`, for the matrix `U`
with columns `eᵢ`. -/
theorem ofLp_sum_eigenvectorBasis {B : Matrix ι ι ℝ} (hB : B.IsHermitian) (x : ι → ℝ) :
    (∑ i, x i • hB.eigenvectorBasis i).ofLp = (hB.eigenvectorUnitary : Matrix ι ι ℝ) *ᵥ x := by
  ext j
  simp [mulVec, dotProduct, IsHermitian.eigenvectorUnitary_apply, mul_comm]

open scoped MatrixOrder in
/-- **Spectral reduction of a quadratic statistic**: for `y ~ N(0, S)` and symmetric `A`, the
statistic `yᵀ A y + ⟨b, y⟩ + c` has the law of `∑ᵢ (λᵢ xᵢ² + βᵢ xᵢ) + c` for a standard
Gaussian `x` on `ι → ℝ`, where `∑ λᵢ = tr (A S)`, `∑ λᵢ² = tr ((A S)²)` and
`∑ βᵢ² = bᵀ S b`. (The `λᵢ` are the eigenvalues of `S^{1/2} A S^{1/2}`.) -/
theorem exists_pi_reduction {S : Matrix ι ι ℝ} (hS : S.PosSemidef) {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (b : ι → ℝ) (c : ℝ) :
    ∃ (Ψ : (ι → ℝ) → EuclideanSpace ℝ ι) (lam β : ι → ℝ), Measurable Ψ ∧
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map Ψ = multivariateGaussian 0 S ∧
      (∀ x, quadStat A b c (Ψ x) = ∑ i, (lam i * x i ^ 2 + β i * x i) + c) ∧
      ∑ i, lam i = (A * S).trace ∧ ∑ i, lam i ^ 2 = (A * S * (A * S)).trace ∧
      ∑ i, β i ^ 2 = b ⬝ᵥ (S *ᵥ b) := by
  set R := CFC.sqrt S with hRdef
  have hR : R.PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  have hRR : R * R = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hRt : Rᵀ = R := by simpa using hR.isHermitian.eq
  have hAt : Aᵀ = A := by simpa using hA.eq
  set B := R * A * R with hBdef
  have hB : B.IsHermitian := by
    simp only [IsHermitian, hBdef, conjTranspose_mul, hR.isHermitian.eq, hA.eq, mul_assoc]
  set U : Matrix ι ι ℝ := ↑hB.eigenvectorUnitary with hUdef
  have hUt : star U = Uᵀ := by simp [star_eq_conjTranspose]
  have hUU : Uᵀ * U = 1 := by rw [← hUt]; exact Unitary.coe_star_mul_self _
  have hUU' : U * Uᵀ = 1 := by rw [← hUt]; exact Unitary.coe_mul_star_self _
  set lam := hB.eigenvalues with hlam
  have hdiag : Uᵀ * B * U = diagonal lam := by
    have h := hB.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    rw [← hUt]
    convert h using 2
    ext i
    simp [hlam]
  set W := R * U with hWdef
  have hWAW : Wᵀ * A * W = diagonal lam := by
    rw [hWdef, transpose_mul, hRt, ← hdiag, hBdef]
    simp only [mul_assoc]
  refine ⟨fun x ↦ toLp 2 (W *ᵥ x), lam, Wᵀ *ᵥ b, by fun_prop, ?_, fun x ↦ ?_, ?_, ?_, ?_⟩
  · rw [multivariateGaussian, stdGaussian_eq_map_pi_orthonormalBasis hB.eigenvectorBasis,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext x : 1
    refine WithLp.ofLp_injective 2 ?_
    simp only [Function.comp_apply, zero_add, ofLp_toEuclideanCLM, ofLp_sum_eigenvectorBasis,
      mulVec_mulVec, hWdef, hRdef, hUdef]
  · change (W *ᵥ x) ⬝ᵥ (A *ᵥ (W *ᵥ x)) + b ⬝ᵥ (W *ᵥ x) + c = _
    rw [mulVec_dotProduct_mulVec, hWAW, dotProduct_mulVec b W, ← mulVec_transpose]
    simp only [dotProduct, mulVec_diagonal, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  · rw [← trace_diagonal, ← hdiag, trace_mul_comm, ← mul_assoc, hUU', one_mul, hBdef,
      trace_mul_comm, ← mul_assoc, hRR, trace_mul_comm]
  · have h1 : diagonal lam * diagonal lam = Uᵀ * (B * B) * U := by
      rw [← hdiag]
      simp only [mul_assoc, ← mul_assoc U, hUU', one_mul]
    have h2 : B * B = R * (A * S * A) * R := by
      rw [hBdef, ← hRR]
      simp only [mul_assoc]
    rw [show ∑ i, lam i ^ 2 = (diagonal lam * diagonal lam).trace by
      simp [diagonal_mul_diagonal, trace_diagonal, sq], h1, trace_mul_comm, ← mul_assoc, hUU',
      one_mul, h2, trace_mul_comm, ← mul_assoc, hRR, trace_mul_comm]
    simp only [mul_assoc]
  · have hWW : W * Wᵀ = S := by
      rw [hWdef, transpose_mul, hRt, mul_assoc, ← mul_assoc U, hUU', one_mul, hRR]
    rw [show ∑ i, (Wᵀ *ᵥ b) i ^ 2 = (Wᵀ *ᵥ b) ⬝ᵥ (Wᵀ *ᵥ b) by simp [dotProduct, sq],
      dotProduct_mulVec, ← mulVec_transpose, transpose_transpose, mulVec_mulVec, ← hWW]
    exact dotProduct_comm _ _

variable {S : Matrix ι ι ℝ} {A : Matrix ι ι ℝ}

/-- The quadratic statistic of `y ~ N(0, S)` is square integrable. -/
theorem memLp_quadStat_multivariateGaussian (hS : S.PosSemidef) (hA : A.IsHermitian)
    (b : ι → ℝ) (c : ℝ) : MemLp (quadStat A b c) 2 (multivariateGaussian 0 S) := by
  obtain ⟨Ψ, lam, β, hΨ, hmap, hQ, -, -, -⟩ := exists_pi_reduction hS hA b c
  rw [← hmap, memLp_map_measure_iff (continuous_quadStat A b c).aestronglyMeasurable
    hΨ.aemeasurable]
  have : quadStat A b c ∘ Ψ = fun x ↦ ∑ i, (lam i * x i ^ 2 + β i * x i) + c := funext hQ
  rw [this]
  exact memLp_sumQuad_pi lam β c

/-- **The mean of a quadratic statistic**: for `y ~ N(0, S)` and symmetric `A`,
`E [yᵀ A y + ⟨b, y⟩ + c] = tr (A S) + c`. -/
theorem integral_quadStat_multivariateGaussian (hS : S.PosSemidef) (hA : A.IsHermitian)
    (b : ι → ℝ) (c : ℝ) :
    ∫ y, quadStat A b c y ∂(multivariateGaussian 0 S) = (A * S).trace + c := by
  obtain ⟨Ψ, lam, β, hΨ, hmap, hQ, hlam, -, -⟩ := exists_pi_reduction hS hA b c
  rw [← hmap, integral_map hΨ.aemeasurable (continuous_quadStat A b c).aestronglyMeasurable]
  simp_rw [hQ]
  rw [integral_sumQuad_pi, hlam]

/-- **The variance of a quadratic statistic**: for `y ~ N(0, S)` and symmetric `A`,
`Var [yᵀ A y + ⟨b, y⟩ + c] = 2 tr ((A S)²) + bᵀ S b`
(that is, `2 ‖S^{1/2} A S^{1/2}‖_F² + bᵀ S b`). -/
theorem variance_quadStat_multivariateGaussian (hS : S.PosSemidef) (hA : A.IsHermitian)
    (b : ι → ℝ) (c : ℝ) :
    Var[quadStat A b c; multivariateGaussian 0 S] =
      2 * (A * S * (A * S)).trace + b ⬝ᵥ (S *ᵥ b) := by
  obtain ⟨Ψ, lam, β, hΨ, hmap, hQ, -, hlam2, hβ⟩ := exists_pi_reduction hS hA b c
  rw [← hmap, variance_map (continuous_quadStat A b c).aemeasurable hΨ.aemeasurable]
  have : quadStat A b c ∘ Ψ = fun x ↦ ∑ i, (lam i * x i ^ 2 + β i * x i) + c := funext hQ
  rw [this, variance_sumQuad_pi, Finset.sum_add_distrib, ← Finset.mul_sum, hlam2, hβ]

end Quadratic

end Population

end ABBKS26
