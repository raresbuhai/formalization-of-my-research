module

public import BHJK25.Spectral.Basic
public import Mathlib.Probability.Independence.Integration

/-!
# Exponential moments of Gaussian quantities

The exponential moments used in the proof of [BHJK25, Lemma 3.7]
(`BHJK25.Spectral.noisy_spike`):

* `E exp(-‖u‖² / 2) = 2^(-n/2)` for a standard Gaussian vector `u ∈ ℝ^n`, hence, by Markov's
  inequality, `‖u‖² < n / 2` with probability at most `(e^(1/4) / √2)^n`;
* for a fixed vector `u` and an eigenvalue `λ ∼ μ_γ` with an independent standard Gaussian vector
  `v`, `E exp(|λ| ⟨v, u⟩² / (4 ‖u‖²)) ≤ 1 - γ + γ √2 ≤ 1 + γ / 2`, since `⟨v, u⟩ / ‖u‖` is a
  standard Gaussian and `E exp(Z² / 4) = √2`.
-/

@[expose] public section

namespace BHJK25.Spectral.TailAux

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

/-- The Lebesgue integral of a product of functions of the coordinates, under a product of
copies of a probability measure. -/
theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, ∏ i, f (x i) ∂(Measure.pi fun _ : ι ↦ μ) = (∫⁻ x, f x ∂μ) ^ Fintype.card ι := by
  have h := lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
    (fun i (x : ι → E) ↦ f (x i))
    (iIndepFun_pi (μ := fun _ : ι ↦ μ) (X := fun _ ↦ f) fun _ ↦ hf.aemeasurable)
    fun i ↦ hf.comp (measurable_pi_apply i)
  rw [h]
  simp_rw [(measurePreserving_eval (fun _ : ι ↦ μ) _).lintegral_comp hf]
  rw [Finset.prod_const, Finset.card_univ]

/-- `E exp(Z² / 4) = √2`, as a Lebesgue integral. -/
theorem lintegral_exp_sq_div_four :
    ∫⁻ x, ENNReal.ofReal (Real.exp (x ^ 2 / 4)) ∂(gaussianReal 0 1) = ENNReal.ofReal √2 := by
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_exp_sq_div_four]
  · exact Integrable.of_integral_ne_zero (by rw [integral_exp_sq_div_four]; positivity)
  · exact ae_of_all _ fun x ↦ (Real.exp_pos _).le

/-- `E exp(-Z² / 2) = 1 / √2`, as a Lebesgue integral. -/
theorem lintegral_exp_neg_sq_div_two :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-(x ^ 2 / 2))) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (1 / √2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal, integral_exp_neg_sq_div_two]
  · exact Integrable.of_integral_ne_zero (by rw [integral_exp_neg_sq_div_two]; positivity)
  · exact ae_of_all _ fun x ↦ (Real.exp_pos _).le

/-- `E exp(c Z² / 4) ≤ E exp(Z² / 4) = √2` for `c ≤ 1`. -/
theorem lintegral_exp_mul_sq_le {c : ℝ} (hc : c ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * x ^ 2 / 4)) ∂(gaussianReal 0 1) ≤ ENNReal.ofReal √2 := by
  rw [← lintegral_exp_sq_div_four]
  refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have := sq_nonneg x
  have : c * x ^ 2 ≤ x ^ 2 := by nlinarith
  linarith

/-- `E exp(-‖u‖² / 2) = 2^(-n/2)` for a standard Gaussian vector `u`. -/
theorem lintegral_gaussVec_exp_neg (n : ℕ) :
    ∫⁻ u, ENNReal.ofReal (Real.exp (-(u ⬝ᵥ u) / 2)) ∂(gaussVec n) =
      ENNReal.ofReal (1 / √2) ^ n := by
  have h : ∀ u : Fin n → ℝ, ENNReal.ofReal (Real.exp (-(u ⬝ᵥ u) / 2)) =
      ∏ i, ENNReal.ofReal (Real.exp (-(u i ^ 2 / 2))) := by
    intro u
    rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ (Real.exp_pos _).le, ← Real.exp_sum]
    congr 1
    simp only [dotProduct, sq, ← Finset.sum_div, Finset.sum_neg_distrib, neg_div]
  simp_rw [h]
  rw [gaussVec, lintegral_pi_prod (f := fun x ↦ ENNReal.ofReal (Real.exp (-(x ^ 2 / 2)))) _
    (by fun_prop), lintegral_exp_neg_sq_div_two, Fintype.card_fin]

/-- `E exp(c ⟨v, u⟩² / (4 ‖u‖²)) ≤ √2` for `c ≤ 1`, a fixed vector `u` and a standard Gaussian
vector `v`: `⟨v, u⟩ / ‖u‖` is a standard Gaussian. -/
theorem lintegral_cross_le_sqrt_two {n : ℕ} (u : Fin n → ℝ) {c : ℝ} (hc : c ≤ 1) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (c * (v ⬝ᵥ u) ^ 2 / (4 * (u ⬝ᵥ u)))) ∂(gaussVec n) ≤
      ENNReal.ofReal √2 := by
  have hs : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  rcases hs.eq_or_lt with h | h
  · simp only [← h, mul_zero, div_zero, Real.exp_zero, ENNReal.ofReal_one, lintegral_const,
      measure_univ, mul_one]
    exact ENNReal.one_le_ofReal.2 (Real.le_sqrt' one_pos |>.2 (by norm_num))
  · set s := u ⬝ᵥ u
    set w : Fin n → ℝ := fun i ↦ u i / √s
    have hw : ∑ i, w i ^ 2 = 1 := by
      have : ∑ i, w i ^ 2 = (∑ i, u i * u i) / s := by
        simp only [w, sq, div_mul_div_comm, Real.mul_self_sqrt h.le, Finset.sum_div]
      rw [this]
      exact div_self h.ne'
    have hv : ∀ v : Fin n → ℝ, c * (v ⬝ᵥ u) ^ 2 / (4 * s) = c * (∑ i, w i * v i) ^ 2 / 4 := by
      intro v
      have : ∑ i, w i * v i = (v ⬝ᵥ u) / √s := by
        simp only [w, dotProduct, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      rw [this, div_pow, Real.sq_sqrt h.le]
      ring
    simp_rw [hv]
    rw [← lintegral_map (f := fun x ↦ ENNReal.ofReal (Real.exp (c * x ^ 2 / 4))) (by fun_prop)
      (by fun_prop), gaussVec_map_inner, hw, Real.toNNReal_one]
    exact lintegral_exp_mul_sq_le hc

/-- `E exp(|λ| ⟨v, u⟩² / (4 ‖u‖²)) ≤ 1 - γ + γ √2 ≤ 1 + γ / 2` for a fixed vector `u`, `λ ∼ μ_γ`
and an independent standard Gaussian vector `v`. -/
theorem lintegral_comp_le {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) {n : ℕ} (u : Fin n → ℝ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (|p.1| * (p.2 ⬝ᵥ u) ^ 2 / (4 * (u ⬝ᵥ u))))
      ∂((eigLaw γ).prod (gaussVec n)) ≤ ENNReal.ofReal (1 + γ / 2) := by
  rw [lintegral_prod _ (by fun_prop), eigLaw, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac]
  simp only [abs_zero, zero_mul, zero_div, Real.exp_zero, ENNReal.ofReal_one, lintegral_const,
    measure_univ, mul_one, smul_eq_mul]
  have hI : ∫⁻ x in Set.Icc (-1 : ℝ) 0, ∫⁻ v, ENNReal.ofReal
      (Real.exp (|x| * (v ⬝ᵥ u) ^ 2 / (4 * (u ⬝ᵥ u)))) ∂(gaussVec n) ≤ ENNReal.ofReal √2 := by
    calc _ ≤ ∫⁻ _ in Set.Icc (-1 : ℝ) 0, ENNReal.ofReal √2 :=
          setLIntegral_mono measurable_const fun x hx ↦
            lintegral_cross_le_sqrt_two u (abs_le.2 ⟨hx.1, hx.2.trans zero_le_one⟩)
      _ = ENNReal.ofReal √2 := by rw [setLIntegral_const, Real.volume_Icc]; norm_num
  have hsqrt : √2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  calc _ ≤ ENNReal.ofReal (1 - γ) + ENNReal.ofReal γ * ENNReal.ofReal √2 := by gcongr
    _ = ENNReal.ofReal (1 - γ + γ * √2) := by
      rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_add (by linarith) (by positivity)]
    _ ≤ ENNReal.ofReal (1 + γ / 2) := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Markov's inequality in the form used here: if `a μ(A) ≤ b` with `a > 0`, then
`μ(A) ≤ b / a`. -/
theorem measure_le_of_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {A : Set α}
    {a b : ℝ} (ha : 0 < a) (h : ENNReal.ofReal a * μ A ≤ ENNReal.ofReal b) :
    μ A ≤ ENNReal.ofReal (b / a) := by
  rw [ENNReal.ofReal_div_of_pos ha, ENNReal.le_div_iff_mul_le (by simp [ha]) (by simp), mul_comm]
  exact h

/-- `‖u‖² < n / 2` with probability at most `(e^(1/4) / √2)^n` for a standard Gaussian vector
`u ∈ ℝ^n`: Markov's inequality for `exp(-‖u‖² / 2)`. -/
theorem gaussVec_norm_lt (n : ℕ) :
    gaussVec n {u | u ⬝ᵥ u < n / 2} ≤ ENNReal.ofReal ((Real.exp (1 / 4) / √2) ^ n) := by
  have hM := mul_meas_ge_le_lintegral₀
    (f := fun u ↦ ENNReal.ofReal (Real.exp (-(u ⬝ᵥ u) / 2))) (μ := gaussVec n)
    (by fun_prop) (ENNReal.ofReal (Real.exp (-(n / 4))))
  rw [lintegral_gaussVec_exp_neg, ← ENNReal.ofReal_pow (by positivity)] at hM
  have hsub : {u : Fin n → ℝ | u ⬝ᵥ u < n / 2} ⊆
      {u | ENNReal.ofReal (Real.exp (-(n / 4))) ≤ ENNReal.ofReal (Real.exp (-(u ⬝ᵥ u) / 2))} :=
    fun u hu ↦ by
      have hu' : u ⬝ᵥ u < n / 2 := hu
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))
  refine (measure_mono hsub).trans ((measure_le_of_mul_le (Real.exp_pos _) hM).trans
    (le_of_eq ?_))
  congr 1
  rw [Real.exp_neg, div_inv_eq_mul, div_pow, div_pow, one_pow, ← Real.exp_nat_mul]
  ring_nf

end BHJK25.Spectral.TailAux
