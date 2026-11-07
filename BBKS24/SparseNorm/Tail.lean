module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProductMeasure

/-!
# Means and tail bounds on finite probability spaces

Tools for `BBKS24.SparseNorm.sparse_norm_bound`, on finite types with the discrete σ-algebra.

* `BBKS24.SparseNorm.mean μ h = ∑ₓ μ{x} h(x)`, the integral as a finite sum
  (`BBKS24.SparseNorm.integral_eq_mean`), with its linearity and monotonicity.
* **Chernoff's bound, multiplicative upper tail** (`BBKS24.SparseNorm.chernoff`): for `q`
  independent samples `g j` of `μ` and `0 ≤ h ≤ a`,
  `P(∑ⱼ h(g j) ≥ q ((1 + ε) E h + α)) ≤ exp(-q ε α / a)` for `0 ≤ ε ≤ 1`.
* **Hoeffding's bound** for averages of independent samples
  (`BBKS24.SparseNorm.hoeffding_pi`), from Mathlib's.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real

namespace BBKS24.SparseNorm

/-! ### Means on finite types -/

section Mean

variable {X : Type*} [Fintype X] [MeasurableSpace X] (μ : Measure X)

/-- The mean `∑ₓ μ{x} h(x)` of `h` under a measure `μ` on a finite type. -/
noncomputable def mean (h : X → ℝ) : ℝ := ∑ x, μ.real {x} * h x

theorem integral_eq_mean [MeasurableSingletonClass X] [IsFiniteMeasure μ] (h : X → ℝ) :
    ∫ x, h x ∂μ = mean μ h := by
  rw [integral_fintype Integrable.of_finite]
  rfl

theorem mean_add (h₁ h₂ : X → ℝ) :
    mean μ (fun x ↦ h₁ x + h₂ x) = mean μ h₁ + mean μ h₂ := by
  simp [mean, mul_add, sum_add_distrib]

theorem mean_sub (h₁ h₂ : X → ℝ) :
    mean μ (fun x ↦ h₁ x - h₂ x) = mean μ h₁ - mean μ h₂ := by
  simp [mean, mul_sub, sum_sub_distrib]

theorem mean_const_mul (c : ℝ) (h : X → ℝ) : mean μ (fun x ↦ c * h x) = c * mean μ h := by
  simp only [mean, mul_sum]
  exact sum_congr rfl fun x _ ↦ by ring

theorem mean_finsetSum {κ : Type*} (s : Finset κ) (h : κ → X → ℝ) :
    mean μ (fun x ↦ ∑ i ∈ s, h i x) = ∑ i ∈ s, mean μ (h i) := by
  simp only [mean, mul_sum]
  exact sum_comm

theorem mean_mono {h₁ h₂ : X → ℝ} (hle : ∀ x, h₁ x ≤ h₂ x) : mean μ h₁ ≤ mean μ h₂ :=
  sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hle x) measureReal_nonneg

theorem mean_nonneg {h : X → ℝ} (h0 : ∀ x, 0 ≤ h x) : 0 ≤ mean μ h :=
  sum_nonneg fun x _ ↦ mul_nonneg measureReal_nonneg (h0 x)

theorem mean_const [MeasurableSingletonClass X] [IsProbabilityMeasure μ] (c : ℝ) :
    mean μ (fun _ ↦ c) = c := by
  rw [mean, ← sum_mul, sum_measureReal_singleton, coe_univ, probReal_univ, one_mul]

theorem mean_sub_const [MeasurableSingletonClass X] [IsProbabilityMeasure μ] (h : X → ℝ)
    (c : ℝ) : mean μ (fun x ↦ h x - c) = mean μ h - c :=
  (mean_sub μ h fun _ ↦ c).trans (by rw [mean_const])

theorem measureReal_eq_mean [MeasurableSingletonClass X] [IsFiniteMeasure μ] (p : X → Prop)
    [DecidablePred p] :
    μ.real {x | p x} = mean μ (fun x ↦ if p x then 1 else 0) := by
  have : {x | p x} = ((univ.filter p : Finset X) : Set X) := by ext; simp
  rw [this, ← sum_measureReal_singleton, mean, sum_filter]
  exact sum_congr rfl fun x _ ↦ by split_ifs <;> simp

theorem mean_le_of_le [MeasurableSingletonClass X] [IsProbabilityMeasure μ] {h : X → ℝ} {c : ℝ}
    (hle : ∀ x, h x ≤ c) :
    mean μ h ≤ c :=
  (mean_mono μ hle).trans_eq (mean_const μ c)

theorem abs_mean_le [MeasurableSingletonClass X] [IsProbabilityMeasure μ] {h : X → ℝ} {c : ℝ}
    (hle : ∀ x, |h x| ≤ c) :
    |mean μ h| ≤ c := by
  rw [abs_le]
  constructor
  · rw [← mean_const μ (-c)]
    exact mean_mono μ fun x ↦ neg_le_of_abs_le (hle x)
  · exact mean_le_of_le μ fun x ↦ le_of_abs_le (hle x)

theorem exists_le_mean [MeasurableSingletonClass X] [IsProbabilityMeasure μ] (h : X → ℝ) :
    ∃ x, h x ≤ mean μ h := by
  obtain ⟨x, hx⟩ := exists_le_integral (μ := μ) (Integrable.of_finite (f := h))
  exact ⟨x, by rwa [integral_eq_mean] at hx⟩

/-- Means under two measures commute. -/
theorem mean_comm {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    (ν : Measure Y) (h : X → Y → ℝ) :
    mean μ (fun x ↦ mean ν (h x)) = mean ν (fun y ↦ mean μ (fun x ↦ h x y)) := by
  simp only [mean, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun y _ ↦ sum_congr rfl fun x _ ↦ by ring

end Mean

/-! ### Products of a measure -/

section Product

variable {X κ : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- The integral of a function of one coordinate under the product measure. -/
theorem integral_infinitePi_eval {f : X → ℝ} (hf : Measurable f) (j : κ) :
    ∫ g, f (g j) ∂(Measure.infinitePi fun _ : κ ↦ μ) = ∫ x, f x ∂μ := by
  rw [← integral_map (measurable_pi_apply j).aemeasurable hf.aestronglyMeasurable,
    Measure.infinitePi_map_eval]

/-- The coordinates of the product measure are independent. -/
theorem iIndepFun_eval {f : X → ℝ} (hf : Measurable f) :
    iIndepFun (fun j (g : κ → X) ↦ f (g j)) (Measure.infinitePi fun _ : κ ↦ μ) :=
  iIndepFun_infinitePi (P := fun _ ↦ μ) (X := fun _ ↦ f) fun _ ↦ hf

/-- **Hoeffding's bound** for independent samples of a centred variable bounded by `B`:
`P(∑ⱼ Y(g j) ≥ c) ≤ exp(-c² / (2 |κ| B²))`. -/
theorem hoeffding_pi [Fintype κ] {Y : X → ℝ} (hY : Measurable Y) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |Y x| ≤ B) (hc : ∫ x, Y x ∂μ = 0) {c : ℝ} (hc0 : 0 ≤ c) :
    (Measure.infinitePi fun _ : κ ↦ μ).real {g | c ≤ ∑ j, Y (g j)} ≤
      exp (-c ^ 2 / (2 * (Fintype.card κ * B ^ 2))) := by
  set P := Measure.infinitePi fun _ : κ ↦ μ
  have hsub : ∀ j ∈ (univ : Finset κ),
      HasSubgaussianMGF (fun g : κ → X ↦ Y (g j)) ((‖B - (-B)‖₊ / 2) ^ 2) P := fun j _ ↦
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hY.comp (measurable_pi_apply j)).aemeasurable
      (ae_of_all _ fun g ↦ abs_le.1 (hb (g j)))
      (by rw [integral_infinitePi_eval μ hY j, hc])
  refine (HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun (iIndepFun_eval μ hY) hsub
    hc0).trans_eq ?_
  have : ((∑ _j : κ, (‖B - (-B)‖₊ / 2) ^ 2 : NNReal) : ℝ) = Fintype.card κ * B ^ 2 := by
    rw [sum_const, nsmul_eq_mul, card_univ]
    push_cast
    rw [Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by linarith)]
    ring
  rw [this]

end Product

/-! ### Chernoff's bound -/

section Chernoff

variable {X R : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype R]

/-- `exp u ≤ 1 + u (1 + ε)` for `0 ≤ u ≤ ε ≤ 1`. -/
theorem exp_le_one_add_mul {u ε : ℝ} (hu : 0 ≤ u) (huε : u ≤ ε) (hε : ε ≤ 1) :
    exp u ≤ 1 + u * (1 + ε) := by
  have h := abs_exp_sub_one_sub_id_le (x := u) (by rw [abs_of_nonneg hu]; linarith)
  have h2 : u ^ 2 ≤ u * ε := by nlinarith
  linarith [le_of_abs_le h]

/-- **Chernoff's bound**, multiplicative upper tail: for `q` independent samples `g j` of `μ`,
a function `0 ≤ h ≤ a`, `0 ≤ ε ≤ 1` and `α`,
`P(∑ⱼ h(g j) ≥ q ((1 + ε) E h + α)) ≤ exp(-q ε α / a)`. -/
theorem chernoff (μ : Measure X) [IsProbabilityMeasure μ] {h : X → ℝ} {a ε α : ℝ}
    (ha : 0 < a) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h0 : ∀ x, 0 ≤ h x) (hle : ∀ x, h x ≤ a) :
    (Measure.infinitePi fun _ : R ↦ μ).real
        {g | Fintype.card R * ((1 + ε) * mean μ h + α) ≤ ∑ j, h (g j)} ≤
      exp (-(Fintype.card R * ε * α / a)) := by
  set P := Measure.infinitePi fun _ : R ↦ μ
  set l := ε / a with hl
  have hl0 : 0 ≤ l := div_nonneg hε ha.le
  have hmeas : ∀ j : R, Measurable fun g : R → X ↦ h (g j) :=
    fun j ↦ (Measurable.of_discrete (f := h)).comp (measurable_pi_apply j)
  -- The moment generating function of one sample.
  have hmgf1 : ∀ j, mgf (fun g : R → X ↦ h (g j)) P l ≤ exp (l * (1 + ε) * mean μ h) := by
    intro j
    rw [mgf, integral_infinitePi_eval μ (Measurable.of_discrete (f := fun x ↦ exp (l * h x))) j,
      integral_eq_mean]
    calc mean μ (fun x ↦ exp (l * h x)) ≤ mean μ (fun x ↦ 1 + l * (1 + ε) * h x) := by
          refine mean_mono μ fun x ↦ ?_
          have hlh : l * h x ≤ ε := by
            calc l * h x ≤ l * a := mul_le_mul_of_nonneg_left (hle x) hl0
              _ = ε := by rw [hl, div_mul_cancel₀ _ ha.ne']
          have := exp_le_one_add_mul (mul_nonneg hl0 (h0 x)) hlh hε1
          linarith
      _ = 1 + l * (1 + ε) * mean μ h := by
          rw [mean_add, mean_const, mean_const_mul]
      _ ≤ exp (l * (1 + ε) * mean μ h) := by
          have := add_one_le_exp (l * (1 + ε) * mean μ h)
          linarith
  have hsum : mgf (fun g : R → X ↦ ∑ j, h (g j)) P l = ∏ j, mgf (fun g : R → X ↦ h (g j)) P l := by
    have := (iIndepFun_eval μ (Measurable.of_discrete (f := h))).mgf_sum (t := l) hmeas univ
    convert this using 2
    ext g
    simp [Finset.sum_apply]
  refine (measure_ge_le_exp_mul_mgf _ hl0 Integrable.of_finite).trans ?_
  rw [hsum]
  calc exp (-l * (Fintype.card R * ((1 + ε) * mean μ h + α))) *
        ∏ j, mgf (fun g : R → X ↦ h (g j)) P l
      ≤ exp (-l * (Fintype.card R * ((1 + ε) * mean μ h + α))) *
          ∏ _j : R, exp (l * (1 + ε) * mean μ h) := by
        gcongr with j
        · exact fun j _ ↦ mgf_nonneg
        · exact hmgf1 j
    _ = exp (-(Fintype.card R * ε * α / a)) := by
        rw [prod_const, card_univ, ← exp_nat_mul, ← exp_add]
        congr 1
        rw [hl]
        field_simp
        ring

end Chernoff

end BBKS24.SparseNorm
