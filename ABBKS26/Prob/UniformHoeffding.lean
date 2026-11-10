module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Hoeffding's inequality for counts in an iid sample, and the norm tail of a Gaussian

For an iid sample `g : Fin m → E` from a probability measure `μ` (the law
`Measure.pi fun _ ↦ μ`) and a measurable set `S ⊆ E`, the number of sample points in `S` is
`∑ l, S.indicator 1 (g l)`.

* `ABBKS26.Unif.measure_upperBad_le`, `ABBKS26.Unif.measure_lowerBad_le`: Hoeffding's inequality,
  `P(#{l : g l ∈ S} ≥ (μ(S) + t) m) ≤ exp(-2 m t²)`, and the same for `≤ (μ(S) - t) m`.
* `ABBKS26.Unif.integral_norm_sq_stdGaussian`: `E ‖G‖² = d` for the standard Gaussian `G` on
  `EuclideanSpace ℝ (Fin d)`.
* `ABBKS26.Unif.measureReal_norm_gt_le`: Markov's inequality, `P(‖G‖ > R) ≤ d / R²`.
-/

@[expose] public section

namespace ABBKS26.Unif

open MeasureTheory ProbabilityTheory Real

variable {E : Type*} {m : ℕ}

/-- The number of points of the sample `g` in `S`, as a real number. -/
noncomputable def indCount (S : Set E) (g : Fin m → E) : ℝ :=
  ∑ l, S.indicator 1 (g l)

theorem indCount_eq_card (S : Set E) [DecidablePred (· ∈ S)] (g : Fin m → E) :
    indCount S g = ((Finset.univ.filter fun l ↦ g l ∈ S).card : ℝ) := by
  rw [indCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  simp only [Set.indicator_apply]
  split_ifs <;> simp

theorem indCount_compl (S : Set E) (g : Fin m → E) : indCount Sᶜ g = m - indCount S g := by
  rw [eq_sub_iff_add_eq, indCount, indCount, ← Finset.sum_add_distrib]
  have h : ∀ l, Sᶜ.indicator (1 : E → ℝ) (g l) + S.indicator 1 (g l) = 1 := by
    intro l
    by_cases hl : g l ∈ S <;> simp [hl]
  simp [h]

variable [MeasurableSpace E]

theorem measurable_indCount {S : Set E} (hS : MeasurableSet S) :
    Measurable fun g : Fin m → E ↦ indCount S g :=
  Finset.measurable_sum _ fun l _ ↦ (measurable_const.indicator hS).comp (measurable_pi_apply l)

variable {μ : Measure E}

variable (μ) in
/-- The samples with at least `(μ(S) + t) m` points in `S`. -/
def upperBad (S : Set E) (t : ℝ) : Set (Fin m → E) :=
  {g | (μ.real S + t) * m ≤ indCount S g}

variable (μ) in
/-- The samples with at most `(μ(S) - t) m` points in `S`. -/
def lowerBad (S : Set E) (t : ℝ) : Set (Fin m → E) :=
  {g | indCount S g ≤ (μ.real S - t) * m}

theorem measurableSet_upperBad {S : Set E} (hS : MeasurableSet S) (t : ℝ) :
    MeasurableSet (upperBad (m := m) μ S t) :=
  measurableSet_le measurable_const (measurable_indCount hS)

theorem measurableSet_lowerBad {S : Set E} (hS : MeasurableSet S) (t : ℝ) :
    MeasurableSet (lowerBad (m := m) μ S t) :=
  measurableSet_le (measurable_indCount hS) measurable_const

theorem lt_of_notMem_upperBad {S : Set E} {t : ℝ} {g : Fin m → E} (hg : g ∉ upperBad μ S t) :
    indCount S g < (μ.real S + t) * m :=
  not_le.1 hg

theorem lt_of_notMem_lowerBad {S : Set E} {t : ℝ} {g : Fin m → E} (hg : g ∉ lowerBad μ S t) :
    (μ.real S - t) * m < indCount S g :=
  not_le.1 hg

variable [IsProbabilityMeasure μ]

/-- **Hoeffding's inequality** for the number of sample points in a measurable set. -/
theorem measureReal_upperBad_le {S : Set E} (hS : MeasurableSet S) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin m ↦ μ).real (upperBad μ S t) ≤ exp (-2 * m * t ^ 2) := by
  set P := Measure.pi fun _ : Fin m ↦ μ
  set f : E → ℝ := S.indicator 1 with hf
  have hfm : Measurable f := measurable_const.indicator hS
  set X : Fin m → (Fin m → E) → ℝ := fun l g ↦ f (g l) - μ.real S with hX
  have hind : iIndepFun X P :=
    iIndepFun_pi (X := fun _ x ↦ f x - μ.real S) fun _ ↦ (hfm.sub_const _).aemeasurable
  have hint : ∀ l, ∫ g, f (g l) ∂P = μ.real S := by
    intro l
    rw [integral_comp_eval hfm.aestronglyMeasurable, hf, integral_indicator_one hS]
  have hsub : ∀ l ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (X l) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro l _
    have hb : ∀ᵐ g ∂P, f (g l) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ae_of_all _ fun g ↦ ?_
      by_cases hg : g l ∈ S <;> simp [hf, hg]
    have h := hasSubgaussianMGF_of_mem_Icc
      ((hfm.comp (measurable_pi_apply l)).aemeasurable) hb
    simp only [Function.comp_def] at h
    rw [hint l] at h
    exact h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind hsub
    (mul_nonneg ht (Nat.cast_nonneg m))
  have hset : upperBad μ S t = {g | t * m ≤ ∑ l, X l g} := by
    ext g
    simp only [upperBad, indCount, Set.mem_ofPred_eq, hX, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← hf]
    constructor <;> intro h <;> linarith
  rw [hset]
  refine h.trans_eq ?_
  congr 1
  simp only [sub_zero, nnnorm_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · have : (m : ℝ) ≠ 0 := by positivity
    field_simp

/-- **Hoeffding's inequality**, lower tail. -/
theorem measureReal_lowerBad_le {S : Set E} (hS : MeasurableSet S) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin m ↦ μ).real (lowerBad μ S t) ≤ exp (-2 * m * t ^ 2) := by
  have hset : lowerBad (m := m) μ S t = upperBad μ Sᶜ t := by
    ext g
    simp only [lowerBad, upperBad, Set.mem_ofPred_eq, indCount_compl,
      probReal_compl_eq_one_sub hS]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact measureReal_upperBad_le hS.compl ht

theorem measure_upperBad_le {S : Set E} (hS : MeasurableSet S) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin m ↦ μ) (upperBad μ S t) ≤ ENNReal.ofReal (exp (-2 * m * t ^ 2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_upperBad_le hS ht)

theorem measure_lowerBad_le {S : Set E} (hS : MeasurableSet S) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun _ : Fin m ↦ μ) (lowerBad μ S t) ≤ ENNReal.ofReal (exp (-2 * m * t ^ 2)) := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_lowerBad_le hS ht)

/-! ### The norm of a standard Gaussian vector -/

variable {d : ℕ}

theorem integral_sq_gaussianReal : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_eq_integral (μ := gaussianReal 0 1) (X := id) aemeasurable_id
  rw [variance_id_gaussianReal] at h
  simpa [integral_id_gaussianReal] using h.symm

theorem integrable_sq_gaussianReal : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal 2).integrable_sq

/-- `E ‖G‖² = d` for a standard Gaussian vector `G` in `ℝ^d`. -/
theorem integral_norm_sq_stdGaussian :
    ∫ x, ‖x‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = d := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [EuclideanSpace.real_norm_sq_eq]
  have hi : ∀ i : Fin d, ∫ x : Fin d → ℝ, x i ^ 2 ∂(Measure.pi fun _ ↦ gaussianReal 0 1) = 1 :=
    fun i ↦ (integral_comp_eval (X := fun _ ↦ ℝ) (μ := fun _ ↦ gaussianReal 0 1)
      (f := fun y : ℝ ↦ y ^ 2) (i := i)
      integrable_sq_gaussianReal.aestronglyMeasurable).trans integral_sq_gaussianReal
  rw [integral_finsetSum _ fun i _ ↦
    integrable_comp_eval (X := fun _ ↦ ℝ) (μ := fun _ ↦ gaussianReal 0 1)
      (f := fun y : ℝ ↦ y ^ 2) (i := i) integrable_sq_gaussianReal]
  simp [hi]

theorem integrable_norm_sq_stdGaussian :
    Integrable (fun x ↦ ‖x‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rw [← map_pi_eq_stdGaussian, integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, EuclideanSpace.real_norm_sq_eq]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_comp_eval (X := fun _ ↦ ℝ) (μ := fun _ ↦ gaussianReal 0 1)
      (f := fun y : ℝ ↦ y ^ 2) (i := i) integrable_sq_gaussianReal

/-- Markov's inequality: `P(‖G‖ > R) ≤ d / R²` for a standard Gaussian vector `G` in `ℝ^d`. -/
theorem measureReal_norm_gt_le {R : ℝ} (hR : 0 < R) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).real {x | R < ‖x‖} ≤ d / R ^ 2 := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
    (ae_of_all _ fun x ↦ by positivity) integrable_norm_sq_stdGaussian (R ^ 2)
  rw [integral_norm_sq_stdGaussian] at h
  have hsub : {x : EuclideanSpace ℝ (Fin d) | R < ‖x‖} ⊆ {x | R ^ 2 ≤ ‖x‖ ^ 2} := by
    intro x (hx : R < ‖x‖)
    change R ^ 2 ≤ ‖x‖ ^ 2
    nlinarith
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact le_trans (mul_le_mul_of_nonneg_left (measureReal_mono hsub (measure_ne_top _ _))
    (by positivity)) h

end ABBKS26.Unif
