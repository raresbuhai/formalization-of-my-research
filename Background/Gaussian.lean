module

public import TauCeti.Probability.Distributions.Gaussian.OwensT
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Gaussian facts

* `Gaussian.prob_quadrant`: for independent standard Gaussians `X, Z` and `s > 0`,
  `P(X ≤ 0, ρ X + s Z ≤ 0) = 1/4 + arctan (ρ / s) / (2π)`, from Owen's `T` function
  (TauCeti): `P = ∫_{(-∞, 0]} φ(x) Φ(-(ρ/s) x) dx = (Φ(0) - 2 T(0, -ρ/s)) / 2`, and
  `T(0, a) = arctan a / (2π)`.
-/

@[expose] public section

namespace Gaussian

open MeasureTheory ProbabilityTheory Real Set

/-- **The orthant probability.** For independent standard Gaussians `X, Z` and `s > 0`,
`P(X ≤ 0, ρ X + s Z ≤ 0) = 1/4 + arctan (ρ / s) / (2π)`. -/
theorem prob_quadrant {ρ s : ℝ} (hs : 0 < s) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | p.1 ≤ 0 ∧ ρ * p.1 + s * p.2 ≤ 0} = 1 / 4 + arctan (ρ / s) / (2 * π) := by
  set S := {p : ℝ × ℝ | p.1 ≤ 0 ∧ ρ * p.1 + s * p.2 ≤ 0} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le (f := fun p : ℝ × ℝ ↦ ρ * p.1 + s * p.2) (by fun_prop) measurable_const)
  have hint : Integrable (S.indicator (fun _ ↦ (1 : ℝ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS]
  change ∫ p, S.indicator (fun _ ↦ (1 : ℝ)) p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  rw [integral_prod _ hint]
  -- The inner integral: `P(Z ≤ -(ρ/s) x)` when `x ≤ 0`, and `0` otherwise.
  have hin : ∀ x : ℝ, ∫ z, S.indicator (fun _ ↦ (1 : ℝ)) (x, z) ∂(gaussianReal 0 1) =
      (Iic 0).indicator (fun x ↦ cdf (gaussianReal 0 1) (-(ρ / s) * x)) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
      have key : ∀ z : ℝ, ρ * x + s * z ≤ 0 ↔ z ≤ -(ρ / s) * x := by
        intro z
        rw [show -(ρ / s) * x = -(ρ * x) / s by ring, le_div_iff₀ hs]
        constructor <;> intro h <;> linarith
      have : (fun z ↦ S.indicator (fun _ ↦ (1 : ℝ)) (x, z)) = (Iic (-(ρ / s) * x)).indicator 1 := by
        funext z
        simp only [hSdef, indicator, mem_ofPred_eq, mem_Iic, key, hx, true_and, Pi.one_apply]
      rw [this, integral_indicator_one measurableSet_Iic, cdf_eq_real]
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx)]
      have : (fun z ↦ S.indicator (fun _ ↦ (1 : ℝ)) (x, z)) = fun _ ↦ 0 := by
        funext z
        simp only [hSdef, indicator, mem_ofPred_eq, hx, false_and, ite_false]
      rw [this, integral_zero]
  simp_rw [hin]
  -- The outer integral, through the Gaussian density and Owen's `T` function.
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : (fun x : ℝ ↦ gaussianPDFReal 0 1 x •
      (Iic 0).indicator (fun x ↦ cdf (gaussianReal 0 1) (-(ρ / s) * x)) x) =
      (Iic 0).indicator
        (fun t ↦ gaussianPDFReal 0 1 t * cdf (gaussianReal 0 1) (-(ρ / s) * t)) := by
    funext x
    by_cases hx : x ≤ 0
    · simp [indicator, hx]
    · simp [indicator, hx]
  rw [h1, integral_indicator measurableSet_Iic]
  have h2 := TauCeti.Probability.integral_Iic_two_mul_gaussianPDFReal_mul_cdf_gaussianReal
    (-(ρ / s)) 0
  rw [TauCeti.Probability.cdf_gaussianReal_self 0 (by norm_num), Real.owensT_zero_left,
    arctan_neg] at h2
  have h3 : ∫ t in Iic 0, 2 * gaussianPDFReal 0 1 t * cdf (gaussianReal 0 1) (-(ρ / s) * t) =
      2 * ∫ t in Iic 0, gaussianPDFReal 0 1 t * cdf (gaussianReal 0 1) (-(ρ / s) * t) := by
    rw [← integral_const_mul]
    congr 1
    funext t
    ring
  rw [h3] at h2
  have hπ := pi_pos
  field_simp at h2 ⊢
  linarith

/-! ### Lines are null -/

instance : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero

/-- A line `a x + b z = 0` through the origin is null for two independent standard Gaussians. -/
theorem prod_line_null {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)) {p : ℝ × ℝ | a * p.1 + b * p.2 = 0} = 0 := by
  have hS : MeasurableSet {p : ℝ × ℝ | a * p.1 + b * p.2 = 0} :=
    measurableSet_eq_fun (f := fun p : ℝ × ℝ ↦ a * p.1 + b * p.2) (by fun_prop) measurable_const
  by_cases hb : b = 0
  · have ha : a ≠ 0 := h.resolve_right (not_not.2 hb)
    have : {p : ℝ × ℝ | a * p.1 + b * p.2 = 0} = {0} ×ˢ univ := by
      ext p
      simp [hb, ha]
    rw [this, Measure.prod_prod, measure_singleton, zero_mul]
  · rw [Measure.measure_prod_null hS]
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | a * p.1 + b * p.2 = 0} = {-(a * x) / b} := by
      ext z
      simp only [mem_preimage, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · intro hz
        field_simp
        linarith
      · intro hz
        rw [hz]
        field_simp
        ring
    simp [this]

/-! ### The standard bivariate Gaussian with correlation `ρ` -/

/-- The standard bivariate Gaussian with correlation `ρ ∈ [-1, 1]`: the law of
`(X, ρ X + √(1 - ρ²) Z)` for independent standard Gaussians `X, Z`. -/
noncomputable def corrPair (ρ : ℝ) : Measure (ℝ × ℝ) :=
  ((gaussianReal 0 1).prod (gaussianReal 0 1)).map fun p ↦ (p.1, ρ * p.1 + √(1 - ρ ^ 2) * p.2)

theorem measurable_corrPairMap (ρ : ℝ) :
    Measurable fun p : ℝ × ℝ ↦ (p.1, ρ * p.1 + √(1 - ρ ^ 2) * p.2) := by fun_prop

instance (ρ : ℝ) : IsProbabilityMeasure (corrPair ρ) := by
  rw [corrPair]
  infer_instance

/-- `P(X = 0) = 0` and `P(Y = 0) = 0` under the bivariate Gaussian, for `ρ ∈ [-1, 1]`. -/
theorem corrPair_axes_null (ρ : ℝ) :
    corrPair ρ {q | q.1 = 0} = 0 ∧ corrPair ρ {q | q.2 = 0} = 0 := by
  have hm := measurable_corrPairMap ρ
  constructor
  · rw [corrPair, Measure.map_apply hm (measurableSet_eq_fun measurable_fst measurable_const)]
    have := prod_line_null (a := 1) (b := 0) (Or.inl one_ne_zero)
    simpa using this
  · rw [corrPair, Measure.map_apply hm (measurableSet_eq_fun measurable_snd measurable_const)]
    have hne : ρ ≠ 0 ∨ √(1 - ρ ^ 2) ≠ 0 := by
      by_cases hρ : ρ = 0
      · right
        rw [hρ]
        simp
      · exact Or.inl hρ
    exact prod_line_null hne

/-- **The orthant probability** of the bivariate Gaussian: `P(X ≤ 0, Y ≤ 0) = 1/4 + arcsin ρ / (2π)`
for `ρ ∈ [-1, 1]`. -/
theorem corrPair_quadrant {ρ : ℝ} (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) :
    (corrPair ρ).real {q | q.1 ≤ 0 ∧ q.2 ≤ 0} = 1 / 4 + arcsin ρ / (2 * π) := by
  have hm := measurable_corrPairMap ρ
  have hQ : MeasurableSet {q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 ≤ 0} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  rw [corrPair, map_measureReal_apply hm hQ]
  change ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
    {p | p.1 ≤ 0 ∧ ρ * p.1 + √(1 - ρ ^ 2) * p.2 ≤ 0} = _
  rcases lt_or_eq_of_le h1 with h1' | rfl
  · rcases lt_or_eq_of_le h2 with h2' | rfl
    · -- `|ρ| < 1`: the orthant probability, with `arctan (ρ / √(1 - ρ²)) = arcsin ρ`.
      have hs : 0 < √(1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith)
      rw [prob_quadrant hs, ← arcsin_eq_arctan ⟨h1', h2'⟩]
    · -- `ρ = 1`: `Y = X`.
      have : {p : ℝ × ℝ | p.1 ≤ 0 ∧ 1 * p.1 + √(1 - 1 ^ 2) * p.2 ≤ 0} = Iic 0 ×ˢ univ := by
        ext p
        simp
      rw [this, measureReal_prod_prod, probReal_univ, mul_one, ← cdf_eq_real,
        TauCeti.Probability.cdf_gaussianReal_self 0 (by norm_num), arcsin_one]
      have := pi_pos
      field_simp
      ring
  · -- `ρ = -1`: `Y = -X`, and `P(X = 0) = 0`.
    have : {p : ℝ × ℝ | p.1 ≤ 0 ∧ -1 * p.1 + √(1 - (-1) ^ 2) * p.2 ≤ 0} = {0} ×ˢ univ := by
      ext p
      simp only [mem_ofPred_eq, mem_prod, mem_singleton_iff, mem_univ, and_true]
      norm_num
      constructor
      · rintro ⟨h, h'⟩
        linarith
      · intro h
        exact ⟨h.le, h.ge⟩
    rw [this, measureReal_prod_prod, probReal_univ, mul_one, arcsin_neg_one]
    simp only [measureReal_def, measure_singleton, ENNReal.toReal_zero]
    have := pi_pos
    field_simp
    ring

/-! ### Sign agreement (Sheppard's formula) -/

/-- **Sheppard's formula**: under the bivariate Gaussian with correlation `ρ ∈ [-1, 1]`, the signs
`0 ≤ X` and `0 ≤ Y` agree with probability `1/2 + arcsin ρ / π`. -/
theorem corrPair_sign_agree {ρ : ℝ} (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) :
    (corrPair ρ).real {q | (0 ≤ q.1 ↔ 0 ≤ q.2)} = 1 / 2 + arcsin ρ / π := by
  have hm := measurable_corrPairMap ρ
  obtain ⟨hX, hY⟩ := corrPair_axes_null ρ
  -- `P(0 ≤ X, 0 ≤ Y) = P(X ≤ 0, Y ≤ 0)`: the law is invariant under negation.
  have hneg : (corrPair ρ).map (fun q ↦ -q) = corrPair ρ := by
    rw [corrPair, Measure.map_map (by fun_prop) hm]
    have : (fun q : ℝ × ℝ ↦ -q) ∘ (fun p : ℝ × ℝ ↦ (p.1, ρ * p.1 + √(1 - ρ ^ 2) * p.2)) =
        (fun p : ℝ × ℝ ↦ (p.1, ρ * p.1 + √(1 - ρ ^ 2) * p.2)) ∘ (fun p : ℝ × ℝ ↦ -p) := by
      funext p
      simp only [Function.comp_apply, Prod.neg_mk, Prod.fst_neg, Prod.snd_neg]
      congr 1
      ring
    rw [this, ← Measure.map_map hm (by fun_prop)]
    congr 1
    have hn : (fun p : ℝ × ℝ ↦ -p) = Prod.map (fun x : ℝ ↦ -x) (fun x : ℝ ↦ -x) := by
      funext p
      rfl
    rw [hn, ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), gaussianReal_map_neg]
    simp
  have hQ : MeasurableSet {q : ℝ × ℝ | q.1 ≤ 0 ∧ q.2 ≤ 0} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_const)
  have hpos : (corrPair ρ).real {q | 0 ≤ q.1 ∧ 0 ≤ q.2} = 1 / 4 + arcsin ρ / (2 * π) := by
    rw [← corrPair_quadrant h1 h2, ← hneg, map_measureReal_apply (by fun_prop) hQ]
    congr 1
    ext q
    simp
  -- `P(X < 0, Y < 0) = P(X ≤ 0, Y ≤ 0)`: the axes are null.
  have hstrict : (corrPair ρ).real {q | q.1 < 0 ∧ q.2 < 0} = 1 / 4 + arcsin ρ / (2 * π) := by
    rw [← corrPair_quadrant h1 h2]
    apply measureReal_congr
    have hnull : {q : ℝ × ℝ | q.1 = 0} ∪ {q | q.2 = 0} =ᵐ[corrPair ρ] (∅ : Set (ℝ × ℝ)) := by
      rw [ae_eq_empty, measure_union_null hX hY]
    filter_upwards [hnull.mem_iff] with q hq
    simp only [mem_union, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_or] at hq
    simp only [eq_iff_iff]
    constructor
    · rintro ⟨a, b⟩
      exact ⟨a.le, b.le⟩
    · rintro ⟨a, b⟩
      exact ⟨lt_of_le_of_ne a hq.1, lt_of_le_of_ne b hq.2⟩
  -- The agreement event is the disjoint union of the two quadrants.
  have hsplit : {q : ℝ × ℝ | (0 ≤ q.1 ↔ 0 ≤ q.2)} =
      {q | 0 ≤ q.1 ∧ 0 ≤ q.2} ∪ {q | q.1 < 0 ∧ q.2 < 0} := by
    ext q
    simp only [mem_ofPred_eq, mem_union]
    constructor
    · intro h
      by_cases ha : 0 ≤ q.1
      · exact Or.inl ⟨ha, h.1 ha⟩
      · exact Or.inr ⟨not_le.1 ha, not_le.1 fun hb ↦ ha (h.2 hb)⟩
    · rintro (⟨a, b⟩ | ⟨a, b⟩)
      · exact ⟨fun _ ↦ b, fun _ ↦ a⟩
      · exact ⟨fun h ↦ absurd h (not_le.2 a), fun h ↦ absurd h (not_le.2 b)⟩
  have hdisj : Disjoint {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} {q | q.1 < 0 ∧ q.2 < 0} :=
    disjoint_left.2 fun q h h' ↦ (not_le.2 h'.1) h.1
  rw [hsplit, measureReal_union hdisj
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt measurable_snd measurable_const)), hpos, hstrict]
  have := pi_pos
  field_simp
  ring

/-! ### Inner products with a standard Gaussian vector -/

section Multivariate

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- For a unit vector `u`, `⟨u, g⟩` is a standard Gaussian. -/
theorem map_inner_stdGaussian {u : E} (hu : ‖u‖ = 1) :
    (stdGaussian E).map (fun g ↦ ⟪u, g⟫) = gaussianReal 0 1 := by
  have h : HasGaussianLaw (fun g ↦ innerSL ℝ u g) (stdGaussian E) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun (innerSL ℝ u)
  have h' := h.map_eq_gaussianReal
  simp only [innerSL_apply_apply] at h'
  rw [h']
  have hmean : ∫ g, ⟪u, g⟫ ∂(stdGaussian E) = 0 := integral_strongDual_stdGaussian (innerSL ℝ u)
  have hvar : Var[fun g ↦ ⟪u, g⟫; stdGaussian E] = 1 := by
    have := variance_dual_stdGaussian (E := E) (innerSL ℝ u)
    rw [innerSL_apply_norm, hu, one_pow] at this
    exact this
  rw [hmean, hvar]
  simp

/-- For orthonormal `u, w`, `(⟨u, g⟩, ⟨w, g⟩)` are independent standard Gaussians. -/
theorem map_inner_pair_stdGaussian {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫ = 0) :
    (stdGaussian E).map (fun g ↦ (⟪u, g⟫, ⟪w, g⟫)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have hpair : HasGaussianLaw (fun g ↦ (⟪u, g⟫, ⟪w, g⟫)) (stdGaussian E) := by
    have := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun
      ((innerSL ℝ u).prod (innerSL ℝ w))
    simpa using this
  have hcov : cov[fun g ↦ ⟪u, g⟫, fun g ↦ ⟪w, g⟫; stdGaussian E] = 0 := by
    rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      innerSL_apply_apply]
    exact huw
  have hind := hpair.indepFun_of_covariance_eq_zero hcov
  rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 hind,
    map_inner_stdGaussian hu, map_inner_stdGaussian hw]

/-- For unit vectors `u, v`, `(⟨u, g⟩, ⟨v, g⟩)` is the bivariate Gaussian with correlation
`⟨u, v⟩`. -/
theorem map_inner_unit_stdGaussian {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).map (fun g ↦ (⟪u, g⟫, ⟪v, g⟫)) = corrPair ⟪u, v⟫ := by
  set ρ := ⟪u, v⟫ with hρ
  set r := v - ρ • u with hr
  have hu2 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hv2 : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  have hr2 : ‖r‖ ^ 2 = 1 - ρ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hr, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_left, inner_smul_right, inner_smul_right, hu2, hv2,
      real_inner_comm u v, ← hρ]
    simp only [conj_trivial]
    ring
  have hsr : √(1 - ρ ^ 2) = ‖r‖ := by rw [← hr2, Real.sqrt_sq (norm_nonneg _)]
  have hinv : ∀ g : E, ⟪v, g⟫ = ρ * ⟪u, g⟫ + ⟪r, g⟫ := by
    intro g
    rw [hr, inner_sub_left, inner_smul_left]
    simp
  rw [corrPair, hsr]
  by_cases hr0 : ‖r‖ = 0
  · -- `v = ρ u`.
    have hre : r = 0 := norm_eq_zero.1 hr0
    have h1 : (fun g : E ↦ (⟪u, g⟫, ⟪v, g⟫)) = (fun x ↦ (x, ρ * x)) ∘ fun g ↦ ⟪u, g⟫ := by
      funext g
      simp [hinv g, hre]
    rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), map_inner_stdGaussian hu, hr0]
    have h2 : (fun p : ℝ × ℝ ↦ (p.1, ρ * p.1 + 0 * p.2)) = (fun x ↦ (x, ρ * x)) ∘ Prod.fst := by
      funext p
      simp
    rw [h2, ← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
    simp
  · -- `v = ρ u + ‖r‖ w` with `w = r / ‖r‖` a unit vector orthogonal to `u`.
    set w := ‖r‖⁻¹ • r with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0]
    have huw : ⟪u, w⟫ = 0 := by
      rw [hw, inner_smul_right, hr, inner_sub_right, inner_smul_right, hu2, ← hρ]
      ring
    have h1 : (fun g : E ↦ (⟪u, g⟫, ⟪v, g⟫)) =
        (fun p : ℝ × ℝ ↦ (p.1, ρ * p.1 + ‖r‖ * p.2)) ∘ fun g ↦ (⟪u, g⟫, ⟪w, g⟫) := by
      funext g
      simp only [Function.comp_apply, hinv g, hw, inner_smul_left, conj_trivial]
      congr 2
      field_simp
    rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), map_inner_pair_stdGaussian hu hwn huw]

/-- **Sheppard's formula** for a standard Gaussian vector: for unit vectors `u, v`, the signs of
`⟨u, g⟩` and `⟨v, g⟩` agree with probability `1/2 + arcsin ⟨u, v⟩ / π`. -/
theorem prob_sign_agree {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (stdGaussian E).real {g | (0 ≤ ⟪u, g⟫ ↔ 0 ≤ ⟪v, g⟫)} = 1 / 2 + arcsin ⟪u, v⟫ / π := by
  have hρ1 : -1 ≤ ⟪u, v⟫ := by
    have := abs_real_inner_le_norm u v
    rw [hu, hv, one_mul] at this
    exact (abs_le.1 this).1
  have hρ2 : ⟪u, v⟫ ≤ 1 := by
    have := real_inner_le_norm u v
    rw [hu, hv, one_mul] at this
    exact this
  rw [← corrPair_sign_agree hρ1 hρ2, ← map_inner_unit_stdGaussian hu hv,
    map_measureReal_apply (by fun_prop)]
  · rfl
  · exact measurableSet_setOfPred.2 (by fun_prop)

end Multivariate

end Gaussian
