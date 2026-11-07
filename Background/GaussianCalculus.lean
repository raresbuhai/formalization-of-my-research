module

public import Background.Gaussian
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Calculus with standard Gaussian vectors

Tools to compute with a standard Gaussian vector `g` in a finite-dimensional inner product space
`E`, all from characteristic functions (`charFun_stdGaussian`):

* `Gaussian.stdGaussian_prod`: two independent standard Gaussians form the standard Gaussian of
  the `L²` product `WithLp 2 (E × F)`.
* `Gaussian.map_prod_stdGaussian`: `A g + B g'` is a standard Gaussian for independent `g, g'`
  when `A A* + B B* = 1`. Special cases: `r g + s g'` for `r² + s² = 1`
  (`Gaussian.map_add_smul_stdGaussian`), and `P g + (1 - P) g'` for an orthogonal projection `P`
  (`Gaussian.map_proj_stdGaussian`): the part of `g` in a subspace is independent of the part
  orthogonal to it.
-/

@[expose] public section

namespace Gaussian

open MeasureTheory ProbabilityTheory Real Set Complex
open scoped RealInnerProductSpace

section Product

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Independent standard Gaussians** form the standard Gaussian of the `L²` product. -/
theorem stdGaussian_prod :
    ((stdGaussian E).prod (stdGaussian F)).map (WithLp.toLp 2) =
      stdGaussian (WithLp 2 (E × F)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_prod, charFun_stdGaussian, charFun_stdGaussian, charFun_stdGaussian,
    ← Complex.exp_add]
  have key : ((‖t‖ : ℝ) : ℂ) ^ 2 =
      ((‖(WithLp.ofLp t).1‖ : ℝ) : ℂ) ^ 2 + ((‖(WithLp.ofLp t).2‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast WithLp.prod_norm_sq_eq_of_L2 t
  rw [key]
  congr 1
  ring

/-- Integrals against the standard Gaussian of the `L²` product are iterated integrals. -/
theorem integral_stdGaussian_prod {φ : WithLp 2 (E × F) → ℝ}
    (hφ : Integrable φ (stdGaussian (WithLp 2 (E × F)))) :
    ∫ ω, φ ω ∂stdGaussian (WithLp 2 (E × F)) =
      ∫ x, ∫ y, φ (WithLp.toLp 2 (x, y)) ∂stdGaussian F ∂stdGaussian E := by
  rw [← stdGaussian_prod] at hφ ⊢
  rw [integral_map (by fun_prop) hφ.aestronglyMeasurable]
  exact integral_prod _ ((integrable_map_measure hφ.aestronglyMeasurable (by fun_prop)).1 hφ)

/-- **Linear images of two independent standard Gaussians**: `A g + B g'` is a standard Gaussian
when `‖A* t‖² + ‖B* t‖² = ‖t‖²` for all `t`, with `A*, B*` the adjoints. -/
theorem map_prod_stdGaussian (A B : E →L[ℝ] F) (A' B' : F → E)
    (hA : ∀ x t, ⟪A x, t⟫ = ⟪x, A' t⟫) (hB : ∀ x t, ⟪B x, t⟫ = ⟪x, B' t⟫)
    (h : ∀ t, ‖A' t‖ ^ 2 + ‖B' t‖ ^ 2 = ‖t‖ ^ 2) :
    ((stdGaussian E).prod (stdGaussian E)).map (fun p ↦ A p.1 + B p.2) = stdGaussian F := by
  apply Measure.ext_of_charFun
  ext t
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have : ∀ p : E × E, cexp (⟪A p.1 + B p.2, t⟫ * I) =
      cexp (⟪p.1, A' t⟫ * I) * cexp (⟪p.2, B' t⟫ * I) := by
    intro p
    rw [← Complex.exp_add, inner_add_left, hA, hB]
    push_cast
    ring_nf
  simp_rw [this]
  rw [integral_prod_mul (fun x : E ↦ cexp (⟪x, A' t⟫ * I)) (fun y : E ↦ cexp (⟪y, B' t⟫ * I))]
  rw [← charFun_apply, ← charFun_apply, charFun_stdGaussian, charFun_stdGaussian,
    charFun_stdGaussian, ← Complex.exp_add]
  have key : ((‖t‖ : ℝ) : ℂ) ^ 2 = ((‖A' t‖ : ℝ) : ℂ) ^ 2 + ((‖B' t‖ : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast (h t).symm
  rw [key]
  congr 1
  ring

/-- **Rotations of two independent standard Gaussians**: `r g + s g'` is a standard Gaussian for
`r² + s² = 1`. -/
theorem map_add_smul_stdGaussian {r s : ℝ} (h : r ^ 2 + s ^ 2 = 1) :
    ((stdGaussian E).prod (stdGaussian E)).map (fun p ↦ r • p.1 + s • p.2) = stdGaussian E := by
  have := map_prod_stdGaussian (r • ContinuousLinearMap.id ℝ E) (s • ContinuousLinearMap.id ℝ E)
    (fun t ↦ r • t) (fun t ↦ s • t) (fun x t ↦ by simp [inner_smul_left, inner_smul_right])
    (fun x t ↦ by simp [inner_smul_left, inner_smul_right])
    (fun t ↦ by rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, ← add_mul, h, one_mul])
  simpa using this

/-- **The part of a standard Gaussian in a subspace is independent of the orthogonal part**:
`P g + (1 - P) g'` is a standard Gaussian for independent `g, g'` and the orthogonal projection
`P` onto any subspace `K`. -/
theorem map_proj_stdGaussian (K : Submodule ℝ E) :
    ((stdGaussian E).prod (stdGaussian E)).map
      (fun p ↦ K.starProjection p.1 + Kᗮ.starProjection p.2) = stdGaussian E := by
  exact map_prod_stdGaussian _ _ K.starProjection Kᗮ.starProjection
    (fun x t ↦ K.inner_starProjection_left_eq_right x t)
    (fun x t ↦ Kᗮ.inner_starProjection_left_eq_right x t)
    (fun t ↦ (K.norm_sq_eq_add_norm_sq_starProjection t).symm)

end Product

/-! ### Integrals -/

section Integral

/-- Integrals against an image of a product measure, as iterated integrals. -/
theorem integral_eq_of_map_prod {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {ρ : Measure γ}
    {L : α × β → γ} (hL : Measurable L) (h : (μ.prod ν).map L = ρ) {φ : γ → ℝ}
    (hφ : Integrable φ ρ) : ∫ x, φ x ∂ρ = ∫ a, ∫ b, φ (L (a, b)) ∂ν ∂μ := by
  subst h
  rw [integral_map hL.aemeasurable hφ.aestronglyMeasurable]
  exact integral_prod _ ((integrable_map_measure hφ.aestronglyMeasurable hL.aemeasurable).1 hφ)

/-- A bounded measurable function is integrable against a finite measure. -/
theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)

/-- A bounded measurable function is square integrable against a finite measure. -/
theorem memLp_two_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)

/-- **Cauchy–Schwarz** for integrals. -/
theorem sq_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hf' : MemLp (fun x ↦ |f x|) (ENNReal.ofReal 2) μ := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hg' : MemLp (fun x ↦ |g x|) (ENNReal.ofReal 2) μ := by
    simpa [Real.norm_eq_abs] using hg.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) Real.HolderConjugate.two_two
    (ae_of_all _ fun x ↦ abs_nonneg (f x)) (ae_of_all _ fun x ↦ abs_nonneg (g x)) hf' hg'
  have hA : ∫ x, |f x| ^ (2 : ℝ) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    congr 1
    funext x
    rw [Real.rpow_two, sq_abs]
  have hB : ∫ x, |g x| ^ (2 : ℝ) ∂μ = ∫ x, g x ^ 2 ∂μ := by
    congr 1
    funext x
    rw [Real.rpow_two, sq_abs]
  rw [hA, hB] at h
  have hA0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have habs : |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x| * |g x| ∂μ := by
    simp_rw [← abs_mul]
    exact abs_integral_le_integral_abs
  calc (∫ x, f x * g x ∂μ) ^ 2 = |∫ x, f x * g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (habs.trans h) 2
    _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hA0,
          ← Real.rpow_mul hB0]
        norm_num

end Integral

/-! ### The real line -/

section RealLine

/-- The standard Gaussian on `ℝ` is `N(0, 1)`. -/
theorem stdGaussian_real : stdGaussian ℝ = gaussianReal 0 1 := by
  have h := map_inner_stdGaussian (E := ℝ) (u := 1) (by simp)
  have : (fun g : ℝ ↦ ⟪(1 : ℝ), g⟫) = id := by
    funext g
    simp
  rwa [this, Measure.map_id] at h

/-- `c₁ X + c₂ Y` for independent standard Gaussians `X, Y` has the law of `√(c₁² + c₂²) Z`. -/
theorem map_linear_gaussianReal (c₁ c₂ : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p ↦ c₁ * p.1 + c₂ * p.2) =
      (gaussianReal 0 1).map (fun x ↦ √(c₁ ^ 2 + c₂ ^ 2) * x) := by
  by_cases h : c₁ ^ 2 + c₂ ^ 2 = 0
  · have h1 : c₁ = 0 := by nlinarith [sq_nonneg c₁, sq_nonneg c₂]
    have h2 : c₂ = 0 := by nlinarith [sq_nonneg c₁, sq_nonneg c₂]
    subst h1 h2
    simp
  · have hκ : 0 < √(c₁ ^ 2 + c₂ ^ 2) :=
      Real.sqrt_pos.2 (lt_of_le_of_ne (by positivity) (Ne.symm h))
    have hκ2 : √(c₁ ^ 2 + c₂ ^ 2) ^ 2 = c₁ ^ 2 + c₂ ^ 2 := Real.sq_sqrt (by positivity)
    have hrs : (c₁ / √(c₁ ^ 2 + c₂ ^ 2)) ^ 2 + (c₂ / √(c₁ ^ 2 + c₂ ^ 2)) ^ 2 = 1 := by
      rw [div_pow, div_pow, ← add_div, hκ2, div_self h]
    have := map_add_smul_stdGaussian (E := ℝ) hrs
    rw [stdGaussian_real] at this
    conv_rhs => rw [← this]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    simp only [Function.comp_apply, smul_eq_mul]
    field_simp

/-- **Cameron–Martin** in dimension one: `E φ(X + c) = E φ(X) e^(cX - c²/2)`. -/
theorem integral_add_const_gaussianReal {φ : ℝ → ℝ} (hφ : Measurable φ) (c : ℝ) :
    ∫ x, φ (x + c) ∂gaussianReal 0 1 =
      ∫ x, φ x * rexp (c * x - c ^ 2 / 2) ∂gaussianReal 0 1 := by
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun x ↦ x + c) (f := φ) (by fun_prop)
    hφ.aestronglyMeasurable
  rw [gaussianReal_map_add_const, zero_add] at h
  rw [← h, integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  congr 1
  funext x
  simp only [gaussianPDFReal, smul_eq_mul, NNReal.coe_one, mul_one, sub_zero]
  rw [show -(x - c) ^ 2 / 2 = -x ^ 2 / 2 + (c * x - c ^ 2 / 2) by ring, Real.exp_add]
  ring

/-- **A shifted Gaussian average**, by Cauchy–Schwarz against the Cameron–Martin density:
`(E φ(X + c))² ≤ e^(c²) E φ(X)²` for bounded `φ`. -/
theorem sq_integral_add_const_le {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hb : ∀ x, |φ x| ≤ C)
    (c : ℝ) :
    (∫ x, φ (x + c) ∂gaussianReal 0 1) ^ 2 ≤ rexp (c ^ 2) * ∫ x, φ x ^ 2 ∂gaussianReal 0 1 := by
  rw [integral_add_const_gaussianReal hφ c]
  have hφ2 : MemLp φ 2 (gaussianReal 0 1) := memLp_two_of_abs_le hφ hb
  have hsq : ∀ x, rexp (c * x - c ^ 2 / 2) ^ 2 = rexp (-c ^ 2) * rexp (2 * c * x) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hint2 : Integrable (fun x ↦ rexp (c * x - c ^ 2 / 2) ^ 2) (gaussianReal 0 1) := by
    simp_rw [hsq]
    exact (integrable_exp_mul_gaussianReal (2 * c)).const_mul _
  have he2 : MemLp (fun x ↦ rexp (c * x - c ^ 2 / 2)) 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hint2
  have h := sq_integral_mul_le hφ2 he2
  have hval : ∫ x, rexp (c * x - c ^ 2 / 2) ^ 2 ∂gaussianReal 0 1 = rexp (c ^ 2) := by
    simp_rw [hsq]
    rw [integral_const_mul]
    have hm := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (2 * c)
    simp only [mgf, id] at hm
    rw [hm, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hval] at h
  linarith

/-- **Compressing a Gaussian** costs at most the factor `1/τ`: `E φ(τX) ≤ τ⁻¹ E φ(X)` for
`0 < τ ≤ 1` and bounded `φ ≥ 0`. -/
theorem integral_const_mul_le {φ : ℝ → ℝ} (hφ : Measurable φ) (h0 : ∀ x, 0 ≤ φ x) {C : ℝ}
    (hb : ∀ x, φ x ≤ C) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∫ x, φ (τ * x) ∂gaussianReal 0 1 ≤ τ⁻¹ * ∫ x, φ x ∂gaussianReal 0 1 := by
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun x ↦ τ * x) (f := φ) (by fun_prop)
    hφ.aestronglyMeasurable
  rw [gaussianReal_map_const_mul, mul_zero] at h
  set v : NNReal := NNReal.mk (τ ^ 2) (sq_nonneg _) * 1 with hvdef
  have hvτ : (v : ℝ) = τ ^ 2 := by simp [hvdef]
  have hv : v ≠ 0 := by
    intro h'
    have := congrArg NNReal.toReal h'
    rw [hvτ, NNReal.coe_zero] at this
    exact (pow_pos hτ 2).ne' this
  rw [← h, integral_gaussianReal_eq_integral_smul hv,
    integral_gaussianReal_eq_integral_smul one_ne_zero, ← integral_const_mul]
  have hC : 0 ≤ C := (h0 0).trans (hb 0)
  have hint : ∀ μ' (v : NNReal), Integrable (fun x ↦ gaussianPDFReal μ' v x * φ x) := by
    intro μ' v
    refine (integrable_gaussianPDFReal μ' v).mul_bdd (c := C) hφ.aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact hb x
  refine integral_mono (hint _ _) ((hint 0 1).const_mul τ⁻¹) fun x ↦ ?_
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (h0 x)
  simp only [gaussianPDFReal, hvτ, NNReal.coe_one, mul_one, sub_zero]
  have hs : √(2 * π * τ ^ 2) = τ * √(2 * π) := by
    rw [show 2 * π * τ ^ 2 = τ ^ 2 * (2 * π) by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hτ.le]
  rw [hs, mul_inv, ← mul_assoc]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : τ ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg x]

/-- **Anti-concentration**: a standard Gaussian lies in an interval of length `2ℓ` with
probability at most `ℓ`. -/
theorem gaussianReal_abs_sub_le (c : ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    (gaussianReal 0 1).real {x | |x - c| ≤ ℓ} ≤ ℓ := by
  have hS : {x : ℝ | |x - c| ≤ ℓ} = Icc (c - ℓ) (c + ℓ) := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hS, measureReal_def, gaussianReal_apply_eq_integral _ one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Icc
      fun x _ ↦ gaussianPDFReal_nonneg 0 1 x)]
  have hpdf : ∀ x, gaussianPDFReal 0 1 x ≤ (√(2 * π))⁻¹ := by
    intro x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one]
    calc (√(2 * π))⁻¹ * rexp (-(x - 0) ^ 2 / 2) ≤ (√(2 * π))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (x - 0)]))
            (by positivity)
      _ = _ := mul_one _
  calc ∫ x in Icc (c - ℓ) (c + ℓ), gaussianPDFReal 0 1 x
      ≤ ∫ x in Icc (c - ℓ) (c + ℓ), (√(2 * π))⁻¹ :=
        setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
          (integrableOn_const (by simp)) measurableSet_Icc fun x _ ↦ hpdf x
    _ = 2 * ℓ * (√(2 * π))⁻¹ := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
    _ ≤ ℓ := by
        have h2 : 2 ≤ √(2 * π) :=
          calc (2 : ℝ) = √(2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
            _ ≤ √(2 * π) := Real.sqrt_le_sqrt (by nlinarith [pi_gt_three])
        calc 2 * ℓ * (√(2 * π))⁻¹ = ℓ * (2 / √(2 * π)) := by ring
          _ ≤ ℓ * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ hℓ
              rw [div_le_one (by positivity)]
              exact h2
          _ = ℓ := mul_one ℓ

/-- **A box for two independent standard Gaussians**: for `σ > 0`,
`P(|X| ≤ a, |ρ X + σ Z| ≤ b) ≤ a b / σ`. -/
theorem prod_box_le (ρ : ℝ) {σ : ℝ} (hσ : 0 < σ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | |p.1| ≤ a ∧ |ρ * p.1 + σ * p.2| ≤ b} ≤ a * b / σ := by
  set S := {p : ℝ × ℝ | |p.1| ≤ a ∧ |ρ * p.1 + σ * p.2| ≤ b} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le (f := fun q : ℝ × ℝ ↦ |q.1|) (by fun_prop) measurable_const).inter
      (measurableSet_le (f := fun q : ℝ × ℝ ↦ |ρ * q.1 + σ * q.2|) (by fun_prop)
        measurable_const)
  have hA : MeasurableSet {x : ℝ | |x| ≤ a} := measurableSet_le (by fun_prop) measurable_const
  have hin : ∀ x, ∫ z, S.indicator 1 (x, z) ∂gaussianReal 0 1 ≤
      b / σ * {x : ℝ | |x| ≤ a}.indicator 1 x := by
    intro x
    by_cases hx : |x| ≤ a
    · rw [indicator_of_mem (show x ∈ {x : ℝ | |x| ≤ a} from hx), Pi.one_apply, mul_one]
      have hiff : ∀ z : ℝ, |ρ * x + σ * z| ≤ b ↔ |z - -(ρ * x) / σ| ≤ b / σ := by
        intro z
        rw [show z - -(ρ * x) / σ = (ρ * x + σ * z) / σ by field_simp; ring, abs_div,
          abs_of_pos hσ, div_le_div_iff_of_pos_right hσ]
      have : (fun z ↦ S.indicator (1 : ℝ × ℝ → ℝ) (x, z)) =
          {z : ℝ | |z - -(ρ * x) / σ| ≤ b / σ}.indicator 1 := by
        funext z
        simp only [hSdef, indicator, mem_ofPred_eq, hx, true_and, hiff, Pi.one_apply]
      rw [this, integral_indicator_one (measurableSet_le (by fun_prop) measurable_const)]
      exact gaussianReal_abs_sub_le _ (div_nonneg hb hσ.le)
    · have : (fun z ↦ S.indicator (1 : ℝ × ℝ → ℝ) (x, z)) = fun _ ↦ 0 := by
        funext z
        simp [hSdef, indicator, hx]
      rw [this, indicator_of_notMem (show x ∉ {x : ℝ | |x| ≤ a} from hx)]
      simp
  have hSi : Integrable (S.indicator (1 : ℝ × ℝ → ℝ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS, integral_prod _ hSi]
  calc ∫ x, ∫ z, S.indicator 1 (x, z) ∂gaussianReal 0 1 ∂gaussianReal 0 1
      ≤ ∫ x, b / σ * {x : ℝ | |x| ≤ a}.indicator 1 x ∂gaussianReal 0 1 := by
        refine integral_mono ?_ (((integrable_const (1 : ℝ)).indicator hA).const_mul _) hin
        exact hSi.integral_prod_left
    _ = b / σ * (gaussianReal 0 1).real {x : ℝ | |x| ≤ a} := by
        rw [integral_const_mul, integral_indicator_one hA]
    _ ≤ b / σ * a := by
        refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hb hσ.le)
        simpa using gaussianReal_abs_sub_le 0 ha
    _ = a * b / σ := by ring

/-- **The bivariate Gaussian density is bounded**: for `|ρ| < 1`,
`P(|X| ≤ a, |Y| ≤ b) ≤ a b / √(1 - ρ²)`. -/
theorem corrPair_box_le {ρ : ℝ} (hρ : ρ ^ 2 < 1) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (corrPair ρ).real {q | |q.1| ≤ a ∧ |q.2| ≤ b} ≤ a * b / √(1 - ρ ^ 2) := by
  have hm := measurable_corrPairMap ρ
  have hB : MeasurableSet {q : ℝ × ℝ | |q.1| ≤ a ∧ |q.2| ≤ b} :=
    (measurableSet_le (f := fun q : ℝ × ℝ ↦ |q.1|) (by fun_prop) measurable_const).inter
      (measurableSet_le (f := fun q : ℝ × ℝ ↦ |q.2|) (by fun_prop) measurable_const)
  rw [corrPair, map_measureReal_apply hm hB]
  exact prod_box_le ρ (Real.sqrt_pos.2 (by linarith)) ha hb

end RealLine

/-! ### Signs and smoothed signs -/

section Sign

/-- The sign `±1`, with `sgn 0 = 1`. -/
noncomputable def sgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

@[fun_prop]
theorem measurable_sgn : Measurable sgn :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

theorem abs_sgn (t : ℝ) : |sgn t| = 1 := by
  unfold sgn
  split_ifs <;> simp

/-- `U_a sgn`, the sign smoothed by the Ornstein–Uhlenbeck operator:
`s_a(t) = E sgn(a t + √(1 - a²) Z)` for a standard Gaussian `Z`. -/
noncomputable def smoothSign (a t : ℝ) : ℝ :=
  ∫ z, sgn (a * t + √(1 - a ^ 2) * z) ∂gaussianReal 0 1

theorem smoothSign_one : smoothSign 1 = sgn := by
  funext t
  simp [smoothSign]

theorem abs_smoothSign_le (a t : ℝ) : |smoothSign a t| ≤ 1 := by
  unfold smoothSign
  refine (abs_integral_le_integral_abs).trans ?_
  simp [abs_sgn]

@[fun_prop]
theorem measurable_smoothSign (a : ℝ) : Measurable (smoothSign a) := by
  have : StronglyMeasurable (fun p : ℝ × ℝ ↦ sgn (a * p.1 + √(1 - a ^ 2) * p.2)) :=
    (by fun_prop : Measurable _).stronglyMeasurable
  exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable

/-- **The semigroup property** `U_a U_b = U_(ab)` on the sign:
`E s_a(b t + √(1 - b²) Z) = s_(ab)(t)`. -/
theorem integral_smoothSign {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (t : ℝ) :
    ∫ z, smoothSign a (b * t + √(1 - b ^ 2) * z) ∂gaussianReal 0 1 = smoothSign (a * b) t := by
  set α := √(1 - a ^ 2) with hαdef
  set β := √(1 - b ^ 2) with hβdef
  have hf : Integrable (fun p : ℝ × ℝ ↦ sgn (a * (b * t + β * p.1) + α * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    integrable_of_abs_le (by fun_prop) fun p ↦ (abs_sgn _).le
  have h1 : ∫ z, smoothSign a (b * t + β * z) ∂gaussianReal 0 1 =
      ∫ p, sgn (a * (b * t + β * p.1) + α * p.2) ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
    rw [integral_prod _ hf]
    rfl
  have h2 := integral_map (μ := (gaussianReal 0 1).prod (gaussianReal 0 1))
    (φ := fun p ↦ (a * β) * p.1 + α * p.2) (f := fun y ↦ sgn (a * b * t + y)) (by fun_prop)
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [map_linear_gaussianReal, integral_map (by fun_prop)
    (Measurable.aestronglyMeasurable (by fun_prop))] at h2
  have hκ : √((a * β) ^ 2 + α ^ 2) = √(1 - (a * b) ^ 2) := by
    congr 1
    rw [mul_pow, hβdef, hαdef, Real.sq_sqrt (by nlinarith), Real.sq_sqrt (by nlinarith)]
    ring
  rw [h1, smoothSign, ← hκ, h2]
  congr 1
  funext p
  congr 1
  ring

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Sheppard's formula**, in expectation: `E sgn⟨p, g⟩ sgn⟨q, g⟩ = (2/π) arcsin ⟨p, q⟩` for
unit vectors `p, q`. -/
theorem integral_sgn_mul_sgn {p q : E} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ∫ g, sgn ⟪p, g⟫ * sgn ⟪q, g⟫ ∂stdGaussian E = 2 / π * arcsin ⟪p, q⟫ := by
  set S := {g : E | (0 ≤ ⟪p, g⟫ ↔ 0 ≤ ⟪q, g⟫)} with hSdef
  have hS : MeasurableSet S := measurableSet_setOfPred.2 (by fun_prop)
  have h : ∀ g, sgn ⟪p, g⟫ * sgn ⟪q, g⟫ = 2 * S.indicator 1 g - 1 := by
    intro g
    by_cases ha : 0 ≤ ⟪p, g⟫ <;> by_cases hb : 0 ≤ ⟪q, g⟫ <;>
      simp [sgn, hSdef, indicator, ha, hb] <;> norm_num
  simp_rw [h]
  have hI : Integrable (fun g ↦ 2 * S.indicator (1 : E → ℝ) g) (stdGaussian E) :=
    ((integrable_const (1 : ℝ)).indicator hS).const_mul 2
  rw [integral_sub hI (integrable_const 1), integral_const_mul, integral_indicator_one hS,
    prob_sign_agree hp hq]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  have := pi_pos
  field_simp
  ring

/-- `s_a(⟨u, g⟩)` averages the sign over an independent copy `g'` of `g`. -/
theorem smoothSign_inner {u : E} (hu : ‖u‖ = 1) (a : ℝ) (g : E) :
    smoothSign a ⟪u, g⟫ = ∫ g', sgn (a * ⟪u, g⟫ + √(1 - a ^ 2) * ⟪u, g'⟫) ∂stdGaussian E := by
  have h := integral_map (μ := stdGaussian E) (φ := fun g' ↦ ⟪u, g'⟫)
    (f := fun z ↦ sgn (a * ⟪u, g⟫ + √(1 - a ^ 2) * z)) (by fun_prop)
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [map_inner_stdGaussian hu] at h
  exact h

/-- **Smoothed correlations** [BGHKLMM26, Fact 3.9]: for unit vectors `u, v` and `a, b ∈ [0, 1]`,
`E s_a(⟨u, g⟩) s_b(⟨v, g⟩) = (2/π) arcsin (a b ⟨u, v⟩)`. -/
theorem integral_smoothSign_mul_smoothSign {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∫ g, smoothSign a ⟪u, g⟫ * smoothSign b ⟪v, g⟫ ∂stdGaussian E =
      2 / π * arcsin (a * b * ⟪u, v⟫) := by
  set α := √(1 - a ^ 2) with hαdef
  set β := √(1 - b ^ 2) with hβdef
  have hα : α ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have hβ : β ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have hu2 : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hv2 : ⟪v, v⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv, one_pow]
  let p : WithLp 2 (E × WithLp 2 (E × E)) := WithLp.toLp 2 (a • u, WithLp.toLp 2 (α • u, 0))
  let q : WithLp 2 (E × WithLp 2 (E × E)) := WithLp.toLp 2 (b • v, WithLp.toLp 2 (0, β • v))
  have hnorm : ∀ x : WithLp 2 (E × WithLp 2 (E × E)), ⟪x, x⟫ = 1 → ‖x‖ = 1 := by
    intro x hx
    rw [real_inner_self_eq_norm_sq] at hx
    nlinarith [norm_nonneg x]
  have hp : ‖p‖ = 1 := hnorm p (by
    simp only [p, WithLp.prod_inner_apply, inner_smul_left, inner_smul_right, inner_zero_left,
      hu2, conj_trivial]
    nlinarith)
  have hq : ‖q‖ = 1 := hnorm q (by
    simp only [q, WithLp.prod_inner_apply, inner_smul_left, inner_smul_right, inner_zero_left,
      hv2, conj_trivial]
    nlinarith)
  have hpq : ⟪p, q⟫ = a * b * ⟪u, v⟫ := by
    simp only [p, q, WithLp.prod_inner_apply, inner_smul_left, inner_smul_right, inner_zero_left,
      inner_zero_right, conj_trivial]
    ring
  have key := integral_sgn_mul_sgn hp hq
  rw [hpq] at key
  have hint : Integrable (fun ω ↦ sgn ⟪p, ω⟫ * sgn ⟪q, ω⟫)
      (stdGaussian (WithLp 2 (E × WithLp 2 (E × E)))) :=
    integrable_of_abs_le (by fun_prop) fun ω ↦ by rw [abs_mul, abs_sgn, abs_sgn, mul_one]
  rw [← key, integral_stdGaussian_prod hint]
  congr 1
  funext g
  have hint2 : Integrable (fun ω : WithLp 2 (E × E) ↦
      sgn ⟪p, WithLp.toLp 2 (g, ω)⟫ * sgn ⟪q, WithLp.toLp 2 (g, ω)⟫)
      (stdGaussian (WithLp 2 (E × E))) :=
    integrable_of_abs_le (by fun_prop) fun ω ↦ by rw [abs_mul, abs_sgn, abs_sgn, mul_one]
  have hpt : ∀ g' g'' : E,
      sgn ⟪p, WithLp.toLp 2 (g, WithLp.toLp 2 (g', g''))⟫ *
          sgn ⟪q, WithLp.toLp 2 (g, WithLp.toLp 2 (g', g''))⟫ =
        sgn (a * ⟪u, g⟫ + α * ⟪u, g'⟫) * sgn (b * ⟪v, g⟫ + β * ⟪v, g''⟫) := by
    intro g' g''
    simp [p, q, real_inner_smul_left]
  rw [integral_stdGaussian_prod hint2]
  simp_rw [hpt]
  rw [smoothSign_inner hu, smoothSign_inner hv, ← integral_mul_const]
  congr 1
  funext g'
  rw [← integral_const_mul]

end InnerProduct

end Sign

end Gaussian
