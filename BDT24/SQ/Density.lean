module

public import BDT24.Model
public import BDT24.Prob.Gauss.Spike

/-!
# The relative density of a planted point

`BDT24.SQ.multivariateGaussian_spikedCov_eq`: for a unit vector `x` and `0 ≤ θ < 1`, the planted
law `N(0, I - θ x xᵀ)` has density
`(1 - θ)^(-1/2) exp(-θ ⟨x, z⟩² / (2 (1 - θ)))` (`BDT24.SQ.spikeDensity`) with respect to
`N(0, I)`, so the relative density `BDT24.relDensity` of a spike is this function almost
everywhere (`BDT24.SQ.relDensity_ae_eq`).

The planted law differs from `N(0, I)` only along `x`: a standard Gaussian is `s x + w` with
`s ~ N(0, 1)` and `w ~ N(0, I - x xᵀ)` independent (and `⟨x, w⟩ = 0` almost surely), and a
planted point is `√(1 - θ) s x + w` (compare the laws of all linear functionals, Cramér–Wold,
`BDT24.Prob.G.ext_of_map_dual`). In one dimension, `N(0, 1 - θ)` has density
`(1 - θ)^(-1/2) exp(-θ t² / (2 (1 - θ)))` with respect to `N(0, 1)` (the ratio of the two
Gaussian densities, `gaussianPDF`).
-/

@[expose] public section

namespace BDT24.SQ

open MeasureTheory ProbabilityTheory

/-- The relative density `(1 - θ)^(-1/2) exp(-θ ⟨x, z⟩² / (2 (1 - θ)))` of `N(0, I - θ x xᵀ)`
with respect to `N(0, I)`, for a unit vector `x`. -/
noncomputable def spikeDensity {m : ℕ} (θ : ℝ) (x : Fin m → ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    ℝ :=
  (√(1 - θ))⁻¹ * Real.exp (-(θ / (2 * (1 - θ))) * (x ⬝ᵥ z.ofLp) ^ 2)

namespace DN

open Matrix WithLp

/-! ### One dimension -/

/-- The one-dimensional density ratio `(1 - θ)^(-1/2) exp(-θ t² / (2 (1 - θ)))` of `N(0, 1 - θ)`
with respect to `N(0, 1)`. -/
noncomputable def dnRatioOne (θ t : ℝ) : ℝ :=
  (√(1 - θ))⁻¹ * Real.exp (-(θ / (2 * (1 - θ))) * t ^ 2)

/-- `BDT24.SQ.spikeDensity` is the one-dimensional ratio at `⟨x, z⟩`. -/
theorem spikeDensity_eq_dnRatioOne {m : ℕ} (θ : ℝ) (x : Fin m → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) : spikeDensity θ x z = dnRatioOne θ (x ⬝ᵥ z.ofLp) :=
  rfl

/-- The one-dimensional ratio is nonnegative. -/
theorem dnRatioOne_nonneg (θ t : ℝ) : 0 ≤ dnRatioOne θ t :=
  mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- The one-dimensional ratio is measurable. -/
theorem measurable_dnRatioOne (θ : ℝ) : Measurable (dnRatioOne θ) := by
  unfold dnRatioOne
  fun_prop

/-- The density `BDT24.SQ.spikeDensity θ x`, as an extended nonnegative function, is
measurable. -/
theorem measurable_ofReal_spikeDensity {m : ℕ} (θ : ℝ) (x : Fin m → ℝ) :
    Measurable fun z ↦ ENNReal.ofReal (spikeDensity θ x z) :=
  (measurable_dnRatioOne θ).ennreal_ofReal.comp (Prob.G.measurable_dotProduct x)

/-- The ratio of the Gaussian densities: `φ₁(t) r(t) = φ_{1-θ}(t)`. -/
theorem gaussianPDFReal_mul_dnRatioOne {θ : ℝ} (h1 : θ < 1) (t : ℝ) :
    gaussianPDFReal 0 1 t * dnRatioOne θ t = gaussianPDFReal 0 (1 - θ).toNNReal t := by
  have hpos : 0 < 1 - θ := by linarith
  have hv : (((1 - θ).toNNReal : ℝ)) = 1 - θ := Real.coe_toNNReal _ hpos.le
  simp only [gaussianPDFReal, dnRatioOne, hv, NNReal.coe_one, sub_zero, mul_one]
  rw [Real.sqrt_mul (by positivity) (1 - θ), mul_inv]
  have he : -t ^ 2 / 2 + -(θ / (2 * (1 - θ))) * t ^ 2 = -t ^ 2 / (2 * (1 - θ)) := by
    field_simp
    ring
  rw [← he, Real.exp_add]
  ring

/-- In one dimension, `N(0, 1 - θ)` is `N(0, 1)` with density `BDT24.SQ.DN.dnRatioOne θ`. -/
theorem gaussianReal_eq_withDensity_dnRatioOne {θ : ℝ} (h1 : θ < 1) :
    gaussianReal 0 (1 - θ).toNNReal =
      (gaussianReal 0 1).withDensity fun t ↦ ENNReal.ofReal (dnRatioOne θ t) := by
  have hv : (1 - θ).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    linarith
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (measurable_dnRatioOne θ).ennreal_ofReal]
  congr 1
  funext t
  rw [Pi.mul_apply, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_mul_dnRatioOne h1]

/-! ### Splitting a Gaussian vector along `x` -/

variable {m : ℕ}

/-- The map `(s, w) ↦ s x + w`. -/
noncomputable def dnSplitMap (x : Fin m → ℝ) (p : ℝ × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  p.1 • toLp 2 x + p.2

/-- The map `(s, w) ↦ s x + w` is measurable. -/
theorem measurable_dnSplitMap (x : Fin m → ℝ) : Measurable (dnSplitMap x) := by
  unfold dnSplitMap
  fun_prop

/-- A continuous linear functional on `ℝ^m` is `y ↦ ⟨ℓ, y⟩` with `ℓ i = L eᵢ`. -/
theorem dnDual_apply (L : StrongDual ℝ (EuclideanSpace ℝ (Fin m)))
    (y : EuclideanSpace ℝ (Fin m)) :
    L y = (fun i ↦ L (EuclideanSpace.single i 1)) ⬝ᵥ y.ofLp := by
  have hy : y = ∑ i, y i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr y]
    simp
  conv_lhs => rw [hy]
  simp [map_sum, map_smul, dotProduct, mul_comm]

/-- `I - θ x xᵀ` is positive semidefinite for a unit vector `x` and `0 ≤ θ ≤ 1`. -/
theorem dnPosSemidef_spikedCov {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {x : Fin m → ℝ}
    (hx : x ⬝ᵥ x = 1) : (spikedCov θ x).PosSemidef := by
  have h := Prob.G.posSemidef_smul_one_sub x (r := 1) (c := θ) h0 (by rw [hx, mul_one]; exact h1)
  rw [one_smul] at h
  exact h

/-- With `θ = 0` the planted covariance is the identity. -/
theorem dnSpikedCov_zero (x : Fin m → ℝ) : spikedCov 0 x = 1 := by
  simp [spikedCov]

/-- **The split of a planted point**: for a unit vector `x` and `0 ≤ θ ≤ 1`, if `s ~ N(0, 1 - θ)`
and `w ~ N(0, I - x xᵀ)` are independent, then `s x + w ~ N(0, I - θ x xᵀ)`. -/
theorem map_dnSplitMap {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) {x : Fin m → ℝ} (hx : x ⬝ᵥ x = 1) :
    ((gaussianReal 0 (1 - θ).toNNReal).prod (multivariateGaussian 0 (spikedCov 1 x))).map
        (dnSplitMap x) = multivariateGaussian 0 (spikedCov θ x) := by
  have hF := measurable_dnSplitMap x
  refine Prob.G.ext_of_map_dual fun L ↦ ?_
  set c : Fin m → ℝ := fun i ↦ L (EuclideanSpace.single i 1) with hc
  have hL : ⇑L = fun y ↦ c ⬝ᵥ y.ofLp := funext (dnDual_apply L)
  have hLF : ⇑L ∘ dnSplitMap x = fun p ↦ (c ⬝ᵥ x) * p.1 + c ⬝ᵥ p.2.ofLp := by
    funext p
    simp [hL, dnSplitMap, dotProduct_add, dotProduct_smul, mul_comm]
  rw [Measure.map_map L.continuous.measurable hF, hLF,
    Prob.G.map_prod_add _ _ (measurable_const_mul _) (Prob.G.measurable_dotProduct c),
    gaussianReal_map_const_mul,
    Prob.G.map_dotProduct_multivariateGaussian (dnPosSemidef_spikedCov zero_le_one le_rfl hx), hL,
    Prob.G.map_dotProduct_multivariateGaussian (dnPosSemidef_spikedCov h0 h1 hx),
    gaussianReal_conv_gaussianReal]
  have hcs := Prob.G.dotProduct_sq_le x c
  rw [hx, one_mul] at hcs
  congr 1
  · simp
  · ext
    simp only [spikedCov, Prob.G.dotProduct_one_sub_smul_vecMulVec_mulVec, NNReal.coe_add,
      NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ (sub_nonneg.2 h1)]
    rw [Real.coe_toNNReal _ (by nlinarith), Real.coe_toNNReal _ (by nlinarith),
      dotProduct_comm c x]
    ring

/-- Under `N(0, I - x xᵀ)`, `⟨x, w⟩ = 0` almost surely for a unit vector `x`. -/
theorem ae_dotProduct_eq_zero {x : Fin m → ℝ} (hx : x ⬝ᵥ x = 1) :
    ∀ᵐ w ∂(multivariateGaussian 0 (spikedCov 1 x)), x ⬝ᵥ w.ofLp = 0 := by
  have h := Prob.G.map_dotProduct_multivariateGaussian (μ := 0)
    (dnPosSemidef_spikedCov zero_le_one le_rfl hx) x
  have hq : x ⬝ᵥ (spikedCov 1 x *ᵥ x) = 0 := by
    rw [spikedCov, Prob.G.dotProduct_one_sub_smul_vecMulVec_mulVec, hx]
    norm_num
  rw [hq] at h
  norm_num at h
  refine ae_of_ae_map (p := fun t ↦ t = 0) (Prob.G.measurable_dotProduct x).aemeasurable ?_
  rw [h, ae_dirac_eq]
  exact Filter.eventually_pure.2 rfl

end DN

open DN

/-- **The density of a planted point**: for a unit vector `x` and `0 ≤ θ < 1`,
`N(0, I - θ x xᵀ)` is `N(0, I)` with density `BDT24.SQ.spikeDensity θ x`. -/
theorem multivariateGaussian_spikedCov_eq {m : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1)
    {x : Fin m → ℝ} (hx : x ⬝ᵥ x = 1) :
    multivariateGaussian 0 (spikedCov θ x) =
      (multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)).withDensity
        fun z ↦ ENNReal.ofReal (spikeDensity θ x z) := by
  have hF := measurable_dnSplitMap x
  have hr := (measurable_dnRatioOne θ).ennreal_ofReal
  have hγ := map_dnSplitMap le_rfl zero_le_one hx
  rw [sub_zero, Real.toNNReal_one, dnSpikedCov_zero] at hγ
  rw [← map_dnSplitMap h0 h1.le hx, gaussianReal_eq_withDensity_dnRatioOne h1,
    prod_withDensity_left hr, ← hγ]
  ext S hS
  rw [Measure.map_apply hF hS, withDensity_apply _ (hF hS), withDensity_apply _ hS,
    setLIntegral_map hS (measurable_ofReal_spikeDensity θ x) hF]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  have hae : ∀ᵐ p ∂((gaussianReal 0 1).prod (multivariateGaussian 0 (spikedCov 1 x))),
      x ⬝ᵥ p.2.ofLp = 0 :=
    ae_of_ae_map (p := fun w : EuclideanSpace ℝ (Fin m) ↦ x ⬝ᵥ w.ofLp = 0)
      measurable_snd.aemeasurable (by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact ae_dotProduct_eq_zero hx)
  filter_upwards [hae] with p hp
  simp only [spikeDensity_eq_dnRatioOne, dnSplitMap, WithLp.ofLp_add, WithLp.ofLp_smul,
    dotProduct_add, dotProduct_smul, hx, hp, smul_eq_mul, mul_one, add_zero]

/-- The relative density of the planted law of a sign pattern is `BDT24.SQ.spikeDensity` of its
spike, almost everywhere under `N(0, I)`. -/
theorem relDensity_ae_eq {d k : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {v : Fin d → SignType}
    (hv : v ∈ spikeSigns d k) :
    relDensity k θ v =ᵐ[multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)]
      spikeDensity θ (spikeVector k v) := by
  have hx : spikeVector k v ⬝ᵥ spikeVector k v = 1 := by
    have hs : √((k : ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
    have hs0 : √((k : ℝ) + 1) ≠ 0 := by positivity
    rw [Prob.G.spikeVector_eq, smul_dotProduct, dotProduct_smul,
      Prob.G.spikeDir_dotProduct_self hv, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow,
      hs, inv_mul_cancel₀ (by positivity)]
  have h := Measure.rnDeriv_withDensity
    (multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ))
    (measurable_ofReal_spikeDensity θ (spikeVector k v))
  rw [← multivariateGaussian_spikedCov_eq h0 h1 hx] at h
  filter_upwards [h] with z hz
  rw [relDensity, hz]
  exact ENNReal.toReal_ofReal (dnRatioOne_nonneg θ _)

end BDT24.SQ
