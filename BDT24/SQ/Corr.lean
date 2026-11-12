module

public import BDT24.SQ.Density
public import BDT24.LowDeg.Defs
public import BDT24.Prob.Gauss.Spike

/-!
# The correlation of two planted laws

`BDT24.SQ.pairCorr_eq`: for two sign patterns `u, v` and `0 ≤ θ < 1`,
`⟨D̄_u, D̄_v⟩ = (1 - θ² ⟨x_u, x_v⟩²)^(-1/2)`.

By `BDT24.SQ.multivariateGaussian_spikedCov_eq`,
`E_{N(0,I)} [D̄_u D̄_v] = E_{z ~ N(0, I - θ x_u x_uᵀ)} D̄_v(z)`, and `D̄_v(z)` depends only on
`⟨x_v, z⟩ ~ N(0, 1 - θ τ²)` (`τ = ⟨x_u, x_v⟩`,
`BDT24.Prob.G.map_dotProduct_multivariateGaussian`). For `s ~ N(0, σ²)` and `c ≥ 0`,
`E exp(-c s²) = (1 + 2 c σ²)^(-1/2)` (`integral_gaussian` against `gaussianPDF`). With
`c = θ / (2 (1 - θ))` and `σ² = 1 - θ τ²`, `1 + 2 c σ² = (1 - θ² τ²)/(1 - θ)`, and the factor
`(1 - θ)^(-1/2)` of the density cancels.
-/

@[expose] public section

namespace BDT24.SQ

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace CR

/-- **A Gaussian moment of `exp(-c s²)`**: for `s ~ N(0, w)` with `w > 0` and `c ≥ 0`,
`E exp(-c s²) = 1/√(1 + 2 c w)`. -/
theorem integral_expSq_gaussianReal_kestrel {c : ℝ} (hc : 0 ≤ c) {w : ℝ≥0} (hw : w ≠ 0) :
    ∫ s, Real.exp (-c * s ^ 2) ∂(gaussianReal 0 w) = 1 / √(1 + 2 * c * w) := by
  have hw' : (0 : ℝ) < w := by positivity
  have hb : 0 < 1 + 2 * c * (w : ℝ) := by positivity
  rw [integral_gaussianReal_eq_integral_smul hw]
  have h : ∀ s : ℝ, gaussianPDFReal 0 w s • Real.exp (-c * s ^ 2) =
      (√(2 * Real.pi * w))⁻¹ * Real.exp (-((1 + 2 * c * w) / (2 * w)) * s ^ 2) := by
    intro s
    rw [gaussianPDFReal, smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [h]
  rw [integral_const_mul, integral_gaussian,
    show Real.pi / ((1 + 2 * c * w) / (2 * w)) = 2 * Real.pi * w / (1 + 2 * c * w) by
      field_simp,
    Real.sqrt_div' _ hb.le]
  have hs : 0 < √(2 * Real.pi * w) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- The spike of a sign pattern is a unit vector. -/
theorem spikeVector_dotProduct_self_heron {d k : ℕ} {v : Fin d → SignType}
    (hv : v ∈ spikeSigns d k) : spikeVector k v ⬝ᵥ spikeVector k v = 1 := by
  have hs : √((k : ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
  rw [Prob.G.spikeVector_eq, smul_dotProduct, dotProduct_smul, Prob.G.spikeDir_dotProduct_self hv,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv, ← sq, hs, inv_mul_cancel₀ (by positivity)]

/-- `spikeDensity θ x` is measurable. -/
theorem measurable_spikeDensity_heron {m : ℕ} (θ : ℝ) (x : Fin m → ℝ) :
    Measurable (spikeDensity θ x) := by
  unfold spikeDensity
  have := Prob.G.measurable_dotProduct x
  fun_prop

/-- `spikeDensity θ x` is nonnegative. -/
theorem spikeDensity_nonneg_heron {m : ℕ} (θ : ℝ) (x : Fin m → ℝ)
    (z : EuclideanSpace ℝ (Fin m)) : 0 ≤ spikeDensity θ x z := by
  unfold spikeDensity
  positivity

/-- For a unit vector `x` and `0 ≤ θ < 1`, `I - θ x xᵀ` is positive semidefinite. -/
theorem posSemidef_spikedCov_heron {m : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1)
    {x : Fin m → ℝ} (hx : x ⬝ᵥ x = 1) : (spikedCov θ x).PosSemidef := by
  have h := Prob.G.posSemidef_smul_one_sub x (r := 1) (c := θ) h0 (by rw [hx]; linarith)
  rwa [one_smul] at h

/-- The expectation of `spikeDensity θ y` under `N(0, I - θ x xᵀ)` for unit vectors `x, y`:
`(√(1 - θ))⁻¹ E exp(-c s²)` for `s ~ N(0, 1 - θ ⟨x, y⟩²)` and `c = θ / (2 (1 - θ))`. -/
theorem integral_spikeDensity_heron {m : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1)
    {x y : Fin m → ℝ} (hx : x ⬝ᵥ x = 1) (hy : y ⬝ᵥ y = 1) :
    ∫ z, spikeDensity θ y z ∂(multivariateGaussian 0 (spikedCov θ x)) =
      (√(1 - θ))⁻¹ * ∫ s, Real.exp (-(θ / (2 * (1 - θ))) * s ^ 2)
        ∂(gaussianReal 0 (1 - θ * (x ⬝ᵥ y) ^ 2).toNNReal) := by
  have hmap := Prob.G.map_dotProduct_multivariateGaussian (μ := 0)
    (posSemidef_spikedCov_heron h0 h1 hx) y
  rw [spikedCov, Prob.G.dotProduct_one_sub_smul_vecMulVec_mulVec, hy] at hmap
  simp only [WithLp.ofLp_zero, dotProduct_zero] at hmap
  rw [← integral_const_mul, ← hmap, integral_map (Prob.G.measurable_dotProduct y).aemeasurable
    (by fun_prop)]
  rfl

end CR

/-- **The correlation of two planted laws**: `⟨D̄_u, D̄_v⟩ = (1 - θ² ⟨x_u, x_v⟩²)^(-1/2)`. -/
theorem pairCorr_eq {d k : ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) {u v : Fin d → SignType}
    (hu : u ∈ spikeSigns d k) (hv : v ∈ spikeSigns d k) :
    pairCorr k θ u v = 1 / √(1 - θ ^ 2 * LowDeg.spikeIP k u v ^ 2) := by
  have hxu := CR.spikeVector_dotProduct_self_heron hu
  have hxv := CR.spikeVector_dotProduct_self_heron hv
  have hτ : LowDeg.spikeIP k u v = spikeVector k u ⬝ᵥ spikeVector k v := rfl
  set τ := LowDeg.spikeIP k u v
  have hτ2 : τ ^ 2 ≤ 1 := by
    have := Prob.G.dotProduct_sq_le (spikeVector k u) (spikeVector k v)
    rw [hxu, hxv, ← hτ] at this
    linarith
  have hσ : 0 < 1 - θ * τ ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hτ2 h0]
  have hc : 0 ≤ θ / (2 * (1 - θ)) := div_nonneg h0 (by linarith)
  have hw : (1 - θ * τ ^ 2).toNNReal ≠ 0 := by simpa using hσ
  -- Step 1: the relative densities are the spike densities.
  have e1 : pairCorr k θ u v = ∫ z, spikeDensity θ (spikeVector k u) z *
      spikeDensity θ (spikeVector k v) z
        ∂(multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) := by
    unfold pairCorr
    refine integral_congr_ae ?_
    filter_upwards [relDensity_ae_eq h0 h1 hu, relDensity_ae_eq h0 h1 hv] with z hzu hzv
    rw [hzu, hzv]
  -- Step 2: integrate against the planted law of `u`.
  have e2 : ∫ z, spikeDensity θ (spikeVector k u) z * spikeDensity θ (spikeVector k v) z
        ∂(multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) =
      ∫ z, spikeDensity θ (spikeVector k v) z
        ∂(multivariateGaussian 0 (spikedCov θ (spikeVector k u))) := by
    rw [multivariateGaussian_spikedCov_eq h0 h1 hxu, integral_withDensity_eq_integral_toReal_smul
      ((CR.measurable_spikeDensity_heron θ _).ennreal_ofReal)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal (CR.spikeDensity_nonneg_heron θ _ z), smul_eq_mul]
  rw [e1, e2, CR.integral_spikeDensity_heron h0 h1 hxu hxv, ← hτ,
    CR.integral_expSq_gaussianReal_kestrel hc hw, Real.coe_toNNReal _ hσ.le]
  -- Step 3: `1 + 2 c σ² = (1 - θ² τ²)/(1 - θ)`.
  have hθ : 0 < 1 - θ := by linarith
  have hθ2 : 0 < 1 - θ ^ 2 * τ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hτ2 (sq_nonneg θ)]
  have key : 1 + 2 * (θ / (2 * (1 - θ))) * (1 - θ * τ ^ 2) = (1 - θ ^ 2 * τ ^ 2) / (1 - θ) := by
    field_simp
    ring
  have hs : 0 < √(1 - θ) := Real.sqrt_pos.2 hθ
  have hs2 : 0 < √(1 - θ ^ 2 * τ ^ 2) := Real.sqrt_pos.2 hθ2
  rw [key, Real.sqrt_div' _ hθ.le]
  field_simp

end BDT24.SQ
