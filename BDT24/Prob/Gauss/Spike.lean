module

public import BDT24.Prob.Gauss.Linear

/-!
# The spike and the regression law

Facts about the definitions of `BDT24/Model.lean` used in `BDT24/Prob/Gauss.lean`:

* `BDT24.Prob.G.sum_sq_signs`: a sign pattern in `BDT24.spikeSigns d k` has `∑ vⱼ² = k`.
* `BDT24.Prob.G.spikedCov_eq`: the planted covariance is `I - (1/(k+2)) u uᵀ` for the direction
  `u = (-1, v)` of the spike (`BDT24.Prob.G.spikeDir`), since `θ/(k+1) = 1/(k+2)`; it is positive
  semidefinite (`BDT24.Prob.G.posSemidef_spikedCov`).
* `BDT24.Prob.G.map_slrLaw`: a continuous linear functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` of a sample
  point of `BDT24.slrLaw S x*` is `N(0, (ℓ + b x*)ᵀ S (ℓ + b x*) + b²)`;
  `BDT24.Prob.G.map_slrLaw_rankOne` evaluates the variance for `S = I - (1/(k+2)) w wᵀ` and
  `x* = w/√6` with `‖w‖² = k`: it is `(4/3) b² + ‖ℓ‖² - (⟨w, ℓ⟩ - √(2/3) b)²/(k+2)`.
-/

@[expose] public section

namespace BDT24.Prob.G

open MeasureTheory ProbabilityTheory Matrix

/-! ### Sign patterns and the spike -/

/-- The direction `(-1, v)` of the spike with sign pattern `v`: the spike is `u/√(k+1)`. -/
noncomputable def spikeDir {d : ℕ} (v : Fin d → SignType) : Fin (d + 1) → ℝ :=
  Fin.cons (-1) fun j ↦ (v j : ℝ)

/-- The square of a sign is `0` or `1`. -/
theorem sq_signType (s : SignType) : (s : ℝ) ^ 2 = if s = 0 then 0 else 1 := by
  cases s <;> simp

/-- A sign is `0` exactly when its value in `ℝ` is. -/
theorem signType_coe_ne_zero (s : SignType) : (s : ℝ) ≠ 0 ↔ s ≠ 0 := by
  cases s <;> simp

/-- A sign pattern with exactly `k` nonzero entries has `∑ vⱼ² = k`. -/
theorem sum_sq_signs {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    ∑ j, (v j : ℝ) ^ 2 = k := by
  simp only [spikeSigns, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rw [← hv, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [sq_signType]
  by_cases h : v j = 0 <;> simp [h]

/-- The direction of the spike has squared norm `k + 1`. -/
theorem spikeDir_dotProduct_self {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    spikeDir v ⬝ᵥ spikeDir v = k + 1 := by
  simp only [dotProduct, Fin.sum_univ_succ, spikeDir, Fin.cons_zero, Fin.cons_succ, ← sq,
    sum_sq_signs hv]
  ring

/-- The spike is `u/√(k+1)` for its direction `u = (-1, v)`. -/
theorem spikeVector_eq {d : ℕ} (k : ℕ) (v : Fin d → SignType) :
    spikeVector k v = (√((k : ℝ) + 1))⁻¹ • spikeDir v := by
  funext i
  cases i using Fin.cases <;> simp [spikeVector, spikeDir, div_eq_inv_mul]

/-- **The planted covariance** is `I - (1/(k+2)) u uᵀ` for the direction `u = (-1, v)` of the
spike: `θ x xᵀ = θ/(k+1) u uᵀ` and `θ/(k+1) = 1/(k+2)`. -/
theorem spikedCov_eq {d : ℕ} (k : ℕ) (v : Fin d → SignType) :
    spikedCov (theta k) (spikeVector k v) =
      1 - ((k : ℝ) + 2)⁻¹ • vecMulVec (spikeDir v) (spikeDir v) := by
  have hs : √((k : ℝ) + 1) ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
  have hs0 : √((k : ℝ) + 1) ≠ 0 := by positivity
  rw [spikedCov, spikeVector_eq, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul]
  congr 2
  rw [theta]
  field_simp
  rw [hs]

/-- The planted covariance is positive semidefinite. -/
theorem posSemidef_spikedCov {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    (spikedCov (theta k) (spikeVector k v)).PosSemidef := by
  have h := posSemidef_smul_one_sub (spikeDir v) (r := 1) (c := ((k : ℝ) + 2)⁻¹)
    (by positivity) (by
      rw [spikeDir_dotProduct_self hv, inv_mul_le_iff₀ (by positivity)]
      linarith)
  rw [one_smul] at h
  rwa [spikedCov_eq]

/-! ### Linear functionals of a regression sample point -/

/-- A continuous linear functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` of a sample point of
`BDT24.slrLaw S x*` is `N(0, (ℓ + b x*)ᵀ S (ℓ + b x*) + b²)`, with `ℓ i = L (eᵢ, 0)` and
`b = L (0, 1)`. -/
theorem map_slrLaw {D : ℕ} {S : Matrix (Fin D) (Fin D) ℝ} (hS : S.PosSemidef) (xs : Fin D → ℝ)
    (L : StrongDual ℝ (EuclideanSpace ℝ (Fin D) × ℝ)) :
    (slrLaw S xs).map L =
      gaussianReal 0
        (((fun i ↦ L (EuclideanSpace.single i 1, 0)) + L (0, 1) • xs) ⬝ᵥ
            (S *ᵥ ((fun i ↦ L (EuclideanSpace.single i 1, 0)) + L (0, 1) • xs)) +
          L (0, 1) ^ 2).toNNReal := by
  rw [slrLaw, Measure.map_map L.continuous.measurable (measurable_response xs)]
  have h : ⇑L ∘ response xs = fun p ↦
      ((fun i ↦ L (EuclideanSpace.single i 1, 0)) + L (0, 1) • xs) ⬝ᵥ p.1.ofLp +
        L (0, 1) * p.2 := by
    funext p
    rw [Function.comp_apply, response, dual_prod_apply, add_dotProduct, smul_dotProduct,
      smul_eq_mul, dotProduct_comm xs]
    simp only [dotProduct]
    ring
  rw [h, map_prod_dotProduct_gaussianReal hS]

/-- The variance identity behind [BDT24, Fact 2.1]: with `t = b/√6`, both sides are
`‖ℓ‖² + 2 t ⟨w, ℓ⟩ + k t² - (⟨w, ℓ⟩ + k t)²/(k+2) + 6 t²`. -/
theorem variance_identity (k : ℕ) (A S b : ℝ) :
    A + 2 * (b * (√6)⁻¹) * S + (b * (√6)⁻¹) ^ 2 * k -
          ((k : ℝ) + 2)⁻¹ * (S + b * (√6)⁻¹ * k) ^ 2 + b ^ 2 =
      4 / 3 * b ^ 2 + A - ((k : ℝ) + 2)⁻¹ * (S - b * √(2 / 3)) ^ 2 := by
  have hr : √6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hr0 : √6 ≠ 0 := by positivity
  have hs : √(2 / 3) * √6 = 2 := by
    rw [← Real.sqrt_mul (by norm_num), show (2 / 3 : ℝ) * 6 = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  set t := b * (√6)⁻¹ with ht
  have hb : b = t * √6 := by rw [ht]; field_simp
  have hbs : b * √(2 / 3) = 2 * t := by rw [hb, mul_assoc, mul_comm √6, hs, mul_comm]
  have hb2 : b ^ 2 = 6 * t ^ 2 := by rw [hb, mul_pow, hr, mul_comm]
  rw [hbs, hb2]
  field_simp
  ring

/-- The law of a continuous linear functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` of a sample point of
`BDT24.slrLaw (I - (1/(k+2)) w wᵀ) (w/√6)` with `‖w‖² = k` is
`N(0, (4/3) b² + ‖ℓ‖² - (⟨w, ℓ⟩ - √(2/3) b)²/(k+2))`. -/
theorem map_slrLaw_rankOne {D k : ℕ} (w : Fin D → ℝ) (hw : w ⬝ᵥ w = k)
    (L : StrongDual ℝ (EuclideanSpace ℝ (Fin D) × ℝ)) :
    (slrLaw (1 - ((k : ℝ) + 2)⁻¹ • vecMulVec w w) ((√6)⁻¹ • w)).map L =
      gaussianReal 0
        (4 / 3 * L (0, 1) ^ 2 +
            (fun i ↦ L (EuclideanSpace.single i 1, 0)) ⬝ᵥ
              (fun i ↦ L (EuclideanSpace.single i 1, 0)) -
          ((k : ℝ) + 2)⁻¹ *
            (w ⬝ᵥ (fun i ↦ L (EuclideanSpace.single i 1, 0)) - L (0, 1) * √(2 / 3)) ^ 2
          ).toNNReal := by
  have hS : (1 - ((k : ℝ) + 2)⁻¹ • vecMulVec w w).PosSemidef := by
    have h := posSemidef_smul_one_sub w (r := 1) (c := ((k : ℝ) + 2)⁻¹) (by positivity) (by
      rw [hw, inv_mul_le_iff₀ (by positivity)]
      linarith)
    rwa [one_smul] at h
  rw [map_slrLaw hS, dotProduct_one_sub_smul_vecMulVec_mulVec]
  congr 2
  set ℓ : Fin D → ℝ := fun i ↦ L (EuclideanSpace.single i 1, 0)
  set b := L (0, 1)
  rw [smul_smul]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm ℓ w, hw, ← variance_identity k (ℓ ⬝ᵥ ℓ) (w ⬝ᵥ ℓ) b]
  ring

end BDT24.Prob.G
