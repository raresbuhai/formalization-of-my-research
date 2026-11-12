module

public import BDT24.Model
public import BDT24.Prob.Gauss.Spike

/-!
# The regression instances of the reduction [BDT24, Fact 2.1]

A planted point `z ~ N(0, I - θ x xᵀ)` and a null point `g ~ N(0, I)` in `ℝ^{d+1}` give the
regression point `pairMap d (z, g)`: the design is the coordinates `2, …, d+1` of `z` and then of
`g`, the response is `√(2/3) (z₁ + g₁)`. It is a sample of sparse linear regression with noise
variance `1` (`BDT24.Prob.pairMap_fwd`): with the sign pattern `v` of the spike, the first
coordinate is `z₁ = ⟨v/2, z_{2..}⟩ + w'` with `w' ~ N(0, 1/2)` independent of the rest, so the
design covariance is `diag(I - v vᵀ/(k+2), I)` (`BDT24.Prob.covF`) and the secret is
`(v/√6, 0)` (`BDT24.Prob.xsF`). The instance is bounded (`BDT24.Prob.bounded_fwd`). The same
holds with the roles of the two points swapped (`BDT24.Prob.pairMap_bwd`).

The statistics of the analysis of the paired test: the residual `z₁ - ⟨v/2, z_{2..}⟩`
(`BDT24.Prob.noiseStat`), of variance `1/2`; the difference `⟨v/2, z_{2..}⟩ - g₁`
(`BDT24.Prob.otherStat`), of variance `1 + k/(2(k+2)) ≥ 1`; the response, of variance
`(2/3)((k+1)/(k+2) + 1) ∈ [1, 4/3]`; and the coordinates of `z`, of variance in `[1/2, 1]`.

The proofs (auxiliary facts in `BDT24.Prob.G`, with `BDT24/Prob/Gauss/Linear.lean` and
`BDT24/Prob/Gauss/Spike.lean`): the planted covariance is `I - u uᵀ/(k+2)` for `u = (-1, v)`, and
`covF = I - w wᵀ/(k+2)`, `xsF = w/√6` for `w = (v, 0)`. Both sides of `pairMap_fwd` are compared
by Cramér–Wold: a functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` is, on either side, a centered Gaussian of
variance `(4/3) b² + ‖ℓ‖² - (⟨w, ℓ⟩ - √(2/3) b)²/(k+2)`. Boundedness follows from Cauchy–Schwarz
`⟨w, a⟩² ≤ k ‖a‖²`, and the four laws from the law of a linear statistic of independent Gaussians.
-/

@[expose] public section

namespace BDT24.Prob

open MeasureTheory ProbabilityTheory Matrix

/-- The regression point of a pair of points of `ℝ^{d+1}`: the design is the coordinates
`2, …, d+1` of the first and then of the second point, the response `√(2/3)` times the sum of
their first coordinates. -/
noncomputable def pairMap (d : ℕ)
    (zg : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin (2 * d)) × ℝ :=
  (WithLp.toLp 2 fun i : Fin (2 * d) ↦
      if h : (i : ℕ) < d then zg.1 ⟨i + 1, by omega⟩
      else zg.2 ⟨i - d + 1, by have := i.isLt; omega⟩,
    √(2 / 3) * (zg.1 0 + zg.2 0))

/-- The design covariance `diag(I - v vᵀ/(k+2), I)` when the planted point comes first. -/
noncomputable def covF (d k : ℕ) (v : Fin d → SignType) : Matrix (Fin (2 * d)) (Fin (2 * d)) ℝ :=
  fun i j ↦
    if hi : (i : ℕ) < d then
      if hj : (j : ℕ) < d then
        (if i = j then 1 else 0) - (v ⟨i, hi⟩ : ℝ) * (v ⟨j, hj⟩ : ℝ) / ((k : ℝ) + 2)
      else 0
    else if i = j then 1 else 0

/-- The design covariance `diag(I, I - v vᵀ/(k+2))` when the planted point comes second. -/
noncomputable def covB (d k : ℕ) (v : Fin d → SignType) : Matrix (Fin (2 * d)) (Fin (2 * d)) ℝ :=
  fun i j ↦
    if hi : d ≤ (i : ℕ) then
      if hj : d ≤ (j : ℕ) then
        (if i = j then 1 else 0) -
          (v ⟨i - d, by have := i.isLt; omega⟩ : ℝ) * (v ⟨j - d, by have := j.isLt; omega⟩ : ℝ) /
            ((k : ℝ) + 2)
      else 0
    else if i = j then 1 else 0

/-- The secret `(v/√6, 0)` when the planted point comes first. -/
noncomputable def xsF (d : ℕ) (v : Fin d → SignType) : Fin (2 * d) → ℝ :=
  fun i ↦ if h : (i : ℕ) < d then (v ⟨i, h⟩ : ℝ) / √6 else 0

/-- The secret `(0, v/√6)` when the planted point comes second. -/
noncomputable def xsB (d : ℕ) (v : Fin d → SignType) : Fin (2 * d) → ℝ :=
  fun i ↦ if h : d ≤ (i : ℕ) then (v ⟨i - d, by have := i.isLt; omega⟩ : ℝ) / √6 else 0

/-- The planted law of one point with sign pattern `v`. -/
noncomputable abbrev plantedLaw (d k : ℕ) (v : Fin d → SignType) :
    Measure (EuclideanSpace ℝ (Fin (d + 1))) :=
  multivariateGaussian 0 (spikedCov (theta k) (spikeVector k v))

/-- The null law of one point. -/
noncomputable abbrev nullLaw (m : ℕ) : Measure (EuclideanSpace ℝ (Fin m)) :=
  multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)


/-! ### Auxiliary facts (namespace `BDT24.Prob.G`) -/

namespace G

/-- The sign pattern `v` on the first block of `Fin (2 d)`: `covF = I - w wᵀ/(k+2)` and
`xsF = w/√6` for this `w`. -/
noncomputable def wF {d : ℕ} (v : Fin d → SignType) : Fin (2 * d) → ℝ :=
  fun i ↦ if h : (i : ℕ) < d then (v ⟨i, h⟩ : ℝ) else 0

/-- The sign pattern `v` on the second block of `Fin (2 d)`: `covB = I - w wᵀ/(k+2)` and
`xsB = w/√6` for this `w`. -/
noncomputable def wB {d : ℕ} (v : Fin d → SignType) : Fin (2 * d) → ℝ :=
  fun i ↦ if h : d ≤ (i : ℕ) then (v ⟨i - d, by have := i.isLt; omega⟩ : ℝ) else 0

variable {d k : ℕ} {v : Fin d → SignType}

/-- `wF` on the first block. -/
theorem wF_left (v : Fin d → SignType) (j : Fin d) : wF v ⟨j, by omega⟩ = v j := by
  simp [wF]

/-- `wF` on the second block. -/
theorem wF_right (v : Fin d → SignType) (j : Fin d) : wF v ⟨j + d, by omega⟩ = 0 := by
  simp [wF]

/-- `wB` on the first block. -/
theorem wB_left (v : Fin d → SignType) (j : Fin d) : wB v ⟨j, by omega⟩ = 0 := by
  simp [wB]

/-- `wB` on the second block. -/
theorem wB_right (v : Fin d → SignType) (j : Fin d) : wB v ⟨j + d, by omega⟩ = v j := by
  simp [wB]

/-- The design covariance with the planted point first is `I - w wᵀ/(k+2)` for `w = wF v`. -/
theorem covF_eq (d k : ℕ) (v : Fin d → SignType) :
    covF d k v = 1 - ((k : ℝ) + 2)⁻¹ • vecMulVec (wF v) (wF v) := by
  ext i j
  simp only [covF, wF, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  by_cases hi : (i : ℕ) < d <;> by_cases hj : (j : ℕ) < d <;>
    simp only [hi, hj, ↓reduceDIte, mul_zero, zero_mul, sub_zero]
  · ring
  · have : i ≠ j := fun h ↦ hj (h ▸ hi)
    simp [this]

/-- The design covariance with the planted point second is `I - w wᵀ/(k+2)` for `w = wB v`. -/
theorem covB_eq (d k : ℕ) (v : Fin d → SignType) :
    covB d k v = 1 - ((k : ℝ) + 2)⁻¹ • vecMulVec (wB v) (wB v) := by
  ext i j
  simp only [covB, wB, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply,
    smul_eq_mul]
  by_cases hi : d ≤ (i : ℕ) <;> by_cases hj : d ≤ (j : ℕ) <;>
    simp only [hi, hj, ↓reduceDIte, mul_zero, zero_mul, sub_zero]
  · ring
  · have : i ≠ j := fun h ↦ hj (h ▸ hi)
    simp [this]

/-- The secret with the planted point first is `wF v/√6`. -/
theorem xsF_eq (d : ℕ) (v : Fin d → SignType) : xsF d v = (√6)⁻¹ • wF v := by
  funext i
  simp only [xsF, wF, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [div_eq_inv_mul]

/-- The secret with the planted point second is `wB v/√6`. -/
theorem xsB_eq (d : ℕ) (v : Fin d → SignType) : xsB d v = (√6)⁻¹ • wB v := by
  funext i
  simp only [xsB, wB, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp [div_eq_inv_mul]

/-- `⟨wF v, ℓ⟩ = ∑ⱼ vⱼ ℓⱼ` over the first block. -/
theorem wF_dotProduct (v : Fin d → SignType) (ℓ : Fin (2 * d) → ℝ) :
    wF v ⬝ᵥ ℓ = ∑ j : Fin d, (v j : ℝ) * ℓ ⟨j, by omega⟩ := by
  rw [dotProduct, sum_fin_two_mul]
  simp [wF_left, wF_right]

/-- `⟨wB v, ℓ⟩ = ∑ⱼ vⱼ ℓ_{d+j}` over the second block. -/
theorem wB_dotProduct (v : Fin d → SignType) (ℓ : Fin (2 * d) → ℝ) :
    wB v ⬝ᵥ ℓ = ∑ j : Fin d, (v j : ℝ) * ℓ ⟨j + d, by omega⟩ := by
  rw [dotProduct, sum_fin_two_mul]
  simp [wB_left, wB_right]

/-- `‖wF v‖² = k`. -/
theorem wF_dotProduct_self (hv : v ∈ spikeSigns d k) : wF v ⬝ᵥ wF v = k := by
  rw [wF_dotProduct, ← sum_sq_signs hv]
  simp [wF_left, sq]

/-- `‖wB v‖² = k`. -/
theorem wB_dotProduct_self (hv : v ∈ spikeSigns d k) : wB v ⬝ᵥ wB v = k := by
  rw [wB_dotProduct, ← sum_sq_signs hv]
  simp [wB_right, sq]

/-- `wF v` has as many nonzero entries as `v`. -/
theorem card_wF (v : Fin d → SignType) :
    (Finset.univ.filter fun i ↦ wF v i ≠ 0).card = (Finset.univ.filter fun j ↦ v j ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, sum_fin_two_mul]
  simp [wF_left, wF_right, signType_coe_ne_zero]

/-- `wB v` has as many nonzero entries as `v`. -/
theorem card_wB (v : Fin d → SignType) :
    (Finset.univ.filter fun i ↦ wB v i ≠ 0).card = (Finset.univ.filter fun j ↦ v j ≠ 0).card := by
  rw [Finset.card_filter, Finset.card_filter, sum_fin_two_mul]
  simp [wB_left, wB_right, signType_coe_ne_zero]

/-- An instance `(I - w wᵀ/(k+2), w/√6)` with `‖w‖² = k` and at most `k` nonzero entries of `w` is
bounded. -/
theorem isBoundedInstance_rankOne {D : ℕ} (w : Fin D → ℝ) (hw : w ⬝ᵥ w = k)
    (hcard : (Finset.univ.filter fun i ↦ w i ≠ 0).card ≤ k) :
    IsBoundedInstance k (1 - ((k : ℝ) + 2)⁻¹ • vecMulVec w w) ((√6)⁻¹ • w) := by
  have hc : (0 : ℝ) ≤ ((k : ℝ) + 2)⁻¹ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hk2 : (0 : ℝ) < k + 2 := by positivity
    have h := posSemidef_smul_one_sub w (r := 1 - ((k : ℝ) + 2)⁻¹) hc (by
      rw [hw, inv_mul_eq_div, div_le_iff₀ hk2, sub_mul, inv_mul_cancel₀ hk2.ne', one_mul]
      linarith)
    convert h using 1
    rw [sub_smul, one_smul]
    abel
  · rw [sub_sub_cancel]
    exact posSemidef_smul_vecMulVec w hc
  · unfold IsSparse
    convert hcard using 3
    simp
  · have h6 : (√6)⁻¹ ^ 2 = 1 / 6 := by rw [inv_pow, Real.sq_sqrt (by norm_num), one_div]
    calc ∑ i, ((√6)⁻¹ • w) i ^ 2 = (√6)⁻¹ ^ 2 * (w ⬝ᵥ w) := by
          simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ k := by rw [h6, hw]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The coefficients of a functional of the regression point on the first point of the pair:
`√(2/3) b` on its first coordinate, `ℓ` on the first block of the design. -/
noncomputable def coefF (d : ℕ) (ℓ : Fin (2 * d) → ℝ) (b : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (b * √(2 / 3)) fun j ↦ ℓ ⟨j, by omega⟩

/-- The coefficients of a functional of the regression point on the second point of the pair:
`√(2/3) b` on its first coordinate, `ℓ` on the second block of the design. -/
noncomputable def coefB (d : ℕ) (ℓ : Fin (2 * d) → ℝ) (b : ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons (b * √(2 / 3)) fun j ↦ ℓ ⟨j + d, by omega⟩

/-- The design of the regression point on the first block is the first point. -/
theorem pairMap_left (zg : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1)))
    (j : Fin d) : (pairMap d zg).1 ⟨j, by omega⟩ = zg.1 j.succ := by
  simp only [pairMap, PiLp.toLp_apply, j.isLt, ↓reduceDIte]
  rfl

/-- The design of the regression point on the second block is the second point. -/
theorem pairMap_right (zg : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1)))
    (j : Fin d) : (pairMap d zg).1 ⟨j + d, by omega⟩ = zg.2 j.succ := by
  simp only [pairMap, PiLp.toLp_apply, show ¬((j : ℕ) + d < d) by omega, ↓reduceDIte]
  exact congrArg zg.2.ofLp (Fin.ext (by simp))

/-- The pairing map is measurable. -/
theorem measurable_pairMap (d : ℕ) : Measurable (pairMap d) := by
  refine Measurable.prodMk ?_ ?_
  · refine (WithLp.measurable_toLp 2 _).comp (Measurable.of_eval fun i ↦ ?_)
    by_cases h : (i : ℕ) < d
    · simp only [h, ↓reduceDIte]
      fun_prop
    · simp only [h, ↓reduceDIte]
      fun_prop
  · fun_prop

/-- A functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` of the regression point of `(z, g)` is
`⟨coefF, z⟩ + ⟨coefB, g⟩`. -/
theorem dual_pairMap (L : StrongDual ℝ (EuclideanSpace ℝ (Fin (2 * d)) × ℝ))
    (zg : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1))) :
    L (pairMap d zg) =
      coefF d (fun i ↦ L (EuclideanSpace.single i 1, 0)) (L (0, 1)) ⬝ᵥ zg.1.ofLp +
        coefB d (fun i ↦ L (EuclideanSpace.single i 1, 0)) (L (0, 1)) ⬝ᵥ zg.2.ofLp := by
  rw [show pairMap d zg = ((pairMap d zg).1, (pairMap d zg).2) from rfl, dual_prod_apply,
    dotProduct, sum_fin_two_mul]
  simp only [pairMap_left, pairMap_right]
  simp only [dotProduct, Fin.sum_univ_succ, coefF, coefB, Fin.cons_zero, Fin.cons_succ, pairMap]
  ring

/-- `‖coefF‖² + ‖coefB‖² = (4/3) b² + ‖ℓ‖²`. -/
theorem coef_dotProduct_self (ℓ : Fin (2 * d) → ℝ) (b : ℝ) :
    coefF d ℓ b ⬝ᵥ coefF d ℓ b + coefB d ℓ b ⬝ᵥ coefB d ℓ b = 4 / 3 * b ^ 2 + ℓ ⬝ᵥ ℓ := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  simp only [dotProduct, Fin.sum_univ_succ, coefF, coefB, Fin.cons_zero, Fin.cons_succ]
  rw [sum_fin_two_mul d (fun i ↦ ℓ i * ℓ i)]
  linear_combination (2 * b ^ 2) * h

/-- `⟨(-1, v), coefF⟩ = ⟨wF v, ℓ⟩ - √(2/3) b`. -/
theorem spikeDir_dotProduct_coefF (v : Fin d → SignType) (ℓ : Fin (2 * d) → ℝ) (b : ℝ) :
    spikeDir v ⬝ᵥ coefF d ℓ b = wF v ⬝ᵥ ℓ - b * √(2 / 3) := by
  rw [wF_dotProduct]
  simp only [dotProduct, Fin.sum_univ_succ, coefF, spikeDir, Fin.cons_zero, Fin.cons_succ]
  ring

/-- `⟨(-1, v), coefB⟩ = ⟨wB v, ℓ⟩ - √(2/3) b`. -/
theorem spikeDir_dotProduct_coefB (v : Fin d → SignType) (ℓ : Fin (2 * d) → ℝ) (b : ℝ) :
    spikeDir v ⬝ᵥ coefB d ℓ b = wB v ⬝ᵥ ℓ - b * √(2 / 3) := by
  rw [wB_dotProduct]
  simp only [dotProduct, Fin.sum_univ_succ, coefB, spikeDir, Fin.cons_zero, Fin.cons_succ]
  ring

/-- The law of a functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` of the regression point of a planted and a
null point: `N(0, (4/3) b² + ‖ℓ‖² - (⟨wF v, ℓ⟩ - √(2/3) b)²/(k+2))`. -/
theorem map_pairMap_fwd (hv : v ∈ spikeSigns d k)
    (L : StrongDual ℝ (EuclideanSpace ℝ (Fin (2 * d)) × ℝ)) :
    (((plantedLaw d k v).prod (nullLaw (d + 1))).map (pairMap d)).map L =
      gaussianReal 0
        (4 / 3 * L (0, 1) ^ 2 +
            (fun i ↦ L (EuclideanSpace.single i 1, 0)) ⬝ᵥ
              (fun i ↦ L (EuclideanSpace.single i 1, 0)) -
          ((k : ℝ) + 2)⁻¹ *
            (wF v ⬝ᵥ (fun i ↦ L (EuclideanSpace.single i 1, 0)) - L (0, 1) * √(2 / 3)) ^ 2
          ).toNNReal := by
  rw [Measure.map_map L.continuous.measurable (measurable_pairMap d),
    show ⇑L ∘ pairMap d = _ from funext (dual_pairMap L),
    map_prod_dotProduct (posSemidef_spikedCov hv) PosSemidef.one, spikedCov_eq,
    dotProduct_one_sub_smul_vecMulVec_mulVec, one_mulVec, spikeDir_dotProduct_coefF,
    ← coef_dotProduct_self]
  congr 2
  ring

/-- The law of a functional `(a, y) ↦ ⟨ℓ, a⟩ + b y` of the regression point of a null and a
planted point: `N(0, (4/3) b² + ‖ℓ‖² - (⟨wB v, ℓ⟩ - √(2/3) b)²/(k+2))`. -/
theorem map_pairMap_bwd (hv : v ∈ spikeSigns d k)
    (L : StrongDual ℝ (EuclideanSpace ℝ (Fin (2 * d)) × ℝ)) :
    (((nullLaw (d + 1)).prod (plantedLaw d k v)).map (pairMap d)).map L =
      gaussianReal 0
        (4 / 3 * L (0, 1) ^ 2 +
            (fun i ↦ L (EuclideanSpace.single i 1, 0)) ⬝ᵥ
              (fun i ↦ L (EuclideanSpace.single i 1, 0)) -
          ((k : ℝ) + 2)⁻¹ *
            (wB v ⬝ᵥ (fun i ↦ L (EuclideanSpace.single i 1, 0)) - L (0, 1) * √(2 / 3)) ^ 2
          ).toNNReal := by
  rw [Measure.map_map L.continuous.measurable (measurable_pairMap d),
    show ⇑L ∘ pairMap d = _ from funext (dual_pairMap L),
    map_prod_dotProduct PosSemidef.one (posSemidef_spikedCov hv), spikedCov_eq,
    dotProduct_one_sub_smul_vecMulVec_mulVec, one_mulVec, spikeDir_dotProduct_coefB,
    ← coef_dotProduct_self]
  congr 2
  ring

end G

/-- **[BDT24, Fact 2.1]**, planted point first: the regression point of a planted and a null
point is a sample of sparse linear regression with design covariance `covF` and secret `xsF`. -/
theorem pairMap_fwd {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    ((plantedLaw d k v).prod (nullLaw (d + 1))).map (pairMap d) =
      slrLaw (covF d k v) (xsF d v) := by
  have : IsFiniteMeasure (slrLaw (covF d k v) (xsF d v)) := by rw [slrLaw]; infer_instance
  refine G.ext_of_map_dual fun L ↦ ?_
  rw [G.map_pairMap_fwd hv, G.covF_eq, G.xsF_eq,
    G.map_slrLaw_rankOne _ (G.wF_dotProduct_self hv)]

/-- **[BDT24, Fact 2.1]**, planted point second. -/
theorem pairMap_bwd {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    ((nullLaw (d + 1)).prod (plantedLaw d k v)).map (pairMap d) =
      slrLaw (covB d k v) (xsB d v) := by
  have : IsFiniteMeasure (slrLaw (covB d k v) (xsB d v)) := by rw [slrLaw]; infer_instance
  refine G.ext_of_map_dual fun L ↦ ?_
  rw [G.map_pairMap_bwd hv, G.covB_eq, G.xsB_eq,
    G.map_slrLaw_rankOne _ (G.wB_dotProduct_self hv)]

/-- The regression instance with the planted point first is bounded. -/
theorem bounded_fwd {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    IsBoundedInstance k (covF d k v) (xsF d v) := by
  rw [G.covF_eq, G.xsF_eq]
  refine G.isBoundedInstance_rankOne _ (G.wF_dotProduct_self hv) ?_
  rw [G.card_wF]
  exact (Finset.mem_filter.mp hv).2.le

/-- The regression instance with the planted point second is bounded. -/
theorem bounded_bwd {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    IsBoundedInstance k (covB d k v) (xsB d v) := by
  rw [G.covB_eq, G.xsB_eq]
  refine G.isBoundedInstance_rankOne _ (G.wB_dotProduct_self hv) ?_
  rw [G.card_wB]
  exact (Finset.mem_filter.mp hv).2.le

/-- The residual `z₁ - ⟨v/2, z_{2..}⟩` of a planted point. -/
noncomputable def noiseStat (d : ℕ) (v : Fin d → SignType) (z : EuclideanSpace ℝ (Fin (d + 1))) :
    ℝ :=
  z 0 - ∑ j : Fin d, (v j : ℝ) / 2 * z j.succ

/-- The difference `⟨v/2, z_{2..}⟩ - g₁` of a planted point `z` and a null point `g`. -/
noncomputable def otherStat (d : ℕ) (v : Fin d → SignType)
    (zg : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1))) : ℝ :=
  ∑ j : Fin d, (v j : ℝ) / 2 * zg.1 j.succ - zg.2 0

/-- The residual of a planted point is `N(0, 1/2)`. -/
theorem law_noiseStat {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    (plantedLaw d k v).map (noiseStat d v) = gaussianReal 0 (1 / 2 : ℝ).toNNReal := by
  have hk := G.sum_sq_signs hv
  have h : noiseStat d v = fun z ↦
      (Fin.cons (1 : ℝ) (fun j ↦ -((v j : ℝ) / 2)) : Fin (d + 1) → ℝ) ⬝ᵥ z.ofLp := by
    funext z
    simp only [noiseStat, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, neg_mul,
      Finset.sum_neg_distrib]
    ring
  rw [h, G.map_dotProduct_multivariateGaussian (G.posSemidef_spikedCov hv), G.spikedCov_eq,
    G.dotProduct_one_sub_smul_vecMulVec_mulVec]
  congr 1
  · simp
  · congr 1
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, G.spikeDir]
    have h1 : ∑ j : Fin d, -((v j : ℝ) / 2) * -((v j : ℝ) / 2) = k / 4 := by
      rw [← hk, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have h2 : ∑ j : Fin d, (v j : ℝ) * -((v j : ℝ) / 2) = -(k / 2) := by
      rw [← hk, Finset.sum_div, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [h1, h2]
    field_simp
    ring

/-- The difference of a planted and a null point is `N(0, 1 + k/(2(k+2)))`. -/
theorem law_otherStat {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    ((plantedLaw d k v).prod (nullLaw (d + 1))).map (otherStat d v) =
      gaussianReal 0 (1 + (k : ℝ) / (2 * ((k : ℝ) + 2))).toNNReal := by
  have hk := G.sum_sq_signs hv
  have h : otherStat d v = fun zg ↦
      (Fin.cons (0 : ℝ) (fun j ↦ (v j : ℝ) / 2) : Fin (d + 1) → ℝ) ⬝ᵥ zg.1.ofLp +
        (Fin.cons (-1 : ℝ) (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) ⬝ᵥ zg.2.ofLp := by
    funext zg
    simp only [otherStat, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    ring
  rw [h, G.map_prod_dotProduct (G.posSemidef_spikedCov hv) PosSemidef.one, G.spikedCov_eq,
    G.dotProduct_one_sub_smul_vecMulVec_mulVec, one_mulVec]
  congr 2
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, G.spikeDir,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have h1 : ∑ j : Fin d, (v j : ℝ) / 2 * ((v j : ℝ) / 2) = k / 4 := by
    rw [← hk, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have h2 : ∑ j : Fin d, (v j : ℝ) * ((v j : ℝ) / 2) = k / 2 := by
    rw [← hk, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h1, h2]
  field_simp
  ring

/-- The response of a planted and a null point is `N(0, (2/3)((k+1)/(k+2) + 1))`. -/
theorem law_resp {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) :
    ((plantedLaw d k v).prod (nullLaw (d + 1))).map (fun zg ↦ √(2 / 3) * (zg.1 0 + zg.2 0)) =
      gaussianReal 0 (2 / 3 * (((k : ℝ) + 1) / ((k : ℝ) + 2) + 1)).toNNReal := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have h : (fun zg : EuclideanSpace ℝ (Fin (d + 1)) × EuclideanSpace ℝ (Fin (d + 1)) ↦
      √(2 / 3) * (zg.1 0 + zg.2 0)) = fun zg ↦
      (Fin.cons √(2 / 3) (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) ⬝ᵥ zg.1.ofLp +
        (Fin.cons √(2 / 3) (0 : Fin d → ℝ) : Fin (d + 1) → ℝ) ⬝ᵥ zg.2.ofLp := by
    funext zg
    simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero]
    ring
  rw [h, G.map_prod_dotProduct (G.posSemidef_spikedCov hv) PosSemidef.one, G.spikedCov_eq,
    G.dotProduct_one_sub_smul_vecMulVec_mulVec, one_mulVec]
  congr 2
  simp only [dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, G.spikeDir,
    Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  linear_combination (6 * (k : ℝ) + 9) * hs

/-- The coordinates of a planted point have variance between `1/2` and `1`. -/
theorem law_coord {d k : ℕ} {v : Fin d → SignType} (hv : v ∈ spikeSigns d k)
    (i : Fin (d + 1)) : ∃ σ2 : NNReal, (1 / 2 : ℝ) ≤ σ2 ∧ (σ2 : ℝ) ≤ 1 ∧
      (plantedLaw d k v).map (fun z ↦ z i) = gaussianReal 0 σ2 := by
  have hP := G.posSemidef_spikedCov hv
  have hSii : spikedCov (theta k) (spikeVector k v) i i =
      1 - ((k : ℝ) + 2)⁻¹ * G.spikeDir v i ^ 2 := by
    simp [G.spikedCov_eq, vecMulVec_apply, sq]
  have hu : G.spikeDir v i ^ 2 ≤ 1 := by
    cases i using Fin.cases with
    | zero => simp [G.spikeDir]
    | succ j =>
      simp only [G.spikeDir, Fin.cons_succ]
      rw [G.sq_signType]
      split_ifs <;> norm_num
  have hc0 : (0 : ℝ) ≤ ((k : ℝ) + 2)⁻¹ := by positivity
  have hc : ((k : ℝ) + 2)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hlo : 1 / 2 ≤ spikedCov (theta k) (spikeVector k v) i i := by
    rw [hSii]
    nlinarith [sq_nonneg (G.spikeDir v i), mul_le_mul_of_nonneg_left hu hc0]
  have hhi : spikedCov (theta k) (spikeVector k v) i i ≤ 1 := by
    rw [hSii]
    nlinarith [sq_nonneg (G.spikeDir v i), mul_nonneg hc0 (sq_nonneg (G.spikeDir v i))]
  refine ⟨(spikedCov (theta k) (spikeVector k v) i i).toNNReal, ?_, ?_, ?_⟩
  · rw [Real.coe_toNNReal _ (by linarith)]
    exact hlo
  · rw [Real.coe_toNNReal _ (by linarith)]
    exact hhi
  · rw [(measurePreserving_eval_multivariateGaussian hP).map_eq]
    simp

end BDT24.Prob
