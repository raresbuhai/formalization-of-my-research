module

public import BDT24.Model
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Linear statistics of Gaussian vectors

Generic tools for `BDT24/Prob/Gauss.lean` [BDT24, Fact 2.1]:

* `BDT24.Prob.G.ext_of_map_dual`: two finite measures on a separable Banach space are equal if
  every continuous linear functional has the same law under both (Cramér–Wold).
* `BDT24.Prob.G.dual_prod_apply`: a continuous linear functional on `ℝ^D × ℝ` is
  `(x, t) ↦ ⟨ℓ, x⟩ + b t`.
* `BDT24.Prob.G.map_dotProduct_multivariateGaussian` (copied from ABBKS26): for `y ~ N(μ, S)`,
  `⟨v, y⟩ ~ N(⟨v, μ⟩, vᵀ S v)`; `BDT24.Prob.G.map_prod_dotProduct` and
  `BDT24.Prob.G.map_prod_dotProduct_gaussianReal`: the same for `⟨α, z⟩ + ⟨β, g⟩` with independent
  `z` and `g`, and for `⟨c, a⟩ + b w` with independent `a ~ N(0, S)` and `w ~ N(0, 1)`.
* Rank-one perturbations `r I - c w wᵀ`: their quadratic form
  (`BDT24.Prob.G.dotProduct_sub_smul_vecMulVec_mulVec`) and positive semidefiniteness
  (`BDT24.Prob.G.posSemidef_smul_one_sub`).
* `BDT24.Prob.G.sum_fin_two_mul`: a sum over `Fin (2 d)` splits into its two halves.
-/

@[expose] public section

namespace BDT24.Prob.G

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped RealInnerProductSpace

/-! ### Cramér–Wold -/

/-- **Cramér–Wold**: two finite measures on a separable Banach space are equal if every continuous
linear functional has the same law under both. -/
theorem ext_of_map_dual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : ∀ L : StrongDual ℝ E, μ.map L = ν.map L) :
    μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, h L]

/-- A continuous linear functional on `ℝ^ι × ℝ` is `(x, t) ↦ ⟨ℓ, x⟩ + b t`, with
`ℓ i = L (eᵢ, 0)` and `b = L (0, 1)`. -/
theorem dual_prod_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : StrongDual ℝ (EuclideanSpace ℝ ι × ℝ)) (x : EuclideanSpace ℝ ι) (t : ℝ) :
    L (x, t) = (fun i ↦ L (EuclideanSpace.single i 1, 0)) ⬝ᵥ x.ofLp + L (0, 1) * t := by
  have h1 : L (x, t) = L (x, 0) + L (0, t) := by rw [← map_add]; simp
  have h2 : L (0, t) = L (0, 1) * t := by
    rw [show ((0 : EuclideanSpace ℝ ι), t) = t • ((0 : EuclideanSpace ℝ ι), (1 : ℝ)) by simp,
      map_smul, smul_eq_mul, mul_comm]
  have h3 : L (x, 0) = ∑ i, x i * L (EuclideanSpace.single i 1, 0) := by
    have hx : x = ∑ i, x i • EuclideanSpace.single i (1 : ℝ) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr x]
      simp
    change (L.comp (ContinuousLinearMap.inl ℝ _ ℝ)) x = _
    conv_lhs => rw [hx]
    simp [map_sum, map_smul]
  rw [h1, h2, h3, dotProduct]
  simp [mul_comm]

/-! ### Laws of linear statistics -/

section Linear

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- `y ↦ v ⬝ᵥ y` is the continuous linear functional `⟪v, ·⟫`. -/
theorem dotProduct_eq_innerSL (v : ι → ℝ) :
    (fun y : EuclideanSpace ℝ ι ↦ v ⬝ᵥ y.ofLp) = ⇑(innerSL ℝ (toLp 2 v)) := by
  ext y
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

/-- A linear statistic is measurable. -/
theorem measurable_dotProduct (v : ι → ℝ) :
    Measurable fun y : EuclideanSpace ℝ ι ↦ v ⬝ᵥ y.ofLp := by
  rw [dotProduct_eq_innerSL]
  exact (innerSL ℝ (toLp 2 v)).continuous.measurable

/-- **The law of a linear statistic** (copied from ABBKS26): for `y ~ N(μ, S)`,
`⟨v, y⟩ ~ N(⟨v, μ⟩, vᵀ S v)`. -/
theorem map_dotProduct_multivariateGaussian [DecidableEq ι] {μ : EuclideanSpace ℝ ι}
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (v : ι → ℝ) :
    (multivariateGaussian μ S).map (fun y ↦ v ⬝ᵥ y.ofLp) =
      gaussianReal (v ⬝ᵥ μ.ofLp) (v ⬝ᵥ (S *ᵥ v)).toNNReal := by
  rw [dotProduct_eq_innerSL, IsGaussian.map_eq_gaussianReal]
  congr 2
  · rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      integral_id_multivariateGaussian]
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  · change Var[fun u ↦ ⟪toLp 2 v, u⟫; multivariateGaussian μ S] = _
    rw [← covarianceBilin_self IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS]

/-- The law of `f x + g y` for independent `x ~ μ` and `y ~ ν` is the convolution of the laws of
`f x` and `g y`. -/
theorem map_prod_add {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) [SFinite ν] {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (μ.prod ν).map (fun p ↦ f p.1 + g p.2) = (μ.map f) ∗ (ν.map g) := by
  rw [Measure.conv, Measure.map_prod_map _ _ hf hg,
    Measure.map_map measurable_add (hf.prodMap hg)]
  rfl

/-- The quadratic form of a positive semidefinite real matrix is nonnegative. -/
theorem quad_nonneg {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (v : ι → ℝ) :
    0 ≤ v ⬝ᵥ (S *ᵥ v) := by
  simpa using hS.dotProduct_mulVec_nonneg v

/-- For independent `z ~ N(0, S)` and `g ~ N(0, T)`, `⟨α, z⟩ + ⟨β, g⟩ ~ N(0, αᵀ S α + βᵀ T β)`. -/
theorem map_prod_dotProduct [DecidableEq ι] [DecidableEq κ] {S : Matrix ι ι ℝ}
    {T : Matrix κ κ ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef) (α : ι → ℝ) (β : κ → ℝ) :
    ((multivariateGaussian 0 S).prod (multivariateGaussian 0 T)).map
        (fun p ↦ α ⬝ᵥ p.1.ofLp + β ⬝ᵥ p.2.ofLp) =
      gaussianReal 0 (α ⬝ᵥ (S *ᵥ α) + β ⬝ᵥ (T *ᵥ β)).toNNReal := by
  rw [map_prod_add _ _ (measurable_dotProduct α) (measurable_dotProduct β),
    map_dotProduct_multivariateGaussian hS, map_dotProduct_multivariateGaussian hT,
    gaussianReal_conv_gaussianReal, Real.toNNReal_add (quad_nonneg hS α) (quad_nonneg hT β)]
  simp

/-- For independent `a ~ N(0, S)` and `w ~ N(0, 1)`, `⟨c, a⟩ + b w ~ N(0, cᵀ S c + b²)`. -/
theorem map_prod_dotProduct_gaussianReal [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (c : ι → ℝ) (b : ℝ) :
    ((multivariateGaussian 0 S).prod (gaussianReal 0 1)).map (fun p ↦ c ⬝ᵥ p.1.ofLp + b * p.2) =
      gaussianReal 0 (c ⬝ᵥ (S *ᵥ c) + b ^ 2).toNNReal := by
  rw [map_prod_add _ _ (measurable_dotProduct c) (measurable_const_mul b),
    map_dotProduct_multivariateGaussian hS, gaussianReal_map_const_mul,
    gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · ext
    simp [Real.coe_toNNReal _ (add_nonneg (quad_nonneg hS c) (sq_nonneg b)),
      Real.coe_toNNReal _ (quad_nonneg hS c)]

end Linear

/-! ### Rank-one perturbations of the identity -/

section RankOne

variable {ι : Type*} [Fintype ι]

/-- The quadratic form of `r I - c w wᵀ`: `aᵀ (r I - c w wᵀ) a = r ⟨a, a⟩ - c ⟨w, a⟩²`. -/
theorem dotProduct_sub_smul_vecMulVec_mulVec [DecidableEq ι] (r c : ℝ) (w a : ι → ℝ) :
    a ⬝ᵥ ((r • (1 : Matrix ι ι ℝ) - c • vecMulVec w w) *ᵥ a) = r * (a ⬝ᵥ a) - c * (w ⬝ᵥ a) ^ 2 := by
  rw [sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, dotProduct_comm a w]
  ring

/-- The quadratic form of `I - c w wᵀ`: `aᵀ (I - c w wᵀ) a = ⟨a, a⟩ - c ⟨w, a⟩²`. -/
theorem dotProduct_one_sub_smul_vecMulVec_mulVec [DecidableEq ι] (c : ℝ) (w a : ι → ℝ) :
    a ⬝ᵥ ((1 - c • vecMulVec w w) *ᵥ a) = a ⬝ᵥ a - c * (w ⬝ᵥ a) ^ 2 := by
  simpa using dotProduct_sub_smul_vecMulVec_mulVec 1 c w a

/-- Cauchy–Schwarz for the dot product: `⟨w, a⟩² ≤ ⟨w, w⟩ ⟨a, a⟩`. -/
theorem dotProduct_sq_le (w a : ι → ℝ) : (w ⬝ᵥ a) ^ 2 ≤ (w ⬝ᵥ w) * (a ⬝ᵥ a) := by
  simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w a

/-- `r I - c w wᵀ` is positive semidefinite when `0 ≤ c` and `c ⟨w, w⟩ ≤ r`. -/
theorem posSemidef_smul_one_sub [DecidableEq ι] (w : ι → ℝ) {r c : ℝ} (hc : 0 ≤ c)
    (h : c * (w ⬝ᵥ w) ≤ r) :
    (r • (1 : Matrix ι ι ℝ) - c • vecMulVec w w).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun a ↦ ?_
  · ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [vecMulVec, hij, Ne.symm hij, mul_comm]
  · rw [star_trivial, dotProduct_sub_smul_vecMulVec_mulVec]
    have h1 := dotProduct_sq_le w a
    have h2 : 0 ≤ a ⬝ᵥ a := by simpa using dotProduct_self_star_nonneg a
    nlinarith [mul_le_mul_of_nonneg_left h1 hc, mul_nonneg (sub_nonneg.2 h) h2]

/-- `c w wᵀ` is positive semidefinite when `0 ≤ c`. -/
theorem posSemidef_smul_vecMulVec {n : Type*} [Finite n] (w : n → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    (c • vecMulVec w w).PosSemidef := by
  simpa using (posSemidef_vecMulVec_self_star w).smul hc

end RankOne

/-! ### Sums over `Fin (2 d)` -/

/-- A sum over `Fin (2 d)` is the sum over its first `d` and its last `d` elements. -/
theorem sum_fin_two_mul {M : Type*} [AddCommMonoid M] (d : ℕ) (f : Fin (2 * d) → M) :
    ∑ i, f i = ∑ j : Fin d, f ⟨j, by omega⟩ + ∑ j : Fin d, f ⟨j + d, by omega⟩ := by
  rw [← (finCongr (two_mul d).symm).sum_comp, Fin.sum_univ_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun j _ ↦ congrArg f (Fin.ext rfl)
  · exact Finset.sum_congr rfl fun j _ ↦ congrArg f (Fin.ext (by simp [add_comm]))

end BDT24.Prob.G
