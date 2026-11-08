module

public import BHJK25.Model
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.ProductMeasure

/-!
# The spectral distributions: notation and Gaussian facts

Notation for the distributions of [BHJK25, Section 3] (`BHJK25.spectralLaw`): the Gaussian matrix
`U` (`BHJK25.Spectral.gaussMat`, independent standard Gaussian entries, row by row) and the map
`(λ, U) ↦ U diag(λ) Uᵀ` (`BHJK25.Spectral.specMap`), together with the facts about Gaussians that
the proof of Theorem 3.1 uses:

* the eigenvalue law `μ_γ` is a probability distribution on `[-1, 0]` for `0 ≤ γ ≤ 1`;
* the Gaussian matrix is invariant under permutations of its columns and under multiplication by
  an orthogonal matrix on the left, and its columns are independent standard Gaussian vectors;
* `⟨w, u⟩` is `N(0, ‖w‖²)` for a standard Gaussian vector `u`;
* two Gaussian integrals: `E exp(Z²/4) = √2` and `E exp(-Z²/2) = 1/√2`.
-/

@[expose] public section

namespace BHJK25.Spectral

open MeasureTheory ProbabilityTheory Matrix

/-- The law of an `n × m` matrix with independent standard Gaussian entries, given row by row, as
in `BHJK25.spectralLaw`. -/
noncomputable def gaussMat (n m : ℕ) : Measure (Fin n → Fin m → ℝ) :=
  Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin m ↦ gaussianReal 0 1

/-- The law of a standard Gaussian vector in `ℝ^n`. -/
noncomputable def gaussVec (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n ↦ gaussianReal 0 1

/-- The map `(λ, U) ↦ U diag(λ) Uᵀ`. -/
def specMap (n m : ℕ) (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of p.2 * Matrix.diagonal p.1 * (Matrix.of p.2)ᵀ

/-- The eigenvalue vector of the null distribution: `m` independent draws from `μ_γ`. -/
noncomputable def nullEig (γ : ℝ) (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ : Fin m ↦ eigLaw γ

/-- The eigenvalue vector of the planted distribution: the last one is `spike`, the others are
independent draws from `μ_γ`. -/
noncomputable def plantedEig (γ : ℝ) (m : ℕ) (spike : ℝ) : Measure (Fin m → ℝ) :=
  Measure.pi fun i : Fin m ↦ if (i : ℕ) + 1 = m then Measure.dirac spike else eigLaw γ

variable {n m : ℕ}

theorem spectralLaw_eq (ν : Measure (Fin m → ℝ)) (n : ℕ) :
    spectralLaw ν n = (ν.prod (gaussMat n m)).map (specMap n m) := rfl

theorem nullLaw_eq (γ : ℝ) (m n : ℕ) :
    nullLaw γ m n = ((nullEig γ m).prod (gaussMat n m)).map (specMap n m) := rfl

theorem plantedLaw_eq (γ : ℝ) (m : ℕ) (spike : ℝ) (n : ℕ) :
    plantedLaw γ m spike n = ((plantedEig γ m spike).prod (gaussMat n m)).map (specMap n m) := rfl

theorem specMap_apply (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) (i j : Fin n) :
    specMap n m p i j = ∑ k, p.2 i k * p.1 k * p.2 j k := by
  simp [specMap, Matrix.mul_apply, Matrix.diagonal, mul_comm, mul_assoc]

theorem measurable_specMap : Measurable (specMap n m) := measurable_spectral

instance isProbabilityMeasure_gaussMat : IsProbabilityMeasure (gaussMat n m) := by
  unfold gaussMat; infer_instance

instance isProbabilityMeasure_gaussVec : IsProbabilityMeasure (gaussVec n) := by
  unfold gaussVec; infer_instance

/-! ### The eigenvalue law -/

theorem isProbabilityMeasure_eigLaw {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    IsProbabilityMeasure (eigLaw γ) := by
  constructor
  rw [eigLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc, smul_eq_mul,
    smul_eq_mul, mul_one, sub_neg_eq_add, zero_add, ENNReal.ofReal_one, mul_one,
    ← ENNReal.ofReal_add (by linarith) h0, sub_add_cancel, ENNReal.ofReal_one]

/-- `μ_γ` lives on `[-1, 0]`. -/
theorem ae_eigLaw_mem (γ : ℝ) : ∀ᵐ x ∂(eigLaw γ), x ∈ Set.Icc (-1 : ℝ) 0 := by
  rw [eigLaw, ae_add_measure_iff]
  refine ⟨Measure.ae_smul_measure ?_ _,
    Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _⟩
  exact (ae_dirac_iff measurableSet_Icc).2 ⟨by norm_num, le_rfl⟩

theorem sparsity_nonneg {C : ℝ} (hC : 0 ≤ C) (n : ℕ) : 0 ≤ sparsity C n :=
  le_min zero_le_one (div_nonneg (mul_nonneg hC (sq_nonneg _)) (Nat.cast_nonneg _))

theorem sparsity_le_one (C : ℝ) (n : ℕ) : sparsity C n ≤ 1 := min_le_left _ _

/-! ### Auxiliary facts about Gaussian vectors and product measures -/

namespace GaussAux

open WithLp

/-- The standard Gaussian vector is Mathlib's standard Gaussian measure on the Euclidean space
`ℝⁿ`, read in coordinates. -/
theorem gaussVec_eq_map_ofLp :
    gaussVec n = (stdGaussian (EuclideanSpace ℝ (Fin n))).map (ofLp (p := 2)) := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id.symm

/-- An orthogonal matrix, as a linear isometry of the Euclidean space `ℝⁿ`. -/
noncomputable def orthIso {O : Matrix (Fin n) (Fin n) ℝ} (hO : O ∈ orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := toLp 2 (O *ᵥ ofLp x)
  invFun x := toLp 2 (Oᵀ *ᵥ ofLp x)
  map_add' x y := by simp [mulVec_add]
  map_smul' c x := by simp [mulVec_smul]
  left_inv x := by
    have : Oᵀ * O = 1 := (mem_orthogonalGroup_iff' _ _).1 hO
    simp [mulVec_mulVec, this]
  right_inv x := by
    have : O * Oᵀ = 1 := (mem_orthogonalGroup_iff _ _).1 hO
    simp [mulVec_mulVec, this]
  norm_map' x := by
    have hO' : Oᵀ * O = 1 := (mem_orthogonalGroup_iff' _ _).1 hO
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    have h : (O *ᵥ ofLp x) ⬝ᵥ (O *ᵥ ofLp x) = ofLp x ⬝ᵥ ofLp x := by
      rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, hO', one_mulVec]
    simpa [dotProduct, sq] using h

/-- An orthogonal matrix does not change the law of a standard Gaussian vector. -/
theorem gaussVec_map_orth {O : Matrix (Fin n) (Fin n) ℝ} (hO : O ∈ orthogonalGroup (Fin n) ℝ) :
    (gaussVec n).map (fun u i ↦ ∑ k, O i k * u k) = gaussVec n := by
  have hf : (fun u i ↦ ∑ k, O i k * u k) ∘ ofLp (p := 2) = ofLp ∘ orthIso hO := by
    ext x i
    simp [orthIso, mulVec, dotProduct]
  rw [gaussVec_eq_map_ofLp, Measure.map_map (by fun_prop) (by fun_prop), hf,
    ← Measure.map_map (by fun_prop) (orthIso hO).continuous.measurable, stdGaussian_map]

variable {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]

/-- A product measure on `ι × κ`, curried, is a product of product measures. -/
theorem pi_map_curry (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι × κ ↦ μ).map (MeasurableEquiv.curry ι κ X) =
      Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ := by
  have h := Measure.infinitePi_map_curry (fun (_ : ι) (_ : κ) ↦ μ)
  simp only [Measure.infinitePi_eq_pi] at h
  exact h

/-- Transposing a doubly indexed family of independent draws from `μ` does not change its law. -/
theorem pi_pi_map_swap (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ).map (fun x j i ↦ x i j) =
      Measure.pi fun _ : κ ↦ Measure.pi fun _ : ι ↦ μ := by
  rw [← pi_map_curry, ← pi_map_curry, Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.pi_map_piCongrLeft (Equiv.prodComm ι κ) (fun _ ↦ μ),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- `E exp(b Z²)` for a standard Gaussian `Z`, as an integral against Lebesgue measure. -/
theorem integral_gaussianReal_exp (b : ℝ) :
    ∫ x, Real.exp (b * x ^ 2) ∂(gaussianReal 0 1) =
      (√(2 * Real.pi))⁻¹ * ∫ x, Real.exp (-(1 / 2 - b) * x ^ 2) := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero, gaussianPDFReal_def,
    ← integral_const_mul]
  congr 1 with x
  simp only [NNReal.coe_one, mul_one, sub_zero, smul_eq_mul, mul_assoc, ← Real.exp_add]
  congr 2
  ring

end GaussAux

/-! ### The Gaussian matrix -/

/-- Permuting the columns of the Gaussian matrix does not change its law. -/
theorem gaussMat_map_colPerm (σ : Equiv.Perm (Fin m)) :
    (gaussMat n m).map (fun U i j ↦ U i (σ j)) = gaussMat n m := by
  have h : MeasurePreserving (fun (u : Fin m → ℝ) j ↦ u (σ j))
      (Measure.pi fun _ ↦ gaussianReal 0 1) (Measure.pi fun _ ↦ gaussianReal 0 1) := by
    convert measurePreserving_arrowCongr' (fun _ : Fin m ↦ gaussianReal 0 1)
      (fun _ : Fin m ↦ gaussianReal 0 1) σ.symm (MeasurableEquiv.refl ℝ)
      (fun _ ↦ MeasurePreserving.id _)
    rfl
  exact (measurePreserving_pi _ _ fun _ ↦ h).map_eq

/-- The columns of the Gaussian matrix are independent standard Gaussian vectors. -/
theorem gaussMat_eq_map_cols :
    gaussMat n m = (Measure.pi fun _ : Fin m ↦ gaussVec n).map (fun V i j ↦ V j i) :=
  (GaussAux.pi_pi_map_swap _).symm

/-- Multiplying the Gaussian matrix by an orthogonal matrix on the left does not change its law. -/
theorem gaussMat_map_orth {O : Matrix (Fin n) (Fin n) ℝ} (hO : O ∈ orthogonalGroup (Fin n) ℝ) :
    (gaussMat n m).map (fun U i j ↦ ∑ k, O i k * U k j) = gaussMat n m := by
  have hv : MeasurePreserving (fun (u : Fin n → ℝ) (i : Fin n) ↦ ∑ k, O i k * u k)
      (gaussVec n) (gaussVec n) := ⟨by fun_prop, GaussAux.gaussVec_map_orth hO⟩
  have hc : (fun (U : Fin n → Fin m → ℝ) i j ↦ ∑ k, O i k * U k j) ∘ (fun V i j ↦ V j i) =
      (fun V i j ↦ V j i) ∘
        fun (V : Fin m → Fin n → ℝ) (j : Fin m) (i : Fin n) ↦ ∑ k, O i k * V j k := rfl
  rw [gaussMat_eq_map_cols, Measure.map_map (by fun_prop) (by fun_prop), hc,
    ← Measure.map_map (by fun_prop) (by fun_prop), (measurePreserving_pi _ _ fun _ ↦ hv).map_eq]

/-- `⟨w, u⟩` is `N(0, ‖w‖²)` for a standard Gaussian vector `u`. -/
theorem gaussVec_map_inner (w : Fin n → ℝ) :
    (gaussVec n).map (fun u ↦ ∑ i, w i * u i) = gaussianReal 0 (∑ i, w i ^ 2).toNNReal := by
  have hf : (fun u ↦ ∑ i, w i * u i) ∘ WithLp.ofLp (p := 2) =
      ⇑(innerSL ℝ (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin n))) := by
    ext x
    simp [innerSL_apply_apply, PiLp.inner_apply, mul_comm]
  rw [GaussAux.gaussVec_eq_map_ofLp, Measure.map_map (by fun_prop) (by fun_prop), hf,
    IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian,
    innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]

theorem integral_exp_sq_div_four :
    ∫ x, Real.exp (x ^ 2 / 4) ∂(gaussianReal 0 1) = √2 := by
  have h := GaussAux.integral_gaussianReal_exp (1 / 4)
  have e (x : ℝ) : 1 / 4 * x ^ 2 = x ^ 2 / 4 := by ring
  have e2 : Real.pi / (1 / 2 - 1 / 4) = 2 * (2 * Real.pi) := by ring
  have hpos : √(2 * Real.pi) ≠ 0 := by positivity
  simp only [e] at h
  rw [h, integral_gaussian, e2, Real.sqrt_mul zero_le_two (2 * Real.pi), mul_left_comm,
    inv_mul_cancel₀ hpos, mul_one]

theorem integral_exp_neg_sq_div_two :
    ∫ x, Real.exp (-(x ^ 2 / 2)) ∂(gaussianReal 0 1) = 1 / √2 := by
  have h := GaussAux.integral_gaussianReal_exp (-(1 / 2))
  have e (x : ℝ) : -(1 / 2) * x ^ 2 = -(x ^ 2 / 2) := by ring
  have e2 : Real.pi / (1 / 2 - -(1 / 2)) = Real.pi := by ring
  have hpos : √Real.pi ≠ 0 := by positivity
  simp only [e] at h
  rw [h, integral_gaussian, e2, Real.sqrt_mul zero_le_two, mul_inv, mul_assoc,
    inv_mul_cancel₀ hpos, mul_one, one_div]

end BHJK25.Spectral
