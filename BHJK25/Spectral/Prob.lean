module

public import BHJK25.Spectral.Basic

/-!
# The spectral distributions are rotation-invariant probability distributions

Both distributions of Theorem 3.1 are probability measures for every `n`, and rotation invariant:
`O U` has the law of `U` for an orthogonal `O`, and `O (U diag(λ) Uᵀ) Oᵀ = (O U) diag(λ) (O U)ᵀ`.
Null matrices are symmetric and negative semidefinite, since `μ_γ` lives on `[-1, 0]`.
-/

@[expose] public section

namespace BHJK25.Spectral

open MeasureTheory ProbabilityTheory Matrix

namespace ProbAux

/-- `μ_γ` is a finite measure for every `γ`. -/
theorem isFiniteMeasure_eigLaw (γ : ℝ) : IsFiniteMeasure (eigLaw γ) := by
  constructor
  rw [eigLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top⟩

/-- The eigenvalue law of the planted distribution has finite marginals. -/
theorem isFiniteMeasure_plantedEig_marginal (γ : ℝ) (m : ℕ) (spike : ℝ) (i : Fin m) :
    IsFiniteMeasure (if (i : ℕ) + 1 = m then Measure.dirac spike else eigLaw γ) := by
  split_ifs
  · infer_instance
  · exact isFiniteMeasure_eigLaw γ

/-- For `0 ≤ γ ≤ 1`, the eigenvalue law of the planted distribution has probability marginals. -/
theorem isProbabilityMeasure_plantedEig_marginal {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (m : ℕ)
    (spike : ℝ) (i : Fin m) :
    IsProbabilityMeasure (if (i : ℕ) + 1 = m then Measure.dirac spike else eigLaw γ) := by
  split_ifs
  · infer_instance
  · exact isProbabilityMeasure_eigLaw h0 h1

/-- `U diag(λ) Uᵀ` is symmetric. -/
theorem specMap_transpose {n m : ℕ} (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) :
    (specMap n m p)ᵀ = specMap n m p := by
  simp [specMap, Matrix.transpose_mul, Matrix.mul_assoc]

/-- `U diag(λ) Uᵀ` is negative semidefinite when every `λ_j` is at most `0`. -/
theorem specMap_nsd {n m : ℕ} (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) (hp : ∀ j, p.1 j ≤ 0)
    (v : Fin n → ℝ) : v ⬝ᵥ (specMap n m p *ᵥ v) ≤ 0 := by
  set U := Matrix.of p.2
  have h : v ⬝ᵥ (specMap n m p *ᵥ v) = (Uᵀ *ᵥ v) ⬝ᵥ (diagonal p.1 *ᵥ (Uᵀ *ᵥ v)) := by
    rw [specMap, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, mulVec_transpose]
  rw [h]
  refine Finset.sum_nonpos fun j _ ↦ ?_
  rw [mulVec_diagonal]
  nlinarith [hp j, mul_self_nonneg ((Uᵀ *ᵥ v) j)]

end ProbAux

theorem isProbabilityMeasure_nullAt {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    IsProbabilityMeasure (nullAt C n) := by
  have := isProbabilityMeasure_eigLaw (sparsity_nonneg hC n) (sparsity_le_one C n)
  rw [nullAt, nullLaw_eq, nullEig]
  infer_instance

theorem isProbabilityMeasure_plantedAt {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    IsProbabilityMeasure (plantedAt C n) := by
  have := ProbAux.isProbabilityMeasure_plantedEig_marginal (sparsity_nonneg hC n)
    (sparsity_le_one C n) n (sparsity C n * Real.log n)
  rw [plantedAt, plantedLaw_eq, plantedEig]
  infer_instance

theorem rotationInvariant_spectralLaw {m : ℕ} (ν : Measure (Fin m → ℝ)) [SFinite ν] (n : ℕ) :
    RotationInvariant (spectralLaw ν n) := by
  intro O hO
  have hG : MeasurePreserving (fun (U : Fin n → Fin m → ℝ) i j ↦ ∑ k, O i k * U k j)
      (gaussMat n m) (gaussMat n m) := ⟨by fun_prop, gaussMat_map_orth hO⟩
  have hp := (MeasurePreserving.id ν).prod hG
  have hc : (fun M ↦ O * M * Oᵀ) ∘ specMap n m =
      specMap n m ∘ Prod.map id fun (U : Fin n → Fin m → ℝ) i j ↦ ∑ k, O i k * U k j := by
    ext p : 1
    have hU : Matrix.of (fun i j ↦ ∑ k, O i k * p.2 k j) = O * Matrix.of p.2 := by
      ext i j
      simp [Matrix.mul_apply]
    simp only [Function.comp_apply, specMap, Prod.map_fst, Prod.map_snd, id_eq, hU,
      Matrix.transpose_mul, Matrix.mul_assoc]
  rw [spectralLaw_eq, Measure.map_map (measurable_conj O) measurable_specMap, hc,
    ← Measure.map_map measurable_specMap hp.measurable, hp.map_eq]

theorem rotationInvariant_nullAt (C : ℝ) (n : ℕ) : RotationInvariant (nullAt C n) := by
  have := ProbAux.isFiniteMeasure_eigLaw (sparsity C n)
  exact rotationInvariant_spectralLaw _ n

theorem rotationInvariant_plantedAt (C : ℝ) (n : ℕ) : RotationInvariant (plantedAt C n) := by
  have := ProbAux.isFiniteMeasure_plantedEig_marginal (sparsity C n) n (sparsity C n * Real.log n)
  exact rotationInvariant_spectralLaw _ n

/-- Null matrices are symmetric and negative semidefinite, with probability `1`. -/
theorem null_nsd {C : ℝ} (hC : 0 ≤ C) (n : ℕ) :
    ProbAtLeast (nullAt C n) 1 fun M ↦ Mᵀ = M ∧ ∀ v, v ⬝ᵥ (M *ᵥ v) ≤ 0 := by
  have := isProbabilityMeasure_eigLaw (sparsity_nonneg hC n) (sparsity_le_one C n)
  set E : Set (Matrix (Fin n) (Fin n) ℝ) := {M | Mᵀ = M ∧ ∀ v, v ⬝ᵥ (M *ᵥ v) ≤ 0} with hE_def
  have hE : MeasurableSet E := by
    rw [hE_def, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.measurableSet (IsClosed.inter
      (isClosed_eq continuous_id.matrix_transpose continuous_id) ?_)
    exact isClosed_iInter fun v ↦ isClosed_le (by fun_prop) continuous_const
  refine ⟨E, hE, ?_, fun M hM ↦ hM⟩
  have hneg : ∀ᵐ p ∂(nullEig (sparsity C n) n).prod (gaussMat n n), ∀ j, p.1 j ≤ 0 := by
    have h1 : ∀ᵐ x ∂(nullEig (sparsity C n) n), ∀ j, x j ≤ 0 := by
      refine ae_all_iff.2 fun j ↦ ?_
      have h := (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin n ↦ eigLaw (sparsity C n))
        (i := j)).eventually (ae_eigLaw_mem _)
      exact h.mono fun x hx ↦ hx.2
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hae : ∀ᵐ M ∂(nullAt C n), M ∈ E := by
    rw [nullAt, nullLaw_eq]
    refine (ae_map_iff measurable_specMap.aemeasurable (p := fun M ↦ M ∈ E) hE).2 ?_
    exact hneg.mono fun p hp ↦ ⟨ProbAux.specMap_transpose p, ProbAux.specMap_nsd p hp⟩
  have := isProbabilityMeasure_nullAt hC n
  rw [(prob_compl_eq_zero_iff hE).1 (ae_iff.1 hae), ENNReal.toReal_one]

end BHJK25.Spectral
