module

public import BHJK25.Spectral.Basic

/-!
# The noisy planted matrix as a function of independent components

The bookkeeping for the proof of [BHJK25, Lemma 3.7] (`BHJK25.Spectral.noisy_spike`), for
`n = k + 1`. A spectral component is a pair `(λⱼ, uⱼ)` of an eigenvalue and a column of the
Gaussian matrix; the matrix `U diag(λ) Uᵀ` is `∑ⱼ λⱼ uⱼ uⱼᵀ`. The noisy matrix
`(1 - ε) M₁ + ε M₀` is a function (`BHJK25.Spectral.TailAux.noisyMat`) of independent pieces
(`BHJK25.Spectral.TailAux.sampleLaw`):

* the spike column `u` of `M₁`, a standard Gaussian vector (its eigenvalue is `λ*`);
* the other `k` components of `M₁`, independent with law `μ_γ ⊗ N(0, I)`
  (`BHJK25.Spectral.TailAux.compLaw`);
* the `k + 1` components of `M₀`, independent with the same law.

`BHJK25.Spectral.TailAux.noisyLaw_eq` identifies the law of the noisy matrix with the image of
this product measure.
-/

@[expose] public section

namespace BHJK25.Spectral.TailAux

open MeasureTheory ProbabilityTheory Matrix

/-- The eigenvalues and the Gaussian matrix (row by row) with the given components: the `j`-th
eigenvalue and the `j`-th column. -/
def toSpec {n m : ℕ} (q : Fin m → ℝ × (Fin n → ℝ)) : (Fin m → ℝ) × (Fin n → Fin m → ℝ) :=
  (fun j ↦ (q j).1, fun i j ↦ (q j).2 i)

theorem measurable_toSpec {n m : ℕ} : Measurable (toSpec (n := n) (m := m)) := by
  unfold toSpec
  fun_prop

/-- The law `μ_γ ⊗ N(0, I_n)` of a spectral component. -/
noncomputable def compLaw (γ : ℝ) (n : ℕ) : Measure (ℝ × (Fin n → ℝ)) :=
  (eigLaw γ).prod (gaussVec n)

/-- The components of the planted matrix: the others, then the spike column `u` with the spike
eigenvalue last. -/
def plantCols {k : ℕ} (spike : ℝ) (x : (Fin (k + 1) → ℝ) × (Fin k → ℝ × (Fin (k + 1) → ℝ))) :
    Fin (k + 1) → ℝ × (Fin (k + 1) → ℝ) :=
  Fin.snoc (α := fun _ ↦ ℝ × (Fin (k + 1) → ℝ)) x.2 (spike, x.1)

/-- The sample space: the spike column and the other components of the planted matrix, and the
components of the null matrix. -/
abbrev Sample (k : ℕ) : Type :=
  ((Fin (k + 1) → ℝ) × (Fin k → ℝ × (Fin (k + 1) → ℝ))) × (Fin (k + 1) → ℝ × (Fin (k + 1) → ℝ))

/-- The law of the sample: everything independent, the spike column standard Gaussian and the
components with law `μ_γ ⊗ N(0, I)`. -/
noncomputable def sampleLaw (γ : ℝ) (k : ℕ) : Measure (Sample k) :=
  ((gaussVec (k + 1)).prod (Measure.pi fun _ : Fin k ↦ compLaw γ (k + 1))).prod
    (Measure.pi fun _ : Fin (k + 1) ↦ compLaw γ (k + 1))

/-- The noisy matrix `(1 - ε) M₁ + ε M₀` as a function of the sample. -/
def noisyMat {k : ℕ} (ε spike : ℝ) (ω : Sample k) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  (1 - ε) • specMap _ _ (toSpec (plantCols spike ω.1)) + ε • specMap _ _ (toSpec ω.2)

theorem plantCols_eq {k : ℕ} (spike : ℝ) :
    plantCols (k := k) spike =
      (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ × (Fin (k + 1) → ℝ)) (Fin.last k)).symm ∘
        Prod.map (Prod.mk spike) id := by
  funext x
  simp [plantCols, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last']

theorem measurable_plantCols {k : ℕ} (spike : ℝ) : Measurable (plantCols (k := k) spike) := by
  rw [plantCols_eq]
  exact (MeasurableEquiv.measurable _).comp (measurable_prodMk_left.prodMap measurable_id)

theorem measurable_noisyMat {k : ℕ} (ε spike : ℝ) : Measurable (noisyMat (k := k) ε spike) :=
  (measurable_noisy ε).comp ((measurable_specMap.comp ((measurable_toSpec.comp
    (measurable_plantCols spike)).comp measurable_fst)).prodMk
    (measurable_specMap.comp (measurable_toSpec.comp measurable_snd)))

instance isProbabilityMeasure_compLaw (γ : ℝ) [IsProbabilityMeasure (eigLaw γ)] (n : ℕ) :
    IsProbabilityMeasure (compLaw γ n) := by
  unfold compLaw; infer_instance

instance isProbabilityMeasure_sampleLaw (γ : ℝ) [IsProbabilityMeasure (eigLaw γ)] (k : ℕ) :
    IsProbabilityMeasure (sampleLaw γ k) := by
  unfold sampleLaw; infer_instance

/-- Eigenvalues and an independent Gaussian matrix, as independent components: the columns of
the Gaussian matrix are independent standard Gaussian vectors. -/
theorem pi_prod_gaussMat {n m : ℕ} (ν : Fin m → Measure ℝ) [∀ j, SigmaFinite (ν j)] :
    (Measure.pi ν).prod (gaussMat n m) =
      (Measure.pi fun j ↦ (ν j).prod (gaussVec n)).map toSpec := by
  have hT : Measurable fun (V : Fin m → Fin n → ℝ) (i : Fin n) (j : Fin m) ↦ V j i := by
    fun_prop
  calc (Measure.pi ν).prod (gaussMat n m)
      = ((Measure.pi ν).map id).prod
          ((Measure.pi fun _ : Fin m ↦ gaussVec n).map fun V i j ↦ V j i) := by
        rw [Measure.map_id, gaussMat_eq_map_cols]
    _ = ((Measure.pi ν).prod (Measure.pi fun _ : Fin m ↦ gaussVec n)).map
          (Prod.map id fun V i j ↦ V j i) := Measure.map_prod_map _ _ measurable_id hT
    _ = ((Measure.pi fun j ↦ (ν j).prod (gaussVec n)).map
          (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin n → ℝ) (Fin m))).map
          (Prod.map id fun V i j ↦ V j i) := by
        rw [(measurePreserving_arrowProdEquivProdArrow ℝ (Fin n → ℝ) (Fin m) ν
          fun _ ↦ gaussVec n).map_eq]
    _ = _ := by
        rw [Measure.map_map (measurable_id.prodMap hT) (MeasurableEquiv.measurable _)]
        rfl

/-- The components of the planted matrix: the spike component `(λ*, u)` split off from the
others. -/
theorem pi_planted {k : ℕ} (γ spike : ℝ) [IsProbabilityMeasure (eigLaw γ)] :
    (Measure.pi fun j : Fin (k + 1) ↦
      (if (j : ℕ) + 1 = k + 1 then Measure.dirac spike else eigLaw γ).prod (gaussVec (k + 1))) =
    ((gaussVec (k + 1)).prod (Measure.pi fun _ : Fin k ↦ compLaw γ (k + 1))).map
      (plantCols spike) := by
  set ρ : Fin (k + 1) → Measure (ℝ × (Fin (k + 1) → ℝ)) := fun j ↦
    (if (j : ℕ) + 1 = k + 1 then Measure.dirac spike else eigLaw γ).prod (gaussVec (k + 1))
  have : ∀ j, IsProbabilityMeasure (ρ j) := fun j ↦ by
    simp only [ρ]
    split_ifs <;> infer_instance
  have h := (measurePreserving_piFinSuccAbove ρ (Fin.last k)).symm
  rw [← h.map_eq]
  have hlast : ρ (Fin.last k) = (gaussVec (k + 1)).map (Prod.mk spike) := by
    simp [ρ, Measure.dirac_prod]
  have hrest : (fun j : Fin k ↦ ρ ((Fin.last k).succAbove j)) = fun _ ↦ compLaw γ (k + 1) := by
    funext j
    have : (j : ℕ) ≠ k := j.isLt.ne
    simp [ρ, compLaw, this]
  rw [hlast, hrest]
  calc _ = (((gaussVec (k + 1)).prod (Measure.pi fun _ : Fin k ↦ compLaw γ (k + 1))).map
        (Prod.map (Prod.mk spike) id)).map
          (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ × (Fin (k + 1) → ℝ)) (Fin.last k)).symm := by
        rw [← Measure.map_prod_map _ _ measurable_prodMk_left measurable_id, Measure.map_id]
    _ = _ := by
        rw [Measure.map_map (MeasurableEquiv.measurable _)
          (measurable_prodMk_left.prodMap measurable_id), plantCols_eq]

/-- The law of the noisy matrix `(1 - ε) M₁ + ε M₀` is the image of the law of the sample. -/
theorem noisyLaw_eq {k : ℕ} (γ spike ε : ℝ) [IsProbabilityMeasure (eigLaw γ)] :
    noisyLaw ε (plantedLaw γ (k + 1) spike (k + 1)) (nullLaw γ (k + 1) (k + 1)) =
      (sampleLaw γ k).map (noisyMat ε spike) := by
  have : ∀ j : Fin (k + 1),
      SigmaFinite (if (j : ℕ) + 1 = k + 1 then Measure.dirac spike else eigLaw γ) := fun j ↦ by
    split_ifs <;> infer_instance
  rw [plantedLaw_eq, nullLaw_eq, plantedEig, nullEig, pi_prod_gaussMat, pi_prod_gaussMat,
    pi_planted, Measure.map_map measurable_toSpec (measurable_plantCols spike),
    Measure.map_map measurable_specMap (measurable_toSpec.comp (measurable_plantCols spike)),
    Measure.map_map measurable_specMap measurable_toSpec, noisyLaw,
    Measure.map_prod_map _ _ (measurable_specMap.comp (measurable_toSpec.comp
      (measurable_plantCols spike))) (measurable_specMap.comp measurable_toSpec),
    Measure.map_map (measurable_noisy ε) ((measurable_specMap.comp (measurable_toSpec.comp
      (measurable_plantCols spike))).prodMap (measurable_specMap.comp measurable_toSpec))]
  rfl

end BHJK25.Spectral.TailAux
