module

public import ABBKS26.Model

/-!
# Samples: notation and basic facts

Notation for samples `ω : Fin n → Fin k × ℝ^d × ℝ^d` of triples (label, clean point, observed
point), and the facts about the law of a sample that the rest of the probability layer uses.

* `ABBKS26.labels ω`, `ABBKS26.clean ω`, `ABBKS26.obs ω`: the labels, clean points and observed
  points of a sample; `ABBKS26.corrupted ω`: the points whose observed point differs from the
  clean one.
* `ABBKS26.stdPt M i y`: the standardized point `Σᵢ^{-1/2} (y - μᵢ)`, with Mathlib's square root
  `CFC.sqrt` (the one `multivariateGaussian` is built with); `ABBKS26.stdClean M ω j` is the
  standardized clean point of the `j`-th sample point, standardized with its own label.
* `ABBKS26.sqNormIn_eq_norm_sq`: `vᵀ S⁻¹ v = ‖S^{-1/2} v‖²`; so a rounding within `δ` moves
  standardized points by at most `δ` (`ABBKS26.norm_stdPt_sub_le_of_isRounding`).
* `ABBKS26.Mixture.isProbabilityMeasure_law`, `ABBKS26.IsCorruption.isProbabilityMeasure`,
  `ABBKS26.IsCorruption.isProbabilityMeasure_pi`: the laws are probability measures.
* `ABBKS26.IsCorruption.measure_label`: a label `i` has probability `wᵢ`.
* `ABBKS26.map_stdPt_multivariateGaussian`: standardizing `N(μᵢ, Σᵢ)` gives `stdGaussian`.
* `ABBKS26.noiseLaw w d`: the label with law `w` and an independent standard Gaussian vector;
  `ABBKS26.noiseLaw_eq_prod`: it is the product `labelLaw w ⊗ stdGaussian`.
* `ABBKS26.IsCorruption.map_stdPair`, `ABBKS26.IsCorruption.pi_map_stdPairs`: the label and the
  standardized clean point of a sample point have law `noiseLaw M.w d`; for a sample, the pairs
  are independent with this law. `ABBKS26.IsCorruption.pi_preimage_stdPairs` and
  `ABBKS26.preimage_stdPairs_setOf` turn an event about labels and standardized clean points into
  one about `n` independent pairs from `noiseLaw M.w d`.
* Generic helpers (`ABBKS26.ProbBasic`): `isUnit_det_sqrt`, `transpose_sqrt`.
-/

@[expose] public section

namespace ABBKS26

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

variable {k d : ℕ}

/-! ### Generic helpers -/

namespace ProbBasic

theorem transpose_sqrt {S : Matrix (Fin d) (Fin d) ℝ} : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
  have h : (CFC.sqrt S).PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  have := h.isHermitian
  simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using this

/-- The square root of a positive definite matrix is invertible. -/
theorem isUnit_det_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsUnit (CFC.sqrt S).det := by
  have h : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hd : (CFC.sqrt S).det * (CFC.sqrt S).det = S.det := by rw [← det_mul, h]
  refine isUnit_iff_ne_zero.2 fun h0 ↦ ?_
  rw [h0, zero_mul] at hd
  exact hS.det_pos.ne' hd.symm

theorem measurableSet_fst_eq {α : Type*} [MeasurableSpace α] (i : Fin k) :
    MeasurableSet {p : Fin k × α | p.1 = i} :=
  measurable_fst (measurableSet_singleton i)

end ProbBasic

open ProbBasic

/-! ### Notation -/

/-- A sample point: a label, the clean point and the observed point. -/
abbrev Triple (k d : ℕ) := Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)

/-- The labels of a sample. -/
def labels {n : ℕ} (ω : Fin n → Triple k d) : Fin n → Fin k := fun j ↦ (ω j).1

/-- The clean points of a sample. -/
def clean {n : ℕ} (ω : Fin n → Triple k d) : Fin n → EuclideanSpace ℝ (Fin d) :=
  fun j ↦ (ω j).2.1

/-- The observed points of a sample. -/
def obs {n : ℕ} (ω : Fin n → Triple k d) : Fin n → EuclideanSpace ℝ (Fin d) :=
  fun j ↦ (ω j).2.2

open Classical in
/-- The corrupted sample points: those whose observed point differs from the clean one. -/
noncomputable def corrupted {n : ℕ} (ω : Fin n → Triple k d) : Finset (Fin n) :=
  Finset.univ.filter fun j ↦ (ω j).2.1 ≠ (ω j).2.2

theorem mem_corrupted {n : ℕ} {ω : Fin n → Triple k d} {j : Fin n} :
    j ∈ corrupted ω ↔ (ω j).2.1 ≠ (ω j).2.2 := by
  simp [corrupted]

/-- The **standardized point** `Σᵢ^{-1/2} (y - μᵢ)` of a point `y` of the `i`-th component, with
Mathlib's square root `CFC.sqrt` (the one `multivariateGaussian` uses). -/
noncomputable def stdPt (M : Mixture k d) (i : Fin k) (y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 ((CFC.sqrt (M.S i))⁻¹ *ᵥ fun a ↦ y a - M.μ i a)

/-- The standardized clean point `Σ_{ℓⱼ}^{-1/2} (yⱼ - μ_{ℓⱼ})` of the `j`-th sample point. -/
noncomputable def stdClean (M : Mixture k d) {n : ℕ} (ω : Fin n → Triple k d) (j : Fin n) :
    EuclideanSpace ℝ (Fin d) :=
  stdPt M (ω j).1 (ω j).2.1

theorem stdPt_apply (M : Mixture k d) (i : Fin k) (y : EuclideanSpace ℝ (Fin d)) (a : Fin d) :
    stdPt M i y a = ((CFC.sqrt (M.S i))⁻¹ *ᵥ fun b ↦ y b - M.μ i b) a := rfl

/-! ### Rounding in standardized coordinates -/

/-- `vᵀ S⁻¹ v = ‖S^{-1/2} v‖²` for positive definite `S`. -/
theorem sqNormIn_eq_norm_sq {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (v : Fin d → ℝ) :
    sqNormIn S v = ‖WithLp.toLp 2 ((CFC.sqrt S)⁻¹ *ᵥ v)‖ ^ 2 := by
  set A := CFC.sqrt S with hAdef
  have hA : A * A = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hinv : S⁻¹ = A⁻¹ * A⁻¹ := by rw [← hA, Matrix.mul_inv_rev]
  have hAt : A⁻¹ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hAdef, transpose_sqrt]
  rw [EuclideanSpace.real_norm_sq_eq, sqNormIn, hinv, ← mulVec_mulVec, dotProduct_mulVec,
    ← mulVec_transpose, hAt]
  simp [dotProduct, sq]

theorem stdPt_sub_stdPt (M : Mixture k d) (i : Fin k) (y z : EuclideanSpace ℝ (Fin d)) :
    stdPt M i y - stdPt M i z =
      WithLp.toLp 2 ((CFC.sqrt (M.S i))⁻¹ *ᵥ fun a ↦ y a - z a) := by
  unfold stdPt
  rw [← WithLp.toLp_sub, ← mulVec_sub]
  congr 2
  funext a
  simp

/-- **Rounding moves standardized points by at most `δ`.** If `r` rounds within `δ ≥ 0`, the
standardized rounded point of a point `z` with label `i` is within `δ` of the standardized `z`. -/
theorem norm_stdPt_sub_le_of_isRounding {M : Mixture k d} (hM : M.Valid) {δ : ℝ} (hδ : 0 ≤ δ)
    {r : Rounding k d} (hr : IsRounding M δ r) (i : Fin k) (z : EuclideanSpace ℝ (Fin d)) :
    ‖stdPt M i (WithLp.toLp 2 fun a ↦ (r (i, z) a : ℝ)) - stdPt M i z‖ ≤ δ := by
  rw [stdPt_sub_stdPt, ← pow_le_pow_iff_left₀ (norm_nonneg _) hδ two_ne_zero,
    ← sqNormIn_eq_norm_sq (hM.posDef i)]
  exact hr i z

/-! ### Measurability -/

theorem measurable_stdPt_right (M : Mixture k d) (i : Fin k) : Measurable (stdPt M i) := by
  unfold stdPt
  have hlin : Continuous fun v : Fin d → ℝ ↦ (CFC.sqrt (M.S i))⁻¹ *ᵥ v :=
    (Matrix.mulVecLin (CFC.sqrt (M.S i))⁻¹).continuous_of_finiteDimensional
  refine (PiLp.continuous_toLp 2 _).measurable.comp (hlin.measurable.comp ?_)
  exact (continuous_pi fun a ↦ ((PiLp.continuous_apply 2 _ a).sub continuous_const)).measurable

theorem measurable_stdPt (M : Mixture k d) :
    Measurable fun p : Fin k × EuclideanSpace ℝ (Fin d) ↦ stdPt M p.1 p.2 :=
  measurable_from_prod_countable_right fun i ↦ measurable_stdPt_right M i

theorem measurable_labels {n : ℕ} : Measurable (labels : (Fin n → Triple k d) → Fin n → Fin k) :=
  Measurable.of_eval fun j ↦ measurable_fst.comp (measurable_pi_apply j)

theorem measurable_label_clean :
    Measurable fun p : Triple k d ↦ (p.1, p.2.1) :=
  measurable_fst.prodMk (measurable_fst.comp measurable_snd)

theorem measurable_stdClean (M : Mixture k d) {n : ℕ} (j : Fin n) :
    Measurable fun ω : Fin n → Triple k d ↦ stdClean M ω j := by
  have h : Measurable fun ω : Fin n → Triple k d ↦ ((ω j).1, (ω j).2.1) :=
    measurable_label_clean.comp (measurable_pi_apply j)
  have h2 := (measurable_stdPt M).comp h
  unfold stdClean
  exact h2

/-- Every set of label vectors is measurable, so every event about the labels alone is. -/
theorem measurableSet_labels_preimage {n : ℕ} (A : Set (Fin n → Fin k)) :
    MeasurableSet {ω : Fin n → Triple k d | labels ω ∈ A} :=
  (Set.toFinite A).measurableSet.preimage measurable_labels

theorem measurableSet_corrupted_one :
    MeasurableSet {p : Triple k d | p.2.1 ≠ p.2.2} :=
  (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)).compl

/-! ### The laws are probability measures -/

/-- The law of a labelled point of a valid mixture is a probability measure. -/
theorem Mixture.isProbabilityMeasure_law {M : Mixture k d} (hM : M.Valid) :
    IsProbabilityMeasure M.law := by
  constructor
  simp only [Mixture.law, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  have h1 : ∀ i : Fin k, ((multivariateGaussian (WithLp.toLp 2 (M.μ i)) (M.S i)).map
      (fun y ↦ (i, y))) Set.univ = 1 := fun i ↦ by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp only [h1, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hM.nonneg_w i), hM.sum_w, ENNReal.ofReal_one]

variable {M : Mixture k d} {ε : ℝ} {P : Measure (Triple k d)}

/-- An `ε`-corruption of a valid mixture is a probability measure. -/
theorem IsCorruption.isProbabilityMeasure (hM : M.Valid) (hP : IsCorruption M ε P) :
    IsProbabilityMeasure P := by
  have := M.isProbabilityMeasure_law hM
  constructor
  have h := congrArg (fun m ↦ m Set.univ) hP.map_clean
  rw [Measure.map_apply measurable_label_clean MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  exact measure_univ

/-- The law of a sample from an `ε`-corruption of a valid mixture is a probability measure. -/
theorem IsCorruption.isProbabilityMeasure_pi (hM : M.Valid) (hP : IsCorruption M ε P) (n : ℕ) :
    IsProbabilityMeasure (Measure.pi fun _ : Fin n ↦ P) := by
  have := hP.isProbabilityMeasure hM
  infer_instance

/-- Under the mixture, the label `i` has probability `wᵢ`. -/
theorem Mixture.law_label (M : Mixture k d) (i : Fin k) :
    M.law {p | p.1 = i} = ENNReal.ofReal (M.w i) := by
  simp only [Mixture.law, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  have h1 : ∀ c : Fin k, ((multivariateGaussian (WithLp.toLp 2 (M.μ c)) (M.S c)).map
      (fun y ↦ (c, y))) {p | p.1 = i} = if c = i then 1 else 0 := fun c ↦ by
    rw [Measure.map_apply (by fun_prop) (measurableSet_fst_eq i)]
    by_cases hc : c = i
    · simp [hc]
    · simp [hc]
  simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Under an `ε`-corruption, the label `i` has probability `wᵢ`. -/
theorem IsCorruption.measure_label (hP : IsCorruption M ε P) (i : Fin k) :
    P {p | p.1 = i} = ENNReal.ofReal (M.w i) := by
  rw [← M.law_label i, ← hP.map_clean,
    Measure.map_apply measurable_label_clean (measurableSet_fst_eq i)]
  rfl

/-! ### Standardization -/

/-- Standardizing the `i`-th component gives the standard Gaussian. -/
theorem map_stdPt_multivariateGaussian {M : Mixture k d} (hM : M.Valid) (i : Fin k) :
    (multivariateGaussian (WithLp.toLp 2 (M.μ i)) (M.S i)).map (stdPt M i) =
      stdGaussian (EuclideanSpace ℝ (Fin d)) := by
  rw [multivariateGaussian, Measure.map_map (measurable_stdPt_right M i) (by fun_prop)]
  have hid : (stdPt M i ∘ fun x ↦ WithLp.toLp 2 (M.μ i) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (M.S i)) x) = id := by
    funext x
    simp only [Function.comp_apply, stdPt, id_eq]
    have : (fun a ↦ (WithLp.toLp 2 (M.μ i) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (M.S i)) x) a - M.μ i a) =
        CFC.sqrt (M.S i) *ᵥ WithLp.ofLp x := by
      funext a
      simp
    rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_sqrt (hM.posDef i)), one_mulVec]
  rw [hid, Measure.map_id]

/-- The law of a label: `i` with probability `w i`. -/
noncomputable def labelLaw (w : Fin k → ℝ) : Measure (Fin k) :=
  ∑ i, ENNReal.ofReal (w i) • Measure.dirac i

/-- The law of the label and the standardized point of a sample point: the label `i` with
probability `w i`, and an independent standard Gaussian vector. -/
noncomputable def noiseLaw (w : Fin k → ℝ) (d : ℕ) :
    Measure (Fin k × EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ENNReal.ofReal (w i) • (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x ↦ (i, x))

variable {w : Fin k → ℝ}

theorem isProbabilityMeasure_labelLaw (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) :
    IsProbabilityMeasure (labelLaw w) := by
  constructor
  simp only [labelLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw i), hw1, ENNReal.ofReal_one]

theorem isProbabilityMeasure_noiseLaw (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) :
    IsProbabilityMeasure (noiseLaw w d) := by
  constructor
  simp only [noiseLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ i : Fin k, ((stdGaussian (EuclideanSpace ℝ (Fin d))).map
      (fun x ↦ (i, x))) Set.univ = 1 := fun i ↦ by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp only [h1, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw i), hw1, ENNReal.ofReal_one]

/-- `noiseLaw w d` is the product of the label law and the standard Gaussian. -/
theorem noiseLaw_eq_prod (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) :
    noiseLaw w d = (labelLaw w).prod (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  have := isProbabilityMeasure_labelLaw hw1 hw
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  simp only [noiseLaw, labelLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Measure.map_apply (by fun_prop) (hs.prod ht), Measure.dirac_apply' _ hs, mul_assoc]
  congr 1
  by_cases hi : i ∈ s
  · rw [Set.mk_preimage_prod_right hi, Set.indicator_of_mem hi, Pi.one_apply, one_mul]
  · rw [Set.mk_preimage_prod_right_eq_empty hi, Set.indicator_of_notMem hi, measure_empty,
      zero_mul]

/-- The label and the standardized point `(i, Σᵢ^{-1/2} (y - μᵢ))` of a labelled point. -/
noncomputable def standardize (M : Mixture k d) (p : Fin k × EuclideanSpace ℝ (Fin d)) :
    Fin k × EuclideanSpace ℝ (Fin d) :=
  (p.1, stdPt M p.1 p.2)

theorem measurable_standardize (M : Mixture k d) : Measurable (standardize M) :=
  measurable_fst.prodMk (measurable_stdPt M)

/-- Under the law of a labelled point, the label and the standardized point have law
`noiseLaw M.w d`. -/
theorem law_map_standardize (hM : M.Valid) : M.law.map (standardize M) = noiseLaw M.w d := by
  rw [Mixture.law, ← Measure.mapₗ_apply_of_measurable (measurable_standardize M), map_sum,
    noiseLaw]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Measure.mapₗ_apply_of_measurable (measurable_standardize M),
    Measure.map_smul _ (measurable_standardize M).aemeasurable,
    Measure.map_map (measurable_standardize M) (by fun_prop),
    ← map_stdPt_multivariateGaussian hM i,
    Measure.map_map (by fun_prop) (measurable_stdPt_right M i)]
  rfl

/-- The label and the standardized clean point of a sample point. -/
noncomputable def stdPair (M : Mixture k d) (p : Triple k d) : Fin k × EuclideanSpace ℝ (Fin d) :=
  (p.1, stdPt M p.1 p.2.1)

theorem measurable_stdPair (M : Mixture k d) : Measurable (stdPair M) :=
  (measurable_standardize M).comp measurable_label_clean

/-- **The law of the label and the standardized clean point.** Under an `ε`-corruption of a valid
mixture it is `noiseLaw M.w d`: a label with law `w` and an independent standard Gaussian. -/
theorem IsCorruption.map_stdPair (hM : M.Valid) (hP : IsCorruption M ε P) :
    P.map (stdPair M) = noiseLaw M.w d := by
  rw [← law_map_standardize hM, ← hP.map_clean,
    Measure.map_map (measurable_standardize M) measurable_label_clean]
  rfl

/-- The labels and standardized clean points of a sample, as pairs. -/
noncomputable def stdPairs (M : Mixture k d) {n : ℕ} (ω : Fin n → Triple k d) :
    Fin n → Fin k × EuclideanSpace ℝ (Fin d) :=
  fun j ↦ stdPair M (ω j)

theorem measurable_stdPairs (M : Mixture k d) (n : ℕ) :
    Measurable (stdPairs M (n := n)) :=
  Measurable.of_eval fun j ↦ (measurable_stdPair M).comp (measurable_pi_apply j)

theorem stdPairs_fst (M : Mixture k d) {n : ℕ} (ω : Fin n → Triple k d) :
    (fun l ↦ (stdPairs M ω l).1) = labels ω := rfl

theorem stdPairs_snd (M : Mixture k d) {n : ℕ} (ω : Fin n → Triple k d) :
    (fun l ↦ (stdPairs M ω l).2) = stdClean M ω := by
  funext l
  rfl

/-- An event about the labels and the standardized clean points of a sample is the preimage under
`stdPairs M` of the same event for label and point pairs. -/
theorem preimage_stdPairs_setOf (M : Mixture k d) {n : ℕ}
    (Q : (Fin n → Fin k) → (Fin n → EuclideanSpace ℝ (Fin d)) → Prop) :
    stdPairs M ⁻¹' {z | Q (fun l ↦ (z l).1) (fun l ↦ (z l).2)} =
      {ω | Q (labels ω) (stdClean M ω)} := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, stdPairs_fst, stdPairs_snd]

/-- **The labels and standardized clean points of a sample** are `n` independent pairs with law
`noiseLaw M.w d`. -/
theorem IsCorruption.pi_map_stdPairs (hM : M.Valid) (hP : IsCorruption M ε P) (n : ℕ) :
    (Measure.pi fun _ : Fin n ↦ P).map (stdPairs M) =
      Measure.pi fun _ : Fin n ↦ noiseLaw M.w d := by
  have := hP.isProbabilityMeasure hM
  unfold stdPairs
  rw [Measure.pi_map_pi fun _ ↦ (measurable_stdPair M).aemeasurable]
  simp only [hP.map_stdPair hM]

/-- Probabilities of events about the labels and standardized clean points of a sample are those
of `n` independent pairs with law `noiseLaw M.w d`. -/
theorem IsCorruption.pi_preimage_stdPairs (hM : M.Valid) (hP : IsCorruption M ε P) {n : ℕ}
    {A : Set (Fin n → Fin k × EuclideanSpace ℝ (Fin d))} (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin n ↦ P) (stdPairs M ⁻¹' A) =
      (Measure.pi fun _ : Fin n ↦ noiseLaw M.w d) A := by
  rw [← hP.pi_map_stdPairs hM n, Measure.map_apply (measurable_stdPairs M n) hA]

end ABBKS26
