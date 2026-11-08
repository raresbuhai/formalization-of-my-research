module

public import BS23.Common.Gaussian
public import TauCeti.Probability.Moments.Pi

/-!
# The good event has high probability

For a valid mixture with weights at least `wmin > 0`, a sample of `n` points fails the good event
`BS23.GoodNoise M.w η D` with probability at most
`k / (n η²) · (1 / wmin + (d + 1)^D (2D)^D)` (`BS23.sampleLaw_not_goodNoise_le`). Along the way:
the law of a sample is a probability measure (`BS23.Mixture.isProbabilityMeasure_sampleLaw`) and
the good event is measurable (`BS23.measurableSet_goodNoise_sample`).

The proof: the map `(i, y) ↦ (i, Σ^{-1/2} (y - μᵢ))` (`BS23.standardize`) sends the law of a
labelled point to the law `BS23.noiseLaw` of a label `i` with probability `wᵢ` and an independent
standard Gaussian vector, since `y = μᵢ + Σ^{1/2} x` with `x` standard Gaussian and `Σ^{1/2}`
invertible (`BS23.law_map_standardize`). Each condition of the good event is that an average of `n`
i.i.d. statistics of these pairs is close to its mean: the indicator `1{ℓ = c}` (mean `w c`,
variance at most `w c`), and `1{ℓ = c} (g^α - E G^α)` (mean `0`, variance at most `E G^{2α}`).
Chebyshev's inequality for averages (TauCeti's weak law) and a union bound over the `k` labels and
the multi-indices of degree at most `D` give the bound. The multi-indices are counted as images of
the `(d + 1)^D` maps `Fin D → Option (Fin d)` (`BS23.exists_countIdx`).
-/

@[expose] public section

namespace BS23

open MeasureTheory ProbabilityTheory Matrix

variable {k d : ℕ}

/-! ### Counting multi-indices -/

/-- The multi-index that counts how often each coordinate occurs in `s`. -/
def countIdx {D : ℕ} (s : Fin D → Option (Fin d)) (i : Fin d) : ℕ :=
  ∑ t, if s t = some i then 1 else 0

theorem countIdx_cons {D : ℕ} (x : Option (Fin d)) (s : Fin D → Option (Fin d)) (i : Fin d) :
    countIdx (Fin.cons x s : Fin (D + 1) → Option (Fin d)) i =
      (if x = some i then 1 else 0) + countIdx s i := by
  simp only [countIdx, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

/-- The multi-index of `s : Fin D → Option (Fin d)` has degree at most `D`. -/
theorem sum_countIdx_le {D : ℕ} (s : Fin D → Option (Fin d)) : ∑ i, countIdx s i ≤ D := by
  unfold countIdx
  rw [Finset.sum_comm]
  calc ∑ t, ∑ i, (if s t = some i then 1 else 0) ≤ ∑ _t : Fin D, 1 := by
        refine Finset.sum_le_sum fun t _ ↦ ?_
        cases s t with
        | none => simp
        | some j => simp
    _ = D := by simp

/-- Every multi-index of degree at most `D` counts the coordinates of some
`s : Fin D → Option (Fin d)`. -/
theorem exists_countIdx : ∀ {D : ℕ} {α : Fin d → ℕ}, ∑ i, α i ≤ D →
    ∃ s : Fin D → Option (Fin d), countIdx s = α
  | 0, α, h => by
    refine ⟨Fin.elim0, funext fun i ↦ ?_⟩
    have : α i = 0 := Nat.le_zero.mp
      ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (α j)) (Finset.mem_univ i)).trans h)
    simp [countIdx, this]
  | D + 1, α, h => by
    classical
    by_cases hD : ∑ i, α i ≤ D
    · obtain ⟨s, hs⟩ := exists_countIdx hD
      refine ⟨Fin.cons none s, funext fun i ↦ ?_⟩
      simp [countIdx_cons, hs]
    · have hpos : ∃ i₀, α i₀ ≠ 0 := by
        by_contra hne
        simp only [not_exists, not_not] at hne
        simp [hne] at hD
      obtain ⟨i₀, hi₀⟩ := hpos
      set α' := Function.update α i₀ (α i₀ - 1) with hα'
      have hsum : ∑ i, α' i ≤ D := by
        have h1 := Finset.sum_update_of_mem (Finset.mem_univ i₀) α (α i₀ - 1)
        have h2 := Finset.add_sum_erase Finset.univ α (Finset.mem_univ i₀)
        rw [Finset.sdiff_singleton_eq_erase] at h1
        rw [← hα'] at h1
        omega
      obtain ⟨s, hs⟩ := exists_countIdx hsum
      refine ⟨Fin.cons (some i₀) s, funext fun i ↦ ?_⟩
      rw [countIdx_cons, hs]
      by_cases hi : i = i₀
      · subst hi
        rw [ite_eq_left rfl]
        simp only [hα', Function.update_self]
        omega
      · simp [hα', Function.update_of_ne hi, Ne.symm hi]

/-! ### The law of the label and the standardized noise -/

/-- The standard Gaussian on `Fin d → ℝ`, as a product. -/
noncomputable abbrev gaussPi (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ ↦ gaussianReal 0 1

/-- The law of the label and the standardized noise of one sample point: the label `i` with
probability `w i`, and an independent standard Gaussian vector. -/
noncomputable def noiseLaw (w : Fin k → ℝ) (d : ℕ) : Measure (Fin k × (Fin d → ℝ)) :=
  ∑ i, ENNReal.ofReal (w i) • (gaussPi d).map (fun x ↦ (i, x))

variable {w : Fin k → ℝ}

theorem isProbabilityMeasure_noiseLaw (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) :
    IsProbabilityMeasure (noiseLaw w d) := by
  constructor
  simp only [noiseLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have h1 : ∀ i : Fin k, ((gaussPi d).map (fun x ↦ (i, x))) Set.univ = 1 := fun i ↦ by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp only [h1, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw i), hw1, ENNReal.ofReal_one]

theorem integrable_noiseLaw {h : Fin k × (Fin d → ℝ) → ℝ} (hm : Measurable h)
    (hi : ∀ i, Integrable (fun x ↦ h (i, x)) (gaussPi d)) : Integrable h (noiseLaw w d) := by
  rw [noiseLaw, integrable_finsetSum_measure]
  intro i _
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  rw [integrable_map_measure hm.aestronglyMeasurable (by fun_prop)]
  exact hi i

theorem integral_noiseLaw (hw : ∀ i, 0 ≤ w i) {h : Fin k × (Fin d → ℝ) → ℝ} (hm : Measurable h)
    (hi : ∀ i, Integrable (fun x ↦ h (i, x)) (gaussPi d)) :
    ∫ z, h z ∂(noiseLaw w d) = ∑ i, w i * ∫ x, h (i, x) ∂(gaussPi d) := by
  rw [noiseLaw, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_smul_measure, integral_map (by fun_prop) hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (hw i), smul_eq_mul]
  · intro i _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [integrable_map_measure hm.aestronglyMeasurable (by fun_prop)]
    exact hi i

/-! ### The statistics -/

/-- The indicator `1{ℓ = c}` of label `c`. -/
noncomputable def labelInd (c : Fin k) (z : Fin k × (Fin d → ℝ)) : ℝ :=
  if z.1 = c then 1 else 0

/-- The centered monomial `1{ℓ = c} (g^α - E G^α)` of the noise on label `c`. -/
noncomputable def noiseMom (c : Fin k) (α : Fin d → ℕ) (z : Fin k × (Fin d → ℝ)) : ℝ :=
  if z.1 = c then ∏ i, z.2 i ^ α i - gaussMomMulti α else 0

theorem measurable_labelInd (c : Fin k) : Measurable (labelInd (d := d) c) :=
  Measurable.ite (measurable_fst (measurableSet_singleton c)) measurable_const measurable_const

theorem measurable_noiseMom (c : Fin k) (α : Fin d → ℕ) : Measurable (noiseMom c α) :=
  Measurable.ite (measurable_fst (measurableSet_singleton c)) (by fun_prop) measurable_const

theorem prod_pow_two_mul (x : Fin d → ℝ) (α : Fin d → ℕ) :
    ∏ i, x i ^ (2 * α i) = (∏ i, x i ^ α i) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ by ring

theorem sub_sq_eq (α : Fin d → ℕ) :
    (fun x : Fin d → ℝ ↦ (∏ i, x i ^ α i - gaussMomMulti α) ^ 2) =
      fun x ↦ (∏ i, x i ^ (2 * α i) - 2 * (gaussMomMulti α : ℝ) * ∏ i, x i ^ α i) +
        (gaussMomMulti α : ℝ) ^ 2 := by
  funext x
  rw [prod_pow_two_mul]
  ring

theorem integrable_sub_sq_pi (α : Fin d → ℕ) :
    Integrable (fun x : Fin d → ℝ ↦ (∏ i, x i ^ α i - gaussMomMulti α) ^ 2) (gaussPi d) := by
  rw [sub_sq_eq]
  exact ((integrable_prod_pow_pi _).sub ((integrable_prod_pow_pi α).const_mul _)).add
    (integrable_const _)

/-- `E (G^α - E G^α)² = E G^{2α} - (E G^α)²`. -/
theorem integral_sub_sq_pi (α : Fin d → ℕ) :
    ∫ x, (∏ i, x i ^ α i - gaussMomMulti α) ^ 2 ∂(gaussPi d) =
      (gaussMomMulti (fun i ↦ 2 * α i) : ℝ) - (gaussMomMulti α : ℝ) ^ 2 := by
  have hX := integrable_prod_pow_pi α
  have hX2 := integrable_prod_pow_pi (fun i ↦ 2 * α i)
  have h1 : Integrable (fun x : Fin d → ℝ ↦
      ∏ i, x i ^ (2 * α i) - 2 * (gaussMomMulti α : ℝ) * ∏ i, x i ^ α i) (gaussPi d) :=
    hX2.sub (hX.const_mul _)
  rw [sub_sq_eq, integral_add h1 (integrable_const _),
    integral_sub hX2 (hX.const_mul _), integral_const_mul, integral_prod_pow_pi,
    integral_prod_pow_pi, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-! ### Means and variances of the statistics -/

theorem labelInd_sq (c : Fin k) (z : Fin k × (Fin d → ℝ)) : labelInd c z ^ 2 = labelInd c z := by
  unfold labelInd
  split_ifs <;> norm_num

theorem labelInd_self (c : Fin k) (x : Fin d → ℝ) : labelInd c (c, x) = 1 := ite_eq_left rfl

theorem labelInd_of_ne {c i : Fin k} (h : i ≠ c) (x : Fin d → ℝ) : labelInd c (i, x) = 0 :=
  ite_eq_right h

theorem noiseMom_self (c : Fin k) (α : Fin d → ℕ) (x : Fin d → ℝ) :
    noiseMom c α (c, x) = ∏ j, x j ^ α j - gaussMomMulti α := ite_eq_left rfl

theorem noiseMom_of_ne {c i : Fin k} (h : i ≠ c) (α : Fin d → ℕ) (x : Fin d → ℝ) :
    noiseMom c α (i, x) = 0 := ite_eq_right h

theorem integrable_labelInd_section (c i : Fin k) :
    Integrable (fun x ↦ labelInd c (i, x)) (gaussPi d) := by
  by_cases hi : i = c
  · subst hi
    simp_rw [labelInd_self]
    exact integrable_const _
  · simp_rw [labelInd_of_ne hi]
    exact integrable_const _

theorem integral_labelInd (hw : ∀ i, 0 ≤ w i) (c : Fin k) :
    ∫ z, labelInd c z ∂(noiseLaw w d) = w c := by
  rw [integral_noiseLaw hw (measurable_labelInd c) (integrable_labelInd_section c),
    Finset.sum_eq_single c (fun i _ hi ↦ by simp_rw [labelInd_of_ne hi]; simp) (by simp)]
  simp_rw [labelInd_self]
  simp

theorem memLp_labelInd (c : Fin k) : MemLp (labelInd c) 2 (noiseLaw w d) := by
  refine (memLp_two_iff_integrable_sq (measurable_labelInd c).aestronglyMeasurable).2 ?_
  simp_rw [labelInd_sq]
  exact integrable_noiseLaw (measurable_labelInd c) (integrable_labelInd_section c)

theorem variance_labelInd_le (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) (c : Fin k) :
    Var[labelInd c; noiseLaw w d] ≤ w c := by
  have := isProbabilityMeasure_noiseLaw (d := d) hw1 hw
  refine (variance_le_expectation_sq (measurable_labelInd c).aestronglyMeasurable).trans_eq ?_
  simp only [Pi.pow_apply, labelInd_sq]
  exact integral_labelInd hw c

theorem integrable_noiseMom_section (c i : Fin k) (α : Fin d → ℕ) :
    Integrable (fun x ↦ noiseMom c α (i, x)) (gaussPi d) := by
  by_cases hi : i = c
  · subst hi
    simp_rw [noiseMom_self]
    exact (integrable_prod_pow_pi α).sub (integrable_const _)
  · simp_rw [noiseMom_of_ne hi]
    exact integrable_const _

theorem integrable_noiseMom_sq_section (c i : Fin k) (α : Fin d → ℕ) :
    Integrable (fun x ↦ noiseMom c α (i, x) ^ 2) (gaussPi d) := by
  by_cases hi : i = c
  · subst hi
    simp_rw [noiseMom_self]
    exact integrable_sub_sq_pi α
  · simp_rw [noiseMom_of_ne hi]
    simp

theorem integral_noiseMom (hw : ∀ i, 0 ≤ w i) (c : Fin k) (α : Fin d → ℕ) :
    ∫ z, noiseMom c α z ∂(noiseLaw w d) = 0 := by
  rw [integral_noiseLaw hw (measurable_noiseMom c α) (integrable_noiseMom_section c · α),
    Finset.sum_eq_single c (fun i _ hi ↦ by simp_rw [noiseMom_of_ne hi]; simp) (by simp)]
  simp_rw [noiseMom_self]
  rw [integral_sub (integrable_prod_pow_pi α) (integrable_const _), integral_prod_pow_pi,
    integral_const]
  simp

theorem memLp_noiseMom (c : Fin k) (α : Fin d → ℕ) : MemLp (noiseMom c α) 2 (noiseLaw w d) :=
  (memLp_two_iff_integrable_sq (measurable_noiseMom c α).aestronglyMeasurable).2
    (integrable_noiseLaw ((measurable_noiseMom c α).pow_const 2)
      (integrable_noiseMom_sq_section c · α))

theorem variance_noiseMom_le (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) (c : Fin k)
    (α : Fin d → ℕ) : Var[noiseMom c α; noiseLaw w d] ≤ gaussMomMulti (fun i ↦ 2 * α i) := by
  have := isProbabilityMeasure_noiseLaw (d := d) hw1 hw
  refine (variance_le_expectation_sq (measurable_noiseMom c α).aestronglyMeasurable).trans ?_
  simp only [Pi.pow_apply]
  rw [integral_noiseLaw hw ((measurable_noiseMom c α).pow_const 2)
      (integrable_noiseMom_sq_section c · α),
    Finset.sum_eq_single c (fun i _ hi ↦ by simp_rw [noiseMom_of_ne hi]; simp) (by simp)]
  simp_rw [noiseMom_self]
  rw [integral_sub_sq_pi]
  have hV : 0 ≤ (gaussMomMulti (fun i ↦ 2 * α i) : ℝ) - (gaussMomMulti α : ℝ) ^ 2 := by
    rw [← integral_sub_sq_pi]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hwc : w c ≤ 1 := hw1 ▸ Finset.single_le_sum (fun i _ ↦ hw i) (Finset.mem_univ c)
  nlinarith [sq_nonneg (gaussMomMulti α : ℝ), hw c]

/-! ### Sums of the statistics over a sample -/

variable {n : ℕ}

theorem sum_labelInd (z : Fin n → Fin k × (Fin d → ℝ)) (c : Fin k) :
    ∑ j, labelInd c (z j) = ((cluster (fun j ↦ (z j).1) c).card : ℝ) := by
  simp only [labelInd, Finset.sum_boole]
  rfl

theorem sum_noiseMom_div (z : Fin n → Fin k × (Fin d → ℝ)) (c : Fin k) (α : Fin d → ℕ) :
    (∑ j, noiseMom c α (z j)) / n =
      (∑ j ∈ cluster (fun j ↦ (z j).1) c, ∏ i, (z j).2 i ^ α i) / n -
        ((cluster (fun j ↦ (z j).1) c).card : ℝ) / n * (gaussMomMulti α : ℝ) := by
  have h : ∑ j, noiseMom c α (z j) =
      ∑ j ∈ cluster (fun j ↦ (z j).1) c, (∏ i, (z j).2 i ^ α i - (gaussMomMulti α : ℝ)) := by
    simp only [noiseMom, cluster]
    rw [Finset.sum_filter]
  rw [h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The good event in terms of the statistics `labelInd` and `noiseMom`. -/
theorem goodNoise_iff (z : Fin n → Fin k × (Fin d → ℝ)) (η : ℝ) (D : ℕ) :
    GoodNoise w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2) ↔
      (∀ c, |(∑ j, labelInd c (z j)) / n - w c| ≤ η * w c) ∧
        ∀ c, ∀ α : Fin d → ℕ, ∑ i, α i ≤ D → |(∑ j, noiseMom c α (z j)) / n| ≤ η := by
  simp only [GoodNoise, sum_labelInd, sum_noiseMom_div]

/-- The good event is measurable. -/
theorem measurableSet_goodNoise (η : ℝ) (D : ℕ) :
    MeasurableSet {z : Fin n → Fin k × (Fin d → ℝ) |
      GoodNoise w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2)} := by
  simp_rw [goodNoise_iff]
  refine measurableSet_setOfPred.2 (Measurable.and (Measurable.forall fun c ↦ ?_)
    (Measurable.forall fun c ↦ Measurable.forall fun α ↦ Measurable.imp measurable_const ?_))
  · refine measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)
    exact continuous_abs.measurable.comp (((Finset.measurable_sum _ fun j _ ↦
      (measurable_labelInd c).comp (measurable_pi_apply j)).div_const _).sub_const _)
  · refine measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)
    exact continuous_abs.measurable.comp ((Finset.measurable_sum _ fun j _ ↦
      (measurable_noiseMom c α).comp (measurable_pi_apply j)).div_const _)

/-- **The good event for the label and noise pairs.** For `n` independent pairs from `noiseLaw w`,
the good event fails with probability at most `k / (n η²) · (1 / wmin + (d + 1)^D (2D)^D)`. -/
theorem pi_noiseLaw_not_goodNoise_le (hw1 : ∑ i, w i = 1) {wmin η : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ w c) (hη : 0 < η) (hn : 0 < n) (D : ℕ) :
    (Measure.pi fun _ : Fin n ↦ noiseLaw w d).real
        {z | ¬ GoodNoise w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2)} ≤
      k / (n * η ^ 2) * (1 / wmin + (d + 1) ^ D * (2 * D) ^ D) := by
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ hwmin.le.trans (hw i)
  have := isProbabilityMeasure_noiseLaw (d := d) hw1 hw0
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set P := Measure.pi fun _ : Fin n ↦ noiseLaw w d with hP
  let A : Fin k → Set (Fin n → Fin k × (Fin d → ℝ)) := fun c ↦
    {z | η * w c ≤ |(∑ j, labelInd c (z j)) / Fintype.card (Fin n) -
      ∫ a, labelInd c a ∂(noiseLaw w d)|}
  let B : Fin k → (Fin D → Option (Fin d)) → Set (Fin n → Fin k × (Fin d → ℝ)) := fun c s ↦
    {z | η ≤ |(∑ j, noiseMom c (countIdx s) (z j)) / Fintype.card (Fin n) -
      ∫ a, noiseMom c (countIdx s) a ∂(noiseLaw w d)|}
  have hsub : {z | ¬ GoodNoise w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2)} ⊆
      (⋃ c, A c) ∪ ⋃ c, ⋃ s, B c s := by
    intro z hz
    simp only [Set.mem_ofPred_eq, goodNoise_iff, not_and_or, not_forall, not_le] at hz
    rcases hz with ⟨c, hc⟩ | ⟨c, α, hα, hc⟩
    · refine Or.inl (Set.mem_iUnion.2 ⟨c, ?_⟩)
      simp only [A, Set.mem_ofPred_eq, integral_labelInd hw0, Fintype.card_fin]
      exact hc.le
    · obtain ⟨s, rfl⟩ := exists_countIdx hα
      refine Or.inr (Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨s, ?_⟩⟩)
      simp only [B, Set.mem_ofPred_eq, integral_noiseMom hw0, Fintype.card_fin, sub_zero]
      exact hc.le
  have hA : ∀ c, P.real (A c) ≤ 1 / (n * η ^ 2 * wmin) := fun c ↦ by
    have hwc : 0 < w c := hwmin.trans_le (hw c)
    have h := TauCeti.meas_ge_le_variance_div_card_mul_sq_pi (ι := Fin n)
      (memLp_labelInd (w := w) (d := d) c)
      (mul_pos hη hwc)
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [Fintype.card_fin]
    calc Var[labelInd c; noiseLaw w d] / (n * (η * w c) ^ 2)
        ≤ w c / (n * (η * w c) ^ 2) := by
          gcongr
          exact variance_labelInd_le hw1 hw0 c
      _ = 1 / (n * η ^ 2 * w c) := by field_simp
      _ ≤ 1 / (n * η ^ 2 * wmin) := by
          gcongr
          exact hw c
  have hB : ∀ c s, P.real (B c s) ≤ (2 * D) ^ D / (n * η ^ 2) := fun c s ↦ by
    have h := TauCeti.meas_ge_le_variance_div_card_mul_sq_pi (ι := Fin n)
      (memLp_noiseMom (w := w) c (countIdx s)) hη
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [Fintype.card_fin]
    gcongr
    exact (variance_noiseMom_le hw1 hw0 c _).trans
      (gaussMomMulti_two_mul_le_real (sum_countIdx_le s))
  calc P.real {z | ¬ GoodNoise w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2)}
      ≤ P.real ((⋃ c, A c) ∪ ⋃ c, ⋃ s, B c s) := measureReal_mono hsub
    _ ≤ P.real (⋃ c, A c) + P.real (⋃ c, ⋃ s, B c s) := measureReal_union_le _ _
    _ ≤ ∑ c, P.real (A c) + ∑ c, ∑ s, P.real (B c s) :=
        add_le_add (measureReal_iUnion_fintype_le _) ((measureReal_iUnion_fintype_le _).trans
          (Finset.sum_le_sum fun c _ ↦ measureReal_iUnion_fintype_le _))
    _ ≤ ∑ _c : Fin k, 1 / (n * η ^ 2 * wmin) +
          ∑ _c : Fin k, ∑ _s : Fin D → Option (Fin d), (2 * D : ℝ) ^ D / (n * η ^ 2) :=
        add_le_add (Finset.sum_le_sum fun c _ ↦ hA c)
          (Finset.sum_le_sum fun c _ ↦ Finset.sum_le_sum fun s _ ↦ hB c s)
    _ = k / (n * η ^ 2) * (1 / wmin + (d + 1) ^ D * (2 * D) ^ D) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_option,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        field_simp

/-! ### From the sample to the label and noise pairs -/

section Sample

open scoped MatrixOrder

/-- The law of a labelled point is a probability measure. -/
theorem Mixture.isProbabilityMeasure_law {M : Mixture k d} (hM : M.Valid)
    (hw : ∀ i, 0 ≤ M.w i) : IsProbabilityMeasure M.law := by
  constructor
  simp only [Mixture.law, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  have h1 : ∀ i : Fin k, ((multivariateGaussian (WithLp.toLp 2 (M.μ i)) M.S).map
      (fun y ↦ (i, y))) Set.univ = 1 := fun i ↦ by
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  simp only [h1, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw i), hM.sum_w, ENNReal.ofReal_one]

/-- The law of a sample is a probability measure. -/
theorem Mixture.isProbabilityMeasure_sampleLaw {M : Mixture k d} (hM : M.Valid)
    (hw : ∀ i, 0 ≤ M.w i) (n : ℕ) : IsProbabilityMeasure (M.sampleLaw n) := by
  have := M.isProbabilityMeasure_law hM hw
  unfold Mixture.sampleLaw
  infer_instance

/-- The label and the standardized noise `(i, Σ^{-1/2} (y - μᵢ))` of a labelled point `(i, y)`. -/
noncomputable def standardize (M : Mixture k d) (p : Fin k × EuclideanSpace ℝ (Fin d)) :
    Fin k × (Fin d → ℝ) :=
  (p.1, (CFC.sqrt M.S)⁻¹ *ᵥ fun i ↦ p.2 i - M.μ p.1 i)

@[fun_prop]
theorem measurable_standardize (M : Mixture k d) : Measurable (standardize M) := by
  unfold standardize
  refine measurable_fst.prodMk ?_
  have hlin : Measurable fun v : Fin d → ℝ ↦ (CFC.sqrt M.S)⁻¹ *ᵥ v :=
    (Matrix.mulVecLin (CFC.sqrt M.S)⁻¹).continuous_of_finiteDimensional.measurable
  refine hlin.comp (Measurable.of_eval fun i ↦ ?_)
  have h1 : Measurable fun p : Fin k × EuclideanSpace ℝ (Fin d) ↦ p.2 i := by fun_prop
  have h2 : Measurable fun p : Fin k × EuclideanSpace ℝ (Fin d) ↦ M.μ p.1 i :=
    (Measurable.of_discrete (f := fun c ↦ M.μ c i)).comp measurable_fst
  exact h1.sub h2

/-- The square root of a positive definite matrix is invertible. -/
theorem isUnit_det_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsUnit (CFC.sqrt S).det := by
  have h : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg
  have hd : (CFC.sqrt S).det * (CFC.sqrt S).det = S.det := by rw [← det_mul, h]
  refine isUnit_iff_ne_zero.2 fun h0 ↦ ?_
  rw [h0, zero_mul] at hd
  exact hS.det_pos.ne' hd.symm

/-- Standardizing a point of the `i`-th component gives `i` and a standard Gaussian vector. -/
theorem map_standardize_component {M : Mixture k d} (hM : M.Valid) (i : Fin k) :
    ((multivariateGaussian (WithLp.toLp 2 (M.μ i)) M.S).map (fun y ↦ (i, y))).map
      (standardize M) = (gaussPi d).map (fun x ↦ (i, x)) := by
  rw [Measure.map_map (measurable_standardize M) (by fun_prop), multivariateGaussian,
    ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, standardize, Prod.mk.injEq, true_and]
  have : (fun j ↦ (WithLp.toLp 2 (M.μ i) +
      Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt M.S) (WithLp.toLp 2 x)) j - M.μ i j) =
      CFC.sqrt M.S *ᵥ x := by
    funext j
    simp
  rw [this, mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_sqrt hM.posDef), one_mulVec]

/-- **The law of the label and the standardized noise.** Under the law of a labelled point, the
label and the standardized noise `(i, Σ^{-1/2} (y - μᵢ))` have law `noiseLaw M.w d`. -/
theorem law_map_standardize {M : Mixture k d} (hM : M.Valid) :
    M.law.map (standardize M) = noiseLaw M.w d := by
  rw [Mixture.law, ← Measure.mapₗ_apply_of_measurable (measurable_standardize M), map_sum,
    noiseLaw]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Measure.mapₗ_apply_of_measurable (measurable_standardize M),
    Measure.map_smul _ (measurable_standardize M).aemeasurable, map_standardize_component hM]

/-- The labels and standardized noises of a sample are `n` independent pairs from `noiseLaw`. -/
theorem sampleLaw_map_standardize {M : Mixture k d} (hM : M.Valid) (hw : ∀ i, 0 ≤ M.w i)
    (n : ℕ) : (M.sampleLaw n).map (fun ω j ↦ standardize M (ω j)) =
      Measure.pi fun _ : Fin n ↦ noiseLaw M.w d := by
  have := M.isProbabilityMeasure_law hM hw
  rw [Mixture.sampleLaw, Measure.pi_map_pi fun _ ↦ (measurable_standardize M).aemeasurable]
  simp only [law_map_standardize hM]

theorem measurable_standardize_pi (M : Mixture k d) (n : ℕ) :
    Measurable fun (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) j ↦ standardize M (ω j) :=
  Measurable.of_eval fun j ↦ (measurable_standardize M).comp (measurable_pi_apply j)

/-- **The good event is measurable.** -/
theorem measurableSet_goodNoise_sample (M : Mixture k d) (n : ℕ) (η : ℝ) (D : ℕ) :
    MeasurableSet {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d) |
      GoodNoise M.w η D (labels ω) (stdNoise M ω)} := by
  have h := (measurableSet_goodNoise (w := M.w) (n := n) (d := d) η D).preimage
    (measurable_standardize_pi M n)
  rw [Set.preimage_ofPred_eq] at h
  have e1 : ∀ ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d),
      (fun j ↦ (standardize M (ω j)).1) = labels ω := fun ω ↦ rfl
  have e2 : ∀ ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d),
      (fun j ↦ (standardize M (ω j)).2) = stdNoise M ω := fun ω ↦ rfl
  simp only [e1, e2] at h
  exact h

/-- **The good event has high probability.** For a valid mixture with weights at least
`wmin > 0`, a sample of `n > 0` points fails the good event with probability at most
`k / (n η²) · (1 / wmin + (d + 1)^D (2D)^D)`. -/
theorem sampleLaw_not_goodNoise_le {M : Mixture k d} (hM : M.Valid) {wmin η : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) (hη : 0 < η) {n : ℕ} (hn : 0 < n) (D : ℕ) :
    (M.sampleLaw n {ω | ¬ GoodNoise M.w η D (labels ω) (stdNoise M ω)}).toReal ≤
      k / (n * η ^ 2) * (1 / wmin + (d + 1) ^ D * (2 * D) ^ D) := by
  have hmeas : MeasurableSet {z : Fin n → Fin k × (Fin d → ℝ) |
      ¬ GoodNoise M.w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2)} :=
    (measurableSet_goodNoise (w := M.w) (n := n) (d := d) η D).compl
  have h : M.sampleLaw n {ω | ¬ GoodNoise M.w η D (labels ω) (stdNoise M ω)} =
      (Measure.pi fun _ : Fin n ↦ noiseLaw M.w d)
        {z | ¬ GoodNoise M.w η D (fun j ↦ (z j).1) (fun j ↦ (z j).2)} := by
    rw [← sampleLaw_map_standardize hM (fun i ↦ hwmin.le.trans (hw i)) n,
      Measure.map_apply (measurable_standardize_pi M n) hmeas]
    rfl
  rw [h]
  exact pi_noiseLaw_not_goodNoise_le hM.sum_w hwmin hw hη hn D

end Sample

end BS23
