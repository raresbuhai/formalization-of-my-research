module

public import ABBKS26.Prob.Basic
public import ABBKS26.Prob.Gaussian
public import TauCeti.Probability.Moments.Pi

/-!
# Empirical moments of the standardized clean points

(G4) For a sample of `n` points from an `ε`-corruption `P` of a valid mixture `M`, the empirical
moments of degree at most `D` of the standardized clean points `gₗ = Σ_{ℓₗ}^{-1/2} (yₗ - μ_{ℓₗ})`
of each cluster are close to the Gaussian ones (`ABBKS26.GoodMoments`): for every component `j`
and every multi-index `α` with `|α| ≤ D`,
`|(1/n) ∑_{ℓₗ = j} gₗ^α - (|Sⱼ|/n) · gaussMomMulti α| ≤ η`.

* `ABBKS26.measurableSet_goodMoments`: the event is measurable.
* `ABBKS26.pi_not_goodMoments_le`: it fails with probability at most
  `k (d + 1)^D (2D)^D / (n η²)`.

As in `BS23/Common/GoodProb.lean` (copied and adapted to one covariance per component): the
label and the standardized clean point of a sample point have law `ABBKS26.noiseLaw M.w d`
(`ABBKS26.IsCorruption.pi_map_stdPairs`), and each condition says that an average of `n` i.i.d.
copies of `1{ℓ = j} (g^α - E G^α)` (mean `0`, variance at most `E G^{2α} ≤ (2D)^D`) is small;
Chebyshev and a union bound over the `k` labels and the `(d + 1)^D` maps
`Fin D → Option (Fin d)` that represent the multi-indices (`ABBKS26.Moments.exists_countIdx`).
-/

@[expose] public section

namespace ABBKS26

open MeasureTheory ProbabilityTheory Matrix

variable {k d : ℕ}

/-- **(G4)** The empirical moments of degree at most `D` of the points `g` of each cluster are
within `η` of the Gaussian ones: `|(1/n) ∑_{l ∈ Sⱼ} gₗ^α - (|Sⱼ|/n) · E G^α| ≤ η`. -/
def GoodMoments {n : ℕ} (η : ℝ) (D : ℕ) (ℓ : Fin n → Fin k)
    (g : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ j, ∀ α : Fin d → ℕ, ∑ i, α i ≤ D →
    |(∑ l ∈ cluster ℓ j, ∏ i, g l i ^ α i) / n -
        ((cluster ℓ j).card : ℝ) / n * (gaussMomMulti α : ℝ)| ≤ η

namespace Moments

open Gauss

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

/-! ### The law of the label and the standardized point -/

local notation "E" d => EuclideanSpace ℝ (Fin d)

variable {w : Fin k → ℝ}

theorem integrable_noiseLaw {h : Fin k × (E d) → ℝ} (hm : Measurable h)
    (hi : ∀ i, Integrable (fun x ↦ h (i, x)) (stdGaussian (E d))) :
    Integrable h (noiseLaw w d) := by
  rw [noiseLaw, integrable_finsetSum_measure]
  intro i _
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  rw [integrable_map_measure hm.aestronglyMeasurable (by fun_prop)]
  exact hi i

theorem integral_noiseLaw (hw : ∀ i, 0 ≤ w i) {h : Fin k × (E d) → ℝ} (hm : Measurable h)
    (hi : ∀ i, Integrable (fun x ↦ h (i, x)) (stdGaussian (E d))) :
    ∫ z, h z ∂(noiseLaw w d) = ∑ i, w i * ∫ x, h (i, x) ∂(stdGaussian (E d)) := by
  rw [noiseLaw, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_smul_measure, integral_map (by fun_prop) hm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (hw i), smul_eq_mul]
  · intro i _
    refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
    rw [integrable_map_measure hm.aestronglyMeasurable (by fun_prop)]
    exact hi i

/-! ### The statistic -/

/-- The centered monomial `1{ℓ = j} (g^α - E G^α)` of the standardized point on label `j`. -/
noncomputable def noiseMom (j : Fin k) (α : Fin d → ℕ) (z : Fin k × (E d)) : ℝ :=
  if z.1 = j then ∏ i, z.2 i ^ α i - gaussMomMulti α else 0

theorem measurable_prod_pow (α : Fin d → ℕ) :
    Measurable fun x : E d ↦ ∏ i, x i ^ α i :=
  Finset.measurable_prod _ fun i _ ↦
    ((PiLp.continuous_apply 2 _ i).measurable).pow_const _

theorem measurable_noiseMom (j : Fin k) (α : Fin d → ℕ) : Measurable (noiseMom j α) :=
  Measurable.ite (ProbBasic.measurableSet_fst_eq j)
    (((measurable_prod_pow α).comp measurable_snd).sub_const _) measurable_const

theorem prod_pow_two_mul (x : E d) (α : Fin d → ℕ) :
    ∏ i, x i ^ (2 * α i) = (∏ i, x i ^ α i) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ ↦ by ring

theorem sub_sq_eq (α : Fin d → ℕ) :
    (fun x : E d ↦ (∏ i, x i ^ α i - gaussMomMulti α) ^ 2) =
      fun x ↦ (∏ i, x i ^ (2 * α i) - 2 * (gaussMomMulti α : ℝ) * ∏ i, x i ^ α i) +
        (gaussMomMulti α : ℝ) ^ 2 := by
  funext x
  rw [prod_pow_two_mul]
  ring

theorem integrable_sub_sq (α : Fin d → ℕ) :
    Integrable (fun x : E d ↦ (∏ i, x i ^ α i - gaussMomMulti α) ^ 2) (stdGaussian (E d)) := by
  rw [sub_sq_eq]
  exact ((integrable_prod_pow_stdGaussian _).sub
    ((integrable_prod_pow_stdGaussian α).const_mul _)).add (integrable_const _)

/-- `E (G^α - E G^α)² = E G^{2α} - (E G^α)²`. -/
theorem integral_sub_sq (α : Fin d → ℕ) :
    ∫ x, (∏ i, x i ^ α i - gaussMomMulti α) ^ 2 ∂(stdGaussian (E d)) =
      (gaussMomMulti (fun i ↦ 2 * α i) : ℝ) - (gaussMomMulti α : ℝ) ^ 2 := by
  have hX := integrable_prod_pow_stdGaussian (d := d) α
  have hX2 := integrable_prod_pow_stdGaussian (d := d) (fun i ↦ 2 * α i)
  have h1 : Integrable (fun x : E d ↦
      ∏ i, x i ^ (2 * α i) - 2 * (gaussMomMulti α : ℝ) * ∏ i, x i ^ α i)
      (stdGaussian (E d)) :=
    hX2.sub (hX.const_mul _)
  rw [sub_sq_eq, integral_add h1 (integrable_const _),
    integral_sub hX2 (hX.const_mul _), integral_const_mul, integral_prod_pow_stdGaussian,
    integral_prod_pow_stdGaussian, integral_const]
  simp only [probReal_univ, one_smul]
  ring

theorem noiseMom_self (j : Fin k) (α : Fin d → ℕ) (x : E d) :
    noiseMom j α (j, x) = ∏ i, x i ^ α i - gaussMomMulti α := ite_eq_left rfl

theorem noiseMom_of_ne {j i : Fin k} (h : i ≠ j) (α : Fin d → ℕ) (x : E d) :
    noiseMom j α (i, x) = 0 := ite_eq_right h

theorem integrable_noiseMom_section (j i : Fin k) (α : Fin d → ℕ) :
    Integrable (fun x ↦ noiseMom j α (i, x)) (stdGaussian (E d)) := by
  by_cases hi : i = j
  · subst hi
    simp_rw [noiseMom_self]
    exact (integrable_prod_pow_stdGaussian α).sub (integrable_const _)
  · simp_rw [noiseMom_of_ne hi]
    exact integrable_const _

theorem integrable_noiseMom_sq_section (j i : Fin k) (α : Fin d → ℕ) :
    Integrable (fun x ↦ noiseMom j α (i, x) ^ 2) (stdGaussian (E d)) := by
  by_cases hi : i = j
  · subst hi
    simp_rw [noiseMom_self]
    exact integrable_sub_sq α
  · simp_rw [noiseMom_of_ne hi]
    simp

theorem integral_noiseMom (hw : ∀ i, 0 ≤ w i) (j : Fin k) (α : Fin d → ℕ) :
    ∫ z, noiseMom j α z ∂(noiseLaw w d) = 0 := by
  rw [integral_noiseLaw hw (measurable_noiseMom j α) (integrable_noiseMom_section j · α),
    Finset.sum_eq_single j (fun i _ hi ↦ by simp_rw [noiseMom_of_ne hi]; simp) (by simp)]
  simp_rw [noiseMom_self]
  rw [integral_sub (integrable_prod_pow_stdGaussian α) (integrable_const _),
    integral_prod_pow_stdGaussian, integral_const]
  simp

theorem memLp_noiseMom (j : Fin k) (α : Fin d → ℕ) : MemLp (noiseMom j α) 2 (noiseLaw w d) :=
  (memLp_two_iff_integrable_sq (measurable_noiseMom j α).aestronglyMeasurable).2
    (integrable_noiseLaw ((measurable_noiseMom j α).pow_const 2)
      (integrable_noiseMom_sq_section j · α))

theorem variance_noiseMom_le (hw1 : ∑ i, w i = 1) (hw : ∀ i, 0 ≤ w i) (j : Fin k)
    (α : Fin d → ℕ) : Var[noiseMom j α; noiseLaw w d] ≤ gaussMomMulti (fun i ↦ 2 * α i) := by
  have := isProbabilityMeasure_noiseLaw (d := d) hw1 hw
  refine (variance_le_expectation_sq (measurable_noiseMom j α).aestronglyMeasurable).trans ?_
  simp only [Pi.pow_apply]
  rw [integral_noiseLaw hw ((measurable_noiseMom j α).pow_const 2)
      (integrable_noiseMom_sq_section j · α),
    Finset.sum_eq_single j (fun i _ hi ↦ by simp_rw [noiseMom_of_ne hi]; simp) (by simp)]
  simp_rw [noiseMom_self]
  rw [integral_sub_sq]
  have hV : 0 ≤ (gaussMomMulti (fun i ↦ 2 * α i) : ℝ) - (gaussMomMulti α : ℝ) ^ 2 := by
    rw [← integral_sub_sq]
    exact integral_nonneg fun x ↦ sq_nonneg _
  have hwj : w j ≤ 1 := hw1 ▸ Finset.single_le_sum (fun i _ ↦ hw i) (Finset.mem_univ j)
  nlinarith [sq_nonneg (gaussMomMulti α : ℝ), hw j]

/-! ### Sums of the statistic over a sample -/

variable {n : ℕ}

theorem sum_noiseMom_div (z : Fin n → Fin k × (E d)) (j : Fin k) (α : Fin d → ℕ) :
    (∑ l, noiseMom j α (z l)) / n =
      (∑ l ∈ cluster (fun l ↦ (z l).1) j, ∏ i, (z l).2 i ^ α i) / n -
        ((cluster (fun l ↦ (z l).1) j).card : ℝ) / n * (gaussMomMulti α : ℝ) := by
  have h : ∑ l, noiseMom j α (z l) =
      ∑ l ∈ cluster (fun l ↦ (z l).1) j, (∏ i, (z l).2 i ^ α i - (gaussMomMulti α : ℝ)) := by
    simp only [noiseMom, cluster]
    rw [Finset.sum_filter]
  rw [h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The good event in terms of the statistic `noiseMom`. -/
theorem goodMoments_iff (z : Fin n → Fin k × (E d)) (η : ℝ) (D : ℕ) :
    GoodMoments η D (fun l ↦ (z l).1) (fun l ↦ (z l).2) ↔
      ∀ j, ∀ α : Fin d → ℕ, ∑ i, α i ≤ D → |(∑ l, noiseMom j α (z l)) / n| ≤ η := by
  simp only [GoodMoments, sum_noiseMom_div]

/-- The good event for label and point pairs is measurable. -/
theorem measurableSet_goodMoments_pairs (η : ℝ) (D : ℕ) :
    MeasurableSet {z : Fin n → Fin k × (E d) |
      GoodMoments η D (fun l ↦ (z l).1) (fun l ↦ (z l).2)} := by
  simp_rw [goodMoments_iff]
  refine measurableSet_setOfPred.2
    (Measurable.forall fun j ↦ Measurable.forall fun α ↦ Measurable.imp measurable_const ?_)
  refine measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)
  exact continuous_abs.measurable.comp ((Finset.measurable_sum _ fun l _ ↦
    (measurable_noiseMom j α).comp (measurable_pi_apply l)).div_const _)

/-- **The good event for label and point pairs.** For `n` independent pairs from `noiseLaw w`,
the good event fails with probability at most `k (d + 1)^D (2D)^D / (n η²)`. -/
theorem pi_noiseLaw_not_goodMoments_le (hw1 : ∑ i, w i = 1) (hw0 : ∀ i, 0 ≤ w i) {η : ℝ}
    (hη : 0 < η) (hn : 0 < n) (D : ℕ) :
    (Measure.pi fun _ : Fin n ↦ noiseLaw w d).real
        {z | ¬ GoodMoments η D (fun l ↦ (z l).1) (fun l ↦ (z l).2)} ≤
      k * (d + 1) ^ D * (2 * D) ^ D / (n * η ^ 2) := by
  have := isProbabilityMeasure_noiseLaw (d := d) hw1 hw0
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set μ := Measure.pi fun _ : Fin n ↦ noiseLaw w d with hμ
  let B : Fin k → (Fin D → Option (Fin d)) → Set (Fin n → Fin k × (E d)) := fun j s ↦
    {z | η ≤ |(∑ l, noiseMom j (countIdx s) (z l)) / Fintype.card (Fin n) -
      ∫ a, noiseMom j (countIdx s) a ∂(noiseLaw w d)|}
  have hsub : {z | ¬ GoodMoments η D (fun l ↦ (z l).1) (fun l ↦ (z l).2)} ⊆
      ⋃ j, ⋃ s, B j s := by
    intro z hz
    simp only [Set.mem_ofPred_eq, goodMoments_iff, not_forall, not_le] at hz
    obtain ⟨j, α, hα, hj⟩ := hz
    obtain ⟨s, rfl⟩ := exists_countIdx hα
    refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨s, ?_⟩⟩
    simp only [B, Set.mem_ofPred_eq, integral_noiseMom hw0, Fintype.card_fin, sub_zero]
    exact hj.le
  have hB : ∀ j s, μ.real (B j s) ≤ (2 * D) ^ D / (n * η ^ 2) := fun j s ↦ by
    have h := TauCeti.meas_ge_le_variance_div_card_mul_sq_pi (ι := Fin n)
      (memLp_noiseMom (w := w) j (countIdx s)) hη
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    rw [Fintype.card_fin]
    gcongr
    exact (variance_noiseMom_le hw1 hw0 j _).trans
      (gaussMomMulti_two_mul_le_real (sum_countIdx_le s))
  calc μ.real {z | ¬ GoodMoments η D (fun l ↦ (z l).1) (fun l ↦ (z l).2)}
      ≤ μ.real (⋃ j, ⋃ s, B j s) := measureReal_mono hsub
    _ ≤ ∑ j, ∑ s, μ.real (B j s) := (measureReal_iUnion_fintype_le _).trans
          (Finset.sum_le_sum fun j _ ↦ measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _j : Fin k, ∑ _s : Fin D → Option (Fin d), (2 * D : ℝ) ^ D / (n * η ^ 2) :=
        Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun s _ ↦ hB j s
    _ = k * (d + 1) ^ D * (2 * D) ^ D / (n * η ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_option,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Moments

open Moments

variable {M : Mixture k d} {ε : ℝ} {P : Measure (Triple k d)} {n : ℕ}

/-- **(G4) is measurable.** -/
theorem measurableSet_goodMoments (M : Mixture k d) (n : ℕ) (η : ℝ) (D : ℕ) :
    MeasurableSet {ω : Fin n → Triple k d | GoodMoments η D (labels ω) (stdClean M ω)} := by
  rw [← preimage_stdPairs_setOf M (GoodMoments η D)]
  exact (measurableSet_goodMoments_pairs (n := n) (k := k) (d := d) η D).preimage
    (measurable_stdPairs M n)

/-- **(G4) fails rarely.** For an `ε`-corruption of a valid mixture, the empirical moments of
degree at most `D` of the standardized clean points of a sample of `n > 0` points fail
`GoodMoments η D` with probability at most `k (d + 1)^D (2D)^D / (n η²)`. -/
theorem pi_not_goodMoments_le (hM : M.Valid) (hP : IsCorruption M ε P) {η : ℝ} (hη : 0 < η)
    (hn : 0 < n) (D : ℕ) :
    (Measure.pi fun _ : Fin n ↦ P).real
        {ω | ¬ GoodMoments η D (labels ω) (stdClean M ω)} ≤
      k * (d + 1) ^ D * (2 * D) ^ D / (n * η ^ 2) := by
  have hmeas := (measurableSet_goodMoments_pairs (n := n) (k := k) (d := d) η D).compl
  have h := hP.pi_preimage_stdPairs hM hmeas
  rw [Set.compl_ofPred, preimage_stdPairs_setOf M (fun ℓ g ↦ ¬ GoodMoments η D ℓ g)] at h
  rw [measureReal_def, h]
  exact pi_noiseLaw_not_goodMoments_le hM.sum_w hM.nonneg_w hη hn D

end ABBKS26
