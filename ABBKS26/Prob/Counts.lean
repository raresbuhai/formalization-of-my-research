module

public import ABBKS26.Prob.Basic
public import TauCeti.Probability.Moments.Pi

/-!
# Cluster sizes and the number of corrupted points

Two good events about a sample of `n` points from an `ε`-corruption `P` of a valid mixture `M`,
with Chebyshev bounds on their failure probabilities.

* (G1) `ABBKS26.GoodCounts M.w η (labels ω)`: every cluster size is within `η n wⱼ` of `n wⱼ`.
  It is measurable (`ABBKS26.measurableSet_goodCounts`) and fails with probability at most
  `k / (n η² wmin)` (`ABBKS26.pi_not_goodCounts_le`).
* (G2) `(corrupted ω).card ≤ (ε + η) n`: few corrupted points. It is measurable
  (`ABBKS26.measurableSet_corrupted_card_le`) and fails with probability at most `ε / (n η²)`
  (`ABBKS26.pi_corrupted_card_gt_le`).

Both come from `ABBKS26.Counts.measureReal_pi_count_dev_le`: under a product of `n` copies of a
probability measure `ν`, the fraction of coordinates in a measurable set `s` deviates from `ν s` by
at least `t` with probability at most `ν s / (n t²)` (Chebyshev, via TauCeti's weak law).
-/

@[expose] public section

namespace ABBKS26

open MeasureTheory ProbabilityTheory

variable {k d : ℕ}

namespace Counts

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Chebyshev for counts.** Under the product of `n > 0` copies of a probability measure `ν`, the
fraction of coordinates in a measurable set `s` deviates from `ν s` by at least `t > 0` with
probability at most `ν s / (n t²)`. -/
theorem measureReal_pi_count_dev_le (ν : Measure Ω) [IsProbabilityMeasure ν] {s : Set Ω}
    (hs : MeasurableSet s) {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) :
    (Measure.pi fun _ : Fin n ↦ ν).real
        {x | t ≤ |(∑ j, s.indicator (1 : Ω → ℝ) (x j)) / n - ν.real s|} ≤
      ν.real s / (n * t ^ 2) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hmem : MemLp (s.indicator (1 : Ω → ℝ)) 2 ν :=
    (memLp_const (1 : ℝ)).indicator hs.nullMeasurableSet
  have hsq : s.indicator (1 : Ω → ℝ) ^ 2 = s.indicator 1 := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hvar : Var[s.indicator (1 : Ω → ℝ); ν] ≤ ν.real s := by
    refine (variance_le_expectation_sq (X := s.indicator (1 : Ω → ℝ))
      ((measurable_const.indicator hs).aestronglyMeasurable)).trans_eq ?_
    rw [hsq, integral_indicator_one hs]
  have h := TauCeti.meas_ge_le_variance_div_card_mul_sq_pi (ι := Fin n) hmem ht
  rw [integral_indicator_one hs, Fintype.card_fin] at h
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (ENNReal.ofReal_le_ofReal ?_))
  gcongr

omit [MeasurableSpace Ω] in
/-- The number of coordinates in `s`, as a sum of indicators. -/
theorem sum_indicator_eq_card {n : ℕ} (s : Set Ω) [DecidablePred (· ∈ s)] (x : Fin n → Ω) :
    ∑ j, s.indicator (1 : Ω → ℝ) (x j) = ((Finset.univ.filter fun j ↦ x j ∈ s).card : ℝ) := by
  simp only [Set.indicator_apply, Pi.one_apply, Finset.sum_boole]

theorem measurable_sum_indicator {n : ℕ} {s : Set Ω} (hs : MeasurableSet s) :
    Measurable fun x : Fin n → Ω ↦ ∑ j, s.indicator (1 : Ω → ℝ) (x j) :=
  Finset.measurable_sum _ fun j _ ↦ (measurable_const.indicator hs).comp (measurable_pi_apply j)

end Counts

open Counts

variable {M : Mixture k d} {ε : ℝ} {P : Measure (Triple k d)}

/-! ### (G1) Cluster sizes -/

/-- **(G1)** Every cluster size is within `η n wⱼ` of its expectation `n wⱼ`. -/
def GoodCounts {n : ℕ} (w : Fin k → ℝ) (η : ℝ) (ℓ : Fin n → Fin k) : Prop :=
  ∀ j, |((cluster ℓ j).card : ℝ) - n * w j| ≤ η * (n * w j)

theorem measurableSet_goodCounts {n : ℕ} (w : Fin k → ℝ) (η : ℝ) :
    MeasurableSet {ω : Fin n → Triple k d | GoodCounts w η (labels ω)} :=
  measurableSet_labels_preimage {ℓ | GoodCounts w η ℓ}

theorem sum_indicator_label {n : ℕ} (ω : Fin n → Triple k d) (j : Fin k) :
    ∑ l, {p : Triple k d | p.1 = j}.indicator (1 : Triple k d → ℝ) (ω l) =
      ((cluster (labels ω) j).card : ℝ) := by
  classical
  rw [sum_indicator_eq_card]
  rfl

/-- **(G1) fails rarely.** For an `ε`-corruption of a valid mixture with weights at least
`wmin > 0`, the cluster sizes of a sample of `n > 0` points fail `GoodCounts M.w η` with probability
at most `k / (n η² wmin)`. -/
theorem pi_not_goodCounts_le (hM : M.Valid) (hP : IsCorruption M ε P) {wmin η : ℝ}
    (hwmin : 0 < wmin) (hw : ∀ j, wmin ≤ M.w j) (hη : 0 < η) {n : ℕ} (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ P).real {ω | ¬ GoodCounts M.w η (labels ω)} ≤
      k / (n * η ^ 2 * wmin) := by
  have := hP.isProbabilityMeasure hM
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set μ := Measure.pi fun _ : Fin n ↦ P with hμ
  let A : Fin k → Set (Fin n → Triple k d) := fun j ↦
    {x | η * M.w j ≤ |(∑ l, {p : Triple k d | p.1 = j}.indicator (1 : Triple k d → ℝ) (x l)) / n -
      M.w j|}
  have hPj : ∀ j, P.real {p | p.1 = j} = M.w j := fun j ↦ by
    rw [measureReal_def, hP.measure_label j, ENNReal.toReal_ofReal (hM.nonneg_w j)]
  have hsub : {ω | ¬ GoodCounts M.w η (labels ω)} ⊆ ⋃ j, A j := by
    intro ω hω
    simp only [GoodCounts, not_forall, not_le, Set.mem_ofPred_eq] at hω
    obtain ⟨j, hj⟩ := hω
    refine Set.mem_iUnion.2 ⟨j, ?_⟩
    simp only [A, Set.mem_ofPred_eq, sum_indicator_label]
    rw [show ((cluster (labels ω) j).card : ℝ) / n - M.w j =
      (((cluster (labels ω) j).card : ℝ) - n * M.w j) / n by field_simp, abs_div,
      abs_of_pos hn', le_div_iff₀ hn']
    linarith
  have hA : ∀ j, μ.real (A j) ≤ 1 / (n * η ^ 2 * wmin) := fun j ↦ by
    have hwj : 0 < M.w j := hwmin.trans_le (hw j)
    have h := measureReal_pi_count_dev_le P (ProbBasic.measurableSet_fst_eq (α := _) j) hn
      (mul_pos hη hwj)
    rw [hPj] at h
    refine h.trans ?_
    calc M.w j / (n * (η * M.w j) ^ 2) = 1 / (n * η ^ 2 * M.w j) := by field_simp
      _ ≤ 1 / (n * η ^ 2 * wmin) := by
          gcongr
          exact hw j
  calc μ.real {ω | ¬ GoodCounts M.w η (labels ω)} ≤ μ.real (⋃ j, A j) := measureReal_mono hsub
    _ ≤ ∑ j, μ.real (A j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin k, 1 / (n * η ^ 2 * wmin) := Finset.sum_le_sum fun j _ ↦ hA j
    _ = k / (n * η ^ 2 * wmin) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-! ### (G2) Corrupted points -/

theorem sum_indicator_corrupted {n : ℕ} (ω : Fin n → Triple k d) :
    ∑ l, {p : Triple k d | p.2.1 ≠ p.2.2}.indicator (1 : Triple k d → ℝ) (ω l) =
      ((corrupted ω).card : ℝ) := by
  classical
  rw [sum_indicator_eq_card]
  unfold corrupted
  congr

/-- **(G2) is measurable.** -/
theorem measurableSet_corrupted_card_le {n : ℕ} (c : ℝ) :
    MeasurableSet {ω : Fin n → Triple k d | ((corrupted ω).card : ℝ) ≤ c} := by
  simp_rw [← sum_indicator_corrupted]
  exact measurableSet_le (measurable_sum_indicator measurableSet_corrupted_one) measurable_const

/-- **(G2) fails rarely.** For an `ε`-corruption of a valid mixture, a sample of `n > 0` points
has more than `(ε + η) n` corrupted points with probability at most `ε / (n η²)`. -/
theorem pi_corrupted_card_gt_le (hM : M.Valid) (hP : IsCorruption M ε P) (hε : 0 ≤ ε)
    {η : ℝ} (hη : 0 < η) {n : ℕ} (hn : 0 < n) :
    (Measure.pi fun _ : Fin n ↦ P).real {ω | (ε + η) * n < ((corrupted ω).card : ℝ)} ≤
      ε / (n * η ^ 2) := by
  have := hP.isProbabilityMeasure hM
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set s := {p : Triple k d | p.2.1 ≠ p.2.2} with hs
  have hq : P.real s ≤ ε := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hε hP.corrupted_le
  have h := measureReal_pi_count_dev_le P measurableSet_corrupted_one hn hη
  refine (measureReal_mono fun ω hω ↦ ?_).trans (h.trans ?_)
  · simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [sum_indicator_corrupted]
    have h1 : ε + η < ((corrupted ω).card : ℝ) / n := by rwa [lt_div_iff₀ hn']
    rw [abs_of_pos (by linarith)]
    linarith
  · gcongr

end ABBKS26
