module

public import BDT24.Model
public import BDT24.Prob.Tail.Bounds

/-!
# Gaussian tail bounds

* Squared norms of Gaussian vectors concentrate (`BDT24.Prob.chi_upper`, `BDT24.Prob.chi_lower`):
  for `n` independent `N(0, σ²)`, the sum of squares exceeds `(51/50) σ² n`, or falls below
  `(49/50) σ² n`, with probability at most `exp(-n/10⁵)`.
* Tails (`BDT24.Prob.gauss_tail`): `P(|X| > T) ≤ 2 exp(-T²/4)` for `T ≥ 0` and variance at most
  `2`.
* Anti-concentration near a grid (`BDT24.Prob.nearInt_le`): for variance in `[1/2, 2]` and
  `a ≥ 1`, `a X` is within `η ≤ 1` of an integer with probability at most
  `2 exp(-T²/4) + (2 a T + 3)(2η/a)`: outside `|X| ≤ T` this is the tail, and inside it the
  `2aT + 3` intervals of length `2η/a` around the grid points have probability at most their
  length each, as the density is at most `1/√π < 1`.
-/

@[expose] public section

namespace BDT24.Prob

open MeasureTheory ProbabilityTheory

/-- `a` is within `η` of an integer. -/
def NearInt (a η : ℝ) : Prop := ∃ m : ℤ, |a - m| ≤ η

/-- **The upper tail of the squared norm.** -/
theorem chi_upper (n : ℕ) (σ2 : NNReal) (hσ : 0 < σ2) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2).real
        {x | (51 / 50 : ℝ) * σ2 * n < ∑ i, x i ^ 2} ≤ Real.exp (-(n : ℝ) / 100000) := by
  have hv0 : (0 : ℝ) < σ2 := hσ
  set t : ℝ := 1 / (200 * σ2) with ht
  have htv : t * σ2 = 1 / 200 := by rw [ht]; field_simp
  have hM : mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 σ2) t = (√(99 / 100))⁻¹ := by
    rw [T.mgf_sq_gaussianReal hσ.ne' (by rw [htv]; norm_num)]
    congr 2
    linear_combination -2 * htv
  have hpos : 0 < mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2) t := by
    rw [T.mgf_sum_sq_pi, hM]
    positivity
  calc _ ≤ (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2).real
          {x | (51 / 50 : ℝ) * σ2 * n ≤ ∑ i, x i ^ 2} :=
        measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hx ↦ hx.le)
    _ ≤ Real.exp (-t * ((51 / 50 : ℝ) * σ2 * n)) * mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)
          (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2) t :=
        measure_ge_le_exp_mul_mgf _ (by positivity) (mgf_pos_iff.1 hpos)
    _ = (Real.exp (-(51 / 10000)) * (√(99 / 100))⁻¹) ^ n := by
        rw [T.mgf_sum_sq_pi, hM, mul_pow, ← Real.exp_nat_mul]
        congr 2
        linear_combination (-(51 / 50) * (n : ℝ)) * htv
    _ ≤ Real.exp (-(1 / 100000)) ^ n := pow_le_pow_left₀ (by positivity) T.upper_factor n
    _ = Real.exp (-(n : ℝ) / 100000) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **The lower tail of the squared norm.** -/
theorem chi_lower (n : ℕ) (σ2 : NNReal) (hσ : 0 < σ2) :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2).real
        {x | ∑ i, x i ^ 2 < (49 / 50 : ℝ) * σ2 * n} ≤ Real.exp (-(n : ℝ) / 100000) := by
  have hv0 : (0 : ℝ) < σ2 := hσ
  set t : ℝ := -(1 / (200 * σ2)) with ht
  have htv : t * σ2 = -(1 / 200) := by rw [ht]; field_simp
  have hM : mgf (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 σ2) t = (√(101 / 100))⁻¹ := by
    rw [T.mgf_sq_gaussianReal hσ.ne' (by rw [htv]; norm_num)]
    congr 2
    linear_combination -2 * htv
  have hpos : 0 < mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)
      (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2) t := by
    rw [T.mgf_sum_sq_pi, hM]
    positivity
  have ht0 : t ≤ 0 := by rw [ht]; exact neg_nonpos.2 (by positivity)
  calc _ ≤ (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2).real
          {x | ∑ i, x i ^ 2 ≤ (49 / 50 : ℝ) * σ2 * n} :=
        measureReal_mono (Set.ofPred_subset_ofPred.2 fun _ hx ↦ hx.le)
    _ ≤ Real.exp (-t * ((49 / 50 : ℝ) * σ2 * n)) * mgf (fun x : Fin n → ℝ ↦ ∑ i, x i ^ 2)
          (Measure.pi fun _ : Fin n ↦ gaussianReal 0 σ2) t :=
        measure_le_le_exp_mul_mgf _ ht0 (mgf_pos_iff.1 hpos)
    _ = (Real.exp (49 / 10000) * (√(101 / 100))⁻¹) ^ n := by
        rw [T.mgf_sum_sq_pi, hM, mul_pow, ← Real.exp_nat_mul]
        congr 2
        linear_combination (-(49 / 50) * (n : ℝ)) * htv
    _ ≤ Real.exp (-(1 / 100000)) ^ n := pow_le_pow_left₀ (by positivity) T.lower_factor n
    _ = Real.exp (-(n : ℝ) / 100000) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **Gaussian tails**, for variance at most `2`. -/
theorem gauss_tail (σ2 : NNReal) (hσ : (σ2 : ℝ) ≤ 2) {T : ℝ} (hT : 0 ≤ T) :
    (gaussianReal 0 σ2).real {x | T < |x|} ≤ 2 * Real.exp (-T ^ 2 / 4) :=
  BDT24.Prob.T.gauss_tail_of_nonneg σ2 hσ hT

/-- **Anti-concentration near a grid.** -/
theorem nearInt_le (σ2 : NNReal) (h1 : (1 / 2 : ℝ) ≤ σ2) (h2 : (σ2 : ℝ) ≤ 2) {a η T : ℝ}
    (ha : 1 ≤ a) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hT : 0 ≤ T) :
    (gaussianReal 0 σ2).real {y | NearInt (a * y) η} ≤
      2 * Real.exp (-T ^ 2 / 4) + (2 * a * T + 3) * (2 * η / a) := by
  have hv : σ2 ≠ 0 := by
    rintro rfl
    norm_num at h1
  have ha0 : 0 < a := by linarith
  set N : ℤ := ⌊a * T + 1⌋ with hN
  have hN1 : (N : ℝ) ≤ a * T + 1 := Int.floor_le _
  have hN0 : 0 ≤ N := Int.floor_nonneg.2 (by positivity)
  have hsub : {y : ℝ | NearInt (a * y) η} ⊆
      {y | T < |y|} ∪ ⋃ m ∈ Finset.Icc (-N) N, {y : ℝ | |y - m / a| ≤ η / a} := by
    rintro y ⟨m, hm⟩
    by_cases hy : T < |y|
    · exact Or.inl hy
    right
    replace hy := not_lt.1 hy
    have hay : |a * y| ≤ a * T := by
      rw [abs_mul, abs_of_pos ha0]
      exact mul_le_mul_of_nonneg_left hy ha0.le
    have hmabs : |(m : ℝ)| ≤ a * T + 1 := by
      have : (m : ℝ) = a * y - (a * y - m) := by ring
      rw [this]
      exact (abs_sub _ _).trans (by linarith)
    simp only [Set.mem_iUnion, Finset.mem_Icc, Set.mem_ofPred_eq, exists_prop]
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have : ((-m : ℤ) : ℝ) ≤ a * T + 1 := by
        push_cast
        linarith [neg_abs_le (m : ℝ)]
      linarith [Int.le_floor.2 this]
    · exact Int.le_floor.2 (le_trans (le_abs_self _) hmabs)
    · have : y - m / a = (a * y - m) / a := by field_simp
      rw [this, abs_div, abs_of_pos ha0]
      exact div_le_div_of_nonneg_right hm ha0.le
  have hsq : (1 / 2 : ℝ) ≤ √(σ2 : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]
    linarith
  have hone : ∀ m : ℤ, (gaussianReal 0 σ2).real {y : ℝ | |y - m / a| ≤ η / a} ≤ 2 * η / a := by
    intro m
    refine (BDT24.Prob.T.gaussianReal_abs_sub_le_le 0 _ hv (by positivity)).trans ?_
    calc η / a / √(σ2 : ℝ) ≤ η / a / (1 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq
      _ = 2 * η / a := by ring
  have hcard : ((Finset.Icc (-N) N).card : ℝ) ≤ 2 * a * T + 3 := by
    have h := Int.card_Icc_of_le (a := -N) (b := N) (by linarith)
    have : ((Finset.Icc (-N) N).card : ℝ) = ((N + 1 - -N : ℤ) : ℝ) := by
      rw [← h]
      norm_cast
    rw [this]
    push_cast
    linarith
  have hgrid : (gaussianReal 0 σ2).real
      (⋃ m ∈ Finset.Icc (-N) N, {y : ℝ | |y - m / a| ≤ η / a}) ≤
        (2 * a * T + 3) * (2 * η / a) := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun m _ ↦ hone m).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)
  calc _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add (BDT24.Prob.T.gauss_tail_of_nonneg σ2 h2 hT) hgrid

end BDT24.Prob
