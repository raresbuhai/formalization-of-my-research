module

public import ABBKS26.Tree.Tree

/-! Singleton references and the observed-data filter used for per-block learning. -/

@[expose] public section

namespace ABBKS26.Select.LearnAux

noncomputable section

open Common Matrix MvPolynomial _root_.ABBKS26.Tree
open scoped BigOperators

variable {n k d : ℕ}

/-- The clean reference for one component, with the same rounding as the observed block. -/
def singletonReference (M : Mixture k d) (j : Fin k) (ω : Fin n → Triple k d)
    (r : Rounding k d) (N : Finset (Fin n)) : Robust.Reference n 1 d where
  model := ⟨fun _ ↦ 1, fun _ ↦ M.μ j, fun _ ↦ M.S j⟩
  label := fun _ ↦ 0
  reference := cluster (labels ω) j
  good := cluster (labels ω) j ∩ (Finset.univ \ corrupted ω) ∩ N
  block := N
  clean := fun l i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ)
  observed := fun l i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)

theorem singletonReference_contamination
    (M : Mixture k d) (j : Fin k) (ω : Fin n → Triple k d)
    (r : Rounding k d) (N : Finset (Fin n)) :
    (singletonReference M j ω r N).contamination = nodeContamination ω N {j} := by
  classical
  have hset : referenceSet ω {j} = cluster (labels ω) j := by
    ext l
    simp only [referenceSet, cluster, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rfl
  simp only [Robust.Reference.contamination, singletonReference, nodeContamination, hset]

theorem singletonReference_valid
    (M : Mixture k d) (j : Fin k) (ω : Fin n → Triple k d)
    (r : Rounding k d) (N : Finset (Fin n)) (hM : M.Valid)
    (hne : (cluster (labels ω) j).Nonempty)
    (hcov : (singletonReference M j ω r N).cov.PosDef) :
    (singletonReference M j ω r N).Valid (1 / 2) := by
  classical
  refine ⟨⟨by norm_num, fun _ ↦ by norm_num [singletonReference],
    by simp [singletonReference], fun _ ↦ hM.posDef j⟩,
    ?_, Finset.inter_subset_right, ?_, hne, hcov, ?_⟩
  · exact Finset.Subset.trans Finset.inter_subset_left Finset.inter_subset_left
  · intro l hl
    have hnot : l ∉ corrupted ω := (Finset.mem_sdiff.mp
      (Finset.mem_inter.mp (Finset.mem_inter.mp hl).1).2).2
    have he : (ω l).2.1 = (ω l).2.2 := not_not.mp (mem_corrupted.not.mp hnot)
    change (fun i ↦ (r ((ω l).1, (ω l).2.2) i : ℝ)) =
      (fun i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ))
    rw [he]
  · intro a
    have ha : a = 0 := Subsingleton.elim _ _
    subst a
    have hc : ((cluster (labels ω) j).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hne).ne'
    simpa only [singletonReference, Finset.filter_true] using (div_self hc).symm

/-- The learner contract uses the terminal leakage allowance, rather than the history sum. -/
theorem singleton_contamination
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params)
    (N : Finset (Fin n)) (j : Fin k)
    (hl : leakage ω N {j} ≤ (params (k - 1)).leakage)
    (hN : w * n / 4 ≤ N.card) :
    (singletonReference M j ω r N).contamination ≤ 2 / 10 ^ 10 := by
  have hk : 0 < k := j.pos
  obtain ⟨hM, _, _, hw, hwj, _, hη, hη100, _, hg, _, _, _, hlast, _, hparams⟩ := hp
  have hlast' : ((params (k - 1)).contamination : ℝ) ≤ 2 / 10 ^ 10 := by
    have hh : ((params (k - 1)).contamination : ℝ) ≤ ((2 / 10 ^ 10 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hlast
    norm_num at hh ⊢
    exact hh
  rw [singletonReference_contamination]
  exact (contamination_bound M ε w η _ D ω N {j} hg hM hw hwj
    ⟨hη.le, hη100⟩ (Finset.singleton_nonempty j) hl hN).trans
      ((hparams (k - 1) (by omega)).2.2.1.trans hlast')

private theorem singleton_between (R : Robust.Reference n 1 d)
    (hR : R.Valid (1 / 2)) (T : Mat d) (a : Vec d) (A : Mat d) :
    Robust.betweenVariance R T a A = 0 := by
  have hw : R.model.weight 0 = 1 := by simpa using hR.1.2.2.1
  simp [Robust.betweenVariance, hw]

/-- For a singleton, every failed filtering iteration is of type A. -/
theorem singleton_typeA (R : Robust.Reference n 1 d) (st : Robust.FilterState n d)
    (hi : Robust.IterationInvariant R st (1 / 2))
    (hf : Robust.FrameNormalized R st)
    (he : R.contamination ≤ 2 / 10 ^ 10)
    (hfail : ¬ Robust.Pass st (1 / 2) 0) : Robust.TypeA R st := by
  apply Robust.nonfar_typeA R st (1 / 2) 0 hi hf ?_ ?_ hfail
  · exact he.trans (by norm_num [Robust.maxContamination, Robust.sigmaSq])
  · intro A _ _
    rw [singleton_between R hi.1]
    norm_num


private theorem momentAccuracy_small (w η : ℝ) (d D : ℕ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hη : 0 < η) (hη100 : η ≤ 1 / 100)
    (hD : 8 ≤ D) :
    2 * momentAccuracy w η d D / w ≤ 1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8) := by
  let a := w / (64 * (d + 1 : ℝ) * D)
  let b := w / (64 * (d + 1 : ℝ))
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hab : a ≤ b := by
    dsimp only [a, b]
    apply div_le_div_of_nonneg_left hw.le (by positivity)
    nlinarith only [hD1, Nat.cast_nonneg (α := ℝ) d]
  have hb1 : b ≤ 1 := by
    dsimp only [b]
    rw [div_le_iff₀ (by positivity)]
    linarith only [hw1, Nat.cast_nonneg (α := ℝ) d]
  have hpow : a ^ (4 * D) ≤ b ^ 8 :=
    (pow_le_pow_of_le_one ha (hab.trans hb1) (by omega)).trans
      (pow_le_pow_left₀ ha hab 8)
  have hwpow : w ^ 8 ≤ w := pow_le_of_le_one hw.le hw1 (by omega)
  have he : 2 * momentAccuracy w η d D / w ≤
      (2 * η / 64 ^ 8) / (d + 1 : ℝ) ^ 8 := by
    have hbpow : b ^ 8 = w ^ 8 / (64 ^ 8 * (d + 1 : ℝ) ^ 8) := by
      simp only [b, div_pow, mul_pow]
    have hh : a ^ (4 * D) ≤ w / (64 ^ 8 * (d + 1 : ℝ) ^ 8) := by
      rw [hbpow] at hpow
      exact hpow.trans (div_le_div_of_nonneg_right hwpow (by positivity))
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * η)
    change 2 * (η * a ^ (4 * D)) / w ≤ _
    rw [div_le_iff₀ hw]
    simpa only [mul_assoc, div_div, mul_div_assoc, div_mul_eq_mul_div] using hh'
  apply he.trans
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [hη100, pow_pos (by positivity : (0 : ℝ) < d + 1) 8]

/-- The scheduled standardized moments are much sharper than the fixed learner tolerance. -/
theorem singleton_standardized_moments
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (j : Fin k)
    (α : Fin d → ℕ) (hα : (∑ i, α i) ≤ D) :
    |(∑ l ∈ cluster (labels ω) j, ∏ i, stdClean M ω l i ^ α i) /
      (cluster (labels ω) j).card - gaussMomMulti α| ≤
        1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8) := by
  have hD := hp.eight_le_degree mode M ε w η Δ D ω r params
  obtain ⟨hM, _, _, hw, hwj, _, hη, hη100, _, hg, hr, _⟩ := hp
  have hw1 : w ≤ 1 := by
    exact (hwj j).trans (hM.sum_w ▸ Finset.single_le_sum
      (fun i _ ↦ hM.nonneg_w i) (Finset.mem_univ j))
  exact (moment_resilience M ε w η D ω r hM hg hr hw hwj ⟨hη, hη100⟩
    (by omega) j D le_rfl α hα).trans (momentAccuracy_small w η d D hw hw1 hη hη100 hD)

/-- The Gaussian expectation determined by the monomial moments. -/
def gaussianValue (P : RPoly d) : ℝ :=
  ∑ α ∈ P.support, P.coeff α * (gaussMomMulti fun i ↦ α i : ℝ)

/-- Monomial accuracy controls every polynomial of the same degree. -/
theorem polynomial_moment_error (S : Finset (Fin n)) (g : Fin n → Vec d)
    (δ : ℝ) (D : ℕ)
    (hm : ∀ α : Fin d → ℕ, (∑ i, α i) ≤ D →
      |Robust.FilterAux.average S (fun l ↦ ∏ i, g l i ^ α i) - gaussMomMulti α| ≤ δ)
    (P : RPoly d) (hP : P.totalDegree ≤ D) :
    |Robust.FilterAux.average S (fun l ↦ eval (g l) P) - gaussianValue P| ≤
      δ * SoS.coeffNorm1 P := by
  classical
  have hexpand : (fun l ↦ eval (g l) P) =
      ∑ α ∈ P.support, P.coeff α • (fun l ↦ ∏ i, g l i ^ α i) := by
    funext l
    simp only [eval_eq', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hexpand]
  simp only [map_sum, map_smul, smul_eq_mul, gaussianValue,
    ← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ α ∈ P.support,
        |P.coeff α * (Robust.FilterAux.average S (fun l ↦ ∏ i, g l i ^ α i) -
          gaussMomMulti (fun i ↦ α i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * δ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left (hm (fun i ↦ α i) ?_) (abs_nonneg _)
      have hd := (le_totalDegree hα).trans hP
      change α.degree ≤ D at hd
      rwa [Finsupp.degree_eq_sum] at hd
    _ = δ * SoS.coeffNorm1 P := by
      rw [SoS.coeffNorm1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- Standardized clean samples satisfy the coefficient-norm polynomial error bound. -/
theorem singleton_polynomial_moments
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (j : Fin k)
    (P : RPoly d) (hP : P.totalDegree ≤ D) :
    |Robust.FilterAux.average (cluster (labels ω) j)
      (fun l ↦ eval (stdClean M ω l) P) - gaussianValue P| ≤
        SoS.coeffNorm1 P / (10 ^ 12 * (d + 1 : ℝ) ^ 8) := by
  have hm := polynomial_moment_error (cluster (labels ω) j)
    (fun l i ↦ stdClean M ω l i) (1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8)) D
    (fun α hα ↦ ?_) P hP
  · simpa only [one_div_mul_eq_div] using hm
  · change |((cluster (labels ω) j).card : ℝ)⁻¹ *
        (∑ l ∈ cluster (labels ω) j, ∏ i, stdClean M ω l i ^ α i) - gaussMomMulti α| ≤ _
    simpa only [div_eq_inv_mul] using
      singleton_standardized_moments mode M ε w η Δ D ω r params hp j α hα

end

end ABBKS26.Select.LearnAux
