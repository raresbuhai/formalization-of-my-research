module

public import ABBKS26.Tree.RefineAuxReference

/-! Clean-pass guarantees for common-covariance references. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix Robust
open scoped BigOperators

variable {n k d : ℕ}

/-- A common component covariance is bounded by the mixture's raw second moment. -/
theorem identical_covariance_le (F : FrameModel k d) (w γ : ℝ) (hF : F.Valid w)
    (hiso : F.Isotropic γ) (hid : ∀ i j, F.cov i = F.cov j)
    (j : Fin k) (u : Vec d) : qform (F.cov j) u ≤ (1 + γ) * sqnorm u := by
  have hw (i : Fin k) : 0 ≤ F.weight i := hF.1.le.trans (hF.2.1 i)
  have hsum : qform (F.cov j) u ≤ qform F.second u := by
    calc
      _ = ∑ i, F.weight i * qform (F.cov j) u := by
        rw [← Finset.sum_mul, hF.2.2.1, one_mul]
      _ ≤ ∑ i, F.weight i *
          (qform (F.cov i) u + (u ⬝ᵥ F.mean i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        rw [hid i j]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (hw i)
      _ = _ := by
        simp only [FrameModel.second, qform, sum_mulVec, dotProduct_sum, smul_mulVec,
          dotProduct_smul, smul_eq_mul, add_mulVec, dotProduct_add, vecMulVec_mulVec,
          op_smul_eq_smul]
        congr 1
        funext i
        rw [dotProduct_comm (F.mean i) u]
        ring
  apply hsum.trans
  simpa only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm]
    using hiso.2.2 u

private theorem weighted_pair_bound (w c : Fin k → ℝ) (π : ℝ)
    (hπ : 0 ≤ π) (hw : ∀ i, π ≤ w i) (i j : Fin k) :
    π * (c i - c j) ^ 2 ≤
      4 * ∑ l, w l * (c l - ∑ a, w a * c a) ^ 2 := by
  let μ := ∑ a, w a * c a
  let V := ∑ l, w l * (c l - μ) ^ 2
  have hsingle (a : Fin k) : π * (c a - μ) ^ 2 ≤ V := by
    apply (mul_le_mul_of_nonneg_right (hw a) (sq_nonneg _)).trans
    exact Finset.single_le_sum
      (fun l _ ↦ mul_nonneg (hπ.trans (hw l)) (sq_nonneg (c l - μ)))
      (Finset.mem_univ a)
  have hs : (c i - c j) ^ 2 ≤ 2 * (c i - μ) ^ 2 + 2 * (c j - μ) ^ 2 := by
    nlinarith only [sq_nonneg (c i + c j - 2 * μ)]
  have hh := mul_le_mul_of_nonneg_left hs hπ
  dsimp only [V, μ] at *
  nlinarith only [hh, hsingle i, hsingle j]

/-- A centered clean pass bounds pairwise population Frobenius distances. -/
theorem centered_pass_pairwise (D : Reference n k d) (st : FilterState n d) (π R : ℝ)
    (hi : IterationInvariant D st π) (hf : FrameNormalized D st)
    (he : D.contamination ≤ min (maxContamination π R) (π / 400))
    (hp : Pass st π R) (hcen : ∀ i, D.model.mean i = 0) (i j : Fin k) :
    π * frobSq (st.frame * D.model.cov i * st.frameᵀ -
      st.frame * D.model.cov j * st.frameᵀ) ≤ 320 * sigmaSq π R := by
  let F := st.frame * D.model.cov i * st.frameᵀ -
    st.frame * D.model.cov j * st.frameᵀ
  have hsym (a : Fin k) : (st.frame * D.model.cov a * st.frameᵀ)ᵀ =
      st.frame * D.model.cov a * st.frameᵀ := by
    have ha := (hi.1.1.2.2.2 a).isHermitian
    simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial] at ha
    rw [transpose_mul, transpose_mul, transpose_transpose, ha, mul_assoc]
  have hF : Fᵀ = F := by
    dsimp only [F]
    rw [transpose_sub, hsym, hsym]
  obtain ⟨A, hA, hn, hdual⟩ := FilterAux.frob_dual_witness F hF
  let c := fun a ↦ (A * (st.frame * D.model.cov a * st.frameᵀ)).trace +
    qform A (st.frame *ᵥ (D.model.mean a - D.mean))
  have hdiff : c i - c j = (A * F).trace := by
    simp only [c, hcen, zero_sub, F, mul_sub, trace_sub]
    ring
  have hpair := weighted_pair_bound D.model.weight c π hi.1.1.1.le hi.1.1.2.1 i j
  rw [hdiff, hdual] at hpair
  have hb := pass_spread D st π R hi hf he hp A hA hn
  change betweenVariance D st.frame D.mean A ≤ 80 * sigmaSq π R at hb
  change π * frobSq F ≤ _
  change π * frobSq F ≤ 4 * betweenVariance D st.frame D.mean A at hpair
  linarith only [hpair, hb]

/-- Common covariance removes its trace contribution from the between-component variance. -/
theorem identical_between_lt_sigma (D : Reference n k d) (π R : ℝ)
    (hD : D.Valid π) (hres : D.Resilient 4 (1 / 10000))
    (hid : ∀ i j, D.model.cov i = D.model.cov j)
    (T A : Mat d) (hn : frobSq A ≤ 1)
    (hM : LE (T * D.cov * Tᵀ) (6 • (1 : Mat d))) :
    betweenVariance D T D.mean A < sigmaSq π R := by
  classical
  let ν := fun j ↦ T *ᵥ (D.model.mean j - D.mean)
  have hw (j : Fin k) : 0 ≤ D.model.weight j := hD.1.1.le.trans (hD.1.2.1 j)
  have hν (j : Fin k) : π * sqnorm (ν j) ≤ 601 / 100 := by
    have h := RBAux.population_second_frame D π hD hres T hM j (ν j)
    have hweight := mul_le_mul_of_nonneg_right (hD.1.2.1 j)
      (sq_nonneg (sqnorm (ν j)))
    have hnonneg := Rounding.DetRoundAux.sqnorm_nonneg (ν j)
    change D.model.weight j * sqnorm (ν j) ^ 2 ≤ _ at h
    by_cases hz : sqnorm (ν j) = 0
    · rw [hz, mul_zero]
      norm_num
    · have hpos : 0 < sqnorm (ν j) := lt_of_le_of_ne hnonneg (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hpos).mp
      nlinarith only [h, hweight]
  have hq (j : Fin k) : π ^ 2 * qform A (ν j) ^ 2 ≤ (601 / 100 : ℝ) ^ 2 := by
    have habs := Rounding.DetRoundAux.abs_qform_le A 1 (by norm_num)
      (by simpa only [one_pow] using hn) (ν j)
    have hh := mul_le_mul_of_nonneg_left habs hD.1.1.le
    have hbound : π * |qform A (ν j)| ≤ 601 / 100 := by
      nlinarith only [hh, hν j]
    have hs := pow_le_pow_left₀ (mul_nonneg hD.1.1.le (abs_nonneg _)) hbound 2
    simpa only [mul_pow, sq_abs] using hs
  obtain ⟨l, _⟩ := hD.2.2.2.2.1
  let j₀ := D.label l
  let c := fun j ↦ (A * (T * D.model.cov j * Tᵀ)).trace + qform A (ν j)
  have hc (j : Fin k) :
      c j - (A * (T * D.model.cov j₀ * Tᵀ)).trace = qform A (ν j) := by
    dsimp only [c]
    rw [hid j j₀]
    ring
  have hvar : betweenVariance D T D.mean A ≤
      ∑ j, D.model.weight j * qform A (ν j) ^ 2 := by
    apply (FilterAux.weighted_variance_min D.model.weight c hD.1.2.2.1
      (A * (T * D.model.cov j₀ * Tᵀ)).trace).trans_eq
    simp only [hc]
  have hsum : π ^ 2 * (∑ j, D.model.weight j * qform A (ν j) ^ 2) ≤
      (601 / 100 : ℝ) ^ 2 := by
    calc
      _ = ∑ j, D.model.weight j * (π ^ 2 * qform A (ν j) ^ 2) := by
        rw [Finset.mul_sum]
        congr 1
        funext j
        ring
      _ ≤ ∑ j, D.model.weight j * (601 / 100 : ℝ) ^ 2 :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hq j) (hw j)
      _ = _ := by rw [← Finset.sum_mul, hD.1.2.2.1, one_mul]
  have hσ : sigmaSq π R * π ^ 2 = 600 + 2 * R ^ 2 * π ^ 2 := by
    unfold sigmaSq
    rw [add_mul, div_mul_cancel₀ _ (sq_pos_of_pos hD.1.1).ne']
  have hh := mul_le_mul_of_nonneg_left hvar (sq_nonneg π)
  have hstrict : betweenVariance D T D.mean A * π ^ 2 < sigmaSq π R * π ^ 2 := by
    nlinarith only [hh, hsum, hσ, mul_nonneg (sq_nonneg R) (sq_nonneg π)]
  exact (mul_lt_mul_iff_left₀ (sq_pos_of_pos hD.1.1)).mp hstrict


end

end ABBKS26.RefineAux
