module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdAffine

/-! Population mean gaps with room for the final affine coefficient rounding. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdMean

open Common Matrix Rounding _root_.ABBKS26.RefineAux
open scoped BigOperators

noncomputable section

variable {d : ℕ}

theorem spread {n k : ℕ} (R : Robust.Reference n k d) (w θ : ℝ)
    (hR : R.Valid w) (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : R.Resilient 4 θ)
    (u : Vec d) (hnorm : (99 / 100 : ℝ) ^ 2 ≤ sqnorm u)
    (hC : (99 / 100 : ℝ) * sqnorm u ≤ qform R.cov u)
    (hvar : ∀ j, qform (R.model.cov j) u ≤ 1 / 1000) :
    ∃ a b, 19 / 20 ≤ |u ⬝ᵥ R.model.mean a - u ⬝ᵥ R.model.mean b| := by
  classical
  by_contra h
  have hpair (a b : Fin k) :
      |u ⬝ᵥ R.model.mean a - u ⬝ᵥ R.model.mean b| < 19 / 20 :=
    lt_of_not_ge (fun hab ↦ h ⟨a, b, hab⟩)
  obtain ⟨l, _⟩ := hR.2.2.2.2.1
  let a := R.label l
  let A := affineReference R 1 (R.model.mean a)
  have hAv : A.Valid w := affineReference_valid R 1 _ w hR (by simp)
  have hAr : A.Resilient 4 θ := affineReference_resilient R 1 _ 4 θ (by simp) hres
  have hAc : A.cov = R.cov := by
    simpa only [one_mul, mul_one, transpose_one] using
      affineReference_cov R 1 (R.model.mean a) hR.2.2.2.2.1
  have hcomponent (j : Fin k) :
      qform (A.model.cov j) u + (u ⬝ᵥ A.model.mean j) ^ 2 ≤
        1 / 1000 + (19 / 20 : ℝ) ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hpair j a).le 2
    rw [sq_abs] at hh
    change qform (1 * R.model.cov j * (1 : Mat d)ᵀ) u +
      (u ⬝ᵥ ((1 : Mat d) *ᵥ (R.model.mean j - R.model.mean a))) ^ 2 ≤ _
    simp only [transpose_one, one_mul, mul_one, one_mulVec, dotProduct_sub]
    linarith only [hh, hvar j]
  have hsecond : qform A.model.second u ≤ 1 / 1000 + (19 / 20 : ℝ) ^ 2 := by
    rw [frame_second_qform]
    calc
      _ ≤ ∑ j, A.model.weight j * (1 / 1000 + (19 / 20 : ℝ) ^ 2) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcomponent j)
          (hAv.1.1.le.trans (hAv.1.2.1 j))
      _ = _ := by rw [← Finset.sum_mul, hAv.1.2.2.1, one_mul]
  have hsecond0 : 0 ≤ qform A.model.second u := by
    rw [frame_second_qform]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (hAv.1.1.le.trans (hAv.1.2.1 j))
    exact add_nonneg ((hAv.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u)
      (sq_nonneg _)
  have he := (abs_le.mp (second_moment_comparison A w θ hAv hθ.1 hAr u)).2
  rw [hAc] at he
  have hprod := mul_le_mul hθ.2 hsecond hsecond0 (by norm_num : (0 : ℝ) ≤ 1 / 10000)
  nlinarith only [he, hprod, hsecond, hC, hnorm, sq_nonneg (u ⬝ᵥ A.mean)]

/-- Stronger mean and variance margins for a covered thin direction. -/
theorem direction {n k : ℕ} (R : Robust.Reference n k d)
    (S : IdCov.Data k d) (w β : ℚ) (γ Δ θ : ℝ) (Y : List (Fin d → ℚ))
    (hR : R.Valid ((w / 2 : ℚ) : ℝ)) (hframe : S.frame = R.model)
    (hS : S.Valid ((w / 2 : ℚ) : ℝ) γ) (hγ : γ ≤ IdCov.gammaStar β)
    (hβ : 0 < β ∧ β ≤ 1 / 100) (hw : 0 < w)
    (hbudget : 16 ≤ Δ ^ 2 * (w : ℝ) * (IdCov.tauStar β : ℝ))
    (hsep : ∃ a b, MeanSeparated Δ (S.mean a) (S.mean b) S.cov)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000) (hres : R.Resilient 4 θ)
    (hC : frobSq (R.cov - 1) ≤ (1 / 100 : ℝ) ^ 2)
    (hnorm : ∀ u ∈ Y, (1 - (β : ℝ)) ^ 2 ≤ sqnorm (fun i ↦ (u i : ℝ)) ∧
      sqnorm (fun i ↦ (u i : ℝ)) ≤ (1 + (β : ℝ)) ^ 2)
    (hcover : ∀ v, sqnorm v = 1 → qform S.cov v ≤ IdCov.tauStar β →
      ∃ u ∈ Y, sqnorm ((fun i ↦ (u i : ℝ)) - v) ≤ (2 * (β : ℝ)) ^ 2) :
    ∃ u ∈ Y, qform S.cov (fun i ↦ (u i : ℝ)) ≤ 61 / 10 * (β : ℝ) ^ 2 ∧
      (∀ j, |(fun i ↦ (u i : ℝ)) ⬝ᵥ S.mean j| ≤ 3 * (sqrtUp (1 / w) : ℝ)) ∧
      ∃ a b, 19 / 20 ≤ |(fun i ↦ (u i : ℝ)) ⬝ᵥ S.mean a -
        (fun i ↦ (u i : ℝ)) ⬝ᵥ S.mean b| := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hβ0 : (0 : ℝ) ≤ β := by exact_mod_cast hβ.1.le
  have hβ100 : (β : ℝ) ≤ 1 / 100 := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr hβ.2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hγ1 : γ ≤ 1 := (hγ.trans (identical_tolerances β hβ).1).trans (by norm_num)
  have hSv : S.frame.Valid ((w : ℝ) / 2) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hS.1
  obtain ⟨a, b, hab⟩ := hsep
  obtain ⟨v, hv, hthin⟩ := mean_thin_direction S.frame S.cov w γ Δ _ hSv hS.2.1
    hγ1 hbudget a b hab
  obtain ⟨u, hu, hnear⟩ := hcover v hv hthin
  let z : Vec d := fun i ↦ (u i : ℝ)
  have hvar := IdGeometry.net_variance S ((w / 2 : ℚ) : ℝ) γ β
    hS hγ hβ a z v hthin hnear
  have hzlo : (99 / 100 : ℝ) ^ 2 ≤ sqnorm z := by
    apply le_trans _ (hnorm u hu).1
    apply pow_le_pow_left₀ (by norm_num)
    linarith only [hβ100]
  have hzhi : sqnorm z ≤ (101 / 100 : ℝ) ^ 2 := by
    apply (hnorm u hu).2.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hβ100]
  have hvarsmall : 61 / 10 * (β : ℝ) ^ 2 ≤ 1 / 1000 := by
    nlinarith only [hβ0, hβ100, sq_nonneg ((β : ℝ) - 1 / 100)]
  have hspread : ∃ a b, 19 / 20 ≤ |z ⬝ᵥ S.mean a - z ⬝ᵥ S.mean b| := by
    suffices ∃ a b, 19 / 20 ≤ |z ⬝ᵥ R.model.mean a - z ⬝ᵥ R.model.mean b| by
      simpa only [← hframe, IdCov.Data.frame] using this
    apply spread R _ θ hR hθ hres z hzlo
    · have hh := (abs_le.mp (Rounding.DetRoundAux.abs_qform_le (R.cov - 1)
        (1 / 100) (by norm_num) hC z)).1
      have he : qform (R.cov - 1) z = qform R.cov z - sqnorm z := by
        simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub, sqnorm]
      rw [he] at hh
      linarith only [hh]
    · intro j
      have he : R.model.cov j = S.cov := by rw [← hframe]; rfl
      rw [he]
      exact hvar.trans hvarsmall
  refine ⟨u, hu, hvar, ?_, hspread⟩
  intro j
  have hm := projected_mean_bound S.frame ((w : ℝ) / 2) γ hSv hS.2.1 j z
  change (w : ℝ) / 2 * (z ⬝ᵥ S.mean j) ^ 2 ≤ (1 + γ) * sqnorm z at hm
  have hγnorm := mul_le_mul_of_nonneg_right hγ1 (Rounding.DetRoundAux.sqnorm_nonneg z)
  have hmean : (w : ℝ) * (z ⬝ᵥ S.mean j) ^ 2 ≤ 5 := by
    nlinarith only [hm, hγnorm, hzhi]
  have hroot : 1 / (w : ℝ) ≤ (sqrtUp (1 / w) : ℝ) ^ 2 := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr (sqrtUp_sq (1 / w))
    push_cast at hh
    exact hh
  have hrootw := (div_le_iff₀ hwR).mp hroot
  have hsq : (z ⬝ᵥ S.mean j) ^ 2 ≤ (3 * (sqrtUp (1 / w) : ℝ)) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hwR).mp
    nlinarith only [hmean, hrootw]
  have hroot0 : (0 : ℝ) ≤ sqrtUp (1 / w) := by unfold sqrtUp; positivity
  nlinarith only [hsq, sq_abs (z ⬝ᵥ S.mean j), abs_nonneg (z ⬝ᵥ S.mean j), hroot0]

end

end ABBKS26.Assembly.Exec.RefineSynth.IdMean
