module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdTransport

/-! Variance margins for affine coefficient rounding in the common-covariance branch. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdGeometry

open Common Matrix Rounding

noncomputable section

variable {m d : ℕ}

/-- The asymmetric triangle estimate leaves room for coefficient rounding after the net. -/
theorem near_three (S : Mat d) (hS : S.PosSemidef) (u v : Vec d) :
    qform S u ≤ 3 * qform S v + 3 / 2 * qform S (u - v) := by
  have hn := hS.dotProduct_mulVec_nonneg (u - (3 : ℝ) • v)
  have he : qform S (u - (3 : ℝ) • v) =
      6 * qform S v + 3 * qform S (u - v) - 2 * qform S u := by
    simp only [qform, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  change 0 ≤ qform S (u - (3 : ℝ) • v) at hn
  linarith only [hn, he]

theorem near_five (S : Mat d) (hS : S.PosSemidef) (c b : Vec d) :
    qform S c ≤ 5 / 4 * qform S b + 5 * qform S (c - b) := by
  have hn := hS.dotProduct_mulVec_nonneg ((4 : ℝ) • c - (5 : ℝ) • b)
  have he : qform S ((4 : ℝ) • c - (5 : ℝ) • b) =
      5 * qform S b + 20 * qform S (c - b) - 4 * qform S c := by
    simp only [qform, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  change 0 ≤ qform S ((4 : ℝ) • c - (5 : ℝ) • b) at hn
  linarith only [hn, he]

/-- This stronger version of the net variance estimate reserves an explicit margin for
the final affine rounding. -/
theorem net_variance (S : IdCov.Data m d) (π γ : ℝ) (β : ℚ)
    (hS : S.Valid π γ) (hγ : γ ≤ IdCov.gammaStar β)
    (hβ : 0 < β ∧ β ≤ 1 / 100) (j : Fin m) (u v : Vec d)
    (hv : qform S.cov v ≤ IdCov.tauStar β)
    (hnear : sqnorm (u - v) ≤ (2 * (β : ℝ)) ^ 2) :
    qform S.cov u ≤ 61 / 10 * (β : ℝ) ^ 2 := by
  have hγ100 : γ ≤ 1 / 100 :=
    hγ.trans (ABBKS26.RefineAux.identical_tolerances β hβ).1
  have hupper := ABBKS26.RefineAux.identical_covariance_le S.frame π γ hS.1 hS.2.1
    (fun _ _ ↦ rfl) j (u - v)
  change qform S.cov (u - v) ≤ (1 + γ) * sqnorm (u - v) at hupper
  have hvariance : qform S.cov (u - v) ≤
      (101 / 100 : ℝ) * (2 * (β : ℝ)) ^ 2 := by
    apply hupper.trans
    have he := mul_le_mul_of_nonneg_right hγ100 (DetRoundAux.sqnorm_nonneg (u - v))
    nlinarith only [he, hnear]
  have hthin := hv.trans (ABBKS26.RefineAux.identical_tolerances β hβ).2
  have hpsd : S.cov.PosSemidef := (hS.1.2.2.2 j).posSemidef
  have ht := near_three S.cov hpsd u v
  nlinarith only [ht, hvariance, hthin, sq_nonneg (β : ℝ)]

/-- Affine rounding preserves the common variance needed by the fixed mean windows. -/
theorem rounded_variance (S : Mat d) (hS : S.PosSemidef) (β : ℝ) (b c : Vec d)
    (hb : qform S b ≤ 61 / 10 * β ^ 2)
    (he : qform S (c - b) ≤ β ^ 2 / 16) :
    qform S c ≤ 9 * β ^ 2 := by
  have ht := near_five S hS c b
  linarith only [ht, hb, he, sq_nonneg β]

/-- Every shell point remains population-valid after bounded affine rounding, regardless
of whether it is the direction later used for completeness. -/
theorem rounded_valid (S : IdCov.Data m d) (π γ : ℝ) (β : ℚ)
    (hS : S.Valid π γ) (hγ : γ ≤ IdCov.gammaStar β)
    (hβ : 0 < β ∧ β ≤ 1 / 100) (j : Fin m)
    (A : Mat d) (hA : A.PosSemidef) (u b c : Vec d)
    (hnorm : sqnorm u ≤ (1 + (β : ℝ)) ^ 2)
    (hb : qform S.cov u = qform A b)
    (he : qform A (c - b) ≤ (β : ℝ) ^ 2 / 16) :
    qform A c ≤ 4 := by
  have hγ100 : γ ≤ 1 / 100 :=
    hγ.trans (ABBKS26.RefineAux.identical_tolerances β hβ).1
  have hβ0 : (0 : ℝ) ≤ β := by exact_mod_cast hβ.1.le
  have hβ100 : (β : ℝ) ≤ 1 / 100 := by
    have hc := Rat.cast_le (K := ℝ) |>.mpr hβ.2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hupper := ABBKS26.RefineAux.identical_covariance_le S.frame π γ hS.1 hS.2.1
    (fun _ _ ↦ rfl) j u
  change qform S.cov u ≤ (1 + γ) * sqnorm u at hupper
  have hnorm' : sqnorm u ≤ (101 / 100 : ℝ) ^ 2 :=
    hnorm.trans (pow_le_pow_left₀ (by positivity) (by linarith only [hβ100]) 2)
  have hraw : qform A b ≤ 2 := by
    have he := mul_le_mul_of_nonneg_right hγ100 (DetRoundAux.sqnorm_nonneg u)
    rw [← hb]
    nlinarith only [hupper, he, hnorm']
  have hβsq : (β : ℝ) ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ hβ0 (by linarith only [hβ100] : (β : ℝ) ≤ 1) 2).trans_eq
      (one_pow 2)
  have ht := near_five A hA c b
  linarith only [ht, hraw, he, hβsq]

end

end ABBKS26.Assembly.Exec.RefineSynth.IdGeometry
