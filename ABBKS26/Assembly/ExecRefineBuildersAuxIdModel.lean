module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdFrame

/-! Population data for SUB with an arbitrary certified rational center. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdModel

open Common Matrix _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

theorem isotropic
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card)
    (F : Robust.FrameResult d)
    (hF : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r N I hI) F
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
        (((params h).isotropy / 10000 : ℚ) : ℝ))
    (a : Fin d → ℚ)
    (hm : sqnorm (F.transform.map (algebraMap ℚ ℝ) *ᵥ
      ((fun i ↦ (a i : ℝ)) - (ABBKS26.RefineAux.roundedReference M ω r N I hI).mean)) ≤
        400 * (params h).contamination) :
    let p := params h
    let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
    let T := F.transform.map (algebraMap ℚ ℝ)
    (ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))).model.Isotropic
      p.isotropy := by
  let p := params h
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let T := F.transform.map (algebraMap ℚ ℝ)
  let A := ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))
  have hv := hp.reference_valid_at mode M ε w η Δ D ω r params N I hI
  have hr := hp.reference_resilient_at mode M ε w η Δ D ω r params N I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree mode M ε w η Δ D ω r params)) (by decide)
  have he := hp.close_frame_error_at mode M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  obtain ⟨hT, _⟩ := hp.frame_population_cov_at mode M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  have hηc := IdFrame.eta_contamination mode M ε w η Δ D ω r params hp h hh
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, _, _, _, hready, _⟩ := hp
  have hstep := hready h hh
  have hγ1 : (p.isotropy : ℝ) ≤ 1 := by
    exact_mod_cast IdFrame.isotropy_le_one mode k _ _ hstep
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, hζ, hζle, _⟩ := hstep
  have hσ1 : (1 : ℝ) ≤ p.sigmaSq := by
    exact_mod_cast ABBKS26.RefineAux.sigmaSq_one_le p hw hw2 hσ
  have hγ : (0 : ℝ) < p.isotropy := by
    exact_mod_cast (show 0 < (params h).isotropy by linarith only [hζ, hζle])
  have hreqγ := hreq.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hbudget : (p.contamination : ℝ) * (10 ^ 10 * p.sigmaSq) ≤
      (p.isotropy : ℝ) ^ 2 := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 10 ^ 10 * p.sigmaSq)).mp
    exact_mod_cast hreqγ
  have hc0 : (0 : ℝ) ≤ p.contamination :=
    (by positivity : 0 ≤ 8 * η).trans hηc
  have hcσ := mul_le_mul_of_nonneg_left hσ1 hc0
  have hγsq : (p.isotropy : ℝ) ^ 2 ≤ p.isotropy := by nlinarith only [hγ.le, hγ1]
  have hcγ : 10 ^ 10 * (p.contamination : ℝ) ≤ p.isotropy := by
    nlinarith only [hbudget, hcσ, hγsq]
  have hb : 400 * (p.contamination : ℝ) ≤ 1 / 100 := by
    linarith only [hcγ, hγ1]
  have herror : 2 * ((p.isotropy : ℝ) / 1000) +
      2 * (400 * p.contamination) + 40 * (η / 10 ^ 8) ≤ p.isotropy := by
    linarith only [hcγ, hηc, hγ.le]
  have hAv : A.Valid (w / 2) :=
    ABBKS26.RefineAux.affineReference_valid R T _ _ hv hT
  have hAr : A.Resilient 4 (η / 10 ^ 8) :=
    ABBKS26.RefineAux.affineReference_resilient R T _ _ _ hT hr
  have hAe : frobSq (A.cov - 1) ≤ ((p.isotropy : ℝ) / 1000) ^ 2 := by
    rw [ABBKS26.RefineAux.affineReference_cov R T _ hv.2.2.2.2.1]
    exact he
  have hAm : sqnorm A.mean ≤ 400 * (p.contamination : ℝ) := by
    rw [ABBKS26.RefineAux.affineReference_mean R T _ hv.2.2.2.2.1]
    rw [show R.mean - (fun i ↦ (a i : ℝ)) =
      -((fun i ↦ (a i : ℝ)) - R.mean) by abel, mulVec_neg,
      Robust.FilterAux.sqnorm_neg]
    exact hm
  exact ABBKS26.RefineAux.isotropic_mono A.model _ _
    (ABBKS26.RefineAux.affine_isotropic_of_empirical A (w / 2) (η / 10 ^ 8)
      (p.isotropy / 1000) (400 * p.contamination) hAv
      ⟨by positivity, by linarith only [hη100]⟩ hAr
      ⟨by positivity, by linarith only [hγ1]⟩ ⟨by positivity, hb⟩ hAe hAm) herror


theorem data
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .identical M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card)
    (F : Robust.FrameResult d)
    (hF : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r N I hI) F
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
        (((params h).isotropy / 10000 : ℚ) : ℝ))
    (a : Fin d → ℚ)
    (hm : sqnorm (F.transform.map (algebraMap ℚ ℝ) *ᵥ
      ((fun i ↦ (a i : ℝ)) - (ABBKS26.RefineAux.roundedReference M ω r N I hI).mean)) ≤
        400 * (params h).contamination) :
    let p := params h
    let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
    let T := F.transform.map (algebraMap ℚ ℝ)
    ∃ S : IdCov.Data I.card d,
      S.frame = (ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))).model ∧
        S.Valid (w / 2) p.isotropy := by
  let p := params h
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let T := F.transform.map (algebraMap ℚ ℝ)
  let A := ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))
  let j₀ : Fin I.card := ⟨0, Finset.card_pos.mpr hI⟩
  let S : IdCov.Data I.card d := ⟨A.model.weight, A.model.mean, A.model.cov j₀⟩
  have hv := hp.reference_valid_at .identical M ε w η Δ D ω r params N I hI
  obtain ⟨hT, _⟩ := hp.frame_population_cov_at .identical M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  have hAv : A.Valid (w / 2) :=
    ABBKS26.RefineAux.affineReference_valid R T _ _ hv hT
  have hiso := isotropic .identical M ε w η Δ D ω r params hp h hh
    N I hI hl hN F hF a hm
  obtain ⟨_, hid, _, _, _, _, _, _, _, _, _, _, _, _, hready, _⟩ := hp
  have hcov (j : Fin I.card) : A.model.cov j = A.model.cov j₀ := by
    change T * M.S (ABBKS26.RefineAux.component I j) * Tᵀ =
      T * M.S (ABBKS26.RefineAux.component I j₀) * Tᵀ
    rw [hid (ABBKS26.RefineAux.component I j) (ABBKS26.RefineAux.component I j₀)]
  have hframe : S.frame = A.model := by
    have he : (fun _ ↦ A.model.cov j₀) = A.model.cov :=
      funext fun j ↦ (hcov j).symm
    change FrameModel.mk A.model.weight A.model.mean (fun _ ↦ A.model.cov j₀) =
      FrameModel.mk A.model.weight A.model.mean A.model.cov
    rw [he]
  have hγ : (p.isotropy : ℝ) ≤ 1 / 4 := by
    obtain ⟨_, _, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hready h hh
    obtain ⟨_, _, _, hγ, _⟩ := hm
    have hβ1 : (params h).subspaceAccuracy / 25 ≤ 1 := by linarith only [hβ100]
    have hpw := pow_le_one₀ (by positivity : 0 ≤ (params h).subspaceAccuracy / 25)
      hβ1 (n := 8)
    have hγQ : (params h).isotropy ≤ 1 / 4 := by
      rw [hγ]
      change ((params h).subspaceAccuracy / 25) ^ 8 / 6 ≤ 1 / 4
      linarith only [hpw]
    have hc := Rat.cast_le (K := ℝ) |>.mpr hγQ
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  refine ⟨S, hframe, ?_⟩
  rw [IdCov.Data.Valid, hframe]
  exact ⟨hAv.1, hiso, hγ⟩


end

end ABBKS26.Assembly.Exec.RefineSynth.IdModel
