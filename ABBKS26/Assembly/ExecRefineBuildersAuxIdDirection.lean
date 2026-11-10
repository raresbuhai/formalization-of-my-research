module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdMean
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdValidity

/-! Population mean witnesses in the actual executable SUB net. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdDirection

open Common Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

/-- The concrete SUB net contains a direction with strict mean and variance margins.
The only execution hypothesis beyond the prepared budget is the rounder's bit budget. -/
theorem prepared (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) (RC : RoundCode) (hRC : RoundSpecL RC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hcard : 2 ≤ I.card)
    (hround : roundFuel (RoundProgram.input
      (IdCoverage.call (IdProgram.problem MC NC) IdNorms.normInput
        (args k ps x h P, fuel))) ≤ fuel) :
    let a := (args k ps x h P, fuel)
    ∃ u ∈ IdProgram.grid MC NC RC a,
      let q := statisticOf d (IdProgram.statistic a u)
      (∀ j ∈ I, qform (M.S j) (fun i ↦ (q.b i : ℝ)) ≤
        61 / 10 * ((ps h).subspaceAccuracy : ℝ) ^ 2) ∧
      (∀ j ∈ I, |q.eval (M.μ j)| ≤ 3 * (sqrtUp (1 / (ps h).w) : ℝ)) ∧
      ∃ a ∈ I, ∃ b ∈ I, 19 / 20 ≤ |q.eval (M.μ a) - q.eval (M.μ b)| := by
  let p := ps h
  let a := (args k ps x h P, fuel)
  let F := IdFrame.frame p x fuel P
  let T := F.transform.map (algebraMap ℚ ℝ)
  let R := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let A := ABBKS26.RefineAux.affineReference R T (fun i ↦ (F.center i : ℝ))
  obtain ⟨hF, _⟩ := IdFrame.prepared ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP
  obtain ⟨hRv, _, _, _⟩ := IdAffine.compatible ps h P M ε w η Δ D ω r I hI
    hp hh hl hP
  have hT := (hp.frame_population_cov_at .identical M ε w η Δ D ω r ps h hh
    P I hI hl hP F hF).1
  have hAv : A.Valid (((p.w / 2 : ℚ) : ℝ)) :=
    ABBKS26.RefineAux.affineReference_valid R T _ _ hRv hT
  obtain ⟨S, hframe, hcover⟩ := IdTransport.prepared_cover MC hMC NC hNC RC hRC
    ps x fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP hround
  obtain ⟨S₀, hframe₀, hS₀, _⟩ := IdInput.prepared_certificate MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hS : S.Valid (((p.w / 2 : ℚ) : ℝ)) p.isotropy := by
    rw [IdCov.Data.Valid, hframe₀] at hS₀
    rwa [IdCov.Data.Valid, hframe]
  have hmean (j : Fin I.card) : S.mean j =
      T *ᵥ (M.μ (ABBKS26.RefineAux.component I j) - (fun i ↦ (F.center i : ℝ))) :=
    congrArg (fun F : FrameModel I.card d ↦ F.mean j) hframe
  have hcov (j : Fin I.card) : S.cov =
      T * M.S (ABBKS26.RefineAux.component I j) * Tᵀ :=
    congrArg (fun F : FrameModel I.card d ↦ F.cov j) hframe
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, _, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hs
  obtain ⟨_, _, _, hγeq, _, _, hsep16⟩ := hm
  have hγ : (p.isotropy : ℝ) ≤ IdCov.gammaStar p.subspaceAccuracy := by
    exact_mod_cast hγeq.le
  have hγ1 : (p.isotropy : ℝ) ≤ 1 :=
    (hγ.trans (ABBKS26.RefineAux.identical_tolerances _ ⟨hβ, hβ100⟩).1).trans
      (by norm_num)
  have hγ0 : (0 : ℝ) ≤ p.isotropy := hS.2.1.1
  have hη : 0 < η := hp.2.2.2.2.2.2.1
  obtain ⟨a₀, _, b₀, _, hab⟩ := Finset.one_lt_card.mp
    (show 1 < (Finset.univ : Finset (Fin I.card)).card by
      simpa using (show 1 < I.card by omega))
  have hsep := hp.separated_at .identical M ε w η Δ D ω r ps h (by omega)
  have hsepS : MeanSeparated p.separation (S.mean a₀) (S.mean b₀) S.cov := by
    rw [hmean a₀, hmean b₀, hcov a₀]
    apply (Separation.meanSeparated_congr (isUnit_iff_ne_zero.mpr hT)).mpr
    obtain ⟨v, hv⟩ := hsep (ABBKS26.RefineAux.component I a₀)
      (ABBKS26.RefineAux.component I b₀) ((I.orderEmbOfFin rfl).injective.ne hab)
    refine ⟨v, ?_⟩
    have he : (M.μ (ABBKS26.RefineAux.component I a₀) - (fun i ↦ (F.center i : ℝ))) -
        (M.μ (ABBKS26.RefineAux.component I b₀) - (fun i ↦ (F.center i : ℝ))) =
          M.μ (ABBKS26.RefineAux.component I a₀) -
            M.μ (ABBKS26.RefineAux.component I b₀) := by abel
    rwa [he]
  have hres := hp.reference_resilient_at .identical M ε w η Δ D ω r ps P I hI
    4 (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .identical M ε w η Δ D ω r ps)) (by decide)
  have hAr : A.Resilient 4 (η / 10 ^ 8) :=
    ABBKS26.RefineAux.affineReference_resilient R T _ _ _ hT hres
  have hC : frobSq (A.cov - 1) ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [ABBKS26.RefineAux.affineReference_cov R T _ hRv.2.2.2.2.1]
    apply (hp.close_frame_error_at .identical M ε w η Δ D ω r ps h hh
      P I hI hl hP F hF).trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hγ1]
  have hβf : IdFuel.accuracy a = p.subspaceAccuracy :=
    IdFuel.fields k ps x fuel h P (by omega)
  let Y := (IdProgram.grid MC NC RC a).map (vectorOf d)
  have hnorm (u) (hu : u ∈ Y) :
      (1 - (p.subspaceAccuracy : ℝ)) ^ 2 ≤ sqnorm (fun i ↦ (u i : ℝ)) ∧
        sqnorm (fun i ↦ (u i : ℝ)) ≤ (1 + (p.subspaceAccuracy : ℝ)) ^ 2 := by
    obtain ⟨uL, huL, rfl⟩ := List.mem_map.mp hu
    have he := IdCoverage.norms (IdProgram.problem MC NC) IdNorms.normInput RC a
      (by rw [hβf]; exact ⟨hβ, hβ100⟩) uL huL
    rwa [hβf] at he
  have hcover' (v) (hv : sqnorm v = 1) (ht : qform S.cov v ≤
      IdCov.tauStar p.subspaceAccuracy) :
      ∃ u ∈ Y, sqnorm ((fun i ↦ (u i : ℝ)) - v) ≤
        (2 * (p.subspaceAccuracy : ℝ)) ^ 2 := by
    obtain ⟨u, hu, he⟩ := hcover v hv ht
    exact ⟨vectorOf d u, List.mem_map.mpr ⟨u, hu, rfl⟩, he⟩
  obtain ⟨u, hu, hvar, hbound, a', b', hspread⟩ := IdMean.direction A S p.w
    p.subspaceAccuracy p.isotropy p.separation (η / 10 ^ 8) Y hAv hframe hS hγ
    ⟨hβ, hβ100⟩ hw (by exact_mod_cast hsep16) ⟨a₀, b₀, hsepS⟩
    ⟨by positivity, by linarith only [hp.2.2.2.2.2.2.2.1]⟩ hAr hC hnorm hcover'
  obtain ⟨uL, huL, rfl⟩ := List.mem_map.mp hu
  have hpre (j : Fin k) (hj : j ∈ I) :
      ∃ i : Fin I.card, ABBKS26.RefineAux.component I i = j := by
    have he : j ∈ Set.range (I.orderEmbOfFin rfl) := by
      rw [I.range_orderEmbOfFin]
      exact hj
    exact he
  have heval (j : Fin I.card) :
      (statisticOf d (IdProgram.statistic a uL)).eval
        (M.μ (ABBKS26.RefineAux.component I j)) =
      (fun i ↦ (vectorOf d uL i : ℝ)) ⬝ᵥ S.mean j := by
    rw [IdProgram.statistic_decoded ps x fuel h P (by omega),
      ABBKS26.RefineAux.meanStatistic_eval, hmean]
  refine ⟨uL, huL, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, rfl⟩ := hpre j hj
    rw [← IdValidity.pullback ps x fuel h P (by omega) M ω r I hI S hframe uL i]
    exact hvar
  · intro j hj
    obtain ⟨i, rfl⟩ := hpre j hj
    rw [heval]
    exact hbound i
  · refine ⟨ABBKS26.RefineAux.component I a', I.orderEmbOfFin_mem rfl a',
      ABBKS26.RefineAux.component I b', I.orderEmbOfFin_mem rfl b', ?_⟩
    rwa [heval, heval]

end

end ABBKS26.Assembly.Exec.RefineSynth.IdDirection
