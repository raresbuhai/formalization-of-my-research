module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdAffine

/-! Prepared variance validity for the concrete affine statistic program. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdValidity

open Common Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

theorem pullback (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k)
    (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (I : Finset (Fin k)) (hI : I.Nonempty) (S : IdCov.Data I.card d)
    (hframe : S.frame = (ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((IdFrame.frame (ps h) x fuel P).transform.map (algebraMap ℚ ℝ))
      (fun i ↦ ((IdFrame.frame (ps h) x fuel P).center i : ℝ))).model)
    (u : Vector) (j : Fin I.card) :
    qform S.cov (fun i ↦ (vectorOf d u i : ℝ)) =
      qform (M.S (ABBKS26.RefineAux.component I j))
        (fun i ↦ ((statisticOf d
          (IdProgram.statistic (args k ps x h P, fuel) u)).b i : ℝ)) := by
  have hcov : S.cov =
      (IdFrame.frame (ps h) x fuel P).transform.map (algebraMap ℚ ℝ) *
        M.S (ABBKS26.RefineAux.component I j) *
          ((IdFrame.frame (ps h) x fuel P).transform.map (algebraMap ℚ ℝ))ᵀ :=
    congrArg (fun F : FrameModel I.card d ↦ F.cov j) hframe
  rw [IdProgram.statistic_decoded ps x fuel h P hh,
    ABBKS26.RefineAux.meanStatistic_b, hcov]
  exact Separation.dotProduct_congr_mulVec _ _ _

/-- Only the magnitude bound for the raw pulled-back coefficients is needed for validity.
Coverage, the thin direction, and rounder semantic fuel do not enter this proof. -/
theorem valid_of_magnitude (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (RC : RoundCode)
    (hmag : ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h P,
      ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
        x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
        Prepared .identical M ε w η Δ D ω r ps →
        localBudget .identical k n d ps ≤ fuel → h < k - 1 →
        I.Nonempty → leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
        ∀ u ∈ IdProgram.grid MC NC RC (args k ps x h P, fuel), ∀ i,
          |(statisticOf d (IdProgram.statistic (args k ps x h P, fuel) u)).b i| ≤
            (2 : ℚ) ^ IdGuard.exponent (args k ps x h P, fuel)) :
    IdGuard.Valid (IdProgram.statistics MC NC RC) := by
  intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP q hq j hj
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hq
  let a := (args k ps x h P, fuel)
  let v := (statisticOf d (IdProgram.statistic a u)).b
  obtain ⟨S, hframe, hS, _⟩ := IdInput.prepared_certificate MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hβ : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 100 :=
    ⟨hs.2.2.1, hs.2.2.2.1⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hs
  have hγ : ((ps h).isotropy : ℝ) ≤ IdCov.gammaStar (ps h).subspaceAccuracy := by
    exact_mod_cast hm.2.2.2.1.le
  have hβf := IdFuel.fields k ps x fuel h P (by omega)
  have hnorm := (IdCoverage.norms (IdProgram.problem MC NC) IdNorms.normInput RC a
    (by rwa [show IdFuel.accuracy a = (ps h).subspaceAccuracy from hβf]) u hu).2
  change sqnorm (fun i ↦ (vectorOf d u i : ℝ)) ≤
    (1 + (IdFuel.accuracy a : ℝ)) ^ 2 at hnorm
  rw [show IdFuel.accuracy a = (ps h).subspaceAccuracy from hβf] at hnorm
  have hj' : j ∈ Set.range (I.orderEmbOfFin rfl) := by
    rw [I.range_orderEmbOfFin]
    exact hj
  obtain ⟨s, rfl⟩ := hj'
  have herror := IdAffine.covariance_error ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hh hl hP v (hmag k ps x fuel h P M ε w η Δ D ω r I
      hx hp hf hh hI hl hP u hu) _ (I.orderEmbOfFin_mem rfl s)
  exact IdGeometry.rounded_valid S (((ps h).w / 2 : ℚ) : ℝ) (ps h).isotropy
    (ps h).subspaceAccuracy hS hγ hβ s (M.S (ABBKS26.RefineAux.component I s))
    (hp.1.posDef _).posSemidef (fun i ↦ (vectorOf d u i : ℝ))
    (fun i ↦ (v i : ℝ))
    (fun i ↦ (SpecDirection.rounded (IdGuard.precision a) (IdGuard.exponent a) v i : ℝ))
    hnorm (pullback ps x fuel h P (by omega) M ω r I hI S hframe u s) herror

end

end ABBKS26.Assembly.Exec.RefineSynth.IdValidity
