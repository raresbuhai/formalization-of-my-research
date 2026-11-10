module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecCertificate
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecCoverage

/-! Transport of thin population directions to the executable spectral grid. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecTransport

open Common Centered Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

abbrev input := SpecCertificate.input

/-- Representation and budget transport for this particular empirical call. -/
def encoding (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (a : Args)
    (hrep : RawRep (nestedInput (SpecInput.query F MC SpecProgram.ball a))
      (SpecSolver.zeroObjective (NC.build (SpecInput.query F MC SpecProgram.ball a))))
    (hμ : 0 < SpecInput.accuracy a) : RCEncoding (input F MC a) where
  raw := nestedInput (SpecInput.query F MC SpecProgram.ball a)
  problem := SpecSolver.zeroObjective (NC.build (SpecInput.query F MC SpecProgram.ball a))
  normBound := SpecConcentration.norm a
  dimension_eq := rfl
  system_eq := rfl
  degree_eq := rfl
  tolerance_eq := rfl
  represents := hrep
  objective_degree := by
    intro f hf
    change f ∈ [[]] at hf
    rw [List.mem_singleton.mp hf]
    simp [SoS.Solver.RawPoly.toPoly]
  ball_le := (SpecTargets.ball_agrees a.1.1 _ _ _ _ _ _).ge
  norm_one_le := SpecConcentration.norm_one_le a
  norm_le := SpecConcentration.nestedNorm_le F MC SpecProgram.ball a hμ

/-- A thin direction is covered by the executable grid at the prepared local budget. -/
theorem prepared_cover (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC)
    (RC : RoundCode) (hRC : RoundSpecL RC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI)
    (i : Fin I.card) (v : Vec d) (hv : sqnorm v = 1)
    (ht : qform ((ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model.cov i)
        v ≤ 3 * ((ps h).subspaceAccuracy : ℝ) ^ 8) :
    let a := (args k ps x h P, fuel)
    ∃ q ∈ SpecFuel.grid (SpecProgram.normalized F MC NC RC) a,
      sqnorm (fun c ↦ (vectorOf d q c : ℝ)) ≤ 4 ∧
      |‖WithLp.toLp 2 (fun c ↦ (vectorOf d q c : ℝ))‖ - 1| ≤
        ((ps h).subspaceAccuracy : ℝ) / 4 ∧
      ‖WithLp.toLp 2 (fun c ↦ (vectorOf d q c : ℝ)) - WithLp.toLp 2 v‖ ≤
        (33 : ℝ) * (ps h).subspaceAccuracy := by
  let a := (args k ps x h P, fuel)
  let G := (ABBKS26.RefineAux.affineReference
    (ABBKS26.RefineAux.roundedReference M ω r P I hI)
    ((SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model
  obtain ⟨hw, hμ, hr⟩ := SpecPrepared.fields k ps x fuel h P (by omega)
  change SpecInput.weight a = (ps h).w / 2 at hw
  change SpecInput.accuracy a = (ps h).subspaceAccuracy at hμ
  change SpecFuel.deviation a = 10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10 at hr
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hμvalid : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 100 :=
    ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hμvalid' : 0 < SpecInput.accuracy a ∧ SpecInput.accuracy a ≤ 1 / 100 := by
    rwa [hμ]
  obtain ⟨hrank, hdim, hnet⟩ := SpecPrepared.caps ps x fuel h P hf hh hμvalid
  have hrep := SpecInput.prepared_rep F hF MC hMC NC hNC SpecProgram.ball ps x
    fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  have hdegree : (SpecProgram.roundArgs F MC NC a).1.degree ≤ 26 := by
    change (SpecSolver.zeroObjective
      (NC.build (SpecInput.query F MC SpecProgram.ball a))).degree ≤ 26
    rw [hrep.2.1]
    exact SpecSolver.solverDegree_le _ (SpecFamily.family_valid d _ _ _
      (SpecInput.payload_raw F MC a)
      (SpecInput.prepared_homogeneous F hF MC hMC ps x fuel h P M ε w η Δ D ω r I hI
        hx hp hf hh hl hP hnf))
  have hrank' := SpecFuel.rank_agrees a hrank
  have hZinput := SpecCertificate.prepared_input F hF MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  let J := input F MC a
  let E := encoding F MC NC a hrep hμvalid'.1
  obtain ⟨run, hrun, hagree⟩ := hRC.semantic
  have hinput : E.roundInput = RoundProgram.input (SpecProgram.roundArgs F MC NC a) := rfl
  have hcap : rankCap (SpecFuel.radius a) (SpecFuel.rank a) ≤ a.2 := by
    rw [hrank']
    exact hdim
  have hbasis : SpecProgram.basis F MC NC RC a = (run E.roundInput).basis.map List.ofFn :=
    hagree E.roundInput _ (by
      rw [hinput]
      exact SpecSolver.roundFuel_le 26 (SpecProgram.roundArgs F MC NC a, a.2) hdegree hcap)
  have hresult := Centered.thmZ (SpecInput.weight a) (SpecFuel.deviation a)
    (SpecInput.accuracy a) ((SpecMoments.run F MC a).toPoly d) J (run E.roundInput)
      hZinput (roundComplement_spec run hrun J E)
  have hdata := SpecFrame.prepared_data F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  obtain ⟨hhom, hcert, _⟩ := SpecMoments.prepared_quartic F hF MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  obtain ⟨hw0, hw2, hμ0, hμ100, _, _, _, _, _, _, _, _, hσ, _, _, _, hm⟩ := hs
  have hπ : 0 < (ps h).w / 2 ∧ (ps h).w / 2 ≤ 1 / 2 :=
    ⟨by positivity, by linarith only [hw2]⟩
  have hσ1 := ABBKS26.RefineAux.sigmaSq_one_le (ps h) hw0 hw2 hσ
  have hr1 : (1 : ℚ) ≤ SpecFuel.deviation a := by
    rw [hr]
    have hn : 0 ≤ 10000 * (ps h).sigmaSq / ((ps h).w / 2) := by positivity
    linarith only [hn]
  have hg : ((ps h).isotropy : ℝ) ≤ gammaStar ((ps h).w / 2)
      (ps h).subspaceAccuracy := by rw [hm.2.2.2.2.2.2.2.2.1]
  have hcover := hresult.2.2.2 G ((ps h).isotropy)
    (by rw [hw]; exact hπ.1) (by rw [hw]; exact hπ.2)
    hμvalid'.1 (hμvalid'.2.trans (by norm_num)) hr1
    (by simpa only [hw, hr] using hdata) (by simpa only [hw, hμ] using hg)
    hhom (by simpa only [hw, hμ] using hcert)
  have hlen : (run E.roundInput).basis.length ≤
      rankCap (SpecFuel.radius a) (SpecFuel.rank a) := by
    rw [hrank']
    exact hresult.1
  have he := SpecCoverage.grid_covers F MC NC RC a hμvalid' hrank hdim hnet
    (run E.roundInput) hbasis hlen hresult.2.2.1 hcover v ⟨hv, i, by rwa [hμ]⟩
  rw [hμ] at he
  dsimp only [a, args] at he ⊢
  exact he

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecTransport
