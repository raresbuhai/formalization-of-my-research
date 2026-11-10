module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdProgram

/-! Transport of thin SUB directions to the executable shell-filtered net. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdTransport

open Common Matrix MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

/-- SUB consumes RC2 on the actual encoded moment system, then supplies the net's coverage.
The rounder's bit-sensitive fuel remains an independent machine obligation. -/
theorem prepared_cover (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) (RC : RoundCode) (hRC : RoundSpecL RC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hround : roundFuel (RoundProgram.input
      (IdCoverage.call (IdProgram.problem MC NC) IdNorms.normInput
        (args k ps x h P, fuel))) ≤ fuel) :
    let Y := IdFrame.frame (ps h) x fuel P
    ∃ S : IdCov.Data I.card d,
      S.frame = (ABBKS26.RefineAux.affineReference
        (ABBKS26.RefineAux.roundedReference M ω r P I hI)
        (Y.transform.map (algebraMap ℚ ℝ)) (fun i ↦ (Y.center i : ℝ))).model ∧
      ∀ v, sqnorm v = 1 → qform S.cov v ≤ IdCov.tauStar (ps h).subspaceAccuracy →
        ∃ u ∈ IdProgram.grid MC NC RC (args k ps x h P, fuel),
          sqnorm ((fun i ↦ (vectorOf d u i : ℝ)) - v) ≤
            (2 * ((ps h).subspaceAccuracy : ℝ)) ^ 2 := by
  let a : Args := (args k ps x h P, fuel)
  let moments := fun q ↦ ((IdInput.run MC a).getD q []).toPoly d
  let J := IdCov.SubspaceAux.input k d (ps h).w (ps h).subspaceAccuracy moments
  obtain ⟨S, hframe, hS, hγ, hcert⟩ := IdInput.prepared_hypotheses MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hβ : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 100 :=
    ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hβ4 : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 4 :=
    ⟨hβ.1, hβ.2.trans (by norm_num)⟩
  have hvalid : J.system.Valid J.degree := IdCov.SubspaceAux.system_valid S _ _ _ _
    (by unfold IdCov.tDegree; omega)
    (IdCov.SubspaceAux.rounded_certificate S moments _ _ hβ4 hcert)
  obtain ⟨hk, hd, hn, _⟩ := IdFuel.caps ps x fuel h P hf hh hβ
  have hβf := IdFuel.fields k ps x fuel h P (by omega)
  change IdFuel.accuracy a = (ps h).subspaceAccuracy at hβf
  have hwf : field a 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hβf' : field a 10 = (ps h).subspaceAccuracy := hβf
  have ht := (IdReify.fields k ps x fuel h P (by omega)).1
  change IdInput.degree a = IdCov.tDegree (ps h).w at ht
  have hε := (IdReify.fields k ps x fuel h P (by omega)).2.2
  change IdPayload.tolerance a = IdCov.epsilonR (ps h).subspaceAccuracy at hε
  have hfamily := IdReify.prepared_family MC hMC ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP
  have hlayout : IdSolver.layoutFuel d J.degree (IdReify.system MC a) ≤ fuel := by
    apply IdPrepared.layout ps fuel h M ε w η Δ D ω r hp hf hh
    simpa only [ht] using IdReify.length_system MC a
  have hball : ballBound J.system J.degree J.tolerance J.M₁ J.X ≤
      (IdNorms.ballInput a : ℝ) := by
    have hb := IdNorms.input_ball a k moments
    rw [hwf, hβf'] at hb
    exact hb
  have hnorm : nestedNorm J.system J.degree J.tolerance J.M₂ ≤
      (IdNorms.normInput a : ℝ) := by
    have hb := IdNorms.input_norm a k moments
      (by rw [hβf']; exact ⟨hβ.1, hβ.2.trans (by norm_num)⟩)
    rw [hwf, hβf'] at hb
    exact hb
  have hproblem : IdProgram.problem MC NC a = SpecSolver.zeroObjective
      (NC.build (IdSolver.query d J.degree (IdReify.system MC a) J.tolerance
        (IdNorms.ballInput a) fuel)) := by
    unfold IdProgram.problem IdProgram.query
    rw [ht, hε]
    rfl
  have hrank : IdFuel.rank a = k := min_eq_right hk
  have hcall : RoundProgram.input
      (IdCoverage.call (IdProgram.problem MC NC) IdNorms.normInput a) =
        RoundInput.mk (IdProgram.problem MC NC a) d J.radius J.rankBound
          (IdNorms.normInput a) := by
    change RoundInput.mk _ _ (IdFuel.accuracy a) (IdFuel.rank a) _ = _
    rw [hβf, hrank]
    rfl
  let E := IdNested.encoding J (IdReify.system MC a) (IdNorms.ballInput a) fuel
    hfamily hvalid hball hlayout NC hNC (IdNorms.normInput a)
    (IdNorms.normInput_one_le a) hnorm
  obtain ⟨run, hrun, hagree⟩ := hRC.semantic
  have hinput : E.roundInput = RoundProgram.input
      (IdCoverage.call (IdProgram.problem MC NC) IdNorms.normInput a) := by
    rw [hcall, hproblem]
    rfl
  have hresult := roundComplement_spec run hrun J E
  have hsub := IdCov.thmSUB k (ps h).w (ps h).subspaceAccuracy moments
    (run E.roundInput) hresult
  have hbasis : IdCoverage.basis (IdProgram.problem MC NC) IdNorms.normInput RC a =
      (run E.roundInput).basis.map List.ofFn := by
    rw [hinput]
    exact hagree _ fuel hround
  have hlen : (run E.roundInput).basis.length ≤
      IdCov.N_pack (IdFuel.accuracy a) a.1.2.1 := by
    change _ ≤ rankCap (IdFuel.accuracy a) k
    rw [hβf]
    exact hsub.1
  have hcover := hsub.2.2.2 S (ps h).isotropy
    (by simpa using Finset.card_le_univ I) hs.1 hs.2.1 hβ4.1 hβ4.2 hS hγ hcert
  change Covers _ _ (ps h).subspaceAccuracy at hcover
  rw [← hβf] at hcover
  refine ⟨S, hframe, ?_⟩
  intro v hv htv
  have he := IdCoverage.covers (IdProgram.problem MC NC) IdNorms.normInput RC a
    (by rwa [hβf]) hk (by rw [hβf]; exact hd)
    (by rw [hβf]; exact hn) (run E.roundInput) hbasis hlen hsub.2.2.1
    hcover v ⟨hv, by simpa only [hβf] using htv⟩
  rw [hβf] at he
  exact he

end

end ABBKS26.Assembly.Exec.RefineSynth.IdTransport
