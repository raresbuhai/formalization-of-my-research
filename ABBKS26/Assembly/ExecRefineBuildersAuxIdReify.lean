module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdSystem
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdPrepared

/-! Reification of the actual rounded SUB system at the prepared local allowance. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdReify

open Common Matrix MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly encRawPoly)

def system (MC : MomentCode) (a : Args) : List RawPoly :=
  IdSystem.run a.1.1 (IdInput.degree a) a.2 (IdPayload.systemError a)
    (IdPayload.moment MC a)

theorem system_polytime (MC : MomentCode) (hMC : MomentSpec MC) :
    ComputableInPolyTime (system MC) encArgs (encList encRawPoly) :=
  IdSystem.run_polytime_of (by fun_prop) IdInput.degree_polytime (snd _ _)
    IdPayload.systemError_polytime (IdPayload.moment_polytime MC hMC)

theorem length_system (MC : MomentCode) (a : Args) :
    (system MC a).length ≤ 2 * IdInput.degree a + 1 :=
  IdSystem.length_run _ _ _ _ _

variable {n k d : ℕ}

theorem fields (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    IdInput.degree (args k ps x h P, fuel) = IdCov.tDegree (ps h).w ∧
      IdPayload.systemError (args k ps x h P, fuel) =
        IdCov.epsilonSys (ps h).w (ps h).subspaceAccuracy ∧
      IdPayload.tolerance (args k ps x h P, fuel) =
        IdCov.epsilonR (ps h).subspaceAccuracy := by
  simp only [IdInput.degree, IdPayload.systemError, IdPayload.tolerance,
    field_args _ _ _ _ _ _ hh]
  exact ⟨rfl, rfl, rfl⟩

noncomputable section

theorem quadratic_length (MC : MomentCode)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1) :
    (IdPayload.moment MC (args k ps x h P, fuel) 2).length ≤ (d + 1) ^ 2 := by
  obtain ⟨hr, he⟩ := IdPrepared.enumeration ps fuel h M ε w η Δ D ω r hp hf hh 2
    (by unfold IdCov.tDegree; omega)
  exact IdRound.length_run d 2 fuel _ _ _ hr he

/-- Every needed even moment is rounded before forming SUB's constraints, and the
executable zero test agrees with the analytic system's zero removal. -/
theorem prepared_system (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    (system MC (args k ps x h P, fuel)).map (fun p ↦ SoS.toReal (p.toPoly d)) =
      IdCov.system (IdCov.SubspaceAux.roundedMoments d (ps h).w
        (ps h).subspaceAccuracy
        (fun q ↦ ((IdInput.run MC (args k ps x h P, fuel)).getD q []).toPoly d))
          (IdCov.tDegree (ps h).w) (IdCov.epsilonSys (ps h).w (ps h).subspaceAccuracy) := by
  let a : Args := (args k ps x h P, fuel)
  obtain ⟨ht, he, _⟩ := fields k ps x fuel h P (by omega)
  have hL := quadratic_length MC ps x fuel h P M ε w η Δ D ω r hp hf hh
  have hrun := IdSystem.run_agrees d (IdCov.tDegree (ps h).w) fuel
    (IdCov.epsilonSys (ps h).w (ps h).subspaceAccuracy) (IdPayload.moment MC a)
    (fun s _ hs ↦ IdPrepared.expansion ps fuel h M ε w η Δ D ω r hp hf hh s _ hs hL)
    (fun s _ hs ↦ (IdPrepared.enumeration ps fuel h M ε w η Δ D ω r hp hf hh
      (2 * s) (by omega)).2)
  change (IdSystem.run d (IdInput.degree a) fuel (IdPayload.systemError a)
    (IdPayload.moment MC a)).map _ = _
  rw [ht, he, hrun]
  apply IdSystem.system_congr
  · intro s hs hs'
    obtain ⟨hr, he'⟩ := IdPrepared.enumeration ps fuel h M ε w η Δ D ω r hp hf hh
      (2 * s) (by omega)
    exact congrArg SoS.toReal (IdPayload.prepared_agrees MC hMC ps x fuel h P
      M ε w η Δ D ω r I hI hx hp hf hh hl hP s ⟨hs, hs'⟩ hr he')
  · unfold IdCov.tDegree
    omega

theorem prepared_family (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    plainSystem ((system MC (args k ps x h P, fuel)).map
      fun p ↦ SoS.toReal (p.toPoly d)) =
      (IdCov.SubspaceAux.input k d (ps h).w (ps h).subspaceAccuracy
        (fun q ↦ ((IdInput.run MC (args k ps x h P, fuel)).getD q []).toPoly d)).system :=
  congrArg plainSystem (prepared_system MC hMC ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP)

/-- The prepared global allowance pays the nested layout, with no new fuel premise. -/
theorem prepared_rep (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) (Bd : ℚ)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    let a := (args k ps x h P, fuel)
    let q := IdSolver.query d (8 * IdInput.degree a) (system MC a)
      (IdPayload.tolerance a) Bd fuel
    RawRep (nestedInput q) (SpecSolver.zeroObjective (NC.build q)) := by
  let a : Args := (args k ps x h P, fuel)
  have ht := (fields k ps x fuel h P (by omega)).1
  change IdInput.degree a = IdCov.tDegree (ps h).w at ht
  have hfamily := prepared_family MC hMC ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP
  obtain ⟨S, _, Q, hJ, _⟩ := IdInput.prepared_subspace MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  apply IdSolver.represents NC hNC
  · change (plainSystem ((system MC a).map fun p ↦ SoS.toReal (p.toPoly d))).Valid
      (8 * IdInput.degree a)
    rw [hfamily, ht]
    exact hJ.1
  · rw [ht]
    apply IdPrepared.layout ps fuel h M ε w η Δ D ω r hp hf hh (system MC a)
    simpa only [ht] using length_system MC a

end

end ABBKS26.Assembly.Exec.RefineSynth.IdReify
