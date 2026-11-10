module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecLedger
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecPrepared
public import ABBKS26.Centered.ThmZ

/-! Exact shape and scalar budget adapters for the executable empirical Z input. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecCertificate

open Common Centered Matrix MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

/-- The empirical family and the actual budgets supplied to the nested solver. -/
def input (F : FrameCode) (MC : MomentCode) (a : Args) : ComplementInput a.1.1 where
  system := (SpecFamily.family a.1.1 (SpecInput.payload F MC a)
    (SpecInput.epsilonQ a) (SpecInput.epsilonH a)).real
  degree := 8
  tolerance := SpecInput.tolerance a
  radius := SpecFuel.radius a
  rankBound := SpecFuel.rank a
  M₁ := SpecProgram.certificateNorm a
  M₂ := SpecComplement.norm a
  X := SpecProgram.instanceNorm a

/-- The executable input satisfies Z uniformly over all compatible component counts. -/
theorem prepared_input (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    let a := (args k ps x h P, fuel)
    CenteredInputSpec (SpecInput.weight a) (SpecFuel.deviation a) (SpecInput.accuracy a)
      ((SpecMoments.run F MC a).toPoly d) (input F MC a) := by
  let a := (args k ps x h P, fuel)
  let S : ℝ := SpecProgram.scale a
  obtain ⟨hw', hμ', hr'⟩ := SpecPrepared.fields k ps x fuel h P (by omega)
  change SpecInput.weight a = (ps h).w / 2 at hw'
  change SpecInput.accuracy a = (ps h).subspaceAccuracy at hμ'
  change SpecFuel.deviation a = 10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10 at hr'
  have hstep := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, hμ, hμ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hstep
  have hπ : 0 < SpecInput.weight a ∧ SpecInput.weight a ≤ 1 / 2 := by
    rw [hw']
    exact ⟨by positivity, by linarith only [hw2]⟩
  have hμ0 : 0 < SpecInput.accuracy a := hμ' ▸ hμ
  have hμ64 : SpecInput.accuracy a ≤ 1 / 64 := by rw [hμ']; linarith only [hμ100]
  obtain ⟨hS, hd, hsize, _, he, hscale⟩ := SpecLedger.scale_bounds a hπ hμ0
  have hSR : 4 ≤ S := by
    change 4 ≤ (SpecProgram.scale a : ℝ)
    exact_mod_cast hS
  have hdR : (d : ℝ) ≤ S := by
    have hd' : (d : ℚ) ≤ SpecProgram.scale a := (by norm_num : (d : ℚ) ≤ d + 1).trans hd
    change (d : ℝ) ≤ (SpecProgram.scale a : ℝ)
    exact_mod_cast hd'
  have heR : 1.1 / (SpecInput.weight a : ℝ) ≤ S := by
    have he' := Rat.cast_mono (K := ℝ) he
    norm_num at he'
    simpa only [S, show (1.1 : ℝ) = 11 / 10 by norm_num] using he'
  have hscaleR : 64 * (d + 1 : ℝ) ^ 2 + 1 / (SpecInput.weight a : ℝ) +
      1 / (12 * ((SpecInput.weight a : ℝ) ^ 8 * (SpecInput.accuracy a : ℝ) ^ 32) ^ 2) +
        1 / ((SpecInput.accuracy a : ℝ) ^ 8 / 100) ≤ S := by
    have hh' := Rat.cast_mono (K := ℝ) hscale
    push_cast at hh'
    rwa [SpecInput.delta, ThmZAux.delta_cast] at hh'
  obtain ⟨hX0, hX, hXlow⟩ := SpecLedger.instance_bounds a hπ hμ0
  have hXR : 0 ≤ (SpecProgram.instanceNorm a : ℝ) ∧
      (SpecProgram.instanceNorm a : ℝ) ≤ S ^ 2 := by
    constructor
    · exact_mod_cast hX0
    · change (SpecProgram.instanceNorm a : ℝ) ≤ (SpecProgram.scale a : ℝ) ^ 2
      exact_mod_cast hX
  have hsR : sizeParameter d ((ps h).w / 2) (ps h).subspaceAccuracy ≤ S := by
    rw [← SpecComplement.size_agrees k ps x fuel h P (by omega)]
    change (SpecComplement.size a : ℝ) ≤ (SpecProgram.scale a : ℝ)
    exact_mod_cast hsize
  obtain ⟨hcap, _, _⟩ := SpecPrepared.caps ps x fuel h P hf hh ⟨hμ, hμ100⟩
  have hround := SpecPayload.prepared_agrees F hF MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  have hshape : CenteredEmpiricalShape (SpecInput.weight a) (SpecFuel.deviation a)
      (SpecInput.accuracy a) ((SpecMoments.run F MC a).toPoly d) (input F MC a) := by
    refine ⟨?_, rfl, rfl, rfl, SpecFuel.rank_agrees a hcap⟩
    change (SpecFamily.family d _ _ _).real = _
    rw [SpecFamily.family_real d _ _ _ (SpecInput.payload_raw F MC a)]
    have hΨ : SoS.toReal ((SpecInput.payload F MC a).toPoly d) =
        empiricalPsi (SpecInput.weight a) (SpecInput.accuracy a)
          ((SpecMoments.run F MC a).toPoly d) := by
      change SoS.toReal ((SpecInput.psi d (SpecPayload.run F MC a)).toPoly d) = _
      rw [SpecInput.psi_real, hround]
      simp only [empiricalPsi, hw', hμ']
      rfl
    rw [hΨ]
    simp only [SpecInput.epsilonQ, SpecInput.epsilonH, SpecInput.delta,
      Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
    rfl
  have hM₁ : (1 : ℚ) ≤ SpecProgram.certificateNorm a := by
    have hpow := one_le_pow₀ (by linarith only [hS] : (1 : ℚ) ≤ SpecProgram.scale a)
      (n := 200)
    have hε : 0 ≤ SpecInput.tolerance a := by
      unfold SpecInput.tolerance roundTolerance
      positivity
    unfold SpecProgram.certificateNorm
    linarith only [hpow, hε]
  have hM₂ : (1 : ℚ) ≤ SpecComplement.norm a := by
    have hrest : 0 ≤ SpecComplement.size a ^ 7 * (2 * (a.1.1 + 1 : ℚ)) ^ 8 := by
      unfold SpecComplement.size
      positivity
    unfold SpecComplement.norm
    linarith only [hrest, sq_nonneg (a.1.1 : ℚ)]
  have hXone : (1 : ℚ) ≤ SpecProgram.instanceNorm a := by
    unfold SpecProgram.instanceNorm
    apply one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 d)
    exact (le_div_iff₀ hπ.1).2 (by linarith only [hπ.2])
  have hbounds : CenteredEmpiricalBounds (SpecInput.weight a) (SpecInput.accuracy a)
      (input F MC a) := by
    refine ⟨S, hSR, hdR, heR, hscaleR, ?_, hXR, hXlow, ?_, ?_, ?_, ?_, ?_⟩
    · change sizeParameter d (SpecInput.weight a) (SpecInput.accuracy a) ≤ S
      simpa only [hw', hμ'] using hsR
    · change (SpecProgram.scale a : ℝ) ^ 200 + (roundTolerance (SpecInput.accuracy a) : ℝ)
        ≤ (SpecProgram.certificateNorm a : ℝ)
      simp only [SpecProgram.certificateNorm, SpecInput.tolerance, Rat.cast_add, Rat.cast_pow]
      exact le_rfl
    · change 1 + (d : ℝ) ^ 2 + sizeParameter d (SpecInput.weight a)
        (SpecInput.accuracy a) ^ 7 * (2 * (d + 1 : ℝ)) ^ 8 ≤ (SpecComplement.norm a : ℝ)
      have heq := SpecComplement.size_agrees k ps x fuel h P (by omega)
      change (SpecComplement.size a : ℝ) = _ at heq
      rw [hw', hμ']
      simp only [SpecComplement.norm, Rat.cast_add, Rat.cast_one, Rat.cast_pow,
        Rat.cast_natCast, Rat.cast_mul, Rat.cast_ofNat,
        heq]
      exact le_rfl
    · change (1 : ℝ) ≤ (SpecProgram.certificateNorm a : ℝ)
      exact_mod_cast hM₁
    · change (1 : ℝ) ≤ (SpecComplement.norm a : ℝ)
      exact_mod_cast hM₂
    · change (1 : ℝ) ≤ (SpecProgram.instanceNorm a : ℝ)
      exact_mod_cast hXone
  exact empirical_complement_conditions _ _ _ _ _ hshape hbounds

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecCertificate
