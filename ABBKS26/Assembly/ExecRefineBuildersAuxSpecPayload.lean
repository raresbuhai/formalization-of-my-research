module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecRound
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobSize

/-! A sample-independent coefficient ledger for the executable quartic payload. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecPayload

open Common _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly encRawPoly)

def magnitude (w : ℚ) : ℚ := 20 / (w / 2) ^ 2

def exponent (w : ℚ) : ℕ := (encRat (magnitude w)).length

theorem magnitude_polytime : ComputableInPolyTime magnitude encRat encRat := by
  exact rat_div' (const 20)
    (FrameAux.Linear.rat_pow' (rat_div' id' (const 2)) (const 2))

theorem exponent_polytime : ComputableInPolyTime exponent encRat encUnary :=
  .of_tidy ((ComputableTidilyInPolyTime.encoding_length encRat).comp
    magnitude_polytime.tidy)

theorem magnitude_le (w : ℚ) : magnitude w ≤ (2 : ℚ) ^ exponent w :=
  (le_abs_self _).trans (FrobSize.of_encoding (le_refl _)).magnitude

theorem precision_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {w μ : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hw : ComputableInPolyTime w enc encRat)
    (hμ : ComputableInPolyTime μ enc encRat) :
    ComputableInPolyTime (fun a ↦ Centered.momentPrecision (d a) (w a / 2) (μ a))
      enc encUnary := by
  have hδ : ComputableInPolyTime (fun a ↦ Centered.delta (w a / 2) (μ a))
      enc encRat := FrameAux.Linear.rat_pow'
    (rat_mul' (rat_div' hw (const 2)) (FrameAux.Linear.rat_pow' hμ (const 4))) (const 8)
  have hdim := rat_natCast' (unary_to_binary.comp hd)
  exact binary_clog_two.comp (FrameAux.Linear.rat_natCeil' (rat_div'
    (rat_mul' (const 3) (FrameAux.Linear.rat_pow' (rat_add' hdim (const 1)) (const 4)))
    (FrameAux.Linear.rat_pow' hδ (const 2))))

def precision (a : Args) : ℕ :=
  Centered.momentPrecision a.1.1 (field a 0 / 2) (field a 10)

theorem precision_polytime : ComputableInPolyTime precision encArgs encUnary :=
  precision_polytime_of (by fun_prop) (field_polytime 0) (field_polytime 10)

def run (F : FrameCode) (M : MomentCode) (a : Args) : RawPoly :=
  SpecRound.run a.1.1 (precision a) (exponent (field a 0)) (SpecMoments.run F M a)

theorem run_polytime (F : FrameCode) (hF : FrameSpec F)
    (M : MomentCode) (hM : MomentSpec M) :
    ComputableInPolyTime (run F M) encArgs encRawPoly :=
  SpecRound.run_polytime_of (by fun_prop) precision_polytime
    (exponent_polytime.comp (field_polytime 0)) (SpecMoments.run_polytime F hF M hM)


noncomputable section

variable {n k d : ℕ}

/-- The guarded dense payload agrees with mathematical coefficient rounding on every
compatible non-FAR node, even for moment programs with duplicate or cancelling terms. -/
theorem prepared_agrees (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    (run F MC (args k ps x h P, fuel)).toPoly d =
      roundPoly (Centered.momentPrecision d ((ps h).w / 2) (ps h).subspaceAccuracy)
        ((SpecMoments.run F MC (args k ps x h P, fuel)).toPoly d) := by
  obtain ⟨hhom, _, hbound⟩ := SpecMoments.prepared_quartic F hF MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  have hw : field (args k ps x h P, fuel) 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hμ : field (args k ps x h P, fuel) 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  dsimp only [run, precision]
  rw [hw, hμ]
  exact SpecRound.run_agrees _ _ _ hhom (fun α ↦ (hbound α).trans (magnitude_le _))


end

end ABBKS26.Assembly.Exec.RefineSynth.SpecPayload
