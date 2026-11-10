module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecInput

/-! Normed complement certificates for the reified centered family. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecComplement

open Common Centered Matrix MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

def size (a : Args) : ℚ :=
  64 * (a.1.1 + 1 : ℚ) ^ 2 * 2 ^ SpecPayload.precision a *
    (⌈1 / (SpecInput.weight a * SpecInput.accuracy a)⌉₊ : ℚ) ^ 40

def norm (a : Args) : ℚ :=
  1 + (a.1.1 : ℚ) ^ 2 + size a ^ 7 * (2 * (a.1.1 + 1 : ℚ)) ^ 8

theorem size_polytime : ComputableInPolyTime size encArgs encRat := by
  have hd : ComputableInPolyTime (fun a : Args ↦ (a.1.1 : ℚ)) encArgs encRat :=
    rat_natCast' (unary_to_binary.comp (by fun_prop))
  have hw := rat_div' (field_polytime 0) (const 2)
  have hμ := field_polytime 10
  exact rat_mul' (rat_mul' (rat_mul' (const 64)
    (FrameAux.Linear.rat_pow' (rat_add' hd (const 1)) (const 2)))
    (rat_two_pow' SpecPayload.precision_polytime))
    (FrameAux.Linear.rat_pow' (rat_natCast'
      (FrameAux.Linear.rat_natCeil' (rat_div' (const 1) (rat_mul' hw hμ)))) (const 40))

theorem norm_polytime : ComputableInPolyTime norm encArgs encRat := by
  have hd : ComputableInPolyTime (fun a : Args ↦ (a.1.1 : ℚ)) encArgs encRat :=
    rat_natCast' (unary_to_binary.comp (by fun_prop))
  exact rat_add' (rat_add' (const 1) (FrameAux.Linear.rat_pow' hd (const 2)))
    (rat_mul' (FrameAux.Linear.rat_pow' size_polytime (const 7))
      (FrameAux.Linear.rat_pow' (rat_mul' (const 2) (rat_add' hd (const 1))) (const 8)))

noncomputable section

variable {d : ℕ}

theorem size_agrees {n : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    (size (args k ps x h P, fuel) : ℝ) =
      sizeParameter d ((ps h).w / 2) (ps h).subspaceAccuracy := by
  have hw : field (args k ps x h P, fuel) 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  have hμ : field (args k ps x h P, fuel) 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  simp only [size, sizeParameter, SpecPayload.precision, SpecInput.weight,
    SpecInput.accuracy, hw, hμ]
  push_cast
  rfl


end

end ABBKS26.Assembly.Exec.RefineSynth.SpecComplement
