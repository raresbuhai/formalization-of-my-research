module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecComplement

/-! Local rational bounds for concentration of the executable centered nested system. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecConcentration

open Common Centered Matrix MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def numerator (a : Args) : ℚ :=
  let b := (a.1.1 + 1 : ℚ) ^ 8
  4 * (2 * (SpecComplement.norm a + 1) * (a.1.1 + 1 : ℚ) ^ 16 * b ^ 5) +
    b * (b + 1) ^ 2 + ((a.1.1 + 1 : ℚ) ^ 2 + 2) ^ 2

def norm (a : Args) : ℚ := numerator a / (4 * SpecInput.accuracy a ^ 4) + 1

theorem numerator_polytime : ComputableInPolyTime numerator encArgs encRat := by
  have hd : ComputableInPolyTime (fun a : Args ↦ (a.1.1 + 1 : ℚ)) encArgs encRat :=
    rat_add' (rat_natCast' (unary_to_binary.comp (by fun_prop))) (const 1)
  have hb := FrameAux.Linear.rat_pow' hd (const 8)
  exact rat_add' (rat_add' (rat_mul' (const 4) (rat_mul'
    (rat_mul' (rat_mul' (const 2) (rat_add' SpecComplement.norm_polytime (const 1)))
      (FrameAux.Linear.rat_pow' hd (const 16)))
    (FrameAux.Linear.rat_pow' hb (const 5))))
    (rat_mul' hb (FrameAux.Linear.rat_pow' (rat_add' hb (const 1)) (const 2))))
    (FrameAux.Linear.rat_pow' (rat_add'
      (FrameAux.Linear.rat_pow' hd (const 2)) (const 2)) (const 2))

theorem norm_polytime : ComputableInPolyTime norm encArgs encRat :=
  rat_add' (rat_div' numerator_polytime (rat_mul' (const 4)
    (FrameAux.Linear.rat_pow' (field_polytime 10) (const 4)))) (const 1)

theorem norm_one_le (a : Args) : 1 ≤ norm a := by
  have hsize : 0 ≤ SpecComplement.size a := by
    unfold SpecComplement.size
    positivity
  have hnorm : 0 ≤ SpecComplement.norm a := by
    unfold SpecComplement.norm
    positivity
  have hn : 0 ≤ numerator a := by
    unfold numerator
    positivity
  unfold norm
  exact le_add_of_nonneg_left (div_nonneg hn (by positivity))

noncomputable section

/-- The square root in `nestedNorm` is replaced by the smaller rational fourth power. -/
theorem nestedNorm_le (F : FrameCode) (MC : MomentCode) (Bd : Args → ℚ) (a : Args)
    (hμ : 0 < SpecInput.accuracy a) :
    nestedNorm (nestedInput (SpecInput.query F MC Bd a)).family.real 8
      (SpecInput.tolerance a) (SpecComplement.norm a) ≤ (norm a : ℝ) := by
  have hμR : (0 : ℝ) < SpecInput.accuracy a := by exact_mod_cast hμ
  have heps : (0 : ℝ) ≤ SpecInput.tolerance a := by
    unfold SpecInput.tolerance Centered.roundTolerance
    positivity
  have hs : (SpecInput.accuracy a : ℝ) ^ 4 ≤
      Real.sqrt (SpecInput.tolerance a : ℝ) := by
    apply (Real.le_sqrt (by positivity) heps).mpr
    simp only [SpecInput.tolerance, Centered.roundTolerance,
      Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
    nlinarith only [pow_nonneg hμR.le 8]
  have hn : 0 ≤ (numerator a : ℝ) := by
    have hsize : 0 ≤ SpecComplement.size a := by unfold SpecComplement.size; positivity
    have hnorm : 0 ≤ SpecComplement.norm a := by unfold SpecComplement.norm; positivity
    have hnum : 0 ≤ numerator a := by unfold numerator; positivity
    exact_mod_cast hnum
  have hd := div_le_div_of_nonneg_left hn
    (by positivity : (0 : ℝ) < 4 * (SpecInput.accuracy a : ℝ) ^ 4)
    (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4))
  change _ ≤ (norm a : ℝ)
  convert add_le_add_right hd 1 using 1
  · simp [nestedNorm, SpecInput.query, SpecSolver.query, nestedInput,
      SpecFamily.plain, RawFamily.real, numerator]
    ring
  · simp only [norm, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_one]
    ring

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecConcentration
