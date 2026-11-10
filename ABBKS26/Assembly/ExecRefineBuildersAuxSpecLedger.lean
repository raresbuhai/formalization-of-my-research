module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecProgram

/-! Explicit coefficient envelopes for the centered target certificates. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecLedger

open Common Centered Matrix MvPolynomial
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

/-- Every summand in the local certificate scale has its advertised interpretation. -/
theorem scale_bounds (a : Builders.Args)
    (hw : 0 < SpecInput.weight a ∧ SpecInput.weight a ≤ 1 / 2)
    (hμ : 0 < SpecInput.accuracy a) :
    4 ≤ SpecProgram.scale a ∧ (a.1.1 + 1 : ℚ) ≤ SpecProgram.scale a ∧
      SpecComplement.size a ≤ SpecProgram.scale a ∧
      1 / SpecInput.weight a ≤ SpecProgram.scale a ∧
      1.1 / SpecInput.weight a ≤ SpecProgram.scale a ∧
      64 * (a.1.1 + 1 : ℚ) ^ 2 + 1 / SpecInput.weight a +
        1 / (12 * SpecInput.delta a ^ 2) + 1 / (SpecInput.accuracy a ^ 8 / 100) ≤
          SpecProgram.scale a := by
  let w := SpecInput.weight a
  let μ := SpecInput.accuracy a
  have hw0 : 0 < w := hw.1
  have hμ0 : 0 < μ := hμ
  have hs : 0 ≤ SpecComplement.size a := by unfold SpecComplement.size; positivity
  have hiw : 0 ≤ 1 / w ^ 2 := by positivity
  have hit : 0 ≤ 1 / (12 * SpecInput.delta a ^ 2) := by positivity
  have hiμ : 0 ≤ 100 / μ ^ 8 := by positivity
  have hD : (1 : ℚ) ≤ a.1.1 + 1 := by exact_mod_cast Nat.le_add_left 1 a.1.1
  have hdim : (a.1.1 + 1 : ℚ) ≤ 64 * (a.1.1 + 1 : ℚ) ^ 2 := by
    have he := le_self_pow₀ hD (by norm_num : (2 : ℕ) ≠ 0)
    nlinarith only [he, sq_nonneg (a.1.1 + 1 : ℚ)]
  have hinv : 1 / w ≤ 1 / w ^ 2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hw0)
    have hw1 : w ≤ 1 := by linarith only [hw.2]
    simpa only [pow_two] using mul_le_of_le_one_right hw0.le hw1
  have he : 1.1 / w ≤ 1 / w ^ 2 := by
    rw [div_le_div_iff₀ hw0 (sq_pos_of_pos hw0)]
    have hsmall : (1.1 : ℚ) * w ≤ 1 := by linarith only [hw.2]
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hw0.le]
  have hμeq : 1 / (μ ^ 8 / 100) = 100 / μ ^ 8 := by ring
  change 4 ≤ SpecProgram.scale a ∧ _
  dsimp only [SpecProgram.scale]
  change 4 ≤ 64 * (a.1.1 + 1 : ℚ) ^ 2 + 1 / w ^ 2 +
      1 / (12 * SpecInput.delta a ^ 2) + 100 / μ ^ 8 + SpecComplement.size a + 4 ∧ _
  rw [show 1 / (SpecInput.accuracy a ^ 8 / 100) = 100 / μ ^ 8 from hμeq]
  exact ⟨by linarith only [hiw, hit, hiμ, hs, sq_nonneg (a.1.1 + 1 : ℚ)],
    by linarith only [hdim, hiw, hit, hiμ, hs],
    by linarith only [hiw, hit, hiμ, sq_nonneg (a.1.1 + 1 : ℚ)],
    by linarith only [hinv, hit, hiμ, hs, sq_nonneg (a.1.1 + 1 : ℚ)],
    by linarith only [he, hit, hiμ, hs, sq_nonneg (a.1.1 + 1 : ℚ)],
    by linarith only [hinv, hs]⟩

theorem instance_bounds (a : Builders.Args)
    (hw : 0 < SpecInput.weight a ∧ SpecInput.weight a ≤ 1 / 2)
    (hμ : 0 < SpecInput.accuracy a) :
    0 ≤ SpecProgram.instanceNorm a ∧
      SpecProgram.instanceNorm a ≤ SpecProgram.scale a ^ 2 ∧
      Real.sqrt a.1.1 * (1.1 / (SpecInput.weight a : ℝ)) ≤
        (SpecProgram.instanceNorm a : ℝ) := by
  obtain ⟨hW, hd, _, _, he, _⟩ := scale_bounds a hw hμ
  have hw0 := hw.1
  have hdim : Real.sqrt a.1.1 ≤ (a.1.1 + 1 : ℚ) := by
    push_cast
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith only [Nat.cast_nonneg (α := ℝ) a.1.1, sq_nonneg (a.1.1 : ℝ)]
  refine ⟨by unfold SpecProgram.instanceNorm; positivity, ?_, ?_⟩
  · change (a.1.1 + 1 : ℚ) * (1.1 / SpecInput.weight a) ≤ SpecProgram.scale a ^ 2
    nlinarith only [mul_le_mul hd he (by positivity) (by linarith only [hW])]
  · have heq : (SpecProgram.instanceNorm a : ℝ) =
        (a.1.1 + 1 : ℚ) * (1.1 / (SpecInput.weight a : ℝ)) := by
      unfold SpecProgram.instanceNorm
      push_cast
      norm_num
    rw [heq]
    exact mul_le_mul_of_nonneg_right hdim
      (by positivity : (0 : ℝ) ≤ 1.1 / (SpecInput.weight a : ℝ))


end

end ABBKS26.Assembly.Exec.RefineSynth.SpecLedger
