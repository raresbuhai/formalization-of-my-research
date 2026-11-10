module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecConcentration

/-! A local rational ball for the centered nested family. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecTargets

open Common Centered Matrix MvPolynomial Rounding
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- Degree eight makes the interpolation constants fixed. Only their exponents depend
on the dimension, so the ball has polynomially many bits. -/
def ball (d : ℕ) (ε M X : ℚ) : ℚ :=
  2 + X ^ 2 + 4 * (d + 1 : ℚ) ^ 4 * (SoS.interpBound 4 : ℚ) ^ (2 * d) *
    5 ^ d * 5 ^ d * (2 * M + 2 * ε + 6 * (d + 1 : ℚ) ^ 2) * 4 ^ 8

theorem ball_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {ε M X : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hε : ComputableInPolyTime ε enc encRat)
    (hM : ComputableInPolyTime M enc encRat)
    (hX : ComputableInPolyTime X enc encRat) :
    ComputableInPolyTime (fun a ↦ ball (d a) (ε a) (M a) (X a)) enc encRat := by
  have hdQ := rat_add' (rat_natCast' (unary_to_binary.comp hd)) (const 1)
  have hfive := FrameAux.Linear.rat_pow' (const (5 : ℚ)) hd
  exact rat_add' (rat_add' (const 2) (FrameAux.Linear.rat_pow' hX (const 2)))
    (rat_mul' (rat_mul' (rat_mul' (rat_mul' (rat_mul'
      (rat_mul' (const 4) (FrameAux.Linear.rat_pow' hdQ (const 4)))
      (FrameAux.Linear.rat_pow' (const (SoS.interpBound 4 : ℚ))
        (unary_mul' (const 2) hd))) hfive) hfive)
      (rat_add' (rat_add' (rat_mul' (const 2) hM) (rat_mul' (const 2) hε))
        (rat_mul' (const 6) (FrameAux.Linear.rat_pow' hdQ (const 2)))))
      (const (4 ^ 8)))

noncomputable section

theorem ball_agrees (d : ℕ) (p : SoS.Solver.RawPoly) (εq εh ε M X : ℚ) :
    (ball d ε M X : ℝ) =
      ballBound (SpecFamily.family d p εq εh).real 8 ε M X := by
  have hc : (SpecFamily.family d p εq εh).real.plain.length = 2 ∧
      (SpecFamily.family d p εq εh).real.slots.length = 1 := by
    simp [SpecFamily.family, SpecFamily.plain, RawFamily.real]
  unfold ballBound
  rw [hc.1, hc.2]
  have hd : (SpecFamily.family d p εq εh).dimension = d := rfl
  rw [hd]
  simp only [ball, gridConst, Rat.cast_add, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
  norm_num
  ring_nf
  exact Or.inl True.intro

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecTargets
