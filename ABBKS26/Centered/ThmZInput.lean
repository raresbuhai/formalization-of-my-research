module

public import ABBKS26.Centered.ThmZAuxProof

/-! Count-uniform input and output contracts for centered subspace theorem Z. -/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section

open Common Matrix MvPolynomial Rounding

variable {d : ℕ}

/-- An RC2 input with the scheduled parameters and certificates for every compatible
model. This contract concerns the input system and contains no rounded output. -/
structure CenteredInputSpec (w r μ : ℚ) (p : QPoly d) (I : ComplementInput d) : Prop where
  radius_eq : I.radius = radius μ
  tolerance_eq : I.tolerance = roundTolerance μ
  rank_eq : I.rankBound = rankBound w r μ
  targets : ∀ {m : ℕ} (F : FrameModel m d) γ,
    0 < w → w ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 64 → 1 ≤ r →
    DataValid F w γ r → γ ≤ gammaStar w μ → p.IsHomogeneous 4 →
    IsSumSq (C (etaStar w μ : ℝ) * nsq ^ 4 - (SoS.toReal p - phi4 F) ^ 2) →
    ∃ Ps, I.Hypotheses Ps ∧ ∀ v, sqnorm v = 1 →
      (∃ i, qform (F.cov i) v ≤ 3 * (μ : ℝ) ^ 8) →
      ∃ P ∈ Ps, 1 - (I.tolerance : ℝ) ≤ sqnorm (P *ᵥ v)

/-- Z's original quantitative output, uniform over all hidden component counts. -/
def CenteredResultSpec (w r μ : ℚ) (p : QPoly d) (Y : RoundOutput d) : Prop :=
  Y.basis.length ≤ dimensionCap w r μ ∧ Projection Y.proj ∧
    Y.proj.rank = Y.basis.length ∧
    ∀ {m : ℕ} (F : FrameModel m d) γ,
      0 < w → w ≤ 1 / 2 → 0 < μ → μ ≤ 1 / 64 → 1 ≤ r →
      DataValid F w γ r → γ ≤ gammaStar w μ → p.IsHomogeneous 4 →
      IsSumSq (C (etaStar w μ : ℝ) * nsq ^ 4 - (SoS.toReal p - phi4 F) ^ 2) →
      Covers Y.proj {v | sqnorm v = 1 ∧ ∃ i, qform (F.cov i) v ≤ 3 * (μ : ℝ) ^ 8}
        (radius μ)

end

end ABBKS26.Centered
