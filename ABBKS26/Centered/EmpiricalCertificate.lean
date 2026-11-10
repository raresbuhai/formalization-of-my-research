module

public import ABBKS26.Centered.EmpiricalLedger
public import ABBKS26.Centered.EmpiricalFeasibility

/-! Shared analytic preparation for the rounded empirical centered system. -/

@[expose] public section

namespace ABBKS26.Centered.EmpiricalCertificate

open Common Matrix MvPolynomial Rounding
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

theorem local_certificate {m : ℕ} (G : FrameModel m d) (w μ g r W X : ℝ)
    (Ψ : RPoly d) (hG : DataValid G w g r)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hμ : 0 < μ ∧ μ ≤ 1 / 64)
    (hg : g ≤ (w ^ 8 * μ ^ 32) ^ 2 / 20) (hΨ : Ψ.IsHomogeneous 4)
    (herr : IsSumSq (C ((w ^ 8 * μ ^ 32) ^ 4) * nsq ^ 4 - (Ψ - psi G) ^ 2))
    (hW : 4 ≤ W) (hd : (d : ℝ) ≤ W) (he : 1.1 / w ≤ W)
    (hsize : 64 * (d + 1 : ℝ) ^ 2 + 1 / w +
      1 / (12 * (w ^ 8 * μ ^ 32) ^ 2) + 1 / (μ ^ 8 / 100) ≤ W)
    (hX : 0 ≤ X ∧ X ≤ W ^ 2) (hXlow : Real.sqrt d * (1.1 / w) ≤ X)
    (hqn : SoS.coeffNorm1 (qConstraint Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2)) ≤ W ^ 5)
    (hhn : SoS.coeffNorm1 (hConstraint Ψ (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)) ≤
      W ^ 7) (i : Fin m) :
    ∃ P : Mat d, Projection P ∧
      (system Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2)
        (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)).Derives
        8 (W ^ 200 + 7 * μ ^ 8) X (C (7 * μ ^ 8) - quad P) ∧
      ∀ v, sqnorm v = 1 → qform (G.cov i) v ≤ 3 * μ ^ 8 →
        1 - 7 * μ ^ 8 ≤ sqnorm (P *ᵥ v) := by
  have hs := ThmZAux.schedule w μ g hw hμ ⟨hG.2.2.1.1, hg⟩
  let t := w ^ 8 * μ ^ 32
  have hqt : 0 ≤ 12 * t ^ 2 ∧ 12 * t ^ 2 ≤ 1 := by
    have ht : 0 < t ∧ t ≤ 1 / 64 := ⟨hs.1, hs.2.1⟩
    constructor
    · positivity
    · nlinarith only [ht.1, ht.2, sq_nonneg (t - 1 / 64)]
  have hht : 0 ≤ 513 * t ^ 2 / w ^ 2 ∧ 513 * t ^ 2 / w ^ 2 ≤ 4 := by
    have hh := hs.2.2.2.2.2.2.1
    have hh' := hs.2.2.2.2.2.2.2.1
    refine ⟨hh.le, hh'.trans ?_⟩
    nlinarith only [hw.1, hw.2, sq_nonneg (w - 1 / 2)]
  obtain ⟨hq, hh⟩ := EmpiricalLedger.transfer_bounds G w g r μ W X Ψ hG hW hd he hX
    hqn hhn t hqt hht
  obtain ⟨P, hP, hder, hnear⟩ := EmpiricalProjection.low_certificate G w μ g r W X
    (W ^ 64) Ψ hG hw hμ hg hΨ herr hsize (by linarith only [hW]) hXlow
      (one_le_pow₀ (by linarith only [hW])) hq hh i
  refine ⟨P, hP, ?_, hnear⟩
  obtain ⟨Ξ, hΞ, hder⟩ := hder
  exact ⟨Ξ, hΞ, hder.mono (EmpiricalLedger.certificate_bound W _ hW)⟩

end

end ABBKS26.Centered.EmpiricalCertificate
