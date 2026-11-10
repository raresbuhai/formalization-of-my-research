module

public import ABBKS26.Centered.Ident
public import ABBKS26.Centered.FeasibleAuxRank
public import ABBKS26.Centered.FeasibleAuxSoS

/-!
# Feasibility and rank bound for centered mixtures

[ABBKS26, Lemma 5.13]: once the eigenspaces of large covariance deviation are removed, the
centered constraint system is feasible; and [ABBKS26, Lemma 5.20]: these eigenspaces have
bounded total rank.
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section


open Matrix

open Common MvPolynomial
variable {k d : ℕ}

/-- Removing all exceptional eigenspaces makes the centered system feasible. -/
theorem feasible
    (F : FrameModel k d) (w γ rF δ εq εh : ℝ) (R : Mat d)
    (hF : DataValid F w γ rF) (hR : Projection R) (hδ : 0 < δ)
    (hsmall : ∀ i v, sqnorm ((deviation F i) *ᵥ ((1 - R) *ᵥ v)) ≤
      (δ + γ) ^ 2 * sqnorm ((1 - R) *ᵥ v))
    (hq : (δ + γ) ^ 2 ≤ εq)
    (hh : 64 * (δ + γ) ^ 4 + 16 * (1.1 / w) ^ 2 * (δ + γ) ^ 2 ≤ εh) :
    IsSumSq (subst (1 - R) (qConstraint (psi F) εq)) ∧
    IsSumSq (substV (1 - R) (hConstraint (psi F) εh)) ∧
    subst (1 - R) (1 - nsq) = 1 - nsq + quad R := by
  have _hδ := hδ
  refine ⟨FeasibleAux.q_feasible F w γ rF (δ + γ) εq (1 - R) hF hsmall hq,
    FeasibleAux.h_feasible F w γ rF (δ + γ) εh (1 - R) hF hsmall hh, ?_⟩
  have hP := Rounding.DetRoundAux.projection_compl R hR
  have hN : subst (1 - R) nsq = nsq - quad R := by
    rw [IdentAux.subst_nsq, hP.1, hP.2, IdentAux.quad_sub, IdentAux.quad_one]
  change (aeval _) (1 - nsq) = _
  rw [map_sub, map_one]
  change 1 - subst (1 - R) nsq = _
  rw [hN]
  ring

/-- The exceptional subspaces have the Frobenius rank bound. -/
theorem rank_bound
    (F : FrameModel k d) (w γ rF δ : ℝ) (hF : DataValid F w γ rF)
    (hδ : 0 < δ) : ∃ R : Mat d, Projection R ∧ R.rank ≤ ⌊rF / (w * δ ^ 2)⌋₊ ∧
      ∀ i v, sqnorm ((deviation F i) *ᵥ ((1 - R) *ᵥ v)) ≤
        (δ + γ) ^ 2 * sqnorm ((1 - R) *ᵥ v) := by
  exact FeasibleAux.rank_complement F w γ rF δ hF hδ

end

end ABBKS26.Centered
