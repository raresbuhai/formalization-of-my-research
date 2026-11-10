module

public import ABBKS26.IdCov.RoundCondAux

/-!
# Rounding conditions for identical covariances

[ABBKS26, Lemma 6.15]: the moment system satisfies the two hypotheses of the
orthogonal-complement rounding (`ABBKS26.Rounding.roundComplement_spec`).
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {k d : ℕ}

private theorem quad_homogeneous (A : Mat d) : (quad A).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  apply IsHomogeneous.sum
  intro j _
  simpa only [mul_assoc] using
    ((isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ j)).C_mul (A i j)

/-- The large-eigenvalue mean projection admits an SoS comparison. -/
theorem spectral_projection
    (D : Data k d) (π γ τ : ℝ) (hD : D.Valid π γ) (hτ : 0 < τ) :
    ∃ P : Mat d, Projection P ∧ LE (τ • P) (between D) ∧
      LE (between D) ((1 + γ) • P + τ • (1 - P)) := by
  have _ := hτ
  apply RoundCondAux.spectral_cut (between D) (RoundCondAux.between_psd D π γ hD)
  intro v
  have hh := (SoS.isSumSq_map (eval v) (sos_bounds D π γ hD).2.2.2).nonneg
  simpa only [map_sub, map_mul, eval_C, ApproxAux.eval_nsq, Q, ApproxAux.eval_quad,
    qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, sqnorm,
    sub_nonneg] using hh

/-- Mean-energy identifiability supplies rounding hypothesis (i). -/
theorem round_ident
    (A : List (RPoly d)) (D : Data k d) (P : Mat d) (deg : ℕ)
    (c τ ε M : ℝ) (hτ : 0 < τ) (hε : c / τ ≤ ε)
    (hP : P.PosSemidef) (hle : LE (τ • P) (between D))
    (hid : SoS.DerivesNq A deg M 1 (C c - Q D)) (hdeg : 2 ≤ deg) :
    SoS.DerivesNq A deg
      (M / τ + SoS.coeffNorm1 (Q D - C τ * quad P) / τ + |ε - c / τ|) 1
      (C ε - quad P) := by
  have _ := hP
  have hhom : (Q D - C τ * quad P).IsHomogeneous 2 :=
    (quad_homogeneous (between D)).sub ((quad_homogeneous P).C_mul τ)
  have hgap : IsSumSq (Q D - C τ * quad P) := by
    apply ApproxAux.quadratic_sos _ hhom
    intro v
    have hv := hle v
    simpa only [Q, map_sub, map_mul, eval_C, ApproxAux.eval_quad,
      qform, smul_mulVec, dotProduct_smul, smul_eq_mul, sub_nonneg] using hv
  have hgd : (Q D - C τ * quad P).totalDegree ≤ deg := by
    exact ((totalDegree_sub _ _).trans (max_le (IdentAux.quad_degree _)
      ((totalDegree_mul _ _).trans (by
        rw [totalDegree_C, zero_add]
        exact IdentAux.quad_degree _)))).trans hdeg
  have hg := SoS.DerivesNq.ofIsSOS (q := 1) A
    (by simpa only [SoS.IsSOS, SoS.toReal_real] using hgap) hgd le_rfl
  have hc := SoS.DerivesNq.ofIsSOS (q := 1) (k := deg) A
    (SoS.IsSOS.const (sub_nonneg.mpr hε)) (by rw [totalDegree_C]; omega) (le_refl _)
  have hh := ((hid.smul (inv_nonneg.mpr hτ.le)).add
    (hg.smul (inv_nonneg.mpr hτ.le))).add hc
  have he : C τ⁻¹ * (C c - Q D) + C τ⁻¹ * (Q D - C τ * quad P) +
      C (ε - c / τ) = C ε - quad P := by
    rw [C_sub, div_eq_mul_inv, C_mul]
    have ht : C τ⁻¹ * C τ = (1 : RPoly d) := by
      rw [← C_mul, inv_mul_cancel₀ hτ.ne', map_one]
    linear_combination -(quad P) * ht
  apply (hh.congr he).mono le_rfl
  simp only [SoS.coeffNorm1_C, div_eq_mul_inv]
  ring_nf
  exact le_rfl

/-- The means span a subspace of rank at most the number of components. -/
theorem mean_span
    (D : Data k d) : ∃ R : Mat d, Projection R ∧ R.rank ≤ k ∧
      ∀ i, R *ᵥ D.mean i = D.mean i := by
  exact RoundCondAux.mean_projection D

/-- Substituted feasibility has bounded linear multipliers. -/
theorem round_feasible
    (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (π γ η ε W : ℝ)
    (hD : D.Valid π γ) (hη : 0 ≤ η) (hsmall : γ + Real.sqrt η ≤ 1)
    (hM : momentCertificate D M t η) (hε : η * gammaD t ≤ ε)
    (hε1 : ε ≤ 1)
    (hW : NormLedger D M t π ε W) :
    ∃ R : Mat d, Projection R ∧ R.rank ≤ k ∧
      (Rounding.plainSystem (system M t ε)).FeasibleComplement R (W ^ (20 * t)) := by
  by_cases ht : t = 0
  · subst t
    refine ⟨0, ⟨by simp, by simp⟩, by simp, ?_⟩
    constructor
    · intro f hf
      have hf' : f = 1 - nsq := by
        simpa [Rounding.plainSystem, system] using hf
      subst f
      simp only [sub_zero, mul_zero, pow_zero, RoundCondAux.subst_one]
      exact SoS.DerivesNq.of_mem (by simp [ball]) le_rfl le_rfl
    · simp [Rounding.plainSystem]
  have ht' : 1 ≤ t := by omega
  have hb := ApproxAux.size_bounds_one ht' hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hε0 : 0 ≤ ε :=
    (mul_nonneg hη (by unfold gammaD; positivity)).trans hε
  obtain ⟨R, hR, hr, hm⟩ := mean_span D
  refine ⟨R, hR, hr, ?_⟩
  constructor
  · intro f hf
    change f ∈ system M t ε at hf
    simp only [system, List.mem_append, List.mem_singleton, List.mem_filter,
      List.mem_map, List.mem_range] at hf
    rcases hf with rfl | ⟨⟨j, hj, rfl⟩, _⟩
    · apply (RoundCondAux.feasible_ball R hR).mono le_rfl
      have hn : SoS.coeffNorm1 (quad R) ≤ (d : ℝ) ^ 2 := by
        simpa only [mul_one] using
          IdentAux.norm_quad R 1 (RoundCondAux.projection_entry R hR)
      calc
        _ ≤ W := by linarith [hb.2.2.1]
        _ ≤ _ := by simpa using SoS.pow_le_pow_of_two_le hW2 (show 1 ≤ 20 * t by omega)
    · let s := j + 2
      have hs : 2 ≤ s ∧ s ≤ 2 * t := by dsimp [s]; omega
      have hd : (constraint M ε s).totalDegree ≤ 4 * s :=
        (ApproxAux.constraint_homogeneous M ε s (hM.1 1 (by omega) (by omega))
          (hM.1 s (by omega) hs.2)).totalDegree_le
      exact SoS.DerivesNq.ofIsSOS ball
        (by simpa only [SoS.IsSOS, SoS.toReal_real] using
          feasibility D M t π γ η ε R hD hη hsmall hM hε hR hm s hs.1 hs.2)
        (RoundCondAux.subst_degree _ _)
        (RoundCondAux.constraint_subst_norm D M t s π ε W (1 - R) ht' hs ⟨hε0, hε1⟩
          hW (Rounding.DetRoundAux.projection_compl R hR) hd)
  · simp [Rounding.plainSystem]

/-- A thin common-covariance direction lies nearly in the mean spectral subspace. -/
theorem geometry
    (D : Data k d) (P : Mat d) (π γ τ τP : ℝ) (u : Vec d)
    (hD : D.Valid π γ) (hP : Projection P) (hu : sqnorm u = 1)
    (hτP : γ ≤ τP ∧ τP ≤ 1 / 2) (hτ : 0 ≤ τ)
    (hlo : LE (τP • P) (between D))
    (hhi : LE (between D) ((1 + γ) • P + τP • (1 - P)))
    (hthin : qform D.cov u ≤ τ) : 1 - 2 * γ - τ - τP ≤ sqnorm (P *ᵥ u) := by
  have _ := hτ
  have _ := hlo
  have hs : ∑ i, D.weight i = 1 := hD.1.2.2.1
  have hsecond : D.frame.second = D.cov + between D := by
    simp only [FrameModel.second, Data.frame, smul_add, Finset.sum_add_distrib,
      ← Finset.sum_smul, hs, one_smul, between]
  have hl := hD.2.1.2.1 u
  have hh := hhi u
  have hp := Rounding.DetRoundAux.projection_sqnorm P hP u
  have hc := Rounding.DetRoundAux.projection_contract P hP u
  rw [hu] at hc
  rw [hsecond] at hl
  simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub] at hl hh
  change u ⬝ᵥ u = 1 at hu
  change sqnorm (P *ᵥ u) = u ⬝ᵥ (P *ᵥ u) at hp
  change u ⬝ᵥ (D.cov *ᵥ u) ≤ τ at hthin
  rw [hu] at hl hh
  rw [← hp] at hh
  have hn : 0 ≤ sqnorm (P *ᵥ u) := Rounding.DetRoundAux.sqnorm_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hτP.1) hn, hD.2.1.1]

end

end ABBKS26.IdCov
