module

public import ABBKS26.Centered.ThmZInput
public import ABBKS26.Centered.EmpiricalCertificate
public import ABBKS26.Centered.EmpiricalComplement

/-! The actual rounded degree-eight empirical family supplies the input contract of Z. -/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section

open Common Matrix MvPolynomial Rounding

variable {d : ℕ}

def empiricalPsi (w μ : ℚ) (p : QPoly d) : RPoly d :=
  SoS.toReal (roundPoly (momentPrecision d w μ) p) - 3 * nsq ^ 2

/-- Exact family shape; coefficient rounding is performed once on the original quartic. -/
structure CenteredEmpiricalShape (w r μ : ℚ) (p : QPoly d)
    (I : ComplementInput d) : Prop where
  system_eq : I.system = system (empiricalPsi w μ p)
    (8 * (delta w μ : ℝ) ^ 2) (256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2)
  degree_eq : I.degree = 8
  radius_eq : I.radius = radius μ
  tolerance_eq : I.tolerance = roundTolerance μ
  rank_eq : I.rankBound = rankBound w r μ

/-- Explicit scalar envelopes for identifiability, matrix instances, and feasible
complements. Sampling, isotropy, and coefficient-rounding error are proved below. -/
structure CenteredEmpiricalBounds (w μ : ℚ) (I : ComplementInput d) where
  scale : ℝ
  scale_four : 4 ≤ scale
  dimension_le : (d : ℝ) ≤ scale
  reciprocal_le : 1.1 / (w : ℝ) ≤ scale
  ident_le : 64 * (d + 1 : ℝ) ^ 2 + 1 / (w : ℝ) +
    1 / (12 * ((w : ℝ) ^ 8 * (μ : ℝ) ^ 32) ^ 2) +
      1 / ((μ : ℝ) ^ 8 / 100) ≤ scale
  size_le : sizeParameter d w μ ≤ scale
  instance_bounds : 0 ≤ I.X ∧ I.X ≤ scale ^ 2
  instance_le : Real.sqrt d * (1.1 / (w : ℝ)) ≤ I.X
  certificate_le : scale ^ 200 + (roundTolerance μ : ℝ) ≤ I.M₁
  complement_le : 1 + (d : ℝ) ^ 2 +
    sizeParameter d w μ ^ 7 * (2 * (d + 1 : ℝ)) ^ 8 ≤ I.M₂
  certificate_one : 1 ≤ I.M₁
  complement_one : 1 ≤ I.M₂
  instance_one : 1 ≤ I.X

/-- Homogeneous quartics give the precise family degree required by RC2. -/
theorem empirical_system_valid (Ψ : RPoly d) (εq εh : ℝ)
    (hΨ : Ψ.IsHomogeneous 4) : (system Ψ εq εh).Valid 8 := by
  refine ⟨List.mem_cons_self, ?_, ?_⟩
  · intro f hf
    change f ∈ [1 - nsq, qConstraint Ψ εq] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact (totalDegree_sub _ _).trans
        (max_le (by simp) (IdentAux.nsq_degree.trans (by norm_num)))
    · rw [List.mem_singleton.mp hf]
      exact (EmpiricalTransfer.q_homogeneous Ψ εq hΨ).totalDegree_le
  · intro f hf
    change f ∈ [hConstraint Ψ εh] at hf
    rw [List.mem_singleton.mp hf]
    exact (IdentAux.hConstraint_homogeneous _ _ hΨ).totalDegree_le

/-- The empirical system has low-eigenvalue certificates and a normed common feasible
complement for every compatible model, with the original radius and rank schedule. -/
theorem empirical_complement_conditions (w r μ : ℚ) (p : QPoly d)
    (I : ComplementInput d) (hshape : CenteredEmpiricalShape w r μ p I)
    (B : CenteredEmpiricalBounds w μ I) : CenteredInputSpec w r μ p I := by
  classical
  refine ⟨hshape.radius_eq, hshape.tolerance_eq, hshape.rank_eq, ?_⟩
  intro m F γ hw hw' hμ hμ' hr hF hγ hp he
  have hwR : 0 < (w : ℝ) ∧ (w : ℝ) ≤ 1 / 2 := by
    refine ⟨by exact_mod_cast hw, ?_⟩
    have ht := Rat.cast_mono (K := ℝ) hw'
    norm_num at ht
    exact ht
  have hμR : 0 < (μ : ℝ) ∧ (μ : ℝ) ≤ 1 / 64 := by
    refine ⟨by exact_mod_cast hμ, ?_⟩
    have ht := Rat.cast_mono (K := ℝ) hμ'
    norm_num at ht
    exact ht
  have hδ : delta w μ ≠ 0 := by unfold delta nu; positivity
  let Ψ := empiricalPsi w μ p
  have hΨ : Ψ.IsHomogeneous 4 := ThmZAux.empirical_homogeneous _
    (EmpiricalLedger.rounded_homogeneous p _ hp)
  have herr := EmpiricalFeasibility.rounded_common_error F w r μ γ p
    hF hδ hγ hp he
  rw [ThmZAux.delta_cast] at herr
  have hg := hγ
  rw [ThmZAux.gamma_cast] at hg
  have hn := norm_ledger F w r μ γ p ⟨hw, hw'⟩ ⟨hμ, hμ'⟩ hF hp he
  have hqn : SoS.coeffNorm1 (qConstraint Ψ
      (8 * ((w : ℝ) ^ 8 * (μ : ℝ) ^ 32) ^ 2)) ≤ B.scale ^ 5 := by
    rw [← ThmZAux.delta_cast]
    exact hn.2.1.trans (pow_le_pow_left₀ (by unfold sizeParameter; positivity) B.size_le 5)
  have hhn : SoS.coeffNorm1 (hConstraint Ψ
      (256 * ((w : ℝ) ^ 8 * (μ : ℝ) ^ 32) ^ 2 / (w : ℝ) ^ 2)) ≤ B.scale ^ 7 := by
    rw [← ThmZAux.delta_cast]
    exact hn.2.2.trans (pow_le_pow_left₀ (by unfold sizeParameter; positivity) B.size_le 7)
  have hcert (i : Fin m) := EmpiricalCertificate.local_certificate F w μ γ r
    B.scale I.X Ψ hF hwR hμR hg hΨ herr B.scale_four B.dimension_le B.reciprocal_le
      B.ident_le B.instance_bounds B.instance_le hqn hhn i
  choose P hP hder hnear using hcert
  obtain ⟨R, hR, hrank, hq, hh⟩ := EmpiricalFeasibility.exists_complement F w r μ γ p
    hF ⟨hw, hw'⟩ ⟨hμ, hμ'⟩ hγ hp he
  have hparams := parameters_valid (d := d) w r μ ⟨hw, hw'⟩ hr ⟨hμ, hμ'⟩
  have hpow : sizeParameter d w μ ^ 5 ≤ sizeParameter d w μ ^ 7 :=
    pow_le_pow_right₀ (by linarith only [hparams.2.2.2]) (by norm_num)
  have hcomp := EmpiricalComplement.feasible_system Ψ _ _ (sizeParameter d w μ ^ 7)
    (by unfold sizeParameter; positivity) hΨ (hn.2.1.trans hpow) hn.2.2 R hR hq hh
  have hcomp' : I.system.FeasibleComplement R I.M₂ := by
    rw [hshape.system_eq]
    exact ⟨fun f hf ↦ (hcomp.1 f hf).mono le_rfl B.complement_le,
      fun f hf ↦ (hcomp.2 f hf).mono le_rfl B.complement_le⟩
  refine ⟨List.ofFn P, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, B.certificate_one, B.complement_one,
      B.instance_one, ?_, ?_, R, hR, ?_, hcomp'⟩
    · rw [hshape.system_eq, hshape.degree_eq]
      exact empirical_system_valid Ψ _ _ hΨ
    · rw [hshape.degree_eq]; decide
    · rw [hshape.degree_eq]; norm_num
    · rw [hshape.tolerance_eq]; unfold roundTolerance; positivity
    · rw [hshape.radius_eq]; unfold radius; positivity
    · rw [hshape.radius_eq]
      exact hparams.2.1
    · rw [hshape.rank_eq]
      exact hparams.2.2.1
    · simpa only [hshape.tolerance_eq, hshape.radius_eq] using hparams.1
    · intro Q hQ
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hQ
      refine ⟨hP i, ?_⟩
      rw [hshape.system_eq, hshape.degree_eq, hshape.tolerance_eq]
      have hi := hder i
      rw [← ThmZAux.delta_cast] at hi
      obtain ⟨Ξ, hΞ, hd⟩ := hi
      refine ⟨Ξ, hΞ, ?_⟩
      have hbound : B.scale ^ 200 + 7 * (μ : ℝ) ^ 8 ≤ I.M₁ := by
        simpa only [roundTolerance, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow] using
          B.certificate_le
      simpa only [roundTolerance, Rat.cast_mul, Rat.cast_ofNat,
        Rat.cast_pow] using hd.mono hbound
    · rwa [hshape.rank_eq]
  · intro v hv hthin
    obtain ⟨i, hi⟩ := hthin
    refine ⟨P i, List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
    simpa only [hshape.tolerance_eq, roundTolerance, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow] using hnear i v hv hi

end

end ABBKS26.Centered
