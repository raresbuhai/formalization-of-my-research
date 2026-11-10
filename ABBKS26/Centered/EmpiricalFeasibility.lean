module

public import ABBKS26.Centered.ThmZAuxProof

/-! Shared analytic preparation for the rounded empirical centered system. -/

@[expose] public section

namespace ABBKS26.Centered.EmpiricalFeasibility

open Common Matrix MvPolynomial Rounding
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

theorem rounding_norm (w μ : ℚ) (hδ : delta w μ ≠ 0) (p : QPoly d)
    (hp : p.IsHomogeneous 4) :
    SoS.coeffNorm1 (SoS.toReal (roundPoly (momentPrecision d w μ) p - p)) ≤
      (delta w μ : ℝ) ^ 2 / 3 := by
  have hc := Nat.le_ceil (3 * (d + 1 : ℚ) ^ 4 / delta w μ ^ 2)
  have hb := Nat.le_pow_clog (by norm_num : 1 < 2)
    ⌈3 * (d + 1 : ℚ) ^ 4 / delta w μ ^ 2⌉₊
  change ⌈3 * (d + 1 : ℚ) ^ 4 / delta w μ ^ 2⌉₊ ≤
    2 ^ momentPrecision d w μ at hb
  have hpow : 3 * (d + 1 : ℚ) ^ 4 / delta w μ ^ 2 ≤
      (2 : ℚ) ^ momentPrecision d w μ := hc.trans (by exact_mod_cast hb)
  have he : (d + 1 : ℚ) ^ 4 / 2 ^ momentPrecision d w μ ≤ delta w μ ^ 2 / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hh := (div_le_iff₀ (sq_pos_of_ne_zero hδ)).mp hpow
    nlinarith only [hh]
  have heR : (d + 1 : ℝ) ^ 4 / 2 ^ momentPrecision d w μ ≤
      (delta w μ : ℝ) ^ 2 / 3 := by
    have hh := Rat.cast_mono (K := ℝ) he
    push_cast at hh
    exact hh
  apply (rounding_bound p _ hp).1.trans
  simpa only [_root_.zpow_neg, zpow_natCast, div_eq_mul_inv] using heR

/-- The scheduled coefficient precision spends one ninth of the fourth-power error. -/
theorem rounding_error (w μ : ℚ) (hδ : delta w μ ≠ 0) (p : QPoly d)
    (hp : p.IsHomogeneous 4) :
    IsSumSq (C ((delta w μ : ℝ) ^ 4 / 9) * nsq ^ 4 -
      SoS.toReal (roundPoly (momentPrecision d w μ) p - p) ^ 2) := by
  let E := SoS.toReal (roundPoly (momentPrecision d w μ) p - p)
  have hn := rounding_norm w μ hδ p hp
  have hs : SoS.coeffNorm1 E ^ 2 ≤ (delta w μ : ℝ) ^ 4 / 9 := by
    have hh := pow_le_pow_left₀ (SoS.coeffNorm1_nonneg E) hn 2
    nlinarith only [hh]
  have hslack := SoS.isSumSq_C_mul (sub_nonneg.mpr hs)
    (SoS.isSumSq_sq ((nsq : RPoly d) ^ 2))
  convert hslack.add (rounding_bound p (momentPrecision d w μ) hp).2 using 1
  simp only [C_sub, E]
  ring

/-- Sampling, the scheduled coefficient grid, and isotropy use exactly the common
error budget needed by the executable centered family. -/
theorem rounded_common_error (F : FrameModel k d) (w r μ : ℚ) (g : ℝ)
    (p : QPoly d) (hF : DataValid F w g r) (hδ : delta w μ ≠ 0)
    (hg : g ≤ gammaStar w μ) (hp : p.IsHomogeneous 4)
    (he : IsSumSq (C (etaStar w μ : ℝ) * nsq ^ 4 - (SoS.toReal p - phi4 F) ^ 2)) :
    IsSumSq (C ((delta w μ : ℝ) ^ 4) * nsq ^ 4 -
      ((SoS.toReal (roundPoly (momentPrecision d w μ) p) - 3 * nsq ^ 2) -
        psi F) ^ 2) := by
  let t : ℝ := delta w μ
  have hg0 := hF.2.2.1.1
  have hghi := hF.2.2.2.1
  have hg' : g ≤ t ^ 2 / 20 := by
    simpa only [gammaStar, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hg
  have hg2 : g ^ 2 ≤ t ^ 4 / 400 := by
    have hh := pow_le_pow_left₀ hg0 hg' 2
    nlinarith only [hh]
  have hplus : (2 + g) ^ 2 ≤ (21 / 10 : ℝ) ^ 2 := by
    nlinarith only [hg0, hghi]
  have hiso : 9 * g ^ 2 * (2 + g) ^ 2 ≤ t ^ 4 / 9 := by
    have hh := mul_le_mul hg2 hplus (sq_nonneg _) (by positivity : 0 ≤ t ^ 4 / 400)
    nlinarith only [hh, pow_nonneg (sq_nonneg t) 2]
  have hsecond : F.second = averageCov F := by
    simp only [FrameModel.second, hF.2.1, vecMulVec_zero, add_zero, averageCov]
  have hi := isotropy_transfer (averageCov F) g
    (IdentAux.average_symm F (fun i ↦ (hF.1.2.2.2 i).isHermitian)) hg0
    (by simpa only [hsecond] using hF.2.2.1.2.1)
    (by simpa only [hsecond] using hF.2.2.1.2.2)
  have hr := rounding_error w μ hδ p hp
  have hr' : IsSumSq (C (t ^ 4 / 9) * nsq ^ 4 -
      (SoS.toReal (roundPoly (momentPrecision d w μ) p) - SoS.toReal p) ^ 2) := by
    simpa only [SoS.toReal, map_sub] using hr
  have he' : IsSumSq (C (t ^ 4 / 9) * nsq ^ 4 - (SoS.toReal p - phi4 F) ^ 2) := by
    simpa only [etaStar, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using he
  have ht := centered_transfer F (SoS.toReal p)
    (SoS.toReal (roundPoly (momentPrecision d w μ) p)) (t ^ 4 / 9) (t ^ 4 / 9) g
      (by positivity) (by positivity) he' hr' hi
  have hslack : 0 ≤ t ^ 4 - 3 * (t ^ 4 / 9 + t ^ 4 / 9 +
      9 * g ^ 2 * (2 + g) ^ 2) := by linarith only [hiso]
  have hs := SoS.isSumSq_C_mul hslack (SoS.isSumSq_sq ((nsq : RPoly d) ^ 2))
  convert hs.add ht using 1
  simp only [C_sub, C_add, C_mul]
  ring

theorem complement_of_error (F : FrameModel k d) (w μ g r : ℝ) (Ψ : RPoly d)
    (hF : DataValid F w g r) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hμ : 0 < μ ∧ μ ≤ 1 / 64) (hg : g ≤ (w ^ 8 * μ ^ 32) ^ 2 / 20)
    (hΨ : Ψ.IsHomogeneous 4)
    (he : IsSumSq (C ((w ^ 8 * μ ^ 32) ^ 4) * nsq ^ 4 - (Ψ - psi F) ^ 2))
    (R : Mat d) (hR : Projection R)
    (hsmall : ∀ i v, sqnorm (deviation F i *ᵥ ((1 - R) *ᵥ v)) ≤
      (w ^ 8 * μ ^ 32 + g) ^ 2 * sqnorm ((1 - R) *ᵥ v)) :
    IsSumSq (subst (1 - R) (qConstraint Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2))) ∧
      IsSumSq (substV (1 - R)
        (hConstraint Ψ (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2))) := by
  obtain ⟨ht, _, _, _, _, _, _, _, _, hq, hh, _, _⟩ :=
    ThmZAux.schedule w μ g hw hμ ⟨hF.2.2.1.1, hg⟩
  have hfe := feasible F w g r (w ^ 8 * μ ^ 32)
    ((w ^ 8 * μ ^ 32 + g) ^ 2)
    (64 * (w ^ 8 * μ ^ 32 + g) ^ 4 +
      16 * (1.1 / w) ^ 2 * (w ^ 8 * μ ^ 32 + g) ^ 2)
    R hF hR ht hsmall le_rfl le_rfl
  have htr := transfer (psi F) Ψ ((w ^ 8 * μ ^ 32) ^ 4)
    ((w ^ 8 * μ ^ 32 + g) ^ 2)
    (64 * (w ^ 8 * μ ^ 32 + g) ^ 4 +
      16 * (1.1 / w) ^ 2 * (w ^ 8 * μ ^ 32 + g) ^ 2)
    (8 * (w ^ 8 * μ ^ 32) ^ 2) (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)
    (IdentAux.psi_homogeneous F) hΨ (by positivity) he
    (by simpa only [← pow_mul] using hq) hh
  constructor
  · have ha := SoS.isSumSq_map (aeval (fun i ↦ lin ((1 - R) i))) htr.1
    convert ha.add (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2) hfe.1) using 1
    simp only [map_sub, map_mul, map_ofNat, subst]
    ring
  · have ha := SoS.isSumSq_map (aeval (Sum.elim (fun i ↦ X (Sum.inl i))
      (fun i ↦ liftV (lin ((1 - R) i))))) htr.2
    convert ha.add (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2) hfe.2.1) using 1
    simp only [map_sub, map_mul, map_ofNat, substV]
    ring

/-- The rounded family has a feasible complement with the original public rank bound. -/
theorem exists_complement (F : FrameModel k d) (w r μ : ℚ) (g : ℝ)
    (p : QPoly d) (hF : DataValid F w g r) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hμ : 0 < μ ∧ μ ≤ 1 / 64) (hg : g ≤ gammaStar w μ)
    (hp : p.IsHomogeneous 4)
    (he : IsSumSq (C (etaStar w μ : ℝ) * nsq ^ 4 - (SoS.toReal p - phi4 F) ^ 2)) :
    let Ψ := SoS.toReal (roundPoly (momentPrecision d w μ) p) - 3 * nsq ^ 2
    ∃ R : Mat d, Projection R ∧ R.rank ≤ rankBound w r μ ∧
      IsSumSq (subst (1 - R) (qConstraint Ψ (8 * (delta w μ : ℝ) ^ 2))) ∧
      IsSumSq (substV (1 - R) (hConstraint Ψ (256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2))) :=
  by
  have hwR : 0 < (w : ℝ) ∧ (w : ℝ) ≤ 1 / 2 := by
    refine ⟨by exact_mod_cast hw.1, ?_⟩
    have hh := Rat.cast_mono (K := ℝ) hw.2
    norm_num at hh
    exact hh
  have hμR : 0 < (μ : ℝ) ∧ (μ : ℝ) ≤ 1 / 64 := by
    refine ⟨by exact_mod_cast hμ.1, ?_⟩
    have hh := Rat.cast_mono (K := ℝ) hμ.2
    norm_num at hh
    exact hh
  have hδ : 0 < delta w μ := by
    have hw0 := hw.1
    have hμ0 := hμ.1
    unfold delta nu
    positivity
  obtain ⟨R, hR, hrank, hsmall⟩ := rank_bound F w g r (delta w μ) hF
    (by exact_mod_cast hδ)
  have hrank' : R.rank ≤ rankBound w r μ := by
    dsimp only [rankBound]
    rw [← Int.floor_toNat, ← Rat.floor_cast (α := ℝ), Int.floor_toNat]
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow] using hrank
  let Ψ := SoS.toReal (roundPoly (momentPrecision d w μ) p) - 3 * nsq ^ 2
  have hΨ : Ψ.IsHomogeneous 4 := by
    have hrnd : (roundPoly (momentPrecision d w μ) p).IsHomogeneous 4 := by
      apply IsHomogeneous.sum
      intro α hα
      apply isHomogeneous_monomial
      rw [Finsupp.degree_eq_weight_one]
      exact hp (mem_support_iff.mp hα)
    exact ThmZAux.empirical_homogeneous _ (hrnd.map (algebraMap ℚ ℝ))
  have herr := rounded_common_error F w r μ g p hF hδ.ne' hg hp he
  rw [ThmZAux.gamma_cast] at hg
  rw [ThmZAux.delta_cast] at hsmall herr
  obtain ⟨hq, hh⟩ := complement_of_error F w μ g r Ψ hF hwR hμR hg hΨ herr R hR hsmall
  refine ⟨R, hR, hrank', ?_, ?_⟩
  · simpa only [ThmZAux.delta_cast] using hq
  · simpa only [ThmZAux.delta_cast] using hh

end

end ABBKS26.Centered.EmpiricalFeasibility
