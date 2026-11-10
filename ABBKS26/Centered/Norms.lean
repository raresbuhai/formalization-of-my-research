module

public import ABBKS26.Centered.Params
public import ABBKS26.Centered.Transfer
public import ABBKS26.Rounding.Raw

/-!
# Centered norm ledger and rounded moment precision

Parameter side conditions and coefficient norm bounds for the rounded centered system.
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {k d : ℕ}

def momentPrecision (d : ℕ) (w μ : ℚ) : ℕ :=
  Nat.clog 2 ⌈3 * (d + 1 : ℚ) ^ 4 / delta w μ ^ 2⌉₊

def sizeParameter (d : ℕ) (w μ : ℚ) : ℝ :=
  64 * (d + 1 : ℝ) ^ 2 * 2 ^ momentPrecision d w μ * (⌈1 / (w * μ)⌉₊ : ℝ) ^ 40

private theorem delta_bounds (w μ : ℚ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hμ : 0 < μ ∧ μ ≤ 1 / 64) : 0 < delta w μ ∧ delta w μ ≤ 1 := by
  have hn : 0 < nu w μ := mul_pos hw.1 (pow_pos hμ.1 _)
  have hn' : nu w μ ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left
      (pow_le_one₀ hμ.1.le (by linarith [hμ.2])) hw.1.le).trans
        (by nlinarith [hw.2])
  exact ⟨pow_pos hn _, pow_le_one₀ hn.le hn'⟩

private theorem size_lower (w μ : ℚ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hμ : 0 < μ ∧ μ ≤ 1 / 64) :
    let A : ℝ := ⌈1 / (w * μ)⌉₊
    1 ≤ A ∧ 1 / (w : ℝ) ≤ A ∧
      64 * ((d + 1 : ℝ) ^ 2 * A) ≤ sizeParameter d w μ := by
  let A : ℝ := ⌈1 / (w * μ)⌉₊
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hμ' : (0 : ℝ) < μ := by exact_mod_cast hμ.1
  have hμ1 : (μ : ℝ) ≤ 1 := by exact_mod_cast (show μ ≤ 1 by linarith [hμ.2])
  have hA : 1 / ((w : ℝ) * μ) ≤ A := by
    dsimp only [A]
    exact_mod_cast Nat.le_ceil (1 / (w * μ))
  have hwA : 1 / (w : ℝ) ≤ A := by
    exact (one_div_le_one_div_of_le (mul_pos hw' hμ')
      (mul_le_of_le_one_right hw'.le hμ1)).trans hA
  have hA1 : 1 ≤ A := by
    have hw1 : (w : ℝ) ≤ 1 := by exact_mod_cast (show w ≤ 1 by linarith [hw.2])
    exact (one_le_div hw').mpr hw1 |>.trans hwA
  have hp : (1 : ℝ) ≤ 2 ^ momentPrecision d w μ := one_le_pow₀ (by norm_num)
  have hAp : A ≤ A ^ 40 := le_self_pow₀ hA1 (by norm_num)
  refine ⟨hA1, hwA, ?_⟩
  dsimp only [sizeParameter]
  calc
    64 * ((d + 1 : ℝ) ^ 2 * A) = 64 * (d + 1 : ℝ) ^ 2 * 1 * A := by ring
    _ ≤ 64 * (d + 1 : ℝ) ^ 2 * 2 ^ momentPrecision d w μ * A ^ 40 := by
      gcongr

/-- The centered schedule has the exact RC2 tolerance and rank side conditions. -/
theorem parameters_valid
    (w rF μ : ℚ) (hw : 0 < w ∧ w ≤ 1 / 2) (hr : 1 ≤ rF)
    (hμ : 0 < μ ∧ μ ≤ 1 / 64) :
    25 * (roundTolerance μ : ℝ) ^ (1 / 8 : ℝ) ≤ radius μ ∧
    radius μ ≤ 1 / 2 ∧ 1 ≤ rankBound w rF μ ∧ 2 ≤ sizeParameter d w μ := by
  have hd := delta_bounds w μ hw hμ
  have hs := size_lower (d := d) w μ hw hμ
  have hm : (0 : ℝ) ≤ μ := by exact_mod_cast hμ.1.le
  have hroot : (7 : ℝ) ^ (1 / 8 : ℝ) ≤ 32 / 25 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos (by norm_num) (by norm_num)
      (by norm_num)]
    norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [roundTolerance, radius, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
    have hpow : ((μ : ℝ) ^ 8) ^ (1 / 8 : ℝ) = μ := by
      simpa using Real.pow_rpow_inv_natCast hm (by norm_num : (8 : ℕ) ≠ 0)
    rw [Real.mul_rpow (by norm_num) (by positivity), hpow]
    nlinarith [mul_le_mul_of_nonneg_right hroot hm]
  · exact_mod_cast (show radius μ ≤ 1 / 2 by dsimp [radius]; linarith [hμ.2])
  · rw [rankBound, Nat.one_le_floor_iff]
    apply (one_le_div (mul_pos hw.1 (pow_pos hd.1 _))).mpr
    have ht := mul_le_mul_of_nonneg_left (pow_le_one₀ hd.1.le hd.2 (n := 2)) hw.1.le
    exact (ht.trans (by linarith [hw.2])).trans hr
  · have hD : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 :=
      one_le_pow₀ (by linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d])
    have hB : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 * (⌈1 / (w * μ)⌉₊ : ℝ) :=
      one_le_mul_of_one_le_of_one_le hD hs.1
    linarith [hs.2.2]

private theorem norm_nat_mul {σ : Type} (n : ℕ) (p : MvPolynomial σ ℝ) :
    SoS.coeffNorm1 ((n : MvPolynomial σ ℝ) * p) = n * SoS.coeffNorm1 p := by
  rw [← map_natCast C n, SoS.coeffNorm1_C_mul, abs_of_nonneg (Nat.cast_nonneg n)]

private theorem norm_nsq : SoS.coeffNorm1 (nsq : RPoly d) ≤ d := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    ∑ i : Fin d, SoS.coeffNorm1 (X i ^ 2 : RPoly d) ≤ ∑ _i : Fin d, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ ↦
        (SoS.coeffNorm1_pow_le (X i : RPoly d) 2).trans_eq (by
          rw [SoS.coeffNorm1_X, one_pow])
    _ = d := by simp

private theorem norm_rename {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ ℝ) :
    SoS.coeffNorm1 (rename f p) ≤ SoS.coeffNorm1 p := by
  rw [rename_eq_aeval]
  simpa using SoS.coeffNorm1_aeval_le (X ∘ f) (β := 1) le_rfl
    (fun i ↦ (SoS.coeffNorm1_X (f i)).le) p

private theorem norm_polarize (p : RPoly d) (hp : p.totalDegree ≤ 4) :
    SoS.coeffNorm1 (polarize p) ≤ 3 * SoS.coeffNorm1 p := by
  have ha : SoS.coeffNorm1
      (aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) p) ≤ 16 * SoS.coeffNorm1 p := by
    refine (SoS.coeffNorm1_aeval_le _ (by norm_num : (1 : ℝ) ≤ 2) (fun i ↦ ?_) p).trans ?_
    · exact (SoS.coeffNorm1_add_le _ _).trans_eq (by
        rw [SoS.coeffNorm1_X, SoS.coeffNorm1_X]
        norm_num)
    · calc
        SoS.coeffNorm1 p * 2 ^ p.totalDegree ≤ SoS.coeffNorm1 p * 2 ^ 4 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hp)
            (SoS.coeffNorm1_nonneg p)
        _ = 16 * SoS.coeffNorm1 p := by ring
  have hb : SoS.coeffNorm1
      (aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) p) ≤ 16 * SoS.coeffNorm1 p := by
    refine (SoS.coeffNorm1_aeval_le _ (by norm_num : (1 : ℝ) ≤ 2) (fun i ↦ ?_) p).trans ?_
    · exact (SoS.coeffNorm1_sub_le _ _).trans_eq (by
        rw [SoS.coeffNorm1_X, SoS.coeffNorm1_X]
        norm_num)
    · calc
        SoS.coeffNorm1 p * 2 ^ p.totalDegree ≤ SoS.coeffNorm1 p * 2 ^ 4 := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hp)
            (SoS.coeffNorm1_nonneg p)
        _ = 16 * SoS.coeffNorm1 p := by ring
  have hv : SoS.coeffNorm1 (2 * liftV p) ≤ 2 * SoS.coeffNorm1 p := by
    have h := norm_nat_mul 2 (liftV p)
    norm_num only [Nat.cast_ofNat] at h
    rw [h]
    exact mul_le_mul_of_nonneg_left (norm_rename Sum.inr p) (by norm_num)
  have hu : SoS.coeffNorm1 (2 * liftU p) ≤ 2 * SoS.coeffNorm1 p := by
    have h := norm_nat_mul 2 (liftU p)
    norm_num only [Nat.cast_ofNat] at h
    rw [h]
    exact mul_le_mul_of_nonneg_left (norm_rename Sum.inl p) (by norm_num)
  unfold polarize
  rw [SoS.coeffNorm1_C_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 12)]
  have h₁ := SoS.coeffNorm1_add_le
    (aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) p)
    (aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) p)
  have h₂ := SoS.coeffNorm1_sub_le
    (aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) p +
      aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) p) (2 * liftV p)
  have h₃ := SoS.coeffNorm1_sub_le
    (aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) p +
      aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) p - 2 * liftV p) (2 * liftU p)
  linarith

private theorem rounded_homogeneous (p : QPoly d) (prec : ℕ)
    (hp : p.IsHomogeneous 4) : (SoS.toReal (roundPoly prec p)).IsHomogeneous 4 := by
  apply IsHomogeneous.map
  apply IsHomogeneous.sum
  intro α hα
  apply isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.mp hα)

private theorem nsq_homogeneous : (nsq : RPoly d).IsHomogeneous 2 := by
  apply IsHomogeneous.sum
  intro i _
  simpa using (isHomogeneous_X ℝ i).pow 2

private theorem norm_nsq_pow (r : ℕ) :
    SoS.coeffNorm1 ((nsq : RPoly d) ^ r) ≤ (d : ℝ) ^ r :=
  (SoS.coeffNorm1_pow_le _ _).trans
    (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) norm_nsq r)

private theorem norm_qConstraint (p : RPoly d) (ε : ℝ) :
    SoS.coeffNorm1 (qConstraint p ε) ≤ ε ^ 2 * (d : ℝ) ^ 4 +
      SoS.coeffNorm1 p ^ 2 / 9 := by
  have hn := norm_nsq_pow (d := d) 4
  have hp := SoS.coeffNorm1_pow_le (C (1 / 3) * p) 2
  rw [SoS.coeffNorm1_C_mul] at hp
  norm_num at hp
  have he := SoS.coeffNorm1_sub_le (C (ε ^ 2) * nsq ^ 4) ((C (1 / 3) * p) ^ 2)
  rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (sq_nonneg ε)] at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg ε)])

private theorem norm_hConstraint (p : RPoly d) (hp : p.totalDegree ≤ 4) (ε : ℝ) :
    SoS.coeffNorm1 (hConstraint p ε) ≤ |ε| * (2 * (d : ℝ) ^ 4) +
      144 * SoS.coeffNorm1 p ^ 2 := by
  have hn : SoS.coeffNorm1 (liftV (nsq : RPoly d) ^ 4 + liftU nsq ^ 4) ≤
      2 * (d : ℝ) ^ 4 := by
    have hv : SoS.coeffNorm1 (liftV (nsq : RPoly d) ^ 4) ≤ (d : ℝ) ^ 4 := by
      rw [liftV, ← map_pow]
      exact (norm_rename _ _).trans (norm_nsq_pow 4)
    have hu : SoS.coeffNorm1 (liftU (nsq : RPoly d) ^ 4) ≤ (d : ℝ) ^ 4 := by
      rw [liftU, ← map_pow]
      exact (norm_rename _ _).trans (norm_nsq_pow 4)
    exact (SoS.coeffNorm1_add_le _ _).trans (by linarith)
  have hpol := norm_polarize p hp
  have hsq := SoS.coeffNorm1_pow_le (4 * polarize p) 2
  have hfour := norm_nat_mul 4 (polarize p)
  norm_num only [Nat.cast_ofNat] at hfour
  rw [hfour] at hsq
  have hsq' : SoS.coeffNorm1 ((4 * polarize p) ^ 2) ≤
      144 * SoS.coeffNorm1 p ^ 2 := by
    have hnpol := SoS.coeffNorm1_nonneg (polarize p)
    calc
      _ ≤ (4 * SoS.coeffNorm1 (polarize p)) ^ 2 := hsq
      _ ≤ (4 * (3 * SoS.coeffNorm1 p)) ^ 2 := by gcongr
      _ = _ := by ring
  have he := SoS.coeffNorm1_sub_le
    (C ε * (liftV (nsq : RPoly d) ^ 4 + liftU nsq ^ 4)) ((4 * polarize p) ^ 2)
  rw [SoS.coeffNorm1_C_mul] at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (abs_nonneg ε)])

/-- The rounded centered system and its single instances have controlled coefficient norms. -/
theorem norm_ledger
    (F : FrameModel k d) (w rF μ : ℚ) (γ : ℝ) (p : QPoly d)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hμ : 0 < μ ∧ μ ≤ 1 / 64)
    (hF : DataValid F w γ rF) (hp : p.IsHomogeneous 4)
    (he : IsSumSq (C (etaStar w μ : ℝ) * nsq ^ 4 - (SoS.toReal p - phi4 F) ^ 2)) :
    let W := sizeParameter d w μ
    let Ψ := SoS.toReal (roundPoly (momentPrecision d w μ) p) - 3 * nsq ^ 2
    SoS.coeffNorm1 Ψ ≤ W ^ 2 ∧
    SoS.coeffNorm1 (qConstraint Ψ (8 * (delta w μ : ℝ) ^ 2)) ≤ W ^ 5 ∧
    SoS.coeffNorm1 (hConstraint Ψ (256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2)) ≤ W ^ 7 := by
  let A : ℝ := ⌈1 / (w * μ)⌉₊
  let B : ℝ := (d + 1 : ℝ) ^ 2 * A
  let W := sizeParameter d w μ
  let Ψ := SoS.toReal (roundPoly (momentPrecision d w μ) p) - 3 * nsq ^ 2
  change SoS.coeffNorm1 Ψ ≤ W ^ 2 ∧
    SoS.coeffNorm1 (qConstraint Ψ (8 * (delta w μ : ℝ) ^ 2)) ≤ W ^ 5 ∧
    SoS.coeffNorm1 (hConstraint Ψ (256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2)) ≤ W ^ 7
  obtain ⟨hA, hwA, hW⟩ := size_lower (d := d) w μ hw hμ
  change 1 ≤ A at hA
  change 1 / (w : ℝ) ≤ A at hwA
  change 64 * B ≤ W at hW
  have hwpos : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwle : (w : ℝ) ≤ 1 / 2 := by
    have ht := Rat.cast_mono (K := ℝ) hw.2
    norm_num at ht
    exact ht
  have hD : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 :=
    one_le_pow₀ (by linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d])
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hD hA
  have hW64 : 64 ≤ W := by linarith only [hW, hB]
  have hW0 : 0 ≤ W := by linarith only [hW64]
  -- This scale absorbs both the coefficient bound and the constraint tolerance terms.
  have hscale : 512 * B ^ 2 ≤ W ^ 2 := by
    have ht := pow_le_pow_left₀ (by positivity : 0 ≤ 64 * B) hW 2
    nlinarith only [ht, sq_nonneg B]
  have hD4 : (d + 1 : ℝ) ^ 4 ≤ B ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left (one_le_pow₀ hA (n := 2))
      (by positivity : 0 ≤ (d + 1 : ℝ) ^ 4)
    dsimp only [B]
    nlinarith only [ht]
  have hd2 : (d : ℝ) ^ 2 ≤ B := by
    have ht : (d : ℝ) ^ 2 ≤ (d + 1 : ℝ) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
    exact ht.trans (le_mul_of_one_le_right (by positivity) hA)
  have hd4 : (d : ℝ) ^ 4 ≤ B ^ 2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg (d : ℝ)) hd2 2
  have hinv : 1 / (w : ℝ) ^ 2 ≤ A ^ 2 := by
    simpa only [div_pow, one_pow] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (w : ℝ)) hwA 2
  obtain ⟨hδpos, hδle⟩ := delta_bounds w μ hw hμ
  have hδ : (delta w μ : ℝ) ^ 2 ≤ 1 := by
    exact_mod_cast pow_le_one₀ hδpos.le hδle (n := 2)
  have hη : 0 ≤ (etaStar w μ : ℝ) ∧ (etaStar w μ : ℝ) ≤ 1 := by
    have ht := pow_le_one₀ hδpos.le hδle (n := 4)
    exact_mod_cast (show 0 ≤ etaStar w μ ∧ etaStar w μ ≤ 1 by
      dsimp only [etaStar]
      constructor
      · positivity
      · linarith)
  have hpR : (SoS.toReal p).IsHomogeneous 4 := hp.map (algebraMap ℚ ℝ)
  have hc := coefficient_bound F w γ rF (etaStar w μ) (SoS.toReal p) hF
    hwle hη hpR he
  have hcard : ((SoS.toReal p).support.card : ℝ) ≤ (d + 1 : ℝ) ^ 4 := by
    have ht := SoS.card_support_le (SoS.toReal p)
    rw [Fintype.card_fin] at ht
    exact_mod_cast ht.trans (Nat.pow_le_pow_right (Nat.succ_pos d) hpR.totalDegree_le)
  have hpB : SoS.coeffNorm1 (SoS.toReal p) ≤ 20 * B ^ 2 := by
    calc
      _ ≤ ((SoS.toReal p).support.card : ℝ) * (20 / (w : ℝ) ^ 2) :=
        SoS.coeffNorm1_le hc
      _ ≤ (d + 1 : ℝ) ^ 4 * (20 * A ^ 2) := by
        apply mul_le_mul hcard
          (by simpa only [mul_one_div] using
            mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 20))
          (by positivity) (by positivity)
      _ = 20 * B ^ 2 := by dsimp only [B]; ring
  have hrnd : SoS.coeffNorm1
      (SoS.toReal (roundPoly (momentPrecision d w μ) p - p)) ≤ B ^ 2 := by
    have ht : (2 : ℝ) ^ (-(momentPrecision d w μ : ℤ)) ≤ 1 := by
      rw [_root_.zpow_neg, zpow_natCast]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact (rounding_bound p (momentPrecision d w μ) hp).1.trans
      ((mul_le_of_le_one_right (by positivity) ht).trans hD4)
  have href : SoS.coeffNorm1 (3 * (nsq : RPoly d) ^ 2) ≤ 3 * B ^ 2 := by
    have ht := norm_nat_mul 3 ((nsq : RPoly d) ^ 2)
    norm_num only [Nat.cast_ofNat] at ht
    rw [ht]
    exact mul_le_mul_of_nonneg_left ((norm_nsq_pow 2).trans
      (hd2.trans (le_self_pow₀ hB (by norm_num)))) (by norm_num)
  have hΨ : SoS.coeffNorm1 Ψ ≤ W ^ 2 := by
    have ht : SoS.toReal (roundPoly (momentPrecision d w μ) p) =
        SoS.toReal (roundPoly (momentPrecision d w μ) p - p) + SoS.toReal p := by
      simp [SoS.toReal, map_sub]
    have ha := SoS.coeffNorm1_add_le
      (SoS.toReal (roundPoly (momentPrecision d w μ) p - p)) (SoS.toReal p)
    have hs := SoS.coeffNorm1_sub_le
      (SoS.toReal (roundPoly (momentPrecision d w μ) p)) (3 * nsq ^ 2)
    rw [← ht] at ha
    change SoS.coeffNorm1 Ψ ≤ _ at hs
    linarith only [hs, ha, hrnd, hpB, href, hscale, sq_nonneg B]
  have hΨdeg : Ψ.totalDegree ≤ 4 := by
    have hn : ((nsq : RPoly d) ^ 2).IsHomogeneous 4 := by
      simpa using (nsq_homogeneous (d := d)).pow 2
    have hn3 : (3 * (nsq : RPoly d) ^ 2).IsHomogeneous 4 := by
      convert (hn.add hn).add hn using 1
      ring
    apply IsHomogeneous.totalDegree_le
    exact (rounded_homogeneous p _ hp).sub hn3
  refine ⟨hΨ, ?_, ?_⟩
  · have hε : (8 * (delta w μ : ℝ) ^ 2) ^ 2 ≤ 64 := by
      nlinarith only [hδ, sq_nonneg ((delta w μ : ℝ) ^ 2),
        mul_nonneg (sq_nonneg (delta w μ : ℝ)) (sub_nonneg.mpr hδ)]
    have hq := norm_qConstraint Ψ (8 * (delta w μ : ℝ) ^ 2)
    have hfirst : (8 * (delta w μ : ℝ) ^ 2) ^ 2 * (d : ℝ) ^ 4 ≤ W ^ 2 := by
      have ht := mul_le_mul hε hd4 (by positivity) (by norm_num : (0 : ℝ) ≤ 64)
      linarith only [ht, hscale, sq_nonneg B]
    have hsecond : SoS.coeffNorm1 Ψ ^ 2 ≤ W ^ 4 := by
      simpa only [← pow_mul] using
        pow_le_pow_left₀ (SoS.coeffNorm1_nonneg Ψ) hΨ 2
    have hgrow : W ^ 2 + W ^ 4 ≤ W ^ 5 := by
      have h24 : W ^ 2 ≤ W ^ 4 :=
        pow_le_pow_right₀ (by linarith only [hW64]) (by norm_num)
      nlinarith only [h24, mul_nonneg (by linarith only [hW64] : 0 ≤ W - 2)
        (pow_nonneg hW0 4)]
    linarith only [hq, hfirst, hsecond, hgrow, pow_nonneg hW0 4]
  · have hε : |256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2| ≤ 256 * A ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      calc
        _ ≤ 256 / (w : ℝ) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg _)
          linarith only [hδ]
        _ ≤ 256 * A ^ 2 := by
          simpa only [mul_one_div] using
            mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 256)
    have hh := norm_hConstraint Ψ hΨdeg
      (256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2)
    have hfirst : |256 * (delta w μ : ℝ) ^ 2 / (w : ℝ) ^ 2| *
        (2 * (d : ℝ) ^ 4) ≤ W ^ 2 := by
      calc
        _ ≤ (256 * A ^ 2) * (2 * (d + 1 : ℝ) ^ 4) := by
          gcongr
          linarith
        _ = 512 * B ^ 2 := by dsimp only [B]; ring
        _ ≤ W ^ 2 := hscale
    have hsecond : SoS.coeffNorm1 Ψ ^ 2 ≤ W ^ 4 := by
      simpa only [← pow_mul] using
        pow_le_pow_left₀ (SoS.coeffNorm1_nonneg Ψ) hΨ 2
    have hgrow : W ^ 2 + 144 * W ^ 4 ≤ W ^ 7 := by
      have h24 : W ^ 2 ≤ W ^ 4 :=
        pow_le_pow_right₀ (by linarith only [hW64]) (by norm_num)
      have hcube : 145 ≤ W ^ 3 := by
        have ht := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hW64 3
        norm_num at ht
        linarith only [ht]
      nlinarith only [h24, mul_nonneg (by linarith only [hcube] : 0 ≤ W ^ 3 - 145)
        (pow_nonneg hW0 4)]
    linarith only [hh, hfirst, hsecond, hgrow]

end

end ABBKS26.Centered
