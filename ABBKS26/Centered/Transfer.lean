module

public import ABBKS26.Centered.Poly

/-!
# Approximate moments for centered mixtures

[ABBKS26, Corollary 5.15 and Lemmas 5.16–5.18]: sum-of-squares certificates for polarization,
transfer of the constraints to the estimated moments, isotropy and rounding.
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {k d : ℕ}

private theorem square_sum_bound {σ : Type} (a b c : MvPolynomial σ ℝ) :
    IsSumSq (3 * (a ^ 2 + b ^ 2 + c ^ 2) - (a + b + c) ^ 2) := by
  convert ((SoS.isSumSq_sq (a - b)).add (SoS.isSumSq_sq (b - c))).add
    (SoS.isSumSq_sq (c - a)) using 1
  ring

private theorem fourth_sos {R : Type} [CommSemiring R] (p : R) : IsSumSq (p ^ 4) := by
  convert SoS.isSumSq_sq (p ^ 2) using 1
  ring

private theorem polarize_sub (p q : RPoly d) :
    polarize (q - p) = polarize q - polarize p := by
  simp only [polarize, liftV, liftU, map_sub]
  ring

private theorem six_square_bound {σ : Type} (a b c e : MvPolynomial σ ℝ) :
    IsSumSq (6 * (a ^ 2 + b ^ 2 + 2 * c ^ 2 + 2 * e ^ 2) -
      (a + b - 2 * c - 2 * e) ^ 2) := by
  have h := SoS.isSumSq_card_mul_sum_sq_sub (Finset.univ : Finset (Fin 6))
    ![a, b, -c, -c, -e, -e]
  norm_num [Fin.sum_univ_succ, map_ofNat] at h
  convert h using 1
  ring

private theorem norm_polarization_bound :
    IsSumSq (144 * (liftV (nsq : RPoly d) ^ 4 + liftU nsq ^ 4) -
      ((aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) nsq) ^ 4 +
        (aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) nsq) ^ 4 +
        2 * liftV nsq ^ 4 + 2 * liftU nsq ^ 4)) := by
  let A : BiPoly d := aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) nsq
  let B : BiPoly d := aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) nsq
  have hN : IsSumSq (nsq : RPoly d) := IsSumSq.sum_sq _ _
  have hA : IsSumSq A := SoS.isSumSq_map (aeval _).toRingHom hN
  have hB : IsSumSq B := SoS.isSumSq_map (aeval _).toRingHom hN
  have hpar : A + B = 2 * (liftV nsq + liftU nsq) := by
    simp only [A, B, nsq, map_sum, map_pow, aeval_X, liftV, liftU, rename_X,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcross : IsSumSq ((A + B) ^ 4 - A ^ 4 - B ^ 4) := by
    have h₁ := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 4)
      ((SoS.isSumSq_pow hA 3).mul hB)
    have h₂ := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 6)
      ((SoS.isSumSq_sq A).mul (SoS.isSumSq_sq B))
    have h₃ := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 4)
      (hA.mul (SoS.isSumSq_pow hB 3))
    convert (h₁.add h₂).add h₃ using 1
    simp only [map_ofNat]
    ring
  have hmean := SoS.isSumSq_add_pow_le (liftV (nsq : RPoly d)) (liftU nsq) 2
  norm_num [map_ofNat] at hmean
  have hbase : IsSumSq (liftV (nsq : RPoly d) ^ 4 + liftU nsq ^ 4) := by
    exact (fourth_sos _).add (fourth_sos _)
  -- The bound 130 is padded to 144 to cancel the polarization denominator.
  have ht := ((SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 16) hmean).add
    hcross).add (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 14) hbase)
  rw [hpar] at ht
  convert ht using 1
  simp only [map_ofNat]
  dsimp only [A, B]
  ring

/-- Polarization preserves a quartic SoS error bound. -/
theorem polarization_bound
    (p : RPoly d) (η : ℝ) (hp : p.IsHomogeneous 4) (hη : 0 ≤ η)
    (h : IsSumSq (C η * nsq ^ 4 - p ^ 2)) :
    IsSumSq (C (6 * η) * (liftV nsq ^ 4 + liftU nsq ^ 4) - polarize p ^ 2) := by
  -- This certificate also works without the homogeneity assumption.
  have _hp := hp
  let a : BiPoly d := aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) p
  let b : BiPoly d := aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) p
  have ha := SoS.isSumSq_map
    (aeval (fun i ↦ X (Sum.inr i) + X (Sum.inl i)) : RPoly d →ₐ[ℝ] BiPoly d) h
  have hb := SoS.isSumSq_map
    (aeval (fun i ↦ X (Sum.inr i) - X (Sum.inl i)) : RPoly d →ₐ[ℝ] BiPoly d) h
  have hv := SoS.isSumSq_map (rename (R := ℝ) (Sum.inr : Fin d → Fin d ⊕ Fin d)) h
  have hu := SoS.isSumSq_map (rename (R := ℝ) (Sum.inl : Fin d → Fin d ⊕ Fin d)) h
  simp only [map_sub, map_mul, map_pow, aeval_C, algebraMap_eq] at ha hb
  simp only [map_sub, map_mul, map_pow, rename_C] at hv hu
  have hn := SoS.isSumSq_C_mul hη (norm_polarization_bound (d := d))
  have he := ((ha.add hb).add
    (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2) hv)).add
    (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2) hu)
  have hc := six_square_bound a b (liftV p) (liftU p)
  have ht := (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 1 / 24) (hn.add he)).add
    (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 1 / 144) hc)
  have h144 : (C (1 / 144) : BiPoly d) = C (1 / 12) ^ 2 := by
    rw [← C_pow]
    norm_num
  have h24 : (C (1 / 24) : BiPoly d) = 6 * C (1 / 12) ^ 2 := by
    rw [← map_ofNat C 6, ← C_pow, ← C_mul]
    norm_num
  have hinv : (C (1 / 12) : BiPoly d) ^ 2 * 144 = 1 := by
    rw [← C_pow, ← map_ofNat C 144, ← C_mul]
    norm_num
  convert ht using 1
  simp only [a, b, polarize, liftV, liftU, C_mul, map_ofNat, h144, h24]
  linear_combination -(6 * C η *
    ((rename Sum.inr nsq) ^ 4 + (rename Sum.inl nsq) ^ 4)) * hinv

/-- Changing a quartic transfers both constraints with explicit tolerances. -/
theorem transfer
    (p q : RPoly d) (η εq εh εq' εh' : ℝ)
    (hp : p.IsHomogeneous 4) (hq : q.IsHomogeneous 4) (hη : 0 ≤ η)
    (he : IsSumSq (C η * nsq ^ 4 - (q - p) ^ 2))
    (hεq : 2 * εq ^ 2 + 2 / 9 * η ≤ εq' ^ 2)
    (hεh : 2 * εh + 192 * η ≤ εh') :
    IsSumSq (qConstraint q εq' - 2 * qConstraint p εq) ∧
      IsSumSq (hConstraint q εh' - 2 * hConstraint p εh) := by
  have hN : IsSumSq ((nsq : RPoly d) ^ 4) := fourth_sos _
  have hB : IsSumSq (liftV (nsq : RPoly d) ^ 4 + liftU nsq ^ 4) := by
    exact (fourth_sos _).add (fourth_sos _)
  have hpol := polarization_bound (q - p) η (hq.sub hp) hη he
  rw [polarize_sub] at hpol
  constructor
  · have hslack := SoS.isSumSq_C_mul (sub_nonneg.mpr hεq) hN
    have herr := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2 / 9) he
    have hsquare := SoS.isSumSq_sq (C (1 / 3) * (2 * p - q))
    convert (hslack.add herr).add hsquare using 1
    simp only [qConstraint, C_sub, C_add, C_mul, C_pow, map_ofNat]
    have heq : (C (2 / 9) : RPoly d) = 2 * C (1 / 3) ^ 2 := by
      rw [← map_ofNat C 2, ← C_pow, ← C_mul]
      norm_num
    rw [heq]
    ring
  · have hslack := SoS.isSumSq_C_mul (sub_nonneg.mpr hεh) hB
    have herr := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 32) hpol
    have hsquare := SoS.isSumSq_sq (4 * (2 * polarize p - polarize q))
    convert (hslack.add herr).add hsquare using 1
    simp only [hConstraint, C_sub, C_add, C_mul, map_ofNat]
    ring

/-- Approximate isotropy bounds the Gaussian reference quartic in SoS. -/
theorem isotropy_transfer
    (S : Mat d) (γ : ℝ) (hs : Sᵀ = S) (hγ : 0 ≤ γ)
    (hlo : LE ((1 - γ) • (1 : Mat d)) S)
    (hhi : LE S ((1 + γ) • (1 : Mat d))) :
    IsSumSq (C (9 * γ ^ 2 * (2 + γ) ^ 2) * nsq ^ 4 -
      (3 * quad S ^ 2 - 3 * nsq ^ 2) ^ 2) := by
  have hnorm (v : Vec d) : 0 ≤ sqnorm v :=
    Rounding.DetRoundAux.sqnorm_nonneg v
  have hlo' (v : Vec d) : (1 - γ) * sqnorm v ≤ qform S v := by
    simpa only [qform, sqnorm, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      using hlo v
  have hhi' (v : Vec d) : qform S v ≤ (1 + γ) * sqnorm v := by
    simpa only [qform, sqnorm, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
      using hhi v
  have hminus := SoSKit.quad_square (S - 1) (by simp [hs]) γ hγ (fun v ↦ by
    rw [show qform (S - 1) v = qform S v - sqnorm v by
      simp [qform, sqnorm, sub_mulVec, dotProduct_sub]]
    exact abs_le.mpr ⟨by nlinarith [hlo' v], by nlinarith [hhi' v]⟩)
  have hplus := SoSKit.quad_square (S + 1) (by simp [hs]) (2 + γ) (by linarith)
    (fun v ↦ by
      rw [show qform (S + 1) v = qform S v + sqnorm v by
        simp [qform, sqnorm, add_mulVec, dotProduct_add]]
      exact abs_le.mpr ⟨by nlinarith [hlo' v, hnorm v], by nlinarith [hhi' v]⟩)
  have hI : quad (1 : Mat d) = nsq := by
    simp [quad, nsq, Matrix.one_apply, pow_two, apply_ite, ite_mul]
  have hsub : quad (S - 1) = quad S - nsq := by
    rw [← hI]
    simp [quad, C_sub, sub_mul, Finset.sum_sub_distrib]
  have hadd : quad (S + 1) = quad S + nsq := by
    rw [← hI]
    simp [quad, C_add, add_mul, Finset.sum_add_distrib]
  rw [hsub] at hminus
  rw [hadd] at hplus
  have ht := SoSKit.prod (C (γ ^ 2) * nsq ^ 2) (C ((2 + γ) ^ 2) * nsq ^ 2)
    ((quad S - nsq) ^ 2) ((quad S + nsq) ^ 2)
    (SoS.isSumSq_C_mul (sq_nonneg _) (SoS.isSumSq_sq nsq))
    (SoS.isSumSq_sq _) hminus hplus
  convert SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 9) ht using 1
  simp only [C_mul, C_pow, map_ofNat]
  ring

private theorem roundRat_error (prec : ℕ) (q : ℚ) :
    |(roundRat prec q : ℝ) - q| ≤ (2 : ℝ) ^ (-(prec : ℤ)) := by
  have hpow : (0 : ℝ) < 2 ^ prec := by positivity
  have hlo : (⌊(2 : ℚ) ^ prec * q⌋ : ℝ) ≤ (2 : ℝ) ^ prec * (q : ℝ) := by
    exact_mod_cast Int.floor_le ((2 : ℚ) ^ prec * q)
  have hhi : (2 : ℝ) ^ prec * (q : ℝ) < (⌊(2 : ℚ) ^ prec * q⌋ : ℝ) + 1 := by
    exact_mod_cast Int.lt_floor_add_one ((2 : ℚ) ^ prec * q)
  have he : (⌊(2 : ℚ) ^ prec * q⌋ : ℝ) / 2 ^ prec - q =
      ((⌊(2 : ℚ) ^ prec * q⌋ : ℝ) - 2 ^ prec * q) / 2 ^ prec := by
    field_simp
  simp only [roundRat, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat,
    _root_.zpow_neg, zpow_natCast]
  rw [he, abs_div, abs_of_pos hpow, ← one_div]
  apply (div_le_div_iff_of_pos_right hpow).mpr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem roundPoly_coeff (p : QPoly d) (prec : ℕ) (α : Fin d →₀ ℕ) :
    (roundPoly prec p).coeff α = roundRat prec (p.coeff α) := by
  classical
  simp only [roundPoly, coeff_sum, coeff_monomial]
  by_cases hα : α ∈ p.support
  · simp [hα]
  · simp [hα, notMem_support_iff.mp hα, roundRat]

private theorem roundPoly_homogeneous (p : QPoly d) (prec r : ℕ)
    (hp : p.IsHomogeneous r) : (roundPoly prec p).IsHomogeneous r := by
  classical
  apply IsHomogeneous.sum
  intro α hα
  apply isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.mp hα)

/-- Rounding a homogeneous quartic controls its coefficient and SoS error. -/
theorem rounding_bound
    (p : QPoly d) (prec : ℕ) (hp : p.IsHomogeneous 4) :
    SoS.coeffNorm1 (SoS.toReal (roundPoly prec p - p)) ≤
      (d + 1 : ℝ) ^ 4 * (2 : ℝ) ^ (-(prec : ℤ)) ∧
    IsSumSq (C (SoS.coeffNorm1 (SoS.toReal (roundPoly prec p - p)) ^ 2) *
      nsq ^ 4 - SoS.toReal (roundPoly prec p - p) ^ 2) := by
  have hhom : (SoS.toReal (roundPoly prec p - p)).IsHomogeneous 4 :=
    ((roundPoly_homogeneous p prec 4 hp).sub hp).map (algebraMap ℚ ℝ)
  refine ⟨?_, SoSKit.l1_square _ 4 hhom⟩
  have hc (α : Fin d →₀ ℕ) :
      |(SoS.toReal (roundPoly prec p - p)).coeff α| ≤ (2 : ℝ) ^ (-(prec : ℤ)) := by
    simpa [SoS.toReal, coeff_map, roundPoly_coeff]
      using roundRat_error prec (p.coeff α)
  have hcard : ((SoS.toReal (roundPoly prec p - p)).support.card : ℝ) ≤
      (d + 1 : ℝ) ^ 4 := by
    have hs := SoS.card_support_le (SoS.toReal (roundPoly prec p - p))
    rw [Fintype.card_fin] at hs
    have ht := hs.trans (Nat.pow_le_pow_right (Nat.succ_pos d) hhom.totalDegree_le)
    exact_mod_cast ht
  exact (SoS.coeffNorm1_le hc).trans
    (mul_le_mul_of_nonneg_right hcard (by positivity))

/-- Sampling, isotropy and coefficient rounding combine into one certificate. -/
theorem centered_transfer
    (F : FrameModel k d) (p p' : RPoly d) (η ηrnd γ : ℝ)
    (hη : 0 ≤ η) (hrnd : 0 ≤ ηrnd)
    (hp : IsSumSq (C η * nsq ^ 4 - (p - phi4 F) ^ 2))
    (hr : IsSumSq (C ηrnd * nsq ^ 4 - (p' - p) ^ 2))
    (hi : IsSumSq (C (9 * γ ^ 2 * (2 + γ) ^ 2) * nsq ^ 4 -
      (3 * quad (averageCov F) ^ 2 - 3 * nsq ^ 2) ^ 2)) :
    IsSumSq (C (3 * (ηrnd + η + 9 * γ ^ 2 * (2 + γ) ^ 2)) * nsq ^ 4 -
      ((p' - 3 * nsq ^ 2) - psi F) ^ 2) := by
  -- The three input certificates suffice for this algebraic combination.
  have _hη := hη
  have _hrnd := hrnd
  have ht := square_sum_bound (p' - p) (p - phi4 F)
    (3 * quad (averageCov F) ^ 2 - 3 * nsq ^ 2)
  have he := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 3) ((hr.add hp).add hi)
  convert he.add ht using 1
  simp only [psi, C_mul, C_add, map_ofNat]
  ring

end

end ABBKS26.Centered
