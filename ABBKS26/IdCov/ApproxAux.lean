module

public import ABBKS26.IdCov.Ident
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Quadratic and rounding facts for approximate moment transfer. -/

@[expose] public section

namespace ABBKS26.IdCov.ApproxAux

noncomputable section

open Common MvPolynomial Matrix Finset
open scoped BigOperators

variable {d : ℕ}

theorem nsq_homogeneous : (nsq : RPoly d).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow i 2

theorem eval_nsq (v : Vec d) : eval v (nsq : RPoly d) = sqnorm v := by
  simp [nsq, sqnorm, dotProduct, pow_two]

theorem eval_quad (A : Mat d) (v : Vec d) : eval v (quad A) = qform A v := by
  simp only [quad, qform, Matrix.mulVec, dotProduct, map_sum, map_mul, eval_C,
    eval_X, mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

theorem quadratic_representation (p : RPoly d) (hp : p.IsHomogeneous 2) :
    ∃ A : Mat d, A.IsHermitian ∧ quad A = p := by
  let A : Mat d := fun i j ↦ constantCoeff (pderiv j (pderiv i p)) / 2
  have he (i j : Fin d) :
      pderiv j (pderiv i p) = C (constantCoeff (pderiv j (pderiv i p))) := by
    exact (totalDegree_eq_zero_iff_eq_C.mp
      (Nat.eq_zero_of_le_zero hp.pderiv.pderiv.totalDegree_le))
  refine ⟨A, ?_, ?_⟩
  · change Aᴴ = A
    ext i j
    change constantCoeff (pderiv i (pderiv j p)) / 2 =
      constantCoeff (pderiv j (pderiv i p)) / 2
    rw [pderiv_comm]
  · have hfirst := hp.sum_X_mul_pderiv
    have hsecond (i : Fin d) := hp.pderiv (i := i) |>.sum_X_mul_pderiv
    have hs : quad A = C (1 / 2 : ℝ) * (∑ i, X i * pderiv i p) := by
      simp only [quad, A, mul_sum]
      refine sum_congr rfl fun i _ ↦ ?_
      conv_rhs => rw [show pderiv i p = ∑ j, X j * pderiv j (pderiv i p) by
        simpa using (hsecond i).symm]
      simp only [mul_sum]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [he i j]
      simp only [div_eq_mul_inv, map_mul, constantCoeff_C, one_mul]
      ring
    rw [hs, hfirst, two_nsmul, mul_add, ← add_mul, ← map_add]
    norm_num

theorem quadratic_sos (p : RPoly d) (hp : p.IsHomogeneous 2)
    (hn : ∀ v, 0 ≤ eval v p) : IsSumSq p := by
  obtain ⟨A, hA, rfl⟩ := quadratic_representation p hp
  apply SoSKit.psd_quad
  refine PosSemidef.of_dotProduct_mulVec_nonneg hA fun v ↦ ?_
  simpa only [star_trivial, eval_quad, qform] using hn v

theorem eval_second {k : ℕ} (D : Data k d) (hs : ∑ i, D.weight i = 1)
    (v : Vec d) : eval v (moment D 2) = qform D.frame.second v := by
  have he : D.frame.second = D.cov + between D := by
    simp only [FrameModel.second, Data.frame, smul_add, sum_add_distrib,
      ← sum_smul, hs, one_smul, between]
  rw [he, second_moment D hs, map_add, Q, S, eval_quad, eval_quad]
  simp only [qform, add_mulVec, dotProduct_add]
  ring

theorem error_constant_bound {t s : ℕ} (hs : 2 ≤ s ∧ s ≤ 2 * t) :
    2 + 2 * alpha s ^ 2 * (s : ℝ) ^ 2 * 2 ^ (2 * s - 2) ≤
      (8 * t : ℝ) ^ (4 * t + 2) := by
  have ht : 1 ≤ t := by omega
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hs' : (s : ℝ) ≤ 2 * t := by exact_mod_cast hs.2
  have ha0 : 0 ≤ alpha s := (IdentAux.alpha_one_le s).trans' (by norm_num)
  have ha : alpha s ^ 2 ≤ (4 * t : ℝ) ^ (2 * s) := by
    calc _ ≤ ((2 * s : ℝ) ^ s) ^ 2 :=
          pow_le_pow_left₀ ha0 (IdentAux.alpha_bound s) 2
      _ = (2 * s : ℝ) ^ (2 * s) := by rw [← pow_mul]; congr 1; omega
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpow : alpha s ^ 2 * 2 ^ (2 * s - 2) ≤ (8 * t : ℝ) ^ (4 * t) := by
    calc _ ≤ (4 * t : ℝ) ^ (2 * s) * 2 ^ (2 * s) :=
          mul_le_mul ha (pow_le_pow_right₀ (by norm_num) (by omega))
            (by positivity) (by positivity)
      _ = (8 * t : ℝ) ^ (2 * s) := by rw [← mul_pow]; congr 1; ring
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hP : (1 : ℝ) ≤ (8 * t : ℝ) ^ (4 * t) := one_le_pow₀ (by linarith)
  have hs2 : (s : ℝ) ^ 2 ≤ (2 * t : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hs' 2
  have hterm := mul_le_mul hpow hs2 (sq_nonneg _) (by positivity)
  rw [pow_add, pow_two (8 * t : ℝ)]
  nlinarith [sq_nonneg (t : ℝ)]

theorem roundRat_error (prec : ℕ) (q : ℚ) :
    |(roundRat prec q : ℝ) - q| ≤ 1 / (2 : ℝ) ^ prec := by
  have hpow : (0 : ℝ) < 2 ^ prec := by positivity
  have hlo : (⌊(2 : ℚ) ^ prec * q⌋ : ℝ) ≤ (2 : ℝ) ^ prec * (q : ℝ) := by
    exact_mod_cast Int.floor_le ((2 : ℚ) ^ prec * q)
  have hhi : (2 : ℝ) ^ prec * (q : ℝ) < (⌊(2 : ℚ) ^ prec * q⌋ : ℝ) + 1 := by
    exact_mod_cast Int.lt_floor_add_one ((2 : ℚ) ^ prec * q)
  have he : (⌊(2 : ℚ) ^ prec * q⌋ : ℝ) / 2 ^ prec - q =
      ((⌊(2 : ℚ) ^ prec * q⌋ : ℝ) - 2 ^ prec * q) / 2 ^ prec := by
    field_simp
  simp only [roundRat, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
  rw [he, abs_div, abs_of_pos hpow]
  apply (div_le_div_iff_of_pos_right hpow).mpr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem roundPoly_coeff (p : QPoly d) (prec : ℕ) (a : Fin d →₀ ℕ) :
    (roundPoly prec p).coeff a = roundRat prec (p.coeff a) := by
  classical
  simp only [roundPoly, coeff_sum, coeff_monomial]
  by_cases ha : a ∈ p.support
  · simp [ha]
  · simp [ha, notMem_support_iff.mp ha, roundRat]

theorem roundPoly_homogeneous (p : QPoly d) (prec r : ℕ)
    (hp : p.IsHomogeneous r) : (roundPoly prec p).IsHomogeneous r := by
  classical
  apply IsHomogeneous.sum
  intro a ha
  apply isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.mp ha)

theorem rounding_norm (p : QPoly d) (prec r : ℕ) (hp : p.IsHomogeneous r) :
    SoS.coeffNorm1 (SoS.toReal (roundPoly prec p - p)) ≤
      (d + 1 : ℝ) ^ r / (2 : ℝ) ^ prec := by
  have hhom : (SoS.toReal (roundPoly prec p - p)).IsHomogeneous r :=
    ((roundPoly_homogeneous p prec r hp).sub hp).map (algebraMap ℚ ℝ)
  have hc (a : Fin d →₀ ℕ) :
      |(SoS.toReal (roundPoly prec p - p)).coeff a| ≤ 1 / (2 : ℝ) ^ prec := by
    simpa [SoS.toReal, coeff_map, roundPoly_coeff] using roundRat_error prec (p.coeff a)
  have hcard : ((SoS.toReal (roundPoly prec p - p)).support.card : ℝ) ≤
      (d + 1 : ℝ) ^ r := by
    have hs := SoS.card_support_le (SoS.toReal (roundPoly prec p - p))
    rw [Fintype.card_fin] at hs
    have ht := hs.trans (Nat.pow_le_pow_right (Nat.succ_pos d) hhom.totalDegree_le)
    exact_mod_cast ht
  simpa only [div_eq_mul_inv, one_mul] using (SoS.coeffNorm1_le hc).trans
    (mul_le_mul_of_nonneg_right hcard (by positivity))

theorem subst_lin (P : Mat d) (a : Vec d) : subst P (lin a) = lin (Pᵀ *ᵥ a) := by
  simp only [subst, lin, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, mul_sum,
    mulVec, dotProduct, transpose_apply, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  exact sum_congr rfl fun i _ ↦ by ring

theorem map_hmom {R T : Type} [CommRing R] [CommRing T] (f : R →+* T)
    (r : ℕ) (a v : R) : f (hmom r a v) = hmom r (f a) (f v) := by
  simp only [hmom, map_sum, map_mul, map_pow, map_natCast]

theorem hmom_even_zero {R : Type} [CommRing R] (s : ℕ) (v : R) :
    hmom (2 * s) 0 v = (Nat.doubleFactorial (2 * s - 1) : R) * v ^ s := by
  rw [hmom, sum_eq_single s]
  · simp [hermCoeff]
  · intro i hi hne
    have hi' : i < s := by simp only [mem_range] at hi; omega
    simp [zero_pow (show 2 * s - 2 * i ≠ 0 by omega)]
  · simp

theorem subst_dev_zero {k : ℕ} (D : Data k d) (hs : ∑ i, D.weight i = 1)
    (R : Mat d) (hR : Projection R) (hm : ∀ i, R *ᵥ D.mean i = D.mean i)
    (s : ℕ) : subst (1 - R) (dev (moment D) s) = 0 := by
  let φ : RPoly d →ₐ[ℝ] RPoly d := aeval (fun i ↦ lin ((1 - R) i))
  have hC (c : ℝ) : φ (C c) = C c := aeval_C _ _
  have hmap (r : ℕ) (a v : RPoly d) : φ (hmom r a v) = hmom r (φ a) (φ v) :=
    map_hmom φ.toRingHom r a v
  have hlin (i : Fin k) : φ (lin (D.mean i)) = 0 := by
    change subst (1 - R) (lin (D.mean i)) = 0
    rw [subst_lin, transpose_sub, transpose_one, hR.1, sub_mulVec, one_mulVec, hm i,
      sub_self]
    simp [lin]
  have hpop (r : ℕ) : φ (moment D r) = hmom r 0 (φ (S D)) := by
    simp only [moment, map_sum, map_mul, hC, hmap, hlin]
    rw [← sum_mul, ← map_sum, hs, map_one, one_mul]
  have htwo : φ (moment D 2) = φ (S D) := by
    have h := hpop (2 * 1)
    rw [hmom_even_zero] at h
    simpa using h
  change φ (dev (moment D) s) = 0
  simp only [dev, map_sub, map_mul, map_pow, htwo, hpop,
    hmom_even_zero, alpha, map_natCast, sub_self]

theorem dev_homogeneous (M : ℕ → RPoly d) (s : ℕ)
    (h₂ : (M 2).IsHomogeneous 2) (hs : (M (2 * s)).IsHomogeneous (2 * s)) :
    (dev M s).IsHomogeneous (2 * s) :=
  hs.sub ((h₂.pow s).C_mul _)

theorem constraint_homogeneous (M : ℕ → RPoly d) (ε : ℝ) (s : ℕ)
    (h₂ : (M 2).IsHomogeneous 2) (hs : (M (2 * s)).IsHomogeneous (2 * s)) :
    (constraint M ε s).IsHomogeneous (4 * s) := by
  have hn : ((nsq : RPoly d) ^ (2 * s)).IsHomogeneous (4 * s) := by
    convert (nsq_homogeneous (d := d)).pow (2 * s) using 1
    omega
  have hd : (dev M s ^ 2).IsHomogeneous (4 * s) := by
    convert (dev_homogeneous M s h₂ hs).pow 2 using 1
    omega
  exact (hn.C_mul ε).sub hd

theorem size_bounds_one {t : ℕ} {W : ℝ} (ht : 1 ≤ t)
    (hW : 64 * (d + 1 : ℝ) ^ 2 * t ≤ W) :
    64 ≤ W ∧ (d : ℝ) ≤ W ∧ 2 * (d : ℝ) ^ 2 ≤ W ∧ 16 * t ≤ W := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hsq : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ t by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem dev_norm {M : ℕ → RPoly d} {s : ℕ} {W : ℝ} (hW : 2 ≤ W)
    (ha : alpha s ≤ W ^ s) (h₂ : SoS.coeffNorm1 (M 2) ≤ W ^ 2)
    (hs : SoS.coeffNorm1 (M (2 * s)) ≤ W ^ (4 * s)) :
    SoS.coeffNorm1 (dev M s) ≤ 2 * W ^ (4 * s) := by
  have hgauss : SoS.coeffNorm1 (C (alpha s) * M 2 ^ s) ≤ W ^ (4 * s) := by
    rw [SoS.coeffNorm1_C_mul, abs_of_nonneg ((IdentAux.alpha_one_le s).trans'
      (by norm_num : (0 : ℝ) ≤ 1))]
    calc _ ≤ W ^ s * (W ^ 2) ^ s := mul_le_mul ha (IdentAux.norm_pow h₂ s)
          (SoS.coeffNorm1_nonneg _) (by positivity)
      _ = W ^ (3 * s) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ _ := SoS.pow_le_pow_of_two_le hW (by omega)
  exact (SoS.coeffNorm1_sub_le _ _).trans (by linarith)

end

end ABBKS26.IdCov.ApproxAux
