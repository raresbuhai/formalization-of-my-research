module

public import ABBKS26.IdCov.ApproxAux

/-!
# Approximate moments for identical covariances

[ABBKS26, Corollary 6.12 and Lemmas 6.13, 6.14]: certified moment errors, normalization of the
variance, transfer of the constraints to the estimated moments, and rounding of coefficients.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial
open ApproxAux
open scoped BigOperators
variable {k d : ℕ}

def gammaD (t : ℕ) : ℝ := (8 * t : ℝ) ^ (4 * t + 2)

/-- A certified second moment is itself nearly isotropic and positive semidefinite. -/
theorem second_approx
    (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (π γ η : ℝ)
    (hD : D.Valid π γ) (ht : 1 ≤ t) (hη : 0 ≤ η) (hsmall : γ + Real.sqrt η ≤ 1)
    (hM : momentCertificate D M t η) :
    IsSumSq (M 2) ∧ IsSumSq (C (1 + γ + Real.sqrt η) * nsq - M 2) := by
  have hhom : (M 2).IsHomogeneous 2 := hM.1 1 (by omega) (by omega)
  have herr := hM.2 1 (by omega) (by omega)
  have hn (v : Vec d) : 0 ≤ sqnorm v := by
    change 0 ≤ ∑ i, v i * v i
    exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)
  have hb (v : Vec d) :
      |eval v (M 2) - eval v (moment D 2)| ≤ Real.sqrt η * sqnorm v := by
    have hb := SoSKit.evaluate_bound (M 2 - moment D 2) η 2 hη herr v
    simpa only [map_sub, Real.sq_sqrt (hn v)] using hb
  have hlo (v : Vec d) : (1 - γ) * sqnorm v ≤ eval v (moment D 2) := by
    rw [eval_second D hD.1.2.2.1]
    simpa only [qform, sqnorm, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] using
      hD.2.1.2.1 v
  have hhi (v : Vec d) : eval v (moment D 2) ≤ (1 + γ) * sqnorm v := by
    rw [eval_second D hD.1.2.2.1]
    simpa only [qform, sqnorm, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] using
      hD.2.1.2.2 v
  constructor
  · apply quadratic_sos _ hhom
    intro v
    have := (abs_le.mp (hb v)).1
    have := mul_nonneg (show 0 ≤ 1 - γ - Real.sqrt η by linarith) (hn v)
    nlinarith [hlo v]
  · apply quadratic_sos _ ((nsq_homogeneous.C_mul _).sub hhom)
    intro v
    simp only [map_sub, map_mul, eval_C, eval_nsq]
    have := (abs_le.mp (hb v)).2
    nlinarith [hhi v]

/-- Variance normalization amplifies moment errors by gammaD. -/
theorem closeness
    (D : Data k d) (M : ℕ → RPoly d) (t s : ℕ) (π γ η : ℝ)
    (hD : D.Valid π γ) (hη : 0 ≤ η) (hsmall : γ + Real.sqrt η ≤ 1)
    (hs : 2 ≤ s ∧ s ≤ 2 * t) (hM : momentCertificate D M t η) :
    IsSumSq (C (η * gammaD t) * nsq ^ (2 * s) -
      (dev M s - dev (moment D) s) ^ 2) := by
  have ht : 1 ≤ t := by omega
  have hN : IsSumSq (nsq : RPoly d) := IsSumSq.sum_sq _ _
  have hb := second_approx D M t π γ η hD ht hη hsmall hM
  have hX : IsSumSq (C (2 : ℝ) * nsq - M 2) := by
    convert (SoS.isSumSq_C_mul
      (show 0 ≤ 2 - (1 + γ + Real.sqrt η) by linarith) hN).add hb.2 using 1
    rw [C_sub]
    ring
  have hY0 : IsSumSq (moment D 2) := by
    rw [second_moment D hD.1.2.2.1]
    exact (sos_bounds D π γ hD).2.1.add (sos_bounds D π γ hD).1
  have hY : IsSumSq (C (2 : ℝ) * nsq - moment D 2) := by
    apply quadratic_sos _ ((nsq_homogeneous.C_mul _).sub (homogeneity D 2 0).1)
    intro v
    have hu := hD.2.1.2.2 v
    rw [← eval_second D hD.1.2.2.1 v] at hu
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hu
    change eval v (moment D 2) ≤ (1 + γ) * sqnorm v at hu
    simp only [map_sub, map_mul, eval_C, eval_nsq]
    have hn : 0 ≤ sqnorm v := by
      change 0 ≤ ∑ i, v i * v i
      exact Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)
    nlinarith [hD.2.2]
  let B : ℝ := (s : ℝ) ^ 2 * 2 ^ (2 * s - 2)
  let T : RPoly d := C B * nsq ^ (2 * s - 2)
  have hT : IsSumSq T :=
    SoS.isSumSq_C_mul (by dsimp [B]; positivity) (SoS.isSumSq_pow hN _)
  have hp : IsSumSq (C (η * B) * nsq ^ (2 * s) -
      (M 2 ^ s - moment D 2 ^ s) ^ 2) := by
    have hh := SoSKit.telescoping (M 2) (moment D 2) 2 (by norm_num)
      hb.1 hY0 hX hY s (by omega)
    have he := hM.2 1 (by omega) (by omega)
    have hpow : (nsq : RPoly d) ^ (2 * s - 2) * nsq ^ 2 = nsq ^ (2 * s) := by
      rw [← pow_add, show 2 * s - 2 + 2 = 2 * s by omega]
    convert hh.add (hT.mul he) using 1
    change _ = (C B * nsq ^ (2 * s - 2) * (M 2 - moment D 2) ^ 2 -
      (M 2 ^ s - moment D 2 ^ s) ^ 2) +
      C B * nsq ^ (2 * s - 2) *
        (C η * nsq ^ 2 - (M 2 - moment D 2) ^ 2)
    rw [C_mul]
    linear_combination -(C B * C η) * hpow
  have hlocal : IsSumSq
      (C (η * (2 + 2 * alpha s ^ 2 * B)) * nsq ^ (2 * s) -
        (dev M s - dev (moment D) s) ^ 2) := by
    have h₁ := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2)
      (hM.2 s (by omega) hs.2)
    have h₂ := SoS.isSumSq_C_mul (show 0 ≤ 2 * alpha s ^ 2 by positivity) hp
    have h₃ := SoSKit.two_squares (M (2 * s) - moment D (2 * s))
      (C (alpha s) * (M 2 ^ s - moment D 2 ^ s))
    convert (h₁.add h₂).add h₃ using 1
    simp only [dev, C_mul, C_add, C_pow, map_ofNat]
    ring
  have hpad := SoS.isSumSq_C_mul
    (mul_nonneg hη (sub_nonneg.mpr (error_constant_bound hs)))
    (SoS.isSumSq_pow hN (2 * s))
  convert hlocal.add hpad using 1
  simp only [B, gammaD, C_mul, C_sub, C_add]
  ring

/-- Approximate constraints derive the exact constraints at twice the tolerance. -/
theorem transfer
    (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (π γ η ε W : ℝ)
    (hD : D.Valid π γ) (hη : 0 ≤ η) (hsmall : γ + Real.sqrt η ≤ 1)
    (he : 0 < ε) (hM : momentCertificate D M t η)
    (hW : NormLedger D M t π ε W) :
    ∀ f ∈ system (moment D) t (2 * ε + 2 * η * gammaD t),
      SoS.DerivesNq (system M t ε) f.totalDegree (W ^ (16 * t + 1)) 1 f := by
  have hWpos : 0 < W := (one_div_pos.mpr he).trans_le hW.2.2.1
  have hW1 : 1 ≤ W := by
    have hp : π ≤ 1 := IdentAux.pi_le_one D hD
    have hdiv : 4 ≤ 4 / π := (le_div_iff₀ hD.1.1).mpr (by linarith)
    linarith [hW.2.1]
  intro f hf
  simp only [system, List.mem_append, List.mem_singleton, List.mem_filter,
    List.mem_map, List.mem_range, ne_eq, decide_eq_true_eq] at hf
  rcases hf with rfl | ⟨⟨j, hj, rfl⟩, hz⟩
  · apply SoS.DerivesNq.of_mem _ le_rfl (one_le_pow₀ hW1)
    simp [system]
  · let s := j + 2
    have hs : 2 ≤ s ∧ s ≤ 2 * t := by dsimp [s]; omega
    have ht : 1 ≤ t := by omega
    have hb := size_bounds_one ht hW.1
    have hW2 : 2 ≤ W := by linarith [hb.1]
    have hW0 : 0 ≤ W := hWpos.le
    have hη1 : η ≤ 1 := by
      have hroot : Real.sqrt η ≤ 1 := by linarith [hD.2.1.1]
      nlinarith [Real.sq_sqrt hη, Real.sqrt_nonneg η]
    have ha : alpha s ≤ W ^ s := by
      apply (IdentAux.alpha_bound s).trans
      apply pow_le_pow_left₀ (by positivity)
      have hs' : (s : ℝ) ≤ 2 * t := by exact_mod_cast hs.2
      linarith [hb.2.2.2]
    have hm₂ : SoS.coeffNorm1 (M 2) ≤ W ^ 2 := hW.2.2.2.1 1 (by omega) (by omega)
    have hp₂ : SoS.coeffNorm1 (moment D 2) ≤ W ^ 2 := by
      rw [second_moment D hD.1.2.2.1]
      have hn := IdentAux.quadratic_norms D π γ hD
      have hQ := hn.2.trans hb.2.2.1
      have hS := hn.1.trans hb.2.2.1
      have hh := SoS.add_le_pow_succ (c := 1) hW2
        (by simpa using hQ) (by simpa using hS)
      exact (SoS.coeffNorm1_add_le _ _).trans (by simpa using hh)
    have hm : SoS.coeffNorm1 (dev M s) ≤ 2 * W ^ (4 * s) := by
      apply ApproxAux.dev_norm hW2 ha hm₂
      exact (hW.2.2.2.1 s (by omega) hs.2).trans
        (SoS.pow_le_pow_of_two_le hW2 (by omega))
    have hp : SoS.coeffNorm1 (dev (moment D) s) ≤ 2 * W ^ (4 * s) := by
      apply ApproxAux.dev_norm hW2 ha hp₂
      simpa only [show 4 * s = 2 * (2 * s) by omega] using
        hW.2.2.2.2 (2 * s) (by omega)
    have hgam : gammaD t ≤ W ^ (4 * t + 2) := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [hb.2.2.2]
    let G : RPoly d := C (2 * η * gammaD t) * nsq ^ (2 * s) +
      2 * dev M s ^ 2 - dev (moment D) s ^ 2
    have hG : IsSumSq G := by
      have hc := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2)
        (closeness D M t s π γ η hD hη hsmall hs hM)
      convert hc.add (SoS.isSumSq_sq (2 * dev M s - dev (moment D) s)) using 1
      simp only [G, C_mul, map_ofNat]
      ring
    have hmh := dev_homogeneous M s (hM.1 1 (by omega) (by omega))
      (hM.1 s (by omega) hs.2)
    have hph := (homogeneity D 0 s).2
    have hmh₂ : (dev M s ^ 2).IsHomogeneous (4 * s) := by
      convert hmh.pow 2 using 1
      omega
    have hph₂ : (dev (moment D) s ^ 2).IsHomogeneous (4 * s) := by
      convert hph.pow 2 using 1
      omega
    have hNh : ((nsq : RPoly d) ^ (2 * s)).IsHomogeneous (4 * s) := by
      convert nsq_homogeneous.pow (2 * s) using 1
      omega
    have hGd : G.totalDegree ≤ 4 * s := by
      apply IsHomogeneous.totalDegree_le
      exact ((hNh.C_mul _).add (by simpa only [map_ofNat] using hmh₂.C_mul 2)).sub hph₂
    have hGn : SoS.coeffNorm1 G ≤ 14 * W ^ (16 * t) := by
      have hfirst : SoS.coeffNorm1 (C (2 * η * gammaD t) * nsq ^ (2 * s) :
          RPoly d) ≤ 2 * W ^ (16 * t) := by
        have hcoef : 2 * η * gammaD t ≤ 2 * W ^ (4 * t + 2) := by
          have hg0 : 0 ≤ gammaD t := by unfold gammaD; positivity
          nlinarith
        rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (by unfold gammaD; positivity)]
        calc _ ≤ (2 * W ^ (4 * t + 2)) * W ^ (2 * s) := mul_le_mul hcoef
              (IdentAux.norm_pow (IdentAux.norm_nsq.trans hb.2.1) _)
              (SoS.coeffNorm1_nonneg _) (by positivity)
          _ = 2 * W ^ (4 * t + 2 + 2 * s) := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
              (SoS.pow_le_pow_of_two_le hW2 (by omega)) (by norm_num)
      have hsq {p : RPoly d} (hn : SoS.coeffNorm1 p ≤ 2 * W ^ (4 * s)) :
          SoS.coeffNorm1 (p ^ 2) ≤ 4 * W ^ (16 * t) := by
        calc _ ≤ (2 * W ^ (4 * s)) ^ 2 := IdentAux.norm_pow hn _
          _ = 4 * W ^ (8 * s) := by
            rw [mul_pow, ← pow_mul, show 4 * s * 2 = 8 * s by omega]
            norm_num
          _ ≤ _ := mul_le_mul_of_nonneg_left
              (SoS.pow_le_pow_of_two_le hW2 (by omega)) (by norm_num)
      have hm' : SoS.coeffNorm1 (2 * dev M s ^ 2) ≤ 8 * W ^ (16 * t) := by
        have hh := SoS.coeffNorm1_C_mul (2 : ℝ) (dev M s ^ 2)
        norm_num only [map_ofNat, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hh
        rw [hh]
        linarith [hsq hm]
      exact (SoS.coeffNorm1_sub_le _ _).trans
        ((add_le_add (SoS.coeffNorm1_add_le _ _) le_rfl).trans (by linarith [hsq hp]))
    have hd : (constraint M ε s).totalDegree ≤ 4 * s :=
      (constraint_homogeneous M ε s (hM.1 1 (by omega) (by omega))
        (hM.1 s (by omega) hs.2)).totalDegree_le
    have hA := (IdentAux.constraint_derives M t s ε hs hd).smul
      (by norm_num : (0 : ℝ) ≤ 2)
    have hB := SoS.DerivesNq.ofIsSOS (q := 1) (system M t ε)
      (by simpa only [SoS.IsSOS, SoS.toReal_real] using hG) hGd hGn
    have hsum := (hA.add hB).congr
      (show C (2 : ℝ) * constraint M ε s + G =
        constraint (moment D) (2 * ε + 2 * η * gammaD t) s by
        simp only [constraint, G, C_add, C_mul, map_ofNat]; ring)
    have hdegree : (constraint (moment D) (2 * ε + 2 * η * gammaD t) s).totalDegree =
        4 * s :=
      IsHomogeneous.totalDegree
        (constraint_homogeneous _ _ _ (homogeneity D 2 0).1 (homogeneity D (2 * s) 0).1)
        hz
    change SoS.DerivesNq _ (constraint (moment D) _ s).totalDegree _ _ _
    rw [hdegree]
    apply hsum.mono le_rfl
    have hP : 1 ≤ W ^ (16 * t) := one_le_pow₀ hW1
    rw [pow_succ]
    nlinarith [hb.1]

/-- All approximate constraints are feasible off the mean span. -/
theorem feasibility
    (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (π γ η ε : ℝ) (R : Mat d)
    (hD : D.Valid π γ) (hη : 0 ≤ η) (hsmall : γ + Real.sqrt η ≤ 1)
    (hM : momentCertificate D M t η) (hε : η * gammaD t ≤ ε)
    (hR : Projection R) (hm : ∀ i, R *ᵥ D.mean i = D.mean i) :
    ∀ s, 2 ≤ s → s ≤ 2 * t → IsSumSq (subst (1 - R) (constraint M ε s)) := by
  intro s hs ht
  let φ : RPoly d →ₐ[ℝ] RPoly d := aeval (fun i ↦ lin ((1 - R) i))
  have hC (c : ℝ) : φ (C c) = C c := aeval_C _ _
  have hz : φ (dev (moment D) s) = 0 := subst_dev_zero D hD.1.2.2.1 R hR hm s
  have he := SoS.isSumSq_map φ (closeness D M t s π γ η hD hη hsmall ⟨hs, ht⟩ hM)
  have hN : IsSumSq (φ nsq) := SoS.isSumSq_map φ (IsSumSq.sum_sq _ _)
  have hpad := SoS.isSumSq_C_mul (sub_nonneg.mpr hε)
    (SoS.isSumSq_pow hN (2 * s))
  simp only [map_sub, map_mul, map_pow, hC, hz, sub_zero] at he
  change IsSumSq (φ (constraint M ε s))
  convert hpad.add he using 1
  simp only [constraint, map_sub, map_mul, map_pow, hC]
  ring

/-- Rounding moments before nested solving makes precision independent of sample size. -/
theorem rounding
    (D : Data k d) (M : ℕ → QPoly d) (t p : ℕ) (η : ℝ)
    (hη : 0 < η) (hM : momentCertificate D (fun r ↦ SoS.toReal (M r)) t η)
    (hp : (d + 1 : ℝ) ^ (4 * t) / Real.sqrt η ≤ (2 : ℝ) ^ p) :
    momentCertificate D (fun r ↦ SoS.toReal (roundPoly p (M r))) t (4 * η) := by
  have hq (s : ℕ) (hs : 1 ≤ s) (ht : s ≤ 2 * t) :
      (M (2 * s)).IsHomogeneous (2 * s) :=
    IsHomogeneous.of_map (algebraMap ℚ ℝ).injective (hM.1 s hs ht)
  constructor
  · intro s hs ht
    exact (roundPoly_homogeneous _ _ _ (hq s hs ht)).map (algebraMap ℚ ℝ)
  · intro s hs ht
    let E : RPoly d := SoS.toReal (roundPoly p (M (2 * s)) - M (2 * s))
    have hhom : E.IsHomogeneous (2 * s) :=
      ((roundPoly_homogeneous _ _ _ (hq s hs ht)).sub (hq s hs ht)).map
        (algebraMap ℚ ℝ)
    have hnorm : SoS.coeffNorm1 E ≤ Real.sqrt η := by
      have htop : (d + 1 : ℝ) ^ (2 * s) ≤ (d + 1 : ℝ) ^ (4 * t) :=
        pow_le_pow_right₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith) (by omega)
      have hprod := (div_le_iff₀ (Real.sqrt_pos.mpr hη)).mp hp
      rw [mul_comm ((2 : ℝ) ^ p)] at hprod
      exact (rounding_norm _ p _ (hq s hs ht)).trans
        ((div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ p)).mpr (htop.trans hprod))
    have hnorm2 : SoS.coeffNorm1 E ^ 2 ≤ η := by
      simpa only [Real.sq_sqrt hη.le] using
        pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) hnorm 2
    have hN : IsSumSq ((nsq : RPoly d) ^ (2 * s)) :=
      SoS.isSumSq_pow (IsSumSq.sum_sq _ _) _
    have he : IsSumSq (C η * nsq ^ (2 * s) - E ^ 2) := by
      convert (SoS.isSumSq_C_mul (sub_nonneg.mpr hnorm2) hN).add
        (SoSKit.l1_square E (2 * s) hhom) using 1
      rw [C_sub]
      ring
    have ho := hM.2 s hs ht
    have htri := SoSKit.two_squares E (-(SoS.toReal (M (2 * s)) - moment D (2 * s)))
    convert (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 2) (he.add ho)).add htri using 1
    simp only [E, SoS.toReal, map_sub, C_mul, map_ofNat]
    ring

end

end ABBKS26.IdCov
