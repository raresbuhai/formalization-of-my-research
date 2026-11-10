module

public import ABBKS26.Centered.IdentAux

/-! Degree and matrix certificates for centered eigenvector identifiability. -/

@[expose] public section

namespace ABBKS26.Centered.IdentAux

noncomputable section

open Common MvPolynomial Matrix
open scoped BigOperators

variable {k d : ℕ}

theorem quad_add (A B : Mat d) : quad (A + B) = quad A + quad B := by
  simp [quad, C_add, add_mul, Finset.sum_add_distrib]

theorem quad_homogeneous (A : Mat d) : (quad A).IsHomogeneous 2 := by
  refine IsHomogeneous.sum _ _ _ fun i _ ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ ?_
  exact ((isHomogeneous_X ℝ i).C_mul _).mul (isHomogeneous_X ℝ j)

theorem nsq_homogeneous : (nsq : RPoly d).IsHomogeneous 2 := by
  exact IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow i 2

theorem psi_homogeneous (F : FrameModel k d) : (psi F).IsHomogeneous 4 := by
  apply IsHomogeneous.sub
  · exact IsHomogeneous.sum _ _ _ fun i _ ↦ ((quad_homogeneous _).pow 2).C_mul _
  · simpa only [map_ofNat] using ((quad_homogeneous (averageCov F)).pow 2).C_mul 3

theorem hConstraint_homogeneous (p : RPoly d) (εh : ℝ) (hp : p.IsHomogeneous 4) :
    (hConstraint p εh).IsHomogeneous 8 := by
  have hv : (liftV p).IsHomogeneous 4 := hp.rename_isHomogeneous
  have hu : (liftU p).IsHomogeneous 4 := hp.rename_isHomogeneous
  have hnV : (liftV (nsq : RPoly d)).IsHomogeneous 2 :=
    nsq_homogeneous.rename_isHomogeneous
  have hnU : (liftU (nsq : RPoly d)).IsHomogeneous 2 :=
    nsq_homogeneous.rename_isHomogeneous
  have hpol : (polarize p).IsHomogeneous 4 := by
    apply IsHomogeneous.C_mul
    apply IsHomogeneous.sub
    · apply IsHomogeneous.sub
      · apply IsHomogeneous.add
        · simpa using hp.aeval _ (fun i ↦
            (isHomogeneous_X ℝ _).add (isHomogeneous_X ℝ _))
        · simpa using hp.aeval _ (fun i ↦
            (isHomogeneous_X ℝ _).sub (isHomogeneous_X ℝ _))
      · simpa only [map_ofNat] using hv.C_mul 2
    · simpa only [map_ofNat] using hu.C_mul 2
  exact ((hnV.pow 4).add (hnU.pow 4)).C_mul εh |>.sub
    (by simpa only [map_ofNat] using (hpol.C_mul 4).pow 2)

/-- Discard zero constraint products before checking the unsubstituted family degrees. -/
theorem derivesAt_of_homogeneous (A : Rounding.FamilySystem d)
    (Ξ : Fin A.slots.length → Mat d) (deg : ℕ) (M : ℝ) (g : RPoly d)
    (hh : ∀ a, (inst A.families[A.slots[a]] (Ξ a)).IsHomogeneous
      A.families[A.slots[a]].totalDegree)
    (h : SoS.DerivesNq (A.instances Ξ) deg M 1 g) : A.DerivesAt Ξ deg M g := by
  classical
  obtain ⟨P, hn, hq⟩ := h
  let Q : SoS.Proof (A.instances Ξ) g deg := {
    mult := fun S ↦ if SoS.System.prod (A.instances Ξ) S = 0 then 0 else P.mult S
    isSOS_mult := fun S ↦ by
      split_ifs
      · exact SoS.IsSOS.zero
      · exact P.isSOS_mult S
    degree_le := fun S hS ↦ by
      split_ifs at hS ⊢ with hz
      · exact (hS rfl).elim
      · exact P.degree_le S hS
    eq_sum := by
      apply P.eq_sum.trans
      apply Finset.sum_congr rfl
      intro S _
      split_ifs with hz <;> simp [hz] }
  have hget (a : Fin A.slots.length) :
      (A.instances Ξ).get (A.slotIndex Ξ a) = inst A.families[A.slots[a]] (Ξ a) := by
    simp [Rounding.FamilySystem.instances, Rounding.FamilySystem.slotIndex]
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro S
    dsimp only [Q]
    split_ifs
    · simpa using (SoS.coeffNorm1_nonneg _).trans (hn S)
    · exact hn S
  · intro S hS
    dsimp only [Q]
    split_ifs <;> simp [hq S hS]
  · intro a ha
    have hz : inst A.families[A.slots[a]] (Ξ a) ≠ 0 := by
      intro hz
      apply ha
      have hp : SoS.System.prod (A.instances Ξ) {A.slotIndex Ξ a} = 0 := by
        simpa only [SoS.System.prod, Finset.prod_singleton] using (hget a).trans hz
      simp only [Q, hp, ite_true]
    have hd := Q.degree_le {A.slotIndex Ξ a} ha
    simpa only [SoS.System.degree, Finset.sum_singleton, hget,
      (hh a).totalDegree hz] using hd

theorem system_derivesAt (F : FrameModel k d) (εq εh M : ℝ) (E : Mat d)
    (g : RPoly d)
    (h : SoS.DerivesNq ((system (psi F) εq εh).instances (fun _ ↦ E)) 8 M 1 g) :
    (system (psi F) εq εh).DerivesAt (fun _ ↦ E) 8 M g := by
  apply derivesAt_of_homogeneous _ _ _ _ _ ?_ h
  intro a
  fin_cases a
  change (inst (hConstraint (psi F) εh) E).IsHomogeneous
    (hConstraint (psi F) εh).totalDegree
  by_cases hz : hConstraint (psi F) εh = 0
  · simp only [hz, inst, map_zero, totalDegree_zero]
    exact isHomogeneous_zero _ _ 0
  · rw [(hConstraint_homogeneous _ _ (psi_homogeneous F)).totalDegree hz]
    simpa only [inst, one_mul] using
      (hConstraint_homogeneous _ εh (psi_homogeneous F)).aeval (n := 1)
        (Sum.elim (fun i ↦ lin (E i)) X) (by
          intro i
          rcases i with i | i
          · change (lin (E i)).IsHomogeneous 1
            exact IsHomogeneous.sum _ _ _ fun j _ ↦ (isHomogeneous_X ℝ j).C_mul _
          · exact isHomogeneous_X ℝ i)

theorem average_symm (F : FrameModel k d) (h : ∀ j, (F.cov j).IsHermitian) :
    (averageCov F)ᵀ = averageCov F := by
  have hs (j : Fin k) : (F.cov j)ᵀ = F.cov j := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h j
  simp only [averageCov, transpose_sum, transpose_smul, hs]

theorem average_error_bound (F : FrameModel k d) (w γ rF : ℝ)
    (hF : DataValid F w γ rF) (v : Vec d) :
    |qform (averageCov F - 1) v| ≤ γ * sqnorm v := by
  have hsecond : F.second = averageCov F := by
    simp only [FrameModel.second, hF.2.1, vecMulVec_zero, add_zero, averageCov]
  have hlo := hF.2.2.1.2.1 v
  have hhi := hF.2.2.1.2.2 v
  rw [hsecond] at hlo hhi
  simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hlo hhi
  simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub]
  exact abs_le.mpr ⟨by dsimp only [sqnorm]; nlinarith,
    by dsimp only [sqnorm]; nlinarith⟩

theorem frob_bound (E : Mat d) (hs : Eᵀ = E) (e : ℝ) (he : 0 ≤ e)
    (hE : ∀ v, |qform E v| ≤ e * sqnorm v) : frobSq E ≤ d * e ^ 2 := by
  have hd (i : Fin d) := (operator_square E hs e he hE).diag_nonneg (i := i)
  have hsym (i j : Fin d) : E j i = E i j := congrFun (congrFun hs i) j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
    mul_one, Matrix.mul_apply, hsym] at hd
  unfold frobSq
  simp only [← pow_two] at hd
  exact (Finset.sum_le_sum fun i _ ↦ sub_nonneg.mp (hd i)).trans_eq (by simp)

theorem projection_entry (P : Mat d) (hP : Projection P) (i j : Fin d) :
    |P i j| ≤ 1 := by
  apply entry_bound P hP.1 1 (by norm_num) ?_ i j
  intro v
  rw [← Rounding.DetRoundAux.projection_sqnorm P hP, one_mul,
    abs_of_nonneg (Rounding.DetRoundAux.sqnorm_nonneg _)]
  exact Rounding.DetRoundAux.projection_contract P hP v

theorem eigen_remainder (E S P : Mat d) (γ δ : ℝ) (hδ : 0 < δ)
    (hE : Eᵀ = E) (hS : Sᵀ = S) (hP : Projection P) (hγ : 0 ≤ γ)
    (hSbound : ∀ v, |qform S v| ≤ γ * sqnorm v)
    (hspec : LE (δ ^ 2 • P) ((E + S) * (E + S))) :
    IsSumSq (C (2 / δ ^ 2) * quad (E * E) +
      C (2 * γ ^ 2 / δ ^ 2) * nsq - quad P) := by
  have hT : ((E - S) * (E - S)).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, transpose_sub, hE, hS] using
      posSemidef_conjTranspose_mul_self (E - S)
  have hC : ((E + S) * (E + S) - δ ^ 2 • P).PosSemidef := by
    apply PosSemidef.of_dotProduct_mulVec_nonneg
    · simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_sub,
        transpose_mul, transpose_add, transpose_smul, hE, hS, hP.1]
    · intro v
      simpa only [star_trivial, sub_mulVec, dotProduct_sub, qform] using
        sub_nonneg.mpr (hspec v)
  have hr := hT.add (((operator_square S hS γ hγ hSbound).smul
    (by norm_num : (0 : ℝ) ≤ 2)).add hC)
  have heq : (E - S) * (E - S) +
      ((2 : ℝ) • (γ ^ 2 • (1 : Mat d) - S * S) +
        ((E + S) * (E + S) - δ ^ 2 • P)) =
      (2 : ℝ) • (E * E) + (2 * γ ^ 2) • (1 : Mat d) - δ ^ 2 • P := by
    rw [show 2 * γ ^ 2 = γ ^ 2 + γ ^ 2 by ring, add_smul]
    simp only [smul_sub, two_smul]
    noncomm_ring
  rw [heq] at hr
  have ht := SoS.isSumSq_C_mul (show 0 ≤ 1 / δ ^ 2 by positivity)
    (SoSKit.psd_quad _ hr)
  rw [quad_sub, quad_add, quad_smul, quad_smul, quad_one, quad_smul] at ht
  have hc : (C (1 / δ ^ 2) : RPoly d) * C (δ ^ 2) = 1 := by
    rw [← C_mul, one_div_mul_cancel (pow_ne_zero _ hδ.ne'), C_1]
  convert ht using 1
  simp only [div_eq_mul_inv, C_mul, C_1, map_ofNat] at hc ⊢
  linear_combination quad P * hc

theorem eigen_parameters (w γ δ W : ℝ) (hw : 0 < w) (hγ : 0 ≤ γ)
    (hγhi : γ ≤ 1 / 10) (hδ : 0 < δ) (hW₂ : 2 ≤ W) (hδW : 1 / δ ≤ W)
    (hW : 64 * (d + 1 : ℝ) ^ 2 + 1 / w ≤ W) :
    4 ≤ W ∧ (d : ℝ) ≤ W ∧ 1.1 / w ≤ W ^ 2 ∧
      2 / δ ^ 2 ≤ 2 * W ^ 2 ∧ 2 * γ ^ 2 / δ ^ 2 ≤ 2 * W ^ 2 := by
  have hW0 : 0 ≤ W := by linarith only [hW₂]
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hz0 : 0 ≤ 1 / w := by positivity
  have hW4 : 4 ≤ W := by nlinarith only [hW, hz0, hd0, sq_nonneg (d : ℝ)]
  have hdW : (d : ℝ) ≤ W := by nlinarith only [hW, hz0, hd0, sq_nonneg (d : ℝ)]
  have hzW : 1 / w ≤ W := by nlinarith only [hW, sq_nonneg (d + 1 : ℝ)]
  have heW : 1.1 / w ≤ W ^ 2 := by
    rw [show 1.1 / w = 1.1 * (1 / w) by ring]
    nlinarith only [hW₂, hzW, sq_nonneg (W - 1)]
  have hcW : 2 / δ ^ 2 ≤ 2 * W ^ 2 := by
    calc
      _ = 2 * (1 / δ) ^ 2 := by ring
      _ ≤ 2 * W ^ 2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hδW 2) (by norm_num)
  have hbW : 2 * γ ^ 2 / δ ^ 2 ≤ 2 * W ^ 2 := by
    have hγ1 : γ ^ 2 ≤ 1 := by nlinarith only [hγ, hγhi]
    calc
      _ = γ ^ 2 * (2 / δ ^ 2) := by ring
      _ ≤ 1 * (2 / δ ^ 2) := mul_le_mul_of_nonneg_right hγ1 (by positivity)
      _ ≤ 2 * W ^ 2 := by simpa only [one_mul] using hcW
  exact ⟨hW4, hdW, heW, hcW, hbW⟩

theorem norm_eigen_remainder (X Y Z : RPoly d) (c b : ℝ)
    (hc : 0 ≤ c) (hb : 0 ≤ b) :
    SoS.coeffNorm1 (C c * X + C b * Y - Z) ≤
      c * SoS.coeffNorm1 X + b * SoS.coeffNorm1 Y + SoS.coeffNorm1 Z := by
  have ha := SoS.coeffNorm1_add_le (C c * X) (C b * Y)
  have hs := SoS.coeffNorm1_sub_le (C c * X + C b * Y) Z
  rw [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_C_mul,
    abs_of_nonneg hc, abs_of_nonneg hb] at ha
  linarith only [ha, hs]

theorem eigen_polynomial_bounds (E P : Mat d) (e c b W : ℝ)
    (hsE : Eᵀ = E) (hP : Projection P) (he : 0 ≤ e)
    (hE : ∀ v, |qform E v| ≤ e * sqnorm v)
    (hW : 0 ≤ W) (hdW : (d : ℝ) ≤ W) (heW : e ≤ W ^ 2)
    (hc0 : 0 ≤ c) (hb0 : 0 ≤ b) (hcW : c ≤ 2 * W ^ 2) (hbW : b ≤ 2 * W ^ 2) :
    let R := C c * quad (E * E) + C b * nsq - quad P
    SoS.coeffNorm1 R ≤ 2 * W ^ 9 + 2 * W ^ 3 + W ^ 2 ∧ R.totalDegree ≤ 8 := by
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hnX : SoS.coeffNorm1 (quad (E * E)) ≤ W ^ 7 := by
    calc
      _ ≤ d ^ 3 * e ^ 2 := norm_energy E hsE e he (entry_bound E hsE e he hE)
      _ ≤ W ^ 3 * (W ^ 2) ^ 2 := by gcongr
      _ = W ^ 7 := by ring
  have hnP : SoS.coeffNorm1 (quad P) ≤ W ^ 2 := by
    exact (norm_quad P 1 (projection_entry P hP)).trans (by
      simpa using pow_le_pow_left₀ hd0 hdW 2)
  constructor
  · calc
      _ ≤ c * SoS.coeffNorm1 (quad (E * E)) + b * SoS.coeffNorm1 (nsq : RPoly d) +
          SoS.coeffNorm1 (quad P) :=
        norm_eigen_remainder (quad (E * E)) nsq (quad P) c b hc0 hb0
      _ ≤ (2 * W ^ 2) * W ^ 7 + (2 * W ^ 2) * W + W ^ 2 := by
        exact add_le_add (add_le_add
          (mul_le_mul hcW hnX (SoS.coeffNorm1_nonneg _) (by positivity))
          (mul_le_mul hbW ((norm_nsq (d := d)).trans hdW)
            (SoS.coeffNorm1_nonneg _) (by positivity))) hnP
      _ = _ := by ring
  · apply (totalDegree_sub _ _).trans
    apply max_le _ ((quad_degree P).trans (by omega))
    apply (totalDegree_add _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by
        simpa only [totalDegree_C, zero_add] using
          (quad_degree (E * E)).trans (by omega : 2 ≤ 8))
    · exact (totalDegree_mul _ _).trans (by
        simpa only [totalDegree_C, zero_add] using
          (nsq_degree (d := d)).trans (by omega : 2 ≤ 8))

theorem eigen_budget (c b W : ℝ) (hW : 4 ≤ W)
    (hcW : c ≤ 2 * W ^ 2) (hbW : b ≤ 2 * W ^ 2) :
    c * W ^ 20 + b + (2 * W ^ 9 + 2 * W ^ 3 + W ^ 2) ≤ W ^ 24 := by
  have hW0 : 0 ≤ W := by linarith only [hW]
  have hp (r : ℕ) (hr : r ≤ 22) : W ^ r ≤ W ^ 22 :=
    pow_le_pow_right₀ (by linarith only [hW]) hr
  calc
    _ ≤ (2 * W ^ 2) * W ^ 20 + 2 * W ^ 2 +
        (2 * W ^ 9 + 2 * W ^ 3 + W ^ 2) := by gcongr
    _ ≤ 9 * W ^ 22 := by
      rw [mul_assoc, ← pow_add]
      norm_num only
      linarith [hp 2 (by omega), hp 3 (by omega), hp 9 (by omega)]
    _ ≤ W ^ 2 * W ^ 22 := mul_le_mul_of_nonneg_right (by nlinarith only [hW])
      (pow_nonneg hW0 _)
    _ = W ^ 24 := by ring

end

end ABBKS26.Centered.IdentAux
