module

public import ABBKS26.Centered.EmpiricalProjection

/-! Shared analytic preparation for the rounded empirical centered system. -/

@[expose] public section

namespace ABBKS26.Centered.EmpiricalLedger

open Common Matrix MvPolynomial Rounding
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

theorem norm_nat_mul {σ : Type} (n : ℕ) (p : MvPolynomial σ ℝ) :
    SoS.coeffNorm1 ((n : MvPolynomial σ ℝ) * p) = n * SoS.coeffNorm1 p := by
  rw [← map_natCast C n, SoS.coeffNorm1_C_mul, abs_of_nonneg (Nat.cast_nonneg n)]

theorem norm_nsq : SoS.coeffNorm1 (nsq : RPoly d) ≤ d := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    ∑ i : Fin d, SoS.coeffNorm1 (X i ^ 2 : RPoly d) ≤ ∑ _i : Fin d, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i _ ↦
        (SoS.coeffNorm1_pow_le (X i : RPoly d) 2).trans_eq (by
          rw [SoS.coeffNorm1_X, one_pow])
    _ = d := by simp

theorem norm_rename {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ ℝ) :
    SoS.coeffNorm1 (rename f p) ≤ SoS.coeffNorm1 p := by
  rw [rename_eq_aeval]
  simpa using SoS.coeffNorm1_aeval_le (X ∘ f) (β := 1) le_rfl
    (fun i ↦ (SoS.coeffNorm1_X (f i)).le) p

theorem norm_polarize (p : RPoly d) (hp : p.totalDegree ≤ 4) :
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

theorem rounded_homogeneous (p : QPoly d) (prec : ℕ)
    (hp : p.IsHomogeneous 4) : (SoS.toReal (roundPoly prec p)).IsHomogeneous 4 := by
  apply IsHomogeneous.map
  apply IsHomogeneous.sum
  intro α hα
  apply isHomogeneous_monomial
  rw [Finsupp.degree_eq_weight_one]
  exact hp (mem_support_iff.mp hα)


theorem norm_nsq_pow (r : ℕ) :
    SoS.coeffNorm1 ((nsq : RPoly d) ^ r) ≤ (d : ℝ) ^ r :=
  (SoS.coeffNorm1_pow_le _ _).trans
    (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) norm_nsq r)

theorem norm_qConstraint (p : RPoly d) (ε : ℝ) :
    SoS.coeffNorm1 (qConstraint p ε) ≤ ε ^ 2 * (d : ℝ) ^ 4 +
      SoS.coeffNorm1 p ^ 2 / 9 := by
  have hn := norm_nsq_pow (d := d) 4
  have hp := SoS.coeffNorm1_pow_le (C (1 / 3) * p) 2
  rw [SoS.coeffNorm1_C_mul] at hp
  norm_num at hp
  have he := SoS.coeffNorm1_sub_le (C (ε ^ 2) * nsq ^ 4) ((C (1 / 3) * p) ^ 2)
  rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (sq_nonneg ε)] at he
  exact he.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (sq_nonneg ε)])

theorem norm_hConstraint (p : RPoly d) (hp : p.totalDegree ≤ 4) (ε : ℝ) :
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


theorem psi_norm (F : FrameModel k d) (w g r : ℝ) (hF : DataValid F w g r) :
    SoS.coeffNorm1 (psi F) ≤ 3 * (d : ℝ) ^ 4 * (1.1 / w) ^ 2 := by
  let e := 1.1 / w
  have he : 0 ≤ e := by have := hF.1.1; positivity
  have hentry (j : Fin k) := IdentAux.entry_bound (deviation F j)
    (IdentAux.deviation_symm F (fun j ↦ (hF.1.2.2.2 j).isHermitian) j) e he
      ((Centered.deviation_bound F w g r hF).2 j)
  have hn : SoS.coeffNorm1 (C (1 / 3) * psi F) ≤ (d : ℝ) ^ 4 * e ^ 2 := by
    rw [IdentAux.quartic_third F hF.1.2.2.1]
    convert IdentAux.weighted_norm F.weight (fun j ↦ quad (deviation F j) ^ 2)
      (fun j ↦ hF.1.1.le.trans (hF.1.2.1 j)) hF.1.2.2.1
      (((d : ℝ) ^ 2 * e) ^ 2)
      (fun j ↦ IdentAux.norm_pow (IdentAux.norm_quad _ e (hentry j)) 2) using 1
    ring
  rw [SoS.coeffNorm1_C_mul] at hn
  norm_num at hn
  dsimp only [e] at hn
  linarith only [hn]

theorem absorb (W : ℝ) (hW : 4 ≤ W) (c m n : ℕ) (hc : c ≤ 4 ^ m) :
    (c : ℝ) * W ^ n ≤ W ^ (m + n) := by
  have hcR : (c : ℝ) ≤ (4 : ℝ) ^ m := by exact_mod_cast hc
  have hbase : (c : ℝ) ≤ W ^ m :=
    hcR.trans (pow_le_pow_left₀ (by norm_num) hW m)
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right hbase (by positivity)

/-- One explicit power pays for the population constraints, the rounded constraints,
and every matrix instance allowed by the target ball. -/
theorem transfer_bounds (F : FrameModel k d) (w g r μ W X : ℝ) (Ψ : RPoly d)
    (hF : DataValid F w g r) (hW : 4 ≤ W) (hd : (d : ℝ) ≤ W)
    (he : 1.1 / w ≤ W) (hX : 0 ≤ X ∧ X ≤ W ^ 2)
    (hqn : SoS.coeffNorm1 (qConstraint Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2)) ≤ W ^ 5)
    (hhn : SoS.coeffNorm1
      (hConstraint Ψ (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)) ≤ W ^ 7)
    (t : ℝ) (hqt : 0 ≤ 12 * t ^ 2 ∧ 12 * t ^ 2 ≤ 1)
    (hht : 0 ≤ 513 * t ^ 2 / w ^ 2 ∧ 513 * t ^ 2 / w ^ 2 ≤ 4) :
    SoS.coeffNorm1 (qConstraint (psi F) (12 * t ^ 2)) +
        2 * SoS.coeffNorm1 (qConstraint Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2)) + 2 ≤ W ^ 64 ∧
      (SoS.coeffNorm1 (hConstraint (psi F) (513 * t ^ 2 / w ^ 2)) +
        2 * SoS.coeffNorm1
          (hConstraint Ψ (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2))) *
            (1 + d * X) ^ 8 + 2 ≤ W ^ 64 := by
  have hW1 : 1 ≤ W := by linarith only [hW]
  have hw := hF.1.1
  have hψ : SoS.coeffNorm1 (psi F) ≤ W ^ 7 := by
    calc
      _ ≤ 3 * (d : ℝ) ^ 4 * (1.1 / w) ^ 2 := psi_norm F w g r hF
      _ ≤ 3 * W ^ 4 * W ^ 2 := by gcongr
      _ = 3 * W ^ 6 := by ring
      _ ≤ W * W ^ 6 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = W ^ 7 := by ring
  have hψsq : SoS.coeffNorm1 (psi F) ^ 2 ≤ W ^ 14 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) hψ 2
  have hq : SoS.coeffNorm1 (qConstraint (psi F) (12 * t ^ 2)) ≤ W ^ 15 := by
    have ht : (12 * t ^ 2) ^ 2 ≤ 1 := pow_le_one₀ hqt.1 hqt.2
    have hfirst : (12 * t ^ 2) ^ 2 * (d : ℝ) ^ 4 ≤ W ^ 4 := by
      exact (mul_le_mul ht (pow_le_pow_left₀ (by positivity) hd 4)
        (by positivity) zero_le_one).trans_eq (one_mul _)
    calc
      _ ≤ (12 * t ^ 2) ^ 2 * (d : ℝ) ^ 4 + SoS.coeffNorm1 (psi F) ^ 2 / 9 :=
        norm_qConstraint _ _
      _ ≤ W ^ 4 + W ^ 14 := add_le_add hfirst
        ((div_le_self (by positivity) (by norm_num)).trans hψsq)
      _ ≤ 2 * W ^ 14 := by
        have hh := pow_le_pow_right₀ hW1 (by norm_num : 4 ≤ 14)
        linarith only [hh]
      _ ≤ W ^ 15 := by simpa using absorb W hW 2 1 14 (by norm_num)
  have hh : SoS.coeffNorm1 (hConstraint (psi F) (513 * t ^ 2 / w ^ 2)) ≤
      W ^ 18 := by
    have ht : |513 * t ^ 2 / w ^ 2| ≤ 4 := by rw [abs_of_nonneg hht.1]; exact hht.2
    calc
      _ ≤ |513 * t ^ 2 / w ^ 2| * (2 * (d : ℝ) ^ 4) +
          144 * SoS.coeffNorm1 (psi F) ^ 2 :=
        norm_hConstraint _ (IdentAux.psi_homogeneous F).totalDegree_le _
      _ ≤ 4 * (2 * W ^ 4) + 144 * W ^ 14 := by gcongr
      _ ≤ 152 * W ^ 14 := by
        have hh := pow_le_pow_right₀ hW1 (by norm_num : 4 ≤ 14)
        linarith only [hh]
      _ ≤ W ^ 18 := by
        simpa using absorb W hW 152 4 14 (by norm_num)
  constructor
  · calc
      _ ≤ W ^ 15 + 2 * W ^ 5 + 2 := by gcongr
      _ ≤ 4 * W ^ 15 := by
        have hp := pow_le_pow_right₀ hW1 (by norm_num : 5 ≤ 15)
        have hp1 : 2 ≤ W ^ 15 := (by linarith only [hW] : (2 : ℝ) ≤ W).trans
          (le_self_pow₀ hW1 (by norm_num))
        linarith only [hp, hp1]
      _ ≤ W ^ 16 := by simpa using absorb W hW 4 1 15 (by norm_num)
      _ ≤ W ^ 64 := pow_le_pow_right₀ hW1 (by norm_num)
  · have hsum : SoS.coeffNorm1 (hConstraint (psi F) (513 * t ^ 2 / w ^ 2)) +
        2 * SoS.coeffNorm1
          (hConstraint Ψ (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)) ≤ W ^ 19 := by
      calc
        _ ≤ W ^ 18 + 2 * W ^ 7 := by gcongr
        _ ≤ 3 * W ^ 18 := by
          have hp := pow_le_pow_right₀ hW1 (by norm_num : 7 ≤ 18)
          linarith only [hp]
        _ ≤ W ^ 19 := by simpa using absorb W hW 3 1 18 (by norm_num)
    have hbase : 1 + (d : ℝ) * X ≤ W ^ 4 := by
      calc
        _ ≤ 1 + W * W ^ 2 := by
          gcongr
          · exact hX.1
          · exact hX.2
        _ ≤ 2 * W ^ 3 := by nlinarith only [one_le_pow₀ hW1 (n := 3)]
        _ ≤ W ^ 4 := by simpa using absorb W hW 2 1 3 (by norm_num)
    calc
      _ ≤ W ^ 19 * (W ^ 4) ^ 8 + 2 := by
        gcongr
        exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hX.1)
      _ = W ^ 51 + 2 := by ring
      _ ≤ 4 * W ^ 51 := by linarith only [one_le_pow₀ hW1 (n := 51)]
      _ ≤ W ^ 52 := by simpa using absorb W hW 4 1 51 (by norm_num)
      _ ≤ W ^ 64 := pow_le_pow_right₀ hW1 (by norm_num)

theorem certificate_bound (W ε : ℝ) (hW : 4 ≤ W) :
    W ^ 24 * (1 + 3 * W ^ 64) + ε ≤ W ^ 200 + ε := by
  have hW1 : 1 ≤ W := by linarith only [hW]
  have hsum : 1 + 3 * W ^ 64 ≤ 4 * W ^ 64 := by
    linarith only [one_le_pow₀ hW1 (n := 64)]
  suffices hmain : W ^ 24 * (1 + 3 * W ^ 64) ≤ W ^ 200 by
    linarith only [hmain]
  calc
    _ ≤ W ^ 24 * (4 * W ^ 64) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * W ^ 88 := by ring
    _ ≤ W ^ 89 := by simpa using absorb W hW 4 1 88 (by norm_num)
    _ ≤ W ^ 200 := pow_le_pow_right₀ hW1 (by norm_num)

end

end ABBKS26.Centered.EmpiricalLedger
