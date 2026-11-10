module

public import ABBKS26.Centered.EmpiricalFeasibility

/-! Shared analytic preparation for the rounded empirical centered system. -/

@[expose] public section

namespace ABBKS26.Centered.EmpiricalComplement

open Common Matrix MvPolynomial Rounding
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

private theorem ball_degree (hd : 0 < d) : (1 - nsq : RPoly d).totalDegree = 2 := by
  classical
  let i : Fin d := ⟨0, hd⟩
  have hn : (nsq : RPoly d) ≠ 0 := by
    intro h
    have he := congrArg (eval (Pi.single i (1 : ℝ))) h
    simp [nsq, Pi.single_apply] at he
  have hdeg := IdentAux.nsq_homogeneous.totalDegree hn
  rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt, totalDegree_neg, hdeg]
  simp only [totalDegree_one, totalDegree_neg, hdeg]
  norm_num

theorem subst_ball (R : Mat d) (hR : Projection R) :
    subst (1 - R) (1 - nsq) = 1 - nsq + quad R := by
  have hP := DetRoundAux.projection_compl R hR
  have hn : subst (1 - R) nsq = nsq - quad R := by
    rw [IdentAux.subst_nsq, hP.1, hP.2, IdentAux.quad_sub, IdentAux.quad_one]
  change (aeval _) (1 - nsq) = _
  rw [map_sub, map_one]
  change 1 - subst (1 - R) nsq = _
  rw [hn]
  ring

theorem feasible_ball (R : Mat d) (hR : Projection R) :
    SoS.DerivesNq ball (1 - nsq : RPoly d).totalDegree
      (1 + SoS.coeffNorm1 (quad R)) 1 (subst (1 - R) (1 - nsq)) := by
  have hd : (quad R).totalDegree ≤ (1 - nsq : RPoly d).totalDegree := by
    by_cases h : d = 0
    · subst d
      simp [quad]
    · rw [ball_degree (Nat.pos_of_ne_zero h)]
      exact IdentAux.quad_degree R
  have hpsd : R.PosSemidef := by
    have hp := posSemidef_conjTranspose_mul_self R
    simpa only [conjTranspose_eq_transpose_of_trivial, hR.1, hR.2] using hp
  have hb : SoS.DerivesNq ball (1 - nsq : RPoly d).totalDegree 1 1 (1 - nsq) :=
    SoS.DerivesNq.of_mem (by simp [ball]) le_rfl le_rfl
  have hq : SoS.DerivesNq ball (1 - nsq : RPoly d).totalDegree
      (SoS.coeffNorm1 (quad R)) 1 (quad R) :=
    SoS.DerivesNq.ofIsSOS ball
      (by simpa only [SoS.IsSOS, SoS.toReal_real] using SoSKit.psd_quad R hpsd)
      hd le_rfl
  rw [subst_ball R hR]
  exact hb.add hq

theorem complement_entry (R : Mat d) (hR : Projection R) (i j : Fin d) :
    |(1 - R) i j| ≤ 2 := by
  have hb := IdentAux.projection_entry R hR i j
  have hi : |(1 : Mat d) i j| ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs <;> norm_num
  exact (abs_sub _ _).trans (by linarith only [hb, hi])

theorem subst_norm (R : Mat d) (hR : Projection R) (f : RPoly d)
    (hf : f.totalDegree ≤ 8) :
    SoS.coeffNorm1 (subst (1 - R) f) ≤
      SoS.coeffNorm1 f * (2 * (d + 1 : ℝ)) ^ 8 := by
  have hbase : 1 ≤ 2 * (d + 1 : ℝ) := by
    have hd := Nat.cast_nonneg (α := ℝ) d
    linarith only [hd]
  apply (SoS.coeffNorm1_aeval_le _ hbase ?_ f).trans
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbase hf) (SoS.coeffNorm1_nonneg f)
  · intro i
    exact (IdentAux.norm_lin (1 - R) 2 (complement_entry R hR) i).trans (by linarith)

theorem substV_norm (R : Mat d) (hR : Projection R) (f : BiPoly d)
    (hf : f.totalDegree ≤ 8) :
    SoS.coeffNorm1 (substV (1 - R) f) ≤
      SoS.coeffNorm1 f * (2 * (d + 1 : ℝ)) ^ 8 := by
  have hbase : 1 ≤ 2 * (d + 1 : ℝ) := by
    have hd := Nat.cast_nonneg (α := ℝ) d
    linarith only [hd]
  apply (SoS.coeffNorm1_aeval_le _ hbase ?_ f).trans
  · exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbase hf) (SoS.coeffNorm1_nonneg f)
  · intro i
    cases i with
    | inl i =>
      exact (SoS.coeffNorm1_X _).le.trans hbase
    | inr i =>
      have hl := IdentAux.norm_lin (1 - R) 2 (complement_entry R hR) i
      have hr : SoS.coeffNorm1 (liftV (lin ((1 - R) i))) ≤
          SoS.coeffNorm1 (lin ((1 - R) i)) := by
        simpa only [liftV, rename_eq_aeval, Function.comp_def, one_pow, mul_one] using
          SoS.coeffNorm1_aeval_le (fun j : Fin d ↦ X (Sum.inr j)) le_rfl
            (fun j ↦ (SoS.coeffNorm1_X (Sum.inr j)).le) (lin ((1 - R) i))
      exact (hr.trans hl).trans (by linarith)

theorem subst_degree (A : Mat d) (f : RPoly d) :
    (subst A f).totalDegree ≤ f.totalDegree := by
  simpa only [subst, mul_one] using
    SoS.totalDegree_aeval_le (fun i ↦ lin (A i)) (fun i ↦ IdentAux.lin_degree (A i)) f

theorem substV_degree (A : Mat d) (f : BiPoly d) :
    (substV A f).totalDegree ≤ f.totalDegree := by
  apply (SoS.totalDegree_aeval_le _ (e := 1) ?_ f).trans_eq (Nat.mul_one _)
  intro i
  cases i with
  | inl i => simp
  | inr i =>
    exact (totalDegree_rename_le _ _).trans (IdentAux.lin_degree _)

/-- The explicit multiplier pays for the ball and both substituted degree-eight
constraints; no solver output or external fuel enters this bound. -/
theorem feasible_system (Ψ : RPoly d) (εq εh C : ℝ) (hC : 0 ≤ C)
    (hΨ : Ψ.IsHomogeneous 4)
    (hqnorm : SoS.coeffNorm1 (qConstraint Ψ εq) ≤ C)
    (hhnorm : SoS.coeffNorm1 (hConstraint Ψ εh) ≤ C)
    (R : Mat d) (hR : Projection R)
    (hq : IsSumSq (subst (1 - R) (qConstraint Ψ εq)))
    (hh : IsSumSq (substV (1 - R) (hConstraint Ψ εh))) :
    (system Ψ εq εh).FeasibleComplement R
      (1 + (d : ℝ) ^ 2 + C * (2 * (d + 1 : ℝ)) ^ 8) := by
  have hqd : (qConstraint Ψ εq).totalDegree ≤ 8 := by
    apply IsHomogeneous.totalDegree_le
    exact ((IdentAux.nsq_homogeneous.pow 4).C_mul _).sub
      (by simpa only [Nat.reduceMul] using (hΨ.C_mul (1 / 3)).pow 2)
  have hhd := (IdentAux.hConstraint_homogeneous Ψ εh hΨ).totalDegree_le
  have hMq : SoS.coeffNorm1 (subst (1 - R) (qConstraint Ψ εq)) ≤
      1 + (d : ℝ) ^ 2 + C * (2 * (d + 1 : ℝ)) ^ 8 := by
    apply (subst_norm R hR _ hqd).trans
    have hb := mul_le_mul_of_nonneg_right hqnorm
      (by positivity : 0 ≤ (2 * (d + 1 : ℝ)) ^ 8)
    nlinarith only [hb, sq_nonneg (d : ℝ)]
  have hMh : SoS.coeffNorm1 (substV (1 - R) (hConstraint Ψ εh)) ≤
      1 + (d : ℝ) ^ 2 + C * (2 * (d + 1 : ℝ)) ^ 8 := by
    apply (substV_norm R hR _ hhd).trans
    have hb := mul_le_mul_of_nonneg_right hhnorm
      (by positivity : 0 ≤ (2 * (d + 1 : ℝ)) ^ 8)
    nlinarith only [hb, sq_nonneg (d : ℝ)]
  constructor
  · intro f hf
    change f ∈ [1 - nsq, qConstraint Ψ εq] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · apply (feasible_ball R hR).mono le_rfl
      have hnorm := IdentAux.norm_quad R 1 (IdentAux.projection_entry R hR)
      simp only [mul_one] at hnorm
      have hc : 0 ≤ C * (2 * (d + 1 : ℝ)) ^ 8 := by positivity
      linarith only [hnorm, hc]
    · rw [List.mem_singleton.mp hf]
      exact SoS.DerivesNq.ofIsSOS ball
        (by simpa only [SoS.IsSOS, SoS.toReal_real] using hq) (subst_degree _ _) hMq
  · intro f hf
    rw [List.mem_singleton.mp hf]
    exact SoS.DerivesNq.ofIsSOS [1 - liftV nsq]
      (by simpa only [SoS.IsSOS, SoS.toReal_real] using hh) (substV_degree _ _) hMh

end

end ABBKS26.Centered.EmpiricalComplement
