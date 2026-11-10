module

public import ABBKS26.Centered.Ident

/-! Sum-of-squares bounds for a linearly substituted centered system. -/

@[expose] public section

namespace ABBKS26.Centered.FeasibleAux

noncomputable section

open Common Matrix MvPolynomial
open scoped BigOperators

variable {k d : ℕ}

private theorem gram_qform (A : Mat d) (v : Vec d) :
    qform (Aᵀ * A) v = sqnorm (A *ᵥ v) := by
  rw [qform, sqnorm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

private theorem energy (E P : Mat d) (a : ℝ)
    (h : ∀ v, sqnorm (E *ᵥ (P *ᵥ v)) ≤ a ^ 2 * sqnorm (P *ᵥ v)) :
    IsSumSq (C (a ^ 2) * subst P nsq - subst (E * P) nsq) := by
  have hp : (a ^ 2 • (Pᵀ * P) - (E * P)ᵀ * (E * P)).PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · apply IsHermitian.sub
      · exact (posSemidef_conjTranspose_mul_self P |>.smul (sq_nonneg a)).isHermitian
      · exact (posSemidef_conjTranspose_mul_self (E * P)).isHermitian
    · intro v
      change 0 ≤ qform (a ^ 2 • (Pᵀ * P) - (E * P)ᵀ * (E * P)) v
      simp only [qform, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
        smul_eq_mul]
      change 0 ≤ a ^ 2 * qform (Pᵀ * P) v - qform ((E * P)ᵀ * (E * P)) v
      rw [gram_qform, gram_qform, ← mulVec_mulVec]
      exact sub_nonneg.mpr (h v)
  simpa only [IdentAux.quad_sub, IdentAux.quad_smul, IdentAux.subst_nsq] using
    SoSKit.psd_quad _ hp

private theorem lin_mul (E P : Mat d) (i : Fin d) :
    lin ((E * P) i) = ∑ j, C (E i j) * lin (P j) := by
  simp only [lin, Matrix.mul_apply, map_sum, C_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem subst_quad_dot (E P : Mat d) :
    subst P (quad E) = ∑ i, lin (P i) * lin ((E * P) i) := by
  simp only [subst, quad, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
    lin_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem quadratic_small (E P : Mat d) (a : ℝ)
    (h : ∀ v, sqnorm (E *ᵥ (P *ᵥ v)) ≤ a ^ 2 * sqnorm (P *ᵥ v)) :
    IsSumSq (C (a ^ 2) * subst P nsq ^ 2 - subst P (quad E) ^ 2) := by
  have he := energy E P a h
  have hN : IsSumSq (subst P nsq) :=
    SoS.isSumSq_map (aeval (fun i ↦ lin (P i))) (IsSumSq.sum_sq _ _)
  have hl := SoS.isSumSq_lagrange Finset.univ
    (fun i ↦ lin (P i)) (fun i ↦ lin ((E * P) i))
  have hn (A : Mat d) : (∑ i, lin (A i) ^ 2) = subst A nsq := by
    simp only [subst, nsq, map_sum, map_pow, aeval_X]
  rw [hn, hn, ← subst_quad_dot] at hl
  convert (hN.mul he).add hl using 1
  ring

private theorem sos_prod {σ : Type*} (A B X Y : MvPolynomial σ ℝ)
    (hA : IsSumSq A) (hY : IsSumSq Y) (hX : IsSumSq (A - X))
    (hB : IsSumSq (B - Y)) : IsSumSq (A * B - X * Y) := by
  convert (hA.mul hB).add (hY.mul hX) using 1
  ring

private theorem sos_square {σ : Type*} (X Y : MvPolynomial σ ℝ)
    (hX : IsSumSq X) (hY : IsSumSq Y) (h : IsSumSq (Y - X)) :
    IsSumSq (Y ^ 2 - X ^ 2) := by
  convert (hY.add hX).mul h using 1
  ring

private theorem average_gap {σ ι : Type*} [Fintype ι] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (B : MvPolynomial σ ℝ) (p : ι → MvPolynomial σ ℝ)
    (hp : ∀ i, IsSumSq (B - p i)) : IsSumSq (B - ∑ i, C (w i) * p i) := by
  have h : IsSumSq (∑ i, C (w i) * (B - p i)) := IsSumSq.sum (fun i _ ↦
    SoS.isSumSq_C_mul (hw i) (hp i))
  simpa only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
    hsum, C_1, one_mul] using h

private theorem average_squares {σ ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (p : ι → MvPolynomial σ ℝ) :
    IsSumSq (∑ i, C (w i) * p i ^ 2) := by
  exact IsSumSq.sum fun i _ ↦ SoS.isSumSq_C_mul (hw i) (SoS.isSumSq_sq _)

private theorem weighted_lagrange {σ ι : Type*} [Fintype ι]
    (w : ι → ℝ) (a b : ι → MvPolynomial σ ℝ) (hw : ∀ i, 0 ≤ w i) :
    IsSumSq ((∑ i, C (w i) * a i ^ 2) * (∑ i, C (w i) * b i ^ 2) -
      (∑ i, C (w i) * a i * b i) ^ 2) := by
  have hs (i : ι) : (C (Real.sqrt (w i)) : MvPolynomial σ ℝ) ^ 2 = C (w i) := by
    rw [← C_pow, Real.sq_sqrt (hw i)]
  have hm (i : ι) : (C (Real.sqrt (w i)) * a i) *
      (C (Real.sqrt (w i)) * b i) = C (w i) * a i * b i := by
    rw [mul_mul_mul_comm, ← pow_two, hs, mul_assoc]
  have h := SoS.isSumSq_lagrange Finset.univ
    (fun i ↦ C (Real.sqrt (w i)) * a i) (fun i ↦ C (Real.sqrt (w i)) * b i)
  simpa only [mul_pow, hs, hm] using h

private theorem q_bound (F : FrameModel k d) (w γ rF a : ℝ) (P : Mat d)
    (hF : DataValid F w γ rF)
    (hsmall : ∀ i v, sqnorm (deviation F i *ᵥ (P *ᵥ v)) ≤ a ^ 2 * sqnorm (P *ᵥ v)) :
    IsSumSq (subst P (C (1 / 3) * psi F)) ∧
      IsSumSq (C (a ^ 2) * subst P nsq ^ 2 - subst P (C (1 / 3) * psi F)) := by
  have hw (i : Fin k) : 0 ≤ F.weight i := hF.1.1.le.trans (hF.1.2.1 i)
  have he : subst P (C (1 / 3) * psi F) =
      ∑ i, C (F.weight i) * subst P (quad (deviation F i)) ^ 2 := by
    rw [IdentAux.quartic_third F hF.1.2.2.1]
    simp only [subst, map_sum, map_mul, map_pow, aeval_C, algebraMap_eq]
  rw [he]
  exact ⟨average_squares _ hw _, average_gap _ hw hF.1.2.2.1 _ _
    (fun i ↦ quadratic_small _ P a (hsmall i))⟩

/-- The substituted quartic constraint has a sum-of-squares certificate. -/
theorem q_feasible (F : FrameModel k d) (w γ rF a εq : ℝ) (P : Mat d)
    (hF : DataValid F w γ rF)
    (hsmall : ∀ i v, sqnorm (deviation F i *ᵥ (P *ᵥ v)) ≤ a ^ 2 * sqnorm (P *ᵥ v))
    (hq : a ^ 2 ≤ εq) : IsSumSq (subst P (qConstraint (psi F) εq)) := by
  obtain ⟨hQ, hgap⟩ := q_bound F w γ rF a P hF hsmall
  have hN : IsSumSq (subst P nsq ^ 2) := SoS.isSumSq_sq _
  have hslack := SoS.isSumSq_C_mul (sub_nonneg.mpr hq) hN
  have hgap' : IsSumSq (C εq * subst P nsq ^ 2 -
      subst P (C (1 / 3) * psi F)) := by
    convert hslack.add hgap using 1
    rw [C_sub]
    ring
  have hpow := sos_square _ _ hQ
    (SoS.isSumSq_C_mul ((sq_nonneg a).trans hq) hN) hgap'
  convert hpow using 1
  simp only [qConstraint, subst, map_sub, map_pow, map_mul, aeval_C,
    algebraMap_eq, mul_pow]
  ring

private def bilin (E P : Mat d) : BiPoly d :=
  ∑ i, X (Sum.inl i) * liftV (lin ((E * P) i))

private theorem bilin_bound (E P : Mat d) (a : ℝ)
    (h : ∀ v, sqnorm (E *ᵥ (P *ᵥ v)) ≤ a ^ 2 * sqnorm (P *ᵥ v)) :
    IsSumSq (C (a ^ 2) * liftU nsq * liftV (subst P nsq) - bilin E P ^ 2) := by
  have he := SoS.isSumSq_map (rename (Sum.inr : Fin d → Fin d ⊕ Fin d))
    (energy E P a h)
  have hU : IsSumSq (liftU (nsq : RPoly d)) :=
    SoS.isSumSq_map (rename Sum.inl) (IsSumSq.sum_sq _ _)
  have hl := SoS.isSumSq_lagrange Finset.univ
    (fun i ↦ X (Sum.inl i)) (fun i ↦ liftV (lin ((E * P) i)))
  have hn : (∑ i, liftV (lin ((E * P) i)) ^ 2) =
      liftV (subst (E * P) nsq) := by
    simp only [liftV, subst, nsq, map_sum, map_pow, aeval_X]
  rw [hn] at hl
  have hu : (∑ i : Fin d, (X (Sum.inl i) : BiPoly d) ^ 2) = liftU nsq := by
    simp only [liftU, nsq, map_sum, map_pow, rename_X]
  rw [hu] at hl
  change IsSumSq (liftU nsq * liftV (subst (E * P) nsq) - bilin E P ^ 2) at hl
  change IsSumSq (liftV (C (a ^ 2) * subst P nsq - subst (E * P) nsq)) at he
  simp only [liftV, map_sub, map_mul, rename_C] at he
  convert (hU.mul he).add hl using 1
  dsimp only [liftV]
  ring

private theorem substV_liftV (P : Mat d) (p : RPoly d) :
    substV P (liftV p) = liftV (subst P p) := by
  simp only [substV, liftV, aeval_rename, Function.comp_def, Sum.elim_inr,
    subst, ← comp_aeval_apply]

private theorem substV_liftU (P : Mat d) (p : RPoly d) :
    substV P (liftU p) = liftU p := by
  simp only [substV, liftU, aeval_rename, Function.comp_def, Sum.elim_inl]
  rw [rename_eq_aeval]
  rfl

private theorem substV_cross (E P : Mat d) :
    substV P (∑ a, ∑ b, C (E a b) * X (Sum.inl a) * X (Sum.inr b)) =
      bilin E P := by
  simp only [substV, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
    Sum.elim_inl, Sum.elim_inr, bilin, lin_mul, liftV, map_sum, map_mul, rename_C,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem hessian_subst (F : FrameModel k d) (P : Mat d)
    (hsum : ∑ i, F.weight i = 1) (hs : ∀ i, (F.cov i).IsHermitian) :
    substV P (4 * polarize (psi F)) =
      8 * (∑ i, C (F.weight i) * bilin (deviation F i) P ^ 2) +
      4 * ∑ i, C (F.weight i) * liftV (subst P (quad (deviation F i))) *
        liftU (quad (deviation F i)) := by
  let f := Sum.elim (fun i : Fin d ↦ X (Sum.inl i) : Fin d → BiPoly d)
    (fun i ↦ liftV (lin (P i)))
  have ht := congrArg (aeval f) (hessian_identity F hsum hs)
  simp only [map_add, map_mul, map_sum, map_pow, _root_.map_ofNat, aeval_C,
    algebraMap_eq, aeval_X, f, Sum.elim_inl, Sum.elim_inr] at ht
  have hv (i : Fin k) : aeval f (liftV (quad (deviation F i))) =
      liftV (subst P (quad (deviation F i))) := substV_liftV P _
  have hu (i : Fin k) : aeval f (liftU (quad (deviation F i))) =
      liftU (quad (deviation F i)) := substV_liftU P _
  have hc (i : Fin k) :
      (∑ a, ∑ b, C (deviation F i a b) * X (Sum.inl a) * liftV (lin (P b))) =
        bilin (deviation F i) P := by
    simpa only [substV, map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X,
      Sum.elim_inl, Sum.elim_inr] using substV_cross (deviation F i) P
  dsimp only [f] at hv hu
  simp only [hv, hu, hc] at ht
  simpa only [substV, map_mul, _root_.map_ofNat, f] using ht

private theorem hessian_bound {σ : Type*} (N M X Y : MvPolynomial σ ℝ)
    (a e : ℝ) (hN : IsSumSq N) (hM : IsSumSq M) (hX : IsSumSq X)
    (hx : IsSumSq (C (a ^ 2) * N * M - X))
    (hy : IsSumSq (C (a ^ 2 * e ^ 2) * M ^ 2 * N ^ 2 - Y ^ 2)) :
    IsSumSq (C (64 * a ^ 4 + 16 * e ^ 2 * a ^ 2) * (M ^ 4 + N ^ 4) -
      (8 * X + 4 * Y) ^ 2) := by
  have hx2 := sos_square X (C (a ^ 2) * N * M) hX
    ((SoS.isSumSq_C_mul (sq_nonneg a) hN).mul hM) hx
  have hs := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 128) hx2
  have ht := SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 32) hy
  have hc : 0 ≤ 64 * a ^ 4 + 16 * e ^ 2 * a ^ 2 := by positivity
  have hm := SoS.isSumSq_C_mul hc (SoS.isSumSq_sq (M ^ 2 - N ^ 2))
  convert ((hs.add ht).add (SoS.isSumSq_sq (8 * X - 4 * Y))).add hm using 1
  simp only [C_add, C_mul, C_pow, map_ofNat]
  ring

/-- The substituted Hessian constraint has a sum-of-squares certificate. -/
theorem h_feasible (F : FrameModel k d) (w γ rF a εh : ℝ) (P : Mat d)
    (hF : DataValid F w γ rF)
    (hsmall : ∀ i v, sqnorm (deviation F i *ᵥ (P *ᵥ v)) ≤ a ^ 2 * sqnorm (P *ᵥ v))
    (hh : 64 * a ^ 4 + 16 * (1.1 / w) ^ 2 * a ^ 2 ≤ εh) :
    IsSumSq (substV P (hConstraint (psi F) εh)) := by
  let N : BiPoly d := liftU nsq
  let M : BiPoly d := liftV (subst P nsq)
  let A : Fin k → BiPoly d := fun i ↦ liftV (subst P (quad (deviation F i)))
  let B : Fin k → BiPoly d := fun i ↦ liftU (quad (deviation F i))
  let X : BiPoly d := ∑ i, C (F.weight i) * bilin (deviation F i) P ^ 2
  let Y : BiPoly d := ∑ i, C (F.weight i) * A i * B i
  let QA : BiPoly d := ∑ i, C (F.weight i) * A i ^ 2
  let QB : BiPoly d := ∑ i, C (F.weight i) * B i ^ 2
  let e : ℝ := 1.1 / w
  have hw (i : Fin k) : 0 ≤ F.weight i := hF.1.1.le.trans (hF.1.2.1 i)
  have hN : IsSumSq N := SoS.isSumSq_map (rename Sum.inl) (IsSumSq.sum_sq _ _)
  have hM : IsSumSq M := SoS.isSumSq_map (rename Sum.inr)
    (SoS.isSumSq_map (aeval (fun i ↦ lin (P i))) (IsSumSq.sum_sq _ _))
  have hX : IsSumSq X := average_squares _ hw _
  have hQB : IsSumSq QB := average_squares _ hw _
  have hx : IsSumSq (C (a ^ 2) * N * M - X) :=
    average_gap _ hw hF.1.2.2.1 _ _ (fun i ↦ bilin_bound _ P a (hsmall i))
  have ha : IsSumSq (C (a ^ 2) * M ^ 2 - QA) := by
    apply average_gap _ hw hF.1.2.2.1
    intro i
    have h := SoS.isSumSq_map (rename (Sum.inr : Fin d → Fin d ⊕ Fin d))
      (quadratic_small (deviation F i) P a (hsmall i))
    simpa only [M, A, liftV, map_sub, map_mul, map_pow, rename_C] using h
  have hb : IsSumSq (C (e ^ 2) * N ^ 2 - QB) := by
    apply average_gap _ hw hF.1.2.2.1
    intro i
    have h := SoS.isSumSq_map (rename (Sum.inl : Fin d → Fin d ⊕ Fin d))
      (SoSKit.quad_square (deviation F i)
        (IdentAux.deviation_symm F (fun j ↦ (hF.1.2.2.2 j).isHermitian) i)
        e (div_nonneg (by norm_num) hF.1.1.le) ((deviation_bound F w γ rF hF).2 i))
    simpa only [N, B, liftU, map_sub, map_mul, map_pow, rename_C] using h
  have hy : IsSumSq (C (a ^ 2 * e ^ 2) * M ^ 2 * N ^ 2 - Y ^ 2) := by
    have hp := sos_prod (C (a ^ 2) * M ^ 2) (C (e ^ 2) * N ^ 2) QA QB
      (SoS.isSumSq_C_mul (sq_nonneg a) (SoS.isSumSq_sq _)) hQB ha hb
    have hl := weighted_lagrange F.weight A B hw
    convert hp.add hl using 1
    simp only [C_mul]
    dsimp only [QA, QB, Y]
    ring
  have hbound := hessian_bound N M X Y a e hN hM hX hx hy
  have hslack := SoS.isSumSq_C_mul (sub_nonneg.mpr hh)
    ((SoS.isSumSq_sq (M ^ 2)).add (SoS.isSumSq_sq (N ^ 2)))
  have heq : substV P (hConstraint (psi F) εh) =
      C εh * (M ^ 4 + N ^ 4) - (8 * X + 4 * Y) ^ 2 := by
    have hv := substV_liftV P (nsq : RPoly d)
    have hu := substV_liftU P (nsq : RPoly d)
    have hi := hessian_subst F P hF.1.2.2.1 (fun i ↦ (hF.1.2.2.2 i).isHermitian)
    change (aeval _) (C εh * (liftV nsq ^ 4 + liftU nsq ^ 4) -
      (4 * polarize (psi F)) ^ 2) = _
    simp only [map_sub, map_mul, map_add, map_pow, aeval_C, algebraMap_eq,
      _root_.map_ofNat]
    change C εh * (substV P (liftV nsq) ^ 4 + substV P (liftU nsq) ^ 4) -
      (4 * substV P (polarize (psi F))) ^ 2 = _
    have hi' : 4 * substV P (polarize (psi F)) = 8 * X + 4 * Y := by
      simpa only [substV, map_mul, _root_.map_ofNat] using hi
    rw [hv, hu, hi']
  rw [heq]
  convert hslack.add hbound using 1
  simp only [C_sub]
  dsimp only [e] at *
  ring

end

end ABBKS26.Centered.FeasibleAux
