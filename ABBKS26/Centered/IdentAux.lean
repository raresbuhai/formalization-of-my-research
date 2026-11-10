module

public import ABBKS26.Centered.Transfer

/-! Elementary matrix and polynomial certificates for centered identifiability. -/

@[expose] public section

namespace ABBKS26.Centered.IdentAux

noncomputable section

open Common MvPolynomial Matrix
open scoped BigOperators

variable {k d : ℕ}

theorem quad_sub (A B : Mat d) : quad (A - B) = quad A - quad B := by
  simp [quad, C_sub, sub_mul, Finset.sum_sub_distrib]

theorem quad_smul (c : ℝ) (A : Mat d) : quad (c • A) = C c * quad A := by
  simp [quad, C_mul, Finset.mul_sum, mul_assoc, smul_eq_mul]

theorem quad_one : quad (1 : Mat d) = nsq := by
  simp [quad, nsq, Matrix.one_apply, pow_two, apply_ite, ite_mul]

theorem subst_nsq (A : Mat d) : subst A nsq = quad (Aᵀ * A) := by
  simp only [subst, nsq, map_sum, map_mul, aeval_X, lin, pow_two,
    Finset.sum_mul_sum, quad, Matrix.mul_apply, Matrix.transpose_apply, map_sum]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem deviation_symm (F : FrameModel k d) (h : ∀ i, (F.cov i).IsHermitian)
    (i : Fin k) : (deviation F i)ᵀ = deviation F i := by
  have hs (j : Fin k) : (F.cov j)ᵀ = F.cov j := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using h j
  simp only [deviation, averageCov, transpose_sub, transpose_sum, transpose_smul, hs]

theorem eigenvalue_bound (E : Mat d) (hE : E.IsHermitian) (e : ℝ)
    (hb : ∀ v, |qform E v| ≤ e * sqnorm v) (j : Fin d) :
    |hE.eigenvalues j| ≤ e := by
  have hv : sqnorm (hE.eigenvectorBasis j : Vec d) = 1 := by
    rw [← Rounding.DetRoundAux.euclidean_sqnorm]
    simp only [WithLp.toLp_ofLp, hE.eigenvectorBasis.orthonormal.1 j, one_pow]
  have hq : qform E (hE.eigenvectorBasis j) = hE.eigenvalues j := by
    simpa only [qform, RCLike.re_to_real, star_trivial] using
      (hE.eigenvalues_eq j).symm
  simpa only [hv, hq, mul_one] using hb (hE.eigenvectorBasis j)

theorem operator_square (E : Mat d) (hs : Eᵀ = E) (e : ℝ) (he : 0 ≤ e)
    (hb : ∀ v, |qform E v| ≤ e * sqnorm v) :
    (e ^ 2 • (1 : Mat d) - E * E).PosSemidef := by
  have hE : E.IsHermitian := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hs
  let U := hE.eigenvectorUnitary
  let D : Mat d := diagonal hE.eigenvalues
  have hD : (e ^ 2 • (1 : Mat d) - D * D).PosSemidef := by
    have hd : e ^ 2 • (1 : Mat d) - D * D =
        diagonal (fun j ↦ e ^ 2 - hE.eigenvalues j ^ 2) := by
      ext a b
      by_cases hab : a = b
      · subst b; simp [D, pow_two]
      · simp [D, hab]
    rw [hd]
    apply posSemidef_diagonal_iff.mpr
    intro j
    apply sub_nonneg.mpr
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) he).mpr (eigenvalue_bound E hE e hb j)
  let φ : Mat d ≃⋆ₐ[ℝ] Mat d := Unitary.conjStarAlgAut ℝ _ U
  have hspec : φ D = E := by
    simpa only [φ, D, RCLike.ofReal_real_eq_id, Function.id_comp] using
      hE.spectral_theorem.symm
  have hid : φ (e ^ 2 • (1 : Mat d) - D * D) = e ^ 2 • 1 - E * E := by
    rw [map_sub, map_mul, map_smul, map_one, hspec]
  rw [← hid]
  exact hD.mul_mul_conjTranspose_same (U : Mat d)

theorem energy_bound (E : Mat d) (hs : Eᵀ = E) (e : ℝ) (he : 0 ≤ e)
    (hb : ∀ v, |qform E v| ≤ e * sqnorm v) :
    IsSumSq (C (e ^ 2) * nsq - quad (E * E)) := by
  simpa only [quad_sub, quad_smul, quad_one] using
    SoSKit.psd_quad _ (operator_square E hs e he hb)

theorem entry_bound (E : Mat d) (hs : Eᵀ = E) (e : ℝ) (he : 0 ≤ e)
    (hb : ∀ v, |qform E v| ≤ e * sqnorm v) (i j : Fin d) : |E i j| ≤ e := by
  have hp := (operator_square E hs e he hb).dotProduct_mulVec_nonneg
    (Pi.single j 1)
  have hnorm : sqnorm (E *ᵥ Pi.single j 1) ≤ e ^ 2 := by
    have hid : sqnorm (E *ᵥ Pi.single j 1) =
        qform (E * E) (Pi.single j 1) := by
      rw [sqnorm, qform, dotProduct_mulVec, ← hs, vecMul_transpose]
      rw [dotProduct_comm, mulVec_mulVec, hs]
    rw [hid]
    simpa [qform, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      dotProduct_single, star_trivial] using hp
  have hi : (E *ᵥ Pi.single j 1) i ^ 2 ≤ e ^ 2 := by
    refine le_trans ?_ hnorm
    simpa only [sqnorm, dotProduct, ← pow_two] using
      Finset.single_le_sum (fun a _ ↦ sq_nonneg ((E *ᵥ Pi.single j 1) a))
        (Finset.mem_univ i)
  simp only [mulVec_single_one, Matrix.col_apply] at hi
  exact (sq_le_sq₀ (abs_nonneg _) he).mp (by simpa only [sq_abs] using hi)

/-- The algebraic part of EV, before dehomogenization and taking a fourth root. -/
theorem raw_certificate (X q B T s : RPoly d) (w wi e εq εh : ℝ)
    (hw : 0 < w) (hwi : w ≤ wi) (hq : 0 < εq)
    (hh : εh ≤ 16 * w ^ 2) (hQ : IsSumSq q)
    (hS : IsSumSq s) (hsi : IsSumSq (s - C wi * X ^ 2))
    (hB : IsSumSq (C (e ^ 6) * nsq ^ 2 - B))
    (hT : IsSumSq (q * B - T ^ 2)) :
    IsSumSq (C (2 * εh + 32 * e ^ 6 * εq) * nsq ^ 4 -
      C (32 * w ^ 2) * X ^ 4 -
      2 * (C εh * (nsq ^ 4 + X ^ 4) - (8 * s + 4 * T) ^ 2) -
      C (16 * e ^ 6 / εq) * (C (εq ^ 2) * nsq ^ 4 - q ^ 2)) := by
  have hwi0 : 0 ≤ wi := hw.le.trans hwi
  have htop := SoSKit.powers (C wi * X ^ 2) s
    (SoS.isSumSq_C_mul hwi0 (SoS.isSumSq_sq X)) hS hsi 2
  have hcs := (hQ.mul hB).add hT
  have hslack : 0 ≤ 64 * wi ^ 2 - 2 * εh - 32 * w ^ 2 := by
    nlinarith [sq_le_sq₀ hw.le hwi0 |>.mpr hwi]
  have h := (((SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 64) htop).add
    (SoS.isSumSq_sq (8 * s + 8 * T))).add
    (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 32) hcs)).add
    (SoS.isSumSq_C_mul (show 0 ≤ 16 * e ^ 6 / εq by positivity)
      (SoS.isSumSq_sq (C εq * nsq ^ 2 - q)))
  have hfour : IsSumSq (X ^ 4) := by
    convert SoS.isSumSq_sq (X ^ 2) using 1
    ring
  have ht := h.add (SoS.isSumSq_C_mul hslack hfour)
  have hc : (C (16 * e ^ 6 / εq) : RPoly d) * C εq = C (16 * e ^ 6) := by
    rw [← C_mul, div_mul_cancel₀ _ hq.ne']
  simp only [C_mul, C_pow, map_ofNat] at hc
  convert ht using 1
  simp only [C_add, C_sub, C_mul, C_pow, map_ofNat]
  linear_combination -(2 * C εq * nsq ^ 4 - 2 * nsq ^ 2 * q) * hc

theorem inst_liftV (A : Mat d) (p : RPoly d) : inst (liftV p) A = p := by
  simp only [inst, liftV, aeval_rename, Function.comp_def, Sum.elim_inr,
    aeval_X_left_apply]

theorem inst_liftU (A : Mat d) (p : RPoly d) : inst (liftU p) A = subst A p := by
  simp only [inst, liftU, subst, aeval_rename, Function.comp_def, Sum.elim_inl]


theorem cross_self (A : Mat d) (hs : Aᵀ = A) :
    (∑ a, ∑ b, C (A a b) * lin (A a) * X b) = quad (A * A) := by
  have hx : quad (A * A) = subst A nsq := by rw [subst_nsq, hs]
  rw [hx]
  simp only [subst, nsq, map_sum, map_pow, aeval_X]
  simp only [lin, pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem quartic_third (F : FrameModel k d) (hsum : ∑ j, F.weight j = 1) :
    C (1 / 3) * psi F = ∑ j, C (F.weight j) * quad (deviation F j) ^ 2 := by
  rw [quartic_identity F hsum]
  have hc : (C (1 / 3) : RPoly d) * 3 = 1 := by
    rw [← map_ofNat C 3, ← C_mul]; norm_num
  rw [← mul_assoc, hc, one_mul]

theorem weighted_sum_sos {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → RPoly d) (hw : ∀ j, 0 ≤ w j) :
    IsSumSq (∑ j, C (w j) * p j ^ 2) := by
  exact IsSumSq.sum fun j _ ↦ SoS.isSumSq_C_mul (hw j) (SoS.isSumSq_sq _)

theorem weighted_term_gap {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → RPoly d) (hw : ∀ j, 0 ≤ w j) (i : ι) :
    IsSumSq ((∑ j, C (w j) * p j ^ 2) - C (w i) * p i ^ 2) := by
  classical
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_sub_cancel_right]
  exact IsSumSq.sum fun j _ ↦ SoS.isSumSq_C_mul (hw j) (SoS.isSumSq_sq _)

theorem substituted_square_bound (E A : Mat d) (hs : Eᵀ = E) (ha : Aᵀ = A)
    (e : ℝ) (he : 0 ≤ e) (hE : ∀ v, |qform E v| ≤ e * sqnorm v)
    (hA : ∀ v, |qform A v| ≤ e * sqnorm v) :
    IsSumSq (C (e ^ 6) * nsq ^ 2 - (subst E (quad A)) ^ 2) := by
  have hX : IsSumSq (quad (E * E)) := by
    apply SoSKit.psd_quad
    simpa only [conjTranspose_eq_transpose_of_trivial, hs] using
      posSemidef_conjTranspose_mul_self E
  have hN : IsSumSq (nsq : RPoly d) := IsSumSq.sum_sq _ _
  have hpow := SoSKit.powers (quad (E * E)) (C (e ^ 2) * nsq) hX
    (SoS.isSumSq_C_mul (sq_nonneg e) hN) (energy_bound E hs e he hE) 2
  have hsub := SoS.isSumSq_map (aeval (fun j ↦ lin (E j)))
    (SoSKit.quad_square A ha e he hA)
  change IsSumSq (subst E (C (e ^ 2) * nsq ^ 2 - quad A ^ 2)) at hsub
  simp only [subst, map_sub, map_mul, map_pow, aeval_C, algebraMap_eq] at hsub
  simp only [← C_pow] at hsub
  change IsSumSq (C (e ^ 2) * (subst E nsq) ^ 2 - (subst E (quad A)) ^ 2)
    at hsub
  rw [subst_nsq, hs] at hsub
  convert (SoS.isSumSq_C_mul (sq_nonneg e) hpow).add hsub using 1
  simp only [C_pow]
  ring

theorem hessian_instance (F : FrameModel k d) (hsum : ∑ j, F.weight j = 1)
    (hs : ∀ j, (F.cov j).IsHermitian) (E : Mat d) :
    inst (4 * polarize (psi F)) E =
      8 * (∑ j, C (F.weight j) *
        (∑ x, ∑ y, C (deviation F j x y) * lin (E x) * X y) ^ 2) +
      4 * ∑ j, C (F.weight j) * quad (deviation F j) *
        subst E (quad (deviation F j)) := by
  have ht := congrArg (aeval (Sum.elim (fun x ↦ lin (E x)) X))
    (hessian_identity F hsum hs)
  simp only [map_add, map_mul, map_sum, map_pow, map_ofNat, aeval_C,
    algebraMap_eq, aeval_X, Sum.elim_inl, Sum.elim_inr] at ht
  have hv (j : Fin k) :
      (aeval (Sum.elim (fun x ↦ lin (E x)) X)) (liftV (quad (deviation F j))) =
        quad (deviation F j) := inst_liftV E _
  have hu (j : Fin k) :
      (aeval (Sum.elim (fun x ↦ lin (E x)) X)) (liftU (quad (deviation F j))) =
        subst E (quad (deviation F j)) := inst_liftU E _
  simp only [hv, hu] at ht
  simpa only [inst, map_mul, map_ofNat] using ht

theorem constraint_instance (p : RPoly d) (εh : ℝ) (E : Mat d) (hs : Eᵀ = E) :
    inst (hConstraint p εh) E =
      C εh * (nsq ^ 4 + quad (E * E) ^ 4) - inst (4 * polarize p) E ^ 2 := by
  have hv := inst_liftV E (nsq : RPoly d)
  have hu := inst_liftU E (nsq : RPoly d)
  rw [subst_nsq, hs] at hu
  change (aeval (Sum.elim (fun x ↦ lin (E x)) X))
    (C εh * (liftV nsq ^ 4 + liftU nsq ^ 4) - (4 * polarize p) ^ 2) = _
  rw [map_sub, map_mul, map_add, map_pow, map_pow, map_pow, aeval_C]
  change C εh * (inst (liftV nsq) E ^ 4 + inst (liftU nsq) E ^ 4) -
    inst (4 * polarize p) E ^ 2 = _
  rw [hv, hu]

theorem centered_raw_certificate (F : FrameModel k d) (w γ rF εq εh : ℝ)
    (i : Fin k) (hF : DataValid F w γ rF) (hq : 0 < εq)
    (hh : εh ≤ 16 * w ^ 2) :
    IsSumSq (C (2 * εh + 32 * (1.1 / w) ^ 6 * εq) * nsq ^ 4 -
      C (32 * w ^ 2) * quad (deviation F i * deviation F i) ^ 4 -
      2 * inst (hConstraint (psi F) εh) (deviation F i) -
      C (16 * (1.1 / w) ^ 6 / εq) * qConstraint (psi F) εq) := by
  let E := deviation F i
  let a : Fin k → RPoly d := fun j ↦ quad (deviation F j)
  let b : Fin k → RPoly d := fun j ↦ subst E (a j)
  let c : Fin k → RPoly d := fun j ↦
    ∑ x, ∑ y, C (deviation F j x y) * lin (E x) * X y
  let q := ∑ j, C (F.weight j) * a j ^ 2
  let B := ∑ j, C (F.weight j) * b j ^ 2
  let T := ∑ j, C (F.weight j) * a j * b j
  let s := ∑ j, C (F.weight j) * c j ^ 2
  have hw (j : Fin k) : 0 ≤ F.weight j := hF.1.1.le.trans (hF.1.2.1 j)
  have hs (j : Fin k) : (deviation F j)ᵀ = deviation F j :=
    deviation_symm F (fun j ↦ (hF.1.2.2.2 j).isHermitian) j
  have he : 0 ≤ 1.1 / w := by have := hF.1.1; positivity
  have hb (j : Fin k) := (deviation_bound F w γ rF hF).2 j
  have hB : IsSumSq (C ((1.1 / w) ^ 6) * nsq ^ 2 - B) := by
    have ht : IsSumSq (∑ j, C (F.weight j) *
        (C ((1.1 / w) ^ 6) * nsq ^ 2 - b j ^ 2)) :=
      IsSumSq.sum fun j _ ↦
      SoS.isSumSq_C_mul (hw j)
        (substituted_square_bound E (deviation F j) (hs i) (hs j)
          (1.1 / w) he (hb i) (hb j))
    simpa only [B, b, a, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← map_sum, hF.1.2.2.1, map_one, one_mul] using ht
  have hci : c i = quad (E * E) := cross_self E (hs i)
  have hsi : IsSumSq (s - C (F.weight i) * quad (E * E) ^ 2) := by
    rw [← hci]
    exact weighted_term_gap F.weight c hw i
  have ht := raw_certificate (quad (E * E)) q B T s w (F.weight i) (1.1 / w)
    εq εh hF.1.1 (hF.1.2.1 i) hq hh
    (weighted_sum_sos F.weight a hw) (weighted_sum_sos F.weight c hw) hsi hB
    (SoSKit.lagrange F.weight a b hw)
  have hqeq : C (1 / 3) * psi F = q := quartic_third F hF.1.2.2.1
  have hhess : inst (4 * polarize (psi F)) E = 8 * s + 4 * T :=
    hessian_instance F hF.1.2.2.1 (fun j ↦ (hF.1.2.2.2 j).isHermitian) E
  have hf : inst (hConstraint (psi F) εh) E =
      C εh * (nsq ^ 4 + quad (E * E) ^ 4) - (8 * s + 4 * T) ^ 2 := by
    rw [constraint_instance _ _ E (hs i), hhess]
  simpa only [E, qConstraint, hqeq, hf] using ht

theorem nsq_degree : (nsq : RPoly d).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun j _ ↦ by rw [totalDegree_X_pow]

theorem lin_degree (v : Vec d) : (lin v).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simp)

theorem quad_degree (A : Mat d) : (quad A).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have hc : (C (A i j) * (X i : RPoly d)).totalDegree ≤ 1 :=
    (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)

theorem subst_quad_degree (E A : Mat d) : (subst E (quad A)).totalDegree ≤ 2 := by
  simp only [subst, quad, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have h₁ := totalDegree_mul (C (A i j)) (lin (E i))
  have h₂ := totalDegree_mul (C (A i j) * lin (E i)) (lin (E j))
  have := lin_degree (E i)
  have := lin_degree (E j)
  rw [totalDegree_C, zero_add] at h₁
  omega

theorem cross_degree (E A : Mat d) :
    (∑ i, ∑ j, C (A i j) * lin (E i) * (X j : RPoly d)).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  have h₁ := totalDegree_mul (C (A i j)) (lin (E i))
  have h₂ := totalDegree_mul (C (A i j) * lin (E i)) (X j)
  have := lin_degree (E i)
  rw [totalDegree_C, zero_add] at h₁
  rw [totalDegree_X] at h₂
  omega

theorem weighted_degree {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → RPoly d) (r : ℕ) (hp : ∀ j, (p j).totalDegree ≤ r) :
    (∑ j, C (w j) * p j).totalDegree ≤ r := by
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by simpa using hp j)

theorem norm_mul {p q : RPoly d} {a b : ℝ}
    (hp : SoS.coeffNorm1 p ≤ a) (hq : SoS.coeffNorm1 q ≤ b) :
    SoS.coeffNorm1 (p * q) ≤ a * b :=
  (SoS.coeffNorm1_mul_le _ _).trans
    (mul_le_mul hp hq (SoS.coeffNorm1_nonneg _) ((SoS.coeffNorm1_nonneg _).trans hp))

theorem norm_pow {p : RPoly d} {a : ℝ} (hp : SoS.coeffNorm1 p ≤ a) (n : ℕ) :
    SoS.coeffNorm1 (p ^ n) ≤ a ^ n :=
  (SoS.coeffNorm1_pow_le _ _).trans
    (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) hp n)

theorem norm_nsq : SoS.coeffNorm1 (nsq : RPoly d) ≤ d := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin d, (1 : ℝ) := Finset.sum_le_sum fun j _ ↦ by
      simpa [SoS.coeffNorm1_X] using SoS.coeffNorm1_pow_le (X j : RPoly d) 2
    _ = d := by simp

theorem norm_lin (E : Mat d) (e : ℝ) (he : ∀ i j, |E i j| ≤ e) (i : Fin d) :
    SoS.coeffNorm1 (lin (E i)) ≤ d * e := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _j : Fin d, e := Finset.sum_le_sum fun j _ ↦ by
      simpa only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, mul_one] using he i j
    _ = d * e := by simp

theorem norm_quad (A : Mat d) (e : ℝ) (he : ∀ i j, |A i j| ≤ e) :
    SoS.coeffNorm1 (quad A) ≤ d ^ 2 * e := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, e := by
      apply Finset.sum_le_sum
      intro i _
      refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      simpa only [SoS.coeffNorm1_X, mul_one, SoS.coeffNorm1_C_mul] using
        (SoS.coeffNorm1_mul_le (C (A i j) * X i) (X j)).trans (by
          simpa only [SoS.coeffNorm1_X, SoS.coeffNorm1_C_mul, mul_one] using he i j)
    _ = _ := by simp; ring

theorem norm_subst_quad (E A : Mat d) (e : ℝ) (he : 0 ≤ e)
    (hE : ∀ i j, |E i j| ≤ e) (hA : ∀ i j, |A i j| ≤ e) :
    SoS.coeffNorm1 (subst E (quad A)) ≤ d ^ 4 * e ^ 3 := by
  simp only [subst, quad, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, e * (d * e) * (d * e) := by
      apply Finset.sum_le_sum
      intro i _
      refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      apply norm_mul _ (norm_lin E e hE j)
      rw [SoS.coeffNorm1_C_mul]
      exact mul_le_mul (hA i j) (norm_lin E e hE i)
        (SoS.coeffNorm1_nonneg _) he
    _ = _ := by simp; ring

theorem norm_cross (E A : Mat d) (e : ℝ) (he : 0 ≤ e)
    (hE : ∀ i j, |E i j| ≤ e) (hA : ∀ i j, |A i j| ≤ e) :
    SoS.coeffNorm1 (∑ i, ∑ j, C (A i j) * lin (E i) * (X j : RPoly d)) ≤
      d ^ 3 * e ^ 2 := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, e * (d * e) := by
      apply Finset.sum_le_sum
      intro i _
      refine (SoS.coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
      have h := norm_mul (p := C (A i j) * lin (E i)) (q := X j)
        (show SoS.coeffNorm1 (C (A i j) * lin (E i)) ≤ e * (d * e) from by
          rw [SoS.coeffNorm1_C_mul]
          exact mul_le_mul (hA i j) (norm_lin E e hE i)
            (SoS.coeffNorm1_nonneg _) he) (SoS.coeffNorm1_X j).le
      simpa only [mul_one] using h
    _ = _ := by simp; ring

theorem norm_energy (E : Mat d) (hs : Eᵀ = E) (e : ℝ) (he : 0 ≤ e)
    (hE : ∀ i j, |E i j| ≤ e) :
    SoS.coeffNorm1 (quad (E * E)) ≤ d ^ 3 * e ^ 2 := by
  rw [← cross_self E hs]
  exact norm_cross E E e he hE hE

theorem weighted_norm {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (p : ι → RPoly d) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1)
    (b : ℝ) (hp : ∀ j, SoS.coeffNorm1 (p j) ≤ b) :
    SoS.coeffNorm1 (∑ j, C (w j) * p j) ≤ b := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j, w j * b := Finset.sum_le_sum fun j _ ↦ by
      rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (hw j)]
      exact mul_le_mul_of_nonneg_left (hp j) (hw j)
    _ = b := by rw [← Finset.sum_mul, hsum, one_mul]

theorem hessian_bounds (F : FrameModel k d) (hsum : ∑ j, F.weight j = 1)
    (hw : ∀ j, 0 ≤ F.weight j) (hs : ∀ j, (F.cov j).IsHermitian)
    (E : Mat d) (e : ℝ) (he : 0 ≤ e) (hE : ∀ x y, |E x y| ≤ e)
    (hA : ∀ j x y, |deviation F j x y| ≤ e) :
    (inst (4 * polarize (psi F)) E).totalDegree ≤ 4 ∧
      SoS.coeffNorm1 (inst (4 * polarize (psi F)) E) ≤ 12 * d ^ 6 * e ^ 4 := by
  rw [hessian_instance F hsum hs E]
  have hdS := weighted_degree F.weight
    (fun j ↦ (∑ x, ∑ y, C (deviation F j x y) * lin (E x) * X y) ^ 2) 4
    (fun j ↦ (totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left 2 (cross_degree E (deviation F j))))
  have hdT := weighted_degree F.weight
    (fun j ↦ quad (deviation F j) * subst E (quad (deviation F j))) 4
    (fun j ↦ (totalDegree_mul _ _).trans
      (add_le_add (quad_degree _) (subst_quad_degree E _)))
  have hnS := weighted_norm F.weight
    (fun j ↦ (∑ x, ∑ y, C (deviation F j x y) * lin (E x) * X y) ^ 2) hw hsum
    ((d ^ 3 * e ^ 2) ^ 2) (fun j ↦ norm_pow (norm_cross E _ e he hE (hA j)) 2)
  have hnT := weighted_norm F.weight
    (fun j ↦ quad (deviation F j) * subst E (quad (deviation F j))) hw hsum
    ((d ^ 2 * e) * (d ^ 4 * e ^ 3))
    (fun j ↦ norm_mul (norm_quad _ e (hA j)) (norm_subst_quad E _ e he hE (hA j)))
  simp_rw [← mul_assoc] at hdT hnT
  rw [← map_ofNat C 8, ← map_ofNat C 4]
  constructor
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_mul _ _).trans (by simpa using hdS)
    · exact (totalDegree_mul _ _).trans (by simpa using hdT)
  · refine (SoS.coeffNorm1_add_le _ _).trans ?_
    rw [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_C_mul]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    calc
      _ ≤ 8 * (d ^ 3 * e ^ 2) ^ 2 + 4 * ((d ^ 2 * e) * (d ^ 4 * e ^ 3)) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hnS (by norm_num)
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [mul_assoc] using hnT) (by norm_num)
      _ = _ := by ring

def geom : RPoly d := 1 + nsq + nsq ^ 2 + nsq ^ 3

theorem geom_sos : IsSumSq (geom : RPoly d) := by
  have hn : IsSumSq (nsq : RPoly d) := IsSumSq.sum_sq _ _
  exact ((IsSumSq.one.add hn).add (SoS.isSumSq_sq nsq)).add (SoS.isSumSq_pow hn 3)

theorem geom_degree : (geom : RPoly d).totalDegree ≤ 6 := by
  have h₁ := totalDegree_add (1 : RPoly d) nsq
  have h₂ := totalDegree_add (1 + nsq : RPoly d) (nsq ^ 2)
  have h₃ := totalDegree_add (1 + nsq + nsq ^ 2 : RPoly d) (nsq ^ 3)
  have hn := nsq_degree (d := d)
  have hp₂ := totalDegree_pow (nsq : RPoly d) 2
  have hp₃ := totalDegree_pow (nsq : RPoly d) 3
  rw [totalDegree_one] at h₁
  dsimp only [geom]
  omega

theorem geom_norm : SoS.coeffNorm1 (geom : RPoly d) ≤ (d + 1 : ℝ) ^ 3 := by
  have h₁ := SoS.coeffNorm1_add_le (1 : RPoly d) nsq
  have h₂ := SoS.coeffNorm1_add_le (1 + nsq : RPoly d) (nsq ^ 2)
  have h₃ := SoS.coeffNorm1_add_le (1 + nsq + nsq ^ 2 : RPoly d) (nsq ^ 3)
  have hn := norm_nsq (d := d)
  have hp₂ := norm_pow hn 2
  have hp₃ := norm_pow hn 3
  rw [SoS.coeffNorm1_one] at h₁
  dsimp only [geom]
  nlinarith [sq_nonneg (d : ℝ)]

theorem tangent_four (X : RPoly d) (c : ℝ) (hc : 0 ≤ c) (hX : IsSumSq X) :
    IsSumSq (X ^ 4 - C (4 * c ^ 3) * X + C (3 * c ^ 4)) := by
  have hs := ((SoS.isSumSq_sq X).add (SoS.isSumSq_C_mul
    (show 0 ≤ 2 * c by positivity) hX)).add
    (SoS.isSumSq_C (show 0 ≤ 3 * c ^ 2 by positivity))
  convert (SoS.isSumSq_sq (X - C c)).mul hs using 1
  simp only [C_mul, C_pow, map_ofNat]
  ring

theorem root_remainder (X Q H : RPoly d) (A b a c t : ℝ)
    (hc : 0 < c) (hb : 0 < b) (hgap : A ≤ b * c ^ 4)
    (ht : 4 * t * b * c ^ 3 = 1) (hX : IsSumSq X)
    (hraw : IsSumSq (C A * nsq ^ 4 - C b * X ^ 4 - 2 * H - C a * Q)) :
    IsSumSq (C c - X - C (c / 4) * geom * (1 - nsq) -
      C (t * a) * Q - C (2 * t) * H) := by
  have ht0 : 0 ≤ t := by
    have : 0 < 4 * b * c ^ 3 := by positivity
    nlinarith
  have hg := SoS.isSumSq_C_mul (sub_nonneg.mpr hgap)
    (SoS.isSumSq_sq ((nsq : RPoly d) ^ 2))
  have hs := ((hraw.add hg).add
    (SoS.isSumSq_C_mul hb.le (tangent_four X c hc.le hX)))
  have hcPoly : (4 : RPoly d) * C t * C b * C c ^ 3 = 1 := by
    rw [← C_pow, ← map_ofNat C 4, ← C_mul, ← C_mul, ← C_mul, ht, C_1]
  have hquarter : (C (1 / 4) : RPoly d) * 4 = 1 := by
    rw [← map_ofNat C 4, ← C_mul]; norm_num
  have hdiv : C (c / 4) = (C (1 / 4) : RPoly d) * C c := by
    rw [← C_mul]; congr 1; ring
  convert SoS.isSumSq_C_mul ht0 hs using 1
  simp only [geom, C_sub, C_mul, C_pow, map_ofNat, hdiv]
  linear_combination
    (X - C (1 / 4) * C c * (3 + nsq ^ 4)) * hcPoly +
      (C t * C b * C c ^ 4 * (3 + nsq ^ 4) - C c) * hquarter

theorem tolerance_bounds (w εq εh c : ℝ) (hw : 0 < w) (hw' : w ≤ 1 / 2)
    (hq : 0 < εq) (hh : 0 < εh ∧ εh ≤ 16 * w ^ 2) (hc : 0 < c ∧ c ≤ 1)
    (hr : ((2 * εh + 32 * (1.1 / w) ^ 6 * εq) / (32 * w ^ 2)) ^
      (1 / 4 : ℝ) ≤ c) :
    2 * εh + 32 * (1.1 / w) ^ 6 * εq ≤ 32 * w ^ 2 * c ^ 4 ∧
      εq ≤ 1 ∧ εh ≤ 4 ∧ 1 ≤ 1.1 / w := by
  have he : 1 ≤ 1.1 / w := (le_div_iff₀ hw).mpr (by linarith)
  have hh0 := hh.1
  have hbase : 0 ≤ (2 * εh + 32 * (1.1 / w) ^ 6 * εq) / (32 * w ^ 2) := by
    positivity
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hbase _) hr 4
  have heq := Real.rpow_inv_natCast_pow (n := 4) hbase (by norm_num)
  simp only [Nat.cast_ofNat] at heq
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, heq] at hp
  have hg := (div_le_iff₀ (show 0 < 32 * w ^ 2 by positivity)).mp hp
  have hc4 : c ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ hc.1.le hc.2 4
  have hw2 : w ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (w - 1 / 2)]
  have hbig : 32 * w ^ 2 * c ^ 4 ≤ 8 := by
    calc
      _ ≤ 32 * w ^ 2 * 1 := mul_le_mul_of_nonneg_left hc4 (by positivity)
      _ ≤ 8 := by linarith
  have he6 : 1 ≤ (1.1 / w) ^ 6 := one_le_pow₀ he
  have hq' := mul_le_mul_of_nonneg_right he6 hq.le
  exact ⟨by nlinarith [hg], by nlinarith, by nlinarith [hh.2], he⟩

theorem numeric_budget (D z u v W : ℝ)
    (hD : 1 ≤ D) (hz : 0 ≤ z) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hW : 64 * D ^ 2 + z + u + v ≤ W) :
    1 + D ^ 4 * (1.1 * z) ^ 2 + 2 * D ^ 4 +
      3 / 8 * D ^ 8 * (1.1 * z) ^ 10 * z ^ 2 * u * v ^ 3 +
      153 / 64 * D ^ 12 * (1.1 * z) ^ 8 * z ^ 2 * v ^ 3 ≤ W ^ 20 := by
  have hW64 : 64 ≤ W := by nlinarith [sq_nonneg (D - 1)]
  have hW0 : 0 ≤ W := by linarith
  have hd : 0 ≤ D := by linarith
  have hD2 : D ^ 2 ≤ W / 64 := by linarith
  have hzW : z ≤ W := by nlinarith [sq_nonneg D]
  have huW : u ≤ W := by nlinarith [sq_nonneg D]
  have hvW : v ≤ W := by nlinarith [sq_nonneg D]
  have hDpow (r : ℕ) : D ^ (2 * r) ≤ (W / 64) ^ r := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg D) hD2 r
  have hp (r : ℕ) (hr : r ≤ 20) : W ^ r ≤ W ^ 20 :=
    pow_le_pow_right₀ (by linarith) hr
  have h₁ : (1 : ℝ) ≤ W ^ 20 / 8 := by
    have hpow := hp 1 (by omega)
    rw [pow_one] at hpow
    linarith
  have h₂ : D ^ 4 * (1.1 * z) ^ 2 ≤ W ^ 20 / 8 := by
    calc
      _ ≤ (W / 64) ^ 2 * (1.1 * W) ^ 2 := by
        exact mul_le_mul (hDpow 2) (pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hzW (by norm_num)) 2) (by positivity) (by positivity)
      _ = (1.1 ^ 2 / 64 ^ 2) * W ^ 4 := by ring
      _ ≤ (1 / 8) * W ^ 4 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hW0 _)
      _ ≤ W ^ 20 / 8 := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_left (hp 4 (by omega)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have h₃ : 2 * D ^ 4 ≤ W ^ 20 / 8 := by
    calc
      _ ≤ 2 * (W / 64) ^ 2 := mul_le_mul_of_nonneg_left (hDpow 2) (by norm_num)
      _ = (2 / 64 ^ 2) * W ^ 2 := by ring
      _ ≤ (1 / 8) * W ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hW0 _)
      _ ≤ W ^ 20 / 8 := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_left (hp 2 (by omega)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have h₄ : 3 / 8 * D ^ 8 * (1.1 * z) ^ 10 * z ^ 2 * u * v ^ 3 ≤ W ^ 20 / 8 := by
    calc
      _ ≤ 3 / 8 * (W / 64) ^ 4 * (1.1 * W) ^ 10 * W ^ 2 * W * W ^ 3 := by
        gcongr
        exact hDpow 4
      _ = (3 / 8 * 1.1 ^ 10 / 64 ^ 4) * W ^ 20 := by ring
      _ ≤ (1 / 8) * W ^ 20 := mul_le_mul_of_nonneg_right
        (by norm_num) (pow_nonneg hW0 20)
      _ = W ^ 20 / 8 := by ring
  have h₅ : 153 / 64 * D ^ 12 * (1.1 * z) ^ 8 * z ^ 2 * v ^ 3 ≤ W ^ 20 / 8 := by
    calc
      _ ≤ 153 / 64 * (W / 64) ^ 6 * (1.1 * W) ^ 8 * W ^ 2 * W ^ 3 := by
        gcongr
        exact hDpow 6
      _ = (153 * 1.1 ^ 8 / 64 ^ 7) * W ^ 19 := by ring
      _ ≤ (1 / 8) * W ^ 19 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hW0 _)
      _ ≤ W ^ 20 / 8 := by simpa only [div_eq_mul_inv, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_left (hp 19 (by omega)) (by norm_num : (0 : ℝ) ≤ 1 / 8)
  linarith [pow_nonneg hW0 20]

theorem data_polynomial_bounds (F : FrameModel k d) (w γ rF εq εh : ℝ)
    (i : Fin k) (hF : DataValid F w γ rF)
    (hq : 0 ≤ εq ∧ εq ≤ 1) (hh : 0 ≤ εh ∧ εh ≤ 4) (he : 1 ≤ 1.1 / w) :
    let E := deviation F i
    let e := 1.1 / w
    let D := (d + 1 : ℝ)
    SoS.coeffNorm1 (quad (E * E)) ≤ D ^ 4 * e ^ 2 ∧
      (qConstraint (psi F) εq).totalDegree ≤ 8 ∧
      SoS.coeffNorm1 (qConstraint (psi F) εq) + 1 ≤ 3 * D ^ 8 * e ^ 4 ∧
      (inst (hConstraint (psi F) εh) E).totalDegree ≤ 8 ∧
      SoS.coeffNorm1 (inst (hConstraint (psi F) εh) E) + 1 ≤ 153 * D ^ 12 * e ^ 8 := by
  dsimp only
  let e := 1.1 / w
  let D := (d + 1 : ℝ)
  let E := deviation F i
  have he0 : 0 ≤ e := zero_le_one.trans he
  have hD : 1 ≤ D := by dsimp [D]; linarith [Nat.cast_nonneg (α := ℝ) d]
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdD : (d : ℝ) ≤ D := by dsimp [D]; linarith
  have hs (j : Fin k) := deviation_symm F
    (fun j ↦ (hF.1.2.2.2 j).isHermitian) j
  have hentry (j : Fin k) := entry_bound (deviation F j) (hs j) e he0
    ((deviation_bound F w γ rF hF).2 j)
  have hw (j : Fin k) : 0 ≤ F.weight j := hF.1.1.le.trans (hF.1.2.1 j)
  have hX := norm_energy E (hs i) e he0 (hentry i)
  have hH := hessian_bounds F hF.1.2.2.1 hw
    (fun j ↦ (hF.1.2.2.2 j).isHermitian) E e he0 (hentry i) hentry
  have hqeq := quartic_third F hF.1.2.2.1
  have hqd : (C (1 / 3) * psi F).totalDegree ≤ 4 := by
    rw [hqeq]
    exact weighted_degree F.weight (fun j ↦ quad (deviation F j) ^ 2) 4
      (fun j ↦ (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (quad_degree _)))
  have hqn : SoS.coeffNorm1 (C (1 / 3) * psi F) ≤ d ^ 4 * e ^ 2 := by
    rw [hqeq]
    convert weighted_norm F.weight (fun j ↦ quad (deviation F j) ^ 2) hw
      hF.1.2.2.1 ((d ^ 2 * e) ^ 2) (fun j ↦ norm_pow (norm_quad _ e (hentry j)) 2)
      using 1
    ring
  have hQd : (qConstraint (psi F) εq).totalDegree ≤ 8 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by
        rw [totalDegree_C, zero_add]
        exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 4 nsq_degree))
    · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hqd)
  have hQn : SoS.coeffNorm1 (qConstraint (psi F) εq) ≤ d ^ 4 + d ^ 8 * e ^ 4 := by
    refine (SoS.coeffNorm1_sub_le _ _).trans ?_
    have h₁ := norm_mul (p := C (εq ^ 2)) (q := nsq ^ 4)
      (show SoS.coeffNorm1 (C (εq ^ 2) : RPoly d) ≤ 1 by
        rw [SoS.coeffNorm1_C, abs_of_nonneg (sq_nonneg _)]
        simpa using pow_le_pow_left₀ hq.1 hq.2 2) (norm_pow norm_nsq 4)
    have h₂ := norm_pow hqn 2
    nlinarith only [h₁, h₂]
  have hFd : (inst (hConstraint (psi F) εh) E).totalDegree ≤ 8 := by
    rw [constraint_instance _ _ E (hs i)]
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, zero_add]
      apply (totalDegree_add _ _).trans
      exact max_le ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 4 nsq_degree))
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left 4 (quad_degree _)))
    · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 hH.1)
  have hFn : SoS.coeffNorm1 (inst (hConstraint (psi F) εh) E) ≤
      4 * d ^ 4 + 148 * d ^ 12 * e ^ 8 := by
    rw [constraint_instance _ _ E (hs i)]
    refine (SoS.coeffNorm1_sub_le _ _).trans ?_
    have hsum : SoS.coeffNorm1 (nsq ^ 4 + quad (E * E) ^ 4) ≤
        d ^ 4 + (d ^ 3 * e ^ 2) ^ 4 :=
      (SoS.coeffNorm1_add_le _ _).trans (add_le_add (norm_pow norm_nsq 4) (norm_pow hX 4))
    have h₁ := norm_mul (p := C εh) (q := nsq ^ 4 + quad (E * E) ^ 4)
      (show SoS.coeffNorm1 (C εh : RPoly d) ≤ 4 by
        rw [SoS.coeffNorm1_C, abs_of_nonneg hh.1]; exact hh.2) hsum
    have h₂ := norm_pow hH.2 2
    nlinarith only [h₁, h₂]
  have hD4 : (d : ℝ) ^ 4 ≤ D ^ 8 * e ^ 4 := by
    calc
      _ ≤ D ^ 4 := pow_le_pow_left₀ hd hdD 4
      _ ≤ D ^ 8 := pow_le_pow_right₀ hD (by omega)
      _ ≤ D ^ 8 * e ^ 4 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ he)
  have hD8 : (d : ℝ) ^ 8 * e ^ 4 ≤ D ^ 8 * e ^ 4 := by gcongr
  have hD12 : (d : ℝ) ^ 12 * e ^ 8 ≤ D ^ 12 * e ^ 8 := by gcongr
  have hD4' : (d : ℝ) ^ 4 ≤ D ^ 12 * e ^ 8 := by
    calc
      _ ≤ D ^ 4 := pow_le_pow_left₀ hd hdD 4
      _ ≤ D ^ 12 := pow_le_pow_right₀ hD (by omega)
      _ ≤ D ^ 12 * e ^ 8 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ he)
  have hOneQ : 1 ≤ D ^ 8 * e ^ 4 := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hD) (one_le_pow₀ he)
  have hOneF : 1 ≤ D ^ 12 * e ^ 8 := one_le_mul_of_one_le_of_one_le
    (one_le_pow₀ hD) (one_le_pow₀ he)
  refine ⟨hX.trans ?_, hQd, ?_, hFd, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg e)
    exact (pow_le_pow_left₀ hd hdD 3).trans (pow_le_pow_right₀ hD (by omega))
  · change SoS.coeffNorm1 (qConstraint (psi F) εq) + 1 ≤ 3 * D ^ 8 * e ^ 4
    nlinarith only [hQn, hD4, hD8, hOneQ]
  · change SoS.coeffNorm1 (inst (hConstraint (psi F) εh) E) + 1 ≤
      153 * D ^ 12 * e ^ 8
    nlinarith only [hFn, hD4', hD12, hOneF]

theorem derive_linear (A : List (RPoly d)) (X Q H : RPoly d) (c aq af : ℝ)
    (hc : 0 < c ∧ c ≤ 1) (haq : 0 ≤ aq) (haf : 0 ≤ af)
    (hball : 1 - nsq ∈ A) (hQ : Q ∈ A) (hH : H ∈ A)
    (hdX : X.totalDegree ≤ 2) (hdQ : Q.totalDegree ≤ 8) (hdH : H.totalDegree ≤ 8)
    (hR : IsSumSq (C c - X - C (c / 4) * geom * (1 - nsq) - C aq * Q - C af * H)) :
    SoS.DerivesNq A 8
      (1 + SoS.coeffNorm1 X + 2 * (d + 1 : ℝ) ^ 4 +
        aq * (SoS.coeffNorm1 Q + 1) + af * (SoS.coeffNorm1 H + 1)) 1 (C c - X) := by
  have hc0 := hc.1.le
  let D := (d + 1 : ℝ)
  let B : RPoly d := C (c / 4) * geom
  let R := C c - X - B * (1 - nsq) - C aq * Q - C af * H
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdBall : (1 - nsq : RPoly d).totalDegree ≤ 2 :=
    (totalDegree_sub _ _).trans (max_le (by simp) nsq_degree)
  have hdB : B.totalDegree ≤ 6 :=
    (totalDegree_mul _ _).trans (by simpa using geom_degree (d := d))
  have hdBX : (B * (1 - nsq)).totalDegree ≤ 8 :=
    (totalDegree_mul _ _).trans (add_le_add hdB hdBall)
  have hdAQ : (C aq * Q).totalDegree ≤ 8 :=
    (totalDegree_mul _ _).trans (by simpa using hdQ)
  have hdAF : (C af * H).totalDegree ≤ 8 :=
    (totalDegree_mul _ _).trans (by simpa using hdH)
  have hdR : R.totalDegree ≤ 8 := by
    apply (totalDegree_sub _ _).trans (max_le ?_ hdAF)
    apply (totalDegree_sub _ _).trans (max_le ?_ hdAQ)
    apply (totalDegree_sub _ _).trans (max_le ?_ hdBX)
    exact (totalDegree_sub _ _).trans (max_le (by simp) (hdX.trans (by omega)))
  have hnB : SoS.coeffNorm1 B ≤ D ^ 3 := by
    rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (by positivity : 0 ≤ c / 4)]
    calc
      _ ≤ 1 * D ^ 3 := mul_le_mul (by linarith : c / 4 ≤ 1) geom_norm
        (SoS.coeffNorm1_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hnBall : SoS.coeffNorm1 (1 - nsq : RPoly d) ≤ 1 + d := by
    exact (SoS.coeffNorm1_sub_le _ _).trans
      (add_le_add (SoS.coeffNorm1_one.le) norm_nsq)
  have hnR : SoS.coeffNorm1 R ≤ 1 + SoS.coeffNorm1 X + D ^ 3 * (1 + d) +
      aq * SoS.coeffNorm1 Q + af * SoS.coeffNorm1 H := by
    apply (SoS.coeffNorm1_sub_le _ _).trans
    apply add_le_add _ (by rw [SoS.coeffNorm1_C_mul, abs_of_nonneg haf])
    apply (SoS.coeffNorm1_sub_le _ _).trans
    apply add_le_add _ (by rw [SoS.coeffNorm1_C_mul, abs_of_nonneg haq])
    apply (SoS.coeffNorm1_sub_le _ _).trans
    apply add_le_add _ (norm_mul hnB hnBall)
    apply (SoS.coeffNorm1_sub_le _ _).trans
    apply add_le_add _ le_rfl
    rw [SoS.coeffNorm1_C, abs_of_pos hc.1]
    exact hc.2
  have hsR := SoS.DerivesNq.ofIsSOS (q := 1) A
    (by simpa only [SoS.IsSOS, SoS.toReal_real] using hR) hdR hnR
  have hsB : SoS.IsSOS B := by
    simpa only [SoS.IsSOS, SoS.toReal_real] using
      SoS.isSumSq_C_mul (by positivity : 0 ≤ c / 4) (geom_sos (d := d))
  have hsBall := ((SoS.DerivesNq.of_mem (q := 1) hball hdBall le_rfl).mulSOS hsB).mono
    (show B.totalDegree + 2 ≤ 8 by omega) (by simpa only [mul_one] using hnB)
  have hsQ := (SoS.DerivesNq.of_mem (q := 1) hQ hdQ le_rfl).smul haq
  have hsH := (SoS.DerivesNq.of_mem (q := 1) hH hdH le_rfl).smul haf
  have ht := ((hsR.add hsBall).add hsQ).add hsH
  have ht' := ht.congr (show R + B * (1 - nsq) + C aq * Q + C af * H = C c - X by
    dsimp only [R]; ring)
  apply ht'.mono le_rfl
  dsimp only [D]
  have hbd : (d + 1 : ℝ) ^ 3 * (1 + d) + (d + 1 : ℝ) ^ 3 ≤
      2 * (d + 1 : ℝ) ^ 4 := by
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [pow_nonneg (show 0 ≤ (d + 1 : ℝ) by positivity) 3]
  dsimp only [D] at *
  nlinarith only [hbd]

end

end ABBKS26.Centered.IdentAux
