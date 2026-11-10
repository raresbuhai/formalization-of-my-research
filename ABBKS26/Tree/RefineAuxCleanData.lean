module

public import ABBKS26.Tree.RefineAuxCleanPass
public import ABBKS26.Tree.RefineAuxPopulation

/-! Population Frobenius bounds in a clean-pass frame. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix Robust
open scoped BigOperators

variable {n k d : ℕ}

private theorem cleanData_partition (R : Robust.Reference n k d) (w : ℝ)
    (hR : R.Valid w) (f : Fin n → ℝ) :
    (∑ j, R.model.weight j *
      ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
        ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), f l) =
      (R.reference.card : ℝ)⁻¹ * ∑ l ∈ R.reference, f l := by
  classical
  have he (j : Fin k) : R.model.weight j *
      ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ =
      (R.reference.card : ℝ)⁻¹ := by
    have hw : 0 < R.model.weight j := hR.1.1.trans_le (hR.1.2.1 j)
    have hc : ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ) ≠ 0 := by
      intro hc
      rw [hR.2.2.2.2.2.2 j, hc, zero_div] at hw
      exact (lt_irrefl 0) hw
    rw [hR.2.2.2.2.2.2 j, div_eq_mul_inv]
    field_simp
  simp only [he, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

private theorem cleanData_raw_second (R : Robust.Reference n k d) (w : ℝ)
    (hR : R.Valid w) (u : Vec d) :
    qform R.cov u = (R.reference.card : ℝ)⁻¹ *
      ∑ l ∈ R.reference, (u ⬝ᵥ R.clean l) ^ 2 - (u ⬝ᵥ R.mean) ^ 2 := by
  have hn : (R.reference.card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hR.2.2.2.2.1).ne'
  have hmean : (R.reference.card : ℝ)⁻¹ *
      ∑ l ∈ R.reference, u ⬝ᵥ R.clean l = u ⬝ᵥ R.mean := by
    simp only [Robust.Reference.mean, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  have he (l : Fin n) : (u ⬝ᵥ (R.clean l - R.mean)) ^ 2 =
      (u ⬝ᵥ R.clean l) ^ 2 - 2 * (u ⬝ᵥ R.clean l) * (u ⬝ᵥ R.mean) +
        (u ⬝ᵥ R.mean) ^ 2 := by rw [dotProduct_sub]; ring
  simp only [Robust.Reference.cov, qform, smul_mulVec, sum_mulVec, dotProduct_smul,
    dotProduct_sum, vecMulVec_mulVec, op_smul_eq_smul, smul_eq_mul]
  simp_rw [dotProduct_comm (R.clean _ - R.mean) u, ← pow_two, he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, mul_add, mul_sub]
  rw [show (R.reference.card : ℝ)⁻¹ *
      (2 * (∑ l ∈ R.reference, u ⬝ᵥ R.clean l) * (u ⬝ᵥ R.mean)) =
      2 * (u ⬝ᵥ R.mean) ^ 2 by rw [← hmean]; ring]
  field_simp
  ring

/-- The empirical covariance of centered components approximates their population second moment. -/
theorem centered_covariance_comparison_precise (R : Robust.Reference n k d) (w θ : ℝ)
    (hR : R.Valid w) (hcen : ∀ j, R.model.mean j = 0)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : R.Resilient 4 θ) (u : Vec d) :
    (1 - 5 * (θ / (d + 1 : ℝ) ^ 8)) * qform R.model.second u ≤ qform R.cov u ∧
      qform R.cov u ≤ (1 + 4 * (θ / (d + 1 : ℝ) ^ 8)) * qform R.model.second u := by
  let δ := θ / (d + 1 : ℝ) ^ 8
  let m := fun j ↦ ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), u ⬝ᵥ R.clean l
  let s := fun j ↦ ((R.reference.filter (fun l ↦ R.label l = j)).card : ℝ)⁻¹ *
    ∑ l ∈ R.reference.filter (fun l ↦ R.label l = j), (u ⬝ᵥ R.clean l) ^ 2
  let V := qform R.model.second u
  let E := (R.reference.card : ℝ)⁻¹ * ∑ l ∈ R.reference, (u ⬝ᵥ R.clean l) ^ 2
  let μ := u ⬝ᵥ R.mean
  have hδ0 : 0 ≤ δ := div_nonneg hθ.1 (by positivity)
  have hd : (1 : ℝ) ≤ d + 1 := by linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hδθ : δ ≤ θ := div_le_self hθ.1 (one_le_pow₀ hd)
  have hδ : δ ≤ 1 / 100 := hδθ.trans hθ.2
  have hw (j : Fin k) : 0 ≤ R.model.weight j := hR.1.1.le.trans (hR.1.2.1 j)
  have hVj (j : Fin k) : 0 ≤ qform (R.model.cov j) u := by
    simpa only [qform, star_trivial] using
      (hR.1.2.2.2 j).posSemidef.dotProduct_mulVec_nonneg u
  have hVeq : (∑ j, R.model.weight j * qform (R.model.cov j) u) = V := by
    simp only [V, FrameModel.second, hcen, vecMulVec_zero, add_zero, qform,
      sum_mulVec, dotProduct_sum, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hV : 0 ≤ V := hVeq ▸ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (hVj j)
  have hsum_m : (∑ j, R.model.weight j * m j) = μ := by
    simp only [m, ← mul_assoc]
    rw [cleanData_partition R w hR]
    simp only [μ, Robust.Reference.mean, dotProduct_smul, dotProduct_sum, smul_eq_mul]
  have hsum_s : (∑ j, R.model.weight j * s j) = E := by
    simp only [s, ← mul_assoc]
    exact cleanData_partition R w hR _
  have hcomponent := centered_component_moments R θ hR.1.2.2.2 hcen hres u
  have hmsq : (∑ j, R.model.weight j * m j ^ 2) ≤ 4 * δ ^ 2 * V := by
    calc
      _ ≤ ∑ j, R.model.weight j * (4 * δ ^ 2 * qform (R.model.cov j) u) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hcomponent j).1 (hw j)
      _ = _ := by rw [← hVeq, Finset.mul_sum]; congr 1; funext j; ring
  have hμsq : μ ^ 2 ≤ 4 * δ ^ 2 * V := by
    apply le_trans _ hmsq
    have hh : 0 ≤ ∑ j, R.model.weight j * (m j - μ) ^ 2 :=
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (hw j) (sq_nonneg _)
    have he : (∑ j, R.model.weight j * (m j - μ) ^ 2) =
        (∑ j, R.model.weight j * m j ^ 2) - μ ^ 2 := by
      simp_rw [sub_sq, mul_add, mul_sub]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp_rw [show ∀ j, R.model.weight j * (2 * m j * μ) =
        2 * μ * (R.model.weight j * m j) by intro j; ring]
      rw [← Finset.mul_sum, hsum_m, ← Finset.sum_mul, hR.1.2.2.1]
      ring
    rw [he] at hh
    linarith only [hh]
  have hE : (1 - 4 * δ) * V ≤ E ∧ E ≤ (1 + 4 * δ) * V := by
    have hl (j : Fin k) := (abs_le.mp (hcomponent j).2).1
    have hu (j : Fin k) := (abs_le.mp (hcomponent j).2).2
    constructor
    · calc
        _ = ∑ j, R.model.weight j * ((1 - 4 * δ) * qform (R.model.cov j) u) := by
          rw [← hVeq, Finset.mul_sum]; congr 1; funext j; ring
        _ ≤ ∑ j, R.model.weight j * s j := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hw j)
          linarith only [hl j]
        _ = E := hsum_s
    · calc
        E = ∑ j, R.model.weight j * s j := hsum_s.symm
        _ ≤ ∑ j, R.model.weight j * ((1 + 4 * δ) * qform (R.model.cov j) u) := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul_of_nonneg_left _ (hw j)
          linarith only [hu j]
        _ = _ := by rw [← hVeq, Finset.mul_sum]; congr 1; funext j; ring
  have hC : qform R.cov u = E - μ ^ 2 := cleanData_raw_second R w hR u
  have hsδ : 4 * δ ^ 2 ≤ δ := by nlinarith only [hδ0, hδ]
  have hsδV := mul_le_mul_of_nonneg_right hsδ hV
  constructor <;> nlinarith only [hC, hE.1, hE.2, hμsq, hsδV, sq_nonneg μ]

/-- The dimension factor in Frobenius error is paid by the resilience denominator. -/
theorem centered_second_frob (R : Reference n k d) (w θ γ : ℝ)
    (hR : R.Valid w) (hcen : ∀ j, R.model.mean j = 0)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : R.Resilient 4 θ)
    (hiso : R.model.Isotropic γ) (hγ : γ ≤ 1) :
    RBAux.FrameLoop.fnorm (R.model.second - R.cov) ≤ 10 * θ := by
  let δ := θ / (d + 1 : ℝ) ^ 8
  have hδ : 0 ≤ δ := div_nonneg hθ.1 (by positivity)
  have hs : (R.model.second - R.cov)ᵀ = R.model.second - R.cov := by
    have hp : R.model.secondᵀ = R.model.second := by
      simp only [FrameModel.second, hcen, vecMulVec_zero, add_zero, transpose_sum,
        transpose_smul]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using
        (hR.1.2.2.2 j).isHermitian
    have hc : R.covᵀ = R.cov := by
      simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using
        hR.2.2.2.2.2.1.isHermitian
    rw [transpose_sub, hp, hc]
  have hq (u : Vec d) :
      |qform (R.model.second - R.cov) u| ≤ (10 * δ) * sqnorm u := by
    have hc := centered_covariance_comparison_precise R w θ hR hcen hθ hres u
    change (1 - 5 * δ) * qform R.model.second u ≤ qform R.cov u ∧
      qform R.cov u ≤ (1 + 4 * δ) * qform R.model.second u at hc
    have hpop := hiso.2.2 u
    simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hpop
    change qform R.model.second u ≤ (1 + γ) * sqnorm u at hpop
    have hn := Rounding.DetRoundAux.sqnorm_nonneg u
    have hp : qform R.model.second u ≤ 2 * sqnorm u := by
      nlinarith only [hpop, mul_le_mul_of_nonneg_right hγ hn]
    have hδp := mul_le_mul_of_nonneg_left hp hδ
    simp only [qform, sub_mulVec, dotProduct_sub]
    change |qform R.model.second u - qform R.cov u| ≤ _
    exact abs_le.mpr ⟨by nlinarith only [hc.2, hδp, mul_nonneg hδ hn],
      by nlinarith only [hc.1, hδp]⟩
  have he := Centered.IdentAux.entry_bound _ hs (10 * δ) (by positivity) hq
  have hb : frobSq (R.model.second - R.cov) ≤ ((d : ℝ) * (10 * δ)) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (10 * δ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he i j) 2
      _ = _ := by simp; ring
  have hd : (d : ℝ) ≤ (d + 1 : ℝ) ^ 8 := by
    exact (by linarith : (d : ℝ) ≤ d + 1).trans
      (le_self_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) d]) (by omega))
  have hδd : (d : ℝ) * δ ≤ θ := by
    dsimp only [δ]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : (0 : ℝ) < (d + 1 : ℝ) ^ 8)]
    nlinarith only [mul_le_mul_of_nonneg_right hd hθ.1]
  have hh := (sq_le_sq₀ (RBAux.FrameLoop.fnorm_nonneg _)
    (by positivity : 0 ≤ (d : ℝ) * (10 * δ))).mp
      (by simpa only [RBAux.FrameLoop.fnorm_sq] using hb)
  linarith only [hh, hδd]

private theorem cleanData_fnorm_smul (a : ℝ) (A : Mat d) :
    RBAux.FrameLoop.fnorm (a • A) = |a| * RBAux.FrameLoop.fnorm A := by
  simp only [RBAux.FrameLoop.fnorm, frobSq, Matrix.smul_apply, smul_eq_mul, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

private theorem cleanData_fnorm_sum {ι : Type*} (s : Finset ι) (A : ι → Mat d) :
    RBAux.FrameLoop.fnorm (∑ j ∈ s, A j) ≤ ∑ j ∈ s, RBAux.FrameLoop.fnorm (A j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, RBAux.FrameLoop.fnorm_zero, le_refl]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (RBAux.FrameLoop.fnorm_add _ _).trans (add_le_add_right ih _)

/-- Pairwise population bounds control each component's deviation from the identity. -/
theorem centered_component_frob (R : Reference n k d) (w θ γ B e : ℝ)
    (hR : R.Valid w) (hcen : ∀ j, R.model.mean j = 0)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 100) (hres : R.Resilient 4 θ)
    (hiso : R.model.Isotropic γ) (hγ : γ ≤ 1) (hB : 0 ≤ B)
    (he : 0 ≤ e) (hC : frobSq (R.cov - 1) ≤ e ^ 2)
    (hpair : ∀ i j, frobSq (R.model.cov i - R.model.cov j) ≤ B) (i : Fin k) :
    frobSq (R.model.cov i - 1) ≤ 2 * B + 2 * (10 * θ + e) ^ 2 := by
  have hw (j : Fin k) : 0 ≤ R.model.weight j := hR.1.1.le.trans (hR.1.2.1 j)
  have hp (j : Fin k) :
      RBAux.FrameLoop.fnorm (R.model.cov i - R.model.cov j) ≤ Real.sqrt B := by
    exact Real.sqrt_le_sqrt (hpair i j)
  have hs : R.model.cov i - R.model.second =
      ∑ j, R.model.weight j • (R.model.cov i - R.model.cov j) := by
    simp only [FrameModel.second, hcen, vecMulVec_zero, add_zero, smul_sub,
      Finset.sum_sub_distrib, ← Finset.sum_smul, hR.1.2.2.1, one_smul]
  have hdev : RBAux.FrameLoop.fnorm (R.model.cov i - R.model.second) ≤
      Real.sqrt B := by
    rw [hs]
    calc
      _ ≤ ∑ j, RBAux.FrameLoop.fnorm
          (R.model.weight j • (R.model.cov i - R.model.cov j)) := cleanData_fnorm_sum _ _
      _ = ∑ j, R.model.weight j *
          RBAux.FrameLoop.fnorm (R.model.cov i - R.model.cov j) := by
        simp only [cleanData_fnorm_smul, abs_of_nonneg (hw _)]
      _ ≤ ∑ j, R.model.weight j * Real.sqrt B :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hp j) (hw j)
      _ = Real.sqrt B := by rw [← Finset.sum_mul, hR.1.2.2.1, one_mul]
  have hsecond := centered_second_frob R w θ γ hR hcen hθ hres hiso hγ
  have hcov : RBAux.FrameLoop.fnorm (R.cov - 1) ≤ e :=
    (sq_le_sq₀ (RBAux.FrameLoop.fnorm_nonneg _) he).mp
      (by simpa only [RBAux.FrameLoop.fnorm_sq] using hC)
  have htotal : RBAux.FrameLoop.fnorm (R.model.cov i - 1) ≤
      Real.sqrt B + (10 * θ + e) := by
    have h := RBAux.FrameLoop.fnorm_add (R.model.cov i - R.model.second)
      (R.model.second - R.cov + (R.cov - 1))
    have hh := RBAux.FrameLoop.fnorm_add (R.model.second - R.cov) (R.cov - 1)
    have heq : R.model.cov i - R.model.second +
        (R.model.second - R.cov + (R.cov - 1)) = R.model.cov i - 1 := by abel
    rw [heq] at h
    linarith only [h, hh, hdev, hsecond, hcov]
  have hh := pow_le_pow_left₀ (RBAux.FrameLoop.fnorm_nonneg _) htotal 2
  rw [RBAux.FrameLoop.fnorm_sq] at hh
  nlinarith only [hh, sq_nonneg (Real.sqrt B - (10 * θ + e)), Real.sq_sqrt hB]


/-- The centered isotropy schedule is smaller than the input weight by a fixed factor. -/
theorem centered_gamma_le (w β : ℚ) (hw : 0 < w ∧ w ≤ 1)
    (hβ : 0 < β ∧ β ≤ 1) : Centered.gammaStar w β ≤ w / 20 := by
  have hν0 : 0 ≤ Centered.nu w β := mul_nonneg hw.1.le (pow_nonneg hβ.1.le 4)
  have hνw : Centered.nu w β ≤ w := by
    exact mul_le_of_le_one_right hw.1.le (pow_le_one₀ hβ.1.le hβ.2)
  have hν1 : Centered.nu w β ≤ 1 := hνw.trans hw.2
  have hδν : Centered.delta w β ≤ Centered.nu w β := by
    simpa only [Centered.delta, pow_one] using
      pow_le_pow_of_le_one hν0 hν1 (show 1 ≤ 8 by omega)
  have hδ0 : 0 ≤ Centered.delta w β := pow_nonneg hν0 _
  have hδ1 : Centered.delta w β ≤ 1 := hδν.trans hν1
  have hδ2 : Centered.delta w β ^ 2 ≤ Centered.delta w β := by
    simpa only [pow_one] using pow_le_pow_of_le_one hδ0 hδ1 (show 1 ≤ 2 by omega)
  exact div_le_div_of_nonneg_right (hδ2.trans (hδν.trans hνw)) (by norm_num)

end

end ABBKS26.RefineAux
