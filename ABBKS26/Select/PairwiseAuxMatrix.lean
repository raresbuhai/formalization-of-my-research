module

public import ABBKS26.Select.Learn

/-! Matrix estimates for the centered pairwise test. -/

@[expose] public section

namespace ABBKS26.Select.PairwiseAux

open Common Matrix
open scoped MatrixOrder

noncomputable section

variable {d : ℕ}

theorem psd_sub (S T : Mat d) (hS : S.IsHermitian) (hT : T.IsHermitian)
    (h : LE S T) : (T - S).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (hT.sub hS) fun v ↦ ?_
  simpa only [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg, qform] using h v

theorem trace_mul_sq_le (A B : Mat d) (hB : Bᵀ = B) :
    (A * B).trace ^ 2 ≤ frobSq A * frobSq B := by
  rw [Robust.FilterAux.trace_inner A B hB]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : Fin d × Fin d ↦ A p.1 p.2) (fun p : Fin d × Fin d ↦ B p.1 p.2)
  simpa only [Fintype.sum_prod_type, frobSq] using h


theorem trace_quad_mono (A S T : Mat d) (hA : Aᵀ = A)
    (hS : S.PosSemidef) (hT : T.PosSemidef) (h : LE S T) :
    (A * S * A * S).trace ≤ (A * T * A * T).trace := by
  have hdiff := psd_sub S T hS.1 hT.1 h
  have hAS : (A * S * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      hS.mul_mul_conjTranspose_same A
  have hAT : (A * T * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      hT.mul_mul_conjTranspose_same A
  have h₁ := Separation.trace_mul_le_trace_mul hdiff hAS
  have h₂ := Separation.trace_mul_le_trace_mul hdiff hAT
  calc
    _ = (S * (A * S * A)).trace := trace_mul_comm _ _
    _ ≤ (T * (A * S * A)).trace := h₁
    _ = ((T * A) * (S * A)).trace := by simp only [mul_assoc]
    _ = ((S * A) * (T * A)).trace := trace_mul_comm _ _
    _ = (S * (A * T * A)).trace := by simp only [mul_assoc]
    _ ≤ (T * (A * T * A)).trace := h₂
    _ = _ := trace_mul_comm _ _

/-- Relative Frobenius accuracy controls every quadratic population center. -/
theorem center_error_sq (A S Q : Mat d) (hS : S.PosDef) (hQ : Qᵀ = Q)
    (herr : frobSq ((CFC.sqrt S)⁻¹ * A * (CFC.sqrt S)⁻¹ - 1) ≤ 1 / 100) :
    (Q * (A - S)).trace ^ 2 ≤ (Q * S * Q * S).trace / 100 := by
  let R := CFC.sqrt S
  let E := R⁻¹ * A * R⁻¹ - 1
  obtain ⟨hRt, hdet, hRR⟩ := Robust.RBAux.sqrt_properties S hS
  change Rᵀ = R at hRt
  change R * R = S at hRR
  have hR : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have heq : R * E * R = A - S := by
    dsimp only [E]
    simp only [mul_sub, sub_mul, mul_one, mul_assoc,
      mul_nonsing_inv_cancel_left _ _ hR, nonsing_inv_mul_cancel_right _ _ hR, hRR]
  have hsym : (R * Q * R)ᵀ = R * Q * R := by
    simp only [transpose_mul, hRt, hQ, mul_assoc]
  have htrace : (Q * (A - S)).trace = (E * (R * Q * R)).trace := by
    calc
      _ = ((Q * R) * (E * R)).trace := by rw [← heq]; simp only [mul_assoc]
      _ = ((E * R) * (Q * R)).trace := trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  have hnorm : frobSq (R * Q * R) = (Q * S * Q * S).trace := by
    rw [← Tree.CompleteAux.trace_sq _
      (by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hsym)]
    calc
      _ = (R * (Q * R * R * Q * R)).trace := by simp only [mul_assoc]
      _ = ((Q * R * R * Q * R) * R).trace := trace_mul_comm _ _
      _ = (Q * (R * R) * Q * (R * R)).trace := by simp only [mul_assoc]
      _ = _ := by rw [hRR]
  rw [htrace]
  calc
    _ ≤ frobSq E * frobSq (R * Q * R) := trace_mul_sq_le _ _ hsym
    _ ≤ (1 / 100) * frobSq (R * Q * R) :=
      mul_le_mul_of_nonneg_right herr (by dsimp only [frobSq]; positivity)
    _ = _ := by rw [hnorm]; ring

theorem trace_quad_smul (Q E : Mat d) (c : ℝ) :
    (Q * (c • E) * Q * (c • E)).trace = c ^ 2 * (Q * E * Q * E).trace := by
  simp only [Matrix.mul_smul, smul_mul, smul_smul, trace_smul, smul_eq_mul, pow_two]

theorem cast_inv (A : Matrix (Fin d) (Fin d) ℚ)
    (hA : (A.map (algebraMap ℚ ℝ)).PosDef) :
    A⁻¹.map (algebraMap ℚ ℝ) = (A.map (algebraMap ℚ ℝ))⁻¹ := by
  have hdet : A.det ≠ 0 := by
    intro hz
    have he := (algebraMap ℚ ℝ).map_det A
    rw [hz, map_zero] at he
    exact hA.det_pos.ne' he.symm
  have he := congrArg ((algebraMap ℚ ℝ).mapMatrix)
    (nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet))
  simp only [map_mul, map_one] at he
  exact (inv_eq_left_inv he).symm

theorem trace_congr_pair (W D X : Mat d) :
    (W * D * W * X).trace = (D * (W * X * W)).trace := by
  calc
    _ = (W * (D * W * X)).trace := by simp only [mul_assoc]
    _ = ((D * W * X) * W).trace := trace_mul_comm _ _
    _ = _ := by simp only [mul_assoc]

theorem trace_whitened_square (W D E : Mat d) (hD : D.IsHermitian)
    (hwhite : W * E * W = 1) :
    (W * D * W * E * (W * D * W) * E).trace = frobSq D := by
  calc
    _ = (W * (D * (W * E * W) * D * W * E)).trace := by simp only [mul_assoc]
    _ = (W * (D * D * W * E)).trace := by rw [hwhite, mul_one]
    _ = ((D * D * W * E) * W).trace := trace_mul_comm _ _
    _ = (D * D * (W * E * W)).trace := by simp only [mul_assoc]
    _ = (D * D).trace := by rw [hwhite, mul_one]
    _ = _ := Tree.CompleteAux.trace_sq _ hD

/-- Accuracy remains bounded in any common whitening frame dominating the covariance. -/
theorem normalized_error (A S E W : Mat d) (hA : A.IsHermitian) (hS : S.PosDef)
    (hE : E.PosSemidef) (hW : Wᵀ = W) (hwhite : W * E * W = 1)
    (c : ℝ) (hc : 0 ≤ c) (hupper : LE S (c • E))
    (herr : frobSq ((CFC.sqrt S)⁻¹ * A * (CFC.sqrt S)⁻¹ - 1) ≤ 1 / 100) :
    frobSq (W * (A - S) * W) ≤ c ^ 2 / 100 := by
  let D := W * (A - S) * W
  have hD : D.IsHermitian := by
    simpa only [D, conjTranspose_eq_transpose_of_trivial, hW] using
      isHermitian_mul_mul_conjTranspose W (hA.sub hS.1)
  have hDt : Dᵀ = D := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hD
  let Q := W * D * W
  have hQt : Qᵀ = Q := by simp only [Q, transpose_mul, hW, hDt, mul_assoc]
  have hQE : (Q * E * Q * E).trace = frobSq D :=
    trace_whitened_square W D E hD hwhite
  have hcenter : (Q * (A - S)).trace = frobSq D := by
    rw [show Q = W * D * W from rfl, trace_congr_pair]
    exact Tree.CompleteAux.trace_sq _ hD
  have hv := trace_quad_mono Q S (c • E) hQt hS.posSemidef (hE.smul hc) hupper
  rw [trace_quad_smul, hQE] at hv
  have hh := center_error_sq A S Q hS hQt herr
  rw [hcenter] at hh
  have hn : 0 ≤ frobSq D := by dsimp only [frobSq]; positivity
  change frobSq D ≤ c ^ 2 / 100
  nlinarith only [hh, hv, hn]

theorem not_frobenius_of_common_bounds (S T : Mat d) (hS : S.PosDef)
    (hT : T.IsHermitian) (R H Δ : ℝ) (hR : 0 < R) (hH : 0 ≤ H)
    (hsum : ∀ v, (10 / 11 : ℝ) * sqnorm v ≤ qform S v + qform T v)
    (hratio : LE S (R • T)) (htrace : ((S - T) * (S - T)).trace ≤ H)
    (hnum : (121 / 100 : ℝ) * H * (1 + R) ^ 2 ≤ Δ ^ 2) :
    ¬ FrobeniusSeparated Δ S T := by
  rintro ⟨t, ht, hsep⟩
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i⟩⟩
  · rw [trace_eq_zero_of_isEmpty] at hsep
    nlinarith only [hsep, sq_nonneg (Δ * t)]
  let v : Vec d := Pi.single i 1
  have hv0 : v ≠ 0 := by
    intro hz
    have hi := congrFun hz i
    simp only [v, Pi.single_eq_same, Pi.zero_apply, one_ne_zero] at hi
  have hq : 0 < qform S v := by
    simpa only [qform, star_trivial] using hS.dotProduct_mulVec_pos hv0
  have hr := hratio v
  have htv := ht v
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hr
  change qform S v ≤ R * qform T v at hr
  change qform T v ≤ t * qform S v at htv
  have hrt : 1 ≤ R * t := by
    have hh := mul_le_mul_of_nonneg_left htv hR.le
    nlinarith only [hr, hh, hq]
  have ht0 : 0 < t := by nlinarith only [hrt, hR]
  let c := (10 / 11 : ℝ) / (1 + t)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlower : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (S *ᵥ x) := by
    intro x
    have hs := hsum x
    have hh := ht x
    change qform T x ≤ t * qform S x at hh
    change c * sqnorm x ≤ qform S x
    dsimp only [c]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 1 + t)]
    linarith only [hs, hh]
  have hbound := Separation.trace_inv_mul_sub_one_sq_le hS hT hc hlower
  have hlt := hsep.trans_le (hbound.trans
    (div_le_div_of_nonneg_right htrace (sq_nonneg c)))
  have hinv : c⁻¹ = (11 / 10 : ℝ) * (1 + t) := by dsimp only [c]; field_simp
  rw [div_eq_mul_inv, ← inv_pow, hinv] at hlt
  have hsmall : 1 + t ≤ (1 + R) * t := by linarith only [hrt]
  have hsq : (1 + t) ^ 2 ≤ (1 + R) ^ 2 * t ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + t) hsmall 2
  have h₁ := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (121 / 100 : ℝ) * H)
  have h₂ := mul_le_mul_of_nonneg_right hnum (sq_nonneg t)
  nlinarith only [hlt, h₁, h₂]

theorem not_centered_of_common_bounds (S T : Mat d) (hS : S.PosDef) (hT : T.PosDef)
    (r : ℝ) (hr : 32 ≤ r)
    (hsum : ∀ v, (10 / 11 : ℝ) * sqnorm v ≤ qform S v + qform T v)
    (hST : LE S ((3 * r ^ 4) • T)) (hTS : LE T ((3 * r ^ 4) • S))
    (htrace : ((S - T) * (S - T)).trace ≤ 6 * r + 1) :
    ¬ CenteredSeparated (r ^ 8) S T := by
  have hr0 : 0 < r := by linarith only [hr]
  have hr1 : 1 ≤ r := by linarith only [hr]
  have hr4 : 1 ≤ r ^ 4 := one_le_pow₀ hr1
  have hR : 0 < 3 * r ^ 4 := by positivity
  have hH : 0 ≤ 6 * r + 1 := by positivity
  have hseven : 136 ≤ r ^ 7 := by
    exact (by norm_num : (136 : ℝ) ≤ 32 ^ 7).trans
      (pow_le_pow_left₀ (by norm_num) hr 7)
  have hnum : (121 / 100 : ℝ) * (6 * r + 1) * (1 + 3 * r ^ 4) ^ 2 ≤ (r ^ 8) ^ 2 := by
    calc
      _ ≤ (121 / 100 : ℝ) * (7 * r) * (4 * r ^ 4) ^ 2 := by
        gcongr <;> linarith only [hr1, hr4]
      _ = (3388 / 25 : ℝ) * r ^ 9 := by ring
      _ ≤ 136 * r ^ 9 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ ≤ r ^ 7 * r ^ 9 := mul_le_mul_of_nonneg_right hseven (by positivity)
      _ = _ := by ring
  have htwelve : 3 ≤ r ^ 12 := by
    exact (by norm_num : (3 : ℝ) ≤ 32 ^ 12).trans
      (pow_le_pow_left₀ (by norm_num) hr 12)
  have hRΔ : 3 * r ^ 4 ≤ (r ^ 8) ^ 2 := by
    calc
      _ ≤ r ^ 12 * r ^ 4 := mul_le_mul_of_nonneg_right htwelve (by positivity)
      _ = _ := by ring
  have hnsp (U V : Mat d) (hV : V.PosSemidef) (hUV : LE U ((3 * r ^ 4) • V)) :
      ¬ SpectrallySeparated (r ^ 8) U V := by
    rintro ⟨v, hv⟩
    have hh := hUV v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
    have hq : 0 ≤ v ⬝ᵥ (V *ᵥ v) := by
      simpa only [star_trivial] using hV.dotProduct_mulVec_nonneg v
    have hb := mul_le_mul_of_nonneg_right hRΔ hq
    linarith only [hv, hh, hb]
  have htrace' : ((T - S) * (T - S)).trace ≤ 6 * r + 1 := by
    rwa [← neg_sub S T, neg_mul_neg]
  intro h
  rcases h with h | h | h | h
  · exact hnsp S T hT.posSemidef hST h
  · exact hnsp T S hS.posSemidef hTS h
  · exact not_frobenius_of_common_bounds S T hS hT.1 _ _ _ hR hH
      hsum hST htrace hnum h
  · exact not_frobenius_of_common_bounds T S hT hS.1 _ _ _ hR hH
      (fun v ↦ by simpa only [add_comm] using hsum v) hTS htrace' hnum h

theorem true_upper (A B S : Mat d) (hB : B.PosSemidef)
    (hlower : LE ((0.9 : ℝ) • S) A) : LE S ((10 / 9 : ℝ) • (A + B)) := by
  intro v
  have hq : 0 ≤ qform B v := by
    simpa only [qform, star_trivial] using hB.dotProduct_mulVec_nonneg v
  have hh := hlower v
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh ⊢
  simp only [add_mulVec, dotProduct_add]
  dsimp only [qform] at hq
  linarith only [hh, hq]

theorem frob_three (D X Y : Mat d) :
    frobSq (-D - X + Y) ≤ 3 * frobSq D + 3 * frobSq X + 3 * frobSq Y := by
  simp only [frobSq, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  nlinarith only [sq_nonneg (D i j - X i j), sq_nonneg (D i j + Y i j),
    sq_nonneg (X i j + Y i j)]

/-- In the absence of a spectral ratio, separation forces a large common-frame gap. -/
theorem large_normalized_difference (A B S T : Mat d)
    (hA : A.PosDef) (hB : B.PosDef) (hS : S.PosDef) (hT : T.PosDef)
    (hlA : LE ((0.9 : ℝ) • S) A) (huA : LE A ((1.1 : ℝ) • S))
    (hlB : LE ((0.9 : ℝ) • T) B) (huB : LE B ((1.1 : ℝ) • T))
    (heA : frobSq ((CFC.sqrt S)⁻¹ * A * (CFC.sqrt S)⁻¹ - 1) ≤ 1 / 100)
    (heB : frobSq ((CFC.sqrt T)⁻¹ * B * (CFC.sqrt T)⁻¹ - 1) ≤ 1 / 100)
    (r : ℝ) (hr : 32 ≤ r) (hsep : CenteredSeparated (r ^ 8) S T)
    (hAB : LE A ((2 * r ^ 4) • B)) (hBA : LE B ((2 * r ^ 4) • A)) :
    let W := (CFC.sqrt (A + B))⁻¹
    2 * r ≤ frobSq (W * (B - A) * W) := by
  let E := A + B
  let Z := CFC.sqrt E
  let W := Z⁻¹
  have hE : E.PosDef := hA.add hB
  obtain ⟨hZt, hZd, hZZ⟩ := Robust.RBAux.sqrt_properties E hE
  change Zᵀ = Z at hZt
  change Z * Z = E at hZZ
  have hZ : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZd
  have hWt : Wᵀ = W := by simp only [W, transpose_nonsing_inv, hZt]
  have hW : IsUnit W.det := isUnit_det_of_left_inverse (mul_nonsing_inv Z hZ)
  have hwhite : W * E * W = 1 := by
    rw [← hZZ]
    simp only [W, ← mul_assoc, nonsing_inv_mul _ hZ, one_mul, mul_nonsing_inv _ hZ]
  have hcon (X : Mat d) (v : Vec d) : qform (W * X * W) v = qform X (W *ᵥ v) := by
    simpa only [hWt] using Robust.RBAux.qform_conjugate W X v
  let P := W * S * W
  let U := W * T * W
  let D := W * (B - A) * W
  let X := W * (A - S) * W
  let Y := W * (B - T) * W
  have hP : P.PosDef := by
    simpa only [P, conjTranspose_eq_transpose_of_trivial, hWt] using
      hS.conjTranspose_mul_mul_same
        (mulVec_injective_of_isUnit (W.isUnit_iff_isUnit_det.mpr hW))
  have hU : U.PosDef := by
    simpa only [U, conjTranspose_eq_transpose_of_trivial, hWt] using
      hT.conjTranspose_mul_mul_same
        (mulVec_injective_of_isUnit (W.isUnit_iff_isUnit_det.mpr hW))
  have hsep' : CenteredSeparated (r ^ 8) P U := by
    have hh := (Separation.centeredSeparated_congr (T := W) hW).mpr hsep
    simpa only [hWt] using hh
  have hsum : ∀ v, (10 / 11 : ℝ) * sqnorm v ≤ qform P v + qform U v := by
    intro v
    have hqa := huA (W *ᵥ v)
    have hqb := huB (W *ᵥ v)
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hqa hqb
    have he : qform A (W *ᵥ v) + qform B (W *ᵥ v) = sqnorm v := by
      dsimp only [qform]
      rw [← dotProduct_add, ← add_mulVec]
      change qform E (W *ᵥ v) = sqnorm v
      rw [← hcon, hwhite]
      simp only [qform, one_mulVec, sqnorm]
    change (10 / 11 : ℝ) * sqnorm v ≤ qform (W * S * W) v + qform (W * T * W) v
    rw [hcon, hcon]
    dsimp only [qform] at he ⊢
    linarith only [he, hqa, hqb]
  have hratio (A₁ B₁ S₁ T₁ : Mat d) (hT₁ : T₁.PosSemidef)
      (hl : LE ((0.9 : ℝ) • S₁) A₁) (hu : LE B₁ ((1.1 : ℝ) • T₁))
      (hAB₁ : LE A₁ ((2 * r ^ 4) • B₁)) :
      LE (W * S₁ * W) ((3 * r ^ 4) • (W * T₁ * W)) := by
    intro v
    have hlv := hl (W *ᵥ v)
    have huv := hu (W *ᵥ v)
    have habv := hAB₁ (W *ᵥ v)
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hlv huv habv
    have hm := mul_le_mul_of_nonneg_left huv (by positivity : 0 ≤ 2 * r ^ 4)
    have hq : 0 ≤ qform T₁ (W *ᵥ v) := by
      simpa only [qform, star_trivial] using hT₁.dotProduct_mulVec_nonneg (W *ᵥ v)
    have hpos := mul_nonneg (pow_nonneg (by linarith only [hr] : 0 ≤ r) 4) hq
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul]
    change qform (W * S₁ * W) v ≤ (3 * r ^ 4) * qform (W * T₁ * W) v
    rw [hcon, hcon]
    dsimp only [qform] at hpos ⊢
    nlinarith only [hlv, habv, hm, hpos]
  have hPS : LE S ((10 / 9 : ℝ) • E) := true_upper A B S hB.posSemidef hlA
  have hUT : LE T ((10 / 9 : ℝ) • E) := by
    simpa only [add_comm] using true_upper B A T hA.posSemidef hlB
  have hX : frobSq X ≤ 1 / 81 := by
    have hh := normalized_error A S E W hA.1 hS hE.posSemidef hWt hwhite
      (10 / 9) (by norm_num) hPS heA
    norm_num at hh
    exact hh
  have hY : frobSq Y ≤ 1 / 81 := by
    have hh := normalized_error B T E W hB.1 hT hE.posSemidef hWt hwhite
      (10 / 9) (by norm_num) hUT heB
    norm_num at hh
    exact hh
  change 2 * r ≤ frobSq D
  by_contra hv
  have hdiff : P - U = -D - X + Y := by
    dsimp only [P, U, D, X, Y]
    noncomm_ring
  have htrace : ((P - U) * (P - U)).trace ≤ 6 * r + 1 := by
    rw [Tree.CompleteAux.trace_sq _ (hP.1.sub hU.1), hdiff]
    have hh := frob_three D X Y
    linarith only [hh, hX, hY, lt_of_not_ge hv]
  exact not_centered_of_common_bounds P U hP hU r hr hsum
    (hratio A B S T hT.posSemidef hlA huB hAB)
    (hratio B A T S hS.posSemidef hlB huA hBA) htrace hsep'

def differenceMatrix (A B : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  (A + B)⁻¹ * (B - A) * (A + B)⁻¹

theorem differenceMatrix_properties (A B : Matrix (Fin d) (Fin d) ℚ)
    (hA : (A.map (algebraMap ℚ ℝ)).PosDef) (hB : (B.map (algebraMap ℚ ℝ)).PosDef) :
    let A' := A.map (algebraMap ℚ ℝ)
    let B' := B.map (algebraMap ℚ ℝ)
    let E := A' + B'
    let R := (differenceMatrix A B).map (algebraMap ℚ ℝ)
    let W := (CFC.sqrt E)⁻¹
    Rᵀ = R ∧ (R * (B' - A')).trace = (R * E * R * E).trace ∧
      (R * E * R * E).trace = frobSq (W * (B' - A') * W) := by
  let f : Matrix (Fin d) (Fin d) ℚ →+* Mat d := (algebraMap ℚ ℝ).mapMatrix
  let A' := A.map (algebraMap ℚ ℝ)
  let B' := B.map (algebraMap ℚ ℝ)
  let E := A' + B'
  let R := (differenceMatrix A B).map (algebraMap ℚ ℝ)
  have hE : E.PosDef := hA.add hB
  have hEcast : (A + B).map (algebraMap ℚ ℝ) = E := map_add f A B
  have hEd : IsUnit E.det := isUnit_iff_ne_zero.mpr hE.det_pos.ne'
  have hR : R = E⁻¹ * (B' - A') * E⁻¹ := by
    change f ((A + B)⁻¹ * (B - A) * (A + B)⁻¹) = _
    rw [map_mul, map_mul, map_sub]
    have hi := cast_inv (A + B) (hEcast.symm ▸ hE)
    change f (A + B)⁻¹ = _ at hi
    rw [hi, hEcast]
    rfl
  have hAt : A'ᵀ = A' := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.1
  have hBt : B'ᵀ = B' := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hB.1
  have hEt : Eᵀ = E := by simp only [E, transpose_add, hAt, hBt]
  have hRt : Rᵀ = R := by
    simp only [hR, transpose_mul, transpose_nonsing_inv, hEt, transpose_sub,
      hAt, hBt, mul_assoc]
  have hRE : R * E = E⁻¹ * (B' - A') := by
    rw [hR, mul_assoc, nonsing_inv_mul _ hEd, mul_one]
  have hgap : (R * (B' - A')).trace = (R * E * R * E).trace := by
    symm
    calc
      _ = ((R * E) * (R * E)).trace := by simp only [mul_assoc]
      _ = ((E⁻¹ * (B' - A')) * (E⁻¹ * (B' - A'))).trace := by rw [hRE]
      _ = _ := by rw [hR]; simp only [mul_assoc]
  let Z := CFC.sqrt E
  let W := Z⁻¹
  obtain ⟨hZt, hZd, hZZ⟩ := Robust.RBAux.sqrt_properties E hE
  change Zᵀ = Z at hZt
  change Z * Z = E at hZZ
  have hZ : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZd
  have hWt : Wᵀ = W := by simp only [W, transpose_nonsing_inv, hZt]
  have hwhite : W * E * W = 1 := by
    rw [← hZZ]
    simp only [W, ← mul_assoc, nonsing_inv_mul _ hZ, one_mul, mul_nonsing_inv _ hZ]
  have hEi : E⁻¹ = W * W := by rw [← hZZ, Matrix.mul_inv_rev]
  have hnorm : R = W * (W * (B' - A') * W) * W := by
    rw [hR, hEi]
    simp only [mul_assoc]
  have hD : (W * (B' - A') * W).IsHermitian := by
    simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial, transpose_mul,
      transpose_sub, hWt, hAt, hBt, mul_assoc]
  refine ⟨hRt, hgap, ?_⟩
  change (R * E * R * E).trace = frobSq (W * (B' - A') * W)
  rw [hnorm]
  exact trace_whitened_square W (W * (B' - A') * W) E hD hwhite

end

end ABBKS26.Select.PairwiseAux
