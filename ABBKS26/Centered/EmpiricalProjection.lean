module

public import ABBKS26.Centered.EmpiricalTransfer

/-! Shared analytic preparation for the rounded empirical centered system. -/

@[expose] public section

namespace ABBKS26.Centered.EmpiricalProjection

open Common Matrix MvPolynomial Rounding
open scoped BigOperators

noncomputable section

variable {k d : ℕ}

/-- Eigenvalues at most one half give a projection controlled by squared deviation.
Every vector of small covariance has almost all of its mass in this projection. -/
theorem low_projection (A : Mat d) (hA : A.PosSemidef) :
    ∃ P : Mat d, Projection P ∧ LE ((1 / 4 : ℝ) • P) ((A - 1) * (A - 1)) ∧
      ∀ v, sqnorm ((1 - P) *ᵥ v) ≤ 2 * qform A v := by
  classical
  let b : Fin d → ℝ := fun j ↦ if hA.1.eigenvalues j ≤ 1 / 2 then 1 else 0
  let D : Mat d := diagonal hA.1.eigenvalues
  let B : Mat d := diagonal b
  let U := hA.1.eigenvectorUnitary
  let φ : Mat d ≃⋆ₐ[ℝ] Mat d := Unitary.conjStarAlgAut ℝ _ U
  have hspec : φ D = A := by
    simpa only [φ, D, RCLike.ofReal_real_eq_id, Function.id_comp] using
      hA.1.spectral_theorem.symm
  have hBB : B * B = B := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    dsimp only [b]
    split_ifs <;> norm_num
  have hBt : (φ B)ᵀ = φ B := by
    change star (φ B) = φ B
    rw [← map_star]
    congr 1
    exact diagonal_transpose _
  have hP : Projection (φ B) := ⟨hBt, by rw [← map_mul, hBB]⟩
  have hs : ((D - 1) * (D - 1) - (1 / 4 : ℝ) • B).PosSemidef := by
    have hdiff : D - 1 = diagonal (fun j ↦ hA.1.eigenvalues j - 1) := by
      dsimp only [D]
      rw [← diagonal_one, ← diagonal_sub]
    have he : (D - 1) * (D - 1) - (1 / 4 : ℝ) • B =
        diagonal (fun j ↦ (hA.1.eigenvalues j - 1) ^ 2 - (1 / 4) * b j) := by
      rw [hdiff, diagonal_mul_diagonal]
      dsimp only [B]
      rw [← diagonal_smul, ← diagonal_sub]
      simp only [pow_two]
      congr 1
    rw [he]
    apply posSemidef_diagonal_iff.mpr
    intro j
    dsimp only [b]
    split_ifs with hj
    · nlinarith only [hj, hA.eigenvalues_nonneg j]
    · simpa only [mul_zero, sub_zero] using sq_nonneg (hA.1.eigenvalues j - 1)
  have hs' := hs.mul_mul_conjTranspose_same (U : Mat d)
  change (φ ((D - 1) * (D - 1) - (1 / 4 : ℝ) • B)).PosSemidef at hs'
  rw [map_sub, map_mul, map_sub, map_one, map_smul, hspec] at hs'
  have hl : (D - (1 / 2 : ℝ) • (1 - B)).PosSemidef := by
    have hdiff : 1 - B = diagonal (fun j ↦ 1 - b j) := by
      dsimp only [B]
      rw [← diagonal_one, ← diagonal_sub]
    have he : D - (1 / 2 : ℝ) • (1 - B) =
        diagonal (fun j ↦ hA.1.eigenvalues j - (1 / 2) * (1 - b j)) := by
      rw [hdiff]
      dsimp only [D]
      rw [← diagonal_smul, ← diagonal_sub]
      rfl
    rw [he]
    apply posSemidef_diagonal_iff.mpr
    intro j
    dsimp only [b]
    split_ifs with hj
    · simpa using hA.eigenvalues_nonneg j
    · have hj' : 1 / 2 < hA.1.eigenvalues j := lt_of_not_ge hj
      linarith only [hj']
  have hl' := hl.mul_mul_conjTranspose_same (U : Mat d)
  change (φ (D - (1 / 2 : ℝ) • (1 - B))).PosSemidef at hl'
  rw [map_sub, map_smul, map_sub, map_one, hspec] at hl'
  refine ⟨φ B, hP, ?_, ?_⟩
  · intro v
    have hv := hs'.dotProduct_mulVec_nonneg v
    change 0 ≤ qform ((A - 1) * (A - 1) - (1 / 4 : ℝ) • φ B) v at hv
    simp only [qform, sub_mulVec, dotProduct_sub] at hv
    exact sub_nonneg.mp hv
  · intro v
    have hv := hl'.dotProduct_mulVec_nonneg v
    have hn := DetRoundAux.projection_sqnorm (1 - φ B)
      (DetRoundAux.projection_compl _ hP) v
    change 0 ≤ qform (A - (1 / 2 : ℝ) • (1 - φ B)) v at hv
    change sqnorm ((1 - φ B) *ᵥ v) = qform (1 - φ B) v at hn
    rw [hn]
    simp only [qform, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at hv
    simp only [qform, sub_mulVec, dotProduct_sub]
    linarith only [hv]

theorem thin_near (A P : Mat d) (hP : Projection P) (μ : ℝ) (hμ : 0 ≤ μ)
    (hl : ∀ v, sqnorm ((1 - P) *ᵥ v) ≤ 2 * qform A v)
    (v : Vec d) (hv : sqnorm v = 1) (ht : qform A v ≤ 3 * μ ^ 8) :
    1 - 7 * μ ^ 8 ≤ sqnorm (P *ᵥ v) := by
  have he : sqnorm (P *ᵥ v) + sqnorm ((1 - P) *ᵥ v) = 1 := by
    rw [DetRoundAux.projection_sqnorm P hP,
      DetRoundAux.projection_sqnorm (1 - P) (DetRoundAux.projection_compl P hP)]
    simp only [qform, sub_mulVec, one_mulVec, dotProduct_sub]
    exact add_sub_cancel (v ⬝ᵥ (P *ᵥ v)) (sqnorm v) ▸ hv
  nlinarith only [he, hl v, ht, pow_nonneg hμ 8]

theorem derives_slacken (A : FamilySystem d) (P : Mat d) (ε ε' M X : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ ε')
    (h : A.Derives 8 M X (C ε - quad P)) :
    A.Derives 8 (M + ε') X (C ε' - quad P) := by
  obtain ⟨Ξ, hΞ, h⟩ := h
  have hs : A.DerivesAt Ξ 8 ε' (C (ε' - ε)) := by
    apply FamilySystem.DerivesAt.ofIsSOS A Ξ
      (SoS.isSumSq_C (sub_nonneg.mpr hε')) (by rw [totalDegree_C]; omega)
    rw [SoS.coeffNorm1_C, abs_of_nonneg (sub_nonneg.mpr hε')]
    linarith only [hε]
  exact ⟨Ξ, hΞ, (h.add hs).congr (by rw [C_sub]; ring)⟩

/-- The rounded empirical system certifies the low-covariance projection. Its norm
depends on explicit family envelopes, rather than on the hidden projection's entries. -/
theorem low_certificate {k : ℕ} (F : FrameModel k d) (w μ g r W X B : ℝ)
    (Ψ : RPoly d) (hF : DataValid F w g r)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hμ : 0 < μ ∧ μ ≤ 1 / 64)
    (hg : g ≤ (w ^ 8 * μ ^ 32) ^ 2 / 20) (hΨ : Ψ.IsHomogeneous 4)
    (he : IsSumSq (C ((w ^ 8 * μ ^ 32) ^ 4) * nsq ^ 4 - (Ψ - psi F) ^ 2))
    (hW : 64 * (d + 1 : ℝ) ^ 2 + 1 / w +
      1 / (12 * (w ^ 8 * μ ^ 32) ^ 2) + 1 / (μ ^ 8 / 100) ≤ W)
    (hW2 : 2 ≤ W) (hX : Real.sqrt d * (1.1 / w) ≤ X) (hB : 1 ≤ B)
    (hnq : SoS.coeffNorm1 (qConstraint (psi F) (12 * (w ^ 8 * μ ^ 32) ^ 2)) +
      2 * SoS.coeffNorm1 (qConstraint Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2)) + 2 ≤ B)
    (hnh : (SoS.coeffNorm1 (hConstraint (psi F)
        (513 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)) +
      2 * SoS.coeffNorm1 (hConstraint Ψ (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2))) *
        (1 + d * X) ^ 8 + 2 ≤ B)
    (i : Fin k) :
    ∃ P : Mat d, Projection P ∧
      (system Ψ (8 * (w ^ 8 * μ ^ 32) ^ 2)
        (256 * (w ^ 8 * μ ^ 32) ^ 2 / w ^ 2)).Derives
        8 (W ^ 24 * (1 + 3 * B) + 7 * μ ^ 8) X (C (7 * μ ^ 8) - quad P) ∧
      ∀ v, sqnorm v = 1 → qform (F.cov i) v ≤ 3 * μ ^ 8 →
        1 - 7 * μ ^ 8 ≤ sqnorm (P *ᵥ v) := by
  have hw0 := hw.1
  let t := w ^ 8 * μ ^ 32
  obtain ⟨ht, _, _, hg2, he0, he1, hh0, hh1, hev, _, _, hqtr, hhtr⟩ :=
    ThmZAux.schedule w μ g hw hμ ⟨hF.2.2.1.1, hg⟩
  obtain ⟨P, hP, hspec, hnear⟩ := low_projection (F.cov i) (hF.1.2.2.2 i).posSemidef
  have hev' := eval_ident F w g r (12 * t ^ 2) (513 * t ^ 2 / w ^ 2)
    (μ ^ 8 / 100) W i hF hw.2 ⟨he0, he1⟩ (by positivity) ⟨hh0, hh1⟩ hev hW
  have hspec' : LE (((1 / 2 : ℝ) ^ 2) • P)
      ((F.cov i - 1) * (F.cov i - 1)) := by norm_num; exact hspec
  have heigen := eigen_ident F w g r (12 * t ^ 2) (513 * t ^ 2 / w ^ 2)
    (μ ^ 8 / 100) (1 / 2) W i P hF (by norm_num) hP hspec' hW2
      (by norm_num; exact hW2) (by
        have hp : 0 ≤ 1 / (12 * t ^ 2) := by positivity
        have he : 0 ≤ 1 / (μ ^ 8 / 100) := by positivity
        linarith only [hW, hp, he]) hev'
  let ε : ℝ := (2 * (μ ^ 8 / 100) + 2 * g ^ 2) / (1 / 2) ^ 2
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hε' : ε ≤ 7 * μ ^ 8 := by
    dsimp only [ε]
    norm_num
    nlinarith only [hg2, pow_nonneg hμ.1.le 8]
  have hX0 : 0 ≤ X := (by positivity : 0 ≤ Real.sqrt (d : ℝ) * (1.1 / w)).trans hX
  have heigen' : (system (psi F) (12 * t ^ 2) (513 * t ^ 2 / w ^ 2)).Derives
      8 (W ^ 24) X (C ε - quad P) := by
    obtain ⟨Ξ, hΞ, hd⟩ := heigen
    refine ⟨Ξ, fun a ↦ (hΞ a).trans ?_, hd⟩
    exact pow_le_pow_left₀ (by positivity) hX 2
  have he' : IsSumSq (C (t ^ 4) * nsq ^ 4 - (psi F - Ψ) ^ 2) := by
    convert he using 1
    ring
  have htr := transfer Ψ (psi F) (t ^ 4) (8 * t ^ 2) (256 * t ^ 2 / w ^ 2)
    (12 * t ^ 2) (513 * t ^ 2 / w ^ 2) hΨ (IdentAux.psi_homogeneous F)
      (by positivity) he' hqtr hhtr
  have hcert := EmpiricalTransfer.derives_transfer Ψ (psi F)
    (8 * t ^ 2) (256 * t ^ 2 / w ^ 2) (12 * t ^ 2) (513 * t ^ 2 / w ^ 2)
    (W ^ 24) X B hΨ (IdentAux.psi_homogeneous F) hX0 hB
      htr.1 htr.2 hnq hnh (C ε - quad P) heigen'
  exact ⟨P, hP, derives_slacken _ P ε _ _ X hε hε' hcert,
    fun v hv ht ↦ thin_near (F.cov i) P hP μ hμ.1.le hnear v hv ht⟩

end

end ABBKS26.Centered.EmpiricalProjection
