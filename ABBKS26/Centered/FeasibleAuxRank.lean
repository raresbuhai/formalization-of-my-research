module

public import ABBKS26.Centered.Ident

/-! Spectral truncation of the total covariance error energy. -/

@[expose] public section

namespace ABBKS26.Centered.FeasibleAux

noncomputable section

open Common Matrix
open scoped BigOperators

variable {d : ℕ}

private theorem spectral_capture (A : Mat d) (hA : A.PosSemidef)
    (t : ℝ) (_ht : 0 < t) :
    ∃ R : Mat d, Projection R ∧ t * R.rank ≤ A.trace ∧
      ∀ v, qform A ((1 - R) *ᵥ v) ≤ t * sqnorm ((1 - R) *ᵥ v) := by
  classical
  let b : Fin d → ℝ := fun j ↦ if t < hA.1.eigenvalues j then 1 else 0
  let D : Mat d := diagonal hA.1.eigenvalues
  let B : Mat d := diagonal b
  let U := hA.1.eigenvectorUnitary
  let φ : Mat d ≃⋆ₐ[ℝ] Mat d := Unitary.conjStarAlgAut ℝ _ U
  have hspec : φ D = A := by
    simpa only [φ, D, RCLike.ofReal_real_eq_id, Function.id_comp] using
      hA.1.spectral_theorem.symm
  have hb (j : Fin d) : b j = 0 ∨ b j = 1 := by
    dsimp only [b]
    split_ifs <;> simp
  have hBB : B * B = B := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    rcases hb j with h | h <;> simp [h]
  have hBt : (φ B)ᵀ = φ B := by
    change star (φ B) = φ B
    rw [← map_star]
    congr 1
    exact diagonal_transpose _
  have hR : Projection (φ B) := ⟨hBt, by rw [← map_mul, hBB]⟩
  have hdiag : (D - t • B).PosSemidef := by
    rw [show D - t • B = diagonal (fun j ↦ hA.1.eigenvalues j - t * b j) by
      simp [D, B, ← diagonal_smul, ← diagonal_sub, smul_eq_mul]]
    apply posSemidef_diagonal_iff.mpr
    intro j
    dsimp only [b]
    split_ifs with hj
    · linarith
    · simpa using hA.eigenvalues_nonneg j
  have htr : 0 ≤ (A - t • φ B).trace := by
    have hp := hdiag.mul_mul_conjTranspose_same (U : Mat d)
    change (φ (D - t • B)).PosSemidef at hp
    rw [map_sub, map_smul, hspec] at hp
    exact hp.trace_nonneg
  rw [trace_sub, trace_smul, Rounding.DetRoundAux.trace_projection_rank _ hR,
    smul_eq_mul] at htr
  refine ⟨φ B, hR, by linarith, ?_⟩
  have hcomp : (t • (1 - B) - (1 - B) * D * (1 - B)).PosSemidef := by
    have hid : t • (1 - B) - (1 - B) * D * (1 - B) =
        diagonal (fun j ↦ t * (1 - b j) - (1 - b j) ^ 2 * hA.1.eigenvalues j) := by
      have hc : 1 - B = diagonal (fun j ↦ 1 - b j) := by
        dsimp only [B]
        rw [← diagonal_one, ← diagonal_sub]
      dsimp only [D]
      rw [hc, diagonal_mul_diagonal, diagonal_mul_diagonal,
        ← diagonal_smul, ← diagonal_sub]
      congr 1
      funext j
      ring_nf
    rw [hid]
    apply posSemidef_diagonal_iff.mpr
    intro j
    dsimp only [b]
    split_ifs with hj
    · simp
    · simp only [sub_zero, mul_one, one_pow, one_mul]
      linarith
  have hp := hcomp.mul_mul_conjTranspose_same (U : Mat d)
  change (φ (t • (1 - B) - (1 - B) * D * (1 - B))).PosSemidef at hp
  rw [map_sub, map_smul, map_mul, map_mul, map_sub, map_one, hspec] at hp
  intro v
  have hv := hp.dotProduct_mulVec_nonneg v
  have he : qform ((1 - φ B) * A * (1 - φ B)) v =
      qform A ((1 - φ B) *ᵥ v) := by
    unfold qform
    rw [← mulVec_mulVec, ← mulVec_mulVec,
      ← Rounding.DetRoundAux.projection_dot _
        (Rounding.DetRoundAux.projection_compl _ hR)]
  have hn := Rounding.DetRoundAux.projection_sqnorm (1 - φ B)
    (Rounding.DetRoundAux.projection_compl _ hR) v
  change sqnorm ((1 - φ B) *ᵥ v) = qform (1 - φ B) v at hn
  change 0 ≤ qform (t • (1 - φ B) - (1 - φ B) * A * (1 - φ B)) v at hv
  simp only [qform, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at hv
  change qform A ((1 - φ B) *ᵥ v) ≤ _
  rw [hn]
  simp only [qform, sub_mulVec, dotProduct_sub] at he ⊢
  linarith

private theorem gram_qform (A : Mat d) (v : Vec d) :
    qform (Aᵀ * A) v = sqnorm (A *ᵥ v) := by
  rw [qform, sqnorm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

private theorem gram_trace (A : Mat d) : (Aᵀ * A).trace = frobSq A := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply, frobSq, pow_two]
  exact Finset.sum_comm

private theorem energy_sub (x y v : Vec d) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : sqnorm x ≤ a ^ 2 * sqnorm v) (hy : sqnorm y ≤ b ^ 2 * sqnorm v) :
    sqnorm (x - y) ≤ (a + b) ^ 2 * sqnorm v := by
  let X : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 x
  let Y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 y
  let V : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
  have hx' : ‖X‖ ≤ a * ‖V‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))).mp
    simpa only [X, V, mul_pow, Rounding.DetRoundAux.euclidean_sqnorm] using hx
  have hy' : ‖Y‖ ≤ b * ‖V‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (norm_nonneg _))).mp
    simpa only [Y, V, mul_pow, Rounding.DetRoundAux.euclidean_sqnorm] using hy
  have hn : ‖X - Y‖ ≤ (a + b) * ‖V‖ := by
    calc
      _ ≤ ‖X‖ + ‖Y‖ := norm_sub_le _ _
      _ ≤ a * ‖V‖ + b * ‖V‖ := add_le_add hx' hy'
      _ = _ := by ring
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [X, Y, V, ← WithLp.toLp_sub, mul_pow,
    Rounding.DetRoundAux.euclidean_sqnorm] using hs

/-- Truncating the weighted total error energy controls every component. -/
theorem rank_complement {k : ℕ} (F : FrameModel k d) (w γ rF δ : ℝ)
    (hF : DataValid F w γ rF) (hδ : 0 < δ) :
    ∃ R : Mat d, Projection R ∧ R.rank ≤ ⌊rF / (w * δ ^ 2)⌋₊ ∧
      ∀ i v, sqnorm (deviation F i *ᵥ ((1 - R) *ᵥ v)) ≤
        (δ + γ) ^ 2 * sqnorm ((1 - R) *ᵥ v) := by
  classical
  let A : Fin k → Mat d := fun i ↦ F.cov i - 1
  let M : Mat d := ∑ i, F.weight i • ((A i)ᵀ * A i)
  have hw (i : Fin k) : 0 ≤ F.weight i := hF.1.1.le.trans (hF.1.2.1 i)
  have hM : M.PosSemidef := by
    apply posSemidef_sum
    intro i _
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (posSemidef_conjTranspose_mul_self (A i)).smul (hw i)
  have htrace : M.trace ≤ rF := by
    simp only [M, trace_sum, trace_smul, smul_eq_mul, gram_trace]
    calc
      _ ≤ ∑ i, F.weight i * rF := Finset.sum_le_sum fun i _ ↦
        mul_le_mul_of_nonneg_left (hF.2.2.2.2 i) (hw i)
      _ = rF := by rw [← Finset.sum_mul, hF.1.2.2.1, one_mul]
  have ht : 0 < w * δ ^ 2 := mul_pos hF.1.1 (sq_pos_of_pos hδ)
  obtain ⟨R, hR, hrank, hbound⟩ := spectral_capture M hM (w * δ ^ 2) ht
  refine ⟨R, hR, ?_, ?_⟩
  · apply (Nat.le_floor_iff (div_nonneg (hM.trace_nonneg.trans htrace) ht.le)).mpr
    exact (le_div_iff₀ ht).mpr (by nlinarith [hrank.trans htrace])
  · intro i v
    let z := (1 - R) *ᵥ v
    have he : sqnorm (A i *ᵥ z) ≤ δ ^ 2 * sqnorm z := by
      have hsum : qform M z = ∑ j, F.weight j * sqnorm (A j *ᵥ z) := by
        simp only [M, qform, sum_mulVec, dotProduct_sum, smul_mulVec,
          dotProduct_smul, smul_eq_mul]
        change (∑ j, F.weight j * qform ((A j)ᵀ * A j) z) = _
        simp only [gram_qform]
      have hi : F.weight i * sqnorm (A i *ᵥ z) ≤ qform M z := by
        rw [hsum]
        exact Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw j)
          (Rounding.DetRoundAux.sqnorm_nonneg (A j *ᵥ z))) (Finset.mem_univ i)
      have hi' := mul_le_mul_of_nonneg_right (hF.1.2.1 i)
        (Rounding.DetRoundAux.sqnorm_nonneg (A i *ᵥ z))
      have hb := hbound v
      change qform M z ≤ w * δ ^ 2 * sqnorm z at hb
      nlinarith [hi'.trans (hi.trans hb)]
    have hav : sqnorm ((averageCov F - 1) *ᵥ z) ≤ γ ^ 2 * sqnorm z := by
      have hs : (averageCov F - 1)ᵀ = averageCov F - 1 := by
        rw [transpose_sub, transpose_one,
          IdentAux.average_symm F (fun j ↦ (hF.1.2.2.2 j).isHermitian)]
      have hp := (IdentAux.operator_square (averageCov F - 1) hs γ hF.2.2.1.1
        (IdentAux.average_error_bound F w γ rF hF)).dotProduct_mulVec_nonneg z
      change 0 ≤ qform (γ ^ 2 • (1 : Mat d) -
        (averageCov F - 1) * (averageCov F - 1)) z at hp
      have heq : (averageCov F - 1) * (averageCov F - 1) =
          (averageCov F - 1)ᵀ * (averageCov F - 1) := by rw [hs]
      rw [heq] at hp
      simp only [qform, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
        dotProduct_smul, smul_eq_mul] at hp
      have hg := gram_qform (averageCov F - 1) z
      dsimp only [qform, sqnorm] at hg ⊢
      linarith
    have hd : deviation F i *ᵥ z = A i *ᵥ z - (averageCov F - 1) *ᵥ z := by
      simp only [deviation, A, sub_mulVec, one_mulVec]
      abel
    rw [hd]
    exact energy_sub _ _ z δ γ hδ.le hF.2.2.1.1 he hav

end

end ABBKS26.Centered.FeasibleAux
