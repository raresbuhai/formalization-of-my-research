module

public import BGHKLMM26.Model
public import BGHKLMM26.IntGap.Tensor

/-!
# From approximate to exact triangle inequalities

A positive semidefinite kernel with unit diagonal that satisfies the signed triangle inequalities
up to `3ε` gives an exact solution of the SDP (`BGHKLMM26.IsSDPSolution`) after mixing with the
identity: the Gram matrix `(1 - δ) K + δ I`, `δ ≥ 3ε`, scales every off-diagonal entry by `1 - δ`,
and `(1 - δ)(1 + 3ε) ≤ 1` (`BGHKLMM26.IntGap.sdp_of_kernel`).
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open scoped RealInnerProductSpace

/-- **Mixing with the identity** turns approximate signed triangle inequalities into exact ones:
the vectors have Gram matrix `(1 - δ) K + δ I`. -/
theorem sdp_of_kernel {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.PosSemidef)
    (hdiag : ∀ i, K i i = 1) {ε δ : ℝ} (hε : 0 ≤ ε) (hεδ : 3 * ε ≤ δ) (hδ1 : δ ≤ 1)
    (htri : ∀ i j k : Fin n, ∀ a ∈ ({1, -1} : Set ℝ), ∀ b ∈ ({1, -1} : Set ℝ),
      ∀ c ∈ ({1, -1} : Set ℝ), -1 - 3 * ε ≤ a * b * K i j + a * c * K i k + b * c * K j k) :
    ∃ v : Fin n → EuclideanSpace ℝ (Fin n), IsSDPSolution n v ∧
      ∀ i j, i ≠ j → ⟪v i, v j⟫ = (1 - δ) * K i j := by
  have hδ0 : 0 ≤ δ := by linarith
  have hδ1' : 0 ≤ 1 - δ := by linarith
  obtain ⟨v, hv⟩ := exists_gram_vectors ((1 - δ) • K + δ • 1)
    ((hK.smul hδ1').add (Matrix.PosSemidef.one.smul hδ0))
  have hoff : ∀ i j, i ≠ j → ⟪v i, v j⟫ = (1 - δ) * K i j := fun i j hij ↦ by
    simp [hv, Matrix.one_apply_ne hij]
  refine ⟨v, ⟨fun i ↦ ?_, fun i j k hij hik hjk a ha b hb c hc ↦ ?_⟩, hoff⟩
  · have h1 : ⟪v i, v i⟫ = 1 := by rw [hv]; simp [hdiag]
    rw [real_inner_self_eq_norm_sq] at h1
    nlinarith [norm_nonneg (v i)]
  · rw [hoff i j hij, hoff i k hik, hoff j k hjk]
    have h := mul_le_mul_of_nonneg_left (htri i j k a ha b hb c hc) hδ1'
    nlinarith [mul_nonneg hε hδ0]

end BGHKLMM26.IntGap
