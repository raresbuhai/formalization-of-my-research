module

public import ABBKS26.Rounding.DetRoundAux
public import ABBKS26.Linalg.Separation

/-! Quadratic form estimates for the statistical part of the filter. -/

@[expose] public section

namespace ABBKS26.Robust.FilterAux

open Common Matrix
open scoped BigOperators

noncomputable section

theorem sqnorm_mulVec_le {d : ℕ} (A : Mat d) (x : Vec d) :
    sqnorm (A *ᵥ x) ≤ frobSq A * sqnorm x := by
  have h (i : Fin d) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) x
  calc
    _ = ∑ i, (∑ j, A i j * x j) ^ 2 := by simp [sqnorm, mulVec, dotProduct, pow_two]
    _ ≤ ∑ i, (∑ j, A i j ^ 2) * (∑ j, x j ^ 2) := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by simp [frobSq, sqnorm, dotProduct, pow_two, Finset.sum_mul]

theorem sqnorm_sub_le {d : ℕ} (x y : Vec d) :
    sqnorm (x - y) ≤ (3 / 2 : ℝ) * sqnorm x + 3 * sqnorm y := by
  simp only [sqnorm, dotProduct, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith only [sq_nonneg (x i + 2 * y i)]

private theorem upper_psd {d : ℕ} (S : Mat d) (hS : S.PosSemidef) (c : ℝ)
    (h : ∀ v, qform S v ≤ c * sqnorm v) : (c • (1 : Mat d) - S).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · have hc : IsSelfAdjoint c := by simp only [IsSelfAdjoint, star_trivial]
    exact (Matrix.isHermitian_one.smul hc).sub hS.1
  · intro v
    simpa only [qform, sqnorm, sub_mulVec, smul_mulVec, one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, star_trivial, sub_nonneg] using h v

private theorem trace_square {d : ℕ} (A : Mat d) (hA : Aᵀ = A) :
    (A * A).trace = frobSq A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, frobSq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : A j i = A i j := congrFun (congrFun hA i) j
  rw [he, pow_two]

theorem trace_quadratic_le {d : ℕ} (A S : Mat d) (hA : Aᵀ = A) (hS : S.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ v, qform S v ≤ c * sqnorm v) :
    (A * S * A * S).trace ≤ c ^ 2 * frobSq A := by
  have hdiff := upper_psd S hS c h
  have hAA : (A * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have hASA : (A * S * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      hS.mul_mul_conjTranspose_same A
  have h₁ := Separation.trace_mul_le_trace_mul hdiff hASA
  have h₂ := Separation.trace_mul_le_trace_mul hdiff hAA
  simp only [smul_mul, one_mul, trace_smul, smul_eq_mul, trace_square A hA] at h₁ h₂
  have he : (A * S * A).trace = (S * (A * A)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [← he] at h₂
  calc
    _ = (S * (A * S * A)).trace := Matrix.trace_mul_comm _ _
    _ ≤ c * (A * S * A).trace := h₁
    _ ≤ c * (c * frobSq A) := mul_le_mul_of_nonneg_left h₂ hc
    _ = _ := by ring

theorem quadratic_variance_le {d : ℕ} (A S : Mat d) (ν δ : Vec d)
    (hA : Aᵀ = A) (hn : frobSq A ≤ 1) (hS : S.PosSemidef)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ v, qform S v ≤ c * sqnorm v)
    (hν : sqnorm ν ≤ c) (hδ : sqnorm δ ≤ 1) :
    2 * (A * S * A * S).trace + 4 * qform (A * S * A) (ν - δ) ≤
      8 * c ^ 2 + 12 * c := by
  have ht := (trace_quadratic_le A S hA hS c hc h).trans
    (mul_le_of_le_one_right (sq_nonneg c) hn)
  have hx : sqnorm (A *ᵥ (ν - δ)) ≤ (3 / 2 : ℝ) * c + 3 := by
    calc
      _ ≤ frobSq A * sqnorm (ν - δ) := sqnorm_mulVec_le A _
      _ ≤ sqnorm (ν - δ) := mul_le_of_le_one_left
        (Rounding.DetRoundAux.sqnorm_nonneg _) hn
      _ ≤ (3 / 2 : ℝ) * sqnorm ν + 3 * sqnorm δ := sqnorm_sub_le ν δ
      _ ≤ _ := by linarith only [hν, hδ]
  have he : qform (A * S * A) (ν - δ) = qform S (A *ᵥ (ν - δ)) := by
    conv_lhs => rw [← hA]
    simp only [qform, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
      hA]
  have hq : qform (A * S * A) (ν - δ) ≤ c * ((3 / 2 : ℝ) * c + 3) := by
    rw [he]
    exact (h _).trans (mul_le_mul_of_nonneg_left hx hc)
  nlinarith only [ht, hq]

end

end ABBKS26.Robust.FilterAux
