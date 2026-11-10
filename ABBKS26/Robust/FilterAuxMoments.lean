module

public import ABBKS26.IdCov.MomPoly

/-! One dimensional projections of the polynomial resilience hypothesis. -/

@[expose] public section

namespace ABBKS26.Robust.FilterAux

open Common Matrix MvPolynomial
open scoped BigOperators

noncomputable section

private theorem lin_smul {d : ℕ} (c : ℝ) (v : Vec d) :
    lin (c • v) = C c * lin v := by
  simp [lin, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]

private theorem lin_single {d : ℕ} (i : Fin d) (c : ℝ) :
    lin (Pi.single i c) = C c * X i := by
  classical
  simp [lin, Pi.single_apply, apply_ite]

private theorem quad_smul {d : ℕ} (c : ℝ) (A : Mat d) :
    quad (c • A) = C c * quad A := by
  simp [quad, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]

private theorem quad_vecMulVec {d : ℕ} (v : Vec d) :
    quad (vecMulVec v v) = lin v ^ 2 := by
  simp only [quad, lin, pow_two, Finset.sum_mul_sum, vecMulVec_apply, C_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem lin_projection {d : ℕ} (i : Fin d) (u x : Vec d) :
    lin (vecMulVec (Pi.single i 1) u *ᵥ x) = C (u ⬝ᵥ x) * X i := by
  rw [vecMulVec_mulVec, op_smul_eq_smul, lin_smul, lin_single]
  simp

theorem quad_projection {d : ℕ} (i : Fin d) (u : Vec d) (S : Mat d) :
    quad (vecMulVec (Pi.single i 1) u * S *
      (vecMulVec (Pi.single i 1) u)ᵀ) = C (qform S u) * X i ^ 2 := by
  let e : Vec d := Pi.single i 1
  have he : vecMulVec e u * S * (vecMulVec e u)ᵀ =
      qform S u • vecMulVec e e := by
    rw [transpose_vecMulVec, vecMulVec_mul, vecMulVec_mul_vecMulVec]
    rw [← dotProduct_mulVec]
    ext a b
    simp only [qform, vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he, quad_smul, quad_vecMulVec, lin_single]
  simp

theorem hmom_monomial {d : ℕ} (i : Fin d) (r : ℕ) (a v : ℝ) :
    IdCov.hmom r (C a * X i) (C v * X i ^ 2) =
      C (IdCov.hmom r a v) * (X i : RPoly d) ^ r := by
  simp only [IdCov.hmom, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : 2 * j ≤ r := by
    simp only [Finset.mem_range] at hj
    omega
  have he : (X i : RPoly d) ^ (r - 2 * j) * (X i ^ 2) ^ j = X i ^ r := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hj']
  simp only [mul_pow, map_pow, map_mul, C_eq_natCast]
  calc
    _ = (C (IdCov.hermCoeff r j : ℝ) * C a ^ (r - 2 * j) * C v ^ j) *
        ((X i : RPoly d) ^ (r - 2 * j) * (X i ^ 2) ^ j) := by
          rw [C_eq_natCast]
          ring
    _ = _ := by rw [he, C_eq_natCast]

theorem hmom_two (a v : ℝ) : IdCov.hmom 2 a v = a ^ 2 + v := by
  norm_num [IdCov.hmom, IdCov.hermCoeff, Finset.sum_range_succ, Nat.choose]

theorem hmom_four (a v : ℝ) : IdCov.hmom 4 a v = a ^ 4 + 6 * a ^ 2 * v + 3 * v ^ 2 := by
  norm_num [IdCov.hmom, IdCov.hermCoeff, Finset.sum_range_succ, Nat.choose]

private theorem normalization (μ S : ℝ) (hS : 0 < S) :
    ∃ c : ℝ, 0 < c ∧ c ^ 2 * (μ ^ 2 + S) = 1 ∧
      |c * μ| ≤ 1 ∧ c ^ 2 * S ≤ 1 := by
  have hm : 0 < μ ^ 2 + S := by positivity
  let c := (Real.sqrt (μ ^ 2 + S))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  have he : c ^ 2 * (μ ^ 2 + S) = 1 := by
    dsimp only [c]
    rw [inv_pow, Real.sq_sqrt hm.le, inv_mul_cancel₀ hm.ne']
  refine ⟨c, hc, he, ?_, ?_⟩
  · apply (abs_le_one_iff_mul_self_le_one).2
    nlinarith only [he, mul_nonneg (sq_nonneg c) hS.le]
  · nlinarith only [he, mul_nonneg (sq_nonneg c) (sq_nonneg μ)]

theorem scalar_moment_bounds (E₂ E₄ μ S δ : ℝ) (hS : 0 < S) (hδ : 0 ≤ δ)
    (h₂ : ∀ c : ℝ, |c ^ 2 * (E₂ - (μ ^ 2 + S))| ≤
      δ * (1 + |c * μ| + c ^ 2 * S) ^ 2)
    (h₄ : ∀ c : ℝ, c ^ 4 * E₄ ≤ c ^ 4 * (μ ^ 4 + 6 * μ ^ 2 * S + 3 * S ^ 2) +
      δ * (1 + |c * μ| + c ^ 2 * S) ^ 4) :
    (1 - 9 * δ) * (μ ^ 2 + S) ≤ E₂ ∧
      E₄ ≤ (3 + 81 * δ) * (μ ^ 2 + S) ^ 2 := by
  obtain ⟨c, hc, he, hμ, hs⟩ := normalization μ S hS
  have hbase : 0 ≤ 1 + |c * μ| + c ^ 2 * S := by positivity
  have hbase' : 1 + |c * μ| + c ^ 2 * S ≤ 3 := by linarith only [hμ, hs]
  have h₂' : |c ^ 2 * (E₂ - (μ ^ 2 + S))| ≤ 9 * δ := by
    calc
      _ ≤ δ * (1 + |c * μ| + c ^ 2 * S) ^ 2 := h₂ c
      _ ≤ δ * 3 ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hbase' 2) hδ
      _ = _ := by ring
  have h₄' : c ^ 4 * E₄ ≤ 3 + 81 * δ := by
    have hg : μ ^ 4 + 6 * μ ^ 2 * S + 3 * S ^ 2 ≤ 3 * (μ ^ 2 + S) ^ 2 := by
      nlinarith only [sq_nonneg (μ ^ 2)]
    have hs' : c ^ 4 * (μ ^ 4 + 6 * μ ^ 2 * S + 3 * S ^ 2) ≤ 3 := by
      have hh := mul_le_mul_of_nonneg_left hg (pow_nonneg hc.le 4)
      nlinarith only [hh, sq_nonneg (c ^ 2 * (μ ^ 2 + S) - 1), congrArg (fun x ↦ x ^ 2) he]
    have hd : δ * (1 + |c * μ| + c ^ 2 * S) ^ 4 ≤ 81 * δ := by
      calc
        _ ≤ δ * 3 ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase hbase' 4) hδ
        _ = _ := by ring
    linarith only [h₄ c, hs', hd]
  constructor
  · have hh : -(9 * δ) * (μ ^ 2 + S) ≤ E₂ - (μ ^ 2 + S) := by
      calc
        _ ≤ (c ^ 2 * (E₂ - (μ ^ 2 + S))) * (μ ^ 2 + S) :=
          mul_le_mul_of_nonneg_right (abs_le.mp h₂').1 (by positivity)
        _ = E₂ - (μ ^ 2 + S) := by
          calc
            _ = (c ^ 2 * (μ ^ 2 + S)) * (E₂ - (μ ^ 2 + S)) := by ring
            _ = _ := by rw [he, one_mul]
    linarith only [hh]
  · have he' : c ^ 4 * (μ ^ 2 + S) ^ 2 = 1 := by
      nlinarith only [congrArg (fun x ↦ x ^ 2) he]
    calc
      E₄ = (c ^ 4 * E₄) * (μ ^ 2 + S) ^ 2 := by
        linear_combination -E₄ * he'
      _ ≤ _ := mul_le_mul_of_nonneg_right h₄' (sq_nonneg _)

end

end ABBKS26.Robust.FilterAux
