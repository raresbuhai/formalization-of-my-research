module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Rounding a pseudo-moment matrix by a column

Let `M ⪰ 0` (the pseudo-moment matrix `Ẽ[vvᵀ]`), `cw ≻ 0`, `uᵀ cw⁻¹ u = 1` and
`G = cw - uuᵀ`. If `tr(G M)` is small, `uᵀMu ≥ 1/2` and the diagonal entry `M_jj` is not too
small, then the column `â = M e_j` is close to the line of `u`: `âᵀ G â ≤ 3 σ² ⟨u, â⟩²` and
`⟨u, â⟩ ≠ 0` (`BS23.ColinearSoS.column_perp_le`).

The linear-algebra facts used, for real matrices:
* `BS23.ColinearSoS.Rounding.sq_dotProduct_mulVec_le`: Cauchy–Schwarz
  `(xᵀAy)² ≤ (xᵀAx)(yᵀAy)` for `A ⪰ 0`;
* `BS23.ColinearSoS.Rounding.quad_mulVec_le`: `(Az)ᵀ B (Az) ≤ (zᵀAz) tr(AB)` for `A, B ⪰ 0`
  (write `B = ∑ᵢ vᵢvᵢᵀ` and apply Cauchy–Schwarz to each `vᵢᵀ A z`);
* `BS23.ColinearSoS.Rounding.trace_mul_nonneg`: `tr(AB) ≥ 0` for `A, B ⪰ 0`.

Proof of the main statement, with `f = e_j`, `w = cw⁻¹u`, `c = ⟨w, f⟩` and `f' = f - c u`:
`G ⪰ 0` (Cauchy–Schwarz for `cw` applied to `w`); `âᵀGâ ≤ tr(GM) fᵀMf`; `f' = G z` for
`z = cw⁻¹ f'` with `zᵀGz = fᵀcw⁻¹f - c² ≤ 3`, so `f'ᵀMf' ≤ 3 tr(GM)`. With `X = uᵀMu`,
`Q = uᵀMf'`, `Y = f'ᵀMf'` one has `⟨u, â⟩ = cX + Q`, `fᵀMf = c²X + 2cQ + Y`, hence
`⟨u, â⟩² = X (fᵀMf - Y) + Q² ≥ X (fᵀMf - Y) ≥ fᵀMf / 4`.
-/

@[expose] public section

namespace BS23.ColinearSoS

open Matrix

namespace Rounding

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- A real positive semidefinite matrix is symmetric. -/
theorem transpose_eq_of_posSemidef {A : Matrix n n ℝ} (hA : A.PosSemidef) : Aᵀ = A := by
  simpa [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.1

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {S : Matrix n n ℝ} (hS : Sᵀ = S) (x y : n → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ (S *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

/-- The quadratic form of a real positive semidefinite matrix is nonnegative. -/
theorem quad_nonneg {A : Matrix n n ℝ} (hA : A.PosSemidef) (x : n → ℝ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

/-- **Cauchy–Schwarz** for the bilinear form of a real positive semidefinite matrix. -/
theorem sq_dotProduct_mulVec_le {A : Matrix n n ℝ} (hA : A.PosSemidef) (x y : n → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have hs := dotProduct_mulVec_comm (transpose_eq_of_posSemidef hA) y x
  have key : ∀ t : ℝ,
      0 ≤ (y ⬝ᵥ (A *ᵥ y)) * (t * t) + 2 * (x ⬝ᵥ (A *ᵥ y)) * t + x ⬝ᵥ (A *ᵥ x) := by
    intro t
    have h := quad_nonneg hA (x + t • y)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hs] at h
    linarith
  have h := discrim_le_zero key
  rw [discrim] at h
  nlinarith

/-- `(abᵀ) y = ⟨b, y⟩ a`. -/
theorem vecMulVec_mulVec_eq_smul (a b y : n → ℝ) : vecMulVec a b *ᵥ y = (b ⬝ᵥ y) • a := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

omit [Fintype n] in
/-- A real positive semidefinite matrix is a finite sum of rank-one matrices `vᵢvᵢᵀ`. -/
theorem exists_eq_sum_vecMulVec [Finite n] {B : Matrix n n ℝ} (hB : B.PosSemidef) :
    ∃ (m : ℕ) (v : Fin m → n → ℝ), B = ∑ i, vecMulVec (v i) (v i) := by
  obtain ⟨m, v, h⟩ := posSemidef_iff_eq_sum_vecMulVec.mp hB
  exact ⟨m, v, by simpa using h⟩

/-- `tr(A ∑ᵢ vᵢvᵢᵀ) = ∑ᵢ vᵢᵀ A vᵢ`. -/
theorem trace_mul_sum_vecMulVec {m : ℕ} (A : Matrix n n ℝ) (v : Fin m → n → ℝ) :
    (A * ∑ i, vecMulVec (v i) (v i)).trace = ∑ i, v i ⬝ᵥ (A *ᵥ v i) := by
  rw [Finset.mul_sum, trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]

/-- The trace of a product of two real positive semidefinite matrices is nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  obtain ⟨m, v, rfl⟩ := exists_eq_sum_vecMulVec hB
  rw [trace_mul_sum_vecMulVec]
  exact Finset.sum_nonneg fun i _ => quad_nonneg hA (v i)

/-- For real positive semidefinite `A, B`: `(Az)ᵀ B (Az) ≤ (zᵀAz) tr(AB)`. -/
theorem quad_mulVec_le {A B : Matrix n n ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (z : n → ℝ) : (A *ᵥ z) ⬝ᵥ (B *ᵥ (A *ᵥ z)) ≤ (z ⬝ᵥ (A *ᵥ z)) * (A * B).trace := by
  obtain ⟨m, v, rfl⟩ := exists_eq_sum_vecMulVec hB
  rw [trace_mul_sum_vecMulVec, sum_mulVec, dotProduct_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [vecMulVec_mulVec_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm (A *ᵥ z) (v i)]
  have h := sq_dotProduct_mulVec_le hA (v i) z
  nlinarith

/-- The scalar part of `column_perp_le`. -/
theorem column_arith {D X F P Q Y c T δ' σ2 R : ℝ} (hD : 0 < D)
    (hP : P = c * X + Q) (hF : F = c ^ 2 * X + 2 * c * Q + Y)
    (hY : Y ≤ 3 * T) (hT0 : 0 ≤ T) (hTδ : T ≤ δ') (hX : 1 / 2 ≤ X)
    (hFD : 1 / (4 * D) ≤ F) (hδD : δ' ≤ 1 / (10 ^ 4 * D)) (hδσ : δ' ≤ 3 * σ2 / 8)
    (hR : R ≤ F * T) :
    R ≤ 3 * σ2 * P ^ 2 ∧ P ≠ 0 := by
  have hid : P ^ 2 = X * (F - Y) + Q ^ 2 := by rw [hP, hF]; ring
  have he : 0 < 1 / D := by positivity
  have h4 : 1 / (4 * D) = 1 / D / 4 := by ring
  have h10 : 1 / (10 ^ 4 * D) = 1 / D / 10 ^ 4 := by ring
  rw [h4] at hFD
  rw [h10] at hδD
  have hYF : Y ≤ F / 2 := by linarith
  have hF0 : 0 < F := by linarith
  have hP2 : F / 4 ≤ P ^ 2 := by
    rw [hid]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by linarith : 0 ≤ F / 2 - Y),
      mul_nonneg (by linarith : (0 : ℝ) ≤ X - 1 / 2) hF0.le, sq_nonneg Q]
  have hPne : P ≠ 0 := by
    rintro rfl
    linarith
  refine ⟨?_, hPne⟩
  have hδ0 : 0 ≤ δ' := hT0.trans hTδ
  calc R ≤ F * T := hR
    _ ≤ F * δ' := mul_le_mul_of_nonneg_left hTδ hF0.le
    _ ≤ (4 * P ^ 2) * δ' := mul_le_mul_of_nonneg_right (by linarith) hδ0
    _ ≤ (4 * P ^ 2) * (3 * σ2 / 8) := mul_le_mul_of_nonneg_left hδσ (by positivity)
    _ ≤ 3 * σ2 * P ^ 2 := by nlinarith [sq_nonneg P]

end Rounding

open Rounding

/-- **Rounding `Ẽ[vvᵀ]` by a column.** Let `M ⪰ 0`, `cw ≻ 0`, `uᵀcw⁻¹u = 1` and
`G = cw - uuᵀ`. If `tr(GM) ≤ δ'`, `uᵀMu ≥ 1/2`, `M_jj ≥ 1/(4d)`, `e_jᵀ cw⁻¹ e_j ≤ 3`,
`δ' ≤ 1/(10⁴ d)` and `δ' ≤ 3σ²/8`, then the column `â = M e_j` satisfies
`âᵀ G â ≤ 3 σ² ⟨u, â⟩²` and `⟨u, â⟩ ≠ 0`. -/
theorem column_perp_le {d : ℕ} {Mm cw : Matrix (Fin d) (Fin d) ℝ} {u : Fin d → ℝ}
    (hM : Mm.PosSemidef) (hcw : cw.PosDef) (hu : u ⬝ᵥ (cw⁻¹ *ᵥ u) = 1)
    {δ' σ2 : ℝ} (htr : ((cw - vecMulVec u u) * Mm).trace ≤ δ')
    (hux : 1 / 2 ≤ u ⬝ᵥ (Mm *ᵥ u))
    (j : Fin d) (hjj : 1 / (4 * d) ≤ Mm j j)
    (hcwj : (Pi.single j 1 : Fin d → ℝ) ⬝ᵥ (cw⁻¹ *ᵥ Pi.single j 1) ≤ 3)
    (hδd : δ' ≤ 1 / (10 ^ 4 * d)) (hδσ : δ' ≤ 3 * σ2 / 8) :
    (Mm *ᵥ Pi.single j 1) ⬝ᵥ ((cw - vecMulVec u u) *ᵥ (Mm *ᵥ Pi.single j 1)) ≤
        3 * σ2 * (u ⬝ᵥ (Mm *ᵥ Pi.single j 1)) ^ 2 ∧
      u ⬝ᵥ (Mm *ᵥ Pi.single j 1) ≠ 0 := by
  set f : Fin d → ℝ := Pi.single j 1 with hf_def
  set G := cw - vecMulVec u u with hG_def
  have hcwT : cwᵀ = cw := transpose_eq_of_posSemidef hcw.posSemidef
  have hiT : cw⁻¹ᵀ = cw⁻¹ := transpose_eq_of_posSemidef hcw.inv.posSemidef
  have hMT : Mmᵀ = Mm := transpose_eq_of_posSemidef hM
  have hcwinv : cw * cw⁻¹ = 1 :=
    mul_nonsing_inv (A := cw) ((isUnit_iff_isUnit_det _).mp hcw.isUnit)
  obtain ⟨w, hw⟩ : ∃ w, w = cw⁻¹ *ᵥ u := ⟨_, rfl⟩
  rw [← hw] at hu
  have hcww : cw *ᵥ w = u := by rw [hw, mulVec_mulVec, hcwinv, one_mulVec]
  have hGv : ∀ x, G *ᵥ x = cw *ᵥ x - (u ⬝ᵥ x) • u := fun x => by
    rw [hG_def, sub_mulVec, vecMulVec_mulVec_eq_smul]
  have hGdot : ∀ x y, x ⬝ᵥ (G *ᵥ y) = x ⬝ᵥ (cw *ᵥ y) - (x ⬝ᵥ u) * (u ⬝ᵥ y) := fun x y => by
    rw [hGv, dotProduct_sub, dotProduct_smul, smul_eq_mul, mul_comm]
  -- `G ⪰ 0`
  have hGT : Gᵀ = G := by rw [hG_def, transpose_sub, hcwT, transpose_vecMulVec]
  have hG : G.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hGT]
    · rw [star_trivial, hGdot]
      have h := sq_dotProduct_mulVec_le hcw.posSemidef w x
      rw [hcww, dotProduct_mulVec_comm hcwT w x, hcww, dotProduct_comm w u, hu] at h
      rw [dotProduct_comm u x]
      nlinarith
  have hT0 : 0 ≤ (G * Mm).trace := trace_mul_nonneg hG hM
  -- `âᵀGâ ≤ tr(GM) fᵀMf`
  have h3 : (Mm *ᵥ f) ⬝ᵥ (G *ᵥ (Mm *ᵥ f)) ≤ (f ⬝ᵥ (Mm *ᵥ f)) * (G * Mm).trace := by
    have h := quad_mulVec_le hM hG f
    rwa [trace_mul_comm] at h
  -- the decomposition `f = c u + f'`
  obtain ⟨c, hc⟩ : ∃ c, c = w ⬝ᵥ f := ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ : ∃ f' : Fin d → ℝ, f' = f - c • u := ⟨_, rfl⟩
  have hf : f = c • u + f' := by rw [hf']; abel
  have hcf : u ⬝ᵥ (cw⁻¹ *ᵥ f) = c := by
    rw [dotProduct_mulVec_comm hiT u f, ← hw, dotProduct_comm, hc]
  obtain ⟨z, hz⟩ : ∃ z, z = cw⁻¹ *ᵥ f' := ⟨_, rfl⟩
  have hz' : z = cw⁻¹ *ᵥ f - c • w := by rw [hz, hf', mulVec_sub, mulVec_smul, hw]
  have huz : u ⬝ᵥ z = 0 := by
    rw [hz', dotProduct_sub, dotProduct_smul, hcf, hu, smul_eq_mul, mul_one, sub_self]
  have hcwz : cw *ᵥ z = f' := by rw [hz, mulVec_mulVec, hcwinv, one_mulVec]
  have hGz : G *ᵥ z = f' := by rw [hGv, hcwz, huz, zero_smul, sub_zero]
  have hzf' : z ⬝ᵥ f' = f ⬝ᵥ (cw⁻¹ *ᵥ f) - c ^ 2 := by
    rw [hf', dotProduct_sub, dotProduct_smul, dotProduct_comm z u, huz, hz', sub_dotProduct,
      smul_dotProduct, ← hc, dotProduct_comm (cw⁻¹ *ᵥ f) f, smul_eq_mul, smul_eq_mul]
    ring
  have hzf'3 : z ⬝ᵥ f' ≤ 3 := by rw [hzf']; nlinarith [sq_nonneg c]
  have hY : f' ⬝ᵥ (Mm *ᵥ f') ≤ 3 * (G * Mm).trace := by
    have h := quad_mulVec_le hG hM z
    rw [hGz] at h
    exact h.trans (mul_le_mul_of_nonneg_right hzf'3 hT0)
  -- the scalar identities
  have hP : u ⬝ᵥ (Mm *ᵥ f) = c * (u ⬝ᵥ (Mm *ᵥ u)) + u ⬝ᵥ (Mm *ᵥ f') := by
    rw [hf, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hF : f ⬝ᵥ (Mm *ᵥ f) = c ^ 2 * (u ⬝ᵥ (Mm *ᵥ u)) + 2 * c * (u ⬝ᵥ (Mm *ᵥ f')) +
      f' ⬝ᵥ (Mm *ᵥ f') := by
    rw [hf]
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul]
    rw [dotProduct_mulVec_comm hMT f' u]
    ring
  have hFjj : f ⬝ᵥ (Mm *ᵥ f) = Mm j j := by
    rw [hf_def, single_one_dotProduct, mulVec_single_one, col_apply]
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr j.pos
  exact column_arith hd hP hF hY hT0 htr hux
    (hFjj ▸ hjj) hδd hδσ h3

end BS23.ColinearSoS
