module

public import BS23.Colinear.Direction
public import BS23.Colinear.Population
public import BS23.ColinearSoS.Rounding

/-!
# The whitened frame of a mixture with colinear means

The linear algebra behind the analysis of the sum-of-squares algorithm for [BS23, Theorem 1.2], in
the coordinates given by an invertible matrix `W` (in the algorithm, the whitening matrix of the
sample). The means are colinear, `μ_c = base + t_c u₀` with `u₀ ≠ 0`, so the covariance of the
mixture is `cov = Σ + τ² u₀u₀ᵀ` (`BS23.Colinear.cov_eq`). Write `κ_u = u₀ᵀ cov⁻¹ u₀`
(`BS23.ColinearSoS.kapU`) and `σ² = κ_u / u₀ᵀΣ⁻¹u₀ = 1 - τ² κ_u ∈ (0, 1]` (`BS23.Mixture.sigmaSq`).

* **The frame.** `cov_W = W cov Wᵀ` and `Σ_W = W Σ Wᵀ` (`BS23.ColinearSoS.covW`,
  `BS23.ColinearSoS.SW`). A vector `â` in these coordinates is the direction `a = Wᵀ â` in the
  original ones, with `aᵀ cov a = âᵀ cov_W â` and `aᵀ Σ a = âᵀ Σ_W â`
  (`BS23.ColinearSoS.quad_cov_transpose_mulVec`, `BS23.ColinearSoS.quad_S_transpose_mulVec`).
* **The line of the means.** The direction `ŭ = W u₀ / √κ_u` (`BS23.ColinearSoS.uhat`) has
  `ŭᵀ cov_W⁻¹ ŭ = 1` (`BS23.ColinearSoS.uhat_dot_covW_inv`). The centered means are
  `W (μ_c - μ̄) = a_c ŭ` with `a_c = (t_c - t̄) √κ_u` (`BS23.ColinearSoS.acoef`,
  `BS23.ColinearSoS.W_mulVec_center`), and `∑_c w_c a_c = 0`, `∑_c w_c a_c² + σ² = 1`
  (`BS23.ColinearSoS.sum_w_acoef`, `BS23.ColinearSoS.sum_w_acoef_sq`): along `ŭ` the mixture is
  the one-dimensional mixture `∑_c w_c N(a_c, σ²)`, of variance `1`.
* **The part orthogonal to the line.** `G = cov_W - ŭŭᵀ` (`BS23.ColinearSoS.Gm`) is positive
  semidefinite (`BS23.ColinearSoS.Gm_posSemidef`; Cauchy–Schwarz for `cov_W`), and
  `vᵀ cov_W v = vᵀGv + ⟨ŭ, v⟩²`, `vᵀ Σ_W v = vᵀGv + σ² ⟨ŭ, v⟩²`
  (`BS23.ColinearSoS.quad_covW_eq`, `BS23.ColinearSoS.quad_SW_eq`). Hence `σ² cov ⪯ Σ ⪯ cov`
  (`BS23.ColinearSoS.sigmaSq_mul_quad_cov_le`, `BS23.ColinearSoS.quad_S_le_quad_cov`). The point
  `v* = cov_W⁻¹ ŭ` has `⟨ŭ, v*⟩ = v*ᵀ cov_W v* = 1` and `v*ᵀ G v* = 0`.
* **Bessel.** If `⟨f, cov_W⁻¹ ŭ⟩ = 0` then `⟨f, v⟩² ≤ (fᵀ cov_W⁻¹ f) · vᵀGv`
  (`BS23.ColinearSoS.sq_dot_le_mul_quad_Gm`): `f = G cov_W⁻¹ f`, then Cauchy–Schwarz for `G`.
* **The Fisher ratio.** For `a = Wᵀ â` and `α = ⟨ŭ, â⟩`, `⟨a, u₀⟩ = √κ_u α` and
  `u₀ᵀΣ⁻¹u₀ = κ_u / σ²`, so `⟨a, u₀⟩² / (aᵀΣa · u₀ᵀΣ⁻¹u₀) = σ² α² / (âᵀGâ + σ² α²)`. It is at
  least `1/4` when `âᵀGâ ≤ 3 σ² α²` (`BS23.ColinearSoS.fisher_of_perp_le`), and `aᵀΣa > 0` when
  `α ≠ 0` (`BS23.ColinearSoS.quad_S_pos_of_uhat_dot_ne_zero`); these are the inputs of the line
  clustering (`BS23.ColinearSoS.fisher_ratio_of_perp_le`, in the form of
  `BS23.Colinear.fisher_ratio`).
* **Separation.** `(μ_c - μ_c')ᵀ Σ⁻¹ (μ_c - μ_c') = (a_c - a_c')² / σ²`
  (`BS23.ColinearSoS.sqNormIn_sub_eq_acoef`).
* **Comparison with a diagonal.** If `vᵀ diag(e) v ≤ (1 + ε) vᵀ cov_W v` for all `v`, with all
  `e_i ≥ 1/2` and `ε ≤ 1/2`, then `fᵀ cov_W⁻¹ f ≤ 3 ‖f‖²`
  (`BS23.ColinearSoS.covW_inv_le`, `BS23.ColinearSoS.covW_inv_single_le`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open Matrix Finset Colinear

variable {k d : ℕ}

/-! ### Definitions -/

/-- `κ_u = u₀ᵀ cov⁻¹ u₀`, the squared length of `u₀` in the geometry of `cov⁻¹`. -/
noncomputable def kapU (M : Mixture k d) (u0 : Fin d → ℝ) : ℝ :=
  u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0)

/-- The covariance of the mixture in the coordinates `W`: `W cov Wᵀ`. -/
noncomputable def covW (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  W * M.cov * Wᵀ

/-- The covariance of the components in the coordinates `W`: `W Σ Wᵀ`. -/
noncomputable def SW (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  W * M.S * Wᵀ

/-- The direction of the means in the coordinates `W`, normalized: `ŭ = W u₀ / √κ_u`. -/
noncomputable def uhat (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ) (u0 : Fin d → ℝ) :
    Fin d → ℝ :=
  (Real.sqrt (kapU M u0))⁻¹ • (W *ᵥ u0)

/-- The positions of the centered means on the line: `a_c = (t_c - t̄) √κ_u`. -/
noncomputable def acoef (M : Mixture k d) (u0 : Fin d → ℝ) (t : Fin k → ℝ) (c : Fin k) : ℝ :=
  (t c - tbar M t) * Real.sqrt (kapU M u0)

/-- The part of the covariance orthogonal to the line of the means: `G = W cov Wᵀ - ŭŭᵀ`. -/
noncomputable def Gm (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ) (u0 : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  covW M W - vecMulVec (uhat M W u0) (uhat M W u0)

/-! ### Generalities -/

namespace Fr

/-- `xᵀ (uuᵀ) x = ⟨u, x⟩²`. -/
theorem quad_vecMulVec (u x : Fin d → ℝ) : quad (vecMulVec u u) x = (u ⬝ᵥ x) ^ 2 := by
  rw [quad, Rounding.vecMulVec_mulVec_eq_smul, dotProduct_smul, smul_eq_mul, dotProduct_comm x u,
    sq]

/-- `(Wᵀ x)ᵀ y = xᵀ (W y)`. -/
theorem transpose_mulVec_dotProduct (W : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    (Wᵀ *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (W *ᵥ y) := by
  rw [mulVec_transpose, dotProduct_mulVec]

/-- `xᵀ (Wᵀ y) = (W x)ᵀ y`. -/
theorem dotProduct_transpose_mulVec (W : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    x ⬝ᵥ (Wᵀ *ᵥ y) = (W *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose]

/-- The bilinear form of `W A Wᵀ`: `xᵀ (W A Wᵀ) y = (Wᵀx)ᵀ A (Wᵀy)`. -/
theorem dotProduct_conj_mulVec (A W : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℝ) :
    x ⬝ᵥ ((W * A * Wᵀ) *ᵥ y) = (Wᵀ *ᵥ x) ⬝ᵥ (A *ᵥ (Wᵀ *ᵥ y)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, transpose_mulVec_dotProduct]

/-- The quadratic form of `W A Wᵀ`: `xᵀ (W A Wᵀ) x = (Wᵀx)ᵀ A (Wᵀx)`. -/
theorem quad_conj (A W : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    quad (W * A * Wᵀ) x = quad A (Wᵀ *ᵥ x) :=
  dotProduct_conj_mulVec A W x x

/-- **Comparison with a diagonal.** If `vᵀ diag(e) v ≤ (1 + ε) vᵀ C v` for all `v`, with all
`e_i ≥ 1/2` and `ε ≤ 1/2`, then `fᵀ C⁻¹ f ≤ 3 ‖f‖²`. -/
theorem inv_quad_le_of_diagonal {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) {e : Fin d → ℝ}
    (he : ∀ i, 1 / 2 ≤ e i) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hup : ∀ v, quad (diagonal e) v ≤ (1 + ε) * quad C v) (f : Fin d → ℝ) :
    f ⬝ᵥ (C⁻¹ *ᵥ f) ≤ 3 * (f ⬝ᵥ f) := by
  have h1 : ∀ v, quad 1 v ≤ 3 * quad C v := by
    intro v
    have hd : 1 / 2 * quad 1 v ≤ quad (diagonal e) v := by
      simp only [quad, one_mulVec, dotProduct, mulVec_diagonal, mul_sum]
      refine sum_le_sum fun i _ => ?_
      nlinarith [mul_nonneg (sub_nonneg.mpr (he i)) (mul_self_nonneg (v i))]
    have hC0 := quad_nonneg hC.posSemidef v
    have hεC := mul_le_mul_of_nonneg_right hε hC0
    nlinarith [hup v]
  have h := inv_quad_le_of_quad_le PosDef.one hC (by norm_num) h1 f
  simpa [inv_one] using h

variable {M : Mixture k d} {base u0 : Fin d → ℝ} {t : Fin k → ℝ}

/-- `σ² = 1 - τ² κ_u`. -/
theorem sigmaSq_eq (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.sigmaSq u0 = 1 - tau2 M t * kapU M u0 :=
  sigmaSq_eq_one_sub hM hM.nonneg_w hu0 hμ

/-- `σ² > 0`. -/
theorem sigmaSq_pos (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0) :
    0 < M.sigmaSq u0 :=
  (colinear_sigmaSq hM.posDef (cov_posDef M hM hM.nonneg_w) hu0 (tau2_nonneg hM.nonneg_w)
    (cov_eq hM hμ)).2.1

/-- `σ² ≤ 1`. -/
theorem sigmaSq_le_one (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.sigmaSq u0 ≤ 1 :=
  (colinear_sigmaSq hM.posDef (cov_posDef M hM hM.nonneg_w) hu0 (tau2_nonneg hM.nonneg_w)
    (cov_eq hM hμ)).2.2

/-- The scalar part of `BS23.ColinearSoS.fisher_of_perp_le`. -/
theorem fisher_arith {g σ2 α κ : ℝ} (hσ : 0 < σ2) (hκ : 0 ≤ κ) (h : g ≤ 3 * σ2 * α ^ 2) :
    1 / 4 * (g + σ2 * α ^ 2) * (κ / σ2) ≤ κ * α ^ 2 := by
  have e : 1 / 4 * (g + σ2 * α ^ 2) * (κ / σ2) =
      κ * α ^ 2 - κ * (3 * σ2 * α ^ 2 - g) / (4 * σ2) := by
    field_simp
    ring
  have h0 : 0 ≤ κ * (3 * σ2 * α ^ 2 - g) / (4 * σ2) :=
    div_nonneg (mul_nonneg hκ (by linarith)) (by positivity)
  linarith

end Fr

open Fr

variable {M : Mixture k d} {W : Matrix (Fin d) (Fin d) ℝ} {base u0 : Fin d → ℝ} {t : Fin k → ℝ}

/-! ### The frame -/

/-- `κ_u > 0` for `u₀ ≠ 0`. -/
theorem kapU_pos (hM : M.Valid) (hu0 : u0 ≠ 0) : 0 < kapU M u0 :=
  inv_quad_pos (cov_posDef M hM hM.nonneg_w) hu0

/-- `κ_u ≥ 0`. -/
theorem kapU_nonneg (hM : M.Valid) (u0 : Fin d → ℝ) : 0 ≤ kapU M u0 :=
  inv_quad_nonneg (cov_posDef M hM hM.nonneg_w) u0

/-- `W u₀ = √κ_u ŭ`. -/
theorem W_mulVec_eq_smul_uhat (hM : M.Valid) (hu0 : u0 ≠ 0) (W : Matrix (Fin d) (Fin d) ℝ) :
    W *ᵥ u0 = Real.sqrt (kapU M u0) • uhat M W u0 := by
  rw [uhat, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (kapU_pos hM hu0)).ne', one_smul]

/-- `cov_W` is symmetric. -/
theorem covW_transpose (hM : M.Valid) (W : Matrix (Fin d) (Fin d) ℝ) :
    (covW M W)ᵀ = covW M W := by
  have h := transpose_eq_of_posDef (cov_posDef M hM hM.nonneg_w)
  rw [covW, transpose_mul, transpose_mul, transpose_transpose, h, Matrix.mul_assoc]

/-- `Σ_W` is symmetric. -/
theorem SW_transpose (hM : M.Valid) (W : Matrix (Fin d) (Fin d) ℝ) : (SW M W)ᵀ = SW M W := by
  have h := transpose_eq_of_posDef hM.posDef
  rw [SW, transpose_mul, transpose_mul, transpose_transpose, h, Matrix.mul_assoc]

/-- `G` is symmetric. -/
theorem Gm_transpose (hM : M.Valid) (W : Matrix (Fin d) (Fin d) ℝ) (u0 : Fin d → ℝ) :
    (Gm M W u0)ᵀ = Gm M W u0 := by
  rw [Gm, transpose_sub, covW_transpose hM, transpose_vecMulVec]

/-- `W cov Wᵀ` is positive definite for `W` invertible. -/
theorem covW_posDef (hM : M.Valid) (hW : IsUnit W) : (covW M W).PosDef := by
  have h := (Matrix.IsUnit.posDef_star_right_conjugate_iff hW).mpr (cov_posDef M hM hM.nonneg_w)
  rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h

/-- `Wᵀ cov_W⁻¹ W y = cov⁻¹ y`. -/
theorem transpose_mulVec_covW_inv (hM : M.Valid) (hW : IsUnit W) (y : Fin d → ℝ) :
    Wᵀ *ᵥ ((covW M W)⁻¹ *ᵥ (W *ᵥ y)) = M.cov⁻¹ *ᵥ y := by
  have hcov := cov_posDef M hM hM.nonneg_w
  have hWinv : W⁻¹ * W = 1 := nonsing_inv_mul W ((isUnit_iff_isUnit_det W).mp hW)
  set z := (covW M W)⁻¹ *ᵥ (W *ᵥ y)
  have h1 : covW M W *ᵥ z = W *ᵥ y := mulVec_inv_mulVec (covW_posDef hM hW) _
  rw [covW, ← mulVec_mulVec, ← mulVec_mulVec] at h1
  have hinv : ∀ x, W⁻¹ *ᵥ (W *ᵥ x) = x := fun x => by rw [mulVec_mulVec, hWinv, one_mulVec]
  have h2 : M.cov *ᵥ (Wᵀ *ᵥ z) = y := by
    rw [← hinv (M.cov *ᵥ (Wᵀ *ᵥ z)), h1, hinv]
  rw [← h2, inv_mulVec_mulVec hcov]

/-- `(W x)ᵀ cov_W⁻¹ (W y) = xᵀ cov⁻¹ y`. -/
theorem W_mulVec_dot_covW_inv (hM : M.Valid) (hW : IsUnit W) (x y : Fin d → ℝ) :
    (W *ᵥ x) ⬝ᵥ ((covW M W)⁻¹ *ᵥ (W *ᵥ y)) = x ⬝ᵥ (M.cov⁻¹ *ᵥ y) := by
  rw [← transpose_mulVec_covW_inv hM hW y, dotProduct_transpose_mulVec]

/-- **`ŭ` is a unit vector of `cov_W⁻¹`**: `ŭᵀ cov_W⁻¹ ŭ = 1`. -/
theorem uhat_dot_covW_inv (hM : M.Valid) (hu0 : u0 ≠ 0) (hW : IsUnit W) :
    uhat M W u0 ⬝ᵥ ((covW M W)⁻¹ *ᵥ uhat M W u0) = 1 := by
  have hκ := kapU_pos hM hu0
  have hs : Real.sqrt (kapU M u0) ≠ 0 := (Real.sqrt_pos.mpr hκ).ne'
  have hss : Real.sqrt (kapU M u0) * Real.sqrt (kapU M u0) = kapU M u0 :=
    Real.mul_self_sqrt hκ.le
  rw [uhat, mulVec_smul, dotProduct_smul, smul_dotProduct, W_mulVec_dot_covW_inv hM hW,
    smul_eq_mul, smul_eq_mul, show u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0) = kapU M u0 from rfl, ← mul_assoc,
    ← mul_inv, hss, inv_mul_cancel₀ hκ.ne']

/-- **The centered means in the frame**: `W (μ_c - μ̄) = a_c ŭ`. -/
theorem W_mulVec_center (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0)
    (W : Matrix (Fin d) (Fin d) ℝ) (c : Fin k) :
    W *ᵥ (M.μ c - M.mean) = acoef M u0 t c • uhat M W u0 := by
  rw [center_eq hM hμ, mulVec_smul, W_mulVec_eq_smul_uhat hM hu0, smul_smul, acoef]

/-- The positions of the means on the line average to `0`: `∑_c w_c a_c = 0`. -/
theorem sum_w_acoef (hM : M.Valid) (u0 : Fin d → ℝ) (t : Fin k → ℝ) :
    ∑ c, M.w c * acoef M u0 t c = 0 := by
  have h : ∑ c, M.w c * (t c - tbar M t) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hM.sum_w, one_mul, tbar, sub_self]
  calc ∑ c, M.w c * acoef M u0 t c
      = (∑ c, M.w c * (t c - tbar M t)) * Real.sqrt (kapU M u0) := by
        rw [sum_mul]
        exact sum_congr rfl fun c _ => by rw [acoef]; ring
    _ = 0 := by rw [h, zero_mul]

/-- **The variance along the line is `1`**: `∑_c w_c a_c² + σ² = 1`. -/
theorem sum_w_acoef_sq (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0) :
    ∑ c, M.w c * acoef M u0 t c ^ 2 + M.sigmaSq u0 = 1 := by
  have h : ∑ c, M.w c * acoef M u0 t c ^ 2 = tau2 M t * kapU M u0 := by
    rw [tau2, sum_mul]
    refine sum_congr rfl fun c _ => ?_
    rw [acoef, mul_pow, Real.sq_sqrt (kapU_nonneg hM u0)]
    ring
  rw [h, sigmaSq_eq hM hu0 hμ]
  ring

/-! ### The orthogonal part `G` -/

/-- `vᵀGv = vᵀ cov_W v - ⟨ŭ, v⟩²`. -/
theorem quad_Gm (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ) (u0 v : Fin d → ℝ) :
    quad (Gm M W u0) v = quad (covW M W) v - (uhat M W u0 ⬝ᵥ v) ^ 2 := by
  rw [Gm, quad_sub_apply, quad_vecMulVec]

/-- `vᵀ cov_W v = vᵀGv + ⟨ŭ, v⟩²`. -/
theorem quad_covW_eq (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ) (u0 v : Fin d → ℝ) :
    quad (covW M W) v = quad (Gm M W u0) v + (uhat M W u0 ⬝ᵥ v) ^ 2 := by
  rw [quad_Gm]
  ring

/-- `u₀ᵀ (Wᵀ v) = √κ_u ⟨ŭ, v⟩`. -/
theorem u0_dot_transpose_mulVec (hM : M.Valid) (hu0 : u0 ≠ 0) (W : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) : u0 ⬝ᵥ (Wᵀ *ᵥ v) = Real.sqrt (kapU M u0) * (uhat M W u0 ⬝ᵥ v) := by
  rw [dotProduct_transpose_mulVec, W_mulVec_eq_smul_uhat hM hu0, smul_dotProduct, smul_eq_mul]

/-- `vᵀ Σ_W v = vᵀGv + σ² ⟨ŭ, v⟩²`. -/
theorem quad_SW_eq (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0)
    (W : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quad (SW M W) v = quad (Gm M W u0) v + M.sigmaSq u0 * (uhat M W u0 ⬝ᵥ v) ^ 2 := by
  have h1 : quad (SW M W) v =
      quad (covW M W) v - tau2 M t * kapU M u0 * (uhat M W u0 ⬝ᵥ v) ^ 2 := by
    rw [SW, covW, quad_conj, quad_conj, cov_eq hM hμ, quad_add_vecMulVec,
      u0_dot_transpose_mulVec hM hu0, mul_pow, Real.sq_sqrt (kapU_nonneg hM u0)]
    ring
  rw [h1, quad_Gm, sigmaSq_eq hM hu0 hμ]
  ring

/-- `G = cov_W - ŭŭᵀ` is positive semidefinite (Cauchy–Schwarz for `cov_W`, `ŭᵀ cov_W⁻¹ ŭ = 1`):
its quadratic form is nonnegative. -/
theorem quad_Gm_nonneg (hM : M.Valid) (hu0 : u0 ≠ 0) (hW : IsUnit W) (v : Fin d → ℝ) :
    0 ≤ quad (Gm M W u0) v := by
  have h := sq_dotProduct_le_quad_mul (covW_posDef hM hW) v (uhat M W u0)
  rw [uhat_dot_covW_inv hM hu0 hW, mul_one, dotProduct_comm] at h
  rw [quad_Gm]
  linarith

/-- `G = cov_W - ŭŭᵀ` is positive semidefinite. -/
theorem Gm_posSemidef (hM : M.Valid) (hu0 : u0 ≠ 0) (hW : IsUnit W) : (Gm M W u0).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, Gm_transpose hM]
  · rw [star_trivial]
    exact quad_Gm_nonneg hM hu0 hW x

/-- The point `v* = cov_W⁻¹ ŭ` has `v*ᵀ cov_W v* = 1`. -/
theorem quad_covW_inv_uhat (hM : M.Valid) (hu0 : u0 ≠ 0) (hW : IsUnit W) :
    quad (covW M W) ((covW M W)⁻¹ *ᵥ uhat M W u0) = 1 := by
  rw [quad_inv_mulVec (covW_posDef hM hW), uhat_dot_covW_inv hM hu0 hW]

/-- The point `v* = cov_W⁻¹ ŭ` has `v*ᵀ G v* = 0`. -/
theorem quad_Gm_covW_inv_uhat (hM : M.Valid) (hu0 : u0 ≠ 0) (hW : IsUnit W) :
    quad (Gm M W u0) ((covW M W)⁻¹ *ᵥ uhat M W u0) = 0 := by
  rw [quad_Gm, quad_covW_inv_uhat hM hu0 hW, uhat_dot_covW_inv hM hu0 hW]
  norm_num

/-- The point `v* = cov_W⁻¹ ŭ` has `v*ᵀ Σ_W v* = σ²`. -/
theorem quad_SW_covW_inv_uhat (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0)
    (hW : IsUnit W) : quad (SW M W) ((covW M W)⁻¹ *ᵥ uhat M W u0) = M.sigmaSq u0 := by
  rw [quad_SW_eq hM hu0 hμ, quad_Gm_covW_inv_uhat hM hu0 hW, uhat_dot_covW_inv hM hu0 hW]
  ring

/-- **Bessel in the geometry of `cov_W`.** If `⟨f, cov_W⁻¹ ŭ⟩ = 0`, then
`⟨f, v⟩² ≤ (fᵀ cov_W⁻¹ f) · vᵀGv`. -/
theorem sq_dot_le_mul_quad_Gm (hM : M.Valid) (hu0 : u0 ≠ 0) (hW : IsUnit W) {f : Fin d → ℝ}
    (hf : f ⬝ᵥ ((covW M W)⁻¹ *ᵥ uhat M W u0) = 0) (v : Fin d → ℝ) :
    (f ⬝ᵥ v) ^ 2 ≤ (f ⬝ᵥ ((covW M W)⁻¹ *ᵥ f)) * quad (Gm M W u0) v := by
  have hC := covW_posDef hM hW
  have hCT := covW_transpose hM W
  have hCiT : (covW M W)⁻¹ᵀ = (covW M W)⁻¹ := transpose_eq_of_posDef hC.inv
  set z := (covW M W)⁻¹ *ᵥ f with hz
  have hCz : covW M W *ᵥ z = f := mulVec_inv_mulVec hC f
  have hzu : z ⬝ᵥ uhat M W u0 = 0 := by
    rw [hz, dotProduct_comm, Colinear.dotProduct_mulVec_comm hCiT, hf]
  have hGv : ∀ x, z ⬝ᵥ (Gm M W u0 *ᵥ x) = z ⬝ᵥ (covW M W *ᵥ x) := by
    intro x
    rw [Gm, sub_mulVec, Rounding.vecMulVec_mulVec_eq_smul, dotProduct_sub, dotProduct_smul, hzu,
      smul_zero, sub_zero]
  have hfv : f ⬝ᵥ v = z ⬝ᵥ (Gm M W u0 *ᵥ v) := by
    rw [hGv, Colinear.dotProduct_mulVec_comm hCT, hCz, dotProduct_comm]
  have hzz : z ⬝ᵥ (Gm M W u0 *ᵥ z) = f ⬝ᵥ z := by
    rw [hGv, hCz, dotProduct_comm]
  rw [hfv, ← hzz]
  exact Rounding.sq_dotProduct_mulVec_le (Gm_posSemidef hM hu0 hW) z v

/-! ### Comparison of `Σ` and `cov` -/

/-- `aᵀ Σ a ≤ aᵀ cov a`. -/
theorem quad_S_le_quad_cov (hM : M.Valid) (hμ : ∀ c, M.μ c = base + t c • u0)
    (a : Fin d → ℝ) : quad M.S a ≤ quad M.cov a := by
  rw [cov_eq hM hμ, quad_add_vecMulVec]
  have := mul_nonneg (tau2_nonneg (t := t) hM.nonneg_w) (sq_nonneg (u0 ⬝ᵥ a))
  linarith

/-- `σ² aᵀ cov a ≤ aᵀ Σ a`. -/
theorem sigmaSq_mul_quad_cov_le (hM : M.Valid) (hu0 : u0 ≠ 0)
    (hμ : ∀ c, M.μ c = base + t c • u0) (a : Fin d → ℝ) :
    M.sigmaSq u0 * quad M.cov a ≤ quad M.S a := by
  have h1 := quad_covW_eq M 1 u0 a
  have h2 := quad_SW_eq hM hu0 hμ 1 a
  have hG := quad_Gm_nonneg hM hu0 isUnit_one (W := 1) a
  have hσ1 := sigmaSq_le_one hM hu0 hμ
  simp only [covW, SW, transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h2
  rw [h1, h2]
  nlinarith [mul_le_mul_of_nonneg_right hσ1 hG]

/-! ### The Fisher ratio of a direction -/

/-- `aᵀ Σ a = âᵀ Σ_W â` for `a = Wᵀ â`. -/
theorem quad_S_transpose_mulVec (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ)
    (â : Fin d → ℝ) : quad M.S (Wᵀ *ᵥ â) = quad (SW M W) â :=
  (quad_conj _ _ _).symm

/-- `aᵀ cov a = âᵀ cov_W â` for `a = Wᵀ â`. -/
theorem quad_cov_transpose_mulVec (M : Mixture k d) (W : Matrix (Fin d) (Fin d) ℝ)
    (â : Fin d → ℝ) : quad M.cov (Wᵀ *ᵥ â) = quad (covW M W) â :=
  (quad_conj _ _ _).symm

/-- `⟨a, u₀⟩ = √κ_u ⟨ŭ, â⟩` for `a = Wᵀ â`. -/
theorem transpose_mulVec_dot_u0 (hM : M.Valid) (hu0 : u0 ≠ 0) (W : Matrix (Fin d) (Fin d) ℝ)
    (â : Fin d → ℝ) : (Wᵀ *ᵥ â) ⬝ᵥ u0 = Real.sqrt (kapU M u0) * (uhat M W u0 ⬝ᵥ â) := by
  rw [dotProduct_comm, u0_dot_transpose_mulVec hM hu0]

/-- `u₀ᵀ Σ⁻¹ u₀ = κ_u / σ²`. -/
theorem inv_quad_S_u0_eq (hM : M.Valid) (hu0 : u0 ≠ 0) :
    u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0) = kapU M u0 / M.sigmaSq u0 := by
  rw [Mixture.sigmaSq, sqNormIn, sqNormIn, show u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0) = kapU M u0 from rfl,
    div_div_cancel₀ (kapU_pos hM hu0).ne']

/-- **The Fisher ratio of a direction close to the line.** For `a = Wᵀ â`, if
`âᵀ G â ≤ 3 σ² ⟨ŭ, â⟩²`, then `⟨a, u₀⟩² ≥ ¼ (aᵀΣa)(u₀ᵀΣ⁻¹u₀)`. -/
theorem fisher_of_perp_le (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0)
    {a â : Fin d → ℝ} (ha : a = Wᵀ *ᵥ â)
    (hperp : quad (Gm M W u0) â ≤ 3 * M.sigmaSq u0 * (uhat M W u0 ⬝ᵥ â) ^ 2) :
    1 / 4 * quad M.S a * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) ≤ (a ⬝ᵥ u0) ^ 2 := by
  subst ha
  rw [quad_S_transpose_mulVec, quad_SW_eq hM hu0 hμ, transpose_mulVec_dot_u0 hM hu0,
    inv_quad_S_u0_eq hM hu0, mul_pow, Real.sq_sqrt (kapU_nonneg hM u0)]
  exact fisher_arith (sigmaSq_pos hM hu0 hμ) (kapU_nonneg hM u0) hperp

/-- For `a = Wᵀ â` with `⟨ŭ, â⟩ ≠ 0`: `aᵀ Σ a > 0`. -/
theorem quad_S_pos_of_uhat_dot_ne_zero (hM : M.Valid) (hu0 : u0 ≠ 0) {a â : Fin d → ℝ}
    (ha : a = Wᵀ *ᵥ â) (hα : uhat M W u0 ⬝ᵥ â ≠ 0) : 0 < quad M.S a := by
  refine quad_pos hM.posDef fun h0 => hα ?_
  have h := transpose_mulVec_dot_u0 hM hu0 W â
  rw [← ha, h0, zero_dotProduct] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (Real.sqrt_pos.mpr (kapU_pos hM hu0)).ne'

/-- **The direction `a = Wᵀ â` for the line clustering**, in the form of
`BS23.Colinear.fisher_ratio`: if `âᵀ G â ≤ 3 σ² ⟨ŭ, â⟩²` and `⟨ŭ, â⟩ ≠ 0`, then
`⟨a, u₀⟩² ≥ ¼ (aᵀΣa)(u₀ᵀΣ⁻¹u₀)`, `σ²/4 · aᵀ cov a ≤ aᵀΣa ≤ aᵀ cov a` and `aᵀΣa > 0`. -/
theorem fisher_ratio_of_perp_le (hM : M.Valid) (hu0 : u0 ≠ 0)
    (hμ : ∀ c, M.μ c = base + t c • u0) {a â : Fin d → ℝ} (ha : a = Wᵀ *ᵥ â)
    (hperp : quad (Gm M W u0) â ≤ 3 * M.sigmaSq u0 * (uhat M W u0 ⬝ᵥ â) ^ 2)
    (hα : uhat M W u0 ⬝ᵥ â ≠ 0) :
    1 / 4 * quad M.S a * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) ≤ (a ⬝ᵥ u0) ^ 2 ∧
      M.sigmaSq u0 / 4 * quad M.cov a ≤ quad M.S a ∧ 0 < quad M.S a ∧
      quad M.S a ≤ quad M.cov a := by
  have hσ := sigmaSq_pos hM hu0 hμ
  have hcov0 := quad_nonneg (cov_posDef M hM hM.nonneg_w).posSemidef a
  have h1 := sigmaSq_mul_quad_cov_le hM hu0 hμ a
  refine ⟨fisher_of_perp_le hM hu0 hμ ha hperp, ?_, quad_S_pos_of_uhat_dot_ne_zero hM hu0 ha hα,
    quad_S_le_quad_cov hM hμ a⟩
  nlinarith [mul_nonneg hσ.le hcov0]

/-! ### Separation -/

/-- **The separation in terms of the positions on the line**:
`(μ_c - μ_c')ᵀ Σ⁻¹ (μ_c - μ_c') = (a_c - a_c')² / σ²`. -/
theorem sqNormIn_sub_eq_acoef (hM : M.Valid) (hu0 : u0 ≠ 0) (hμ : ∀ c, M.μ c = base + t c • u0)
    (c c' : Fin k) :
    sqNormIn M.S (M.μ c - M.μ c') = (acoef M u0 t c - acoef M u0 t c') ^ 2 / M.sigmaSq u0 := by
  rw [sqNormIn_sub_eq hμ, inv_quad_S_u0_eq hM hu0, acoef, acoef, ← sub_mul, mul_pow,
    Real.sq_sqrt (kapU_nonneg hM u0)]
  ring

/-! ### Comparison with a diagonal -/

/-- **`cov_W⁻¹` is bounded** when `cov_W` is close to a diagonal: if `vᵀ diag(e) v ≤
(1 + ε) vᵀ cov_W v` for all `v`, with all `e_i ≥ 1/2` and `ε ≤ 1/2`, then
`fᵀ cov_W⁻¹ f ≤ 3 ‖f‖²`. -/
theorem covW_inv_le (hM : M.Valid) (hW : IsUnit W) {e : Fin d → ℝ} (he : ∀ i, 1 / 2 ≤ e i)
    {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hup : ∀ v, quad (diagonal e) v ≤ (1 + ε) * quad (covW M W) v) (f : Fin d → ℝ) :
    f ⬝ᵥ ((covW M W)⁻¹ *ᵥ f) ≤ 3 * (f ⬝ᵥ f) :=
  inv_quad_le_of_diagonal (covW_posDef hM hW) he hε hup f

/-- `BS23.ColinearSoS.covW_inv_le` for a coordinate vector: `e_jᵀ cov_W⁻¹ e_j ≤ 3`. -/
theorem covW_inv_single_le (hM : M.Valid) (hW : IsUnit W) {e : Fin d → ℝ}
    (he : ∀ i, 1 / 2 ≤ e i) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hup : ∀ v, quad (diagonal e) v ≤ (1 + ε) * quad (covW M W) v) (j : Fin d) :
    (Pi.single j 1 : Fin d → ℝ) ⬝ᵥ ((covW M W)⁻¹ *ᵥ Pi.single j 1) ≤ 3 := by
  have h := covW_inv_le hM hW he hε hup (Pi.single j 1)
  have h1 : (Pi.single j 1 : Fin d → ℝ) ⬝ᵥ Pi.single j 1 = 1 := by simp
  rwa [h1, mul_one] at h

end BS23.ColinearSoS
