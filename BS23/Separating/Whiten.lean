module

public import BS23.Colinear.Basis
public import BS23.Colinear.Cast
public import BS23.Colinear.Line

/-!
# Rational whitening of the sample

Step 2 of the algorithm for [BS23, Theorem 1.1]. The points `Y` are centered at their empirical
mean `ȳ` and mapped by the matrix `W = W Ĉ` (`BS23.Separating.W`) whose `i`-th row is the
`Ĉ`-orthogonal basis vector `λᵢ = BS23.Colinear.basisVec Ĉ i` divided by the power of two
`hᵢ = BS23.Separating.scaleOf (λᵢᵀĈλᵢ) = 2 ^ ⌈log₄ (λᵢᵀĈλᵢ / 2)⌉`
(`BS23.Separating.wRow`). All of this is rational arithmetic: the whitened points
`Xⱼ = W (Yⱼ - ȳ)` (`BS23.Separating.whiten`) are computed exactly by the machine, and over `ℚ`
they are the casts of the real ones (`BS23.Separating.whiten_cast`).

* **Normalization.** `κ(q) = q / (scaleOf q)² ∈ (1/2, 2]` for `q > 0`
  (`BS23.Separating.half_lt_div_scaleOf_sq`, `BS23.Separating.div_scaleOf_sq_le_two`).
* **Whitened covariance.** For a symmetric `C`, `W C · C · (W C)ᵀ = diag κ` with
  `κᵢ = λᵢᵀCλᵢ / hᵢ²` (`BS23.Separating.W_mul_mul_transpose`), and `κᵢ ∈ (1/2, 2]` when `C` is
  positive definite (`BS23.Separating.half_lt_kappa`, `BS23.Separating.kappa_le_two`). The
  whitened points have mean zero (`BS23.Separating.mean_whiten`) and empirical covariance
  `W Ĉ Wᵀ` (`BS23.Separating.empCov_whiten`, `BS23.Separating.sum_whiten_mul_whiten`), which is
  `diag κ` when `Ĉ` is positive definite (`BS23.Separating.empCov_whiten_eq_diagonal`).
* **Invertibility.** `det(W)² det C = ∏ᵢ κᵢ` (`BS23.Separating.det_W_sq_mul_det`), so `W C` is
  invertible for a positive definite `C` (`BS23.Separating.det_W_ne_zero`,
  `BS23.Separating.isUnit_W`).
* **Pointwise.** If all `κᵢ ∈ (1/2, 2]` then `‖v‖²/2 < vᵀ diag(κ) v ≤ 2 ‖v‖²` for `v ≠ 0`
  (`BS23.Separating.half_sum_sq_lt_dotProduct_diagonal`,
  `BS23.Separating.dotProduct_diagonal_le_two_mul`), so `‖v‖²/2 < vᵀĈ_X v ≤ 2 ‖v‖²` for the
  covariance `Ĉ_X` of the whitened points
  (`BS23.Separating.half_sum_sq_lt_quad_empCov_whiten`,
  `BS23.Separating.quad_empCov_whiten_le`).
* **Pairs.** `∑_{i,j} ⟨Yᵢ - Yⱼ, v⟩² = 2 n² vᵀĈv` (`BS23.Separating.sum_sum_sq_sub_dotProduct`);
  for the whitened points, `‖v‖² < n⁻² ∑_{i,j} ⟨Xᵢ - Xⱼ, v⟩² ≤ 4 ‖v‖²` for `v ≠ 0`
  (`BS23.Separating.sum_sq_lt_pairSum_whiten`, `BS23.Separating.pairSum_whiten_le`).
* **Identities.** `uᵀĈv = (1/n) ∑ⱼ ⟨u, Yⱼ - ȳ⟩⟨v, Yⱼ - ȳ⟩`
  (`BS23.Separating.dotProduct_empCov_mulVec`, `BS23.Separating.quad_empCov`),
  `⟨Xⱼ, v⟩ = ⟨Yⱼ - ȳ, Wᵀv⟩` (`BS23.Separating.whiten_dotProduct`),
  `(Wᵀv)ᵀ C (Wᵀv) = vᵀ diag(κ) v` (`BS23.Separating.quad_transpose_W_mulVec`), and `Ĉ` is
  positive definite as soon as its quadratic form is positive
  (`BS23.Separating.empCov_posDef_of_quad_pos`).
-/

@[expose] public section

namespace BS23.Separating

open Matrix Colinear

variable {n d : ℕ}

section Defs

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K]

/-- The power of two `2^e`, `e = ⌈log₄ (q / 2)⌉`, by which a basis vector with quadratic form
value `q` is divided: `q / (scaleOf q)² ∈ (1/2, 2]` for `q > 0`. -/
def scaleOf (q : K) : K := topScale (1 / 2) q

/-- The `i`-th whitening row: the `C`-orthogonal basis vector `λᵢ` divided by
`scaleOf (λᵢᵀCλᵢ)`. -/
def wRow (C : Matrix (Fin d) (Fin d) K) (i : Fin d) : Fin d → K :=
  (scaleOf (quad C (basisVec C i)))⁻¹ • basisVec C i

/-- The whitening matrix, with rows `BS23.Separating.wRow C i`. -/
def W (C : Matrix (Fin d) (Fin d) K) : Matrix (Fin d) (Fin d) K := Matrix.of (wRow C)

/-- The `i`-th diagonal entry `κᵢ = λᵢᵀCλᵢ / (scaleOf (λᵢᵀCλᵢ))²` of `W C · C · (W C)ᵀ`. -/
def kappa (C : Matrix (Fin d) (Fin d) K) (i : Fin d) : K :=
  quad C (basisVec C i) / scaleOf (quad C (basisVec C i)) ^ 2

/-- The whitened points `Xⱼ = W Ĉ (Yⱼ - ȳ)`. -/
def whiten (Y : Fin n → Fin d → K) : Fin n → Fin d → K :=
  fun j i ↦ wRow (empCov Y) i ⬝ᵥ (Y j - mean Y)

end Defs

/-! ### Generalities on centered points and quadratic forms -/

section Field

variable {K : Type*} [Field K]

/-- The centered points sum to zero. -/
theorem sum_sub_mean [CharZero K] (Y : Fin n → Fin d → K) : ∑ j, (Y j - mean Y) = 0 := by
  funext a
  rw [Finset.sum_apply, Pi.zero_apply]
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mean]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hn.ne'), sub_self]

/-- The bilinear form of the empirical covariance:
`uᵀĈv = (1/n) ∑ⱼ ⟨u, Yⱼ - ȳ⟩ ⟨v, Yⱼ - ȳ⟩`. -/
theorem dotProduct_empCov_mulVec (Y : Fin n → Fin d → K) (u v : Fin d → K) :
    u ⬝ᵥ (empCov Y *ᵥ v) =
      (∑ j, (u ⬝ᵥ (Y j - mean Y)) * (v ⬝ᵥ (Y j - mean Y))) / n := by
  simp only [dotProduct, mulVec, empCov, Pi.sub_apply, Finset.sum_mul, Finset.mul_sum,
    Finset.sum_div]
  -- both sides as `∑ a, ∑ b, ∑ j` (`u` indexed by `a`, `v` by `b`)
  conv_rhs => rw [Finset.sum_comm]; enter [2, b]; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-- `vᵀĈv = (1/n) ∑ⱼ ⟨Yⱼ - ȳ, v⟩²`. -/
theorem quad_empCov (Y : Fin n → Fin d → K) (v : Fin d → K) :
    quad (empCov Y) v = (∑ j, ((Y j - mean Y) ⬝ᵥ v) ^ 2) / n := by
  rw [quad, dotProduct_empCov_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [dotProduct_comm, sq]

/-- `(A C Bᵀ)_{ab} = ⟨A_a, C B_b⟩` (rows `A_a`, `B_b`). -/
theorem mul_mul_transpose_apply (A C B : Matrix (Fin d) (Fin d) K) (a b : Fin d) :
    (A * C * Bᵀ) a b = A a ⬝ᵥ (C *ᵥ B b) := by
  rw [mul_mul_apply, transpose_transpose]

/-- `(Aᵀv)ᵀ C (Aᵀv) = vᵀ (A C Aᵀ) v`. -/
theorem quad_transpose_mulVec (A C : Matrix (Fin d) (Fin d) K) (v : Fin d → K) :
    quad C (Aᵀ *ᵥ v) = quad (A * C * Aᵀ) v := by
  rw [quad, quad, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec v A, ← mulVec_transpose]

/-- `∑_{i,j} ⟨Yᵢ - Yⱼ, v⟩² = 2 n² vᵀĈv`. -/
theorem sum_sum_sq_sub_dotProduct [CharZero K] (Y : Fin n → Fin d → K) (v : Fin d → K) :
    ∑ i, ∑ j, ((Y i - Y j) ⬝ᵥ v) ^ 2 = 2 * (n : K) ^ 2 * quad (empCov Y) v := by
  set x : Fin n → K := fun j ↦ (Y j - mean Y) ⬝ᵥ v with hx
  have hsub : ∀ i j, (Y i - Y j) ⬝ᵥ v = x i - x j := by
    intro i j
    rw [hx, ← sub_dotProduct]
    congr 1
    abel
  have hsum : ∑ j, x j = 0 := by
    rw [hx, ← sum_dotProduct, sum_sub_mean, zero_dotProduct]
  have hexp : ∑ i, ∑ j, (x i - x j) ^ 2 =
      2 * (n : K) * ∑ j, x j ^ 2 - 2 * (∑ j, x j) * ∑ j, x j := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  simp only [hsub]
  rw [hexp, hsum, quad_empCov]
  rcases eq_or_ne (n : K) 0 with hn | hn
  · rw [hn]
    ring
  · field_simp
    ring

theorem dotProduct_diagonal_mulVec (κ v : Fin d → K) :
    v ⬝ᵥ (diagonal κ *ᵥ v) = ∑ i, κ i * v i ^ 2 := by
  simp only [dotProduct, mulVec_diagonal]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end Field

/-! ### Pointwise bounds for a diagonal form -/

section Order

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- `vᵀ diag(κ) v ≤ 2 ‖v‖²` if all `κᵢ ≤ 2`. -/
theorem dotProduct_diagonal_le_two_mul {κ : Fin d → K} (hκ : ∀ i, κ i ≤ 2) (v : Fin d → K) :
    v ⬝ᵥ (diagonal κ *ᵥ v) ≤ 2 * ∑ i, v i ^ 2 := by
  rw [dotProduct_diagonal_mulVec, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right (hκ i) (sq_nonneg _)

/-- `‖v‖²/2 < vᵀ diag(κ) v` if all `κᵢ > 1/2` and `v ≠ 0`. -/
theorem half_sum_sq_lt_dotProduct_diagonal {κ : Fin d → K} (hκ : ∀ i, 1 / 2 < κ i)
    {v : Fin d → K} (hv : v ≠ 0) :
    1 / 2 * ∑ i, v i ^ 2 < v ⬝ᵥ (diagonal κ *ᵥ v) := by
  rw [dotProduct_diagonal_mulVec, Finset.mul_sum]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := hi
  exact Finset.sum_lt_sum (fun j _ ↦ mul_le_mul_of_nonneg_right (hκ j).le (sq_nonneg _))
    ⟨i, Finset.mem_univ _, mul_lt_mul_of_pos_right (hκ i) (by positivity)⟩

end Order

/-! ### The scale and the whitened points -/

section Floor

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K]

theorem scaleOf_eq (q : K) : scaleOf q = 2 ^ Int.clog 4 (q / 2) := by
  rw [scaleOf, topScale]
  congr 2
  ring

theorem W_apply (C : Matrix (Fin d) (Fin d) K) (i k : Fin d) : W C i k = wRow C i k :=
  rfl

theorem wRow_dotProduct (C : Matrix (Fin d) (Fin d) K) (i : Fin d) (v : Fin d → K) :
    wRow C i ⬝ᵥ v = (scaleOf (quad C (basisVec C i)))⁻¹ * (basisVec C i ⬝ᵥ v) := by
  rw [wRow, smul_dotProduct, smul_eq_mul]

/-- The whitened points are `W Ĉ (Yⱼ - ȳ)`. -/
theorem whiten_eq_mulVec (Y : Fin n → Fin d → K) (j : Fin n) :
    whiten Y j = W (empCov Y) *ᵥ (Y j - mean Y) :=
  rfl

/-- `⟨Xⱼ, v⟩ = ⟨Yⱼ - ȳ, Wᵀ v⟩`. -/
theorem whiten_dotProduct (Y : Fin n → Fin d → K) (j : Fin n) (v : Fin d → K) :
    whiten Y j ⬝ᵥ v = (Y j - mean Y) ⬝ᵥ ((W (empCov Y))ᵀ *ᵥ v) := by
  rw [whiten_eq_mulVec, dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- **The empirical second moments of the whitened points** are `W Ĉ Wᵀ`. -/
theorem sum_whiten_mul_whiten (Y : Fin n → Fin d → K) (a b : Fin d) :
    (∑ j, whiten Y j a * whiten Y j b) / n =
      (W (empCov Y) * empCov Y * (W (empCov Y))ᵀ) a b := by
  rw [mul_mul_transpose_apply, dotProduct_empCov_mulVec]
  rfl

theorem one_div_mul_sum_whiten_mul_whiten (Y : Fin n → Fin d → K) (a b : Fin d) :
    1 / (n : K) * ∑ j, whiten Y j a * whiten Y j b =
      (W (empCov Y) * empCov Y * (W (empCov Y))ᵀ) a b := by
  rw [one_div_mul_eq_div, sum_whiten_mul_whiten]

theorem scaleOf_sq (q : K) : scaleOf q ^ 2 = 4 ^ Int.clog 4 (q / 2) := by
  rw [scaleOf_eq, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul]
  norm_num

/-- **The whitened points have mean zero.** -/
theorem mean_whiten (Y : Fin n → Fin d → K) : mean (whiten Y) = 0 := by
  funext i
  change (∑ j, wRow (empCov Y) i ⬝ᵥ (Y j - mean Y)) / n = 0
  rw [← dotProduct_sum, sum_sub_mean, dotProduct_zero, zero_div]

/-- **The empirical covariance of the whitened points** is `W Ĉ Wᵀ`. -/
theorem empCov_whiten (Y : Fin n → Fin d → K) :
    empCov (whiten Y) = W (empCov Y) * empCov Y * (W (empCov Y))ᵀ := by
  ext a b
  rw [← sum_whiten_mul_whiten]
  simp only [empCov, mean_whiten, Pi.zero_apply, sub_zero]

variable [IsStrictOrderedRing K]

theorem scaleOf_pos (q : K) : 0 < scaleOf q := by
  rw [scaleOf_eq]
  exact zpow_pos two_pos _

theorem scaleOf_ne_zero (q : K) : scaleOf q ≠ 0 :=
  (scaleOf_pos q).ne'

/-- `q / (scaleOf q)² ≤ 2`. -/
theorem div_scaleOf_sq_le_two (q : K) : q / scaleOf q ^ 2 ≤ 2 := by
  have h := Int.self_le_zpow_clog (R := K) (b := 4) (by norm_num) (q / 2)
  rw [Nat.cast_ofNat, ← scaleOf_sq] at h
  rw [div_le_iff₀ (pow_pos (scaleOf_pos q) 2)]
  linarith

/-- `1/2 < q / (scaleOf q)²` for `q > 0`. -/
theorem half_lt_div_scaleOf_sq {q : K} (hq : 0 < q) : 1 / 2 < q / scaleOf q ^ 2 := by
  have h := Int.zpow_pred_clog_lt_self (R := K) (b := 4) (by norm_num) (half_pos hq)
  rw [Nat.cast_ofNat, zpow_sub_one₀ (by norm_num), ← scaleOf_sq] at h
  rw [lt_div_iff₀ (pow_pos (scaleOf_pos q) 2)]
  linarith

theorem kappa_le_two (C : Matrix (Fin d) (Fin d) K) (i : Fin d) : kappa C i ≤ 2 :=
  div_scaleOf_sq_le_two _

end Floor

/-! ### Over the reals -/

section Real

theorem kappa_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) : 0 < kappa C i :=
  div_pos (quad_basisVec_pos hC i) (pow_pos (scaleOf_pos _) 2)

/-- `κᵢ > 1/2` for a positive definite `C`. -/
theorem half_lt_kappa {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    1 / 2 < kappa C i :=
  half_lt_div_scaleOf_sq (quad_basisVec_pos hC i)

/-- **Whitening a symmetric matrix**: `W C · C · (W C)ᵀ = diag κ`. -/
theorem W_mul_mul_transpose {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) :
    W C * C * (W C)ᵀ = diagonal (kappa C) := by
  ext a b
  rw [mul_mul_transpose_apply]
  change wRow C a ⬝ᵥ (C *ᵥ wRow C b) = _
  rw [wRow, wRow, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, kappa, ← quad]
    field_simp [scaleOf_ne_zero]
  · rw [diagonal_apply_ne _ hab, basisVec_orth hC hab, mul_zero, mul_zero]

/-- `det(W)² det C = ∏ᵢ κᵢ`. -/
theorem det_W_sq_mul_det {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) :
    (W C).det ^ 2 * C.det = ∏ i, kappa C i := by
  rw [← det_diagonal, ← W_mul_mul_transpose hC, det_mul, det_mul, det_transpose]
  ring

/-- **The whitening matrix is invertible** for a positive definite `C`. -/
theorem det_W_ne_zero {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) : (W C).det ≠ 0 := by
  intro h
  have h' := det_W_sq_mul_det (transpose_eq_of_posDef hC)
  rw [h] at h'
  have hpos : 0 < ∏ i, kappa C i := Finset.prod_pos fun i _ ↦ kappa_pos hC i
  simp at h'
  linarith

theorem isUnit_W {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) : IsUnit (W C) :=
  (isUnit_iff_isUnit_det _).mpr (det_W_ne_zero hC).isUnit

/-- `(Wᵀv)ᵀ C (Wᵀv) = vᵀ diag(κ) v` for a symmetric `C`. -/
theorem quad_transpose_W_mulVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) (v : Fin d → ℝ) :
    quad C ((W C)ᵀ *ᵥ v) = v ⬝ᵥ (diagonal (kappa C) *ᵥ v) := by
  rw [quad_transpose_mulVec, W_mul_mul_transpose hC, quad]

/-- **The whitened points have covariance `diag κ`** when `Ĉ` is positive definite. -/
theorem empCov_whiten_eq_diagonal {Y : Fin n → Fin d → ℝ} (hC : (empCov Y).PosDef) :
    empCov (whiten Y) = diagonal (kappa (empCov Y)) := by
  rw [empCov_whiten, W_mul_mul_transpose (transpose_eq_of_posDef hC)]

/-- `‖v‖²/2 < vᵀĈ_X v` for the covariance `Ĉ_X` of the whitened points and `v ≠ 0`. -/
theorem half_sum_sq_lt_quad_empCov_whiten {Y : Fin n → Fin d → ℝ} (hC : (empCov Y).PosDef)
    {v : Fin d → ℝ} (hv : v ≠ 0) :
    1 / 2 * ∑ i, v i ^ 2 < quad (empCov (whiten Y)) v := by
  rw [empCov_whiten_eq_diagonal hC, quad]
  exact half_sum_sq_lt_dotProduct_diagonal (half_lt_kappa hC) hv

/-- `vᵀĈ_X v ≤ 2 ‖v‖²` for the covariance `Ĉ_X` of the whitened points. -/
theorem quad_empCov_whiten_le {Y : Fin n → Fin d → ℝ} (hC : (empCov Y).PosDef)
    (v : Fin d → ℝ) : quad (empCov (whiten Y)) v ≤ 2 * ∑ i, v i ^ 2 := by
  rw [empCov_whiten_eq_diagonal hC, quad]
  exact dotProduct_diagonal_le_two_mul (kappa_le_two _) v

/-- `‖v‖² < n⁻² ∑_{i,j} ⟨Xᵢ - Xⱼ, v⟩²` for the whitened points and `v ≠ 0`. -/
theorem sum_sq_lt_pairSum_whiten {Y : Fin n → Fin d → ℝ} (hC : (empCov Y).PosDef)
    {v : Fin d → ℝ} (hv : v ≠ 0) :
    ∑ i, v i ^ 2 < (∑ i, ∑ j, ((whiten Y i - whiten Y j) ⬝ᵥ v) ^ 2) / (n : ℝ) ^ 2 := by
  have hn : (n : ℝ) ≠ 0 := by
    intro hn
    have h0 : empCov Y = 0 := by
      ext a b
      simp [empCov, hn]
    have := quad_pos hC hv
    simp [h0, quad] at this
  rw [sum_sum_sq_sub_dotProduct, mul_div_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero 2 hn)]
  have := half_sum_sq_lt_quad_empCov_whiten hC hv
  linarith

/-- `n⁻² ∑_{i,j} ⟨Xᵢ - Xⱼ, v⟩² ≤ 4 ‖v‖²` for the whitened points. -/
theorem pairSum_whiten_le {Y : Fin n → Fin d → ℝ} (hC : (empCov Y).PosDef) (v : Fin d → ℝ) :
    (∑ i, ∑ j, ((whiten Y i - whiten Y j) ⬝ᵥ v) ^ 2) / (n : ℝ) ^ 2 ≤ 4 * ∑ i, v i ^ 2 := by
  rw [sum_sum_sq_sub_dotProduct]
  have h := quad_empCov_whiten_le hC v
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · rw [hn]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
      div_zero]
    positivity
  · rw [mul_div_right_comm, mul_div_cancel_right₀ _ (pow_ne_zero 2 hn)]
    linarith

/-- The empirical covariance is positive definite if its quadratic form is positive. -/
theorem empCov_posDef_of_quad_pos {Y : Fin n → Fin d → ℝ}
    (h : ∀ v, v ≠ 0 → 0 < quad (empCov Y) v) : (empCov Y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · change (empCov Y)ᴴ = empCov Y
    rw [conjTranspose_eq_transpose_of_trivial]
    exact empCov_transpose Y
  · rw [star_trivial]
    exact h x hx

end Real

/-! ### Casting from the rationals -/

section Cast

theorem scaleOf_cast (q : ℚ) : scaleOf (q : ℝ) = ((scaleOf q : ℚ) : ℝ) := by
  have h := topScale_cast (1 / 2) q
  push_cast at h
  exact h

theorem wRow_cast (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    wRow (C.map ((↑) : ℚ → ℝ)) i = fun k ↦ ((wRow C i k : ℚ) : ℝ) := by
  funext k
  simp only [wRow, basisVec_cast, quad_cast, scaleOf_cast, Pi.smul_apply, smul_eq_mul]
  push_cast
  rfl

theorem W_cast (C : Matrix (Fin d) (Fin d) ℚ) :
    W (C.map ((↑) : ℚ → ℝ)) = (W C).map ((↑) : ℚ → ℝ) := by
  ext i k
  simp only [W_apply, wRow_cast, map_apply]

theorem kappa_cast (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    kappa (C.map ((↑) : ℚ → ℝ)) i = ((kappa C i : ℚ) : ℝ) := by
  simp only [kappa, basisVec_cast, quad_cast, scaleOf_cast]
  push_cast
  rfl

/-- **Whitening commutes with casting**: the whitened real points of rational points are the
casts of the whitened rational points. -/
theorem whiten_cast (Y : Fin n → Fin d → ℚ) :
    whiten (fun j a ↦ (Y j a : ℝ)) = fun j i ↦ ((whiten Y j i : ℚ) : ℝ) := by
  funext j i
  simp only [whiten, empCov_cast, wRow_cast, mean_cast, sub_cast, dotProduct_cast]

end Cast

end BS23.Separating
