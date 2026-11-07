module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The ellipsoid method

The central-cut ellipsoid method with rounding, in the form an algorithm with exact rational
arithmetic can run [Grötschel–Lovász–Schrijver, *Geometric Algorithms and Combinatorial
Optimization*, §3.2]. Everything here is about real vectors and matrices; the algorithm, which
computes rational approximations, comes later.

* **Ellipsoids without inverses** (`Ellipsoid.Mem`): `x ∈ E(c, P)` means
  `(uᵀ (x - c))² ≤ uᵀ P u` for every `u`, which for positive definite `P` is the usual
  `(x - c)ᵀ P⁻¹ (x - c) ≤ 1`. Every argument below is then about quadratic forms of `P`, and no
  inverse is ever needed.
* **The step** (`Ellipsoid.stepCenter`, `Ellipsoid.stepShape`): cutting `E(c, P)` by `a` at its
  center gives `c' = c - σ P a / √(aᵀ P a)` and `P' = (1 + 4σ²) (P - 2σ (P a)(P a)ᵀ / (aᵀ P a))`,
  with `σ = 1/(4n)` in dimension `n`. These are not the smallest ellipsoid containing the
  half-ellipsoid (that has `σ = 1/(n+1)`): they leave slack. `Ellipsoid.mem_step`: every point of
  the half-ellipsoid is in `E(c', (1 - σ²) P')`.
* **Rounding** (`Ellipsoid.step`): the slack absorbs rounding. If `c₁` and `P₁` are within `δ` of
  `c'` and `P'` entry by entry, and `δ` is small compared to the smallest eigenvalue of `P`, then
  `E(c₁, P₁)` still contains the half-ellipsoid, and `det P₁ ≤ (1 - 3σ/4) det P`. The proof of
  the volume bound uses that determinants are monotone in the Loewner order
  (`Ellipsoid.det_le_det_of_posSemidef_sub`).
* **The method** (`Ellipsoid.iterate`): after `K` steps, every point that each cut kept is still in
  the ellipsoid, whose determinant is at most `(1 - 3σ/4)^K` times the first one. An ellipsoid
  that contains a ball of radius `r` has determinant at least `r^(2n)`
  (`Ellipsoid.pow_le_det_of_ball`), so the points kept cannot contain such a ball once
  `(1 - 3σ/4)^K det P₀ < r^(2n)`, which takes `K = O(n² log (R / r))` steps from a ball of
  radius `R` (`Ellipsoid.pow_six_mul_card_le`: every `6n` steps halve the bound).
* **Minimizing** (`Ellipsoid.exists_feasible_le`): cut infeasible centers by a separating
  hyperplane and feasible ones by the objective. If the feasible set contains a ball on which the
  objective is at most `v`, some feasible center has objective at most `v`.

The eigenvalues of the shapes stay between `λ / 4^k` and `2^k Λ`, so `O(K)` bits after the binary
point suffice for the rounding.
-/

@[expose] public section

namespace Ellipsoid

open Matrix

variable {ι : Type*} [Fintype ι]

/-! ### Determinants and the Loewner order -/

open scoped MatrixOrder in
/-- **Determinants are monotone** in the Loewner order: if `A` is positive definite and `B - A` is
positive semidefinite, then `det A ≤ det B`. With `S = √A`, the matrix `C = S⁻¹ B S⁻¹` has
`C - 1` positive semidefinite, so its eigenvalues are at least `1`, and
`det B / det A = det C ≥ 1`. -/
theorem det_le_det_of_posSemidef_sub [DecidableEq ι] {A B : Matrix ι ι ℝ} (hA : A.PosDef)
    (hBA : (B - A).PosSemidef) : A.det ≤ B.det := by
  set S := CFC.sqrt A
  have hS : S.PosSemidef := nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg A)
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A (nonneg_iff_posSemidef.2 hA.posSemidef)
  have hdetA : 0 < A.det := hA.det_pos
  have hdetS : S.det ≠ 0 := by
    intro h
    rw [← hSS, det_mul, h, zero_mul] at hdetA
    exact lt_irrefl _ hdetA
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.2 hdetS
  set T := S⁻¹
  have hTS : T * S = 1 := nonsing_inv_mul S hSu
  have hST : S * T = 1 := mul_nonsing_inv S hSu
  have hTh : Tᴴ = T := by rw [conjTranspose_nonsing_inv, hS.isHermitian.eq]
  -- `C = T B T` and `C - 1 = T (B - A) T` is positive semidefinite.
  have hC : (T * B * T - 1).PosSemidef := by
    have h := hBA.conjTranspose_mul_mul_same T
    rw [hTh] at h
    have : T * (B - A) * T = T * B * T - 1 := by
      rw [mul_sub, sub_mul, ← hSS, show T * (S * S) * T = (T * S) * (S * T) by
        simp only [Matrix.mul_assoc], hTS, hST, Matrix.one_mul]
    rwa [this] at h
  have hCh : (T * B * T).IsHermitian := by
    have h := hC.isHermitian
    rw [IsHermitian, conjTranspose_sub, conjTranspose_one] at h
    exact sub_left_injective h
  -- The eigenvalues of `C` are at least `1`.
  have heig : ∀ i, 1 ≤ hCh.eigenvalues i := by
    intro i
    rw [hCh.eigenvalues_eq]
    set v := hCh.eigenvectorBasis i
    have h1 := hC.dotProduct_mulVec_nonneg (WithLp.ofLp v)
    have hv : star (WithLp.ofLp v) ⬝ᵥ WithLp.ofLp v = 1 := by
      have := hCh.eigenvectorBasis.orthonormal.1 i
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, real_inner_self_eq_norm_sq,
        this, one_pow]
    rw [sub_mulVec, dotProduct_sub, one_mulVec, hv] at h1
    simpa using h1
  have hdetC : 1 ≤ (T * B * T).det := by
    rw [hCh.det_eq_prod_eigenvalues]
    simpa using Finset.one_le_prod₀ fun i (_ : i ∈ Finset.univ) ↦ heig i
  -- `det C det A = det B`.
  have hTS' : T.det * S.det = 1 := by rw [← det_mul, hTS, det_one]
  have hprod : (T * B * T).det * A.det = B.det := by
    rw [det_mul, det_mul, ← hSS, det_mul]
    calc T.det * B.det * T.det * (S.det * S.det) = B.det * (T.det * S.det) ^ 2 := by ring
      _ = B.det := by rw [hTS', one_pow, mul_one]
  calc A.det = 1 * A.det := (one_mul _).symm
    _ ≤ (T * B * T).det * A.det := mul_le_mul_of_nonneg_right hdetC hdetA.le
    _ = B.det := hprod

/-- A real symmetric matrix with `uᵀ P u ≥ 0` for all `u` is positive semidefinite. -/
theorem posSemidef_of_quad {P : Matrix ι ι ℝ} (hPs : Pᵀ = P) (hP : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) :
    P.PosSemidef :=
  .of_dotProduct_mulVec_nonneg (by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hPs])
    fun u ↦ by simpa using hP u

/-- A real symmetric matrix with `uᵀ P u > 0` for all `u ≠ 0` is positive definite. -/
theorem posDef_of_quad {P : Matrix ι ι ℝ} (hPs : Pᵀ = P) (hP : ∀ u, u ≠ 0 → 0 < u ⬝ᵥ P *ᵥ u) :
    P.PosDef :=
  .of_dotProduct_mulVec_pos (by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hPs])
    fun u hu ↦ by simpa using hP u hu

/-- If `uᵀ P u ≥ λ uᵀ u` for all `u`, with `λ > 0`, then `det P ≥ λⁿ`. -/
theorem pow_le_det [DecidableEq ι] {P : Matrix ι ι ℝ} (hPs : Pᵀ = P) {lam : ℝ} (hlam : 0 < lam)
    (hP : ∀ u, lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ P *ᵥ u) : lam ^ Fintype.card ι ≤ P.det := by
  have hA : (lam • (1 : Matrix ι ι ℝ)).PosDef := PosDef.one.smul hlam
  have hBA : (P - lam • (1 : Matrix ι ι ℝ)).PosSemidef := by
    refine posSemidef_of_quad (by rw [transpose_sub, transpose_smul, transpose_one, hPs]) fun u ↦ ?_
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    linarith [hP u]
  simpa [det_smul] using det_le_det_of_posSemidef_sub hA hBA

/-! ### Quadratic forms -/

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {P : Matrix ι ι ℝ} (hPs : Pᵀ = P) (u v : ι → ℝ) :
    v ⬝ᵥ P *ᵥ u = u ⬝ᵥ P *ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hPs, dotProduct_comm]

/-- **Cauchy–Schwarz** for the form of a positive semidefinite matrix:
`(uᵀ P v)² ≤ (uᵀ P u)(vᵀ P v)`. -/
theorem sq_dotProduct_mulVec_le {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    (hP : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) (u v : ι → ℝ) :
    (u ⬝ᵥ P *ᵥ v) ^ 2 ≤ (u ⬝ᵥ P *ᵥ u) * (v ⬝ᵥ P *ᵥ v) := by
  have h : ∀ t : ℝ, 0 ≤ (v ⬝ᵥ P *ᵥ v) * (t * t) + (2 * (u ⬝ᵥ P *ᵥ v)) * t + u ⬝ᵥ P *ᵥ u := by
    intro t
    have := hP (u + t • v)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, dotProduct_mulVec_comm hPs u v] at this
    linarith
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

/-! ### Ellipsoids and the step -/

/-- `x` is in the ellipsoid with center `c` and shape `P`: `(uᵀ (x - c))² ≤ uᵀ P u` for every `u`.
For positive definite `P` this is the usual `(x - c)ᵀ P⁻¹ (x - c) ≤ 1`; stated this way, it needs
no inverse. -/
def Mem (c : ι → ℝ) (P : Matrix ι ι ℝ) (x : ι → ℝ) : Prop :=
  ∀ u : ι → ℝ, (u ⬝ᵥ (x - c)) ^ 2 ≤ u ⬝ᵥ P *ᵥ u

/-- The step size `σ = 1 / (4n)` in dimension `n`. -/
noncomputable def stepSize (ι : Type*) [Fintype ι] : ℝ := 1 / (4 * Fintype.card ι)

/-- The center after a cut by `a` at the center: `c - σ P a / √(aᵀ P a)`. -/
noncomputable def stepCenter (c a : ι → ℝ) (P : Matrix ι ι ℝ) : ι → ℝ :=
  c - (stepSize ι / Real.sqrt (a ⬝ᵥ P *ᵥ a)) • (P *ᵥ a)

/-- The shape after a cut by `a` at the center: `(1 + 4σ²) (P - 2σ (P a)(P a)ᵀ / (aᵀ P a))`. -/
noncomputable def stepShape (a : ι → ℝ) (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (1 + 4 * stepSize ι ^ 2) •
    (P - (2 * stepSize ι / (a ⬝ᵥ P *ᵥ a)) • vecMulVec (P *ᵥ a) (P *ᵥ a))

theorem stepSize_pos [Nonempty ι] : 0 < stepSize ι := by
  unfold stepSize
  have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  positivity

theorem stepSize_le [Nonempty ι] : stepSize ι ≤ 1 / 4 := by
  unfold stepSize
  have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  gcongr
  linarith

theorem card_mul_stepSize [Nonempty ι] : (Fintype.card ι : ℝ) * stepSize ι = 1 / 4 := by
  unfold stepSize
  have : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  field_simp

theorem stepShape_transpose {a : ι → ℝ} {P : Matrix ι ι ℝ} (hPs : Pᵀ = P) :
    (stepShape a P)ᵀ = stepShape a P := by
  simp [stepShape, transpose_sub, transpose_smul, hPs, transpose_vecMulVec]

theorem quad_stepShape {a : ι → ℝ} {P : Matrix ι ι ℝ} (u : ι → ℝ) :
    u ⬝ᵥ stepShape a P *ᵥ u = (1 + 4 * stepSize ι ^ 2) *
      (u ⬝ᵥ P *ᵥ u - 2 * stepSize ι / (a ⬝ᵥ P *ᵥ a) * ((P *ᵥ a) ⬝ᵥ u) ^ 2) := by
  simp only [stepShape, smul_mulVec, sub_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_smul, dotProduct_sub, smul_eq_mul, dotProduct_comm u (P *ᵥ a)]
  ring

/-- The cut shrinks the volume: `det P' = (1 + 4σ²)ⁿ (1 - 2σ) det P`. -/
theorem det_stepShape [DecidableEq ι] {a : ι → ℝ} {P : Matrix ι ι ℝ}
    (ha : a ⬝ᵥ P *ᵥ a ≠ 0) :
    (stepShape a P).det =
      (1 + 4 * stepSize ι ^ 2) ^ Fintype.card ι * (1 - 2 * stepSize ι) * P.det := by
  set k := 2 * stepSize ι / (a ⬝ᵥ P *ᵥ a)
  have hfac : P - k • vecMulVec (P *ᵥ a) (P *ᵥ a) = P * (1 + vecMulVec (-k • a) (P *ᵥ a)) := by
    rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Matrix.add_apply,
      Pi.smul_apply, smul_eq_mul, neg_smul, mulVec_neg, mulVec_smul, Pi.neg_apply]
    ring
  have hk : k * (a ⬝ᵥ P *ᵥ a) = 2 * stepSize ι := div_mul_cancel₀ _ ha
  have hdot : (P *ᵥ a) ⬝ᵥ (-k • a) = -(2 * stepSize ι) := by
    rw [dotProduct_smul, dotProduct_comm, smul_eq_mul, neg_mul, hk]
  rw [stepShape, det_smul, hfac, det_mul, vecMulVec_eq Unit,
    det_one_add_replicateCol_mul_replicateRow, hdot]
  ring

/-! ### The scalar inequalities -/

/-- The inequality behind a step, in the coordinates of the cut. With `s = âᵀ (x - c)` along the
cut direction, `α` the component of `u` along it and `N` the rest, the old ellipsoid gives
`q² ≤ N (1 - s²)` for the remaining part `q` of `uᵀ (x - c)`. -/
theorem step_scalar {σ q N α s : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ 1 / 4) (hN : 0 ≤ N)
    (hq : q ^ 2 ≤ N * (1 - s ^ 2)) (hs₁ : -1 ≤ s) (hs₀ : s ≤ 0) :
    (q + α * (s + σ)) ^ 2 ≤ (1 - σ ^ 2) * ((1 + 4 * σ ^ 2) * (N + (1 - 2 * σ) * α ^ 2)) := by
  set κ := 1 - 2 * σ
  set t := s + σ
  set m := 1 - s ^ 2
  have hκ : 1 / 2 ≤ κ := by simp only [κ]; linarith
  have hκ0 : 0 < κ := by linarith
  have hm : 0 ≤ m := by simp only [m]; nlinarith
  -- `(q + α t)² ≤ (N + κ α²)(m + t² / κ)`, by the arithmetic-geometric mean inequality.
  set X := N * t ^ 2 / κ
  set Y := κ * α ^ 2 * m
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hXY : X * Y = N * m * (α * t) ^ 2 := by
    simp only [X, Y]
    field_simp
  have hsq : (2 * q * (α * t)) ^ 2 ≤ (X + Y) ^ 2 := by
    have h1 : q ^ 2 * (α * t) ^ 2 ≤ N * m * (α * t) ^ 2 :=
      mul_le_mul_of_nonneg_right hq (sq_nonneg _)
    nlinarith [sq_nonneg (X - Y)]
  have hcross : 2 * q * (α * t) ≤ X + Y := by
    have := sq_le_sq.1 hsq
    rw [abs_of_nonneg (add_nonneg hX hY)] at this
    exact (le_abs_self _).trans this
  have hamgm : (q + α * t) ^ 2 ≤ (N + κ * α ^ 2) * (m + t ^ 2 / κ) := by
    have : (N + κ * α ^ 2) * (m + t ^ 2 / κ) = N * m + X + Y + α ^ 2 * t ^ 2 := by
      simp only [X, Y]
      field_simp
      ring
    rw [this]
    nlinarith
  -- `m + t² / κ ≤ 1 + σ² / κ ≤ (1 - σ²)(1 + 4σ²)` on `-1 ≤ s ≤ 0`.
  have hφ : m + t ^ 2 / κ ≤ 1 + σ ^ 2 / κ := by
    have hnum : κ * m + t ^ 2 - κ - σ ^ 2 = 2 * σ * s * (s + 1) := by
      simp only [κ, m, t]
      ring
    have hdiff : m + t ^ 2 / κ - (1 + σ ^ 2 / κ) = (κ * m + t ^ 2 - κ - σ ^ 2) / κ := by
      field_simp
      ring
    have : (κ * m + t ^ 2 - κ - σ ^ 2) / κ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by
        rw [hnum]
        have h1 : 0 ≤ 2 * σ * (s + 1) := mul_nonneg (by linarith) (by linarith)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h1 hs₀]) hκ0.le
    linarith
  have hconst : 1 + σ ^ 2 / κ ≤ (1 - σ ^ 2) * (1 + 4 * σ ^ 2) := by
    have h2 : σ ^ 2 / κ ≤ 2 * σ ^ 2 := by
      rw [div_le_iff₀ hκ0]
      nlinarith
    have h3 : 0 ≤ 1 - 4 * σ ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg σ) h3]
  calc (q + α * (s + σ)) ^ 2 ≤ (N + κ * α ^ 2) * (m + t ^ 2 / κ) := hamgm
    _ ≤ (N + κ * α ^ 2) * ((1 - σ ^ 2) * (1 + 4 * σ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hφ.trans hconst) (by positivity)
    _ = _ := by ring

/-- Moving the center and shape a little keeps a point that is inside with slack `θ`. -/
theorem perturb_scalar {p r Q θ : ℝ} (hθ : 0 ≤ θ) (hQ : 0 ≤ Q)
    (hp : p ^ 2 ≤ (1 - θ) * Q) (hr : r ^ 2 ≤ θ ^ 2 / 64 * Q) : (p + r) ^ 2 ≤ (1 - θ / 4) * Q := by
  have h1 : (p * r) ^ 2 ≤ (θ * Q / 8) ^ 2 := by
    have : (p * r) ^ 2 = p ^ 2 * r ^ 2 := by ring
    rw [this]
    calc p ^ 2 * r ^ 2 ≤ ((1 - θ) * Q) * (θ ^ 2 / 64 * Q) :=
          mul_le_mul hp hr (sq_nonneg _) (by nlinarith)
      _ ≤ (θ * Q / 8) ^ 2 := by nlinarith [mul_nonneg hθ hQ, sq_nonneg (θ * Q)]
  have h2 : p * r ≤ θ * Q / 8 := by
    have := sq_le_sq.1 h1
    rw [abs_of_nonneg (by positivity : 0 ≤ θ * Q / 8)] at this
    exact (le_abs_self _).trans this
  nlinarith [mul_nonneg (mul_nonneg hθ hθ) hQ]

/-- `(1 + x)ⁿ ≤ 1 / (1 - n x)` for `0 ≤ x` and `n x < 1`, as `(1 + x)ⁿ (1 - n x) ≤ 1`. -/
theorem one_add_pow_mul_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (1 + x) ^ n * (1 - n * x) ≤ 1 := by
  rcases le_or_gt (1 - n * x) 0 with h | h
  · exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) h).trans zero_le_one
  · have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) n
    rw [mul_neg, ← sub_eq_add_neg, ← sub_eq_add_neg] at hb
    calc (1 + x) ^ n * (1 - n * x) ≤ (1 + x) ^ n * (1 - x) ^ n := by
          gcongr
      _ = (1 - x ^ 2) ^ n := by rw [← mul_pow]; ring
      _ ≤ 1 := pow_le_one₀ (by nlinarith) (by nlinarith)

/-- The volume factor of a rounded step: `((1 + σ²/4)(1 + 4σ²))ⁿ (1 - 2σ) ≤ 1 - 3σ/4` for
`σ = 1 / (4n)`. -/
theorem volume_factor_le [Nonempty ι] :
    ((1 + stepSize ι ^ 2 / 4) * (1 + 4 * stepSize ι ^ 2)) ^ Fintype.card ι *
      (1 - 2 * stepSize ι) ≤ 1 - 3 * stepSize ι / 4 := by
  set σ := stepSize ι
  set n := Fintype.card ι
  have hσ := stepSize_pos (ι := ι)
  have hσ' := stepSize_le (ι := ι)
  have hnσ : (n : ℝ) * σ = 1 / 4 := card_mul_stepSize
  have hx : (1 + σ ^ 2 / 4) * (1 + 4 * σ ^ 2) ≤ 1 + 5 * σ ^ 2 := by
    have h3 : 0 ≤ 3 / 4 - σ ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sq_nonneg σ) h3]
  have hpow := one_add_pow_mul_le (x := 5 * σ ^ 2) (by positivity) (by nlinarith) n
  have hnx : (n : ℝ) * (5 * σ ^ 2) = 5 * σ / 4 := by
    rw [show (n : ℝ) * (5 * σ ^ 2) = 5 * σ * (n * σ) by ring, hnσ]
    ring
  rw [hnx] at hpow
  have hle : ((1 + σ ^ 2 / 4) * (1 + 4 * σ ^ 2)) ^ n ≤ (1 + 5 * σ ^ 2) ^ n :=
    pow_le_pow_left₀ (by positivity) hx n
  have h12 : 0 ≤ 1 - 2 * σ := by linarith
  calc ((1 + σ ^ 2 / 4) * (1 + 4 * σ ^ 2)) ^ n * (1 - 2 * σ)
      ≤ (1 + 5 * σ ^ 2) ^ n * ((1 - 5 * σ / 4) * (1 - 3 * σ / 4)) := by
        gcongr
        nlinarith
    _ = (1 + 5 * σ ^ 2) ^ n * (1 - 5 * σ / 4) * (1 - 3 * σ / 4) := by ring
    _ ≤ 1 * (1 - 3 * σ / 4) := by gcongr; linarith
    _ = 1 - 3 * σ / 4 := one_mul _

/-! ### The step -/

/-- **The exact step keeps the half-ellipsoid, with slack.** If `x` is in the ellipsoid
`E(c, P)` and on the side `aᵀ (x - c) ≤ 0` of the cut, then
`(uᵀ (x - c'))² ≤ (1 - σ²) uᵀ P' u` for every `u`, where `c'` and `P'` are the new center and
shape. -/
theorem mem_step [Nonempty ι] {c a x : ι → ℝ} {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    (hP : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) (ha : 0 < a ⬝ᵥ P *ᵥ a) (hx : Mem c P x)
    (hcut : a ⬝ᵥ (x - c) ≤ 0) (u : ι → ℝ) :
    (u ⬝ᵥ (x - stepCenter c a P)) ^ 2 ≤ (1 - stepSize ι ^ 2) * (u ⬝ᵥ stepShape a P *ᵥ u) := by
  set σ := stepSize ι
  set s₀ := a ⬝ᵥ P *ᵥ a
  set w := Real.sqrt s₀
  have hw0 : 0 < w := Real.sqrt_pos.2 ha
  have hw : w ^ 2 = s₀ := Real.sq_sqrt ha.le
  set y := x - c
  set α' := u ⬝ᵥ P *ᵥ a
  set t₀ := a ⬝ᵥ y
  set N := u ⬝ᵥ P *ᵥ u - α' ^ 2 / s₀
  set q := u ⬝ᵥ y - α' / s₀ * t₀
  have hsym : a ⬝ᵥ P *ᵥ u = α' := dotProduct_mulVec_comm hPs u a
  have hN : 0 ≤ N := by
    have := sq_dotProduct_mulVec_le hPs hP u a
    simp only [N]
    rw [sub_nonneg, div_le_iff₀ ha]
    exact this
  -- The old ellipsoid, in the direction `u - (α' / s₀) a + λ a`.
  have key : ∀ l : ℝ, (q + l * t₀) ^ 2 ≤ N + l ^ 2 * s₀ := by
    intro l
    have h := hx (u + (l - α' / s₀) • a)
    have e1 : (u + (l - α' / s₀) • a) ⬝ᵥ y = q + l * t₀ := by
      simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, q, t₀]
      ring
    have e2 : (u + (l - α' / s₀) • a) ⬝ᵥ P *ᵥ (u + (l - α' / s₀) • a) = N + l ^ 2 * s₀ := by
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul, hsym, N]
      field_simp
      ring
    rwa [e1, e2] at h
  -- So `s₀ q² ≤ N (s₀ - t₀²)`.
  have ht₀ : t₀ ^ 2 ≤ s₀ := hx a
  have hdisc : s₀ * q ^ 2 ≤ N * (s₀ - t₀ ^ 2) := by
    have h : ∀ l : ℝ, 0 ≤ (s₀ - t₀ ^ 2) * (l * l) + (-2 * q * t₀) * l + (N - q ^ 2) := by
      intro l
      nlinarith [key l]
    have := discrim_le_zero h
    rw [discrim] at this
    nlinarith
  -- In the coordinates of the cut: `s = t₀ / w`, `α = α' / w`.
  set s := t₀ / w
  set α := α' / w
  have hq : q ^ 2 ≤ N * (1 - s ^ 2) := by
    have : s ^ 2 = t₀ ^ 2 / s₀ := by rw [div_pow, hw]
    rw [this, mul_sub, mul_one, ← sub_nonneg]
    have : N - N * (t₀ ^ 2 / s₀) - q ^ 2 = (N * (s₀ - t₀ ^ 2) - s₀ * q ^ 2) / s₀ := by
      field_simp
    rw [this]
    exact div_nonneg (by linarith) ha.le
  have hs₀ : s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hcut hw0.le
  have hs₁ : -1 ≤ s := by
    rw [le_div_iff₀ hw0]
    have := sq_le_sq.1 (show t₀ ^ 2 ≤ w ^ 2 by rw [hw]; exact ht₀)
    rw [abs_of_pos hw0] at this
    linarith [neg_abs_le t₀]
  have hlhs : u ⬝ᵥ (x - stepCenter c a P) = q + α * (s + σ) := by
    have : x - stepCenter c a P = y + (σ / w) • (P *ᵥ a) := by
      simp only [stepCenter, y, w, σ]
      abel
    rw [this, dotProduct_add, dotProduct_smul, smul_eq_mul]
    simp only [q, α, s, α']
    field_simp
    linear_combination (u ⬝ᵥ P *ᵥ a * t₀) * hw
  have hrhs : u ⬝ᵥ stepShape a P *ᵥ u = (1 + 4 * σ ^ 2) * (N + (1 - 2 * σ) * α ^ 2) := by
    rw [quad_stepShape, dotProduct_comm (P *ᵥ a) u]
    simp only [N, α, div_pow, hw]
    ring
  rw [hlhs, hrhs]
  exact step_scalar stepSize_pos stepSize_le hN hq hs₁ hs₀

/-- `|uᵀ v| ≤ δ ∑ |uᵢ|` when every `|vᵢ| ≤ δ`. -/
theorem abs_dotProduct_le {u v : ι → ℝ} {δ : ℝ} (hv : ∀ i, |v i| ≤ δ) :
    |u ⬝ᵥ v| ≤ δ * ∑ i, |u i| := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hv i) (abs_nonneg _)

/-- `|uᵀ E u| ≤ δ (∑ |uᵢ|)²` when every `|E i j| ≤ δ`. -/
theorem abs_quad_le {u : ι → ℝ} {E : Matrix ι ι ℝ} {δ : ℝ} (hE : ∀ i j, |E i j| ≤ δ) :
    |u ⬝ᵥ E *ᵥ u| ≤ δ * (∑ i, |u i|) ^ 2 := by
  have h : ∀ i, |(E *ᵥ u) i| ≤ δ * ∑ j, |u j| := fun i ↦ by
    have : (E *ᵥ u) i = u ⬝ᵥ (fun j ↦ E i j) := by simp [mulVec, dotProduct_comm]
    rw [this]
    exact abs_dotProduct_le fun j ↦ hE i j
  calc |u ⬝ᵥ E *ᵥ u| ≤ (δ * ∑ j, |u j|) * ∑ i, |u i| := abs_dotProduct_le h
    _ = δ * (∑ i, |u i|) ^ 2 := by ring

theorem dotProduct_self_nonneg' (u : ι → ℝ) : 0 ≤ u ⬝ᵥ u :=
  Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _

/-- `(∑ |uᵢ|)² ≤ n uᵀu`. -/
theorem sq_sum_abs_le (u : ι → ℝ) : (∑ i, |u i|) ^ 2 ≤ Fintype.card ι * (u ⬝ᵥ u) := by
  have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ |u i|)
  simpa [dotProduct, sq_abs, ← sq] using this

/-! ### The rounded step -/

/-- **One step of the ellipsoid method, rounded.** Let `P` be symmetric with
`λ uᵀu ≤ uᵀ P u ≤ Λ uᵀu`, and cut by `a ≠ 0` at the center `c`. If `c₁` and the symmetric `P₁` are
within `δ` of the exact new center and shape, entry by entry, and `δ` is small compared to `λ`,
then:
* the new ellipsoid contains every point of the old one on the side `aᵀ (x - c) ≤ 0`;
* its determinant is at most `1 - 3σ/4` times the old one, where `σ = 1/(4n)`;
* `(λ/4) uᵀu ≤ uᵀ P₁ u ≤ 2Λ uᵀu`;
* the center moves by at most `σ √Λ + δ` in each coordinate. -/
theorem step [DecidableEq ι] [Nonempty ι] {c a c₁ : ι → ℝ} {P P₁ : Matrix ι ι ℝ} {lam Λ δ : ℝ}
    (hPs : Pᵀ = P) (hlam : 0 < lam) (hPlam : ∀ u, lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ P *ᵥ u)
    (hPΛ : ∀ u, u ⬝ᵥ P *ᵥ u ≤ Λ * (u ⬝ᵥ u)) (ha : a ≠ 0) (hP₁s : P₁ᵀ = P₁)
    (hc₁ : ∀ i, |c₁ i - stepCenter c a P i| ≤ δ) (hP₁ : ∀ i j, |P₁ i j - stepShape a P i j| ≤ δ)
    (hδ₁ : Fintype.card ι * δ ≤ stepSize ι ^ 2 * lam / 8)
    (hδ₂ : Fintype.card ι * δ ^ 2 ≤ stepSize ι ^ 4 * lam / 128) :
    (∀ x, Mem c P x → a ⬝ᵥ (x - c) ≤ 0 → Mem c₁ P₁ x) ∧
      P₁.det ≤ (1 - 3 * stepSize ι / 4) * P.det ∧
      (∀ u, lam / 4 * (u ⬝ᵥ u) ≤ u ⬝ᵥ P₁ *ᵥ u) ∧ (∀ u, u ⬝ᵥ P₁ *ᵥ u ≤ 2 * Λ * (u ⬝ᵥ u)) ∧
      ∀ i, |c₁ i - c i| ≤ stepSize ι * Real.sqrt Λ + δ := by
  set σ := stepSize ι
  set n := Fintype.card ι
  set P' := stepShape a P
  set c' := stepCenter c a P
  have hσ : 0 < σ := stepSize_pos
  have hσ' : σ ≤ 1 / 4 := stepSize_le
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hc₁ (Classical.arbitrary ι))
  have hP0 : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u :=
    fun u ↦ (mul_nonneg hlam.le (dotProduct_self_nonneg' u)).trans (hPlam u)
  have ha0 : 0 < a ⬝ᵥ P *ᵥ a := by
    have : 0 < a ⬝ᵥ a := lt_of_le_of_ne (dotProduct_self_nonneg' a)
      (Ne.symm (mt dotProduct_self_eq_zero.1 ha))
    exact (mul_pos hlam this).trans_le (hPlam a)
  -- Bounds on the exact new shape `P'`.
  have hP'lo : ∀ u, (1 - 2 * σ) * (u ⬝ᵥ P *ᵥ u) ≤ u ⬝ᵥ P' *ᵥ u := by
    intro u
    have hcs : ((P *ᵥ a) ⬝ᵥ u) ^ 2 ≤ (u ⬝ᵥ P *ᵥ u) * (a ⬝ᵥ P *ᵥ a) := by
      rw [dotProduct_comm]
      exact sq_dotProduct_mulVec_le hPs hP0 u a
    have : 2 * σ / (a ⬝ᵥ P *ᵥ a) * ((P *ᵥ a) ⬝ᵥ u) ^ 2 ≤ 2 * σ * (u ⬝ᵥ P *ᵥ u) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ha0]
      nlinarith
    rw [quad_stepShape]
    have h12 : 0 ≤ (1 - 2 * σ) * (u ⬝ᵥ P *ᵥ u) := mul_nonneg (by linarith) (hP0 u)
    calc (1 - 2 * σ) * (u ⬝ᵥ P *ᵥ u) ≤ (1 + 4 * σ ^ 2) * ((1 - 2 * σ) * (u ⬝ᵥ P *ᵥ u)) :=
          le_mul_of_one_le_left h12 (by nlinarith)
      _ = (1 + 4 * σ ^ 2) * (u ⬝ᵥ P *ᵥ u - 2 * σ * (u ⬝ᵥ P *ᵥ u)) := by ring
      _ ≤ _ := by gcongr
  have hP'hi : ∀ u, u ⬝ᵥ P' *ᵥ u ≤ (1 + 4 * σ ^ 2) * (u ⬝ᵥ P *ᵥ u) := by
    intro u
    rw [quad_stepShape]
    have : 0 ≤ 2 * σ / (a ⬝ᵥ P *ᵥ a) * ((P *ᵥ a) ⬝ᵥ u) ^ 2 := by positivity
    nlinarith
  have hP'lam : ∀ u, lam / 2 * (u ⬝ᵥ u) ≤ u ⬝ᵥ P' *ᵥ u := by
    intro u
    nlinarith [hPlam u, hP'lo u, dotProduct_self_nonneg' u, hP0 u]
  -- The rounding errors.
  have hE : ∀ u, |u ⬝ᵥ (P₁ - P') *ᵥ u| ≤ δ * n * (u ⬝ᵥ u) := by
    intro u
    have h := abs_quad_le (u := u) (E := P₁ - P') (δ := δ) fun i j ↦ by
      simpa [Matrix.sub_apply] using hP₁ i j
    calc |u ⬝ᵥ (P₁ - P') *ᵥ u| ≤ δ * (∑ i, |u i|) ^ 2 := h
      _ ≤ δ * (n * (u ⬝ᵥ u)) := mul_le_mul_of_nonneg_left (sq_sum_abs_le u) hδ
      _ = δ * n * (u ⬝ᵥ u) := by ring
  have hsplit : ∀ u, u ⬝ᵥ P₁ *ᵥ u = u ⬝ᵥ P' *ᵥ u + u ⬝ᵥ (P₁ - P') *ᵥ u := by
    intro u
    rw [sub_mulVec, dotProduct_sub]
    ring
  have hsmall : ∀ u, δ * n * (u ⬝ᵥ u) ≤ σ ^ 2 / 4 * (u ⬝ᵥ P' *ᵥ u) := by
    intro u
    have h1 : δ * n ≤ σ ^ 2 * lam / 8 := by linarith
    calc δ * n * (u ⬝ᵥ u) ≤ σ ^ 2 * lam / 8 * (u ⬝ᵥ u) :=
          mul_le_mul_of_nonneg_right h1 (dotProduct_self_nonneg' u)
      _ = σ ^ 2 / 4 * (lam / 2 * (u ⬝ᵥ u)) := by ring
      _ ≤ σ ^ 2 / 4 * (u ⬝ᵥ P' *ᵥ u) := by gcongr; exact hP'lam u
  have hP₁lo : ∀ u, (1 - σ ^ 2 / 4) * (u ⬝ᵥ P' *ᵥ u) ≤ u ⬝ᵥ P₁ *ᵥ u := by
    intro u
    rw [hsplit]
    nlinarith [neg_abs_le (u ⬝ᵥ (P₁ - P') *ᵥ u), hE u, hsmall u]
  have hP₁hi : ∀ u, u ⬝ᵥ P₁ *ᵥ u ≤ (1 + σ ^ 2 / 4) * (u ⬝ᵥ P' *ᵥ u) := by
    intro u
    rw [hsplit]
    nlinarith [le_abs_self (u ⬝ᵥ (P₁ - P') *ᵥ u), hE u, hsmall u]
  have hcerr : ∀ u, (u ⬝ᵥ (c' - c₁)) ^ 2 ≤ (σ ^ 2) ^ 2 / 64 * (u ⬝ᵥ P' *ᵥ u) := by
    intro u
    have h1 : |u ⬝ᵥ (c' - c₁)| ≤ δ * ∑ i, |u i| := abs_dotProduct_le fun i ↦ by
      rw [Pi.sub_apply, abs_sub_comm]
      exact hc₁ i
    have h2 : (u ⬝ᵥ (c' - c₁)) ^ 2 ≤ δ ^ 2 * (n * (u ⬝ᵥ u)) := by
      rw [← sq_abs]
      calc |u ⬝ᵥ (c' - c₁)| ^ 2 ≤ (δ * ∑ i, |u i|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = δ ^ 2 * (∑ i, |u i|) ^ 2 := by ring
        _ ≤ δ ^ 2 * (n * (u ⬝ᵥ u)) := mul_le_mul_of_nonneg_left (sq_sum_abs_le u) (sq_nonneg δ)
    calc (u ⬝ᵥ (c' - c₁)) ^ 2 ≤ δ ^ 2 * (n * (u ⬝ᵥ u)) := h2
      _ = n * δ ^ 2 * (u ⬝ᵥ u) := by ring
      _ ≤ σ ^ 4 * lam / 128 * (u ⬝ᵥ u) :=
          mul_le_mul_of_nonneg_right hδ₂ (dotProduct_self_nonneg' u)
      _ = (σ ^ 2) ^ 2 / 64 * (lam / 2 * (u ⬝ᵥ u)) := by ring
      _ ≤ (σ ^ 2) ^ 2 / 64 * (u ⬝ᵥ P' *ᵥ u) := by gcongr; exact hP'lam u
  have hP₁lam : ∀ u, lam / 4 * (u ⬝ᵥ u) ≤ u ⬝ᵥ P₁ *ᵥ u := by
    intro u
    have h1 := hP₁lo u
    have h2 := hP'lam u
    have h3 : 1 / 2 ≤ 1 - σ ^ 2 / 4 := by nlinarith
    have h4 : 0 ≤ lam / 2 * (u ⬝ᵥ u) := mul_nonneg (by positivity) (dotProduct_self_nonneg' u)
    calc lam / 4 * (u ⬝ᵥ u) = 1 / 2 * (lam / 2 * (u ⬝ᵥ u)) := by ring
      _ ≤ (1 - σ ^ 2 / 4) * (lam / 2 * (u ⬝ᵥ u)) := mul_le_mul_of_nonneg_right h3 h4
      _ ≤ (1 - σ ^ 2 / 4) * (u ⬝ᵥ P' *ᵥ u) := mul_le_mul_of_nonneg_left h2 (by linarith)
      _ ≤ _ := h1
  refine ⟨fun x hx hcut u ↦ ?_, ?_, hP₁lam, fun u ↦ ?_, fun i ↦ ?_⟩
  · -- Containment: the exact step keeps `x` with slack, and the rounding uses up part of it.
    have h1 := mem_step hPs hP0 ha0 hx hcut u
    have heq : u ⬝ᵥ (x - c₁) = u ⬝ᵥ (x - c') + u ⬝ᵥ (c' - c₁) := by
      rw [← dotProduct_add]
      congr 1
      abel
    rw [heq]
    have h2 := perturb_scalar (sq_nonneg σ)
      ((mul_nonneg (by positivity) (dotProduct_self_nonneg' u)).trans (hP'lam u)) h1 (hcerr u)
    exact h2.trans (hP₁lo u)
  · -- Volume: `det P₁ ≤ det ((1 + σ²/4) P') = (1 + σ²/4)ⁿ (1 + 4σ²)ⁿ (1 - 2σ) det P`.
    have hP₁pd : P₁.PosDef := posDef_of_quad hP₁s fun u hu ↦ by
      have : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_nonneg' u)
        (Ne.symm (mt dotProduct_self_eq_zero.1 hu))
      nlinarith [hP₁lam u]
    have hsub : ((1 + σ ^ 2 / 4) • P' - P₁).PosSemidef := by
      refine posSemidef_of_quad ?_ fun u ↦ ?_
      · rw [transpose_sub, transpose_smul, stepShape_transpose hPs, hP₁s]
      · rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
        linarith [hP₁hi u]
    have hdet := det_le_det_of_posSemidef_sub hP₁pd hsub
    rw [det_smul, det_stepShape ha0.ne'] at hdet
    have hdetP : 0 ≤ P.det := (pow_nonneg hlam.le _).trans (pow_le_det hPs hlam hPlam)
    calc P₁.det ≤ (1 + σ ^ 2 / 4) ^ n * ((1 + 4 * σ ^ 2) ^ n * (1 - 2 * σ) * P.det) := hdet
      _ = (((1 + σ ^ 2 / 4) * (1 + 4 * σ ^ 2)) ^ n * (1 - 2 * σ)) * P.det := by
          rw [mul_pow]
          ring
      _ ≤ (1 - 3 * σ / 4) * P.det := mul_le_mul_of_nonneg_right volume_factor_le hdetP
  · -- The upper bound.
    have hσ2 : σ ^ 2 ≤ 1 / 16 := by nlinarith
    have h3 : (1 + σ ^ 2 / 4) * (1 + 4 * σ ^ 2) ≤ 2 := by
      nlinarith [mul_nonneg (sq_nonneg σ) (sub_nonneg.2 hσ2)]
    calc u ⬝ᵥ P₁ *ᵥ u ≤ (1 + σ ^ 2 / 4) * (u ⬝ᵥ P' *ᵥ u) := hP₁hi u
      _ ≤ (1 + σ ^ 2 / 4) * ((1 + 4 * σ ^ 2) * (u ⬝ᵥ P *ᵥ u)) := by gcongr; exact hP'hi u
      _ = (1 + σ ^ 2 / 4) * (1 + 4 * σ ^ 2) * (u ⬝ᵥ P *ᵥ u) := by ring
      _ ≤ 2 * (u ⬝ᵥ P *ᵥ u) := mul_le_mul_of_nonneg_right h3 (hP0 u)
      _ ≤ 2 * (Λ * (u ⬝ᵥ u)) := by gcongr; exact hPΛ u
      _ = 2 * Λ * (u ⬝ᵥ u) := by ring
  · -- The center moves by `σ |(P a)ᵢ| / √(aᵀ P a) + δ ≤ σ √Λ + δ`.
    set w := Real.sqrt (a ⬝ᵥ P *ᵥ a)
    have hw0 : 0 < w := Real.sqrt_pos.2 ha0
    have hΛ : 0 ≤ Λ := by
      have h := (hPlam a).trans (hPΛ a)
      have : 0 < a ⬝ᵥ a := lt_of_le_of_ne (dotProduct_self_nonneg' a)
        (Ne.symm (mt dotProduct_self_eq_zero.1 ha))
      nlinarith
    have hPa : |(P *ᵥ a) i| ≤ Real.sqrt Λ * w := by
      have hcs := sq_dotProduct_mulVec_le hPs hP0 (Pi.single i 1) a
      have e : Pi.single i (1 : ℝ) ⬝ᵥ P *ᵥ a = (P *ᵥ a) i := by simp
      rw [e] at hcs
      have hii : Pi.single i 1 ⬝ᵥ P *ᵥ Pi.single i (1 : ℝ) ≤ Λ := by
        simpa using hPΛ (Pi.single i 1)
      rw [← Real.sqrt_mul hΛ, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (hcs.trans (mul_le_mul_of_nonneg_right hii ha0.le))
    have hc'c : |c' i - c i| ≤ σ * Real.sqrt Λ := by
      have e : c' i - c i = -(σ / w * (P *ᵥ a) i) := by
        simp only [c', stepCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, σ, w]
        ring
      rw [e, abs_neg, abs_mul, abs_div, abs_of_pos hσ, abs_of_pos hw0, div_mul_eq_mul_div,
        div_le_iff₀ hw0]
      nlinarith [mul_le_mul_of_nonneg_left hPa hσ.le]
    calc |c₁ i - c i| = |(c₁ i - c' i) + (c' i - c i)| := by ring_nf
      _ ≤ |c₁ i - c' i| + |c' i - c i| := abs_add_le _ _
      _ ≤ δ + σ * Real.sqrt Λ := add_le_add (hc₁ i) hc'c
      _ = σ * Real.sqrt Λ + δ := add_comm _ _

/-- **A ball inside an ellipsoid bounds its determinant from below**: if `E(c, P)` contains the
ball of radius `r > 0` around `z`, then `det P ≥ (r²)ⁿ`. -/
theorem pow_le_det_of_ball [DecidableEq ι] {c z : ι → ℝ} {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    {r : ℝ} (hr : 0 < r) (h : ∀ x, (x - z) ⬝ᵥ (x - z) ≤ r ^ 2 → Mem c P x) :
    (r ^ 2) ^ Fintype.card ι ≤ P.det := by
  refine pow_le_det hPs (by positivity) fun u ↦ ?_
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hm : 0 < u ⬝ᵥ u := lt_of_le_of_ne (dotProduct_self_nonneg' u)
    (Ne.symm (mt dotProduct_self_eq_zero.1 hu))
  set t := r / Real.sqrt (u ⬝ᵥ u)
  have ht : t ^ 2 * (u ⬝ᵥ u) = r ^ 2 := by
    simp only [t, div_pow, Real.sq_sqrt hm.le]
    field_simp
  have hball : ∀ e : ℝ, e ^ 2 = 1 → ((z + (e * t) • u) - z) ⬝ᵥ ((z + (e * t) • u) - z) ≤ r ^ 2 :=
    fun e he ↦ by
      rw [add_sub_cancel_left, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
        ← ht]
      nlinarith
  have hp := h _ (hball 1 (by norm_num)) u
  have hn := h _ (hball (-1) (by norm_num)) u
  have e : ∀ e : ℝ, u ⬝ᵥ (z + (e * t) • u - c) = u ⬝ᵥ (z - c) + e * t * (u ⬝ᵥ u) := by
    intro e
    rw [show z + (e * t) • u - c = (z - c) + (e * t) • u by abel, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
  rw [e] at hp hn
  have : r ^ 2 * (u ⬝ᵥ u) = (t * (u ⬝ᵥ u)) ^ 2 := by rw [← ht]; ring
  rw [this]
  nlinarith

/-! ### Sizes of the step -/

theorem single_quad [DecidableEq ι] (P : Matrix ι ι ℝ) (i j : ι) :
    Pi.single i 1 ⬝ᵥ P *ᵥ Pi.single j 1 = P i j := by
  simp [mulVec, dotProduct, Pi.single_apply]

theorem single_dotProduct_mulVec [DecidableEq ι] (P : Matrix ι ι ℝ) (a : ι → ℝ) (i : ι) :
    Pi.single i 1 ⬝ᵥ P *ᵥ a = (P *ᵥ a) i := by
  simp [single_dotProduct]

/-- The entries of `P a` are at most `√(Λ aᵀPa)`. -/
theorem sq_mulVec_le {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    (hP0 : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) {Λ : ℝ} (hPΛ : ∀ u, u ⬝ᵥ P *ᵥ u ≤ Λ * (u ⬝ᵥ u)) (a : ι → ℝ)
    (i : ι) : (P *ᵥ a) i ^ 2 ≤ Λ * (a ⬝ᵥ P *ᵥ a) := by
  classical
  have h := sq_dotProduct_mulVec_le hPs hP0 (Pi.single i 1) a
  have hi := hPΛ (Pi.single i 1)
  rw [single_quad, single_dotProduct_mulVec] at h
  rw [single_quad] at hi
  simp only [single_dotProduct, Pi.single_eq_same, mul_one] at hi
  have hq := hP0 a
  calc (P *ᵥ a) i ^ 2 ≤ P i i * (a ⬝ᵥ P *ᵥ a) := h
    _ ≤ Λ * (a ⬝ᵥ P *ᵥ a) := mul_le_mul_of_nonneg_right hi hq

/-- The entries of a positive semidefinite `P` with `uᵀPu ≤ Λ uᵀu` are at most `Λ`. -/
theorem abs_entry_le {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    (hP0 : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) {Λ : ℝ} (hPΛ : ∀ u, u ⬝ᵥ P *ᵥ u ≤ Λ * (u ⬝ᵥ u)) (i j : ι) :
    |P i j| ≤ Λ := by
  classical
  have h := sq_dotProduct_mulVec_le hPs hP0 (Pi.single i 1) (Pi.single j 1)
  have hi := hPΛ (Pi.single i 1)
  have hj := hPΛ (Pi.single j 1)
  have hi0 := hP0 (Pi.single i 1)
  have hj0 := hP0 (Pi.single j 1)
  rw [single_quad, single_quad, single_quad] at h
  rw [single_quad] at hi hj hi0 hj0
  simp only [single_dotProduct, Pi.single_eq_same, mul_one] at hi hj
  have hΛ : 0 ≤ Λ := hi0.trans hi
  rw [← sq_le_sq₀ (abs_nonneg _) hΛ, sq_abs]
  nlinarith [mul_le_mul hi hj hj0 hΛ]

/-- **The center moves by at most `σ √Λ`.** -/
theorem abs_stepCenter_sub_le {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    (hP0 : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) {Λ : ℝ} (hPΛ : ∀ u, u ⬝ᵥ P *ᵥ u ≤ Λ * (u ⬝ᵥ u))
    {c a : ι → ℝ} (ha : 0 < a ⬝ᵥ P *ᵥ a) (i : ι) :
    |stepCenter c a P i - c i| ≤ stepSize ι * Real.sqrt Λ := by
  have hσ : 0 ≤ stepSize ι := by unfold stepSize; positivity
  have hsq := sq_mulVec_le hPs hP0 hPΛ a i
  have hΛ : 0 ≤ Λ := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [hPΛ a, dotProduct_self_nonneg' a]
  have hs : 0 < Real.sqrt (a ⬝ᵥ P *ᵥ a) := Real.sqrt_pos.2 ha
  have habs : |(P *ᵥ a) i| ≤ Real.sqrt Λ * Real.sqrt (a ⬝ᵥ P *ᵥ a) := by
    rw [← Real.sqrt_mul hΛ, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hsq
  simp only [stepCenter, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left, abs_neg,
    abs_mul, abs_div, abs_of_nonneg hσ, abs_of_pos hs]
  rw [div_mul_eq_mul_div, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hσ
  rw [div_le_iff₀ hs]
  exact habs

/-- **The new shape has entries at most `2Λ`.** -/
theorem abs_stepShape_le [Nonempty ι] {P : Matrix ι ι ℝ} (hPs : Pᵀ = P)
    (hP0 : ∀ u, 0 ≤ u ⬝ᵥ P *ᵥ u) {Λ : ℝ} (hPΛ : ∀ u, u ⬝ᵥ P *ᵥ u ≤ Λ * (u ⬝ᵥ u))
    {a : ι → ℝ} (ha : 0 < a ⬝ᵥ P *ᵥ a) (i j : ι) : |stepShape a P i j| ≤ 2 * Λ := by
  set σ := stepSize ι
  set q := a ⬝ᵥ P *ᵥ a
  have hσ : 0 < σ := stepSize_pos
  have hσ' : σ ≤ 1 / 4 := stepSize_le
  have hPij := abs_entry_le hPs hP0 hPΛ i j
  have hΛ : 0 ≤ Λ := (abs_nonneg _).trans hPij
  have hi := sq_mulVec_le hPs hP0 hPΛ a i
  have hj := sq_mulVec_le hPs hP0 hPΛ a j
  -- `|(Pa)ᵢ (Pa)ⱼ| ≤ Λ q`.
  have hprod : |(P *ᵥ a) i * (P *ᵥ a) j| ≤ Λ * q := by
    rw [abs_mul]
    nlinarith [abs_nonneg ((P *ᵥ a) i), abs_nonneg ((P *ᵥ a) j), sq_abs ((P *ᵥ a) i),
      sq_abs ((P *ᵥ a) j), sq_nonneg (|(P *ᵥ a) i| - |(P *ᵥ a) j|)]
  have hterm : |2 * σ / q * ((P *ᵥ a) i * (P *ᵥ a) j)| ≤ 2 * σ * Λ := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * σ / q), div_mul_eq_mul_div,
      div_le_iff₀ ha]
    nlinarith
  have hentry : stepShape a P i j =
      (1 + 4 * σ ^ 2) * (P i j - 2 * σ / q * ((P *ᵥ a) i * (P *ᵥ a) j)) := by
    simp [stepShape, vecMulVec_apply, σ, q]
  rw [hentry, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 + 4 * σ ^ 2)]
  have h1 : |P i j - 2 * σ / q * ((P *ᵥ a) i * (P *ᵥ a) j)| ≤ Λ + 2 * σ * Λ :=
    (abs_sub _ _).trans (add_le_add hPij hterm)
  calc (1 + 4 * σ ^ 2) * |P i j - 2 * σ / q * ((P *ᵥ a) i * (P *ᵥ a) j)|
      ≤ (1 + 4 * σ ^ 2) * (Λ + 2 * σ * Λ) := by gcongr
    _ = ((1 + 4 * σ ^ 2) * (1 + 2 * σ)) * Λ := by ring
    _ ≤ 2 * Λ := by
        have : (1 + 4 * σ ^ 2) * (1 + 2 * σ) ≤ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this hΛ

/-! ### The method -/

/-- **The ellipsoid method.** Run `K` rounded steps from `E(c 0, P 0)`, cutting by `a k` at the
center `c k`. Let `T k` be the points still to keep: they shrink, and each cut keeps them
(`aₖᵀ (x - cₖ) ≤ 0` for `x ∈ T (k+1)`). If the rounding error `δ` is small compared to the
smallest eigenvalue bound `λ / 4^K` the steps can reach, then every `T k` stays inside the
ellipsoid, and `det P K ≤ (1 - 3σ/4)^K det P 0`.

Each step's hypotheses may use the bounds at its start: `P k` is symmetric with eigenvalues in
`[λ / 4^k, 2^k Λ]`, and `c k` is within `k (√(2^K Λ) + δ)` of `c 0`. An implementation that
clamps its numbers uses them to show that the clamps never act. -/
theorem iterate [DecidableEq ι] [Nonempty ι] (K : ℕ) (c a : ℕ → ι → ℝ) (P : ℕ → Matrix ι ι ℝ)
    (T : ℕ → Set (ι → ℝ)) {lam Λ δ : ℝ} (hlam : 0 < lam) (h0s : (P 0)ᵀ = P 0)
    (h0lam : ∀ u, lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ P 0 *ᵥ u) (h0Λ : ∀ u, u ⬝ᵥ P 0 *ᵥ u ≤ Λ * (u ⬝ᵥ u))
    (h0T : ∀ x ∈ T 0, Mem (c 0) (P 0) x)
    (hstep : ∀ k < K, (P k)ᵀ = P k → (∀ u, lam / 4 ^ k * (u ⬝ᵥ u) ≤ u ⬝ᵥ P k *ᵥ u) →
      (∀ u, u ⬝ᵥ P k *ᵥ u ≤ 2 ^ k * Λ * (u ⬝ᵥ u)) →
      (∀ i, |c k i - c 0 i| ≤ k * (Real.sqrt (2 ^ K * Λ) + δ)) →
      a k ≠ 0 ∧ (P (k + 1))ᵀ = P (k + 1) ∧
      (∀ i, |c (k + 1) i - stepCenter (c k) (a k) (P k) i| ≤ δ) ∧
      (∀ i j, |P (k + 1) i j - stepShape (a k) (P k) i j| ≤ δ) ∧
      ∀ x ∈ T (k + 1), x ∈ T k ∧ a k ⬝ᵥ (x - c k) ≤ 0)
    (hδ₁ : Fintype.card ι * δ ≤ stepSize ι ^ 2 * (lam / 4 ^ K) / 8)
    (hδ₂ : Fintype.card ι * δ ^ 2 ≤ stepSize ι ^ 4 * (lam / 4 ^ K) / 128) :
    ∀ k ≤ K, (∀ x ∈ T k, Mem (c k) (P k) x) ∧
      (P k).det ≤ (1 - 3 * stepSize ι / 4) ^ k * (P 0).det ∧ (P k)ᵀ = P k ∧
      (∀ u, lam / 4 ^ k * (u ⬝ᵥ u) ≤ u ⬝ᵥ P k *ᵥ u) ∧
      (∀ u, u ⬝ᵥ P k *ᵥ u ≤ 2 ^ k * Λ * (u ⬝ᵥ u)) ∧
      ∀ i, |c k i - c 0 i| ≤ k * (Real.sqrt (2 ^ K * Λ) + δ) := by
  intro k
  induction k with
  | zero => intro _; simpa using ⟨h0T, h0s, h0lam, h0Λ⟩
  | succ k ih =>
    intro hk
    obtain ⟨hT, hdet, hs, hlo, hhi, hcen⟩ := ih (by omega)
    obtain ⟨ha, hs', hc, hP, hcut⟩ := hstep k (by omega) hs hlo hhi hcen
    have hlamk : 0 < lam / 4 ^ k := by positivity
    have h4 : lam / 4 ^ K ≤ lam / 4 ^ k :=
      div_le_div_of_nonneg_left hlam.le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
    have hσ := stepSize_pos (ι := ι)
    obtain ⟨hmem, hdet', hlo', hhi', hcen'⟩ := step hs hlamk hlo hhi ha hs' hc hP
      (hδ₁.trans (by gcongr)) (hδ₂.trans (by gcongr))
    refine ⟨fun x hx ↦ hmem x (hT x (hcut x hx).1) (hcut x hx).2, ?_, hs', fun u ↦ ?_,
      fun u ↦ ?_, fun i ↦ ?_⟩
    · have : 0 ≤ 1 - 3 * stepSize ι / 4 := by linarith [stepSize_le (ι := ι)]
      calc (P (k + 1)).det ≤ (1 - 3 * stepSize ι / 4) * (P k).det := hdet'
        _ ≤ (1 - 3 * stepSize ι / 4) * ((1 - 3 * stepSize ι / 4) ^ k * (P 0).det) := by gcongr
        _ = _ := by ring
    · have := hlo' u
      rw [pow_succ, ← div_div]
      linarith
    · have := hhi' u
      rw [pow_succ]
      linarith
    · have hΛ : 0 ≤ Λ := by
        have h := (h0lam (Pi.single (Classical.arbitrary ι) 1)).trans
          (h0Λ (Pi.single (Classical.arbitrary ι) 1))
        simp only [single_dotProduct, Pi.single_eq_same, one_mul] at h
        linarith
      have hΛk : Real.sqrt (2 ^ k * Λ) ≤ Real.sqrt (2 ^ K * Λ) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (by omega)) hΛ)
      have hσ1 : stepSize ι * Real.sqrt (2 ^ k * Λ) ≤ Real.sqrt (2 ^ K * Λ) := by
        have := stepSize_le (ι := ι)
        nlinarith [Real.sqrt_nonneg (2 ^ k * Λ)]
      calc |c (k + 1) i - c 0 i| = |(c (k + 1) i - c k i) + (c k i - c 0 i)| := by ring_nf
        _ ≤ |c (k + 1) i - c k i| + |c k i - c 0 i| := abs_add_le _ _
        _ ≤ (stepSize ι * Real.sqrt (2 ^ k * Λ) + δ) + k * (Real.sqrt (2 ^ K * Λ) + δ) :=
            add_le_add (hcen' i) (hcen i)
        _ ≤ (k + 1 : ℕ) * (Real.sqrt (2 ^ K * Λ) + δ) := by push_cast; linarith

/-! ### Minimizing a convex function -/

/-- The starting ellipsoid: the ball `xᵀx ≤ s` around `0` is `E(0, s I)`. -/
theorem mem_zero_smul_one [DecidableEq ι] {s : ℝ} {x : ι → ℝ} (hx : x ⬝ᵥ x ≤ s) :
    Mem 0 (s • (1 : Matrix ι ι ℝ)) x := by
  intro u
  have hcs : (u ⬝ᵥ x) ^ 2 ≤ (u ⬝ᵥ u) * (x ⬝ᵥ x) := by
    simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u x
  rw [sub_zero, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  nlinarith [dotProduct_self_nonneg' u]

/-- `6n` steps halve the determinant bound: `(1 - 3σ/4)^(6n) ≤ 1/2`. -/
theorem pow_six_mul_card_le [Nonempty ι] :
    (1 - 3 * stepSize ι / 4) ^ (6 * Fintype.card ι) ≤ 1 / 2 := by
  set x := 3 * stepSize ι / 4
  set m := 6 * Fintype.card ι
  have hσ := stepSize_pos (ι := ι)
  have hσ' := stepSize_le (ι := ι)
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by simp only [x]; linarith
  have hmx : 1 ≤ (m : ℝ) * x := by
    have := card_mul_stepSize (ι := ι)
    simp only [m, x]
    push_cast
    nlinarith
  have hb : 1 + m * x ≤ (1 + x) ^ m := one_add_mul_le_pow (by linarith) m
  have hprod : (1 - x) ^ m * (1 + x) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h0 : 0 ≤ (1 - x) ^ m := pow_nonneg (by linarith) m
  nlinarith

/-- **Minimizing with the ellipsoid method.** Run the method of `Ellipsoid.iterate` on a set `C`
and an objective `f`, with an oracle that declares each center feasible (`feas k`) or not. At a
center declared infeasible the cut `a k` keeps `C`; at one declared feasible it is an objective
cut, which keeps the points of `C` with smaller objective (for a convex `f`, a subgradient). If
`C` contains the ball of radius `r` around `z`, `f ≤ v` on that ball, and the determinant bound
has dropped below `(r²)ⁿ`, then some center declared feasible has objective at most `v`.

The oracle need not decide membership in `C` exactly: it may declare feasible the points of a
larger set, as long as its cuts keep `C`. As in `Ellipsoid.iterate`, each step's hypotheses may
use the bounds at its start. -/
theorem exists_feasible_le [DecidableEq ι] [Nonempty ι] (K : ℕ) (c a : ℕ → ι → ℝ)
    (P : ℕ → Matrix ι ι ℝ) (C : Set (ι → ℝ)) (feas : ℕ → Prop) (f : (ι → ℝ) → ℝ)
    {lam Λ δ r v : ℝ} {z : ι → ℝ}
    (hlam : 0 < lam) (h0s : (P 0)ᵀ = P 0) (h0lam : ∀ u, lam * (u ⬝ᵥ u) ≤ u ⬝ᵥ P 0 *ᵥ u)
    (h0Λ : ∀ u, u ⬝ᵥ P 0 *ᵥ u ≤ Λ * (u ⬝ᵥ u)) (h0C : ∀ x ∈ C, Mem (c 0) (P 0) x)
    (hstep : ∀ k < K, (P k)ᵀ = P k → (∀ u, lam / 4 ^ k * (u ⬝ᵥ u) ≤ u ⬝ᵥ P k *ᵥ u) →
      (∀ u, u ⬝ᵥ P k *ᵥ u ≤ 2 ^ k * Λ * (u ⬝ᵥ u)) →
      (∀ i, |c k i - c 0 i| ≤ k * (Real.sqrt (2 ^ K * Λ) + δ)) →
      a k ≠ 0 ∧ (P (k + 1))ᵀ = P (k + 1) ∧
      (∀ i, |c (k + 1) i - stepCenter (c k) (a k) (P k) i| ≤ δ) ∧
      (∀ i j, |P (k + 1) i j - stepShape (a k) (P k) i j| ≤ δ) ∧
      (¬ feas k → ∀ x ∈ C, a k ⬝ᵥ (x - c k) ≤ 0) ∧
      (feas k → ∀ x ∈ C, f x < f (c k) → a k ⬝ᵥ (x - c k) ≤ 0))
    (hδ₁ : Fintype.card ι * δ ≤ stepSize ι ^ 2 * (lam / 4 ^ K) / 8)
    (hδ₂ : Fintype.card ι * δ ^ 2 ≤ stepSize ι ^ 4 * (lam / 4 ^ K) / 128) (hr : 0 < r)
    (hball : ∀ x, (x - z) ⬝ᵥ (x - z) ≤ r ^ 2 → x ∈ C ∧ f x ≤ v)
    (hK : (1 - 3 * stepSize ι / 4) ^ K * (P 0).det < (r ^ 2) ^ Fintype.card ι) :
    ∃ k < K, feas k ∧ f (c k) ≤ v := by
  by_contra hne
  push Not at hne
  -- The points still to keep: in `C`, and better than every feasible center so far.
  let T : ℕ → Set (ι → ℝ) := fun k ↦ {x | x ∈ C ∧ ∀ j < k, feas j → f x < f (c j)}
  have hT0 : ∀ x ∈ T 0, Mem (c 0) (P 0) x := fun x hx ↦ h0C x hx.1
  have hstep' : ∀ k < K, (P k)ᵀ = P k → (∀ u, lam / 4 ^ k * (u ⬝ᵥ u) ≤ u ⬝ᵥ P k *ᵥ u) →
      (∀ u, u ⬝ᵥ P k *ᵥ u ≤ 2 ^ k * Λ * (u ⬝ᵥ u)) →
      (∀ i, |c k i - c 0 i| ≤ k * (Real.sqrt (2 ^ K * Λ) + δ)) →
      a k ≠ 0 ∧ (P (k + 1))ᵀ = P (k + 1) ∧
      (∀ i, |c (k + 1) i - stepCenter (c k) (a k) (P k) i| ≤ δ) ∧
      (∀ i j, |P (k + 1) i j - stepShape (a k) (P k) i j| ≤ δ) ∧
      ∀ x ∈ T (k + 1), x ∈ T k ∧ a k ⬝ᵥ (x - c k) ≤ 0 := by
    intro k hk hsk hlo hhi hcen
    obtain ⟨ha, hs, hc, hP, hsep, hobj⟩ := hstep k hk hsk hlo hhi hcen
    refine ⟨ha, hs, hc, hP, fun x hx ↦ ⟨⟨hx.1, fun j hj ↦ hx.2 j (by omega)⟩, ?_⟩⟩
    by_cases hck : feas k
    · exact hobj hck x hx.1 (hx.2 k (by omega) hck)
    · exact hsep hck x hx.1
  obtain ⟨hmem, hdet, hs, -, -, -⟩ :=
    iterate K c a P T hlam h0s h0lam h0Λ hT0 hstep' hδ₁ hδ₂ K le_rfl
  -- The ball stays among the points to keep, so the last ellipsoid contains it.
  have hin : ∀ x, (x - z) ⬝ᵥ (x - z) ≤ r ^ 2 → Mem (c K) (P K) x := by
    intro x hx
    obtain ⟨hxC, hfx⟩ := hball x hx
    exact hmem x ⟨hxC, fun j hj hcj ↦ hfx.trans_lt (hne j hj hcj)⟩
  have := pow_le_det_of_ball hs hr hin
  linarith

end Ellipsoid
