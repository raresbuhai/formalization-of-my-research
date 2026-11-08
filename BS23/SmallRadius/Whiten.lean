module

public import BS23.SmallRadius.Frame
public import BS23.SmallRadius.GoodProb
public import BS23.Separating.Setup

/-!
# The whitening of the small-radius algorithm, and the standard frame of a sample

Steps 2–4 of the algorithm of [BS23, Theorem 1.3] (with its moment constraint in two degrees), as
computable functions of the rational points `Y₁, …, Yₙ ∈ ℚ^d`:

* the uncentered second moment `Ĉ₀ = (1/n) ∑ⱼ Yⱼ Yⱼᵀ` (`BS23.SmallRadius.secondMoment`);
* the whitening matrix `A` (`BS23.SmallRadius.whitenMat`) whose row `i` is `2^{eᵢ} λᵢ`
  (`BS23.SmallRadius.whitenRow`), with `λᵢ = BS23.Colinear.basisVec Ĉ₀ i` the `Ĉ₀`-orthogonal
  basis and `eᵢ = -⌊log₄ (λᵢᵀĈ₀λᵢ)⌋` (`BS23.SmallRadius.whitenExp`), so that
  `κᵢ = 4^{eᵢ} λᵢᵀĈ₀λᵢ ∈ [1, 4)` (`BS23.SmallRadius.whitenKappa`,
  `BS23.SmallRadius.one_le_whitenKappa`, `BS23.SmallRadius.whitenKappa_lt_four`) and
  `A Ĉ₀ Aᵀ = diag κ` (`BS23.SmallRadius.whitenMat_mul_mul_transpose`);
* the re-rounded data `z_{ja} = ⌊2^p · clamp_{[-n², n²]} ((A Yⱼ)_a)⌋ / 2^p`
  (`BS23.SmallRadius.whitenData`, with `BS23.SmallRadius.reRound`);
* the data part of the guard: all leading principal minors of `Ĉ₀` are positive
  (`BS23.SmallRadius.LeadMinorsPos`).

**The standard frame of a sample** (`BS23.SmallRadius.modelFrame`). For a sample `ω` of a mixture
`M` with `Σ = M.S ≻ 0`, rounded by `r`, the algorithm's data are an invertible image of standard
points: with `Σ^{1/2} = CFC.sqrt Σ`, `G = A Σ^{1/2}` (`BS23.SmallRadius.Gmat`), the standardized
means `m_c = Σ^{-1/2} μ_c` (`BS23.SmallRadius.stdMean`), the standardized noises
`gⱼ = BS23.stdNoise M ω j` and the errors `eⱼ = Σ^{-1/2} (ỹⱼ - yⱼ) + G⁻¹ ρⱼ`, where
`ρⱼ = zⱼ - A ỹⱼ` is the re-rounding error (`BS23.SmallRadius.regridErr`), the data are
`zⱼ = G (m_{ℓⱼ} + gⱼ + eⱼ)`.

**`BS23.SmallRadius.frame_of_model`.** For a valid mixture with weights at least `w`, radius
`sqNormIn Σ μ_c ≤ R²`, separation `Csep ln (1/w) ≤ sqNormIn Σ (μ_a - μ_b)`, the parameter facts
`BS23.SmallRadius.SRParams`, a rounding within `1/n`, and a sample in the graded good event
`BS23.SmallRadius.GoodGraded`, the leading principal minors of `Ĉ₀` are positive and the frame is
good (`BS23.SmallRadius.SRFrame.Good`) at the grid precision `p = gridPrec R n d`. The proof
(for real `v`, with `b = Σ^{1/2} v`, so `vᵀΣv = ‖b‖²`):

1. `vᵀĈ₀v = (1/n) ∑ⱼ ⟨ζ⁰ⱼ, b⟩²` with `ζ⁰ⱼ = m_{ℓⱼ} + gⱼ + Σ^{-1/2}(ỹⱼ - yⱼ)`
   (`BS23.SmallRadius.quad_secondMoment_yt`). By `(x + y + u)² ≤ 3 (x² + y² + u²)` and the
   degree-`2` good event, `vᵀĈ₀v ≤ 3 (R² + 1 + k δ + 1/n²) ‖b‖²`
   (`BS23.SmallRadius.sum_sq_dotProduct_le`), with `δ = τ₂ (d+1)²` and `k δ ≤ 1/64`.
2. By `(x + u)² ≥ x²/2 - u²`, dropping the squared means, and the first and second moments of
   the degree-`2` good event, `vᵀĈ₀v ≥ (½ (1 - k δ (1 + 2|R|)) - 1/n²) ‖b‖²`
   (`BS23.SmallRadius.le_sum_sq_dotProduct`), and `k δ (1 + 2|R|) ≤ 1/64`
   (`BS23.SmallRadius.k_mul_δ_le`). So `Σ / 5 ⪯ Ĉ₀ ⪯ 3 (R² + 2) Σ`
   (`BS23.SmallRadius.quad_bounds`), and `Ĉ₀ ≻ 0`.
3. `A Ĉ₀ Aᵀ = diag κ` with `κᵢ ∈ [1, 4)` gives `‖Gᵀv‖² = (Aᵀv)ᵀΣ(Aᵀv) ≤ 5 vᵀ diag(κ) v ≤ 20 ‖v‖²`
   and `‖v‖² ≤ vᵀ diag(κ) v ≤ 3 (R² + 2) ‖Gᵀv‖²`.
4. The unrounded frame (data `A ỹⱼ`, errors `Σ^{-1/2}(ỹⱼ - yⱼ)`,
   `BS23.SmallRadius.modelFrame₀`) is good (`BS23.SmallRadius.modelFrame₀_good`), so
   `|(A ỹⱼ)_a| ≤ n²` (`BS23.SmallRadius.SRFrame.Good.abs_z_le`): the clamp does nothing, and the
   grid error is `|ρ_{ja}| ≤ 2^{-p}`, so `‖G⁻¹ρⱼ‖² ≤ 3 (R² + 2) d 4^{-p} ≤ 1/n²` and
   `‖eⱼ‖² ≤ 2 (1/n² + 1/n²) = 4/n²` (`BS23.SmallRadius.modelFrame_good`).
5. `‖Σ^{-1/2} x‖² = sqNormIn Σ x` gives the radius and separation fields.
-/

@[expose] public section

namespace BS23.SmallRadius

open Matrix Finset Colinear
open scoped MatrixOrder

variable {n d k : ℕ}

/-! ### The whitening of the algorithm -/

/-- The **uncentered second moment** `Ĉ₀ = (1/n) ∑ⱼ Yⱼ Yⱼᵀ`. -/
def secondMoment {K : Type*} [Field K] (Y : Fin n → Fin d → K) : Matrix (Fin d) (Fin d) K :=
  fun a b ↦ (∑ j, Y j a * Y j b) / n

/-- The exponent `eᵢ = -⌊log₄ (λᵢᵀCλᵢ)⌋` of the `i`-th whitening row. -/
def whitenExp (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) : ℤ :=
  -Int.log 4 (quad C (basisVec C i))

/-- The `i`-th **whitening row** `2^{eᵢ} λᵢ`. -/
def whitenRow (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) : Fin d → ℚ :=
  (2 : ℚ) ^ whitenExp C i • basisVec C i

/-- The **whitening matrix** `A`, with rows `BS23.SmallRadius.whitenRow C i`. -/
def whitenMat (C : Matrix (Fin d) (Fin d) ℚ) : Matrix (Fin d) (Fin d) ℚ :=
  Matrix.of (whitenRow C)

/-- The `i`-th diagonal entry `κᵢ = 4^{eᵢ} λᵢᵀCλᵢ` of `A C Aᵀ` (analysis only). -/
def whitenKappa (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) : ℚ :=
  4 ^ whitenExp C i * quad C (basisVec C i)

/-- `x` clamped to `[-B, B]`. -/
def clampAbs (B x : ℚ) : ℚ := max (-B) (min B x)

/-- `x` clamped to `[-B, B]`, then rounded down to a multiple of `2^{-p}`. -/
def reRound (p : ℕ) (B x : ℚ) : ℚ := (⌊(2 : ℚ) ^ p * clampAbs B x⌋ : ℚ) / 2 ^ p

/-- The **whitened, re-rounded data** `z_{ja} = ⌊2^p clamp_{[-n², n²]} ((A Yⱼ)_a)⌋ / 2^p`, with
`A` the whitening matrix of the second moment of the points. -/
def whitenData (p : ℕ) (Y : Fin n → Fin d → ℚ) : Fin n → Fin d → ℚ :=
  fun j a ↦ reRound p ((n : ℚ) ^ 2) ((whitenMat (secondMoment Y) *ᵥ Y j) a)

/-- The **data part of the guard**: all leading principal minors of `C` are positive. -/
def LeadMinorsPos (C : Matrix (Fin d) (Fin d) ℚ) : Prop := ∀ i, 0 < (lead C i).det

instance (C : Matrix (Fin d) (Fin d) ℚ) : Decidable (LeadMinorsPos C) :=
  inferInstanceAs (Decidable (∀ i, 0 < (lead C i).det))

/-! ### Facts about the whitening -/

section Generic

variable {K : Type*} [Field K]

theorem secondMoment_apply (Y : Fin n → Fin d → K) (a b : Fin d) :
    secondMoment Y a b = (∑ j, Y j a * Y j b) / n :=
  rfl

theorem secondMoment_transpose (Y : Fin n → Fin d → K) : (secondMoment Y)ᵀ = secondMoment Y := by
  ext a b
  rw [transpose_apply, secondMoment_apply, secondMoment_apply]
  congr 1
  exact sum_congr rfl fun j _ ↦ mul_comm _ _

/-- `C₀ v = (1/n) ∑ⱼ ⟨Yⱼ, v⟩ Yⱼ`, coordinatewise. -/
theorem secondMoment_mulVec (Y : Fin n → Fin d → K) (v : Fin d → K) (a : Fin d) :
    (secondMoment Y *ᵥ v) a = (∑ j, Y j a * (Y j ⬝ᵥ v)) / n := by
  simp only [mulVec, dotProduct, secondMoment_apply, sum_div, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun b _ ↦ ?_
  ring

/-- `vᵀ C₀ v = (1/n) ∑ⱼ ⟨Yⱼ, v⟩²`. -/
theorem quad_secondMoment (Y : Fin n → Fin d → K) (v : Fin d → K) :
    quad (secondMoment Y) v = (∑ j, (Y j ⬝ᵥ v) ^ 2) / n := by
  rw [quad, dotProduct]
  simp only [secondMoment_mulVec, mul_div_assoc', ← sum_div, mul_sum]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sq, dotProduct, sum_mul]
  exact sum_congr rfl fun a _ ↦ by ring

end Generic

theorem secondMoment_cast (Y : Fin n → Fin d → ℚ) :
    secondMoment (fun j a ↦ (Y j a : ℝ)) = (secondMoment Y).map ((↑) : ℚ → ℝ) := by
  ext a b
  simp [secondMoment_apply]

/-- `κᵢ ≥ 1` when `λᵢᵀCλᵢ > 0`. -/
theorem one_le_whitenKappa {C : Matrix (Fin d) (Fin d) ℚ} {i : Fin d}
    (hq : 0 < quad C (basisVec C i)) : 1 ≤ whitenKappa C i := by
  have h := Int.zpow_log_le_self (R := ℚ) (b := 4) (by norm_num) hq
  push_cast at h
  rw [whitenKappa, whitenExp, _root_.zpow_neg, ← div_eq_inv_mul,
    le_div_iff₀ (zpow_pos (by norm_num) _), one_mul]
  exact h

/-- `κᵢ < 4`. -/
theorem whitenKappa_lt_four (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) : whitenKappa C i < 4 := by
  have h := Int.lt_zpow_succ_log_self (R := ℚ) (b := 4) (by norm_num) (quad C (basisVec C i))
  push_cast at h
  rw [whitenKappa, whitenExp, _root_.zpow_neg, ← div_eq_inv_mul,
    div_lt_iff₀ (zpow_pos (by norm_num) _)]
  rwa [zpow_add_one₀ (by norm_num), mul_comm] at h

/-- The rows of the whitening matrix, over the reals. -/
theorem whitenMat_map_apply (C : Matrix (Fin d) (Fin d) ℚ) (i : Fin d) :
    (whitenMat C).map ((↑) : ℚ → ℝ) i =
      (2 : ℝ) ^ whitenExp C i • basisVec (C.map ((↑) : ℚ → ℝ)) i := by
  funext l
  simp [whitenMat, whitenRow, basisVec_cast]

/-- **Whitening**: `A C Aᵀ = diag κ` for a symmetric `C`. -/
theorem whitenMat_mul_mul_transpose {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ))ᵀ = C.map ((↑) : ℚ → ℝ)) :
    (whitenMat C).map ((↑) : ℚ → ℝ) * C.map ((↑) : ℚ → ℝ) * ((whitenMat C).map ((↑) : ℚ → ℝ))ᵀ =
      diagonal fun i ↦ ((whitenKappa C i : ℚ) : ℝ) := by
  ext a b
  rw [Separating.mul_mul_transpose_apply, whitenMat_map_apply, whitenMat_map_apply, mulVec_smul,
    smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  by_cases hab : a = b
  · subst hab
    rw [diagonal_apply_eq, ← quad, basisVec_cast, quad_cast, whitenKappa, Rat.cast_mul,
      Rat.cast_zpow, ← mul_assoc, ← mul_zpow]
    norm_num
  · rw [diagonal_apply_ne _ hab, basisVec_orth hC hab, mul_zero, mul_zero]

/-- `(Aᵀv)ᵀ C (Aᵀv) = ∑ᵢ κᵢ vᵢ²` for a symmetric `C`. -/
theorem quad_whitenMat_transpose {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ))ᵀ = C.map ((↑) : ℚ → ℝ)) (v : Fin d → ℝ) :
    quad (C.map ((↑) : ℚ → ℝ)) (((whitenMat C).map ((↑) : ℚ → ℝ))ᵀ *ᵥ v) =
      ∑ i, ((whitenKappa C i : ℚ) : ℝ) * v i ^ 2 := by
  rw [Separating.quad_transpose_mulVec, whitenMat_mul_mul_transpose hC, quad,
    Separating.dotProduct_diagonal_mulVec]

theorem one_le_whitenKappa_cast {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ)).PosDef) (i : Fin d) : (1 : ℝ) ≤ ((whitenKappa C i : ℚ) : ℝ) := by
  have h := quad_basisVec_pos hC i
  rw [basisVec_cast, quad_cast] at h
  have hq : 0 < quad C (basisVec C i) := by exact_mod_cast h
  exact_mod_cast one_le_whitenKappa hq

theorem dotProduct_self_eq_sum_sq (u : Fin d → ℝ) : u ⬝ᵥ u = ∑ i, u i ^ 2 := by
  simp [dotProduct, sq]

/-- `‖v‖² ≤ (Aᵀv)ᵀ C (Aᵀv) ≤ 4 ‖v‖²` for a positive definite `C`. -/
theorem quad_whitenMat_transpose_bounds {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ)).PosDef) (v : Fin d → ℝ) :
    v ⬝ᵥ v ≤ quad (C.map ((↑) : ℚ → ℝ)) (((whitenMat C).map ((↑) : ℚ → ℝ))ᵀ *ᵥ v) ∧
      quad (C.map ((↑) : ℚ → ℝ)) (((whitenMat C).map ((↑) : ℚ → ℝ))ᵀ *ᵥ v) ≤ 4 * (v ⬝ᵥ v) := by
  rw [quad_whitenMat_transpose (transpose_eq_of_posDef hC), dotProduct_self_eq_sum_sq, mul_sum]
  refine ⟨sum_le_sum fun i _ ↦ ?_, sum_le_sum fun i _ ↦ ?_⟩
  · have := one_le_whitenKappa_cast hC i
    nlinarith [sq_nonneg (v i)]
  · have : ((whitenKappa C i : ℚ) : ℝ) ≤ 4 := by exact_mod_cast (whitenKappa_lt_four C i).le
    nlinarith [sq_nonneg (v i)]

/-- `det(A)² det C = ∏ᵢ κᵢ` for a symmetric `C`. -/
theorem det_whitenMat_sq_mul_det {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ))ᵀ = C.map ((↑) : ℚ → ℝ)) :
    ((whitenMat C).map ((↑) : ℚ → ℝ)).det ^ 2 * (C.map ((↑) : ℚ → ℝ)).det =
      ∏ i, ((whitenKappa C i : ℚ) : ℝ) := by
  rw [← det_diagonal, ← whitenMat_mul_mul_transpose hC, det_mul, det_mul, det_transpose]
  ring

/-- **The whitening matrix is invertible** for a positive definite `C`. -/
theorem det_whitenMat_ne_zero {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ)).PosDef) : ((whitenMat C).map ((↑) : ℚ → ℝ)).det ≠ 0 := by
  intro h
  have h' := det_whitenMat_sq_mul_det (transpose_eq_of_posDef hC)
  rw [h] at h'
  have hpos : 0 < ∏ i, ((whitenKappa C i : ℚ) : ℝ) :=
    prod_pos fun i _ ↦ lt_of_lt_of_le one_pos (one_le_whitenKappa_cast hC i)
  simp at h'
  linarith

/-- The leading principal minors of `C` are positive if `C` is positive definite over `ℝ`. -/
theorem leadMinorsPos_of_posDef {C : Matrix (Fin d) (Fin d) ℚ}
    (hC : (C.map ((↑) : ℚ → ℝ)).PosDef) : LeadMinorsPos C := by
  intro i
  have h := det_lead_pos hC i
  have e : (((lead C i).det : ℚ) : ℝ) = ((lead C i).map ((↑) : ℚ → ℝ)).det :=
    (Rat.castHom ℝ).map_det (lead C i)
  rw [lead_cast, ← e] at h
  exact_mod_cast h

/-! ### Re-rounding -/

theorem clampAbs_of_abs_le {B x : ℚ} (h : |x| ≤ B) : clampAbs B x = x := by
  rw [clampAbs, min_eq_right (le_of_abs_le h), max_eq_right (neg_le_of_abs_le h)]

/-- Without clamping, re-rounding moves a number by at most `2^{-p}`. -/
theorem abs_reRound_sub_le (p : ℕ) {B x : ℚ} (h : |x| ≤ B) : |reRound p B x - x| ≤ 1 / 2 ^ p := by
  rw [reRound, clampAbs_of_abs_le h]
  have h2 : (0 : ℚ) < 2 ^ p := by positivity
  have hf1 := Int.floor_le ((2 : ℚ) ^ p * x)
  have hf2 := Int.lt_floor_add_one ((2 : ℚ) ^ p * x)
  have e : (⌊(2 : ℚ) ^ p * x⌋ : ℚ) / 2 ^ p - x = ((⌊(2 : ℚ) ^ p * x⌋ : ℚ) - 2 ^ p * x) / 2 ^ p := by
    rw [sub_div, mul_div_cancel_left₀ _ h2.ne']
  rw [e, abs_div, abs_of_pos h2]
  refine div_le_div_of_nonneg_right ?_ h2.le
  rw [abs_le]
  constructor <;> linarith

/-! ### Two facts about dot products -/

/-- `‖u + v‖² ≤ 2 (‖u‖² + ‖v‖²)`. -/
theorem dotProduct_add_le_two (u v : Fin d → ℝ) :
    (u + v) ⬝ᵥ (u + v) ≤ 2 * (u ⬝ᵥ u + v ⬝ᵥ v) := by
  simp only [dotProduct, Pi.add_apply, ← sum_add_distrib, mul_sum]
  refine sum_le_sum fun i _ ↦ ?_
  nlinarith [sq_nonneg (u i - v i)]

theorem sum_card_cluster (ℓ : Fin n → Fin k) : ∑ c, ((cluster ℓ c).card : ℝ) = n := by
  have := SRFrame.Good.sum_cluster_eq ℓ (fun _ ↦ (1 : ℝ))
  simpa using this

/-! ### The second moment of a perturbed sample: the deterministic bounds -/

/-- **Upper bound.** For points `ζⱼ = m_{ℓⱼ} + gⱼ + eⱼ` with `‖m_c‖² ≤ R²`, `‖eⱼ‖² ≤ 1/n²` and the
second moments of `⟨gⱼ, b⟩` within `δ ‖b‖²` of the Gaussian ones in every cluster:
`(1/n) ∑ⱼ ⟨ζⱼ, b⟩² ≤ 3 (R² + 1 + k δ + 1/n²) ‖b‖²`. -/
theorem sum_sq_dotProduct_le (hn : 0 < n) {ℓ : Fin n → Fin k} {m : Fin k → Fin d → ℝ}
    {g e : Fin n → Fin d → ℝ} {R δ : ℝ} (hm : ∀ c, m c ⬝ᵥ m c ≤ R ^ 2)
    (he : ∀ j, e j ⬝ᵥ e j ≤ 1 / (n : ℝ) ^ 2) (b : Fin d → ℝ)
    (h2 : ∀ c, |(∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) / n -
      ((cluster ℓ c).card : ℝ) / n * (b ⬝ᵥ b)| ≤ δ * (b ⬝ᵥ b)) :
    (∑ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2) / n ≤
      3 * (R ^ 2 + 1 + k * δ + 1 / (n : ℝ) ^ 2) * (b ⬝ᵥ b) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  set B := b ⬝ᵥ b with hB
  have hB0 : 0 ≤ B := dotProduct_self_nonneg' b
  have hx : ∀ c, (m c ⬝ᵥ b) ^ 2 ≤ R ^ 2 * B := fun c ↦
    (dotProduct_sq_le _ _).trans (mul_le_mul_of_nonneg_right (hm c) hB0)
  have hε : ∀ j, (e j ⬝ᵥ b) ^ 2 ≤ 1 / (n : ℝ) ^ 2 * B := fun j ↦
    (dotProduct_sq_le _ _).trans (mul_le_mul_of_nonneg_right (he j) hB0)
  have hy : ∀ c, ∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2 ≤ (cluster ℓ c).card * B + n * (δ * B) := by
    intro c
    have h := (abs_le.1 (h2 c)).2
    have e1 : (∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) / n - ((cluster ℓ c).card : ℝ) / n * B =
        ((∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) - (cluster ℓ c).card * B) / n := by ring
    rw [e1, div_le_iff₀ hN] at h
    linarith
  have hysum : ∑ j, (g j ⬝ᵥ b) ^ 2 ≤ n * B + k * (n * (δ * B)) := by
    rw [← SRFrame.Good.sum_cluster_eq ℓ]
    calc ∑ c, ∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2
        ≤ ∑ c, (((cluster ℓ c).card : ℝ) * B + n * (δ * B)) := sum_le_sum fun c _ ↦ hy c
      _ = n * B + k * (n * (δ * B)) := by
        rw [sum_add_distrib, ← sum_mul, sum_card_cluster]
        simp
  have hxsum : ∑ j, (m (ℓ j) ⬝ᵥ b) ^ 2 ≤ n * (R ^ 2 * B) :=
    (sum_le_sum fun j _ ↦ hx (ℓ j)).trans_eq (by simp)
  have hεsum : ∑ j, (e j ⬝ᵥ b) ^ 2 ≤ n * (1 / (n : ℝ) ^ 2 * B) :=
    (sum_le_sum fun j _ ↦ hε j).trans_eq (by simp)
  have hpt : ∀ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2 ≤
      3 * ((m (ℓ j) ⬝ᵥ b) ^ 2 + (g j ⬝ᵥ b) ^ 2 + (e j ⬝ᵥ b) ^ 2) := by
    intro j
    rw [add_dotProduct, add_dotProduct]
    nlinarith [sq_nonneg (m (ℓ j) ⬝ᵥ b - g j ⬝ᵥ b), sq_nonneg (g j ⬝ᵥ b - e j ⬝ᵥ b),
      sq_nonneg (m (ℓ j) ⬝ᵥ b - e j ⬝ᵥ b)]
  have htot : ∑ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2 ≤
      3 * (n * (R ^ 2 * B) + (n * B + k * (n * (δ * B))) + n * (1 / (n : ℝ) ^ 2 * B)) := by
    calc ∑ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2
        ≤ ∑ j, 3 * ((m (ℓ j) ⬝ᵥ b) ^ 2 + (g j ⬝ᵥ b) ^ 2 + (e j ⬝ᵥ b) ^ 2) :=
          sum_le_sum fun j _ ↦ hpt j
      _ = 3 * (∑ j, (m (ℓ j) ⬝ᵥ b) ^ 2 + ∑ j, (g j ⬝ᵥ b) ^ 2 + ∑ j, (e j ⬝ᵥ b) ^ 2) := by
          rw [← mul_sum, sum_add_distrib, sum_add_distrib]
      _ ≤ _ := by linarith
  rw [div_le_iff₀ hN]
  calc ∑ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2
      ≤ 3 * (n * (R ^ 2 * B) + (n * B + k * (n * (δ * B))) + n * (1 / (n : ℝ) ^ 2 * B)) := htot
    _ = 3 * (R ^ 2 + 1 + k * δ + 1 / (n : ℝ) ^ 2) * B * n := by ring

/-- **Lower bound.** For points `ζⱼ = m_{ℓⱼ} + gⱼ + eⱼ` with `‖m_c‖² ≤ R²`, `‖eⱼ‖² ≤ 1/n²`, and
the first and second moments of `⟨gⱼ, b⟩` within `δ ‖b‖` and `δ ‖b‖²` of the Gaussian ones in
every cluster: `(1/n) ∑ⱼ ⟨ζⱼ, b⟩² ≥ (½ (1 - k δ (1 + 2|R|)) - 1/n²) ‖b‖²`. -/
theorem le_sum_sq_dotProduct (hn : 0 < n) {ℓ : Fin n → Fin k} {m : Fin k → Fin d → ℝ}
    {g e : Fin n → Fin d → ℝ} {R δ : ℝ} (hm : ∀ c, m c ⬝ᵥ m c ≤ R ^ 2)
    (he : ∀ j, e j ⬝ᵥ e j ≤ 1 / (n : ℝ) ^ 2) (b : Fin d → ℝ)
    (h1 : ∀ c, |(∑ j ∈ cluster ℓ c, g j ⬝ᵥ b) / n| ≤ δ * Real.sqrt (b ⬝ᵥ b))
    (h2 : ∀ c, |(∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) / n -
      ((cluster ℓ c).card : ℝ) / n * (b ⬝ᵥ b)| ≤ δ * (b ⬝ᵥ b)) :
    (1 / 2 * (1 - k * δ * (1 + 2 * |R|)) - 1 / (n : ℝ) ^ 2) * (b ⬝ᵥ b) ≤
      (∑ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2) / n := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  set B := b ⬝ᵥ b with hB
  have hB0 : 0 ≤ B := dotProduct_self_nonneg' b
  set sB := Real.sqrt B with hsB
  have hsB0 : 0 ≤ sB := Real.sqrt_nonneg _
  have hsB2 : sB ^ 2 = B := Real.sq_sqrt hB0
  have hx : ∀ c, |m c ⬝ᵥ b| ≤ |R| * sB := fun c ↦ by
    have h : (m c ⬝ᵥ b) ^ 2 ≤ (|R| * sB) ^ 2 := by
      rw [mul_pow, sq_abs, hsB2]
      exact (dotProduct_sq_le _ _).trans (mul_le_mul_of_nonneg_right (hm c) hB0)
    exact abs_le_of_sq_le_sq h (by positivity)
  have hε : ∀ j, (e j ⬝ᵥ b) ^ 2 ≤ 1 / (n : ℝ) ^ 2 * B := fun j ↦
    (dotProduct_sq_le _ _).trans (mul_le_mul_of_nonneg_right (he j) hB0)
  have hcl : ∀ c, ((cluster ℓ c).card : ℝ) * B - n * (δ * B) - n * (2 * |R| * δ * B) ≤
      ∑ j ∈ cluster ℓ c, (m c ⬝ᵥ b + g j ⬝ᵥ b) ^ 2 := by
    intro c
    set x := m c ⬝ᵥ b
    have hY1 : |∑ j ∈ cluster ℓ c, g j ⬝ᵥ b| ≤ n * (δ * sB) := by
      have h := h1 c
      rw [abs_div, abs_of_pos hN, div_le_iff₀ hN] at h
      linarith
    have hY2 : ((cluster ℓ c).card : ℝ) * B - n * (δ * B) ≤
        ∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2 := by
      have h := (abs_le.1 (h2 c)).1
      have e1 : (∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) / n - ((cluster ℓ c).card : ℝ) / n * B =
          ((∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) - (cluster ℓ c).card * B) / n := by ring
      rw [e1, le_div_iff₀ hN] at h
      linarith
    have hexp : ∑ j ∈ cluster ℓ c, (x + g j ⬝ᵥ b) ^ 2 = ((cluster ℓ c).card : ℝ) * x ^ 2 +
        2 * x * ∑ j ∈ cluster ℓ c, g j ⬝ᵥ b + ∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2 := by
      simp only [add_sq, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
    have hcross : |2 * x * ∑ j ∈ cluster ℓ c, g j ⬝ᵥ b| ≤ n * (2 * |R| * δ * B) := by
      rw [abs_mul, abs_mul, abs_two]
      calc 2 * |x| * |∑ j ∈ cluster ℓ c, g j ⬝ᵥ b| ≤ 2 * (|R| * sB) * (n * (δ * sB)) := by
            gcongr
            exact hx c
        _ = n * (2 * |R| * δ * B) := by rw [← hsB2]; ring
    have hx2 : 0 ≤ ((cluster ℓ c).card : ℝ) * x ^ 2 := by positivity
    rw [hexp]
    linarith [neg_abs_le (2 * x * ∑ j ∈ cluster ℓ c, g j ⬝ᵥ b)]
  have hsplit : ∑ j, (m (ℓ j) ⬝ᵥ b + g j ⬝ᵥ b) ^ 2 =
      ∑ c, ∑ j ∈ cluster ℓ c, (m c ⬝ᵥ b + g j ⬝ᵥ b) ^ 2 := by
    rw [← SRFrame.Good.sum_cluster_eq ℓ]
    refine sum_congr rfl fun c _ ↦ sum_congr rfl fun j hj ↦ ?_
    rw [(mem_filter.1 hj).2]
  have hsum : n * B - k * (n * (δ * B)) - k * (n * (2 * |R| * δ * B)) ≤
      ∑ j, (m (ℓ j) ⬝ᵥ b + g j ⬝ᵥ b) ^ 2 := by
    rw [hsplit]
    calc n * B - k * (n * (δ * B)) - k * (n * (2 * |R| * δ * B))
        = ∑ c, (((cluster ℓ c).card : ℝ) * B - n * (δ * B) - n * (2 * |R| * δ * B)) := by
          rw [sum_sub_distrib, sum_sub_distrib, ← sum_mul, sum_card_cluster]
          simp
      _ ≤ _ := sum_le_sum fun c _ ↦ hcl c
  have hpt : ∀ j, 1 / 2 * (m (ℓ j) ⬝ᵥ b + g j ⬝ᵥ b) ^ 2 - (e j ⬝ᵥ b) ^ 2 ≤
      ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2 := by
    intro j
    rw [add_dotProduct, add_dotProduct]
    nlinarith [sq_nonneg (m (ℓ j) ⬝ᵥ b + g j ⬝ᵥ b + 2 * (e j ⬝ᵥ b))]
  have hεsum : ∑ j, (e j ⬝ᵥ b) ^ 2 ≤ n * (1 / (n : ℝ) ^ 2 * B) :=
    (sum_le_sum fun j _ ↦ hε j).trans_eq (by simp)
  have htot : 1 / 2 * (n * B - k * (n * (δ * B)) - k * (n * (2 * |R| * δ * B))) -
      n * (1 / (n : ℝ) ^ 2 * B) ≤ ∑ j, ((m (ℓ j) + g j + e j) ⬝ᵥ b) ^ 2 := by
    calc 1 / 2 * (n * B - k * (n * (δ * B)) - k * (n * (2 * |R| * δ * B))) -
          n * (1 / (n : ℝ) ^ 2 * B)
        ≤ ∑ j, (1 / 2 * (m (ℓ j) ⬝ᵥ b + g j ⬝ᵥ b) ^ 2 - (e j ⬝ᵥ b) ^ 2) := by
          rw [sum_sub_distrib, ← mul_sum]
          linarith
      _ ≤ _ := sum_le_sum fun j _ ↦ hpt j
  rw [le_div_iff₀ hN]
  calc (1 / 2 * (1 - k * δ * (1 + 2 * |R|)) - 1 / (n : ℝ) ^ 2) * B * n
      = 1 / 2 * (n * B - k * (n * (δ * B)) - k * (n * (2 * |R| * δ * B))) -
          n * (1 / (n : ℝ) ^ 2 * B) := by ring
    _ ≤ _ := htot

/-! ### The constants -/

/-- `τ₂ (d+1)² ≤ 2 w 256^{-t}` for `t ≥ 1`. -/
theorem τ_two_mul_le {w : ℝ} (hw : 0 ≤ w) (d : ℕ) {t : ℕ} (ht : 1 ≤ t) :
    τ w d t 2 * ((d : ℝ) + 1) ^ 2 ≤ 2 * w * (1 / 256) ^ t := by
  have hs : Real.sqrt (((2 : ℕ) : ℝ) ^ 2) = 2 := by
    rw [Nat.cast_ofNat, Real.sqrt_sq (by norm_num)]
  have hD : (0 : ℝ) < ((d : ℝ) + 1) ^ (2 * t) := by positivity
  have hle : ((d : ℝ) + 1) ^ 2 ≤ ((d : ℝ) + 1) ^ (2 * t) :=
    pow_le_pow_right₀ (by linarith [d.cast_nonneg (α := ℝ)]) (by omega)
  have hfrac : ((d : ℝ) + 1) ^ 2 / ((d : ℝ) + 1) ^ (2 * t) ≤ 1 := (div_le_one hD).2 hle
  have ha : (0 : ℝ) ≤ 2 * w * (1 / 256) ^ t := by positivity
  calc τ w d t 2 * ((d : ℝ) + 1) ^ 2
      = 2 * w * (1 / 256) ^ t * (((d : ℝ) + 1) ^ 2 / ((d : ℝ) + 1) ^ (2 * t)) := by
        rw [τ, hs]
        field_simp
    _ ≤ 2 * w * (1 / 256) ^ t * 1 := mul_le_mul_of_nonneg_left hfrac ha
    _ = 2 * w * (1 / 256) ^ t := mul_one _

/-- `t 256^{-t} ≤ 1/128` for `t ≥ 1`. -/
theorem mul_inv_256_pow_le {t : ℕ} (ht : 1 ≤ t) : (t : ℝ) * (1 / 256) ^ t ≤ 1 / 128 := by
  have h1 : (t : ℝ) ≤ 2 ^ t := by exact_mod_cast (Nat.lt_two_pow_self (n := t)).le
  have h2 : ((1 : ℝ) / 128) ^ t ≤ 1 / 128 := by
    calc ((1 : ℝ) / 128) ^ t ≤ (1 / 128) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
      _ = 1 / 128 := pow_one _
  calc (t : ℝ) * (1 / 256) ^ t ≤ 2 ^ t * (1 / 256) ^ t :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (1 / 128) ^ t := by rw [← mul_pow]; norm_num
    _ ≤ 1 / 128 := h2

/-- **The constant of the good event**: `k δ (1 + 2|R|) ≤ 1/64` for `δ = τ₂ (d+1)²`, given
`k w ≤ 1`. -/
theorem k_mul_δ_le {w R : ℝ} {s t : ℕ} (hP : SRParams k d n w R s t) (hkw : (k : ℝ) * w ≤ 1) :
    (k : ℝ) * (τ w d t 2 * ((d : ℝ) + 1) ^ 2) * (1 + 2 * |R|) ≤ 1 / 64 := by
  have ht := hP.t_pos
  have hw := hP.w_pos
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hX : 0 ≤ τ w d t 2 * ((d : ℝ) + 1) ^ 2 := by
    have := τ_pos hw d t 2
    positivity
  have hτ := τ_two_mul_le hw.le d ht
  have hR : 1 + 2 * |R| ≤ t := by
    have h1 : 2 * |R| ≤ R ^ 2 + 1 := by nlinarith [sq_nonneg (|R| - 1), sq_abs R]
    have h2 := hP.t_ge
    nlinarith [sq_nonneg R]
  have hta := mul_inv_256_pow_le ht
  calc (k : ℝ) * (τ w d t 2 * ((d : ℝ) + 1) ^ 2) * (1 + 2 * |R|)
      ≤ k * (τ w d t 2 * ((d : ℝ) + 1) ^ 2) * t :=
        mul_le_mul_of_nonneg_left hR (mul_nonneg hk0 hX)
    _ ≤ k * (2 * w * (1 / 256) ^ t) * t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hk0) (Nat.cast_nonneg _)
    _ = 2 * (k * w) * (t * (1 / 256) ^ t) := by ring
    _ ≤ 2 * 1 * (1 / 128) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hkw (by norm_num)) hta (by positivity)
          (by norm_num)
    _ = 1 / 64 := by norm_num

/-! ### The standard frame of a sample -/

/-- The rounded sample points `ỹⱼ = r (ωⱼ)`, as rationals. -/
def roundedPts (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    Fin n → Fin d → ℚ :=
  fun j a ↦ r (ω j) a

/-- The whitening matrix `A` of the rounded sample, over the reals. -/
noncomputable def Ahat (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  (whitenMat (secondMoment (roundedPts r ω))).map (↑)

/-- The map `G = A Σ^{1/2}` from the standard frame to the data frame. -/
noncomputable def Gmat (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Ahat r ω * CFC.sqrt M.S

/-- The standardized mean `m_c = Σ^{-1/2} μ_c`. -/
noncomputable def stdMean (M : Mixture k d) (c : Fin k) : Fin d → ℝ :=
  (CFC.sqrt M.S)⁻¹ *ᵥ M.μ c

/-- The **re-rounding error** `ρⱼ = zⱼ - A ỹⱼ` of the whitened data. -/
noncomputable def regridErr (p : ℕ) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) : Fin d → ℝ :=
  fun a ↦ (whitenData p (roundedPts r ω) j a : ℝ) -
    ((whitenMat (secondMoment (roundedPts r ω)) *ᵥ roundedPts r ω j) a : ℝ)

/-- **The standard frame of a sample**, at grid precision `p`: the labels of `ω`, the algorithm's
whitened re-rounded data, `G = A Σ^{1/2}`, the means `Σ^{-1/2} μ_c`, the standardized noises, the
errors `Σ^{-1/2} (ỹⱼ - yⱼ) + G⁻¹ ρⱼ`, and the weights of `M`. -/
noncomputable def modelFrame (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (p : ℕ) : SRFrame n d k where
  ℓ := labels ω
  z := whitenData p (roundedPts r ω)
  G := Gmat M r ω
  m := stdMean M
  g := stdNoise M ω
  e j := Separating.roundErr M r ω j + (Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j
  wt := M.w

/-- The frame before re-rounding: data `A ỹⱼ` and errors `Σ^{-1/2} (ỹⱼ - yⱼ)` (analysis only). -/
noncomputable def modelFrame₀ (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : SRFrame n d k where
  ℓ := labels ω
  z j := whitenMat (secondMoment (roundedPts r ω)) *ᵥ roundedPts r ω j
  G := Gmat M r ω
  m := stdMean M
  g := stdNoise M ω
  e := Separating.roundErr M r ω
  wt := M.w

/-! ### The sample in the standard frame -/

theorem secondMoment_yt (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    secondMoment (Separating.yt r ω) = (secondMoment (roundedPts r ω)).map (↑) :=
  secondMoment_cast _

/-- `ζ⁰ⱼ = m_{ℓⱼ} + gⱼ + Σ^{-1/2} (ỹⱼ - yⱼ) = Σ^{-1/2} ỹⱼ`. -/
theorem std_add_eq (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    stdMean M (labels ω j) + stdNoise M ω j + Separating.roundErr M r ω j =
      (CFC.sqrt M.S)⁻¹ *ᵥ Separating.yt r ω j := by
  rw [stdMean, stdNoise, Separating.roundErr, ← mulVec_add, ← mulVec_add]
  congr 1
  funext i
  simp only [labels, Pi.add_apply, Pi.sub_apply]
  ring

/-- `⟨ỹⱼ, v⟩ = ⟨ζ⁰ⱼ, Σ^{1/2} v⟩`. -/
theorem dotProduct_yt (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) (u : Fin d → ℝ) :
    Separating.yt r ω j ⬝ᵥ u =
      (stdMean M (labels ω j) + stdNoise M ω j + Separating.roundErr M r ω j) ⬝ᵥ
        (CFC.sqrt M.S *ᵥ u) := by
  rw [std_add_eq, dotProduct_mulVec, ← mulVec_transpose, transpose_sqrt, mulVec_mulVec,
    Separating.sqrt_mul_inv_sqrt hS, one_mulVec]

/-- `vᵀĈ₀v = (1/n) ∑ⱼ ⟨ζ⁰ⱼ, Σ^{1/2} v⟩²`. -/
theorem quad_secondMoment_yt (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (u : Fin d → ℝ) :
    quad ((secondMoment (roundedPts r ω)).map (↑)) u =
      (∑ j, ((stdMean M (labels ω j) + stdNoise M ω j + Separating.roundErr M r ω j) ⬝ᵥ
        (CFC.sqrt M.S *ᵥ u)) ^ 2) / n := by
  rw [← secondMoment_yt, quad_secondMoment]
  congr 1
  exact sum_congr rfl fun j _ ↦ by rw [dotProduct_yt M hS]

theorem sqrt_mulVec_inv_sqrt_mulVec {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (u : Fin d → ℝ) : CFC.sqrt S *ᵥ ((CFC.sqrt S)⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, Separating.sqrt_mul_inv_sqrt hS, one_mulVec]

/-- `‖Σ^{1/2} u‖² = uᵀΣu`. -/
theorem sqrt_mulVec_dot_self {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) (u : Fin d → ℝ) :
    (CFC.sqrt S *ᵥ u) ⬝ᵥ (CFC.sqrt S *ᵥ u) = quad S u := by
  rw [dotProduct_self_eq_sum_sq, Separating.sum_sq_sqrt_mulVec hS]

/-- `‖Σ^{-1/2} u‖² = sqNormIn Σ u`. -/
theorem inv_sqrt_mulVec_dot_self {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef)
    (u : Fin d → ℝ) :
    ((CFC.sqrt S)⁻¹ *ᵥ u) ⬝ᵥ ((CFC.sqrt S)⁻¹ *ᵥ u) = sqNormIn S u := by
  rw [dotProduct_self_eq_sum_sq, Separating.sum_sq_inv_sqrt_mulVec hS]

theorem roundErr_dot_self_le (M : Mixture k d) (hS : M.S.PosDef) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    Separating.roundErr M r ω j ⬝ᵥ Separating.roundErr M r ω j ≤ 1 / (n : ℝ) ^ 2 := by
  rw [dotProduct_self_eq_sum_sq]
  exact Separating.sum_sq_roundErr_le M hS hr ω j

/-- The first and second moments of the degree-`2` good event, in the form used by the bounds:
`|(1/n) ∑_{S_c} ⟨gⱼ, b⟩| ≤ δ ‖b‖` and `|(1/n) ∑_{S_c} ⟨gⱼ, b⟩² - (|S_c|/n) ‖b‖²| ≤ δ ‖b‖²`, with
`δ = τ₂ (d+1)²`. -/
theorem stdNoise_moments {M : Mixture k d} {w : ℝ} {t : ℕ}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hω : GoodGraded M w t ω) (ht : 1 ≤ t) :
    (∀ c b, |(∑ j ∈ cluster (labels ω) c, stdNoise M ω j ⬝ᵥ b) / n| ≤
      τ w d t 2 * ((d : ℝ) + 1) ^ 2 * Real.sqrt (b ⬝ᵥ b)) ∧
    (∀ c b, |(∑ j ∈ cluster (labels ω) c, (stdNoise M ω j ⬝ᵥ b) ^ 2) / n -
      ((cluster (labels ω) c).card : ℝ) / n * (b ⬝ᵥ b)| ≤
        τ w d t 2 * ((d : ℝ) + 1) ^ 2 * (b ⬝ᵥ b)) := by
  have hG := hω 2 (by omega)
  have hU := uniformNoise_of_goodNoise (S := 1) (1 : Matrix (Fin d) (Fin d) ℝ) (by simp)
    (fun j ↦ (one_mulVec _).symm) hG
  refine ⟨fun c b ↦ ?_, fun c b ↦ ?_⟩
  · have h := hU c 1 (by norm_num) b
    rw [one_mulVec] at h
    simpa [gaussMom] using h
  · have h := hU c 2 le_rfl b
    rw [one_mulVec, Real.sq_sqrt (dotProduct_self_nonneg' b)] at h
    have hg2 : (gaussMom 2 : ℝ) = 1 := by simp [gaussMom]
    rwa [hg2, mul_one] at h

/-- **The second moment is within the factors of the covariance**: `Σ / 5 ⪯ Ĉ₀ ⪯ 3 (R² + 2) Σ`. -/
theorem quad_bounds (M : Mixture k d) (hS : M.S.PosDef) (hsum : ∑ c, M.w c = 1) {w R : ℝ}
    {s t : ℕ} (hw : ∀ c, w ≤ M.w c) (hrad : ∀ c, sqNormIn M.S (M.μ c) ≤ R ^ 2)
    (hP : SRParams k d n w R s t) {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hω : GoodGraded M w t ω) (u : Fin d → ℝ) :
    quad M.S u ≤ 5 * quad ((secondMoment (roundedPts r ω)).map (↑)) u ∧
      quad ((secondMoment (roundedPts r ω)).map (↑)) u ≤ 3 * (R ^ 2 + 2) * quad M.S u := by
  have hn := hP.n_pos
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2⟩ := stdNoise_moments hω hP.t_pos
  set δ := τ w d t 2 * ((d : ℝ) + 1) ^ 2 with hδ_def
  have hδ0 : 0 ≤ δ := by
    have := τ_pos hP.w_pos d t 2
    positivity
  have hkw : (k : ℝ) * w ≤ 1 := by
    calc (k : ℝ) * w = ∑ _c : Fin k, w := by simp
      _ ≤ ∑ c, M.w c := sum_le_sum fun c _ ↦ hw c
      _ = 1 := hsum
  have hδ := k_mul_δ_le hP hkw
  have hm : ∀ c, stdMean M c ⬝ᵥ stdMean M c ≤ R ^ 2 := fun c ↦ by
    rw [stdMean, inv_sqrt_mulVec_dot_self hS.posSemidef]
    exact hrad c
  have he := roundErr_dot_self_le M hS hr ω
  have hlo := le_sum_sq_dotProduct hn hm he (CFC.sqrt M.S *ᵥ u) (fun c ↦ h1 c _)
    (fun c ↦ h2 c _)
  have hhi := sum_sq_dotProduct_le hn hm he (CFC.sqrt M.S *ᵥ u) (fun c ↦ h2 c _)
  rw [← quad_secondMoment_yt M hS, sqrt_mulVec_dot_self hS.posSemidef] at hlo hhi
  have hn2 : 1 / (n : ℝ) ^ 2 ≤ 1 / 4 := by
    have h20 : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast hP.n_ge
    push_cast at h20
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have hqS := quad_nonneg hS.posSemidef u
  have hkδ : (k : ℝ) * δ ≤ 1 / 64 := by
    have : (k : ℝ) * δ ≤ k * δ * (1 + 2 * |R|) :=
      le_mul_of_one_le_right (mul_nonneg (Nat.cast_nonneg _) hδ0) (by linarith [abs_nonneg R])
    linarith
  constructor
  · have hcoef : 1 / 5 ≤ 1 / 2 * (1 - k * δ * (1 + 2 * |R|)) - 1 / (n : ℝ) ^ 2 := by linarith
    have := mul_le_mul_of_nonneg_right hcoef hqS
    linarith
  · have hcoef : 3 * (R ^ 2 + 1 + k * δ + 1 / (n : ℝ) ^ 2) ≤ 3 * (R ^ 2 + 2) := by linarith
    have := mul_le_mul_of_nonneg_right hcoef hqS
    linarith

/-- A real matrix whose quadratic form dominates a positive definite one is positive definite. -/
theorem posDef_of_quad_le {C S : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) (hS : S.PosDef)
    {c : ℝ} (hc : 0 < c) (h : ∀ u, quad S u ≤ c * quad C u) : C.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · change Cᴴ = C
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hC
  · rw [star_trivial]
    have h1 := quad_pos hS hx
    have h2 := h x
    change 0 < quad C x
    by_contra hneg
    push Not at hneg
    nlinarith

/-! ### The frame is good -/

/-- `Gᵀ v = Σ^{1/2} (Aᵀ v)`. -/
theorem Gmat_transpose_mulVec (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) :
    (Gmat M r ω)ᵀ *ᵥ v = CFC.sqrt M.S *ᵥ ((Ahat r ω)ᵀ *ᵥ v) := by
  rw [Gmat, transpose_mul, transpose_sqrt, ← mulVec_mulVec]

/-- **The second moment of the rounded sample is positive definite** (over the reals). -/
theorem secondMoment_posDef (M : Mixture k d) (hS : M.S.PosDef) (hsum : ∑ c, M.w c = 1)
    {w R : ℝ} {s t : ℕ} (hw : ∀ c, w ≤ M.w c) (hrad : ∀ c, sqNormIn M.S (M.μ c) ≤ R ^ 2)
    (hP : SRParams k d n w R s t) {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hω : GoodGraded M w t ω) :
    ((secondMoment (roundedPts r ω)).map ((↑) : ℚ → ℝ)).PosDef := by
  refine posDef_of_quad_le ?_ hS (by norm_num : (0 : ℝ) < 5) fun u ↦
    (quad_bounds M hS hsum hw hrad hP hr hω u).1
  rw [← secondMoment_cast, secondMoment_transpose]

/-- **The frame before re-rounding is good.** -/
theorem modelFrame₀_good (M : Mixture k d) (hM : M.Valid) {w R Csep : ℝ} {s t : ℕ}
    (hw : ∀ c, w ≤ M.w c) (hrad : ∀ c, sqNormIn M.S (M.μ c) ≤ R ^ 2)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / w) ≤ sqNormIn M.S (M.μ a - M.μ b))
    (hP : SRParams k d n w R s t) {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hω : GoodGraded M w t ω) :
    (modelFrame₀ M r ω).Good w R Csep s t := by
  have hS := hM.posDef
  have hB := quad_bounds M hS hM.sum_w hw hrad hP hr hω
  have hpd := secondMoment_posDef M hS hM.sum_w hw hrad hP hr hω
  have hA := quad_whitenMat_transpose_bounds hpd
  have hn : (0 : ℝ) < n := by exact_mod_cast hP.n_pos
  have hz : ∀ j, (modelFrame₀ M r ω).zR j =
      (modelFrame₀ M r ω).G *ᵥ (modelFrame₀ M r ω).ζ j := by
    intro j
    change _ = Gmat M r ω *ᵥ
      (stdMean M (labels ω j) + stdNoise M ω j + Separating.roundErr M r ω j)
    rw [std_add_eq, Gmat, ← mulVec_mulVec, sqrt_mulVec_inv_sqrt_mulVec hS]
    exact (Colinear.mulVec_cast (whitenMat (secondMoment (roundedPts r ω)))
      (roundedPts r ω j)).symm
  have hG : IsUnit (modelFrame₀ M r ω).G.det := by
    change IsUnit (Gmat M r ω).det
    rw [Gmat, det_mul]
    exact (det_whitenMat_ne_zero hpd).isUnit.mul
      ((isUnit_iff_isUnit_det _).1 (isUnit_sqrt_of_posDef hS))
  have hup : ∀ v, ((modelFrame₀ M r ω).Gᵀ *ᵥ v) ⬝ᵥ ((modelFrame₀ M r ω).Gᵀ *ᵥ v) ≤
      20 * (v ⬝ᵥ v) := by
    intro v
    change ((Gmat M r ω)ᵀ *ᵥ v) ⬝ᵥ ((Gmat M r ω)ᵀ *ᵥ v) ≤ _
    rw [Gmat_transpose_mulVec, sqrt_mulVec_dot_self hS.posSemidef]
    have h1 := (hB ((Ahat r ω)ᵀ *ᵥ v)).1
    have h2 := (hA v).2
    unfold Ahat at h1 ⊢
    linarith
  have hlow : ∀ v, v ⬝ᵥ v ≤
      3 * (R ^ 2 + 2) * (((modelFrame₀ M r ω).Gᵀ *ᵥ v) ⬝ᵥ ((modelFrame₀ M r ω).Gᵀ *ᵥ v)) := by
    intro v
    change _ ≤ 3 * (R ^ 2 + 2) * (((Gmat M r ω)ᵀ *ᵥ v) ⬝ᵥ ((Gmat M r ω)ᵀ *ᵥ v))
    rw [Gmat_transpose_mulVec, sqrt_mulVec_dot_self hS.posSemidef]
    have h1 := (hB ((Ahat r ω)ᵀ *ᵥ v)).2
    have h2 := (hA v).1
    unfold Ahat at h1 ⊢
    linarith
  have herr : ∀ j, (modelFrame₀ M r ω).e j ⬝ᵥ (modelFrame₀ M r ω).e j ≤ 4 / (n : ℝ) ^ 2 := by
    intro j
    have h := roundErr_dot_self_le M hS hr ω j
    have : 1 / (n : ℝ) ^ 2 ≤ 4 / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact h.trans this
  have hradius : ∀ c, (modelFrame₀ M r ω).m c ⬝ᵥ (modelFrame₀ M r ω).m c ≤ R ^ 2 := by
    intro c
    change stdMean M c ⬝ᵥ stdMean M c ≤ R ^ 2
    rw [stdMean, inv_sqrt_mulVec_dot_self hS.posSemidef]
    exact hrad c
  have hsep' : ∀ a b, a ≠ b → Csep * Real.log (1 / w) ≤
      ((modelFrame₀ M r ω).m a - (modelFrame₀ M r ω).m b) ⬝ᵥ
        ((modelFrame₀ M r ω).m a - (modelFrame₀ M r ω).m b) := by
    intro a b hab
    change _ ≤ (stdMean M a - stdMean M b) ⬝ᵥ (stdMean M a - stdMean M b)
    rw [stdMean, stdMean, ← mulVec_sub, inv_sqrt_mulVec_dot_self hS.posSemidef]
    exact hsep a b hab
  exact { z_eq := hz, G_inv := hG, G_up := hup, G_low := hlow, err := herr, radius := hradius,
          sep := hsep', wt_ge := hw, wt_sum := hM.sum_w, good := hω, params := hP }

/-- **The standard frame of a sample is good**, at any grid precision `p` with
`3 (R² + 2) d n² ≤ 4^p`. -/
theorem modelFrame_good (M : Mixture k d) (hM : M.Valid) {w R Csep : ℝ} {s t : ℕ}
    (hw : ∀ c, w ≤ M.w c) (hrad : ∀ c, sqNormIn M.S (M.μ c) ≤ R ^ 2)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / w) ≤ sqNormIn M.S (M.μ a - M.μ b))
    (hP : SRParams k d n w R s t) {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hω : GoodGraded M w t ω) {p : ℕ}
    (hp : 3 * (R ^ 2 + 2) * d * (n : ℝ) ^ 2 ≤ 4 ^ p) :
    (modelFrame M r ω p).Good w R Csep s t := by
  have hS := hM.posDef
  have h0 := modelFrame₀_good M hM hw hrad hsep hP hr hω
  have hG : IsUnit (Gmat M r ω).det := h0.G_inv
  have hn : (0 : ℝ) < n := h0.n_pos_real
  -- the re-rounding error
  have hρa : ∀ j a, regridErr p r ω j a ^ 2 ≤ 1 / 4 ^ p := by
    intro j a
    have hx : |(whitenMat (secondMoment (roundedPts r ω)) *ᵥ roundedPts r ω j) a| ≤
        (n : ℚ) ^ 2 := by
      have := h0.abs_z_le j a
      exact_mod_cast this
    have h1 := abs_reRound_sub_le p hx
    have h2 : |regridErr p r ω j a| ≤ 1 / 2 ^ p := by
      have e : regridErr p r ω j a =
          ((reRound p ((n : ℚ) ^ 2) ((whitenMat (secondMoment (roundedPts r ω)) *ᵥ
              roundedPts r ω j) a) -
            (whitenMat (secondMoment (roundedPts r ω)) *ᵥ roundedPts r ω j) a : ℚ) : ℝ) := by
        rw [Rat.cast_sub]
        rfl
      rw [e, ← Rat.cast_abs]
      calc _ ≤ ((1 / 2 ^ p : ℚ) : ℝ) := Rat.cast_le.2 h1
        _ = 1 / 2 ^ p := by push_cast; ring
    calc regridErr p r ω j a ^ 2 = |regridErr p r ω j a| ^ 2 := (sq_abs _).symm
      _ ≤ (1 / 2 ^ p) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = 1 / 4 ^ p := by
        rw [div_pow, one_pow, ← pow_mul, mul_comm p 2, pow_mul]
        norm_num
  have hρ : ∀ j, regridErr p r ω j ⬝ᵥ regridErr p r ω j ≤ d * (1 / 4 ^ p) := by
    intro j
    rw [dotProduct_self_eq_sum_sq]
    exact (sum_le_sum fun a _ ↦ hρa j a).trans_eq (by simp)
  have hkey : 3 * (R ^ 2 + 2) * (d * (1 / 4 ^ p)) ≤ 1 / (n : ℝ) ^ 2 := by
    have h4 : (0 : ℝ) < 4 ^ p := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [show 3 * (R ^ 2 + 2) * (d * (1 / 4 ^ p)) = 3 * (R ^ 2 + 2) * d / 4 ^ p by ring,
      div_le_div_iff₀ h4 hn2]
    linarith
  have hGρ : ∀ j, ((Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j) ⬝ᵥ
      ((Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j) ≤ 1 / (n : ℝ) ^ 2 := by
    intro j
    have h1 := h0.Ginv_mulVec_le (regridErr p r ω j)
    have h2 := mul_le_mul_of_nonneg_left (hρ j) (SRFrame.Good.three_R_sq_nonneg R)
    exact (h1.trans h2).trans hkey
  have hz : ∀ j, (modelFrame M r ω p).zR j =
      (modelFrame M r ω p).G *ᵥ (modelFrame M r ω p).ζ j := by
    intro j
    have h := h0.z_eq j
    change (fun a ↦ ((whitenMat (secondMoment (roundedPts r ω)) *ᵥ roundedPts r ω j) a : ℝ)) =
      Gmat M r ω *ᵥ (stdMean M (labels ω j) + stdNoise M ω j + Separating.roundErr M r ω j) at h
    change (fun a ↦ (whitenData p (roundedPts r ω) j a : ℝ)) =
      Gmat M r ω *ᵥ (stdMean M (labels ω j) + stdNoise M ω j +
        (Separating.roundErr M r ω j + (Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j))
    rw [← add_assoc, mulVec_add, ← h, mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]
    funext a
    simp [regridErr]
  have herr : ∀ j, (modelFrame M r ω p).e j ⬝ᵥ (modelFrame M r ω p).e j ≤ 4 / (n : ℝ) ^ 2 := by
    intro j
    change (Separating.roundErr M r ω j + (Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j) ⬝ᵥ
      (Separating.roundErr M r ω j + (Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j) ≤ _
    have h1 := dotProduct_add_le_two (Separating.roundErr M r ω j)
      ((Gmat M r ω)⁻¹ *ᵥ regridErr p r ω j)
    have h2 := roundErr_dot_self_le M hS hr ω j
    have h3 := hGρ j
    have e : 2 * (1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2) = 4 / (n : ℝ) ^ 2 := by ring
    linarith
  exact { z_eq := hz, G_inv := h0.G_inv, G_up := h0.G_up, G_low := h0.G_low, err := herr,
          radius := h0.radius, sep := h0.sep, wt_ge := h0.wt_ge, wt_sum := h0.wt_sum,
          good := h0.good, params := h0.params }

/-- **The frame of a sample** [BS23, Theorem 1.3, analysis]. For a valid mixture with weights at
least `w`, radius `sqNormIn Σ μ_c ≤ R²`, separation `Csep ln (1/w) ≤ sqNormIn Σ (μ_a - μ_b)`, the
parameter facts, a rounding within `1/n` and a sample in the graded good event:

* the second moment `Ĉ₀` of the rounded points has positive leading principal minors (the data
  part of the guard passes), and
* the standard frame at the grid precision `gridPrec R n d` is good; its labels are those of the
  sample, its data the algorithm's whitened re-rounded data `whitenData (gridPrec R n d) Y` of
  the rounded points `Y = roundedPts r ω`, its map `G = A Σ^{1/2}`, its means `Σ^{-1/2} μ_c`, its
  noises `stdNoise M ω` and its weights `M.w` (all by definition, `BS23.SmallRadius.modelFrame`).
-/
theorem frame_of_model (M : Mixture k d) (hM : M.Valid) {w Csep : ℝ} {R : ℚ} {s t : ℕ}
    (hw : ∀ c, w ≤ M.w c) (hrad : ∀ c, sqNormIn M.S (M.μ c) ≤ (R : ℝ) ^ 2)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / w) ≤ sqNormIn M.S (M.μ a - M.μ b))
    (hP : SRParams k d n w R s t) {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} (hω : GoodGraded M w t ω) :
    LeadMinorsPos (secondMoment (roundedPts r ω)) ∧
      (modelFrame M r ω (gridPrec R n d)).Good w R Csep s t :=
  ⟨leadMinorsPos_of_posDef (secondMoment_posDef M hM.posDef hM.sum_w hw hrad hP hr hω),
    modelFrame_good M hM hw hrad hsep hP hr hω (le_four_pow_gridPrec R n d)⟩

end BS23.SmallRadius
