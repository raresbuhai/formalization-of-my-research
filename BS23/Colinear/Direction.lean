module

public import BS23.Colinear.Basis
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The direction step: the Fisher ratio of `Ĉ⁻¹ g`

The step (DIR) of the analysis of the colinear-means algorithm [BS23, Section 6]. The covariance of
the mixture is `cov = Σ + τ² u₀ u₀ᵀ`; write `κ = u₀ᵀ cov⁻¹ u₀` and `σ² = κ / u₀ᵀ Σ⁻¹ u₀`
(`BS23.Mixture.sigmaSq`). If `Ĉ` is within `1 ± ε` of `cov` (as quadratic forms) and the gradient
`g = c u₀ + E` points along `u₀` up to a small error `E`, then the direction `a = Ĉ⁻¹ g` has a large
**Fisher ratio** `⟨a, u₀⟩² / (aᵀ Σ a · u₀ᵀ Σ⁻¹ u₀) ≥ 1/4`, and `aᵀ Σ a` is comparable to `aᵀ cov a`
(`BS23.Colinear.fisher_ratio`).

* **Lengths.** `BS23.Colinear.qnorm C x = √(xᵀ C x)`, with Cauchy–Schwarz
  (`BS23.Colinear.abs_dotProduct_mulVec_le`) and the triangle inequality
  (`BS23.Colinear.qnorm_add_le`). Cauchy–Schwarz also holds for a symmetric form dominated by a
  positive definite one (`BS23.Colinear.sq_dotProduct_mulVec_le_of_abs_quad_le`).
* **Variational facts.** `⟨v, u⟩² ≤ vᵀCv · uᵀC⁻¹u` (`BS23.Colinear.sq_dotProduct_le_quad_mul`);
  `Ĉ ≼ c Σ'` gives `uᵀΣ'⁻¹u ≤ c uᵀĈ⁻¹u` (`BS23.Colinear.inv_quad_le_of_quad_le`; with the basis of
  `Ĉ`, `BS23.Colinear.inv_quad_le_sum_basisVec`); and
  `|⟨E, θ⟩| ≤ B √(θᵀΣ'θ)` for all `θ` gives `EᵀΣ'⁻¹E ≤ B²`
  (`BS23.Colinear.inv_quad_le_sq_of_abs_le`).
* **Perturbed inverses.** In the geometry of `A`, if `Ĉ` is within `1 ± ε` of `A` then
  `‖Ĉ⁻¹h‖ ≤ ‖h‖_{A⁻¹} / (1 - ε)` and `‖Ĉ⁻¹h - A⁻¹h‖ ≤ ε/(1 - ε) ‖h‖_{A⁻¹}`
  (`BS23.Colinear.qnorm_inv_mulVec_le`, `BS23.Colinear.qnorm_inv_sub_inv_le`).
* **Colinear means.** `σ² = 1 - τ² κ ∈ (0, 1]` (`BS23.Colinear.colinear_sigmaSq`) and
  `a₀ = cov⁻¹ u₀` has `a₀ᵀ Σ a₀ = σ² κ` (`BS23.Colinear.quad_S_inv_cov`), `a₀ᵀ cov a₀ = κ`.
  The proof of the main lemma writes `a = c a₀ + r` with `‖r‖_cov ≤ (σ/4) |c| √κ`.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix

variable {d : ℕ}

/-! ### The quadratic form of a sum -/

theorem quad_add_smul {B : Matrix (Fin d) (Fin d) ℝ} (hB : Bᵀ = B) (x y : Fin d → ℝ) (t : ℝ) :
    quad B (x + t • y) = quad B x + 2 * t * (x ⬝ᵥ (B *ᵥ y)) + t ^ 2 * quad B y := by
  simp only [quad, mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec_comm hB y x]
  ring

theorem quad_add {B : Matrix (Fin d) (Fin d) ℝ} (hB : Bᵀ = B) (x y : Fin d → ℝ) :
    quad B (x + y) = quad B x + 2 * (x ⬝ᵥ (B *ᵥ y)) + quad B y := by
  simpa using quad_add_smul hB x y 1

theorem quad_neg (B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : quad B (-x) = quad B x := by
  simp [quad, mulVec_neg]

theorem quad_sub_apply (A B : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    quad (A - B) x = quad A x - quad B x := by
  simp [quad, sub_mulVec, dotProduct_sub]

/-- The quadratic form of `S + τ uuᵀ`. -/
theorem quad_add_vecMulVec (S : Matrix (Fin d) (Fin d) ℝ) (τ : ℝ) (u x : Fin d → ℝ) :
    quad (S + τ • vecMulVec u u) x = quad S x + τ * (u ⬝ᵥ x) ^ 2 := by
  simp only [quad, add_mulVec, smul_mulVec, vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, op_smul_eq_smul]
  rw [dotProduct_comm x u]
  ring

/-! ### Cauchy–Schwarz -/

/-- **Cauchy–Schwarz** for a symmetric form `B` dominated by a positive definite form `A`:
if `|xᵀBx| ≤ ε xᵀAx` for all `x`, then `(xᵀBy)² ≤ ε² (xᵀAx)(yᵀAy)`. -/
theorem sq_dotProduct_mulVec_le_of_abs_quad_le {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    (hB : Bᵀ = B) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ v, |quad B v| ≤ ε * quad A v)
    (x y : Fin d → ℝ) :
    (x ⬝ᵥ (B *ᵥ y)) ^ 2 ≤ ε ^ 2 * quad A x * quad A y := by
  have hAT := transpose_eq_of_posDef hA
  set β := x ⬝ᵥ (B *ᵥ y)
  have key : ∀ t : ℝ, 2 * t * β ≤ ε * (quad A x + t ^ 2 * quad A y) := by
    intro t
    have h1 := (abs_le.mp (h (x + t • y))).2
    have h2 := (abs_le.mp (h (x + (-t) • y))).1
    rw [quad_add_smul hB, quad_add_smul hAT] at h1 h2
    nlinarith
  rcases eq_or_ne y 0 with rfl | hy
  · simp [β, quad]
  have hb : 0 < quad A y := quad_pos hA hy
  rcases hε.eq_or_lt with rfl | hε'
  · have := key β
    nlinarith
  set t := β / (ε * quad A y)
  have ht : t * (ε * quad A y) = β := div_mul_cancel₀ β (by positivity)
  have h1 := key t
  rw [← ht] at h1
  have h2 : ε * (t ^ 2 * quad A y) ≤ ε * quad A x := by nlinarith
  calc β ^ 2 = (t * (ε * quad A y)) ^ 2 := by rw [ht]
    _ = ε * (t ^ 2 * quad A y) * (ε * quad A y) := by ring
    _ ≤ ε * quad A x * (ε * quad A y) := by gcongr
    _ = ε ^ 2 * quad A x * quad A y := by ring

/-- **Cauchy–Schwarz** for a positive definite form. -/
theorem sq_dotProduct_mulVec_le {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (x y : Fin d → ℝ) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ quad A x * quad A y := by
  have := sq_dotProduct_mulVec_le_of_abs_quad_le hA (transpose_eq_of_posDef hA) zero_le_one
    (fun v ↦ by rw [one_mul, abs_of_nonneg (quad_nonneg hA.posSemidef v)]) x y
  simpa using this

/-! ### Lengths in the geometry of a matrix -/

/-- The length `√(xᵀ C x)` of `x` in the geometry of `C`. -/
noncomputable def qnorm (C : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ := Real.sqrt (quad C x)

theorem qnorm_nonneg (C : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : 0 ≤ qnorm C x :=
  Real.sqrt_nonneg _

theorem sq_qnorm {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (x : Fin d → ℝ) :
    qnorm C x ^ 2 = quad C x :=
  Real.sq_sqrt (quad_nonneg hC.posSemidef x)

theorem qnorm_smul (C : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : Fin d → ℝ) :
    qnorm C (c • x) = |c| * qnorm C x := by
  rw [qnorm, quad_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, qnorm]

theorem qnorm_neg (C : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) : qnorm C (-x) = qnorm C x := by
  rw [qnorm, quad_neg, qnorm]

theorem qnorm_le_qnorm {S C : Matrix (Fin d) (Fin d) ℝ} {x : Fin d → ℝ}
    (h : quad S x ≤ quad C x) : qnorm S x ≤ qnorm C x :=
  Real.sqrt_le_sqrt h

/-- Cauchy–Schwarz for a symmetric form dominated by a positive definite form, with lengths. -/
theorem abs_dotProduct_mulVec_le_of_abs_quad_le {A B : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef)
    (hB : Bᵀ = B) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ v, |quad B v| ≤ ε * quad A v)
    (x y : Fin d → ℝ) :
    |x ⬝ᵥ (B *ᵥ y)| ≤ ε * qnorm A x * qnorm A y := by
  have hle := Real.abs_le_sqrt (sq_dotProduct_mulVec_le_of_abs_quad_le hA hB hε h x y)
  rwa [Real.sqrt_mul (by have := quad_nonneg hA.posSemidef x; positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_sq hε] at hle

/-- **Cauchy–Schwarz**: `|xᵀ C y| ≤ ‖x‖_C ‖y‖_C`. -/
theorem abs_dotProduct_mulVec_le {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (x y : Fin d → ℝ) : |x ⬝ᵥ (C *ᵥ y)| ≤ qnorm C x * qnorm C y := by
  have := abs_dotProduct_mulVec_le_of_abs_quad_le hC (transpose_eq_of_posDef hC) zero_le_one
    (fun v ↦ by rw [one_mul, abs_of_nonneg (quad_nonneg hC.posSemidef v)]) x y
  simpa using this

/-- The triangle inequality. -/
theorem qnorm_add_le {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (x y : Fin d → ℝ) :
    qnorm C (x + y) ≤ qnorm C x + qnorm C y := by
  rw [qnorm, Real.sqrt_le_left (add_nonneg (qnorm_nonneg C x) (qnorm_nonneg C y)),
    quad_add (transpose_eq_of_posDef hC), ← sq_qnorm hC x, ← sq_qnorm hC y]
  have := (abs_le.mp (abs_dotProduct_mulVec_le hC x y)).2
  nlinarith

theorem qnorm_sub_le {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (x y : Fin d → ℝ) :
    qnorm C (x - y) ≤ qnorm C x + qnorm C y := by
  rw [sub_eq_add_neg, ← qnorm_neg C y]
  exact qnorm_add_le hC x (-y)

/-! ### Variational facts -/

theorem quad_inv_mulVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (u : Fin d → ℝ) :
    quad C (C⁻¹ *ᵥ u) = u ⬝ᵥ (C⁻¹ *ᵥ u) := by
  rw [quad, mulVec_inv_mulVec hC, dotProduct_comm]

theorem inv_quad_nonneg {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (u : Fin d → ℝ) :
    0 ≤ u ⬝ᵥ (C⁻¹ *ᵥ u) :=
  quad_nonneg hC.inv.posSemidef u

theorem inv_quad_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) {u : Fin d → ℝ}
    (hu : u ≠ 0) : 0 < u ⬝ᵥ (C⁻¹ *ᵥ u) :=
  quad_pos hC.inv hu

/-- `⟨v, u⟩² ≤ vᵀCv · uᵀC⁻¹u`. -/
theorem sq_dotProduct_le_quad_mul {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (v u : Fin d → ℝ) :
    (v ⬝ᵥ u) ^ 2 ≤ quad C v * (u ⬝ᵥ (C⁻¹ *ᵥ u)) := by
  have := sq_dotProduct_mulVec_le hC v (C⁻¹ *ᵥ u)
  rwa [mulVec_inv_mulVec hC, quad_inv_mulVec hC] at this

/-- `|⟨v, u⟩| ≤ ‖v‖_C √(uᵀC⁻¹u)`. -/
theorem abs_dotProduct_le {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (v u : Fin d → ℝ) :
    |v ⬝ᵥ u| ≤ qnorm C v * Real.sqrt (u ⬝ᵥ (C⁻¹ *ᵥ u)) := by
  have := Real.abs_le_sqrt (sq_dotProduct_le_quad_mul hC v u)
  rwa [Real.sqrt_mul (quad_nonneg hC.posSemidef v)] at this

/-- If `Ĉ ≼ c Σ'` then `uᵀΣ'⁻¹u ≤ c · uᵀĈ⁻¹u`. -/
theorem inv_quad_le_of_quad_le {C D : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (hD : D.PosDef)
    {c : ℝ} (hc : 0 ≤ c) (h : ∀ v, quad C v ≤ c * quad D v) (u : Fin d → ℝ) :
    u ⬝ᵥ (D⁻¹ *ᵥ u) ≤ c * (u ⬝ᵥ (C⁻¹ *ᵥ u)) := by
  set v := D⁻¹ *ᵥ u
  have hX : u ⬝ᵥ v = v ⬝ᵥ u := dotProduct_comm _ _
  have hXq : quad D v = u ⬝ᵥ v := quad_inv_mulVec hD u
  have hY := inv_quad_nonneg hC u
  have hX0 : 0 ≤ u ⬝ᵥ v := inv_quad_nonneg hD u
  have hsq := sq_dotProduct_le_quad_mul hC v u
  rw [← hX] at hsq
  have hle : (u ⬝ᵥ v) * (u ⬝ᵥ v) ≤ (u ⬝ᵥ v) * (c * (u ⬝ᵥ (C⁻¹ *ᵥ u))) := by
    have := h v
    rw [hXq] at this
    nlinarith
  rcases hX0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · exact le_of_mul_le_mul_left hle h0

/-- The `(1 + ε)` form of `BS23.Colinear.inv_quad_le_of_quad_le`. -/
theorem inv_quad_le_of_quad_le_one_add {C D : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (hD : D.PosDef) {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ v, quad C v ≤ (1 + ε) * quad D v)
    (u : Fin d → ℝ) :
    u ⬝ᵥ (D⁻¹ *ᵥ u) ≤ (1 + ε) * (u ⬝ᵥ (C⁻¹ *ᵥ u)) :=
  inv_quad_le_of_quad_le hC hD (by linarith) h u

/-- The selection bound (SEL): if `Ĉ ≼ (1 + ε) cov`, the basis `λᵢ` of `Ĉ` has
`uᵀ cov⁻¹ u ≤ (1 + ε) ∑ᵢ ⟨λᵢ, u⟩² / λᵢᵀĈλᵢ`. -/
theorem inv_quad_le_sum_basisVec {C cov : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (hcov : cov.PosDef) {ε : ℝ} (hε : 0 ≤ ε) (hup : ∀ v, quad C v ≤ (1 + ε) * quad cov v)
    (u : Fin d → ℝ) :
    u ⬝ᵥ (cov⁻¹ *ᵥ u) ≤ (1 + ε) * ∑ i, (basisVec C i ⬝ᵥ u) ^ 2 / quad C (basisVec C i) := by
  rw [sum_sq_div_quad_basisVec hC]
  exact inv_quad_le_of_quad_le_one_add hC hcov hε hup u

/-- If `|⟨E, θ⟩| ≤ B ‖θ‖_{Σ'}` for every `θ`, then `EᵀΣ'⁻¹E ≤ B²`. -/
theorem inv_quad_le_sq_of_abs_le {D : Matrix (Fin d) (Fin d) ℝ} (hD : D.PosDef)
    {E : Fin d → ℝ} {B : ℝ} (h : ∀ θ, |E ⬝ᵥ θ| ≤ B * Real.sqrt (quad D θ)) :
    E ⬝ᵥ (D⁻¹ *ᵥ E) ≤ B ^ 2 := by
  set X := E ⬝ᵥ (D⁻¹ *ᵥ E)
  have hX0 : 0 ≤ X := inv_quad_nonneg hD E
  have hθ := h (D⁻¹ *ᵥ E)
  rw [quad_inv_mulVec hD, abs_of_nonneg hX0] at hθ
  rcases hX0.eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.mpr h0
  have hXs : X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0).symm
  have hsB : Real.sqrt X ≤ B := by
    have : Real.sqrt X * Real.sqrt X ≤ B * Real.sqrt X := hXs ▸ hθ
    exact le_of_mul_le_mul_right this hs
  calc X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX0).symm
    _ ≤ B ^ 2 := pow_le_pow_left₀ hs.le hsB 2

/-! ### Perturbed inverses -/

private theorem le_div_of_mul_sq_le {N K e : ℝ} (hN : 0 ≤ N) (he : 0 < e) (hK : 0 ≤ K)
    (h : e * N ^ 2 ≤ K * N) : N ≤ K / e := by
  rw [le_div_iff₀ he]
  rcases hN.eq_or_lt with h0 | h0
  · rw [← h0]; simpa using hK
  · nlinarith

/-- If `(1 - ε) A ≼ Ĉ`, then `‖Ĉ⁻¹h‖_A ≤ √(hᵀA⁻¹h) / (1 - ε)`. -/
theorem qnorm_inv_mulVec_le {A C : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (hC : C.PosDef)
    {ε : ℝ} (hε : ε < 1) (hlow : ∀ v, (1 - ε) * quad A v ≤ quad C v) (h : Fin d → ℝ) :
    qnorm A (C⁻¹ *ᵥ h) ≤ Real.sqrt (h ⬝ᵥ (A⁻¹ *ᵥ h)) / (1 - ε) := by
  set x := C⁻¹ *ᵥ h
  have hCx : quad C x = x ⬝ᵥ h := by rw [quad, mulVec_inv_mulVec hC]
  have hcs := (abs_le.mp (abs_dotProduct_le hA x h)).2
  refine le_div_of_mul_sq_le (qnorm_nonneg _ _) (by linarith) (Real.sqrt_nonneg _) ?_
  rw [sq_qnorm hA, mul_comm (Real.sqrt _)]
  linarith [hlow x]

/-- If `(1 - ε) A ≼ Ĉ ≼ (1 + ε) A`, then `‖Ĉ⁻¹h - A⁻¹h‖_A ≤ ε / (1 - ε) · √(hᵀA⁻¹h)`. -/
theorem qnorm_inv_sub_inv_le {A C : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) (hC : C.PosDef)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hlow : ∀ v, (1 - ε) * quad A v ≤ quad C v)
    (hup : ∀ v, quad C v ≤ (1 + ε) * quad A v) (h : Fin d → ℝ) :
    qnorm A (C⁻¹ *ᵥ h - A⁻¹ *ᵥ h) ≤ ε / (1 - ε) * Real.sqrt (h ⬝ᵥ (A⁻¹ *ᵥ h)) := by
  set y := A⁻¹ *ᵥ h with hy'
  set z := C⁻¹ *ᵥ h - y with hz
  have hBT : (A - C)ᵀ = A - C := by
    rw [transpose_sub, transpose_eq_of_posDef hA, transpose_eq_of_posDef hC]
  have hB : ∀ v, |quad (A - C) v| ≤ ε * quad A v := by
    intro v
    rw [quad_sub_apply, abs_le]
    constructor <;> linarith [hlow v, hup v]
  have hCz : quad C z = z ⬝ᵥ ((A - C) *ᵥ y) := by
    have e1 : C *ᵥ z = h - C *ᵥ y := by rw [hz, mulVec_sub, mulVec_inv_mulVec hC]
    have e2 : (A - C) *ᵥ y = h - C *ᵥ y := by rw [sub_mulVec, hy', mulVec_inv_mulVec hA]
    rw [quad, e1, e2]
  have hcs := (abs_le.mp (abs_dotProduct_mulVec_le_of_abs_quad_le hA hBT hε0 hB z y)).2
  have hy : qnorm A y = Real.sqrt (h ⬝ᵥ (A⁻¹ *ᵥ h)) := by rw [qnorm, quad_inv_mulVec hA]
  rw [hy] at hcs
  rw [div_mul_eq_mul_div]
  refine le_div_of_mul_sq_le (qnorm_nonneg _ _) (by linarith)
    (mul_nonneg hε0 (Real.sqrt_nonneg _)) ?_
  rw [sq_qnorm hA]
  nlinarith [hlow z]

/-! ### The Fisher ratio of the direction -/

/-- `S + τ uuᵀ` is positive definite for `S` positive definite and `τ ≥ 0`. -/
theorem posDef_add_smul_vecMulVec {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) {τ : ℝ}
    (hτ : 0 ≤ τ) (u : Fin d → ℝ) : (S + τ • vecMulVec u u).PosDef :=
  hS.add_posSemidef (by simpa using (posSemidef_vecMulVec_self_star u).smul hτ)

/-- For colinear means: `S *ᵥ cov⁻¹ u₀ = (1 - τ² κ) u₀` and `κ = (1 - τ² κ) · u₀ᵀ S⁻¹ u₀`,
where `cov = S + τ² u₀ u₀ᵀ` and `κ = u₀ᵀ cov⁻¹ u₀`. -/
theorem colinear_identities {S cov : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (hcov : cov.PosDef)
    {u0 : Fin d → ℝ} {τ2 : ℝ} (hcov_eq : cov = S + τ2 • vecMulVec u0 u0) :
    S *ᵥ (cov⁻¹ *ᵥ u0) = (1 - τ2 * (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0))) • u0 ∧
      u0 ⬝ᵥ (cov⁻¹ *ᵥ u0) = (1 - τ2 * (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0))) * (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) := by
  set a₀ := cov⁻¹ *ᵥ u0
  set κ := u0 ⬝ᵥ a₀
  have h1 : cov *ᵥ a₀ = u0 := mulVec_inv_mulVec hcov u0
  have hSa : S *ᵥ a₀ = (1 - τ2 * κ) • u0 := by
    have h2 : cov *ᵥ a₀ = S *ᵥ a₀ + (τ2 * κ) • u0 := by
      rw [hcov_eq, add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
    rw [h1] at h2
    rw [sub_smul, one_smul, eq_sub_iff_add_eq]
    exact h2.symm
  refine ⟨hSa, ?_⟩
  have ha : a₀ = (1 - τ2 * κ) • (S⁻¹ *ᵥ u0) := by
    rw [← mulVec_smul, ← hSa, inv_mulVec_mulVec hS]
  calc κ = u0 ⬝ᵥ a₀ := rfl
    _ = (1 - τ2 * κ) * (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) := by
      conv_lhs => rw [ha]
      rw [dotProduct_smul, smul_eq_mul]

/-- `σ² = κ / u₀ᵀ S⁻¹ u₀` equals `1 - τ² κ`; hence `0 < σ² ≤ 1`. -/
theorem colinear_sigmaSq {S cov : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (hcov : cov.PosDef)
    {u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {τ2 : ℝ} (hτ2 : 0 ≤ τ2)
    (hcov_eq : cov = S + τ2 • vecMulVec u0 u0) :
    (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) / (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) = 1 - τ2 * (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) ∧
      0 < (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) / (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) ∧
      (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) / (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) ≤ 1 := by
  have hκ := inv_quad_pos hcov hu0
  have hq := inv_quad_pos hS hu0
  have heq : (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) / (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) = 1 - τ2 * (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) := by
    rw [div_eq_iff hq.ne']
    exact (colinear_identities hS hcov hcov_eq).2
  refine ⟨heq, div_pos hκ hq, ?_⟩
  rw [heq]
  nlinarith

/-- `cov⁻¹ u₀` has `‖cov⁻¹ u₀‖²_S = σ² κ`. -/
theorem quad_S_inv_cov {S cov : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (hcov : cov.PosDef)
    {u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {τ2 : ℝ} (hτ2 : 0 ≤ τ2)
    (hcov_eq : cov = S + τ2 • vecMulVec u0 u0) :
    quad S (cov⁻¹ *ᵥ u0) =
      (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) / (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) * (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) := by
  rw [(colinear_sigmaSq hS hcov hu0 hτ2 hcov_eq).1, quad,
    (colinear_identities hS hcov hcov_eq).1, dotProduct_smul, smul_eq_mul, dotProduct_comm]

/-- **The Fisher ratio of the direction** (step (DIR)). Let `cov = S + τ² u₀u₀ᵀ` (`τ² ≥ 0`),
`κ = u₀ᵀ cov⁻¹ u₀`, `σ² = κ / u₀ᵀ S⁻¹ u₀`, let `Ĉ` be within `1 ± ε` of `cov` with
`ε ≤ σ / 16` and `ε ≤ 1/4`, and let `g = c u₀ + E` with `c ≠ 0` and
`‖E‖_{cov⁻¹} ≤ |c| √κ σ / 16`. Then `a = Ĉ⁻¹ g` satisfies
`⟨a, u₀⟩² ≥ ¼ (aᵀSa)(u₀ᵀS⁻¹u₀)`, `σ²/4 · aᵀ cov a ≤ aᵀSa ≤ aᵀ cov a` and `aᵀSa > 0`. -/
theorem fisher_ratio {S cov C : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (hC : C.PosDef)
    {u0 : Fin d → ℝ} (hu0 : u0 ≠ 0) {τ2 : ℝ} (hτ2 : 0 ≤ τ2)
    (hcov_eq : cov = S + τ2 • vecMulVec u0 u0) {σ2 : ℝ}
    (hσ2 : σ2 = (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) / (u0 ⬝ᵥ (S⁻¹ *ᵥ u0))) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hεσ : ε ≤ Real.sqrt σ2 / 16) (hε4 : ε ≤ 1 / 4)
    (hlow : ∀ v, (1 - ε) * quad cov v ≤ quad C v) (hup : ∀ v, quad C v ≤ (1 + ε) * quad cov v)
    {c : ℝ} (hc : c ≠ 0) {E : Fin d → ℝ}
    (hE : E ⬝ᵥ (cov⁻¹ *ᵥ E) ≤
      (|c| * Real.sqrt (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) * Real.sqrt σ2 / 16) ^ 2)
    {a : Fin d → ℝ} (ha : a = C⁻¹ *ᵥ (c • u0 + E)) :
    1 / 4 * quad S a * (u0 ⬝ᵥ (S⁻¹ *ᵥ u0)) ≤ (a ⬝ᵥ u0) ^ 2 ∧
      σ2 / 4 * quad cov a ≤ quad S a ∧ 0 < quad S a ∧ quad S a ≤ quad cov a := by
  have hcov : cov.PosDef := hcov_eq ▸ posDef_add_smul_vecMulVec hS hτ2 u0
  -- constants
  set κ := u0 ⬝ᵥ (cov⁻¹ *ᵥ u0) with hκdef
  set q := u0 ⬝ᵥ (S⁻¹ *ᵥ u0) with hqdef
  have hκ : 0 < κ := inv_quad_pos hcov hu0
  have hq : 0 < q := inv_quad_pos hS hu0
  obtain ⟨-, hσ2pos, hσ2le⟩ := colinear_sigmaSq hS hcov hu0 hτ2 hcov_eq
  rw [← hσ2] at hσ2pos hσ2le
  have hσ2q : σ2 * q = κ := by rw [hσ2]; exact div_mul_cancel₀ κ hq.ne'
  set σ := Real.sqrt σ2 with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.mpr hσ2pos
  have hσ1 : σ ≤ 1 := by
    rw [hσdef, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hσ2le
  have hσsq : σ ^ 2 = σ2 := Real.sq_sqrt hσ2pos.le
  set K := Real.sqrt κ with hKdef
  have hK : 0 < K := Real.sqrt_pos.mpr hκ
  have hKsq : K ^ 2 = κ := Real.sq_sqrt hκ.le
  set X := |c| * K with hXdef
  have hX : 0 < X := mul_pos (abs_pos.mpr hc) hK
  -- the main vector `a₀ = cov⁻¹ u₀`
  set a₀ := cov⁻¹ *ᵥ u0 with ha₀
  have hNa₀ : qnorm cov a₀ = K := by rw [qnorm, quad_inv_mulVec hcov]
  have hNSa₀ : qnorm S a₀ = σ * K := by
    rw [qnorm, quad_S_inv_cov hS hcov hu0 hτ2 hcov_eq, ← hσ2,
      Real.sqrt_mul hσ2pos.le]
  have hSle : ∀ x, quad S x ≤ quad cov x := by
    intro x
    rw [hcov_eq, quad_add_vecMulVec]
    nlinarith [sq_nonneg (u0 ⬝ᵥ x)]
  -- the error `r = a - c a₀`
  set r := a - c • a₀ with hrdef
  have har : a = c • a₀ + r := by rw [hrdef]; abel
  have hr : r = c • (C⁻¹ *ᵥ u0 - cov⁻¹ *ᵥ u0) + C⁻¹ *ᵥ E := by
    rw [hrdef, ha, mulVec_add, mulVec_smul, smul_sub]
    abel
  have h1e : 0 < 1 - ε := by linarith
  have hw1 := qnorm_inv_sub_inv_le hcov hC hε0 (by linarith) hlow hup u0
  have hw2 := qnorm_inv_mulVec_le hcov hC (by linarith) hlow E
  have hEs : Real.sqrt (E ⬝ᵥ (cov⁻¹ *ᵥ E)) ≤ X * σ / 16 := by
    calc Real.sqrt (E ⬝ᵥ (cov⁻¹ *ᵥ E)) ≤ Real.sqrt ((X * σ / 16) ^ 2) := by
          apply Real.sqrt_le_sqrt
          convert hE using 2
      _ = X * σ / 16 := Real.sqrt_sq (by positivity)
  have hNr : qnorm cov r ≤ σ * X / 4 := by
    have hεσ' : ε + σ / 16 ≤ σ / 4 * (1 - ε) := by
      nlinarith [mul_le_mul_of_nonneg_left hε4 hσ.le]
    calc qnorm cov r ≤ |c| * qnorm cov (C⁻¹ *ᵥ u0 - cov⁻¹ *ᵥ u0) + qnorm cov (C⁻¹ *ᵥ E) := by
          rw [hr, ← qnorm_smul]; exact qnorm_add_le hcov _ _
      _ ≤ |c| * (ε / (1 - ε) * K) + X * σ / 16 / (1 - ε) := by
          gcongr
          exact hw2.trans (div_le_div_of_nonneg_right hEs h1e.le)
      _ = X * (ε + σ / 16) / (1 - ε) := by
          rw [hXdef]; field_simp
      _ ≤ σ * X / 4 := by
          rw [div_le_iff₀ h1e]
          nlinarith [mul_le_mul_of_nonneg_left hεσ' hX.le]
  have hNr0 := qnorm_nonneg cov r
  -- (A): the Fisher ratio
  have hau : a ⬝ᵥ u0 = c * κ + r ⬝ᵥ u0 := by
    rw [har, add_dotProduct, smul_dotProduct, smul_eq_mul, dotProduct_comm a₀ u0]
  have hru : |r ⬝ᵥ u0| ≤ qnorm cov r * K := by
    have := abs_dotProduct_mulVec_le hcov r a₀
    rwa [ha₀, mulVec_inv_mulVec hcov, ← ha₀, hNa₀] at this
  have hP : 3 / 4 * (X * K) ≤ |a ⬝ᵥ u0| := by
    have h1 : |c * κ| - |r ⬝ᵥ u0| ≤ |a ⬝ᵥ u0| := by
      have := abs_sub (a ⬝ᵥ u0) (r ⬝ᵥ u0)
      rw [hau, add_sub_cancel_right] at this
      rw [hau]
      linarith
    have h2 : |c * κ| = X * K := by
      rw [abs_mul, abs_of_pos hκ, hXdef, ← hKsq]; ring
    have h3 : qnorm cov r * K ≤ σ * X / 4 * K := mul_le_mul_of_nonneg_right hNr hK.le
    have h4 : σ * X / 4 * K ≤ X * K / 4 := by
      have := mul_le_mul_of_nonneg_right hσ1 (mul_pos hX hK).le
      linarith
    linarith
  have hNSa_le : qnorm S a ≤ 5 / 4 * (σ * X) := by
    calc qnorm S a ≤ qnorm S (c • a₀) + qnorm S r := by rw [har]; exact qnorm_add_le hS _ _
      _ ≤ |c| * (σ * K) + qnorm cov r := by
          rw [qnorm_smul, hNSa₀]; gcongr; exact qnorm_le_qnorm (hSle r)
      _ = σ * X + qnorm cov r := by rw [hXdef]; ring
      _ ≤ 5 / 4 * (σ * X) := by linarith
  have hNSa_ge : 3 / 4 * (σ * X) ≤ qnorm S a := by
    have h1 : qnorm S (c • a₀) ≤ qnorm S a + qnorm S r := by
      have : c • a₀ = a - r := by rw [har]; abel
      rw [this]; exact qnorm_sub_le hS _ _
    rw [qnorm_smul, hNSa₀, show |c| * (σ * K) = σ * X by rw [hXdef]; ring] at h1
    have h2 := qnorm_le_qnorm (hSle r)
    linarith
  have hNa_le : qnorm cov a ≤ 5 / 4 * X := by
    calc qnorm cov a ≤ qnorm cov (c • a₀) + qnorm cov r := by
          rw [har]; exact qnorm_add_le hcov _ _
      _ = X + qnorm cov r := by rw [qnorm_smul, hNa₀]
      _ ≤ 5 / 4 * X := by
          have := mul_le_mul_of_nonneg_right hσ1 hX.le
          linarith
  have hQSa_le : quad S a ≤ (5 / 4 * (σ * X)) ^ 2 := by
    rw [← sq_qnorm hS a]; exact pow_le_pow_left₀ (qnorm_nonneg S a) hNSa_le 2
  have hQSa_ge : (3 / 4 * (σ * X)) ^ 2 ≤ quad S a := by
    rw [← sq_qnorm hS a]; exact pow_le_pow_left₀ (by positivity) hNSa_ge 2
  have hQa_le : quad cov a ≤ (5 / 4 * X) ^ 2 := by
    rw [← sq_qnorm hcov a]; exact pow_le_pow_left₀ (qnorm_nonneg cov a) hNa_le 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc 1 / 4 * quad S a * q ≤ 1 / 4 * (5 / 4 * (σ * X)) ^ 2 * q := by gcongr
      _ = 25 / 64 * X ^ 2 * (σ ^ 2 * q) := by ring
      _ = 25 / 64 * (X * K) ^ 2 := by rw [hσsq, hσ2q, ← hKsq]; ring
      _ ≤ (3 / 4 * (X * K)) ^ 2 := by linarith [sq_nonneg (X * K)]
      _ ≤ |a ⬝ᵥ u0| ^ 2 := pow_le_pow_left₀ (by positivity) hP 2
      _ = (a ⬝ᵥ u0) ^ 2 := sq_abs _
  · calc σ2 / 4 * quad cov a ≤ σ2 / 4 * (5 / 4 * X) ^ 2 := by gcongr
      _ = 25 / 64 * (σ ^ 2 * X ^ 2) := by linear_combination (-(25 / 64) * X ^ 2) * hσsq
      _ ≤ (3 / 4 * (σ * X)) ^ 2 := by linarith [sq_nonneg (σ * X)]
      _ ≤ quad S a := hQSa_ge
  · exact lt_of_lt_of_le (by positivity) hQSa_ge
  · exact hSle a

end BS23.Colinear
