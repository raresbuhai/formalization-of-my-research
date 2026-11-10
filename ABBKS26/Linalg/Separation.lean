module

public import ABBKS26.Model
public import Mathlib.Analysis.Matrix.Order

/-!
# Separation of covariances: Frobenius-close pairs and congruence invariance

Matrix facts behind the refinement stage of the proof of [ABBKS26, Theorem 5.2] and the passage
to whitened coordinates. Quadratic-form bounds are written as in `ABBKS26/Model.lean`:
`S ⪰ c I` is `∀ v, c (v ⬝ᵥ v) ≤ v ⬝ᵥ S v`, and `S ⪯ C I` is `∀ v, v ⬝ᵥ S v ≤ C (v ⬝ᵥ v)`. The
squared Frobenius distance of symmetric matrices is `tr ((S₁ - S₂)²)`.

## Main results

* `ABBKS26.Separation.trace_mul_nonneg`: `tr (X Y) ≥ 0` for positive semidefinite `X`, `Y`.
* `ABBKS26.Separation.trace_inv_mul_sub_one_sq_le`: for positive definite `S₁ ⪰ c I` and
  symmetric `S₂`, `tr ((S₁⁻¹ S₂ - 1)²) ≤ tr ((S₁ - S₂)²) / c²`;
  `ABBKS26.Separation.trace_inv_mul_sub_one_sq_le_of_le` is the version with
  `tr ((S₁ - S₂)²) ≤ θ²`.
* `ABBKS26.Separation.not_frobeniusSeparated`: if `S₁, S₂ ⪰ c I`, `S₁ ⪯ C I`,
  `tr ((S₁ - S₂)²) ≤ θ²` and `θ C ≤ Δ c²` (as `θ² C² ≤ Δ² c⁴`), then `S₁` and `S₂` are not
  relatively Frobenius separated (`ABBKS26.FrobeniusSeparated`).
* `ABBKS26.Separation.spectrallySeparated_of_centeredSeparated`: under the same bounds for both
  matrices, `Δ`-separation (`ABBKS26.CenteredSeparated`) is spectral separation in one of the two
  orders.
* Invariance under congruence `S ↦ T S Tᵀ`, `μ ↦ T μ` for invertible `T`:
  `ABBKS26.Separation.spectrallySeparated_congr`, `ABBKS26.Separation.frobeniusSeparated_congr`,
  `ABBKS26.Separation.centeredSeparated_congr`, `ABBKS26.Separation.meanSeparated_congr`.
-/

@[expose] public section

namespace ABBKS26

namespace Separation

open Matrix
open scoped MatrixOrder

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The **trace of a product of positive semidefinite matrices** is nonnegative. -/
theorem trace_mul_nonneg {X Y : Matrix n n ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    0 ≤ (X * Y).trace := by
  classical
  obtain ⟨a, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg
  rw [← mul_assoc, trace_mul_comm, ← mul_assoc, star_eq_conjTranspose]
  exact (hX.mul_mul_conjTranspose_same a).trace_nonneg

omit [DecidableEq n] in
/-- The trace against a positive semidefinite matrix is monotone in the Loewner order. -/
theorem trace_mul_le_trace_mul {X X' Y : Matrix n n ℝ} (h : (X' - X).PosSemidef)
    (hY : Y.PosSemidef) : (X * Y).trace ≤ (X' * Y).trace := by
  have := trace_mul_nonneg h hY
  rw [sub_mul, trace_sub] at this
  linarith

/-- `S ⪰ c I` for `c > 0` gives `S⁻¹ ⪯ c⁻¹ I`. -/
theorem posSemidef_smul_one_sub_inv {S : Matrix n n ℝ} {c : ℝ} (hS : S.PosDef) (hc : 0 < c)
    (hcS : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)) : (c⁻¹ • (1 : Matrix n n ℝ) - S⁻¹).PosSemidef := by
  have hdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hS.det_pos.ne'
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · refine IsHermitian.sub ?_ hS.inv.isHermitian
    simp [IsHermitian]
  · set y := S⁻¹ *ᵥ x with hy
    have hSy : S *ᵥ y = x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    have h1 : c * (y ⬝ᵥ y) ≤ x ⬝ᵥ y := by
      have := hcS y
      rwa [hSy, dotProduct_comm y x] at this
    have h2 : 0 ≤ (x - c • y) ⬝ᵥ (x - c • y) := by
      simpa using dotProduct_self_star_nonneg (x - c • y)
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm y x] at h2
    have h3 : c * (x ⬝ᵥ y) ≤ x ⬝ᵥ x := by nlinarith
    simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
      dotProduct_smul, smul_eq_mul, ← hy]
    rw [sub_nonneg, inv_mul_eq_div, le_div_iff₀ hc]
    linarith

/-- **Relative Frobenius distance from the Frobenius distance**: for positive definite `S₁ ⪰ c I`
(`c > 0`) and symmetric `S₂`, `tr ((S₁⁻¹ S₂ - 1)²) ≤ tr ((S₁ - S₂)²) / c²`.

With `D = S₂ - S₁` and `P = S₁⁻¹ ⪯ c⁻¹ I`, `S₁⁻¹ S₂ - 1 = P D`, and
`tr (P D P D) = tr (P (D P D)) ≤ c⁻¹ tr (D P D) = c⁻¹ tr (P D²) ≤ c⁻² tr (D²)`. -/
theorem trace_inv_mul_sub_one_sq_le {S₁ S₂ : Matrix n n ℝ} {c : ℝ} (hS₁ : S₁.PosDef)
    (hS₂ : S₂.IsHermitian) (hc : 0 < c) (hc₁ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S₁ *ᵥ v)) :
    ((S₁⁻¹ * S₂ - 1) * (S₁⁻¹ * S₂ - 1)).trace ≤ ((S₁ - S₂) * (S₁ - S₂)).trace / c ^ 2 := by
  have hdet : IsUnit S₁.det := isUnit_iff_ne_zero.mpr hS₁.det_pos.ne'
  set D := S₂ - S₁ with hDdef
  have hD : D.IsHermitian := hS₂.sub hS₁.isHermitian
  have hP : S₁⁻¹.PosSemidef := hS₁.inv.posSemidef
  have hle := posSemidef_smul_one_sub_inv hS₁ hc hc₁
  have heq : S₁⁻¹ * S₂ - 1 = S₁⁻¹ * D := by
    rw [hDdef, mul_sub, nonsing_inv_mul _ hdet]
  have hDD : (S₁ - S₂) * (S₁ - S₂) = D * D := by
    rw [hDdef, ← neg_sub S₁ S₂, neg_mul_neg]
  have hDPD : (D * S₁⁻¹ * D).PosSemidef := by
    have := hP.conjTranspose_mul_mul_same D
    rwa [hD.eq] at this
  have hD2 : (D * D).PosSemidef := by
    have := posSemidef_conjTranspose_mul_self D
    rwa [hD.eq] at this
  have step1 : (S₁⁻¹ * (D * S₁⁻¹ * D)).trace ≤ c⁻¹ * (D * S₁⁻¹ * D).trace := by
    have := trace_mul_le_trace_mul hle hDPD
    simpa [smul_mul_assoc, trace_smul] using this
  have step2 : (S₁⁻¹ * (D * D)).trace ≤ c⁻¹ * (D * D).trace := by
    have := trace_mul_le_trace_mul hle hD2
    simpa [smul_mul_assoc, trace_smul] using this
  have hcyc : (D * S₁⁻¹ * D).trace = (S₁⁻¹ * (D * D)).trace := by
    rw [trace_mul_comm, ← mul_assoc]
    exact trace_mul_comm _ _
  rw [heq, hDD, show S₁⁻¹ * D * (S₁⁻¹ * D) = S₁⁻¹ * (D * S₁⁻¹ * D) by simp only [mul_assoc]]
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  calc (S₁⁻¹ * (D * S₁⁻¹ * D)).trace ≤ c⁻¹ * (S₁⁻¹ * (D * D)).trace := by rw [← hcyc]; exact step1
    _ ≤ c⁻¹ * (c⁻¹ * (D * D).trace) := mul_le_mul_of_nonneg_left step2 hci
    _ = (D * D).trace / c ^ 2 := by field_simp

/-- `trace_inv_mul_sub_one_sq_le` with a bound `tr ((S₁ - S₂)²) ≤ θ²`. -/
theorem trace_inv_mul_sub_one_sq_le_of_le {S₁ S₂ : Matrix n n ℝ} {c θ : ℝ} (hS₁ : S₁.PosDef)
    (hS₂ : S₂.IsHermitian) (hc : 0 < c) (hc₁ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S₁ *ᵥ v))
    (hθ : ((S₁ - S₂) * (S₁ - S₂)).trace ≤ θ ^ 2) :
    ((S₁⁻¹ * S₂ - 1) * (S₁⁻¹ * S₂ - 1)).trace ≤ θ ^ 2 / c ^ 2 :=
  (trace_inv_mul_sub_one_sq_le hS₁ hS₂ hc hc₁).trans
    (div_le_div_of_nonneg_right hθ (by positivity))

end General

variable {d : ℕ}

/-- **Frobenius-close covariances are not relatively Frobenius separated**: if `S₁ ⪰ c I`
(positive definite), `S₂ ⪰ c I` (symmetric), `S₁ ⪯ C I`, `tr ((S₁ - S₂)²) ≤ θ²` and
`θ² C² ≤ Δ² c⁴`, then `¬ FrobeniusSeparated Δ S₁ S₂`.

Every `t` with `S₂ ⪯ t S₁` is at least `c / C`, so `Δ² t² ≥ θ² / c² ≥ tr ((S₁⁻¹ S₂ - 1)²)`. -/
theorem not_frobeniusSeparated {S₁ S₂ : Matrix (Fin d) (Fin d) ℝ} {c C θ Δ : ℝ}
    (hS₁ : S₁.PosDef) (hS₂ : S₂.IsHermitian) (hc : 0 < c)
    (hc₁ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S₁ *ᵥ v)) (hc₂ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S₂ *ᵥ v))
    (hC₁ : ∀ v, v ⬝ᵥ (S₁ *ᵥ v) ≤ C * (v ⬝ᵥ v))
    (hθ : ((S₁ - S₂) * (S₁ - S₂)).trace ≤ θ ^ 2) (hΔ : θ ^ 2 * C ^ 2 ≤ Δ ^ 2 * c ^ 4) :
    ¬ FrobeniusSeparated Δ S₁ S₂ := by
  rintro ⟨t, ht, hlt⟩
  have htr := trace_inv_mul_sub_one_sq_le_of_le hS₁ hS₂ hc hc₁ hθ
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i⟩⟩
  · rw [Matrix.trace_eq_zero_of_isEmpty] at hlt
    nlinarith [sq_nonneg (Δ * t)]
  set v : Fin d → ℝ := Pi.single i 1
  have hvv : v ⬝ᵥ v = 1 := by simp [v]
  have h2 := hc₂ v
  have h1 := hc₁ v
  have hC := hC₁ v
  have htv := ht v
  rw [hvv, mul_one] at h1 h2 hC
  -- `c ≤ t * q` with `c ≤ q ≤ C`, so `t > 0` and `c ≤ t C`.
  set q := v ⬝ᵥ (S₁ *ᵥ v)
  have hq : 0 < q := lt_of_lt_of_le hc h1
  have ht0 : 0 < t := by
    by_contra h
    push Not at h
    nlinarith
  have hcC : c ≤ t * C := by nlinarith
  have hC0 : 0 < C := by nlinarith
  -- `θ² ≤ Δ² c² t²`
  have hct : c ^ 2 ≤ t ^ 2 * C ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hc.le hcC 2
  have hθ' : θ ^ 2 * C ^ 2 ≤ (Δ ^ 2 * c ^ 2 * t ^ 2) * C ^ 2 := by
    calc θ ^ 2 * C ^ 2 ≤ Δ ^ 2 * c ^ 4 := hΔ
      _ = Δ ^ 2 * c ^ 2 * c ^ 2 := by ring
      _ ≤ Δ ^ 2 * c ^ 2 * (t ^ 2 * C ^ 2) :=
          mul_le_mul_of_nonneg_left hct (by positivity)
      _ = (Δ ^ 2 * c ^ 2 * t ^ 2) * C ^ 2 := by ring
  have hθ'' : θ ^ 2 ≤ Δ ^ 2 * c ^ 2 * t ^ 2 := le_of_mul_le_mul_right hθ' (by positivity)
  have : θ ^ 2 / c ^ 2 ≤ Δ ^ 2 * t ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

/-- **Frobenius-close separated covariances are spectrally separated**: if `S₁, S₂` are positive
definite with `c I ⪯ Sᵢ ⪯ C I`, `tr ((S₁ - S₂)²) ≤ θ²` and `θ² C² ≤ Δ² c⁴` (that is,
`θ C ≤ Δ c²`), then `Δ`-separation of `S₁` and `S₂` is spectral separation in one of the two
orders. -/
theorem spectrallySeparated_of_centeredSeparated {S₁ S₂ : Matrix (Fin d) (Fin d) ℝ}
    {c C θ Δ : ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosDef) (hc : 0 < c)
    (hc₁ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S₁ *ᵥ v)) (hc₂ : ∀ v, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S₂ *ᵥ v))
    (hC₁ : ∀ v, v ⬝ᵥ (S₁ *ᵥ v) ≤ C * (v ⬝ᵥ v)) (hC₂ : ∀ v, v ⬝ᵥ (S₂ *ᵥ v) ≤ C * (v ⬝ᵥ v))
    (hθ : ((S₁ - S₂) * (S₁ - S₂)).trace ≤ θ ^ 2) (hΔ : θ ^ 2 * C ^ 2 ≤ Δ ^ 2 * c ^ 4)
    (hsep : CenteredSeparated Δ S₁ S₂) :
    SpectrallySeparated Δ S₁ S₂ ∨ SpectrallySeparated Δ S₂ S₁ := by
  have hθ' : ((S₂ - S₁) * (S₂ - S₁)).trace ≤ θ ^ 2 := by
    rwa [← neg_sub S₁ S₂, neg_mul_neg]
  rcases hsep with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (not_frobeniusSeparated hS₁ hS₂.isHermitian hc hc₁ hc₂ hC₁ hθ hΔ)
  · exact absurd h (not_frobeniusSeparated hS₂ hS₁.isHermitian hc hc₂ hc₁ hC₂ hθ' hΔ)

/-! ### Invariance under congruence -/

section Congruence

variable {T : Matrix (Fin d) (Fin d) ℝ}

/-- The quadratic form of `T S Tᵀ` at `v` is that of `S` at `Tᵀ v`. -/
theorem dotProduct_congr_mulVec (T S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    v ⬝ᵥ ((T * S * Tᵀ) *ᵥ v) = (Tᵀ *ᵥ v) ⬝ᵥ (S *ᵥ (Tᵀ *ᵥ v)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- `(T a) ⬝ᵥ v = a ⬝ᵥ (Tᵀ v)`. -/
theorem mulVec_dotProduct_eq (T : Matrix (Fin d) (Fin d) ℝ) (a v : Fin d → ℝ) :
    (T *ᵥ a) ⬝ᵥ v = a ⬝ᵥ (Tᵀ *ᵥ v) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- For invertible `T`, every vector is `Tᵀ w` for some `w`. -/
theorem transpose_mulVec_inv (hT : IsUnit T.det) (w : Fin d → ℝ) :
    Tᵀ *ᵥ ((Tᵀ)⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, mul_nonsing_inv _ (by rwa [det_transpose]), one_mulVec]

/-- A statement about all quadratic forms is invariant under the change of variables `v ↦ Tᵀ v`
for invertible `T`. -/
theorem forall_congr_transpose (hT : IsUnit T.det) (p : (Fin d → ℝ) → Prop) :
    (∀ v, p (Tᵀ *ᵥ v)) ↔ ∀ w, p w :=
  ⟨fun h w ↦ transpose_mulVec_inv hT w ▸ h _, fun h _ ↦ h _⟩

/-- An existential over vectors is invariant under the change of variables `v ↦ Tᵀ v` for
invertible `T`. -/
theorem exists_congr_transpose (hT : IsUnit T.det) (p : (Fin d → ℝ) → Prop) :
    (∃ v, p (Tᵀ *ᵥ v)) ↔ ∃ w, p w :=
  ⟨fun ⟨v, h⟩ ↦ ⟨_, h⟩, fun ⟨w, h⟩ ↦ ⟨(Tᵀ)⁻¹ *ᵥ w, by rwa [transpose_mulVec_inv hT]⟩⟩

/-- Similar matrices have the same `tr (X²)`. -/
theorem trace_conj_sq {U : Matrix (Fin d) (Fin d) ℝ} (hU : IsUnit U.det)
    (X : Matrix (Fin d) (Fin d) ℝ) : ((U⁻¹ * X * U) * (U⁻¹ * X * U)).trace = (X * X).trace := by
  have h1 : (U⁻¹ * X * U) * (U⁻¹ * X * U) = U⁻¹ * (X * X) * U := by
    simp only [mul_assoc, mul_nonsing_inv_cancel_left _ _ hU]
  rw [h1, trace_mul_comm, ← mul_assoc, mul_nonsing_inv _ hU, one_mul]

/-- **Spectral separation is invariant under congruence** by an invertible matrix. -/
theorem spectrallySeparated_congr (hT : IsUnit T.det) {Δ : ℝ}
    {S₁ S₂ : Matrix (Fin d) (Fin d) ℝ} :
    SpectrallySeparated Δ (T * S₁ * Tᵀ) (T * S₂ * Tᵀ) ↔ SpectrallySeparated Δ S₁ S₂ := by
  unfold SpectrallySeparated
  simp only [dotProduct_congr_mulVec]
  exact exists_congr_transpose hT fun w ↦ Δ ^ 2 * (w ⬝ᵥ (S₂ *ᵥ w)) < w ⬝ᵥ (S₁ *ᵥ w)

/-- The relative matrix `(T S₁ Tᵀ)⁻¹ (T S₂ Tᵀ) - 1` is similar to `S₁⁻¹ S₂ - 1`. -/
theorem inv_congr_mul_congr_sub_one (hT : IsUnit T.det) (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) :
    (T * S₁ * Tᵀ)⁻¹ * (T * S₂ * Tᵀ) - 1 = (Tᵀ)⁻¹ * (S₁⁻¹ * S₂ - 1) * Tᵀ := by
  have hTt : IsUnit Tᵀ.det := by rwa [det_transpose]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  rw [mul_sub, sub_mul, mul_one, nonsing_inv_mul _ hTt]
  congr 1
  simp only [mul_assoc, nonsing_inv_mul_cancel_left _ _ hT]

/-- **Relative Frobenius separation is invariant under congruence** by an invertible matrix. -/
theorem frobeniusSeparated_congr (hT : IsUnit T.det) {Δ : ℝ}
    {S₁ S₂ : Matrix (Fin d) (Fin d) ℝ} :
    FrobeniusSeparated Δ (T * S₁ * Tᵀ) (T * S₂ * Tᵀ) ↔ FrobeniusSeparated Δ S₁ S₂ := by
  have hTt : IsUnit Tᵀ.det := by rwa [det_transpose]
  unfold FrobeniusSeparated
  simp only [dotProduct_congr_mulVec, inv_congr_mul_congr_sub_one hT,
    trace_conj_sq hTt]
  refine exists_congr fun t ↦ and_congr_left fun _ ↦ ?_
  exact forall_congr_transpose hT fun w ↦ w ⬝ᵥ (S₂ *ᵥ w) ≤ t * (w ⬝ᵥ (S₁ *ᵥ w))

/-- **`Δ`-separation of centered Gaussians is invariant under congruence** by an invertible
matrix [ABBKS26, Definition 5.1]. -/
theorem centeredSeparated_congr (hT : IsUnit T.det) {Δ : ℝ}
    {S₁ S₂ : Matrix (Fin d) (Fin d) ℝ} :
    CenteredSeparated Δ (T * S₁ * Tᵀ) (T * S₂ * Tᵀ) ↔ CenteredSeparated Δ S₁ S₂ := by
  unfold CenteredSeparated
  rw [spectrallySeparated_congr hT, spectrallySeparated_congr hT, frobeniusSeparated_congr hT,
    frobeniusSeparated_congr hT]

/-- **`Δ`-separation of Gaussians with a common covariance is invariant under invertible linear
maps** `x ↦ T x` [ABBKS26, Definition 6.1]: means `T μᵢ`, covariance `T S Tᵀ`. -/
theorem meanSeparated_congr (hT : IsUnit T.det) {Δ : ℝ} {μ₁ μ₂ : Fin d → ℝ}
    {S : Matrix (Fin d) (Fin d) ℝ} :
    MeanSeparated Δ (T *ᵥ μ₁) (T *ᵥ μ₂) (T * S * Tᵀ) ↔ MeanSeparated Δ μ₁ μ₂ S := by
  unfold MeanSeparated
  simp only [dotProduct_congr_mulVec, ← mulVec_sub, mulVec_dotProduct_eq T (μ₁ - μ₂)]
  exact exists_congr_transpose hT fun w ↦ 2 * Δ ^ 2 * (w ⬝ᵥ (S *ᵥ w)) < ((μ₁ - μ₂) ⬝ᵥ w) ^ 2

end Congruence

end Separation

end ABBKS26
