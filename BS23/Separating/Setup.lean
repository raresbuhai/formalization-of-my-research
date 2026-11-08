module

public import BS23.Common.UniformProof
public import BS23.Separating.Whiten
public import BS23.Colinear.Moments

/-!
# The model quantities of the analysis of the separating bipartition

The sample `ω` of a mixture `M` with `Σ = M.S ≻ 0`, rounded by `r`, seen through the whitening of
the algorithm for [BS23, Theorem 1.1]. With `Σ^{1/2} = CFC.sqrt Σ` (Mathlib's square root, the one
in `BS23.stdNoise`):

* the rounded points `ỹⱼ = r (ωⱼ)` cast to the reals (`BS23.Separating.yt`);
* their standardized noise `ĝⱼ = Σ^{-1/2} (ỹⱼ - μ_{ℓⱼ})` (`BS23.Separating.ghat`), which is the
  standardized noise `gⱼ = BS23.stdNoise M ω j` of the real point plus the rounding error
  `εⱼ = Σ^{-1/2} (ỹⱼ - yⱼ)` (`BS23.Separating.ghat_eq`, `BS23.Separating.roundErr`) with
  `‖εⱼ‖² = sqNormIn Σ (ỹⱼ - yⱼ) ≤ 1/n²` (`BS23.Separating.sum_sq_roundErr_le`);
* the whitening matrix `W = W Ĉ` of the empirical covariance `Ĉ` of the `ỹⱼ`
  (`BS23.Separating.Wr`), `B = W Σ^{1/2}` (`BS23.Separating.Bm`), the whitened means
  `m_c = W (μ_c - ȳ)` (`BS23.Separating.mc`) and the whitened noise `ζⱼ = B ĝⱼ`
  (`BS23.Separating.zeta`), so that the whitened points are `xⱼ = m_{ℓⱼ} + ζⱼ`
  (`BS23.Separating.whiten_yt`);
* the quadratic form `N(v) = (Wᵀv)ᵀ Σ (Wᵀv) = ‖Bᵀv‖²` of the whitened noise
  (`BS23.Separating.Nform`, `BS23.Separating.Nform_eq_sum_sq`).

**Covariance comparison** (CV1). If, in every cluster, the empirical first and second moments of
`⟨ĝⱼ, b⟩` are within `δ ‖b‖` and `δ ‖b‖²` of the Gaussian ones `0` and `‖b‖²`, with `δ ≤ 1/8`,
and every cluster has at least `wmin n / 2` points (`BS23.Separating.GhatMoments`), then
`(wmin/4) λᵀΣλ ≤ λᵀĈλ` for every `λ`
(`BS23.Separating.quad_S_le_quad_empCov_yt`; the abstract form is
`BS23.Separating.quad_empCov_ge_of_moments`). The proof keeps only the pairs inside a cluster in
`λᵀĈλ = (2n²)⁻¹ ∑_{i,j} ⟨ỹᵢ - ỹⱼ, λ⟩²`; inside cluster `c`, `ỹᵢ - ỹⱼ = Σ^{1/2} (ĝᵢ - ĝⱼ)`, and
`∑_{i,j ∈ S_c} (aᵢ - aⱼ)² = 2 |S_c|² (avg a² - (avg a)²) ≥ |S_c|² ‖b‖²` for `aᵢ = ⟨ĝᵢ, b⟩`,
`b = Σ^{1/2} λ`. These moment hypotheses follow from `BS23.GoodNoise` (degrees `1` and `2`) and
the rounding, with `δ = 2 η (d + 1)² / wmin + 4 / n` (`BS23.Separating.ghatMoments_of_goodNoise`),
which gives CV1 on the good event (`BS23.Separating.quad_S_le_quad_empCov_yt_of_goodNoise`).
So `Ĉ` is positive definite (`BS23.Separating.empCov_yt_posDef`).

**The noise form** (CV2). From CV1 at `λ = Wᵀv` and `W Ĉ Wᵀ = diag κ`, `κᵢ ≤ 2`:
`N(v) ≤ (8 / wmin) ‖v‖²` (`BS23.Separating.Nform_le`). Hence every entry of `B` has
`B_{lk}² ≤ N(e_l) ≤ 8 / wmin` (`BS23.Separating.sq_Bm_apply_le`), `|B_{lk}| ≤ 3 / √wmin`, and every
row and every column of `B` has `ℓ₁` norm at most `3 (d + 1) / √wmin`
(`BS23.Separating.sum_abs_Bm_col_le`, `BS23.Separating.sum_abs_Bm_row_le`).
-/

@[expose] public section

namespace BS23.Separating

open Matrix Finset Colinear
open scoped MatrixOrder

variable {k d n : ℕ}

/-! ### Definitions -/

/-- The rounded sample points `ỹⱼ = r (ωⱼ)`, cast to the reals. -/
def yt (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : Fin n → Fin d → ℝ :=
  fun j i ↦ (r (ω j) i : ℝ)

/-- The standardized noise `ĝⱼ = Σ^{-1/2} (ỹⱼ - μ_{ℓⱼ})` of the rounded points. -/
noncomputable def ghat (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) : Fin d → ℝ :=
  (CFC.sqrt M.S)⁻¹ *ᵥ (yt r ω j - M.μ (labels ω j))

/-- The standardized rounding error `εⱼ = Σ^{-1/2} (ỹⱼ - yⱼ)`. -/
noncomputable def roundErr (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) : Fin d → ℝ :=
  (CFC.sqrt M.S)⁻¹ *ᵥ (yt r ω j - fun i ↦ (ω j).2 i)

/-- The whitening matrix `W = W Ĉ` of the rounded sample. -/
noncomputable def Wr (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  W (empCov (yt r ω))

/-- `B = W Σ^{1/2}`, which maps the standardized noise to the whitened noise. -/
noncomputable def Bm (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Wr r ω * CFC.sqrt M.S

/-- The whitened mean `m_c = W (μ_c - ȳ)` of component `c`. -/
noncomputable def mc (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (c : Fin k) : Fin d → ℝ :=
  Wr r ω *ᵥ (M.μ c - mean (yt r ω))

/-- The whitened noise `ζⱼ = B ĝⱼ`. -/
noncomputable def zeta (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) : Fin d → ℝ :=
  Bm M r ω *ᵥ ghat M r ω j

/-- The quadratic form `N(v) = (Wᵀv)ᵀ Σ (Wᵀv) = vᵀ W Σ Wᵀ v` of the whitened noise. -/
noncomputable def Nform (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) : ℝ :=
  quad M.S ((Wr r ω)ᵀ *ᵥ v)

/-! ### Linear algebra of the square root -/

/-- `‖Σ^{-1/2} u‖² = uᵀ Σ⁻¹ u`. -/
theorem sum_sq_inv_sqrt_mulVec {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef)
    (u : Fin d → ℝ) : ∑ i, ((CFC.sqrt S)⁻¹ *ᵥ u) i ^ 2 = sqNormIn S u := by
  set A := CFC.sqrt S
  have hAt : Aᵀ = A := transpose_sqrt S
  have hAA : A * A = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have h1 : ∑ i, (A⁻¹ *ᵥ u) i ^ 2 = (A⁻¹ *ᵥ u) ⬝ᵥ (A⁻¹ *ᵥ u) := by
    simp [dotProduct, sq]
  rw [h1, sqNormIn, ← hAA, Matrix.mul_inv_rev, ← mulVec_mulVec, dotProduct_mulVec u,
    ← mulVec_transpose, transpose_nonsing_inv, hAt]

/-- `‖Σ^{1/2} v‖² = vᵀ Σ v`. -/
theorem sum_sq_sqrt_mulVec {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) (v : Fin d → ℝ) :
    ∑ i, (CFC.sqrt S *ᵥ v) i ^ 2 = quad S v := by
  have h := dotProduct_mul_transpose_mulVec (CFC.sqrt S) v
  rw [← eq_sqrt_mul_transpose_sqrt hS, transpose_sqrt] at h
  rw [quad, h]

/-- `Σ^{1/2} Σ^{-1/2} = 1` for `Σ ≻ 0`. -/
theorem sqrt_mul_inv_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    CFC.sqrt S * (CFC.sqrt S)⁻¹ = 1 :=
  mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_sqrt_of_posDef hS))

/-! ### The rounded points -/

/-- `ĝⱼ = gⱼ + εⱼ`: the standardized noise of the rounded point is that of the real point plus the
standardized rounding error. -/
theorem ghat_eq (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    ghat M r ω j = stdNoise M ω j + roundErr M r ω j := by
  rw [ghat, stdNoise, roundErr, ← mulVec_add]
  congr 1
  funext i
  simp only [labels, Pi.sub_apply, Pi.add_apply]
  ring

/-- **The rounding error**: `‖εⱼ‖² = sqNormIn Σ (ỹⱼ - yⱼ) ≤ 1/n²` for a rounding within `1/n`. -/
theorem sum_sq_roundErr_le (M : Mixture k d) (hS : M.S.PosDef) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    ∑ i, roundErr M r ω j i ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
  rw [roundErr, sum_sq_inv_sqrt_mulVec hS.posSemidef, ← _root_.one_div_pow]
  exact hr (ω j).1 (ω j).2

/-- `ỹⱼ = μ_{ℓⱼ} + Σ^{1/2} ĝⱼ`. -/
theorem yt_eq (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    yt r ω j = M.μ (labels ω j) + CFC.sqrt M.S *ᵥ ghat M r ω j := by
  rw [ghat, mulVec_mulVec, sqrt_mul_inv_sqrt hS, one_mulVec, add_sub_cancel]

/-- **The whitened points** are `xⱼ = m_{ℓⱼ} + ζⱼ`. -/
theorem whiten_yt (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) :
    whiten (yt r ω) j = mc M r ω (labels ω j) + zeta M r ω j := by
  rw [whiten_eq_mulVec, mc, zeta, Bm, ← Wr, ← mulVec_mulVec, ← mulVec_add]
  congr 1
  rw [yt_eq M hS r ω j]
  abel

/-- `xᵢ - xⱼ = ζᵢ - ζⱼ` for two points of the same cluster. -/
theorem whiten_yt_sub_of_labels_eq (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) {i j : Fin n} (h : labels ω i = labels ω j) :
    whiten (yt r ω) i - whiten (yt r ω) j = zeta M r ω i - zeta M r ω j := by
  rw [whiten_yt M hS, whiten_yt M hS, h]
  abel

/-- `⟨ζⱼ, v⟩ = ⟨ĝⱼ, Bᵀv⟩`. -/
theorem zeta_dotProduct (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n) (v : Fin d → ℝ) :
    zeta M r ω j ⬝ᵥ v = ghat M r ω j ⬝ᵥ ((Bm M r ω)ᵀ *ᵥ v) := by
  rw [zeta, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- `m_a - m_b = W (μ_a - μ_b)`. -/
theorem mc_sub (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (a b : Fin k) :
    mc M r ω a - mc M r ω b = Wr r ω *ᵥ (M.μ a - M.μ b) := by
  rw [mc, mc, ← mulVec_sub]
  congr 1
  abel

/-- `N(v) = ‖Bᵀv‖²`. -/
theorem Nform_eq_sum_sq (M : Mixture k d) (hS : M.S.PosSemidef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) :
    Nform M r ω v = ∑ i, ((Bm M r ω)ᵀ *ᵥ v) i ^ 2 := by
  rw [Nform, Bm, transpose_mul, transpose_sqrt, ← mulVec_mulVec, sum_sq_sqrt_mulVec hS]

theorem Nform_nonneg (M : Mixture k d) (hS : M.S.PosSemidef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (v : Fin d → ℝ) : 0 ≤ Nform M r ω v := by
  rw [Nform_eq_sum_sq M hS]
  positivity

/-! ### Covariance comparison (CV1) -/

/-- `∑_{i,j ∈ s} (aᵢ - aⱼ)² = 2 |s| ∑_{i ∈ s} aᵢ² - 2 (∑_{i ∈ s} aᵢ)²`. -/
theorem sum_sum_sub_sq_eq {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 =
      2 * (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 - 2 * (∑ i ∈ s, a i) ^ 2 := by
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
    ← sum_mul]
  ring

/-- **One cluster**: if the average of the `aᵢ` is within `δ √B` of `0` and the average of the
`aᵢ²` within `δ B` of `B`, with `0 ≤ δ ≤ 1/8`, then `∑_{i,j ∈ s} (aᵢ - aⱼ)² ≥ |s|² B`. -/
theorem sq_card_mul_le_sum_sum_sub_sq {ι : Type*} {s : Finset ι} {a : ι → ℝ} {δ B : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 8) (hB : 0 ≤ B)
    (h1 : |(∑ i ∈ s, a i) / s.card| ≤ δ * Real.sqrt B)
    (h2 : |(∑ i ∈ s, a i ^ 2) / s.card - B| ≤ δ * B) :
    (s.card : ℝ) ^ 2 * B ≤ ∑ i ∈ s, ∑ j ∈ s, (a i - a j) ^ 2 := by
  rw [sum_sum_sub_sq_eq]
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [card_eq_zero.mp h0]
    simp
  have hm : (0 : ℝ) < s.card := by exact_mod_cast hpos
  set m : ℝ := (s.card : ℝ)
  set A1 := ∑ i ∈ s, a i
  set A2 := ∑ i ∈ s, a i ^ 2
  have hA1 : A1 ^ 2 ≤ δ ^ 2 * B * m ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, div_pow, mul_pow, Real.sq_sqrt hB, div_le_iff₀ (by positivity)] at h
    linarith
  have hA2 : (1 - δ) * B * m ≤ A2 := by
    have h := (abs_le.mp h2).1
    rw [le_sub_iff_add_le, le_div_iff₀ hm] at h
    linarith
  have hpoly : 0 ≤ 1 - 2 * δ - 2 * δ ^ 2 := by nlinarith
  nlinarith [mul_nonneg (mul_nonneg hB (sq_nonneg m)) hpoly, mul_le_mul_of_nonneg_left hA2 hm.le]

/-- **Covariance comparison**, abstract form. Let `Yⱼ = μ_{ℓⱼ} + A gⱼ`, let every cluster have at
least `wmin n / 2` points, and let the empirical first and second moments of `⟨gⱼ, b⟩` in every
cluster be within `δ ‖b‖` and `δ ‖b‖²` of `0` and `‖b‖²`, with `0 ≤ δ ≤ 1/8`. Then
`(wmin/4) ‖Aᵀv‖² ≤ vᵀĈv` for the empirical covariance `Ĉ` of the `Yⱼ`. -/
theorem quad_empCov_ge_of_moments {Y : Fin n → Fin d → ℝ} {ℓ : Fin n → Fin k}
    {μ : Fin k → Fin d → ℝ} {A : Matrix (Fin d) (Fin d) ℝ} {g : Fin n → Fin d → ℝ}
    (hY : ∀ j, Y j = μ (ℓ j) + A *ᵥ g j) (hn : 0 < n) {wmin δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 8) (hsize : ∀ c, wmin * n / 2 ≤ ((cluster ℓ c).card : ℝ))
    (h1 : ∀ c b, |(∑ j ∈ cluster ℓ c, g j ⬝ᵥ b) / (cluster ℓ c).card| ≤
      δ * Real.sqrt (∑ i, b i ^ 2))
    (h2 : ∀ c b, |(∑ j ∈ cluster ℓ c, (g j ⬝ᵥ b) ^ 2) / (cluster ℓ c).card - ∑ i, b i ^ 2| ≤
      δ * ∑ i, b i ^ 2)
    (v : Fin d → ℝ) : wmin / 4 * ∑ i, (Aᵀ *ᵥ v) i ^ 2 ≤ quad (empCov Y) v := by
  set b := Aᵀ *ᵥ v
  set B := ∑ i, b i ^ 2
  have hB : 0 ≤ B := by positivity
  have hpair : ∀ i j, ℓ i = ℓ j → (Y i - Y j) ⬝ᵥ v = g i ⬝ᵥ b - g j ⬝ᵥ b := by
    intro i j h
    rw [hY i, hY j, h, add_sub_add_left_eq_sub, ← mulVec_sub, dotProduct_comm, dotProduct_mulVec,
      ← mulVec_transpose, dotProduct_comm, sub_dotProduct]
  have hclus : ∀ c, ((cluster ℓ c).card : ℝ) ^ 2 * B ≤
      ∑ i ∈ cluster ℓ c, ∑ j ∈ cluster ℓ c, ((Y i - Y j) ⬝ᵥ v) ^ 2 := by
    intro c
    have h : ∑ i ∈ cluster ℓ c, ∑ j ∈ cluster ℓ c, ((Y i - Y j) ⬝ᵥ v) ^ 2 =
        ∑ i ∈ cluster ℓ c, ∑ j ∈ cluster ℓ c, (g i ⬝ᵥ b - g j ⬝ᵥ b) ^ 2 := by
      refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
      rw [hpair i j ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)]
    rw [h]
    exact sq_card_mul_le_sum_sum_sub_sq hδ0 hδ hB (h1 c b) (h2 c b)
  have hsplit : ∑ c, ∑ i ∈ cluster ℓ c, ∑ j ∈ cluster ℓ c, ((Y i - Y j) ⬝ᵥ v) ^ 2 ≤
      ∑ i, ∑ j, ((Y i - Y j) ⬝ᵥ v) ^ 2 := by
    rw [← sum_fiberwise univ ℓ (fun i ↦ ∑ j, ((Y i - Y j) ⬝ᵥ v) ^ 2)]
    refine sum_le_sum fun c _ ↦ sum_le_sum fun i _ ↦ ?_
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ sq_nonneg _
  have hcard : ∑ c, ((cluster ℓ c).card : ℝ) = n := by
    have h := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ) (f := ℓ)
      (fun _ _ ↦ mem_univ _)
    rw [card_univ, Fintype.card_fin] at h
    exact_mod_cast h.symm
  have hlow : ∑ c, wmin * n / 2 * ((cluster ℓ c).card : ℝ) * B ≤
      ∑ c, ((cluster ℓ c).card : ℝ) ^ 2 * B := by
    refine sum_le_sum fun c _ ↦ ?_
    have h0 : (0 : ℝ) ≤ (cluster ℓ c).card := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right (hsize c) (mul_nonneg h0 hB)]
  have hsum : ∑ c, wmin * n / 2 * ((cluster ℓ c).card : ℝ) * B = wmin * n / 2 * n * B := by
    rw [← sum_mul, ← mul_sum, hcard]
  rw [hsum] at hlow
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : wmin * n / 2 * n * B ≤ 2 * (n : ℝ) ^ 2 * quad (empCov Y) v := by
    rw [← sum_sum_sq_sub_dotProduct]
    exact hlow.trans ((sum_le_sum fun c _ ↦ hclus c).trans hsplit)
  have hn2 : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by positivity
  refine le_of_mul_le_mul_left ?_ hn2
  linarith

/-- The hypotheses of the covariance comparison for the rounded sample: every cluster has at least
`wmin n / 2` points, and in every cluster the empirical first and second moments of `⟨ĝⱼ, b⟩`
are within `δ ‖b‖` and `δ ‖b‖²` of the Gaussian ones `0` and `‖b‖²`. -/
structure GhatMoments (M : Mixture k d) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (wmin δ : ℝ) : Prop where
  size : ∀ c, wmin * n / 2 ≤ ((cluster (labels ω) c).card : ℝ)
  mom1 : ∀ c b, |(∑ j ∈ cluster (labels ω) c, ghat M r ω j ⬝ᵥ b) /
      (cluster (labels ω) c).card| ≤ δ * Real.sqrt (∑ i, b i ^ 2)
  mom2 : ∀ c b, |(∑ j ∈ cluster (labels ω) c, (ghat M r ω j ⬝ᵥ b) ^ 2) /
      (cluster (labels ω) c).card - ∑ i, b i ^ 2| ≤ δ * ∑ i, b i ^ 2

/-- **Covariance comparison** (CV1): `(wmin/4) λᵀΣλ ≤ λᵀĈλ` for the empirical covariance `Ĉ` of
the rounded sample. -/
theorem quad_S_le_quad_empCov_yt (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (hn : 0 < n) {wmin δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1 / 8) (h : GhatMoments M r ω wmin δ) (v : Fin d → ℝ) :
    wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v := by
  have h' := quad_empCov_ge_of_moments (yt_eq M hS r ω) hn hδ0 hδ h.size h.mom1 h.mom2 v
  rwa [transpose_sqrt, sum_sq_sqrt_mulVec hS.posSemidef] at h'

/-- **The empirical covariance of the rounded sample is positive definite** under CV1. -/
theorem empCov_yt_posDef (M : Mixture k d) (hS : M.S.PosDef) {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin : ℝ} (hwmin : 0 < wmin)
    (hcv : ∀ v, wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v) :
    (empCov (yt r ω)).PosDef :=
  empCov_posDef_of_quad_pos fun v hv ↦
    (mul_pos (by positivity) (quad_pos hS hv)).trans_le (hcv v)

/-! ### The moment hypotheses on the good event -/

/-- `⟨εⱼ, b⟩² ≤ ‖b‖² / n²` for a rounding within `1/n`. -/
theorem sq_roundErr_dotProduct_le (M : Mixture k d) (hS : M.S.PosDef) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (j : Fin n)
    (b : Fin d → ℝ) : (roundErr M r ω j ⬝ᵥ b) ^ 2 ≤ (∑ i, b i ^ 2) / (n : ℝ) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (roundErr M r ω j) b
  have hε := sum_sq_roundErr_le M hS hr ω j
  calc (roundErr M r ω j ⬝ᵥ b) ^ 2 ≤ (∑ i, roundErr M r ω j i ^ 2) * ∑ i, b i ^ 2 := h
    _ ≤ 1 / (n : ℝ) ^ 2 * ∑ i, b i ^ 2 := mul_le_mul_of_nonneg_right hε (by positivity)
    _ = _ := by ring

/-- `|e| ≤ √B / n` from `e² ≤ B / n²`. -/
theorem abs_le_sqrt_div_of_sq_le {e B : ℝ} (hn : 0 < n) (he : e ^ 2 ≤ B / (n : ℝ) ^ 2) :
    |e| * n ≤ Real.sqrt B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ (by positivity)] at he
  rw [Real.le_sqrt (by positivity) ((by positivity : (0 : ℝ) ≤ e ^ 2 * (n : ℝ) ^ 2).trans he),
    mul_pow, sq_abs]
  exact he

/-- **First moment of a perturbed cluster.** If `|(1/n) ∑_{j ∈ s} xⱼ| ≤ η' √B`, every
`eⱼ² ≤ B / n²` and `|s| ≥ wmin n / 2`, then
`|(1/|s|) ∑_{j ∈ s} (xⱼ + eⱼ)| ≤ (2 η' / wmin + 4 / n) √B`. -/
theorem abs_avg_add_le {s : Finset (Fin n)} {x e : Fin n → ℝ} {η' wmin B : ℝ} (hn : 0 < n)
    (hwmin : 0 < wmin) (hη' : 0 ≤ η') (hm : wmin * n / 2 ≤ (s.card : ℝ))
    (hx1 : |(∑ j ∈ s, x j) / n| ≤ η' * Real.sqrt B) (he : ∀ j ∈ s, e j ^ 2 ≤ B / (n : ℝ) ^ 2) :
    |(∑ j ∈ s, (x j + e j)) / s.card| ≤ (2 * η' / wmin + 4 / n) * Real.sqrt B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ)
  set m : ℝ := (s.card : ℝ)
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hsB := Real.sqrt_nonneg B
  have hE1 : |∑ j ∈ s, e j| * N ≤ m * Real.sqrt B := by
    calc |∑ j ∈ s, e j| * N ≤ (∑ j ∈ s, |e j|) * N :=
          mul_le_mul_of_nonneg_right (abs_sum_le_sum_abs _ _) hN.le
      _ = ∑ j ∈ s, |e j| * N := sum_mul _ _ _
      _ ≤ ∑ j ∈ s, Real.sqrt B := sum_le_sum fun j hj ↦ abs_le_sqrt_div_of_sq_le hn (he j hj)
      _ = m * Real.sqrt B := by rw [sum_const, nsmul_eq_mul]
  have hX1 : |∑ j ∈ s, x j| ≤ η' * Real.sqrt B * N := by
    rwa [abs_div, abs_of_pos hN, div_le_iff₀ hN] at hx1
  have hNm : N ≤ 2 / wmin * m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hwmin]
    linarith
  have k1 : η' * Real.sqrt B * N ≤ 2 * η' / wmin * Real.sqrt B * m :=
    calc η' * Real.sqrt B * N ≤ η' * Real.sqrt B * (2 / wmin * m) :=
          mul_le_mul_of_nonneg_left hNm (mul_nonneg hη' hsB)
      _ = 2 * η' / wmin * Real.sqrt B * m := by ring
  have k2 : |∑ j ∈ s, e j| ≤ 4 / N * Real.sqrt B * m := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hN]
    nlinarith [mul_nonneg hm0.le hsB]
  rw [sum_add_distrib, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
  calc |∑ j ∈ s, x j + ∑ j ∈ s, e j| ≤ |∑ j ∈ s, x j| + |∑ j ∈ s, e j| := abs_add_le _ _
    _ ≤ 2 * η' / wmin * Real.sqrt B * m + 4 / N * Real.sqrt B * m := by linarith
    _ = (2 * η' / wmin + 4 / N) * Real.sqrt B * m := by ring

/-- One term of the second moment of a perturbed cluster:
`|(x + e)² - x²| ≤ (x² + B) / n + B / n²` for `e² ≤ B / n²`. -/
theorem abs_add_sq_sub_sq_le {x e B : ℝ} (hn : 0 < n) (hB : 0 ≤ B)
    (he : e ^ 2 ≤ B / (n : ℝ) ^ 2) :
    |(x + e) ^ 2 - x ^ 2| ≤ (x ^ 2 + B) / n + B / (n : ℝ) ^ 2 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hae := abs_le_sqrt_div_of_sq_le hn he
  have h1 : |(x + e) ^ 2 - x ^ 2| ≤ 2 * |x| * |e| + e ^ 2 := by
    rw [show (x + e) ^ 2 - x ^ 2 = 2 * x * e + e ^ 2 by ring]
    calc |2 * x * e + e ^ 2| ≤ |2 * x * e| + |e ^ 2| := abs_add_le _ _
      _ = 2 * |x| * |e| + e ^ 2 := by
        rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg e)]
  have h2 : 2 * |x| * |e| ≤ (x ^ 2 + B) / n := by
    rw [le_div_iff₀ hN]
    have hs := Real.sq_sqrt hB
    have hx := sq_abs x
    nlinarith [sq_nonneg (|x| - Real.sqrt B), mul_le_mul_of_nonneg_left hae (abs_nonneg x)]
  linarith

/-- **Second moment of a perturbed cluster.** If
`|(1/n) ∑_{j ∈ s} xⱼ² - (|s|/n) B| ≤ η' B`, every `eⱼ² ≤ B / n²`, `|s| ≥ wmin n / 2` and
`2 η' / wmin ≤ 1`, then `|(1/|s|) ∑_{j ∈ s} (xⱼ + eⱼ)² - B| ≤ (2 η' / wmin + 4 / n) B`. -/
theorem abs_avg_add_sq_sub_le {s : Finset (Fin n)} {x e : Fin n → ℝ} {η' wmin B : ℝ}
    (hn : 0 < n) (hwmin : 0 < wmin) (hB : 0 ≤ B) (hη' : 0 ≤ η') (hη'w : 2 * η' / wmin ≤ 1)
    (hm : wmin * n / 2 ≤ (s.card : ℝ))
    (hx2 : |(∑ j ∈ s, x j ^ 2) / n - (s.card : ℝ) / n * B| ≤ η' * B)
    (he : ∀ j ∈ s, e j ^ 2 ≤ B / (n : ℝ) ^ 2) :
    |(∑ j ∈ s, (x j + e j) ^ 2) / s.card - B| ≤ (2 * η' / wmin + 4 / n) * B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set N : ℝ := (n : ℝ)
  set m : ℝ := (s.card : ℝ)
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  set T := ∑ j ∈ s, x j ^ 2
  have hX2 : |T - m * B| ≤ η' * B * N := by
    rw [show T / N - m / N * B = (T - m * B) / N by field_simp, abs_div, abs_of_pos hN,
      div_le_iff₀ hN] at hx2
    exact hx2
  have hE2 : |∑ j ∈ s, ((x j + e j) ^ 2 - x j ^ 2)| ≤ T / N + m * B / N + m * B / N ^ 2 := by
    calc |∑ j ∈ s, ((x j + e j) ^ 2 - x j ^ 2)| ≤ ∑ j ∈ s, |(x j + e j) ^ 2 - x j ^ 2| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, ((x j ^ 2 + B) / N + B / N ^ 2) :=
          sum_le_sum fun j hj ↦ abs_add_sq_sub_sq_le hn hB (he j hj)
      _ = T / N + m * B / N + m * B / N ^ 2 := by
          rw [sum_add_distrib, ← sum_div, sum_add_distrib, sum_const, sum_const, nsmul_eq_mul,
            nsmul_eq_mul]
          ring
  have hsplit : ∑ j ∈ s, (x j + e j) ^ 2 - m * B =
      (T - m * B) + ∑ j ∈ s, ((x j + e j) ^ 2 - x j ^ 2) := by
    rw [sum_sub_distrib]
    ring
  have hNm : N ≤ 2 / wmin * m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hwmin]
    linarith
  -- the three pieces
  have k1 : η' * B * N ≤ 2 * η' / wmin * B * m :=
    calc η' * B * N ≤ η' * B * (2 / wmin * m) := mul_le_mul_of_nonneg_left hNm (mul_nonneg hη' hB)
      _ = 2 * η' / wmin * B * m := by ring
  have hT : T ≤ m * B + η' * B * N := by linarith [(abs_le.mp hX2).2]
  have k2 : T / N ≤ m * B / N + η' * B := by
    rw [div_le_iff₀ hN, add_mul, div_mul_cancel₀ _ hN.ne']
    linarith
  have hη'm : η' * N ≤ m := by
    have : η' ≤ wmin / 2 := by
      rw [div_le_iff₀ hwmin] at hη'w
      linarith
    nlinarith
  have k3 : η' * B ≤ m * B / N := by
    rw [le_div_iff₀ hN]
    nlinarith [mul_le_mul_of_nonneg_right hη'm hB]
  have k4 : m * B / N ^ 2 ≤ m * B / N := by
    apply div_le_div_of_nonneg_left (mul_nonneg hm0.le hB) hN
    nlinarith
  have hfin : |∑ j ∈ s, (x j + e j) ^ 2 - m * B| ≤ (2 * η' / wmin + 4 / N) * B * m := by
    rw [hsplit]
    have h4 : (2 * η' / wmin + 4 / N) * B * m = 2 * η' / wmin * B * m + 4 * (m * B / N) := by
      ring
    calc |(T - m * B) + ∑ j ∈ s, ((x j + e j) ^ 2 - x j ^ 2)|
        ≤ |T - m * B| + |∑ j ∈ s, ((x j + e j) ^ 2 - x j ^ 2)| := abs_add_le _ _
      _ ≤ (2 * η' / wmin + 4 / N) * B * m := by linarith
  rw [show (∑ j ∈ s, (x j + e j) ^ 2) / m - B = (∑ j ∈ s, (x j + e j) ^ 2 - m * B) / m by
      field_simp, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
  exact hfin

/-- On the good event, every cluster has at least `wmin n / 2` points. -/
theorem wmin_mul_le_card_cluster {w : Fin k → ℝ} {η wmin : ℝ} {D : ℕ} {ℓ : Fin n → Fin k}
    {g : Fin n → Fin d → ℝ} (hG : GoodNoise w η D ℓ g) (hn : 0 < n) (hw : ∀ c, wmin ≤ w c)
    (hwmin : 0 ≤ wmin) (hη : 2 * η ≤ 1) (c : Fin k) :
    wmin * n / 2 ≤ ((cluster ℓ c).card : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have h := (abs_le.mp (hG.1 c)).1
  have hwc : 0 ≤ w c := hwmin.trans (hw c)
  have h' : wmin / 2 ≤ ((cluster ℓ c).card : ℝ) / n := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 / 2 - η by linarith) hwc, hw c]
  rw [le_div_iff₀ hN] at h'
  linarith

/-- **The moment hypotheses on the good event**: `BS23.GoodNoise` up to degree `D ≥ 2` with error
`η ≤ 1/2`, all weights at least `wmin`, and a rounding within `1/n` give `GhatMoments` with
`δ = 2 η (d + 1)² / wmin + 4 / n`, as long as `2 η (d + 1)² / wmin ≤ 1`. -/
theorem ghatMoments_of_goodNoise (M : Mixture k d) (hS : M.S.PosDef) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)}
    {wmin η : ℝ} {D : ℕ} (hn : 0 < n) (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c)
    (hD : 2 ≤ D) (hη : 2 * η ≤ 1) (hηw : 2 * (η * ((d : ℝ) + 1) ^ 2) / wmin ≤ 1)
    (hG : GoodNoise M.w η D (labels ω) (stdNoise M ω)) :
    GhatMoments M r ω wmin (2 * (η * ((d : ℝ) + 1) ^ 2) / wmin + 4 / n) := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hG.2 (labels ω ⟨0, hn⟩) 0 (by simp))
  have hG2 : GoodNoise M.w η 2 (labels ω) (stdNoise M ω) :=
    ⟨hG.1, fun c α hα ↦ hG.2 c α (hα.trans hD)⟩
  have hU := uniformNoise_of_goodNoise (S := 1) (1 : Matrix (Fin d) (Fin d) ℝ) (by simp)
    (fun j ↦ (one_mulVec _).symm) hG2
  set η' := η * ((d : ℝ) + 1) ^ 2 with hη'_def
  have hη'0 : 0 ≤ η' := mul_nonneg hη0 (by positivity)
  have hq : ∀ b : Fin d → ℝ, b ⬝ᵥ ((1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ b) = ∑ i, b i ^ 2 := by
    intro b
    simp [dotProduct, sq]
  have hsize := wmin_mul_le_card_cluster hG hn hw hwmin.le hη
  have hghat : ∀ j b, ghat M r ω j ⬝ᵥ b = stdNoise M ω j ⬝ᵥ b + roundErr M r ω j ⬝ᵥ b := by
    intro j b
    rw [ghat_eq, add_dotProduct]
  refine ⟨hsize, fun c b ↦ ?_, fun c b ↦ ?_⟩
  · simp_rw [hghat]
    refine abs_avg_add_le hn hwmin hη'0 (hsize c) ?_
      fun j _ ↦ sq_roundErr_dotProduct_le M hS hr ω j b
    have h := hU c 1 (by norm_num) b
    rw [hq] at h
    simpa [gaussMom] using h
  · simp_rw [hghat]
    have hB : 0 ≤ ∑ i, b i ^ 2 := by positivity
    refine abs_avg_add_sq_sub_le hn hwmin hB hη'0 hηw (hsize c) ?_
      fun j _ ↦ sq_roundErr_dotProduct_le M hS hr ω j b
    have h := hU c 2 (by norm_num) b
    rw [hq, Real.sq_sqrt hB] at h
    have hg2 : (gaussMom 2 : ℝ) = 1 := by simp [gaussMom]
    rwa [hg2, mul_one] at h

/-- **Covariance comparison on the good event** (CV1): `(wmin/4) λᵀΣλ ≤ λᵀĈλ` when
`2 η (d + 1)² / wmin + 4 / n ≤ 1/8`. -/
theorem quad_S_le_quad_empCov_yt_of_goodNoise (M : Mixture k d) (hS : M.S.PosDef)
    {r : Rounding k d} (hr : IsRounding M.S (1 / n) r)
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin η : ℝ} {D : ℕ} (hn : 0 < n)
    (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) (hD : 2 ≤ D) (hη : 2 * η ≤ 1)
    (hδ : 2 * (η * ((d : ℝ) + 1) ^ 2) / wmin + 4 / n ≤ 1 / 8)
    (hG : GoodNoise M.w η D (labels ω) (stdNoise M ω)) (v : Fin d → ℝ) :
    wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v := by
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hG.2 (labels ω ⟨0, hn⟩) 0 (by simp))
  have h0 : 0 ≤ 2 * (η * ((d : ℝ) + 1) ^ 2) / wmin := by positivity
  have h4 : 0 ≤ 4 / (n : ℝ) := by positivity
  exact quad_S_le_quad_empCov_yt M hS r ω hn (by positivity) hδ
    (ghatMoments_of_goodNoise M hS hr hn hwmin hw hD hη (by linarith) hG) v

/-! ### The noise form (CV2) -/

/-- **The noise form** (CV2): `N(v) ≤ (8 / wmin) ‖v‖²` under CV1. -/
theorem Nform_le {M : Mixture k d} {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin : ℝ} (hwmin : 0 < wmin)
    (hcv : ∀ v, wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v) (v : Fin d → ℝ) :
    Nform M r ω v ≤ 8 / wmin * ∑ i, v i ^ 2 := by
  have h := hcv ((Wr r ω)ᵀ *ᵥ v)
  rw [Wr, quad_transpose_W_mulVec (empCov_transpose _)] at h
  have h2 := dotProduct_diagonal_le_two_mul (kappa_le_two (empCov (yt r ω))) v
  rw [Nform, Wr, div_mul_eq_mul_div, le_div_iff₀ hwmin]
  linarith

/-- The squared entries of row `l` of `B` sum to `N(e_l)`. -/
theorem sum_sq_Bm_row (M : Mixture k d) (hS : M.S.PosSemidef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (l : Fin d) :
    ∑ i, Bm M r ω l i ^ 2 = Nform M r ω (Pi.single l 1) := by
  rw [Nform_eq_sum_sq M hS, mulVec_single_one]
  rfl

/-- **The entries of `B`**: `B_{lk}² ≤ N(e_l) ≤ 8 / wmin` under CV1. -/
theorem sq_Bm_apply_le {M : Mixture k d} (hS : M.S.PosSemidef) {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin : ℝ} (hwmin : 0 < wmin)
    (hcv : ∀ v, wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v) (l i : Fin d) :
    Bm M r ω l i ^ 2 ≤ 8 / wmin := by
  have h1 : Bm M r ω l i ^ 2 ≤ ∑ i', Bm M r ω l i' ^ 2 :=
    single_le_sum (f := fun i' ↦ Bm M r ω l i' ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i)
  have h2 := Nform_le hwmin hcv (Pi.single l 1)
  have h3 : ∑ i', (Pi.single l (1 : ℝ) : Fin d → ℝ) i' ^ 2 = 1 := by
    rw [sum_eq_single l (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp
  rw [h3, mul_one, ← sum_sq_Bm_row M hS] at h2
  exact h1.trans h2

/-- `|B_{lk}| ≤ 3 / √wmin` under CV1. -/
theorem abs_Bm_apply_le {M : Mixture k d} (hS : M.S.PosSemidef) {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin : ℝ} (hwmin : 0 < wmin)
    (hcv : ∀ v, wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v) (l i : Fin d) :
    |Bm M r ω l i| ≤ 3 / Real.sqrt wmin := by
  have h := sq_Bm_apply_le hS hwmin hcv l i
  have hs := Real.sq_sqrt hwmin.le
  have hs0 := Real.sqrt_pos.mpr hwmin
  rw [le_div_iff₀ hs0]
  rw [le_div_iff₀ hwmin] at h
  have ht : (|Bm M r ω l i| * Real.sqrt wmin) ^ 2 ≤ 8 := by
    rw [mul_pow, sq_abs, hs]
    exact h
  nlinarith [abs_nonneg (Bm M r ω l i), mul_nonneg (abs_nonneg (Bm M r ω l i)) hs0.le]

/-- **The columns of `B`** have `ℓ₁` norm `∑_l |B_{lk}| ≤ 3 (d + 1) / √wmin` under CV1 (these are
the coefficients of the linear form `φ_k(v) = (Bᵀv)_k`). -/
theorem sum_abs_Bm_col_le {M : Mixture k d} (hS : M.S.PosSemidef) {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin : ℝ} (hwmin : 0 < wmin)
    (hcv : ∀ v, wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v) (i : Fin d) :
    ∑ l, |Bm M r ω l i| ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
  have hs0 := Real.sqrt_pos.mpr hwmin
  calc ∑ l, |Bm M r ω l i| ≤ ∑ _l : Fin d, 3 / Real.sqrt wmin :=
        sum_le_sum fun l _ ↦ abs_Bm_apply_le hS hwmin hcv l i
    _ = (d : ℝ) * (3 / Real.sqrt wmin) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hs0]
        linarith

/-- **The rows of `B`** have `ℓ₁` norm `∑_k |B_{lk}| ≤ 3 (d + 1) / √wmin` under CV1. -/
theorem sum_abs_Bm_row_le {M : Mixture k d} (hS : M.S.PosSemidef) {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {wmin : ℝ} (hwmin : 0 < wmin)
    (hcv : ∀ v, wmin / 4 * quad M.S v ≤ quad (empCov (yt r ω)) v) (l : Fin d) :
    ∑ i, |Bm M r ω l i| ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
  have hs0 := Real.sqrt_pos.mpr hwmin
  calc ∑ i, |Bm M r ω l i| ≤ ∑ _i : Fin d, 3 / Real.sqrt wmin :=
        sum_le_sum fun i _ ↦ abs_Bm_apply_le hS hwmin hcv l i
    _ = (d : ℝ) * (3 / Real.sqrt wmin) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 3 * ((d : ℝ) + 1) / Real.sqrt wmin := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hs0]
        linarith

end BS23.Separating
