module

public import BGHKLMM26.SDP
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vectors with a given Gram matrix

For a positive definite matrix `A`, the vectors `wₖ = ∑_{l<k} cₖₗ wₗ + √Dₖ eₖ` in `ℝⁿ`, with
`cₖ = A_{<k}⁻¹ aₖ` (the column above the diagonal, `aₖ`, solved against the leading block) and
`Dₖ = Aₖₖ - aₖ·cₖ > 0`, have Gram matrix `A` (`BGHKLMM26.Factor.inner_vec`). For a standard
Gaussian `g`, `ξₖ = ⟨wₖ, g⟩ = ∑_{l<k} cₖₗ ξₗ + √Dₖ gₖ`, which a machine computes one coordinate
at a time.

The coefficients come from the positive definiteness test of the sum-of-squares solver
(`SoS.PDTest`): `cₖ = adj(B) b / det B` and `Dₖ = s / det B` for the leading block `B`, its column
`b` and Schur complement `s` (`BGHKLMM26.Factor.pdtest_spec`).
-/

@[expose] public section

namespace BGHKLMM26.Factor

open Real Finset
open scoped RealInnerProductSpace

/-! ### Vectors from coefficients -/

section Vectors

variable {n : ℕ} (c : ℕ → ℕ → ℝ) (D : ℕ → ℝ)

/-- The unit vector `eₖ` of `ℝⁿ` (`0` past `n`). -/
noncomputable def unitVec (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if h : k < n then EuclideanSpace.single ⟨k, h⟩ 1 else 0

/-- `wₖ = ∑_{l<k} cₖₗ wₗ + √Dₖ eₖ`. -/
noncomputable def vec : ℕ → EuclideanSpace ℝ (Fin n)
  | k => ∑ l : Fin k, c k l • vec l + √(D k) • unitVec k
decreasing_by exact l.2

theorem vec_eq (k : ℕ) :
    vec (n := n) c D k = ∑ l ∈ range k, c k l • vec c D l + √(D k) • unitVec k := by
  rw [vec, ← Fin.sum_univ_eq_sum_range (fun l ↦ c k l • vec (n := n) c D l)]

theorem inner_unitVec (k : ℕ) (g : EuclideanSpace ℝ (Fin n)) :
    ⟪unitVec k, g⟫ = if h : k < n then g ⟨k, h⟩ else 0 := by
  unfold unitVec
  split_ifs with h
  · simp [EuclideanSpace.inner_single_left]
  · simp

/-- `wₖ` has no coordinates past `k`. -/
theorem vec_apply_eq_zero {k : ℕ} {m : Fin n} (hm : k < m) : vec c D k m = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [vec_eq]
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_zero fun l hl ↦ by
      rw [ih l (Finset.mem_range.1 hl) ((Finset.mem_range.1 hl).trans hm), mul_zero]]
    simp only [unitVec, zero_add]
    split_ifs with h
    · simp [Fin.ext_iff, (Nat.ne_of_lt hm).symm]
    · simp

theorem inner_unitVec_vec {k j : ℕ} (hj : j < k) : ⟪unitVec (n := n) k, vec c D j⟫ = 0 := by
  rw [inner_unitVec]
  split_ifs with h
  · exact vec_apply_eq_zero c D (m := ⟨k, h⟩) hj
  · rfl

theorem inner_unitVec_self {k : ℕ} (hk : k < n) : ⟪unitVec (n := n) k, unitVec k⟫ = 1 := by
  rw [inner_unitVec, dite_eq_left hk, unitVec, dite_eq_left hk]
  simp

/-- **The Gram matrix.** If `cₖ` solves `∑_{l<k} Aⱼₗ cₖₗ = Aⱼₖ` for `j < k` and
`Dₖ = Aₖₖ - ∑_{l<k} Aₖₗ cₖₗ ≥ 0`, then `⟨wᵢ, wⱼ⟩ = Aᵢⱼ`. -/
theorem inner_vec (A : ℕ → ℕ → ℝ) (hA : ∀ i j, A i j = A j i)
    (hc : ∀ k < n, ∀ j < k, ∑ l ∈ range k, A j l * c k l = A j k)
    (hD : ∀ k < n, D k = A k k - ∑ l ∈ range k, A k l * c k l) (hD0 : ∀ k < n, 0 ≤ D k) :
    ∀ i j, i < n → j < n → ⟪vec (n := n) c D i, vec c D j⟫ = A i j := by
  -- By strong induction on `max i j`; the case `j ≤ i` suffices by symmetry.
  suffices h : ∀ i, i < n → ∀ j ≤ i, ⟪vec (n := n) c D i, vec c D j⟫ = A i j by
    intro i j hi hj
    rcases le_total j i with hji | hij
    · exact h i hi j hji
    · rw [real_inner_comm, h j hj i hij, hA]
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi j hji
    have hlow : ∀ l < i, ∀ m < i, ⟪vec (n := n) c D l, vec c D m⟫ = A l m := by
      intro l hl m hm
      rcases le_total m l with hml | hlm
      · exact ih l hl (hl.trans hi) m hml
      · rw [real_inner_comm, ih m hm (hm.trans hi) l hlm, hA]
    rcases lt_or_eq_of_le hji with hj | rfl
    · -- `j < i`: `⟨wᵢ, wⱼ⟩ = ∑ cᵢₗ Aₗⱼ = Aⱼᵢ`.
      rw [vec_eq, inner_add_left, inner_smul_left, inner_unitVec_vec c D hj, mul_zero, add_zero,
        sum_inner]
      simp only [inner_smul_left, conj_trivial]
      rw [show ∑ l ∈ range i, c i l * ⟪vec (n := n) c D l, vec c D j⟫ =
          ∑ l ∈ range i, A j l * c i l from Finset.sum_congr rfl fun l hl ↦ by
            rw [hlow l (Finset.mem_range.1 hl) j hj, hA, mul_comm],
        hc i hi j hj, hA]
    · -- `j = i`: `⟨wᵢ, wᵢ⟩ = cᵢ·Bcᵢ + Dᵢ = cᵢ·aᵢ + Dᵢ = Aᵢᵢ`.
      set S := ∑ l ∈ range j, c j l • vec (n := n) c D l with hS
      have hSS : ⟪S, S⟫ = ∑ l ∈ range j, A j l * c j l := by
        rw [hS, sum_inner]
        refine Finset.sum_congr rfl fun l hl ↦ ?_
        have hl' := Finset.mem_range.1 hl
        rw [inner_smul_left, inner_sum, conj_trivial]
        simp only [inner_smul_right]
        rw [show ∑ m ∈ range j, c j m * ⟪vec (n := n) c D l, vec c D m⟫ =
            ∑ m ∈ range j, A l m * c j m from Finset.sum_congr rfl fun m hm ↦ by
              rw [hlow l hl' m (Finset.mem_range.1 hm), mul_comm],
          hc j hi l hl', hA, mul_comm]
      have hSe : ⟪S, unitVec (n := n) j⟫ = 0 := by
        rw [hS, sum_inner]
        refine Finset.sum_eq_zero fun l hl ↦ ?_
        rw [inner_smul_left, real_inner_comm, inner_unitVec_vec c D (Finset.mem_range.1 hl),
          mul_zero]
      rw [vec_eq, ← hS, inner_add_left, inner_add_right, inner_add_right, hSS, inner_smul_right,
        hSe, mul_zero, add_zero, inner_smul_left, inner_smul_left, inner_smul_right,
        real_inner_comm, hSe, inner_unitVec_self hi, conj_trivial, mul_zero, zero_add, mul_one,
        ← Real.sqrt_mul (hD0 j hi), Real.sqrt_mul_self (hD0 j hi), hD j hi]
      ring

/-- **`ξₖ = ⟨wₖ, g⟩` is computed one coordinate at a time**: `ξₖ = ∑_{l<k} cₖₗ ξₗ + √Dₖ gₖ`. -/
theorem inner_vec_eq {k : ℕ} (hk : k < n) (g : EuclideanSpace ℝ (Fin n)) :
    ⟪vec (n := n) c D k, g⟫ = ∑ l ∈ range k, c k l * ⟪vec c D l, g⟫ + √(D k) * g ⟨k, hk⟩ := by
  rw [vec_eq, inner_add_left, sum_inner, inner_smul_left, inner_unitVec, dite_eq_left hk]
  simp only [inner_smul_left, conj_trivial]

/-! ### Bounds on the coefficients -/

open Matrix

theorem sum_fin_ite_mem {s : Finset ℕ} (hs : s ⊆ range n) (f : ℕ → ℝ) :
    ∑ i : Fin n, (if (i : ℕ) ∈ s then f i else 0) = ∑ i ∈ s, f i := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i ∈ s then f i else 0), Finset.sum_ite_mem,
    Finset.inter_eq_right.2 hs]

/-- If the Gram matrix of `v` is at least `λ I`, then `‖∑ aᵢ vᵢ‖² ≥ λ ∑ aᵢ²`. -/
theorem norm_sq_sum_ge {v : ℕ → EuclideanSpace ℝ (Fin n)} {A : Matrix (Fin n) (Fin n) ℝ}
    (hgram : ∀ i j : Fin n, ⟪v i, v j⟫ = A i j) {lam : ℝ}
    (hquad : ∀ a : Fin n → ℝ, lam * ∑ i, a i ^ 2 ≤ a ⬝ᵥ A *ᵥ a) {s : Finset ℕ}
    (hs : s ⊆ range n) (a : ℕ → ℝ) : lam * ∑ i ∈ s, a i ^ 2 ≤ ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
  set a' : Fin n → ℝ := fun i ↦ if (i : ℕ) ∈ s then a i else 0 with ha'
  have h1 : ∑ i, a' i ^ 2 = ∑ i ∈ s, a i ^ 2 := by
    rw [← sum_fin_ite_mem hs]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [ha']
    split_ifs <;> simp
  have hrow : ∀ i : Fin n, (A *ᵥ a') i = ∑ j ∈ s, a j * ⟪v i, v j⟫ := by
    intro i
    rw [mulVec, dotProduct, ← sum_fin_ite_mem hs (fun j ↦ a j * ⟪v i, v j⟫)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [ha']
    split_ifs
    · rw [hgram]; ring
    · ring
  have h2 : a' ⬝ᵥ A *ᵥ a' = ‖∑ i ∈ s, a i • v i‖ ^ 2 := by
    have e1 : a' ⬝ᵥ A *ᵥ a' = ∑ i ∈ s, a i * ∑ j ∈ s, a j * ⟪v i, v j⟫ := by
      rw [dotProduct, ← sum_fin_ite_mem hs (fun i ↦ a i * ∑ j ∈ s, a j * ⟪v i, v j⟫)]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hrow]
      simp only [ha']
      split_ifs <;> ring
    rw [e1, ← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_smul_left, inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [real_inner_smul_right]
  rw [← h1, ← h2]
  exact hquad a'

/-- `Dₖ ≤ ‖wₖ‖²`: `wₖ` is `√Dₖ eₖ` plus a vector orthogonal to `eₖ`. -/
theorem diag_le_norm_sq {k : ℕ} (hk : k < n) (hD : 0 ≤ D k) : D k ≤ ‖vec (n := n) c D k‖ ^ 2 := by
  set S := ∑ l ∈ range k, c k l • vec (n := n) c D l with hS
  have hSe : ⟪S, √(D k) • unitVec (n := n) k⟫ = 0 := by
    rw [hS, sum_inner]
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm,
      inner_unitVec_vec c D (Finset.mem_range.1 hl), mul_zero, mul_zero]
  have he : ‖√(D k) • unitVec (n := n) k‖ ^ 2 = D k := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hD, ← real_inner_self_eq_norm_sq,
      inner_unitVec_self hk, mul_one]
  rw [vec_eq, ← hS, norm_add_sq_real, hSe, he]
  nlinarith [sq_nonneg ‖S‖]

/-- **The coefficients are bounded** when the Gram matrix is at least `λ I`:
`λ (1 + ∑_{l<k} cₖₗ²) ≤ Dₖ`, since `wₖ - ∑ cₖₗ wₗ = √Dₖ eₖ`. -/
theorem coef_sq_le {A : Matrix (Fin n) (Fin n) ℝ}
    (hgram : ∀ i j : Fin n, ⟪vec (n := n) c D i, vec c D j⟫ = A i j) {lam : ℝ}
    (hquad : ∀ a : Fin n → ℝ, lam * ∑ i, a i ^ 2 ≤ a ⬝ᵥ A *ᵥ a) {k : ℕ} (hk : k < n)
    (hD : 0 ≤ D k) : lam * (1 + ∑ l ∈ range k, c k l ^ 2) ≤ D k := by
  set a : ℕ → ℝ := fun i ↦ if i = k then 1 else -c k i with ha
  have hs : insert k (range k) ⊆ range n := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact Finset.mem_range.2 hk
    · exact Finset.mem_range.2 ((Finset.mem_range.1 hi).trans hk)
  have hnot : k ∉ range k := by simp
  have h := norm_sq_sum_ge hgram hquad hs a
  have hsum : ∑ i ∈ insert k (range k), a i • vec (n := n) c D i = √(D k) • unitVec k := by
    rw [Finset.sum_insert hnot]
    have : ∑ i ∈ range k, a i • vec (n := n) c D i = -∑ l ∈ range k, c k l • vec c D l := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      simp only [ha, ite_eq_right (Finset.mem_range.1 hi).ne, neg_smul]
    rw [this, vec_eq c D k]
    simp only [ha, ↓reduceIte, one_smul]
    abel
  have hsq : ∑ i ∈ insert k (range k), a i ^ 2 = 1 + ∑ l ∈ range k, c k l ^ 2 := by
    rw [Finset.sum_insert hnot]
    simp only [ha, ↓reduceIte, one_pow]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [ite_eq_right (Finset.mem_range.1 hi).ne, neg_sq]
  have he : ‖√(D k) • unitVec (n := n) k‖ ^ 2 = D k := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hD, ← real_inner_self_eq_norm_sq,
      inner_unitVec_self hk, mul_one]
  rw [hsum, he, hsq] at h
  exact h

end Vectors

/-! ### The coefficients from the positive definiteness test -/

section PDTest

open Matrix SoS.PDTest

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)

/-- The entries of `A` on indices below `n` (`0` past `n`). -/
noncomputable def entry (i j : ℕ) : ℝ := if h : i < n ∧ j < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- `cₖₗ = (adj(B) b)ₗ / det B` for the leading block `B` of size `k` and the column `b`
above `Aₖₖ`. -/
noncomputable def coef (k l : ℕ) : ℝ :=
  if h : k < n ∧ l < k then cof (leadBlock A ⟨k, h.1⟩) ⟨l, h.2⟩ / (lead (leadBlock A ⟨k, h.1⟩)).det
  else 0

/-- `Dₖ = s / det B`, for the Schur complement `s = Aₖₖ det B - bᵀ adj(B) b`. -/
noncomputable def diagD (k : ℕ) : ℝ :=
  if h : k < n then schur (leadBlock A ⟨k, h⟩) / (lead (leadBlock A ⟨k, h⟩)).det else 0

variable {A}

theorem lead_leadBlock_apply (k : Fin n) (i j : Fin k) :
    lead (leadBlock A k) i j = A ⟨i, by omega⟩ ⟨j, by omega⟩ := rfl

theorem col_leadBlock_apply (k : Fin n) (i : Fin k) :
    SoS.PDTest.col (leadBlock A k) i = A ⟨i, by omega⟩ k := rfl

theorem leadBlock_last (k : Fin n) : leadBlock A k (Fin.last k) (Fin.last k) = A k k := rfl

theorem posDef_leadBlock (hA : A.PosDef) (k : Fin n) : (leadBlock A k).PosDef :=
  hA.submatrix (Fin.castLE_injective _)

theorem posDef_lead_leadBlock (hA : A.PosDef) (k : Fin n) : (lead (leadBlock A k)).PosDef :=
  (posDef_leadBlock hA k).submatrix (Fin.castSucc_injective _)

theorem det_lead_pos (hA : A.PosDef) (k : Fin n) : 0 < (lead (leadBlock A k)).det :=
  (posDef_lead_leadBlock hA k).det_pos

/-- `B u = det B · b`. -/
theorem lead_mulVec_cof (k : Fin n) :
    lead (leadBlock A k) *ᵥ cof (leadBlock A k) =
      (lead (leadBlock A k)).det • SoS.PDTest.col (leadBlock A k) := by
  simp only [cof, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]

/-- The Schur complement of a positive definite matrix is positive. -/
theorem schur_pos (hA : A.PosDef) (hAs : Aᵀ = A) (k : Fin n) : 0 < schur (leadBlock A k) := by
  set L := leadBlock A k
  have hLs : Lᵀ = L := by simp [L, leadBlock, transpose_submatrix, hAs]
  have hL := posDef_leadBlock hA k
  have hd := det_lead_pos hA k
  set d := (lead L).det
  set u := cof L
  set b := SoS.PDTest.col L
  have hBs : (lead L)ᵀ = lead L := by rw [transpose_submatrix, hLs]
  have hBu : lead L *ᵥ u = d • b := lead_mulVec_cof k
  have huBu : u ⬝ᵥ lead L *ᵥ u = d * (b ⬝ᵥ u) := by
    rw [hBu, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  have hv : witness L ≠ 0 := by
    intro h
    have := congrFun h (Fin.last k)
    simp only [witness, Fin.snoc_last, Pi.zero_apply] at this
    exact hd.ne' this
  have hpos := hL.dotProduct_mulVec_pos hv
  simp only [star_trivial] at hpos
  rw [witness, quad_snoc hLs] at hpos
  have : -u ⬝ᵥ lead L *ᵥ -u = d * (b ⬝ᵥ u) := by
    rw [mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, huBu]
  rw [this, dotProduct_neg] at hpos
  have hs : schur L = L (Fin.last k) (Fin.last k) * d - b ⬝ᵥ u := rfl
  rw [hs]
  have : 0 < d * (L (Fin.last k) (Fin.last k) * d - b ⬝ᵥ u) := by nlinarith
  exact pos_of_mul_pos_right this hd.le

/-- **The coefficients solve the leading blocks**: `∑_{l<k} Aⱼₗ cₖₗ = Aⱼₖ` for `j < k`. -/
theorem sum_entry_coef (hA : A.PosDef) {k : ℕ} (hk : k < n) {j : ℕ} (hj : j < k) :
    ∑ l ∈ Finset.range k, entry A j l * coef A k l = entry A j k := by
  have hd := det_lead_pos hA ⟨k, hk⟩
  have hjn : j < n := hj.trans hk
  set L := leadBlock A ⟨k, hk⟩
  have h := congrFun (lead_mulVec_cof (A := A) ⟨k, hk⟩) ⟨j, hj⟩
  rw [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
  rw [← Fin.sum_univ_eq_sum_range (fun l ↦ entry A j l * coef A k l)]
  have hterm : ∀ l : Fin k, entry A j l * coef A k l =
      lead L ⟨j, hj⟩ l * cof L l / (lead L).det := by
    intro l
    simp only [entry, coef, dite_eq_left (show j < n ∧ (l : ℕ) < n from ⟨hjn, l.2.trans hk⟩),
      dite_eq_left (show k < n ∧ (l : ℕ) < k from ⟨hk, l.2⟩), mul_div_assoc]
    rfl
  rw [Finset.sum_congr rfl fun l _ ↦ hterm l, ← Finset.sum_div, h, mul_div_cancel_left₀ _ hd.ne',
    col_leadBlock_apply, entry, dite_eq_left ⟨hjn, hk⟩]

/-- **The Schur complement is `Dₖ`**: `Dₖ = Aₖₖ - ∑_{l<k} Aₖₗ cₖₗ`, for symmetric `A`. -/
theorem diagD_eq (hA : A.PosDef) (hAs : Aᵀ = A) {k : ℕ} (hk : k < n) :
    diagD A k = entry A k k - ∑ l ∈ Finset.range k, entry A k l * coef A k l := by
  have hd := det_lead_pos hA ⟨k, hk⟩
  set L := leadBlock A ⟨k, hk⟩
  rw [← Fin.sum_univ_eq_sum_range (fun l ↦ entry A k l * coef A k l)]
  have hterm : ∀ l : Fin k, entry A k l * coef A k l =
      SoS.PDTest.col L l * cof L l / (lead L).det := by
    intro l
    have hsym : A ⟨k, hk⟩ ⟨l, l.2.trans hk⟩ = A ⟨l, l.2.trans hk⟩ ⟨k, hk⟩ := by
      rw [← transpose_apply A, hAs]
    simp only [entry, coef, dite_eq_left (show k < n ∧ (l : ℕ) < n from ⟨hk, l.2.trans hk⟩),
      dite_eq_left (show k < n ∧ (l : ℕ) < k from ⟨hk, l.2⟩), mul_div_assoc, hsym]
    rfl
  rw [Finset.sum_congr rfl fun l _ ↦ hterm l, ← Finset.sum_div, diagD, dite_eq_left hk, schur,
    entry, dite_eq_left ⟨hk, hk⟩, sub_div, mul_div_cancel_right₀ _ hd.ne', dotProduct]
  rfl

theorem diagD_pos (hA : A.PosDef) (hAs : Aᵀ = A) {k : ℕ} (hk : k < n) : 0 < diagD A k := by
  rw [diagD, dite_eq_left hk]
  exact div_pos (schur_pos hA hAs ⟨k, hk⟩) (det_lead_pos hA ⟨k, hk⟩)

/-- **The vectors of a positive definite matrix**: `⟨wᵢ, wⱼ⟩ = Aᵢⱼ`. -/
theorem inner_vec_pd (hA : A.PosDef) (hAs : Aᵀ = A) {i j : ℕ} (hi : i < n) (hj : j < n) :
    ⟪vec (n := n) (coef A) (diagD A) i, vec (coef A) (diagD A) j⟫ = A ⟨i, hi⟩ ⟨j, hj⟩ := by
  have h := inner_vec (n := n) (coef A) (diagD A) (entry A) (fun i j ↦ by
      unfold entry
      split_ifs with h1 h2 h2
      · rw [← transpose_apply A, hAs]
      · exact absurd ⟨h1.2, h1.1⟩ h2
      · exact absurd ⟨h2.2, h2.1⟩ h1
      · rfl)
    (fun k hk j hj ↦ sum_entry_coef hA hk hj) (fun k hk ↦ diagD_eq hA hAs hk)
    (fun k hk ↦ (diagD_pos hA hAs hk).le) i j hi hj
  rw [h, entry, dite_eq_left ⟨hi, hj⟩]

end PDTest

/-! ### Rescaling the moments -/

section Rescale

open Matrix

/-- The largest diagonal moment, at least `0`. -/
def smax (n : ℕ) (M : ℕ → ℕ → ℚ) : ℚ := ((List.range n).map fun i ↦ M i i).foldr max 0

theorem le_foldr_max {l : List ℚ} {x : ℚ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {l : List ℚ} {b : ℚ} (hb : 0 ≤ b) (h : ∀ x ∈ l, x ≤ b) :
    l.foldr max 0 ≤ b := by
  induction l with
  | nil => simpa using hb
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun x hx ↦ h x (List.mem_cons_of_mem _ hx))

theorem le_smax {n : ℕ} {M : ℕ → ℕ → ℚ} {i : ℕ} (hi : i < n) : M i i ≤ smax n M :=
  le_foldr_max (List.mem_map_of_mem (f := fun i ↦ M i i) (List.mem_range.2 hi))

theorem smax_nonneg (n : ℕ) (M : ℕ → ℕ → ℚ) : 0 ≤ smax n M := by
  unfold smax
  induction (List.range n).map fun i ↦ M i i with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons]; exact ih.trans (le_max_right _ _)

theorem smax_le {n : ℕ} {M : ℕ → ℕ → ℚ} {b : ℚ} (hb : 0 ≤ b) (h : ∀ i < n, M i i ≤ b) :
    smax n M ≤ b :=
  foldr_max_le hb fun x hx ↦ by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact h i (List.mem_range.1 hi)

/-- The rescaled moments: `1` on the diagonal, `Mᵢⱼ / (s + τ)` off it, for `s` the largest
diagonal moment. Adding `s - Mᵢᵢ + τ` to the diagonal and dividing by `s + τ` keeps a positive
semidefinite `M` positive definite. -/
def rescaled (n : ℕ) (M : ℕ → ℕ → ℚ) (τ : ℚ) (i j : ℕ) : ℚ :=
  if i = j then 1 else M i j / (smax n M + τ)

/-- The rescaled moments as a real matrix. -/
noncomputable def toMat {n : ℕ} (f : ℕ → ℕ → ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (f i j : ℝ)

theorem rescaled_symm {n : ℕ} {M : ℕ → ℕ → ℚ} (hM : ∀ i j, M i j = M j i) (τ : ℚ) :
    (toMat (n := n) (rescaled n M τ))ᵀ = toMat (rescaled n M τ) := by
  ext i j
  simp only [transpose_apply, toMat, rescaled, hM j i]
  by_cases h : (j : ℕ) = i
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- **The rescaled moments are at least `τ / (s + τ)` times the identity.** -/
theorem rescaled_quad_ge {n : ℕ} {M : ℕ → ℕ → ℚ}
    (hpsd : ∀ a : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * (M i j : ℝ)) {τ : ℚ}
    (hτ : 0 < τ) (a : Fin n → ℝ) :
    (τ : ℝ) / (smax n M + τ) * ∑ i, a i ^ 2 ≤ a ⬝ᵥ toMat (rescaled n M τ) *ᵥ a := by
  set S : ℝ := smax n M + τ with hS
  have hs0 : (0 : ℝ) ≤ smax n M := by exact_mod_cast smax_nonneg n M
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hSpos : 0 < S := by rw [hS]; linarith
  have hquad : a ⬝ᵥ toMat (rescaled n M τ) *ᵥ a =
      ((∑ i : Fin n, ∑ j : Fin n, a i * a j * (M i j : ℝ)) +
        ∑ i : Fin n, (S - M i i) * a i ^ 2) / S := by
    simp only [dotProduct, mulVec, toMat, rescaled, Finset.mul_sum]
    rw [eq_div_iff hSpos.ne', Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_mul, ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
      ← Finset.sum_erase_add (s := Finset.univ) (a := i) _ (Finset.mem_univ i)]
    rw [ite_eq_left rfl]
    have hoff : ∀ j ∈ Finset.univ.erase i, a i * (((if (i : ℕ) = j then (1 : ℚ)
        else M i j / (smax n M + τ) : ℚ) : ℝ) * a j) * S = a i * a j * M i j := by
      intro j hj
      have hij : (i : ℕ) ≠ j := fun h ↦ (Finset.ne_of_mem_erase hj) (Fin.ext h.symm)
      rw [ite_eq_right hij]
      push_cast
      rw [hS]
      field_simp
    rw [Finset.sum_congr rfl hoff]
    push_cast
    ring
  rw [hquad, le_div_iff₀ hSpos]
  have hdiag : ∀ i : Fin n, (τ : ℝ) * a i ^ 2 ≤ (S - M i i) * a i ^ 2 := by
    intro i
    have : (M i i : ℝ) ≤ smax n M := by exact_mod_cast le_smax i.2
    nlinarith [sq_nonneg (a i)]
  have h1 := hpsd a
  have h2 : ∑ i : Fin n, (τ : ℝ) * a i ^ 2 ≤ ∑ i : Fin n, (S - M i i) * a i ^ 2 :=
    Finset.sum_le_sum fun i _ ↦ hdiag i
  rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hSpos.ne', Finset.mul_sum]
  linarith

/-- **The rescaled moments are positive definite.** -/
theorem rescaled_posDef {n : ℕ} {M : ℕ → ℕ → ℚ} (hM : ∀ i j, M i j = M j i)
    (hpsd : ∀ a : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, a i * a j * (M i j : ℝ)) {τ : ℚ}
    (hτ : 0 < τ) :
    (toMat (n := n) (rescaled n M τ)).PosDef := by
  refine Ellipsoid.posDef_of_quad (rescaled_symm hM τ) fun a ha ↦ ?_
  have hs0 : (0 : ℝ) ≤ smax n M := by exact_mod_cast smax_nonneg n M
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  have hsum : 0 < ∑ i, a i ^ 2 :=
    lt_of_lt_of_le (by positivity : 0 < a i ^ 2)
      (Finset.single_le_sum (f := fun i ↦ a i ^ 2) (fun j _ ↦ by positivity) (Finset.mem_univ i))
  exact lt_of_lt_of_le (by positivity) (rescaled_quad_ge hpsd hτ a)

end Rescale

/-! ### From the solver's output to the vectors of the analysis -/

section FromSoS

open SDP GW

theorem pairExp_comm (n i j : ℕ) : pairExp n i j = pairExp n j i := by
  unfold pairExp
  exact List.map_congr_left fun l _ ↦ add_comm _ _

theorem momentsOf_symm (n : ℕ) (out : SoS.Solver.RawPoly) (i j : ℕ) :
    momentsOf n out i j = momentsOf n out j i := by
  rw [momentsOf, momentsOf, pairExp_comm]

/-- The matrix of the analysis: the rescaled moments of the solver's output. -/
noncomputable def sosMat (I : Instance) (out : SoS.Solver.RawPoly) (τ : ℚ) :
    Matrix (Fin I.1) (Fin I.1) ℝ := toMat (rescaled I.1 (momentsOf I.1 out) τ)

/-- The vectors of the analysis. -/
noncomputable def sosVec (I : Instance) (out : SoS.Solver.RawPoly) (τ : ℚ) :
    ℕ → EuclideanSpace ℝ (Fin I.1) :=
  vec (coef (sosMat I out τ)) (diagD (sosMat I out τ))

/-- **The vectors of the analysis, from the solver** [BGHKLMM26, Section 3]: unit vectors whose
Gram matrix is the rescaled moments, with the triangle inequalities up to `1/20` and SDP value at
least `opt - γ - (2(η + γ) + τ) W`. -/
theorem sosVec_spec {I : Instance} (hI : Valid I) {η γ τ : ℚ} (hη : 0 < η) (hγ : 0 < γ)
    (hτ : 0 < τ) (he : η + γ ≤ 1 / 1000) (hτ1 : τ ≤ 1 / 1000) {out : SoS.Solver.RawPoly}
    (hc : SoS.Solver.Correct (problem I) η γ out) :
    (∀ i < I.1, ‖sosVec I out τ i‖ = 1) ∧
    (∀ i j, i < I.1 → j < I.1 →
      ⟪sosVec I out τ i, sosVec I out τ j⟫ = rescaled I.1 (momentsOf I.1 out) τ i j) ∧
    Triangle (sosVec I out τ) I.1 (1 / 20) ∧
    opt I - γ - (2 * ((η : ℝ) + γ) + τ) * totalWeight I ≤ sdp (sosVec I out τ) I := by
  obtain ⟨hpsd, hdiag, htri, hval⟩ := correct_spec hI hη hγ hc
  set M := momentsOf I.1 out with hMdef
  set e : ℝ := (η : ℝ) + γ with hedef
  have he' : e ≤ 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).2 he
    push_cast at this
    rw [hedef]; exact this
  have he0 : 0 ≤ e := by rw [hedef]; positivity
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  have hτ1r : (τ : ℝ) ≤ 1 / 1000 := by
    have := (Rat.cast_le (K := ℝ)).2 hτ1
    push_cast at this
    exact this
  have hpd := rescaled_posDef (n := I.1) (fun i j ↦ momentsOf_symm I.1 out i j) hpsd hτ
  have hsym := rescaled_symm (n := I.1) (fun i j ↦ momentsOf_symm I.1 out i j) τ
  have hgram : ∀ i j, i < I.1 → j < I.1 →
      ⟪sosVec I out τ i, sosVec I out τ j⟫ = rescaled I.1 M τ i j := by
    intro i j hi hj
    exact inner_vec_pd hpd hsym hi hj
  have hunit : ∀ i < I.1, ‖sosVec I out τ i‖ = 1 := by
    intro i hi
    have h := hgram i i hi hi
    rw [rescaled, ite_eq_left rfl, real_inner_self_eq_norm_sq] at h
    push_cast at h
    nlinarith [norm_nonneg (sosVec I out τ i)]
  -- `S = s + τ`, with `s` the largest diagonal moment, is within `2e + τ` of `1`.
  set S : ℝ := smax I.1 M + τ with hSdef
  have hs_up : (smax I.1 M : ℝ) ≤ 1 + 2 * e := by
    have : smax I.1 M ≤ 1 + 2 * (η + γ) :=
      smax_le (by positivity) fun i hi ↦ by
        have := (abs_le.1 (hdiag i hi)).2
        have h2 : ((M i i : ℚ) : ℝ) ≤ ((1 + 2 * (η + γ) : ℚ) : ℝ) := by
          push_cast; rw [← hedef]; linarith
        exact (Rat.cast_le (K := ℝ)).1 h2
    have h3 := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h3
    rw [hedef]; exact h3
  have hs_lo : ∀ i < I.1, 1 - 2 * e ≤ (smax I.1 M : ℝ) := fun i hi ↦ by
    have h1 := (abs_le.1 (hdiag i hi)).1
    have h2 : (M i i : ℝ) ≤ smax I.1 M := by exact_mod_cast le_smax hi
    linarith
  have hoff : ∀ i j, i ≠ j → (rescaled I.1 M τ i j : ℝ) = M i j / S := by
    intro i j hij
    rw [rescaled, ite_eq_right hij]
    push_cast
    rfl
  refine ⟨hunit, hgram, ?_, ?_⟩
  · -- The triangle inequalities, divided by `S`.
    intro i j k hi hj hk hij hik hjk b b'
    have hS : 1 - 2 * e ≤ S := by have := hs_lo i hi; rw [hSdef]; linarith
    have hSpos : 0 < S := by linarith
    rw [hgram i j hi hj, hgram i k hi hk, hgram j k hj hk, hoff i j hij, hoff i k hik,
      hoff j k hjk]
    have h := htri i j k hi hj hk hij hik hjk b b'
    have h' : (bsign b * M i j + bsign b' * M i k - bsign b * bsign b' * M j k) / S ≤
        (1 + 4 * e) / S := by
      apply div_le_div_of_nonneg_right _ hSpos.le
      linarith
    have h1 : (1 + 4 * e) / S ≤ 1 + 1 / 20 := by
      rw [div_le_iff₀ hSpos]
      nlinarith
    have : (bsign b * M i j + bsign b' * M i k - bsign b * bsign b' * M j k) / S =
        bsign b * (M i j / S) + bsign b' * (M i k / S) - bsign b * bsign b' * (M j k / S) := by
      field_simp
    linarith
  · -- The SDP value: each term moves by at most `(2e + τ) w`.
    unfold sdp totalWeight
    have hterm : ∀ c ∈ I.2, (c.2.2 : ℝ) * ((1 + bsign c.2.1 * M c.1.1 c.1.2) / 2) -
        (2 * e + τ) * c.2.2 ≤ sdpTerm (sosVec I out τ) c := by
      intro c hc
      obtain ⟨hij, hj, hw⟩ := hI.1 c hc
      have hi : c.1.1 < I.1 := hij.trans hj
      have hw' : (0 : ℝ) ≤ c.2.2 := by exact_mod_cast hw
      have hS : 1 - 2 * e ≤ S := by have := hs_lo _ hi; rw [hSdef]; linarith
      have hSpos : 0 < S := by linarith
      have hS1 : |1 - S| ≤ 2 * e + τ := by
        rw [abs_le]; constructor <;> (rw [hSdef]; linarith [hs_lo _ hi])
      have hρ : rho (sosVec I out τ) c.1.1 c.1.2 c.2.1 = bsign c.2.1 * (M c.1.1 c.1.2 / S) := by
        rw [rho, hgram _ _ hi hj, hoff _ _ hij.ne]
      -- `|M_ij / S| ≤ 1` by Cauchy–Schwarz on unit vectors.
      have hcs : |(M c.1.1 c.1.2 : ℝ) / S| ≤ 1 := by
        have := abs_real_inner_le_norm (sosVec I out τ c.1.1) (sosVec I out τ c.1.2)
        rw [hgram _ _ hi hj, hoff _ _ hij.ne, hunit _ hi, hunit _ hj, one_mul] at this
        exact this
      have hdiff : |bsign c.2.1 * (M c.1.1 c.1.2 : ℝ) - bsign c.2.1 * (M c.1.1 c.1.2 / S)| ≤
          2 * e + τ := by
        have hb : |bsign c.2.1| = 1 := by rcases bsign_cases c.2.1 with h | h <;> rw [h] <;> simp
        rw [← mul_sub, abs_mul, hb, one_mul,
          show (M c.1.1 c.1.2 : ℝ) - M c.1.1 c.1.2 / S = M c.1.1 c.1.2 / S * (S - 1) by
            field_simp, abs_mul, abs_sub_comm]
        calc |(M c.1.1 c.1.2 : ℝ) / S| * |1 - S| ≤ 1 * (2 * e + τ) :=
              mul_le_mul hcs hS1 (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
      unfold sdpTerm
      rw [hρ]
      have h2 := (abs_le.1 hdiff).2
      have : (c.2.2 : ℝ) * ((1 + bsign c.2.1 * M c.1.1 c.1.2) / 2) - (2 * e + τ) * c.2.2 ≤
          (c.2.2 : ℝ) * ((1 + bsign c.2.1 * (M c.1.1 c.1.2 / S)) / 2) := by
        have : (1 + bsign c.2.1 * (M c.1.1 c.1.2 : ℝ)) / 2 - (2 * e + τ) ≤
            (1 + bsign c.2.1 * (M c.1.1 c.1.2 / S)) / 2 := by
          have h0 : 0 ≤ 2 * e + τ := by positivity
          linarith
        have := mul_le_mul_of_nonneg_left this hw'
        linarith
      exact this
    have hsum := List.sum_le_sum (l := I.2) hterm
    rw [list_sum_map_sub] at hsum
    rw [show ((I.2.map fun c ↦ (2 * e + τ) * (c.2.2 : ℝ)).sum) =
        (2 * e + τ) * (I.2.map fun c ↦ (c.2.2 : ℝ)).sum from List.sum_map_mul_left _ _ _] at hsum
    linarith

/-- **The coefficients of the solver's vectors are bounded**: `0 < Dₖ ≤ 1` and
`∑_{l<k} cₖₗ² ≤ 2/τ`, because the rescaled moments are at least `τ/(s + τ)` times the
identity. -/
theorem sosVec_coef {I : Instance} (hI : Valid I) {η γ τ : ℚ} (hη : 0 < η) (hγ : 0 < γ)
    (hτ : 0 < τ) (he : η + γ ≤ 1 / 1000) (hτ1 : τ ≤ 1 / 1000) {out : SoS.Solver.RawPoly}
    (hc : SoS.Solver.Correct (problem I) η γ out) {k : ℕ} (hk : k < I.1) :
    0 < diagD (sosMat I out τ) k ∧ diagD (sosMat I out τ) k ≤ 1 ∧
      ∑ l ∈ Finset.range k, coef (sosMat I out τ) k l ^ 2 ≤ 2 / τ := by
  obtain ⟨hpsd, hdiag, -, -⟩ := correct_spec hI hη hγ hc
  obtain ⟨hunit, -, -, -⟩ := sosVec_spec hI hη hγ hτ he hτ1 hc
  have hpd := rescaled_posDef (n := I.1) (fun i j ↦ momentsOf_symm I.1 out i j) hpsd hτ
  have hsym := rescaled_symm (n := I.1) (fun i j ↦ momentsOf_symm I.1 out i j) τ
  have hD := diagD_pos hpd hsym hk
  have hgram : ∀ i j : Fin I.1, ⟪sosVec I out τ i, sosVec I out τ j⟫ = sosMat I out τ i j :=
    fun i j ↦ inner_vec_pd hpd hsym i.2 j.2
  have hquad := rescaled_quad_ge (n := I.1) hpsd hτ
  have h1 := coef_sq_le _ _ hgram hquad hk hD.le
  have h2 := diag_le_norm_sq (coef (sosMat I out τ)) (diagD (sosMat I out τ)) hk hD.le
  have hu : ‖sosVec I out τ k‖ = 1 := hunit k hk
  rw [sosVec] at hu
  rw [hu, one_pow] at h2
  refine ⟨hD, h2, ?_⟩
  -- `s + τ ≤ 2`.
  have hs : smax I.1 (momentsOf I.1 out) ≤ 1 + 2 * (η + γ) :=
    smax_le (by positivity) fun i hi ↦ by
      have h := (abs_le.1 (hdiag i hi)).2
      have h' : ((momentsOf I.1 out i i : ℚ) : ℝ) ≤ ((1 + 2 * (η + γ) : ℚ) : ℝ) := by
        push_cast; linarith
      exact (Rat.cast_le (K := ℝ)).1 h'
  have hS : smax I.1 (momentsOf I.1 out) + τ ≤ 2 := by linarith
  have hS' : ((smax I.1 (momentsOf I.1 out) : ℚ) : ℝ) + τ ≤ 2 := by exact_mod_cast hS
  have hs0 : (0 : ℝ) ≤ smax I.1 (momentsOf I.1 out) := by exact_mod_cast smax_nonneg _ _
  have hτr : (0 : ℝ) < τ := by exact_mod_cast hτ
  set S : ℝ := smax I.1 (momentsOf I.1 out) + τ
  have hSpos : 0 < S := by positivity
  have h3 : (τ : ℝ) / S * (1 + ∑ l ∈ Finset.range k, coef (sosMat I out τ) k l ^ 2) ≤ 1 :=
    h1.trans h2
  rw [div_mul_eq_mul_div, div_le_one hSpos] at h3
  rw [le_div_iff₀ hτr]
  have hsq : 0 ≤ ∑ l ∈ Finset.range k, coef (sosMat I out τ) k l ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

end FromSoS

end BGHKLMM26.Factor
