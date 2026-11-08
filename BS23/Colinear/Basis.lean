module

public import BS23.Colinear.Alg
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The `C`-orthogonal basis and the selection step

Facts about the steps 2–4 of the colinear-means algorithm (`BS23/Colinear/Alg.lean`).

* **The basis.** For a positive definite `C`, the vectors `λᵢ = BS23.Colinear.basisVec C i` are
  `C`-orthogonal (`BS23.Colinear.basisVec_orth`), have `λᵢᵀ C λᵢ > 0`
  (`BS23.Colinear.quad_basisVec_pos`) and form a basis (`BS23.Colinear.basisVec_linearIndependent`).
  The key fact is that the leading block `C_{[i]}` maps `λᵢ` (restricted to its support, the first
  `i + 1` coordinates) to `det C_{[i]} eᵢ`; so `(C λᵢ)ⱼ = 0` for `j < i`, and
  `λᵢᵀ C λᵢ = det C_{[i]} · det C_{[i-1]}` is a product of two leading principal minors.
* **The direction.** `BS23.Colinear.direction C g = C⁻¹ g`
  (`BS23.Colinear.direction_eq`), and `∑ᵢ ⟨λᵢ, u⟩² / λᵢᵀCλᵢ = uᵀ C⁻¹ u`
  (`BS23.Colinear.sum_sq_div_quad_basisVec`); so some `i` has `⟨λᵢ, u⟩² / λᵢᵀCλᵢ ≥ uᵀ C⁻¹ u / d`
  (`BS23.Colinear.exists_le_sq_div_quad_basisVec`).
* **Selection.** `BS23.Colinear.selectBest` returns a candidate `(m, i)` (`3 ≤ m ≤ M`) of maximal
  score (`BS23.Colinear.selectBest_spec`), and returns one whenever there is a candidate
  (`BS23.Colinear.selectBest_isSome`).
* **Scaling.** `BS23.Colinear.quad_smul`: `(cv)ᵀ C (cv) = c² vᵀ C v`.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix

variable {d : ℕ}

/-! ### Generalities on the quadratic form -/

section Field

variable {K : Type*} [Field K]

theorem quad_smul (C : Matrix (Fin d) (Fin d) K) (c : K) (v : Fin d → K) :
    quad C (c • v) = c ^ 2 * quad C v := by
  simp only [quad, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end Field

/-- A real positive definite matrix equals its transpose. -/
theorem transpose_eq_of_posDef {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) : Cᵀ = C := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hC.isHermitian.eq

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem dotProduct_mulVec_comm {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) (x y : Fin d → ℝ) :
    x ⬝ᵥ (C *ᵥ y) = y ⬝ᵥ (C *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hC]

theorem quad_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) {v : Fin d → ℝ} (hv : v ≠ 0) :
    0 < quad C v := by
  simpa [quad] using hC.dotProduct_mulVec_pos hv

theorem quad_nonneg {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosSemidef) (v : Fin d → ℝ) :
    0 ≤ quad C v := by
  simpa [quad] using hC.dotProduct_mulVec_nonneg v

theorem mulVec_inv_mulVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (u : Fin d → ℝ) :
    C *ᵥ (C⁻¹ *ᵥ u) = u := by
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det C).mp hC.isUnit), one_mulVec]

theorem inv_mulVec_mulVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (u : Fin d → ℝ) :
    C⁻¹ *ᵥ (C *ᵥ u) = u := by
  rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det C).mp hC.isUnit), one_mulVec]

/-! ### The leading blocks and the basis vectors -/

/-- The leading blocks of a positive definite matrix are positive definite. -/
theorem lead_posDef {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    (lead C i).PosDef :=
  hC.submatrix (Fin.castLE_injective _)

theorem det_lead_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    0 < (lead C i).det :=
  (lead_posDef hC i).det_pos

theorem basisVec_of_lt (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : i < j) :
    basisVec C i j = 0 := by
  simp [basisVec, not_le.mpr (Fin.lt_def.mp h)]

/-- `C_{[i]}` maps `λᵢ` to `det C_{[i]} eᵢ`: `(C λᵢ)ⱼ = [j = i] det C_{[i]}` for `j ≤ i`. -/
theorem mulVec_basisVec_of_le (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : j ≤ i) :
    (C *ᵥ basisVec C i) j = if j = i then (lead C i).det else 0 := by
  have hj : j.val < i.val + 1 := Nat.lt_succ_of_le h
  have hsum : (C *ᵥ basisVec C i) j =
      (lead C i * (lead C i).adjugate) ⟨j.val, hj⟩ (Fin.last i) := by
    simp only [mulVec, dotProduct]
    symm
    refine Fintype.sum_of_injective (Fin.castLE i.isLt) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro k hk
      have : ¬ k.val ≤ i.val := by
        intro hk'
        exact hk ⟨⟨k.val, Nat.lt_succ_of_le hk'⟩, Fin.ext rfl⟩
      simp [basisVec, this]
    · intro k
      have hk : (Fin.castLE i.isLt k).val ≤ i.val := Nat.le_of_lt_succ k.isLt
      simp only [basisVec, hk, dite_true, lead, submatrix_apply]
      congr 2
  rw [hsum, mul_adjugate, Matrix.smul_apply, smul_eq_mul]
  by_cases hji : j = i
  · subst hji
    have : (⟨j.val, hj⟩ : Fin (j + 1)) = Fin.last j := Fin.ext rfl
    rw [this, Matrix.one_apply_eq, mul_one]
    simp
  · have : (⟨j.val, hj⟩ : Fin (i + 1)) ≠ Fin.last i := by
      intro h'
      exact hji (Fin.ext (by simpa [Fin.ext_iff] using h'))
    simp [Matrix.one_apply_ne this, hji]

theorem mulVec_basisVec_of_lt (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : j < i) :
    (C *ᵥ basisVec C i) j = 0 := by
  simp [mulVec_basisVec_of_le C h.le, h.ne]

theorem mulVec_basisVec_self (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    (C *ᵥ basisVec C i) i = (lead C i).det := by
  simp [mulVec_basisVec_of_le C le_rfl]

/-- The diagonal entry `(λᵢ)ᵢ` is the previous leading principal minor `det C_{[i-1]}`. -/
theorem basisVec_self (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    basisVec C i i = ((lead C i).submatrix Fin.castSucc Fin.castSucc).det := by
  have h : (⟨i.val, Nat.lt_succ_of_le le_rfl⟩ : Fin (i + 1)) = Fin.last i := Fin.ext rfl
  simp only [basisVec, le_refl, dite_true, h]
  rw [adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp [← two_mul, pow_mul]

theorem basisVec_self_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    0 < basisVec C i i := by
  rw [basisVec_self]
  exact ((lead_posDef hC i).submatrix (Fin.castSucc_injective _)).det_pos

/-- `λᵢᵀ C λᵢ = det C_{[i]} · (λᵢ)ᵢ`. -/
theorem quad_basisVec (C : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    quad C (basisVec C i) = (lead C i).det * basisVec C i i := by
  unfold quad
  rw [dotProduct, Finset.sum_eq_single i, mulVec_basisVec_self, mul_comm]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [mulVec_basisVec_of_lt C hlt, mul_zero]
    · rw [basisVec_of_lt C hgt, zero_mul]
  · simp

theorem quad_basisVec_pos {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    0 < quad C (basisVec C i) := by
  rw [quad_basisVec]
  exact mul_pos (det_lead_pos hC i) (basisVec_self_pos hC i)

theorem quad_basisVec_ne_zero {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (i : Fin d) :
    quad C (basisVec C i) ≠ 0 :=
  (quad_basisVec_pos hC i).ne'

theorem basisVec_orth_of_lt (C : Matrix (Fin d) (Fin d) ℝ) {i j : Fin d} (h : i < j) :
    basisVec C i ⬝ᵥ (C *ᵥ basisVec C j) = 0 := by
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases le_or_gt k i with hki | hki
  · rw [mulVec_basisVec_of_lt C (lt_of_le_of_lt hki h), mul_zero]
  · rw [basisVec_of_lt C hki, zero_mul]

/-- **`C`-orthogonality** of the basis vectors. -/
theorem basisVec_orth {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C) {i j : Fin d} (h : i ≠ j) :
    basisVec C i ⬝ᵥ (C *ᵥ basisVec C j) = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact basisVec_orth_of_lt C hlt
  · rw [dotProduct_mulVec_comm hC]
    exact basisVec_orth_of_lt C hgt

/-- Pairing a combination of the basis vectors with `C λⱼ` picks out its `j`-th coefficient. -/
theorem sum_smul_basisVec_dotProduct {C : Matrix (Fin d) (Fin d) ℝ} (hC : Cᵀ = C)
    (g : Fin d → ℝ) (j : Fin d) :
    (∑ i, g i • basisVec C i) ⬝ᵥ (C *ᵥ basisVec C j) = g j * quad C (basisVec C j) := by
  rw [sum_dotProduct, Finset.sum_eq_single j]
  · rw [smul_dotProduct, smul_eq_mul, quad]
  · intro i _ hij
    rw [smul_dotProduct, basisVec_orth hC hij, smul_zero]
  · simp

/-- The basis vectors are linearly independent. -/
theorem basisVec_linearIndependent {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) :
    LinearIndependent ℝ (basisVec C) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := sum_smul_basisVec_dotProduct (transpose_eq_of_posDef hC) g j
  rw [hg, zero_dotProduct] at h
  exact (mul_eq_zero.mp h.symm).resolve_right (quad_basisVec_ne_zero hC j)

/-- The basis vectors span `ℝ^d`. -/
theorem span_basisVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) :
    Submodule.span ℝ (Set.range (basisVec C)) = ⊤ :=
  (basisVec_linearIndependent hC).span_eq_top_of_card_eq_finrank' (by simp)

/-- The expansion of a vector in the `C`-orthogonal basis:
`w = ∑ᵢ (⟨λᵢ, C w⟩ / λᵢᵀCλᵢ) λᵢ`. -/
theorem eq_sum_basisVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (w : Fin d → ℝ) :
    w = ∑ i, ((basisVec C i ⬝ᵥ (C *ᵥ w)) / quad C (basisVec C i)) • basisVec C i := by
  have hT := transpose_eq_of_posDef hC
  obtain ⟨α, hα'⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    ((span_basisVec hC).symm ▸ Submodule.mem_top : w ∈ Submodule.span ℝ (Set.range (basisVec C)))
  have hw : w = ∑ i, α i • basisVec C i := hα'.symm
  have hα : ∀ j, α j = (basisVec C j ⬝ᵥ (C *ᵥ w)) / quad C (basisVec C j) := by
    intro j
    rw [eq_div_iff (quad_basisVec_ne_zero hC j), dotProduct_mulVec_comm hT, hw,
      sum_smul_basisVec_dotProduct hT]
  conv_lhs => rw [hw]
  simp only [hα]

/-- **The direction** is `C⁻¹ g`. -/
theorem direction_eq {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef) (g : Fin d → ℝ) :
    direction C g = C⁻¹ *ᵥ g := by
  rw [eq_sum_basisVec hC (C⁻¹ *ᵥ g), mulVec_inv_mulVec hC]
  rfl

/-- `∑ᵢ ⟨λᵢ, u⟩² / λᵢᵀCλᵢ = uᵀ C⁻¹ u`. -/
theorem sum_sq_div_quad_basisVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (u : Fin d → ℝ) :
    ∑ i, (basisVec C i ⬝ᵥ u) ^ 2 / quad C (basisVec C i) = u ⬝ᵥ (C⁻¹ *ᵥ u) := by
  conv_rhs => rw [eq_sum_basisVec hC (C⁻¹ *ᵥ u), mulVec_inv_mulVec hC]
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dotProduct_smul, smul_eq_mul, dotProduct_comm u]
  ring

/-- Some basis vector carries a `1/d` share of `uᵀ C⁻¹ u`. -/
theorem exists_le_sq_div_quad_basisVec {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    (hd : 0 < d) (u : Fin d → ℝ) :
    ∃ i, u ⬝ᵥ (C⁻¹ *ᵥ u) / d ≤ (basisVec C i ⬝ᵥ u) ^ 2 / quad C (basisVec C i) := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le hne (f := fun _ ↦ u ⬝ᵥ (C⁻¹ *ᵥ u) / d)
    (g := fun i ↦ (basisVec C i ⬝ᵥ u) ^ 2 / quad C (basisVec C i)) (by
      rw [sum_sq_div_quad_basisVec hC, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd.ne')])
  exact ⟨i, hi⟩

/-! ### Selection -/

section Select

variable {K : Type*} [LinearOrder K]

theorem argmaxFrom_spec {α : Type*} (f : α → K) (l : List α) (b : α) :
    argmaxFrom f l b ∈ b :: l ∧ ∀ q ∈ b :: l, f q ≤ f (argmaxFrom f l b) := by
  induction l generalizing b with
  | nil => simp [argmaxFrom]
  | cons a l ih =>
    obtain ⟨hmem, hmax⟩ := ih (if f b < f a then a else b)
    simp only [argmaxFrom]
    have hb : f b ≤ f (if f b < f a then a else b) := by
      split_ifs with h
      · exact h.le
      · exact le_rfl
    have ha : f a ≤ f (if f b < f a then a else b) := by
      split_ifs with h
      · exact le_rfl
      · exact not_lt.mp h
    refine ⟨?_, ?_⟩
    · rcases List.mem_cons.mp hmem with h | h
      · rw [h]; split_ifs <;> simp
      · simp [h]
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hb.trans (hmax _ List.mem_cons_self)
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ha.trans (hmax _ List.mem_cons_self)
      · exact hmax q (List.mem_cons_of_mem _ hq)

variable [Field K]

theorem mem_candidates {M : ℕ} {m : ℕ} {i : Fin d} :
    (m, i) ∈ candidates M d ↔ 3 ≤ m ∧ m ≤ M := by
  simp only [candidates, List.mem_flatMap, List.mem_range'_1, List.mem_map, List.mem_finRange,
    true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨m', hm', i', rfl, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨m, by omega, i, rfl, rfl⟩

theorem candidates_ne_nil {M : ℕ} (hM : 3 ≤ M) (hd : 1 ≤ d) : candidates M d ≠ [] :=
  List.ne_nil_of_mem (mem_candidates (i := ⟨0, hd⟩).mpr ⟨le_rfl, hM⟩)

/-- `BS23.Colinear.selectBest` returns a candidate of maximal score. -/
theorem selectBest_spec {n M : ℕ} {Y : Fin n → Fin d → K} {p : ℕ × Fin d}
    (h : selectBest M Y = some p) :
    p ∈ candidates M d ∧ ∀ q ∈ candidates M d, score Y q ≤ score Y p := by
  unfold selectBest at h
  split at h
  · cases h
  · rename_i b l hl
    cases h
    rw [hl]
    exact argmaxFrom_spec (score Y) l b

theorem selectBest_isSome {n M : ℕ} (Y : Fin n → Fin d → K) (h : candidates M d ≠ []) :
    ∃ p, selectBest M Y = some p := by
  unfold selectBest
  split
  · contradiction
  · exact ⟨_, rfl⟩

end Select

end BS23.Colinear
