module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Residuals against a family of vectors

For a family `f : ι → ℝ^n` whose Gram matrix `G = (fᵢ ⬝ fⱼ)` is invertible, the residual of a
vector `y` (`BHSV25.Net.resid`) is `y` minus its orthogonal projection `∑ᵢ cᵢ fᵢ` onto the span of
the family, with `c = G⁻¹ (fᵢ ⬝ y)ᵢ`. These are the quantities of Gram–Schmidt, written without
square roots, as the greedy net of `BHSV25/Net/Greedy.lean` uses them:

* the residual is orthogonal to the family and differs from `y` by a combination of it
  (`BHSV25.Net.col_dotProduct_resid`), it is the shortest such vector
  (`BHSV25.Net.resid_dotProduct_self_le`) and the only one orthogonal to the family
  (`BHSV25.Net.eq_resid`), and it is linear in `y` (`BHSV25.Net.residL`);
* adding a vector `y` to the family multiplies the Gram determinant by the squared length of its
  residual (`BHSV25.Net.det_gramF_snocF`), does not lengthen residuals
  (`BHSV25.Net.resid_snocF_le`), and changes them by one Gram–Schmidt step
  (`BHSV25.Net.resid_snocF`);
* residuals do not change when the family is scaled or reindexed (`BHSV25.Net.resid_smul_family`,
  `BHSV25.Net.resid_comp_equiv`).

Families of columns indexed by lists, `BHSV25.Net.colsL`, are reindexed to families on
`Fin L.length ⊕ Unit` when a column is appended (`BHSV25.Net.det_gramF_colsL_append`,
`BHSV25.Net.resid_colsL_append`).
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix

variable {n : ℕ} {ι : Type*} [Fintype ι]

theorem dot_self_nonneg (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Fintype.sum_nonneg fun i ↦ mul_self_nonneg (v i)

/-! ### Definitions -/

/-- The Gram matrix `(fᵢ ⬝ fⱼ)` of a family of vectors. -/
def gramF (f : ι → Fin n → ℝ) : Matrix ι ι ℝ := Matrix.of fun i j ↦ f i ⬝ᵥ f j

/-- The combination `∑ᵢ cᵢ fᵢ`. -/
def combF (f : ι → Fin n → ℝ) (c : ι → ℝ) : Fin n → ℝ := ∑ i, c i • f i

variable [DecidableEq ι] in
/-- The coefficients `G⁻¹ (fᵢ ⬝ y)ᵢ` of the projection of `y` onto the span of the family. -/
noncomputable def coefF (f : ι → Fin n → ℝ) (y : Fin n → ℝ) : ι → ℝ :=
  (gramF f)⁻¹ *ᵥ fun i ↦ f i ⬝ᵥ y

variable [DecidableEq ι] in
/-- The **residual** of `y`: `y` minus its orthogonal projection onto the span of the family
(when the Gram determinant is not `0`). -/
noncomputable def resid (f : ι → Fin n → ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  y - combF f (coefF f y)

/-! ### Combinations -/

theorem combF_dotProduct (f : ι → Fin n → ℝ) (c : ι → ℝ) (y : Fin n → ℝ) :
    combF f c ⬝ᵥ y = ∑ i, c i * (f i ⬝ᵥ y) := by
  simp only [combF, sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem dotProduct_combF (f : ι → Fin n → ℝ) (c : ι → ℝ) (y : Fin n → ℝ) :
    y ⬝ᵥ combF f c = ∑ i, c i * (y ⬝ᵥ f i) := by
  rw [dotProduct_comm, combF_dotProduct]
  simp only [dotProduct_comm]

theorem combF_add (f : ι → Fin n → ℝ) (c d : ι → ℝ) :
    combF f (c + d) = combF f c + combF f d := by
  simp only [combF, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem combF_sub (f : ι → Fin n → ℝ) (c d : ι → ℝ) :
    combF f (c - d) = combF f c - combF f d := by
  simp only [combF, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem combF_smul (f : ι → Fin n → ℝ) (a : ℝ) (c : ι → ℝ) :
    combF f (a • c) = a • combF f c := by
  simp only [combF, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem combF_single [DecidableEq ι] (f : ι → Fin n → ℝ) (i : ι) :
    combF f (Pi.single i 1) = f i := by
  simp only [combF]
  rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj])
    (fun h ↦ absurd (Finset.mem_univ i) h)]
  simp

theorem gramF_mulVec (f : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι) :
    (gramF f *ᵥ c) i = f i ⬝ᵥ combF f c := by
  rw [dotProduct_combF]
  simp only [mulVec, dotProduct, gramF, of_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

/-! ### The residual -/

variable [DecidableEq ι] (f : ι → Fin n → ℝ)

theorem resid_add_combF (y : Fin n → ℝ) : resid f y + combF f (coefF f y) = y := by
  simp [resid]

theorem isUnit_det_gramF {f : ι → Fin n → ℝ} (hdet : (gramF f).det ≠ 0) : IsUnit (gramF f).det :=
  isUnit_iff_ne_zero.2 hdet

/-- **The residual is orthogonal to the family.** -/
theorem col_dotProduct_resid (hdet : (gramF f).det ≠ 0) (y : Fin n → ℝ) (i : ι) :
    f i ⬝ᵥ resid f y = 0 := by
  rw [resid, dotProduct_sub, ← gramF_mulVec, coefF, mulVec_mulVec,
    mul_nonsing_inv _ (isUnit_det_gramF hdet), one_mulVec, sub_self]

theorem combF_dotProduct_resid (hdet : (gramF f).det ≠ 0) (c : ι → ℝ) (y : Fin n → ℝ) :
    combF f c ⬝ᵥ resid f y = 0 := by
  rw [combF_dotProduct]
  simp [col_dotProduct_resid f hdet]

theorem resid_dotProduct_combF (hdet : (gramF f).det ≠ 0) (c : ι → ℝ) (y : Fin n → ℝ) :
    resid f y ⬝ᵥ combF f c = 0 := by
  rw [dotProduct_comm, combF_dotProduct_resid f hdet]

/-- Inner products with a residual only see the residual. -/
theorem dotProduct_resid_eq (hdet : (gramF f).det ≠ 0) (y z : Fin n → ℝ) :
    z ⬝ᵥ resid f y = resid f z ⬝ᵥ resid f y := by
  conv_lhs => rw [← resid_add_combF f z]
  rw [add_dotProduct, combF_dotProduct_resid f hdet, add_zero]

theorem coefF_combF (hdet : (gramF f).det ≠ 0) (c : ι → ℝ) : coefF f (combF f c) = c := by
  have h : (fun i ↦ f i ⬝ᵥ combF f c) = gramF f *ᵥ c := funext fun i ↦ (gramF_mulVec f c i).symm
  rw [coefF, h, mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_gramF hdet), one_mulVec]

theorem resid_combF (hdet : (gramF f).det ≠ 0) (c : ι → ℝ) : resid f (combF f c) = 0 := by
  rw [resid, coefF_combF f hdet, sub_self]

/-- The vectors of the family have residual `0`. -/
theorem resid_col (hdet : (gramF f).det ≠ 0) (i : ι) : resid f (f i) = 0 := by
  rw [← combF_single f i, resid_combF f hdet]

theorem coefF_add (y z : Fin n → ℝ) : coefF f (y + z) = coefF f y + coefF f z := by
  have h : (fun i ↦ f i ⬝ᵥ (y + z)) = (fun i ↦ f i ⬝ᵥ y) + fun i ↦ f i ⬝ᵥ z :=
    funext fun i ↦ dotProduct_add _ _ _
  rw [coefF, h, mulVec_add, ← coefF, ← coefF]

theorem coefF_smul (a : ℝ) (y : Fin n → ℝ) : coefF f (a • y) = a • coefF f y := by
  have h : (fun i ↦ f i ⬝ᵥ (a • y)) = a • fun i ↦ f i ⬝ᵥ y :=
    funext fun i ↦ by simp [dotProduct_smul]
  rw [coefF, h, mulVec_smul, ← coefF]

/-- The residual as a linear map. -/
noncomputable def residL : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun := resid f
  map_add' y z := by
    simp only [resid, coefF_add, combF_add]
    abel
  map_smul' a y := by
    simp only [resid, coefF_smul, combF_smul, RingHom.id_apply, smul_sub]

theorem resid_sum {κ : Type*} (s : Finset κ) (y : κ → Fin n → ℝ) :
    resid f (∑ k ∈ s, y k) = ∑ k ∈ s, resid f (y k) :=
  map_sum (residL f) y s

theorem resid_smul (a : ℝ) (y : Fin n → ℝ) : resid f (a • y) = a • resid f y :=
  (residL f).map_smul a y

/-- **The residual is the shortest** of the vectors `y - ∑ᵢ cᵢ fᵢ`. -/
theorem resid_dotProduct_self_le (hdet : (gramF f).det ≠ 0) (y : Fin n → ℝ) (c : ι → ℝ) :
    resid f y ⬝ᵥ resid f y ≤ (y - combF f c) ⬝ᵥ (y - combF f c) := by
  have h : y - combF f c = resid f y + combF f (coefF f y - c) := by
    rw [combF_sub, resid]
    abel
  rw [h, add_dotProduct, dotProduct_add, dotProduct_add, resid_dotProduct_combF f hdet,
    combF_dotProduct_resid f hdet]
  have := dot_self_nonneg (combF f (coefF f y - c))
  linarith

/-- **Uniqueness**: a vector orthogonal to the family that differs from `y` by a combination of
it is the residual of `y`. -/
theorem eq_resid (hdet : (gramF f).det ≠ 0) {y z : Fin n → ℝ} (hz : ∀ i, f i ⬝ᵥ z = 0)
    (c : ι → ℝ) (hc : y - z = combF f c) : z = resid f y := by
  have hd : resid f y - z = combF f (c - coefF f y) := by
    rw [combF_sub, ← hc, resid]
    abel
  have hdd : (resid f y - z) ⬝ᵥ (resid f y - z) = 0 := by
    have h1 : (resid f y - z) ⬝ᵥ (resid f y - z) =
        combF f (c - coefF f y) ⬝ᵥ (resid f y - z) := by rw [← hd]
    rw [h1, combF_dotProduct]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [dotProduct_sub, col_dotProduct_resid f hdet, hz i, sub_zero, mul_zero]
  have h0 := dotProduct_self_eq_zero.1 hdd
  exact (sub_eq_zero.1 h0).symm

/-! ### Scaling and reindexing -/

omit [Fintype ι] [DecidableEq ι] in
theorem gramF_smul_family (s : ℝ) : gramF (fun i ↦ s • f i) = (s * s) • gramF f := by
  ext i j
  simp only [gramF, of_apply, smul_dotProduct, dotProduct_smul, smul_eq_mul, Matrix.smul_apply]
  ring

theorem det_gramF_smul_family (s : ℝ) :
    (gramF fun i ↦ s • f i).det = (s * s) ^ Fintype.card ι * (gramF f).det := by
  rw [gramF_smul_family, det_smul]

/-- Scaling the family by `s ≠ 0` does not change residuals. -/
theorem resid_smul_family (hdet : (gramF f).det ≠ 0) {s : ℝ} (hs : s ≠ 0) (y : Fin n → ℝ) :
    resid (fun i ↦ s • f i) y = resid f y := by
  have hdet' : (gramF fun i ↦ s • f i).det ≠ 0 := by
    rw [det_gramF_smul_family]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hs hs)) hdet
  symm
  refine eq_resid _ hdet' (fun i ↦ ?_) (s⁻¹ • coefF f y) ?_
  · rw [smul_dotProduct, col_dotProduct_resid f hdet, smul_zero]
  · rw [resid, sub_sub_cancel]
    simp only [combF, Pi.smul_apply, smul_eq_mul, smul_smul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    field_simp

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem gramF_comp_equiv (e : κ ≃ ι) : gramF (f ∘ e) = reindex e.symm e.symm (gramF f) := by
  ext i j
  simp [gramF]

theorem det_gramF_comp_equiv (e : κ ≃ ι) : (gramF (f ∘ e)).det = (gramF f).det := by
  rw [gramF_comp_equiv, det_reindex_self]

/-- Reindexing the family does not change residuals. -/
theorem resid_comp_equiv (hdet : (gramF f).det ≠ 0) (e : κ ≃ ι) (y : Fin n → ℝ) :
    resid (f ∘ e) y = resid f y := by
  have hdet' : (gramF (f ∘ e)).det ≠ 0 := by rwa [det_gramF_comp_equiv]
  symm
  refine eq_resid _ hdet' (fun k ↦ col_dotProduct_resid f hdet y (e k)) (coefF f y ∘ e) ?_
  rw [resid, sub_sub_cancel, combF, combF]
  exact (Equiv.sum_comp e fun i ↦ coefF f y i • f i).symm

/-! ### Appending a vector -/

/-- The family `f` followed by the vector `y`. -/
def snocF (f : ι → Fin n → ℝ) (y : Fin n → ℝ) : ι ⊕ Unit → Fin n → ℝ := Sum.elim f fun _ ↦ y

omit [Fintype ι] [DecidableEq ι] in
theorem gramF_snocF (y : Fin n → ℝ) :
    gramF (snocF f y) = fromBlocks (gramF f) (Matrix.of fun i (_ : Unit) ↦ f i ⬝ᵥ y)
      (Matrix.of fun (_ : Unit) j ↦ y ⬝ᵥ f j) (Matrix.of fun _ _ ↦ y ⬝ᵥ y) := by
  ext (i | i) (j | j) <;> simp [gramF, snocF]

/-- **Adding a vector multiplies the Gram determinant by the squared length of its residual.** -/
theorem det_gramF_snocF (hdet : (gramF f).det ≠ 0) (y : Fin n → ℝ) :
    (gramF (snocF f y)).det = (gramF f).det * (resid f y ⬝ᵥ resid f y) := by
  have : Invertible (gramF f) := invertibleOfIsUnitDet _ (isUnit_det_gramF hdet)
  rw [gramF_snocF, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  congr 1
  rw [det_unique]
  have hr : resid f y ⬝ᵥ resid f y = y ⬝ᵥ y - y ⬝ᵥ combF f (coefF f y) := by
    rw [← dotProduct_resid_eq f hdet y y, resid, dotProduct_sub]
  have hsum : ∀ (g : ι → ℝ) (A : Matrix ι ι ℝ),
      ∑ j, (∑ i, g i * A i j) * g j = ∑ j, (A *ᵥ g) j * g j := by
    intro g A
    simp only [mulVec, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [hr, dotProduct_combF]
  simp only [Matrix.sub_apply, of_apply, Matrix.mul_apply]
  congr 1
  simp only [dotProduct_comm y]
  rw [hsum (fun i ↦ f i ⬝ᵥ y), coefF]

theorem det_gramF_snocF_ne_zero (hdet : (gramF f).det ≠ 0) {y : Fin n → ℝ}
    (hy : resid f y ≠ 0) : (gramF (snocF f y)).det ≠ 0 := by
  rw [det_gramF_snocF f hdet]
  exact mul_ne_zero hdet (fun h ↦ hy (dotProduct_self_eq_zero.1 h))

omit [DecidableEq ι] in
theorem combF_snocF (u : Fin n → ℝ) (c : ι → ℝ) (a : ℝ) :
    combF (snocF f u) (Sum.elim c fun _ ↦ a) = combF f c + a • u := by
  simp [combF, snocF, Fintype.sum_sum_type]

/-- **Adding a vector does not lengthen residuals.** -/
theorem resid_snocF_le {u : Fin n → ℝ} (hdet : (gramF (snocF f u)).det ≠ 0) (y : Fin n → ℝ) :
    resid (snocF f u) y ⬝ᵥ resid (snocF f u) y ≤ resid f y ⬝ᵥ resid f y := by
  have h := resid_dotProduct_self_le (snocF f u) hdet y (Sum.elim (coefF f y) fun _ ↦ 0)
  rwa [combF_snocF, zero_smul, add_zero, ← resid] at h

/-- **One Gram–Schmidt step**: adding `u`, with residual `r ≠ 0`, removes from the residual of `y`
its component along `r`. -/
theorem resid_snocF (hdet : (gramF f).det ≠ 0) {u : Fin n → ℝ} (hu : resid f u ≠ 0)
    (y : Fin n → ℝ) :
    resid (snocF f u) y = resid f y -
      ((resid f u ⬝ᵥ y) / (resid f u ⬝ᵥ resid f u)) • resid f u := by
  have hrr : resid f u ⬝ᵥ resid f u ≠ 0 := fun h ↦ hu (dotProduct_self_eq_zero.1 h)
  symm
  refine eq_resid _ (det_gramF_snocF_ne_zero f hdet hu) (fun k ↦ ?_)
    (Sum.elim (coefF f y - ((resid f u ⬝ᵥ y) / (resid f u ⬝ᵥ resid f u)) • coefF f u)
      fun _ ↦ (resid f u ⬝ᵥ y) / (resid f u ⬝ᵥ resid f u)) ?_
  · rcases k with i | i
    · simp only [snocF, Sum.elim_inl, dotProduct_sub, dotProduct_smul,
        col_dotProduct_resid f hdet, smul_zero, sub_zero]
    · simp only [snocF, Sum.elim_inr]
      have h1 : u ⬝ᵥ resid f y = resid f u ⬝ᵥ y := by
        rw [dotProduct_resid_eq f hdet y u, dotProduct_comm, ← dotProduct_resid_eq f hdet u y,
          dotProduct_comm]
      have h2 : u ⬝ᵥ resid f u = resid f u ⬝ᵥ resid f u := dotProduct_resid_eq f hdet u u
      rw [dotProduct_sub, dotProduct_smul, h1, h2, smul_eq_mul, div_mul_cancel₀ _ hrr, sub_self]
  · generalize (resid f u ⬝ᵥ y) / (resid f u ⬝ᵥ resid f u) = a
    rw [combF_snocF, combF_sub, combF_smul, resid, resid]
    simp only [smul_sub]
    abel

/-! ### Columns indexed by lists -/

/-- The columns `col L[0], …, col L[k - 1]` of a list `L` of indices. -/
def colsL (col : ℕ → Fin n → ℝ) (L : List ℕ) : Fin L.length → Fin n → ℝ := fun j ↦ col L[j]

/-- `Fin L.length ⊕ Unit` indexes `L ++ [u]`. -/
def appendEquiv (L : List ℕ) (u : ℕ) : Fin L.length ⊕ Unit ≃ Fin (L ++ [u]).length :=
  (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans
    (finSumFinEquiv.trans (finCongr (by simp)))

theorem colsL_append_comp (col : ℕ → Fin n → ℝ) (L : List ℕ) (u : ℕ) :
    colsL col (L ++ [u]) ∘ appendEquiv L u = snocF (colsL col L) (col u) := by
  funext k
  rcases k with j | j
  · simp [colsL, appendEquiv, snocF, List.getElem_append_left]
  · simp [colsL, appendEquiv, snocF]

theorem det_gramF_colsL_append (col : ℕ → Fin n → ℝ) (L : List ℕ) (u : ℕ) :
    (gramF (colsL col (L ++ [u]))).det = (gramF (snocF (colsL col L) (col u))).det := by
  rw [← colsL_append_comp, det_gramF_comp_equiv]

theorem resid_colsL_append (col : ℕ → Fin n → ℝ) (L : List ℕ) (u : ℕ)
    (hdet : (gramF (colsL col (L ++ [u]))).det ≠ 0) (y : Fin n → ℝ) :
    resid (colsL col (L ++ [u])) y = resid (snocF (colsL col L) (col u)) y := by
  rw [← colsL_append_comp, resid_comp_equiv _ hdet]

/-- The Gram determinant of the empty family is `1`. -/
theorem det_gramF_nil (col : ℕ → Fin n → ℝ) : (gramF (colsL col [])).det = 1 := by
  have : IsEmpty (Fin ([] : List ℕ).length) := by simp only [List.length_nil]; infer_instance
  exact Matrix.det_isEmpty

/-- The residual against the empty family is the vector itself. -/
theorem resid_nil (col : ℕ → Fin n → ℝ) (y : Fin n → ℝ) : resid (colsL col []) y = y := by
  simp [resid, combF]

end Net

end BHSV25
