module

public import BHSV25.Model

/-!
# Coordinates in an eigenbasis

The proofs behind the matrix part of the spectral toolkit (`BHSV25/Spectral/Basic.lean`), about a
symmetric real matrix `A` and the orthonormal basis `u₀, u₁, …` of eigenvectors that Mathlib
chooses (`Matrix.IsHermitian.eigenvectorBasis`).

The toolkit imports this file, so the definitions here (`BHSV25.Spectral.Impl.coeff`,
`BHSV25.Spectral.Impl.InEigSpan`, `BHSV25.Spectral.Impl.proj`) are copies of the toolkit's, and
definitionally equal to them; the toolkit's lemmas are proved by the ones here.

* `x = ∑ᵢ cᵢ uᵢ` with `cᵢ = ⟨uᵢ, x⟩`, so `⟨x, y⟩ = ∑ cᵢ(x) cᵢ(y)`, `‖x‖² = ∑ cᵢ²` and
  `xᵀ A x = ∑ μᵢ cᵢ²`.
* **Counting eigenvalues** (Courant–Fischer): if the only vector of the span of the eigenvectors
  with eigenvalues in `S` orthogonal to `r` given vectors is `0`, at most `r` eigenvalues lie in `S`
  (`BHSV25.Spectral.Impl.card_le_of_inEigSpan`).
-/

@[expose] public section

namespace BHSV25

namespace Spectral

namespace Impl

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℝ}

/-- The coefficient of `x` on the `i`-th eigenvector of `A`. -/
noncomputable def coeff (hA : A.IsHermitian) (i : ι) (x : ι → ℝ) : ℝ :=
  ⇑(hA.eigenvectorBasis i) ⬝ᵥ x

/-- `x` lies in the span of the eigenvectors of `A` whose eigenvalues satisfy `S`. -/
def InEigSpan (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) : Prop :=
  ∀ i, ¬ S (hA.eigenvalues i) → coeff hA i x = 0

open Classical in
/-- The orthogonal projection of `x` onto the span of the eigenvectors of `A` whose eigenvalues
satisfy `S`. -/
noncomputable def proj (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) : ι → ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ S (hA.eigenvalues i)), coeff hA i x • ⇑(hA.eigenvectorBasis i)

theorem coeff_eq_inner (hA : A.IsHermitian) (i : ι) (x : ι → ℝ) :
    coeff hA i x = inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 x) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [coeff, dotProduct_comm]

theorem sum_coeff_smul (hA : A.IsHermitian) (x : ι → ℝ) :
    ∑ i, coeff hA i x • ⇑(hA.eigenvectorBasis i) = x := by
  have h := congrArg WithLp.ofLp ((hA.eigenvectorBasis).sum_repr' (WithLp.toLp 2 x))
  simpa [coeff_eq_inner, WithLp.ofLp_sum] using h

theorem dotProduct_eq_sum_coeff (hA : A.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ y = ∑ i, coeff hA i x * coeff hA i y := by
  have h := (hA.eigenvectorBasis).sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  simp only [coeff_eq_inner]
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simp only [star_trivial] at h
  rw [dotProduct_comm, ← h]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [real_inner_comm]

theorem coeff_smul (hA : A.IsHermitian) (i : ι) (c : ℝ) (x : ι → ℝ) :
    coeff hA i (c • x) = c * coeff hA i x := by
  simp [coeff, dotProduct_smul]

theorem coeff_zero (hA : A.IsHermitian) (i : ι) : coeff hA i 0 = 0 :=
  dotProduct_zero _

theorem coeff_sum {κ : Type*} (hA : A.IsHermitian) (i : ι) (s : Finset κ) (x : κ → ι → ℝ) :
    coeff hA i (∑ k ∈ s, x k) = ∑ k ∈ s, coeff hA i (x k) :=
  dotProduct_sum _ _ _

theorem coeff_eigenvector (hA : A.IsHermitian) (i j : ι) :
    coeff hA i ⇑(hA.eigenvectorBasis j) = if i = j then 1 else 0 := by
  rw [coeff_eq_inner, WithLp.toLp_ofLp, OrthonormalBasis.inner_eq_ite]

theorem sum_coeff_sq (hA : A.IsHermitian) (x : ι → ℝ) : ∑ i, coeff hA i x ^ 2 = x ⬝ᵥ x := by
  rw [dotProduct_eq_sum_coeff hA x x]
  exact Finset.sum_congr rfl fun i _ ↦ sq _

theorem eq_of_coeff_eq (hA : A.IsHermitian) {x y : ι → ℝ} (h : ∀ i, coeff hA i x = coeff hA i y) :
    x = y := by
  rw [← sum_coeff_smul hA x, ← sum_coeff_smul hA y]
  simp only [h]

theorem eq_zero_of_coeff_eq_zero (hA : A.IsHermitian) {x : ι → ℝ} (h : ∀ i, coeff hA i x = 0) :
    x = 0 :=
  eq_of_coeff_eq hA fun i ↦ by rw [h i, coeff_zero]

theorem exists_coeff_ne_zero (hA : A.IsHermitian) {x : ι → ℝ} (hx : x ≠ 0) :
    ∃ i, coeff hA i x ≠ 0 := by
  by_contra h
  push Not at h
  exact hx (eq_zero_of_coeff_eq_zero hA h)

theorem coeff_mulVec (hA : A.IsHermitian) (i : ι) (x : ι → ℝ) :
    coeff hA i (A *ᵥ x) = hA.eigenvalues i * coeff hA i x := by
  have hs : Aᵀ = A := hA.isSymm
  rw [coeff, dotProduct_mulVec, ← mulVec_transpose, hs, hA.mulVec_eigenvectorBasis i,
    smul_dotProduct, smul_eq_mul, coeff]

theorem dotProduct_mulVec_eq (hA : A.IsHermitian) (x y : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = ∑ i, hA.eigenvalues i * coeff hA i x * coeff hA i y := by
  rw [dotProduct_eq_sum_coeff hA x (A *ᵥ y)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_mulVec]
  ring

theorem quad_eq (hA : A.IsHermitian) (x : ι → ℝ) :
    x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i * coeff hA i x ^ 2 := by
  rw [dotProduct_mulVec_eq hA x x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

theorem coeff_sum_smul_eigenvector (hA : A.IsHermitian) (i : ι) (s : Finset ι) (c : ι → ℝ) :
    coeff hA i (∑ j ∈ s, c j • ⇑(hA.eigenvectorBasis j)) = if i ∈ s then c i else 0 := by
  rw [coeff_sum]
  simp only [coeff_smul, coeff_eigenvector, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]

theorem coeff_proj (hA : A.IsHermitian) (S : ℝ → Prop) (i : ι) (x : ι → ℝ)
    [Decidable (S (hA.eigenvalues i))] :
    coeff hA i (proj hA S x) = if S (hA.eigenvalues i) then coeff hA i x else 0 := by
  classical
  rw [proj, coeff_sum_smul_eigenvector]
  by_cases h : S (hA.eigenvalues i) <;> simp [h]

theorem inEigSpan_proj (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) :
    InEigSpan hA S (proj hA S x) := by
  classical
  intro i hi
  rw [coeff_proj, ite_eq_right hi]

open Classical in
/-- **Courant–Fischer, counting form**: if the only vector in the span of the eigenvectors with
eigenvalues in `S` that is orthogonal to `w 0, …, w (r - 1)` is `0`, then at most `r` eigenvalues
(with multiplicity) lie in `S`. -/
theorem card_le_of_inEigSpan (hA : A.IsHermitian) (S : ℝ → Prop) {r : ℕ} (w : Fin r → ι → ℝ)
    (h : ∀ x, InEigSpan hA S x → (∀ j, w j ⬝ᵥ x = 0) → x = 0) :
    (Finset.univ.filter fun i ↦ S (hA.eigenvalues i)).card ≤ r := by
  set F := Finset.univ.filter fun i ↦ S (hA.eigenvalues i) with hF
  let u : ι → ι → ℝ := fun i ↦ ⇑(hA.eigenvectorBasis i)
  let M : Matrix (Fin r) F ℝ := fun j i ↦ w j ⬝ᵥ u i
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    let c' : ι → ℝ := fun i ↦ if hi : i ∈ F then c ⟨i, hi⟩ else 0
    let x : ι → ℝ := ∑ i ∈ F, c' i • u i
    have hcx : ∀ i, coeff hA i x = c' i := by
      intro i
      rw [coeff_sum_smul_eigenvector]
      by_cases hi : i ∈ F
      · rw [ite_eq_left hi]
      · rw [ite_eq_right hi]
        simp [c', hi]
    have hx : x = 0 := by
      refine h x (fun i hi ↦ ?_) (fun j ↦ ?_)
      · have : i ∉ F := by simpa [hF] using hi
        rw [hcx]
        simp [c', this]
      · have hj := congrFun hc j
        rw [Matrix.mulVecLin_apply, Pi.zero_apply] at hj
        simp only [x, dotProduct_sum, dotProduct_smul, smul_eq_mul]
        rw [← hj, Matrix.mulVec, dotProduct]
        rw [← Finset.sum_coe_sort F]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        simp [c', M, mul_comm]
    funext i
    have := hcx i
    rw [hx, coeff_zero] at this
    simpa [c'] using this.symm
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem quad_gt_of_inEigSpan (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (τ < ·) x) (hx : x ≠ 0) : τ * (x ⬝ᵥ x) < x ⬝ᵥ (A *ᵥ x) := by
  rw [quad_eq hA, ← sum_coeff_sq hA, Finset.mul_sum]
  obtain ⟨i₀, hi₀⟩ := exists_coeff_ne_zero hA hx
  have hle : ∀ i, τ * coeff hA i x ^ 2 ≤ hA.eigenvalues i * coeff hA i x ^ 2 := by
    intro i
    by_cases hi : τ < hA.eigenvalues i
    · exact mul_le_mul_of_nonneg_right hi.le (sq_nonneg _)
    · rw [h i hi]
      simp
  refine Finset.sum_lt_sum (fun i _ ↦ hle i) ⟨i₀, Finset.mem_univ _, ?_⟩
  have hμ : τ < hA.eigenvalues i₀ := by
    by_contra hμ
    exact hi₀ (h i₀ hμ)
  exact mul_lt_mul_of_pos_right hμ (by positivity)

theorem quad_le_of_inEigSpan (hA : A.IsHermitian) {τ : ℝ} {x : ι → ℝ}
    (h : InEigSpan hA (· ≤ τ) x) : x ⬝ᵥ (A *ᵥ x) ≤ τ * (x ⬝ᵥ x) := by
  rw [quad_eq hA, ← sum_coeff_sq hA, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  by_cases hi : hA.eigenvalues i ≤ τ
  · exact mul_le_mul_of_nonneg_right hi (sq_nonneg _)
  · rw [h i hi]
    simp

end Impl

end Spectral

end BHSV25
