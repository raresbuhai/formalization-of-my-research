module

public import BHSV25.Spectral.Basic
public import BHSV25.Net.ColumnSubset

/-!
# Vectors of an eigenspace from few columns of a spectral filter

Let `A` be a symmetric real matrix with eigenvalues `μᵢ` and orthonormal eigenvectors `uᵢ`, and
let `P` act on the eigenbasis by multiplication with numbers `φᵢ ∈ [-1, 1]`: in the algorithms,
`P` is a power of `(I - Ã) / 2` or of `Ã`, which the machine computes exactly. Suppose that
`|φᵢ| ≤ ℓ` outside a set `R` of at most `T` indices, and let `w` be a vector of norm at most `1`
whose coefficients vanish except on indices of `R` with `φᵢ ≥ h > 0`. Then `w` is close to a
combination of `T` columns of `P` with coefficients at most `n / h` (`BHSV25.Net.exists_near`),
and stays close when the coefficients are rounded:
`‖P (∑ⱼ β'ⱼ e_{f j}) - w‖² ≤ 2 (T s)² + 2 (ℓ T n / h)²` when every `|β'ⱼ - βⱼ| ≤ s`.

The proof: the vectors `m_v = (φᵢ uᵢ(v))_{i ∈ R}`, the coordinates of the columns `P e_v` on `R`,
are spanned by `T` of them with coefficients at most `1` (`BHSV25.Net.exists_column_subset_fin`).
The vector `x = ∑ᵢ (cᵢ(w) / φᵢ) uᵢ` has norm at most `1 / h` and `P x = w`, so the coordinates of
`w` on `R` are `∑_v x_v m_v`, a combination of the `T` chosen columns with coefficients at most
`∑_v |x_v| ≤ n / h`. Outside `R`, `P` shrinks the combination by `ℓ`.

A power `B^k` of a matrix that multiplies the `i`-th coefficient by `c` multiplies it by `c^k`
(`BHSV25.Net.coeff_pow_mulVec`); `BHSV25/Net/Correct.lean` applies this to the two filters.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix Spectral

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}

/-! ### Coefficients are linear -/

theorem coeff_add (hA : A.IsHermitian) (i : Fin n) (x y : Fin n → ℝ) :
    coeff hA i (x + y) = coeff hA i x + coeff hA i y := by
  simp only [coeff, dotProduct_add]

theorem coeff_sub (hA : A.IsHermitian) (i : Fin n) (x y : Fin n → ℝ) :
    coeff hA i (x - y) = coeff hA i x - coeff hA i y := by
  simp only [coeff, dotProduct_sub]

theorem coeff_smul (hA : A.IsHermitian) (i : Fin n) (c : ℝ) (x : Fin n → ℝ) :
    coeff hA i (c • x) = c * coeff hA i x := by
  simp only [coeff, dotProduct_smul, smul_eq_mul]

theorem coeff_sum (hA : A.IsHermitian) (i : Fin n) {κ : Type*} (s : Finset κ)
    (x : κ → Fin n → ℝ) : coeff hA i (∑ j ∈ s, x j) = ∑ j ∈ s, coeff hA i (x j) := by
  simp only [coeff, dotProduct_sum]

theorem coeff_single (hA : A.IsHermitian) (i v : Fin n) :
    coeff hA i (Pi.single v 1) = hA.eigenvectorBasis i v := by
  simp only [coeff, dotProduct_single, mul_one]

/-- The eigenvectors are orthonormal. -/
theorem coeff_eigenvector (hA : A.IsHermitian) (l i : Fin n) :
    coeff hA l ⇑(hA.eigenvectorBasis i) = if l = i then 1 else 0 := by
  have h := orthonormal_iff_ite.1 hA.eigenvectorBasis.orthonormal l i
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  rw [coeff, dotProduct_comm]
  simpa using h

/-- **Powers of a filter**: if `B` multiplies the `i`-th coefficient by `c`, then `B^k`
multiplies it by `c^k`. -/
theorem coeff_pow_mulVec (hA : A.IsHermitian) {B : Matrix (Fin n) (Fin n) ℝ} {i : Fin n} {c : ℝ}
    (hB : ∀ x, coeff hA i (B *ᵥ x) = c * coeff hA i x) (k : ℕ) (x : Fin n → ℝ) :
    coeff hA i ((B ^ k) *ᵥ x) = c ^ k * coeff hA i x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mulVec_mulVec, ih, hB, pow_succ]
    ring

/-! ### Sparse vectors -/

/-- A combination of `T` standard basis vectors has squared norm at most the square of the sum
of the absolute values of its coefficients. -/
theorem dotProduct_sum_single_le {T : ℕ} (f : Fin T → Fin n) (γ : Fin T → ℝ) :
    (∑ j, γ j • Pi.single (f j) (1 : ℝ)) ⬝ᵥ (∑ j, γ j • Pi.single (f j) (1 : ℝ)) ≤
      (∑ j, |γ j|) ^ 2 := by
  classical
  set e : Fin T → Fin n → ℝ := fun j ↦ Pi.single (f j) (1 : ℝ) with hedef
  set y : Fin n → ℝ := ∑ j, γ j • e j with hydef
  have hy : ∀ u, |y u| ≤ ∑ j, |γ j| * e j u := by
    intro u
    simp only [y, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ ↦ ?_))
    rw [abs_mul]
    congr 1
    rcases eq_or_ne u (f j) with h | h
    · subst h
      simp [e]
    · simp [e, h]
  have h1 : ∑ u, |y u| ≤ ∑ j, |γ j| := by
    calc ∑ u, |y u| ≤ ∑ u, ∑ j, |γ j| * e j u :=
          Finset.sum_le_sum fun u _ ↦ hy u
      _ = ∑ j, |γ j| * ∑ u, e j u := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = ∑ j, |γ j| := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [e]
          rw [Finset.sum_pi_single' (f j) (1 : ℝ) Finset.univ]
          simp
  have h2 : y ⬝ᵥ y = ∑ u, |y u| ^ 2 := by
    simp only [dotProduct, sq_abs, ← sq]
  calc y ⬝ᵥ y = ∑ u, |y u| ^ 2 := h2
    _ ≤ (∑ u, |y u|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun u _ ↦ abs_nonneg _
    _ ≤ (∑ j, |γ j|) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun u _ ↦ abs_nonneg _) h1 2

/-! ### The approximation -/

/-- The vector with coefficients `cᵢ(w) / φᵢ` in the eigenbasis. -/
noncomputable def preimage (hA : A.IsHermitian) (φ : Fin n → ℝ) (w : Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, (coeff hA i w / φ i) • ⇑(hA.eigenvectorBasis i)

theorem coeff_preimage (hA : A.IsHermitian) (φ : Fin n → ℝ) (w : Fin n → ℝ) (l : Fin n) :
    coeff hA l (preimage hA φ w) = coeff hA l w / φ l := by
  classical
  rw [preimage, coeff_sum]
  simp only [coeff_smul, coeff_eigenvector, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem preimage_bound (hA : A.IsHermitian) {φ : Fin n → ℝ} {w : Fin n → ℝ} {h : ℝ}
    (hh : 0 < h) (hw1 : w ⬝ᵥ w ≤ 1) (hw : ∀ i, coeff hA i w ≠ 0 → h ≤ φ i) (v : Fin n) :
    |preimage hA φ w v| ≤ 1 / h := by
  set x := preimage hA φ w
  have hxx : x ⬝ᵥ x ≤ 1 / h ^ 2 := by
    rw [← sum_coeff_sq hA x, ← sum_coeff_sq hA w] at *
    have hterm : ∀ l, coeff hA l x ^ 2 ≤ coeff hA l w ^ 2 / h ^ 2 := by
      intro l
      rw [coeff_preimage]
      by_cases hc : coeff hA l w = 0
      · simp [hc]
      · have hφ := hw l hc
        have hφ0 : 0 < φ l := hh.trans_le hφ
        rw [div_pow]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          (pow_le_pow_left₀ hh.le hφ 2)
    calc ∑ l, coeff hA l x ^ 2 ≤ ∑ l, coeff hA l w ^ 2 / h ^ 2 :=
          Finset.sum_le_sum fun l _ ↦ hterm l
      _ = (∑ l, coeff hA l w ^ 2) / h ^ 2 := by rw [Finset.sum_div]
      _ ≤ 1 / h ^ 2 := div_le_div_of_nonneg_right hw1 (by positivity)
  have hv : x v ^ 2 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    have := Finset.single_le_sum (f := fun u ↦ x u * x u) (fun u _ ↦ mul_self_nonneg (x u))
      (Finset.mem_univ v)
    simpa [sq] using this
  have h2 : |x v| ^ 2 ≤ (1 / h) ^ 2 := by
    rw [sq_abs, div_pow, one_pow]
    exact hv.trans hxx
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 h2

/-- **Approximation by few columns of a filter.** -/
theorem exists_near (hA : A.IsHermitian) (P : Matrix (Fin n) (Fin n) ℝ) (φ : Fin n → ℝ)
    (hP : ∀ i x, coeff hA i (P *ᵥ x) = φ i * coeff hA i x) (R : Finset (Fin n)) {T : ℕ}
    (hR : R.card ≤ T) (hn : 0 < n) {ℓ h : ℝ} (hh : 0 < h) (hφ1 : ∀ i, |φ i| ≤ 1)
    (hφl : ∀ i ∉ R, |φ i| ≤ ℓ) (w : Fin n → ℝ) (hw1 : w ⬝ᵥ w ≤ 1)
    (hw : ∀ i, coeff hA i w ≠ 0 → i ∈ R ∧ h ≤ φ i) :
    ∃ f : Fin T → Fin n, ∃ β : Fin T → ℝ, (∀ j, |β j| ≤ n / h) ∧
      ∀ (β' : Fin T → ℝ) (s : ℝ), (∀ j, |β' j - β j| ≤ s) →
        (P *ᵥ (∑ j, β' j • Pi.single (f j) 1) - w) ⬝ᵥ
            (P *ᵥ (∑ j, β' j • Pi.single (f j) 1) - w) ≤
          2 * (T * s) ^ 2 + 2 * (ℓ * (T * (n / h))) ^ 2 := by
  classical
  set u : Fin n → Fin n → ℝ := fun i ↦ ⇑(hA.eigenvectorBasis i) with hudef
  let m : Fin n → R → ℝ := fun v i ↦ φ i * u i v
  obtain ⟨g, α, hα, hα1⟩ := exists_column_subset_fin m (by simpa using hR) hn
  set x := preimage hA φ w
  have hxu : ∀ v, |x v| ≤ 1 / h := preimage_bound hA hh hw1 (fun i hi ↦ (hw i hi).2)
  -- the coordinates of `w` on `R` are `∑_v x_v m_v`
  have hkey : ∀ i : R, ∑ v, x v * m v i = coeff hA i w := by
    intro i
    have h1 : ∑ v, x v * m v i = φ i * coeff hA i x := by
      simp only [m, coeff, dotProduct, Finset.mul_sum, u]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      ring
    rw [h1, coeff_preimage]
    by_cases hc : coeff hA i w = 0
    · simp [hc]
    · have hφ0 : φ i ≠ 0 := (hh.trans_le (hw i hc).2).ne'
      field_simp
  set β : Fin T → ℝ := fun j ↦ ∑ v, x v * α v j with hβdef
  have hβ : ∀ j, |β j| ≤ n / h := by
    intro j
    calc |β j| ≤ ∑ v, |x v * α v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : Fin n, 1 / h := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          rw [abs_mul]
          calc |x v| * |α v j| ≤ (1 / h) * 1 :=
                mul_le_mul (hxu v) (hα1 v j) (abs_nonneg _) (by positivity)
            _ = 1 / h := mul_one _
      _ = n / h := by simp [div_eq_mul_inv]
  have hβR : ∀ i : R, ∑ j, β j * m (g j) i = coeff hA i w := by
    intro i
    rw [← hkey i]
    simp only [β, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    have hv := congrFun (hα v) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hv
    rw [hv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  refine ⟨g, β, hβ, fun β' s hs ↦ ?_⟩
  set v₀ : Fin n → ℝ := ∑ j, β j • Pi.single (g j) 1 with hv₀
  set v' : Fin n → ℝ := ∑ j, β' j • Pi.single (g j) 1 with hv'
  have hcoeff_v : ∀ (γ : Fin T → ℝ) (i : Fin n),
      coeff hA i (∑ j, γ j • Pi.single (g j) 1) = ∑ j, γ j * u i (g j) := by
    intro γ i
    rw [coeff_sum]
    simp only [coeff_smul, coeff_single, u]
  -- the coefficients of the error
  set a : Fin n → ℝ := fun i ↦ φ i * coeff hA i (v' - v₀)
  set b : Fin n → ℝ := fun i ↦ φ i * coeff hA i v₀ - coeff hA i w
  have hab : ∀ i, coeff hA i (P *ᵥ v' - w) = a i + b i := by
    intro i
    simp only [a, b, coeff_sub, hP]
    ring
  have hbR : ∀ i ∈ R, b i = 0 := by
    intro i hi
    have := hβR ⟨i, hi⟩
    simp only [m] at this
    have hv0 : coeff hA i v₀ = ∑ j, β j * u i (g j) := hcoeff_v β i
    simp only [b, hv0, ← this, Finset.mul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hbnR : ∀ i ∉ R, b i ^ 2 ≤ ℓ ^ 2 * coeff hA i v₀ ^ 2 := by
    intro i hi
    have hw0 : coeff hA i w = 0 := by
      by_contra hc
      exact hi (hw i hc).1
    simp only [b, hw0, sub_zero, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hφl i hi) 2
  have hsum_a : ∑ i, a i ^ 2 ≤ (T * s) ^ 2 := by
    have h1 : ∑ i, a i ^ 2 ≤ (v' - v₀) ⬝ᵥ (v' - v₀) := by
      rw [← sum_coeff_sq hA]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      simp only [a, mul_pow]
      have : φ i ^ 2 ≤ 1 := by
        rw [← sq_abs]
        exact pow_le_one₀ (abs_nonneg _) (hφ1 i)
      nlinarith [sq_nonneg (coeff hA i (v' - v₀))]
    have hdiff : v' - v₀ = ∑ j, (β' j - β j) • Pi.single (g j) (1 : ℝ) := by
      simp only [v', v₀, ← Finset.sum_sub_distrib, sub_smul]
    have h2 := dotProduct_sum_single_le g (fun j ↦ β' j - β j)
    rw [← hdiff] at h2
    have h3 : ∑ j, |β' j - β j| ≤ T * s := by
      calc ∑ j, |β' j - β j| ≤ ∑ _j : Fin T, s := Finset.sum_le_sum fun j _ ↦ hs j
        _ = T * s := by simp
    have h4 : 0 ≤ ∑ j, |β' j - β j| := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    calc ∑ i, a i ^ 2 ≤ (v' - v₀) ⬝ᵥ (v' - v₀) := h1
      _ ≤ (∑ j, |β' j - β j|) ^ 2 := h2
      _ ≤ (T * s) ^ 2 := pow_le_pow_left₀ h4 h3 2
  have hsum_b : ∑ i, b i ^ 2 ≤ (ℓ * (T * (n / h))) ^ 2 := by
    have h1 : ∑ i, b i ^ 2 ≤ ℓ ^ 2 * (v₀ ⬝ᵥ v₀) := by
      rw [← sum_coeff_sq hA, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ ?_
      by_cases hi : i ∈ R
      · rw [hbR i hi]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        positivity
      · exact hbnR i hi
    have h2 := dotProduct_sum_single_le g β
    have h3 : ∑ j, |β j| ≤ T * (n / h) := by
      calc ∑ j, |β j| ≤ ∑ _j : Fin T, (n / h : ℝ) := Finset.sum_le_sum fun j _ ↦ hβ j
        _ = T * (n / h) := by simp
    have h4 : 0 ≤ ∑ j, |β j| := Finset.sum_nonneg fun j _ ↦ abs_nonneg _
    calc ∑ i, b i ^ 2 ≤ ℓ ^ 2 * (v₀ ⬝ᵥ v₀) := h1
      _ ≤ ℓ ^ 2 * (T * (n / h)) ^ 2 :=
          mul_le_mul_of_nonneg_left (h2.trans (pow_le_pow_left₀ h4 h3 2)) (sq_nonneg _)
      _ = (ℓ * (T * (n / h))) ^ 2 := by ring
  rw [← sum_coeff_sq hA]
  calc ∑ i, coeff hA i (P *ᵥ v' - w) ^ 2 = ∑ i, (a i + b i) ^ 2 := by simp only [hab]
    _ ≤ ∑ i, (2 * a i ^ 2 + 2 * b i ^ 2) :=
        Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (a i - b i)]
    _ = 2 * ∑ i, a i ^ 2 + 2 * ∑ i, b i ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (T * s) ^ 2 + 2 * (ℓ * (T * (n / h))) ^ 2 := by linarith

end Net

end BHSV25
