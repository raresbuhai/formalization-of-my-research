module

public import BHSV25.Alg.Rounding
public import BHSV25.Net.Spec

/-!
# Independent sets near the bottom eigenspace

The analysis of [BHSV25, Theorem 7.20], for one candidate vector.

* **Closeness to the bottom eigenvectors** [BHSV25, Lemma 7.22]. For an independent set `I` of a
  `d`-regular graph on `n` vertices (`d ≥ 1`), the vector `u` with `u_x = 1/√n` on `I` and
  `-1/√n` off `I` (`BHSV25.Alg.signVec`) has `uᵀ Ã u = 1 - 4 |I| / n`
  (`BHSV25.Alg.quad_signVec`). Since the eigenvalues are at least `-1`, the part of a vector `x`
  outside the span of the eigenvectors with eigenvalue at most `-θ` has
  `(1 - θ) ‖x - P x‖² ≤ xᵀ Ã x + ‖x‖²` (`BHSV25.Alg.one_sub_mul_dist_proj_le`), so
  `‖u - P u‖² ≤ 4 γ' / (1 - θ)` with `γ' = 1/2 - |I| / n`. In particular `|I| ≤ n / 2`
  (`BHSV25.Alg.two_mul_card_le`).
* **Rounding** [BHSV25, Lemma 7.23]. Thresholding a vector `w` at `0` misclassifies at most
  `n ‖w - u‖²` vertices (`BHSV25.Alg.card_misclassified_le`), and the rounding of
  `BHSV25.Alg.roundIndep` loses at most one vertex per misclassified one.

`BHSV25/Alg/IndepSetGS.lean` combines them for one candidate at constant precision
(`BHSV25.Alg.card_roundIndep_thrBits_ge`).
-/

@[expose] public section

namespace BHSV25.Alg

open Matrix

/-! ### Distances to spans of eigenvectors -/

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

theorem coeff_sub (hA : A.IsHermitian) (i : ι) (x y : ι → ℝ) :
    Spectral.coeff hA i (x - y) = Spectral.coeff hA i x - Spectral.coeff hA i y := by
  unfold Spectral.coeff
  rw [dotProduct_sub]

open Classical in
theorem dist_proj_sq (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) :
    (x - Spectral.proj hA S x) ⬝ᵥ (x - Spectral.proj hA S x) =
      ∑ i, if S (hA.eigenvalues i) then 0 else Spectral.coeff hA i x ^ 2 := by
  rw [← Spectral.sum_coeff_sq hA]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [coeff_sub, Spectral.coeff_proj]
  split_ifs <;> ring

open Classical in
theorem proj_dot_self (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) :
    Spectral.proj hA S x ⬝ᵥ Spectral.proj hA S x =
      ∑ i, if S (hA.eigenvalues i) then Spectral.coeff hA i x ^ 2 else 0 := by
  rw [← Spectral.sum_coeff_sq hA]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Spectral.coeff_proj]
  split_ifs <;> ring

/-- A projection is no longer than the vector. -/
theorem proj_dot_self_le (hA : A.IsHermitian) (S : ℝ → Prop) (x : ι → ℝ) :
    Spectral.proj hA S x ⬝ᵥ Spectral.proj hA S x ≤ x ⬝ᵥ x := by
  classical
  rw [proj_dot_self, ← Spectral.sum_coeff_sq hA]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

end Spectral

/-- `‖a + b‖² ≤ (1 + η) ‖a‖² + (1 + 1/η) ‖b‖²` for `η > 0`. -/
theorem dot_add_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) {η : ℝ} (hη : 0 < η) :
    (a + b) ⬝ᵥ (a + b) ≤ (1 + η) * (a ⬝ᵥ a) + (1 + 1 / η) * (b ⬝ᵥ b) := by
  simp only [dotProduct, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have e : (1 + η) * (a i * a i) + (1 + 1 / η) * (b i * b i) - (a i + b i) * (a i + b i) =
      (η * a i - b i) ^ 2 / η := by
    field_simp
    ring
  have h : 0 ≤ (η * a i - b i) ^ 2 / η := div_nonneg (sq_nonneg _) hη.le
  linarith only [e, h]

theorem neg_dot_neg {ι : Type*} [Fintype ι] (a : ι → ℝ) : (-a) ⬝ᵥ (-a) = a ⬝ᵥ a := by
  rw [neg_dotProduct, dotProduct_neg, neg_neg]

/-! ### Graphs -/

theorem eig_ge_neg_one (G : Graph) (i : Fin G.1) : -1 ≤ G.normAdj_isHermitian.eigenvalues i :=
  (abs_le.1 (G.abs_eig_le_one i)).1

/-- **The part outside the bottom eigenspace**: since the eigenvalues are at least `-1`,
`(1 - θ) ‖x - P x‖² ≤ xᵀ Ã x + ‖x‖²`, for `P` the projection onto the span of the eigenvectors
with eigenvalue at most `-θ`. -/
theorem one_sub_mul_dist_proj_le (G : Graph) (θ : ℝ) (x : Fin G.1 → ℝ) :
    (1 - θ) * ((x - Spectral.proj G.normAdj_isHermitian (· ≤ -θ) x) ⬝ᵥ
        (x - Spectral.proj G.normAdj_isHermitian (· ≤ -θ) x)) ≤
      x ⬝ᵥ (G.normAdj *ᵥ x) + x ⬝ᵥ x := by
  classical
  rw [dist_proj_sq, Spectral.quad_eq G.normAdj_isHermitian,
    ← Spectral.sum_coeff_sq G.normAdj_isHermitian x,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hμ := eig_ge_neg_one G i
  have hc := sq_nonneg (Spectral.coeff G.normAdj_isHermitian i x)
  split_ifs with h
  · have := mul_nonneg (by linarith only [hμ] :
      0 ≤ G.normAdj_isHermitian.eigenvalues i + 1) hc
    linarith only [this]
  · have := mul_nonneg (by linarith only [not_le.1 h] :
      0 ≤ G.normAdj_isHermitian.eigenvalues i + θ) hc
    linarith only [this]

/-- The vector of a set `I` of vertices: `1/√n` on `I`, `-1/√n` off `I`. -/
noncomputable def signVec {n : ℕ} (I : Finset (Fin n)) : Fin n → ℝ :=
  fun x ↦ if x ∈ I then 1 / Real.sqrt n else -(1 / Real.sqrt n)

theorem one_div_sqrt_sq (n : ℕ) : (1 / Real.sqrt n) ^ 2 = 1 / n := by
  rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

theorem signVec_sq {n : ℕ} (I : Finset (Fin n)) (x : Fin n) : signVec I x ^ 2 = 1 / n := by
  unfold signVec
  split_ifs
  · exact one_div_sqrt_sq n
  · rw [neg_sq]
    exact one_div_sqrt_sq n

theorem signVec_dot_self {n : ℕ} (hn : 0 < n) (I : Finset (Fin n)) :
    signVec I ⬝ᵥ signVec I = 1 := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  simp only [dotProduct, ← sq, signVec_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp

open Classical in
/-- The products of entries of `signVec`, against an entry of the normalized adjacency
matrix of a graph in which `I` is independent. -/
theorem normAdj_mul_signVec (G : Graph) {I : Finset (Fin G.1)}
    (hI : G.2.IsIndepSet (I : Set (Fin G.1))) (x y : Fin G.1) :
    G.normAdj x y * (signVec I x * signVec I y) =
      (1 / G.1) * (G.normAdj x y - 2 * (if x ∈ I then 1 else 0) * G.normAdj x y -
        2 * (if y ∈ I then 1 else 0) * G.normAdj x y) := by
  have hs := one_div_sqrt_sq G.1
  unfold signVec
  by_cases hx : x ∈ I <;> by_cases hy : y ∈ I
  · have h0 : G.normAdj x y = 0 := by
      unfold Graph.normAdj
      refine ite_eq_right fun hadj ↦ hI (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hadj.ne hadj
    rw [h0]
    ring
  · simp only [hx, hy, ↓reduceIte]
    rw [← hs]
    ring
  · simp only [hx, hy, ↓reduceIte]
    rw [← hs]
    ring
  · simp only [hx, hy, ↓reduceIte]
    rw [← hs]
    ring

open Classical in
/-- **The quadratic form at `signVec`** [BHSV25, proof of Lemma 7.22]: in a `d`-regular graph
with `d ≥ 1`, for an independent set `I`, `uᵀ Ã u = 1 - 4 |I| / n`. -/
theorem quad_signVec (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d) (hd0 : d ≠ 0)
    (hn : 0 < G.1) {I : Finset (Fin G.1)} (hI : G.2.IsIndepSet (I : Set (Fin G.1))) :
    signVec I ⬝ᵥ (G.normAdj *ᵥ signVec I) = 1 - 4 * I.card / G.1 := by
  classical
  set A := G.normAdj with hA
  have hn' : (G.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hrow : ∀ x, ∑ y, A x y = 1 := fun x ↦ by
    have := congrFun (G.normAdj_mulVec_one hd hd0) x
    simpa [mulVec, dotProduct] using this
  have hsym : ∀ x y, A x y = A y x := fun x y ↦ by
    have := G.normAdj_isHermitian.apply y x
    rw [star_trivial] at this
    exact this
  have hcol : ∀ y, ∑ x, A x y = 1 := fun y ↦ by
    rw [← hrow y]
    exact Finset.sum_congr rfl fun x _ ↦ hsym x y
  have hcard : ∑ x : Fin G.1, (if x ∈ I then (1 : ℝ) else 0) = I.card := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h1 : signVec I ⬝ᵥ (A *ᵥ signVec I) = ∑ x, ∑ y, A x y * (signVec I x * signVec I y) := by
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun y _ ↦ by ring
  have hpt : ∀ x y, A x y * (signVec I x * signVec I y) = (1 / G.1) * A x y -
      (2 / G.1) * ((if x ∈ I then 1 else 0) * A x y) -
      (2 / G.1) * ((if y ∈ I then 1 else 0) * A x y) := fun x y ↦ by
    rw [hA, normAdj_mul_signVec G hI]
    ring
  have hS1 : ∑ x, ∑ y, A x y = G.1 := by
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hS2 : ∑ x, ∑ y, (if x ∈ I then (1 : ℝ) else 0) * A x y = I.card := by
    simp_rw [← Finset.mul_sum, hrow, mul_one]
    exact hcard
  have hS3 : ∑ x, ∑ y, (if y ∈ I then (1 : ℝ) else 0) * A x y = I.card := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hcol, mul_one]
    exact hcard
  calc signVec I ⬝ᵥ (A *ᵥ signVec I) = ∑ x, ∑ y, A x y * (signVec I x * signVec I y) := h1
    _ = ∑ x, ∑ y, ((1 / G.1) * A x y - (2 / G.1) * ((if x ∈ I then 1 else 0) * A x y) -
          (2 / G.1) * ((if y ∈ I then 1 else 0) * A x y)) := by simp only [hpt]
    _ = (1 / G.1) * ∑ x, ∑ y, A x y -
          (2 / G.1) * ∑ x, ∑ y, (if x ∈ I then 1 else 0) * A x y -
          (2 / G.1) * ∑ x, ∑ y, (if y ∈ I then 1 else 0) * A x y := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (1 / G.1) * G.1 - (2 / G.1) * I.card - (2 / G.1) * I.card := by rw [hS1, hS2, hS3]
    _ = 1 - 4 * I.card / G.1 := by
      field_simp
      ring

open Classical in
/-- In a `d`-regular graph with `d ≥ 1`, an independent set has at most `n / 2` vertices. -/
theorem two_mul_card_le (G : Graph) {d : ℕ} (hd : G.2.IsRegularOfDegree d) (hd0 : d ≠ 0)
    {I : Finset (Fin G.1)} (hI : G.2.IsIndepSet (I : Set (Fin G.1))) : 2 * I.card ≤ G.1 := by
  rcases Nat.eq_zero_or_pos G.1 with h0 | hn
  · have := I.card_le_univ
    simp only [Fintype.card_fin] at this
    omega
  have hq := quad_signVec G hd hd0 hn hI
  have habs := G.abs_quad_normAdj_le (signVec I)
  rw [signVec_dot_self hn, hq] at habs
  have hn' : (0 : ℝ) < G.1 := Nat.cast_pos.2 hn
  have h := (abs_le.1 habs).1
  have h' : 4 * (I.card : ℝ) / G.1 ≤ 2 := by linarith only [h]
  rw [div_le_iff₀ hn'] at h'
  exact_mod_cast (by linarith only [h'] : (2 * I.card : ℝ) ≤ G.1)

/-! ### Thresholding -/

/-- The vertices `i < n` whose entry `c[i]` is at least `0`, as membership bits. -/
def thrBits (n : ℕ) (c : List ℚ) : List Bool := (List.range n).map fun i ↦ decide (0 ≤ c.getD i 0)

theorem mem_vertexSet_thrBits (G : Graph) (c : List ℚ) (x : Fin G.1) :
    x ∈ G.vertexSet (thrBits G.1 c) ↔ 0 ≤ Net.vecOf G.1 c x := by
  rw [Graph.vertexSet, Finset.mem_filter,
    List.getD_eq_getElem _ _ (by rw [thrBits, List.length_map, List.length_range]; exact x.2)]
  simp [thrBits, Net.vecOf]

/-- **Misclassified vertices** [BHSV25, proof of Lemma 7.23]: thresholding `w` at `0`
misclassifies at most `n ‖w - u‖²` vertices, for `u = signVec I`. -/
theorem card_misclassified_le {n : ℕ} (hn : 0 < n) (I : Finset (Fin n)) (w : Fin n → ℝ) :
    (((I.filter fun x ↦ w x < 0).card + ((Finset.univ.filter fun x ↦ 0 ≤ w x) \ I).card : ℕ) : ℝ)
      ≤ n * ((w - signVec I) ⬝ᵥ (w - signVec I)) := by
  classical
  set M := Finset.univ.filter fun x ↦ (x ∈ I ∧ w x < 0) ∨ (x ∉ I ∧ 0 ≤ w x) with hM
  have hcard : (I.filter fun x ↦ w x < 0).card + ((Finset.univ.filter fun x ↦ 0 ≤ w x) \ I).card =
      M.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [hM, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and]
      exact or_congr_right and_comm
    · rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.1 hx').2 (Finset.mem_filter.1 hx).1
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hs : 0 < 1 / Real.sqrt n := one_div_pos.2 (Real.sqrt_pos.2 hn')
  have hterm : ∀ x ∈ M, 1 / (n : ℝ) ≤ (w - signVec I) x * (w - signVec I) x := by
    intro x hx
    rw [← one_div_sqrt_sq n, ← sq, Pi.sub_apply]
    rcases (Finset.mem_filter.1 hx).2 with ⟨hxI, hw⟩ | ⟨hxI, hw⟩
    · rw [signVec, ite_eq_left hxI, show w x - 1 / Real.sqrt n = -(1 / Real.sqrt n - w x) by ring,
        neg_sq]
      exact pow_le_pow_left₀ hs.le (by linarith only [hw]) 2
    · rw [signVec, ite_eq_right hxI, sub_neg_eq_add]
      exact pow_le_pow_left₀ hs.le (by linarith only [hw]) 2
  have hsum : M.card * (1 / (n : ℝ)) ≤ (w - signVec I) ⬝ᵥ (w - signVec I) := by
    have h1 := Finset.card_nsmul_le_sum M _ _ hterm
    rw [nsmul_eq_mul] at h1
    refine h1.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ M)
      fun x _ _ ↦ mul_self_nonneg _
  rw [hcard]
  have := mul_le_mul_of_nonneg_left hsum hn'.le
  rw [mul_comm (M.card : ℝ), ← mul_assoc, mul_one_div_cancel hn'.ne', one_mul] at this
  exact this

/-! ### One candidate -/

end BHSV25.Alg
