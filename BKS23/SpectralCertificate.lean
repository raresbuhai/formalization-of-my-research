module

public import BKS23.SpectralDefs
public import BKS23.CliqueProgram
public import Mathlib.Analysis.Matrix.Order

/-!
# The spectral certificate

[BKS23, Lemma 4.13], as a proof from the clique program: if the centred cut matrix
`M_uv = 𝟙[u ∼ v] - q` of a graph `R'` whose cut contains that of `G` has norm at most `√Λ`
(`BKS23.Spectral.NormLE`), then the clique program of `G` proves
`|x| |y| ≤ Λ / (1 - q)²`, with `x = (w_u)_{u ∈ U}` and `y = (w_v)_{v ∉ U}`, in degree `6`.

The proof, with `z = |x| |y|` and `P = xᵀ M y`:

* `P = (1 - q) z` modulo the edge axioms `w_u w_v = 0` for the non-edges `u ≁ v` of `R'`;
* `P² ≤ ‖x‖² ‖M y‖²` (Lagrange's identity) and `‖M y‖² ≤ Λ ‖y‖²` (a sum of squares, since the
  form `Λ ‖y‖² - ‖M y‖²` is positive semidefinite);
* `‖x‖² ‖y‖² = z` modulo the Boolean axioms; so `(1 - q)² z² ≤ Λ z`;
* `c - z = ((c - z)² + (c z - z²)) / c` with `c = Λ / (1 - q)²`.

The positive semidefinite form is a sum of squares by the factorization `Q = Bᴴ B` of Mathlib
(`BKS23.Spectral.isSOS_of_sum_sq_le`). The multipliers have `‖·‖₁` at most
`(n + Λ + 1/Λ + 1/(1 - q) + 2)^12` (`BKS23.Spectral.certificate_norm_le`).
-/

@[expose] public section

namespace BKS23.Spectral

open SoS MvPolynomial Finset

/-! ### Identities in commutative rings -/

section Identities

variable {R ι κ : Type*} [CommRing R]

/-- **Lagrange's identity**, doubled:
`2 ((∑ fᵢ²) (∑ gᵢ²) - (∑ fᵢ gᵢ)²) = ∑_{i, j} (fᵢ gⱼ - fⱼ gᵢ)²`. -/
theorem two_mul_lagrange (s : Finset ι) (f g : ι → R) :
    2 * ((∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) - (∑ i ∈ s, f i * g i) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 := by
  have h : ∑ i ∈ s, ∑ j ∈ s, (f i * g j - f j * g i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, f i ^ 2 * g j ^ 2 + ∑ i ∈ s, ∑ j ∈ s, f j ^ 2 * g i ^ 2 -
        2 * ∑ i ∈ s, ∑ j ∈ s, f i * g i * (f j * g j) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [h, sum_comm (f := fun i j ↦ f j ^ 2 * g i ^ 2), sq (∑ i ∈ s, f i * g i), sum_mul_sum,
    sum_mul_sum]
  ring

variable [Fintype ι]

/-- A Gram form: `∑_{v, w} (∑_{u ∈ s} K_uv K_uw) p_v p_w = ∑_{u ∈ s} (∑_v K_uv p_v)²`. -/
theorem sum_sum_gram (f : ℝ →+* R) (s : Finset κ) (K : κ → ι → ℝ) (p : ι → R) :
    ∑ v, ∑ w, f (∑ u ∈ s, K u v * K u w) * (p v * p w) =
      ∑ u ∈ s, (∑ v, f (K u v) * p v) ^ 2 := by
  calc _ = ∑ v, ∑ u ∈ s, ∑ w, f (K u v * K u w) * (p v * p w) :=
        sum_congr rfl fun v _ ↦ by simp_rw [map_sum, sum_mul]; exact sum_comm
    _ = ∑ u ∈ s, ∑ v, ∑ w, f (K u v * K u w) * (p v * p w) := sum_comm
    _ = _ := sum_congr rfl fun u _ ↦ by
        rw [sq, sum_mul_sum]
        exact sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ by rw [map_mul]; ring

variable [DecidableEq ι]

/-- A diagonal form: `∑_{v, w} Λ 𝟙[v = w] p_v p_w = Λ ∑_v p_v²`. -/
theorem sum_sum_diag (f : ℝ →+* R) (Λ : ℝ) (p : ι → R) :
    ∑ v, ∑ w, f (Λ * if v = w then 1 else 0) * (p v * p w) = f Λ * ∑ v, p v ^ 2 := by
  rw [mul_sum]
  refine sum_congr rfl fun v _ ↦ ?_
  rw [sum_eq_single v (fun w _ hw ↦ by simp [Ne.symm hw]) (by simp)]
  simp [sq]

/-- The form `Λ ‖p‖² - ∑_{u ∈ s} (K p)_u²` as a quadratic form. -/
theorem sum_sum_spectral (f : ℝ →+* R) (Λ : ℝ) (s : Finset κ) (K : κ → ι → ℝ) (p : ι → R) :
    ∑ v, ∑ w, f ((Λ * if v = w then 1 else 0) - ∑ u ∈ s, K u v * K u w) * (p v * p w) =
      f Λ * ∑ v, p v ^ 2 - ∑ u ∈ s, (∑ v, f (K u v) * p v) ^ 2 := by
  simp only [map_sub, sub_mul, sum_sub_distrib, sum_sum_diag, sum_sum_gram]

end Identities

/-! ### Positive semidefinite forms are sums of squares -/

section PSD

variable {σ ι κ : Type*} [Fintype ι]

open scoped MatrixOrder in
/-- **A positive semidefinite form is a sum of squares**: if
`∑_{u ∈ s} (∑_v K_uv y_v)² ≤ Λ ∑_v y_v²` for every real `y`, then
`Λ ∑_v p_v² - ∑_{u ∈ s} (∑_v K_uv p_v)²` is a sum of squares, for any polynomials `p_v`. -/
theorem isSOS_of_sum_sq_le {Λ : ℝ} (s : Finset κ) (K : κ → ι → ℝ)
    (h : ∀ y : ι → ℝ, ∑ u ∈ s, (∑ v, K u v * y v) ^ 2 ≤ Λ * ∑ v, y v ^ 2)
    (p : ι → MvPolynomial σ ℝ) :
    IsSOS (C Λ * ∑ v, p v ^ 2 - ∑ u ∈ s, (∑ v, C (K u v) * p v) ^ 2) := by
  classical
  set Q : Matrix ι ι ℝ :=
    Matrix.of fun v w ↦ (Λ * if v = w then 1 else 0) - ∑ u ∈ s, K u v * K u w with hQ
  have hpsd : Q.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.IsHermitian.ext fun v w ↦ ?_)
      fun y ↦ ?_
    · simp only [hQ, Matrix.of_apply, star_trivial, eq_comm (a := w), mul_comm (K _ w)]
    · have e := sum_sum_spectral (RingHom.id ℝ) Λ s K y
      simp only [RingHom.id_apply] at e
      have : dotProduct (star y) (Q.mulVec y) = ∑ v, ∑ w, Q v w * (y v * y w) := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, mul_sum]
        exact sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ by ring
      rw [this]
      simp only [hQ, Matrix.of_apply]
      rw [e]
      linarith [h y]
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpsd.nonneg
  have hQB : ∀ v w, (Λ * if v = w then 1 else 0) - ∑ u ∈ s, K u v * K u w =
      ∑ l, B l v * B l w := fun v w ↦ by
    have := congrFun (congrFun hB v) w
    simpa [hQ, Matrix.mul_apply, Matrix.star_apply] using this
  rw [← sum_sum_spectral C Λ s K p]
  simp_rw [hQB]
  rw [sum_sum_gram C univ B p]
  exact IsSOS.sum _ fun l _ ↦ IsSOS.sq _

end PSD

/-! ### The polynomials -/

section Polys

variable {n : ℕ}

/-- `(M y)_u = ∑_{v ∉ U} M_uv y_v`. -/
noncomputable def rowForm (q : ℝ) (R : SimpleGraph (Fin n)) (U : Finset (Fin n)) (u : Fin n) :
    MvPolynomial (Fin n) ℝ :=
  ∑ v ∈ Uᶜ, C (cent q R u v) * X v

/-- `P = xᵀ M y = ∑_{u ∈ U} x_u (M y)_u`. -/
noncomputable def bilin (q : ℝ) (R : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    MvPolynomial (Fin n) ℝ :=
  ∑ u ∈ U, X u * rowForm q R U u

/-- `z = |x| |y|`. -/
noncomputable def sizeProd (U : Finset (Fin n)) : MvPolynomial (Fin n) ℝ :=
  (∑ u ∈ U, X u) * ∑ v ∈ Uᶜ, X v

variable {q : ℝ} {R : SimpleGraph (Fin n)} {U : Finset (Fin n)}

theorem card_le_n (S : Finset (Fin n)) : (S.card : ℝ) ≤ n := by
  exact_mod_cast (card_le_univ S).trans_eq (Fintype.card_fin n)

/-- A sum over vertices of terms of norm at most `c` has norm at most `n c`. -/
theorem coeffNorm1_sum_fin_le (S : Finset (Fin n)) {f : Fin n → MvPolynomial (Fin n) ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hf : ∀ i ∈ S, coeffNorm1 (f i) ≤ c) : coeffNorm1 (∑ i ∈ S, f i) ≤ n * c := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ i ∈ S, coeffNorm1 (f i) ≤ ∑ _i ∈ S, c := sum_le_sum hf
    _ = S.card * c := by rw [sum_const, nsmul_eq_mul]
    _ ≤ n * c := mul_le_mul_of_nonneg_right (card_le_n S) hc

theorem abs_cent_le (hq : 0 ≤ q) (hq1 : q ≤ 1) (u v : Fin n) : |cent q R u v| ≤ 1 := by
  unfold cent
  split_ifs
  · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith)]; linarith

theorem coeffNorm1_sum_X_le (S : Finset (Fin n)) :
    coeffNorm1 (∑ i ∈ S, X i : MvPolynomial (Fin n) ℝ) ≤ n := by
  simpa using coeffNorm1_sum_fin_le S zero_le_one fun i _ ↦ (coeffNorm1_X i).le

theorem coeffNorm1_sum_X_sq_le (S : Finset (Fin n)) :
    coeffNorm1 (∑ i ∈ S, X i ^ 2 : MvPolynomial (Fin n) ℝ) ≤ n := by
  simpa using coeffNorm1_sum_fin_le S zero_le_one fun i _ ↦ coeffNorm1_X_sq_le i

theorem totalDegree_sum_X_le (S : Finset (Fin n)) :
    (∑ i ∈ S, X i : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 :=
  totalDegree_finsetSum_le fun i _ ↦ (totalDegree_X i).le

theorem totalDegree_sum_X_sq_le (S : Finset (Fin n)) :
    (∑ i ∈ S, X i ^ 2 : MvPolynomial (Fin n) ℝ).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun i _ ↦ (totalDegree_X_pow i 2).le

theorem coeffNorm1_rowForm_le (hq : 0 ≤ q) (hq1 : q ≤ 1) (u : Fin n) :
    coeffNorm1 (rowForm q R U u) ≤ n := by
  unfold rowForm
  simpa using coeffNorm1_sum_fin_le Uᶜ zero_le_one fun v _ ↦ by
    rw [coeffNorm1_C_mul, coeffNorm1_X, mul_one]
    exact abs_cent_le hq hq1 u v

theorem totalDegree_rowForm_le (u : Fin n) : (rowForm q R U u).totalDegree ≤ 1 :=
  totalDegree_finsetSum_le fun v _ ↦ (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, totalDegree_X])

theorem coeffNorm1_bilin_le (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    coeffNorm1 (bilin q R U) ≤ (n : ℝ) ^ 2 := by
  rw [sq]
  refine coeffNorm1_sum_fin_le U (Nat.cast_nonneg n) fun u _ ↦ ?_
  refine (coeffNorm1_mul_le _ _).trans ?_
  rw [coeffNorm1_X, one_mul]
  exact coeffNorm1_rowForm_le hq hq1 u

theorem totalDegree_bilin_le : (bilin q R U).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun u _ ↦ (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have := totalDegree_rowForm_le (q := q) (R := R) (U := U) u
    omega)

theorem coeffNorm1_sizeProd_le (U : Finset (Fin n)) :
    coeffNorm1 (sizeProd U) ≤ (n : ℝ) ^ 2 := by
  rw [sq]
  exact (coeffNorm1_mul_le _ _).trans
    (mul_le_mul (coeffNorm1_sum_X_le U) (coeffNorm1_sum_X_le Uᶜ) (coeffNorm1_nonneg _)
      (Nat.cast_nonneg n))

theorem totalDegree_sizeProd_le (U : Finset (Fin n)) : (sizeProd U).totalDegree ≤ 2 :=
  (totalDegree_mul _ _).trans (by
    have := totalDegree_sum_X_le U
    have := totalDegree_sum_X_le Uᶜ
    omega)

end Polys

/-! ### The steps -/

section Steps

variable {n : ℕ} {A : System (Fin n) ℝ} {k : ℝ} {q Λ : ℝ} {R : SimpleGraph (Fin n)}
  {U : Finset (Fin n)}

/-- `P = (1 - q) z` by the edge axioms: `P - (1 - q) z = -∑_{u ≁ v} x_u y_v`. -/
theorem derivesEq_edge (hA : Biclique.Axioms A U R.Adj k) (q : ℝ) :
    DerivesEq A 2 ((n : ℝ) ^ 2) (bilin q R U - C (1 - q) * sizeProd U) := by
  have h : ∀ u ∈ U, ∀ v ∈ Uᶜ,
      DerivesEq A 2 1 (C (cent q R u v - (1 - q)) * (X u * X v)) := by
    intro u hu v hv
    by_cases huv : R.Adj u v
    · have : cent q R u v - (1 - q) = 0 := by simp [cent, huv]
      rw [this, C_0, zero_mul]
      exact DerivesEq.zero A 2 zero_le_one
    · have : cent q R u v - (1 - q) = -1 := by
        unfold cent; simp only [huv, ↓reduceIte]; ring
      rw [this]
      simpa using (hA.edge_eq hu hv huv).smul (-1)
  have hs := DerivesEq.sum U fun u hu ↦ DerivesEq.sum Uᶜ fun v hv ↦ h u hu v hv
  refine (hs.mono le_rfl ?_).congr ?_
  · simp only [sum_const, nsmul_eq_mul, mul_one, sq]
    exact mul_le_mul (card_le_n U) (card_le_n Uᶜ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [bilin, sizeProd, sum_mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [rowForm, mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun v _ ↦ by rw [map_sub]; ring

/-- `P² = (1 - q)² z²`: the edge step times `P + (1 - q) z`. -/
theorem derivesEq_sq (hA : Biclique.Axioms A U R.Adj k) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    DerivesEq A 6 ((2 * (n : ℝ) ^ 2 + 1) ^ 2 * (n : ℝ) ^ 2)
      (bilin q R U ^ 2 - C ((1 - q) ^ 2) * sizeProd U ^ 2) := by
  have hrn : coeffNorm1 (bilin q R U + C (1 - q) * sizeProd U) ≤ 2 * (n : ℝ) ^ 2 := by
    refine (coeffNorm1_add_le _ _).trans ?_
    rw [coeffNorm1_C_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - q)]
    have h1 := coeffNorm1_bilin_le (R := R) (U := U) hq hq1
    have h2 : (1 - q) * coeffNorm1 (sizeProd U) ≤ 1 * (n : ℝ) ^ 2 :=
      mul_le_mul (by linarith) (coeffNorm1_sizeProd_le U) (coeffNorm1_nonneg _) zero_le_one
    linarith
  have hrd : (bilin q R U + C (1 - q) * sizeProd U).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le totalDegree_bilin_le ((totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]; exact totalDegree_sizeProd_le U)))
  have h := (derivesEq_edge hA q (R := R)).mul (bilin q R U + C (1 - q) * sizeProd U)
  have hr0 := coeffNorm1_nonneg (bilin q R U + C (1 - q) * sizeProd U)
  refine (h.mono (by omega) ?_).congr ?_
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) (by linarith) 2)
      (by positivity)
  · rw [map_pow]
    ring

/-- `Λ ‖y‖² - ‖M y‖²` is a sum of squares. -/
theorem isSOS_spectral (hnorm : NormLE q U Λ R) :
    IsSOS (C Λ * ∑ v ∈ Uᶜ, X v ^ 2 - ∑ u ∈ U, rowForm q R U u ^ 2) := by
  have h := isSOS_of_sum_sq_le (ι := ↥(Uᶜ : Finset (Fin n))) (Λ := Λ) U
    (fun u v ↦ cent q R u v) ?_ (fun v ↦ (X (v : Fin n) : MvPolynomial (Fin n) ℝ))
  · simp only [rowForm, ← sum_coe_sort Uᶜ]
    exact h
  · intro y
    let y' : Fin n → ℝ := fun i ↦ if hi : i ∈ Uᶜ then y ⟨i, hi⟩ else 0
    have hy : ∀ v : (Uᶜ : Finset (Fin n)), y' v = y v := fun v ↦ by
      simp [y', Finset.mem_compl.1 v.2]
    have := hnorm y'
    simpa only [← sum_coe_sort Uᶜ, hy] using this

/-- `P² ≤ Λ ‖x‖² ‖y‖²`: Lagrange's identity and the spectral bound. -/
theorem derivesN_lagrange (hq : 0 ≤ q) (hq1 : q ≤ 1) (hΛ : 0 ≤ Λ) (hnorm : NormLE q U Λ R)
    (A : System (Fin n) ℝ) :
    DerivesN A 6 (Λ * (n : ℝ) ^ 2 + (n : ℝ) ^ 4)
      (C Λ * ((∑ u ∈ U, X u ^ 2) * ∑ v ∈ Uᶜ, X v ^ 2) - bilin q R U ^ 2) := by
  have hL : IsSOS ((∑ u ∈ U, X u ^ 2) * (∑ u ∈ U, rowForm q R U u ^ 2) - bilin q R U ^ 2) := by
    have h2 : (C (1 / 2 : ℝ) * 2 : MvPolynomial (Fin n) ℝ) = 1 := by
      rw [show (2 : MvPolynomial (Fin n) ℝ) = C 2 from (map_ofNat C 2).symm, ← C_mul]
      norm_num
    have e : (∑ u ∈ U, X u ^ 2) * (∑ u ∈ U, rowForm q R U u ^ 2) - bilin q R U ^ 2 =
        C (1 / 2) * ∑ i ∈ U, ∑ j ∈ U, (X i * rowForm q R U j - X j * rowForm q R U i) ^ 2 := by
      rw [← two_mul_lagrange U (fun u ↦ (X u : MvPolynomial (Fin n) ℝ)) (rowForm q R U), bilin]
      linear_combination (-((∑ u ∈ U, X u ^ 2) * (∑ u ∈ U, rowForm q R U u ^ 2) -
        (∑ u ∈ U, X u * rowForm q R U u) ^ 2)) * h2
    rw [e]
    exact (IsSOS.const (by norm_num)).mul
      (IsSOS.sum _ fun i _ ↦ IsSOS.sum _ fun j _ ↦ IsSOS.sq _)
  have hS : IsSOS (C Λ * ((∑ u ∈ U, X u ^ 2) * ∑ v ∈ Uᶜ, X v ^ 2) - bilin q R U ^ 2) := by
    have e : C Λ * ((∑ u ∈ U, X u ^ 2) * ∑ v ∈ Uᶜ, X v ^ 2) - bilin q R U ^ 2 =
        ((∑ u ∈ U, X u ^ 2) * (∑ u ∈ U, rowForm q R U u ^ 2) - bilin q R U ^ 2) +
          (∑ u ∈ U, X u ^ 2) * (C Λ * ∑ v ∈ Uᶜ, X v ^ 2 - ∑ u ∈ U, rowForm q R U u ^ 2) := by
      ring
    rw [e]
    exact hL.add ((IsSOS.sum _ fun _ _ ↦ IsSOS.sq _).mul (isSOS_spectral hnorm))
  refine DerivesN.ofIsSOS A hS ?_ ?_
  · refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_sum_X_sq_le U
      have := totalDegree_sum_X_sq_le Uᶜ
      omega
    · refine (totalDegree_pow _ 2).trans ?_
      have := totalDegree_bilin_le (q := q) (R := R) (U := U)
      omega
  · refine (coeffNorm1_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [coeffNorm1_C_mul, abs_of_nonneg hΛ, sq]
      exact mul_le_mul_of_nonneg_left ((coeffNorm1_mul_le _ _).trans
        (mul_le_mul (coeffNorm1_sum_X_sq_le U) (coeffNorm1_sum_X_sq_le Uᶜ) (coeffNorm1_nonneg _)
          (Nat.cast_nonneg n))) hΛ
    · refine (coeffNorm1_pow_le _ 2).trans ?_
      calc coeffNorm1 (bilin q R U) ^ 2 ≤ ((n : ℝ) ^ 2) ^ 2 :=
            pow_le_pow_left₀ (coeffNorm1_nonneg _) (coeffNorm1_bilin_le hq hq1) 2
        _ = (n : ℝ) ^ 4 := by ring

/-- `‖x‖² ‖y‖² = z` by the Boolean axioms:
`x_u² y_v² - x_u y_v = y_v² (x_u² - x_u) + x_u (y_v² - y_v)`. -/
theorem derivesEq_bool (hA : Biclique.Axioms A U R.Adj k) :
    DerivesEq A 6 (8 * (n : ℝ) ^ 2)
      ((∑ u ∈ U, X u ^ 2) * (∑ v ∈ Uᶜ, X v ^ 2) - sizeProd U) := by
  have h : ∀ u ∈ U, ∀ v ∈ Uᶜ,
      DerivesEq A 6 8 (X v ^ 2 * (X u ^ 2 - X u) + X u * (X v ^ 2 - X v)) := by
    intro u _ v _
    have h1 := (hA.bool.eq u).mul (X v ^ 2)
    have h2 := (hA.bool.eq v).mul (X u)
    have n1 : (coeffNorm1 (X v ^ 2 : MvPolynomial (Fin n) ℝ) + 1) ^ 2 * 1 ≤ 4 := by
      rw [mul_one, show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact pow_le_pow_left₀ (by linarith [coeffNorm1_nonneg (X v ^ 2 : MvPolynomial (Fin n) ℝ)])
        (by linarith [coeffNorm1_X_sq_le (σ := Fin n) v]) 2
    have n2 : (coeffNorm1 (X u : MvPolynomial (Fin n) ℝ) + 1) ^ 2 * 1 ≤ 4 := by
      rw [coeffNorm1_X]; norm_num
    have := (h1.mono (k' := 6) (by rw [totalDegree_X_pow]) n1).add
      (h2.mono (k' := 6) (by rw [totalDegree_X]; omega) n2)
    exact this.mono le_rfl (by norm_num)
  have hs := DerivesEq.sum U fun u hu ↦ DerivesEq.sum Uᶜ fun v hv ↦ h u hu v hv
  refine (hs.mono le_rfl ?_).congr ?_
  · simp only [sum_const, nsmul_eq_mul]
    have := mul_le_mul (card_le_n U) (card_le_n Uᶜ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  · rw [sizeProd, sum_mul_sum, sum_mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun u _ ↦ ?_
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun v _ ↦ by ring

/-- `(1 - q)² z² ≤ Λ z`. -/
theorem derivesN_quad (hA : Biclique.Axioms A U R.Adj k) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hΛ : 0 ≤ Λ)
    (hnorm : NormLE q U Λ R) :
    DerivesN A 6 (Λ * (n : ℝ) ^ 2 + (n : ℝ) ^ 4 +
        (Λ * (8 * (n : ℝ) ^ 2) + (2 * (n : ℝ) ^ 2 + 1) ^ 2 * (n : ℝ) ^ 2))
      (C Λ * sizeProd U - C ((1 - q) ^ 2) * sizeProd U ^ 2) := by
  have he := ((derivesEq_bool hA).smul Λ).neg.add (derivesEq_sq hA hq hq1)
  rw [abs_of_nonneg hΛ] at he
  exact (derivesN_lagrange hq hq1 hΛ hnorm A).of_eq (he.congr (by ring))

end Steps

/-- The norm bound of the certificate: the multipliers are at most
`(n² + c)² / c + (Λ n² + n⁴ + 8 Λ n² + (2 n² + 1)² n²) / Λ ≤ W¹²`. -/
theorem certificate_norm_le {N Λ c W : ℝ} (hN : 0 ≤ N) (hΛ : 0 < Λ) (hc : 0 < c) (hW : 2 ≤ W)
    (hNW : N ≤ W) (hΛW : Λ ≤ W) (hΛi : 1 / Λ ≤ W) (hcW : c ≤ W ^ 3) (hci : 1 / c ≤ W) :
    1 / c * (c + N ^ 2) ^ 2 +
        1 / Λ * (Λ * N ^ 2 + N ^ 4 + (Λ * (8 * N ^ 2) + (2 * N ^ 2 + 1) ^ 2 * N ^ 2)) ≤
      W ^ 12 := by
  have hW0 : 0 ≤ W := by linarith
  have h1 : 1 / c * (c + N ^ 2) ^ 2 ≤ W * (W ^ 3 + W ^ 2) ^ 2 := by gcongr
  have h2 : 1 / Λ * (Λ * N ^ 2 + N ^ 4 + (Λ * (8 * N ^ 2) + (2 * N ^ 2 + 1) ^ 2 * N ^ 2)) ≤
      W * (W * W ^ 2 + W ^ 4 + (W * (8 * W ^ 2) + (2 * W ^ 2 + 1) ^ 2 * W ^ 2)) := by
    gcongr
  have h3 : W ^ 3 ≤ W ^ 7 := pow_le_pow_of_two_le hW (by norm_num)
  have h4 : W ^ 4 ≤ W ^ 7 := pow_le_pow_of_two_le hW (by norm_num)
  have h5 : W ^ 5 ≤ W ^ 7 := pow_le_pow_of_two_le hW (by norm_num)
  have h6 : W ^ 6 ≤ W ^ 7 := pow_le_pow_of_two_le hW (by norm_num)
  have h32 : (32 : ℝ) ≤ W ^ 5 := by
    calc (32 : ℝ) = 2 ^ 5 := by norm_num
      _ ≤ W ^ 5 := pow_le_pow_left₀ (by norm_num) hW 5
  have h7 : 23 * W ^ 7 ≤ W ^ 12 := by
    have : W ^ 12 = W ^ 5 * W ^ 7 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hW0 7)
  linarith

/-- **The spectral certificate** [BKS23, Lemma 4.13]. -/
theorem certificate_spectral {n k ℓ : ℕ} {L : List (ℕ × ℕ)} {G R' : SimpleGraph (Fin n)}
    (hL : Clique.ListsNonEdges G L) {U : Finset (Fin n)}
    (hcut : ∀ u ∈ U, ∀ v ∈ Uᶜ, G.Adj u v → R'.Adj u v) {q Λ : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (hΛ : 0 < Λ) (hnorm : NormLE q U Λ R') :
    DerivesN (Clique.realSystem n k ℓ L) 6
      (((n : ℝ) + Λ + 1 / Λ + 1 / (1 - q) + 2) ^ 12)
      (C (Λ / (1 - q) ^ 2) - (∑ u ∈ U, X u) * ∑ v ∈ Uᶜ, X v) := by
  have hA := Clique.axioms (k := k) (ℓ := ℓ) hL hcut
  have hq0 : 0 < 1 - q := by linarith
  set W := (n : ℝ) + Λ + 1 / Λ + 1 / (1 - q) + 2 with hW
  set c := Λ / (1 - q) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hΛi0 : 0 ≤ 1 / Λ := by positivity
  have hqi0 : 0 ≤ 1 / (1 - q) := by positivity
  have hqW : 1 / (1 - q) ≤ W := by linarith
  have hcW : c ≤ W ^ 3 := by
    have : c = Λ * (1 / (1 - q)) ^ 2 := by rw [hc]; field_simp
    rw [this, pow_succ' W 2]
    exact mul_le_mul (by linarith) (pow_le_pow_left₀ hqi0 hqW 2) (by positivity) (by linarith)
  have hci : 1 / c ≤ W := by
    have h1 : 1 / c = (1 - q) ^ 2 / Λ := by rw [hc, one_div_div]
    have h2 : (1 - q) ^ 2 / Λ ≤ 1 / Λ :=
      div_le_div_of_nonneg_right (pow_le_one₀ hq0.le (by linarith)) hΛ.le
    linarith
  -- `(c - z)² ≥ 0` and `Λ z - (1 - q)² z² ≥ 0`.
  have h1 := DerivesN.ofIsSOS (Clique.realSystem n k ℓ L) (IsSOS.sq (C c - sizeProd U))
    (k := 6) (M := (c + (n : ℝ) ^ 2) ^ 2)
    ((totalDegree_pow _ 2).trans (by
      have := (totalDegree_sub (C c) (sizeProd U)).trans
        (max_le (by rw [totalDegree_C]; omega) (totalDegree_sizeProd_le U))
      omega))
    ((coeffNorm1_pow_le _ 2).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _)
      ((coeffNorm1_sub_le _ _).trans (by
        rw [coeffNorm1_C, abs_of_pos hc0]
        linarith [coeffNorm1_sizeProd_le U])) 2))
  have h2 := derivesN_quad hA hq hq1.le hΛ.le hnorm
  have h := (h1.smul (one_div_nonneg.2 hc0.le)).add (h2.smul hΛi0)
  refine (h.mono le_rfl ?_).congr ?_
  · exact certificate_norm_le hn0 hΛ hc0 (by linarith) (by linarith) (by linarith) (by linarith)
      hcW hci
  · -- `c - z = (c - z)² / c + (Λ z - (1 - q)² z²) / Λ`.
    have e1 : (C (1 / c) * C c : MvPolynomial (Fin n) ℝ) = 1 := by
      rw [← C_mul, one_div_mul_cancel hc0.ne', C_1]
    have e2 : (C (1 / Λ) * C Λ : MvPolynomial (Fin n) ℝ) = 1 := by
      rw [← C_mul, one_div_mul_cancel hΛ.ne', C_1]
    have e3 : (C (1 / c) : MvPolynomial (Fin n) ℝ) = C (1 / Λ) * C ((1 - q) ^ 2) := by
      rw [← C_mul, hc]
      congr 1
      field_simp
    rw [sizeProd]
    linear_combination (C c - 2 * ((∑ u ∈ U, X u) * ∑ v ∈ Uᶜ, X v)) * e1 +
      ((∑ u ∈ U, X u) * ∑ v ∈ Uᶜ, X v) * e2 + ((∑ u ∈ U, X u) * ∑ v ∈ Uᶜ, X v) ^ 2 * e3

end BKS23.Spectral
