module

public import Background.SumOfSquares.PseudoBounds

/-!
# Sum-of-squares inequalities between sums, products and powers

Sums of squares of real polynomials that compare sums, products and powers. Write `p ≼ q` when
`q - p` is a sum of squares (`IsSumSq (q - p)`). The inequalities come with bounds on the total
degree of the sum of squares (`SoS.totalDegree_lagrange_le`, …); since the leading terms of real
squares cannot cancel (`SoS.two_mul_totalDegree_le`), these also bound the degrees of the squares.

* **Cauchy–Schwarz.** `SoS.isSumSq_lagrange`: `(∑ uᵢ vᵢ)² ≼ (∑ uᵢ²)(∑ vᵢ²)`, from Lagrange's
  identity `2 ((∑ uᵢ²)(∑ vᵢ²) - (∑ uᵢ vᵢ)²) = ∑ᵢ ∑ⱼ (uᵢ vⱼ - uⱼ vᵢ)²`
  (`SoS.two_mul_lagrange`, in every commutative ring).
* **Products and powers.** In every commutative ring: if `0 ≼ Zᵢ ≼ Yᵢ`, then `∏ Zᵢ ≼ ∏ Yᵢ`
  (`SoS.isSumSq_prod_sub_prod`); if `0 ≼ X ≼ Y`, then `X^m ≼ Y^m` (`SoS.isSumSq_pow_sub_pow`).
  For a constant `0 ≤ c ≼ X`: `c^N ≼ X^N` (`SoS.isSumSq_pow_ge_const`).
* **Power means.** `SoS.isSumSq_powMean`: for `N` terms and `e = 2^j`,
  `(∑ aᵢ)^e ≼ N^(e-1) ∑ aᵢ^e`. For two terms, `(x + y)^e ≼ 2^(e-1) (x^e + y^e)`
  (`SoS.isSumSq_add_pow_le`) and, for `j ≥ 1`, `2^(1-e) x^e ≼ (x + y)^e + y^e`
  (`SoS.isSumSq_pow_add_ge`).
* **Coefficient norms.** `SoS.isSumSq_l1`: a homogeneous `p` of degree `2D` in finitely many
  variables has `p ≼ ‖p‖₁ (∑ₐ Xₐ²)^D`. Each monomial of `p` is `c X^β X^β'` with
  `deg β = deg β' = D`, and `± X^β X^β' ≼ ½ (X^(2β) + X^(2β')) ≼ (∑ₐ Xₐ²)^D`.
* **Substitution.** `SoS.isSumSq_aeval`: `aeval φ` maps sums of squares to sums of squares
  (ring homomorphisms do, `SoS.isSumSq_map`). It multiplies the total degree by at most
  `maxᵢ deg φᵢ` (`SoS.totalDegree_aeval_le`, in `Background/SumOfSquares/Calculus.lean`) and
  `‖·‖₁` by at most `β^deg` when every `‖φᵢ‖₁ ≤ β`, `β ≥ 1` (`SoS.coeffNorm1_aeval_le`, in
  `Background/SumOfSquares/PseudoBounds.lean`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Finset

variable {σ : Type*}

/-! ### Generalities -/

/-- A square is a sum of squares. -/
theorem isSumSq_sq {R : Type*} [CommSemiring R] (x : R) : IsSumSq (x ^ 2) := by
  rw [sq]
  exact IsSumSq.mul_self x

/-- A sum of squares times a nonnegative constant is a sum of squares. -/
theorem isSumSq_C_mul {c : ℝ} (hc : 0 ≤ c) {p : MvPolynomial σ ℝ} (hp : IsSumSq p) :
    IsSumSq (C c * p) :=
  (isSumSq_C hc).mul hp

/-- Transitivity of `≼`. -/
theorem isSumSq_sub_trans {R : Type*} [CommRing R] {x y z : R} (hxy : IsSumSq (y - x))
    (hyz : IsSumSq (z - y)) : IsSumSq (z - x) := by
  have h := hyz.add hxy
  rwa [sub_add_sub_cancel] at h

/-- If `0 ≼ x ≼ y`, then `y` is a sum of squares. -/
theorem isSumSq_of_sub {R : Type*} [CommRing R] {x y : R} (hx : IsSumSq x)
    (hxy : IsSumSq (y - x)) : IsSumSq y := by
  have h := hx.add hxy
  rwa [add_sub_cancel] at h

/-- `C (1 / 2) * 2 = 1`. -/
theorem C_half_mul_two : (C (1 / 2 : ℝ) : MvPolynomial σ ℝ) * 2 = 1 := by
  rw [← map_ofNat (C : ℝ →+* MvPolynomial σ ℝ) 2, ← C_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    C_1]

/-! ### Cauchy–Schwarz -/

/-- **Lagrange's identity**, in every commutative ring. -/
theorem two_mul_lagrange {R ι : Type*} [CommRing R] (s : Finset ι) (u v : ι → R) :
    2 * ((∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, u i * v i) ^ 2) =
      ∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2 := by
  have e : ∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * v j ^ 2 + ∑ i ∈ s, ∑ j ∈ s, u j ^ 2 * v i ^ 2 -
        2 * ∑ i ∈ s, ∑ j ∈ s, (u i * v i) * (u j * v j) := by
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    ring
  have h1 : ∑ i ∈ s, ∑ j ∈ s, u i ^ 2 * v j ^ 2 = (∑ i ∈ s, u i ^ 2) * ∑ j ∈ s, v j ^ 2 :=
    (sum_mul_sum _ _ _ _).symm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, u j ^ 2 * v i ^ 2 = (∑ i ∈ s, u i ^ 2) * ∑ j ∈ s, v j ^ 2 := by
    rw [sum_comm]
    exact (sum_mul_sum _ _ _ _).symm
  have h3 : ∑ i ∈ s, ∑ j ∈ s, (u i * v i) * (u j * v j) = (∑ i ∈ s, u i * v i) ^ 2 := by
    rw [sq, sum_mul_sum]
  rw [e, h1, h2, h3]
  ring

/-- **Cauchy–Schwarz (P1).** `(∑ uᵢ vᵢ)² ≼ (∑ uᵢ²)(∑ vᵢ²)` for polynomials `uᵢ`, `vᵢ`. -/
theorem isSumSq_lagrange {ι : Type*} (s : Finset ι) (u v : ι → MvPolynomial σ ℝ) :
    IsSumSq ((∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, u i * v i) ^ 2) := by
  have e : (∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, u i * v i) ^ 2 =
      C (1 / 2) * ∑ i ∈ s, ∑ j ∈ s, (u i * v j - u j * v i) ^ 2 := by
    rw [← two_mul_lagrange, ← mul_assoc, C_half_mul_two, one_mul]
  rw [e]
  exact isSumSq_C_mul (by norm_num) (IsSumSq.sum fun i _ ↦ IsSumSq.sum_sq _ _)

/-- The degree in Cauchy–Schwarz. -/
theorem totalDegree_lagrange_le {R ι : Type*} [CommRing R] (s : Finset ι)
    {u v : ι → MvPolynomial σ R} {du dv : ℕ} (hu : ∀ i ∈ s, (u i).totalDegree ≤ du)
    (hv : ∀ i ∈ s, (v i).totalDegree ≤ dv) :
    ((∑ i ∈ s, u i ^ 2) * (∑ i ∈ s, v i ^ 2) - (∑ i ∈ s, u i * v i) ^ 2).totalDegree ≤
      2 * (du + dv) := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · have h1 : (∑ i ∈ s, u i ^ 2).totalDegree ≤ 2 * du := totalDegree_finsetSum_le fun i hi ↦
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hu i hi))
    have h2 : (∑ i ∈ s, v i ^ 2).totalDegree ≤ 2 * dv := totalDegree_finsetSum_le fun i hi ↦
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hv i hi))
    exact (totalDegree_mul _ _).trans (by omega)
  · have h : (∑ i ∈ s, u i * v i).totalDegree ≤ du + dv := totalDegree_finsetSum_le fun i hi ↦
      (totalDegree_mul _ _).trans (add_le_add (hu i hi) (hv i hi))
    exact (totalDegree_pow _ _).trans (by omega)

/-! ### Products and powers -/

/-- If `0 ≼ Zᵢ ≼ Yᵢ` for all `i ∈ s`, then `∏ Zᵢ ≼ ∏ Yᵢ`, in every commutative ring. -/
theorem isSumSq_prod_sub_prod {R ι : Type*} [CommRing R] (s : Finset ι) {Y Z : ι → R}
    (hZ : ∀ i ∈ s, IsSumSq (Z i)) (hYZ : ∀ i ∈ s, IsSumSq (Y i - Z i)) :
    IsSumSq (∏ i ∈ s, Y i - ∏ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [prod_empty, prod_empty, sub_self]; exact IsSumSq.zero
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    have hZa := hZ a (mem_insert_self a s)
    have hYZa := hYZ a (mem_insert_self a s)
    have ih' := ih (fun i hi ↦ hZ i (mem_insert_of_mem hi))
      (fun i hi ↦ hYZ i (mem_insert_of_mem hi))
    have hP : IsSumSq (∏ i ∈ s, Z i) := IsSumSq.prod fun i hi ↦ hZ i (mem_insert_of_mem hi)
    have e : Y a * ∏ i ∈ s, Y i - Z a * ∏ i ∈ s, Z i =
        Y a * (∏ i ∈ s, Y i - ∏ i ∈ s, Z i) + (Y a - Z a) * ∏ i ∈ s, Z i := by ring
    rw [e]
    exact ((isSumSq_of_sub hZa hYZa).mul ih').add (hYZa.mul hP)

/-- **Powers (P3).** If `0 ≼ X ≼ Y`, then `X^m ≼ Y^m`, in every commutative ring. -/
theorem isSumSq_pow_sub_pow {R : Type*} [CommRing R] {X Y : R} (hX : IsSumSq X)
    (hXY : IsSumSq (Y - X)) (m : ℕ) : IsSumSq (Y ^ m - X ^ m) := by
  have h := isSumSq_prod_sub_prod (range m) (Y := fun _ ↦ Y) (Z := fun _ ↦ X) (fun _ _ ↦ hX)
    fun _ _ ↦ hXY
  rwa [prod_const, prod_const, card_range] at h

/-- The degree in `SoS.isSumSq_pow_sub_pow`. -/
theorem totalDegree_pow_sub_pow_le {R : Type*} [CommRing R] (X Y : MvPolynomial σ R) (m : ℕ) :
    (Y ^ m - X ^ m).totalDegree ≤ m * max X.totalDegree Y.totalDegree :=
  (totalDegree_sub _ _).trans (max_le
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (le_max_right _ _)))
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (le_max_left _ _))))

/-- **Powers of a lower bound (P6).** If `0 ≤ c ≼ X`, then `c^N ≼ X^N`. -/
theorem isSumSq_pow_ge_const {X : MvPolynomial σ ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hX : IsSumSq (X - C c)) (N : ℕ) : IsSumSq (X ^ N - C (c ^ N)) := by
  rw [C_pow]
  exact isSumSq_pow_sub_pow (isSumSq_C hc) hX N

/-- The degree in `SoS.isSumSq_pow_ge_const`. -/
theorem totalDegree_pow_sub_C_le {R : Type*} [CommRing R] (X : MvPolynomial σ R) (c : R)
    (N : ℕ) : (X ^ N - C c).totalDegree ≤ N * X.totalDegree :=
  (totalDegree_sub_C_le _ _).trans (totalDegree_pow _ _)

/-! ### Power means -/

/-- `(∑ aᵢ)² ≼ N ∑ aᵢ²` for `N` terms. -/
theorem isSumSq_card_mul_sum_sq_sub {ι : Type*} (s : Finset ι) (a : ι → MvPolynomial σ ℝ) :
    IsSumSq (C (s.card : ℝ) * ∑ i ∈ s, a i ^ 2 - (∑ i ∈ s, a i) ^ 2) := by
  have h := isSumSq_lagrange s (fun _ ↦ 1) a
  simp only [one_pow, one_mul, sum_const, nsmul_eq_mul, mul_one] at h
  rwa [map_natCast]

/-- `SoS.isSumSq_powMean` for `j + 1`, by induction on `j`. -/
theorem isSumSq_powMean_succ {ι : Type*} (s : Finset ι) (a : ι → MvPolynomial σ ℝ) (j : ℕ) :
    IsSumSq (C ((s.card : ℝ) ^ (2 ^ (j + 1) - 1)) * ∑ i ∈ s, a i ^ 2 ^ (j + 1) -
      (∑ i ∈ s, a i) ^ 2 ^ (j + 1)) := by
  induction j with
  | zero => simpa using isSumSq_card_mul_sum_sq_sub s a
  | succ j ih =>
    obtain ⟨f, hf⟩ : ∃ f, 2 ^ (j + 1) = f + 1 :=
      ⟨2 ^ (j + 1) - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    have h2 : 2 ^ (j + 1 + 1) = 2 * f + 2 := by rw [pow_succ, hf]; ring
    have hT : IsSumSq ((∑ i ∈ s, a i) ^ (f + 1)) := by
      rw [← hf, pow_succ, pow_mul]
      exact isSumSq_sq _
    rw [hf, show f + 1 - 1 = f by omega, C_pow] at ih
    rw [h2, show 2 * f + 2 - 1 = 2 * f + 1 by omega, C_pow]
    have hS : ∑ i ∈ s, a i ^ (2 * f + 2) = ∑ i ∈ s, (a i ^ (f + 1)) ^ 2 :=
      sum_congr rfl fun i _ ↦ by ring
    have e : ∀ N S₂ S₁ T : MvPolynomial σ ℝ, N ^ (2 * f + 1) * S₂ - T ^ (2 * f + 2) =
        N ^ (2 * f) * (N * S₂ - S₁ ^ 2) + ((N ^ f * S₁) ^ 2 - (T ^ (f + 1)) ^ 2) :=
      fun _ _ _ _ ↦ by ring
    rw [hS, e _ _ (∑ i ∈ s, a i ^ (f + 1))]
    exact ((isSumSq_pow (isSumSq_C (Nat.cast_nonneg _)) _).mul
      (isSumSq_card_mul_sum_sq_sub s fun i ↦ a i ^ (f + 1))).add (isSumSq_pow_sub_pow hT ih 2)

/-- **Power means (P2).** `(∑ aᵢ)^(2^j) ≼ N^(2^j - 1) ∑ aᵢ^(2^j)` for `N` terms. -/
theorem isSumSq_powMean {ι : Type*} (s : Finset ι) (a : ι → MvPolynomial σ ℝ) (j : ℕ) :
    IsSumSq (C ((s.card : ℝ) ^ (2 ^ j - 1)) * ∑ i ∈ s, a i ^ 2 ^ j -
      (∑ i ∈ s, a i) ^ 2 ^ j) := by
  cases j with
  | zero => simp only [pow_zero, Nat.sub_self, C_1, one_mul, pow_one, sub_self]; exact .zero
  | succ j => exact isSumSq_powMean_succ s a j

/-- The degree in `SoS.isSumSq_powMean`. -/
theorem totalDegree_powMean_le {ι : Type*} (s : Finset ι) {a : ι → MvPolynomial σ ℝ} {e : ℕ}
    (ha : ∀ i ∈ s, (a i).totalDegree ≤ e) (c : ℝ) (j : ℕ) :
    (C c * ∑ i ∈ s, a i ^ 2 ^ j - (∑ i ∈ s, a i) ^ 2 ^ j).totalDegree ≤ 2 ^ j * e := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact totalDegree_finsetSum_le fun i hi ↦
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (ha i hi))
  · exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (totalDegree_finsetSum_le ha))

/-- **Two terms.** `(x + y)^(2^j) ≼ 2^(2^j - 1) (x^(2^j) + y^(2^j))`. -/
theorem isSumSq_add_pow_le (x y : MvPolynomial σ ℝ) (j : ℕ) :
    IsSumSq (C ((2 : ℝ) ^ (2 ^ j - 1)) * (x ^ 2 ^ j + y ^ 2 ^ j) - (x + y) ^ 2 ^ j) := by
  have h := isSumSq_powMean (univ : Finset (Fin 2)) ![x, y] j
  rw [card_univ, Fintype.card_fin, Fin.sum_univ_two, Fin.sum_univ_two] at h
  simpa using h

/-- **A lower bound (P4).** `2^(1 - 2^j) x^(2^j) ≼ (x + y)^(2^j) + y^(2^j)` for `j ≥ 1`. -/
theorem isSumSq_pow_add_ge (x y : MvPolynomial σ ℝ) {j : ℕ} (hj : j ≠ 0) :
    IsSumSq ((x + y) ^ 2 ^ j - C (((2 : ℝ) ^ (2 ^ j - 1))⁻¹) * x ^ 2 ^ j + y ^ 2 ^ j) := by
  have h := isSumSq_add_pow_le (x + y) (-y) j
  rw [(Nat.even_pow.2 ⟨even_two, hj⟩).neg_pow, add_neg_cancel_right] at h
  have h' := isSumSq_C_mul (inv_nonneg.2 (pow_nonneg zero_le_two (2 ^ j - 1))) h
  convert h' using 1
  rw [mul_sub, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), C_1, one_mul]
  ring

/-- The degree in `SoS.isSumSq_add_pow_le` and `SoS.isSumSq_pow_add_ge`. -/
theorem totalDegree_add_pow_le {R : Type*} [CommRing R] (x y : MvPolynomial σ R) {e : ℕ}
    (hx : x.totalDegree ≤ e) (hy : y.totalDegree ≤ e) (c : R) (m : ℕ) :
    (C c * (x ^ m + y ^ m) - (x + y) ^ m).totalDegree ≤ m * e ∧
      ((x + y) ^ m - C c * x ^ m + y ^ m).totalDegree ≤ m * e := by
  have hxm : (x ^ m).totalDegree ≤ m * e :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hx)
  have hym : (y ^ m).totalDegree ≤ m * e :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hy)
  have hxym : ((x + y) ^ m).totalDegree ≤ m * e := (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ ((totalDegree_add _ _).trans (max_le hx hy)))
  have hC : ∀ p : MvPolynomial σ R, (C c * p).totalDegree ≤ p.totalDegree := fun p ↦
    (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add])
  refine ⟨(totalDegree_sub _ _).trans (max_le ?_ hxym), (totalDegree_add _ _).trans
    (max_le ((totalDegree_sub _ _).trans (max_le hxym ((hC _).trans hxm))) hym)⟩
  exact (hC _).trans ((totalDegree_add _ _).trans (max_le hxm hym))

/-! ### Coefficient norms -/

/-- `X^(2β) ≼ (∑ₐ Xₐ²)^deg β`. -/
theorem isSumSq_sumSq_pow_sub_monomial_mul_self [Fintype σ] (β : σ →₀ ℕ) :
    IsSumSq ((∑ a, X a ^ 2 : MvPolynomial σ ℝ) ^ β.degree - monomial β 1 * monomial β 1) := by
  classical
  have hm : (monomial β 1 * monomial β 1 : MvPolynomial σ ℝ) =
      ∏ a ∈ β.support, (X a ^ 2) ^ β a := by
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, ← prod_mul_distrib]
    exact prod_congr rfl fun a _ ↦ by ring
  have hY : (∑ a, X a ^ 2 : MvPolynomial σ ℝ) ^ β.degree =
      ∏ a ∈ β.support, (∑ b, X b ^ 2) ^ β a := by
    rw [prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [hm, hY]
  refine isSumSq_prod_sub_prod _ (fun a _ ↦ isSumSq_pow (isSumSq_sq _) _) fun a _ ↦
    isSumSq_pow_sub_pow (isSumSq_sq _) ?_ _
  rw [← add_sum_erase _ _ (mem_univ a), add_sub_cancel_left]
  exact IsSumSq.sum_sq _ _

/-- If `m², m'² ≼ Y`, then `± m m' ≼ Y`. -/
theorem isSumSq_sub_mul_of_sub_mul_self {Y m m' : MvPolynomial σ ℝ} (h : IsSumSq (Y - m * m))
    (h' : IsSumSq (Y - m' * m')) : IsSumSq (Y - m * m') ∧ IsSumSq (Y + m * m') := by
  have hh : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h2 := C_half_mul_two (σ := σ)
  constructor
  · have e : Y - m * m' = C (1 / 2) * (Y - m * m) + C (1 / 2) * (Y - m' * m') +
        C (1 / 2) * (m - m') ^ 2 := by
      linear_combination (-(Y - m * m')) * h2
    rw [e]
    exact ((isSumSq_C_mul hh h).add (isSumSq_C_mul hh h')).add (isSumSq_C_mul hh (isSumSq_sq _))
  · have e : Y + m * m' = C (1 / 2) * (Y - m * m) + C (1 / 2) * (Y - m' * m') +
        C (1 / 2) * (m + m') ^ 2 := by
      linear_combination (-(Y + m * m')) * h2
    rw [e]
    exact ((isSumSq_C_mul hh h).add (isSumSq_C_mul hh h')).add (isSumSq_C_mul hh (isSumSq_sq _))

/-- A monomial `c X^γ` of degree `2D` has `c X^γ ≼ |c| (∑ₐ Xₐ²)^D`. -/
theorem isSumSq_C_abs_mul_sub_monomial [Fintype σ] {γ : σ →₀ ℕ} {D : ℕ}
    (hγ : γ.degree = 2 * D) (c : ℝ) :
    IsSumSq (C |c| * (∑ a, X a ^ 2 : MvPolynomial σ ℝ) ^ D - monomial γ c) := by
  obtain ⟨β, hβ, hβD⟩ := Finsupp.exists_le_degree_eq γ D (by omega)
  obtain ⟨β', rfl⟩ := le_iff_exists_add.mp hβ
  have hβ'D : β'.degree = D := by
    rw [map_add] at hγ
    omega
  have h := isSumSq_sumSq_pow_sub_monomial_mul_self (σ := σ) β
  have h' := isSumSq_sumSq_pow_sub_monomial_mul_self (σ := σ) β'
  rw [hβD] at h
  rw [hβ'D] at h'
  obtain ⟨hm, hp⟩ := isSumSq_sub_mul_of_sub_mul_self h h'
  have hmon : (monomial (β + β') c : MvPolynomial σ ℝ) =
      C c * (monomial β 1 * monomial β' 1) := by
    rw [monomial_mul_monomial, C_mul_monomial, mul_one, mul_one]
  rw [hmon]
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc, ← mul_sub]
    exact isSumSq_C_mul hc hm
  · have e : ∀ A B : MvPolynomial σ ℝ, C (-c) * A - C c * B = C (-c) * (A + B) := fun A B ↦ by
      rw [C_neg]
      ring
    rw [abs_of_neg hc, e]
    exact isSumSq_C_mul (by linarith) hp

/-- **Coefficient norms (P5).** A homogeneous `p` of degree `2D` in finitely many variables has
`p ≼ ‖p‖₁ (∑ₐ Xₐ²)^D`. -/
theorem isSumSq_l1 [Fintype σ] {p : MvPolynomial σ ℝ} {D : ℕ} (hp : p.IsHomogeneous (2 * D)) :
    IsSumSq (C (coeffNorm1 p) * (∑ a, X a ^ 2) ^ D - p) := by
  have e : ∑ γ ∈ p.support, (C |p.coeff γ| * (∑ a, X a ^ 2 : MvPolynomial σ ℝ) ^ D -
      monomial γ (p.coeff γ)) = C (coeffNorm1 p) * (∑ a, X a ^ 2) ^ D - p := by
    rw [sum_sub_distrib, ← sum_mul, ← map_sum, ← as_sum, coeffNorm1]
  rw [← e]
  refine IsSumSq.sum fun γ hγ ↦ isSumSq_C_abs_mul_sub_monomial ?_ _
  by_contra h
  exact mem_support_iff.1 hγ (hp.coeff_eq_zero h)

/-- The degree in `SoS.isSumSq_l1`. -/
theorem totalDegree_l1_le [Fintype σ] {p : MvPolynomial σ ℝ} {D : ℕ}
    (hp : p.IsHomogeneous (2 * D)) :
    (C (coeffNorm1 p) * (∑ a, X a ^ 2) ^ D - p).totalDegree ≤ 2 * D := by
  refine (totalDegree_sub _ _).trans (max_le ?_ hp.totalDegree_le)
  have hX : (∑ a, X a ^ 2 : MvPolynomial σ ℝ).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le fun a _ ↦ (totalDegree_pow _ _).trans (by rw [totalDegree_X])
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ hX)

/-! ### Substitution -/

/-- **Substitution (P7).** `aeval φ` maps sums of squares to sums of squares. -/
theorem isSumSq_aeval {τ : Type*} (φ : σ → MvPolynomial τ ℝ) {p : MvPolynomial σ ℝ}
    (hp : IsSumSq p) : IsSumSq (aeval φ p) :=
  isSumSq_map (aeval φ) hp

end SoS
