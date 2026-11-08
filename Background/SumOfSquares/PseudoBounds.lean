module

public import Background.SumOfSquares.Moments
public import Background.SumOfSquares.Normed

/-!
# Bounds for pseudo-expectations

Facts about a degree-`ℓ` pseudo-expectation `Ẽ` that use only its positivity on squares, one
constraint at a time with multiplier `1`, and an explicit ball constraint. They suffice for
analyses in which the pseudo-expectation found by the solver is used directly, with no
sum-of-squares proofs from the constraints.

* **Coefficient norms.** `SoS.coeffNorm1_aeval_le`: substituting polynomials with `‖φᵢ‖₁ ≤ β`,
  `β ≥ 1`, multiplies `‖·‖₁` by at most `β^deg`. `SoS.abs_eval_le_of_isHomogeneous`: a homogeneous
  `p` of degree `r` has `|p(b)| ≤ ‖p‖₁ M^r` when every `|bᵢ| ≤ M`, so in particular
  `|p(b)| ≤ ‖p‖₁ ‖b‖₂^r`.
* **Bounded values.** `SoS.PseudoExpectation.abs_apply_le`: if `ℓ` is even and `Ẽ` satisfies an
  explicit ball `B - ∑ i, xᵢ² ≥ 0` up to `η`, then `|Ẽ f| ≤ ‖f‖₁ c^(ℓ / 2)` for `deg f ≤ ℓ`, with
  `c = 1 + |B| + η ‖B - ∑ i, xᵢ²‖₂` (from the bound on the moments,
  `SoS.PseudoExpectation.abs_apply_monomial_le`).
* **One constraint.** `SoS.PseudoExpectation.ApproxSatisfies.neg_le_apply_of_mem`: a constraint
  `f ≥ 0` satisfied up to `η` has `Ẽ f ≥ -η ‖f‖₂`.
* **Weak triangle inequality.** `SoS.two_pow_mul_add_pow_eq_sum`: in every commutative ring,
  `2^(2s-1) (A^(2s) + B^(2s)) = ∑_{k ≤ s} C(2s, 2k) ((A + B)^(s-k) (A - B)^k)²` for `s ≥ 1`, so
  `Ẽ (A + B)^(2s) ≤ 2^(2s-1) (Ẽ A^(2s) + Ẽ B^(2s))` when `2 s deg A, 2 s deg B ≤ ℓ`
  (`SoS.PseudoExpectation.apply_add_pow_le`).
* **Jensen for powers of a sum of squares.** `SoS.pow_sub_mul_add_eq_sq_mul_sum`: the identity
  `Z^(m+1) - (m+1) Z + m = (Z - 1)² ∑_{j < m} (j + 1) Z^(m-1-j)`. With `Z = X^s / t^s` for a sum
  of squares `X`, it gives `Ẽ X^s ≤ t^s` from `Ẽ X^(rs) ≤ t^(rs)` at degree `r s deg X ≤ ℓ`
  (`SoS.PseudoExpectation.apply_pow_le_of_apply_pow_mul_le`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Finset

variable {σ : Type*}

/-! ### Coefficient norms -/

/-- Substituting polynomials `φ i` with `‖φ i‖₁ ≤ β`, `β ≥ 1`, for the variables multiplies
`‖·‖₁` by at most `β^deg`. -/
theorem coeffNorm1_aeval_le {τ : Type*} (φ : σ → MvPolynomial τ ℝ) {β : ℝ} (hβ : 1 ≤ β)
    (hφ : ∀ i, coeffNorm1 (φ i) ≤ β) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (aeval φ p) ≤ coeffNorm1 p * β ^ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine (coeffNorm1_sum_le _ _).trans ?_
  rw [coeffNorm1, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm ↦ ?_
  have h1 : coeffNorm1 (m.prod fun i k ↦ φ i ^ k) ≤ β ^ p.totalDegree := by
    rw [Finsupp.prod]
    refine (coeffNorm1_prod_le _ _).trans ?_
    calc ∏ i ∈ m.support, coeffNorm1 (φ i ^ m i) ≤ ∏ i ∈ m.support, β ^ m i :=
          Finset.prod_le_prod₀ (fun i _ ↦ coeffNorm1_nonneg _) fun i _ ↦
            (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hφ i) _)
      _ = β ^ (m.sum fun _ e ↦ e) := by rw [Finset.prod_pow_eq_pow_sum, Finsupp.sum]
      _ ≤ β ^ p.totalDegree := pow_le_pow_right₀ hβ (le_totalDegree hm)
  rw [aeval_monomial, algebraMap_eq, coeffNorm1_C_mul]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

/-- A monomial `bᵐ` is at most `M^deg m` in absolute value when every `|bᵢ| ≤ M`. -/
theorem abs_prod_pow_le {b : σ → ℝ} {M : ℝ} (hb : ∀ i, |b i| ≤ M) (m : σ →₀ ℕ) :
    |∏ i ∈ m.support, b i ^ m i| ≤ M ^ m.degree := by
  rw [Finset.abs_prod, show m.degree = ∑ i ∈ m.support, m i from rfl,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i _ ↦ by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb i) _

/-- A homogeneous polynomial `p` of degree `r` has `|p(b)| ≤ ‖p‖₁ M^r` when every `|bᵢ| ≤ M`. -/
theorem abs_eval_le_of_isHomogeneous {p : MvPolynomial σ ℝ} {r : ℕ} (hp : p.IsHomogeneous r)
    {b : σ → ℝ} {M : ℝ} (hb : ∀ i, |b i| ≤ M) : |eval b p| ≤ coeffNorm1 p * M ^ r := by
  rw [eval_eq, coeffNorm1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  have hdeg : m.degree = r := not_not.1 fun h ↦ mem_support_iff.1 hm (hp.coeff_eq_zero h)
  rw [abs_mul, ← hdeg]
  exact mul_le_mul_of_nonneg_left (abs_prod_pow_le hb m) (abs_nonneg _)

/-- Every polynomial `p` has `|p(b)| ≤ ‖p‖₁ M^deg p` when every `|bᵢ| ≤ M` and `M ≥ 1`. -/
theorem abs_eval_le {p : MvPolynomial σ ℝ} {b : σ → ℝ} {M : ℝ} (hM : 1 ≤ M)
    (hb : ∀ i, |b i| ≤ M) : |eval b p| ≤ coeffNorm1 p * M ^ p.totalDegree := by
  rw [eval_eq, coeffNorm1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((abs_prod_pow_le hb m).trans
    (pow_le_pow_right₀ hM (le_totalDegree hm))) (abs_nonneg _)

/-- `|p(b)| ≤ ‖p‖₁ (∑ i, |bᵢ|)^r` for `p` homogeneous of degree `r`. -/
theorem abs_eval_le_of_isHomogeneous_sum_abs [Fintype σ] {p : MvPolynomial σ ℝ} {r : ℕ}
    (hp : p.IsHomogeneous r) (b : σ → ℝ) :
    |eval b p| ≤ coeffNorm1 p * (∑ i, |b i|) ^ r :=
  abs_eval_le_of_isHomogeneous hp fun i ↦
    Finset.single_le_sum (f := fun j ↦ |b j|) (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ i)

/-- `|p(b)| ≤ ‖p‖₁ ‖b‖₂^r` for `p` homogeneous of degree `r`. -/
theorem abs_eval_le_of_isHomogeneous_sqrt [Fintype σ] {p : MvPolynomial σ ℝ} {r : ℕ}
    (hp : p.IsHomogeneous r) (b : σ → ℝ) :
    |eval b p| ≤ coeffNorm1 p * Real.sqrt (∑ i, b i ^ 2) ^ r :=
  abs_eval_le_of_isHomogeneous hp fun i ↦ Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun j ↦ b j ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ i))

/-! ### Sums of squares -/

theorem isSumSq_pow {R : Type*} [CommSemiring R] {x : R} (hx : IsSumSq x) (n : ℕ) :
    IsSumSq (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact IsSumSq.one
  | succ n ih => rw [pow_succ]; exact ih.mul hx

/-- A nonnegative real constant is a sum of squares. -/
theorem isSumSq_C {c : ℝ} (hc : 0 ≤ c) : IsSumSq (C c : MvPolynomial σ ℝ) := by
  have := IsSOS.const (σ := σ) hc
  rwa [IsSOS, toReal_real] at this

/-! ### Two identities -/

/-- The sum `∑_{m ≤ 2s} g m`, split into even and odd `m`. -/
theorem sum_range_two_mul_add_one {M : Type*} [AddCommMonoid M] (g : ℕ → M) (s : ℕ) :
    ∑ m ∈ range (2 * s + 1), g m =
      ∑ k ∈ range (s + 1), g (2 * k) + ∑ k ∈ range s, g (2 * k + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [show 2 * (s + 1) + 1 = 2 * s + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ (fun k ↦ g (2 * k)) (s + 1), sum_range_succ (fun k ↦ g (2 * k + 1)) s,
      show 2 * (s + 1) = 2 * s + 1 + 1 by ring]
    abel

/-- `(P + Q)^(2s) + (P - Q)^(2s) = 2 ∑_{k ≤ s} C(2s, 2k) (P^(s-k) Q^k)²`, in every commutative
ring: the odd terms of the binomial expansions cancel. -/
theorem add_pow_add_sub_pow_eq {R : Type*} [CommRing R] (P Q : R) (s : ℕ) :
    (P + Q) ^ (2 * s) + (P - Q) ^ (2 * s) =
      2 * ∑ k ∈ range (s + 1), ((2 * s).choose (2 * k) : R) * (P ^ (s - k) * Q ^ k) ^ 2 := by
  rw [add_comm P Q, sub_eq_neg_add, add_pow, add_pow, ← sum_add_distrib,
    sum_range_two_mul_add_one, mul_sum]
  have hodd : ∀ k ∈ range s, Q ^ (2 * k + 1) * P ^ (2 * s - (2 * k + 1)) *
      ((2 * s).choose (2 * k + 1) : R) + (-Q) ^ (2 * k + 1) * P ^ (2 * s - (2 * k + 1)) *
      ((2 * s).choose (2 * k + 1) : R) = 0 := fun k _ ↦ by
    rw [(odd_two_mul_add_one k).neg_pow]
    ring
  rw [sum_eq_zero hodd, add_zero]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk' : 2 * s - 2 * k = 2 * (s - k) := by
    have := mem_range.1 hk
    omega
  rw [(even_two_mul k).neg_pow, hk', pow_mul, pow_mul]
  ring

/-- `2^(2s-1) (A^(2s) + B^(2s)) = ∑_{k ≤ s} C(2s, 2k) ((A + B)^(s-k) (A - B)^k)²` for `s ≥ 1`, in a
domain of characteristic zero. -/
theorem two_pow_mul_add_pow_eq_sum_of_charZero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {s : ℕ} (hs : 1 ≤ s) (A B : R) :
    2 ^ (2 * s - 1) * (A ^ (2 * s) + B ^ (2 * s)) =
      ∑ k ∈ range (s + 1),
        ((2 * s).choose (2 * k) : R) * ((A + B) ^ (s - k) * (A - B) ^ k) ^ 2 := by
  have h := add_pow_add_sub_pow_eq (A + B) (A - B) s
  rw [show A + B + (A - B) = 2 * A by ring, show A + B - (A - B) = 2 * B by ring, mul_pow,
    mul_pow, ← mul_add, show 2 * s = 2 * s - 1 + 1 by omega, pow_succ', mul_assoc,
    ← show 2 * s = 2 * s - 1 + 1 by omega] at h
  exact mul_left_cancel₀ two_ne_zero h

/-- **The weak triangle identity**: `2^(2s-1) (A^(2s) + B^(2s)) =
∑_{k ≤ s} C(2s, 2k) ((A + B)^(s-k) (A - B)^k)²` for `s ≥ 1`, in every commutative ring. It is the
identity for the variables of `ℤ[A, B]`, mapped. -/
theorem two_pow_mul_add_pow_eq_sum {R : Type*} [CommRing R] {s : ℕ} (hs : 1 ≤ s) (A B : R) :
    2 ^ (2 * s - 1) * (A ^ (2 * s) + B ^ (2 * s)) =
      ∑ k ∈ range (s + 1),
        ((2 * s).choose (2 * k) : R) * ((A + B) ^ (s - k) * (A - B) ^ k) ^ 2 := by
  have h := congrArg (aeval ![A, B])
    (two_pow_mul_add_pow_eq_sum_of_charZero hs (X 0 : MvPolynomial (Fin 2) ℤ) (X 1))
  simpa using h

/-- `Z^(m+1) - (m+1) Z + m = (Z - 1)² ∑_{j < m} (j + 1) Z^(m-1-j)`, in every commutative ring. -/
theorem pow_sub_mul_add_eq_sq_mul_sum {R : Type*} [CommRing R] (Z : R) (m : ℕ) :
    Z ^ (m + 1) - (m + 1) * Z + m =
      (Z - 1) ^ 2 * ∑ j ∈ range m, ((j : R) + 1) * Z ^ (m - 1 - j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hS : ∑ j ∈ range (m + 1), ((j : R) + 1) * Z ^ (m + 1 - 1 - j) =
        Z * ∑ j ∈ range m, ((j : R) + 1) * Z ^ (m - 1 - j) + (m + 1) := by
      rw [sum_range_succ, mul_sum]
      congr 1
      · refine sum_congr rfl fun j hj ↦ ?_
        have : m + 1 - 1 - j = m - 1 - j + 1 := by
          have := mem_range.1 hj
          omega
        rw [this, pow_succ]
        ring
      · simp
    rw [hS]
    push_cast
    linear_combination Z * ih

/-- `Z^r - r Z + (r - 1) = (Z - 1)² ∑_{j < r-1} (j + 1) Z^(r-2-j)` for `r ≥ 1`, in every
commutative ring. -/
theorem pow_sub_mul_add_eq_sq_mul_sum' {R : Type*} [CommRing R] (Z : R) {r : ℕ} (hr : 1 ≤ r) :
    Z ^ r - r * Z + (r - 1) =
      (Z - 1) ^ 2 * ∑ j ∈ range (r - 1), ((j : R) + 1) * Z ^ (r - 2 - j) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega, show m + 1 - 2 = m - 1 by omega]
  push_cast
  rw [add_sub_cancel_right]
  exact pow_sub_mul_add_eq_sq_mul_sum Z m

namespace PseudoExpectation

variable {K : Type*} [Field K] [Algebra K ℝ] {ℓ : ℕ}

/-! ### Bounded values -/

/-- **Bounded values.** If `ℓ` is even and `Ẽ` satisfies an explicit bound `B - ∑ i, xᵢ² ≥ 0` up
to `η`, then `|Ẽ f| ≤ ‖f‖₁ c^(ℓ / 2)` for every `f` of degree at most `ℓ`, where
`c = 1 + |B| + η ‖B - ∑ i, xᵢ²‖₂`. -/
theorem abs_apply_le [Fintype σ] (hℓ : Even ℓ) (E : PseudoExpectation σ ℓ)
    {A : System σ K} {η : ℝ} (hη : 0 ≤ η) (hE : E.ApproxSatisfies A η 0) {B : K}
    (hB : (C B - ∑ i, X i ^ 2) ∈ A) {f : MvPolynomial σ ℝ} (hf : f.totalDegree ≤ ℓ) :
    |E f| ≤ coeffNorm1 f * (1 + |algebraMap K ℝ B| +
      η * coeffNorm (toReal (C B - ∑ i, X i ^ 2 : MvPolynomial σ K))) ^ (ℓ / 2) := by
  rw [E.coe_apply, apply_eq_sum_coeff_mul, coeffNorm1, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm ↦ ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (E.abs_apply_monomial_le hℓ hη hE hB ((le_totalDegree hm).trans hf)) (abs_nonneg _)

/-! ### One constraint -/

/-- A constraint `fᵢ ≥ 0` that `Ẽ` satisfies up to `η` has `Ẽ fᵢ ≥ -η ‖fᵢ‖₂` (the multiplier
`1`). -/
theorem ApproxSatisfies.neg_le_apply_get {E : PseudoExpectation σ ℓ} {A : System σ K} {η : ℝ}
    {r : ℕ} (hE : E.ApproxSatisfies A η r) (i : Fin A.length)
    (hdeg : max (A.get i).totalDegree r ≤ ℓ) :
    -(η * coeffNorm (toReal (A.get i))) ≤ E (toReal (A.get i)) := by
  have h := hE {i} 1 IsSumSq.one (by rwa [Finset.sum_singleton, totalDegree_one, zero_add])
  have hn : coeffNorm (1 : MvPolynomial σ ℝ) = 1 := by rw [← C_1, coeffNorm_C, abs_one]
  rwa [Finset.prod_singleton, hn, mul_one, one_mul, System.prod, Finset.prod_singleton] at h

/-- A constraint `f ≥ 0` of `A` that `Ẽ` satisfies up to `η` has `Ẽ f ≥ -η ‖f‖₂`. -/
theorem ApproxSatisfies.neg_le_apply_of_mem {E : PseudoExpectation σ ℓ} {A : System σ K}
    {η : ℝ} {r : ℕ} (hE : E.ApproxSatisfies A η r) {f : MvPolynomial σ K} (hf : f ∈ A)
    (hdeg : max f.totalDegree r ≤ ℓ) : -(η * coeffNorm (toReal f)) ≤ E (toReal f) := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  exact hE.neg_le_apply_get i hdeg

/-! ### The weak triangle inequality -/

variable (E : PseudoExpectation σ ℓ)

/-- `Ẽ A^(2s) ≥ 0` when `2 s deg A ≤ ℓ`. -/
theorem apply_pow_two_mul_nonneg {A : MvPolynomial σ ℝ} {e s : ℕ} (hA : A.totalDegree ≤ e)
    (hs : 2 * s * e ≤ ℓ) : 0 ≤ E (A ^ (2 * s)) := by
  rw [pow_mul', sq]
  refine E.map_mul_self_nonneg ?_
  have := (totalDegree_pow A s).trans (Nat.mul_le_mul_left s hA)
  rw [mul_assoc] at hs
  exact (Nat.mul_le_mul_left 2 this).trans hs

/-- **Weak triangle inequality**: `Ẽ (A + B)^(2s) ≤ 2^(2s-1) (Ẽ A^(2s) + Ẽ B^(2s))` when `A` and
`B` have degree at most `e` and `2 s e ≤ ℓ`. -/
theorem apply_add_pow_le {A B : MvPolynomial σ ℝ} {e s : ℕ} (hA : A.totalDegree ≤ e)
    (hB : B.totalDegree ≤ e) (hs : 2 * s * e ≤ ℓ) :
    E ((A + B) ^ (2 * s)) ≤ 2 ^ (2 * s - 1) * (E (A ^ (2 * s)) + E (B ^ (2 * s))) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · norm_num
  set g : ℕ → MvPolynomial σ ℝ := fun k ↦ (A + B) ^ (s - (k + 1)) * (A - B) ^ (k + 1)
  have hid : (2 : MvPolynomial σ ℝ) ^ (2 * s - 1) * (A ^ (2 * s) + B ^ (2 * s)) =
      ∑ k ∈ range s, C ((2 * s).choose (2 * (k + 1)) : ℝ) * (g k * g k) + (A + B) ^ (2 * s) := by
    rw [two_pow_mul_add_pow_eq_sum hs1, sum_range_succ']
    congr 1
    · refine sum_congr rfl fun k _ ↦ ?_
      rw [map_natCast, sq]
    · rw [mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one,
        Nat.sub_zero, ← pow_mul, mul_comm]
  have hE := congrArg E hid
  rw [map_add, E.map_sum, show (2 : MvPolynomial σ ℝ) ^ (2 * s - 1) = C (2 ^ (2 * s - 1)) by
    rw [map_pow, map_ofNat], map_C_mul, map_add] at hE
  have hdAB : (A + B).totalDegree ≤ e := (totalDegree_add A B).trans (max_le hA hB)
  have hdAB' : (A - B).totalDegree ≤ e := (totalDegree_sub A B).trans (max_le hA hB)
  have hnn : 0 ≤ ∑ k ∈ range s, E (C ((2 * s).choose (2 * (k + 1)) : ℝ) * (g k * g k)) := by
    refine sum_nonneg fun k hk ↦ ?_
    rw [map_C_mul]
    refine mul_nonneg (Nat.cast_nonneg _) (E.map_mul_self_nonneg ?_)
    have hk : k + 1 ≤ s := mem_range.1 hk
    have hg : (g k).totalDegree ≤ s * e := by
      refine (totalDegree_mul _ _).trans ?_
      have h₁ := (totalDegree_pow (A + B) (s - (k + 1))).trans (Nat.mul_le_mul_left _ hdAB)
      have h₂ := (totalDegree_pow (A - B) (k + 1)).trans (Nat.mul_le_mul_left _ hdAB')
      calc _ ≤ (s - (k + 1)) * e + (k + 1) * e := add_le_add h₁ h₂
        _ = s * e := by rw [← add_mul, Nat.sub_add_cancel hk]
    rw [mul_assoc] at hs
    exact (Nat.mul_le_mul_left 2 hg).trans hs
  linarith

/-- The weak triangle inequality for polynomials of degree at most `1`. -/
theorem apply_add_pow_le_of_totalDegree_le_one {A B : MvPolynomial σ ℝ} {s : ℕ}
    (hA : A.totalDegree ≤ 1) (hB : B.totalDegree ≤ 1) (hs : 2 * s ≤ ℓ) :
    E ((A + B) ^ (2 * s)) ≤ 2 ^ (2 * s - 1) * (E (A ^ (2 * s)) + E (B ^ (2 * s))) :=
  E.apply_add_pow_le hA hB (by rwa [mul_one])

/-- The weak triangle inequality, reversed: `Ẽ A^(2s) ≤ 2^(2s-1) (Ẽ (A + B)^(2s) + Ẽ B^(2s))`. -/
theorem apply_pow_le_add {A B : MvPolynomial σ ℝ} {e s : ℕ} (hA : A.totalDegree ≤ e)
    (hB : B.totalDegree ≤ e) (hs : 2 * s * e ≤ ℓ) :
    E (A ^ (2 * s)) ≤ 2 ^ (2 * s - 1) * (E ((A + B) ^ (2 * s)) + E (B ^ (2 * s))) := by
  have hAB : (A + B).totalDegree ≤ e := (totalDegree_add A B).trans (max_le hA hB)
  have h := E.apply_add_pow_le (B := -B) hAB (by rwa [totalDegree_neg]) hs
  rwa [add_neg_cancel_right, (even_two_mul s).neg_pow] at h

/-! ### Jensen for powers of a sum of squares -/

/-- **Jensen for powers of a sum of squares**: if `X` is a sum of squares of degree at most `e`,
`r ≥ 1`, `r s e ≤ ℓ`, `t > 0` and `Ẽ X^(rs) ≤ t^(rs)`, then `Ẽ X^s ≤ t^s`. Apply `Ẽ` to
`Z^r - r Z + (r - 1) = (Z - 1)² ∑_{j < r-1} (j + 1) Z^(r-2-j)` with `Z = X^s / t^s`, whose right
side is a sum of squares of degree at most `r s e`. -/
theorem apply_pow_le_of_apply_pow_mul_le {X : MvPolynomial σ ℝ} (hX : IsSumSq X) {e r s : ℕ}
    (hXe : X.totalDegree ≤ e) (hr : 1 ≤ r) (hℓ : r * s * e ≤ ℓ) {t : ℝ} (ht : 0 < t)
    (h : E (X ^ (r * s)) ≤ t ^ (r * s)) : E (X ^ s) ≤ t ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  set c : ℝ := (t ^ s)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (pow_pos ht s)
  set Z : MvPolynomial σ ℝ := C c * X ^ s with hZ
  have hid := pow_sub_mul_add_eq_sq_mul_sum Z m
  rw [show ((m : MvPolynomial σ ℝ) + 1) = C ((m : ℝ) + 1) by simp,
    show (m : MvPolynomial σ ℝ) = C (m : ℝ) by simp] at hid
  -- The right side is a sum of squares.
  have hZsos : IsSumSq Z := (isSumSq_C hc0.le).mul (isSumSq_pow hX s)
  have hsos : IsSumSq ((Z - 1) ^ 2 *
      ∑ j ∈ range m, ((j : MvPolynomial σ ℝ) + 1) * Z ^ (m - 1 - j)) := by
    refine IsSumSq.mul (by rw [sq]; exact IsSumSq.mul_self _)
      (IsSumSq.sum fun j _ ↦ IsSumSq.mul ?_ (isSumSq_pow hZsos _))
    rw [show ((j : MvPolynomial σ ℝ) + 1) = C ((j : ℝ) + 1) by simp]
    exact isSumSq_C (by positivity)
  -- Both sides have degree at most `(m + 1) s e ≤ ℓ`.
  have hZdeg : Z.totalDegree ≤ s * e := by
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hXe)
  have hdeg : (Z ^ (m + 1) - C ((m : ℝ) + 1) * Z + C (m : ℝ)).totalDegree ≤ ℓ := by
    rw [mul_assoc] at hℓ
    refine le_trans ?_ hℓ
    have h₁ : (Z ^ (m + 1)).totalDegree ≤ (m + 1) * (s * e) :=
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hZdeg)
    have h₂ : (C ((m : ℝ) + 1) * Z).totalDegree ≤ (m + 1) * (s * e) := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact hZdeg.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos m))
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le h₁ h₂)) ?_)
    rw [totalDegree_C]
    exact Nat.zero_le _
  have h0 : 0 ≤ E (Z ^ (m + 1) - C ((m : ℝ) + 1) * Z + C (m : ℝ)) := by
    rw [hid]
    exact E.nonneg_of_isSumSq hsos (hid ▸ hdeg)
  have hZpow : Z ^ (m + 1) = C (c ^ (m + 1)) * X ^ ((m + 1) * s) := by
    rw [hZ, mul_pow, ← map_pow, ← pow_mul, mul_comm s]
  rw [map_add, map_sub, map_C_mul, map_C, hZpow, map_C_mul, hZ, map_C_mul] at h0
  have hcv : c ^ (m + 1) * E (X ^ ((m + 1) * s)) ≤ 1 := by
    calc c ^ (m + 1) * E (X ^ ((m + 1) * s)) ≤ c ^ (m + 1) * t ^ ((m + 1) * s) :=
          mul_le_mul_of_nonneg_left h (pow_nonneg hc0.le _)
      _ = 1 := by
        rw [hc, inv_pow, ← pow_mul, mul_comm s, inv_mul_cancel₀ (pow_ne_zero _ ht.ne')]
  have hcu : c * E (X ^ s) ≤ 1 := by
    have hm : (0 : ℝ) < m + 1 := by positivity
    nlinarith
  calc E (X ^ s) = t ^ s * (c * E (X ^ s)) := by
        rw [hc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), one_mul]
    _ ≤ t ^ s * 1 := mul_le_mul_of_nonneg_left hcu (pow_nonneg ht.le _)
    _ = t ^ s := mul_one _

end PseudoExpectation

end SoS
