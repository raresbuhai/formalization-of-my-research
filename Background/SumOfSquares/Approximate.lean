module

public import Mathlib.Algebra.Order.Chebyshev
public import Background.SumOfSquares.PseudoExpectation
public import Background.SumOfSquares.Calculus
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Approximate soundness

The sum-of-squares algorithm only finds pseudo-expectations that satisfy the constraints up to an
error `η` (`SoS.PseudoExpectation.ApproxSatisfies`). Soundness survives this error, losing a
factor that depends on the size of the proof:

* `SoS.Proof.size`: `∑ S, ‖p S‖₁ ∏ i ∈ S, ‖fᵢ‖₂` for a proof with multipliers `p S` from
  constraints `fᵢ`.
* `SoS.PseudoExpectation.ApproxSatisfies.apply_proof`: if `Ẽ` satisfies `A` up to `η` and `P`
  proves `g ≥ 0` from `A`, then `Ẽ (h g) ≥ -η ‖h‖₂ · P.size` for every admissible sum of
  squares `h`.
* `SoS.Proof.size_le`: a proof of bit complexity `B` has
  `P.size ≤ 2^m (n + 1)^(k + ∑ deg fᵢ) 2^(B (m + 1))`, for `m` constraints in `n` variables.

Along the way: the coefficient norms `‖·‖₁` (`SoS.coeffNorm1`) and `‖·‖₂` (`SoS.coeffNorm`), with
`‖h m‖₂ ≤ ‖h‖₂ ‖m‖₁`; and the count of monomials, at most `(n + 1)^d` of degree at most `d`.
-/

@[expose] public section

namespace SoS

open MvPolynomial

variable {σ : Type*}

/-! ### Coefficient norms -/

/-- The sum `‖p‖₁` of the absolute values of the coefficients of a real polynomial. -/
noncomputable def coeffNorm1 (p : MvPolynomial σ ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

theorem coeffNorm_nonneg (p : MvPolynomial σ ℝ) : 0 ≤ coeffNorm p :=
  Real.sqrt_nonneg _

theorem coeffNorm1_nonneg (p : MvPolynomial σ ℝ) : 0 ≤ coeffNorm1 p :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp] theorem coeffNorm_zero : coeffNorm (0 : MvPolynomial σ ℝ) = 0 := by
  simp [coeffNorm]

@[simp] theorem coeffNorm1_zero : coeffNorm1 (0 : MvPolynomial σ ℝ) = 0 := by
  simp [coeffNorm1]

/-- `‖p‖₂` may be computed over any finite set of monomials containing the support. -/
theorem coeffNorm_eq_of_support_subset {p : MvPolynomial σ ℝ} {U : Finset (σ →₀ ℕ)}
    (h : p.support ⊆ U) : coeffNorm p = Real.sqrt (∑ m ∈ U, p.coeff m ^ 2) := by
  unfold coeffNorm
  congr 1
  refine Finset.sum_subset h fun m _ hm ↦ ?_
  rw [notMem_support_iff.1 hm]
  ring

/-- `‖p‖₁` may be computed over any finite set of monomials containing the support. -/
theorem coeffNorm1_eq_of_support_subset {p : MvPolynomial σ ℝ} {U : Finset (σ →₀ ℕ)}
    (h : p.support ⊆ U) : coeffNorm1 p = ∑ m ∈ U, |p.coeff m| := by
  unfold coeffNorm1
  refine Finset.sum_subset h fun m _ hm ↦ ?_
  rw [notMem_support_iff.1 hm, abs_zero]

/-- The triangle inequality for `‖·‖₂`. -/
theorem coeffNorm_add_le (p q : MvPolynomial σ ℝ) :
    coeffNorm (p + q) ≤ coeffNorm p + coeffNorm q := by
  classical
  set U := p.support ∪ q.support
  rw [coeffNorm_eq_of_support_subset (support_add.trans le_rfl : (p + q).support ⊆ U),
    coeffNorm_eq_of_support_subset (Finset.subset_union_left : p.support ⊆ U),
    coeffNorm_eq_of_support_subset (Finset.subset_union_right : q.support ⊆ U)]
  set a := ∑ m ∈ U, p.coeff m ^ 2
  set b := ∑ m ∈ U, q.coeff m ^ 2
  have ha : 0 ≤ a := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hb : 0 ≤ b := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  -- `∑ pq ≤ √a √b` by Cauchy–Schwarz.
  have hcs : ∑ m ∈ U, p.coeff m * q.coeff m ≤ Real.sqrt a * Real.sqrt b := by
    rw [← Real.sqrt_mul ha]
    calc ∑ m ∈ U, p.coeff m * q.coeff m ≤ |∑ m ∈ U, p.coeff m * q.coeff m| := le_abs_self _
      _ = Real.sqrt ((∑ m ∈ U, p.coeff m * q.coeff m) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hsum : ∑ m ∈ U, (p + q).coeff m ^ 2 =
      a + 2 * ∑ m ∈ U, p.coeff m * q.coeff m + b := by
    simp only [a, b, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    ring
  rw [hsum]
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have h0 : 0 ≤ Real.sqrt a + Real.sqrt b := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc Real.sqrt (a + 2 * ∑ m ∈ U, p.coeff m * q.coeff m + b)
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq h0

theorem coeffNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    coeffNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffNorm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (coeffNorm_add_le _ _).trans (add_le_add_right ih _)

theorem coeffNorm_smul (c : ℝ) (p : MvPolynomial σ ℝ) : coeffNorm (c • p) = |c| * coeffNorm p := by
  rw [coeffNorm_eq_of_support_subset (support_smul : (c • p).support ⊆ p.support), coeffNorm]
  simp only [coeff_smul, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Multiplying by a monomial shifts the coefficients, so it preserves `‖·‖₂`. -/
theorem coeffNorm_monomial_mul (α : σ →₀ ℕ) (p : MvPolynomial σ ℝ) :
    coeffNorm (monomial α 1 * p) = coeffNorm p := by
  classical
  have hsupp : (monomial α (1 : ℝ) * p).support ⊆ p.support.image (α + ·) := by
    intro m hm
    have := support_mul (monomial α (1 : ℝ)) p hm
    rw [support_monomial, ite_eq_right one_ne_zero, Finset.mem_add] at this
    obtain ⟨x, hx, y, hy, rfl⟩ := this
    rw [Finset.mem_singleton.1 hx]
    exact Finset.mem_image_of_mem _ hy
  rw [coeffNorm_eq_of_support_subset hsupp, Finset.sum_image (fun _ _ _ _ h ↦ add_left_cancel h)]
  simp [coeffNorm, coeff_monomial_mul]

theorem coeffNorm_monomial (s : σ →₀ ℕ) (a : ℝ) : coeffNorm (monomial s a) = |a| := by
  classical
  rw [coeffNorm_eq_of_support_subset (support_monomial_subset : (monomial s a).support ⊆ {s})]
  simp [Real.sqrt_sq_eq_abs]

theorem coeffNorm_C (a : ℝ) : coeffNorm (C a : MvPolynomial σ ℝ) = |a| := by
  rw [C_apply, coeffNorm_monomial]

/-- `‖h m‖₂ ≤ ‖h‖₂ ‖m‖₁`. -/
theorem coeffNorm_mul_le (h m : MvPolynomial σ ℝ) :
    coeffNorm (h * m) ≤ coeffNorm h * coeffNorm1 m := by
  classical
  have hm : h * m = ∑ α ∈ m.support, m.coeff α • (monomial α 1 * h) := by
    conv_lhs => rw [m.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one, mul_comm]
  rw [hm, coeffNorm1, Finset.mul_sum]
  refine (coeffNorm_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [coeffNorm_smul, coeffNorm_monomial_mul, mul_comm]

theorem coeffNorm1_add_le (p q : MvPolynomial σ ℝ) :
    coeffNorm1 (p + q) ≤ coeffNorm1 p + coeffNorm1 q := by
  classical
  set U := p.support ∪ q.support
  rw [coeffNorm1_eq_of_support_subset (support_add.trans le_rfl : (p + q).support ⊆ U),
    coeffNorm1_eq_of_support_subset (Finset.subset_union_left : p.support ⊆ U),
    coeffNorm1_eq_of_support_subset (Finset.subset_union_right : q.support ⊆ U),
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun m _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact abs_add_le _ _

theorem coeffNorm1_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    coeffNorm1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffNorm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (coeffNorm1_add_le _ _).trans (add_le_add_right ih _)

theorem coeffNorm1_smul (c : ℝ) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (c • p) = |c| * coeffNorm1 p := by
  rw [coeffNorm1_eq_of_support_subset (support_smul : (c • p).support ⊆ p.support), coeffNorm1,
    Finset.mul_sum]
  simp [abs_mul]

/-- Multiplying by a monomial shifts the coefficients, so it preserves `‖·‖₁`. -/
theorem coeffNorm1_monomial_mul (α : σ →₀ ℕ) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (monomial α 1 * p) = coeffNorm1 p := by
  classical
  have hsupp : (monomial α (1 : ℝ) * p).support ⊆ p.support.image (α + ·) := by
    intro m hm
    have := support_mul (monomial α (1 : ℝ)) p hm
    rw [support_monomial, ite_eq_right one_ne_zero, Finset.mem_add] at this
    obtain ⟨x, hx, y, hy, rfl⟩ := this
    rw [Finset.mem_singleton.1 hx]
    exact Finset.mem_image_of_mem _ hy
  rw [coeffNorm1_eq_of_support_subset hsupp,
    Finset.sum_image (fun _ _ _ _ h ↦ add_left_cancel h)]
  simp [coeffNorm1, coeff_monomial_mul]

/-- `‖g h‖₁ ≤ ‖g‖₁ ‖h‖₁`. -/
theorem coeffNorm1_mul_le (g h : MvPolynomial σ ℝ) :
    coeffNorm1 (g * h) ≤ coeffNorm1 g * coeffNorm1 h := by
  classical
  have hg : g * h = ∑ α ∈ g.support, g.coeff α • (monomial α 1 * h) := by
    conv_lhs => rw [g.as_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [smul_eq_C_mul, ← mul_assoc, C_mul_monomial, mul_one]
  rw [hg]
  conv_rhs => rw [coeffNorm1, Finset.sum_mul]
  refine (coeffNorm1_sum_le _ _).trans (Finset.sum_le_sum fun α _ ↦ ?_)
  rw [coeffNorm1_smul, coeffNorm1_monomial_mul]

/-- `‖g‖₁² ≤ (number of monomials) · ‖g‖₂²`, by Cauchy–Schwarz. -/
theorem coeffNorm1_sq_le (g : MvPolynomial σ ℝ) :
    coeffNorm1 g ^ 2 ≤ g.support.card * coeffNorm g ^ 2 := by
  rw [coeffNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _), coeffNorm1]
  have := sq_sum_le_card_mul_sum_sq (s := g.support) (f := fun m ↦ |g.coeff m|)
  simpa [sq_abs] using this

/-! ### Counting monomials -/

/-- Every monomial of degree at most `d` is a sum of `d` terms, each a variable or `0`. -/
theorem exists_fin_option_of_degree_le {d : ℕ} {m : σ →₀ ℕ} (hm : m.degree ≤ d) :
    ∃ c : Fin d → Option σ, (∑ j, (c j).elim 0 fun i ↦ Finsupp.single i 1) = m := by
  classical
  induction d generalizing m with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact ((Finsupp.degree_eq_zero_iff m).1 (Nat.le_zero.1 hm)).symm
  | succ d ih =>
    by_cases h0 : m = 0
    · exact ⟨fun _ ↦ none, by simp [h0]⟩
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.2 h0
    have hle : Finsupp.single i 1 ≤ m :=
      Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi))
    have hsplit : m - Finsupp.single i 1 + Finsupp.single i 1 = m := tsub_add_cancel_of_le hle
    have hdeg : (m - Finsupp.single i 1).degree ≤ d := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this
      omega
    obtain ⟨c, hc⟩ := ih hdeg
    refine ⟨Fin.cons (some i) c, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Option.elim_some, hc]
    rw [add_comm, hsplit]

/-- In `n` variables there are at most `(n + 1)^d` monomials of degree at most `d`. -/
theorem card_le_of_degree_le [Fintype σ] (s : Finset (σ →₀ ℕ)) {d : ℕ}
    (h : ∀ m ∈ s, m.degree ≤ d) : s.card ≤ (Fintype.card σ + 1) ^ d := by
  classical
  let F : (Fin d → Option σ) → (σ →₀ ℕ) :=
    fun c ↦ ∑ j, (c j).elim 0 fun i ↦ Finsupp.single i 1
  calc s.card ≤ (Finset.univ.image F).card := by
        refine Finset.card_le_card fun m hm ↦ ?_
        obtain ⟨c, hc⟩ := exists_fin_option_of_degree_le (h m hm)
        exact Finset.mem_image.2 ⟨c, Finset.mem_univ _, hc⟩
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = (Fintype.card σ + 1) ^ d := by
        simp [Finset.card_univ, Fintype.card_option]

/-- A polynomial in `n` variables of degree `d` has at most `(n + 1)^d` monomials. -/
theorem card_support_le [Fintype σ] {R : Type*} [CommSemiring R] (p : MvPolynomial σ R) :
    p.support.card ≤ (Fintype.card σ + 1) ^ p.totalDegree :=
  card_le_of_degree_le _ fun _ hm ↦ le_totalDegree hm

/-! ### Approximate soundness -/

section Soundness

variable {K : Type*} [Field K] [Algebra K ℝ]

/-- The size of a proof: `∑ S, ‖p S‖₁ ∏ i ∈ S, ‖fᵢ‖₂`. -/
noncomputable def Proof.size {A : System σ K} {g : MvPolynomial σ K} {k : ℕ} (P : Proof A g k) :
    ℝ :=
  ∑ S, coeffNorm1 (toReal (P.mult S)) * ∏ i ∈ S, coeffNorm (toReal (A.get i))

omit [Algebra K ℝ] in
/-- The degree budget of approximate soundness: at degree `0`, or when no constraint is constant,
`∑ i ∈ S, max (deg fᵢ) r ≤ (1 + r) ∑ i ∈ S, deg fᵢ`. -/
theorem System.sum_max_le {A : System σ K} {r : ℕ}
    (hr : r = 0 ∨ ∀ i, (A.get i).totalDegree ≠ 0) (S : Finset (Fin A.length)) :
    ∑ i ∈ S, max (A.get i).totalDegree r ≤ A.degree S + r * A.degree S := by
  rcases hr with rfl | hr
  · simp [System.degree]
  · have h₁ : ∑ i ∈ S, max (A.get i).totalDegree r ≤ ∑ i ∈ S, ((A.get i).totalDegree + r) :=
      Finset.sum_le_sum fun i _ ↦ max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at h₁
    have h₂ : S.card ≤ A.degree S := by
      rw [Finset.card_eq_sum_ones, System.degree]
      exact Finset.sum_le_sum fun i _ ↦ Nat.one_le_iff_ne_zero.2 (hr i)
    have h₃ : S.card * r ≤ r * A.degree S := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left r h₂
    unfold System.degree at h₃ ⊢
    omega

/-- **Approximate soundness.** If `Ẽ` satisfies `A` up to `η` at degree `r` and `P` proves
`g ≥ 0` from `A` at degree `k`, then `Ẽ (h g) ≥ -η ‖h‖₂ · P.size` for every sum of squares `h`
with `deg h + r k + k ≤ ℓ`.

Either `r = 0` (as for the output of the algorithm, [BKS23, Fact 3.6]) or no constraint of `A`
is constant: constant constraints cannot be factored out of an approximate inequality. -/
theorem PseudoExpectation.ApproxSatisfies.apply_proof {ℓ : ℕ} {E : PseudoExpectation σ ℓ}
    {A : System σ K} {η : ℝ} {r : ℕ} (hη : 0 ≤ η) (hA : E.ApproxSatisfies A η r)
    (hr : r = 0 ∨ ∀ i, (A.get i).totalDegree ≠ 0) {g : MvPolynomial σ K} {k : ℕ}
    (P : Proof A g k) (h : MvPolynomial σ ℝ) (hh : IsSumSq h)
    (hdeg : h.totalDegree + (r * k + k) ≤ ℓ) :
    -(η * coeffNorm h * P.size) ≤ E (h * toReal g) := by
  classical
  have hg : E (h * toReal g) = ∑ S, E (h * toReal (P.mult S * A.prod S)) := by
    conv_lhs => rw [P.eq_sum]
    rw [toReal_sum, Finset.mul_sum, E.map_sum]
  rw [hg, Proof.size, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun S _ ↦ ?_
  by_cases hS : P.mult S = 0
  · simp [hS]
  rw [toReal_mul, ← mul_assoc h]
  have hP := P.degree_le S hS
  have hm := totalDegree_toReal_le (P.mult S)
  have hmul := totalDegree_mul h (toReal (P.mult S))
  have hsum := System.sum_max_le hr S
  have hrk : r * A.degree S ≤ r * k := Nat.mul_le_mul_left r (by omega)
  have happ := hA S (h * toReal (P.mult S)) (hh.mul (P.isSOS_mult S)) (by omega)
  refine le_trans ?_ happ
  have hprod : 0 ≤ ∏ i ∈ S, coeffNorm (toReal (A.get i)) :=
    Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _
  have hnorm := coeffNorm_mul_le h (toReal (P.mult S))
  rw [neg_le_neg_iff, ← mul_assoc, mul_assoc η, mul_assoc η]
  have key := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnorm hprod) hη
  calc _ ≤ _ := key
    _ = _ := by ring

/-! ### Bounding the size by the bit complexity -/

/-- A real polynomial with coefficients at most `M` has `‖p‖₁ ≤ (number of monomials) · M`. -/
theorem coeffNorm1_le {p : MvPolynomial σ ℝ} {M : ℝ} (h : ∀ m, |p.coeff m| ≤ M) :
    coeffNorm1 p ≤ p.support.card * M := by
  unfold coeffNorm1
  simpa using Finset.sum_le_card_nsmul p.support _ M fun m _ ↦ h m

/-- A real polynomial with coefficients at most `M` has `‖p‖₂ ≤ (number of monomials) · M`. -/
theorem coeffNorm_le {p : MvPolynomial σ ℝ} {M : ℝ} (hM : 0 ≤ M) (h : ∀ m, |p.coeff m| ≤ M) :
    coeffNorm p ≤ p.support.card * M := by
  have hsq : ∑ m ∈ p.support, p.coeff m ^ 2 ≤ p.support.card * M ^ 2 := by
    simpa using Finset.sum_le_card_nsmul p.support _ (M ^ 2) fun m _ ↦
      (sq_le_sq₀ (abs_nonneg _) hM).2 (h m) |>.trans_eq' (sq_abs _).symm
  have hcard : Real.sqrt (p.support.card : ℝ) ≤ p.support.card := by
    calc Real.sqrt (p.support.card : ℝ) ≤ Real.sqrt ((p.support.card : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_self_pow two_ne_zero p.support.card)
      _ = p.support.card := Real.sqrt_sq (Nat.cast_nonneg _)
  calc coeffNorm p ≤ Real.sqrt (p.support.card * M ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt p.support.card * M := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]
    _ ≤ p.support.card * M := mul_le_mul_of_nonneg_right hcard hM

/-- **Size from bit complexity.** A proof of degree `k` and bit complexity `B ≥ 0` from `m`
constraints in `n` variables has `P.size ≤ 2^m ((n + 1)^k 2^B) ((n + 1)^(∑ deg fᵢ) (2^B)^m)`. -/
theorem Proof.size_le [Fintype σ] {A : System σ K} {g : MvPolynomial σ K} {k : ℕ}
    (P : Proof A g k) {B : ℝ} (hB : 0 ≤ B) (hP : P.BitComplexityLE B) :
    P.size ≤ 2 ^ A.length * (((Fintype.card σ + 1 : ℝ) ^ k * 2 ^ B) *
      ((Fintype.card σ + 1 : ℝ) ^ A.degree Finset.univ * ((2 : ℝ) ^ B) ^ A.length)) := by
  classical
  obtain ⟨hA, -, hm⟩ := hP
  set N : ℝ := Fintype.card σ + 1 with hNdef
  have hN : 1 ≤ N := by simp [N]
  have h2B : 1 ≤ (2 : ℝ) ^ B := Real.one_le_rpow (by norm_num) hB
  have hcard : ∀ p : MvPolynomial σ ℝ, (p.support.card : ℝ) ≤ N ^ p.totalDegree := fun p ↦ by
    rw [hNdef]
    exact_mod_cast card_support_le p
  -- Each multiplier has `‖p S‖₁ ≤ (n + 1)^k 2^B`.
  have hmult : ∀ S, coeffNorm1 (toReal (P.mult S)) ≤ N ^ k * 2 ^ B := by
    intro S
    by_cases hS : P.mult S = 0
    · simp only [hS, toReal_zero, coeffNorm1_zero]
      positivity
    have hcoef : ∀ m, |(toReal (P.mult S)).coeff m| ≤ 2 ^ B := fun m ↦ by
      simpa [toReal, coeff_map] using hm S m
    have hdeg : (toReal (P.mult S)).totalDegree ≤ k :=
      (totalDegree_toReal_le _).trans (by have := P.degree_le S hS; omega)
    refine (coeffNorm1_le hcoef).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (hcard _).trans (pow_le_pow_right₀ hN hdeg)
  -- Each constraint has `‖fᵢ‖₂ ≤ (n + 1)^(deg fᵢ) 2^B`.
  set F : Fin A.length → ℝ := fun i ↦ N ^ (A.get i).totalDegree * 2 ^ B
  have hF1 : ∀ i, 1 ≤ F i := fun i ↦ one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN) h2B
  have hcons : ∀ i, coeffNorm (toReal (A.get i)) ≤ F i := by
    intro i
    have hcoef : ∀ m, |(toReal (A.get i)).coeff m| ≤ 2 ^ B := fun m ↦ by
      simpa [toReal, coeff_map] using hA _ (List.get_mem A i) m
    refine (coeffNorm_le (by positivity) hcoef).trans
      (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (hcard _).trans (pow_le_pow_right₀ hN (totalDegree_toReal_le _))
  -- The product over `S` is at most the product over all constraints, since each `F i ≥ 1`.
  have hprod : ∀ S : Finset (Fin A.length),
      ∏ i ∈ S, coeffNorm (toReal (A.get i)) ≤ ∏ i, F i := by
    intro S
    have hS : ∏ i ∈ S, coeffNorm (toReal (A.get i)) ≤ ∏ i ∈ S, F i :=
      Finset.prod_le_prod₀ (fun i _ ↦ coeffNorm_nonneg _) fun i _ ↦ hcons i
    have hrest : 1 ≤ ∏ i ∈ Finset.univ \ S, F i := by
      simpa using Finset.prod_le_prod₀ (s := Finset.univ \ S) (fun _ _ ↦ zero_le_one)
        fun i _ ↦ hF1 i
    rw [← Finset.prod_sdiff (Finset.subset_univ S)]
    calc ∏ i ∈ S, coeffNorm (toReal (A.get i)) ≤ ∏ i ∈ S, F i := hS
      _ ≤ (∏ i ∈ Finset.univ \ S, F i) * ∏ i ∈ S, F i :=
          le_mul_of_one_le_left (Finset.prod_nonneg fun i _ ↦ zero_le_one.trans (hF1 i)) hrest
  have hall : ∏ i, F i = N ^ A.degree Finset.univ * ((2 : ℝ) ^ B) ^ A.length := by
    simp only [F, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, System.degree]
  calc P.size ≤ ∑ _S : Finset (Fin A.length),
        (N ^ k * 2 ^ B) * (N ^ A.degree Finset.univ * ((2 : ℝ) ^ B) ^ A.length) := by
        unfold Proof.size
        refine Finset.sum_le_sum fun S _ ↦ ?_
        rw [← hall]
        exact mul_le_mul (hmult S) (hprod S)
          (Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        ring

/-- **Approximate soundness with bit complexity.** If `Ẽ` satisfies `A` up to `η` and `g ≥ 0`
has a proof of degree `k` and bit complexity `B ≥ 0` from the `m` constraints `fᵢ` of `A` in `n`
variables, then `Ẽ (h g) ≥ -η ‖h‖₂ · 2^m ((n + 1)^k 2^B) ((n + 1)^(∑ deg fᵢ) (2^B)^m)` for every
sum of squares `h` with `deg h + r k + k ≤ ℓ`. -/
theorem PseudoExpectation.ApproxSatisfies.apply_derivesWithin [Fintype σ] {ℓ : ℕ}
    {E : PseudoExpectation σ ℓ} {A : System σ K} {η : ℝ} {r : ℕ} (hη : 0 ≤ η)
    (hA : E.ApproxSatisfies A η r) (hr : r = 0 ∨ ∀ i, (A.get i).totalDegree ≠ 0)
    {g : MvPolynomial σ K} {k : ℕ} {B : ℝ} (hB : 0 ≤ B) (hg : A ⊢[k, B] g)
    (h : MvPolynomial σ ℝ) (hh : IsSumSq h) (hdeg : h.totalDegree + (r * k + k) ≤ ℓ) :
    -(η * coeffNorm h * (2 ^ A.length * (((Fintype.card σ + 1 : ℝ) ^ k * 2 ^ B) *
      ((Fintype.card σ + 1 : ℝ) ^ A.degree Finset.univ * ((2 : ℝ) ^ B) ^ A.length)))) ≤
      E (h * toReal g) := by
  obtain ⟨P, hP⟩ := hg
  refine le_trans ?_ (hA.apply_proof hη hr P h hh hdeg)
  rw [neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_left (P.size_le hB hP)
    (mul_nonneg hη (coeffNorm_nonneg h))

end Soundness

end SoS
