module

public import Background.SumOfSquares.Approximate

/-!
# Sum-of-squares proofs with bounded multipliers

Real sum-of-squares proofs that also bound the norms `‖·‖₁` (`SoS.coeffNorm1`, the sum of the
absolute values of the coefficients) of their multipliers. These norms are what approximate
soundness pays for (`SoS.PseudoExpectation.ApproxSatisfies.apply_proof`), and they bound the bit
complexity of a proof (`SoS.DerivesN.derivesWithin`). Unlike bounds on single coefficients, they
compose: `‖p + q‖₁ ≤ ‖p‖₁ + ‖q‖₁` and `‖p q‖₁ ≤ ‖p‖₁ ‖q‖₁`.

* `SoS.DerivesN A k M g`: a degree-`k` proof of `g ≥ 0` from `A` whose multipliers all have
  `‖·‖₁ ≤ M`.
* `SoS.DerivesEq A k M q`: `A` proves `q = 0`, that is, both `q ≥ 0` and `-q ≥ 0`. The equality
  constraints `h = 0` of `A` (both `h` and `-h` in `A`) are the basic examples
  (`SoS.DerivesEq.of_mem`). Equalities may be multiplied by a sum of squares `s` at degree `deg s`
  more (`SoS.DerivesEq.mulSOS`), and by any polynomial `r` at degree `2 deg r` more
  (`SoS.DerivesEq.mul`), since `r = ((r + 1) / 2)² - ((r - 1) / 2)²`.
* The rules of `Background/SumOfSquares/Calculus.lean` with norms: `zero`, `ofIsSOS`, `of_mem`,
  `add`, `sum`, `mulSOS`, `smul`; and `SoS.DerivesN.of_eq`, which replaces `g` by a `g'` with
  `A ⊢ g' - g = 0`.

Constraints are used by membership (`f ∈ A`), so a proof built for some constraints applies to
every system that contains them.
-/

@[expose] public section

namespace SoS

open MvPolynomial

variable {σ : Type*}

/-! ### The norm `‖·‖₁` -/

theorem abs_coeff_le_coeffNorm1 (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |p.coeff m| ≤ coeffNorm1 p := by
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (f := fun m ↦ |p.coeff m|) (fun _ _ ↦ abs_nonneg _) hm
  · rw [notMem_support_iff.1 hm, abs_zero]
    exact coeffNorm1_nonneg p

theorem coeffNorm1_monomial (s : σ →₀ ℕ) (a : ℝ) : coeffNorm1 (monomial s a) = |a| := by
  classical
  rw [coeffNorm1_eq_of_support_subset (support_monomial_subset : (monomial s a).support ⊆ {s})]
  simp

theorem coeffNorm1_C (a : ℝ) : coeffNorm1 (C a : MvPolynomial σ ℝ) = |a| :=
  coeffNorm1_monomial 0 a

theorem coeffNorm1_one : coeffNorm1 (1 : MvPolynomial σ ℝ) = 1 := by
  simpa using coeffNorm1_C (σ := σ) 1

theorem coeffNorm1_X (i : σ) : coeffNorm1 (X i : MvPolynomial σ ℝ) = 1 := by
  rw [X, coeffNorm1_monomial, abs_one]

theorem coeffNorm1_neg (p : MvPolynomial σ ℝ) : coeffNorm1 (-p) = coeffNorm1 p := by
  simpa using coeffNorm1_smul (-1) p

theorem coeffNorm1_sub_le (p q : MvPolynomial σ ℝ) :
    coeffNorm1 (p - q) ≤ coeffNorm1 p + coeffNorm1 q := by
  simpa [sub_eq_add_neg, coeffNorm1_neg] using coeffNorm1_add_le p (-q)

theorem coeffNorm1_C_mul (a : ℝ) (p : MvPolynomial σ ℝ) :
    coeffNorm1 (C a * p) = |a| * coeffNorm1 p := by
  rw [← smul_eq_C_mul, coeffNorm1_smul]

theorem coeffNorm1_pow_le (p : MvPolynomial σ ℝ) (n : ℕ) :
    coeffNorm1 (p ^ n) ≤ coeffNorm1 p ^ n := by
  induction n with
  | zero => simp [coeffNorm1_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coeffNorm1_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (coeffNorm1_nonneg _))

theorem coeffNorm1_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) :
    coeffNorm1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, coeffNorm1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffNorm1_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (coeffNorm1_mul_le _ _).trans (mul_le_mul_of_nonneg_left ih (coeffNorm1_nonneg _))

/-- `‖p‖₂ ≤ ‖p‖₁`. -/
theorem coeffNorm_le_coeffNorm1 (p : MvPolynomial σ ℝ) : coeffNorm p ≤ coeffNorm1 p := by
  rw [coeffNorm, coeffNorm1]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ ↦ abs_nonneg _, ?_⟩
  calc ∑ m ∈ p.support, p.coeff m ^ 2 = ∑ m ∈ p.support, |p.coeff m| ^ 2 := by
        simp only [sq_abs]
    _ ≤ (∑ m ∈ p.support, |p.coeff m|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ ↦ abs_nonneg _

/-- A product of variables, indexed by a function, has `‖·‖₁ ≤ 1`. -/
theorem coeffNorm1_prod_X_le' {ι : Type*} [Fintype ι] (Q : ι → σ) :
    coeffNorm1 (∏ j, X (Q j) : MvPolynomial σ ℝ) ≤ 1 :=
  (coeffNorm1_prod_le _ _).trans (by simp [coeffNorm1_X])

/-- A product of variables has `‖·‖₁ ≤ 1`. -/
theorem coeffNorm1_prod_X_le (s : Finset σ) :
    coeffNorm1 (∏ i ∈ s, X i : MvPolynomial σ ℝ) ≤ 1 :=
  (coeffNorm1_prod_le s _).trans (by simp [coeffNorm1_X])

/-! ### Real polynomials -/

@[simp] theorem toReal_real (p : MvPolynomial σ ℝ) : toReal p = p := by
  simp [toReal, Algebra.algebraMap_self, map_id]

theorem IsSOS.const {c : ℝ} (hc : 0 ≤ c) : IsSOS (C c : MvPolynomial σ ℝ) := by
  have : (C c : MvPolynomial σ ℝ) = C (Real.sqrt c) ^ 2 := by
    rw [← C_pow, Real.sq_sqrt hc]
  rw [this]
  exact IsSOS.sq _

/-! ### Proofs with bounded multipliers -/

/-- `A ⊢[k] g` by a proof whose multipliers all have `‖·‖₁ ≤ M`. -/
def DerivesN (A : System σ ℝ) (k : ℕ) (M : ℝ) (g : MvPolynomial σ ℝ) : Prop :=
  ∃ P : Proof A g k, ∀ S, coeffNorm1 (P.mult S) ≤ M

/-- `A ⊢[k] q = 0` with multipliers of `‖·‖₁ ≤ M`: proofs of `q ≥ 0` and of `-q ≥ 0`. -/
def DerivesEq (A : System σ ℝ) (k : ℕ) (M : ℝ) (q : MvPolynomial σ ℝ) : Prop :=
  DerivesN A k M q ∧ DerivesN A k M (-q)

namespace DerivesN

variable {A : System σ ℝ} {k k' : ℕ} {M M' M₁ M₂ : ℝ} {g g' g₁ g₂ : MvPolynomial σ ℝ}

theorem nonneg (h : DerivesN A k M g) : 0 ≤ M := by
  obtain ⟨P, hP⟩ := h
  exact (coeffNorm1_nonneg _).trans (hP ∅)

theorem mono (h : DerivesN A k M g) (hk : k ≤ k') (hM : M ≤ M') : DerivesN A k' M' g := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.weaken hk, fun S ↦ (hP S).trans hM⟩

theorem congr (h : DerivesN A k M g) (e : g = g') : DerivesN A k M g' := e ▸ h

theorem zero (A : System σ ℝ) (k : ℕ) (hM : 0 ≤ M) : DerivesN A k M 0 :=
  ⟨Proof.zero A k, fun S ↦ by simpa [Proof.zero] using hM⟩

theorem ofIsSOS (A : System σ ℝ) {p : MvPolynomial σ ℝ} (hp : IsSOS p)
    (hdeg : p.totalDegree ≤ k) (hM : coeffNorm1 p ≤ M) : DerivesN A k M p := by
  refine ⟨Proof.ofIsSOS A hp hdeg, fun S ↦ ?_⟩
  simp only [Proof.ofIsSOS]
  split_ifs
  · exact hM
  · simpa using (coeffNorm1_nonneg p).trans hM

theorem of_mem {f : MvPolynomial σ ℝ} (hf : f ∈ A) (hdeg : f.totalDegree ≤ k) (hM : 1 ≤ M) :
    DerivesN A k M f := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  refine ⟨Proof.assumption A i hdeg, fun S ↦ ?_⟩
  simp only [Proof.assumption]
  split_ifs
  · simpa [coeffNorm1_one] using hM
  · simpa using zero_le_one.trans hM

theorem add (h₁ : DerivesN A k M₁ g₁) (h₂ : DerivesN A k M₂ g₂) :
    DerivesN A k (M₁ + M₂) (g₁ + g₂) := by
  obtain ⟨P₁, h₁⟩ := h₁
  obtain ⟨P₂, h₂⟩ := h₂
  exact ⟨P₁.add P₂, fun S ↦ (coeffNorm1_add_le _ _).trans (add_le_add (h₁ S) (h₂ S))⟩

theorem mulSOS {q : MvPolynomial σ ℝ} (hq : IsSOS q) (h : DerivesN A k M g) :
    DerivesN A (q.totalDegree + k) (coeffNorm1 q * M) (q * g) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.mulSOS hq, fun S ↦ (coeffNorm1_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (hP S) (coeffNorm1_nonneg _))⟩

theorem smul {c : ℝ} (hc : 0 ≤ c) (h : DerivesN A k M g) : DerivesN A k (c * M) (C c * g) := by
  have := h.mulSOS (IsSOS.const hc)
  rwa [totalDegree_C, zero_add, coeffNorm1_C, abs_of_nonneg hc] at this

theorem sum {ι : Type*} (s : Finset ι) {g : ι → MvPolynomial σ ℝ} {M : ι → ℝ}
    (h : ∀ i ∈ s, DerivesN A k (M i) (g i)) : DerivesN A k (∑ i ∈ s, M i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero A k le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-- Norms bound the bit complexity. -/
theorem derivesWithin {B : ℝ} (h : DerivesN A k M g) (hM : M ≤ 2 ^ B)
    (hA : ∀ f ∈ A, CoeffsLE f (2 ^ B)) (hg : CoeffsLE g (2 ^ B)) : A ⊢[k, B] g := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, hA, hg, fun S m ↦ ?_⟩
  simpa using (abs_coeff_le_coeffNorm1 (P.mult S) m).trans ((hP S).trans hM)

end DerivesN

namespace DerivesEq

variable {A : System σ ℝ} {k k' : ℕ} {M M' M₁ M₂ : ℝ} {q q' q₁ q₂ : MvPolynomial σ ℝ}

theorem nonneg (h : DerivesEq A k M q) : 0 ≤ M := h.1.nonneg

theorem mono (h : DerivesEq A k M q) (hk : k ≤ k') (hM : M ≤ M') : DerivesEq A k' M' q :=
  ⟨h.1.mono hk hM, h.2.mono hk hM⟩

theorem congr (h : DerivesEq A k M q) (e : q = q') : DerivesEq A k M q' := e ▸ h

theorem zero (A : System σ ℝ) (k : ℕ) (hM : 0 ≤ M) : DerivesEq A k M 0 :=
  ⟨DerivesN.zero A k hM, by simpa using DerivesN.zero A k hM⟩

/-- An equality constraint `h = 0` of `A`: both `h` and `-h` are constraints. -/
theorem of_mem {h : MvPolynomial σ ℝ} (h₁ : h ∈ A) (h₂ : -h ∈ A) (hdeg : h.totalDegree ≤ k)
    (hM : 1 ≤ M) : DerivesEq A k M h :=
  ⟨DerivesN.of_mem h₁ hdeg hM, DerivesN.of_mem h₂ (by rwa [totalDegree_neg]) hM⟩

theorem neg (h : DerivesEq A k M q) : DerivesEq A k M (-q) :=
  ⟨h.2, by simpa using h.1⟩

theorem add (h₁ : DerivesEq A k M₁ q₁) (h₂ : DerivesEq A k M₂ q₂) :
    DerivesEq A k (M₁ + M₂) (q₁ + q₂) :=
  ⟨h₁.1.add h₂.1, (h₁.2.add h₂.2).congr (by ring)⟩

theorem sub (h₁ : DerivesEq A k M₁ q₁) (h₂ : DerivesEq A k M₂ q₂) :
    DerivesEq A k (M₁ + M₂) (q₁ - q₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

theorem sum {ι : Type*} (s : Finset ι) {q : ι → MvPolynomial σ ℝ} {M : ι → ℝ}
    (h : ∀ i ∈ s, DerivesEq A k (M i) (q i)) : DerivesEq A k (∑ i ∈ s, M i) (∑ i ∈ s, q i) :=
  ⟨DerivesN.sum s fun i hi ↦ (h i hi).1, by
    simpa [Finset.sum_neg_distrib] using DerivesN.sum s fun i hi ↦ (h i hi).2⟩

theorem mulSOS {s : MvPolynomial σ ℝ} (hs : IsSOS s) (h : DerivesEq A k M q) :
    DerivesEq A (s.totalDegree + k) (coeffNorm1 s * M) (s * q) :=
  ⟨h.1.mulSOS hs, by simpa [mul_neg] using h.2.mulSOS hs⟩

theorem smul (c : ℝ) (h : DerivesEq A k M q) : DerivesEq A k (|c| * M) (C c * q) := by
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc]
    exact ⟨h.1.smul hc, by simpa [mul_neg] using h.2.smul hc⟩
  · rw [abs_of_nonpos hc]
    have e : C c * q = C (-c) * -q := by rw [C_neg]; ring
    rw [e]
    exact ⟨h.2.smul (neg_nonneg.2 hc), by simpa [mul_neg] using h.1.smul (neg_nonneg.2 hc)⟩

/-- **Multiplying an equality by any polynomial** `r`, at degree `2 deg r` more:
`r q = ((r + 1) / 2)² q + ((r - 1) / 2)² (-q)`. -/
theorem mul (r : MvPolynomial σ ℝ) (h : DerivesEq A k M q) :
    DerivesEq A (2 * r.totalDegree + k) ((coeffNorm1 r + 1) ^ 2 * M) (r * q) := by
  set a := C (1 / 2 : ℝ) * (r + 1)
  set b := C (1 / 2 : ℝ) * (r - 1)
  have hM := h.nonneg
  have hr := coeffNorm1_nonneg r
  have hda : (a ^ 2).totalDegree ≤ 2 * r.totalDegree := by
    refine (totalDegree_pow _ 2).trans ?_
    have : a.totalDegree ≤ r.totalDegree := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_add _ _).trans (max_le le_rfl (by simp))
    omega
  have hdb : (b ^ 2).totalDegree ≤ 2 * r.totalDegree := by
    refine (totalDegree_pow _ 2).trans ?_
    have : b.totalDegree ≤ r.totalDegree := by
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (totalDegree_sub _ _).trans (max_le le_rfl (by simp))
    omega
  have hna : coeffNorm1 (a ^ 2) ≤ (coeffNorm1 r + 1) ^ 2 / 2 := by
    refine (coeffNorm1_pow_le _ 2).trans ?_
    have : coeffNorm1 a ≤ (coeffNorm1 r + 1) / 2 := by
      rw [coeffNorm1_C_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := coeffNorm1_add_le r 1
      rw [coeffNorm1_one] at this
      linarith
    nlinarith [coeffNorm1_nonneg a]
  have hnb : coeffNorm1 (b ^ 2) ≤ (coeffNorm1 r + 1) ^ 2 / 2 := by
    refine (coeffNorm1_pow_le _ 2).trans ?_
    have : coeffNorm1 b ≤ (coeffNorm1 r + 1) / 2 := by
      rw [coeffNorm1_C_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := coeffNorm1_sub_le r 1
      rw [coeffNorm1_one] at this
      linarith
    nlinarith [coeffNorm1_nonneg b]
  have hab : a ^ 2 - b ^ 2 = r := by
    have h4 : (C (1 / 2 : ℝ) * C (1 / 2) * 4 : MvPolynomial σ ℝ) = 1 := by
      rw [show (4 : MvPolynomial σ ℝ) = C 4 from (map_ofNat C 4).symm, ← C_mul, ← C_mul]
      norm_num
    simp only [a, b]
    linear_combination r * h4
  have key : ∀ {u : MvPolynomial σ ℝ}, DerivesN A k M u → DerivesN A k M (-u) →
      DerivesN A (2 * r.totalDegree + k) ((coeffNorm1 r + 1) ^ 2 * M) (r * u) := by
    intro u h₁ h₂
    have := ((h₁.mulSOS (IsSOS.sq a)).mono (k' := 2 * r.totalDegree + k) (by omega) le_rfl).add
      ((h₂.mulSOS (IsSOS.sq b)).mono (k' := 2 * r.totalDegree + k) (by omega) le_rfl)
    refine (this.mono le_rfl ?_).congr ?_
    · calc coeffNorm1 (a ^ 2) * M + coeffNorm1 (b ^ 2) * M
          ≤ (coeffNorm1 r + 1) ^ 2 / 2 * M + (coeffNorm1 r + 1) ^ 2 / 2 * M :=
            add_le_add (mul_le_mul_of_nonneg_right hna hM) (mul_le_mul_of_nonneg_right hnb hM)
        _ = _ := by ring
    · rw [← hab]
      ring
  exact ⟨key h.1 h.2, by simpa [mul_neg] using key h.2 (by simpa using h.1)⟩

end DerivesEq

namespace DerivesN

variable {A : System σ ℝ} {k : ℕ} {M M' : ℝ} {g g' : MvPolynomial σ ℝ}

/-- Replace `g` by `g'` when `A` proves `g' - g = 0`. -/
theorem of_eq (h : DerivesN A k M g) (he : DerivesEq A k M' (g' - g)) :
    DerivesN A k (M + M') g' := by
  simpa using h.add he.1

end DerivesN

end SoS

/-! ### Norm bounds as powers of a size parameter

Norm bounds of explicit proofs are conveniently powers `W^e` of one size parameter `W ≥ 2`; their
sums and products are again powers, with exponents in `ℕ`. -/

namespace SoS

variable {W : ℝ}

theorem pow_le_pow_of_two_le (hW : 2 ≤ W) {a b : ℕ} (h : a ≤ b) : W ^ a ≤ W ^ b :=
  pow_le_pow_right₀ (by linarith) h

theorem pow_nonneg_of_two_le (hW : 2 ≤ W) (a : ℕ) : 0 ≤ W ^ a :=
  pow_nonneg (by linarith) a

theorem le_pow_of_two_le (hW : 2 ≤ W) {n : ℕ} (hn : 1 ≤ n) : W ≤ W ^ n :=
  (pow_one W).symm.le.trans (pow_le_pow_of_two_le hW hn)

theorem one_le_pow_of_two_le (hW : 2 ≤ W) (n : ℕ) : 1 ≤ W ^ n :=
  one_le_pow₀ (by linarith)

/-- `c ≤ W^n` for a constant `c ≤ 2^n`. -/
theorem le_pow_of_le_two_pow (hW : 2 ≤ W) {c : ℝ} {n : ℕ} (hc : c ≤ 2 ^ n) : c ≤ W ^ n :=
  hc.trans (pow_le_pow_left₀ (by norm_num) hW n)

/-- `x + y ≤ W^(c + 1)` if `x, y ≤ W^c`. -/
theorem add_le_pow_succ (hW : 2 ≤ W) {x y : ℝ} {c : ℕ} (hx : x ≤ W ^ c) (hy : y ≤ W ^ c) :
    x + y ≤ W ^ (c + 1) := by
  rw [pow_succ]
  nlinarith [pow_nonneg_of_two_le hW c]

/-- `(x + 1)² ≤ W^(2b + 2)` if `0 ≤ x ≤ W^b`. -/
theorem add_one_sq_le_pow (hW : 2 ≤ W) {x : ℝ} {b : ℕ} (hx₀ : 0 ≤ x) (hx : x ≤ W ^ b) :
    (x + 1) ^ 2 ≤ W ^ (2 * b + 2) := by
  have h1 : 1 ≤ W ^ b := one_le_pow₀ (by linarith)
  have : x + 1 ≤ W ^ (b + 1) := by
    rw [pow_succ]
    nlinarith
  calc (x + 1) ^ 2 ≤ (W ^ (b + 1)) ^ 2 := pow_le_pow_left₀ (by linarith) this 2
    _ = W ^ (2 * b + 2) := by rw [← pow_mul]; ring_nf

/-- A sum over a set of at most `W^c` elements of terms at most `W^a` is at most `W^(a + c)`. -/
theorem sum_le_pow {ι : Type*} (hW : 2 ≤ W) (s : Finset ι) {f : ι → ℝ} {a c : ℕ}
    (hf : ∀ i ∈ s, f i ≤ W ^ a) (hs : (s.card : ℝ) ≤ W ^ c) : ∑ i ∈ s, f i ≤ W ^ (a + c) := by
  calc ∑ i ∈ s, f i ≤ ∑ _i ∈ s, W ^ a := Finset.sum_le_sum hf
    _ = s.card * W ^ a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ W ^ c * W ^ a := mul_le_mul_of_nonneg_right hs (pow_nonneg_of_two_le hW a)
    _ = W ^ (a + c) := by rw [pow_add, mul_comm]

end SoS

/-! ### Approximate soundness for proofs with bounded multipliers -/

namespace SoS

open MvPolynomial

variable {σ : Type*} {ℓ : ℕ}

theorem totalDegree_toReal_rat (p : MvPolynomial σ ℚ) : (toReal p).totalDegree = p.totalDegree := by
  simp only [toReal, totalDegree, support_map_of_injective _ (algebraMap ℚ ℝ).injective]

/-- Approximate satisfaction of a rational system is approximate satisfaction of its real image. -/
theorem PseudoExpectation.ApproxSatisfies.map_toReal {E : PseudoExpectation σ ℓ}
    {A : System σ ℚ} {η : ℝ} {r : ℕ} (hA : E.ApproxSatisfies A η r) :
    E.ApproxSatisfies (A.map toReal) η r := by
  classical
  intro S h hh hdeg
  set e : Fin (A.map toReal).length ≃ Fin A.length := finCongr (List.length_map _)
  have hget : ∀ i, (A.map toReal).get i = toReal (A.get (e i)) := fun i ↦ by
    simp [e, List.get_eq_getElem]
  have h1 := hA (S.map e.toEmbedding) h hh (by
    rw [Finset.sum_map]
    convert hdeg using 3 with i
    rw [hget, totalDegree_toReal_rat]
    rfl)
  rw [Finset.prod_map] at h1
  simp only [System.prod, Finset.prod_map, toReal_prod, toReal_real] at h1 ⊢
  simp only [hget]
  convert h1 using 3

/-- **Approximate soundness for proofs with bounded multipliers.** If `Ẽ` satisfies the real
system `A` up to `η` and `A ⊢[k] g` with multipliers of `‖·‖₁ ≤ M`, then
`Ẽ g ≥ -η M ∏ᵢ (1 + ‖fᵢ‖₂)`. -/
theorem DerivesN.approx_ge {E : PseudoExpectation σ ℓ} {A : System σ ℝ} {η : ℝ} (hη : 0 ≤ η)
    (hA : E.ApproxSatisfies A η 0) {k : ℕ} (hk : k ≤ ℓ) {M : ℝ} {g : MvPolynomial σ ℝ}
    (h : DerivesN A k M g) :
    -(η * M * ∏ i : Fin A.length, (1 + coeffNorm (A.get i))) ≤ E g := by
  obtain ⟨P, hP⟩ := h
  have hM : 0 ≤ M := (coeffNorm1_nonneg _).trans (hP ∅)
  have h1 := hA.apply_proof hη (Or.inl rfl) P 1 (IsSumSq.one) (by simpa using hk)
  rw [one_mul, toReal_real] at h1
  have hnorm1 : coeffNorm (1 : MvPolynomial σ ℝ) = 1 := by
    rw [← C_1, coeffNorm_C, abs_one]
  rw [hnorm1, mul_one] at h1
  refine le_trans ?_ h1
  rw [neg_le_neg_iff, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hη
  calc P.size = ∑ S, coeffNorm1 (toReal (P.mult S)) * ∏ i ∈ S, coeffNorm (toReal (A.get i)) := rfl
    _ ≤ ∑ S : Finset (Fin A.length), M * ∏ i ∈ S, coeffNorm (A.get i) := by
        refine Finset.sum_le_sum fun S _ ↦ ?_
        simp only [toReal_real]
        exact mul_le_mul_of_nonneg_right (hP S)
          (Finset.prod_nonneg fun _ _ ↦ coeffNorm_nonneg _)
    _ = M * ∏ i : Fin A.length, (1 + coeffNorm (A.get i)) := by
        rw [← Finset.mul_sum, Finset.prod_one_add, Finset.powerset_univ]

end SoS
