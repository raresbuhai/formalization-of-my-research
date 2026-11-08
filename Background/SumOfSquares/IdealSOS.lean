module

public import Background.SumOfSquares.Boolean
public import Background.SumOfSquares.PowerSOS

/-!
# Sums of squares plus an explicit ideal

`SoS.SosPlusIdeal A k M g` says that `g = s + ∑ᵢ rᵢ fᵢ`, where `s` is a sum of squares, the
multipliers `rᵢ` sit only on equality constraints `fᵢ = 0` of `A` (both `fᵢ` and `-fᵢ` in `A`,
`SoS.HasEq`), `deg s ≤ k`, `deg rᵢ + deg fᵢ ≤ k`, and `s` and every `rᵢ` have `‖·‖₁ ≤ M`. The
multipliers `rᵢ` are arbitrary polynomials, not sums of squares.

Such certificates multiply without growing the degree beyond `k₁ + k₂` (`SoS.SosPlusIdeal.mul`),
whereas the normed proofs of `Background/SumOfSquares/Normed.lean` double the degree of a
multiplier at every product with an equality (`SoS.DerivesEq.mul`). The degree is doubled only once,
when the certificate is turned into a normed proof (`SoS.SosPlusIdeal.toDerivesN`):
`A ⊢[2k] g` with multipliers of `‖·‖₁ ≤ M + |A| (M + 1)²`. Approximate soundness follows
(`SoS.SosPlusIdeal.approx_ge`): a pseudo-expectation of degree `ℓ ≥ 2k` that satisfies `A` up to
`η` has `Ẽ g ≥ -η (M + |A| (M + 1)²) ∏ᵢ (1 + ‖fᵢ‖₂)`.

* Rules, all with explicit degrees and norms: `of_isSumSq`, `ideal` (`q h` for an equality
  `h = 0` of `A`), `isSumSq_add_mul`, `zero`, `add`, `sum`, `mulSOS`, `smul` (`c ≥ 0`), `mul`
  (degree `k₁ + k₂`, norm `M₁ (M₂ + ‖g₂‖₁)`), `pow` (degree `n k`, norm `(M + ‖g‖₁)^n`), and
  `of_eq_add_ideal` (adding a combination of equalities).
* **Boolean variables on a set.** `SoS.BooleanOn A U`: `A` contains `xᵢ² = xᵢ` for every `i ∈ U`,
  but the other variables need not be Boolean (unlike `SoS.Boolean`). For `i, i' ∈ U` and sums
  `p = ∑ j ∈ T, x_{w j}` over variables `w j ∈ U` (with `w = id`, `T = U` for `p_U`):
  - (B1) `xᵢ ≥ 0` and (B2) `1 - xᵢ ≥ 0`, in degree `2`;
  - (B3) `p ≥ 0` and `|T| - p ≥ 0`, in degree `2`;
  - (B4) `|T| p - p² ≥ 0`, in degree `2`;
  - (B5) `xᵢ xᵢ' ≥ 0` and `xᵢ (1 - xᵢ') ≥ 0`, in degree `4`;
  - (B6) **Hölder**: `(∑ⱼ x_{w j} yⱼ)^(2^t) ≤ p^(2^t - 1) ∑ⱼ x_{w j} yⱼ^(2^t)` for arbitrary
    polynomials `yⱼ` of degree at most `e`, in degree `2^t (e + 2)` and norm `(3 c²)^(2^t)`,
    where `c ≥ 1` bounds `|T| maxⱼ ‖yⱼ‖₁` (`SoS.BooleanOn.holder`). The case `2^t = 2` is
    Cauchy–Schwarz with `uⱼ = x_{w j}`, `vⱼ = x_{w j} yⱼ`, followed by `x_{w j}² = x_{w j}`
    modulo the ideal (`SoS.SosPlusIdeal.holder_two`); the step squares, as
    `B² - A² = (B - A)(B - A + 2A)`. It holds for any polynomials `aⱼ` with `aⱼ² = aⱼ` in `A`,
    `deg aⱼ ≤ 1` and `‖aⱼ‖₁ ≤ 1` in place of `x_{w j}` (`SoS.SosPlusIdeal.holder_idem`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Finset

variable {σ : Type*}

/-- `g = s + ∑ᵢ rᵢ fᵢ` with `s` a sum of squares of degree at most `k` and multipliers `rᵢ` only on
equality constraints `fᵢ = 0` of `A` (`SoS.HasEq`), with `deg rᵢ + deg fᵢ ≤ k`; `s` and every `rᵢ`
have `‖·‖₁ ≤ M`. -/
def SosPlusIdeal (A : System σ ℝ) (k : ℕ) (M : ℝ) (g : MvPolynomial σ ℝ) : Prop :=
  ∃ (s : MvPolynomial σ ℝ) (r : Fin A.length → MvPolynomial σ ℝ),
    IsSumSq s ∧ s.totalDegree ≤ k ∧ coeffNorm1 s ≤ M ∧
    (∀ i, r i ≠ 0 → HasEq A (A.get i) ∧ (r i).totalDegree + (A.get i).totalDegree ≤ k ∧
      coeffNorm1 (r i) ≤ M) ∧
    g = s + ∑ i, r i * A.get i

/-- A sum over a set of polynomials of `‖·‖₁ ≤ b` has `‖·‖₁ ≤ |T| b`. -/
theorem coeffNorm1_sum_le_card_mul {ι : Type*} (T : Finset ι) (f : ι → MvPolynomial σ ℝ) {b : ℝ}
    (hf : ∀ j ∈ T, coeffNorm1 (f j) ≤ b) : coeffNorm1 (∑ j ∈ T, f j) ≤ T.card * b := by
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ j ∈ T, coeffNorm1 (f j) ≤ ∑ _j ∈ T, b := sum_le_sum hf
    _ = T.card * b := by rw [sum_const, nsmul_eq_mul]

namespace SosPlusIdeal

variable {A : System σ ℝ} {k k' k₁ k₂ : ℕ} {M M' M₁ M₂ : ℝ} {g g' g₁ g₂ : MvPolynomial σ ℝ}

theorem nonneg (h : SosPlusIdeal A k M g) : 0 ≤ M := by
  obtain ⟨s, -, -, -, hs, -, -⟩ := h
  exact (coeffNorm1_nonneg s).trans hs

theorem mono (h : SosPlusIdeal A k M g) (hk : k ≤ k') (hM : M ≤ M') : SosPlusIdeal A k' M' g := by
  obtain ⟨s, r, hs, hsd, hsn, hr, rfl⟩ := h
  refine ⟨s, r, hs, hsd.trans hk, hsn.trans hM, fun i hi ↦ ?_, rfl⟩
  obtain ⟨h₁, h₂, h₃⟩ := hr i hi
  exact ⟨h₁, h₂.trans hk, h₃.trans hM⟩

theorem congr (h : SosPlusIdeal A k M g) (e : g = g') : SosPlusIdeal A k M g' := e ▸ h

/-- The polynomial itself has degree at most `k`. -/
theorem totalDegree_le (h : SosPlusIdeal A k M g) : g.totalDegree ≤ k := by
  obtain ⟨s, r, -, hsd, -, hr, rfl⟩ := h
  refine (totalDegree_add _ _).trans (max_le hsd (totalDegree_finsetSum_le fun i _ ↦ ?_))
  by_cases hi : r i = 0
  · simp [hi]
  · exact (totalDegree_mul _ _).trans (hr i hi).2.1

/-- Every multiplier, zero or not, has `‖·‖₁ ≤ M`. -/
theorem coeffNorm1_mult_le {r : Fin A.length → MvPolynomial σ ℝ} (hM : 0 ≤ M)
    (hr : ∀ i, r i ≠ 0 → HasEq A (A.get i) ∧ (r i).totalDegree + (A.get i).totalDegree ≤ k ∧
      coeffNorm1 (r i) ≤ M) (i : Fin A.length) : coeffNorm1 (r i) ≤ M := by
  by_cases hi : r i = 0
  · rw [hi, coeffNorm1_zero]
    exact hM
  · exact (hr i hi).2.2

/-- A sum of squares. -/
theorem of_isSumSq (A : System σ ℝ) {s : MvPolynomial σ ℝ} (hs : IsSumSq s)
    (hd : s.totalDegree ≤ k) (hn : coeffNorm1 s ≤ M) : SosPlusIdeal A k M s :=
  ⟨s, 0, hs, hd, hn, fun _ hi ↦ (hi rfl).elim, by simp⟩

theorem zero (A : System σ ℝ) (k : ℕ) (hM : 0 ≤ M) : SosPlusIdeal A k M 0 :=
  of_isSumSq A IsSumSq.zero (by simp) (by simpa using hM)

/-- A sum of squares plus a multiple `q h` of an equality `h = 0` of `A`. -/
theorem isSumSq_add_mul {s h : MvPolynomial σ ℝ} (hs : IsSumSq s) (hh : HasEq A h)
    (q : MvPolynomial σ ℝ) (hsd : s.totalDegree ≤ k) (hqd : q.totalDegree + h.totalDegree ≤ k)
    (hsn : coeffNorm1 s ≤ M) (hqn : coeffNorm1 q ≤ M) : SosPlusIdeal A k M (s + q * h) := by
  classical
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hh.1
  refine ⟨s, Pi.single i q, hs, hsd, hsn, fun j hj ↦ ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [Pi.single_eq_same]
      exact ⟨hh, hqd, hqn⟩
    · simp [hji] at hj
  · rw [sum_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, zero_mul])
      (fun h ↦ absurd (mem_univ i) h), Pi.single_eq_same]

/-- A multiple `q h` of an equality `h = 0` of `A`, for any polynomial `q`. -/
theorem ideal {h : MvPolynomial σ ℝ} (hh : HasEq A h) (q : MvPolynomial σ ℝ)
    (hd : q.totalDegree + h.totalDegree ≤ k) (hn : coeffNorm1 q ≤ M) :
    SosPlusIdeal A k M (q * h) := by
  have := isSumSq_add_mul IsSumSq.zero hh q (by simp) hd
    (by rw [coeffNorm1_zero]; exact (coeffNorm1_nonneg q).trans hn) hn
  rwa [zero_add] at this

theorem add (h₁ : SosPlusIdeal A k M₁ g₁) (h₂ : SosPlusIdeal A k M₂ g₂) :
    SosPlusIdeal A k (M₁ + M₂) (g₁ + g₂) := by
  have hM₁ := h₁.nonneg
  have hM₂ := h₂.nonneg
  obtain ⟨s₁, r₁, hs₁, hsd₁, hsn₁, hr₁, rfl⟩ := h₁
  obtain ⟨s₂, r₂, hs₂, hsd₂, hsn₂, hr₂, rfl⟩ := h₂
  refine ⟨s₁ + s₂, r₁ + r₂, hs₁.add hs₂, (totalDegree_add _ _).trans (max_le hsd₁ hsd₂),
    (coeffNorm1_add_le _ _).trans (add_le_add hsn₁ hsn₂), fun i hi ↦ ?_, ?_⟩
  · simp only [Pi.add_apply] at hi ⊢
    by_cases h₁ : r₁ i = 0
    · rw [h₁, zero_add] at hi ⊢
      obtain ⟨a, b, c⟩ := hr₂ i hi
      exact ⟨a, b, c.trans (by linarith)⟩
    by_cases h₂ : r₂ i = 0
    · rw [h₂, add_zero] at hi ⊢
      obtain ⟨a, b, c⟩ := hr₁ i h₁
      exact ⟨a, b, c.trans (by linarith)⟩
    obtain ⟨a, b, c⟩ := hr₁ i h₁
    obtain ⟨-, b', c'⟩ := hr₂ i h₂
    refine ⟨a, ?_, (coeffNorm1_add_le _ _).trans (add_le_add c c')⟩
    have hadd := totalDegree_add (r₁ i) (r₂ i)
    have := max_le_iff.2 ⟨b, b'⟩
    omega
  · simp only [Pi.add_apply, add_mul, sum_add_distrib]
    ring

theorem sum {ι : Type*} (T : Finset ι) {g : ι → MvPolynomial σ ℝ} {M : ι → ℝ}
    (h : ∀ j ∈ T, SosPlusIdeal A k (M j) (g j)) :
    SosPlusIdeal A k (∑ j ∈ T, M j) (∑ j ∈ T, g j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using zero A k le_rfl
  | insert a T ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a T)).add (ih fun j hj ↦ h j (mem_insert_of_mem hj))

/-- Multiplying by a sum of squares `q`. -/
theorem mulSOS {q : MvPolynomial σ ℝ} (hq : IsSumSq q) (h : SosPlusIdeal A k M g) :
    SosPlusIdeal A (q.totalDegree + k) (coeffNorm1 q * M) (q * g) := by
  obtain ⟨s, r, hs, hsd, hsn, hr, rfl⟩ := h
  refine ⟨q * s, fun i ↦ q * r i, hq.mul hs, (totalDegree_mul _ _).trans (by omega),
    (coeffNorm1_mul_le _ _).trans (mul_le_mul_of_nonneg_left hsn (coeffNorm1_nonneg _)),
    fun i hi ↦ ?_, ?_⟩
  · simp only at hi ⊢
    have hri : r i ≠ 0 := fun h0 ↦ hi (by simp [h0])
    obtain ⟨a, b, c⟩ := hr i hri
    refine ⟨a, ?_, (coeffNorm1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left c (coeffNorm1_nonneg _))⟩
    have := totalDegree_mul q (r i)
    omega
  · rw [mul_add, mul_sum]
    congr 1
    exact sum_congr rfl fun i _ ↦ by ring

/-- Multiplying by a constant `c ≥ 0`. -/
theorem smul {c : ℝ} (hc : 0 ≤ c) (h : SosPlusIdeal A k M g) :
    SosPlusIdeal A k (c * M) (C c * g) := by
  have := h.mulSOS (isSumSq_C hc)
  rwa [totalDegree_C, zero_add, coeffNorm1_C, abs_of_nonneg hc] at this

/-- **Products**: `g₁ g₂ = s₁ s₂ + ∑ᵢ (r₁ᵢ g₂ + s₁ r₂ᵢ) fᵢ`, in degree `k₁ + k₂`. -/
theorem mul (h₁ : SosPlusIdeal A k₁ M₁ g₁) (h₂ : SosPlusIdeal A k₂ M₂ g₂) :
    SosPlusIdeal A (k₁ + k₂) (M₁ * (M₂ + coeffNorm1 g₂)) (g₁ * g₂) := by
  have hM₁ := h₁.nonneg
  have hM₂ := h₂.nonneg
  have hg₂ := h₂.totalDegree_le
  have hng₂ := coeffNorm1_nonneg g₂
  obtain ⟨s₁, r₁, hs₁, hsd₁, hsn₁, hr₁, rfl⟩ := h₁
  obtain ⟨s₂, r₂, hs₂, hsd₂, hsn₂, hr₂, hg⟩ := h₂
  have hrn₁ := coeffNorm1_mult_le hM₁ hr₁
  have hrn₂ := coeffNorm1_mult_le hM₂ hr₂
  refine ⟨s₁ * s₂, fun i ↦ r₁ i * g₂ + s₁ * r₂ i, hs₁.mul hs₂,
    (totalDegree_mul _ _).trans (by omega), ?_, fun i hi ↦ ?_, ?_⟩
  · calc coeffNorm1 (s₁ * s₂) ≤ coeffNorm1 s₁ * coeffNorm1 s₂ := coeffNorm1_mul_le _ _
      _ ≤ M₁ * M₂ := mul_le_mul hsn₁ hsn₂ (coeffNorm1_nonneg _) hM₁
      _ ≤ M₁ * (M₂ + coeffNorm1 g₂) := mul_le_mul_of_nonneg_left (by linarith) hM₁
  · simp only at hi ⊢
    have hA : HasEq A (A.get i) ∧ (A.get i).totalDegree ≤ k₁ + k₂ := by
      by_cases h₁ : r₁ i = 0
      · have h₂ : r₂ i ≠ 0 := fun h₂ ↦ hi (by rw [h₁, h₂]; ring)
        obtain ⟨a, b, -⟩ := hr₂ i h₂
        exact ⟨a, by omega⟩
      · obtain ⟨a, b, -⟩ := hr₁ i h₁
        exact ⟨a, by omega⟩
    have d₁ : (r₁ i * g₂).totalDegree + (A.get i).totalDegree ≤ k₁ + k₂ := by
      by_cases h₁ : r₁ i = 0
      · rw [h₁, zero_mul, totalDegree_zero, zero_add]
        exact hA.2
      · have := (hr₁ i h₁).2.1
        have := totalDegree_mul (r₁ i) g₂
        omega
    have d₂ : (s₁ * r₂ i).totalDegree + (A.get i).totalDegree ≤ k₁ + k₂ := by
      by_cases h₂ : r₂ i = 0
      · rw [h₂, mul_zero, totalDegree_zero, zero_add]
        exact hA.2
      · have := (hr₂ i h₂).2.1
        have := totalDegree_mul s₁ (r₂ i)
        omega
    refine ⟨hA.1, ?_, ?_⟩
    · have hadd := totalDegree_add (r₁ i * g₂) (s₁ * r₂ i)
      have := max_le_iff.2 ⟨d₁, d₂⟩
      omega
    · calc coeffNorm1 (r₁ i * g₂ + s₁ * r₂ i)
          ≤ coeffNorm1 (r₁ i) * coeffNorm1 g₂ + coeffNorm1 s₁ * coeffNorm1 (r₂ i) :=
            (coeffNorm1_add_le _ _).trans (add_le_add (coeffNorm1_mul_le _ _)
              (coeffNorm1_mul_le _ _))
        _ ≤ M₁ * coeffNorm1 g₂ + M₁ * M₂ :=
            add_le_add (mul_le_mul_of_nonneg_right (hrn₁ i) hng₂)
              (mul_le_mul hsn₁ (hrn₂ i) (coeffNorm1_nonneg _) hM₁)
        _ = M₁ * (M₂ + coeffNorm1 g₂) := by ring
  · have e₁ : (∑ i, r₁ i * A.get i) * g₂ = ∑ i, r₁ i * g₂ * A.get i := by
      rw [sum_mul]
      exact sum_congr rfl fun i _ ↦ by ring
    have e₂ : s₁ * ∑ i, r₂ i * A.get i = ∑ i, s₁ * r₂ i * A.get i := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    have e₃ : ∑ i, (r₁ i * g₂ + s₁ * r₂ i) * A.get i =
        ∑ i, r₁ i * g₂ * A.get i + ∑ i, s₁ * r₂ i * A.get i := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ ↦ by ring
    change _ = s₁ * s₂ + ∑ i, (r₁ i * g₂ + s₁ * r₂ i) * A.get i
    rw [e₃, ← e₁, ← e₂]
    linear_combination s₁ * hg

/-- **Powers**, in degree `n k`. -/
theorem pow (h : SosPlusIdeal A k M g) (n : ℕ) :
    SosPlusIdeal A (n * k) ((M + coeffNorm1 g) ^ n) (g ^ n) := by
  induction n with
  | zero =>
    rw [zero_mul, pow_zero, pow_zero]
    exact of_isSumSq A IsSumSq.one (by simp) coeffNorm1_one.le
  | succ n ih =>
    rw [pow_succ, pow_succ, add_mul, one_mul]
    exact ih.mul h

/-- Adding a combination `∑ j ∈ T, qⱼ eⱼ` of equalities `eⱼ = 0` of `A`. -/
theorem of_eq_add_ideal {ι : Type*} (h : SosPlusIdeal A k M g) (T : Finset ι)
    {e q : ι → MvPolynomial σ ℝ} (he : ∀ j ∈ T, HasEq A (e j))
    (hd : ∀ j ∈ T, (q j).totalDegree + (e j).totalDegree ≤ k)
    (hn : ∀ j ∈ T, coeffNorm1 (q j) ≤ M') (hg : g' = g + ∑ j ∈ T, q j * e j) :
    SosPlusIdeal A k (M + T.card * M') g' := by
  have := h.add (sum T (M := fun _ ↦ M') fun j hj ↦ ideal (he j hj) (q j) (hd j hj) (hn j hj))
  rw [sum_const, nsmul_eq_mul] at this
  exact this.congr hg.symm

/-- **The normed proof.** `A ⊢[2k] g` with multipliers of `‖·‖₁ ≤ M + |A| (M + 1)²`: the sum of
squares is a multiplier as it is, and each `rᵢ fᵢ` is `DerivesEq.mul`, which doubles the degree of
`rᵢ`. -/
theorem toDerivesN (h : SosPlusIdeal A k M g) :
    DerivesN A (2 * k) (M + A.length * (M + 1) ^ 2) g := by
  have hM := h.nonneg
  obtain ⟨s, r, hs, hsd, hsn, hr, rfl⟩ := h
  have h₁ : DerivesN A (2 * k) M s :=
    DerivesN.ofIsSOS A (by rwa [IsSOS, toReal_real]) (by omega) hsn
  have h₂ : DerivesN A (2 * k) (∑ _i : Fin A.length, (M + 1) ^ 2) (∑ i, r i * A.get i) := by
    refine DerivesN.sum univ (M := fun _ ↦ (M + 1) ^ 2) (g := fun i ↦ r i * A.get i)
      fun i _ ↦ ?_
    by_cases hi : r i = 0
    · rw [hi, zero_mul]
      exact DerivesN.zero A _ (sq_nonneg _)
    · obtain ⟨hh, hd, hn⟩ := hr i hi
      refine ((hh.derivesEq le_rfl le_rfl).mul (r i)).1.mono (by omega) ?_
      rw [mul_one]
      exact pow_le_pow_left₀ (by linarith [coeffNorm1_nonneg (r i)]) (by linarith) 2
  have := h₁.add h₂
  rwa [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this

/-- **Approximate soundness.** A pseudo-expectation of degree `ℓ ≥ 2k` that satisfies `A` up to
`η` has `Ẽ g ≥ -η (M + |A| (M + 1)²) ∏ᵢ (1 + ‖fᵢ‖₂)`. -/
theorem approx_ge {ℓ : ℕ} {E : PseudoExpectation σ ℓ} {η : ℝ} (hη : 0 ≤ η)
    (hE : E.ApproxSatisfies A η 0) (hk : 2 * k ≤ ℓ) (h : SosPlusIdeal A k M g) :
    -(η * (M + A.length * (M + 1) ^ 2) * ∏ i : Fin A.length, (1 + coeffNorm (A.get i))) ≤
      E g :=
  h.toDerivesN.approx_ge hη hE hk

/-! ### Hölder's inequality for idempotents -/

/-- (B6) for exponent `2`: `(∑ⱼ aⱼ yⱼ)² ≤ (∑ⱼ aⱼ) ∑ⱼ aⱼ yⱼ²` when `aⱼ² = aⱼ` in `A`. This is
Cauchy–Schwarz `(∑ⱼ aⱼ (aⱼ yⱼ))² ≤ (∑ⱼ aⱼ²) ∑ⱼ (aⱼ yⱼ)²`, followed by `aⱼ² = aⱼ`. -/
theorem holder_two {ι : Type*} (T : Finset ι) {a : ι → MvPolynomial σ ℝ}
    (ha : ∀ j ∈ T, HasEq A (a j ^ 2 - a j)) (had : ∀ j ∈ T, (a j).totalDegree ≤ 1)
    (han : ∀ j ∈ T, coeffNorm1 (a j) ≤ 1) (y : ι → MvPolynomial σ ℝ) {e : ℕ}
    (hyd : ∀ j ∈ T, (y j).totalDegree ≤ e) {β : ℝ} (hyn : ∀ j ∈ T, coeffNorm1 (y j) ≤ β) :
    SosPlusIdeal A (2 * e + 4) (6 * T.card ^ 2 * β ^ 2)
      ((∑ j ∈ T, a j) * ∑ j ∈ T, a j * y j ^ 2 - (∑ j ∈ T, a j * y j) ^ 2) := by
  have hn0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have haf : ∀ j ∈ T, ∀ f : MvPolynomial σ ℝ, coeffNorm1 (a j * f) ≤ coeffNorm1 f := fun j hj f ↦
    (coeffNorm1_mul_le _ _).trans (mul_le_of_le_one_left (coeffNorm1_nonneg _) (han j hj))
  have hy2 : ∀ j ∈ T, coeffNorm1 (y j ^ 2) ≤ β ^ 2 := fun j hj ↦
    (coeffNorm1_pow_le _ 2).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hyn j hj) 2)
  have hay : ∀ j ∈ T, coeffNorm1 (a j * y j) ≤ β := fun j hj ↦ (haf j hj _).trans (hyn j hj)
  -- The pieces and their norms.
  have hW : coeffNorm1 (∑ j ∈ T, a j ^ 2) ≤ T.card := by
    simpa using coeffNorm1_sum_le_card_mul T _ fun j hj ↦
      (coeffNorm1_pow_le _ 2).trans (pow_le_one₀ (coeffNorm1_nonneg _) (han j hj))
  have hS' : coeffNorm1 (∑ j ∈ T, (a j * y j) ^ 2) ≤ T.card * β ^ 2 :=
    coeffNorm1_sum_le_card_mul T _ fun j hj ↦
      (coeffNorm1_pow_le _ 2).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hay j hj) 2)
  have hS : coeffNorm1 (∑ j ∈ T, a j * y j ^ 2) ≤ T.card * β ^ 2 :=
    coeffNorm1_sum_le_card_mul T _ fun j hj ↦ (haf j hj _).trans (hy2 j hj)
  have hL' : coeffNorm1 (∑ j ∈ T, a j * (a j * y j)) ≤ T.card * β :=
    coeffNorm1_sum_le_card_mul T _ fun j hj ↦ (haf j hj _).trans (hay j hj)
  have hL : coeffNorm1 (∑ j ∈ T, a j * y j) ≤ T.card * β :=
    coeffNorm1_sum_le_card_mul T _ hay
  -- Their degrees.
  have hWd : (∑ j ∈ T, a j ^ 2).totalDegree ≤ 2 := totalDegree_finsetSum_le fun j hj ↦
    (totalDegree_pow _ _).trans (by have := had j hj; omega)
  have hSd : (∑ j ∈ T, a j * y j ^ 2).totalDegree ≤ 2 * e + 1 := totalDegree_finsetSum_le
    fun j hj ↦ (totalDegree_mul _ _).trans (by
      have := had j hj
      have := (totalDegree_pow (y j) 2).trans (Nat.mul_le_mul_left 2 (hyd j hj))
      omega)
  have hL'd : (∑ j ∈ T, a j * (a j * y j)).totalDegree ≤ e + 2 := totalDegree_finsetSum_le
    fun j hj ↦ (totalDegree_mul _ _).trans (by
      have := had j hj
      have := (totalDegree_mul (a j) (y j)).trans (add_le_add (had j hj) (hyd j hj))
      omega)
  have hLd : (∑ j ∈ T, a j * y j).totalDegree ≤ e + 1 := totalDegree_finsetSum_le fun j hj ↦
    (totalDegree_mul _ _).trans (by have := had j hj; have := hyd j hj; omega)
  -- The sum of squares from Cauchy–Schwarz.
  have hs : IsSumSq ((∑ j ∈ T, a j ^ 2) * (∑ j ∈ T, (a j * y j) ^ 2) -
      (∑ j ∈ T, a j * (a j * y j)) ^ 2) := isSumSq_lagrange T a fun j ↦ a j * y j
  have hsd : ((∑ j ∈ T, a j ^ 2) * (∑ j ∈ T, (a j * y j) ^ 2) -
      (∑ j ∈ T, a j * (a j * y j)) ^ 2).totalDegree ≤ 2 * e + 4 :=
    (totalDegree_lagrange_le T (u := a) (v := fun j ↦ a j * y j) (du := 1) (dv := e + 1) had
      fun j hj ↦ (totalDegree_mul _ _).trans (by have := had j hj; have := hyd j hj; omega)).trans
      (by omega)
  have hsn : coeffNorm1 ((∑ j ∈ T, a j ^ 2) * (∑ j ∈ T, (a j * y j) ^ 2) -
      (∑ j ∈ T, a j * (a j * y j)) ^ 2) ≤ 2 * T.card ^ 2 * β ^ 2 := by
    refine (coeffNorm1_sub_le _ _).trans ?_
    have h₁ := (coeffNorm1_mul_le (∑ j ∈ T, a j ^ 2) (∑ j ∈ T, (a j * y j) ^ 2)).trans
      (mul_le_mul hW hS' (coeffNorm1_nonneg _) hn0)
    have h₂ := (coeffNorm1_pow_le (∑ j ∈ T, a j * (a j * y j)) 2).trans
      (pow_le_pow_left₀ (coeffNorm1_nonneg _) hL' 2)
    nlinarith
  -- The multipliers of `aⱼ² - aⱼ`.
  refine ((of_isSumSq A hs hsd hsn).of_eq_add_ideal T (e := fun j ↦ a j ^ 2 - a j)
    (q := fun j ↦ -((∑ i ∈ T, a i ^ 2) * y j ^ 2 + ∑ i ∈ T, a i * y i ^ 2 -
      (∑ i ∈ T, a i * (a i * y i) + ∑ i ∈ T, a i * y i) * y j))
    (M' := 4 * T.card * β ^ 2) ha (fun j hj ↦ ?_) (fun j hj ↦ ?_) ?_).mono le_rfl
    (le_of_eq (by ring))
  · have hyd2 := (totalDegree_pow (y j) 2).trans (Nat.mul_le_mul_left 2 (hyd j hj))
    have h₁ := totalDegree_mul (∑ i ∈ T, a i ^ 2) (y j ^ 2)
    have h₂ := totalDegree_add ((∑ i ∈ T, a i ^ 2) * y j ^ 2) (∑ i ∈ T, a i * y i ^ 2)
    have h₃ := totalDegree_add (∑ i ∈ T, a i * (a i * y i)) (∑ i ∈ T, a i * y i)
    have h₄ := totalDegree_mul (∑ i ∈ T, a i * (a i * y i) + ∑ i ∈ T, a i * y i) (y j)
    have h₅ := totalDegree_sub ((∑ i ∈ T, a i ^ 2) * y j ^ 2 + ∑ i ∈ T, a i * y i ^ 2)
      ((∑ i ∈ T, a i * (a i * y i) + ∑ i ∈ T, a i * y i) * y j)
    have h₆ : (a j ^ 2 - a j).totalDegree ≤ 2 := (totalDegree_sub _ _).trans
      (max_le ((totalDegree_pow _ 2).trans (by have := had j hj; omega))
        (by have := had j hj; omega))
    have := hyd j hj
    rw [totalDegree_neg]
    omega
  · have hβ : 0 ≤ β := (coeffNorm1_nonneg _).trans (hyn j hj)
    rw [coeffNorm1_neg]
    refine (coeffNorm1_sub_le _ _).trans ?_
    have h₁ := (coeffNorm1_add_le ((∑ i ∈ T, a i ^ 2) * y j ^ 2) (∑ i ∈ T, a i * y i ^ 2)).trans
      (add_le_add ((coeffNorm1_mul_le _ _).trans
        (mul_le_mul hW (hy2 j hj) (coeffNorm1_nonneg _) hn0)) hS)
    have h₂ := (coeffNorm1_mul_le (∑ i ∈ T, a i * (a i * y i) + ∑ i ∈ T, a i * y i) (y j)).trans
      (mul_le_mul ((coeffNorm1_add_le _ _).trans (add_le_add hL' hL)) (hyn j hj)
        (coeffNorm1_nonneg _) (by positivity))
    nlinarith
  · have e₁ : ∑ j ∈ T, (a j * y j) ^ 2 - ∑ j ∈ T, a j * y j ^ 2 =
        ∑ j ∈ T, y j ^ 2 * (a j ^ 2 - a j) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    have e₂ : ∑ j ∈ T, a j ^ 2 - ∑ j ∈ T, a j = ∑ j ∈ T, (a j ^ 2 - a j) :=
      (sum_sub_distrib _ _).symm
    have e₃ : ∑ j ∈ T, a j * (a j * y j) - ∑ j ∈ T, a j * y j =
        ∑ j ∈ T, y j * (a j ^ 2 - a j) := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    have e₄ : ∀ W S K : MvPolynomial σ ℝ,
        ∑ j ∈ T, -(W * y j ^ 2 + S - K * y j) * (a j ^ 2 - a j) =
          -(W * ∑ j ∈ T, y j ^ 2 * (a j ^ 2 - a j)) - S * ∑ j ∈ T, (a j ^ 2 - a j) +
            K * ∑ j ∈ T, y j * (a j ^ 2 - a j) := by
      intro W S K
      rw [mul_sum, mul_sum, mul_sum, ← sum_neg_distrib, ← sum_sub_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun j _ ↦ by ring
    rw [e₄, ← e₁, ← e₂, ← e₃]
    ring

/-- The norm bound in the induction step of `holder_idem_aux`. -/
private theorem holder_norm_step {a b : ℝ} (ha : 1 ≤ a) (hb : 3 ≤ b) :
    6 * a ^ 2 + (b - 3) * a ^ 2 * ((b - 3) * a ^ 2 + 6 * a) ≤ (b ^ 2 - 3) * a ^ 4 := by
  have h : 0 ≤ a ^ 2 * (a - 1) * ((b - 2) * a + 1) :=
    mul_nonneg (mul_nonneg (sq_nonneg a) (by linarith)) (by nlinarith)
  nlinarith [h]

/-- (B6) for exponents `2^(t+1)`, with the exact norm bound of the induction. -/
theorem holder_idem_aux {ι : Type*} (T : Finset ι) {a : ι → MvPolynomial σ ℝ}
    (ha : ∀ j ∈ T, HasEq A (a j ^ 2 - a j)) (had : ∀ j ∈ T, (a j).totalDegree ≤ 1)
    (han : ∀ j ∈ T, coeffNorm1 (a j) ≤ 1) (x : ι → MvPolynomial σ ℝ) {e : ℕ}
    (hxd : ∀ j ∈ T, (x j).totalDegree ≤ e) {β c : ℝ} (hxn : ∀ j ∈ T, coeffNorm1 (x j) ≤ β)
    (hc : 1 ≤ c) (hβc : T.card * β ≤ c) (t : ℕ) :
    SosPlusIdeal A (2 ^ (t + 1) * (e + 2))
      (((3 : ℝ) ^ 2 ^ (t + 1) - 3) * c ^ (2 * 2 ^ (t + 1)))
      ((∑ j ∈ T, a j) ^ (2 ^ (t + 1) - 1) * ∑ j ∈ T, a j * x j ^ 2 ^ (t + 1) -
        (∑ j ∈ T, a j * x j) ^ 2 ^ (t + 1)) := by
  have hnβ : 0 ≤ (T.card : ℝ) * β := by
    rcases T.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
    · simp
    · exact mul_nonneg (Nat.cast_nonneg _) ((coeffNorm1_nonneg _).trans (hxn j₀ hj₀))
  have haf : ∀ j ∈ T, ∀ f : MvPolynomial σ ℝ, coeffNorm1 (a j * f) ≤ coeffNorm1 f := fun j hj f ↦
    (coeffNorm1_mul_le _ _).trans (mul_le_of_le_one_left (coeffNorm1_nonneg _) (han j hj))
  have hp : coeffNorm1 (∑ j ∈ T, a j) ≤ T.card := by
    simpa using coeffNorm1_sum_le_card_mul T a han
  have hpd : (∑ j ∈ T, a j).totalDegree ≤ 1 := totalDegree_finsetSum_le had
  have hL : coeffNorm1 (∑ j ∈ T, a j * x j) ≤ c :=
    (coeffNorm1_sum_le_card_mul T _ fun j hj ↦ (haf j hj _).trans (hxn j hj)).trans hβc
  have hLd : (∑ j ∈ T, a j * x j).totalDegree ≤ e + 1 := totalDegree_finsetSum_le fun j hj ↦
    (totalDegree_mul _ _).trans (by have := had j hj; have := hxd j hj; omega)
  induction t with
  | zero =>
    have h := holder_two T ha had han x hxd hxn
    rw [show 2 ^ (0 + 1) = 2 by norm_num, show 2 - 1 = 1 by norm_num, pow_one]
    refine h.mono (by omega) ?_
    have h₁ : ((T.card : ℝ) * β) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hnβ hβc 2
    have h₂ : c ^ 2 ≤ c ^ (2 * 2) := pow_le_pow_right₀ hc (by norm_num)
    nlinarith
  | succ t ih =>
    obtain ⟨f, hf⟩ : ∃ f, 2 ^ (t + 1) = f + 1 :=
      ⟨2 ^ (t + 1) - 1, (Nat.sub_add_cancel Nat.one_le_two_pow).symm⟩
    have hQs : IsSumSq ((∑ j ∈ T, a j * x j) ^ (f + 1) + (∑ j ∈ T, a j * x j) ^ (f + 1)) := by
      rw [← hf, pow_succ, pow_mul]
      exact (isSumSq_sq _).add (isSumSq_sq _)
    have h2 : 2 ^ (t + 1 + 1) = 2 * f + 2 := by rw [pow_succ, hf]; ring
    rw [hf, Nat.add_sub_cancel] at ih
    rw [h2, show 2 * f + 2 - 1 = 2 * f + 1 by omega]
    set p := ∑ j ∈ T, a j with hp_def
    set L := ∑ j ∈ T, a j * x j with hL_def
    set n : ℝ := (T.card : ℝ) with hn_def
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hc0 : 0 ≤ c := by linarith
    -- The case `2` applied to `x^(f+1)`, times `p^(2f)`.
    have hb : SosPlusIdeal A (2 * ((f + 1) * e) + 4) (6 * n ^ 2 * (β ^ (f + 1)) ^ 2)
        (p * ∑ j ∈ T, a j * (x j ^ (f + 1)) ^ 2 - (∑ j ∈ T, a j * x j ^ (f + 1)) ^ 2) :=
      holder_two T ha had han (fun j ↦ x j ^ (f + 1))
        (fun j hj ↦ (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hxd j hj)))
        (fun j hj ↦ (coeffNorm1_pow_le _ _).trans
          (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hxn j hj) _))
    have hq : IsSumSq (p ^ (2 * f)) := by
      rw [mul_comm, pow_mul]
      exact isSumSq_sq _
    have hqd : (p ^ (2 * f)).totalDegree ≤ 2 * f :=
      (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (2 * f) hpd)
    have hqn : coeffNorm1 (p ^ (2 * f)) ≤ n ^ (2 * f) :=
      (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hp _)
    have hdeg : (2 * f + 2) * (e + 2) = 2 * ((f + 1) * e) + 4 * f + 4 := by ring
    have h₁ : SosPlusIdeal A ((2 * f + 2) * (e + 2)) (6 * c ^ (2 * f + 2))
        (p ^ (2 * f) * (p * ∑ j ∈ T, a j * (x j ^ (f + 1)) ^ 2 -
          (∑ j ∈ T, a j * x j ^ (f + 1)) ^ 2)) := by
      refine (hb.mulSOS hq).mono (by omega) ?_
      calc coeffNorm1 (p ^ (2 * f)) * (6 * n ^ 2 * (β ^ (f + 1)) ^ 2)
          ≤ n ^ (2 * f) * (6 * n ^ 2 * (β ^ (f + 1)) ^ 2) :=
            mul_le_mul_of_nonneg_right hqn (by positivity)
        _ = 6 * (n * β) ^ (2 * f + 2) := by ring
        _ ≤ 6 * c ^ (2 * f + 2) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnβ hβc _) (by norm_num)
    -- `(B - A)(B - A + 2A)` with `B - A` the case `f + 1` and `A = L^(f+1)`.
    have hLp : coeffNorm1 (L ^ (f + 1)) ≤ c ^ (f + 1) :=
      (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hL _)
    have hQ : SosPlusIdeal A ((f + 1) * (e + 2)) (2 * c ^ (f + 1)) (L ^ (f + 1) + L ^ (f + 1)) :=
      of_isSumSq A hQs ((totalDegree_add _ _).trans (max_le
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (by omega)))
        ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (by omega)))))
        ((coeffNorm1_add_le _ _).trans (by linarith))
    have hTn : coeffNorm1 (p ^ f * ∑ j ∈ T, a j * x j ^ (f + 1) - L ^ (f + 1)) ≤
        2 * c ^ (f + 1) := by
      have hS : coeffNorm1 (∑ j ∈ T, a j * x j ^ (f + 1)) ≤ n * β ^ (f + 1) :=
        coeffNorm1_sum_le_card_mul T _ fun j hj ↦ (haf j hj _).trans
          ((coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) (hxn j hj) _))
      have hpf : coeffNorm1 (p ^ f) ≤ n ^ f :=
        (coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) hp _)
      have h₃ : coeffNorm1 (p ^ f * ∑ j ∈ T, a j * x j ^ (f + 1)) ≤ c ^ (f + 1) :=
        calc _ ≤ coeffNorm1 (p ^ f) * coeffNorm1 (∑ j ∈ T, a j * x j ^ (f + 1)) :=
              coeffNorm1_mul_le _ _
          _ ≤ n ^ f * (n * β ^ (f + 1)) :=
              mul_le_mul hpf hS (coeffNorm1_nonneg _) (pow_nonneg hn0 _)
          _ = (n * β) ^ (f + 1) := by ring
          _ ≤ c ^ (f + 1) := pow_le_pow_left₀ hnβ hβc _
      exact (coeffNorm1_sub_le _ _).trans (by linarith)
    have hM₁ : 0 ≤ ((3 : ℝ) ^ (f + 1) - 3) * c ^ (2 * (f + 1)) := ih.nonneg
    have h₂ := ih.mul (ih.add hQ)
    have hg₂n : coeffNorm1 (p ^ f * ∑ j ∈ T, a j * x j ^ (f + 1) - L ^ (f + 1) +
        (L ^ (f + 1) + L ^ (f + 1))) ≤ 4 * c ^ (f + 1) :=
      (coeffNorm1_add_le _ _).trans
        (by linarith [coeffNorm1_add_le (L ^ (f + 1)) (L ^ (f + 1))])
    have h₂' := h₂.mono (k' := (2 * f + 2) * (e + 2)) (le_of_eq (by ring))
      (M' := ((3 : ℝ) ^ (f + 1) - 3) * c ^ (2 * (f + 1)) *
        (((3 : ℝ) ^ (f + 1) - 3) * c ^ (2 * (f + 1)) + 6 * c ^ (f + 1)))
      (mul_le_mul_of_nonneg_left (by linarith) hM₁)
    refine ((h₁.add h₂').mono le_rfl ?_).congr ?_
    · have e₁ : c ^ (2 * f + 2) = (c ^ (f + 1)) ^ 2 := by ring
      have e₂ : c ^ (2 * (f + 1)) = (c ^ (f + 1)) ^ 2 := by ring
      have e₃ : c ^ (2 * (2 * f + 2)) = (c ^ (f + 1)) ^ 4 := by ring
      have e₄ : (3 : ℝ) ^ (2 * f + 2) = ((3 : ℝ) ^ (f + 1)) ^ 2 := by ring
      rw [e₁, e₂, e₃, e₄]
      exact holder_norm_step (one_le_pow₀ hc) (le_self_pow₀ (by norm_num) (by omega))
    · have hS : ∑ j ∈ T, a j * (x j ^ (f + 1)) ^ 2 = ∑ j ∈ T, a j * x j ^ (2 * f + 2) :=
        sum_congr rfl fun j _ ↦ by ring
      rw [hS]
      ring

/-- **Hölder's inequality for idempotents (B6).** If `aⱼ² = aⱼ` in `A`, `deg aⱼ ≤ 1` and
`‖aⱼ‖₁ ≤ 1` for `j ∈ T`, then `(∑ⱼ aⱼ xⱼ)^(2^t) ≤ (∑ⱼ aⱼ)^(2^t - 1) ∑ⱼ aⱼ xⱼ^(2^t)` for any
polynomials `xⱼ` of degree at most `e`, in degree `2^t (e + 2)` and with norm `(3 c²)^(2^t)` for any
`c ≥ 1` with `|T| ‖xⱼ‖₁ ≤ c`. -/
theorem holder_idem {ι : Type*} (T : Finset ι) {a : ι → MvPolynomial σ ℝ}
    (ha : ∀ j ∈ T, HasEq A (a j ^ 2 - a j)) (had : ∀ j ∈ T, (a j).totalDegree ≤ 1)
    (han : ∀ j ∈ T, coeffNorm1 (a j) ≤ 1) (x : ι → MvPolynomial σ ℝ) {e : ℕ}
    (hxd : ∀ j ∈ T, (x j).totalDegree ≤ e) {β c : ℝ} (hxn : ∀ j ∈ T, coeffNorm1 (x j) ≤ β)
    (hc : 1 ≤ c) (hβc : T.card * β ≤ c) (t : ℕ) :
    SosPlusIdeal A (2 ^ t * (e + 2)) ((3 * c ^ 2) ^ 2 ^ t)
      ((∑ j ∈ T, a j) ^ (2 ^ t - 1) * ∑ j ∈ T, a j * x j ^ 2 ^ t -
        (∑ j ∈ T, a j * x j) ^ 2 ^ t) := by
  cases t with
  | zero =>
    refine (zero A _ (by positivity)).congr ?_
    simp
  | succ t =>
    refine (holder_idem_aux T ha had han x hxd hxn hc hβc t).mono le_rfl ?_
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (by linarith) _)

end SosPlusIdeal

/-! ### Boolean variables on a set -/

/-- The variables in `U` are Boolean: `A` contains `xᵢ² = xᵢ` for every `i ∈ U`. -/
def BooleanOn (A : System σ ℝ) (U : Finset σ) : Prop := ∀ i ∈ U, HasEq A (X i ^ 2 - X i)

theorem Boolean.booleanOn {A : System σ ℝ} (hB : Boolean A) (U : Finset σ) : BooleanOn A U :=
  fun i _ ↦ hB i

namespace BooleanOn

variable {A : System σ ℝ} {U : Finset σ} {i i' : σ}

theorem mono {U' : Finset σ} (hB : BooleanOn A U) (h : U' ⊆ U) : BooleanOn A U' :=
  fun i hi ↦ hB i (h hi)

/-- (B1) `xᵢ = xᵢ² - (xᵢ² - xᵢ) ≥ 0`. -/
theorem X_nonneg (hB : BooleanOn A U) (hi : i ∈ U) : SosPlusIdeal A 2 1 (X i) := by
  refine (SosPlusIdeal.isSumSq_add_mul (isSumSq_sq (X i)) (hB i hi) (-1)
    (by rw [totalDegree_X_pow]) ?_ (coeffNorm1_X_sq_le i) ?_).congr (by ring)
  · rw [totalDegree_neg, totalDegree_one, zero_add]
    exact totalDegree_X_sq_sub_X_le i
  · rw [coeffNorm1_neg, coeffNorm1_one]

theorem totalDegree_one_sub_X_le (i : σ) : (1 - X i : MvPolynomial σ ℝ).totalDegree ≤ 1 :=
  (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_one]; omega) (by rw [totalDegree_X]))

theorem coeffNorm1_one_sub_X_le (i : σ) : coeffNorm1 (1 - X i : MvPolynomial σ ℝ) ≤ 2 :=
  (coeffNorm1_sub_le _ _).trans (by rw [coeffNorm1_one, coeffNorm1_X]; norm_num)

/-- (B2) `1 - xᵢ = (1 - xᵢ)² - (xᵢ² - xᵢ) ≥ 0`. -/
theorem one_sub_X_nonneg (hB : BooleanOn A U) (hi : i ∈ U) : SosPlusIdeal A 2 4 (1 - X i) := by
  have hd := totalDegree_one_sub_X_le (σ := σ) i
  have hn := coeffNorm1_one_sub_X_le (σ := σ) i
  refine (SosPlusIdeal.isSumSq_add_mul (isSumSq_sq (1 - X i)) (hB i hi) (-1)
    ((totalDegree_pow _ 2).trans (by omega)) ?_ ?_ ?_).congr (by ring)
  · rw [totalDegree_neg, totalDegree_one, zero_add]
    exact totalDegree_X_sq_sub_X_le i
  · exact (coeffNorm1_pow_le _ 2).trans
      (by nlinarith [coeffNorm1_nonneg (1 - X i : MvPolynomial σ ℝ)])
  · rw [coeffNorm1_neg, coeffNorm1_one]
    norm_num

/-- (B3) `p = ∑ j ∈ T, x_{w j} ≥ 0`, for variables `w j ∈ U`. -/
theorem sum_nonneg (hB : BooleanOn A U) {ι : Type*} (T : Finset ι) {w : ι → σ}
    (hw : ∀ j ∈ T, w j ∈ U) : SosPlusIdeal A 2 T.card (∑ j ∈ T, X (w j)) := by
  have := SosPlusIdeal.sum T (M := fun _ ↦ (1 : ℝ)) fun j hj ↦ hB.X_nonneg (hw j hj)
  rwa [sum_const, nsmul_eq_mul, mul_one] at this

/-- (B3) `|T| - p ≥ 0` for `p = ∑ j ∈ T, x_{w j}`, for variables `w j ∈ U`. -/
theorem card_sub_sum_nonneg (hB : BooleanOn A U) {ι : Type*} (T : Finset ι) {w : ι → σ}
    (hw : ∀ j ∈ T, w j ∈ U) :
    SosPlusIdeal A 2 (4 * T.card) (C (T.card : ℝ) - ∑ j ∈ T, X (w j)) := by
  have := SosPlusIdeal.sum T (M := fun _ ↦ (4 : ℝ)) fun j hj ↦ hB.one_sub_X_nonneg (hw j hj)
  rw [sum_const, nsmul_eq_mul, mul_comm] at this
  refine this.congr ?_
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, map_natCast]

/-- (B4) `|T| p - p² ≥ 0` for `p = ∑ j ∈ T, x_{w j}`, for variables `w j ∈ U`: by Cauchy–Schwarz,
`p² ≤ |T| ∑ⱼ x_{w j}²`, and `x_{w j}² = x_{w j}`. -/
theorem card_mul_sum_sub_sq_nonneg (hB : BooleanOn A U) {ι : Type*} (T : Finset ι) {w : ι → σ}
    (hw : ∀ j ∈ T, w j ∈ U) :
    SosPlusIdeal A 2 (3 * T.card ^ 2)
      (C (T.card : ℝ) * ∑ j ∈ T, X (w j) - (∑ j ∈ T, X (w j)) ^ 2) := by
  have hs : IsSumSq (C (T.card : ℝ) * ∑ j ∈ T, X (w j) ^ 2 - (∑ j ∈ T, X (w j)) ^ 2 :
      MvPolynomial σ ℝ) := isSumSq_card_mul_sum_sq_sub T fun j ↦ X (w j)
  have hd : (C (T.card : ℝ) * ∑ j ∈ T, X (w j) ^ 2 - (∑ j ∈ T, X (w j)) ^ 2 :
      MvPolynomial σ ℝ).totalDegree ≤ 2 := by
    have := totalDegree_powMean_le T (a := fun j ↦ (X (w j) : MvPolynomial σ ℝ)) (e := 1)
      (fun j _ ↦ (totalDegree_X _).le) (T.card : ℝ) 1
    simpa using this
  have h₁ : coeffNorm1 (∑ j ∈ T, X (w j) ^ 2 : MvPolynomial σ ℝ) ≤ T.card := by
    simpa using coeffNorm1_sum_le_card_mul T _ fun j _ ↦ coeffNorm1_X_sq_le (w j)
  have h₂ : coeffNorm1 (∑ j ∈ T, X (w j) : MvPolynomial σ ℝ) ≤ T.card := by
    simpa using coeffNorm1_sum_le_card_mul T _ fun j _ ↦ (coeffNorm1_X (σ := σ) (w j)).le
  have hn : coeffNorm1 (C (T.card : ℝ) * ∑ j ∈ T, X (w j) ^ 2 - (∑ j ∈ T, X (w j)) ^ 2 :
      MvPolynomial σ ℝ) ≤ 2 * T.card ^ 2 := by
    refine (coeffNorm1_sub_le _ _).trans ?_
    rw [coeffNorm1_C_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    have h₃ := (coeffNorm1_pow_le (∑ j ∈ T, X (w j) : MvPolynomial σ ℝ) 2).trans
      (pow_le_pow_left₀ (coeffNorm1_nonneg _) h₂ 2)
    nlinarith [Nat.cast_nonneg (α := ℝ) T.card]
  refine ((SosPlusIdeal.of_isSumSq A hs hd hn).of_eq_add_ideal T
    (e := fun j ↦ X (w j) ^ 2 - X (w j)) (q := fun _ ↦ -C (T.card : ℝ)) (M' := T.card)
    (fun j hj ↦ hB _ (hw j hj)) (fun j _ ↦ ?_) (fun j _ ↦ ?_) ?_).mono le_rfl
    (le_of_eq (by ring))
  · rw [totalDegree_neg, totalDegree_C, zero_add]
    exact totalDegree_X_sq_sub_X_le _
  · rw [coeffNorm1_neg, coeffNorm1_C, abs_of_nonneg (Nat.cast_nonneg _)]
  · rw [← mul_sum, sum_sub_distrib]
    ring

/-- (B3) for `p_U = ∑ i ∈ U, xᵢ`: `p_U ≥ 0`. -/
theorem sum_self_nonneg (hB : BooleanOn A U) : SosPlusIdeal A 2 U.card (∑ i ∈ U, X i) :=
  hB.sum_nonneg U (w := id) fun _ h ↦ h

/-- (B3) for `p_U = ∑ i ∈ U, xᵢ`: `|U| - p_U ≥ 0`. -/
theorem card_sub_sum_self_nonneg (hB : BooleanOn A U) :
    SosPlusIdeal A 2 (4 * U.card) (C (U.card : ℝ) - ∑ i ∈ U, X i) :=
  hB.card_sub_sum_nonneg U (w := id) fun _ h ↦ h

/-- (B4) for `p_U = ∑ i ∈ U, xᵢ`: `|U| p_U - p_U² ≥ 0`. -/
theorem card_mul_sum_self_sub_sq_nonneg (hB : BooleanOn A U) :
    SosPlusIdeal A 2 (3 * U.card ^ 2) (C (U.card : ℝ) * ∑ i ∈ U, X i - (∑ i ∈ U, X i) ^ 2) :=
  hB.card_mul_sum_sub_sq_nonneg U (w := id) fun _ h ↦ h

theorem totalDegree_X_mul_X_le (i i' : σ) : (X i * X i' : MvPolynomial σ ℝ).totalDegree ≤ 2 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_X, totalDegree_X])

/-- (B5) `xᵢ xᵢ' = (xᵢ xᵢ')² - xᵢ'² (xᵢ² - xᵢ) - xᵢ (xᵢ'² - xᵢ') ≥ 0`. -/
theorem X_mul_X_nonneg (hB : BooleanOn A U) (hi : i ∈ U) (hi' : i' ∈ U) :
    SosPlusIdeal A 4 3 (X i * X i') := by
  have h₁ := SosPlusIdeal.of_isSumSq A (k := 4) (M := 1) (isSumSq_sq (X i * X i'))
    ((totalDegree_pow _ 2).trans (by have := totalDegree_X_mul_X_le (σ := σ) i i'; omega))
    ((coeffNorm1_pow_le _ 2).trans (pow_le_one₀ (coeffNorm1_nonneg _)
      ((coeffNorm1_mul_le _ _).trans (by rw [coeffNorm1_X, coeffNorm1_X, one_mul]))))
  have h₂ := SosPlusIdeal.ideal (k := 4) (M := 1) (hB i hi) (-(X i' ^ 2))
    (by rw [totalDegree_neg, totalDegree_X_pow]; have := totalDegree_X_sq_sub_X_le (σ := σ) i
        omega)
    (by rw [coeffNorm1_neg]; exact coeffNorm1_X_sq_le i')
  have h₃ := SosPlusIdeal.ideal (k := 4) (M := 1) (hB i' hi') (-X i)
    (by rw [totalDegree_neg, totalDegree_X]; have := totalDegree_X_sq_sub_X_le (σ := σ) i'
        omega)
    (by rw [coeffNorm1_neg, coeffNorm1_X])
  exact ((h₁.add h₂).add h₃).mono le_rfl (by norm_num) |>.congr (by ring)

/-- (B5) `xᵢ (1 - xᵢ') = (xᵢ (1 - xᵢ'))² - xᵢ (xᵢ'² - xᵢ') - (1 - xᵢ')² (xᵢ² - xᵢ) ≥ 0`. -/
theorem X_mul_one_sub_X_nonneg (hB : BooleanOn A U) (hi : i ∈ U) (hi' : i' ∈ U) :
    SosPlusIdeal A 4 9 (X i * (1 - X i')) := by
  have hd := totalDegree_one_sub_X_le (σ := σ) i'
  have hn := coeffNorm1_one_sub_X_le (σ := σ) i'
  have hn2 : coeffNorm1 ((1 - X i') ^ 2 : MvPolynomial σ ℝ) ≤ 4 := (coeffNorm1_pow_le _ 2).trans
    (by nlinarith [coeffNorm1_nonneg (1 - X i' : MvPolynomial σ ℝ)])
  have h₁ := SosPlusIdeal.of_isSumSq A (k := 4) (M := 4) (isSumSq_sq (X i * (1 - X i')))
    ((totalDegree_pow _ 2).trans (by
      have := (totalDegree_mul (X i : MvPolynomial σ ℝ) (1 - X i')).trans
        (add_le_add (totalDegree_X (R := ℝ) i).le hd)
      omega))
    ((coeffNorm1_pow_le _ 2).trans (by
      have : coeffNorm1 (X i * (1 - X i') : MvPolynomial σ ℝ) ≤ 2 :=
        (coeffNorm1_mul_le _ _).trans (by rw [coeffNorm1_X, one_mul]; exact hn)
      nlinarith [coeffNorm1_nonneg (X i * (1 - X i') : MvPolynomial σ ℝ)]))
  have h₂ := SosPlusIdeal.ideal (k := 4) (M := 1) (hB i' hi') (-X i)
    (by rw [totalDegree_neg, totalDegree_X]; have := totalDegree_X_sq_sub_X_le (σ := σ) i'
        omega)
    (by rw [coeffNorm1_neg, coeffNorm1_X])
  have h₃ := SosPlusIdeal.ideal (k := 4) (M := 4) (hB i hi) (-(1 - X i') ^ 2)
    (by
      rw [totalDegree_neg]
      have := (totalDegree_pow (1 - X i' : MvPolynomial σ ℝ) 2).trans (Nat.mul_le_mul_left 2 hd)
      have := totalDegree_X_sq_sub_X_le (σ := σ) i
      omega)
    (by rw [coeffNorm1_neg]; exact hn2)
  exact ((h₁.add h₂).add h₃).mono le_rfl (by norm_num) |>.congr (by ring)

/-- **Hölder's inequality (B6)** for Boolean variables `w j ∈ U`: with `p = ∑ j ∈ T, x_{w j}`,
`(∑ⱼ x_{w j} yⱼ)^(2^t) ≤ p^(2^t - 1) ∑ⱼ x_{w j} yⱼ^(2^t)` for any polynomials `yⱼ` of degree at most
`e`, in degree `2^t (e + 2)` and with norm `(3 c²)^(2^t)` for any `c ≥ 1` with `|T| ‖yⱼ‖₁ ≤ c`. -/
theorem holder (hB : BooleanOn A U) {ι : Type*} (T : Finset ι) {w : ι → σ}
    (hw : ∀ j ∈ T, w j ∈ U) (y : ι → MvPolynomial σ ℝ) {e : ℕ}
    (hyd : ∀ j ∈ T, (y j).totalDegree ≤ e) {β c : ℝ} (hyn : ∀ j ∈ T, coeffNorm1 (y j) ≤ β)
    (hc : 1 ≤ c) (hβc : T.card * β ≤ c) (t : ℕ) :
    SosPlusIdeal A (2 ^ t * (e + 2)) ((3 * c ^ 2) ^ 2 ^ t)
      ((∑ j ∈ T, X (w j)) ^ (2 ^ t - 1) * ∑ j ∈ T, X (w j) * y j ^ 2 ^ t -
        (∑ j ∈ T, X (w j) * y j) ^ 2 ^ t) :=
  SosPlusIdeal.holder_idem T (a := fun j ↦ X (w j)) (fun j hj ↦ hB _ (hw j hj))
    (fun _ _ ↦ (totalDegree_X _).le) (fun _ _ ↦ (coeffNorm1_X _).le) y hyd hyn hc hβc t

/-- (B6) for `p_U = ∑ i ∈ U, xᵢ`:
`(∑ i ∈ U, xᵢ yᵢ)^(2^t) ≤ p_U^(2^t - 1) ∑ i ∈ U, xᵢ yᵢ^(2^t)`. -/
theorem holder_self (hB : BooleanOn A U) (y : σ → MvPolynomial σ ℝ) {e : ℕ}
    (hyd : ∀ i ∈ U, (y i).totalDegree ≤ e) {β c : ℝ} (hyn : ∀ i ∈ U, coeffNorm1 (y i) ≤ β)
    (hc : 1 ≤ c) (hβc : U.card * β ≤ c) (t : ℕ) :
    SosPlusIdeal A (2 ^ t * (e + 2)) ((3 * c ^ 2) ^ 2 ^ t)
      ((∑ i ∈ U, X i) ^ (2 ^ t - 1) * ∑ i ∈ U, X i * y i ^ 2 ^ t -
        (∑ i ∈ U, X i * y i) ^ 2 ^ t) :=
  hB.holder U (w := id) (fun _ h ↦ h) y hyd hyn hc hβc t

end BooleanOn

end SoS
