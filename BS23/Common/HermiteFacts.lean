module

public import BS23.Common.Hermite
public import BS23.Common.Good
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Identities for the Hermite polynomials with a variance parameter

Facts about `BS23.hermite` and `BS23.hmom` (`BS23/Common/Hermite.lean`), over any commutative
ring unless stated:

* `BS23.hermite_eq_hmom_neg`: `He_m(x; q) = hmom m x (-q)`.
* Homogeneity: `He_m(β x; β² q) = β^m He_m(x; q)`, and the same for `hmom`.
* `BS23.hmom_add_var`: adding variances, `hmom m a (u + v) = ∑_l c_{m,l} v^l hmom (m-2l) a u`
  (`E (a + √u Z + √v Z')^m`, expanded in `Z'`). It gives
  * the heat identity `BS23.sum_hmom_eq_hermite`:
    `∑_i (-1)^i c_{m,i} q^i hmom (m-2i) a v = He_m(a; q - v)`, i.e. `E He_m(a + √v Z; q) =
    He_m(a; q - v)`;
  * the inversion `BS23.pow_eq_sum_hermite`: `x^r = ∑_i c_{r,i} q^i He_{r-2i}(x; q)`.
* `BS23.hmom_sq_eq_sum_gaussMom`, `BS23.hmom_eq_sum_gaussMom`: `hmom r a v` as the binomial
  expansion of `E (a + √v Z)^r` with the Gaussian moments `BS23.gaussMom`.
* The three-term recurrences `He_{m+2} = x He_{m+1} - (m+1) q He_m` and
  `hmom (m+2) = a hmom (m+1) + (m+1) v hmom m`.
* Derivatives: `∂ₓ He_m = m He_{m-1}` and `∂_q He_m = -C(m, 2) He_{m-2}`, as identities of the
  termwise derivative sums over any commutative ring, and as `HasDerivAt` over `ℝ`, also along
  any line `t ↦ (x + t a, q + t b)` (`BS23.hasDerivAt_hermite_line`); likewise
  `∂ₐ hmom m = m hmom (m-1)` and `∂_v hmom m = C(m, 2) hmom (m-2)`.

Here `c_{m,i} = BS23.hermCoeff m i = C(m, 2i) (2i-1)‼ = m! / (i! (m-2i)! 2^i)`.
-/

@[expose] public section

namespace BS23

open Finset
open scoped Nat

/-! ### The coefficients -/

theorem hermCoeff_eq_zero {m i : ℕ} (h : m < 2 * i) : hermCoeff m i = 0 := by
  simp [hermCoeff, Nat.choose_eq_zero_of_lt h]

@[simp] theorem hermCoeff_zero_right (m : ℕ) : hermCoeff m 0 = 1 := by simp [hermCoeff]

theorem hermCoeff_two_mul_self (n : ℕ) : hermCoeff (2 * n) n = (2 * n - 1)‼ := by
  simp [hermCoeff]

/-- `(2i-1)‼ · 2^i · i! = (2i)!`. -/
theorem doubleFactorial_two_mul_sub_one_mul (i : ℕ) :
    (2 * i - 1)‼ * (2 ^ i * i !) = (2 * i)! := by
  cases i with
  | zero => rfl
  | succ i =>
    have h1 := Nat.doubleFactorial_two_mul (i + 1)
    have h2 := Nat.factorial_eq_mul_doubleFactorial (2 * i + 1)
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, ← h1, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
      h2, mul_comm]

/-- `c_{m,i} · 2^i · i! · (m-2i)! = m!`. -/
theorem hermCoeff_mul_factorial {m i : ℕ} (h : 2 * i ≤ m) :
    hermCoeff m i * (2 ^ i * i ! * (m - 2 * i)!) = m ! := by
  rw [hermCoeff]
  calc m.choose (2 * i) * (2 * i - 1)‼ * (2 ^ i * i ! * (m - 2 * i)!)
      = m.choose (2 * i) * ((2 * i - 1)‼ * (2 ^ i * i !)) * (m - 2 * i)! := by ring
    _ = m ! := by rw [doubleFactorial_two_mul_sub_one_mul, Nat.choose_mul_factorial_mul_factorial h]

/-- The coefficient identity behind `hmom_add_var`. -/
theorem hermCoeff_add_mul_choose (m l j : ℕ) :
    hermCoeff m (l + j) * (l + j).choose j = hermCoeff m l * hermCoeff (m - 2 * l) j := by
  rcases lt_or_ge m (2 * (l + j)) with h | h
  · rw [hermCoeff_eq_zero h, zero_mul]
    rcases lt_or_ge m (2 * l) with h' | h'
    · rw [hermCoeff_eq_zero h', zero_mul]
    · rw [hermCoeff_eq_zero (show m - 2 * l < 2 * j by omega), mul_zero]
  · have hF : 0 < 2 ^ (l + j) * l ! * j ! * (m - 2 * (l + j))! := by positivity
    refine Nat.eq_of_mul_eq_mul_right hF ?_
    have e1 : hermCoeff m (l + j) * (l + j).choose j * (2 ^ (l + j) * l ! * j ! *
        (m - 2 * (l + j))!) = hermCoeff m (l + j) * (2 ^ (l + j) * ((l + j).choose j * l ! * j !)
        * (m - 2 * (l + j))!) := by ring
    have e2 : hermCoeff m l * hermCoeff (m - 2 * l) j * (2 ^ (l + j) * l ! * j ! *
        (m - 2 * (l + j))!) = hermCoeff m l * (hermCoeff (m - 2 * l) j * (2 ^ j * j ! *
        (m - 2 * l - 2 * j)!)) * (2 ^ l * l !) := by
      rw [show m - 2 * l - 2 * j = m - 2 * (l + j) by omega]; ring
    rw [e1, e2, Nat.add_choose_mul_factorial_mul_factorial, hermCoeff_mul_factorial h,
      hermCoeff_mul_factorial (by omega), mul_assoc, mul_comm ((m - 2 * l)!),
      hermCoeff_mul_factorial (by omega)]

/-- `(2i+1)‼ = (2i+1) (2i-1)‼`. -/
theorem doubleFactorial_two_mul_add_one (i : ℕ) : (2 * i + 1)‼ = (2 * i + 1) * (2 * i - 1)‼ :=
  Nat.doubleFactorial_add_one (2 * i)

/-- The coefficient identity behind the three-term recurrence. -/
theorem hermCoeff_succ_succ (m i : ℕ) :
    hermCoeff (m + 2) (i + 1) = hermCoeff (m + 1) (i + 1) + (m + 1) * hermCoeff m i := by
  simp only [hermCoeff]
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 - 1 = 2 * i + 1 by omega,
    show m + 2 = m + 1 + 1 by ring, Nat.choose_succ_succ' (m + 1) (2 * i + 1),
    doubleFactorial_two_mul_add_one]
  have := Nat.add_one_mul_choose_eq m (2 * i)
  calc ((m + 1).choose (2 * i + 1) + (m + 1).choose (2 * i + 1 + 1)) *
        ((2 * i + 1) * (2 * i - 1)‼)
      = (m + 1).choose (2 * i + 1 + 1) * ((2 * i + 1) * (2 * i - 1)‼) +
          (m + 1).choose (2 * i + 1) * (2 * i + 1) * (2 * i - 1)‼ := by ring
    _ = _ := by rw [← this]; ring

/-- The coefficient identity behind `∂ₓ He_{m+1} = (m+1) He_m`. -/
theorem sub_mul_hermCoeff (m i : ℕ) :
    (m + 1 - 2 * i) * hermCoeff (m + 1) i = (m + 1) * hermCoeff m i := by
  simp only [hermCoeff]
  have := Nat.choose_mul_succ_eq m (2 * i)
  calc (m + 1 - 2 * i) * ((m + 1).choose (2 * i) * (2 * i - 1)‼)
      = (m + 1).choose (2 * i) * (m + 1 - 2 * i) * (2 * i - 1)‼ := by ring
    _ = _ := by rw [← this]; ring

/-- The coefficient identity behind `∂_q He_{m+2} = -C(m+2, 2) He_m`. -/
theorem succ_mul_hermCoeff (m i : ℕ) :
    (i + 1) * hermCoeff (m + 2) (i + 1) = (m + 2).choose 2 * hermCoeff m i := by
  simp only [hermCoeff]
  rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 - 1 = 2 * i + 1 by omega,
    doubleFactorial_two_mul_add_one]
  have h1 : (m + 2) * (m + 1).choose (2 * i + 1) = (m + 2).choose (2 * i + 1 + 1) * (2 * i + 2) :=
    Nat.add_one_mul_choose_eq (m + 1) (2 * i + 1)
  have h2 : (m + 1) * m.choose (2 * i) = (m + 1).choose (2 * i + 1) * (2 * i + 1) :=
    Nat.add_one_mul_choose_eq m (2 * i)
  have h3 : (m + 2) * (m + 1) = (m + 2).choose 2 * 2 := by
    have := Nat.add_one_mul_choose_eq (m + 1) 1
    rwa [Nat.choose_one_right] at this
  generalize (m + 2).choose (2 * i + 1 + 1) = A at *
  generalize (m + 1).choose (2 * i + 1) = B at *
  generalize m.choose (2 * i) = C at *
  generalize (m + 2).choose 2 = E at *
  generalize (2 * i - 1)‼ = d
  refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num) ?_
  calc 2 * ((i + 1) * (A * ((2 * i + 1) * d))) = A * (2 * i + 2) * (2 * i + 1) * d := by ring
    _ = (m + 2) * (B * (2 * i + 1)) * d := by rw [← h1]; ring
    _ = (m + 2) * (m + 1) * C * d := by rw [← h2]; ring
    _ = 2 * (E * (C * d)) := by rw [h3]; ring

/-! ### Basic values -/

variable {K : Type*} [CommRing K]

/-- A sum over `range (m / 2 + 1)` whose terms vanish beyond `m / 2` may be taken over any longer
range. -/
theorem sum_range_half_eq {M : Type*} [AddCommMonoid M] {m N : ℕ} (hN : m / 2 < N) (f : ℕ → M)
    (hf : ∀ i, m < 2 * i → f i = 0) :
    ∑ i ∈ range (m / 2 + 1), f i = ∑ i ∈ range N, f i := by
  apply Finset.sum_subset
  · intro i hi
    simp only [mem_range] at hi ⊢
    omega
  · intro i _ hi'
    simp only [mem_range, not_lt] at hi'
    exact hf i (by omega)

theorem hermite_eq_sum_range {m N : ℕ} (hN : m / 2 < N) (x q : K) :
    hermite m x q = ∑ i ∈ range N, (-1) ^ i * (hermCoeff m i : K) * x ^ (m - 2 * i) * q ^ i :=
  sum_range_half_eq hN _ fun i hi ↦ by simp [hermCoeff_eq_zero hi]

theorem hmom_eq_sum_range {m N : ℕ} (hN : m / 2 < N) (a v : K) :
    hmom m a v = ∑ i ∈ range N, (hermCoeff m i : K) * a ^ (m - 2 * i) * v ^ i :=
  sum_range_half_eq hN _ fun i hi ↦ by simp [hermCoeff_eq_zero hi]

@[simp] theorem hermite_zero (x q : K) : hermite 0 x q = 1 := by simp [hermite]

@[simp] theorem hmom_zero (a v : K) : hmom 0 a v = 1 := by simp [hmom]

@[simp] theorem hermite_one (x q : K) : hermite 1 x q = x := by simp [hermite]

@[simp] theorem hmom_one (a v : K) : hmom 1 a v = a := by simp [hmom]

theorem hermite_two (x q : K) : hermite 2 x q = x ^ 2 - q := by
  simp [hermite, sum_range_succ, hermCoeff]
  ring

theorem hmom_two (a v : K) : hmom 2 a v = a ^ 2 + v := by
  simp [hmom, sum_range_succ, hermCoeff]

/-- `He_m(x; q) = hmom m x (-q)`. -/
theorem hermite_eq_hmom_neg (m : ℕ) (x q : K) : hermite m x q = hmom m x (-q) := by
  simp only [hermite, hmom]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [neg_pow]
  ring

theorem hmom_eq_hermite_neg (m : ℕ) (a v : K) : hmom m a v = hermite m a (-v) := by
  rw [hermite_eq_hmom_neg, neg_neg]

/-- At variance `0`, `hmom r a 0 = a^r`. -/
@[simp] theorem hmom_zero_var (r : ℕ) (a : K) : hmom r a 0 = a ^ r := by
  rw [hmom, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

@[simp] theorem hermite_zero_var (r : ℕ) (x : K) : hermite r x 0 = x ^ r := by
  rw [hermite_eq_hmom_neg, neg_zero, hmom_zero_var]

/-! ### Homogeneity and parity -/

/-- Homogeneity: `He_m(β x; β² q) = β^m He_m(x; q)`. -/
theorem hermite_mul (m : ℕ) (β x q : K) :
    hermite m (β * x) (β ^ 2 * q) = β ^ m * hermite m x q := by
  simp only [hermite, mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi' : 2 * i ≤ m := by simp only [mem_range] at hi; omega
  have hp : β ^ m = β ^ (m - 2 * i) * (β ^ 2) ^ i := by
    rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hi']
  rw [hp]
  ring

/-- Homogeneity: `hmom m (β a) (β² v) = β^m hmom m a v`. -/
theorem hmom_mul (m : ℕ) (β a v : K) : hmom m (β * a) (β ^ 2 * v) = β ^ m * hmom m a v := by
  rw [hmom_eq_hermite_neg, hmom_eq_hermite_neg, ← mul_neg, hermite_mul]

theorem hermite_neg (m : ℕ) (x q : K) : hermite m (-x) q = (-1) ^ m * hermite m x q := by
  have := hermite_mul m (-1) x q
  rwa [neg_one_sq, one_mul, neg_one_mul] at this

theorem hmom_neg (m : ℕ) (a v : K) : hmom m (-a) v = (-1) ^ m * hmom m a v := by
  rw [hmom_eq_hermite_neg, hmom_eq_hermite_neg, hermite_neg]

/-! ### Adding variances -/

/-- Adding variances: `hmom m a (u + v) = ∑_l c_{m,l} v^l hmom (m - 2l) a u`. In probabilistic
terms, `E (a + √u Z + √v Z')^m` expanded in the independent Gaussian `Z'`. -/
theorem hmom_add_var (m : ℕ) (a u v : K) :
    hmom m a (u + v) =
      ∑ l ∈ range (m / 2 + 1), (hermCoeff m l : K) * v ^ l * hmom (m - 2 * l) a u := by
  simp only [hmom, add_pow, mul_sum]
  rw [sum_sigma', sum_sigma']
  refine Finset.sum_nbij' (fun x ↦ ⟨x.1 - x.2, x.2⟩) (fun y ↦ ⟨y.1 + y.2, y.2⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hx
    simp only [mem_sigma, mem_range] at hx ⊢
    omega
  · rintro ⟨l, j⟩ hy
    simp only [mem_sigma, mem_range] at hy ⊢
    omega
  · rintro ⟨i, j⟩ hx
    simp only [mem_sigma, mem_range] at hx
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    omega
  · rintro ⟨l, j⟩ _
    simp
  · rintro ⟨i, j⟩ hx
    simp only [mem_sigma, mem_range] at hx
    obtain ⟨l, rfl⟩ : ∃ l, i = l + j := ⟨i - j, by omega⟩
    simp only [Nat.add_sub_cancel]
    have hc := congrArg (Nat.cast : ℕ → K) (hermCoeff_add_mul_choose m l j)
    push_cast at hc
    rw [show m - 2 * l - 2 * j = m - 2 * (l + j) by omega]
    linear_combination (a ^ (m - 2 * (l + j)) * u ^ j * v ^ l) * hc

/-- The heat identity: `∑_i (-1)^i c_{m,i} q^i hmom (m - 2i) a v = He_m(a; q - v)`, i.e.
`E He_m(a + √v Z; q) = He_m(a; q - v)`. -/
theorem sum_hmom_eq_hermite (m : ℕ) (a q v : K) :
    ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : K) * q ^ i * hmom (m - 2 * i) a v =
      hermite m a (q - v) := by
  rw [hermite_eq_hmom_neg, show -(q - v) = v + -q by ring, hmom_add_var]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [neg_pow]
  ring

/-- Inversion: `x^r = ∑_i c_{r,i} q^i He_{r-2i}(x; q)`. -/
theorem pow_eq_sum_hermite (r : ℕ) (x q : K) :
    x ^ r = ∑ i ∈ range (r / 2 + 1), (hermCoeff r i : K) * q ^ i * hermite (r - 2 * i) x q := by
  have h := hmom_add_var r x (-q) q
  rw [neg_add_cancel, hmom_zero_var] at h
  rw [h]
  simp only [hermite_eq_hmom_neg]

/-! ### Gaussian moments -/

/-- `hmom r a (s²)` is the binomial expansion of `E (a + s Z)^r`. -/
theorem hmom_sq_eq_sum_gaussMom (r : ℕ) (a s : K) :
    hmom r a (s ^ 2) =
      ∑ p ∈ range (r + 1), (r.choose p : K) * a ^ (r - p) * (gaussMom p : K) * s ^ p := by
  have hsub : (range (r / 2 + 1)).image (fun i ↦ 2 * i) ⊆ range (r + 1) := by
    intro p hp
    simp only [mem_image, mem_range] at hp ⊢
    omega
  rw [← Finset.sum_subset hsub, Finset.sum_image]
  · rw [hmom]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [hermCoeff, gaussMom, even_two_mul, ite_true, Nat.cast_mul, pow_mul]
    ring
  · intro i _ j _ h
    simpa using h
  · intro p hp hp'
    have hodd : ¬ Even p := by
      rintro ⟨i, rfl⟩
      apply hp'
      simp only [mem_image, mem_range] at hp ⊢
      exact ⟨i, by omega, by omega⟩
    simp [gaussMom, hodd]

/-- The moments of a Gaussian of mean `a` and variance `v ≥ 0`:
`hmom r a v = ∑_p C(r, p) a^(r-p) E Z^p (√v)^p`. -/
theorem hmom_eq_sum_gaussMom (r : ℕ) (a : ℝ) {v : ℝ} (hv : 0 ≤ v) :
    hmom r a v =
      ∑ p ∈ range (r + 1), (r.choose p : ℝ) * a ^ (r - p) * (gaussMom p : ℝ) * Real.sqrt v ^ p := by
  rw [← hmom_sq_eq_sum_gaussMom, Real.sq_sqrt hv]

/-! ### Three-term recurrences -/

/-- `hmom (m + 2) a v = a hmom (m + 1) a v + (m + 1) v hmom m a v`. -/
theorem hmom_succ_succ (m : ℕ) (a v : K) :
    hmom (m + 2) a v = a * hmom (m + 1) a v + (m + 1) * v * hmom m a v := by
  rw [hmom_eq_sum_range (m := m + 2) (N := m / 2 + 1 + 1) (by omega),
    hmom_eq_sum_range (m := m + 1) (N := m / 2 + 1 + 1) (by omega), hmom,
    sum_range_succ' (fun i ↦ (hermCoeff (m + 2) i : K) * a ^ (m + 2 - 2 * i) * v ^ i),
    sum_range_succ' (fun i ↦ (hermCoeff (m + 1) i : K) * a ^ (m + 1 - 2 * i) * v ^ i),
    mul_add, mul_sum, mul_sum]
  have key : ∀ j ∈ range (m / 2 + 1),
      (hermCoeff (m + 2) (j + 1) : K) * a ^ (m + 2 - 2 * (j + 1)) * v ^ (j + 1) =
        a * ((hermCoeff (m + 1) (j + 1) : K) * a ^ (m + 1 - 2 * (j + 1)) * v ^ (j + 1)) +
          (m + 1) * v * ((hermCoeff m j : K) * a ^ (m - 2 * j) * v ^ j) := by
    intro j _
    have hc := congrArg (Nat.cast : ℕ → K) (hermCoeff_succ_succ m j)
    push_cast at hc
    have ha : (hermCoeff (m + 1) (j + 1) : K) * (a * a ^ (m + 1 - 2 * (j + 1))) =
        hermCoeff (m + 1) (j + 1) * a ^ (m - 2 * j) := by
      rcases le_or_gt (2 * (j + 1)) (m + 1) with h | h
      · rw [← pow_succ', show m + 1 - 2 * (j + 1) + 1 = m - 2 * j by omega]
      · rw [hermCoeff_eq_zero h, Nat.cast_zero, zero_mul, zero_mul]
    rw [show m + 2 - 2 * (j + 1) = m - 2 * j by omega]
    linear_combination (a ^ (m - 2 * j) * v ^ (j + 1)) * hc - v ^ (j + 1) * ha
  rw [sum_congr rfl key, sum_add_distrib]
  simp only [hermCoeff_zero_right, Nat.cast_one, one_mul, pow_zero, mul_one, Nat.mul_zero,
    Nat.sub_zero]
  ring

/-- The three-term recurrence `He_{m+2}(x; q) = x He_{m+1}(x; q) - (m + 1) q He_m(x; q)`. -/
theorem hermite_succ_succ (m : ℕ) (x q : K) :
    hermite (m + 2) x q = x * hermite (m + 1) x q - (m + 1) * q * hermite m x q := by
  simp only [hermite_eq_hmom_neg]
  rw [hmom_succ_succ]
  ring

/-! ### Derivatives -/

/-- The termwise `x`-derivative of `He_m(x; q)` is `m He_{m-1}(x; q)`. -/
theorem sum_hermite_deriv_x (m : ℕ) (x q : K) :
    ∑ i ∈ range (m / 2 + 1),
        (-1) ^ i * (hermCoeff m i : K) * ((m - 2 * i : ℕ) * x ^ (m - 2 * i - 1)) * q ^ i =
      m * hermite (m - 1) x q := by
  cases m with
  | zero => simp
  | succ n =>
    rw [sum_range_half_eq (N := n / 2 + 1 + 1) (by omega) _
        (fun i hi ↦ by simp [hermCoeff_eq_zero hi]),
      Nat.add_sub_cancel, hermite_eq_sum_range (N := n / 2 + 1 + 1) (by omega), mul_sum]
    refine sum_congr rfl fun i _ ↦ ?_
    have hc := congrArg (Nat.cast : ℕ → K) (sub_mul_hermCoeff n i)
    push_cast at hc
    rw [show n + 1 - 2 * i - 1 = n - 2 * i by omega]
    push_cast
    linear_combination ((-1) ^ i * x ^ (n - 2 * i) * q ^ i) * hc

/-- The termwise `q`-derivative of `He_m(x; q)` is `-C(m, 2) He_{m-2}(x; q)`. -/
theorem sum_hermite_deriv_q (m : ℕ) (x q : K) :
    ∑ i ∈ range (m / 2 + 1),
        (-1) ^ i * (hermCoeff m i : K) * x ^ (m - 2 * i) * ((i : K) * q ^ (i - 1)) =
      -((m.choose 2 : ℕ) : K) * hermite (m - 2) x q := by
  match m with
  | 0 => simp
  | 1 => simp
  | n + 2 =>
    rw [show (n + 2) / 2 + 1 = n / 2 + 1 + 1 by omega, sum_range_succ', Nat.add_sub_cancel,
      hermite, mul_sum]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    refine sum_congr rfl fun j _ ↦ ?_
    have hc := congrArg (Nat.cast : ℕ → K) (succ_mul_hermCoeff n j)
    push_cast at hc
    rw [show n + 2 - 2 * (j + 1) = n - 2 * j by omega, Nat.add_sub_cancel]
    push_cast
    linear_combination (-(-1) ^ j * x ^ (n - 2 * j) * q ^ j) * hc

/-- The derivative of `He_m` along a line: for `X = x + t a` and `Q = q + t b`,
`d/dt He_m(X; Q) = a m He_{m-1}(X; Q) - b C(m, 2) He_{m-2}(X; Q)`. -/
theorem hasDerivAt_hermite_line (m : ℕ) (x q a b t : ℝ) :
    HasDerivAt (fun s ↦ hermite m (x + s * a) (q + s * b))
      (a * (m * hermite (m - 1) (x + t * a) (q + t * b)) -
        b * ((m.choose 2 : ℝ) * hermite (m - 2) (x + t * a) (q + t * b))) t := by
  have hX : HasDerivAt (fun s : ℝ ↦ x + s * a) a t := by
    simpa using ((hasDerivAt_id t).mul_const a).const_add x
  have hQ : HasDerivAt (fun s : ℝ ↦ q + s * b) b t := by
    simpa using ((hasDerivAt_id t).mul_const b).const_add q
  have hterm : ∀ i ∈ range (m / 2 + 1), HasDerivAt
      (fun s ↦ (-1) ^ i * (hermCoeff m i : ℝ) * (x + s * a) ^ (m - 2 * i) * (q + s * b) ^ i)
      ((-1) ^ i * (hermCoeff m i : ℝ) *
          (((m - 2 * i : ℕ) : ℝ) * (x + t * a) ^ (m - 2 * i - 1) * a) * (q + t * b) ^ i +
        (-1) ^ i * (hermCoeff m i : ℝ) * (x + t * a) ^ (m - 2 * i) *
          ((i : ℝ) * (q + t * b) ^ (i - 1) * b)) t :=
    fun i _ ↦ ((hX.pow (m - 2 * i)).const_mul _).mul (hQ.pow i)
  convert HasDerivAt.sum hterm using 1
  · ext s
    simp [hermite]
  · have hD1 := sum_hermite_deriv_x m (x + t * a) (q + t * b)
    have hD2 := sum_hermite_deriv_q m (x + t * a) (q + t * b)
    have e1 : ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) *
          (((m - 2 * i : ℕ) : ℝ) * (x + t * a) ^ (m - 2 * i - 1) * a) * (q + t * b) ^ i =
        a * ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) *
          (((m - 2 * i : ℕ) : ℝ) * (x + t * a) ^ (m - 2 * i - 1)) * (q + t * b) ^ i := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    have e2 : ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) *
          (x + t * a) ^ (m - 2 * i) * ((i : ℝ) * (q + t * b) ^ (i - 1) * b) =
        b * ∑ i ∈ range (m / 2 + 1), (-1) ^ i * (hermCoeff m i : ℝ) *
          (x + t * a) ^ (m - 2 * i) * ((i : ℝ) * (q + t * b) ^ (i - 1)) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ by ring
    rw [sum_add_distrib]
    linear_combination (-1 : ℝ) * e1 - e2 - a * hD1 - b * hD2

/-- `∂ₓ He_m(x; q) = m He_{m-1}(x; q)`. -/
theorem hasDerivAt_hermite_x (m : ℕ) (x q : ℝ) :
    HasDerivAt (fun y ↦ hermite m y q) (m * hermite (m - 1) x q) x := by
  simpa using hasDerivAt_hermite_line m 0 q 1 0 x

/-- `∂_q He_m(x; q) = -C(m, 2) He_{m-2}(x; q)`. -/
theorem hasDerivAt_hermite_q (m : ℕ) (x q : ℝ) :
    HasDerivAt (fun r ↦ hermite m x r) (-((m.choose 2 : ℝ) * hermite (m - 2) x q)) q := by
  simpa using hasDerivAt_hermite_line m x 0 0 1 q

/-- The derivative of `hmom m` along a line: for `X = x + t a` and `V = v + t b`,
`d/dt hmom m X V = a m hmom (m-1) X V + b C(m, 2) hmom (m-2) X V`. -/
theorem hasDerivAt_hmom_line (m : ℕ) (x v a b t : ℝ) :
    HasDerivAt (fun s ↦ hmom m (x + s * a) (v + s * b))
      (a * (m * hmom (m - 1) (x + t * a) (v + t * b)) +
        b * ((m.choose 2 : ℝ) * hmom (m - 2) (x + t * a) (v + t * b))) t := by
  have h := hasDerivAt_hermite_line m x (-v) a (-b) t
  simp only [hmom_eq_hermite_neg]
  convert h using 1
  · ext s
    congr 1
    ring
  · rw [show -(v + t * b) = -v + t * -b by ring]
    ring

/-- `∂ₐ hmom m a v = m hmom (m-1) a v`. -/
theorem hasDerivAt_hmom_a (m : ℕ) (a v : ℝ) :
    HasDerivAt (fun y ↦ hmom m y v) (m * hmom (m - 1) a v) a := by
  simpa using hasDerivAt_hmom_line m 0 v 1 0 a

/-- `∂_v hmom m a v = C(m, 2) hmom (m-2) a v`. -/
theorem hasDerivAt_hmom_v (m : ℕ) (a v : ℝ) :
    HasDerivAt (fun r ↦ hmom m a r) ((m.choose 2 : ℝ) * hmom (m - 2) a v) v := by
  simpa using hasDerivAt_hmom_line m a 0 0 1 v

end BS23
