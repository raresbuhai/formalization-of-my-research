module

public import BS23.ColinearSoS.Defs
public import BS23.Common.HermiteFacts
public import BS23.Common.Gaussian
public import Background.SumOfSquares.Holder
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The moments along the line of means: log-convexity and ratios

Facts about the moments `M_{2l} = lineMom w a σ² l = ∑_c w_c hmom (2l) a_c σ²` of the
one-dimensional mixture `∑_c w_c N(a_c, σ²)` (weights `w_c ≥ 0` summing to `1`, `σ² ≥ 0`,
normalized by `∑_c w_c a_c² + σ² = 1`), and about the normalized coefficients
`β_l = nbeta w a σ² m l = (2m-1)‼ M_{2l} / (2l-1)‼` that decide which of the sum-of-squares
programs for [BS23, Theorem 1.2] concentrates on the line of means.

* `BS23.ColinearSoS.hmom_eq_integral`: `hmom r a v = E (a + √v Z)^r` for a standard Gaussian `Z`.
* `BS23.ColinearSoS.lineMom_zero`, `BS23.ColinearSoS.lineMom_one`: `M_0 = M_2 = 1`.
* **Log-convexity** `BS23.ColinearSoS.lineMom_sq_le`: `M_{2l+2}² ≤ M_{2l} M_{2l+4}`, since the
  quadratic form `x ↦ E (x X^l + X^(l+2))²` of the mixture `X` is nonnegative. Hence
  `M_{2l}^s ≤ M_{2s}^l` for `l ≤ s` (`BS23.ColinearSoS.lineMom_pow_le`) and `M_{2l} ≥ 1`
  (`BS23.ColinearSoS.one_le_lineMom`).
* `BS23.ColinearSoS.mul_pow_le_lineMom`: `wmin a_c^(2l) ≤ M_{2l}`.
* **Stein bounds** `BS23.ColinearSoS.hmom_two_mul_le`:
  `hmom (2j) a v ≤ (a² + (4j-3) v) hmom (2j-2) a v`, from the recurrence
  `hmom (m+2) = a hmom (m+1) + (m+1) v hmom m`; so
  `M_{2j} ≤ (A² + (4j-3) σ²) M_{2j-2}` when all `a_c² ≤ A²`
  (`BS23.ColinearSoS.lineMom_succ_le`).
* **Lemma U** `BS23.ColinearSoS.nbeta_mul_two_pow_le`: if `M_{2s} ≥ (4s)^s`, then
  `β_l 2^(s-l) ≤ β_s` for `l ≤ s` (order `2s`). Indeed `β_l ≤ (2s)^(s-l) M_{2l}` and
  `M_{2l} ≤ M_{2s}^(l/s) ≤ M_{2s} / (4s)^(s-l)`. In the same way, if `M_{2s} ≤ X^s` with
  `X ≥ 2s`, then all `β_l ≤ X^s` (`BS23.ColinearSoS.nbeta_le_of_lineMom_le`).
* **Lemma L** `BS23.ColinearSoS.two_mul_nbeta_le`: if all `a_c² ≤ A²`, `σ² ≤ 1/16` and
  `t ≥ 5A² + 8`, then `2 β_t ≤ β_l` for `l < t` (order `2t`). With `r_j = M_{2j} / (2j-1)‼`,
  the Stein bound gives `r_{j+1} ≤ (A²/(2j+1) + 1/8) r_j`: for `j ≥ J = ⌈2A²⌉` this is
  `r_{j+1} ≤ (3/8) r_j`, and for `j < J` it is `(j+1) r_{j+1} ≤ J r_j`, so `r_J ≤ (J^J/J!) r_l
  ≤ 3^J r_l`. Then `r_t ≤ (3/8)^(t-J) 3^J r_l ≤ r_l / 2`.
-/

@[expose] public section

namespace BS23.ColinearSoS

open Finset MeasureTheory ProbabilityTheory
open scoped Nat

/-! ### One Gaussian -/

namespace Ratio

/-- The terms of `hmom (2l) a v` are nonnegative for `v ≥ 0`. -/
theorem hmom_term_nonneg {v : ℝ} (hv : 0 ≤ v) (a : ℝ) (l i : ℕ) :
    0 ≤ (hermCoeff (2 * l) i : ℝ) * a ^ (2 * l - 2 * i) * v ^ i :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Even.pow_nonneg ⟨l - i, by omega⟩ _))
    (pow_nonneg hv _)

/-- `hmom (2l) a v ≥ 0` for `v ≥ 0`. -/
theorem hmom_two_mul_nonneg {v : ℝ} (hv : 0 ≤ v) (a : ℝ) (l : ℕ) : 0 ≤ hmom (2 * l) a v :=
  Finset.sum_nonneg fun i _ ↦ hmom_term_nonneg hv a l i

/-- `(a + b z)^r` as a polynomial in `z`. -/
theorem affine_pow_eq (r : ℕ) (a b : ℝ) :
    (fun z : ℝ ↦ (a + b * z) ^ r) =
      fun z ↦ ∑ p ∈ range (r + 1), ((r.choose p : ℝ) * a ^ (r - p) * b ^ p) * z ^ p := by
  funext z
  rw [add_comm, add_pow]
  refine sum_congr rfl fun p _ ↦ ?_
  ring

/-- `(a + b z)^r` is integrable for the standard Gaussian. -/
theorem integrable_affine_pow (r : ℕ) (a b : ℝ) :
    Integrable (fun z : ℝ ↦ (a + b * z) ^ r) (gaussianReal 0 1) := by
  rw [affine_pow_eq]
  exact integrable_finsetSum _ fun p _ ↦ (integrable_pow_gaussianReal p).const_mul _

/-- `E (a + b Z)^r = ∑_p C(r, p) a^(r-p) E Z^p b^p` for a standard Gaussian `Z`. -/
theorem integral_affine_pow (r : ℕ) (a b : ℝ) :
    ∫ z, (a + b * z) ^ r ∂(gaussianReal 0 1) =
      ∑ p ∈ range (r + 1), (r.choose p : ℝ) * a ^ (r - p) * (gaussMom p : ℝ) * b ^ p := by
  rw [affine_pow_eq, integral_finsetSum _ fun p _ ↦ (integrable_pow_gaussianReal p).const_mul _]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [integral_const_mul, integral_pow_gaussianReal]
  ring

end Ratio

/-- The moments of a Gaussian of mean `a` and variance `v ≥ 0`:
`hmom r a v = E (a + √v Z)^r` for a standard Gaussian `Z`. -/
theorem hmom_eq_integral (r : ℕ) (a v : ℝ) (hv : 0 ≤ v) :
    hmom r a v = ∫ z, (a + Real.sqrt v * z) ^ r ∂(gaussianReal 0 1) := by
  rw [hmom_eq_sum_gaussMom r a hv, Ratio.integral_affine_pow]

namespace Ratio

/-- The quadratic form `x ↦ E (x f^l + f^(l+2))²`, `f = a + √v Z`, is nonnegative. -/
theorem quad_hmom_nonneg {v : ℝ} (hv : 0 ≤ v) (a : ℝ) (l : ℕ) (x : ℝ) :
    0 ≤ hmom (2 * l) a v * (x * x) + 2 * hmom (2 * (l + 1)) a v * x +
      hmom (2 * (l + 2)) a v := by
  have hint := fun r ↦ integrable_affine_pow r a (Real.sqrt v)
  have e : ∀ z : ℝ, (x * (a + Real.sqrt v * z) ^ l + (a + Real.sqrt v * z) ^ (l + 2)) ^ 2 =
      (x * x) * (a + Real.sqrt v * z) ^ (2 * l) +
        (2 * x) * (a + Real.sqrt v * z) ^ (2 * (l + 1)) +
        (a + Real.sqrt v * z) ^ (2 * (l + 2)) := fun z ↦ by ring
  have h0 : 0 ≤ ∫ z, (x * (a + Real.sqrt v * z) ^ l + (a + Real.sqrt v * z) ^ (l + 2)) ^ 2
      ∂(gaussianReal 0 1) := integral_nonneg fun z ↦ sq_nonneg _
  simp_rw [e] at h0
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul,
    ← hmom_eq_integral _ _ _ hv, ← hmom_eq_integral _ _ _ hv, ← hmom_eq_integral _ _ _ hv] at h0
  · linarith
  · exact (hint _).const_mul _
  · exact (hint _).const_mul _
  · exact ((hint _).const_mul _).add ((hint _).const_mul _)
  · exact hint _

end Ratio

variable {k : ℕ} {w a : Fin k → ℝ} {σ2 : ℝ}

/-! ### Basic values and log-convexity -/

/-- `M_0 = 1`. -/
theorem lineMom_zero (hw1 : ∑ c, w c = 1) : lineMom w a σ2 0 = 1 := by
  simp [lineMom, hw1]

/-- `M_2 = ∑_c w_c a_c² + σ² = 1`. -/
theorem lineMom_one (hw1 : ∑ c, w c = 1) (hvar : ∑ c, w c * a c ^ 2 + σ2 = 1) :
    lineMom w a σ2 1 = 1 := by
  simp only [lineMom, mul_one, hmom_two, mul_add, sum_add_distrib, ← sum_mul, hw1, one_mul]
  exact hvar

/-- `M_{2l} ≥ 0`. -/
theorem lineMom_nonneg (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) (l : ℕ) : 0 ≤ lineMom w a σ2 l :=
  Finset.sum_nonneg fun c _ ↦ mul_nonneg (hw c) (Ratio.hmom_two_mul_nonneg hσ _ _)

/-- The quadratic form `x ↦ M_{2l} x² + 2 M_{2l+2} x + M_{2l+4}` is nonnegative. -/
theorem Ratio.lineMom_quad_nonneg (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) (l : ℕ) (x : ℝ) :
    0 ≤ lineMom w a σ2 l * (x * x) + 2 * lineMom w a σ2 (l + 1) * x + lineMom w a σ2 (l + 2) := by
  have e : lineMom w a σ2 l * (x * x) + 2 * lineMom w a σ2 (l + 1) * x + lineMom w a σ2 (l + 2) =
      ∑ c, w c * (hmom (2 * l) (a c) σ2 * (x * x) + 2 * hmom (2 * (l + 1)) (a c) σ2 * x +
        hmom (2 * (l + 2)) (a c) σ2) := by
    simp only [lineMom, sum_mul, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun c _ ↦ ?_
    ring
  rw [e]
  exact Finset.sum_nonneg fun c _ ↦ mul_nonneg (hw c) (Ratio.quad_hmom_nonneg hσ _ _ _)

/-- **Log-convexity** `M_{2l+2}² ≤ M_{2l} M_{2l+4}` (Cauchy–Schwarz). -/
theorem lineMom_sq_le (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) (l : ℕ) :
    lineMom w a σ2 (l + 1) ^ 2 ≤ lineMom w a σ2 l * lineMom w a σ2 (l + 2) := by
  have h := discrim_le_zero (Ratio.lineMom_quad_nonneg hw hσ l (a := a))
  rw [discrim] at h
  linarith

/-- **Lyapunov**: `M_{2l}^s ≤ M_{2s}^l` for `l ≤ s`. -/
theorem lineMom_pow_le (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (hσ : 0 ≤ σ2) {l s : ℕ}
    (hls : l ≤ s) : lineMom w a σ2 l ^ s ≤ lineMom w a σ2 s ^ l :=
  SoS.pow_le_pow_of_sq_le_mul_of_le (a := lineMom w a σ2) (t := s) (lineMom_zero hw1)
    (fun r _ ↦ lineMom_nonneg hw hσ r)
    (fun r hr _ ↦ by
      have h := lineMom_sq_le hw hσ (a := a) (r - 1)
      rwa [show r - 1 + 1 = r by omega, show r - 1 + 2 = r + 1 by omega] at h) hls le_rfl

/-- `M_{2l} ≥ 1`. -/
theorem one_le_lineMom (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (hσ : 0 ≤ σ2)
    (hvar : ∑ c, w c * a c ^ 2 + σ2 = 1) (l : ℕ) : 1 ≤ lineMom w a σ2 l := by
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · rw [lineMom_zero hw1]
  · have h := lineMom_pow_le hw hw1 hσ (a := a) (show 1 ≤ l from hl)
    rwa [lineMom_one hw1 hvar, one_pow, pow_one] at h

/-! ### Lower bounds by the means -/

/-- `a^(2l) ≤ hmom (2l) a v` for `v ≥ 0`. -/
theorem pow_le_hmom {a v : ℝ} (hv : 0 ≤ v) (l : ℕ) : a ^ (2 * l) ≤ hmom (2 * l) a v := by
  have h := Finset.single_le_sum (f := fun i ↦ (hermCoeff (2 * l) i : ℝ) * a ^ (2 * l - 2 * i) *
    v ^ i) (fun i _ ↦ Ratio.hmom_term_nonneg hv a l i) (mem_range.2 (Nat.succ_pos (2 * l / 2)))
  simpa [hmom] using h

/-- `wmin a_c^(2l) ≤ M_{2l}` when all weights are at least `wmin ≥ 0`. -/
theorem mul_pow_le_lineMom {wmin : ℝ} (hwm : ∀ c, wmin ≤ w c) (hw0 : 0 ≤ wmin) (hσ : 0 ≤ σ2)
    (c : Fin k) (l : ℕ) : wmin * a c ^ (2 * l) ≤ lineMom w a σ2 l := by
  have hw : ∀ c, 0 ≤ w c := fun c ↦ hw0.trans (hwm c)
  calc wmin * a c ^ (2 * l) ≤ w c * a c ^ (2 * l) :=
        mul_le_mul_of_nonneg_right (hwm c) (Even.pow_nonneg ⟨l, by ring⟩ _)
    _ ≤ w c * hmom (2 * l) (a c) σ2 := mul_le_mul_of_nonneg_left (pow_le_hmom hσ l) (hw c)
    _ ≤ lineMom w a σ2 l :=
        Finset.single_le_sum (f := fun c ↦ w c * hmom (2 * l) (a c) σ2)
          (fun c _ ↦ mul_nonneg (hw c) (Ratio.hmom_two_mul_nonneg hσ _ _)) (mem_univ c)

/-! ### The Stein bounds -/

/-- `a hmom (2i+1) a v ≤ hmom (2i+2) a v` for `v ≥ 0`. -/
theorem Ratio.mul_hmom_odd_le {v : ℝ} (hv : 0 ≤ v) (a : ℝ) (i : ℕ) :
    a * hmom (2 * i + 1) a v ≤ hmom (2 * i + 2) a v := by
  have e := hmom_succ_succ (2 * i) a v
  have h0 : 0 ≤ (((2 * i : ℕ) : ℝ) + 1) * v * hmom (2 * i) a v :=
    mul_nonneg (mul_nonneg (by positivity) hv) (Ratio.hmom_two_mul_nonneg hv a i)
  linarith

/-- **Stein bound** `hmom (2j) a v ≤ (a² + (4j-3) v) hmom (2j-2) a v` for `j ≥ 1`, `v ≥ 0`. -/
theorem hmom_two_mul_le {a v : ℝ} (j : ℕ) (hj : 1 ≤ j) (hv : 0 ≤ v) :
    hmom (2 * j) a v ≤ (a ^ 2 + (4 * j - 3) * v) * hmom (2 * j - 2) a v := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rcases i with _ | i
  · norm_num [hmom_two]
  · rw [show 2 * (i + 1 + 1) = 2 * i + 2 + 2 by ring, show 2 * i + 2 + 2 - 2 = 2 * i + 2 by omega]
    have e4 := hmom_succ_succ (2 * i + 2) a v
    have e3 := hmom_succ_succ (2 * i + 1) a v
    rw [show 2 * i + 1 + 2 = 2 * i + 2 + 1 by ring, show 2 * i + 1 + 1 = 2 * i + 2 by ring] at e3
    have key := mul_le_mul_of_nonneg_left (Ratio.mul_hmom_odd_le hv a i)
      (show 0 ≤ (((2 * i + 1 : ℕ) : ℝ) + 1) * v by positivity)
    rw [e4, e3]
    push_cast at key ⊢
    nlinarith [key]

/-- `M_{2j} ≤ (A² + (4j-3) σ²) M_{2j-2}` for `j ≥ 1` when all `a_c² ≤ A²`. -/
theorem lineMom_succ_le (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {A2 : ℝ} (hA : ∀ c, a c ^ 2 ≤ A2)
    (j : ℕ) (hj : 1 ≤ j) :
    lineMom w a σ2 j ≤ (A2 + (4 * j - 3) * σ2) * lineMom w a σ2 (j - 1) := by
  rw [lineMom, lineMom, mul_sum]
  refine sum_le_sum fun c _ ↦ ?_
  rw [show 2 * (j - 1) = 2 * j - 2 by omega]
  have h2 : 0 ≤ hmom (2 * j - 2) (a c) σ2 := by
    rw [show 2 * j - 2 = 2 * (j - 1) by omega]
    exact Ratio.hmom_two_mul_nonneg hσ _ _
  have h3 : (a c ^ 2 + (4 * j - 3) * σ2) * hmom (2 * j - 2) (a c) σ2 ≤
      (A2 + (4 * j - 3) * σ2) * hmom (2 * j - 2) (a c) σ2 :=
    mul_le_mul_of_nonneg_right (by linarith [hA c]) h2
  calc w c * hmom (2 * j) (a c) σ2
      ≤ w c * ((A2 + (4 * j - 3) * σ2) * hmom (2 * j - 2) (a c) σ2) :=
        mul_le_mul_of_nonneg_left ((hmom_two_mul_le j hj hσ).trans h3) (hw c)
    _ = (A2 + (4 * j - 3) * σ2) * (w c * hmom (2 * j - 2) (a c) σ2) := by ring

/-! ### Comparing the normalized coefficients: the upper program -/

namespace Ratio

/-- `β_m = M_{2m}`. -/
private theorem nbeta_self (w a : Fin k → ℝ) (σ2 : ℝ) (m : ℕ) :
    nbeta w a σ2 m m = lineMom w a σ2 m := by
  rw [nbeta, mul_div_cancel_left₀ _ (Nat.cast_pos.2 (Nat.doubleFactorial_pos _)).ne']

/-- `(2s-1)‼ ≤ (2s)^(s-l) (2l-1)‼` for `l ≤ s`. -/
theorem doubleFactorial_le {l s : ℕ} (h : l ≤ s) :
    (2 * s - 1)‼ ≤ (2 * s) ^ (s - l) * (2 * l - 1)‼ := by
  induction s, h using Nat.le_induction with
  | base => simp
  | succ s hls ih =>
    rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega, Nat.doubleFactorial_add_one,
      show s + 1 - l = s - l + 1 by omega]
    calc (2 * s + 1) * (2 * s - 1)‼ ≤ (2 * (s + 1)) * ((2 * s) ^ (s - l) * (2 * l - 1)‼) :=
          Nat.mul_le_mul (by omega) ih
      _ ≤ (2 * (s + 1)) * ((2 * (s + 1)) ^ (s - l) * (2 * l - 1)‼) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _))
      _ = (2 * (s + 1)) ^ (s - l + 1) * (2 * l - 1)‼ := by ring

/-- `β_l ≤ (2s)^(s-l) M_{2l}` for the coefficients of order `2s`, `l ≤ s`. -/
theorem nbeta_le_mul (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {l s : ℕ} (h : l ≤ s) :
    nbeta w a σ2 s l ≤ (2 * s : ℝ) ^ (s - l) * lineMom w a σ2 l := by
  have hD : ((2 * s - 1)‼ : ℝ) ≤ (2 * s : ℝ) ^ (s - l) * ((2 * l - 1)‼ : ℝ) := by
    exact_mod_cast doubleFactorial_le h
  rw [nbeta, div_le_iff₀ (Nat.cast_pos.2 (Nat.doubleFactorial_pos _))]
  calc ((2 * s - 1)‼ : ℝ) * lineMom w a σ2 l
      ≤ (2 * s : ℝ) ^ (s - l) * ((2 * l - 1)‼ : ℝ) * lineMom w a σ2 l :=
        mul_le_mul_of_nonneg_right hD (lineMom_nonneg hw hσ l)
    _ = _ := by ring

/-- If `x^s ≤ y^l`, `l ≤ s ≠ 0`, and `X^s ≤ y`, then `X^(s-l) x ≤ y`. -/
theorem pow_sub_mul_le {x y X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) {l s : ℕ} (hls : l ≤ s)
    (hs : s ≠ 0) (h1 : x ^ s ≤ y ^ l) (h2 : X ^ s ≤ y) : X ^ (s - l) * x ≤ y := by
  have hy : 0 ≤ y := (pow_nonneg hX s).trans h2
  refine (pow_le_pow_iff_left₀ (mul_nonneg (pow_nonneg hX _) hx) hy hs).1 ?_
  calc (X ^ (s - l) * x) ^ s = (X ^ s) ^ (s - l) * x ^ s := by ring
    _ ≤ y ^ (s - l) * y ^ l :=
        mul_le_mul (pow_le_pow_left₀ (pow_nonneg hX _) h2 _) h1 (pow_nonneg hx _)
          (pow_nonneg hy _)
    _ = y ^ s := by rw [← pow_add, Nat.sub_add_cancel hls]

/-- If `x^s ≤ y^l`, `s ≠ 0` and `0 ≤ y ≤ X^s`, then `x ≤ X^l`. -/
theorem le_pow_of_pow_le {x y X : ℝ} (hx : 0 ≤ x) (hX : 0 ≤ X) {l s : ℕ} (hs : s ≠ 0)
    (h1 : x ^ s ≤ y ^ l) (hy : 0 ≤ y) (h2 : y ≤ X ^ s) : x ≤ X ^ l := by
  refine (pow_le_pow_iff_left₀ hx (pow_nonneg hX _) hs).1 ?_
  calc x ^ s ≤ y ^ l := h1
    _ ≤ (X ^ s) ^ l := pow_le_pow_left₀ hy h2 _
    _ = (X ^ l) ^ s := by ring

end Ratio

/-- **Lemma U**: if `M_{2s} ≥ (4s)^s`, `s ≥ 1`, then the normalized coefficients of order `2s`
decay geometrically away from the top: `β_l 2^(s-l) ≤ β_s` for `l ≤ s`. -/
theorem nbeta_mul_two_pow_le (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (hσ : 0 ≤ σ2) {s : ℕ}
    (hs : 1 ≤ s) (hM : (4 * s : ℝ) ^ s ≤ lineMom w a σ2 s) :
    ∀ l ≤ s, nbeta w a σ2 s l * 2 ^ (s - l) ≤ nbeta w a σ2 s s := by
  intro l hl
  rw [Ratio.nbeta_self]
  have h2 := Ratio.pow_sub_mul_le (lineMom_nonneg hw hσ l) (by positivity : (0 : ℝ) ≤ 4 * s) hl
    (by omega) (lineMom_pow_le hw hw1 hσ hl) hM
  calc nbeta w a σ2 s l * 2 ^ (s - l)
      ≤ (2 * s : ℝ) ^ (s - l) * lineMom w a σ2 l * 2 ^ (s - l) :=
        mul_le_mul_of_nonneg_right (Ratio.nbeta_le_mul hw hσ hl) (by positivity)
    _ = (4 * s : ℝ) ^ (s - l) * lineMom w a σ2 l := by
        rw [show (4 * s : ℝ) = 2 * s * 2 by ring, mul_pow (2 * (s : ℝ)) 2]
        ring
    _ ≤ _ := h2

/-- **(T1)**: if `M_{2s} ≤ X^s` with `X ≥ 2s`, then all normalized coefficients of order `2s` are
at most `X^s`. -/
theorem nbeta_le_of_lineMom_le (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1) (hσ : 0 ≤ σ2) {s : ℕ}
    {X : ℝ} (hX : 2 * s ≤ X) (hM : lineMom w a σ2 s ≤ X ^ s) :
    ∀ l ≤ s, nbeta w a σ2 s l ≤ X ^ s := by
  intro l hl
  have hX0 : 0 ≤ X := le_trans (by positivity) hX
  have hMl : lineMom w a σ2 l ≤ X ^ l := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · obtain rfl : l = 0 := by omega
      exact hM
    · exact Ratio.le_pow_of_pow_le (lineMom_nonneg hw hσ l) hX0 hs.ne'
        (lineMom_pow_le hw hw1 hσ hl) (lineMom_nonneg hw hσ s) hM
  calc nbeta w a σ2 s l ≤ (2 * s : ℝ) ^ (s - l) * lineMom w a σ2 l := Ratio.nbeta_le_mul hw hσ hl
    _ ≤ X ^ (s - l) * X ^ l :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hX _) hMl (lineMom_nonneg hw hσ l)
          (pow_nonneg hX0 _)
    _ = X ^ s := by rw [← pow_add, Nat.sub_add_cancel hl]

/-! ### Comparing the normalized coefficients: the lower program -/

namespace Ratio

/-- The ratio `r_j = M_{2j} / (2j-1)‼`, so that `β_l = (2m-1)‼ r_l`. -/
noncomputable def normMom (w a : Fin k → ℝ) (σ2 : ℝ) (j : ℕ) : ℝ :=
  lineMom w a σ2 j / ((2 * j - 1)‼ : ℝ)

/-- `r_j ≥ 0`. -/
theorem normMom_nonneg (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) (j : ℕ) : 0 ≤ normMom w a σ2 j :=
  div_nonneg (lineMom_nonneg hw hσ j) (Nat.cast_nonneg _)

/-- `β_l = (2m-1)‼ r_l`. -/
theorem nbeta_eq_mul_normMom (w a : Fin k → ℝ) (σ2 : ℝ) (m l : ℕ) :
    nbeta w a σ2 m l = ((2 * m - 1)‼ : ℝ) * normMom w a σ2 l := by
  rw [nbeta, normMom, mul_div_assoc]

/-- `(2i+1)‼ = (2i+1) (2i-1)‼`, over the reals. -/
theorem doubleFactorial_succ_cast (i : ℕ) :
    ((2 * (i + 1) - 1)‼ : ℝ) = (2 * i + 1) * ((2 * i - 1)‼ : ℝ) := by
  rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, Nat.doubleFactorial_add_one]
  push_cast
  ring

/-- The Stein bound with `σ² ≤ 1/16`: `M_{2i+2} ≤ (A² + (4i+1)/16) M_{2i}`. -/
theorem lineMom_succ_le' (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {A2 : ℝ} (hA : ∀ c, a c ^ 2 ≤ A2)
    (hσ16 : σ2 ≤ 1 / 16) (i : ℕ) :
    lineMom w a σ2 (i + 1) ≤ (A2 + (4 * i + 1) / 16) * lineMom w a σ2 i := by
  have h := lineMom_succ_le hw hσ hA (i + 1) (by omega)
  rw [Nat.add_sub_cancel] at h
  have h1 : (4 * ((i + 1 : ℕ) : ℝ) - 3) * σ2 ≤ (4 * i + 1) / 16 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ i by positivity]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (lineMom_nonneg hw hσ i))

/-- Past `2A²`, the ratios decay: `r_{i+1} ≤ (3/8) r_i` for `i ≥ 2A²`. -/
theorem normMom_succ_le (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {A2 : ℝ} (hA : ∀ c, a c ^ 2 ≤ A2)
    (hσ16 : σ2 ≤ 1 / 16) {i : ℕ} (hi : 2 * A2 ≤ i) :
    normMom w a σ2 (i + 1) ≤ 3 / 8 * normMom w a σ2 i := by
  have hD : (0 : ℝ) < ((2 * i - 1)‼ : ℝ) := Nat.cast_pos.2 (Nat.doubleFactorial_pos _)
  have h := lineMom_succ_le' hw hσ hA hσ16 i
  have h1 : lineMom w a σ2 (i + 1) ≤ 3 / 8 * (2 * i + 1) * lineMom w a σ2 i :=
    h.trans (mul_le_mul_of_nonneg_right (by linarith) (lineMom_nonneg hw hσ i))
  rw [normMom, normMom, doubleFactorial_succ_cast, div_le_iff₀ (by positivity)]
  calc lineMom w a σ2 (i + 1) ≤ 3 / 8 * (2 * i + 1) * lineMom w a σ2 i := h1
    _ = _ := by field_simp

/-- Before `J ≥ 2A²`, the ratios grow at most like `J^i / i!`: `(i+1) r_{i+1} ≤ J r_i` for
`i < J`. -/
theorem succ_mul_normMom_le (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {A2 : ℝ}
    (hA : ∀ c, a c ^ 2 ≤ A2) (hσ16 : σ2 ≤ 1 / 16) {J i : ℕ} (hJ : 2 * A2 ≤ J) (hi : i < J) :
    ((i : ℝ) + 1) * normMom w a σ2 (i + 1) ≤ J * normMom w a σ2 i := by
  have hD : (0 : ℝ) < ((2 * i - 1)‼ : ℝ) := Nat.cast_pos.2 (Nat.doubleFactorial_pos _)
  have hM := lineMom_nonneg hw hσ (a := a) i
  have hiJ : (i : ℝ) + 1 ≤ J := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have e1 : ((i : ℝ) + 1) * A2 ≤ ((i : ℝ) + 1) * (J / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have e2 : ((i : ℝ) + 1) * (4 * i + 1) ≤ J * (4 * i + 1) :=
    mul_le_mul_of_nonneg_right hiJ (by positivity)
  have e3 : (0 : ℝ) ≤ J * i := by positivity
  have hc : ((i : ℝ) + 1) * (A2 + (4 * i + 1) / 16) ≤ J * (2 * i + 1) := by nlinarith
  have h1 : ((i : ℝ) + 1) * lineMom w a σ2 (i + 1) ≤ J * (2 * i + 1) * lineMom w a σ2 i := by
    calc ((i : ℝ) + 1) * lineMom w a σ2 (i + 1)
        ≤ ((i : ℝ) + 1) * ((A2 + (4 * i + 1) / 16) * lineMom w a σ2 i) :=
          mul_le_mul_of_nonneg_left (lineMom_succ_le' hw hσ hA hσ16 i) (by positivity)
      _ = ((i : ℝ) + 1) * (A2 + (4 * i + 1) / 16) * lineMom w a σ2 i := by ring
      _ ≤ J * (2 * i + 1) * lineMom w a σ2 i := mul_le_mul_of_nonneg_right hc hM
  rw [normMom, normMom, doubleFactorial_succ_cast, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff₀ (by positivity) hD]
  calc ((i : ℝ) + 1) * lineMom w a σ2 (i + 1) * ((2 * i - 1)‼ : ℝ)
      ≤ J * (2 * i + 1) * lineMom w a σ2 i * ((2 * i - 1)‼ : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hD.le
    _ = _ := by ring

/-- Geometric decay: if `r_{i+1} ≤ ρ r_i` for `i ≥ l`, then `r_{l+n} ≤ ρ^n r_l`. -/
theorem le_geom {r : ℕ → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) {l : ℕ}
    (h : ∀ i, l ≤ i → r (i + 1) ≤ ρ * r i) (n : ℕ) : r (l + n) ≤ ρ ^ n * r l := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc r (l + (n + 1)) = r (l + n + 1) := by rw [Nat.add_assoc]
      _ ≤ ρ * r (l + n) := h _ (by omega)
      _ ≤ ρ * (ρ ^ n * r l) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (n + 1) * r l := by ring

/-- Factorial growth: if `r ≥ 0` and `(i+1) r_{i+1} ≤ J r_i` for `i < J`, then
`r_J J! ≤ J^J r_l` for `l ≤ J`. -/
theorem mul_factorial_le {r : ℕ → ℝ} (hr : ∀ i, 0 ≤ r i) {J : ℕ}
    (h : ∀ i, i < J → ((i : ℝ) + 1) * r (i + 1) ≤ J * r i) {l : ℕ} (hl : l ≤ J) :
    r J * (J ! : ℝ) ≤ (J : ℝ) ^ J * r l := by
  have key : ∀ n, l + n ≤ J → r (l + n) * ((l + n)! : ℝ) ≤ (J : ℝ) ^ n * (l ! : ℝ) * r l := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [Nat.add_zero, pow_zero, one_mul, mul_comm]
    | succ n ih =>
      intro hn
      have ih := ih (by omega)
      have hs := h (l + n) (by omega)
      calc r (l + (n + 1)) * ((l + (n + 1))! : ℝ)
          = (((l + n : ℕ) : ℝ) + 1) * r (l + n + 1) * ((l + n)! : ℝ) := by
            rw [show l + (n + 1) = l + n + 1 by ring, Nat.factorial_succ]
            push_cast
            ring
        _ ≤ J * r (l + n) * ((l + n)! : ℝ) := mul_le_mul_of_nonneg_right hs (by positivity)
        _ ≤ J * ((J : ℝ) ^ n * (l ! : ℝ) * r l) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (J : ℝ) ^ (n + 1) * (l ! : ℝ) * r l := by ring
  have h1 := key (J - l) (by omega)
  rw [Nat.add_sub_cancel' hl] at h1
  have h2 : (l ! : ℝ) ≤ (J : ℝ) ^ l := by
    exact_mod_cast (Nat.factorial_le_pow l).trans (Nat.pow_le_pow_left hl l)
  calc r J * (J ! : ℝ) ≤ (J : ℝ) ^ (J - l) * (l ! : ℝ) * r l := h1
    _ ≤ (J : ℝ) ^ (J - l) * (J : ℝ) ^ l * r l :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) (hr l)
    _ = (J : ℝ) ^ J * r l := by rw [← pow_add, Nat.sub_add_cancel hl]

/-- `J^J / J! ≤ e^J ≤ 3^J`. -/
theorem pow_self_le (J : ℕ) : (J : ℝ) ^ J ≤ 3 ^ J * (J ! : ℝ) := by
  have h := Real.pow_div_factorial_le_exp (J : ℝ) (Nat.cast_nonneg J) J
  rw [div_le_iff₀ (by positivity), ← Real.exp_one_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le J) (by positivity))

/-- `(3/8)^n 3^J ≤ 1/2` when `2n ≥ 3J + 12`. -/
theorem geom_mul_pow_le {n J : ℕ} (h : 3 * J + 12 ≤ 2 * n) :
    (3 / 8 : ℝ) ^ n * 3 ^ J ≤ 1 / 2 := by
  refine (pow_le_pow_iff_left₀ (by positivity) (by norm_num) two_ne_zero).1 ?_
  calc ((3 / 8 : ℝ) ^ n * 3 ^ J) ^ 2 = (3 / 8 : ℝ) ^ (2 * n) * (3 ^ 2) ^ J := by
        rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n 2, mul_comm J 2]
    _ ≤ (3 / 8 : ℝ) ^ (3 * J + 12) * (3 ^ 2) ^ J :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) h)
          (by positivity)
    _ = ((3 / 8 : ℝ) ^ 3 * 3 ^ 2) ^ J * (3 / 8) ^ 12 := by
        rw [pow_add, pow_mul, mul_pow]
        ring
    _ ≤ 1 * (3 / 8 : ℝ) ^ 12 :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by positivity)
    _ ≤ (1 / 2) ^ 2 := by norm_num

/-- The two-phase estimate behind Lemma L, for the ratios `r_j`: `2 r_t ≤ r_l` for `l < t`. -/
theorem two_mul_normMom_le (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {A2 : ℝ}
    (hA : ∀ c, a c ^ 2 ≤ A2) (hA0 : 0 ≤ A2) (hσ16 : σ2 ≤ 1 / 16) {t : ℕ}
    (ht : 5 * A2 + 8 ≤ t) {l : ℕ} (hl : l < t) :
    2 * normMom w a σ2 t ≤ normMom w a σ2 l := by
  set J := ⌈2 * A2⌉₊
  have hJ1 : 2 * A2 ≤ J := Nat.le_ceil _
  have hJ2 : (J : ℝ) < 2 * A2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hr := normMom_nonneg hw hσ (a := a)
  have hdec : ∀ i, J ≤ i → normMom w a σ2 (i + 1) ≤ 3 / 8 * normMom w a σ2 i := fun i hi ↦
    normMom_succ_le hw hσ hA hσ16 (hJ1.trans (by exact_mod_cast hi))
  rcases le_or_gt J l with hJl | hlJ
  · have h1 := le_geom (by norm_num) (fun i hi ↦ hdec i (hJl.trans hi)) (t - l)
    rw [Nat.add_sub_cancel' hl.le] at h1
    have h2 : (3 / 8 : ℝ) ^ (t - l) ≤ 3 / 8 := by
      simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 3 / 8) (by norm_num)
        (show 1 ≤ t - l by omega)
    nlinarith [hr l, hr t]
  · have hJt : J < t := by exact_mod_cast (show (J : ℝ) < t by linarith)
    have hn : 3 * J + 12 ≤ 2 * (t - J) := by
      have : (5 * J + 11 : ℝ) < 2 * t := by linarith
      have : 5 * J + 11 < 2 * t := by exact_mod_cast this
      omega
    have h1 := le_geom (by norm_num) hdec (t - J)
    rw [Nat.add_sub_cancel' hJt.le] at h1
    have h2 := mul_factorial_le hr (fun i hi ↦ succ_mul_normMom_le hw hσ hA hσ16 hJ1 hi) hlJ.le
    have h3 : normMom w a σ2 J ≤ 3 ^ J * normMom w a σ2 l := by
      have hf : (0 : ℝ) < (J ! : ℝ) := by positivity
      refine le_of_mul_le_mul_right ?_ hf
      calc normMom w a σ2 J * (J ! : ℝ) ≤ (J : ℝ) ^ J * normMom w a σ2 l := h2
        _ ≤ 3 ^ J * (J ! : ℝ) * normMom w a σ2 l :=
            mul_le_mul_of_nonneg_right (pow_self_le J) (hr l)
        _ = 3 ^ J * normMom w a σ2 l * (J ! : ℝ) := by ring
    have h4 := geom_mul_pow_le hn
    calc 2 * normMom w a σ2 t ≤ 2 * ((3 / 8 : ℝ) ^ (t - J) * normMom w a σ2 J) := by linarith
      _ ≤ 2 * ((3 / 8 : ℝ) ^ (t - J) * (3 ^ J * normMom w a σ2 l)) := by gcongr
      _ = 2 * ((3 / 8 : ℝ) ^ (t - J) * 3 ^ J) * normMom w a σ2 l := by ring
      _ ≤ 2 * (1 / 2) * normMom w a σ2 l := by gcongr; exact hr l
      _ = normMom w a σ2 l := by ring

end Ratio

/-- **Lemma L**: if all `a_c² ≤ A²`, `σ² ≤ 1/16` and `t ≥ 5A² + 8`, then the top normalized
coefficient of order `2t` is at most half of every other one: `2 β_t ≤ β_l` for `l < t`. -/
theorem two_mul_nbeta_le (hw : ∀ c, 0 ≤ w c) (hσ : 0 ≤ σ2) {A2 : ℝ} (hA : ∀ c, a c ^ 2 ≤ A2)
    (hA0 : 0 ≤ A2) (hσ16 : σ2 ≤ 1 / 16) {t : ℕ} (ht : 5 * A2 + 8 ≤ t) :
    ∀ l < t, 2 * nbeta w a σ2 t t ≤ nbeta w a σ2 t l := by
  intro l hl
  have h := Ratio.two_mul_normMom_le hw hσ hA hA0 hσ16 ht hl
  rw [Ratio.nbeta_eq_mul_normMom, Ratio.nbeta_eq_mul_normMom]
  have hD : (0 : ℝ) ≤ ((2 * t - 1)‼ : ℝ) := Nat.cast_nonneg _
  nlinarith

end BS23.ColinearSoS
