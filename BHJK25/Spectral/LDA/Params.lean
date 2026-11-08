module

public import BHJK25.Model
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The parameters of Theorem 3.1

The real-number bookkeeping that turns the advantage bound for general parameters into the
bound of [BHJK25, Theorem 3.1]. With `N = n`, `L = log n`, `γ = C L²/N`, `λ* = γ L` and
`D = N^(1/3)/L^(b+1)`, for all large `n`:

* `0 < γ ≤ 1/2`, so that `γ = min(1, C L²/N)` (`BHJK25.sparsity`);
* `λ* · 2 D (D + 1) ≤ 4 C L³/N^(1/3) ≤ 1`;
* `(1/√(1 - γ) + 10 D³ λ*/√γ)/√N ≤ √2/√N + 10 √C/L^(3b+1) ≤ 1/L^b`.

The asymptotic inputs are `log^k n = o(n^s)` for `s > 0` and `log n → ∞`.
-/

@[expose] public section

namespace BHJK25.Spectral.LDAAux

open Filter

/-- `log^k n ≤ c n^s` for all large `n`, for `s > 0` and `c > 0`. -/
theorem eventually_log_pow_le (k : ℕ) {s c : ℝ} (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ k ≤ c * (n : ℝ) ^ s := by
  have h := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).bound hc)
  filter_upwards [h] with n hn
  rw [Real.rpow_natCast, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ s)] at hn
  exact (Real.le_norm_self _).trans hn

theorem eventually_le_log (R : ℝ) : ∀ᶠ n : ℕ in atTop, R ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop R

/-- `0 < C L²/N ≤ 1/2`. -/
theorem gamma_bounds {C N L : ℝ} (hC : 0 < C) (hN : 0 < N) (hL : 1 ≤ L)
    (h1 : C * L ^ 2 ≤ N / 2) : 0 < C * L ^ 2 / N ∧ C * L ^ 2 / N ≤ 1 / 2 := by
  have hL0 : 0 < L := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hN]
  linarith

/-- The condition `λ* · 2 D (D + 1) ≤ 1` of the Legendre bound. -/
theorem degree_cond {C N L : ℝ} (a : ℕ) (hC : 0 < C) (hN : 1 ≤ N) (hL : 1 ≤ L)
    (h2 : 4 * C * L ^ 3 ≤ N ^ (1 / 3 : ℝ)) :
    C * L ^ 2 / N * L * (2 * (N ^ (1 / 3 : ℝ) / L ^ a) * (N ^ (1 / 3 : ℝ) / L ^ a + 1)) ≤ 1 := by
  have hc1 : 1 ≤ N ^ (1 / 3 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hN3 : N = (N ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  set c := N ^ (1 / 3 : ℝ)
  have hL0 : 0 < L := by linarith
  have hLa : 1 ≤ L ^ a := one_le_pow₀ hL
  have hD0 : 0 ≤ c / L ^ a := by positivity
  have hDc : c / L ^ a ≤ c := div_le_self (by linarith) hLa
  have hDD : 2 * (c / L ^ a) * (c / L ^ a + 1) ≤ 4 * c ^ 2 := by nlinarith
  have ht0 : 0 ≤ C * L ^ 2 / N * L := by positivity
  calc C * L ^ 2 / N * L * (2 * (c / L ^ a) * (c / L ^ a + 1))
      ≤ C * L ^ 2 / N * L * (4 * c ^ 2) := mul_le_mul_of_nonneg_left hDD ht0
    _ = 4 * C * L ^ 3 / c := by
      rw [hN3]
      field_simp
    _ ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h2

/-- The first term of the advantage: `(1/√(1 - γ))/√N ≤ 1/(2 L^b)`. -/
theorem first_term {N L γ : ℝ} (b : ℕ) (hN : 0 < N) (hL : 1 ≤ L) (hγ : γ ≤ 1 / 2)
    (h3 : 2 * √2 * L ^ b ≤ √N) : 1 / √(1 - γ) / √N ≤ 1 / (2 * L ^ b) := by
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  have hL0 : 0 < L := by linarith
  have h1 : 1 / √(1 - γ) ≤ √2 := by
    rw [one_div, ← Real.sqrt_inv]
    apply Real.sqrt_le_sqrt
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc 1 / √(1 - γ) / √N ≤ √2 / √N := div_le_div_of_nonneg_right h1 hsN.le
    _ ≤ 1 / (2 * L ^ b) := by
      rw [div_le_div_iff₀ hsN (by positivity)]
      linarith

/-- The second term of the advantage: `(10 D³ λ*/√γ)/√N = 10 √C L²/L^(3(b+1))`. -/
theorem second_term_eq {C N L : ℝ} (b : ℕ) (hC : 0 < C) (hN : 0 < N) (hL : 1 ≤ L) :
    10 * (N ^ (1 / 3 : ℝ) / L ^ (b + 1)) ^ 3 * (C * L ^ 2 / N * L) / √(C * L ^ 2 / N) / √N =
      10 * √C * L ^ 2 / L ^ (3 * (b + 1)) := by
  have hL0 : 0 < L := by linarith
  have hD3 : (N ^ (1 / 3 : ℝ) / L ^ (b + 1)) ^ 3 = N / L ^ (3 * (b + 1)) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← pow_mul, mul_comm (b + 1)]
    norm_num
  have hγ : √(C * L ^ 2 / N) = √C * L / √N := by
    rw [Real.sqrt_div' _ hN.le, Real.sqrt_mul hC.le, Real.sqrt_sq hL0.le]
  have hsC : 0 < √C := Real.sqrt_pos.2 hC
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  have hC2 : C = √C ^ 2 := (Real.sq_sqrt hC.le).symm
  have hN2 : N = √N ^ 2 := (Real.sq_sqrt hN.le).symm
  rw [hD3, hγ]
  set s := √C
  set r := √N
  rw [hC2, hN2]
  field_simp

/-- The second term of the advantage: `(10 D³ λ*/√γ)/√N ≤ 1/(2 L^b)`. -/
theorem second_term {C N L : ℝ} (b : ℕ) (hC : 0 < C) (hN : 0 < N) (hL : 1 ≤ L)
    (h4 : 20 * √C ≤ L) :
    10 * (N ^ (1 / 3 : ℝ) / L ^ (b + 1)) ^ 3 * (C * L ^ 2 / N * L) / √(C * L ^ 2 / N) / √N ≤
      1 / (2 * L ^ b) := by
  have hL0 : 0 < L := by linarith
  rw [second_term_eq b hC hN hL, div_le_div_iff₀ (by positivity) (by positivity)]
  have hLL : L ≤ L ^ (2 * b + 1) := le_self_pow₀ hL (by omega)
  have hpow : L ^ (3 * (b + 1)) = L ^ 2 * L ^ b * L ^ (2 * b + 1) := by
    rw [← pow_add, ← pow_add]
    ring_nf
  rw [hpow]
  have hLb : 0 < L ^ 2 * L ^ b := by positivity
  nlinarith

/-- The parameters of Theorem 3.1 satisfy the hypotheses of the advantage bound for general
parameters, and the bound is at most `1/log^b n`, for all large `n`. -/
theorem params_eventually {C : ℝ} (hC : 0 < C) (b : ℕ) : ∀ᶠ n : ℕ in atTop,
    0 < n ∧ 0 < sparsity C n ∧ sparsity C n < 1 ∧ 0 ≤ sparsity C n * Real.log n ∧
      sparsity C n * Real.log n *
          (2 * ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (b + 1)) *
            ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (b + 1) + 1)) ≤ 1 ∧
      (1 / √(1 - sparsity C n) + 10 * ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ (b + 1)) ^ 3 *
          (sparsity C n * Real.log n) / √(sparsity C n)) / √(n : ℝ) ≤ 1 / Real.log n ^ b := by
  filter_upwards [eventually_ge_atTop 1, eventually_le_log 1, eventually_le_log (20 * √C),
    eventually_log_pow_le 2 one_pos (c := 1 / (2 * C)) (by positivity),
    eventually_log_pow_le 3 (s := 1 / 3) (by norm_num) (c := 1 / (4 * C)) (by positivity),
    eventually_log_pow_le b (s := 1 / 2) (by norm_num) (c := 1 / (2 * √2)) (by positivity)]
    with n hn hL1 hL20 h1 h2 h3
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  set L := Real.log n
  have h1' : C * L ^ 2 ≤ (n : ℝ) / 2 := by
    rw [Real.rpow_one, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h1
    linarith
  have h2' : 4 * C * L ^ 3 ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h2
    linarith
  have h3' : 2 * √2 * L ^ b ≤ √(n : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)] at h3
    rw [Real.sqrt_eq_rpow (n : ℝ)]
    linarith
  obtain ⟨hγ0, hγ1⟩ := gamma_bounds hC hN0 hL1 h1'
  have hsp : sparsity C n = C * L ^ 2 / n := min_eq_right (by linarith)
  have hL0 : 0 < L := by linarith
  rw [hsp]
  refine ⟨by omega, hγ0, by linarith, by positivity, degree_cond (b + 1) hC hN hL1 h2', ?_⟩
  have hsum := add_le_add (first_term b hN0 hL1 hγ1 h3') (second_term b hC hN0 hL1 hL20)
  rw [add_div]
  calc _ ≤ 1 / (2 * L ^ b) + 1 / (2 * L ^ b) := hsum
    _ = 1 / L ^ b := by
      field_simp
      ring

end BHJK25.Spectral.LDAAux
