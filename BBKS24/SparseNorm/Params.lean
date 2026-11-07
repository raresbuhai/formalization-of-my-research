module

public import BBKS24.SparseNorm.Levels
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The parameters of the sparse norm bound

Real arithmetic for `BBKS24.SparseNorm.sparse_norm_bound`, with `N ≥ 1` columns,
`Λ = log(N + 2) ≥ 1`, and `Q = s K² ≤ (N + 2)²`:

* `t = ⌈10 Λ⌉` levels (`BBKS24.SparseNorm.nLevels`), so that `2^t ≥ 20 (N + 2)²`;
* `L j = ⌈8800 · 2^j Λ⌉` Maurey samples at level `j` (`BBKS24.SparseNorm.nSamples`), so that
  they fail with probability at most `1 / (40 t Q)` (`BBKS24.SparseNorm.maurey_le`);
* `α = 1 / (20 t Q)`, for which the Chernoff event fails with probability at most `δ` once
  `|R| ≥ 10⁹ Q Λ⁴ log(2/δ)` (`BBKS24.SparseNorm.sum_chernoff_le`).
-/

@[expose] public section

open Finset Real

namespace BBKS24.SparseNorm

variable {N : ℕ}

theorem one_le_log (hN : 1 ≤ N) : 1 ≤ log (N + 2) := by
  rw [le_log_iff_exp_le (by positivity)]
  have h := exp_one_lt_d9
  have : (3 : ℝ) ≤ N + 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  linarith

theorem log_le_add_two : log (N + 2) ≤ N + 2 := by
  have := log_le_sub_one_of_pos (show (0 : ℝ) < N + 2 by positivity)
  linarith

theorem exp_mul_log (k : ℕ) : exp (k * log (N + 2)) = ((N : ℝ) + 2) ^ k := by
  rw [exp_nat_mul, exp_log (by positivity)]

/-- The number of levels, `⌈10 log(N + 2)⌉`. -/
noncomputable def nLevels (N : ℕ) : ℕ := ⌈10 * log (N + 2)⌉₊

theorem le_nLevels : 10 * log (N + 2) ≤ nLevels N := Nat.le_ceil _

theorem nLevels_le (hN : 1 ≤ N) : (nLevels N : ℝ) ≤ 11 * log (N + 2) := by
  have h1 := one_le_log hN
  have := Nat.ceil_lt_add_one (show 0 ≤ 10 * log ((N : ℝ) + 2) by positivity)
  unfold nLevels
  linarith

theorem one_le_nLevels (hN : 1 ≤ N) : 1 ≤ nLevels N := by
  have h1 := one_le_log hN
  have : (1 : ℝ) ≤ nLevels N := by linarith [le_nLevels (N := N)]
  exact_mod_cast this

/-- `2^t ≥ 20 (N + 2)²`, so `2^(-t) ≤ 1 / (20 Q)`. -/
theorem le_two_pow_nLevels (hN : 1 ≤ N) : 20 * ((N : ℝ) + 2) ^ 2 ≤ 2 ^ nLevels N := by
  have h1 := one_le_log hN
  have hl2 := log_two_gt_d9
  have h6 : ((N : ℝ) + 2) ^ 6 ≤ 2 ^ nLevels N := by
    rw [← exp_mul_log, ← exp_log (show (0 : ℝ) < 2 by norm_num), ← exp_nat_mul,
      exp_log (show (0 : ℝ) < 2 by norm_num), exp_le_exp]
    have := le_nLevels (N := N)
    push_cast
    nlinarith
  have h3 : (3 : ℝ) ≤ N + 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have : (81 : ℝ) ≤ ((N : ℝ) + 2) ^ 4 := by
    calc (81 : ℝ) = 3 ^ 4 := by norm_num
      _ ≤ ((N : ℝ) + 2) ^ 4 := pow_le_pow_left₀ (by norm_num) h3 4
  nlinarith [pow_pos (show (0 : ℝ) < N + 2 by positivity) 2]

/-- The number of Maurey samples at level `j`, `⌈8800 · 2^j log(N + 2)⌉`. -/
noncomputable def nSamples (N : ℕ) (j : ℕ) : ℕ := ⌈8800 * 2 ^ j * log (N + 2)⌉₊

theorem nSamples_pos (hN : 1 ≤ N) (j : ℕ) : 0 < nSamples N j := by
  have := one_le_log hN
  exact Nat.ceil_pos.2 (by positivity)

theorem nSamples_le (hN : 1 ≤ N) (j : ℕ) :
    (nSamples N j : ℝ) ≤ 8800 * 2 ^ j * log (N + 2) + 1 := by
  have := one_le_log hN
  exact (Nat.ceil_lt_add_one (by positivity)).le

/-- The Maurey samples fail with probability at most `1 / (40 t Q)` at every level. -/
theorem maurey_le (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q) (hQN : Q ≤ ((N : ℝ) + 2) ^ 2) (j : ℕ) :
    4 * exp (-(nSamples N j * (lvl j / 10) ^ 2) / 8) ≤ 1 / Q / 40 / nLevels N := by
  set Λ := log ((N : ℝ) + 2)
  have h1 := one_le_log hN
  have ht := nLevels_le hN
  have ht1 : (1 : ℝ) ≤ nLevels N := by exact_mod_cast one_le_nLevels hN
  have hexp : (nSamples N j * (lvl j / 10) ^ 2) / 8 ≥ 11 * Λ := by
    have hL : 8800 * 2 ^ j * Λ ≤ nSamples N j := Nat.le_ceil _
    rw [div_pow, lvl_sq]
    have h2 : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
    have h3 : (0 : ℝ) < (1 / 2) ^ j := by positivity
    have : 8800 * 2 ^ j * Λ * (1 / 2) ^ j ≤ nSamples N j * (1 / 2) ^ j :=
      mul_le_mul_of_nonneg_right hL h3.le
    have h4 : 8800 * 2 ^ j * Λ * (1 / 2) ^ j = 8800 * Λ := by
      rw [mul_right_comm, mul_assoc 8800, h2, mul_one]
    rw [ge_iff_le, le_div_iff₀ (by norm_num), mul_div_assoc', le_div_iff₀ (by norm_num)]
    linarith
  have h11 : exp (-(nSamples N j * (lvl j / 10) ^ 2) / 8) ≤ 1 / ((N : ℝ) + 2) ^ 11 := by
    rw [← exp_mul_log, one_div, ← exp_neg, exp_le_exp]
    push_cast
    rw [neg_div]
    linarith
  -- `160 t Q ≤ (N + 2)^11`.
  have hN3 : (3 : ℝ) ≤ N + 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hΛN := log_le_add_two (N := N)
  have h8 : (6561 : ℝ) ≤ ((N : ℝ) + 2) ^ 8 := by
    calc (6561 : ℝ) = 3 ^ 8 := by norm_num
      _ ≤ ((N : ℝ) + 2) ^ 8 := pow_le_pow_left₀ (by norm_num) hN3 8
  have hbig : 160 * (nLevels N : ℝ) * Q ≤ ((N : ℝ) + 2) ^ 11 := by
    have hp : 0 < (N : ℝ) + 2 := by positivity
    have : (nLevels N : ℝ) ≤ 11 * ((N : ℝ) + 2) := by linarith
    calc 160 * (nLevels N : ℝ) * Q ≤ 160 * (11 * ((N : ℝ) + 2)) * ((N : ℝ) + 2) ^ 2 := by
          gcongr
      _ = 1760 * ((N : ℝ) + 2) ^ 3 := by ring
      _ ≤ ((N : ℝ) + 2) ^ 8 * ((N : ℝ) + 2) ^ 3 := by
          gcongr
          linarith
      _ = ((N : ℝ) + 2) ^ 11 := by ring
  calc 4 * exp (-(nSamples N j * (lvl j / 10) ^ 2) / 8) ≤ 4 * (1 / ((N : ℝ) + 2) ^ 11) := by
        gcongr
    _ ≤ 4 * (1 / (160 * (nLevels N : ℝ) * Q)) := by
        gcongr
    _ = 1 / Q / 40 / nLevels N := by
        field_simp
        ring

/-- The total number of Maurey samples up to level `i`: at most `2^i (17600 Λ + 1)`. -/
theorem sum_nSamples_le (hN : 1 ≤ N) (i : ℕ) :
    (∑ j ∈ range (i + 1), (nSamples N j : ℝ)) ≤ 2 ^ i * (17600 * log (N + 2) + 1) := by
  have h1 := one_le_log hN
  have hgeom : (∑ j ∈ range (i + 1), (2 : ℝ) ^ j) ≤ 2 * 2 ^ i := by
    have := geom_sum_eq (show (2 : ℝ) ≠ 1 by norm_num) (i + 1)
    rw [this, pow_succ]
    norm_num
    linarith
  have hi : ((i : ℝ) + 1) ≤ 2 ^ i := by
    have := Nat.lt_two_pow_self (n := i)
    have : (i : ℝ) + 1 ≤ ((2 ^ i : ℕ) : ℝ) := by exact_mod_cast this
    simpa using this
  calc (∑ j ∈ range (i + 1), (nSamples N j : ℝ))
      ≤ ∑ j ∈ range (i + 1), (8800 * 2 ^ j * log (N + 2) + 1) :=
        sum_le_sum fun j _ ↦ nSamples_le hN j
    _ = 8800 * log (N + 2) * (∑ j ∈ range (i + 1), (2 : ℝ) ^ j) + (i + 1) := by
        rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
        push_cast
        simp only [mul_one]
        congr 1
        exact sum_congr rfl fun j _ ↦ by ring
    _ ≤ 8800 * log (N + 2) * (2 * 2 ^ i) + 2 ^ i := by gcongr
    _ = 2 ^ i * (17600 * log (N + 2) + 1) := by ring

/-- **Each level of the Chernoff union bound**: with `|Ω₀| = 2N` samples, `α = 1 / (20 t Q)` and
`|R| ≥ 10⁹ Q Λ⁴ log(2/δ)`, the `i`-th term is at most `δ / t`. -/
theorem chernoff_term_le (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {q : ℝ} (hq : 10 ^ 9 * Q * log (N + 2) ^ 4 * log (2 / δ) ≤ q) (i : ℕ) :
    ((2 * N : ℕ) : ℝ) ^ (∑ j ∈ range (i + 1), nSamples N j) *
        exp (-(q * (1 / Q / 20 / nLevels N) * 2 ^ i / 40)) ≤ δ / nLevels N := by
  set Λ := log ((N : ℝ) + 2) with hΛ
  set t := (nLevels N : ℝ) with htdef
  have h1 : 1 ≤ Λ := one_le_log hN
  have ht := nLevels_le hN
  have ht1 : (1 : ℝ) ≤ t := by
    rw [htdef]
    exact_mod_cast one_le_nLevels hN
  have hD : log 2 ≤ log (2 / δ) :=
    log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := log_two_gt_d9
  set D := log (2 / δ)
  -- `log (2N) ≤ 2Λ`.
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcard : (0 : ℝ) < ((2 * N : ℕ) : ℝ) := by push_cast; linarith
  have hlogc : log ((2 * N : ℕ) : ℝ) ≤ 2 * Λ := by
    have h2 : 2 * Λ = log (((N : ℝ) + 2) ^ 2) := by
      rw [log_pow]
      push_cast
      ring
    rw [h2]
    exact log_le_log hcard (by push_cast; nlinarith)
  have hlogc0 : 0 ≤ log ((2 * N : ℕ) : ℝ) := log_nonneg (by push_cast; linarith)
  -- The power as an exponential.
  set S := ∑ j ∈ range (i + 1), nSamples N j
  have hS : (S : ℝ) ≤ 2 ^ i * (17600 * Λ + 1) := by
    have := sum_nSamples_le hN i
    simpa [S] using this
  have hpow : ((2 * N : ℕ) : ℝ) ^ S = exp (S * log ((2 * N : ℕ) : ℝ)) := by
    rw [exp_nat_mul, exp_log hcard]
  -- The requirement on `q`.
  have hlogt : log t ≤ 11 * Λ := (log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hlogδ : log (1 / δ) ≤ D := log_le_log (by positivity) (by gcongr; norm_num)
  have hreq : (17600 * Λ + 1) * (2 * Λ) + (log t + log (1 / δ)) ≤ q / (800 * t * Q) := by
    rw [le_div_iff₀ (by positivity)]
    have hΛ2 : Λ ^ 2 ≤ Λ ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
    have hΛ3 : Λ ^ 3 ≤ Λ ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    have hΛ14 : Λ ≤ Λ ^ 4 := by nlinarith
    have hD0 : 0 < D := by linarith
    have hlhs : (17600 * Λ + 1) * (2 * Λ) + (log t + log (1 / δ)) ≤ 35213 * Λ ^ 2 + D := by
      nlinarith
    have hD69 : 1 ≤ D * (100 / 69) := by norm_num at hl2; nlinarith
    calc ((17600 * Λ + 1) * (2 * Λ) + (log t + log (1 / δ))) * (800 * t * Q)
        ≤ (35213 * Λ ^ 2 + D) * (800 * (11 * Λ) * Q) := by
          gcongr
      _ = 8800 * Q * (35213 * Λ ^ 3 + Λ * D) := by ring
      _ ≤ 8800 * Q * (35213 * (Λ ^ 4 * (D * (100 / 69))) + Λ ^ 4 * D) := by
          gcongr
          exact hΛ3.trans (le_mul_of_one_le_right (by positivity) hD69)
      _ = 8800 * (35213 * (100 / 69) + 1) * (Q * Λ ^ 4 * D) := by ring
      _ ≤ 10 ^ 9 * (Q * Λ ^ 4 * D) := by
          gcongr
          norm_num
      _ = 10 ^ 9 * Q * Λ ^ 4 * D := by ring
      _ ≤ q := hq
  -- Conclude.
  rw [hpow, ← exp_add, ← exp_log (show 0 < δ / t by positivity), exp_le_exp, log_div hδ.ne'
    (by positivity)]
  have hq' : q * (1 / Q / 20 / t) * 2 ^ i / 40 = 2 ^ i * (q / (800 * t * Q)) := by
    field_simp
    ring
  rw [hq']
  have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hlt0 : 0 ≤ log t + log (1 / δ) := by
    have := log_nonneg ht1
    have : 0 ≤ log (1 / δ) := log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    linarith
  have hlog1δ : log (1 / δ) = -log δ := by rw [one_div, log_inv]
  have hA : (S : ℝ) * log ((2 * N : ℕ) : ℝ) ≤ 2 ^ i * ((17600 * Λ + 1) * (2 * Λ)) := by
    calc (S : ℝ) * log ((2 * N : ℕ) : ℝ) ≤ (2 ^ i * (17600 * Λ + 1)) * (2 * Λ) :=
          mul_le_mul hS hlogc hlogc0 (by positivity)
      _ = _ := by ring
  have : 2 ^ i * ((17600 * Λ + 1) * (2 * Λ)) - 2 ^ i * (q / (800 * t * Q)) ≤
      -(log t + log (1 / δ)) := by
    have := mul_le_mul_of_nonneg_left hreq (show (0 : ℝ) ≤ 2 ^ i by positivity)
    nlinarith
  linarith

/-- **The Chernoff union bound**: the sum over the levels is at most `δ`. -/
theorem sum_chernoff_le (hN : 1 ≤ N) {Q : ℝ} (hQ : 0 < Q) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {q : ℝ} (hq : 10 ^ 9 * Q * log (N + 2) ^ 4 * log (2 / δ) ≤ q) :
    ∑ i ∈ range (nLevels N), ((2 * N : ℕ) : ℝ) ^ (∑ j ∈ range (i + 1), nSamples N j) *
        exp (-(q * (1 / Q / 20 / nLevels N) * 2 ^ i / 40)) ≤ δ := by
  have ht1 : (0 : ℝ) < nLevels N := by exact_mod_cast one_le_nLevels hN
  calc _ ≤ ∑ _i ∈ range (nLevels N), δ / nLevels N :=
        sum_le_sum fun i _ ↦ chernoff_term_le hN hQ hδ hδ1 hq i
    _ = δ := by
        rw [sum_const, card_range, nsmul_eq_mul]
        field_simp

end BBKS24.SparseNorm
