module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Spectral bounds that tend to `0`

The hardness theorems with vanishing spectral bounds (Theorems 1.5 and 1.6, as Corollary 8.4 and
Theorem 8.6 state them) bound the spectrum of their output graphs by `c / 2^a`, for the precision
`a = a₀ + ⌈log₂ n⌉` of the template, while the output has at most `b n^e` vertices for an input
on `n` vertices. Here:

* `2^{⌈log₂ n⌉}` is between `n` and `2n` (`BHSV25.Hard.pow_clog_bounds`);
* `c / n ≤ c (b / N)^{1/e}` when `N ≤ b n^e` (`BHSV25.Hard.div_le_rate`), and this rate tends to
  `0` as `N → ∞` (`BHSV25.Hard.tendsto_rate`), so it is a bound on the spectrum in terms of the
  number of vertices of the output alone.
-/

@[expose] public section

namespace BHSV25.Hard

open Filter Topology

/-- The rate `c (b / N)^{1/e}`. -/
noncomputable def rate (c b : ℝ) (e N : ℕ) : ℝ := c * (b / N) ^ ((e : ℝ)⁻¹)

theorem tendsto_rate (c b : ℝ) {e : ℕ} (he : e ≠ 0) : Tendsto (rate c b e) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat b).rpow_const
    (p := (e : ℝ)⁻¹) (Or.inr (by positivity))
  rw [Real.zero_rpow (by positivity)] at h
  have h2 := h.const_mul c
  rw [mul_zero] at h2
  exact h2

/-- `c / n ≤ c (b / N)^{1/e}` when `N ≤ b n^e`. -/
theorem div_le_rate {c b : ℝ} (hc : 0 ≤ c) {e n N : ℕ} (he : e ≠ 0) (hn : 0 < n) (hN : 0 < N)
    (hNb : (N : ℝ) ≤ b * n ^ e) : c / n ≤ rate c b e N := by
  unfold rate
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (1 / (n : ℝ)) ^ e ≤ b / N := by
    rw [one_div_pow, div_le_div_iff₀ (by positivity) hN', one_mul]
    linarith
  have h2 : ((1 / (n : ℝ)) ^ e) ^ ((e : ℝ)⁻¹) = 1 / n :=
    Real.pow_rpow_inv_natCast (by positivity) he
  have h3 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ (e : ℝ)⁻¹)
  rw [h2] at h3
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left h3 hc

/-- `n ≤ 2^{⌈log₂ n⌉} < 2n` for `n ≥ 1`. -/
theorem pow_clog_bounds {n : ℕ} (hn : 1 ≤ n) : n ≤ 2 ^ Nat.clog 2 n ∧ 2 ^ Nat.clog 2 n < 2 * n := by
  refine ⟨Nat.le_pow_clog (by norm_num) n, ?_⟩
  rcases Nat.eq_or_lt_of_le hn with h | h
  · subst h
    simp
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have h2 : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by norm_num) h)
    have h3 : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      rw [← pow_succ']
      congr 1
      exact (Nat.succ_pred_eq_of_pos h2).symm
    omega

end BHSV25.Hard
