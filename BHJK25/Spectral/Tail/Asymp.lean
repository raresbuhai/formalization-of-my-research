module

public import BHJK25.Model
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Asymptotics for the noisy spike

The inequalities in `n` that the proof of [BHJK25, Lemma 3.7] (`BHJK25.Spectral.noisy_spike`)
needs for all large `n`, with `L = log n`:

* `γ = min(1, C L² / n) = C L² / n` (`BHJK25.sparsity`);
* `(e^(1/4) / √2)^n ≤ n^(-e) / 2`, since `e^(1/4) < √2`;
* `exp(C L² - (1 - ε) C L³ / 16) ≤ n^(-e) / 2` and `(1 - ε) C L³ / 4 > 3`.
-/

@[expose] public section

namespace BHJK25.Spectral.TailAux

open Filter

theorem eventually_log_ge (K : ℝ) : ∀ᶠ n : ℕ in atTop, K ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop K

/-- `γ = C log² n / n` for all large `n`: the cap at `1` is not active. -/
theorem eventually_sparsity_eq {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, sparsity C n = C * Real.log n ^ 2 / n := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / C by positivity))] with n hn
  simp only [Function.comp_apply, one_mul, add_zero] at hn
  rw [sparsity, min_eq_right]
  calc C * Real.log n ^ 2 / n = C * (Real.log n ^ 2 / n) := mul_div_assoc _ _ _
    _ ≤ C * (1 / C) := by gcongr
    _ = 1 := by field_simp

theorem exp_quarter_div_sqrt_two_lt_one : Real.exp (1 / 4) / √2 < 1 := by
  rw [div_lt_one (by positivity)]
  have h4 : Real.exp (1 / 4) ^ 4 < √2 ^ 4 := by
    rw [← Real.exp_nat_mul, show √2 ^ 4 = (√2 ^ 2) ^ 2 by ring, Real.sq_sqrt zero_le_two]
    norm_num
    linarith [Real.exp_one_lt_d9]
  exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h4

/-- `(e^(1/4) / √2)^n ≤ n^(-e) / 2` for all large `n`. -/
theorem eventually_norm_bound (e : ℕ) :
    ∀ᶠ n : ℕ in atTop, (Real.exp (1 / 4) / √2) ^ n ≤ 1 / (n : ℝ) ^ e / 2 := by
  have hq0 : 0 ≤ Real.exp (1 / 4) / √2 := by positivity
  have h := tendsto_pow_const_mul_const_pow_of_abs_lt_one e
    (by rw [abs_of_nonneg hq0]; exact exp_quarter_div_sqrt_two_lt_one)
  filter_upwards [h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    eventually_ge_atTop 1] with n hn hn1
  have hpos : 0 < (n : ℝ) ^ e := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    positivity
  rw [div_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- `exp(C L² - (1 - ε) C L³ / 16) ≤ n^(-e) / 2` and `(1 - ε) C L³ / 4 > 3` for all large `n`,
where `L = log n`. -/
theorem eventually_cross_bound {C ε : ℝ} (hC : 0 < C) (hε1 : ε < 1) (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (C * Real.log n ^ 2 - (1 - ε) * C * Real.log n ^ 3 / 16) ≤ 1 / (n : ℝ) ^ e / 2 ∧
        3 < (1 - ε) * C * Real.log n ^ 3 / 4 := by
  set a := (1 - ε) * C / 16
  have ha : 0 < a := div_pos (mul_pos (by linarith) hC) (by norm_num)
  filter_upwards [eventually_log_ge 1, eventually_log_ge ((C + e + 1) / a),
    eventually_ge_atTop 1] with n h1 h2 hn
  set L := Real.log n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have haL : C + e + 1 ≤ a * L := by rwa [div_le_iff₀ ha, mul_comm] at h2
  have hL2 : L ≤ L ^ 2 := by nlinarith
  have hL1 : 1 ≤ L ^ 2 := by nlinarith
  have he : (e : ℝ) * L ≤ e * L ^ 2 := mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg e)
  have hmain : (C + e + 1) * L ^ 2 ≤ a * L * L ^ 2 :=
    mul_le_mul_of_nonneg_right haL (sq_nonneg L)
  have hcube : (1 - ε) * C * L ^ 3 = 16 * (a * L * L ^ 2) := by ring
  have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
  refine ⟨?_, ?_⟩
  · have hpow : (n : ℝ) ^ e = Real.exp (e * L) := by
      rw [Real.exp_nat_mul, Real.exp_log hn']
    have hrhs : 1 / (n : ℝ) ^ e / 2 = Real.exp (-(e * L) - Real.log 2) := by
      rw [hpow, Real.exp_sub, Real.exp_neg, Real.exp_log two_pos]
      ring
    rw [hrhs, hcube]
    apply Real.exp_le_exp.2
    have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    nlinarith
  · rw [hcube]
    nlinarith

end BHJK25.Spectral.TailAux
