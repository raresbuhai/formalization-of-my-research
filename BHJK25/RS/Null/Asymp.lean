module

public import BHJK25.RS.Basic.Params

/-!
# The asymptotics of the null bound

With `L = log n`, `u = 1/(2T)`, `a = n^(1 - 1/T)` and `b = n^(1 - u)`, the logarithm of the union
bound `n^{2(k-1)ℓ} q^m n^{W+1} / q^{W+1}` is `(x + t) L + (m - t) log q` with `x = 2 (k - 1) ℓ` and
`t = W + 1`. It is at most `-a` as soon as `log q ≥ (1 + u) L`, `t ≥ b`, `m ≤ 4a`, `L ≥ 1`, and
`x` and `9a` are at most `u b / 2` (`BHJK25.RS.NullAux.log_bound_le`); the last two hold for large
`n`, since `log n` and `n^(1 - 1/T)` are small against `n^(1 - u)`
(`BHJK25.RS.NullAux.eventually_params`).
-/

@[expose] public section

namespace BHJK25.RS.NullAux

open Real Filter

/-- **The exponent of the union bound** is at most `-a`. -/
theorem log_bound_le {L Lq x m t a b u : ℝ} (hL : 1 ≤ L) (ha : 0 ≤ a) (hu : 0 < u)
    (hu2 : u ≤ 1 / 2) (hq : (1 + u) * L ≤ Lq) (ht : b ≤ t) (hm : m ≤ 4 * a)
    (hx : x ≤ u * b / 2) (hab : 9 * a ≤ u * b / 2) :
    (x + t) * L + (m - t) * Lq ≤ -a := by
  have hb : 18 * a ≤ u * b := by linarith
  have hub : u * b ≤ b / 2 := by
    have : 0 ≤ b := by nlinarith
    nlinarith
  have htm : 0 ≤ t - m := by linarith
  have h1 : (m - t) * Lq ≤ (m - t) * ((1 + u) * L) := by
    have := mul_le_mul_of_nonneg_left hq htm
    linarith
  have h2 : m * (1 + u) ≤ 6 * a := by nlinarith
  have h3 : u * b ≤ u * t := mul_le_mul_of_nonneg_left ht hu.le
  have h4 : x + m * (1 + u) - u * t ≤ -3 * a := by linarith
  have h5 : (x + m * (1 + u) - u * t) * L ≤ -3 * a * L :=
    mul_le_mul_of_nonneg_right h4 (by linarith)
  have h6 : -3 * a * L ≤ -a := by nlinarith
  have h7 : (x + t) * L + (m - t) * ((1 + u) * L) = (x + m * (1 + u) - u * t) * L := by ring
  linarith

/-- For large `n`: `n ≥ 2`, `log n ≥ 1`, `2 (k - 1) (3 log n + 7) ≤ u b / 2` and
`9 a ≤ u b / 2`, with `u = 1/(2T)`, `a = n^(1 - 1/T)` and `b = n^(1 - u)`. -/
theorem eventually_params (k : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ log n ∧
      2 * ((k - 1 : ℕ) : ℝ) * (3 * log n + 7) ≤
        1 / (2 * (T : ℝ)) * exp (log n * (1 - 1 / (2 * (T : ℝ)))) / 2 ∧
      9 * exp (log n * (1 - 1 / (T : ℝ))) ≤
        1 / (2 * (T : ℝ)) * exp (log n * (1 - 1 / (2 * (T : ℝ)))) / 2 := by
  set u : ℝ := 1 / (2 * (T : ℝ))
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hu : 0 < u := by positivity
  have hu2 : u ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) two_pos]
    linarith
  have e1 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  have e2 : ∀ᶠ n : ℕ in atTop, 1 ≤ log n :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have e3 := eventually_log_le (s := 1 / 2) (by norm_num) (6 * ((k - 1 : ℕ) : ℝ))
    (14 * ((k - 1 : ℕ) : ℝ)) (c := u / 2) (by positivity)
  have e4 := (tendsto_rpow_atTop hu).comp tendsto_natCast_atTop_atTop |>.eventually_ge_atTop
    (18 / u)
  filter_upwards [e1, e2, e3, e4] with n hn hL h3 h4
  simp only [Function.comp_apply] at h4
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  refine ⟨hn, hL, ?_, ?_⟩
  · have hle : (n : ℝ) ^ (1 / 2 : ℝ) ≤ exp (log n * (1 - u)) := by
      rw [← rpow_def_of_pos hn0]
      exact rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have : u / 2 * (n : ℝ) ^ (1 / 2 : ℝ) ≤ u / 2 * exp (log n * (1 - u)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have hdiv : u * exp (log n * (1 - u)) / 2 = u / 2 * exp (log n * (1 - u)) := by ring
    rw [hdiv]
    linarith
  · rw [rpow_def_of_pos hn0] at h4
    have hsplit : exp (log n * (1 - u)) = exp (log n * (1 - 1 / (T : ℝ))) * exp (log n * u) := by
      rw [← exp_add]
      congr 1
      have : (1 : ℝ) / T = 2 * u := by
        simp only [u]
        field_simp
      rw [this]
      ring
    rw [hsplit]
    have hea : 0 < exp (log n * (1 - 1 / (T : ℝ))) := exp_pos _
    have h18 : 18 ≤ u * exp (log n * u) := by
      rw [div_le_iff₀ hu] at h4
      linarith
    nlinarith

end BHJK25.RS.NullAux
