module

public import Background.PhiSeries
public import Background.SumOfSquares.Algorithm.Loop
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Numerics for sampling Gaussians

Copied from `BGHKLMM26/Numerics.lean` (papers do not import each other). Rational approximations,
with error bounds, of what a Turing machine needs to draw Gaussians from coins:

* `π`, from Mathlib's bounds by nested square roots `√(2 + √(2 + ⋯))`, computed from below with
  the integer square root `SoS.Loop.sqrtP` (`BDT24.Num.abs_piQ_sub_le`);
* `Φ`, from its series (`Gaussian.Phi_eq`) and `π` (`BDT24.Num.abs_phiQ_sub_le`);
* a Gaussian from its cell `⌊2^B Φ(g)⌋`, by bisection on `Φ` (`BDT24.Num.abs_cellInv_sub_le`).
-/

@[expose] public section

namespace BDT24.Num

open Real Gaussian SoS.Loop ProbabilityTheory

/-! ### Square roots from below -/

theorem sqrtP_le_sqrt (p : ℕ) {r : ℚ} (hr : 0 ≤ r) : (sqrtP p r : ℝ) ≤ √(r : ℝ) := by
  set M := ⌊r * 4 ^ p⌋.natAbs
  set s := Nat.sqrt M
  have h4 : (4 : ℚ) ^ p = (2 ^ p) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hM0 : 0 ≤ ⌊r * 4 ^ p⌋ := Int.floor_nonneg.2 (by positivity)
  have hMcast : (M : ℚ) = (⌊r * 4 ^ p⌋ : ℚ) := by
    simp only [M]
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hM0)]
  have hMle : (M : ℝ) ≤ (r : ℝ) * (2 ^ p) ^ 2 := by
    have : (M : ℚ) ≤ r * 4 ^ p := by rw [hMcast]; exact Int.floor_le _
    rw [h4] at this
    exact_mod_cast this
  have hs1 : ((s : ℝ)) ^ 2 ≤ M := by exact_mod_cast Nat.sqrt_le' M
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have hst : (s : ℝ) ≤ √(r : ℝ) * 2 ^ p := by
    rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
      Real.sq_sqrt (by exact_mod_cast hr)]
    linarith
  have : (sqrtP p r : ℝ) = (s : ℝ) / 2 ^ p := by simp [sqrtP, s, M]
  rw [this, div_le_iff₀ hp]
  exact hst

theorem sqrtP_nonneg (p : ℕ) (r : ℚ) : 0 ≤ sqrtP p r := by
  unfold sqrtP
  positivity

/-- `√a - √b ≤ √(a - b)` for `0 ≤ b ≤ a`. -/
theorem sqrt_sub_sqrt_le {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) : √a - √b ≤ √(a - b) := by
  rw [sub_le_iff_le_add]
  rw [show a = (a - b) + b by ring]
  calc √((a - b) + b) ≤ √((√(a - b) + √b) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [add_sq, Real.sq_sqrt (by linarith), Real.sq_sqrt hb]
        nlinarith [Real.sqrt_nonneg (a - b), Real.sqrt_nonneg b]
    _ = √(a - b) + √b := Real.sqrt_sq (by positivity)
    _ = _ := by rw [show a - b + b - b = a - b by ring]

/-! ### `π` -/

/-- The nested square roots `√(2 + √(2 + ⋯))`, `n` deep, each taken from below within `2^-p`. -/
def nestQ (p : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sqrtP p (2 + nestQ p n)

theorem nestQ_nonneg (p n : ℕ) : 0 ≤ nestQ p n := by
  cases n with
  | zero => simp [nestQ]
  | succ n => exact sqrtP_nonneg p _

theorem nestQ_spec (p n : ℕ) : (nestQ p n : ℝ) ≤ sqrtTwoAddSeries 0 n ∧
    sqrtTwoAddSeries 0 n - 2 / 2 ^ p ≤ nestQ p n := by
  induction n with
  | zero =>
    simp only [nestQ, Rat.cast_zero, sqrtTwoAddSeries_zero, zero_sub, le_refl, true_and]
    rw [neg_le]
    simp only [neg_zero]
    positivity
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    have h0 : (0 : ℝ) ≤ nestQ p n := by exact_mod_cast nestQ_nonneg p n
    have hr : (0 : ℚ) ≤ 2 + nestQ p n := by have := nestQ_nonneg p n; linarith
    have hup := sqrtP_le_sqrt p hr
    have hlo := abs_sqrtP_sub_le p hr
    have hdef : sqrtTwoAddSeries 0 (n + 1) = √(2 + sqrtTwoAddSeries 0 n) := rfl
    rw [nestQ, hdef]
    push_cast at hup hlo ⊢
    have hmono : √(2 + (nestQ p n : ℝ)) ≤ √(2 + sqrtTwoAddSeries 0 n) :=
      Real.sqrt_le_sqrt (by linarith)
    -- `√(2 + a) - √(2 + b) ≤ (a - b) / 2`.
    have hlip : √(2 + sqrtTwoAddSeries 0 n) - √(2 + (nestQ p n : ℝ)) ≤
        (sqrtTwoAddSeries 0 n - nestQ p n) / 2 := by
      have hs1 : √2 ≤ √(2 + (nestQ p n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      have hs2 : √2 ≤ √(2 + sqrtTwoAddSeries 0 n) := Real.sqrt_le_sqrt (by linarith)
      have h2 : (1 : ℝ) ≤ √2 := by rw [Real.one_le_sqrt]; norm_num
      have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 + sqrtTwoAddSeries 0 n by linarith)
      have hsq' := Real.sq_sqrt (show (0 : ℝ) ≤ 2 + (nestQ p n : ℝ) by linarith)
      nlinarith
    refine ⟨hup.trans hmono, ?_⟩
    rw [abs_le] at hlo
    have : (2 : ℝ) / 2 ^ (p) / 2 + 1 / 2 ^ p = 2 / 2 ^ p := by ring
    nlinarith [hlo.1]

/-- `π` within `3 / 2^n`: `2^(n+1) √(2 - a)` for the nested square roots `a` of depth `n`. -/
def piQ (n : ℕ) : ℚ := 2 ^ (n + 1) * sqrtP (4 * n + 3) (2 - nestQ (4 * n + 3) n)

theorem abs_piQ_sub_le (n : ℕ) : |(piQ n : ℝ) - π| ≤ 3 / 2 ^ n := by
  have hπ1 := Real.pi_gt_sqrtTwoAddSeries n
  have hπ2 := Real.pi_lt_sqrtTwoAddSeries n
  have ha2 := Real.sqrtTwoAddSeries_lt_two n
  obtain ⟨h1, h2⟩ := nestQ_spec (4 * n + 3) n
  obtain ⟨a, ha⟩ : ∃ a, a = sqrtTwoAddSeries 0 n := ⟨_, rfl⟩
  obtain ⟨â, hâ⟩ : ∃ â : ℝ, â = ((nestQ (4 * n + 3) n : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← ha] at hπ1 hπ2 ha2 h1 h2
  rw [← hâ] at h1 h2
  set p := 4 * n + 3 with hpdef
  have hr : (0 : ℚ) ≤ 2 - nestQ p n := by
    have : (nestQ p n : ℝ) < 2 := by rw [← hâ]; linarith
    have : nestQ p n < 2 := by exact_mod_cast this
    linarith
  have hsq := abs_sqrtP_sub_le p hr
  have hup := sqrtP_le_sqrt p hr
  push_cast at hsq hup
  rw [← hâ] at hsq hup
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (sqrtP p (2 - nestQ p n) : ℝ) := ⟨_, rfl⟩
  rw [← hq] at hsq hup
  -- `√(2 - â) - √(2 - a) ≤ √(a - â) ≤ 2^-(2n+1)`.
  have hd2 : √(2 - â) - √(2 - a) ≤ 1 / 2 ^ (2 * n + 1) := by
    refine (sqrt_sub_sqrt_le (by linarith) (by linarith)).trans ?_
    rw [show (1 : ℝ) / 2 ^ (2 * n + 1) = √((1 / 2 ^ (2 * n + 1)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    refine Real.sqrt_le_sqrt ?_
    have : (2 : ℝ) / 2 ^ p = (1 / 2 ^ (2 * n + 1)) ^ 2 := by
      rw [div_pow, one_pow, ← pow_mul]
      have : p = (2 * n + 1) * 2 + 1 := by omega
      rw [this, pow_succ]
      field_simp
    linarith
  have hd1 : √(2 - a) ≤ √(2 - â) := Real.sqrt_le_sqrt (by linarith)
  have hpiQ : (piQ n : ℝ) = 2 ^ (n + 1) * q := by simp [piQ, hq, p]
  rw [hpiQ]
  have hpn : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [abs_le] at hsq
  have e1 : (2 : ℝ) ^ (n + 1) * (1 / 2 ^ p) ≤ 1 / 2 ^ n := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have e2 : (2 : ℝ) ^ (n + 1) * (1 / 2 ^ (2 * n + 1)) ≤ 1 / 2 ^ n := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have e3 : (1 : ℝ) / 4 ^ n ≤ 1 / 2 ^ n := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  -- `2^(n+1) q` is within `1/2^n` of `2^(n+1) √(2 - a)`.
  have k1 : 2 ^ (n + 1) * q ≤ 2 ^ (n + 1) * √(2 - a) + 1 / 2 ^ n := by
    have : q ≤ √(2 - a) + 1 / 2 ^ (2 * n + 1) := by linarith
    calc 2 ^ (n + 1) * q ≤ 2 ^ (n + 1) * (√(2 - a) + 1 / 2 ^ (2 * n + 1)) :=
          mul_le_mul_of_nonneg_left this hpn.le
      _ ≤ _ := by rw [mul_add]; linarith
  have k2 : 2 ^ (n + 1) * √(2 - a) - 1 / 2 ^ n ≤ 2 ^ (n + 1) * q := by
    have : √(2 - a) - 1 / 2 ^ p ≤ q := by linarith [hsq.1]
    calc 2 ^ (n + 1) * √(2 - a) - 1 / 2 ^ n ≤ 2 ^ (n + 1) * (√(2 - a) - 1 / 2 ^ p) := by
          rw [mul_sub]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left this hpn.le
  have e4 : (3 : ℝ) / 2 ^ n = 3 * (1 / 2 ^ n) := by ring
  rw [abs_le, e4]
  constructor <;> linarith

theorem pi_le_piQ_add (n : ℕ) : π ≤ piQ n + 3 / 2 ^ n := by
  have := abs_le.1 (abs_piQ_sub_le n)
  linarith [this.1]

/-! ### `Φ` -/

/-- The terms of the series of `T(x) = ∫₀ˣ e^(-t²/2) dt`, on rationals. -/
def phiTermQ (x : ℚ) (m : ℕ) : ℚ :=
  (-1) ^ m * x ^ (2 * m + 1) / (2 ^ m * (m.factorial : ℚ) * (2 * m + 1))

/-- The first `N` terms of the series of `T(x)`. -/
def phiSumQ (N : ℕ) (x : ℚ) : ℚ := ((List.range N).map (phiTermQ x)).sum

/-- `1/√(2π)`, from `π` within `3/2^n`. -/
def invSqrt2piQ (n : ℕ) : ℚ := 1 / sqrtP n (2 * piQ n)

/-- **`Φ` on rationals**: `1/2 + T_N(x) / √(2π)`. -/
def phiQ (n N : ℕ) (x : ℚ) : ℚ := 1 / 2 + phiSumQ N x * invSqrt2piQ n

theorem phiSumQ_eq (N : ℕ) (x : ℚ) :
    (phiSumQ N x : ℝ) = ∑ m ∈ Finset.range N, phiTerm x m := by
  induction N with
  | zero => simp [phiSumQ]
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [phiSumQ, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    push_cast [phiTermQ, phiTerm]
    ring

theorem two_le_sqrt_two_pi : 2 ≤ √(2 * π) :=
  calc (2 : ℝ) = √(2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ √(2 * π) := Real.sqrt_le_sqrt (by nlinarith [pi_gt_three])

theorem pow_ge_32 {n : ℕ} (hn : 5 ≤ n) : (1 : ℝ) / 2 ^ n ≤ 1 / 32 := by
  rw [div_le_div_iff₀ (by positivity) (by norm_num), one_mul, one_mul]
  exact_mod_cast (show (32 : ℕ) ≤ 2 ^ n from (pow_le_pow_right₀ (by norm_num) hn :
    2 ^ 5 ≤ 2 ^ n))

theorem piQ_ge {n : ℕ} (hn : 5 ≤ n) : (2.9 : ℝ) ≤ piQ n := by
  have hπ := abs_le.1 (abs_piQ_sub_le n)
  have : (3 : ℝ) / 2 ^ n ≤ 3 / 32 := by
    have := pow_ge_32 hn
    have e : (3 : ℝ) / 2 ^ n = 3 * (1 / 2 ^ n) := by ring
    rw [e]; linarith
  linarith [pi_gt_three, hπ.1]

theorem two_le_sqrtP_piQ {n : ℕ} (hn : 5 ≤ n) : (2 : ℝ) ≤ sqrtP n (2 * piQ n) := by
  have hpq := piQ_ge hn
  have hr : (0 : ℚ) ≤ 2 * piQ n := by
    have : (0 : ℝ) ≤ 2 * piQ n := by linarith
    exact_mod_cast this
  have hsq := abs_le.1 (abs_sqrtP_sub_le n hr)
  push_cast at hsq
  have hsq2 : (2.4 : ℝ) ≤ √(2 * (piQ n : ℝ)) :=
    calc (2.4 : ℝ) = √(2.4 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have := pow_ge_32 hn
  linarith [hsq.1]

/-- `|T(x)| ≤ √(2π) / 2`, since `0 < Φ < 1`. -/
theorem abs_phiSum_le (x : ℝ) : |phiSum x| ≤ √(2 * π) / 2 := by
  have h := Phi_eq x
  have h1 := Phi_pos x
  have h2 := Phi_lt_one x
  have hs : 0 < √(2 * π) := by linarith [two_le_sqrt_two_pi]
  have : phiSum x = (Phi x - 1 / 2) * √(2 * π) := by
    rw [h]; field_simp; ring
  rw [this, abs_mul, abs_of_pos hs]
  have : |Phi x - 1 / 2| ≤ 1 / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  nlinarith

/-- `1/√(2π)` within `2/2^n`, for `n ≥ 5`. -/
theorem abs_invSqrt2piQ_sub_le {n : ℕ} (hn : 5 ≤ n) :
    |(invSqrt2piQ n : ℝ) - 1 / √(2 * π)| ≤ 1 / 2 ^ n := by
  have hπ := abs_le.1 (abs_piQ_sub_le n)
  have h32 : (3 : ℝ) / 2 ^ n ≤ 1 / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2 : ℝ) ^ 5 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    linarith
  have hpi3 := pi_gt_three
  have hpiQ3 : (3 : ℝ) - 1 / 10 ≤ piQ n := by linarith [hπ.1]
  have hr : (0 : ℚ) ≤ 2 * piQ n := by
    have : (0 : ℝ) ≤ 2 * piQ n := by linarith
    exact_mod_cast this
  have hsq := abs_le.1 (abs_sqrtP_sub_le n hr)
  push_cast at hsq
  set s : ℝ := (sqrtP n (2 * piQ n) : ℝ) with hsdef
  have hs0 : √(2 * π) ≥ 2 := two_le_sqrt_two_pi
  have hsq2 : (2.4 : ℝ) ≤ √(2 * (piQ n : ℝ)) :=
    calc (2.4 : ℝ) = √(2.4 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith)
  have hs2 : 2 ≤ s := two_le_sqrtP_piQ hn
  -- `|√(2π̂) - √(2π)| ≤ |2π̂ - 2π| / 4`.
  have hroot : |√(2 * (piQ n : ℝ)) - √(2 * π)| ≤ 6 / 2 ^ n / 4 := by
    have hsum : 4 ≤ √(2 * (piQ n : ℝ)) + √(2 * π) := by linarith
    have hmul : (√(2 * (piQ n : ℝ)) - √(2 * π)) * (√(2 * (piQ n : ℝ)) + √(2 * π)) =
        2 * (piQ n : ℝ) - 2 * π := by
      have e : (√(2 * (piQ n : ℝ)) - √(2 * π)) * (√(2 * (piQ n : ℝ)) + √(2 * π)) =
          √(2 * (piQ n : ℝ)) ^ 2 - √(2 * π) ^ 2 := by ring
      rw [e, Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity)]
    have habs : |2 * (piQ n : ℝ) - 2 * π| ≤ 6 / 2 ^ n := by
      rw [show 2 * (piQ n : ℝ) - 2 * π = 2 * ((piQ n : ℝ) - π) by ring, abs_mul, abs_two]
      have := abs_piQ_sub_le n
      have e : (6 : ℝ) / 2 ^ n = 2 * (3 / 2 ^ n) := by ring
      rw [e]
      linarith
    rw [← hmul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < √(2 * (piQ n : ℝ)) + √(2 * π))]
      at habs
    rw [le_div_iff₀ (by norm_num)]
    nlinarith [abs_nonneg (√(2 * (piQ n : ℝ)) - √(2 * π))]
  have hss : |s - √(2 * π)| ≤ 1 / 2 ^ n + 6 / 2 ^ n / 4 := by
    have : s - √(2 * π) = (s - √(2 * (piQ n : ℝ))) + (√(2 * (piQ n : ℝ)) - √(2 * π)) := by ring
    rw [this]
    refine (abs_add_le _ _).trans (add_le_add ?_ hroot)
    exact abs_le.2 ⟨by linarith [hsq.1], by linarith [hsq.2]⟩
  have hinv : (invSqrt2piQ n : ℝ) = 1 / s := by simp [invSqrt2piQ, hsdef]
  rw [hinv, div_sub_div _ _ (by linarith) (by linarith), one_mul, mul_one, abs_div,
    abs_of_pos (by nlinarith : (0 : ℝ) < s * √(2 * π)), abs_sub_comm, div_le_iff₀ (by nlinarith)]
  have : (4 : ℝ) ≤ s * √(2 * π) := by nlinarith
  calc |s - √(2 * π)| ≤ 1 / 2 ^ n + 6 / 2 ^ n / 4 := hss
    _ ≤ 1 / 2 ^ n * 4 := by
        have : (6 : ℝ) / 2 ^ n / 4 = 1 / 2 ^ n * (3 / 2) := by ring
        rw [this]
        have : (0 : ℝ) ≤ 1 / 2 ^ n := by positivity
        linarith
    _ ≤ 1 / 2 ^ n * (s * √(2 * π)) := by gcongr

theorem invSqrt2piQ_nonneg (n : ℕ) : 0 ≤ invSqrt2piQ n := by
  unfold invSqrt2piQ
  exact div_nonneg zero_le_one (sqrtP_nonneg n _)

theorem invSqrt2piQ_le {n : ℕ} (hn : 5 ≤ n) : (invSqrt2piQ n : ℝ) ≤ 1 / 2 := by
  have h := two_le_sqrtP_piQ hn
  simp only [invSqrt2piQ]
  push_cast
  exact one_div_le_one_div_of_le (by norm_num) h

/-- **`Φ` on rationals is accurate**: for `n ≥ 5` and `N ≥ 3x²`,
`|phiQ - Φ(x)| ≤ |x|/2^N + 2/2^n`. -/
theorem abs_phiQ_sub_le {n N : ℕ} (hn : 5 ≤ n) {x : ℚ} (hN : 3 * (x : ℝ) ^ 2 ≤ N) :
    |(phiQ n N x : ℝ) - Phi x| ≤ |(x : ℝ)| / 2 ^ N + 2 / 2 ^ n := by
  have hT := abs_phiSum_sub_le (x : ℝ) hN
  have hc := abs_invSqrt2piQ_sub_le hn
  have hTb := abs_phiSum_le (x : ℝ)
  have hcpos : (0 : ℝ) ≤ invSqrt2piQ n := by exact_mod_cast invSqrt2piQ_nonneg n
  have hc12 : (invSqrt2piQ n : ℝ) ≤ 1 / 2 := invSqrt2piQ_le hn
  rw [Phi_eq, phiQ]
  push_cast
  rw [phiSumQ_eq]
  set S := ∑ m ∈ Finset.range N, phiTerm (x : ℝ) m
  set c : ℝ := ((invSqrt2piQ n : ℚ) : ℝ)
  have hsplit : 1 / 2 + S * c - (1 / 2 + phiSum x / √(2 * π)) =
      (S - phiSum x) * c + phiSum x * (c - 1 / √(2 * π)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hcpos]
  have h1 : |S - phiSum x| * c ≤ 2 * |(x : ℝ)| * (1 / 2) ^ N * (1 / 2) := by
    rw [abs_sub_comm]
    exact mul_le_mul hT hc12 hcpos (by positivity)
  have hs2 : √(2 * π) / 2 ≤ 2 := by
    have : √(2 * π) ≤ 4 := by
      rw [show (4 : ℝ) = √(4 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by nlinarith [pi_lt_d2])
    linarith
  have h2 : |phiSum x| * |c - 1 / √(2 * π)| ≤ 2 * (1 / 2 ^ n) :=
    mul_le_mul (hTb.trans hs2) hc (abs_nonneg _) (by norm_num)
  have e : 2 * |(x : ℝ)| * (1 / 2) ^ N * (1 / 2) = |(x : ℝ)| / 2 ^ N := by
    rw [one_div_pow]; ring
  have e2 : (2 : ℝ) / 2 ^ n = 2 * (1 / 2 ^ n) := by ring
  linarith

/-! ### Gaussians from their cells -/

/-- One step of bisection for `f(x) < u`. -/
def bisectStep (f : ℚ → ℚ) (u : ℚ) (p : ℚ × ℚ) : ℚ × ℚ :=
  if f ((p.1 + p.2) / 2) < u then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)

/-- `K` steps of bisection on `[-X, X]`. -/
def bisect (f : ℚ → ℚ) (u X : ℚ) (K : ℕ) : ℚ × ℚ := (bisectStep f u)^[K] (-X, X)

theorem bisect_spec (f : ℚ → ℚ) (u : ℚ) {X : ℚ} (hX : 0 ≤ X) (K : ℕ) :
    -X ≤ (bisect f u X K).1 ∧ (bisect f u X K).1 ≤ (bisect f u X K).2 ∧
    (bisect f u X K).2 ≤ X ∧
    (bisect f u X K).2 - (bisect f u X K).1 = 2 * X / 2 ^ K ∧
    ((bisect f u X K).1 = -X ∨ f (bisect f u X K).1 < u) ∧
    ((bisect f u X K).2 = X ∨ u ≤ f (bisect f u X K).2) := by
  induction K with
  | zero =>
    simp only [bisect, Function.iterate_zero, id]
    exact ⟨le_rfl, by linarith, le_rfl, by ring, by simp, by simp⟩
  | succ K ih =>
    obtain ⟨h0, h1, h5, h2, h3, h4⟩ := ih
    simp only [bisect, Function.iterate_succ_apply'] at h0 h1 h5 h2 h3 h4 ⊢
    set lo := ((bisectStep f u)^[K] (-X, X)).1
    set hi := ((bisectStep f u)^[K] (-X, X)).2
    have hp : (bisectStep f u)^[K] (-X, X) = (lo, hi) := rfl
    rw [hp]
    unfold bisectStep
    simp only
    split_ifs with hm
    · refine ⟨by linarith, by linarith, h5, ?_, Or.inr hm, h4⟩
      rw [show hi - (lo + hi) / 2 = (hi - lo) / 2 by ring, h2, pow_succ]
      field_simp
    · refine ⟨h0, by linarith, by linarith, ?_, h3, Or.inr (not_lt.1 hm)⟩
      rw [show (lo + hi) / 2 - lo = (hi - lo) / 2 by ring, h2, pow_succ]
      field_simp

/-- The Gaussian density is at least `(1/4)(1/2)^((R+1)²)` on `[-(R+1), R+1]`. -/
theorem gaussianPDFReal_ge {R : ℕ} {c : ℝ} (hc : |c| ≤ R + 1) :
    (1 / 4) * (1 / 2 : ℝ) ^ ((R + 1) ^ 2) ≤ gaussianPDFReal 0 1 c := by
  have hφ : (0.39 : ℝ) ≤ (√(2 * π))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) (by positivity), Real.sqrt_le_left (by norm_num)]
    nlinarith [pi_lt_d2]
  have hpdf : gaussianPDFReal 0 1 c = (√(2 * π))⁻¹ * rexp (-c ^ 2 / 2) := by
    simp [gaussianPDFReal]
  rw [hpdf]
  have hc2 : c ^ 2 ≤ ((R : ℝ) + 1) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg c) hc 2
  have hexp : (1 / 2 : ℝ) ^ ((R + 1) ^ 2) ≤ rexp (-c ^ 2 / 2) := by
    have hl : (1 / 2 : ℝ) ^ ((R + 1) ^ 2) = rexp (-(((R + 1) ^ 2 : ℕ) : ℝ) * Real.log 2) := by
      rw [show (1 / 2 : ℝ) = rexp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num, ← Real.exp_nat_mul]
      ring_nf
    rw [hl, Real.exp_le_exp]
    have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    push_cast
    nlinarith [sq_nonneg c]
  have h1 : (1 / 4 : ℝ) ≤ (√(2 * π))⁻¹ := by linarith
  exact mul_le_mul h1 hexp (by positivity) (by positivity)

/-- `Φ` grows at least at the density's lower bound on `[-(R+1), R+1]`. -/
theorem Phi_sub_ge {R : ℕ} {a b : ℝ} (hab : a ≤ b) (ha : -(R + 1 : ℝ) ≤ a)
    (hb : b ≤ R + 1) : (b - a) * ((1 / 4) * (1 / 2 : ℝ) ^ ((R + 1) ^ 2)) ≤ Phi b - Phi a := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Phi (gaussianPDFReal 0 1) hab'
    continuous_Phi.continuousOn
    (fun x _ ↦ TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero x)
  have hc' : |c| ≤ R + 1 := abs_le.2 ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have := gaussianPDFReal_ge hc'
  rw [hcd, le_div_iff₀ (by linarith)] at this
  linarith

/-- Recover a Gaussian from its cell `j`: bisection on `phiQ` for the middle `(2j+1)/2^(B+1)` of
the cell. -/
def cellInv (n N K B : ℕ) (X : ℚ) (j : ℕ) : ℚ :=
  (bisect (phiQ n N) ((2 * j + 1) / 2 ^ (B + 1)) X K).1

/-- **Recovering a Gaussian from its cell**: for `|g| ≤ R`, `X = R + 1`, accurate `Φ` and fine
enough cells, the bisection is within `δ + 2X/2^K` of `g`. -/
theorem abs_cellInv_sub_le {n N K B R : ℕ} {g δ : ℝ} (hn : 5 ≤ n) (hg : |g| ≤ R)
    (hN : 3 * ((R : ℝ) + 1) ^ 2 ≤ N) (hδ0 : 0 < δ)
    (hB : 1 / 2 ^ (B + 1) + (((R : ℝ) + 1) / 2 ^ N + 2 / 2 ^ n) ≤
      δ * ((1 / 4) * (1 / 2) ^ ((R + 1) ^ 2))) :
    |(cellInv n N K B (R + 1) (cellOf B g) : ℝ) - g| ≤ δ + 2 * (R + 1) / 2 ^ K := by
  set X : ℚ := R + 1 with hXdef
  have hX : (0 : ℚ) ≤ X := by positivity
  have hXr : (X : ℝ) = R + 1 := by simp [hXdef]
  set j := cellOf B g with hjdef
  set u : ℚ := (2 * j + 1) / 2 ^ (B + 1) with hudef
  obtain ⟨h0, h1, h5, h2, h3, h4⟩ := bisect_spec (phiQ n N) u hX K
  set lo := (bisect (phiQ n N) u X K).1
  set hi := (bisect (phiQ n N) u X K).2
  set m := (1 / 4) * (1 / 2 : ℝ) ^ ((R + 1) ^ 2) with hmdef
  have hm : 0 < m := by positivity
  -- The cell: `j ≤ 2^B Φ(g) < j + 1`.
  have hcell := Nat.floor_eq_iff (show (0 : ℝ) ≤ 2 ^ B * Phi g by
    have := Phi_pos g; positivity) |>.1 hjdef.symm
  have h2B : (0 : ℝ) < 2 ^ B := by positivity
  have hcl : (j : ℝ) / 2 ^ B ≤ Phi g := by rw [div_le_iff₀ h2B]; linarith [hcell.1]
  have hcu : Phi g < ((j : ℝ) + 1) / 2 ^ B := by rw [lt_div_iff₀ h2B]; linarith [hcell.2]
  have hur : (u : ℝ) = ((j : ℝ) + 1 / 2) / 2 ^ B := by
    rw [hudef]; push_cast; rw [pow_succ]; field_simp
  -- `phiQ` is accurate on `[-X, X]`.
  have hacc : ∀ y : ℚ, -X ≤ y → y ≤ X →
      |(phiQ n N y : ℝ) - Phi y| ≤ ((R : ℝ) + 1) / 2 ^ N + 2 / 2 ^ n := by
    intro y hy1 hy2
    have hy : |(y : ℝ)| ≤ R + 1 := by
      rw [← hXr]; exact abs_le.2 ⟨by exact_mod_cast hy1, by exact_mod_cast hy2⟩
    have hN' : 3 * (y : ℝ) ^ 2 ≤ N := by
      have : (y : ℝ) ^ 2 ≤ ((R : ℝ) + 1) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
      linarith
    refine (abs_phiQ_sub_le hn hN').trans ?_
    gcongr
  set err := ((R : ℝ) + 1) / 2 ^ N + 2 / 2 ^ n with herr
  have hg' := abs_le.1 hg
  have hg' := abs_le.1 hg
  have hloX : -X ≤ lo := h0
  have hhiX : hi ≤ X := h5
  have hlor : -((R : ℝ) + 1) ≤ lo := by rw [← hXr]; exact_mod_cast h0
  have hhir : (hi : ℝ) ≤ R + 1 := by rw [← hXr]; exact_mod_cast h5
  have hlohi : (lo : ℝ) ≤ hi := by exact_mod_cast h1
  have hlenr : (hi : ℝ) - lo = 2 * (R + 1) / 2 ^ K := by
    have := congrArg (fun q : ℚ ↦ (q : ℝ)) h2
    push_cast at this
    rw [this, hXr]
  have hhalf : (j : ℝ) / 2 ^ B + 1 / 2 ^ (B + 1) = u := by
    rw [hur, pow_succ]; field_simp
  have hhalf' : (u : ℝ) + 1 / 2 ^ (B + 1) = ((j : ℝ) + 1) / 2 ^ B := by
    rw [hur, pow_succ]; field_simp; ring
  -- `lo ≤ g + δ`.
  have hlo : (lo : ℝ) ≤ g + δ := by
    by_contra hcon
    push Not at hcon
    have hlo_ne : lo ≠ -X := by
      intro h
      have : (lo : ℝ) = -(R + 1) := by rw [h]; push_cast; rw [hXr]
      linarith
    have hf : phiQ n N lo < u := h3.resolve_left hlo_ne
    have hfr : (phiQ n N lo : ℝ) < u := by exact_mod_cast hf
    have hacc' := abs_le.1 (hacc lo hloX (h1.trans h5))
    have hmono : Phi (g + δ) ≤ Phi lo := strictMono_Phi.monotone hcon.le
    have hinc := Phi_sub_ge (R := R) (a := g) (b := g + δ) (by linarith) (by linarith)
      (by linarith)
    rw [show g + δ - g = δ by ring, ← hmdef] at hinc
    linarith [hacc'.1]
  -- `g - δ ≤ hi`.
  have hhi : g - δ ≤ hi := by
    by_contra hcon
    push Not at hcon
    have hhi_ne : hi ≠ X := by
      intro h
      have : (hi : ℝ) = R + 1 := by rw [h, hXr]
      linarith
    have hf : u ≤ phiQ n N hi := h4.resolve_left hhi_ne
    have hfr : (u : ℝ) ≤ phiQ n N hi := by exact_mod_cast hf
    have hacc' := abs_le.1 (hacc hi (h0.trans h1) h5)
    have hmono : Phi hi ≤ Phi (g - δ) := strictMono_Phi.monotone hcon.le
    have hinc := Phi_sub_ge (R := R) (a := g - δ) (b := g) (by linarith) (by linarith)
      (by linarith)
    rw [show g - (g - δ) = δ by ring, ← hmdef] at hinc
    linarith [hacc'.2]
  have hci : (cellInv n N K B (R + 1) (cellOf B g) : ℝ) = lo := rfl
  rw [hci, abs_le]
  constructor
  · linarith
  · linarith [show (0 : ℝ) ≤ 2 * (R + 1) / 2 ^ K by positivity]

end BDT24.Num
