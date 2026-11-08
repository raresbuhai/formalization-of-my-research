module

public import BS23.Model
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The parameters of the small-radius algorithm

The algorithm of [BS23, Theorem 1.3] (with its moment constraint in two degrees) reads its
parameters off the input data: the number `k` of components, the weight bound `w = wmin`, the
radius bound `R`, the number `n` of points and the dimension `d`. With `L₀ = logInv w ≈ log₂ (1/w)`:

* `BS23.SmallRadius.sDeg w = 2 ^ ⌈log₂ (L₀ + 8)⌉`, the identification degree `s`, a power of `2`
  with `L₀ + 8 ≤ s ≤ 2 (L₀ + 8)`;
* `BS23.SmallRadius.tDeg w R = 2 ^ ⌈log₂ (max s (4 ⌈R²⌉ + 4))⌉`, the scale degree `t`, a power of
  `2` with `s ∣ t` and `4 ⌈R²⌉ + 4 ≤ t`;
* `BS23.SmallRadius.mDeg w R = t / s` (a power of `2`), `BS23.SmallRadius.ℓDeg w R = 64 t` (the
  SoS degree) and `BS23.SmallRadius.Kc w R = (256 s)^t` (the constant of the moment constraint);
* `BS23.SmallRadius.gridPrec R n d`, the number `p` of bits after the point of the re-rounded
  data, `BS23.SmallRadius.ballBd n = 2^(4 n²)`, the ball bound of the solver,
  `BS23.SmallRadius.accExp n len = (n + len + 2)²`, the accuracy exponent of the solver for a
  problem of encoded length `len`, and `BS23.SmallRadius.coinBits n = n + 8`, the coins per round;
* `BS23.SmallRadius.τ w d t r = w · 256^{-t} · (d+1)^{-2t} · √(r^r)`, the tolerance of the good
  event of degree `r` (analysis only).

**The guard** (`BS23.SmallRadius.NumGuard`, decidable; `BS23.SmallRadius.numGuardB` is a Boolean
version through `Nat.log`): `k ≥ 2`, `d ≥ 1`, `n ≥ 2^20`, `(d+1)^(4t) ≤ n`, `2^(4t) ≤ n` and
`k ≤ n`. (The algorithm also checks that the leading principal minors of the second moment
matrix are positive; that part depends on the data and is not here.) Under the sample size of the
theorem the guard passes (`BS23.SmallRadius.guard_of_sampleSize`).

**The parameter facts used by the analysis** are collected, for real `w` and `R` and abstract
degrees `s` and `t`, in `BS23.SmallRadius.SRParams`; the guard gives them for the computed degrees
(`BS23.SmallRadius.srParams_of_numGuard`).

Facts about the degrees: `BS23.SmallRadius.le_sDeg` (`L₀ + 8 ≤ s`), `BS23.SmallRadius.sDeg_le`
(`s ≤ 2 (L₀ + 8)`), `BS23.SmallRadius.sDeg_dvd_tDeg`, `BS23.SmallRadius.four_ceil_le_tDeg`
(`4 ⌈R²⌉ + 4 ≤ t`), `BS23.SmallRadius.tDeg_le` (`t ≤ 2 (s + 4 ⌈R²⌉ + 4)`), and in real terms, for
`0 < w ≤ 1`: `BS23.SmallRadius.logInv_le_real` (`L₀ ≤ 2 + (3/2) ln (1/w)`),
`BS23.SmallRadius.sDeg_le_real` (`s ≤ 20 + 3 ln (1/w)`), `BS23.SmallRadius.tDeg_le_real`
(`t ≤ 56 (R² + ln (1/w) + 1)`) and `BS23.SmallRadius.le_mul_two_pow_sDeg` (`256 ≤ w 2^s`).
-/

@[expose] public section

namespace BS23.SmallRadius

/-! ### The parameters -/

/-- The exponent `⌈log₂ (L₀ + 8)⌉` of the identification degree, `L₀ = logInv w`. -/
def sExp (w : ℚ) : ℕ := Nat.clog 2 (logInv w + 8)

/-- The **identification degree** `s = 2 ^ ⌈log₂ (L₀ + 8)⌉`, `L₀ = logInv w`. -/
def sDeg (w : ℚ) : ℕ := 2 ^ sExp w

/-- The exponent `⌈log₂ (max s (4 ⌈R²⌉ + 4))⌉` of the scale degree. -/
def tExp (w R : ℚ) : ℕ := Nat.clog 2 (max (sDeg w) (4 * ⌈R ^ 2⌉₊ + 4))

/-- The **scale degree** `t = 2 ^ ⌈log₂ (max s (4 ⌈R²⌉ + 4))⌉`. -/
def tDeg (w R : ℚ) : ℕ := 2 ^ tExp w R

/-- The ratio `m = t / s` of the two degrees, a power of `2`. -/
def mDeg (w R : ℚ) : ℕ := tDeg w R / sDeg w

/-- The degree `ℓ = 64 t` of the SoS program. -/
def ℓDeg (w R : ℚ) : ℕ := 64 * tDeg w R

/-- The constant `K = (256 s)^t` of the moment constraint. -/
def Kc (w R : ℚ) : ℕ := (256 * sDeg w) ^ tDeg w R

/-- The **grid precision** `p = ⌈log₂ (4 (⌈R²⌉ + 2) (d + 1) n²)⌉ + 1`: the whitened data are
re-rounded to multiples of `2^{-p}`. -/
def gridPrec (R : ℚ) (n d : ℕ) : ℕ := Nat.clog 2 (4 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2) + 1

/-- The **ball bound** `2^(4 n²)` given to the solver. -/
def ballBd (n : ℕ) : ℕ := 2 ^ (4 * n ^ 2)

/-- The **accuracy exponent** `(n + len + 2)²` for a program of encoded length `len`: the solver
is run with accuracies `η = γ = 2^{-e}`. -/
def accExp (n len : ℕ) : ℕ := (n + len + 2) ^ 2

/-- The number `n + 8` of **coin bits per round**. -/
def coinBits (n : ℕ) : ℕ := n + 8

/-- The **tolerance** `τ_r = w · 256^{-t} · (d+1)^{-2t} · √(r^r)` of the good event of degree `r`
(analysis only; `0^0 = 1`). -/
noncomputable def τ (w : ℝ) (d t r : ℕ) : ℝ :=
  w * (1 / 256) ^ t / ((d : ℝ) + 1) ^ (2 * t) * Real.sqrt ((r : ℝ) ^ r)

/-! ### The guard -/

/-- The **numeric guard** of the algorithm: `k ≥ 2`, `d ≥ 1`, `n ≥ 2^20`, `(d+1)^(4t) ≤ n`,
`2^(4t) ≤ n` and `k ≤ n`, with `t = tDeg w R`. -/
structure NumGuard (k : ℕ) (w R : ℚ) (n d : ℕ) : Prop where
  two_le_k : 2 ≤ k
  one_le_d : 1 ≤ d
  n_ge : 2 ^ 20 ≤ n
  dpow_le : (d + 1) ^ (4 * tDeg w R) ≤ n
  tpow_le : 2 ^ (4 * tDeg w R) ≤ n
  k_le : k ≤ n

theorem numGuard_iff (k : ℕ) (w R : ℚ) (n d : ℕ) :
    NumGuard k w R n d ↔ 2 ≤ k ∧ 1 ≤ d ∧ 2 ^ 20 ≤ n ∧ (d + 1) ^ (4 * tDeg w R) ≤ n ∧
      2 ^ (4 * tDeg w R) ≤ n ∧ k ≤ n :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

instance (k : ℕ) (w R : ℚ) (n d : ℕ) : Decidable (NumGuard k w R n d) :=
  decidable_of_iff _ (numGuard_iff k w R n d).symm

/-- The numeric guard as a Boolean, with the two large powers compared through `Nat.log`
(`BS23.SmallRadius.numGuardB_iff`). -/
def numGuardB (k : ℕ) (w R : ℚ) (n d : ℕ) : Bool :=
  decide (2 ≤ k) && decide (1 ≤ d) && decide (2 ^ 20 ≤ n) &&
    decide (4 * tDeg w R ≤ Nat.log (d + 1) n) && decide (4 * tDeg w R ≤ Nat.log 2 n) &&
    decide (k ≤ n)

theorem numGuardB_iff (k : ℕ) (w R : ℚ) (n d : ℕ) :
    numGuardB k w R n d = true ↔ NumGuard k w R n d := by
  rw [numGuard_iff]
  simp only [numGuardB, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨hk, hd⟩, hn⟩, h1⟩, h2⟩, h3⟩
    have hn0 : n ≠ 0 := by positivity
    exact ⟨hk, hd, hn, (Nat.le_log_iff_pow_le (by omega) hn0).1 h1,
      (Nat.le_log_iff_pow_le (by omega) hn0).1 h2, h3⟩
  · rintro ⟨hk, hd, hn, h1, h2, h3⟩
    have hn0 : n ≠ 0 := by positivity
    exact ⟨⟨⟨⟨⟨hk, hd⟩, hn⟩, (Nat.le_log_iff_pow_le (by omega) hn0).2 h1⟩,
      (Nat.le_log_iff_pow_le (by omega) hn0).2 h2⟩, h3⟩

/-! ### Facts about the degrees -/

/-- `2^⌈log₂ x⌉ ≤ 2 x` for `x ≥ 1`. -/
theorem two_pow_clog_le {x : ℕ} (hx : 1 ≤ x) : 2 ^ Nat.clog 2 x ≤ 2 * x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hx
    have hpos := Nat.clog_pos (b := 2) (by norm_num) hx
    calc 2 ^ Nat.clog 2 x = 2 * 2 ^ (Nat.clog 2 x).pred := by
          rw [← pow_succ']
          congr 1
          exact (Nat.succ_pred_eq_of_pos hpos).symm
      _ ≤ 2 * x := by omega

theorem sDeg_pos (w : ℚ) : 0 < sDeg w := by unfold sDeg; positivity

theorem tDeg_pos (w R : ℚ) : 0 < tDeg w R := by unfold tDeg; positivity

/-- `L₀ + 8 ≤ s`. -/
theorem le_sDeg (w : ℚ) : logInv w + 8 ≤ sDeg w := Nat.le_pow_clog (by norm_num) _

/-- `s ≤ 2 (L₀ + 8)`. -/
theorem sDeg_le (w : ℚ) : sDeg w ≤ 2 * (logInv w + 8) := two_pow_clog_le (by omega)

theorem eight_le_sDeg (w : ℚ) : 8 ≤ sDeg w := by have := le_sDeg w; omega

theorem max_le_tDeg (w R : ℚ) : max (sDeg w) (4 * ⌈R ^ 2⌉₊ + 4) ≤ tDeg w R :=
  Nat.le_pow_clog (by norm_num) _

/-- `s ≤ t`. -/
theorem sDeg_le_tDeg (w R : ℚ) : sDeg w ≤ tDeg w R := (le_max_left _ _).trans (max_le_tDeg w R)

/-- `4 ⌈R²⌉ + 4 ≤ t`. -/
theorem four_ceil_le_tDeg (w R : ℚ) : 4 * ⌈R ^ 2⌉₊ + 4 ≤ tDeg w R :=
  (le_max_right _ _).trans (max_le_tDeg w R)

/-- `t ≤ 2 max (s, 4 ⌈R²⌉ + 4) ≤ 2 (s + 4 ⌈R²⌉ + 4)`. -/
theorem tDeg_le (w R : ℚ) : tDeg w R ≤ 2 * (sDeg w + 4 * ⌈R ^ 2⌉₊ + 4) := by
  have h := two_pow_clog_le (x := max (sDeg w) (4 * ⌈R ^ 2⌉₊ + 4)) (by
    have := sDeg_pos w; omega)
  have : max (sDeg w) (4 * ⌈R ^ 2⌉₊ + 4) ≤ sDeg w + 4 * ⌈R ^ 2⌉₊ + 4 := by omega
  unfold tDeg tExp
  omega

theorem eight_le_tDeg (w R : ℚ) : 8 ≤ tDeg w R := (eight_le_sDeg w).trans (sDeg_le_tDeg w R)

theorem sExp_le_tExp (w R : ℚ) : sExp w ≤ tExp w R :=
  (Nat.pow_le_pow_iff_right (by norm_num)).1 (sDeg_le_tDeg w R)

/-- `s ∣ t` (both are powers of `2`). -/
theorem sDeg_dvd_tDeg (w R : ℚ) : sDeg w ∣ tDeg w R := Nat.pow_dvd_pow 2 (sExp_le_tExp w R)

theorem mDeg_eq (w R : ℚ) : mDeg w R = 2 ^ (tExp w R - sExp w) := by
  unfold mDeg tDeg sDeg
  rw [Nat.pow_div (sExp_le_tExp w R) (by norm_num)]

theorem mDeg_mul_sDeg (w R : ℚ) : mDeg w R * sDeg w = tDeg w R :=
  Nat.div_mul_cancel (sDeg_dvd_tDeg w R)

theorem mDeg_pos (w R : ℚ) : 0 < mDeg w R := by rw [mDeg_eq]; positivity

/-- `4 R² + 4 ≤ t`, as reals. -/
theorem four_sq_le_tDeg (w R : ℚ) : 4 * (R : ℝ) ^ 2 + 4 ≤ tDeg w R := by
  have h1 : (R ^ 2 : ℚ) ≤ ⌈R ^ 2⌉₊ := Nat.le_ceil _
  have h2 : ((4 * ⌈R ^ 2⌉₊ + 4 : ℕ) : ℝ) ≤ tDeg w R := by exact_mod_cast four_ceil_le_tDeg w R
  have h3 : (R : ℝ) ^ 2 ≤ (⌈R ^ 2⌉₊ : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

/-- `⌈R²⌉ < R² + 1`, as reals. -/
theorem ceil_sq_lt (R : ℚ) : (⌈R ^ 2⌉₊ : ℝ) < (R : ℝ) ^ 2 + 1 := by
  have h : (⌈R ^ 2⌉₊ : ℚ) < R ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg R)
  exact_mod_cast h

/-- `2 ^ L₀ ≥ 1 / w`: `1 ≤ w · 2 ^ L₀` for `w > 0`. -/
theorem one_le_mul_two_pow_logInv {w : ℚ} (hw : 0 < w) : 1 ≤ (w : ℝ) * 2 ^ logInv w := by
  have h1 : w⁻¹ ≤ (⌈w⁻¹⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : (⌈w⁻¹⌉₊ : ℚ) ≤ 2 ^ logInv w := by exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h3 : (w : ℝ)⁻¹ ≤ 2 ^ logInv w := by exact_mod_cast h1.trans h2
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  calc (1 : ℝ) = (w : ℝ) * (w : ℝ)⁻¹ := (mul_inv_cancel₀ hw'.ne').symm
    _ ≤ (w : ℝ) * 2 ^ logInv w := mul_le_mul_of_nonneg_left h3 hw'.le

/-- `256 ≤ w · 2^s`: `s ≥ log₂ (1/w) + 8`. -/
theorem le_mul_two_pow_sDeg {w : ℚ} (hw : 0 < w) : 256 ≤ (w : ℝ) * 2 ^ sDeg w := by
  have h := one_le_mul_two_pow_logInv hw
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have h2 : (2 : ℝ) ^ (logInv w + 8) ≤ 2 ^ sDeg w :=
    pow_le_pow_right₀ (by norm_num) (le_sDeg w)
  rw [pow_add] at h2
  nlinarith

/-- `2 ^ L₀ ≤ 4 / w` for `0 < w ≤ 1`. -/
theorem two_pow_logInv_le {w : ℚ} (hw : 0 < w) (hw1 : w ≤ 1) :
    (2 : ℝ) ^ logInv w ≤ 4 / w := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1' : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
  have hN : 1 ≤ ⌈w⁻¹⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]
    positivity)
  have h1 : 2 ^ logInv w ≤ 2 * ⌈w⁻¹⌉₊ := two_pow_clog_le hN
  have h2 : (⌈w⁻¹⌉₊ : ℚ) < w⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1' : (2 : ℝ) ^ logInv w ≤ 2 * (⌈w⁻¹⌉₊ : ℝ) := by exact_mod_cast h1
  have h2' : (⌈w⁻¹⌉₊ : ℝ) < (w : ℝ)⁻¹ + 1 := by exact_mod_cast h2
  have h3 : (w : ℝ)⁻¹ + 1 ≤ 2 / w := by
    rw [div_eq_mul_inv]
    have : 1 ≤ (w : ℝ)⁻¹ := one_le_inv_iff₀.2 ⟨hw', hw1'⟩
    linarith
  calc (2 : ℝ) ^ logInv w ≤ 2 * (⌈w⁻¹⌉₊ : ℝ) := h1'
    _ ≤ 2 * (2 / w) := by linarith
    _ = 4 / w := by ring

/-- `L₀ ≤ 2 + (3/2) ln (1/w)` for `0 < w ≤ 1`. -/
theorem logInv_le_real {w : ℚ} (hw : 0 < w) (hw1 : w ≤ 1) :
    (logInv w : ℝ) ≤ 2 + 3 / 2 * Real.log (1 / (w : ℝ)) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1' : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
  have h := Real.log_le_log (by positivity) (two_pow_logInv_le hw hw1)
  rw [Real.log_pow, div_eq_mul_one_div, Real.log_mul (by norm_num) (by positivity),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
  have hl2 := Real.log_two_gt_d9
  have hlw : 0 ≤ Real.log (1 / (w : ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hw']; linarith)
  have hL : (0 : ℝ) ≤ logInv w := Nat.cast_nonneg _
  push_cast at h
  -- `L₀ log 2 ≤ 2 log 2 + log (1/w)` and `log 2 > 2/3`
  nlinarith

/-- `s ≤ 20 + 3 ln (1/w)` for `0 < w ≤ 1`. -/
theorem sDeg_le_real {w : ℚ} (hw : 0 < w) (hw1 : w ≤ 1) :
    (sDeg w : ℝ) ≤ 20 + 3 * Real.log (1 / (w : ℝ)) := by
  have h1 : (sDeg w : ℝ) ≤ 2 * ((logInv w : ℝ) + 8) := by exact_mod_cast sDeg_le w
  have h2 := logInv_le_real hw hw1
  linarith

/-- `t ≤ 56 (R² + ln (1/w) + 1)` for `0 < w ≤ 1`. -/
theorem tDeg_le_real {w : ℚ} (hw : 0 < w) (hw1 : w ≤ 1) (R : ℚ) :
    (tDeg w R : ℝ) ≤ 56 * ((R : ℝ) ^ 2 + Real.log (1 / (w : ℝ)) + 1) := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1' : (w : ℝ) ≤ 1 := by exact_mod_cast hw1
  have h1 : (tDeg w R : ℝ) ≤ 2 * ((sDeg w : ℝ) + 4 * (⌈R ^ 2⌉₊ : ℝ) + 4) := by
    exact_mod_cast tDeg_le w R
  have h2 := sDeg_le_real hw hw1
  have h3 := ceil_sq_lt R
  have hlw : 0 ≤ Real.log (1 / (w : ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hw']; linarith)
  have hR : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  linarith

/-- `gridPrec`: `8 (⌈R²⌉ + 2) (d + 1) n² ≤ 2^p`. -/
theorem le_two_pow_gridPrec (R : ℚ) (n d : ℕ) :
    8 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 ≤ 2 ^ gridPrec R n d := by
  set c := Nat.clog 2 (4 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2) with hc
  have h : 4 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) _
  have e : 2 ^ gridPrec R n d = 2 ^ c * 2 := pow_succ 2 c
  rw [e]
  calc 8 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 = 4 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 * 2 := by
        ring
    _ ≤ 2 ^ c * 2 := Nat.mul_le_mul_right 2 h

theorem le_four_pow_of_le_two_pow {R : ℚ} {n d p : ℕ}
    (h : 8 * (⌈R ^ 2⌉₊ + 2) * (d + 1) * n ^ 2 ≤ 2 ^ p) :
    3 * ((R : ℝ) ^ 2 + 2) * d * n ^ 2 ≤ 4 ^ p := by
  have h' := (Nat.cast_le (α := ℝ)).2 h
  push_cast at h'
  have h2 : (2 : ℝ) ^ p ≤ 4 ^ p := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have h1 : (R ^ 2 : ℚ) ≤ ⌈R ^ 2⌉₊ := Nat.le_ceil _
  have h3 : (R : ℝ) ^ 2 ≤ (⌈R ^ 2⌉₊ : ℝ) := by exact_mod_cast h1
  have hR : 0 ≤ (R : ℝ) ^ 2 := sq_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have a1 : 3 * ((R : ℝ) ^ 2 + 2) ≤ 8 * ((⌈R ^ 2⌉₊ : ℝ) + 2) := by linarith
  have a2 : 3 * ((R : ℝ) ^ 2 + 2) * d ≤ 8 * ((⌈R ^ 2⌉₊ : ℝ) + 2) * ((d : ℝ) + 1) :=
    mul_le_mul a1 (by linarith) hd (by positivity)
  have a3 : 3 * ((R : ℝ) ^ 2 + 2) * d * n ^ 2 ≤
      8 * ((⌈R ^ 2⌉₊ : ℝ) + 2) * ((d : ℝ) + 1) * n ^ 2 := mul_le_mul_of_nonneg_right a2 hn
  linarith

/-- `gridPrec`: `3 (R² + 2) d n² ≤ 4^p`, so `3 (R² + 2) d 4^{-p} ≤ 1 / n²`. -/
theorem le_four_pow_gridPrec (R : ℚ) (n d : ℕ) :
    3 * ((R : ℝ) ^ 2 + 2) * d * n ^ 2 ≤ 4 ^ gridPrec R n d :=
  le_four_pow_of_le_two_pow (le_two_pow_gridPrec R n d)

/-! ### The tolerances -/

theorem one_le_pow_self (r : ℕ) : (1 : ℝ) ≤ (r : ℝ) ^ r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  · exact one_le_pow₀ (by exact_mod_cast hr)

theorem τ_pos {w : ℝ} (hw : 0 < w) (d t r : ℕ) : 0 < τ w d t r := by
  unfold τ
  have : 0 < Real.sqrt ((r : ℝ) ^ r) := Real.sqrt_pos.2 (by linarith [one_le_pow_self r])
  positivity

theorem τ_sq (w : ℝ) (d t r : ℕ) :
    τ w d t r ^ 2 = w ^ 2 * (1 / 256) ^ (2 * t) / ((d : ℝ) + 1) ^ (4 * t) * (r : ℝ) ^ r := by
  unfold τ
  rw [mul_pow, Real.sq_sqrt (by linarith [one_le_pow_self r]), div_pow, mul_pow, ← pow_mul,
    ← pow_mul]
  ring_nf

/-- For degrees `r ≤ 2` the tolerance is at most `w / 128`. -/
theorem τ_le_of_le_two {w : ℝ} (hw : 0 ≤ w) (d : ℕ) {t r : ℕ} (ht : 1 ≤ t) (hr : r ≤ 2) :
    τ w d t r ≤ w / 128 := by
  unfold τ
  have h1 : ((1 : ℝ) / 256) ^ t ≤ 1 / 256 := by
    calc ((1 : ℝ) / 256) ^ t ≤ (1 / 256) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) ht
      _ = 1 / 256 := pow_one _
  have h2 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ (2 * t) := one_le_pow₀ (by linarith [d.cast_nonneg (α := ℝ)])
  have h3 : Real.sqrt ((r : ℝ) ^ r) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    interval_cases r <;> norm_num
  have h4 : 0 ≤ Real.sqrt ((r : ℝ) ^ r) := Real.sqrt_nonneg _
  calc w * (1 / 256) ^ t / ((d : ℝ) + 1) ^ (2 * t) * Real.sqrt ((r : ℝ) ^ r)
      ≤ w * (1 / 256) ^ t * Real.sqrt ((r : ℝ) ^ r) := by
        gcongr
        exact div_le_self (by positivity) h2
    _ ≤ w * (1 / 256) * 2 := by gcongr
    _ = w / 128 := by ring

/-! ### The parameter facts used by the analysis -/

/-- **The parameter facts** used by the analysis, for a weight bound `w`, a radius bound `R`, and
degrees `s`, `t`, with `k` components, dimension `d` and `n` points: the guard inequalities, and
the relations between `s`, `t`, `w` and `R`. -/
structure SRParams (k d n : ℕ) (w R : ℝ) (s t : ℕ) : Prop where
  two_le_k : 2 ≤ k
  one_le_d : 1 ≤ d
  w_pos : 0 < w
  w_le_half : w ≤ 1 / 2
  s_pow : ∃ a, s = 2 ^ a
  t_pow : ∃ a, t = 2 ^ a
  s_dvd_t : s ∣ t
  eight_le_s : 8 ≤ s
  /-- `s ≥ log₂ (1/w) + 8`. -/
  s_ge : 256 ≤ w * 2 ^ s
  s_le : (s : ℝ) ≤ 20 + 3 * Real.log (1 / w)
  t_ge : 4 * R ^ 2 + 4 ≤ t
  t_le : (t : ℝ) ≤ 56 * (R ^ 2 + Real.log (1 / w) + 1)
  n_ge : 2 ^ 20 ≤ n
  dpow_le : (d + 1) ^ (4 * t) ≤ n
  tpow_le : 2 ^ (4 * t) ≤ n
  k_le : k ≤ n

/-- **The guard gives the parameter facts** for the computed degrees. -/
theorem srParams_of_numGuard {k : ℕ} {w R : ℚ} {n d : ℕ} (hG : NumGuard k w R n d)
    (hw : 0 < w) (hw2 : (w : ℝ) ≤ 1 / 2) :
    SRParams k d n w R (sDeg w) (tDeg w R) where
  two_le_k := hG.two_le_k
  one_le_d := hG.one_le_d
  w_pos := by exact_mod_cast hw
  w_le_half := hw2
  s_pow := ⟨_, rfl⟩
  t_pow := ⟨_, rfl⟩
  s_dvd_t := sDeg_dvd_tDeg w R
  eight_le_s := eight_le_sDeg w
  s_ge := le_mul_two_pow_sDeg hw
  s_le := sDeg_le_real hw (by
    have : (w : ℝ) ≤ 1 := by linarith
    exact_mod_cast this)
  t_ge := four_sq_le_tDeg w R
  t_le := tDeg_le_real hw (by
    have : (w : ℝ) ≤ 1 := by linarith
    exact_mod_cast this) R
  n_ge := hG.n_ge
  dpow_le := hG.dpow_le
  tpow_le := hG.tpow_le
  k_le := hG.k_le

namespace SRParams

variable {k d n : ℕ} {w R : ℝ} {s t : ℕ}

theorem s_pos (h : SRParams k d n w R s t) : 0 < s := by have := h.eight_le_s; omega

theorem s_le_t (h : SRParams k d n w R s t) : s ≤ t := by
  obtain ⟨a, ha⟩ := h.t_pow
  exact Nat.le_of_dvd (by rw [ha]; positivity) h.s_dvd_t

theorem eight_le_t (h : SRParams k d n w R s t) : 8 ≤ t := h.eight_le_s.trans h.s_le_t

theorem t_pos (h : SRParams k d n w R s t) : 0 < t := by have := h.eight_le_t; omega

theorem div_mul_s (h : SRParams k d n w R s t) : t / s * s = t := Nat.div_mul_cancel h.s_dvd_t

/-- `m = t / s` is a power of `2`. -/
theorem m_pow (h : SRParams k d n w R s t) : ∃ a, t / s = 2 ^ a := by
  obtain ⟨a, rfl⟩ := h.s_pow
  obtain ⟨b, rfl⟩ := h.t_pow
  have hab : a ≤ b := (Nat.pow_le_pow_iff_right (by norm_num)).1 h.s_le_t
  exact ⟨b - a, Nat.pow_div hab (by norm_num)⟩

theorem n_pos (h : SRParams k d n w R s t) : 0 < n := by have := h.n_ge; positivity

theorem w_le_one (h : SRParams k d n w R s t) : w ≤ 1 := by linarith [h.w_le_half]

theorem two_le_inv_w (h : SRParams k d n w R s t) : 2 ≤ 1 / w := by
  rw [le_div_iff₀ h.w_pos]; linarith [h.w_le_half]

theorem log_inv_w_nonneg (h : SRParams k d n w R s t) : 0 ≤ Real.log (1 / w) :=
  Real.log_nonneg (by linarith [h.two_le_inv_w])

/-- `t ≤ 2^(4t) ≤ n`. -/
theorem t_le_n (h : SRParams k d n w R s t) : t ≤ n := by
  have h1 : t < 2 ^ t := Nat.lt_two_pow_self
  have h2 : 2 ^ t ≤ 2 ^ (4 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := h.tpow_le
  omega

/-- `d + 1 ≤ (d+1)^(4t) ≤ n`. -/
theorem d_lt_n (h : SRParams k d n w R s t) : d < n := by
  have h1 : d + 1 ≤ (d + 1) ^ (4 * t) := Nat.le_self_pow (by have := h.t_pos; omega) _
  have := h.dpow_le
  omega

/-- `R² ≤ t / 4`. -/
theorem R_sq_le (h : SRParams k d n w R s t) : R ^ 2 ≤ t / 4 := by
  have := h.t_ge; linarith

/-- `3 (R² + 2) ≤ n`. -/
theorem three_R_sq_le_n (h : SRParams k d n w R s t) : 3 * (R ^ 2 + 2) ≤ n := by
  have h1 := h.t_ge
  have h2 : (t : ℝ) ≤ n := by exact_mod_cast h.t_le_n
  have h4 : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by exact_mod_cast h.n_ge
  push_cast at h4
  linarith

/-- `1 / w ≤ 2^s ≤ 2^(4t) ≤ n`. -/
theorem inv_w_le_n (h : SRParams k d n w R s t) : 1 / w ≤ n := by
  have hw := h.w_pos
  have h1 : 1 / w ≤ (2 : ℝ) ^ s := by
    rw [div_le_iff₀ hw]
    nlinarith [h.s_ge]
  have h2 : (2 : ℝ) ^ s ≤ 2 ^ (4 * t) :=
    pow_le_pow_right₀ (by norm_num) (by have := h.s_le_t; omega)
  have h3 : ((2 ^ (4 * t) : ℕ) : ℝ) ≤ n := by exact_mod_cast h.tpow_le
  push_cast at h3
  linarith

end SRParams

/-! ### The guard passes under the sample size of the theorem -/

/-- **The guard passes.** With `k ≥ 2` components of weights at least `w` (so `k w ≤ 1`),
`0 < w ≤ 1/2`, `d ≥ 1`, and `n ≥ ((d+1)/w)^(C (R² + ln (1/w) + 1))` for some `C ≥ 2^64`, the
numeric guard holds: `(d+1)^(4t) ≤ n`, `2^(4t) ≤ n`, `2^20 ≤ n` and `k ≤ n`. -/
theorem guard_of_sampleSize {k d n : ℕ} {w R : ℚ} {C : ℝ} (hk : 2 ≤ k) (hd : 1 ≤ d)
    (hw : 0 < w) (hw2 : (w : ℝ) ≤ 1 / 2) (hkw : (k : ℝ) * w ≤ 1) (hC : 2 ^ 64 ≤ C)
    (hn : (((d : ℝ) + 1) / w) ^ (C * ((R : ℝ) ^ 2 + Real.log (1 / (w : ℝ)) + 1)) ≤ n) :
    NumGuard k w R n d := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1 : w ≤ 1 := by
    have : (w : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  set x : ℝ := ((d : ℝ) + 1) / w with hx
  set B : ℝ := (R : ℝ) ^ 2 + Real.log (1 / (w : ℝ)) + 1 with hB
  have hd' : (2 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hinvw : 2 ≤ 1 / (w : ℝ) := by rw [le_div_iff₀ hw']; linarith
  have hdx : (d : ℝ) + 1 ≤ x := by
    rw [hx, le_div_iff₀ hw']
    nlinarith
  have hinvx : 1 / (w : ℝ) ≤ x := by
    rw [hx, div_le_div_iff_of_pos_right hw']
    linarith
  have hx4 : 4 ≤ x := by
    rw [hx, le_div_iff₀ hw']
    nlinarith
  have hlw : 0 ≤ Real.log (1 / (w : ℝ)) := Real.log_nonneg (by linarith)
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith [sq_nonneg (R : ℝ)]
  have hE : 2 ^ 64 * B ≤ C * B := mul_le_mul_of_nonneg_right hC (by linarith)
  -- `x^m ≤ n` whenever `m ≤ C B`
  have key : ∀ m : ℕ, (m : ℝ) ≤ 2 ^ 64 * B → x ^ m ≤ n := fun m hm ↦ by
    calc x ^ m = x ^ (m : ℝ) := (Real.rpow_natCast x m).symm
      _ ≤ x ^ (C * B) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ n := hn
  have ht := tDeg_le_real hw hw1 R
  have h4t : ((4 * tDeg w R : ℕ) : ℝ) ≤ 2 ^ 64 * B := by
    push_cast
    nlinarith
  refine ⟨hk, hd, ?_, ?_, ?_, ?_⟩
  · have h1 : (2 : ℝ) ^ 20 ≤ x ^ 10 := by
      calc (2 : ℝ) ^ 20 = 4 ^ 10 := by norm_num
        _ ≤ x ^ 10 := pow_le_pow_left₀ (by norm_num) hx4 _
    have h2 := key 10 (by push_cast; nlinarith)
    have : ((2 ^ 20 : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  · have h1 : ((d : ℝ) + 1) ^ (4 * tDeg w R) ≤ x ^ (4 * tDeg w R) :=
      pow_le_pow_left₀ (by positivity) hdx _
    have h2 := key _ h4t
    have : (((d + 1) ^ (4 * tDeg w R) : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  · have h1 : (2 : ℝ) ^ (4 * tDeg w R) ≤ x ^ (4 * tDeg w R) :=
      pow_le_pow_left₀ (by norm_num) (by linarith) _
    have h2 := key _ h4t
    have : ((2 ^ (4 * tDeg w R) : ℕ) : ℝ) ≤ n := by push_cast; linarith
    exact_mod_cast this
  · have h1 : (k : ℝ) ≤ 1 / w := by rw [le_div_iff₀ hw']; linarith
    have h2 := key 1 (by push_cast; nlinarith)
    rw [pow_one] at h2
    have : (k : ℝ) ≤ n := by linarith
    exact_mod_cast this

end BS23.SmallRadius
