module

public import BHJK25.RS.Defs
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Bounds on the parameters

Bounds on `c = ⌈log₂ n⌉`, the number of bits `r` (`BHJK25.RS.rbits`), the side `ℓ` of the grid
(`BHJK25.RS.ell`), the field size `q = 2^r`, the number of coefficients `m` (`BHJK25.RS.mdeg`)
and the agreement threshold `t = W + 1` (`BHJK25.RS.thr`), used by the several parts of the
proof. With `L = log n`:

* `ℓ ≤ r`, and `r ≤ ℓ^(k-1)` for `k ≥ 2` (`BHJK25.RS.ell_le_rbits`, `BHJK25.RS.rbits_le_pow_ell`);
* `r ≤ 2c + 4` (`BHJK25.RS.rbits_le`), the field has `q = 2^r` elements
  (`BHJK25.RS.card_fld`), and `q ≥ n^(1 + 1/(2T))`, that is `(1 + 1/(2T)) L ≤ r log 2`
  (`BHJK25.RS.log_le_rbits`);
* `L ≤ c log 2 < L + log 2`, so `c ≤ 1.47 L + 1` and `ℓ ≤ 3L + 7` for `n ≥ 2`
  (`BHJK25.RS.clog_le_log`, `BHJK25.RS.ell_le_log`);
* `n^(1 - 1/T) ≤ m ≤ 4 n^(1 - 1/T)`, with `n^(1 - 1/T)` written as `exp(L (1 - 1/T))`
  (`BHJK25.RS.exp_le_mdeg`, `BHJK25.RS.mdeg_le_exp`);
* `2nm < (t - 1)^2` (`BHJK25.RS.two_mul_mdeg_lt_sq`), and `n^(1 - 1/(2T))` is the geometric mean
  of `n` and `n^(1 - 1/T)` (`BHJK25.RS.exp_sq_eq`);
* `A L + B ≤ c n^s` for all large `n`, when `c, s > 0` (`BHJK25.RS.eventually_log_le`).
-/

@[expose] public section

namespace BHJK25.RS

open Real Filter

variable {k T n : ℕ}

/-! ### The grid -/

/-- The side of the grid is at most the number of bits. -/
theorem ell_le_rbits (k T n : ℕ) : ell k T n ≤ rbits T n := by
  unfold ell
  rcases h : (List.range (rbits T n + 1)).find? (fun l ↦ decide (rbits T n ≤ l ^ (k - 1))) with
    _ | l
  · simp
  · have hl := List.mem_of_find?_eq_some h
    rw [List.mem_range] at hl
    simpa using Nat.lt_succ_iff.1 hl

/-- For `k ≥ 2`, the grid has at least `r` cells. -/
theorem rbits_le_pow_ell (hk : 2 ≤ k) (T n : ℕ) : rbits T n ≤ ell k T n ^ (k - 1) := by
  unfold ell
  rcases h : (List.range (rbits T n + 1)).find? (fun l ↦ decide (rbits T n ≤ l ^ (k - 1))) with
    _ | l
  · exact Nat.le_self_pow (by omega) _
  · simpa using List.find?_some h

/-! ### The number of bits and the field -/

/-- `⌈c / (2T)⌉ ≤ c`, so `r ≤ 2c + 4`. -/
theorem rbits_le (T n : ℕ) : rbits T n ≤ 2 * Nat.clog 2 n + 4 := by
  unfold rbits
  have : (Nat.clog 2 n + 2 * T - 1) / (2 * T) ≤ Nat.clog 2 n := by
    rcases Nat.eq_zero_or_pos T with rfl | hT
    · simp
    · refine Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 ?_)
      have h1 := Nat.le_mul_of_pos_right (Nat.clog 2 n) (by omega : 0 < 2 * T)
      have h2 : (Nat.clog 2 n).succ * (2 * T) = Nat.clog 2 n * (2 * T) + 2 * T :=
        Nat.succ_mul _ _
      omega
  omega

/-- The extra bits `⌈c / (2T)⌉`: `c ≤ 2T ⌈c/(2T)⌉ ≤ c + 2T - 1`. -/
theorem ceil_bounds (hT : 1 ≤ T) (c : ℕ) :
    c ≤ (c + 2 * T - 1) / (2 * T) * (2 * T) ∧
      (c + 2 * T - 1) / (2 * T) * (2 * T) ≤ c + 2 * T - 1 := by
  refine ⟨?_, Nat.div_mul_le_self _ _⟩
  have h := Nat.lt_div_mul_add (a := c + 2 * T - 1) (b := 2 * T) (by omega)
  omega

/-- The field has `q = 2^r` elements. -/
theorem card_fld (T n : ℕ) : Fintype.card (Fld T n) = 2 ^ rbits T n := by
  rw [← Fintype.card_congr (bitEquiv T n)]
  simp

/-! ### Logarithms -/

/-- `log n ≤ c log 2`, since `n ≤ 2^c`. -/
theorem log_le_clog (n : ℕ) : log n ≤ Nat.clog 2 n * log 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (log_nonneg one_le_two)
  have h : (n : ℝ) ≤ 2 ^ Nat.clog 2 n := by exact_mod_cast Nat.le_pow_clog one_lt_two n
  calc log n ≤ log (2 ^ Nat.clog 2 n) := log_le_log (by exact_mod_cast hn) h
    _ = _ := by rw [log_pow]

/-- `c log 2 < log n + log 2`, since `2^(c - 1) < n`, for `n ≥ 2`. -/
theorem clog_lt_log (hn : 2 ≤ n) : Nat.clog 2 n * log 2 < log n + log 2 := by
  have h := Nat.pow_pred_clog_lt_self one_lt_two (by omega : 1 < n)
  have hc : 1 ≤ Nat.clog 2 n := Nat.clog_pos one_lt_two (by omega)
  have h' : (2 : ℝ) ^ (Nat.clog 2 n - 1) < n := by exact_mod_cast h
  have h2 := log_lt_log (by positivity) h'
  rw [log_pow] at h2
  have : ((Nat.clog 2 n - 1 : ℕ) : ℝ) = Nat.clog 2 n - 1 := by
    rw [Nat.cast_sub hc, Nat.cast_one]
  rw [this] at h2
  linarith

/-- `c ≤ 1.47 log n + 1`, for `n ≥ 2`, since `log 2 > 1 / 1.47`. -/
theorem clog_le_log (hn : 2 ≤ n) : (Nat.clog 2 n : ℝ) ≤ 147 / 100 * log n + 1 := by
  have h1 := clog_lt_log hn
  have h2 := log_two_gt_d9
  have h3 : 0 ≤ log (n : ℝ) := log_natCast_nonneg n
  by_contra h
  have h4 : (147 / 100 * log n + 1) * log 2 ≤ Nat.clog 2 n * log 2 :=
    mul_le_mul_of_nonneg_right (le_of_not_ge h) (by linarith)
  nlinarith

/-- `ℓ ≤ r ≤ 3 log n + 7`, for `n ≥ 2`. -/
theorem ell_le_log (k T : ℕ) (hn : 2 ≤ n) : (ell k T n : ℝ) ≤ 3 * log n + 7 := by
  have h1 : (ell k T n : ℝ) ≤ 2 * Nat.clog 2 n + 4 := by
    exact_mod_cast (ell_le_rbits k T n).trans (rbits_le T n)
  have h2 := clog_le_log hn
  have h3 : 0 ≤ log (n : ℝ) := log_natCast_nonneg n
  linarith

/-- `q = 2^r ≥ n^(1 + 1/(2T))`: `(1 + 1/(2T)) log n ≤ r log 2`. -/
theorem log_le_rbits (hT : 1 ≤ T) (n : ℕ) :
    (1 + 1 / (2 * (T : ℝ))) * log n ≤ rbits T n * log 2 := by
  set c := Nat.clog 2 n
  have hT' : (0 : ℝ) < 2 * T := by positivity
  have hceil : (c : ℝ) ≤ ((c + 2 * T - 1) / (2 * T) : ℕ) * (2 * T) := by
    exact_mod_cast (ceil_bounds hT c).1
  have hceil' : (c : ℝ) / (2 * T) ≤ ((c + 2 * T - 1) / (2 * T) : ℕ) := by
    rw [div_le_iff₀ hT']
    exact hceil
  have hr : (c : ℝ) + c / (2 * T) ≤ rbits T n := by
    unfold rbits
    push_cast
    linarith
  have hl := log_le_clog n
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have hc : (1 + 1 / (2 * (T : ℝ))) * c = c + c / (2 * T) := by ring
  have hpos : 0 ≤ 1 + 1 / (2 * (T : ℝ)) := by positivity
  calc (1 + 1 / (2 * (T : ℝ))) * log n ≤ (1 + 1 / (2 * (T : ℝ))) * (c * log 2) :=
        mul_le_mul_of_nonneg_left hl hpos
    _ = (c + c / (2 * T)) * log 2 := by rw [← hc]; ring
    _ ≤ rbits T n * log 2 := mul_le_mul_of_nonneg_right hr hlog2.le

/-! ### The number of coefficients -/

theorem mdeg_pos (T n : ℕ) : 0 < mdeg T n := Nat.two_pow_pos _

/-- The exponent `d = ⌈(1 - 1/T) c⌉` of `m = 2^d`: `(T - 1) c ≤ T d ≤ (T - 1) c + T - 1`. -/
theorem mdeg_exp_bounds (hT : 1 ≤ T) (c : ℕ) :
    (T - 1) * c ≤ ((T - 1) * c + T - 1) / T * T ∧
      ((T - 1) * c + T - 1) / T * T ≤ (T - 1) * c + T - 1 := by
  refine ⟨?_, Nat.div_mul_le_self _ _⟩
  have h := Nat.lt_div_mul_add (a := (T - 1) * c + T - 1) (b := T) (by omega)
  omega

theorem one_sub_inv_nonneg (hT : 1 ≤ T) : 0 ≤ 1 - 1 / (T : ℝ) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  rw [sub_nonneg, div_le_one (by linarith)]
  exact hT'

/-- The exponent `d` of `m = 2^d`, in real numbers: `(1 - 1/T) c ≤ d ≤ (1 - 1/T) c + 1`. -/
theorem mdeg_exp_real (hT : 1 ≤ T) (c : ℕ) :
    (1 - 1 / (T : ℝ)) * c ≤ (((T - 1) * c + T - 1) / T : ℕ) ∧
      ((((T - 1) * c + T - 1) / T : ℕ) : ℝ) ≤ (1 - 1 / (T : ℝ)) * c + 1 := by
  obtain ⟨d, hd⟩ : ∃ d, d = ((T - 1) * c + T - 1) / T := ⟨_, rfl⟩
  rw [← hd]
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : (T - 1) * c ≤ d * T := hd ▸ (mdeg_exp_bounds hT c).1
  have h2 : d * T ≤ (T - 1) * c + T - 1 := hd ▸ (mdeg_exp_bounds hT c).2
  have h1' : ((T : ℝ) - 1) * c ≤ d * T := by
    have : (((T - 1) * c : ℕ) : ℝ) ≤ ((d * T : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast [Nat.cast_sub hT] at this
    exact this
  have h2' : (d : ℝ) * T ≤ ((T : ℝ) - 1) * c + T := by
    have h3 : d * T ≤ (T - 1) * c + T := by omega
    have : ((d * T : ℕ) : ℝ) ≤ (((T - 1) * c + T : ℕ) : ℝ) := by exact_mod_cast h3
    push_cast [Nat.cast_sub hT] at this
    exact this
  have hid : (1 - 1 / (T : ℝ)) * c = ((T : ℝ) - 1) * c / T := by field_simp
  constructor
  · rw [hid, div_le_iff₀ hT']
    exact h1'
  · rw [hid, div_add_one hT'.ne', le_div_iff₀ hT']
    exact h2'

/-- `m = 2^d` as `exp(d log 2)`. -/
theorem mdeg_eq_exp (T n : ℕ) :
    (mdeg T n : ℝ) = exp ((((T - 1) * Nat.clog 2 n + T - 1) / T : ℕ) * log 2) := by
  rw [exp_nat_mul, exp_log two_pos]
  unfold mdeg
  push_cast
  rfl

/-- `m ≥ n^(1 - 1/T)`. -/
theorem exp_le_mdeg (hT : 1 ≤ T) (n : ℕ) : exp (log n * (1 - 1 / (T : ℝ))) ≤ mdeg T n := by
  rw [mdeg_eq_exp]
  apply exp_le_exp.2
  have h := (mdeg_exp_real hT (Nat.clog 2 n)).1
  have hl := log_le_clog n
  have hpos := one_sub_inv_nonneg hT
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  calc log n * (1 - 1 / (T : ℝ)) ≤ (Nat.clog 2 n * log 2) * (1 - 1 / (T : ℝ)) :=
        mul_le_mul_of_nonneg_right hl hpos
    _ = ((1 - 1 / (T : ℝ)) * Nat.clog 2 n) * log 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h hlog2.le

/-- `m ≥ n^(1 - 1/T)`, with the power written as `rpow`. -/
theorem rpow_le_mdeg (hT : 1 ≤ T) (n : ℕ) : (n : ℝ) ^ (1 - 1 / (T : ℝ)) ≤ mdeg T n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero]
    exact (zero_rpow_le_one _).trans (Nat.one_le_cast.2 (mdeg_pos T 0))
  · rw [rpow_def_of_pos (by exact_mod_cast hn)]
    exact exp_le_mdeg hT n

/-- `m ≤ 4 n^(1 - 1/T)` for `n ≥ 2`. -/
theorem mdeg_le_exp (hT : 1 ≤ T) (hn : 2 ≤ n) :
    (mdeg T n : ℝ) ≤ 4 * exp (log n * (1 - 1 / (T : ℝ))) := by
  rw [mdeg_eq_exp]
  have h := (mdeg_exp_real hT (Nat.clog 2 n)).2
  have hl := clog_lt_log hn
  have hpos := one_sub_inv_nonneg hT
  have hle1 : 1 - 1 / (T : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (T : ℝ) := by positivity
    linarith
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have h4 : (4 : ℝ) = exp (2 * log 2) := by
    rw [two_mul, exp_add, exp_log two_pos]
    norm_num
  rw [h4, ← exp_add]
  apply exp_le_exp.2
  set d := ((((T - 1) * Nat.clog 2 n + T - 1) / T : ℕ) : ℝ)
  set c := (Nat.clog 2 n : ℝ)
  set a := 1 - 1 / (T : ℝ)
  have step1 : d * log 2 ≤ (a * c + 1) * log 2 := mul_le_mul_of_nonneg_right h hlog2.le
  have step2 : a * (c * log 2) ≤ a * (log n + log 2) := mul_le_mul_of_nonneg_left hl.le hpos
  have step3 : a * log 2 ≤ log 2 := by nlinarith
  nlinarith

/-! ### The threshold -/

theorem thr_eq (T n : ℕ) : thr T n = Nat.sqrt (2 * n * mdeg T n) + 2 := rfl

/-- `2nm < (t - 1)^2` for the threshold `t = ⌊√(2nm)⌋ + 2`. -/
theorem two_mul_mdeg_lt_sq (T n : ℕ) :
    2 * n * mdeg T n < (Nat.sqrt (2 * n * mdeg T n) + 1) ^ 2 := by
  rw [sq]
  exact Nat.lt_succ_sqrt _

/-- `n^(1 - 1/(2T))` squared is `n · n^(1 - 1/T)`. -/
theorem exp_sq_eq (hn : 0 < n) (hT : 1 ≤ T) :
    exp (log n * (1 - 1 / (2 * (T : ℝ)))) ^ 2 = n * exp (log n * (1 - 1 / (T : ℝ))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hT0 : (T : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    linarith
  rw [← exp_nat_mul, ← exp_log hn0, ← exp_add, log_exp]
  congr 1
  field_simp
  ring

/-! ### Asymptotics -/

/-- `A log n + B ≤ c n^s` for large `n`, when `c, s > 0`. -/
theorem eventually_log_le {s : ℝ} (hs : 0 < s) (A B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, A * log n + B ≤ c * (n : ℝ) ^ s := by
  have hK : 0 < c / (2 * (|A| + 1)) := by positivity
  have h1 := (isLittleO_log_rpow_atTop hs).bound hK
  have h2 := (tendsto_rpow_atTop hs).eventually_ge_atTop (2 * (|B| + 1) / c)
  have h3 : ∀ᶠ x : ℝ in atTop, 0 ≤ x := eventually_ge_atTop 0
  have h : ∀ᶠ x : ℝ in atTop, A * log x + B ≤ c * x ^ s := by
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx3 s)] at hx1
    have hxs : 0 ≤ x ^ s := rpow_nonneg hx3 s
    have hA : A * log x ≤ |A| * |log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have hA2 : |A| * |log x| ≤ |A| * (c / (2 * (|A| + 1)) * x ^ s) :=
      mul_le_mul_of_nonneg_left hx1 (abs_nonneg A)
    have hA3 : |A| * (c / (2 * (|A| + 1))) ≤ c / 2 := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [abs_nonneg A]
    have hA4 : |A| * (c / (2 * (|A| + 1)) * x ^ s) ≤ c / 2 * x ^ s := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hA3 hxs
    have hB : B ≤ c / 2 * x ^ s := by
      rw [div_le_iff₀ hc] at hx2
      have := le_abs_self B
      nlinarith
    linarith
  exact tendsto_natCast_atTop_atTop.eventually h

end BHJK25.RS
