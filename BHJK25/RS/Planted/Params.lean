module

public import BHJK25.RS.Basic.Params

/-!
# Bounds on the parameters for the planted case

With `c = ⌈log₂ n⌉`, `L = log n`, `Z = n^(1 - 1/T) = exp(L (1 - 1/T))` and
`H = n^(1 - 1/(2T)) = exp(L (1 - 1/(2T)))`, on top of the bounds of
`BHJK25/RS/Basic/Params.lean`:

* `12 n² ≤ t q` for the threshold `t = W + 1` and the field size `q = 2^r`, since `t² > 2nm` and
  `m q² ≥ 2^(3c + 8) ≥ 256 n³`;
* `Z + 1 ≤ t ≤ 3H + 2`, since `Z ≤ m ≤ 4 Z`;
* the probability `(1 - ε/2)^(2r)` that the `2r` bits of a column escape the noise is at least
  `exp(-0.49 L / T - 3/2)` when `ε T ≤ 1/5`: `log(1 - ε/2) ≥ -(10/9)(ε/2)` and
  `(10/9) ε r ≤ (c/3 + 10/9) / T`, while `c ≤ L / log 2 + 1` and `1 / (3 log 2) ≤ 0.49`.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Real

variable {k T n : ℕ}

/-! ### Natural-number bounds -/

/-- `2r ≤ 3c + 9`, that is `r ≤ (3/2) c + 9/2`. -/
theorem two_rbits_le (hT : 1 ≤ T) (n : ℕ) : 2 * rbits T n ≤ 3 * Nat.clog 2 n + 9 := by
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.clog 2 n := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = (c + 2 * T - 1) / (2 * T) := ⟨_, rfl⟩
  have h2 : e * (2 * T) ≤ c + 2 * T - 1 := he ▸ (ceil_bounds hT c).2
  have hr : rbits T n = c + e + 4 := by subst hc; subst he; rfl
  have he2 : 2 * e ≤ c + 1 := by
    by_contra hcon
    have h3 : (c + 2) * T ≤ 2 * e * T := Nat.mul_le_mul_right _ (by omega)
    have h4 : (c + 2) * T = c * T + 2 * T := by ring
    have h5 : c ≤ c * T := Nat.le_mul_of_pos_right _ (by omega)
    have h6 : 2 * e * T = e * (2 * T) := by ring
    omega
  rw [hr, ← hc]
  omega

/-- `m q² ≥ 256 n³`. -/
theorem mdeg_mul_card_sq (hT : 1 ≤ T) (n : ℕ) :
    256 * n ^ 3 ≤ mdeg T n * (2 ^ rbits T n) ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c, c = Nat.clog 2 n := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = ((T - 1) * c + T - 1) / T := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = (c + 2 * T - 1) / (2 * T) := ⟨_, rfl⟩
  have h1 : (T - 1) * c ≤ d * T := hd ▸ (mdeg_exp_bounds hT c).1
  have h2 : c ≤ e * (2 * T) := he ▸ (ceil_bounds hT c).1
  have hde : c ≤ d + 2 * e := by
    have h3 : T * c ≤ T * (d + 2 * e) := by
      have h4 : T * c = (T - 1) * c + c := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hT]
      have h5 : T * (d + 2 * e) = d * T + e * (2 * T) := by ring
      omega
    exact Nat.le_of_mul_le_mul_left h3 (by omega)
  have hn : n ≤ 2 ^ c := hc ▸ Nat.le_pow_clog one_lt_two n
  have hr : rbits T n = c + e + 4 := by subst hc; subst he; rfl
  have hm : mdeg T n = 2 ^ d := by subst hc; subst hd; rfl
  calc 256 * n ^ 3 ≤ 2 ^ 8 * (2 ^ c) ^ 3 := by
        have := Nat.pow_le_pow_left hn 3
        norm_num
        omega
    _ = 2 ^ (3 * c + 8) := by ring
    _ ≤ 2 ^ (d + 2 * (c + e + 4)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = mdeg T n * (2 ^ rbits T n) ^ 2 := by rw [hm, hr]; ring

/-- `12 n² ≤ t q`. -/
theorem thr_mul_card (hT : 1 ≤ T) (n : ℕ) : 12 * n ^ 2 ≤ thr T n * 2 ^ rbits T n := by
  have h1 := two_mul_mdeg_lt_sq T n
  have h2 := mdeg_mul_card_sq hT n
  have h3 : Nat.sqrt (2 * n * mdeg T n) + 1 ≤ thr T n := by rw [thr_eq]; omega
  have h4 : (Nat.sqrt (2 * n * mdeg T n) + 1) ^ 2 ≤ thr T n ^ 2 := Nat.pow_le_pow_left h3 2
  rw [← Nat.pow_le_pow_iff_left (n := 2) (by norm_num)]
  have h5 : 2 * n * mdeg T n * (2 ^ rbits T n) ^ 2 ≤ thr T n ^ 2 * (2 ^ rbits T n) ^ 2 :=
    Nat.mul_le_mul_right _ (h1.le.trans h4)
  calc (12 * n ^ 2) ^ 2 = 144 * n ^ 4 := by ring
    _ ≤ 512 * n ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
    _ = 2 * n * (256 * n ^ 3) := by ring
    _ ≤ 2 * n * (mdeg T n * (2 ^ rbits T n) ^ 2) := Nat.mul_le_mul_left _ h2
    _ = 2 * n * mdeg T n * (2 ^ rbits T n) ^ 2 := by ring
    _ ≤ thr T n ^ 2 * (2 ^ rbits T n) ^ 2 := h5
    _ = (thr T n * 2 ^ rbits T n) ^ 2 := by ring

/-! ### The number of coefficients and the threshold -/

/-- `n^(1 - 1/T) ≤ n`. -/
theorem exp_le_self (hT : 1 ≤ T) (n : ℕ) (hn : 1 ≤ n) :
    exp (log n * (1 - 1 / (T : ℝ))) ≤ n := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hl : 0 ≤ log (n : ℝ) := log_natCast_nonneg n
  have h1 : 0 ≤ 1 / (T : ℝ) := by positivity
  calc exp (log n * (1 - 1 / (T : ℝ))) ≤ exp (log n) := exp_le_exp.2 (by nlinarith)
    _ = n := exp_log hpos

/-- `t ≥ n^(1 - 1/T) + 1`, since `(t - 1)^2 > 2nm ≥ 2 n n^(1 - 1/T) ≥ n^(2 - 2/T)`. -/
theorem exp_add_one_le_thr (hT : 1 ≤ T) (hn : 1 ≤ n) :
    exp (log n * (1 - 1 / (T : ℝ))) + 1 ≤ thr T n := by
  set Z := exp (log n * (1 - 1 / (T : ℝ)))
  set s := Nat.sqrt (2 * n * mdeg T n)
  have h1 : ((2 * n * mdeg T n : ℕ) : ℝ) < ((s + 1) ^ 2 : ℕ) := by
    exact_mod_cast two_mul_mdeg_lt_sq T n
  push_cast at h1
  have hZm := exp_le_mdeg hT n
  have hZn := exp_le_self hT n hn
  have hZ0 : 0 ≤ Z := (exp_pos _).le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : Z ^ 2 < ((s : ℝ) + 1) ^ 2 := by
    calc Z ^ 2 = Z * Z := sq Z
      _ ≤ n * mdeg T n := mul_le_mul hZn hZm hZ0 hn0
      _ ≤ 2 * n * mdeg T n := by
          have : (0 : ℝ) ≤ n * mdeg T n := by positivity
          linarith
      _ < _ := h1
  have h3 : Z < s + 1 := (pow_lt_pow_iff_left₀ hZ0 (by positivity) (by norm_num)).1 h2
  rw [thr_eq]
  push_cast
  linarith

/-- `t ≤ 3 n^(1 - 1/(2T)) + 2` for `n ≥ 2`, since `(t - 2)^2 ≤ 2nm ≤ 8 n n^(1 - 1/T)`. -/
theorem thr_le_exp (hT : 1 ≤ T) (hn : 2 ≤ n) :
    (thr T n : ℝ) ≤ 3 * exp (log n * (1 - 1 / (2 * T : ℝ))) + 2 := by
  set H := exp (log n * (1 - 1 / (2 * T : ℝ)))
  set s := Nat.sqrt (2 * n * mdeg T n)
  have h1 : ((s ^ 2 : ℕ) : ℝ) ≤ ((2 * n * mdeg T n : ℕ) : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (2 * n * mdeg T n)
  push_cast at h1
  have hm := mdeg_le_exp hT hn
  have hH : (n : ℝ) * exp (log n * (1 - 1 / (T : ℝ))) = H ^ 2 := (exp_sq_eq (by omega) hT).symm
  have h2 : (s : ℝ) ^ 2 ≤ (3 * H) ^ 2 := by
    calc (s : ℝ) ^ 2 ≤ 2 * n * mdeg T n := h1
      _ ≤ 2 * n * (4 * exp (log n * (1 - 1 / (T : ℝ)))) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = 8 * H ^ 2 := by rw [← hH]; ring
      _ ≤ (3 * H) ^ 2 := by nlinarith [sq_nonneg H]
  have h3 : (s : ℝ) ≤ 3 * H :=
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num)).1 h2
  rw [thr_eq]
  push_cast
  linarith

/-! ### Escaping the noise -/

/-- `log(1 - x) ≥ -(10/9) x` for `0 ≤ x ≤ 1/10`. -/
theorem log_one_sub_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 10) :
    -(10 / 9 * x) ≤ log (1 - x) := by
  have hpos : 0 < 1 - x := by linarith
  have h1 := one_sub_inv_le_log_of_pos hpos
  have h2 : (1 - x)⁻¹ ≤ 1 + 10 / 9 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith
  linarith

/-- The `2r` bits of a column escape the noise with probability at least
`exp(-0.49 log n / T - 3/2)`, when `ε T ≤ 1/5`. -/
theorem exp_le_escape (hT : 1 ≤ T) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) (hεT : ε * T ≤ 1 / 5) :
    exp (-(49 / 100 * log n / T) - 3 / 2) ≤ (1 - ε / 2) ^ (2 * rbits T n) := by
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hε1 : ε ≤ 1 / 5 := by nlinarith
  set r := rbits T n
  have hlog := log_one_sub_ge (x := ε / 2) (by linarith) (by linarith)
  have hpos : 0 < 1 - ε / 2 := by linarith
  have hc := clog_le_log hn
  have hl : 0 ≤ log (n : ℝ) := log_natCast_nonneg n
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hr2 : 2 * (r : ℝ) ≤ 3 * Nat.clog 2 n + 9 := by exact_mod_cast two_rbits_le hT n
  have key : 10 / 9 * ε * r ≤ (49 / 100 * log n + 13 / 9) / T := by
    rw [le_div_iff₀ hTpos]
    have h1 : 10 / 9 * ε * r * T = 10 / 9 * r * (ε * T) := by ring
    have h2 : 10 / 9 * r * (ε * T) ≤ 10 / 9 * r * (1 / 5) :=
      mul_le_mul_of_nonneg_left hεT (by positivity)
    have h4 : 10 / 9 * r * (1 / 5) ≤ 49 / 100 * log n + 13 / 9 := by linarith
    linarith
  have key2 : (49 / 100 * log n + 13 / 9) / T ≤ 49 / 100 * log n / T + 3 / 2 := by
    rw [add_div]
    have : 13 / 9 / (T : ℝ) ≤ 13 / 9 := div_le_self (by norm_num) hT'
    linarith
  calc exp (-(49 / 100 * log n / T) - 3 / 2) ≤ exp ((2 * r : ℕ) * log (1 - ε / 2)) := by
        apply exp_le_exp.2
        have h5 := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * r)
        push_cast
        linarith
    _ = (1 - ε / 2) ^ (2 * r) := by rw [exp_nat_mul, exp_log hpos]

end BHJK25.RS.PlantedAux
