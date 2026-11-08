module

public import BHJK25.RS.Null.Asymp
public import BHJK25.RS.Null.Union

/-!
# Acceptance of a uniform tensor is unlikely

For large `n`, the union bound `n^{2(k-1)ℓ} q^m n^{W+1} / q^{W+1}` of
`BHJK25.RS.NullAux.uniformProb_accept_le` is at most `exp(-n^(1 - 1/T))`: its logarithm is
`(x + t) log n + (m - t) r log 2` with `x = 2 (k - 1) ℓ` and `t = W + 1`, and the parameter bounds
of `BHJK25/RS/Basic/Params.lean` with the asymptotics of `BHJK25/RS/Null/Asymp.lean` bound it by
`-n^(1 - 1/T)` (`BHJK25.RS.NullAux.log_bound_le`).
-/

@[expose] public section

namespace BHJK25.RS.NullAux

open Real Filter

variable {k T : ℕ}

/-- The probability of the complement of an event is one minus its probability. -/
theorem uniformProb_not {k n : ℕ} (E : Tensor k n → Prop) :
    uniformProb k n (fun M ↦ ¬ E M) = 1 - uniformProb k n E := by
  classical
  unfold uniformProb
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le _), Fintype.card_fun,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat, sub_div, div_self (by positivity)]

/-- `n^(1 - 1/(2T)) ≤ W + 1`, since `n^(2 - 1/T) ≤ n m < (W + 1)^2`. -/
theorem exp_le_thr {n : ℕ} (hn : 0 < n) (hT : 1 ≤ T) :
    exp (log n * (1 - 1 / (2 * (T : ℝ)))) ≤ thr T n := by
  set b := exp (log n * (1 - 1 / (2 * (T : ℝ))))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hb2 := exp_sq_eq hn hT
  have hna : (n : ℝ) * exp (log n * (1 - 1 / (T : ℝ))) ≤ n * mdeg T n :=
    mul_le_mul_of_nonneg_left (exp_le_mdeg hT n) hn0
  have hnm : (n : ℝ) * mdeg T n ≤ 2 * n * mdeg T n := by
    have : (0 : ℝ) ≤ n * mdeg T n := by positivity
    linarith
  have ht : (2 * n * mdeg T n : ℝ) < (thr T n : ℝ) ^ 2 := by
    have h := (two_mul_mdeg_lt_sq T n).trans_le (Nat.pow_le_pow_left (Nat.le_succ _) 2)
    exact_mod_cast h
  have hsq : b ^ 2 < (thr T n : ℝ) ^ 2 := by linarith
  have hb : 0 ≤ b := (exp_pos _).le
  have hthr : (0 : ℝ) ≤ thr T n := Nat.cast_nonneg _
  exact (pow_lt_pow_iff_left₀ hb hthr two_ne_zero).1 hsq |>.le

/-- **Acceptance of a uniform tensor is unlikely**: for large `n`, it has probability at most
`exp(-n^(1 - 1/T))`, with `n^(1 - 1/T)` written as `exp(log n (1 - 1/T))`. -/
theorem uniformProb_accept_le_exp (hk : 2 ≤ k) (hT : 1 ≤ T) :
    ∀ᶠ n : ℕ in atTop, uniformProb k n (fun M ↦ Accept k T n M) ≤
      exp (-exp (log n * (1 - 1 / (T : ℝ)))) := by
  filter_upwards [eventually_params k hT] with n ⟨hn, hL, hx, hab⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hP := uniformProb_accept_le (T := T) (n := n) hk
  refine hP.trans ?_
  have hQ : (0 : ℝ) < 2 ^ rbits T n := by positivity
  have hXpos : 0 < (n : ℝ) ^ (2 * (k - 1) * ell k T n) * ((2 : ℝ) ^ rbits T n) ^ mdeg T n *
      (n : ℝ) ^ thr T n / ((2 : ℝ) ^ rbits T n) ^ thr T n := by positivity
  rw [← log_le_iff_le_exp hXpos]
  have hlog : log ((n : ℝ) ^ (2 * (k - 1) * ell k T n) * ((2 : ℝ) ^ rbits T n) ^ mdeg T n *
      (n : ℝ) ^ thr T n / ((2 : ℝ) ^ rbits T n) ^ thr T n) =
      (((2 * (k - 1) * ell k T n : ℕ) : ℝ) + thr T n) * log n +
        ((mdeg T n : ℝ) - thr T n) * (rbits T n * log 2) := by
    rw [log_div (by positivity) (by positivity), log_mul (by positivity) (by positivity),
      log_mul (by positivity) (by positivity)]
    simp only [log_pow]
    ring
  rw [hlog]
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hxle : ((2 * (k - 1) * ell k T n : ℕ) : ℝ) ≤
      1 / (2 * (T : ℝ)) * exp (log n * (1 - 1 / (2 * (T : ℝ)))) / 2 := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
    refine le_trans ?_ hx
    exact mul_le_mul_of_nonneg_left (ell_le_log k T hn) (by positivity)
  refine log_bound_le hL (exp_pos _).le (by positivity) ?_ (log_le_rbits hT n)
    (exp_le_thr (by omega) hT) (mdeg_le_exp hT hn) hxle hab
  rw [div_le_div_iff₀ (by positivity) two_pos]
  linarith

end BHJK25.RS.NullAux
