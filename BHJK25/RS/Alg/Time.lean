module

public import BHJK25.RS.Alg.Loop
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The running time `n^{O(log^{1/(k-1)} n)}`

For a fixed `T`, the machine of the loop (`BHJK25.RS.AlgAux.loop_time`) runs after one that writes
`T` in unary in front of the input; the factor `(2T + 3)^c` that this costs goes into the constant
of `BHJK25.RunsInTime`. The rest of the bound is `(n^L + 1)(|x| + 2)^c ≤ 2 · 3^c (n + 2)^{L + kc}`,
since `|x| + 2 ≤ 3 (n + 2)^k` (`BHJK25.RS.AlgAux.time_le`). The side `ℓ` of the grid is the least
with `ℓ^{k-1} ≥ r`, so `ℓ ≤ r^{1/(k-1)} + 1`, and `2^r ≤ (n + 2)^8`, so `r ≤ 12 log (n + 2)`
(`BHJK25.RS.AlgAux.rbits_le_log`). Hence `ℓ ≤ 12 log^{1/(k-1)} (n + 2) + 1`
(`BHJK25.RS.AlgAux.ell_le_rpow_log`), and
`L + kc = 2 (k - 1) ℓ + kc ≤ C (log^{1/(k-1)} (n + 2) + 1)` for `C = 26 k + kc`, which does not
depend on `T` (`BHJK25.RS.AlgAux.pow_le_tensorTime`).
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

open Turing.MultiTapeTM

variable {k : ℕ}

/-! ### The side of the grid -/

/-- `ℓ` is the least with `ℓ^{k-1} ≥ r`. -/
theorem ell_cases (hk : 2 ≤ k) (T n : ℕ) :
    ell k T n = 0 ∨ (ell k T n - 1) ^ (k - 1) < rbits T n := by
  unfold ell
  cases h : (List.range (rbits T n + 1)).find? (fun l ↦ decide (rbits T n ≤ l ^ (k - 1))) with
  | none =>
    exfalso
    have := List.find?_eq_none.1 h (rbits T n) (List.mem_range.2 (Nat.lt_succ_self _))
    simp only [decide_eq_true_eq] at this
    exact this (Nat.le_self_pow (by omega) _)
  | some l =>
    simp only [Option.getD_some]
    obtain ⟨-, i, hi, hil, hmin⟩ := List.find?_eq_some_iff_getElem.1 h
    simp only [List.getElem_range] at hil
    subst hil
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · right
      have := hmin (i - 1) (by omega)
      simpa only [List.getElem_range, Bool.not_eq_true', decide_eq_false_iff_not, not_le]
        using this

theorem rbits_le_log (T n : ℕ) : (rbits T n : ℝ) ≤ 12 * Real.log ((n : ℝ) + 2) := by
  have hN : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
  have h1 : 2 ^ rbits T n ≤ (n + 2) ^ 8 := by
    have h3 : 64 ≤ (n + 2) ^ 6 :=
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ (n + 2) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have h4 : (2 * n + 1) ^ 2 ≤ 4 * (n + 2) ^ 2 :=
      calc (2 * n + 1) ^ 2 ≤ (2 * (n + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * (n + 2) ^ 2 := by ring
    calc 2 ^ rbits T n ≤ 16 * (2 * n + 1) ^ 2 := two_pow_rbits_le T n
      _ ≤ 16 * (4 * (n + 2) ^ 2) := Nat.mul_le_mul_left _ h4
      _ = 64 * (n + 2) ^ 2 := by ring
      _ ≤ (n + 2) ^ 6 * (n + 2) ^ 2 := Nat.mul_le_mul_right _ h3
      _ = (n + 2) ^ 8 := by ring
  have h2 : (2 : ℝ) ^ rbits T n ≤ ((n : ℝ) + 2) ^ 8 := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_pow, Real.log_pow] at h3
  have hl2 : (2 : ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hr : (0 : ℝ) ≤ rbits T n := Nat.cast_nonneg _
  have h5 : (rbits T n : ℝ) * (2 / 3) ≤ (rbits T n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hl2.le hr
  push_cast at h3
  linarith

/-- **`ℓ ≤ 12 log^{1/(k-1)} (n + 2) + 1`.** -/
theorem ell_le_rpow_log (hk : 2 ≤ k) (T n : ℕ) :
    (ell k T n : ℝ) ≤ 12 * Real.log ((n : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) + 1 := by
  have hN : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [n.cast_nonneg (α := ℝ)]
  have hlog : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg hN
  have hX : 0 ≤ Real.log ((n : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) := Real.rpow_nonneg hlog _
  have hk1 : (1 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have he : 0 < 1 / ((k : ℝ) - 1) := by positivity
  have he1 : 1 / ((k : ℝ) - 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hk1
  rcases Nat.eq_zero_or_pos (ell k T n) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    linarith
  rcases ell_cases hk T n with h | h
  · omega
  have hr : ((ell k T n - 1 : ℕ) : ℝ) ^ (k - 1) < (rbits T n : ℝ) := by exact_mod_cast h
  have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hroot : ((ell k T n - 1 : ℕ) : ℝ) < (rbits T n : ℝ) ^ (1 / ((k : ℝ) - 1)) := by
    have := Real.rpow_lt_rpow (by positivity) hr he
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), hkc,
      mul_one_div_cancel (by linarith), Real.rpow_one] at this
  have hr12 : (rbits T n : ℝ) ^ (1 / ((k : ℝ) - 1)) ≤
      12 * Real.log ((n : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) :=
    calc (rbits T n : ℝ) ^ (1 / ((k : ℝ) - 1))
        ≤ (12 * Real.log ((n : ℝ) + 2)) ^ (1 / ((k : ℝ) - 1)) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (rbits_le_log T n) he.le
      _ = 12 ^ (1 / ((k : ℝ) - 1)) * Real.log ((n : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) :=
          Real.mul_rpow (by norm_num) hlog
      _ ≤ 12 * Real.log ((n : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ hX
          calc (12 : ℝ) ^ (1 / ((k : ℝ) - 1)) ≤ 12 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) he1
            _ = 12 := Real.rpow_one 12
  have hcast : (ell k T n : ℝ) = ((ell k T n - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hpos, Nat.cast_one]
    ring
  linarith

/-! ### The bound -/

/-- **`(n + 2)^{L + kc}` is within the running time** of the theorem, for `C = 26 k + kc`. -/
theorem pow_le_tensorTime (hk : 2 ≤ k) (c T : ℕ) (x : TensorInput k) :
    (x.1 + 2) ^ ((mkDat k T x.1 (table x.2)).L + k * c) ≤ tensorTime k (26 * k + k * c) x := by
  unfold tensorTime
  set X := Real.log ((x.1 : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) with hXdef
  have hN : (1 : ℝ) ≤ (x.1 : ℝ) + 2 := by linarith [x.1.cast_nonneg (α := ℝ)]
  have hX : 0 ≤ X := Real.rpow_nonneg (Real.log_nonneg hN) _
  have hell := ell_le_rpow_log hk T x.1
  rw [← hXdef] at hell
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hL : ((mkDat k T x.1 (table x.2)).L : ℝ) = 2 * ((k : ℝ) - 1) * ell k T x.1 := by
    change ((2 * (k - 1) * ell k T x.1 : ℕ) : ℝ) = _
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega)]
    norm_num
  have hexp : ((((mkDat k T x.1 (table x.2)).L + k * c : ℕ)) : ℝ) ≤
      ((26 * k + k * c : ℕ) : ℝ) * (X + 1) := by
    push_cast
    rw [hL]
    have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    have h1 : 2 * ((k : ℝ) - 1) * ell k T x.1 ≤ 2 * ((k : ℝ) - 1) * (12 * X + 1) :=
      mul_le_mul_of_nonneg_left hell (by linarith)
    nlinarith [mul_nonneg hc hX, mul_nonneg (by linarith : (0 : ℝ) ≤ k) hX,
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ k) hc) hX]
  have h : ((((x.1 + 2) ^ ((mkDat k T x.1 (table x.2)).L + k * c) : ℕ)) : ℝ) ≤
      ((x.1 : ℝ) + 2) ^ (((26 * k + k * c : ℕ) : ℝ) * (X + 1)) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_two, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hN hexp
  exact_mod_cast h.trans (Nat.le_ceil _)

/-- **The bound of the loop is within the running time**, up to `2 · 3^c (2T + 3)^c`. -/
theorem time_le (hk : 2 ≤ k) (c T : ℕ) (x : TensorInput k) :
    (x.1 ^ (mkDat k T x.1 (table x.2)).L + 1) * ((encInp k (T, x)).length + 2) ^ c ≤
      2 * 3 ^ c * (2 * T + 3) ^ c * tensorTime k (26 * k + k * c) x := by
  set L := (mkDat k T x.1 (table x.2)).L
  have hsz := Nat.size_le_self x.1
  have hpk : x.1 + 2 ≤ (x.1 + 2) ^ k := Nat.le_self_pow (by omega) _
  have hnk : x.1 ^ k ≤ (x.1 + 2) ^ k := Nat.pow_le_pow_left (by omega) _
  have h1 : (encInp k (T, x)).length + 2 ≤ (2 * T + 3) * ((encTensor k x).length + 2) := by
    rw [length_encInp, length_encTensor]
    dsimp only
    generalize 2 * x.1.size + 1 + x.1 ^ k = E
    nlinarith
  have h2 : (encTensor k x).length + 2 ≤ 3 * (x.1 + 2) ^ k := by
    rw [length_encTensor]
    omega
  have h3 : x.1 ^ L + 1 ≤ 2 * (x.1 + 2) ^ L := by
    have := Nat.pow_le_pow_left (show x.1 ≤ x.1 + 2 by omega) L
    have := Nat.one_le_pow L (x.1 + 2) (by omega)
    omega
  calc (x.1 ^ L + 1) * ((encInp k (T, x)).length + 2) ^ c
      ≤ (2 * (x.1 + 2) ^ L) * ((2 * T + 3) * (3 * (x.1 + 2) ^ k)) ^ c :=
        Nat.mul_le_mul h3 (Nat.pow_le_pow_left (h1.trans (Nat.mul_le_mul_left _ h2)) c)
    _ = 2 * 3 ^ c * (2 * T + 3) ^ c * (x.1 + 2) ^ (L + k * c) := by
        rw [mul_pow, mul_pow, ← pow_mul, pow_add]
        ring
    _ ≤ 2 * 3 ^ c * (2 * T + 3) ^ c * tensorTime k (26 * k + k * c) x :=
        Nat.mul_le_mul_left _ (pow_le_tensorTime hk c T x)

/-! ### The running time -/

/-- **The algorithm runs in time `n^{O(log^{1/(k-1)} n)}`**, with a constant in the exponent that
does not depend on `T`. -/
theorem run_time (hk : 2 ≤ k) : ∃ C : ℕ, ∀ T : ℕ,
    RunsInTime (encTensor k) Encoding.encBool (run k T) (tensorTime k C) := by
  obtain ⟨c, hc⟩ := loop_time k (by omega)
  refine ⟨26 * k + k * c, fun T ↦ ?_⟩
  have hF : ComputableInO (fun y : Inp k ↦ run k y.1 y.2) (encInp k) encBool
      (fun y ↦ c * ((y.2.1 ^ (mkDat k y.1 y.2.1 (table y.2.2)).L + 1) *
        ((encInp k y).length + 2) ^ c))
      (fun y ↦ c * ((y.2.1 ^ (mkDat k y.1 y.2.1 (table y.2.2)).L + 1) *
        ((encInp k y).length + 2) ^ c)) :=
    ComputableInO.of_bounds hc 1 (fun _ ↦ by omega) (fun _ ↦ by omega) (fun y ↦ by simp)
  have hg : ComputableInO (fun x : TensorInput k ↦ (T, x)) (encTensor k) (encInp k) _ _ :=
    (ComputableInO.const T).prod (ComputableInO.of_eq (f := fun x ↦ x) fun _ ↦ rfl)
  obtain ⟨c', hc', -⟩ := hF.comp hg
  set K := 2 * 3 ^ c * (2 * T + 3) ^ c
  have hb : ∀ x : TensorInput k, c' * ((encTensor k x).length + (encTensor k x).length +
      c * ((x.1 ^ (mkDat k T x.1 (table x.2)).L + 1) * ((encInp k (T, x)).length + 2) ^ c) + 1) ≤
      c' * (2 + c * K) * (tensorTime k (26 * k + k * c) x + (encTensor k x).length + 1) := by
    intro x
    have h : c * ((x.1 ^ (mkDat k T x.1 (table x.2)).L + 1) * ((encInp k (T, x)).length + 2) ^ c)
        ≤ c * K * tensorTime k (26 * k + k * c) x := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left c (time_le hk c T x)
    generalize c * ((x.1 ^ (mkDat k T x.1 (table x.2)).L + 1) *
      ((encInp k (T, x)).length + 2) ^ c) = P at *
    generalize (encTensor k x).length = E at *
    generalize tensorTime k (26 * k + k * c) x = tt at *
    generalize c * K = A at *
    rw [Nat.mul_assoc]
    refine Nat.mul_le_mul_left c' ?_
    nlinarith [Nat.zero_le (A * E), Nat.zero_le A]
  exact ⟨c' * (2 + c * K), hc'.mono (fun x ↦ hb x) (fun x ↦ hb x)⟩

end BHJK25.RS.AlgAux
