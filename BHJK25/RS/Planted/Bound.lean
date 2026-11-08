module

public import BHJK25.RS.Planted.Tail

/-!
# The planted bound for a fixed large `n`

For `n ≥ 2` with `log n ≥ 3600 T` and `4 (k - 1) (3 log n + 7) ≤ n`, the layout exists, it has at
least `n/2` columns, and the two failure probabilities are each at most `exp(-n^(1 - 1/T)) / 2`.
Both conditions hold for all large `n`.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Finset Real Filter

variable {k T : ℕ}

/-- **The planted bound for a fixed large `n`.** -/
theorem planted_bound_at (hk : 2 ≤ k) (hT : 1 ≤ T) {ε : ℝ} (hε : 0 < ε) (hεT : ε * T ≤ 1 / 5)
    {n : ℕ} (hn : 2 ≤ n) (hlog : 3600 * (T : ℝ) ≤ log n)
    (hK : 4 * ((k - 1 : ℕ) : ℝ) * (3 * log n + 7) ≤ n) :
    1 - exp (-(n : ℝ) ^ (1 - 1 / (T : ℝ))) ≤
      noisyProb ε (planted k T n) (fun M ↦ Accept k T n M) := by
  classical
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hε1 : ε ≤ 1 / 5 := by nlinarith
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hl0 : 0 ≤ log (n : ℝ) := log_natCast_nonneg n
  -- The layout exists and has at least `n / 2` columns.
  set K1 : ℝ := ((k - 1 : ℕ) : ℝ) with hK1
  have hK10 : 0 ≤ K1 := Nat.cast_nonneg _
  have hell := ell_le_log k T hn
  have hlay : (((2 * (k - 1) * ell k T n : ℕ)) : ℝ) ≤ n / 2 := by
    have h1 : K1 * ell k T n ≤ K1 * (3 * log n + 7) := mul_le_mul_of_nonneg_left hell hK10
    push_cast
    rw [← hK1]
    linarith
  have h : 2 * (k - 1) * ell k T n < n := by
    have : (((2 * (k - 1) * ell k T n : ℕ)) : ℝ) < n := by linarith
    exact_mod_cast this
  have hN : (n : ℝ) / 2 ≤ (cols h).card := by
    have h1 : (n : ℝ) ≤ ((((cols h).card + 2 * (k - 1) * ell k T n : ℕ)) : ℝ) := by
      exact_mod_cast card_cols_ge h
    rw [Nat.cast_add] at h1
    linarith
  -- The parameters.
  set Z := exp (log n * (1 - 1 / (T : ℝ))) with hZdef
  have hZ : (n : ℝ) ^ (1 - 1 / (T : ℝ)) = Z := rpow_def_of_pos hnpos _
  set H := exp (log n * (1 - 1 / (2 * T : ℝ))) with hHdef
  set L := log n / T with hLdef
  have hHx : H = n * exp (-(L / 2)) := by
    have h1 : H = exp (log n) * exp (-(L / 2)) := by
      rw [hHdef, hLdef, ← exp_add]
      congr 1
      field_simp
      ring
    rw [h1, exp_log hnpos]
  have hZH : Z ≤ H := by
    apply exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ hl0
    have : 1 / (2 * T : ℝ) ≤ 1 / T := by
      apply one_div_le_one_div_of_le hTpos
      linarith
    linarith
  have hlogT : 3600 ≤ L := by
    rw [hLdef, le_div_iff₀ hTpos]
    linarith
  have hH5 : 5 ≤ H := by
    have h1 : log n / 2 ≤ log n * (1 - 1 / (2 * T : ℝ)) := by
      have : 1 / (2 * T : ℝ) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        linarith
      nlinarith
    have h2 : (4 : ℝ) ≤ log n / 2 := by
      have : (3600 : ℝ) ≤ log n := by nlinarith
      linarith
    have h3 := add_one_le_exp 4
    calc (5 : ℝ) = 4 + 1 := by norm_num
      _ ≤ exp 4 := h3
      _ ≤ H := exp_le_exp.2 (h2.trans h1)
  have hL : 34 * exp (3 / 2) ≤ exp (L / 100) := by
    have h1 : exp (L / 100) = exp (3 / 2) * exp (L / 100 - 3 / 2) := by
      rw [← exp_add]
      congr 1
      ring
    have h2 := add_one_le_exp (L / 100 - 3 / 2)
    rw [h1]
    have h3 : (0 : ℝ) < exp (3 / 2) := exp_pos _
    nlinarith
  have hρ : exp (-(49 / 100 * L) - 3 / 2) ≤ (1 - ε / 2) ^ (2 * rbits T n) := by
    have h1 := exp_le_escape hT hn hε hεT
    have h2 : 49 / 100 * log n / T = 49 / 100 * L := by rw [hLdef]; ring
    rwa [h2] at h1
  have ht1 := exp_add_one_le_thr hT (by omega : 1 ≤ n)
  have ht2 := thr_le_exp hT hn
  have htq := thr_mul_card hT n
  -- The two failure probabilities.
  have hPA : probFewClean h ε (3 * thr T n) ≤ exp (-Z) / 2 :=
    (probFewClean_le h hε.le (by linarith) _).trans
      (clean_tail ht2 hZH hH5 hnpos.le hN hρ hHx hL)
  have hPB : probManyDup h (2 * thr T n) ≤ exp (-Z) / 2 := by
    refine (probManyDup_le h _).trans ?_
    rw [card_fld]
    exact dup_tail ((card_le_univ _).trans_eq (Fintype.card_fin n)) htq ht1 (exp_pos _).le
      (Nat.two_pow_pos _)
  calc 1 - exp (-(n : ℝ) ^ (1 - 1 / (T : ℝ))) = 1 - exp (-Z) := by rw [hZ]
    _ ≤ 1 - probFewClean h ε (3 * thr T n) - probManyDup h (2 * thr T n) := by linarith
    _ ≤ _ := accept_prob_ge hk h hε.le (by linarith)
    _ ≤ _ := le_noisyProb_planted h hε.le (by linarith)

end BHJK25.RS.PlantedAux
