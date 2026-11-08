module

public import BHJK25.RS.Planted.Good
public import BHJK25.RS.Planted.Params

/-!
# The two failure probabilities

* **Few clean columns** (`BHJK25.RS.PlantedAux.probFewClean_le`): the cells of distinct columns
  are disjoint, so `Pr_e[#clean < a] ≤ 2^a exp(-ρ N / 2)`, with `N` columns and
  `ρ = (1 - ε/2)^(2r)`. With `a = 3t`, `t ≤ 3H + 2`, `N ≥ n/2` and
  `ρ ≥ exp(-0.49 L/T - 3/2)`, this is at most `exp(-n^(1 - 1/T)) / 2` once
  `exp(L/(100 T)) ≥ 34 exp(3/2)` (`L = log n`, `H = n^(1 - 1/(2T))`).
* **Many repeated values** (`BHJK25.RS.PlantedAux.probManyDup_le`): `#repeated ≥ 2t` forces at
  least `t` columns repeating an earlier one, which has probability at most
  `C(N, t) n^t / q^t ≤ (n² / q)^t / t! ≤ (e n² / (t q))^t ≤ 4^(-t)`, since `12 n² ≤ t q`; and
  `4^(-t) ≤ exp(-n^(1 - 1/T)) / 2` since `t ≥ n^(1 - 1/T) + 1`.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Finset Real

variable {k T n : ℕ}

/-! ### Few clean columns -/

/-- The columns of the layout are disjoint from its `2 (k - 1) ℓ` vertices. -/
theorem card_cols_ge (h : 2 * (k - 1) * ell k T n < n) :
    n ≤ (cols h).card + 2 * (k - 1) * ell k T n := by
  have h1 : (univ.filter fun v ↦ ¬ ∀ s b t, layout h s b t ≠ v) ⊆
      univ.image fun x : Fin 2 × Fin (k - 1) × Fin (ell k T n) ↦ layout h x.1 x.2.1 x.2.2 := by
    intro v hv
    simp only [mem_filter, mem_univ, true_and, not_forall, not_not] at hv
    obtain ⟨s, b, t, hv⟩ := hv
    exact mem_image.2 ⟨(s, b, t), mem_univ _, hv⟩
  have h2 := (card_le_card h1).trans card_image_le
  have h3 := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    fun v ↦ ∀ s b t, layout h s b t ≠ v
  rw [card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin] at h2
  rw [card_univ, Fintype.card_fin] at h3
  have h4 : (cols h).card = (univ.filter fun v ↦ ∀ s b t, layout h s b t ≠ v).card := rfl
  rw [h4]
  have h5 : 2 * (k - 1) * ell k T n = 2 * ((k - 1) * ell k T n) := by ring
  omega

/-- `Pr_e[#clean < a] ≤ 2^a exp(-ρ N / 2)`. -/
theorem probFewClean_le (h : 2 * (k - 1) * ell k T n < n) {ε : ℝ} (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2)
    (a : ℕ) : probFewClean h ε a ≤
      2 ^ a * exp (-((1 - ε / 2) ^ (2 * rbits T n) * (cols h).card / 2)) := by
  have hp0 : 0 ≤ ε / 2 := by linarith
  have hp1 : ε / 2 ≤ 1 := by linarith
  have hdisj : ((cols h : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint (cellSet (layout h)) :=
    fun v hv _ _ hvw ↦ cellSet_disjoint (mem_cols.1 hv) hvw
  have h1 := sum_flipW_card_lt hp0 hp1 (cols h) (cellSet (layout h)) hdisj a
  have hq0 : 0 ≤ 1 - ε / 2 := by linarith
  have hq1 : 1 - ε / 2 ≤ 1 := by linarith
  have h2 := prod_one_sub_le_exp (cols := cols h)
    (ρ := fun v ↦ (1 - ε / 2) ^ (cellSet (layout h) v).card)
    (ρ₀ := (1 - ε / 2) ^ (2 * rbits T n))
    (fun v _ ↦ pow_le_pow_of_le_one hq0 hq1 (card_cellSet_le _ v))
    (fun v _ ↦ pow_le_one₀ hq0 hq1)
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))

/-- The arithmetic of the clean-column bound. -/
theorem clean_tail {t : ℕ} {Z H ρ N x L : ℝ} (ht : (t : ℝ) ≤ 3 * H + 2) (hZH : Z ≤ H)
    (hH5 : 5 ≤ H) (hx : 0 ≤ x) (hN : x / 2 ≤ N) (hρ : exp (-(49 / 100 * L) - 3 / 2) ≤ ρ)
    (hHx : H = x * exp (-(L / 2))) (hL : 34 * exp (3 / 2) ≤ exp (L / 100)) :
    (2 : ℝ) ^ (3 * t) * exp (-(ρ * N / 2)) ≤ exp (-Z) / 2 := by
  have hl1 := log_two_lt_d9
  have hl2 := log_two_gt_d9
  have hexp1 : exp (-(49 / 100 * L) - 3 / 2) = exp (-(L / 2)) * (exp (L / 100) * exp (-(3 / 2)))
      := by
    rw [← exp_add, ← exp_add]
    congr 1
    ring
  have h34 : 34 ≤ exp (L / 100) * exp (-(3 / 2)) := by
    rw [exp_neg, le_mul_inv_iff₀ (exp_pos _)]
    exact hL
  have hkey : 34 * H ≤ x * exp (-(49 / 100 * L) - 3 / 2) := by
    rw [hexp1, hHx, ← mul_assoc]
    have hpos : 0 ≤ x * exp (-(L / 2)) := by positivity
    nlinarith
  have hρ0 : 0 ≤ ρ := (exp_pos _).le.trans hρ
  have hρN : 34 * H / 4 ≤ ρ * N / 2 := by
    calc 34 * H / 4 ≤ x * exp (-(49 / 100 * L) - 3 / 2) / 4 := by linarith
      _ ≤ x * ρ / 4 := by gcongr
      _ = ρ * (x / 2) / 2 := by ring
      _ ≤ ρ * N / 2 := by gcongr
  have h2pow : (2 : ℝ) ^ (3 * t) = exp ((3 * t : ℕ) * log 2) := by
    rw [exp_nat_mul, exp_log two_pos]
  rw [h2pow, ← exp_add, ← exp_log (two_pos : (0 : ℝ) < 2), ← exp_sub, exp_log two_pos]
  apply exp_le_exp.2
  push_cast
  nlinarith

/-! ### Many repeated values -/

/-- `Pr_α[#repeated ≥ 2t] ≤ C(N, t) n^t / q^t`. -/
theorem probManyDup_le (h : 2 * (k - 1) * ell k T n < n) (t : ℕ) :
    probManyDup h (2 * t) ≤
      ((cols h).card.choose t : ℝ) * n ^ t / (Fintype.card (Fld T n) : ℝ) ^ t := by
  set q := Fintype.card (Fld T n)
  have hq : (0 : ℝ) < q := by exact_mod_cast Fintype.card_pos
  have hcardF : (Fintype.card (Fin n → Fld T n) : ℝ) = (q : ℝ) ^ n := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    rfl
  have h1 : probManyDup h (2 * t) ≤ ((q : ℝ) ^ n)⁻¹ *
      ((univ.filter fun α : Fin n → Fld T n ↦ t ≤ (laterCols (cols h) α).card).card : ℝ) := by
    rw [probManyDup, hcardF]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← sum_boole]
    refine sum_le_sum fun α _ ↦ ?_
    by_cases hd : 2 * t ≤ (dupCols (cols h) α).card
    · have := card_dupCols_le (cols h) α
      rw [ite_eq_left hd, ite_eq_left (by omega)]
    · rw [ite_eq_right hd]
      split_ifs <;> norm_num
  have h2 := card_laterCols_le (F := Fld T n) (cols h) t
  have h2' : ((univ.filter fun α : Fin n → Fld T n ↦ t ≤ (laterCols (cols h) α).card).card : ℝ) *
      (q : ℝ) ^ t ≤ ((cols h).card.choose t : ℝ) * n ^ t * (q : ℝ) ^ n := by
    exact_mod_cast h2
  refine h1.trans ?_
  rw [inv_mul_le_iff₀ (by positivity), mul_div_assoc', le_div_iff₀ (by positivity)]
  linarith

/-- The arithmetic of the repeated-value bound. -/
theorem dup_tail {t N n q : ℕ} {Z : ℝ} (hNn : N ≤ n) (htq : 12 * n ^ 2 ≤ t * q)
    (hZt : Z + 1 ≤ t) (hZ : 0 ≤ Z) (hq : 0 < q) :
    (N.choose t : ℝ) * n ^ t / (q : ℝ) ^ t ≤ exp (-Z) / 2 := by
  have ht : (0 : ℝ) < t := by linarith
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hfac : (0 : ℝ) < t.factorial := by exact_mod_cast t.factorial_pos
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (n : ℝ) ^ 2 / q := ⟨_, rfl⟩
  have h1 : (N.choose t : ℝ) * n ^ t / (q : ℝ) ^ t ≤ a ^ t / t.factorial := by
    have hc : (N.choose t : ℝ) ≤ (n : ℝ) ^ t / t.factorial :=
      (Nat.choose_le_pow_div t N).trans (by gcongr)
    calc (N.choose t : ℝ) * n ^ t / (q : ℝ) ^ t ≤ (n : ℝ) ^ t / t.factorial * n ^ t / q ^ t := by
          gcongr
      _ = a ^ t / t.factorial := by
          rw [ha, div_pow, ← pow_mul, mul_comm 2 t, pow_mul]
          field_simp
  have h2 : a ^ t / t.factorial ≤ (a * exp 1 / t) ^ t := by
    have hfe := pow_div_factorial_le_exp (t : ℝ) ht.le t
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have htt : (0 : ℝ) < (t : ℝ) ^ t := by positivity
    have e1 : (a * exp 1 / t) ^ t = a ^ t * exp t / (t : ℝ) ^ t := by
      rw [div_pow, mul_pow, exp_one_pow]
    rw [e1, le_div_iff₀ htt]
    calc a ^ t / t.factorial * (t : ℝ) ^ t = a ^ t * ((t : ℝ) ^ t / t.factorial) := by ring
      _ ≤ a ^ t * exp t := mul_le_mul_of_nonneg_left hfe (by positivity)
  have h3 : a * exp 1 / t ≤ 1 / 4 := by
    have he := exp_one_lt_d9
    have htq' : (12 : ℝ) * n ^ 2 ≤ t * q := by exact_mod_cast htq
    rw [div_le_iff₀ ht, ha, div_mul_eq_mul_div, div_le_iff₀ hq']
    have hn2 : (0 : ℝ) ≤ n ^ 2 := by positivity
    nlinarith
  have h4 : ((1 : ℝ) / 4) ^ t ≤ exp (-Z) / 2 := by
    have hl2 := log_two_gt_d9
    have h14 : (1 : ℝ) / 4 = exp (-(2 * log 2)) := by
      rw [exp_neg, two_mul, exp_add, exp_log two_pos]
      norm_num
    rw [h14, ← exp_nat_mul, ← exp_log (two_pos : (0 : ℝ) < 2), ← exp_sub, exp_log two_pos]
    apply exp_le_exp.2
    nlinarith
  calc _ ≤ a ^ t / t.factorial := h1
    _ ≤ (a * exp 1 / t) ^ t := h2
    _ ≤ ((1 : ℝ) / 4) ^ t := pow_le_pow_left₀ (by rw [ha]; positivity) h3 t
    _ ≤ exp (-Z) / 2 := h4

end BHJK25.RS.PlantedAux
