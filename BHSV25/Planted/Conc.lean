module

public import BHSV25.Planted.Prob

/-!
# Concentration in random planting

[BHSV25, Lemmas 7.13–7.15] for a uniform coloring `χ : Fin n → Fin k` and a symmetric matrix `X`
with nonnegative entries, zero diagonal, rows summing to `1` and squared rows summing to at most
`s` (for a `d`-regular host, `X = A_H / d` and `s = 1 / d`). Three functions of `χ`:

* the class sizes `|χ⁻¹(a)|` (`BHSV25.Planted.cnt`), of average `n / k`;
* the weights between classes `∑_{χ x = a, χ y = b} X_xy` (`BHSV25.Planted.edg`), of average
  `n / k²`, which are the numerators of the model of the planted graph;
* the dispersions `∑_{χ x = a} (D_x(b) - 1/k)²` with `D_x(b) = ∑_{χ y = b} X_xy`
  (`BHSV25.Planted.dev`), of average at most `n s / k²`, which bound the dispersions of the model
  (the mean minimizes the sum of squares).

Changing one color changes them by at most `1`, `2` and `3`, so by McDiarmid's inequality each is
within `c n^(3/4)` of its average except on `2 exp(-2 √n) k^n ≤ k^n / n` colorings
(`BHSV25.Planted.card_bad_le`). The paper takes the deviation `O(√(n log n))`; `n^(3/4)` makes the
error terms powers of `n`, which are at most powers of `d + 1`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {n k : ℕ}

/-! ### The three functions -/

/-- The size `|χ⁻¹(a)|` of a color class. -/
noncomputable def cnt (χ : Fin n → Fin k) (a : Fin k) : ℝ := ∑ x, if χ x = a then 1 else 0

/-- The weight `∑_{χ x = a, χ y = b} X_xy` between two color classes. -/
noncomputable def edg (X : Fin n → Fin n → ℝ) (χ : Fin n → Fin k) (a b : Fin k) : ℝ :=
  ∑ x, ∑ y, if χ x = a ∧ χ y = b then X x y else 0

/-- The weight `D_x(b) = ∑_{χ y = b} X_xy` from `x` to a color class. -/
noncomputable def dwt (X : Fin n → Fin n → ℝ) (χ : Fin n → Fin k) (x : Fin n) (b : Fin k) : ℝ :=
  ∑ y, if χ y = b then X x y else 0

/-- The dispersion `∑_{χ x = a} (D_x(b) - 1/k)²` around the expected weight `1 / k`. -/
noncomputable def dev (X : Fin n → Fin n → ℝ) (χ : Fin n → Fin k) (a b : Fin k) : ℝ :=
  ∑ x, if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0

/-- The hypotheses on `X`: nonnegative, symmetric, zero diagonal, rows summing to `1`, squared rows
summing to at most `s`. -/
structure IsWeight (X : Fin n → Fin n → ℝ) (s : ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ X x y
  symm : ∀ x y, X x y = X y x
  diag : ∀ x, X x x = 0
  rowSum : ∀ x, ∑ y, X x y = 1
  sqSum : ∀ x, ∑ y, X x y ^ 2 ≤ s

/-! ### Averages -/

theorem sum_pair (hk : 0 < k) {x y : Fin n} (hxy : x ≠ y) (a b : Fin k) :
    ∑ χ : Fin n → Fin k, (if χ x = a then (1 : ℝ) else 0) * (if χ y = b then 1 else 0) =
      (k : ℝ) ^ n / k / k := by
  have := sum_mul_of_indep hk x (fun c ↦ if c = a then (1 : ℝ) else 0)
    (fun χ ↦ if χ y = b then 1 else 0) (fun χ c ↦ by
      simp only [Function.update_of_ne (Ne.symm hxy)])
  rw [this, sum_ite_eq_color hk y b]
  simp
  ring

/-- The average class size is `n / k`. -/
theorem sum_cnt (hk : 0 < k) (a : Fin k) :
    ∑ χ : Fin n → Fin k, cnt χ a = (n : ℝ) * ((k : ℝ) ^ n / k) := by
  simp only [cnt]
  rw [Finset.sum_comm]
  simp only [sum_ite_eq_color hk, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The average weight between two classes is `n / k²`. -/
theorem sum_edg (hk : 0 < k) {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s) (a b : Fin k) :
    ∑ χ : Fin n → Fin k, edg X χ a b = (n : ℝ) * ((k : ℝ) ^ n / k / k) := by
  simp only [edg]
  rw [Finset.sum_comm]
  have hpt : ∀ x y, ∑ χ : Fin n → Fin k, (if χ x = a ∧ χ y = b then X x y else 0) =
      X x y * ((k : ℝ) ^ n / k / k) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [hX.diag]
      simp
    · rw [← sum_pair hk hxy a b, mul_sum]
      refine sum_congr rfl fun χ _ ↦ ?_
      by_cases h1 : χ x = a <;> by_cases h2 : χ y = b <;> simp [h1, h2]
  have : ∀ x, ∑ χ : Fin n → Fin k, ∑ y, (if χ x = a ∧ χ y = b then X x y else 0) =
      (k : ℝ) ^ n / k / k := by
    intro x
    rw [Finset.sum_comm]
    simp only [hpt, ← sum_mul, hX.rowSum, one_mul]
  simp only [this, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem sum_sq_sub_inv (hk : 0 < k) (b : Fin k) :
    ∑ c : Fin k, ((if c = b then (1 : ℝ) else 0) - 1 / k) ^ 2 = 1 - 1 / (k : ℝ) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : ∀ c : Fin k, ((if c = b then (1 : ℝ) else 0) - 1 / k) ^ 2 =
      (1 - 2 / (k : ℝ)) * (if c = b then 1 else 0) + 1 / (k : ℝ) ^ 2 := by
    intro c
    by_cases h : c = b
    · simp only [h, ite_true]; ring
    · simp only [h, ite_false]; ring
  simp only [e, sum_add_distrib, ← mul_sum, sum_ite_eq', mem_univ, ite_true, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem sum_sub_inv (hk : 0 < k) (b : Fin k) :
    ∑ c : Fin k, ((if c = b then (1 : ℝ) else 0) - 1 / k) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [sum_sub_distrib, sum_ite_eq', ite_eq_left (mem_univ _), sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one_div_cancel hk', sub_self]

/-- The average of the product of the centered indicators at `y` and `y'` over the colorings with
`χ x = a`. -/
theorem sum_triple (hk : 0 < k) {x y y' : Fin n} (hy : y ≠ x) (hy' : y' ≠ x) (a b : Fin k) :
    ∑ χ : Fin n → Fin k, (if χ x = a then (1 : ℝ) else 0) *
        (((if χ y = b then (1 : ℝ) else 0) - 1 / k) *
          ((if χ y' = b then (1 : ℝ) else 0) - 1 / k)) =
      if y = y' then (1 - 1 / k) * ((k : ℝ) ^ n / k / k) else 0 := by
  have hg0 : ∑ c : Fin k, ((if c = b then (1 : ℝ) else 0) - 1 / k) = 0 := sum_sub_inv hk b
  have hg2 : ∑ c : Fin k, ((if c = b then (1 : ℝ) else 0) - 1 / k) ^ 2 = 1 - 1 / (k : ℝ) :=
    sum_sq_sub_inv hk b
  by_cases hyy : y = y'
  · subst hyy
    rw [ite_eq_left rfl]
    have h := sum_mul_of_indep hk y (fun c ↦ ((if c = b then (1 : ℝ) else 0) - 1 / k) ^ 2)
      (fun χ ↦ if χ x = a then (1 : ℝ) else 0)
      (fun χ c ↦ by simp only [Function.update_of_ne (Ne.symm hy)])
    rw [sum_ite_eq_color hk x a, hg2] at h
    calc _ = ∑ χ : Fin n → Fin k, ((if χ y = b then (1 : ℝ) else 0) - 1 / k) ^ 2 *
          (if χ x = a then (1 : ℝ) else 0) := sum_congr rfl fun χ _ ↦ by ring
      _ = _ := h
      _ = _ := by ring
  · rw [ite_eq_right hyy]
    have h := sum_mul_of_indep hk y' (fun c ↦ (if c = b then (1 : ℝ) else 0) - 1 / k)
      (fun χ ↦ (if χ x = a then (1 : ℝ) else 0) * ((if χ y = b then (1 : ℝ) else 0) - 1 / k))
      (fun χ c ↦ by
        simp only [Function.update_of_ne (Ne.symm hy'), Function.update_of_ne hyy])
    rw [hg0, zero_div, zero_mul] at h
    refine Eq.trans ?_ h
    exact sum_congr rfl fun χ _ ↦ by ring

theorem dwt_sub_inv {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s)
    (χ : Fin n → Fin k) (x : Fin n) (b : Fin k) :
    dwt X χ x b - 1 / k = ∑ y, X x y * ((if χ y = b then 1 else 0) - 1 / k) := by
  simp only [dwt, mul_sub, sum_sub_distrib, ← sum_mul, hX.rowSum, one_mul]
  congr 1
  refine sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> simp

/-- The average dispersion is at most `n s / k²`. -/
theorem sum_dev_le (hk : 0 < k) {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s)
    (a b : Fin k) :
    ∑ χ : Fin n → Fin k, dev X χ a b ≤ n * s * ((k : ℝ) ^ n / k / k) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hK : (0 : ℝ) ≤ (k : ℝ) ^ n / k / k := by positivity
  have hx : ∀ x, ∑ χ : Fin n → Fin k,
      (if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0) ≤ s * ((k : ℝ) ^ n / k / k) := by
    intro x
    have e1 : ∀ χ : Fin n → Fin k, (if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0) =
        ∑ y, ∑ y', X x y * X x y' * ((if χ x = a then (1 : ℝ) else 0) *
          (((if χ y = b then (1 : ℝ) else 0) - 1 / k) *
            ((if χ y' = b then (1 : ℝ) else 0) - 1 / k))) := by
      intro χ
      rw [dwt_sub_inv hX, sq, sum_mul_sum]
      by_cases h : χ x = a
      · simp only [h, ite_true, one_mul]
        exact sum_congr rfl fun y _ ↦ sum_congr rfl fun y' _ ↦ by ring
      · simp [h]
    simp only [e1]
    have e3 : ∑ χ : Fin n → Fin k, ∑ y, ∑ y', X x y * X x y' *
        ((if χ x = a then (1 : ℝ) else 0) * (((if χ y = b then (1 : ℝ) else 0) - 1 / k) *
          ((if χ y' = b then (1 : ℝ) else 0) - 1 / k))) =
        ∑ y, ∑ y', X x y * X x y' * ∑ χ : Fin n → Fin k,
          ((if χ x = a then (1 : ℝ) else 0) * (((if χ y = b then (1 : ℝ) else 0) - 1 / k) *
            ((if χ y' = b then (1 : ℝ) else 0) - 1 / k))) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun y _ ↦ ?_
      rw [Finset.sum_comm]
      simp only [mul_sum]
    rw [e3]
    -- the terms
    have e2 : ∀ y y', X x y * X x y' * ∑ χ : Fin n → Fin k, (if χ x = a then (1 : ℝ) else 0) *
        (((if χ y = b then (1 : ℝ) else 0) - 1 / k) *
          ((if χ y' = b then (1 : ℝ) else 0) - 1 / k)) =
        if y = y' then X x y ^ 2 * ((1 - 1 / k) * ((k : ℝ) ^ n / k / k)) else 0 := by
      intro y y'
      by_cases hy : y = x
      · subst hy
        rw [hX.diag]
        simp
      by_cases hy' : y' = x
      · subst hy'
        rw [hX.diag]
        by_cases hyy : y = y'
        · exact absurd hyy hy
        · simp [hyy]
      rw [sum_triple hk hy hy' a b]
      by_cases hyy : y = y'
      · subst hyy; simp only [ite_true]; ring
      · simp [hyy]
    simp only [e2]
    simp only [sum_ite_eq, mem_univ, ite_true, ← sum_mul]
    have h1 : 0 ≤ 1 - 1 / (k : ℝ) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hk1
    have h2 : 1 - 1 / (k : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / k := by positivity
      linarith
    calc (∑ y, X x y ^ 2) * ((1 - 1 / k) * ((k : ℝ) ^ n / k / k))
        ≤ s * ((1 - 1 / k) * ((k : ℝ) ^ n / k / k)) :=
          mul_le_mul_of_nonneg_right (hX.sqSum x) (by positivity)
      _ ≤ s * ((k : ℝ) ^ n / k / k) := by
          have hs : 0 ≤ s := le_trans (sum_nonneg fun y _ ↦ sq_nonneg (X x y)) (hX.sqSum x)
          refine mul_le_mul_of_nonneg_left ?_ hs
          calc (1 - 1 / k) * ((k : ℝ) ^ n / k / k) ≤ 1 * ((k : ℝ) ^ n / k / k) :=
                mul_le_mul_of_nonneg_right h2 hK
            _ = _ := one_mul _
  simp only [dev]
  rw [Finset.sum_comm]
  calc ∑ x, ∑ χ : Fin n → Fin k, (if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0)
      ≤ ∑ _x : Fin n, s * ((k : ℝ) ^ n / k / k) := sum_le_sum fun x _ ↦ hx x
    _ = n * s * ((k : ℝ) ^ n / k / k) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Bounded differences -/

theorem cnt_update (χ : Fin n → Fin k) (i : Fin n) (c a : Fin k) :
    |cnt (Function.update χ i c) a - cnt χ a| ≤ 1 := by
  have h := Cslib.Probability.hasBoundedDifferences_sum
    (score := fun (_ : Fin n) (c : Fin k) ↦ if c = a then (1 : ℝ) else 0) (c := fun _ ↦ 1)
    (fun _ c c' ↦ by split_ifs <;> simp) χ i c
  simpa [cnt] using h

theorem edg_update {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s) (χ : Fin n → Fin k)
    (i : Fin n) (c a b : Fin k) :
    |edg X (Function.update χ i c) a b - edg X χ a b| ≤ 2 := by
  set χ' := Function.update χ i c
  have hpt : ∀ x y, |(if χ' x = a ∧ χ' y = b then X x y else 0) -
      (if χ x = a ∧ χ y = b then X x y else 0)| ≤
      (if x = i then X x y else 0) + (if y = i then X x y else 0) := by
    intro x y
    have h0 := hX.nonneg x y
    by_cases hx : x = i
    · simp only [hx, ite_true]
      have : ∀ p q : Prop, [Decidable p] → [Decidable q] →
          |(if p then X i y else 0) - (if q then X i y else 0)| ≤ X i y := by
        intro p q _ _
        have := hX.nonneg i y
        split_ifs <;> simp [abs_of_nonneg this, this]
      have h1 := this (χ' i = a ∧ χ' y = b) (χ i = a ∧ χ y = b)
      have h2 : (0 : ℝ) ≤ if y = i then X i y else 0 := by split_ifs <;> simp [hX.nonneg]
      subst hx
      linarith
    by_cases hy : y = i
    · simp only [hy, ite_true, hx, ite_false, zero_add]
      have : ∀ p q : Prop, [Decidable p] → [Decidable q] →
          |(if p then X x i else 0) - (if q then X x i else 0)| ≤ X x i := by
        intro p q _ _
        have := hX.nonneg x i
        split_ifs <;> simp [abs_of_nonneg this, this]
      subst hy
      exact this _ _
    · have e1 : χ' x = χ x := Function.update_of_ne hx _ _
      have e2 : χ' y = χ y := Function.update_of_ne hy _ _
      simp [e1, e2, hx, hy]
  calc |edg X χ' a b - edg X χ a b|
      = |∑ x, ∑ y, ((if χ' x = a ∧ χ' y = b then X x y else 0) -
          (if χ x = a ∧ χ y = b then X x y else 0))| := by
        simp only [edg, ← sum_sub_distrib]
    _ ≤ ∑ x, ∑ y, |(if χ' x = a ∧ χ' y = b then X x y else 0) -
          (if χ x = a ∧ χ y = b then X x y else 0)| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ abs_sum_le_sum_abs _ _)
    _ ≤ ∑ x, ∑ y, ((if x = i then X x y else 0) + (if y = i then X x y else 0)) :=
        sum_le_sum fun x _ ↦ sum_le_sum fun y _ ↦ hpt x y
    _ = 2 := by
        simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
        rw [Finset.sum_comm]
        simp only [sum_ite_eq', mem_univ, ite_true]
        rw [hX.rowSum]
        have : ∑ x, X x i = 1 := by rw [← hX.rowSum i]; exact sum_congr rfl fun x _ ↦ hX.symm x i
        rw [this]
        norm_num

theorem dwt_nonneg {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s) (χ : Fin n → Fin k)
    (x : Fin n) (b : Fin k) : 0 ≤ dwt X χ x b :=
  sum_nonneg fun y _ ↦ by split_ifs <;> simp [hX.nonneg]

theorem dwt_le_one {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s) (χ : Fin n → Fin k)
    (x : Fin n) (b : Fin k) : dwt X χ x b ≤ 1 := by
  rw [← hX.rowSum x]
  exact sum_le_sum fun y _ ↦ by split_ifs <;> simp [hX.nonneg]

theorem dev_update (hk : 0 < k) {X : Fin n → Fin n → ℝ} {s : ℝ} (hX : IsWeight X s)
    (χ : Fin n → Fin k) (i : Fin n) (c a b : Fin k) :
    |dev X (Function.update χ i c) a b - dev X χ a b| ≤ 3 := by
  set χ' := Function.update χ i c
  have hk0 : (0 : ℝ) ≤ 1 / k := by positivity
  have hk1 : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hk)]; exact_mod_cast hk
  have hsq : ∀ χ₀ : Fin n → Fin k, ∀ x, (dwt X χ₀ x b - 1 / k) ^ 2 ≤ 1 := by
    intro χ₀ x
    have h1 := dwt_nonneg hX χ₀ x b
    have h2 := dwt_le_one hX χ₀ x b
    rw [sq_le_one_iff_abs_le_one, abs_le]
    constructor <;> linarith
  have hdw : ∀ x, x ≠ i → |dwt X χ' x b - dwt X χ x b| ≤ X x i := by
    intro x _
    have e : dwt X χ' x b - dwt X χ x b =
        (if χ' i = b then X x i else 0) - (if χ i = b then X x i else 0) := by
      simp only [dwt, ← sum_sub_distrib]
      rw [sum_eq_single i (fun y _ hy ↦ by
        rw [show χ' y = χ y from Function.update_of_ne hy _ _, sub_self]) (by simp)]
    rw [e]
    have := hX.nonneg x i
    split_ifs <;> simp [abs_of_nonneg this, this]
  have hpt : ∀ x, |(if χ' x = a then (dwt X χ' x b - 1 / k) ^ 2 else 0) -
      (if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0)| ≤
      (if x = i then 1 else 0) + 2 * X x i := by
    intro x
    have hXi := hX.nonneg x i
    by_cases hx : x = i
    · subst hx
      simp only [ite_true]
      rw [hX.diag]
      have h1 := hsq χ' x
      have h2 := hsq χ x
      have h3 : 0 ≤ (dwt X χ' x b - 1 / k) ^ 2 := sq_nonneg _
      have h4 : 0 ≤ (dwt X χ x b - 1 / k) ^ 2 := sq_nonneg _
      rw [abs_le]
      constructor <;> split_ifs <;> linarith
    · have e : χ' x = χ x := Function.update_of_ne hx _ _
      rw [e, ite_eq_right hx, zero_add]
      by_cases ha : χ x = a
      · simp only [ha, ite_true]
        have h := hdw x hx
        have e2 : (dwt X χ' x b - 1 / k) ^ 2 - (dwt X χ x b - 1 / k) ^ 2 =
            (dwt X χ' x b - dwt X χ x b) * (dwt X χ' x b + dwt X χ x b - 2 / k) := by ring
        rw [e2, abs_mul]
        have h5 : |dwt X χ' x b + dwt X χ x b - 2 / k| ≤ 2 := by
          have := dwt_nonneg hX χ' x b
          have := dwt_le_one hX χ' x b
          have := dwt_nonneg hX χ x b
          have := dwt_le_one hX χ x b
          have e3 : (2 : ℝ) / k = 2 * (1 / k) := by ring
          rw [abs_le, e3]
          constructor <;> linarith
        calc |dwt X χ' x b - dwt X χ x b| * |dwt X χ' x b + dwt X χ x b - 2 / k|
            ≤ X x i * 2 := mul_le_mul h h5 (abs_nonneg _) hXi
          _ = 2 * X x i := by ring
      · simp [ha, hXi]
  calc |dev X χ' a b - dev X χ a b|
      = |∑ x, ((if χ' x = a then (dwt X χ' x b - 1 / k) ^ 2 else 0) -
          (if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0))| := by
        simp only [dev, ← sum_sub_distrib]
    _ ≤ ∑ x, |(if χ' x = a then (dwt X χ' x b - 1 / k) ^ 2 else 0) -
          (if χ x = a then (dwt X χ x b - 1 / k) ^ 2 else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ((if x = i then 1 else 0) + 2 * X x i) := sum_le_sum fun x _ ↦ hpt x
    _ = 3 := by
        rw [sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ _), ← mul_sum]
        have : ∑ x, X x i = 1 := by rw [← hX.rowSum i]; exact sum_congr rfl fun x _ ↦ hX.symm x i
        rw [this]
        norm_num

/-! ### The bad colorings -/

/-- `n^(1/4)`, as `√√n`. -/
noncomputable def qr (n : ℕ) : ℝ := Real.sqrt (Real.sqrt n)

theorem qr_sq (n : ℕ) : qr n ^ 2 = Real.sqrt n := Real.sq_sqrt (Real.sqrt_nonneg _)

theorem qr_pos (hn : 0 < n) : 0 < qr n :=
  Real.sqrt_pos.2 (Real.sqrt_pos.2 (by exact_mod_cast hn))

/-- `2 exp(-2 √n) ≤ 1 / n`. -/
theorem two_exp_neg_le (hn : 0 < n) : 2 * Real.exp (-2 * Real.sqrt n) ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.quadratic_le_exp_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt n)
  have h2 : (2 * Real.sqrt n) ^ 2 / 2 = 2 * n := by
    rw [mul_pow, Real.sq_sqrt hn'.le]; ring
  rw [h2] at h1
  have h3 : 2 * (n : ℝ) ≤ Real.exp (2 * Real.sqrt n) := by
    have := Real.sqrt_nonneg (n : ℝ)
    linarith
  rw [show -2 * Real.sqrt n = -(2 * Real.sqrt n) by ring, Real.exp_neg, le_div_iff₀ hn']
  rw [← div_eq_mul_inv, mul_comm, ← mul_div_assoc, div_le_one (Real.exp_pos _)]
  linarith

/-- **One deviation**: a function that changes by at most `c` when one color changes is at least
`c n / n^(1/4)` away from its average on at most `k^n / n` colorings. -/
theorem card_far_le (hk : 0 < k) (hn : 0 < n) (f : (Fin n → Fin k) → ℝ) {c : ℝ} (hc : 0 < c)
    (hf : ∀ χ i a, |f (Function.update χ i a) - f χ| ≤ c) :
    ((univ.filter fun χ ↦ c * n / qr n ≤ |f χ - (∑ χ', f χ') / (k : ℝ) ^ n|).card : ℝ) ≤
      (k : ℝ) ^ n / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := qr_pos hn
  have h := card_dev_le hk f hf (ε := c * n / qr n) (by positivity)
  have he : -2 * (c * n / qr n) ^ 2 / (n * c ^ 2) = -2 * Real.sqrt n := by
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 hn').ne'
    rw [div_pow, qr_sq, mul_pow]
    field_simp
    rw [Real.sq_sqrt hn'.le]
  rw [he] at h
  refine h.trans ?_
  have := two_exp_neg_le hn
  calc 2 * Real.exp (-2 * Real.sqrt n) * (k : ℝ) ^ n ≤ 1 / n * (k : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = (k : ℝ) ^ n / n := by ring

/-- The **good colorings**: the class sizes within `n^(3/4)` of `n / k`, the weights between
classes within `2 n^(3/4)` of `n / k²`, and the dispersions within `3 n^(3/4)` of their
averages. -/
def Good (X : Fin n → Fin n → ℝ) (χ : Fin n → Fin k) : Prop :=
  (∀ a, |cnt χ a - n / k| < n / qr n) ∧ (∀ a b, |edg X χ a b - n / (k : ℝ) ^ 2| < 2 * n / qr n) ∧
    ∀ a b, |dev X χ a b - (∑ χ', dev X χ' a b) / (k : ℝ) ^ n| < 3 * n / qr n

open Classical in
/-- **Few bad colorings** [BHSV25, Lemmas 7.13–7.15]: at most `(k + 2 k²) k^n / n` colorings are
not good. -/
theorem card_not_good_le (hk : 0 < k) (hn : 0 < n) {X : Fin n → Fin n → ℝ} {s : ℝ}
    (hX : IsWeight X s) :
    ((univ.filter fun χ : Fin n → Fin k ↦ ¬ Good X χ).card : ℝ) ≤
      (k + 2 * (k : ℝ) ^ 2) * ((k : ℝ) ^ n / n) := by
  have hkn : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  set E1 : Fin k → Finset (Fin n → Fin k) := fun a ↦ univ.filter fun χ ↦
    1 * n / qr n ≤ |cnt χ a - (∑ χ', cnt χ' a) / (k : ℝ) ^ n|
  set E2 : Fin k × Fin k → Finset (Fin n → Fin k) := fun p ↦ univ.filter fun χ ↦
    2 * n / qr n ≤ |edg X χ p.1 p.2 - (∑ χ', edg X χ' p.1 p.2) / (k : ℝ) ^ n|
  set E3 : Fin k × Fin k → Finset (Fin n → Fin k) := fun p ↦ univ.filter fun χ ↦
    3 * n / qr n ≤ |dev X χ p.1 p.2 - (∑ χ', dev X χ' p.1 p.2) / (k : ℝ) ^ n|
  have hm1 : ∀ a, (∑ χ' : Fin n → Fin k, cnt χ' a) / (k : ℝ) ^ n = n / k := by
    intro a
    rw [sum_cnt hk]
    field_simp
  have hm2 : ∀ a b, (∑ χ' : Fin n → Fin k, edg X χ' a b) / (k : ℝ) ^ n = n / (k : ℝ) ^ 2 := by
    intro a b
    rw [sum_edg hk hX]
    field_simp
  have hsub : (univ.filter fun χ : Fin n → Fin k ↦ ¬ Good X χ) ⊆
      (univ.biUnion E1 ∪ univ.biUnion E2) ∪ univ.biUnion E3 := by
    intro χ hχ
    rw [mem_filter] at hχ
    simp only [Good, not_and_or, not_forall, not_lt] at hχ
    simp only [mem_union, mem_biUnion, mem_univ, true_and, E1, E2, E3, mem_filter, Prod.exists]
    rcases hχ.2 with ⟨a, ha⟩ | ⟨a, b, hab⟩ | ⟨a, b, hab⟩
    · left; left; exact ⟨a, by rw [hm1, one_mul]; exact ha⟩
    · left; right; exact ⟨a, b, by rw [hm2]; exact hab⟩
    · right; exact ⟨a, b, hab⟩
  have hc1 : ∀ a, ((E1 a).card : ℝ) ≤ (k : ℝ) ^ n / n := fun a ↦
    card_far_le hk hn (fun χ ↦ cnt χ a) one_pos fun χ i c ↦ cnt_update χ i c a
  have hc2 : ∀ p, ((E2 p).card : ℝ) ≤ (k : ℝ) ^ n / n := fun p ↦
    card_far_le hk hn (fun χ ↦ edg X χ p.1 p.2) two_pos fun χ i c ↦ edg_update hX χ i c p.1 p.2
  have hc3 : ∀ p, ((E3 p).card : ℝ) ≤ (k : ℝ) ^ n / n := fun p ↦
    card_far_le hk hn (fun χ ↦ dev X χ p.1 p.2) three_pos
      fun χ i c ↦ dev_update hk hX χ i c p.1 p.2
  have hb : ∀ {ι : Type} [Fintype ι] (E : ι → Finset (Fin n → Fin k)),
      (∀ i, ((E i).card : ℝ) ≤ (k : ℝ) ^ n / n) →
      ((univ.biUnion E).card : ℝ) ≤ Fintype.card ι * ((k : ℝ) ^ n / n) := by
    intro ι _ E hE
    calc ((univ.biUnion E).card : ℝ) ≤ ∑ i, ((E i).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _i : ι, (k : ℝ) ^ n / n := sum_le_sum fun i _ ↦ hE i
      _ = Fintype.card ι * ((k : ℝ) ^ n / n) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
  have h1 := hb E1 hc1
  have h2 := hb E2 hc2
  have h3 := hb E3 hc3
  simp only [Fintype.card_fin, Fintype.card_prod, Nat.cast_mul] at h1 h2 h3
  calc ((univ.filter fun χ : Fin n → Fin k ↦ ¬ Good X χ).card : ℝ)
      ≤ (((univ.biUnion E1 ∪ univ.biUnion E2) ∪ univ.biUnion E3).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ (univ.biUnion E1).card + (univ.biUnion E2).card + (univ.biUnion E3).card := by
        have := card_union_le (univ.biUnion E1 ∪ univ.biUnion E2) (univ.biUnion E3)
        have := card_union_le (univ.biUnion E1) (univ.biUnion E2)
        exact_mod_cast (by omega)
    _ ≤ (k + 2 * (k : ℝ) ^ 2) * ((k : ℝ) ^ n / n) := by nlinarith

end Planted

end BHSV25
