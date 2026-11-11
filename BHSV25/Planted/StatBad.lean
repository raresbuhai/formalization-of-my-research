module

public import BHSV25.Planted.Prob
public import BHSV25.Spectral.Basic
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Statistically bad vertices

[BHSV25, Definition B.13 and Lemma B.14] for a `d`-regular host: a vertex `x` is **statistically
bad** under the colors `χ` (`BHSV25.Planted.badSet`) if for some color `a ≠ χ(x)` fewer than
`d / (2k)` of its neighbors have the color `a`. With probability at least `1 - O_{k,α}(1/n)`, at
most `α n` vertices are bad, when `4 k e^(-d / (2k²)) ≤ α` (`BHSV25.Planted.card_many_bad_le`).

* A vertex is bad for a color with probability at most `2 e^(-d/(2k²))`, by Hoeffding's
  inequality for the `d` neighbors (McDiarmid's inequality with one coordinate per neighbor), so at
  most `2 k n e^(-d/(2k²)) ≤ α n / 2` vertices are bad on average.
* If `(d + 1)⁴ > n`, Markov's inequality: `e^(-d/(2k²)) ≤ 24 (2k²/d)⁴ = O_k(1/n)`.
* If `(d + 1)⁴ ≤ n`, McDiarmid's inequality for the number of bad vertices, which changes by at most
  `d + 1` when one color changes: more than `α n` bad vertices is `α n / 2` above the average, on
  at most `2 e^(-α² n / (2 (d + 1)²)) k^n ≤ 16 k^n / (α⁴ n)` colorings.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {H : Graph} {k : ℕ}

open Classical in
/-- The number of neighbors of `x` with the color `a`. -/
noncomputable def nbrCol (H : Graph) (χ : Fin H.1 → Fin k) (x : Fin H.1) (a : Fin k) : ℕ :=
  (univ.filter fun y ↦ H.2.Adj x y ∧ χ y = a).card

open Classical in
/-- The **statistically bad** vertices: those with fewer than `d / (2k)` neighbors of some other
color. -/
noncomputable def badSet (H : Graph) (d : ℕ) (χ : Fin H.1 → Fin k) : Finset (Fin H.1) :=
  univ.filter fun x ↦ ∃ a : Fin k, a ≠ χ x ∧ 2 * k * nbrCol H χ x a < d

/-! ### One vertex -/

open Classical in
theorem nbrCol_eq_sum (χ : Fin H.1 → Fin k) (x : Fin H.1) (a : Fin k) :
    (nbrCol H χ x a : ℝ) =
      ∑ y, (if H.2.Adj x y then 1 else 0) * (if χ y = a then (1 : ℝ) else 0) := by
  rw [nbrCol, card_eq_sum_ones, sum_filter]
  push_cast
  refine sum_congr rfl fun y _ ↦ ?_
  by_cases h1 : H.2.Adj x y <;> by_cases h2 : χ y = a <;> simp [h1, h2]

open Classical in
theorem nbrCol_update (χ : Fin H.1 → Fin k) (x : Fin H.1) (a : Fin k) (i : Fin H.1) (c : Fin k) :
    |(nbrCol H (Function.update χ i c) x a : ℝ) - nbrCol H χ x a| ≤
      if H.2.Adj x i then 1 else 0 := by
  rw [nbrCol_eq_sum, nbrCol_eq_sum, ← sum_sub_distrib]
  rw [sum_eq_single i (fun y _ hy ↦ by rw [Function.update_of_ne hy, sub_self]) (by simp)]
  rw [Function.update_self]
  by_cases h1 : H.2.Adj x i <;> simp only [h1, ite_true, ite_false, one_mul, zero_mul, sub_self,
    abs_zero, le_refl]
  split_ifs <;> norm_num

open Classical in
theorem sum_nbrCol {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hk : 0 < k) (x : Fin H.1)
    (a : Fin k) :
    ∑ χ : Fin H.1 → Fin k, (nbrCol H χ x a : ℝ) = d * ((k : ℝ) ^ H.1 / k) := by
  simp only [nbrCol_eq_sum]
  rw [Finset.sum_comm]
  simp only [← mul_sum, sum_ite_eq_color hk]
  rw [← sum_mul]
  congr 1
  rw [sum_boole]
  have := hreg x
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter] at this
  exact_mod_cast this

open Classical in
/-- A vertex is bad for the color `a` on at most `2 e^(-d/(2k²)) k^n` colorings. -/
theorem card_bad_one_le {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) (hk : 0 < k)
    (x : Fin H.1) (a : Fin k) :
    ((univ.filter fun χ : Fin H.1 → Fin k ↦ 2 * k * nbrCol H χ x a < d).card : ℝ) ≤
      2 * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) * (k : ℝ) ^ H.1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hkn : (0 : ℝ) < (k : ℝ) ^ H.1 := by positivity
  have h := card_dev_le' hk (fun χ ↦ (nbrCol H χ x a : ℝ))
    (fun i ↦ if H.2.Adj x i then 1 else 0) (fun χ i c ↦ nbrCol_update χ x a i c)
    (ε := d / (2 * k)) (by positivity)
  have hc : ∑ i, (if H.2.Adj x i then (1 : ℝ) else 0) ^ 2 = d := by
    have e : ∀ i, (if H.2.Adj x i then (1 : ℝ) else 0) ^ 2 = if H.2.Adj x i then 1 else 0 :=
      fun i ↦ by split_ifs <;> norm_num
    simp only [e]
    rw [sum_boole]
    have := hreg x
    rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter] at this
    rw [this]
  rw [hc, sum_nbrCol hreg hk] at h
  have he : -2 * ((d : ℝ) / (2 * k)) ^ 2 / d = -(d : ℝ) / (2 * (k : ℝ) ^ 2) := by
    field_simp
  rw [he] at h
  have hmean : d * ((k : ℝ) ^ H.1 / k) / (k : ℝ) ^ H.1 = d / k := by field_simp
  rw [hmean] at h
  have hsub : (univ.filter fun χ : Fin H.1 → Fin k ↦ 2 * k * nbrCol H χ x a < d) ⊆
      univ.filter fun χ ↦ (d : ℝ) / (2 * k) ≤ |(nbrCol H χ x a : ℝ) - d / k| := by
    intro χ hχ
    rw [mem_filter] at hχ ⊢
    refine ⟨mem_univ _, ?_⟩
    have h1 : (2 * k * nbrCol H χ x a : ℝ) < d := by exact_mod_cast hχ.2
    rw [abs_sub_comm, le_abs]
    left
    have : (nbrCol H χ x a : ℝ) < d / (2 * k) := by
      rw [lt_div_iff₀ (by positivity)]; linarith
    have e2 : (d : ℝ) / k = d / (2 * k) + d / (2 * k) := by field_simp; ring
    linarith
  exact le_trans (by exact_mod_cast card_le_card hsub) h

/-! ### The number of bad vertices -/

open Classical in
/-- On average at most `2 k n e^(-d/(2k²))` vertices are bad. -/
theorem sum_card_badSet_le {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) (hk : 0 < k) :
    ∑ χ : Fin H.1 → Fin k, ((badSet H d χ).card : ℝ) ≤
      H.1 * (k * (2 * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) * (k : ℝ) ^ H.1)) := by
  have h1 : ∀ χ : Fin H.1 → Fin k, ((badSet H d χ).card : ℝ) =
      ∑ x, if x ∈ badSet H d χ then 1 else 0 := fun χ ↦ by
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x, ∑ χ : Fin H.1 → Fin k, (if x ∈ badSet H d χ then (1 : ℝ) else 0) ≤
      k * (2 * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) * (k : ℝ) ^ H.1) := by
    intro x
    rw [sum_boole]
    have hsub : (univ.filter fun χ : Fin H.1 → Fin k ↦ x ∈ badSet H d χ) ⊆
        univ.biUnion fun a : Fin k ↦
          univ.filter fun χ : Fin H.1 → Fin k ↦ 2 * k * nbrCol H χ x a < d := by
      intro χ hχ
      rw [mem_filter, badSet, mem_filter] at hχ
      obtain ⟨a, -, ha⟩ := hχ.2.2
      exact mem_biUnion.2 ⟨a, mem_univ _, mem_filter.2 ⟨mem_univ _, ha⟩⟩
    calc ((univ.filter fun χ : Fin H.1 → Fin k ↦ x ∈ badSet H d χ).card : ℝ)
        ≤ ∑ a : Fin k, ((univ.filter fun χ : Fin H.1 → Fin k ↦
            2 * k * nbrCol H χ x a < d).card : ℝ) := by
          exact_mod_cast (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ _a : Fin k, 2 * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) * (k : ℝ) ^ H.1 :=
          sum_le_sum fun a _ ↦ card_bad_one_le hreg hd hk x a
      _ = k * (2 * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) * (k : ℝ) ^ H.1) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc ∑ x, ∑ χ : Fin H.1 → Fin k, (if x ∈ badSet H d χ then (1 : ℝ) else 0)
      ≤ ∑ _x : Fin H.1, k * (2 * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) * (k : ℝ) ^ H.1) :=
        sum_le_sum fun x _ ↦ h2 x
    _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

open Classical in
/-- Changing one color changes the number of bad vertices by at most `d + 1`. -/
theorem card_badSet_update {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (χ : Fin H.1 → Fin k)
    (i : Fin H.1) (c : Fin k) :
    |((badSet H d (Function.update χ i c)).card : ℝ) - (badSet H d χ).card| ≤ d + 1 := by
  set χ' := Function.update χ i c
  have hsame : ∀ x, x ≠ i → ¬ H.2.Adj x i → (x ∈ badSet H d χ' ↔ x ∈ badSet H d χ) := by
    intro x hx hxi
    have e1 : χ' x = χ x := Function.update_of_ne hx _ _
    have e2 : ∀ a, nbrCol H χ' x a = nbrCol H χ x a := by
      intro a
      simp only [nbrCol]
      congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        have hy : y ≠ i := fun h ↦ hxi (h ▸ h1)
        exact ⟨h1, by rw [← h2]; exact (Function.update_of_ne hy _ _).symm⟩
      · rintro ⟨h1, h2⟩
        have hy : y ≠ i := fun h ↦ hxi (h ▸ h1)
        exact ⟨h1, by rw [← h2]; exact Function.update_of_ne hy _ _⟩
    simp only [badSet, mem_filter, mem_univ, true_and, e1, e2]
  have h1 : ∀ χ₀ : Fin H.1 → Fin k, ((badSet H d χ₀).card : ℝ) =
      ∑ x, if x ∈ badSet H d χ₀ then 1 else 0 := fun χ₀ ↦ by
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
  rw [h1, h1, ← sum_sub_distrib]
  calc |∑ x, ((if x ∈ badSet H d χ' then (1 : ℝ) else 0) - if x ∈ badSet H d χ then 1 else 0)|
      ≤ ∑ x, |(if x ∈ badSet H d χ' then (1 : ℝ) else 0) - if x ∈ badSet H d χ then 1 else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, ((if x = i then 1 else 0) + if H.2.Adj x i then (1 : ℝ) else 0) := by
        refine sum_le_sum fun x _ ↦ ?_
        by_cases hx : x = i
        · simp only [hx, ite_true]
          have : 0 ≤ (if H.2.Adj i i then (1 : ℝ) else 0) := by split_ifs <;> norm_num
          have : |(if i ∈ badSet H d χ' then (1 : ℝ) else 0) - if i ∈ badSet H d χ then 1 else 0|
              ≤ 1 := by split_ifs <;> norm_num
          linarith
        by_cases hxi : H.2.Adj x i
        · simp only [hx, hxi, ite_true, ite_false, zero_add]
          split_ifs <;> norm_num
        · have hiff := hsame x hx hxi
          simp only [hx, hxi, ite_false, add_zero]
          by_cases hb : x ∈ badSet H d χ
          · rw [ite_eq_left (hiff.2 hb), ite_eq_left hb]; simp
          · rw [ite_eq_right (fun h ↦ hb (hiff.1 h)), ite_eq_right hb]; simp
    _ = d + 1 := by
        rw [sum_add_distrib, sum_ite_eq', ite_eq_left (mem_univ _), sum_boole]
        have := hreg i
        rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
          at this
        have e : (univ.filter fun x ↦ H.2.Adj x i) = univ.filter (H.2.Adj i) := by
          ext x; simp [H.2.adj_comm]
        rw [e, this]
        ring

/-! ### Many bad vertices are unlikely -/

theorem exp_neg_le_two_div_sq {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  simp only [Nat.factorial] at h
  norm_num at h
  nlinarith

theorem exp_neg_le_div_pow_four {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 24 / y ^ 4 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 4
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  simp only [Nat.factorial] at h
  norm_num at h
  nlinarith

open Classical in
/-- **Few bad vertices** [BHSV25, Lemma B.14]: if `4 k e^(-d/(2k²)) ≤ α`, more than `α n` vertices
are bad on at most `(16 / α⁴ + 12288 k⁹ / α) k^n / n` colorings. -/
theorem card_many_bad_le {d : ℕ} (hreg : H.2.IsRegularOfDegree d) (hd : d ≠ 0) (hk : 0 < k)
    (hn : 0 < H.1) {α : ℝ} (hα : 0 < α)
    (hdα : 4 * k * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) ≤ α) :
    ((univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card).card : ℝ) ≤
      (16 / α ^ 4 + 12288 * (k : ℝ) ^ 9 / α) * ((k : ℝ) ^ H.1 / H.1) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hnR : (0 : ℝ) < H.1 := by exact_mod_cast hn
  have hkn : (0 : ℝ) < (k : ℝ) ^ H.1 := by positivity
  set e := Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hsum := sum_card_badSet_le hreg hd hk (H := H)
  rw [← he] at hsum
  have hC : 0 ≤ 16 / α ^ 4 := by positivity
  have hC' : 0 ≤ 12288 * (k : ℝ) ^ 9 / α := by positivity
  by_cases hcase : H.1 < (d + 1) ^ 4
  · -- Markov's inequality
    have hmk : ((univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card).card : ℝ) *
        (α * H.1) ≤ ∑ χ : Fin H.1 → Fin k, ((badSet H d χ).card : ℝ) := by
      calc ((univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card).card : ℝ) *
            (α * H.1) = ∑ _χ ∈ univ.filter fun χ : Fin H.1 → Fin k ↦
              α * H.1 < (badSet H d χ).card, α * H.1 := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ χ ∈ univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card,
              ((badSet H d χ).card : ℝ) := sum_le_sum fun χ hχ ↦ (mem_filter.1 hχ).2.le
        _ ≤ ∑ χ : Fin H.1 → Fin k, ((badSet H d χ).card : ℝ) :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity
    -- `e ≤ 6144 k⁸ / n`
    have hd4 : (H.1 : ℝ) < 16 * (d : ℝ) ^ 4 := by
      have h1 : (H.1 : ℝ) < ((d : ℝ) + 1) ^ 4 := by exact_mod_cast hcase
      have h2 : ((d : ℝ) + 1) ^ 4 ≤ (2 * d) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      nlinarith
    have hy : 0 < (d : ℝ) / (2 * (k : ℝ) ^ 2) := by positivity
    have he1 : e ≤ 24 / ((d : ℝ) / (2 * (k : ℝ) ^ 2)) ^ 4 := by
      rw [he, neg_div]; exact exp_neg_le_div_pow_four hy
    have he2 : 24 / ((d : ℝ) / (2 * (k : ℝ) ^ 2)) ^ 4 ≤ 6144 * (k : ℝ) ^ 8 / H.1 := by
      rw [div_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hnR]
      have : (2 * (k : ℝ) ^ 2) ^ 4 = 16 * (k : ℝ) ^ 8 := by ring
      rw [this]
      nlinarith [pow_pos hkR 8]
    have hb : ((univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card).card : ℝ) ≤
        12288 * (k : ℝ) ^ 9 / α * ((k : ℝ) ^ H.1 / H.1) := by
      have h3 := hmk.trans hsum
      rw [← le_div_iff₀ (by positivity)] at h3
      refine h3.trans ?_
      have h4 : (H.1 : ℝ) * (k * (2 * e * (k : ℝ) ^ H.1)) / (α * H.1) =
          2 * k * e * (k : ℝ) ^ H.1 / α := by field_simp
      rw [h4, div_le_iff₀ hα]
      have h5 : 2 * (k : ℝ) * e ≤ 2 * k * (6144 * (k : ℝ) ^ 8 / H.1) :=
        mul_le_mul_of_nonneg_left (he1.trans he2) (by positivity)
      have h6 : 12288 * (k : ℝ) ^ 9 / α * ((k : ℝ) ^ H.1 / H.1) * α =
          2 * k * (6144 * (k : ℝ) ^ 8 / H.1) * (k : ℝ) ^ H.1 := by field_simp; ring
      rw [h6]
      exact mul_le_mul_of_nonneg_right h5 hkn.le
    refine hb.trans ?_
    have : 0 ≤ 16 / α ^ 4 * ((k : ℝ) ^ H.1 / H.1) := by positivity
    nlinarith
  · -- McDiarmid's inequality
    push Not at hcase
    have hmc := card_dev_le hk (fun χ ↦ ((badSet H d χ).card : ℝ)) (c := d + 1)
      (fun χ i c ↦ card_badSet_update hreg χ i c) (ε := α * H.1 / 2) (by positivity)
    have hmean : (∑ χ' : Fin H.1 → Fin k, ((badSet H d χ').card : ℝ)) / (k : ℝ) ^ H.1 ≤
        α * H.1 / 2 := by
      rw [div_le_iff₀ hkn]
      refine hsum.trans ?_
      have : (H.1 : ℝ) * (k * (2 * e * (k : ℝ) ^ H.1)) = H.1 * (2 * k * e) * (k : ℝ) ^ H.1 := by
        ring
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ hkn.le
      nlinarith
    have hsub : (univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card) ⊆
        univ.filter fun χ ↦ α * H.1 / 2 ≤ |((badSet H d χ).card : ℝ) -
          (∑ χ' : Fin H.1 → Fin k, ((badSet H d χ').card : ℝ)) / (k : ℝ) ^ H.1| := by
      intro χ hχ
      rw [mem_filter] at hχ ⊢
      refine ⟨mem_univ _, ?_⟩
      rw [le_abs]
      left
      linarith [hχ.2]
    have hy : 0 < α ^ 2 * H.1 / (2 * ((d : ℝ) + 1) ^ 2) := by positivity
    have hexp : 2 * Real.exp (-2 * (α * H.1 / 2) ^ 2 / (H.1 * ((d : ℝ) + 1) ^ 2)) ≤
        16 / α ^ 4 / H.1 := by
      have e1 : -2 * (α * H.1 / 2) ^ 2 / (H.1 * ((d : ℝ) + 1) ^ 2) =
          -(α ^ 2 * H.1 / (2 * ((d : ℝ) + 1) ^ 2)) := by field_simp
      rw [e1]
      have h1 := exp_neg_le_two_div_sq hy
      have h2 : 2 * (2 / (α ^ 2 * H.1 / (2 * ((d : ℝ) + 1) ^ 2)) ^ 2) ≤ 16 / α ^ 4 / H.1 := by
        have hd4 : ((d : ℝ) + 1) ^ 4 ≤ H.1 := by exact_mod_cast hcase
        have e2 : 2 * (2 / (α ^ 2 * H.1 / (2 * ((d : ℝ) + 1) ^ 2)) ^ 2) =
            16 * ((d : ℝ) + 1) ^ 4 / (α ^ 4 * (H.1 : ℝ) ^ 2) := by field_simp; ring
        rw [e2, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 := mul_le_mul_of_nonneg_left hd4 (by positivity : (0 : ℝ) ≤ 16 * (α ^ 4 * H.1))
        nlinarith
      nlinarith
    calc ((univ.filter fun χ : Fin H.1 → Fin k ↦ α * H.1 < (badSet H d χ).card).card : ℝ)
        ≤ 2 * Real.exp (-2 * (α * H.1 / 2) ^ 2 / (H.1 * ((d : ℝ) + 1) ^ 2)) * (k : ℝ) ^ H.1 :=
          le_trans (by exact_mod_cast card_le_card hsub) hmc
      _ ≤ 16 / α ^ 4 / H.1 * (k : ℝ) ^ H.1 := mul_le_mul_of_nonneg_right hexp hkn.le
      _ ≤ (16 / α ^ 4 + 12288 * (k : ℝ) ^ 9 / α) * ((k : ℝ) ^ H.1 / H.1) := by
          rw [div_mul_eq_mul_div, mul_div_assoc']
          rw [div_le_div_iff_of_pos_right hnR]
          nlinarith

end Planted

end BHSV25
