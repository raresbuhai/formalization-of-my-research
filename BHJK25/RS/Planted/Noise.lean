module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Noise on disjoint groups of coordinates

Each coordinate of `e : ι → Bool` is flipped (`true`) independently with probability `p`
(`BHJK25.RS.PlantedAux.flipW`). For pairwise disjoint groups `C v` of coordinates (`v ∈ cols`),
the events "no coordinate of `C v` is flipped" are independent, with probabilities
`(1 - p)^|C v|`. We use this only through a Chernoff-type bound: the probability that fewer than
`a` groups are clean is at most `2^a E[2^(-#clean)] = 2^a ∏_v (1 - (1 - p)^|C v| / 2)`.
The independence is proved by expanding the product `∏_v (1 - a 1[C v clean])` over the subsets
`A` of groups: `∏_{v ∈ A} 1[C v clean] = 1[⋃_{v ∈ A} C v clean]`, and a union of disjoint groups
is clean with probability `∏_{v ∈ A} (1 - p)^|C v|`.
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Finset

variable {ι V : Type*}

/-- The probability of the flip pattern `e` when each coordinate is flipped independently with
probability `p`. -/
noncomputable def flipW [Fintype ι] (p : ℝ) (e : ι → Bool) : ℝ := ∏ i, if e i then p else 1 - p

theorem flipW_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e : ι → Bool) :
    0 ≤ flipW p e :=
  prod_nonneg fun i _ ↦ by split_ifs <;> linarith

/-- Summing a product of functions of the coordinates over all patterns. -/
theorem sum_prod_bool [Fintype ι] [DecidableEq ι] (f : ι → Bool → ℝ) :
    ∑ e : ι → Bool, ∏ i, f i (e i) = ∏ i, (f i true + f i false) := by
  rw [← Fintype.prod_sum]
  exact prod_congr rfl fun i _ ↦ Fintype.sum_bool (f i)

/-- The flip probabilities sum to `1`. -/
theorem sum_flipW [Fintype ι] [DecidableEq ι] (p : ℝ) : ∑ e : ι → Bool, flipW p e = 1 := by
  unfold flipW
  rw [sum_prod_bool (fun _ b ↦ if b then p else 1 - p)]
  simp

/-- `1` if the pattern `e` flips no coordinate of `C`, `0` otherwise. -/
noncomputable def allOff (C : Finset ι) (e : ι → Bool) : ℝ := ∏ i ∈ C, if e i then 0 else 1

theorem allOff_eq (C : Finset ι) (e : ι → Bool) :
    allOff C e = if ∀ i ∈ C, e i = false then 1 else 0 := by
  unfold allOff
  split_ifs with h
  · exact prod_eq_one fun i hi ↦ by rw [h i hi]; rfl
  · push Not at h
    obtain ⟨i, hi, hei⟩ := h
    exact prod_eq_zero hi (by simp [hei])

/-- A set `C` of coordinates is left clean with probability `(1 - p)^|C|`. -/
theorem sum_flipW_allOff [Fintype ι] [DecidableEq ι] (p : ℝ) (C : Finset ι) :
    ∑ e : ι → Bool, flipW p e * allOff C e = (1 - p) ^ C.card := by
  have h1 : ∀ e : ι → Bool, flipW p e * allOff C e =
      ∏ i, (if e i then p else 1 - p) * (if i ∈ C then (if e i then 0 else 1) else 1) := by
    intro e
    rw [prod_mul_distrib, flipW, allOff, prod_ite_mem, univ_inter]
  simp_rw [h1]
  rw [sum_prod_bool (fun i b ↦ (if b then p else 1 - p) * (if i ∈ C then (if b then 0 else 1)
    else 1))]
  calc _ = ∏ i, if i ∈ C then 1 - p else 1 :=
        prod_congr rfl fun i _ ↦ by by_cases hi : i ∈ C <;> simp [hi]
    _ = (1 - p) ^ C.card := by rw [prod_ite_mem, univ_inter, prod_const]

/-- **Independence of disjoint groups**: for pairwise disjoint groups `C v`,
`E[∏_v (1 - a 1[C v clean])] = ∏_v (1 - a (1 - p)^|C v|)`. -/
theorem sum_flipW_prod [Fintype ι] [DecidableEq ι] (p a : ℝ) (cols : Finset V) (C : V → Finset ι)
    (hC : (cols : Set V).PairwiseDisjoint C) :
    ∑ e : ι → Bool, flipW p e * ∏ v ∈ cols, (1 - a * allOff (C v) e) =
      ∏ v ∈ cols, (1 - a * (1 - p) ^ (C v).card) := by
  classical
  have hdisj : ∀ A ∈ cols.powerset, (A : Set V).PairwiseDisjoint C :=
    fun A hA ↦ hC.subset (coe_subset.2 (mem_powerset.1 hA))
  have hexp : ∀ e : ι → Bool, ∏ v ∈ cols, (1 - a * allOff (C v) e) =
      ∑ A ∈ cols.powerset, (-a) ^ A.card * allOff (A.biUnion C) e := by
    intro e
    rw [show ∏ v ∈ cols, (1 - a * allOff (C v) e) = ∏ v ∈ cols, (-a * allOff (C v) e + 1) from
      prod_congr rfl fun _ _ ↦ by ring, prod_add]
    refine sum_congr rfl fun A hA ↦ ?_
    rw [prod_const_one, mul_one, prod_mul_distrib, prod_const, allOff, prod_biUnion (hdisj A hA)]
    rfl
  have hexp2 : ∏ v ∈ cols, (1 - a * (1 - p) ^ (C v).card) =
      ∑ A ∈ cols.powerset, (-a) ^ A.card * (1 - p) ^ (A.biUnion C).card := by
    rw [show ∏ v ∈ cols, (1 - a * (1 - p) ^ (C v).card) =
      ∏ v ∈ cols, (-a * (1 - p) ^ (C v).card + 1) from prod_congr rfl fun _ _ ↦ by ring, prod_add]
    refine sum_congr rfl fun A hA ↦ ?_
    rw [prod_const_one, mul_one, prod_mul_distrib, prod_const, card_biUnion (hdisj A hA),
      prod_pow_eq_pow_sum]
  simp_rw [hexp, mul_sum]
  rw [sum_comm, hexp2]
  refine sum_congr rfl fun A _ ↦ ?_
  simp_rw [mul_left_comm (flipW p _) ((-a) ^ A.card)]
  rw [← mul_sum, sum_flipW_allOff]

/-- **Few clean groups are unlikely**: the probability that fewer than `a` of the pairwise
disjoint groups `C v` are clean is at most `2^a ∏_v (1 - (1 - p)^|C v| / 2)`. -/
theorem sum_flipW_card_lt [Fintype ι] [DecidableEq ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (cols : Finset V) (C : V → Finset ι) (hC : (cols : Set V).PairwiseDisjoint C) (a : ℕ) :
    ∑ e : ι → Bool,
        (if (cols.filter fun v ↦ ∀ i ∈ C v, e i = false).card < a then flipW p e else 0) ≤
      2 ^ a * ∏ v ∈ cols, (1 - 1 / 2 * (1 - p) ^ (C v).card) := by
  rw [← sum_flipW_prod p (1 / 2) cols C hC, mul_sum]
  refine sum_le_sum fun e _ ↦ ?_
  have hW := flipW_nonneg hp0 hp1 e
  have hprod : ∏ v ∈ cols, (1 - 1 / 2 * allOff (C v) e) =
      (1 / 2 : ℝ) ^ (cols.filter fun v ↦ ∀ i ∈ C v, e i = false).card := by
    calc ∏ v ∈ cols, (1 - 1 / 2 * allOff (C v) e) =
          ∏ v ∈ cols, if ∀ i ∈ C v, e i = false then (1 / 2 : ℝ) else 1 :=
          prod_congr rfl fun v _ ↦ by rw [allOff_eq]; split_ifs <;> norm_num
      _ = _ := by rw [prod_ite, prod_const, prod_const_one, mul_one]
  rw [hprod]
  split_ifs with hlt
  · set c := (cols.filter fun v ↦ ∀ i ∈ C v, e i = false).card
    have h2 : (2 : ℝ) ^ c ≤ 2 ^ a := pow_le_pow_right₀ (by norm_num) hlt.le
    have h3 : (1 : ℝ) ≤ 2 ^ a * (1 / 2) ^ c := by
      rw [one_div_pow, mul_one_div, one_le_div (by positivity)]
      exact h2
    calc flipW p e = 1 * flipW p e := (one_mul _).symm
      _ ≤ (2 ^ a * (1 / 2) ^ c) * flipW p e := mul_le_mul_of_nonneg_right h3 hW
      _ = _ := by ring
  · positivity

/-- `∏_v (1 - ρ_v / 2) ≤ exp(-ρ₀ |cols| / 2)` when `ρ₀ ≤ ρ_v ≤ 1`. -/
theorem prod_one_sub_le_exp {cols : Finset V} {ρ : V → ℝ} {ρ₀ : ℝ}
    (h0 : ∀ v ∈ cols, ρ₀ ≤ ρ v) (h1 : ∀ v ∈ cols, ρ v ≤ 1) :
    ∏ v ∈ cols, (1 - 1 / 2 * ρ v) ≤ Real.exp (-(ρ₀ * cols.card / 2)) := by
  have hρ₀1 : ρ₀ ≤ 1 ∨ cols = ∅ := by
    rcases cols.eq_empty_or_nonempty with h | ⟨v, hv⟩
    · exact Or.inr h
    · exact Or.inl ((h0 v hv).trans (h1 v hv))
  rcases hρ₀1 with hρ₀1 | hempty
  · calc ∏ v ∈ cols, (1 - 1 / 2 * ρ v) ≤ ∏ _v ∈ cols, (1 - 1 / 2 * ρ₀) :=
          prod_le_prod₀ (fun v hv ↦ by linarith [h1 v hv]) fun v hv ↦ by linarith [h0 v hv]
      _ = (1 - 1 / 2 * ρ₀) ^ cols.card := prod_const _
      _ ≤ Real.exp (-(1 / 2 * ρ₀)) ^ cols.card :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(1 / 2 * ρ₀))]) _
      _ = Real.exp (-(ρ₀ * cols.card / 2)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  · subst hempty
    simp

end BHJK25.RS.PlantedAux
