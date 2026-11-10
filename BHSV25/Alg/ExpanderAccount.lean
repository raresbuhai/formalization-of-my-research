module

public import BHSV25.Alg.ExpanderContract
public import BHSV25.Alg.Cluster

/-!
# Accounting for the algorithm of Theorem 7.1

Facts for counting the vertices colored by the algorithm of [BHSV25, Theorem 7.1], whose clusters
are the merged parts of the groups of equal rows (`BHSV25/Alg/ExpanderGrid.lean`):

* each cluster is rounded against the independent set `V_{a_i^*} \ S` of the part of its
  representative minus a cover `S` of the edges inside the parts
  (`BHSV25.Alg.isIndepSet_part_sdiff`);
* **comparison with `α`** (`BHSV25.Alg.sub_sum_max_le_alpha`): if the part sizes are within
  `C δ n` of `π`, then `n - ∑_i max(0, 2 |V_{a_i^*}| - |V'_i|) ≤ (α + m (2k + 2) C δ) n`, by
  `α = ∑_i (π(S_i) - max(0, 2 π_{a_i^*} - π(S_i)))` (`BHSV25.Alg.alpha_eq_sum_rowRep`).
-/

@[expose] public section

namespace BHSV25

namespace Alg

open Finset Matrix

variable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {π : Fin k → ℝ}

/-- The sizes of the intersections of a set with the parts of a partition add up to its size. -/
theorem sum_card_inter_part {G : Graph} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (χ : Fin G.1 → ι) (T : Finset (Fin G.1)) :
    ∑ i, ((T ∩ part G χ i).card : ℝ) = T.card := by
  have h := card_eq_sum_card_fiberwise (f := χ) (s := T) (t := univ) fun x _ ↦ mem_univ _
  have e : ∀ i, T ∩ part G χ i = T.filter fun x ↦ χ x = i := fun i ↦ by
    ext x
    rw [mem_inter, mem_part, mem_filter]
  simp only [e]
  exact_mod_cast h.symm

/-- `max 0` is `1`-Lipschitz. -/
theorem max_zero_le_add_abs (x y : ℝ) : max 0 y ≤ max 0 x + |y - x| :=
  max_le (by positivity) (by linarith [le_abs_self (y - x), le_max_right 0 x])

/-- The independent set `V_a \ S` of a part, for a cover `S` of the edges inside the parts. -/
theorem isIndepSet_part_sdiff {G : Graph} (χ : Fin G.1 → Fin k) (S : Finset (Fin G.1))
    (hS : ∀ u v, G.2.Adj u v → χ u = χ v → u ∈ S ∨ v ∈ S) (a : Fin k) :
    G.2.IsIndepSet ((part G χ a \ S : Finset (Fin G.1)) : Set (Fin G.1)) := by
  intro u hu v hv _ huv
  rw [mem_coe, mem_sdiff, mem_part] at hu hv
  rcases hS u v huv (hu.1.trans hv.1.symm) with h | h
  · exact hu.2 h
  · exact hv.2 h

/-- **Comparison with `α`**: if the part sizes are within `C δ n` of `π`, then
`n - ∑_i max(0, 2 |V_{a_i^*}| - |V'_i|) ≤ (α + m (2k + 2) C δ) n`. -/
theorem sub_sum_max_le_alpha (hπ : ∀ a, 0 < π a) (n : ℕ) (s : Fin k → ℝ)
    (hs : ∑ a, s a = n) {C δ : ℝ} (hCδ : 0 ≤ C * δ)
    (hclose : ∀ a, |s a / n - π a| ≤ C * δ) (hn : 0 < n) :
    (n : ℝ) - ∑ i : Reps M π, max 0 (2 * s i.1 - ∑ a ∈ rowGroup M i.1, s a) ≤
      (alpha M π + Fintype.card (Reps M π) * ((2 * k + 2) * (C * δ))) * n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hclose' : ∀ a, |s a - n * π a| ≤ C * δ * n := by
    intro a
    have h := hclose a
    rw [← mul_le_mul_iff_of_pos_right hnR, ← abs_of_pos hnR, ← abs_mul, abs_of_pos hnR] at h
    rw [sub_mul, div_mul_cancel₀ _ hnR.ne'] at h
    rw [mul_comm (n : ℝ)]
    exact h
  have halpha : alpha M π = ∑ i : Reps M π,
      ((∑ b ∈ rowGroup M i.1, π b) - max 0 (2 * π i.1 - ∑ b ∈ rowGroup M i.1, π b)) := by
    rw [alpha_eq_sum_rowRep hπ]
    exact Finset.sum_subtype _ (fun a ↦ by simp) _
  have hn' : (n : ℝ) = ∑ i : Reps M π, ∑ a ∈ rowGroup M i.1, s a := by
    rw [sum_reps_rowGroup, hs]
  have hgroupsum : ∀ i : Reps M π,
      |∑ a ∈ rowGroup M i.1, s a - n * ∑ a ∈ rowGroup M i.1, π a| ≤ k * (C * δ * n) := by
    intro i
    rw [mul_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a ∈ rowGroup M i.1, |s a - n * π a| ≤ ∑ _a ∈ rowGroup M i.1, C * δ * n :=
          sum_le_sum fun a _ ↦ hclose' a
      _ ≤ ∑ _a : Fin k, C * δ * n :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ by positivity
      _ = k * (C * δ * n) := by simp
  have hterm : ∀ i : Reps M π,
      (∑ a ∈ rowGroup M i.1, s a) - max 0 (2 * s i.1 - ∑ a ∈ rowGroup M i.1, s a) ≤
        n * ((∑ b ∈ rowGroup M i.1, π b) - max 0 (2 * π i.1 - ∑ b ∈ rowGroup M i.1, π b)) +
          (2 * k + 2) * (C * δ) * n := by
    intro i
    set s' := ∑ a ∈ rowGroup M i.1, s a
    set p' := ∑ b ∈ rowGroup M i.1, π b
    have h1 := hgroupsum i
    have h2 := hclose' i.1
    have h3 := max_zero_le_add_abs (2 * s i.1 - s') (n * (2 * π i.1 - p'))
    have h4 : n * max 0 (2 * π i.1 - p') = max 0 (n * (2 * π i.1 - p')) := by
      rw [mul_max_of_nonneg _ _ hnR.le, mul_zero]
    have h5 : |n * (2 * π i.1 - p') - (2 * s i.1 - s')| ≤ 2 * (C * δ * n) + k * (C * δ * n) := by
      have e : n * (2 * π i.1 - p') - (2 * s i.1 - s') =
          -2 * (s i.1 - n * π i.1) + (s' - n * p') := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_neg, abs_two]
      linarith
    have h6 := neg_abs_le (s' - n * p')
    have h7 : s' ≤ n * p' + k * (C * δ * n) := by linarith [le_abs_self (s' - n * p')]
    nlinarith
  calc (n : ℝ) - ∑ i : Reps M π, max 0 (2 * s i.1 - ∑ a ∈ rowGroup M i.1, s a)
      = ∑ i : Reps M π, ((∑ a ∈ rowGroup M i.1, s a) -
          max 0 (2 * s i.1 - ∑ a ∈ rowGroup M i.1, s a)) := by
        rw [sum_sub_distrib, ← hn']
    _ ≤ ∑ i : Reps M π, (n * ((∑ b ∈ rowGroup M i.1, π b) -
          max 0 (2 * π i.1 - ∑ b ∈ rowGroup M i.1, π b)) + (2 * k + 2) * (C * δ) * n) :=
        sum_le_sum fun i _ ↦ hterm i
    _ = (alpha M π + Fintype.card (Reps M π) * ((2 * k + 2) * (C * δ))) * n := by
        rw [sum_add_distrib, ← mul_sum, ← halpha, sum_const, card_univ, nsmul_eq_mul]
        ring

end Alg

end BHSV25
