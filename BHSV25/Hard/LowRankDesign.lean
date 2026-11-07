module

public import BHSV25.Hard.Pipeline

/-!
# The design for Theorem 1.6

The reduction of [BHSV25, Theorem 8.6] as a design (`BHSV25.Hard.LowRank.design`). The types
are `(b, α, β)` with a block `b < 9` and a slot `(α, β) ∈ [m]²`; block `b` is in group `b / 2`:

* group `0` (blocks `0, 1`): independent cells of color `2`, except the slots with `β = 0`, which
  are **absorbers** (garbage);
* group `1` (blocks `2, 3`): copies of the input graph, colored `0` on `I` and `1` on `J` in
  block `2`, the other way round in block `3`;
* groups `2, 3, 4` (blocks `4, 5`, `6, 7` and `8`): independent cells of colors `0`, `1`, `2`.

Groups `0` and `1` are joined completely (density `4/4`): with the copies of the input graph this
is the graph `G'` of Algorithm 2, made exactly regular by the absorbers: the copy of `G` in
`(b, α, β)` is joined to the absorber `(b - 2, α, 0)` by the complement of `G`, and the absorbers
`(b', α', 0)` of a block are joined to each other by copies of `G`, so that `W⁰` has zero row
sums. Groups `2, 3, 4` form the tripartite graph `G''`, with densities `3/4`, `2/4`, `2/4`; every
type has degree `8 m²` in types. Each color has `3 m²` types.
-/

@[expose] public section

namespace BHSV25.Hard.LowRank

open Finset

variable (m : ℕ)

/-- The types: a block `b < 9` and a slot `(α, β)`. -/
abbrev Ty := Fin 9 × Fin m × Fin m

/-- The group of a block. -/
def grB (b : Fin 9) : Fin 5 := ⟨b / 2, by omega⟩

/-- The densities between groups, in quarters. -/
def q (i j : Fin 5) : ℕ :=
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 4
  else if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then 3
  else if (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 2
  else 0

/-- A block of copies of the input graph. -/
def realB (b : Fin 9) : Prop := b = 2 ∨ b = 3

/-- A block holding absorbers. -/
def absB (b : Fin 9) : Prop := b = 0 ∨ b = 1

instance (b : Fin 9) : Decidable (realB b) := by unfold realB; infer_instance
instance (b : Fin 9) : Decidable (absB b) := by unfold absB; infer_instance

/-- The indicator of a proposition, as an integer. -/
def zi (P : Prop) [Decidable P] : ℤ := if P then 1 else 0

/-- The correction between types: copies of the input graph on the diagonal of the real blocks
and between absorbers of the same block, its complement between a copy and its absorber. -/
def W0 (τ τ' : Ty m) : ℤ :=
  zi (realB τ.1 ∧ τ' = τ) +
  zi (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0) -
  zi (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧ (τ'.2.2 : ℕ) = 0) -
  zi (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧ (τ.2.2 : ℕ) = 0)

theorem zi_and (P Q : Prop) [Decidable P] [Decidable Q] : zi (P ∧ Q) = zi P * zi Q := by
  unfold zi; by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem zi_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : zi P = zi Q := by
  unfold zi; by_cases hP : P
  · rw [ite_eq_left hP, ite_eq_left (h.1 hP)]
  · rw [ite_eq_right hP, ite_eq_right (fun hQ ↦ hP (h.2 hQ))]

theorem blocks_ne (b b' : Fin 9) (h : realB b) (h' : (b' : ℕ) + 2 = b) :
    grB b ≠ grB b' ∧ 1 ≤ q (grB b) (grB b') := by
  revert b b'; decide

theorem W0_symm (τ τ' : Ty m) : W0 m τ τ' = W0 m τ' τ := by
  unfold W0
  have h1 : zi (realB τ.1 ∧ τ' = τ) = zi (realB τ'.1 ∧ τ = τ') := by
    by_cases h : τ' = τ
    · subst h; rfl
    · unfold zi
      rw [ite_eq_right (fun h'' ↦ h h''.2), ite_eq_right (fun h'' ↦ h h''.2.symm)]
  have h2 : zi (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0) =
      zi (absB τ'.1 ∧ τ.1 = τ'.1 ∧ (τ'.2.2 : ℕ) = 0 ∧ (τ.2.2 : ℕ) = 0) := by
    exact zi_congr ⟨fun ⟨a, b, c, d⟩ ↦ ⟨b ▸ a, b.symm, d, c⟩,
      fun ⟨a, b, c, d⟩ ↦ ⟨b ▸ a, b.symm, d, c⟩⟩
  have h3 : zi (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧ (τ'.2.2 : ℕ) = 0) =
      zi (absB τ'.1 ∧ (τ.1 : ℕ) = τ'.1 + 2 ∧ τ.2.1 = τ'.2.1 ∧ (τ'.2.2 : ℕ) = 0) := by
    refine zi_congr ⟨fun ⟨a, b, c, d⟩ ↦ ⟨?_, b.symm, c.symm, d⟩,
      fun ⟨a, b, c, d⟩ ↦ ⟨?_, b.symm, c.symm, d⟩⟩
    · simp only [realB, absB, Fin.ext_iff] at a ⊢; omega
    · simp only [realB, absB, Fin.ext_iff] at a ⊢; omega
  have h4 : zi (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧ (τ.2.2 : ℕ) = 0) =
      zi (realB τ'.1 ∧ (τ.1 : ℕ) + 2 = τ'.1 ∧ τ.2.1 = τ'.2.1 ∧ (τ.2.2 : ℕ) = 0) := by
    refine zi_congr ⟨fun ⟨a, b, c, d⟩ ↦ ⟨?_, b.symm, c.symm, d⟩,
      fun ⟨a, b, c, d⟩ ↦ ⟨?_, b.symm, c.symm, d⟩⟩
    · simp only [realB, absB, Fin.ext_iff] at a ⊢; omega
    · simp only [realB, absB, Fin.ext_iff] at a ⊢; omega
  rw [h1, h2, h3, h4]
  ring

theorem W0_cases (τ τ' : Ty m) : W0 m τ τ' = -1 ∨ W0 m τ τ' = 0 ∨ W0 m τ τ' = 1 := by
  unfold W0 zi
  split_ifs with h1 h2 h3 h4 h4 h3 h4 h4 h2 h3 h4 h4 h3 h4 h4 <;>
    first
    | (right; right; rfl) | (right; left; rfl) | (left; rfl)
    | (exfalso; simp only [realB, absB, Fin.ext_iff, Prod.ext_iff] at *; omega)

theorem sum_zi_eq {α : Type*} [Fintype α] [DecidableEq α] (x : α) :
    ∑ y : α, zi (y = x) = 1 := by
  unfold zi; rw [sum_ite_eq']; simp

theorem sum_zi_val0 (hm : 0 < m) : ∑ β : Fin m, zi ((β : ℕ) = 0) = 1 := by
  rw [Fintype.sum_eq_single ⟨0, hm⟩ (fun β hβ ↦ by
    unfold zi; rw [ite_eq_right (fun h ↦ hβ (Fin.ext h))])]
  unfold zi; simp

theorem sum_ty (f : Fin 9 → ℤ) (g h : Fin m → ℤ) :
    ∑ τ' : Ty m, f τ'.1 * g τ'.2.1 * h τ'.2.2 = (∑ b, f b) * (∑ α, g α) * ∑ β, h β := by
  simp only [Fintype.sum_prod_type, ← mul_sum, ← sum_mul]

theorem sum_zi_add_two (b : Fin 9) :
    zi (realB b) * ∑ b' : Fin 9, zi ((b' : ℕ) + 2 = b) = zi (realB b) := by
  revert b; decide

theorem sum_zi_sub_two (b : Fin 9) :
    zi (absB b) * ∑ b' : Fin 9, zi ((b' : ℕ) = b + 2) = zi (absB b) := by
  revert b; decide

theorem sums_zi (τ : Ty m) :
    ∑ τ' : Ty m, zi (realB τ.1 ∧ τ' = τ) = zi (realB τ.1) ∧
    ∑ τ' : Ty m, zi (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0) =
      zi (absB τ.1) * zi ((τ.2.2 : ℕ) = 0) * m ∧
    ∑ τ' : Ty m, zi (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧
      (τ'.2.2 : ℕ) = 0) = zi (realB τ.1) ∧
    ∑ τ' : Ty m, zi (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧
      (τ.2.2 : ℕ) = 0) = zi (absB τ.1) * zi ((τ.2.2 : ℕ) = 0) * m := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le _) τ.2.1.2
  have hval0 := sum_zi_val0 m hm
  have hone : ∑ _α : Fin m, (1 : ℤ) = m := by simp
  have e1 : ∑ τ' : Ty m, zi (realB τ.1 ∧ τ' = τ) = zi (realB τ.1) := by
    simp_rw [zi_and, ← mul_sum, sum_zi_eq, mul_one]
  have e2 : ∑ τ' : Ty m, zi (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0) =
      zi (absB τ.1) * zi ((τ.2.2 : ℕ) = 0) * m := by
    have : ∀ τ' : Ty m, zi (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0) =
        zi (absB τ.1) * zi ((τ.2.2 : ℕ) = 0) *
          (zi (τ'.1 = τ.1) * (fun _ ↦ (1 : ℤ)) τ'.2.1 * zi ((τ'.2.2 : ℕ) = 0)) := by
      intro τ'; simp only [zi_and]; ring
    simp_rw [this, ← mul_sum]
    rw [sum_ty m (fun b ↦ zi (b = τ.1)) (fun _ ↦ 1) (fun β ↦ zi ((β : ℕ) = 0)), sum_zi_eq,
      hval0, hone]
    ring
  have e3 : ∑ τ' : Ty m, zi (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧
      (τ'.2.2 : ℕ) = 0) = zi (realB τ.1) := by
    have : ∀ τ' : Ty m, zi (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧
        (τ'.2.2 : ℕ) = 0) = zi (realB τ.1) *
          (zi ((τ'.1 : ℕ) + 2 = τ.1) * zi (τ'.2.1 = τ.2.1) * zi ((τ'.2.2 : ℕ) = 0)) := by
      intro τ'; simp only [zi_and]; ring
    simp_rw [this, ← mul_sum]
    rw [sum_ty m (fun b ↦ zi ((b : ℕ) + 2 = τ.1)) (fun α ↦ zi (α = τ.2.1))
      (fun β ↦ zi ((β : ℕ) = 0)), sum_zi_eq, hval0, mul_one, mul_one, sum_zi_add_two]
  have e4 : ∑ τ' : Ty m, zi (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧
      (τ.2.2 : ℕ) = 0) = zi (absB τ.1) * zi ((τ.2.2 : ℕ) = 0) * m := by
    have : ∀ τ' : Ty m, zi (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧
        (τ.2.2 : ℕ) = 0) = zi ((τ.2.2 : ℕ) = 0) * (zi (absB τ.1) *
          (zi ((τ'.1 : ℕ) = τ.1 + 2) * zi (τ'.2.1 = τ.2.1) * (fun _ ↦ (1 : ℤ)) τ'.2.2)) := by
      intro τ'; simp only [zi_and]; ring
    simp_rw [this, ← mul_sum]
    rw [sum_ty m (fun b ↦ zi ((b : ℕ) = τ.1 + 2)) (fun α ↦ zi (α = τ.2.1)) (fun _ ↦ 1),
      sum_zi_eq, hone, mul_one]
    linear_combination (zi ((τ.2.2 : ℕ) = 0) * (m : ℤ)) * sum_zi_sub_two τ.1
  exact ⟨e1, e2, e3, e4⟩

theorem W0_sum (τ : Ty m) : ∑ τ', W0 m τ τ' = 0 := by
  obtain ⟨e1, e2, e3, e4⟩ := sums_zi m τ
  unfold W0
  simp only [sum_add_distrib, sum_sub_distrib]
  rw [e1, e2, e3, e4]
  ring

theorem zi_le_one (P : Prop) [Decidable P] : zi P ≤ 1 := by unfold zi; split_ifs <;> norm_num

theorem zi_nonneg (P : Prop) [Decidable P] : 0 ≤ zi P := by unfold zi; split_ifs <;> norm_num

theorem abs_W0_le (τ τ' : Ty m) : |W0 m τ τ'| ≤
    zi (realB τ.1 ∧ τ' = τ) +
    zi (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0) +
    zi (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧ (τ'.2.2 : ℕ) = 0) +
    zi (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧ (τ.2.2 : ℕ) = 0) := by
  unfold W0
  have h0 : ∀ (P : Prop) [Decidable P], 0 ≤ zi P := fun P _ ↦ by unfold zi; split_ifs <;> norm_num
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    linarith [h0 (realB τ.1 ∧ τ' = τ),
      h0 (absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0),
      h0 (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧ (τ'.2.2 : ℕ) = 0),
      h0 (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧ (τ.2.2 : ℕ) = 0)]

theorem sum_abs_W0 (τ : Ty m) : ∑ τ', |(W0 m τ τ' : ℝ)| ≤ 2 * m + 2 := by
  obtain ⟨e1, e2, e3, e4⟩ := sums_zi m τ
  have h : ∑ τ', |W0 m τ τ'| ≤ 2 * m + 2 := by
    refine (sum_le_sum fun τ' _ ↦ abs_W0_le m τ τ').trans ?_
    simp only [sum_add_distrib]
    rw [e1, e2, e3, e4]
    have := zi_le_one (realB τ.1)
    have h2 : zi (absB τ.1) * zi ((τ.2.2 : ℕ) = 0) ≤ 1 :=
      (mul_le_mul_of_nonneg_left (zi_le_one _) (zi_nonneg _)).trans
        ((mul_one _).le.trans (zi_le_one _))
    nlinarith [zi_nonneg (realB τ.1)]
  have := (Int.cast_le (R := ℝ)).2 h
  push_cast at this
  simpa using this

theorem W0_eq_neg {τ τ' : Ty m} (h : W0 m τ τ' = -1) :
    (realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1) ∨ (absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2) := by
  by_cases h3 : realB τ.1 ∧ (τ'.1 : ℕ) + 2 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧ (τ'.2.2 : ℕ) = 0
  · exact Or.inl ⟨h3.1, h3.2.1⟩
  by_cases h4 : absB τ.1 ∧ (τ'.1 : ℕ) = τ.1 + 2 ∧ τ'.2.1 = τ.2.1 ∧ (τ.2.2 : ℕ) = 0
  · exact Or.inr ⟨h4.1, h4.2.1⟩
  unfold W0 zi at h
  rw [ite_eq_right h3, ite_eq_right h4] at h
  split_ifs at h <;> omega

theorem W0_eq_pos {τ τ' : Ty m} (h : W0 m τ τ' = 1) : τ'.1 = τ.1 := by
  by_cases h1 : realB τ.1 ∧ τ' = τ
  · rw [h1.2]
  by_cases h2 : absB τ.1 ∧ τ'.1 = τ.1 ∧ (τ.2.2 : ℕ) = 0 ∧ (τ'.2.2 : ℕ) = 0
  · exact h2.2.1
  unfold W0 zi at h
  rw [ite_eq_right h1, ite_eq_right h2] at h
  split_ifs at h <;> omega

theorem reg_ty (τ : Ty m) :
    ∑ τ' : Ty m, (if grB τ.1 ≠ grB τ'.1 then q (grB τ.1) (grB τ'.1) else 0) = 8 * m ^ 2 := by
  have h9 : ∀ b : Fin 9, ∑ b' : Fin 9, (if grB b ≠ grB b' then q (grB b) (grB b') else 0) = 8 := by
    decide
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  rw [← mul_sum, h9]
  ring

theorem q_symm_aux (i j : Fin 5) : q i j = q j i := by
  unfold q; fin_cases i <;> fin_cases j <;> rfl

/-- **The design of Theorem 1.6.** -/
abbrev design : Design where
  Ty := Ty m
  K := 5
  gr τ := grB τ.1
  r := 2
  q := q
  d₀ := 8 * m ^ 2
  W0 := W0 m
  q_symm i j := by unfold q; fin_cases i <;> fin_cases j <;> rfl
  q_le i j := by unfold q; fin_cases i <;> fin_cases j <;> decide
  reg := reg_ty m
  W0_symm := W0_symm m
  W0_cases := W0_cases m
  W0_neg τ τ' h := by
    rcases W0_eq_neg m h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact blocks_ne _ _ h1 h2
    · have := blocks_ne τ'.1 τ.1 (by simp only [realB, absB, Fin.ext_iff] at h1 ⊢; omega)
        h2.symm
      exact ⟨this.1.symm, by rw [q_symm_aux]; exact this.2⟩
  W0_pos τ τ' h := by
    simp only [W0_eq_pos m h]
  W0_sum := W0_sum m

end BHSV25.Hard.LowRank
