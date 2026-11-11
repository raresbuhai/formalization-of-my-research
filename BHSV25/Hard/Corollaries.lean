module

public import BHSV25.Hard.Model

/-!
# Theorem 1.8 (2) from Theorem 1.9 (2), and the model of Theorem 1.5

* **Theorem 1.8 (2)** (Corollary 8.3, `BHSV25.Hard.expanderColoring_repeatedRows_hardness`): for a
  model with repeated rows, `α > 0` for its stationary distribution (the positive `π` of the
  definition, normalized), and `δ = α / 2` works, by Theorem 1.9 (2) with `γ = α / 2`.
* **The model of Theorem 1.5** (`BHSV25.Hard.M3`): `[[0, 1/2, 1/2], [1, 0, 0], [1, 0, 0]]` with
  `π = (1/2, 1/4, 1/4)` has characteristic polynomial `X (X - 1) (X + 1)` and `α = 1/2`.
  Theorem 1.5 itself is in `BHSV25/Hard/Unbalanced.lean`.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM Polynomial Cslib.Complexity

/-- **Theorem 1.8 (2)** of [BHSV25] (Corollary 8.3). -/
theorem expanderColoring_repeatedRows_hardness (hUGC : UniqueGames.KhotUGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (hrows : ¬ Function.Injective M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε lam : ℝ, 0 < ε → 0 < lam →
      PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
        G.IsOneSidedExpander lam ∧ G.MColorable M ε) k δ) := by
  classical
  obtain ⟨π, hπpos, hrev⟩ := hM.reversible
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, M a = M b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hrows
    obtain ⟨a, b, h1, h2⟩ := hrows
    exact ⟨a, b, h1, h2⟩
  set S := ∑ c, π c
  have hS : 0 < S := sum_pos (fun c _ ↦ hπpos c) ⟨a, mem_univ _⟩
  set π' : Fin k → ℝ := fun c ↦ π c / S
  have hπ' : IsStationary M π' := by
    refine ⟨fun c ↦ div_pos (hπpos c) hS, ?_, fun c d ↦ ?_⟩
    · simp only [π', ← sum_div]; exact div_self hS.ne'
    · simp only [π']
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, hrev]
  have hα : 0 < alpha M π' := by
    unfold alpha
    have hterm : ∀ c, 0 ≤ min (π' c)
        (∑ d ∈ univ.filter (fun d ↦ d ≠ c ∧ M d = M c), π' d) :=
      fun c ↦ le_min (hπ'.1 c).le (sum_nonneg fun d _ ↦ (hπ'.1 d).le)
    refine lt_of_lt_of_le ?_ (single_le_sum (fun c _ ↦ hterm c) (mem_univ a))
    refine lt_min (hπ'.1 a) ?_
    exact sum_pos' (fun d _ ↦ (hπ'.1 d).le)
      ⟨b, mem_filter.2 ⟨mem_univ _, hne.symm, hab.symm⟩, hπ'.1 b⟩
  refine ⟨alpha M π' / 2, by positivity, fun ε lam hε hlam ↦ ?_⟩
  have h := expanderColoring_hardness hUGC M hM π' hπ' (alpha M π' / 2) ε lam (by positivity)
    (by linarith) hε hlam
  rwa [show alpha M π' - alpha M π' / 2 = alpha M π' / 2 by ring] at h

/-! ### The model of Theorem 1.5 -/

/-- The model of Theorem 1.5: one class of half the vertices joined to two classes of a quarter. -/
noncomputable def M3 : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 1 / 2; 1, 0, 0; 1, 0, 0]

/-- Its stationary distribution. -/
noncomputable def π3 : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

theorem charpoly_M3 : M3.charpoly = (X - C 0) * (X - C 1) * (X - C (-1)) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [M3, Fin.isValue, Matrix.charmatrix_apply_eq, ne_eq, Fin.reduceEq, not_false_eq_true,
    Matrix.charmatrix_apply_ne, mul_neg, neg_mul, neg_neg, zero_ne_one, one_ne_zero, map_zero,
    sub_zero, map_one, map_neg, sub_neg_eq_add, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons, one_div]
  have h2 : (C (2⁻¹ : ℝ)) * (2 : ℝ[X]) = 1 := by
    rw [show (2 : ℝ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  linear_combination (-X) * h2

theorem isModel_M3 : IsModel M3 where
  nonneg a b := by fin_cases a <;> fin_cases b <;> norm_num [M3]
  rowSum a := by fin_cases a <;> simp [M3, Fin.sum_univ_three]; norm_num
  diag a := by fin_cases a <;> simp [M3]
  reversible := ⟨π3, fun a ↦ by fin_cases a <;> norm_num [π3], fun a b ↦ by
    fin_cases a <;> fin_cases b <;> norm_num [M3, π3]⟩
  secondEig := by
    rw [charpoly_M3, roots_mul (by
      simp only [ne_eq, mul_eq_zero, X_sub_C_ne_zero, or_self, not_false_eq_true]),
      roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)), roots_X_sub_C,
      roots_X_sub_C, roots_X_sub_C]
    simp [Multiset.filter_singleton]

theorem isStationary_M3 : IsStationary M3 π3 := by
  refine ⟨fun a ↦ by fin_cases a <;> norm_num [π3], by simp [π3, Fin.sum_univ_three]; norm_num,
    fun a b ↦ by fin_cases a <;> fin_cases b <;> norm_num [M3, π3]⟩

theorem alpha_M3 : alpha M3 π3 = 1 / 2 := by
  classical
  have h01 : M3 0 ≠ M3 1 := fun h ↦ by have := congrFun h 0; norm_num [M3] at this
  have h02 : M3 0 ≠ M3 2 := fun h ↦ by have := congrFun h 0; norm_num [M3] at this
  have h12 : M3 1 = M3 2 := by
    funext j; fin_cases j <;> simp [M3]
  have e0 : univ.filter (fun d : Fin 3 ↦ d ≠ 0 ∧ M3 d = M3 0) = ∅ := by
    ext d; fin_cases d <;> simp [h12, h02.symm]
  have e1 : univ.filter (fun d : Fin 3 ↦ d ≠ 1 ∧ M3 d = M3 1) = {2} := by
    ext d; fin_cases d <;> simp [h02, h12]
  have e2 : univ.filter (fun d : Fin 3 ↦ d ≠ 2 ∧ M3 d = M3 2) = {1} := by
    ext d; fin_cases d <;> simp [h02, h12]
  unfold alpha
  rw [Fin.sum_univ_three, e0, e1, e2]
  simp [π3]
  norm_num

end BHSV25.Hard
