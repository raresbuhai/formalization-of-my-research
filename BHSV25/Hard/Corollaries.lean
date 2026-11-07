module

public import BHSV25.Hard.Model

/-!
# Theorems 1.5 and 1.8 (2) from Theorem 1.9 (2)

* **Theorem 1.8 (2)** (Corollary 8.3, `BHSV25.Hard.expanderColoring_repeatedRows_hardness`): for a
  model with repeated rows, `α > 0` for its stationary distribution (the positive `π` of the
  definition, normalized), and `δ = α / 2` works, by Theorem 1.9 (2) with `γ = α / 2`.
* **Theorem 1.5** (Corollary 8.4, `BHSV25.Hard.threeColoring_unbalanced_hardness`): the model
  `[[0, 1/2, 1/2], [1, 0, 0], [1, 0, 0]]` with `π = (1/2, 1/4, 1/4)` has characteristic polynomial
  `X (X - 1) (X + 1)` and `α = 1/2`; an `(M, ε)`-coloring gives `3` independent sets covering all
  but `ε n` vertices, by uncoloring the vertices covering its monochromatic edges
  (`BHSV25.Hard.hasColoring_of_mColorable`).
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM Polynomial

/-- An `(M, ε)`-coloring gives a `(k, ε)`-coloring: uncolor the vertices covering the
monochromatic edges. -/
theorem hasColoring_of_mColorable {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} {ε : ℝ} (G : Graph)
    (h : G.MColorable M ε) : G.HasColoring k ε := by
  classical
  obtain ⟨χ, -, S, hS, hmono⟩ := h
  set c : List ℕ := List.ofFn fun v : Fin G.1 ↦ if v ∈ S then k else (χ v : ℕ)
  have hcol : ∀ v, G.color k c v = if v ∈ S then k else (χ v : ℕ) := by
    intro v
    unfold Graph.color
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [v.2, ↓reduceDIte, Option.getD_some, Fin.eta]
  refine ⟨c, fun u v huv hu ↦ ?_, ?_⟩
  · rw [hcol] at hu ⊢
    rw [hcol]
    have huS : u ∉ S := by intro h; rw [ite_eq_left h] at hu; exact lt_irrefl _ hu
    rw [ite_eq_right huS]
    by_cases hvS : v ∈ S
    · rw [ite_eq_left hvS]; exact (χ u).2.ne
    · rw [ite_eq_right hvS]
      intro heq
      rcases hmono u v huv (Fin.ext heq) with h | h
      · exact huS h
      · exact hvS h
  · unfold Graph.numColored
    have hsub : Sᶜ ⊆ univ.filter fun v ↦ G.color k c v < k := by
      intro v hv
      rw [mem_compl] at hv
      simp only [mem_filter, mem_univ, true_and, hcol, ite_eq_right hv]
      exact (χ v).2
    have h1 := card_le_card hsub
    rw [card_compl, Fintype.card_fin] at h1
    have h2 : (S.card : ℝ) ≤ G.1 := by exact_mod_cast (card_le_univ S).trans (by simp)
    have h3 : ((G.1 - S.card : ℕ) : ℝ) = G.1 - S.card := by
      rw [Nat.cast_sub (by exact_mod_cast h2)]
    have h4 : ((G.1 - S.card : ℕ) : ℝ) ≤ (univ.filter fun v ↦ G.color k c v < k).card := by
      exact_mod_cast h1
    linarith

/-- **Theorem 1.8 (2)** of [BHSV25] (Corollary 8.3). -/
theorem expanderColoring_repeatedRows_hardness (hUGC : UniqueGames.UGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (hrows : ¬ Function.Injective M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε lam : ℝ, 0 < ε → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M ε →
          G.IsColoring k δ (A G)) →
        NPSubsetP := by
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
  refine ⟨alpha M π' / 2, by positivity, fun ε lam hε hlam A hA hsolve ↦ ?_⟩
  refine expanderColoring_hardness hUGC M hM π' hπ' (alpha M π' / 2) ε lam (by positivity) hε
    hlam A hA fun G h1 h2 h3 ↦ ?_
  rw [show alpha M π' - alpha M π' / 2 = alpha M π' / 2 by ring]
  exact hsolve G h1 h2 h3

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

/-- **Theorem 1.5** of [BHSV25] (Corollary 8.4). -/
theorem threeColoring_unbalanced_hardness (hUGC : UniqueGames.UGC) :
    ∀ ε γ lam : ℝ, 0 < ε → 0 < γ → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 ε →
          G.IsColoring 3 (1 / 2 - γ) (A G)) →
        NPSubsetP := by
  intro ε γ lam hε hγ hlam A hA hsolve
  refine expanderColoring_hardness hUGC M3 isModel_M3 π3 isStationary_M3 γ ε lam hγ hε hlam A hA
    fun G h1 h2 h3 ↦ ?_
  rw [alpha_M3]
  exact hsolve G h1 h2 (hasColoring_of_mColorable G h3)

end BHSV25.Hard
