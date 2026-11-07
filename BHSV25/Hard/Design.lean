module

public import BHSV25.Hard.Coloring
public import BHSV25.Hard.Dyadic

/-!
# Templates from designs

A **design** (`BHSV25.Hard.Design`) is the finite combinatorial data of a template: finitely
many types, each in one of `K` groups, dyadic densities `q i j / 2^r` between groups, and a
correction `W⁰` between types. Its template (`BHSV25.Hard.Design.template`) has the cells
`(τ, s)` for a type `τ` and `s ∈ Γ₀^r` (`BHSV25/Hard/Cayley.lean`): cells of different groups
`i, j` are adjacent when `hval (s + s') < q i j`, and `W ((τ, s), (τ', s')) = W⁰ τ τ'` if
`s = s'` and `0` otherwise.

* The template is `d₀ 4^(a r)`-regular if every type has `∑_{τ'} q (gr τ) (gr τ') = d₀` over the
  types of other groups (`BHSV25.Hard.Design.template`).
* It is close to its planted matrix `q (gr u) (gr u') / 2^r` (zero inside groups), with error
  `|types| · err a r` (`BHSV25.Hard.Design.template_approx`), by the pseudo-randomness of the sets
  `{hval < q}` (`BHSV25.Hard.Cayley.pr_lt`).
* Labels of the types give labels of the cells (`BHSV25.Hard.Design.labels`), valid when the
  conditions hold type by type (`BHSV25.Hard.Design.labels_valid`).
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Cayley

/-- A **design** of a template. -/
structure Design where
  /-- The types. -/
  Ty : Type
  [fin : Fintype Ty]
  [deq : DecidableEq Ty]
  /-- The number of groups. -/
  K : ℕ
  /-- The group of a type. -/
  gr : Ty → Fin K
  /-- The dyadic precision of the densities. -/
  r : ℕ
  /-- The densities between groups, in units of `2^(-r)`. -/
  q : Fin K → Fin K → ℕ
  /-- The degree in types. -/
  d₀ : ℕ
  /-- The correction between types. -/
  W0 : Ty → Ty → ℤ
  q_symm : ∀ i j, q i j = q j i
  q_le : ∀ i j, q i j ≤ 2 ^ r
  reg : ∀ τ, ∑ τ', (if gr τ ≠ gr τ' then q (gr τ) (gr τ') else 0) = d₀
  W0_symm : ∀ τ τ', W0 τ τ' = W0 τ' τ
  W0_cases : ∀ τ τ', W0 τ τ' = -1 ∨ W0 τ τ' = 0 ∨ W0 τ τ' = 1
  W0_neg : ∀ τ τ', W0 τ τ' = -1 → gr τ ≠ gr τ' ∧ 1 ≤ q (gr τ) (gr τ')
  W0_pos : ∀ τ τ', W0 τ τ' = 1 → gr τ = gr τ'
  W0_sum : ∀ τ, ∑ τ', W0 τ τ' = 0

attribute [instance] Design.fin Design.deq

namespace Design

variable (D : Design) (a : ℕ)

/-- The cells: a type and a point of `Γ₀^r`. -/
abbrev Cell := D.Ty × (Fin D.r → Gam0 a)

/-- The adjacency of cells. -/
def Tc (c c' : D.Cell a) : Prop :=
  D.gr c.1 ≠ D.gr c'.1 ∧ hval (c.2 + c'.2) < D.q (D.gr c.1) (D.gr c'.1)

instance (c c' : D.Cell a) : Decidable (D.Tc a c c') := by unfold Tc; infer_instance

/-- The correction between cells. -/
def Wc (c c' : D.Cell a) : ℤ := if c.2 = c'.2 then D.W0 c.1 c'.1 else 0

/-- The numbering of the cells. -/
noncomputable def eqv : D.Cell a ≃ Fin (Fintype.card (D.Cell a)) := Fintype.equivFin _

theorem add_self_gam {r : ℕ} (s : Fin r → Gam0 a) : s + s = 0 := by
  funext l
  simp only [Pi.add_apply, Pi.zero_apply]
  ext <;> simp [add_self_zmod2]

theorem hval_zero {r : ℕ} : hval (0 : Fin r → Gam0 a) = 0 := by
  simp [hval, bent]

theorem Tc_symm (c c' : D.Cell a) : D.Tc a c c' ↔ D.Tc a c' c := by
  unfold Tc
  rw [add_comm c.2, D.q_symm, ne_comm]

theorem Wc_cases (c c' : D.Cell a) : D.Wc a c c' = -1 ∨ D.Wc a c c' = 0 ∨ D.Wc a c c' = 1 := by
  unfold Wc; split_ifs
  · exact D.W0_cases _ _
  · exact Or.inr (Or.inl rfl)

theorem card_Tc (c : D.Cell a) :
    (univ.filter fun c' ↦ D.Tc a c c').card = D.d₀ * (4 ^ a) ^ D.r := by
  rw [card_filter, Fintype.sum_prod_type]
  have h : ∀ τ', (∑ s' : Fin D.r → Gam0 a, if D.Tc a c (τ', s') then 1 else 0) =
      (if D.gr c.1 ≠ D.gr τ' then D.q (D.gr c.1) (D.gr τ') else 0) * (4 ^ a) ^ D.r := by
    intro τ'
    by_cases hg : D.gr c.1 = D.gr τ'
    · simp [Tc, hg]
    · have hc := card_lt a D.r (D.q (D.gr c.1) (D.gr τ')) (D.q_le _ _)
      rw [← card_add_lt c.2] at hc
      rw [show (∑ s' : Fin D.r → Gam0 a, if D.Tc a c (τ', s') then 1 else 0) =
          (univ.filter fun s' : Fin D.r → Gam0 a ↦
            hval (c.2 + s') < D.q (D.gr c.1) (D.gr τ')).card by
        rw [card_filter]; exact sum_congr rfl fun s' _ ↦ by simp [Tc, hg]]
      rw [ite_eq_left hg]
      exact_mod_cast hc
  simp_rw [h, ← sum_mul, D.reg]

/-- The template of a design. -/
noncomputable abbrev template : Template where
  C := Fintype.card (D.Cell a)
  T u u' := decide (D.Tc a ((D.eqv a).symm u) ((D.eqv a).symm u'))
  W u u' := D.Wc a ((D.eqv a).symm u) ((D.eqv a).symm u')
  d := D.d₀ * (4 ^ a) ^ D.r
  T_symm u u' := by simp only [decide_eq_decide]; exact D.Tc_symm a _ _
  T_irrefl u := by simp [Tc]
  W_symm u u' := by
    unfold Wc
    by_cases h : ((D.eqv a).symm u).2 = ((D.eqv a).symm u').2
    · rw [ite_eq_left h, ite_eq_left h.symm, D.W0_symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  W_cases u u' := D.Wc_cases a _ _
  W_neg u u' h := by
    unfold Wc at h
    by_cases hs : ((D.eqv a).symm u).2 = ((D.eqv a).symm u').2
    · rw [ite_eq_left hs] at h
      obtain ⟨h1, h2⟩ := D.W0_neg _ _ h
      simp only [decide_eq_true_eq, Tc]
      refine ⟨h1, ?_⟩
      rw [hs, add_self_gam, hval_zero]
      exact h2
    · rw [ite_eq_right hs] at h
      exact absurd h (by decide)
  W_pos u u' h := by
    unfold Wc at h
    by_cases hs : ((D.eqv a).symm u).2 = ((D.eqv a).symm u').2
    · rw [ite_eq_left hs] at h
      simp [Tc, D.W0_pos _ _ h]
    · rw [ite_eq_right hs] at h
      exact absurd h (by decide)
  W_sum u := by
    rw [← Equiv.sum_comp (D.eqv a) (fun u' ↦ D.Wc a ((D.eqv a).symm u) ((D.eqv a).symm u'))]
    simp only [Equiv.symm_apply_apply]
    rw [Fintype.sum_prod_type]
    simp only [Wc, sum_ite_eq, mem_univ, ite_true]
    exact D.W0_sum _
  T_reg u := by
    rw [← D.card_Tc a ((D.eqv a).symm u)]
    refine card_bij (fun u' _ ↦ (D.eqv a).symm u') (by simp) (by simp)
      (fun c hc ↦ ⟨D.eqv a c, by simpa using hc, by simp⟩)

theorem card_gamr : Fintype.card (Fin D.r → Gam0 a) = (2 * 4 ^ a) ^ D.r := by
  rw [Fintype.card_fun, card_gam0, Fintype.card_fin]

theorem card_cell : Fintype.card (D.Cell a) = Fintype.card D.Ty * (2 * 4 ^ a) ^ D.r := by
  rw [Fintype.card_prod, card_gamr]

theorem sum_cells {β : Type*} [AddCommMonoid β] (F : Fin (Fintype.card (D.Cell a)) → β) :
    ∑ u, F u = ∑ τ, ∑ s, F (D.eqv a (τ, s)) := by
  rw [← Equiv.sum_comp (D.eqv a) F, Fintype.sum_prod_type]

/-- The group of a cell. -/
noncomputable def grc (u : Fin (Fintype.card (D.Cell a))) : Fin D.K :=
  D.gr ((D.eqv a).symm u).1

/-- The type of a cell. -/
noncomputable def typ (u : Fin (Fintype.card (D.Cell a))) : D.Ty := ((D.eqv a).symm u).1

/-- The planted densities between groups, `0` inside groups. -/
noncomputable def Chat (i j : Fin D.K) : ℝ := if i = j then 0 else (D.q i j : ℝ) / 2 ^ D.r

/-- **The template is close to its planted matrix.** -/
theorem template_approx (X Y : Fin (Fintype.card (D.Cell a)) → ℝ) :
    |∑ u, ∑ u', X u * (ind ((D.template a).T u u' = true) - D.Chat (D.grc a u) (D.grc a u')) *
      Y u'| ≤ (Fintype.card D.Ty * err a D.r) * (X ⬝ᵥ X + Y ⬝ᵥ Y) := by
  simp only [sum_cells, grc, Equiv.symm_apply_apply]
  have hcomm : ∀ τ, (∑ s, ∑ τ', ∑ s', X (D.eqv a (τ, s)) *
      (ind (decide (D.Tc a (τ, s) (τ', s')) = true) - D.Chat (D.gr τ) (D.gr τ')) *
        Y (D.eqv a (τ', s'))) = ∑ τ', ∑ s, ∑ s', X (D.eqv a (τ, s)) *
      (ind (decide (D.Tc a (τ, s) (τ', s')) = true) - D.Chat (D.gr τ) (D.gr τ')) *
        Y (D.eqv a (τ', s')) := fun τ ↦ sum_comm
  rw [sum_congr rfl fun τ _ ↦ hcomm τ]
  have hpt : ∀ τ τ', |∑ s, ∑ s', X (D.eqv a (τ, s)) *
      (ind (decide (D.Tc a (τ, s) (τ', s')) = true) - D.Chat (D.gr τ) (D.gr τ')) *
        Y (D.eqv a (τ', s'))| ≤
      err a D.r * (∑ s, X (D.eqv a (τ, s)) ^ 2 + ∑ s', Y (D.eqv a (τ', s')) ^ 2) := by
    intro τ τ'
    by_cases hg : D.gr τ = D.gr τ'
    · have : ∀ s s', ind (decide (D.Tc a (τ, s) (τ', s')) = true) -
          D.Chat (D.gr τ) (D.gr τ') = 0 := by
        intro s s'
        rw [ind_of_not (by simp [Tc, hg]), Chat, ite_eq_left hg, sub_zero]
      simp only [this, mul_zero, zero_mul, sum_const_zero, abs_zero]
      exact mul_nonneg (err_nonneg a D.r) (by positivity)
    · have h := pr_lt a D.r (D.q (D.gr τ) (D.gr τ')) (D.q_le _ _)
        (fun s ↦ X (D.eqv a (τ, s))) (fun s' ↦ Y (D.eqv a (τ', s')))
      have hrw : ∑ s, ∑ s', X (D.eqv a (τ, s)) *
          (ind (decide (D.Tc a (τ, s) (τ', s')) = true) - D.Chat (D.gr τ) (D.gr τ')) *
            Y (D.eqv a (τ', s')) =
          ∑ s, ∑ s', X (D.eqv a (τ, s)) * ind (hval (s + s') < D.q (D.gr τ) (D.gr τ')) *
            Y (D.eqv a (τ', s')) - ((D.q (D.gr τ) (D.gr τ') : ℝ) / 2 ^ D.r *
              ∑ s, X (D.eqv a (τ, s))) * ∑ s', Y (D.eqv a (τ', s')) := by
        have hpt2 : ∀ s s', X (D.eqv a (τ, s)) *
            (ind (decide (D.Tc a (τ, s) (τ', s')) = true) - D.Chat (D.gr τ) (D.gr τ')) *
              Y (D.eqv a (τ', s')) =
            X (D.eqv a (τ, s)) * ind (hval (s + s') < D.q (D.gr τ) (D.gr τ')) *
              Y (D.eqv a (τ', s')) - (D.q (D.gr τ) (D.gr τ') : ℝ) / 2 ^ D.r *
                (X (D.eqv a (τ, s)) * Y (D.eqv a (τ', s'))) := by
          intro s s'
          have hT : ind (decide (D.Tc a (τ, s) (τ', s')) = true) =
              ind (hval (s + s') < D.q (D.gr τ) (D.gr τ')) := by
            congr 1; simp [Tc, hg]
          rw [hT, Chat, ite_eq_right hg]
          ring
        simp only [hpt2, sum_sub_distrib, ← mul_sum, ← sum_mul]
        ring
      rw [hrw]
      exact h
  calc _ ≤ ∑ τ, ∑ τ', |∑ s, ∑ s', X (D.eqv a (τ, s)) *
        (ind (decide (D.Tc a (τ, s) (τ', s')) = true) - D.Chat (D.gr τ) (D.gr τ')) *
          Y (D.eqv a (τ', s'))| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun τ _ ↦ abs_sum_le_sum_abs _ _)
    _ ≤ ∑ τ, ∑ τ', err a D.r * (∑ s, X (D.eqv a (τ, s)) ^ 2 + ∑ s', Y (D.eqv a (τ', s')) ^ 2) :=
        sum_le_sum fun τ _ ↦ sum_le_sum fun τ' _ ↦ hpt τ τ'
    _ = _ := by
        simp only [dotProduct, sum_cells, ← mul_sum, sum_add_distrib, sum_const, card_univ,
          nsmul_eq_mul, sq]
        ring

/-- The rows of the correction have the absolute sums of the rows of `W⁰`. -/
theorem sum_abs_W (u : Fin (Fintype.card (D.Cell a))) :
    ∑ u', |((D.template a).W u u' : ℝ)| = ∑ τ', |(D.W0 (D.typ a u) τ' : ℝ)| := by
  rw [sum_cells]
  simp only [Equiv.symm_apply_apply, Wc, typ]
  refine sum_congr rfl fun τ' _ ↦ ?_
  rw [Fintype.sum_eq_single ((D.eqv a).symm u).2 (fun s hs ↦ by simp [Ne.symm hs])]
  simp

/-- Counting the cells by their types. -/
theorem card_cells (P : D.Ty → Prop) [DecidablePred P] :
    (univ.filter fun u : Fin (Fintype.card (D.Cell a)) ↦ P (D.typ a u)).card =
      (2 * 4 ^ a) ^ D.r * (univ.filter P).card := by
  rw [card_filter, sum_cells, card_filter, mul_sum]
  refine sum_congr rfl fun τ _ ↦ ?_
  simp only [typ, Equiv.symm_apply_apply, sum_const, card_univ, card_gamr, smul_eq_mul]

/-- Disjoint colors of two types. -/
def DisjT {k : ℕ} (c₁ c₂ : D.Ty → Fin k) (τ τ' : D.Ty) : Prop :=
  c₁ τ ≠ c₁ τ' ∧ c₁ τ ≠ c₂ τ' ∧ c₂ τ ≠ c₁ τ' ∧ c₂ τ ≠ c₂ τ'

/-- Labels of the cells from labels of the types. -/
noncomputable def labels {k : ℕ} (c₁ c₂ : D.Ty → Fin k) (garb : D.Ty → Prop)
    [DecidablePred garb] : (D.template a).Labels k where
  c₁ u := c₁ (D.typ a u)
  c₂ u := c₂ (D.typ a u)
  garbage u := garb (D.typ a u)

/-- **Valid labels from conditions on types.** -/
theorem labels_valid {k : ℕ} (c₁ c₂ : D.Ty → Fin k) (garb : D.Ty → Prop)
    [DecidablePred garb]
    (hT : ∀ τ τ', D.gr τ ≠ D.gr τ' → 0 < D.q (D.gr τ) (D.gr τ') → D.DisjT c₁ c₂ τ τ')
    (hW : ∀ τ τ', τ ≠ τ' → D.W0 τ τ' ≠ 0 → garb τ ∨ garb τ' ∨ D.DisjT c₁ c₂ τ τ')
    (hD : ∀ τ, D.W0 τ τ = 1 → garb τ ∨ c₁ τ ≠ c₂ τ) :
    (D.labels a c₁ c₂ garb).Valid where
  disj_T u u' h := by
    simp only [decide_eq_true_eq, Tc] at h
    exact hT _ _ h.1 (lt_of_le_of_lt (Nat.zero_le _) h.2)
  disj_W u u' hne h := by
    simp only [Wc] at h
    split_ifs at h with hs
    · have hτ : D.typ a u ≠ D.typ a u' := by
        intro hτ
        apply hne
        have : (D.eqv a).symm u = (D.eqv a).symm u' := Prod.ext hτ hs
        simpa using this
      exact hW _ _ hτ h
    · exact absurd rfl h
  diag u h := by
    simp only [Wc, ite_true] at h
    exact hD _ h

end Design

end BHSV25.Hard
