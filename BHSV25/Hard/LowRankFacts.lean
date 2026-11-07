module

public import BHSV25.Hard.LowRankDesign

/-!
# The design for Theorem 1.6: labels and counts

The coloring of the yes-instances (`BHSV25.Hard.LowRank.labels`): block `b` of the design of
`BHSV25/Hard/LowRankDesign.lean` has colors `col₁ b` (outside `J`) and `col₂ b` (on `J`), and the
garbage types are the absorbers. Every color is `col₁` of `3` blocks and `col₂` of `3` blocks,
so each color class has a third of the vertices (`BHSV25.Hard.LowRank.card_col₁`).
-/

@[expose] public section

namespace BHSV25.Hard.LowRank

open Finset

variable (m : ℕ)

/-- The color outside `J` of a block. -/
def col₁ (b : Fin 9) : Fin 3 := ![2, 2, 0, 1, 0, 0, 1, 1, 2] b

/-- The color on `J` of a block. -/
def col₂ (b : Fin 9) : Fin 3 := ![2, 2, 1, 0, 0, 0, 1, 1, 2] b

/-- The absorbers. -/
def garb (τ : Ty m) : Prop := absB τ.1 ∧ (τ.2.2 : ℕ) = 0

instance : DecidablePred (garb m) := fun τ ↦ by unfold garb; infer_instance

theorem colors_disj (b b' : Fin 9) (h : grB b ≠ grB b') (hq : 0 < q (grB b) (grB b')) :
    col₁ b ≠ col₁ b' ∧ col₁ b ≠ col₂ b' ∧ col₂ b ≠ col₁ b' ∧ col₂ b ≠ col₂ b' := by
  revert b b'; decide

theorem real_colors (b : Fin 9) (h : realB b) : col₁ b ≠ col₂ b := by
  revert b; decide

theorem absB_of_real {b b' : Fin 9} (h : realB b) (h' : (b' : ℕ) + 2 = b) : absB b' := by
  simp only [realB, absB, Fin.ext_iff] at h ⊢; omega

/-- **The labels are valid.** -/
theorem labels_valid (a : ℕ) :
    ((design m).labels a (fun τ ↦ col₁ τ.1) (fun τ ↦ col₂ τ.1) (garb m)).Valid := by
  refine Design.labels_valid (design m) a _ _ _ (fun τ τ' h hq ↦ colors_disj τ.1 τ'.1 h hq)
    (fun τ τ' hne hW ↦ ?_) (fun τ h ↦ ?_)
  · by_contra hc
    simp only [not_or, garb] at hc
    apply hW
    change W0 m τ τ' = 0
    unfold W0 zi
    rw [ite_eq_right (fun h ↦ hne h.2.symm), ite_eq_right (fun h ↦ hc.1 ⟨h.1, h.2.2.1⟩),
      ite_eq_right (fun h ↦ hc.2.1 ⟨absB_of_real h.1 h.2.1, h.2.2.2⟩),
      ite_eq_right (fun h ↦ hc.1 ⟨h.1, h.2.2.2⟩)]
    norm_num
  · change W0 m τ τ = 1 at h
    by_cases hr : realB τ.1
    · exact Or.inr (real_colors _ hr)
    · left
      by_contra hg
      unfold W0 zi at h
      rw [ite_eq_right (fun h ↦ hr h.1), ite_eq_right (fun h' ↦ hg ⟨h'.1, h'.2.2.1⟩),
        ite_eq_right (fun h ↦ hr h.1), ite_eq_right (fun h' ↦ hg ⟨h'.1, h'.2.2.2⟩)] at h
      norm_num at h

theorem card_block (P : Fin 9 → Prop) [DecidablePred P] :
    (univ.filter fun τ : Ty m ↦ P τ.1).card = (univ.filter P).card * (m * m) := by
  rw [card_filter, Fintype.sum_prod_type, card_filter, sum_mul]
  refine sum_congr rfl fun b _ ↦ ?_
  split_ifs <;> simp

theorem card_col₁ (c : Fin 3) :
    (univ.filter fun τ : Ty m ↦ col₁ τ.1 = c).card = 3 * m ^ 2 := by
  rw [card_block m (fun b ↦ col₁ b = c),
    show (univ.filter fun b ↦ col₁ b = c).card = 3 by revert c; decide]
  ring

theorem card_col₂ (c : Fin 3) :
    (univ.filter fun τ : Ty m ↦ col₂ τ.1 = c).card = 3 * m ^ 2 := by
  rw [card_block m (fun b ↦ col₂ b = c),
    show (univ.filter fun b ↦ col₂ b = c).card = 3 by revert c; decide]
  ring

theorem card_garb : (univ.filter fun τ : Ty m ↦ garb m τ).card = 2 * m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : (univ.filter fun τ : Ty m ↦ garb m τ) =
      (univ.filter absB) ×ˢ ((univ : Finset (Fin m)) ×ˢ {(⟨0, hm⟩ : Fin m)}) := by
    ext ⟨b, α, β⟩
    rw [mem_filter, mem_product, mem_product, mem_filter, mem_singleton, Fin.ext_iff]
    simp only [mem_univ, true_and, garb]
  rw [this, card_product, card_product, card_singleton, card_univ, Fintype.card_fin,
    show (univ.filter absB).card = 2 by decide]
  ring

theorem W0_real {τ : Ty m} (h : realB τ.1) : W0 m τ τ = 1 := by
  have hab : ¬ absB τ.1 := by simp only [realB, absB, Fin.ext_iff] at h ⊢; omega
  unfold W0 zi
  rw [ite_eq_left ⟨h, rfl⟩, ite_eq_right (fun h' ↦ hab h'.1), ite_eq_right (fun h' ↦ by omega),
    ite_eq_right (fun h' ↦ hab h'.1)]
  norm_num

theorem card_real_le : 2 * m ^ 2 ≤ (univ.filter fun τ : Ty m ↦ W0 m τ τ = 1).card := by
  have h1 : (univ.filter fun τ : Ty m ↦ realB τ.1).card = 2 * m ^ 2 := by
    rw [card_block m realB, show (univ.filter realB).card = 2 by decide]; ring
  rw [← h1]
  exact card_le_card fun τ hτ ↦ by
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢; exact W0_real m hτ

theorem card_ty : Fintype.card (Ty m) = 9 * m ^ 2 := by
  simp [Fintype.card_prod]; ring

end BHSV25.Hard.LowRank
