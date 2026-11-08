module

public import BHJK25.RS.Basic.Cells

/-!
# The cells of a column

The entries of the tensor at the `2r` cells of a column `v` (`BHJK25.RS.PlantedAux.cellSet`): there
are at most `2r` of them, and those of distinct columns are distinct, since the only column in a
cell of `v` is `v` (`BHJK25.RS.eq_of_mem_cell`).
-/

@[expose] public section

namespace BHJK25.RS.PlantedAux

open Finset

variable {k T n : ℕ}

/-- The cells of the column `v` of the layout, as entries. -/
def cellSet (g : Guess k T n) (v : Fin n) : Finset (KSet k n) :=
  univ.filter fun S ↦ ∃ s : Fin 2, ∃ i : Fin (rbits T n), S.1 = cell g s v i

theorem mem_cellSet {g : Guess k T n} {v : Fin n} {S : KSet k n} :
    S ∈ cellSet g v ↔ ∃ s : Fin 2, ∃ i : Fin (rbits T n), S.1 = cell g s v i := by
  simp [cellSet]

/-- A column has at most `2r` cells. -/
theorem card_cellSet_le (g : Guess k T n) (v : Fin n) : (cellSet g v).card ≤ 2 * rbits T n := by
  calc (cellSet g v).card
      ≤ ((univ : Finset (Fin 2 × Fin (rbits T n))).image fun p ↦ cell g p.1 v p.2).card := by
        refine card_le_card_of_injOn (fun S ↦ S.1) (fun S hS ↦ ?_) Subtype.val_injective.injOn
        obtain ⟨s, i, hS⟩ := mem_cellSet.1 (mem_coe.1 hS)
        simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range, Prod.exists]
        exact ⟨s, i, hS.symm⟩
    _ ≤ (univ : Finset (Fin 2 × Fin (rbits T n))).card := card_image_le
    _ = 2 * rbits T n := by simp

/-- The cells of distinct columns are distinct. -/
theorem cellSet_disjoint {g : Guess k T n} {v w : Fin n} (hv : IsCol g v) (hvw : v ≠ w) :
    Disjoint (cellSet g v) (cellSet g w) := by
  rw [disjoint_left]
  intro S hSv hSw
  obtain ⟨s, i, hi⟩ := mem_cellSet.1 hSv
  obtain ⟨s', i', hi'⟩ := mem_cellSet.1 hSw
  have hmem : v ∈ cell g s' w i' := hi' ▸ hi ▸ self_mem_cell g s v i
  exact hvw (eq_of_mem_cell hv hmem)

end BHJK25.RS.PlantedAux
