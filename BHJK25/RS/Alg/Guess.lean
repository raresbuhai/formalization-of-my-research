module

public import BHJK25.RS.Alg.Basic
public import BHJK25.RS.Basic.Cells
public import BHJK25.RS.Basic.Lists
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Guesses as indices, and the bits that the algorithm reads

The indices `idx < n^L` are the guesses: through `finFunctionFinEquiv`, an index is its `L` digits
in base `n`, a function `f : Fin L → Fin n`, and through the positions
`(s, b, t) ↦ (s (k - 1) + b) ℓ + t` (`BHJK25.RS.AlgAux.posEquiv`, a bijection onto `Fin L`), this
is the guess `BHJK25.RS.AlgAux.guessOf f`. Every guess arises this way
(`BHJK25.RS.AlgAux.guessOf_surjective`). The digits are distinct exactly when the guess is valid
(`BHJK25.RS.AlgAux.nodupB_digits`), and a vertex is a column exactly when it is not a digit
(`BHJK25.RS.AlgAux.not_mem_digits`).

For a valid guess and a column `v`, the bit that the algorithm reads from the table at
`BHJK25.RS.AlgAux.tabIdx` is the entry of the tensor at the cell of `v`
(`BHJK25.RS.AlgAux.getD_tabIdx`), so the bit lists that it reads are those of the field elements
`α_v` and `β_v` (`BHJK25.RS.AlgAux.bitList_eq`).
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

open Function

variable {k T n : ℕ}

/-! ### Positions -/

/-- The positions of the guessed vertices: side `s`, block `b` and position `t` at the digit
`(s (k - 1) + b) ℓ + t`. -/
def posEquiv (k l : ℕ) : Fin 2 × Fin (k - 1) × Fin l ≃ Fin (2 * (k - 1) * l) :=
  ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans
    (finProdFinEquiv.trans (finCongr (Nat.mul_assoc 2 (k - 1) l).symm))

theorem posEquiv_val (l : ℕ) (x : Fin 2 × Fin (k - 1) × Fin l) :
    (posEquiv k l x : ℕ) = pos k l x.1 x.2.1 x.2.2 := by
  simp [posEquiv, finProdFinEquiv_apply_val, pos]
  ring

/-! ### Guesses from indices -/

/-- The guess whose vertex at side `s`, block `b` and position `t` is the digit
`f ((s (k - 1) + b) ℓ + t)`. -/
def guessOf (f : Fin (2 * (k - 1) * ell k T n) → Fin n) : Guess k T n :=
  fun s b t ↦ f (posEquiv k (ell k T n) (s, b, t))

theorem guessOf_surjective : Surjective (guessOf (k := k) (T := T) (n := n)) := by
  intro g
  refine ⟨fun j ↦ g ((posEquiv k (ell k T n)).symm j).1 ((posEquiv k (ell k T n)).symm j).2.1
    ((posEquiv k (ell k T n)).symm j).2.2, ?_⟩
  funext s b t
  simp [guessOf]

theorem valid_guessOf (f : Fin (2 * (k - 1) * ell k T n) → Fin n) :
    (guessOf f).Valid ↔ Injective f :=
  Equiv.injective_comp (posEquiv k (ell k T n)) f

/-- Digit `j` of the index of `f` is `f j`. -/
theorem dig_eq {L : ℕ} (f : Fin L → Fin n) (j : Fin L) :
    dig n (finFunctionFinEquiv f) j = f j := by
  have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv f) j
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

theorem digits_eq (w : List Bool) (f : Fin (2 * (k - 1) * ell k T n) → Fin n) :
    digits (mkDat k T n w) (finFunctionFinEquiv f) = List.ofFn fun j ↦ (f j : ℕ) := by
  refine List.ext_getElem (by simp [digits, mkDat]) fun j h₁ h₂ ↦ ?_
  simp only [digits, mkDat, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact dig_eq f ⟨j, by simpa [digits, mkDat] using h₁⟩

theorem nodupB_iff (l : List ℕ) : nodupB l = true ↔ l.Nodup := by
  rw [nodupB, beq_iff_eq]
  constructor
  · intro h
    exact List.dedup_eq_self.1 ((List.dedup_sublist _).eq_of_length h)
  · intro h
    rw [List.dedup_eq_self.2 h]

/-- The digits are distinct exactly when the guess is valid. -/
theorem nodupB_digits (w : List Bool) (f : Fin (2 * (k - 1) * ell k T n) → Fin n) :
    nodupB (digits (mkDat k T n w) (finFunctionFinEquiv f)) = true ↔ (guessOf f).Valid := by
  rw [nodupB_iff, valid_guessOf, digits_eq, List.nodup_ofFn]
  exact Fin.val_injective.of_comp_iff f

/-- A vertex is a column exactly when it is not a digit. -/
theorem not_mem_digits (w : List Bool) (f : Fin (2 * (k - 1) * ell k T n) → Fin n) (v : Fin n) :
    (v : ℕ) ∉ digits (mkDat k T n w) (finFunctionFinEquiv f) ↔ IsCol (guessOf f) v := by
  rw [digits_eq, List.mem_ofFn]
  constructor
  · intro h s b t hv
    exact h ⟨_, congrArg Fin.val hv⟩
  · rintro h ⟨j, hj⟩
    have := h ((posEquiv k (ell k T n)).symm j).1 ((posEquiv k (ell k T n)).symm j).2.1
      ((posEquiv k (ell k T n)).symm j).2.2
    simp only [guessOf, Prod.mk.eta, Equiv.apply_symm_apply] at this
    exact this (Fin.ext hj)

/-! ### The bits of the table -/

open Classical in
/-- The entry of the table at the index of an injective tuple is the entry of the tensor at its
set of values. -/
theorem getD_table (M : Tensor k n) (tup : Fin k → Fin n) (h : Injective tup) :
    (table M).getD (∑ i, (tup i : ℕ) * n ^ (i : ℕ)) false =
      M ⟨Finset.univ.image tup, by
        rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]⟩ := by
  rw [← finFunctionFinEquiv_apply, List.getD_eq_getElem _ _ (by
    simp only [table, List.length_ofFn]
    exact (finFunctionFinEquiv tup).2)]
  simp only [table, List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply, h, ↓reduceDIte]

/-- The tuple of the cell carrying bit `i` of side `s` of the column `v`. -/
def cellTuple (g : Guess k T n) (s : Fin 2) (v : Fin n) (i : ℕ) : Fin k → Fin n :=
  fun j ↦ if h : (j : ℕ) < k - 1 then g s ⟨j, h⟩ (digit k T n i ⟨j, h⟩) else v

theorem cellTuple_injective {g : Guess k T n} (hg : g.Valid) {v : Fin n} (hv : IsCol g v)
    (s : Fin 2) (i : ℕ) : Injective (cellTuple g s v i) := by
  intro j₁ j₂ h
  simp only [cellTuple] at h
  split_ifs at h with h₁ h₂ h₂
  · exact Fin.ext (Fin.mk.inj_iff.1 (valid_eq hg h).2.1)
  · exact absurd h (hv _ _ _)
  · exact absurd h.symm (hv _ _ _)
  · exact Fin.ext (by omega)

theorem image_cellTuple (hk : 1 ≤ k) (g : Guess k T n) (s : Fin 2) (v : Fin n) (i : ℕ) :
    Finset.univ.image (cellTuple g s v i) = cell g s v i := by
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and, cell, Finset.mem_insert, cellTuple]
  constructor
  · rintro ⟨j, hj⟩
    split_ifs at hj with h
    · exact Or.inr ⟨⟨j, h⟩, hj⟩
    · exact Or.inl hj.symm
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨⟨k - 1, by omega⟩, by simp⟩
    · exact ⟨⟨b, by omega⟩, by simp⟩

theorem readAt_cell (hk : 1 ≤ k) {g : Guess k T n} (hg : g.Valid) {v : Fin n} (hv : IsCol g v)
    (M : Tensor k n) (s : Fin 2) (i : ℕ) :
    (table M).getD (∑ j, (cellTuple g s v i j : ℕ) * n ^ (j : ℕ)) false =
      readAt M (cell g s v i) := by
  rw [getD_table M _ (cellTuple_injective hg hv s i)]
  simp only [readAt, card_cell hk hg hv s i, ↓reduceDIte]
  congr 1
  exact Subtype.ext (image_cellTuple hk g s v i)

/-- The index of the cell computed by the algorithm is that of the tuple of the cell. -/
theorem tabIdx_eq (hk : 1 ≤ k) (w : List Bool) (f : Fin (2 * (k - 1) * ell k T n) → Fin n)
    (s : Fin 2) (v : Fin n) (i : ℕ) :
    tabIdx k (mkDat k T n w) (finFunctionFinEquiv f) s v i =
      ∑ j, (cellTuple (guessOf f) s v i j : ℕ) * n ^ (j : ℕ) := by
  let G : ℕ → ℕ := fun j ↦ if h : j < k - 1 then
    (guessOf f s ⟨j, h⟩ (digit k T n i ⟨j, h⟩) : ℕ) * n ^ j else v * n ^ j
  have hG : ∀ j : Fin k, (cellTuple (guessOf f) s v i j : ℕ) * n ^ (j : ℕ) = G j := by
    intro j
    simp only [cellTuple, G]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl fun j _ ↦ hG j, Fin.sum_univ_eq_sum_range G k,
    show Finset.range k = Finset.range (k - 1 + 1) by rw [Nat.sub_add_cancel hk],
    Finset.sum_range_succ]
  simp only [tabIdx, mkDat, sum_map_range]
  congr 1
  · refine Finset.sum_congr rfl fun b hb ↦ ?_
    have hb' : b < k - 1 := Finset.mem_range.1 hb
    simp only [G, hb', ↓reduceDIte]
    congr 1
    have hpos := posEquiv_val (k := k) (ell k T n) (s, ⟨b, hb'⟩, digit k T n i ⟨b, hb'⟩)
    simp only [digit] at hpos
    rw [← hpos, dig_eq]
    rfl
  · simp [G]

/-- **The algorithm reads the cells**: for a valid guess and a column `v`, the bit at the index
computed by the algorithm is the entry at the cell carrying bit `i` of side `s` of `v`. -/
theorem getD_tabIdx (hk : 1 ≤ k) (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n)
    (hg : (guessOf f).Valid) {v : Fin n} (hv : IsCol (guessOf f) v) (s : Fin 2) (i : ℕ) :
    (table M).getD (tabIdx k (mkDat k T n (table M)) (finFunctionFinEquiv f) s v i) false =
      readAt M (cell (guessOf f) s v i) := by
  rw [tabIdx_eq hk, readAt_cell hk hg hv]

theorem eltList_ofBits (c : Fin (rbits T n) → Bool) :
    eltList (ofBits c) = List.ofFn fun i ↦ (c i).toNat := by
  unfold eltList bitEquiv
  rw [Equiv.ofBijective_symm_apply_apply]

/-- **The bit lists are those of the field elements** `α_v` and `β_v`. -/
theorem bitList_eq (hk : 1 ≤ k) (M : Tensor k n) (f : Fin (2 * (k - 1) * ell k T n) → Fin n)
    (hg : (guessOf f).Valid) {v : Fin n} (hv : IsCol (guessOf f) v) (s : Fin 2) :
    bitList k (mkDat k T n (table M)) (finFunctionFinEquiv f) s v =
      eltList (readElt (guessOf f) s M v) := by
  rw [readElt, eltList_ofBits]
  refine List.ext_getElem (by simp [bitList, mkDat]) fun i h₁ h₂ ↦ ?_
  simp only [bitList, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [show (mkDat k T n (table M)).w = table M from rfl, getD_tabIdx hk M f hg hv s i]

end BHJK25.RS.AlgAux
