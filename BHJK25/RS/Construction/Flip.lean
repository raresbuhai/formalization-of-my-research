module

public import BHJK25.RS.Construction.Field
public import BHJK25.RS.Basic.Cells

/-!
# Flipping one entry of the planted tensor

Let `A` be a nonempty set of at most `m` entries. Some entry `S ∈ A` can be flipped by an
injective map of the randomness of the planted tensor (`BHJK25.RS.Sample`) that keeps the other
entries of `A` (`BHJK25.RS.ConsAux.exists_flip`). The maps are involutions:

* if every entry of `A` is a cell of some `α_v`, add `U^i` to `α_v` (`flipAlpha`); the `β_w`
  change, but no entry of `A` carries them;
* a padding entry is flipped directly (`flipPad`);
* bit `i` of `β_v` is flipped by adding `U^i` to `β'_v` when `α_v` is not unique among the
  columns, and otherwise by adding to the coefficients `x` those of a polynomial `p` of degree
  `< |A| ≤ m` with `p(α_v) = U^i` and `p(α_w) = 0` for the other columns `w` with a `β`-cell in
  `A` (`flipBeta`, `shiftPoly`).
-/

@[expose] public section

namespace BHJK25.RS.ConsAux

open Polynomial

variable {k T n : ℕ}

theorem cell_cases (h : 2 * (k - 1) * ell k T n < n) (S : KSet k n) :
    IsCellOf h 0 S ∨ IsCellOf h 1 S ∨ (¬IsCellOf h 0 S ∧ ¬IsCellOf h 1 S) := by
  tauto

/-! ### Flipping a bit of `α_v` -/

/-- Add `U^i` to `α_v`. -/
noncomputable def flipAlpha (v : Fin n) (i : Fin (rbits T n)) (ω : Sample k T n) :
    Sample k T n :=
  (ω.1, Function.update ω.2.1 v (ω.2.1 v + unitBit i), ω.2.2.1, ω.2.2.2)

theorem flipAlpha_involutive (v : Fin n) (i : Fin (rbits T n)) :
    Function.Involutive (flipAlpha (k := k) v i) := by
  intro ω
  simp only [flipAlpha, Function.update_self, Function.update_idem, add_assoc, add_self,
    add_zero, Function.update_eq_self]

theorem flip_alpha (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) {v : Fin n}
    (hv : IsCol (layout h) v) (i : Fin (rbits T n)) {S : KSet k n}
    (hS : S.1 = cell (layout h) 0 v i) {A : Finset (KSet k n)} (hA : ∀ S' ∈ A, IsCellOf h 0 S')
    (ω : Sample k T n) :
    encode h (flipAlpha v i ω) S = !encode h ω S ∧
      ∀ S' ∈ A, S' ≠ S → encode h (flipAlpha v i ω) S' = encode h ω S' := by
  refine ⟨?_, fun S' hS' hne ↦ ?_⟩
  · rw [encode_alpha hk h _ hv i hS, encode_alpha hk h _ hv i hS]
    simp only [flipAlpha, Function.update_self, bits_add_unitBit_self]
  · obtain ⟨w, j, hw, hS'w⟩ := hA S' hS'
    rw [encode_alpha hk h _ hw j hS'w, encode_alpha hk h _ hw j hS'w]
    simp only [flipAlpha]
    by_cases hwv : w = v
    · subst hwv
      have hji : j ≠ i := by
        rintro rfl
        exact hne (Subtype.ext (hS'w.trans hS.symm))
      rw [Function.update_self, bits_add_unitBit_of_ne _ hji]
    · rw [Function.update_of_ne hwv]

/-! ### Flipping a padding bit -/

/-- Flip the padding bit at `S`. -/
noncomputable def flipPad (S : KSet k n) (ω : Sample k T n) : Sample k T n :=
  (ω.1, ω.2.1, ω.2.2.1, Function.update ω.2.2.2 S (!ω.2.2.2 S))

theorem flipPad_involutive (S : KSet k n) : Function.Involutive (flipPad (T := T) S) := by
  intro ω
  simp only [flipPad, Function.update_self, Function.update_idem, Bool.not_not,
    Function.update_eq_self]

theorem flip_pad (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) {S : KSet k n}
    (h0 : ¬IsCellOf h 0 S) (h1 : ¬IsCellOf h 1 S) (ω : Sample k T n) :
    encode h (flipPad S ω) S = !encode h ω S ∧
      ∀ S', S' ≠ S → encode h (flipPad S ω) S' = encode h ω S' := by
  refine ⟨?_, fun S' hne ↦ ?_⟩
  · rw [encode_pad h _ h0 h1, encode_pad h _ h0 h1]
    simp only [flipPad, Function.update_self]
  · rcases cell_cases h S' with ⟨w, j, hw, hS'⟩ | ⟨w, j, hw, hS'⟩ | ⟨h0', h1'⟩
    · rw [encode_alpha hk h _ hw j hS', encode_alpha hk h _ hw j hS']
      rfl
    · rw [encode_beta hk h _ hw j hS', encode_beta hk h _ hw j hS']
      rfl
    · rw [encode_pad h _ h0' h1', encode_pad h _ h0' h1']
      simp only [flipPad, Function.update_of_ne hne]

/-! ### Flipping a bit of `β_v` -/

open Classical in
/-- The columns `w ≠ v` with a `β`-cell in `A`. -/
noncomputable def betaCols (h : 2 * (k - 1) * ell k T n < n) (A : Finset (KSet k n))
    (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w ↦ w ≠ v ∧ ∃ S' ∈ A, ∃ j : Fin (rbits T n),
    IsCol (layout h) w ∧ S'.1 = cell (layout h) 1 w j

theorem mem_betaCols {h : 2 * (k - 1) * ell k T n < n} {A : Finset (KSet k n)} {v w : Fin n} :
    w ∈ betaCols h A v ↔ w ≠ v ∧ ∃ S' ∈ A, ∃ j : Fin (rbits T n),
      IsCol (layout h) w ∧ S'.1 = cell (layout h) 1 w j := by
  simp [betaCols]

/-- Fewer columns than entries carry the other `β`-cells of `A`. -/
theorem card_betaCols_lt (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n)
    {A : Finset (KSet k n)} {S : KSet k n} (hSA : S ∈ A) {v : Fin n} {i : Fin (rbits T n)}
    (hS : S.1 = cell (layout h) 1 v i) :
    (betaCols h A v).card < A.card := by
  classical
  let col : KSet k n → Fin n := fun S' ↦ if hc : IsCellOf h 1 S' then hc.choose else v
  have hsub : betaCols h A v ⊆ (A.erase S).image col := by
    intro w hw
    obtain ⟨hwv, S', hS'A, j, hwc, hS'⟩ := mem_betaCols.1 hw
    have hc : IsCellOf h 1 S' := ⟨w, j, hwc, hS'⟩
    refine Finset.mem_image.2 ⟨S', Finset.mem_erase.2 ⟨?_, hS'A⟩, ?_⟩
    · rintro rfl
      exact hwv (cell_inj hk (layout_valid h) hwc j.2 i.2 (hS'.symm.trans hS)).2.1
    · change (if hc : IsCellOf h 1 S' then hc.choose else v) = w
      rw [dite_eq_left hc]
      obtain ⟨hc1, hc2⟩ := hc.choose_spec.choose_spec
      exact (cell_inj hk (layout_valid h) hc1 hc.choose_spec.choose.2 j.2
        (hc2.symm.trans hS')).2.1
  calc (betaCols h A v).card ≤ ((A.erase S).image col).card := Finset.card_le_card hsub
    _ ≤ (A.erase S).card := Finset.card_image_le
    _ < A.card := Finset.card_erase_lt_of_mem hSA

/-- A polynomial `p` with `p(α_v) = U^i` (when `α_v` is unique among the columns) that vanishes at
`α_w` for the columns `w` of `betaCols`. -/
noncomputable def shiftPoly (h : 2 * (k - 1) * ell k T n < n) (A : Finset (KSet k n))
    (v : Fin n) (i : Fin (rbits T n)) (α : Fin n → Fld T n) : (Fld T n)[X] :=
  C (unitBit i * ((∏ w ∈ betaCols h A v, (X - C (α w))).eval (α v))⁻¹) *
    ∏ w ∈ betaCols h A v, (X - C (α w))

section Shift

variable {h : 2 * (k - 1) * ell k T n < n} {A : Finset (KSet k n)} {v : Fin n}
  {i : Fin (rbits T n)} {α : Fin n → Fld T n}

theorem natDegree_shiftPoly_le : (shiftPoly h A v i α).natDegree ≤ (betaCols h A v).card :=
  (natDegree_C_mul_le _ _).trans (natDegree_finsetProd_X_sub_C_eq_card _ _).le

theorem eval_shiftPoly_of_mem {w : Fin n} (hw : w ∈ betaCols h A v) :
    (shiftPoly h A v i α).eval (α w) = 0 := by
  have h0 : (∏ w ∈ betaCols h A v, (X - C (α w))).eval (α w) = 0 := by
    rw [eval_prod]
    exact Finset.prod_eq_zero hw (by simp)
  rw [shiftPoly, eval_mul, h0, mul_zero]

theorem eval_shiftPoly_self (hu : UniqueCol (layout h) α v) :
    (shiftPoly h A v i α).eval (α v) = unitBit i := by
  have hne : (∏ w ∈ betaCols h A v, (X - C (α w))).eval (α v) ≠ 0 := by
    rw [eval_prod, Finset.prod_ne_zero_iff]
    intro w hw
    obtain ⟨hwv, -, -, -, hwc, -⟩ := mem_betaCols.1 hw
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    exact (hu w hwc hwv).symm
  rw [shiftPoly, eval_mul, eval_C, mul_assoc, inv_mul_cancel₀ hne, mul_one]

end Shift

open Classical in
/-- Flip bit `i` of `β_v`: add `U^i` to `β'_v` if `α_v` is not unique among the columns, and the
coefficients of `shiftPoly` to `x` if it is. -/
noncomputable def flipBeta (h : 2 * (k - 1) * ell k T n < n) (A : Finset (KSet k n)) (v : Fin n)
    (i : Fin (rbits T n)) (ω : Sample k T n) : Sample k T n :=
  if UniqueCol (layout h) ω.2.1 v then
    (fun j ↦ ω.1 j + (shiftPoly h A v i ω.2.1).coeff j, ω.2.1, ω.2.2.1, ω.2.2.2)
  else (ω.1, ω.2.1, Function.update ω.2.2.1 v (ω.2.2.1 v + unitBit i), ω.2.2.2)

section FlipBeta

variable {h : 2 * (k - 1) * ell k T n < n} {A : Finset (KSet k n)} {v : Fin n}
  {i : Fin (rbits T n)}

theorem flipBeta_alpha (ω : Sample k T n) : (flipBeta h A v i ω).2.1 = ω.2.1 := by
  unfold flipBeta
  split_ifs <;> rfl

theorem flipBeta_pad (ω : Sample k T n) : (flipBeta h A v i ω).2.2.2 = ω.2.2.2 := by
  unfold flipBeta
  split_ifs <;> rfl

theorem flipBeta_involutive : Function.Involutive (flipBeta h A v i) := by
  rintro ⟨x, α, β', pad⟩
  by_cases hu : UniqueCol (layout h) α v
  · simp [flipBeta, hu, add_assoc, add_self]
  · simp [flipBeta, hu, add_assoc, add_self]

theorem sum_coeff_add {m : ℕ} (x : Fin m → Fld T n) (p : (Fld T n)[X]) (hp : p.natDegree < m)
    (a : Fld T n) :
    ∑ j : Fin m, (x j + p.coeff j) * a ^ (j : ℕ) = ∑ j, x j * a ^ (j : ℕ) + p.eval a := by
  rw [eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range (fun j ↦ p.coeff j * a ^ j),
    ← Finset.sum_add_distrib]
  simp_rw [add_mul]

theorem betaVal_flipBeta (hk : 2 ≤ k) {S : KSet k n} (hSA : S ∈ A) (hAm : A.card ≤ mdeg T n)
    (hS : S.1 = cell (layout h) 1 v i) (ω : Sample k T n) {w : Fin n}
    (hw : w = v ∨ w ∈ betaCols h A v) :
    betaVal (layout h) (flipBeta h A v i ω) w =
      betaVal (layout h) ω w + if w = v then unitBit i else 0 := by
  have hdeg : (shiftPoly h A v i ω.2.1).natDegree < mdeg T n :=
    natDegree_shiftPoly_le.trans_lt ((card_betaCols_lt hk h hSA hS).trans_le hAm)
  obtain ⟨x, α, β', pad⟩ := ω
  by_cases hu : UniqueCol (layout h) α v
  · have hω : flipBeta h A v i (x, α, β', pad) =
        (fun j ↦ x j + (shiftPoly h A v i α).coeff j, α, β', pad) := by
      simp [flipBeta, hu]
    rw [hω]
    unfold betaVal
    by_cases huw : UniqueCol (layout h) α w
    · simp only [huw, ite_true]
      rw [sum_coeff_add _ _ hdeg]
      rcases hw with rfl | hw
      · rw [eval_shiftPoly_self hu, ite_eq_left rfl]
      · rw [eval_shiftPoly_of_mem hw, ite_eq_right (mem_betaCols.1 hw).1]
    · have hwv : w ≠ v := by
        rintro rfl
        exact huw hu
      simp [huw, hwv]
  · have hω : flipBeta h A v i (x, α, β', pad) =
        (x, α, Function.update β' v (β' v + unitBit i), pad) := by
      simp [flipBeta, hu]
    rw [hω]
    unfold betaVal
    by_cases huw : UniqueCol (layout h) α w
    · have hwv : w ≠ v := by
        rintro rfl
        exact hu huw
      simp [huw, hwv]
    · by_cases hwv : w = v
      · subst hwv
        simp [huw]
      · simp [huw, hwv]

theorem flip_beta (hk : 2 ≤ k) {S : KSet k n} (hSA : S ∈ A) (hAm : A.card ≤ mdeg T n)
    (hv : IsCol (layout h) v) (hS : S.1 = cell (layout h) 1 v i) (ω : Sample k T n) :
    encode h (flipBeta h A v i ω) S = !encode h ω S ∧
      ∀ S' ∈ A, S' ≠ S → encode h (flipBeta h A v i ω) S' = encode h ω S' := by
  refine ⟨?_, fun S' hS'A hne ↦ ?_⟩
  · rw [encode_beta hk h _ hv i hS, encode_beta hk h _ hv i hS,
      betaVal_flipBeta hk hSA hAm hS ω (Or.inl rfl), ite_eq_left rfl, bits_add_unitBit_self]
  · rcases cell_cases h S' with ⟨w, j, hw, hS'⟩ | ⟨w, j, hw, hS'⟩ | ⟨h0', h1'⟩
    · rw [encode_alpha hk h _ hw j hS', encode_alpha hk h _ hw j hS', flipBeta_alpha]
    · rw [encode_beta hk h _ hw j hS', encode_beta hk h _ hw j hS']
      by_cases hwv : w = v
      · subst hwv
        have hji : j ≠ i := by
          rintro rfl
          exact hne (Subtype.ext (hS'.trans hS.symm))
        rw [betaVal_flipBeta hk hSA hAm hS ω (Or.inl rfl), ite_eq_left rfl,
          bits_add_unitBit_of_ne _ hji]
      · have hmem : w ∈ betaCols h A v := mem_betaCols.2 ⟨hwv, S', hS'A, j, hw, hS'⟩
        rw [betaVal_flipBeta hk hSA hAm hS ω (Or.inr hmem), ite_eq_right hwv, add_zero]
    · rw [encode_pad h _ h0' h1', encode_pad h _ h0' h1', flipBeta_pad]

end FlipBeta

/-- Some entry of a nonempty set `A` of at most `m` entries can be flipped by an injective map of
the randomness that keeps the other entries of `A`. -/
theorem exists_flip (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (A : Finset (KSet k n))
    (hA : A.Nonempty) (hAm : A.card ≤ mdeg T n) :
    ∃ S ∈ A, ∃ τ : Sample k T n → Sample k T n, Function.Injective τ ∧ ∀ ω,
      encode h (τ ω) S = !encode h ω S ∧
        ∀ S' ∈ A, S' ≠ S → encode h (τ ω) S' = encode h ω S' := by
  by_cases hall : ∀ S ∈ A, IsCellOf h 0 S
  · obtain ⟨S, hSA⟩ := hA
    obtain ⟨v, i, hv, hS⟩ := hall S hSA
    exact ⟨S, hSA, flipAlpha v i, (flipAlpha_involutive v i).injective,
      flip_alpha hk h hv i hS hall⟩
  · simp only [not_forall] at hall
    obtain ⟨S, hSA, h0⟩ := hall
    by_cases h1 : IsCellOf h 1 S
    · obtain ⟨v, i, hv, hS⟩ := h1
      exact ⟨S, hSA, flipBeta h A v i, flipBeta_involutive.injective,
        flip_beta hk hSA hAm hv hS⟩
    · exact ⟨S, hSA, flipPad S, (flipPad_involutive S).injective, fun ω ↦
        ⟨(flip_pad hk h h0 h1 ω).1, fun S' _ hne ↦ (flip_pad hk h h0 h1 ω).2 S' hne⟩⟩

end BHJK25.RS.ConsAux
