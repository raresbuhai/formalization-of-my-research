module

public import BHJK25.RS.Basic.Cells

/-!
# Prescribed agreements are unlikely

For a valid guess `g`, a set `J` of columns and a map `f : F → F`, the tensors with
`β_v = f(α_v)` for every `v ∈ J` are a fraction `q^{-|J|}` of all tensors: the `r |J|` cells
carrying the `β_v` are distinct entries, which are not cells carrying the `α_v`, and the condition
prescribes their bits as a function of the other entries.

The counting is `BHJK25.RS.NullAux.card_graph`: when the entries at an injective family of
positions `φ` are prescribed as a function `H` of the entries elsewhere, the tensors satisfying the
prescription times the `2^|κ|` values at those positions are all the tensors (adding to a tensor
satisfying the prescription any pattern of flips at the positions `φ` is a bijection).
-/

@[expose] public section

namespace BHJK25.RS.NullAux

open Function

/-! ### Prescribing some coordinates -/

section Graph

variable {ι κ : Type} {φ : κ → ι} {H : (ι → Bool) → κ → Bool}

/-- The pattern `z` at the positions `φ`, and `false` elsewhere. -/
noncomputable def flips (φ : κ → ι) (z : κ → Bool) : ι → Bool := extend φ z fun _ ↦ false

theorem flips_apply (hφ : Injective φ) (z : κ → Bool) (j : κ) : flips φ z (φ j) = z j :=
  hφ.extend_apply _ _ _

theorem flips_off (z : κ → Bool) {x : ι} (hx : ∀ j, φ j ≠ x) : flips φ z x = false :=
  extend_apply' _ _ _ fun ⟨j, hj⟩ ↦ hx j hj

/-- The tensor `M` with the flips `z` at the positions `φ`. -/
noncomputable def flip (φ : κ → ι) (M : ι → Bool) (z : κ → Bool) : ι → Bool :=
  fun x ↦ xor (M x) (flips φ z x)

theorem flip_off (M : ι → Bool) (z : κ → Bool) {x : ι} (hx : ∀ j, φ j ≠ x) :
    flip φ M z x = M x := by
  simp only [flip, flips_off z hx, Bool.xor_false]

theorem flip_flip (M : ι → Bool) (z : κ → Bool) : flip φ (flip φ M z) z = M := by
  funext x
  simp only [flip, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The flips that make `M` satisfy the prescription. -/
def fix (φ : κ → ι) (H : (ι → Bool) → κ → Bool) (M : ι → Bool) : κ → Bool :=
  fun j ↦ xor (M (φ j)) (H M j)

theorem H_flip
    (hH : ∀ M M' : ι → Bool, (∀ x, (∀ j, φ j ≠ x) → M x = M' x) → H M = H M')
    (M : ι → Bool) (z : κ → Bool) : H (flip φ M z) = H M :=
  hH _ _ fun _ hx ↦ flip_off M z hx

variable (hφ : Injective φ)
  (hH : ∀ M M' : ι → Bool, (∀ x, (∀ j, φ j ≠ x) → M x = M' x) → H M = H M')
include hφ hH

theorem flip_fix (M : ι → Bool) (j : κ) :
    flip φ M (fix φ H M) (φ j) = H (flip φ M (fix φ H M)) j := by
  rw [H_flip hH]
  simp only [flip, flips_apply hφ, fix, ← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]

/-- Tensors satisfying the prescription, with flips at the positions `φ`, are all tensors. -/
noncomputable def graphEquiv :
    {M : ι → Bool // ∀ j, M (φ j) = H M j} × (κ → Bool) ≃ (ι → Bool) where
  toFun p := flip φ p.1.1 p.2
  invFun M := (⟨flip φ M (fix φ H M), flip_fix hφ hH M⟩, fix φ H M)
  left_inv := by
    rintro ⟨⟨M, hM⟩, z⟩
    have hz : fix φ H (flip φ M z) = z := by
      funext j
      simp only [fix, H_flip hH, flip, flips_apply hφ, ← hM j]
      cases M (φ j) <;> cases z j <;> rfl
    ext x
    · simp only [hz, flip_flip]
    · simp only [hz]
  right_inv M := flip_flip M _

/-- Prescribing the entries at the positions `φ` divides the number of tensors by `2^|κ|`. -/
theorem card_graph [Fintype ι] [Fintype κ] [Fintype {M : ι → Bool // ∀ j, M (φ j) = H M j}] :
    Fintype.card {M : ι → Bool // ∀ j, M (φ j) = H M j} * 2 ^ Fintype.card κ =
      2 ^ Fintype.card ι := by
  classical
  have h := Fintype.card_congr (graphEquiv hφ hH)
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool] at h
  exact h

end Graph

/-! ### Prescribing the values `β_v` -/

variable {k T n : ℕ}

/-- The cell carrying bit `i` of `β_v`, as an entry. -/
def betaCell (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) (J : Finset (Fin n))
    (hJ : ∀ v ∈ J, IsCol g v) (p : J × Fin (rbits T n)) : KSet k n :=
  ⟨cell g 1 p.1 p.2, card_cell (by omega) hg (hJ _ p.1.2) 1 _⟩

theorem betaCell_injective (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) (J : Finset (Fin n))
    (hJ : ∀ v ∈ J, IsCol g v) : Injective (betaCell hk hg J hJ) := by
  rintro ⟨v, i⟩ ⟨v', i'⟩ h
  have h' := congrArg Subtype.val h
  obtain ⟨-, h1, h2⟩ := cell_inj hk hg (hJ _ v.2) i.2 i'.2 h'
  exact Prod.ext (Subtype.ext h1) (Fin.ext h2)

theorem readAt_betaCell (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) (J : Finset (Fin n))
    (hJ : ∀ v ∈ J, IsCol g v) (M : Tensor k n) (p : J × Fin (rbits T n)) :
    readAt M (cell g 1 p.1 p.2) = M (betaCell hk hg J hJ p) := by
  unfold readAt
  split_ifs with hc
  · rfl
  · exact absurd (card_cell (by omega) hg (hJ _ p.1.2) 1 _) hc

/-- The entries at the `α`-cells of the columns in `J` are not `β`-cells of these columns. -/
theorem readAt_alpha_eq (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) {J : Finset (Fin n)}
    (hJ : ∀ v ∈ J, IsCol g v) {M M' : Tensor k n}
    (h : ∀ x, (∀ p, betaCell hk hg J hJ p ≠ x) → M x = M' x) {v : Fin n} (hv : IsCol g v)
    (i : ℕ) : readAt M (cell g 0 v i) = readAt M' (cell g 0 v i) := by
  unfold readAt
  split_ifs with hc
  · refine h _ fun p hp ↦ ?_
    exact absurd (side_eq_of_cell_eq hk hg hv (congrArg Subtype.val hp).symm) (by decide)
  · rfl

/-- `β_v = f(α_v)` for the columns `v ∈ J` says that the bits on the `β`-cells are those of
`f(α_v)`. -/
theorem prescribed_iff (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) (J : Finset (Fin n))
    (hJ : ∀ v ∈ J, IsCol g v) (f : Fld T n → Fld T n) (M : Tensor k n) :
    (∀ v ∈ J, readElt g 1 M v = f (readElt g 0 M v)) ↔
      ∀ p : J × Fin (rbits T n), M (betaCell hk hg J hJ p) =
        (bitEquiv T n).symm (f (readElt g 0 M p.1)) p.2 := by
  have key : ∀ v : J, readElt g 1 M v =
      bitEquiv T n fun i ↦ M (betaCell hk hg J hJ (v, i)) := by
    intro v
    unfold readElt
    simp only [bitEquiv, Equiv.ofBijective_apply]
    congr 1
    funext i
    exact readAt_betaCell hk hg J hJ M (v, i)
  constructor
  · intro h p
    have h1 := h p.1 p.1.2
    rw [key p.1, ← Equiv.eq_symm_apply] at h1
    exact congrFun h1 p.2
  · intro h v hv
    rw [key ⟨v, hv⟩, ← Equiv.eq_symm_apply]
    funext i
    exact h (⟨v, hv⟩, i)

/-- **Prescribed agreements.** The tensors with `β_v = f(α_v)` for the columns `v ∈ J` of a
valid guess, times `q^|J| = 2^(r |J|)`, are all the tensors. -/
theorem card_prescribed (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) (J : Finset (Fin n))
    (hJ : ∀ v ∈ J, IsCol g v) (f : Fld T n → Fld T n)
    [Fintype {M : Tensor k n // ∀ v ∈ J, readElt g 1 M v = f (readElt g 0 M v)}] :
    Fintype.card {M : Tensor k n // ∀ v ∈ J, readElt g 1 M v = f (readElt g 0 M v)} *
        2 ^ (rbits T n * J.card) = 2 ^ Fintype.card (KSet k n) := by
  classical
  have hH : ∀ M M' : Tensor k n, (∀ x, (∀ p, betaCell hk hg J hJ p ≠ x) → M x = M' x) →
      (fun M : Tensor k n ↦ fun p : J × Fin (rbits T n) ↦
        (bitEquiv T n).symm (f (readElt g 0 M p.1)) p.2) M =
      (fun M : Tensor k n ↦ fun p : J × Fin (rbits T n) ↦
        (bitEquiv T n).symm (f (readElt g 0 M p.1)) p.2) M' := by
    intro M M' h
    funext p
    have : readElt g 0 M p.1 = readElt g 0 M' p.1 := by
      unfold readElt
      congr 1
      funext i
      exact readAt_alpha_eq hk hg hJ h (hJ _ p.1.2) i
    simp only [this]
  have h := card_graph (betaCell_injective hk hg J hJ) hH
  have hc : Fintype.card (J × Fin (rbits T n)) = rbits T n * J.card := by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Nat.mul_comm]
  rw [hc] at h
  rw [← h, Fintype.card_congr (Equiv.subtypeEquivRight (prescribed_iff hk hg J hJ f))]

end BHJK25.RS.NullAux
