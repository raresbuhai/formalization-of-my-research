module

public import BHJK25.RS.Basic.Params

/-!
# Cells, the hidden layout and the planted bits

Facts about the cells of a guess (`BHJK25.RS.cell`), used by the several parts of the proof.

* Two numbers below `ℓ^(k-1)` with the same `k - 1` digits in base `ℓ` are equal
  (`BHJK25.RS.eq_of_digits`), so two bits `i, i' < r ≤ ℓ^(k-1)` with the same digits are equal
  (`BHJK25.RS.eq_of_digit_eq`).
* For a valid guess `g` and a column `v` (`k ≥ 2`): each cell `cell g s v i` is a set of `k`
  vertices (`BHJK25.RS.card_cell`); the only column in it is `v`; and it determines its side, its
  column and its bit `i < r` (`BHJK25.RS.cell_inj`). In particular an `α`-cell is never a
  `β`-cell (`BHJK25.RS.side_eq_of_cell_eq`).
* The hidden layout is a valid guess (`BHJK25.RS.layout_valid`). So the planted tensor
  (`BHJK25.RS.encode`) carries bit `i` of `α_v` at the cell of bit `i` of side `0` of a column `v`
  of the layout (`BHJK25.RS.encode_alpha`), bit `i` of `β_v` at the cell of bit `i` of side `1`
  (`BHJK25.RS.encode_beta`), and a padding bit at every other entry (`BHJK25.RS.encode_pad`).
-/

@[expose] public section

namespace BHJK25.RS

open Finset

variable {k T n : ℕ}

/-! ### Digits -/

/-- Numbers below `l^d` with the same first `d` digits in base `l` are equal. -/
theorem eq_of_digits {l : ℕ} : ∀ {d i j : ℕ}, i < l ^ d → j < l ^ d →
    (∀ b < d, i / l ^ b % l = j / l ^ b % l) → i = j
  | 0, i, j, hi, hj, _ => by
    rw [pow_zero] at hi hj
    omega
  | d + 1, i, j, hi, hj, h => by
    have hl : 0 < l := by
      rcases Nat.eq_zero_or_pos l with rfl | hl
      · rw [zero_pow (Nat.succ_ne_zero d)] at hi
        omega
      · exact hl
    have h0 := h 0 (Nat.succ_pos d)
    rw [pow_zero, Nat.div_one, Nat.div_one] at h0
    have hi' : i / l < l ^ d := by
      rw [Nat.div_lt_iff_lt_mul hl, ← pow_succ]
      exact hi
    have hj' : j / l < l ^ d := by
      rw [Nat.div_lt_iff_lt_mul hl, ← pow_succ]
      exact hj
    have hq : i / l = j / l := by
      refine eq_of_digits hi' hj' fun b hb ↦ ?_
      have := h (b + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    rw [← Nat.div_add_mod i l, ← Nat.div_add_mod j l, hq, h0]

/-- Two numbers below `r` with the same digits in base `ℓ` are equal. -/
theorem eq_of_digit_eq (hk : 2 ≤ k) {i j : ℕ} (hi : i < rbits T n) (hj : j < rbits T n)
    (h : ∀ b, digit k T n i b = digit k T n j b) : i = j := by
  have hr := rbits_le_pow_ell hk T n
  refine eq_of_digits (lt_of_lt_of_le hi hr) (lt_of_lt_of_le hj hr) fun b hb ↦ ?_
  have := congrArg Fin.val (h ⟨b, hb⟩)
  simpa [digit] using this

/-! ### Cells of a valid guess -/

theorem mem_cell {g : Guess k T n} {s : Fin 2} {v : Fin n} {i : ℕ} {x : Fin n} :
    x ∈ cell g s v i ↔ x = v ∨ ∃ b, g s b (digit k T n i b) = x := by
  simp [cell]

/-- A column lies in its cells. -/
theorem self_mem_cell (g : Guess k T n) (s : Fin 2) (v : Fin n) (i : ℕ) : v ∈ cell g s v i :=
  mem_insert_self v _

/-- The vertex at position `digit_b(i)` of block `b` of side `s` lies in the cell. -/
theorem guess_mem_cell (g : Guess k T n) (s : Fin 2) (v : Fin n) (i : ℕ) (b : Fin (k - 1)) :
    g s b (digit k T n i b) ∈ cell g s v i :=
  mem_insert_of_mem (mem_image_of_mem _ (mem_univ b))

/-- The only column in a cell of the column `v` is `v`. -/
theorem eq_of_mem_cell {g : Guess k T n} {s : Fin 2} {v w : Fin n} {i : ℕ} (hw : IsCol g w)
    (h : w ∈ cell g s v i) : w = v := by
  rcases mem_cell.1 h with h | ⟨b, hb⟩
  · exact h
  · exact absurd hb (hw s b _)

/-- The vertices of a valid guess determine their side, block and position. -/
theorem valid_eq {g : Guess k T n} (hg : g.Valid) {s s' : Fin 2} {b b' : Fin (k - 1)}
    {t t' : Fin (ell k T n)} (h : g s b t = g s' b' t') : s = s' ∧ b = b' ∧ t = t' := by
  have := hg (a₁ := (s, b, t)) (a₂ := (s', b', t')) h
  simp only [Prod.mk.injEq] at this
  exact this

/-- A cell of a column of a valid guess has `k` vertices. -/
theorem card_cell (hk : 1 ≤ k) {g : Guess k T n} (hg : g.Valid) {v : Fin n} (hv : IsCol g v)
    (s : Fin 2) (i : ℕ) : (cell g s v i).card = k := by
  unfold cell
  rw [card_insert_of_notMem, card_image_of_injective, card_univ, Fintype.card_fin]
  · omega
  · intro b b' hbb'
    exact (valid_eq hg hbb').2.1
  · simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun b hb ↦ hv s b _ hb

/-- Equal cells, one of a column of a valid guess, have the same side: a cell contains a vertex
of the first block of its side. -/
theorem side_eq_of_cell_eq (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) {s s' : Fin 2}
    {v v' : Fin n} (hv : IsCol g v) {i i' : ℕ} (h : cell g s v i = cell g s' v' i') : s = s' := by
  set b₀ : Fin (k - 1) := ⟨0, by omega⟩
  have hmem : g s' b₀ (digit k T n i' b₀) ∈ cell g s v i := h ▸ guess_mem_cell g s' v' i' b₀
  rcases mem_cell.1 hmem with h1 | ⟨b, hb⟩
  · exact absurd h1 (hv s' b₀ _)
  · exact (valid_eq hg hb).1

/-- A cell of a column of a valid guess determines its side, its column and its bit `i < r`. -/
theorem cell_inj (hk : 2 ≤ k) {g : Guess k T n} (hg : g.Valid) {s s' : Fin 2} {v v' : Fin n}
    (hv : IsCol g v) {i i' : ℕ} (hi : i < rbits T n) (hi' : i' < rbits T n)
    (h : cell g s v i = cell g s' v' i') : s = s' ∧ v = v' ∧ i = i' := by
  have hvv : v = v' := eq_of_mem_cell hv (h ▸ self_mem_cell g s v i : v ∈ cell g s' v' i')
  refine ⟨side_eq_of_cell_eq hk hg hv h, hvv, eq_of_digit_eq hk hi hi' fun b ↦ ?_⟩
  have hmem : g s b (digit k T n i b) ∈ cell g s' v' i' := h ▸ guess_mem_cell g s v i b
  rcases mem_cell.1 hmem with h1 | ⟨b', hb'⟩
  · exact absurd (h1.trans hvv.symm) (hv s b _)
  · obtain ⟨-, rfl, h2⟩ := valid_eq hg hb'
    exact h2.symm

/-! ### The hidden layout -/

theorem divmod_inj {d a a' c c' : ℕ} (hc : c < d) (hc' : c' < d) (h : a * d + c = a' * d + c') :
    a = a' ∧ c = c' := by
  have hd : 0 < d := by omega
  have h1 := (Nat.div_mod_unique hd).2 ⟨(by ring : c + d * a = a * d + c), hc⟩
  have h2 := (Nat.div_mod_unique hd).2 ⟨(show c' + d * a' = a * d + c by rw [h]; ring), hc'⟩
  exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩

/-- The hidden layout is a valid guess. -/
theorem layout_valid (h : 2 * (k - 1) * ell k T n < n) : (layout h).Valid := by
  rintro ⟨s, b, t⟩ ⟨s', b', t'⟩ he
  have he' : ((s : ℕ) * (k - 1) + b) * ell k T n + t =
      ((s' : ℕ) * (k - 1) + b') * ell k T n + t' := congrArg Fin.val he
  obtain ⟨h1, h2⟩ := divmod_inj t.2 t'.2 he'
  obtain ⟨h3, h4⟩ := divmod_inj b.2 b'.2 h1
  simp only [Prod.mk.injEq]
  exact ⟨Fin.ext h3, Fin.ext h4, Fin.ext h2⟩

/-! ### The planted bits -/

/-- `S` is the cell of a bit of side `s` of a column of the layout. -/
abbrev IsCellOf (h : 2 * (k - 1) * ell k T n < n) (s : Fin 2) (S : KSet k n) : Prop :=
  ∃ v, ∃ i : Fin (rbits T n), IsCol (layout h) v ∧ S.1 = cell (layout h) s v i

/-- At the cell of bit `i` of side `0` of a column `v`, the planted tensor has bit `i` of
`α_v`. -/
theorem encode_alpha (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    {v : Fin n} (hv : IsCol (layout h) v) (i : Fin (rbits T n)) {S : KSet k n}
    (hS : S.1 = cell (layout h) 0 v i) : encode h ω S = (bitEquiv T n).symm (ω.2.1 v) i := by
  have hα : IsCellOf h 0 S := ⟨v, i, hv, hS⟩
  unfold encode
  rw [dite_eq_left hα]
  obtain ⟨-, hS'⟩ := hα.choose_spec.choose_spec
  obtain ⟨-, h1, h2⟩ := cell_inj hk (layout_valid h) hv i.2 hα.choose_spec.choose.2
    (hS.symm.trans hS')
  rw [show hα.choose_spec.choose = i from Fin.ext h2.symm, ← h1]

/-- At the cell of bit `i` of side `1` of a column `v`, the planted tensor has bit `i` of
`β_v`. -/
theorem encode_beta (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    {v : Fin n} (hv : IsCol (layout h) v) (i : Fin (rbits T n)) {S : KSet k n}
    (hS : S.1 = cell (layout h) 1 v i) :
    encode h ω S = (bitEquiv T n).symm (betaVal (layout h) ω v) i := by
  have hnα : ¬IsCellOf h 0 S := by
    rintro ⟨w, j, hw, hS'⟩
    exact absurd (side_eq_of_cell_eq hk (layout_valid h) hw (hS'.symm.trans hS)) (by decide)
  have hβ : IsCellOf h 1 S := ⟨v, i, hv, hS⟩
  unfold encode
  rw [dite_eq_right hnα, dite_eq_left hβ]
  obtain ⟨-, hS'⟩ := hβ.choose_spec.choose_spec
  obtain ⟨-, h1, h2⟩ := cell_inj hk (layout_valid h) hv i.2 hβ.choose_spec.choose.2
    (hS.symm.trans hS')
  rw [show hβ.choose_spec.choose = i from Fin.ext h2.symm, ← h1]

/-- Every other entry of the planted tensor is a padding bit. -/
theorem encode_pad (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n) {S : KSet k n}
    (h0 : ¬IsCellOf h 0 S) (h1 : ¬IsCellOf h 1 S) : encode h ω S = ω.2.2.2 S := by
  unfold encode
  rw [dite_eq_right h0, dite_eq_right h1]

/-- `BHJK25.RS.encode_alpha`, read at a cell. -/
theorem readAt_encode_alpha (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    {v : Fin n} (hv : IsCol (layout h) v) (i : Fin (rbits T n)) :
    readAt (encode h ω) (cell (layout h) 0 v i) = (bitEquiv T n).symm (ω.2.1 v) i := by
  rw [readAt, dite_eq_left (card_cell (by omega) (layout_valid h) hv 0 i)]
  exact encode_alpha hk h ω hv i rfl

/-- `BHJK25.RS.encode_beta`, read at a cell. -/
theorem readAt_encode_beta (hk : 2 ≤ k) (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n)
    {v : Fin n} (hv : IsCol (layout h) v) (i : Fin (rbits T n)) :
    readAt (encode h ω) (cell (layout h) 1 v i) =
      (bitEquiv T n).symm (betaVal (layout h) ω v) i := by
  rw [readAt, dite_eq_left (card_cell (by omega) (layout_valid h) hv 1 i)]
  exact encode_beta hk h ω hv i rfl

end BHJK25.RS
