module

public import BHSV25.Planted.FullAlg

/-!
# Uncoloring

The deterministic part of [BHSV25, Lemma B.20] (`BHSV25.Planted.uncolor_spec`): let `χ` be a
proper `k`-coloring of `G`, `c` a coloring, and `R` a set of vertices colored by `c` as by `χ`,
each with at least `d / (6k)` neighbors in `R` of every other color. Suppose that no nonempty set
`W` of vertices colored wrongly by `c` gives each of its vertices at least `d / (6k)` neighbors in
`W`. Then uncoloring (`BHSV25.Planted.uncolor`) keeps `R` colored, colors every vertex it keeps as
`χ` does, and only uncolors.

The proof: by induction no vertex of `R` ever violates; a round with no violating vertex changes
nothing, and every other round uncolors a vertex, so after `n + 1` rounds no vertex violates. The
wrongly colored vertices that remain then form a set `W` as above: a vertex `y` of `W` has at
least `d / (6k)` neighbors of the color `χ(y)`, and these are colored wrongly, as their own color
under `χ` differs from `χ(y)`. So `W` is empty.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {G : Graph} {k : ℕ}

/-! ### Counting on a graph -/

open Classical in
theorem nbrCount_graph (c : List ℕ) (y : Fin G.1) (a : ℕ) :
    nbrCount G.1 k (adjTable G) c y a =
      (univ.filter fun z : Fin G.1 ↦ G.2.Adj y z ∧ c.getD z k = a).card := by
  rw [nbrCount, Net.countP_range, card_filter]
  refine sum_congr rfl fun z _ ↦ ?_
  simp [Alg.adjBit_adjTable]

theorem getD_uncolorStep (d : ℕ) (c : List ℕ) (y : Fin G.1) :
    (uncolorStep G.1 k d (adjTable G) c).getD y k =
      if violates G.1 k d (adjTable G) c y then k else c.getD y k :=
  Net.getD_map_range G.1 _ k y.2

open Classical in
theorem violates_iff (d : ℕ) (c : List ℕ) (y : Fin G.1) :
    violates G.1 k d (adjTable G) c y = true ↔ c.getD y k < k ∧ ∃ a < k, a ≠ c.getD y k ∧
      6 * k * (univ.filter fun z : Fin G.1 ↦ G.2.Adj y z ∧ c.getD z k = a).card < d := by
  simp only [violates, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range,
    Bool.not_eq_true', decide_eq_false_iff_not, nbrCount_graph]

open Classical in
theorem violates_congr (d : ℕ) {c c' : List ℕ} (h : ∀ z : Fin G.1, c.getD z k = c'.getD z k)
    (y : Fin G.1) :
    violates G.1 k d (adjTable G) c y = violates G.1 k d (adjTable G) c' y := by
  have hf : ∀ a, (univ.filter fun z : Fin G.1 ↦ G.2.Adj y z ∧ c.getD z k = a) =
      univ.filter fun z : Fin G.1 ↦ G.2.Adj y z ∧ c'.getD z k = a := fun a ↦ by
    ext z; simp only [mem_filter, mem_univ, true_and, h z]
  rw [Bool.eq_iff_iff, violates_iff, violates_iff, h y]
  simp only [hf]

/-! ### The rounds -/

/-- The number of colored vertices. -/
noncomputable def numCol' (G : Graph) (k : ℕ) (c : List ℕ) : ℕ :=
  (univ.filter fun y : Fin G.1 ↦ c.getD y k < k).card

theorem uncolorStep_getD_eq_or (d : ℕ) (c : List ℕ) (y : Fin G.1) :
    (uncolorStep G.1 k d (adjTable G) c).getD y k = c.getD y k ∨
      (uncolorStep G.1 k d (adjTable G) c).getD y k = k := by
  rw [getD_uncolorStep]
  split_ifs <;> simp

theorem numCol'_uncolorStep_le (d : ℕ) (c : List ℕ) :
    numCol' G k (uncolorStep G.1 k d (adjTable G) c) ≤ numCol' G k c := by
  refine card_le_card fun y hy ↦ ?_
  rw [mem_filter] at hy ⊢
  refine ⟨hy.1, ?_⟩
  rcases uncolorStep_getD_eq_or d c y with h | h
  · rw [← h]; exact hy.2
  · rw [h] at hy; exact absurd hy.2 (lt_irrefl k)

theorem numCol'_uncolorStep_lt (d : ℕ) (c : List ℕ) {y : Fin G.1}
    (hy : violates G.1 k d (adjTable G) c y = true) :
    numCol' G k (uncolorStep G.1 k d (adjTable G) c) < numCol' G k c := by
  refine card_lt_card ⟨fun x hx ↦ ?_, fun hsub ↦ ?_⟩
  · rw [mem_filter] at hx ⊢
    refine ⟨hx.1, ?_⟩
    rcases uncolorStep_getD_eq_or d c x with h | h
    · rw [← h]; exact hx.2
    · rw [h] at hx; exact absurd hx.2 (lt_irrefl k)
  · have hy' := ((violates_iff d c y).1 hy).1
    have := hsub (mem_filter.2 ⟨mem_univ _, hy'⟩)
    rw [mem_filter, getD_uncolorStep, ite_eq_left hy] at this
    exact lt_irrefl k this.2

/-- A round without violating vertex changes no color. -/
theorem uncolorStep_getD_of_none (d : ℕ) (c : List ℕ)
    (h : ∀ y : Fin G.1, violates G.1 k d (adjTable G) c y = false) (y : Fin G.1) :
    (uncolorStep G.1 k d (adjTable G) c).getD y k = c.getD y k := by
  rw [getD_uncolorStep, ite_eq_right (by simp [h y])]

/-- **After `n + 1` rounds no vertex violates.** -/
theorem uncolor_no_violates (d : ℕ) (c : List ℕ) (y : Fin G.1) :
    violates G.1 k d (adjTable G) (uncolor G.1 k d (adjTable G) c) y = false := by
  set f := uncolorStep G.1 k d (adjTable G)
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  -- if a round has no violating vertex, neither has the next
  have hpres : ∀ j, (∀ y : Fin G.1, violates G.1 k d (adjTable G) (f^[j] c) y = false) →
      ∀ y : Fin G.1, violates G.1 k d (adjTable G) (f^[j + 1] c) y = false := by
    intro j hj y
    rw [Function.iterate_succ_apply', violates_congr d (uncolorStep_getD_of_none d _ hj)]
    exact hj y
  have hall : ∀ j ≤ G.1 + 1, ∃ y : Fin G.1, violates G.1 k d (adjTable G) (f^[j] c) y = true := by
    intro j hj
    by_contra hnone
    push Not at hnone
    simp only [Bool.not_eq_true] at hnone
    have : ∀ i, ∀ y : Fin G.1, violates G.1 k d (adjTable G) (f^[j + i] c) y = false := by
      intro i
      induction i with
      | zero => exact hnone
      | succ i ih => exact hpres (j + i) ih
    have h2 := this (G.1 + 1 - j) y
    rw [show j + (G.1 + 1 - j) = G.1 + 1 by omega] at h2
    rw [uncolor] at hcon
    rw [h2] at hcon
    exact Bool.false_ne_true hcon
  have hdec : ∀ j ≤ G.1 + 1, numCol' G k (f^[j] c) + j ≤ numCol' G k c := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨y, hy⟩ := hall j (by omega)
      have h1 : numCol' G k (f (f^[j] c)) < numCol' G k (f^[j] c) :=
        numCol'_uncolorStep_lt d (f^[j] c) hy
      rw [Function.iterate_succ_apply']
      have := ih (by omega)
      omega
  have h1 := hdec (G.1 + 1) le_rfl
  have h2 : numCol' G k c ≤ G.1 := by
    have := card_le_univ (univ.filter fun y : Fin G.1 ↦ c.getD y k < k)
    rwa [Fintype.card_fin] at this
  omega

theorem uncolor_getD_eq_or (d : ℕ) (c : List ℕ) (y : Fin G.1) :
    (uncolor G.1 k d (adjTable G) c).getD y k = c.getD y k ∨
      (uncolor G.1 k d (adjTable G) c).getD y k = k := by
  rw [uncolor]
  generalize G.1 + 1 = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rcases uncolorStep_getD_eq_or d ((uncolorStep G.1 k d (adjTable G))^[m] c) y with h | h
    · rw [h]; exact ih
    · exact Or.inr h

/-! ### Lemma B.20 -/

open Classical in
/-- **Uncoloring** [BHSV25, Lemma B.20, deterministic part]. -/
theorem uncolor_spec (χ : Fin G.1 → Fin k) (hχ : ∀ u v, G.2.Adj u v → χ u ≠ χ v) (d : ℕ)
    (c : List ℕ) (R : Finset (Fin G.1)) (hR : ∀ y ∈ R, c.getD y k = χ y)
    (hRdeg : ∀ y ∈ R, ∀ a : Fin k, a ≠ χ y →
      d ≤ 6 * k * (R.filter fun z ↦ G.2.Adj y z ∧ χ z = a).card)
    (hW : ∀ W : Finset (Fin G.1), (∀ y ∈ W, c.getD y k < k ∧ c.getD y k ≠ χ y) →
      (∀ y ∈ W, d ≤ 6 * k * (W.filter (G.2.Adj y)).card) → W = ∅) :
    (∀ y : Fin G.1, (uncolor G.1 k d (adjTable G) c).getD y k < k →
      (uncolor G.1 k d (adjTable G) c).getD y k = χ y) ∧
    (∀ y ∈ R, (uncolor G.1 k d (adjTable G) c).getD y k = χ y) ∧
    (∀ y : Fin G.1, (uncolor G.1 k d (adjTable G) c).getD y k = c.getD y k ∨
      (uncolor G.1 k d (adjTable G) c).getD y k = k) := by
  set f := uncolorStep G.1 k d (adjTable G)
  -- `R` stays colored as by `χ`
  have hRinv : ∀ j, ∀ y ∈ R, (f^[j] c).getD y k = χ y := by
    intro j
    induction j with
    | zero => exact hR
    | succ j ih =>
      intro y hy
      rw [Function.iterate_succ_apply', getD_uncolorStep, ite_eq_right, ih y hy]
      rw [Bool.not_eq_true, ← Bool.not_eq_true, violates_iff]
      rintro ⟨-, a, ha, hne, hlt⟩
      rw [ih y hy] at hne
      have h1 := hRdeg y hy ⟨a, ha⟩ (fun h ↦ hne (by rw [← h]))
      have h2 : (R.filter fun z ↦ G.2.Adj y z ∧ χ z = ⟨a, ha⟩).card ≤
          (univ.filter fun z : Fin G.1 ↦ G.2.Adj y z ∧ (f^[j] c).getD z k = a).card := by
        refine card_le_card fun z hz ↦ ?_
        rw [mem_filter] at hz ⊢
        refine ⟨mem_univ _, hz.2.1, ?_⟩
        rw [ih z hz.1, hz.2.2]
      have := Nat.mul_le_mul_left (6 * k) h2
      omega
  set c' := uncolor G.1 k d (adjTable G) c with hc'
  have hR' : ∀ y ∈ R, c'.getD y k = χ y := hRinv (G.1 + 1)
  have hor := uncolor_getD_eq_or (G := G) (k := k) d c
  -- the wrongly colored vertices that remain
  set W := univ.filter fun y : Fin G.1 ↦ c'.getD y k < k ∧ c'.getD y k ≠ χ y with hWdef
  have hWc : ∀ y ∈ W, c.getD y k < k ∧ c.getD y k ≠ χ y := by
    intro y hy
    rw [mem_filter] at hy
    rcases hor y with h | h
    · rw [← h]; exact hy.2
    · rw [h] at hy; exact absurd hy.2.1 (lt_irrefl k)
  have hWdeg : ∀ y ∈ W, d ≤ 6 * k * (W.filter (G.2.Adj y)).card := by
    intro y hy
    rw [mem_filter] at hy
    have hnv := uncolor_no_violates (k := k) d c y
    rw [← hc'] at hnv
    have hχk : (χ y : ℕ) < k := (χ y).2
    have h1 : ¬ 6 * k * (univ.filter fun z : Fin G.1 ↦
        G.2.Adj y z ∧ c'.getD z k = χ y).card < d := by
      intro hlt
      have := (violates_iff d c' y).2 ⟨hy.2.1, χ y, hχk, Ne.symm hy.2.2, hlt⟩
      rw [hnv] at this
      exact Bool.false_ne_true this
    have h2 : (univ.filter fun z : Fin G.1 ↦ G.2.Adj y z ∧ c'.getD z k = χ y) ⊆
        W.filter (G.2.Adj y) := by
      intro z hz
      rw [mem_filter] at hz
      rw [mem_filter, hWdef, mem_filter]
      refine ⟨⟨mem_univ _, by rw [hz.2.2]; exact hχk, ?_⟩, hz.2.1⟩
      rw [hz.2.2]
      intro h
      exact hχ y z hz.2.1 (Fin.ext h)
    have := Nat.mul_le_mul_left (6 * k) (card_le_card h2)
    omega
  have hW0 := hW W hWc hWdeg
  refine ⟨fun y hy ↦ ?_, hR', hor⟩
  by_contra hne
  have : y ∈ W := mem_filter.2 ⟨mem_univ _, hy, hne⟩
  rw [hW0] at this
  simp at this

end Planted

end BHSV25
