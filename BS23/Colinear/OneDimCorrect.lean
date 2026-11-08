module

public import BS23.Colinear.OneDim
public import BS23.Model

/-!
# The clustering on the line is correct

The deterministic guarantee of the line clustering `BS23.OneDim.cluster`
(`BS23.OneDim.cluster_clustersWithin`). The points `z₁, …, z_n ∈ ℝ` have labels `ℓ` in `k ≥ 2`
components with centers `p c`, pairwise at least `Γ s` apart. A tail function `τ` bounds the
fraction of the points of each component at distance at least `ρ s` from its center, and every
component holds at least a `w` fraction of the points. If

* `τ (Γ / 10) < θ` (a cell far from every center is light),
* `τ A + 3 k θ ≤ ε` (the coverage is at least `1 - ε` at a scale of at least `A s`),
* `ε + τ (3 Γ / 20) < w` (every component has a heavy cell close to its center), and
* some grid scale `H / 2^ℓ`, `ℓ ≤ ℓmax`, lies in `[A s, Γ s / 20]`,

then the output clusters the points with error at most `τ (3 Γ / 10)`: a point within `3 Γ s / 10`
of its center gets the rank of its center among the sorted centers.

The proof:

1. At the good grid scale, the points within `A s` of their center lie in at most `3 k` cells, and
   light cells hold fewer than `θ n` points each, so the coverage is at least `1 - ε`
   (`BS23.OneDim.coverage_ge`). Hence the chosen scale `δ` is at most `Γ s / 20` and has coverage
   at least `1 - ε` (`BS23.OneDim.level_spec`).
2. A heavy cell meets the interval of radius `Γ s / 10` around some center
   (`BS23.OneDim.exists_near_of_mem_heavy`), and only one (`BS23.OneDim.near_unique`): its *group*.
   Every component has a heavy cell in its group (`BS23.OneDim.exists_heavy_near`).
3. Consecutive heavy cells of one group are closer than consecutive heavy cells of different groups,
   so the boundaries are exactly the last cells of the groups but the rightmost one
   (`BS23.OneDim.Grouped.boundaries_eq`, a purely combinatorial statement), and a point close to its
   center lies on the correct side of every boundary midpoint (`BS23.OneDim.mid_iff`).
-/

@[expose] public section

namespace BS23.OneDim

open Finset

/-! ### The next heavy cell, gaps, boundaries -/

section Next

variable (S : Finset ℤ)

theorem next_eq_some_iff {p q : ℤ} :
    next S p = some q ↔ q ∈ S ∧ p < q ∧ ∀ r ∈ S, p < r → q ≤ r := by
  unfold next
  split_ifs with h
  · rw [Option.some.injEq]
    have hm := Finset.min'_mem _ h
    rw [Finset.mem_filter] at hm
    constructor
    · rintro rfl
      exact ⟨hm.1, hm.2, fun r hr hpr ↦ Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hr, hpr⟩)⟩
    · rintro ⟨hq, hpq, hmin⟩
      exact le_antisymm (Finset.min'_le _ _ (Finset.mem_filter.2 ⟨hq, hpq⟩)) (hmin _ hm.1 hm.2)
  · simp only [false_iff, not_and]
    exact fun hq hpq _ ↦ h ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩

theorem isSome_next_iff {p : ℤ} : (next S p).isSome ↔ ∃ q ∈ S, p < q := by
  unfold next
  split_ifs with h
  · simp only [Option.isSome_some, true_iff]
    obtain ⟨q, hq⟩ := h
    exact ⟨q, Finset.mem_filter.1 hq⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_exists, not_and]
    exact fun q hq hpq ↦ h ⟨q, Finset.mem_filter.2 ⟨hq, hpq⟩⟩

theorem gap_eq_of_next {p q : ℤ} (h : next S p = some q) : gap S p = q - p := by
  simp [gap, h]

/-- Moving down in the order of `before` shrinks `before`. -/
theorem before_ssubset {p p' : ℤ} (hp : p ∈ S) (hps : (next S p).isSome)
    (hlt : gap S p' < gap S p ∨ (gap S p = gap S p' ∧ p < p')) : before S p ⊂ before S p' := by
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨p, Finset.mem_filter.2 ⟨hp, hps, hlt⟩, fun h ↦ ?_⟩
    have := (Finset.mem_filter.1 h).2.2
    omega
  · intro q hq
    simp only [before, Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1, by omega⟩

/-- There are at most `k - 1` boundaries. -/
theorem card_boundaries_le (k : ℕ) : (boundaries k S).card ≤ k - 1 := by
  have hmaps : Set.MapsTo (fun p ↦ (before S p).card) (boundaries k S) (Finset.range (k - 1)) :=
    fun p hp ↦ Finset.mem_range.2 (Finset.mem_filter.1 hp).2.2
  have hinj : Set.InjOn (fun p ↦ (before S p).card) (boundaries k S) := by
    intro p hp p' hp' heq
    simp only at heq
    rw [Finset.mem_coe, boundaries, Finset.mem_filter] at hp hp'
    by_contra hne
    have key : gap S p' < gap S p ∨ (gap S p = gap S p' ∧ p < p') ∨
        gap S p < gap S p' ∨ (gap S p' = gap S p ∧ p' < p) := by omega
    rcases key with h1 | h1 | h1 | h1
    · exact (Finset.card_lt_card (before_ssubset S hp.1 hp.2.1 (Or.inl h1))).ne heq
    · exact (Finset.card_lt_card (before_ssubset S hp.1 hp.2.1 (Or.inr h1))).ne heq
    · exact (Finset.card_lt_card (before_ssubset S hp'.1 hp'.2.1 (Or.inl h1))).ne heq.symm
    · exact (Finset.card_lt_card (before_ssubset S hp'.1 hp'.2.1 (Or.inr h1))).ne heq.symm
  calc (boundaries k S).card ≤ (Finset.range (k - 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = k - 1 := Finset.card_range _

theorem labelOfCell_le (k : ℕ) (P : ℤ) : labelOfCell k S P ≤ k - 1 :=
  (Finset.card_filter_le _ _).trans (card_boundaries_le S k)

/-- **Labels are below `k`**, whatever the cells. -/
theorem labelOfCell_lt {k : ℕ} (hk : 0 < k) (P : ℤ) : labelOfCell k S P < k :=
  (labelOfCell_le S k P).trans_lt (by omega)

end Next

/-! ### Boundaries between groups (combinatorics) -/

section Grouped

variable {k : ℕ} (S : Finset ℤ) (g : ℤ → Fin k) (p : Fin k → ℝ)

/-- The rank of `c` among the centers `p`: the number of smaller centers. -/
noncomputable def rank (c : Fin k) : ℕ := (Finset.univ.filter fun a ↦ p a < p c).card

/-- The crossings: the cells followed by a cell of another group. -/
def crossings : Finset ℤ := S.filter fun b ↦ ∃ b', next S b = some b' ∧ g b ≠ g b'

/-- The cells `S` fall into groups `g` with distinct positions `p`: every group has a cell, the
groups are ordered along the line as their positions, and consecutive cells of one group are
closer than consecutive cells of different groups. -/
structure Grouped : Prop where
  inj : Function.Injective p
  surj : ∀ c, ∃ Q ∈ S, g Q = c
  ord : ∀ Q ∈ S, ∀ Q' ∈ S, p (g Q) < p (g Q') → Q < Q'
  gap_lt : ∀ q ∈ S, ∀ q' ∈ S, ∀ b ∈ S, ∀ b' ∈ S, b < b' → g q = g q' → g b ≠ g b' →
    q' - q < b' - b

variable {S g p}

theorem rank_lt (c : Fin k) : rank p c < k := by
  have : (Finset.univ.filter fun a ↦ p a < p c) ⊂ Finset.univ :=
    Finset.filter_ssubset.2 ⟨c, Finset.mem_univ _, lt_irrefl _⟩
  simpa [rank] using Finset.card_lt_card this

theorem rank_injective (hinj : Function.Injective p) : Function.Injective (rank p) := by
  intro c c' heq
  by_contra hne
  have key : ∀ {a b : Fin k}, p a < p b → rank p a < rank p b := by
    intro a b hab
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, hab⟩,
        fun h ↦ lt_irrefl _ (Finset.mem_filter.1 h).2⟩
    · intro x hx
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.trans hab⟩
  rcases lt_trichotomy (p c) (p c') with h | h | h
  · exact (key h).ne heq
  · exact hne (hinj h)
  · exact (key h).ne heq.symm

theorem card_filter_exists_lt (hinj : Function.Injective p) (hk : 0 < k) :
    (Finset.univ.filter fun a ↦ ∃ c, p a < p c).card = k - 1 := by
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ p ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have : (Finset.univ.filter fun a ↦ ∃ c, p a < p c) = Finset.univ.erase m := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨c, hc⟩ rfl
      exact absurd (hm c (Finset.mem_univ _)) (not_le.2 hc)
    · intro ha
      exact ⟨m, lt_of_le_of_ne (hm a (Finset.mem_univ _)) (fun h ↦ ha (hinj h))⟩
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]

namespace Grouped

theorem lt_of_next (hG : Grouped S g p) {b b' : ℤ} (hb : b ∈ S) (h : next S b = some b')
    (hne : g b ≠ g b') : p (g b) < p (g b') := by
  obtain ⟨hb', hbb', -⟩ := (next_eq_some_iff S).1 h
  rcases lt_trichotomy (p (g b)) (p (g b')) with hlt | heq | hgt
  · exact hlt
  · exact absurd (hG.inj heq) hne
  · exact absurd (hG.ord _ hb' _ hb hgt) (not_lt.2 hbb'.le)

/-- No group lies strictly between the groups of a cell and of the next one. -/
theorem le_of_next (hG : Grouped S g p) {b b' : ℤ} (hb : b ∈ S) (h : next S b = some b')
    {c : Fin k} (hc : p (g b) < p c) : p (g b') ≤ p c := by
  obtain ⟨hb', -, hmin⟩ := (next_eq_some_iff S).1 h
  by_contra hlt
  push Not at hlt
  obtain ⟨Q, hQ, rfl⟩ := hG.surj c
  have h1 := hG.ord _ hb _ hQ hc
  have h2 := hG.ord _ hQ _ hb' hlt
  have h3 := hmin Q hQ h1
  omega

/-- A crossing is the last cell of its group. -/
theorem le_of_mem_crossings (hG : Grouped S g p) {b : ℤ} (hb : b ∈ crossings S g) {Q : ℤ}
    (hQ : Q ∈ S) (hgQ : g Q = g b) : Q ≤ b := by
  obtain ⟨hbS, b', hnext, hne⟩ := Finset.mem_filter.1 hb
  obtain ⟨hb', hbb', hmin⟩ := (next_eq_some_iff S).1 hnext
  by_contra hlt
  push Not at hlt
  have h1 := hmin Q hQ hlt
  rcases lt_trichotomy (p (g b')) (p (g b)) with h3 | h3 | h3
  · have := hG.ord _ hb' _ hbS h3
    omega
  · exact hne (hG.inj h3).symm
  · rw [← hgQ] at h3
    have := hG.ord _ hQ _ hb' h3
    omega

theorem injOn (hG : Grouped S g p) : Set.InjOn g (crossings S g) := by
  intro b hb b' hb' heq
  rw [Finset.mem_coe] at hb hb'
  exact le_antisymm (hG.le_of_mem_crossings hb' (Finset.mem_filter.1 hb).1 heq)
    (hG.le_of_mem_crossings hb (Finset.mem_filter.1 hb').1 heq.symm)

/-- Every group with a group to its right ends with a crossing. -/
theorem mem_image_crossings (hG : Grouped S g p) {a c : Fin k} (hac : p a < p c) :
    ∃ b ∈ crossings S g, g b = a := by
  have hne : (S.filter fun Q ↦ g Q = a).Nonempty := by
    obtain ⟨Q, hQ, hgQ⟩ := hG.surj a
    exact ⟨Q, Finset.mem_filter.2 ⟨hQ, hgQ⟩⟩
  have hbmem := Finset.max'_mem _ hne
  set b := (S.filter fun Q ↦ g Q = a).max' hne
  rw [Finset.mem_filter] at hbmem
  obtain ⟨Qc, hQc, hgQc⟩ := hG.surj c
  have hbQ : b < Qc := hG.ord _ hbmem.1 _ hQc (by rw [hbmem.2, hgQc]; exact hac)
  obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 ((isSome_next_iff S).2 ⟨Qc, hQc, hbQ⟩)
  obtain ⟨hb'S, hbb', -⟩ := (next_eq_some_iff S).1 hb'
  refine ⟨b, Finset.mem_filter.2 ⟨hbmem.1, b', hb', fun h ↦ ?_⟩, hbmem.2⟩
  have : b' ≤ b := Finset.le_max' _ _ (Finset.mem_filter.2 ⟨hb'S, h.symm.trans hbmem.2⟩)
  omega

theorem image_crossings (hG : Grouped S g p) :
    (crossings S g).image g = Finset.univ.filter fun a ↦ ∃ c, p a < p c := by
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hbS, b', hnext, hne⟩ := Finset.mem_filter.1 hb
    exact ⟨g b', hG.lt_of_next hbS hnext hne⟩
  · rintro ⟨c, hc⟩
    exact hG.mem_image_crossings hc

theorem card_crossings (hG : Grouped S g p) (hk : 0 < k) : (crossings S g).card = k - 1 := by
  rw [← Finset.card_image_of_injOn hG.injOn, hG.image_crossings, card_filter_exists_lt hG.inj hk]

/-- **The boundaries are the crossings**: the `k - 1` largest gaps are those between groups. -/
theorem boundaries_eq (hG : Grouped S g p) (hk : 2 ≤ k) : boundaries k S = crossings S g := by
  ext b
  constructor
  · intro hb
    obtain ⟨hbS, hsome, hcard⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hsome
    refine Finset.mem_filter.2 ⟨hbS, b', hb', fun heq ↦ ?_⟩
    obtain ⟨hb'S, -, -⟩ := (next_eq_some_iff S).1 hb'
    have hsub : crossings S g ⊆ before S b := by
      intro q hq
      obtain ⟨hqS, q', hq', hne⟩ := Finset.mem_filter.1 hq
      obtain ⟨hq'S, hqq', -⟩ := (next_eq_some_iff S).1 hq'
      refine Finset.mem_filter.2 ⟨hqS, Option.isSome_iff_exists.2 ⟨q', hq'⟩, Or.inl ?_⟩
      rw [gap_eq_of_next S hb', gap_eq_of_next S hq']
      exact hG.gap_lt b hbS b' hb'S q hqS q' hq'S hqq' heq hne
    have := Finset.card_le_card hsub
    rw [hG.card_crossings (by omega)] at this
    omega
  · intro hb
    obtain ⟨hbS, b', hb', hne⟩ := Finset.mem_filter.1 hb
    refine Finset.mem_filter.2 ⟨hbS, Option.isSome_iff_exists.2 ⟨b', hb'⟩, ?_⟩
    obtain ⟨hb'S, hbb', -⟩ := (next_eq_some_iff S).1 hb'
    have hsub : before S b ⊆ (crossings S g).erase b := by
      intro q hq
      obtain ⟨hqS, hqsome, hlt⟩ := Finset.mem_filter.1 hq
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 hqsome
      obtain ⟨hq'S, -, -⟩ := (next_eq_some_iff S).1 hq'
      refine Finset.mem_erase.2 ⟨fun h ↦ ?_, Finset.mem_filter.2 ⟨hqS, q', hq', fun heq ↦ ?_⟩⟩
      · subst h
        omega
      · have := hG.gap_lt q hqS q' hq'S b hbS b' hb'S hbb' heq hne
        rw [gap_eq_of_next S hb', gap_eq_of_next S hq'] at hlt
        omega
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hb, hG.card_crossings (by omega)] at this
    omega

/-- **The label of a cell** that lies on the correct side of every crossing midpoint, for the
group `c`, is the rank of `c`. -/
theorem labelOfCell_eq (hG : Grouped S g p) (hk : 2 ≤ k) {P : ℤ} {c : Fin k}
    (hmid : ∀ b ∈ crossings S g, b + (b + gap S b) < 2 * P ↔ p (g b) < p c) :
    labelOfCell k S P = rank p c := by
  unfold labelOfCell rank
  rw [hG.boundaries_eq hk, Finset.filter_congr hmid,
    ← Finset.card_image_of_injOn (hG.injOn.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))]
  congr 1
  ext a
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, ⟨-, hb⟩, rfl⟩
    exact hb
  · intro ha
    obtain ⟨b, hb, rfl⟩ := hG.mem_image_crossings ha
    exact ⟨b, ⟨hb, ha⟩, rfl⟩

end Grouped

end Grouped

/-! ### Geometry of cells -/

section Geometry

variable {n k : ℕ}

/-- The cell `Q` at scale `δ` meets the open interval of radius `Γ s / 10` around `p c`. -/
def Near (δ Γ s : ℝ) (p : Fin k → ℝ) (Q : ℤ) (c : Fin k) : Prop :=
  (Q : ℝ) * δ < p c + Γ * s / 10 ∧ p c - Γ * s / 10 < (Q : ℝ) * δ + δ

theorem cell_mul_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : (cell δ x : ℝ) * δ ≤ x :=
  (le_div_iff₀ hδ).1 (Int.floor_le _)

theorem lt_cell_mul_add {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : x < (cell δ x : ℝ) * δ + δ := by
  have := (div_lt_iff₀ hδ).1 (Int.lt_floor_add_one (x / δ))
  unfold cell
  linarith

theorem int_lt_of_mul_lt {δ : ℝ} (hδ : 0 < δ) {a b : ℤ} (hab : (a : ℝ) * δ < (b : ℝ) * δ) :
    a < b := by
  exact_mod_cast lt_of_mul_lt_mul_right hab hδ.le

theorem sep_of_lt {p : Fin k → ℝ} {d : ℝ} (hsep : ∀ a b, a ≠ b → d ≤ |p a - p b|) {a b : Fin k}
    (hab : p a < p b) : d ≤ p b - p a := by
  have := hsep b a (fun h ↦ by rw [h] at hab; exact lt_irrefl _ hab)
  rwa [abs_of_pos (by linarith)] at this

/-- A cell meets the intervals around at most one center. -/
theorem near_unique {p : Fin k → ℝ} {s Γ δ : ℝ} (hδΓ : δ ≤ Γ * s / 20)
    (hsep : ∀ a b, a ≠ b → Γ * s ≤ |p a - p b|) {Q : ℤ} {c c' : Fin k}
    (hc : Near δ Γ s p Q c) (hc' : Near δ Γ s p Q c') : c = c' := by
  by_contra hne
  have := hsep c c' hne
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨h3, h4⟩ := hc'
  rcases abs_cases (p c - p c') with ⟨h5, -⟩ | ⟨h5, -⟩ <;> rw [h5] at this <;> linarith

/-- Cells near centers are ordered as the centers. -/
theorem lt_of_near {p : Fin k → ℝ} {s Γ δ : ℝ} (hδ : 0 < δ) (hδΓ : δ ≤ Γ * s / 20) {Q Q' : ℤ}
    {c c' : Fin k} (hQ : Near δ Γ s p Q c) (hQ' : Near δ Γ s p Q' c')
    (hcc' : Γ * s ≤ p c' - p c) : Q < Q' := by
  apply int_lt_of_mul_lt hδ
  obtain ⟨h1, -⟩ := hQ
  obtain ⟨-, h2⟩ := hQ'
  linarith

/-- Two cells near one center are closer than two cells near different centers. -/
theorem gap_lt_of_near {p : Fin k → ℝ} {s Γ δ : ℝ} (hδ : 0 < δ) (hδΓ : δ ≤ Γ * s / 20)
    {q q' b b' : ℤ} {a a' c : Fin k} (hq : Near δ Γ s p q c) (hq' : Near δ Γ s p q' c)
    (hb : Near δ Γ s p b a) (hb' : Near δ Γ s p b' a') (haa' : Γ * s ≤ p a' - p a) :
    q' - q < b' - b := by
  apply int_lt_of_mul_lt hδ
  push_cast
  obtain ⟨h1, h2⟩ := hq
  obtain ⟨h3, h4⟩ := hq'
  obtain ⟨h5, h6⟩ := hb
  obtain ⟨h7, h8⟩ := hb'
  linarith

/-- **The midpoint test.** For consecutive cells `b`, `b'` near consecutive centers `p a < p a'`,
a point `x` within `3 Γ s / 10` of a center `p c` lies to the right of the midpoint of `b` and `b'`
(in cells) exactly when `p c` is to the right of `p a`. -/
theorem mid_iff {p : Fin k → ℝ} {s Γ δ : ℝ} (hδ : 0 < δ) (hδΓ : δ ≤ Γ * s / 20) {a a' c : Fin k}
    {b b' : ℤ} {x : ℝ} (hb : Near δ Γ s p b a) (hb' : Near δ Γ s p b' a')
    (haa' : Γ * s ≤ p a' - p a) (hbetween : p a < p c → p a' ≤ p c)
    (hx : |x - p c| < 3 * Γ / 10 * s) : b + b' < 2 * cell δ x ↔ p a < p c := by
  have h1 := cell_mul_le hδ x
  have h2 := lt_cell_mul_add hδ x
  rw [abs_lt] at hx
  obtain ⟨hb1, hb2⟩ := hb
  obtain ⟨hb1', hb2'⟩ := hb'
  constructor
  · intro hlt
    by_contra hle
    push Not at hle
    have h3 : ((b : ℝ) + b') * δ < (2 * (cell δ x : ℝ)) * δ :=
      mul_lt_mul_of_pos_right (by exact_mod_cast hlt) hδ
    linarith
  · intro hlt
    have h3 := hbetween hlt
    apply int_lt_of_mul_lt hδ
    push_cast
    linarith

/-! ### Counting points -/

theorem sum_card_cluster (ℓ : Fin n → Fin k) : ∑ c, ((BS23.cluster ℓ c).card : ℝ) = n := by
  have := Finset.card_eq_sum_card_fiberwise (f := ℓ) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this.symm

theorem card_filter_eq_sum_cluster (ℓ : Fin n → Fin k) (R : Fin k → Fin n → Prop)
    [∀ c, DecidablePred (R c)] :
    (Finset.univ.filter fun j ↦ R (ℓ j) j).card =
      ∑ c, ((BS23.cluster ℓ c).filter (R c)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := ℓ) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  congr 1
  ext j
  simp only [BS23.cluster, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hR, rfl⟩
    exact ⟨rfl, hR⟩
  · rintro ⟨rfl, hR⟩
    exact ⟨hR, rfl⟩

/-- Summing the tail bounds over the components. -/
theorem card_far_le (ℓ : Fin n → Fin k) (z : Fin n → ℝ) (p : Fin k → ℝ) {r t : ℝ}
    (htail : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ r ≤ |z j - p c|).card : ℝ) ≤
      t * (BS23.cluster ℓ c).card) :
    ((Finset.univ.filter fun j ↦ r ≤ |z j - p (ℓ j)|).card : ℝ) ≤ t * n := by
  calc ((Finset.univ.filter fun j ↦ r ≤ |z j - p (ℓ j)|).card : ℝ)
      = ∑ c, (((BS23.cluster ℓ c).filter fun j ↦ r ≤ |z j - p c|).card : ℝ) := by
        exact_mod_cast card_filter_eq_sum_cluster ℓ (fun c j ↦ r ≤ |z j - p c|)
    _ ≤ ∑ c, t * ((BS23.cluster ℓ c).card : ℝ) := Finset.sum_le_sum fun c _ ↦ htail c
    _ = t * n := by rw [← Finset.mul_sum, sum_card_cluster]

theorem card_not_heavy_le {z : Fin n → ℝ} {θ ε δ : ℝ} (hn : 0 < n)
    (hcov : 1 - ε ≤ coverage θ δ z) :
    ((Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z).card : ℝ) ≤ ε * n := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j ↦ cell δ (z j) ∈ heavy θ δ z)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hsplit' : ((Finset.univ.filter fun j ↦ cell δ (z j) ∈ heavy θ δ z).card : ℝ) +
      (Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z).card = n := by
    exact_mod_cast hsplit
  unfold coverage at hcov
  rw [le_div_iff₀ (by exact_mod_cast hn)] at hcov
  linarith

/-! ### Coverage and the chosen scale -/

/-- **Coverage at a coarse enough scale**: at a scale `δ ≥ A s`, all points but those at distance
at least `A s` from their center and those in the at most `3 k` light cells near the centers are
in heavy cells. -/
theorem coverage_ge {z : Fin n → ℝ} {ℓ : Fin n → Fin k} {p : Fin k → ℝ} {s A τ θ ε δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ) (hθ : 0 < θ) (hAδ : A * s ≤ δ)
    (htail : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ A * s ≤ |z j - p c|).card : ℝ) ≤
      τ * (BS23.cluster ℓ c).card)
    (hε : τ + 3 * k * θ ≤ ε) : 1 - ε ≤ coverage θ δ z := by
  set m : Fin k → ℤ := fun c ↦ cell δ (p c - A * s)
  set N : Finset ℤ := Finset.univ.biUnion fun c ↦ Finset.Icc (m c) (m c + 2)
  set L : Finset ℤ := N.filter fun Q ↦ Q ∉ heavy θ δ z
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- a point close to its center lies in one of the three cells near the center
  have hnear : ∀ j, |z j - p (ℓ j)| < A * s → cell δ (z j) ∈ N := by
    intro j hj
    rw [abs_lt] at hj
    have h1 := cell_mul_le hδ (z j)
    have h2 := lt_cell_mul_add hδ (z j)
    have h3 := cell_mul_le hδ (p (ℓ j) - A * s)
    have h4 := lt_cell_mul_add hδ (p (ℓ j) - A * s)
    refine Finset.mem_biUnion.2 ⟨ℓ j, Finset.mem_univ _, Finset.mem_Icc.2 ⟨?_, ?_⟩⟩
    · have : m (ℓ j) < cell δ (z j) + 1 := by
        apply int_lt_of_mul_lt hδ
        push_cast
        simp only [m]
        linarith
      omega
    · have : cell δ (z j) < m (ℓ j) + 3 := by
        apply int_lt_of_mul_lt hδ
        push_cast
        simp only [m]
        linarith
      omega
  have hsub : (Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z) ⊆
      (Finset.univ.filter fun j ↦ A * s ≤ |z j - p (ℓ j)|) ∪
        (Finset.univ.filter fun j ↦ cell δ (z j) ∈ L) := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hfar : A * s ≤ |z j - p (ℓ j)|
    · exact Or.inl ⟨Finset.mem_univ _, hfar⟩
    · exact Or.inr ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨hnear j (not_le.1 hfar), hj.2⟩⟩
  have hL : ((Finset.univ.filter fun j ↦ cell δ (z j) ∈ L).card : ℝ) ≤ 3 * k * θ * n := by
    have h1 : (Finset.univ.filter fun j ↦ cell δ (z j) ∈ L).card =
        ∑ Q ∈ L, cellCount δ z Q := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun j ↦ cell δ (z j)) (t := L)
        (s := Finset.univ.filter fun j ↦ cell δ (z j) ∈ L)
        (fun j hj ↦ (Finset.mem_filter.1 (Finset.mem_coe.1 hj)).2)]
      refine Finset.sum_congr rfl fun Q hQ ↦ ?_
      unfold cellCount
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · intro hj
        exact ⟨hj ▸ hQ, hj⟩
    have h2 : ∀ Q ∈ L, (cellCount δ z Q : ℝ) ≤ θ * n := by
      intro Q hQ
      have hQ' := (Finset.mem_filter.1 hQ).2
      by_contra hlt
      push Not at hlt
      apply hQ'
      refine Finset.mem_filter.2 ⟨?_, hlt.le⟩
      have hpos : 0 < cellCount δ z Q := by
        have : (0 : ℝ) < cellCount δ z Q := lt_of_le_of_lt (by positivity) hlt
        exact_mod_cast this
      obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, (Finset.mem_filter.1 hj).2⟩
    have h3 : (N.card : ℝ) ≤ 3 * k := by
      have h4 : N.card ≤ ∑ c : Fin k, (Finset.Icc (m c) (m c + 2)).card := Finset.card_biUnion_le
      have h5 : ∀ c : Fin k, (Finset.Icc (m c) (m c + 2)).card = 3 := by
        intro c
        rw [Int.card_Icc, show m c + 2 + 1 - m c = 3 by ring]
        rfl
      simp only [h5, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
      have : (N.card : ℝ) ≤ (k * 3 : ℕ) := by exact_mod_cast h4
      push_cast at this
      linarith
    have hθn : 0 ≤ θ * n := by positivity
    calc ((Finset.univ.filter fun j ↦ cell δ (z j) ∈ L).card : ℝ)
        = ∑ Q ∈ L, (cellCount δ z Q : ℝ) := by rw [h1]; push_cast; rfl
      _ ≤ ∑ Q ∈ L, θ * n := Finset.sum_le_sum h2
      _ = L.card * (θ * n) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N.card * (θ * n) :=
          mul_le_mul_of_nonneg_right
            (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) hθn
      _ ≤ 3 * k * (θ * n) := mul_le_mul_of_nonneg_right h3 hθn
      _ = 3 * k * θ * n := by ring
  have hfar := card_far_le ℓ z p htail
  have hcard : ((Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z).card : ℝ) ≤
      (Finset.univ.filter fun j ↦ A * s ≤ |z j - p (ℓ j)|).card +
        (Finset.univ.filter fun j ↦ cell δ (z j) ∈ L).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun j ↦ cell δ (z j) ∈ heavy θ δ z)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have hsplit' : ((Finset.univ.filter fun j ↦ cell δ (z j) ∈ heavy θ δ z).card : ℝ) +
      (Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z).card = n := by
    exact_mod_cast hsplit
  have hεn : (τ + 3 * k * θ) * n ≤ ε * n := mul_le_mul_of_nonneg_right hε hnpos.le
  unfold coverage
  rw [le_div_iff₀ hnpos]
  linarith

theorem scale_pos {H : ℝ} (hH : 0 < H) (L : ℕ) : 0 < scale H L := by
  unfold scale
  positivity

theorem scale_anti {H : ℝ} (hH : 0 ≤ H) {L L' : ℕ} (hLL' : L ≤ L') : scale H L' ≤ scale H L :=
  div_le_div_of_nonneg_left hH (by positivity) (pow_le_pow_right₀ (by norm_num) hLL')

/-- The chosen level is at least every level with enough coverage, and has enough coverage. -/
theorem level_spec {z : Fin n → ℝ} {θ ε H : ℝ} {ℓmax L : ℕ} (hL : L ≤ ℓmax)
    (hcovL : 1 - ε ≤ coverage θ (scale H L) z) :
    L ≤ level θ ε H ℓmax z ∧ 1 - ε ≤ coverage θ (scale H (level θ ε H ℓmax z)) z := by
  have hmem : L ∈ (Finset.range (ℓmax + 1)).filter fun ℓ ↦ 1 - ε ≤ coverage θ (scale H ℓ) z :=
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hcovL⟩
  obtain ⟨L', hL', heq⟩ := Finset.exists_mem_eq_sup _ ⟨L, hmem⟩ id
  refine ⟨Finset.le_sup (f := id) hmem, ?_⟩
  unfold level
  rw [heq]
  exact (Finset.mem_filter.1 hL').2

/-! ### Heavy cells and groups -/

/-- **A heavy cell is near a center**: otherwise all its points are at distance at least
`Γ s / 10` from their centers, and there are fewer than `θ n` of those. -/
theorem exists_near_of_mem_heavy {z : Fin n → ℝ} {ℓ : Fin n → Fin k} {p : Fin k → ℝ}
    {s Γ τ θ δ : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (htail : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ Γ / 10 * s ≤ |z j - p c|).card : ℝ) ≤
      τ * (BS23.cluster ℓ c).card)
    (hτθ : τ < θ) {Q : ℤ} (hQ : Q ∈ heavy θ δ z) : ∃ c, Near δ Γ s p Q c := by
  by_contra hne
  push Not at hne
  have hsub : (Finset.univ.filter fun j ↦ cell δ (z j) = Q) ⊆
      Finset.univ.filter fun j ↦ Γ / 10 * s ≤ |z j - p (ℓ j)| := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hlt
    push Not at hlt
    rw [abs_lt] at hlt
    apply hne (ℓ j)
    have h1 := cell_mul_le hδ (z j)
    have h2 := lt_cell_mul_add hδ (z j)
    rw [hj.2] at h1 h2
    constructor <;> linarith
  have h1 : (cellCount δ z Q : ℝ) ≤ τ * n :=
    le_trans (by exact_mod_cast Finset.card_le_card hsub) (card_far_le ℓ z p htail)
  have h2 := (Finset.mem_filter.1 hQ).2
  have : τ * n < θ * n := mul_lt_mul_of_pos_right hτθ (by exact_mod_cast hn)
  linarith

/-- **Every component has a heavy cell near its center**: at most `ε n` points are outside heavy
cells and at most `τ (3 Γ / 20) |S_c|` points of `c` are at distance at least `3 Γ s / 20` from
`p c`, fewer than `|S_c|` together. -/
theorem exists_heavy_near {z : Fin n → ℝ} {ℓ : Fin n → Fin k} {p : Fin k → ℝ}
    {s Γ τ w θ ε δ : ℝ} (hn : 0 < n) (hδ : 0 < δ) (hδΓ : δ ≤ Γ * s / 20)
    (hsep : ∀ a b, a ≠ b → Γ * s ≤ |p a - p b|)
    (hcov : 1 - ε ≤ coverage θ δ z) (hw : 0 < w)
    (hsize : ∀ c, w * n ≤ (BS23.cluster ℓ c).card)
    (htail : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ 3 * Γ / 20 * s ≤ |z j - p c|).card : ℝ) ≤
      τ * (BS23.cluster ℓ c).card)
    (hεw : ε + τ < w) (hnear : ∀ Q ∈ heavy θ δ z, ∃ c, Near δ Γ s p Q c) (c : Fin k) :
    ∃ Q ∈ heavy θ δ z, Near δ Γ s p Q c := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hout := card_not_heavy_le hn hcov
  have hSpos : (0 : ℝ) < (BS23.cluster ℓ c).card := lt_of_lt_of_le (by positivity) (hsize c)
  have hτ : 0 ≤ τ := by
    have h1 := htail c
    have h0 : (0 : ℝ) ≤ (((BS23.cluster ℓ c).filter fun j ↦ 3 * Γ / 20 * s ≤ |z j - p c|).card :
        ℝ) := Nat.cast_nonneg _
    by_contra hneg
    push Not at hneg
    have : τ * (BS23.cluster ℓ c).card < 0 := mul_neg_of_neg_of_pos hneg hSpos
    linarith
  have hSn : ((BS23.cluster ℓ c).card : ℝ) ≤ n := by
    have := Finset.card_le_univ (BS23.cluster ℓ c)
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  set G := (BS23.cluster ℓ c).filter fun j ↦
    cell δ (z j) ∈ heavy θ δ z ∧ |z j - p c| < 3 * Γ / 20 * s
  have hsub : BS23.cluster ℓ c ⊆ G ∪ ((Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z) ∪
      ((BS23.cluster ℓ c).filter fun j ↦ 3 * Γ / 20 * s ≤ |z j - p c|)) := by
    intro j hj
    simp only [G, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : cell δ (z j) ∈ heavy θ δ z
    · by_cases h2 : |z j - p c| < 3 * Γ / 20 * s
      · exact Or.inl ⟨hj, h1, h2⟩
      · exact Or.inr (Or.inr ⟨hj, not_lt.1 h2⟩)
    · exact Or.inr (Or.inl h1)
  have hGne : G.Nonempty := by
    rw [← Finset.card_pos]
    by_contra h0
    push Not at h0
    have h1 := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
    have h2 : ((BS23.cluster ℓ c).card : ℝ) ≤ G.card +
        (((Finset.univ.filter fun j ↦ cell δ (z j) ∉ heavy θ δ z).card : ℝ) +
          ((BS23.cluster ℓ c).filter fun j ↦ 3 * Γ / 20 * s ≤ |z j - p c|).card) := by
      exact_mod_cast h1
    have h3 : (G.card : ℝ) = 0 := by exact_mod_cast Nat.le_zero.1 h0
    have h4 := htail c
    have h5 : τ * (BS23.cluster ℓ c).card ≤ τ * n := mul_le_mul_of_nonneg_left hSn hτ
    have h6 := hsize c
    have h7 : (ε + τ) * n < w * n := mul_lt_mul_of_pos_right hεw hnpos
    linarith
  obtain ⟨j, hj⟩ := hGne
  obtain ⟨-, hjheavy, hjclose⟩ := Finset.mem_filter.1 hj
  refine ⟨cell δ (z j), hjheavy, ?_⟩
  obtain ⟨c', hc'⟩ := hnear _ hjheavy
  by_cases hcc : c' = c
  · exact hcc ▸ hc'
  · exfalso
    have := hsep c' c hcc
    have h1 := cell_mul_le hδ (z j)
    have h2 := lt_cell_mul_add hδ (z j)
    obtain ⟨h3, h4⟩ := hc'
    rw [abs_lt] at hjclose
    rcases abs_cases (p c' - p c) with ⟨h5, -⟩ | ⟨h5, -⟩ <;> rw [h5] at this <;> linarith

end Geometry

/-! ### The guarantee -/

theorem outCluster_ofFn {n : ℕ} (f : Fin n → ℕ) (j : Fin n) :
    outCluster (List.ofFn f) j = f j := by
  simp [outCluster]

/-- **The clustering on the line is correct** (with the tail bounds at the four radii used). -/
theorem cluster_clustersWithin_of_tails {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (z : Fin n → ℝ)
    (ℓ : Fin n → Fin k) (p : Fin k → ℝ) {s Γ w θ ε A H : ℝ} (τ : ℝ → ℝ) {ℓmax : ℕ}
    (hsep : ∀ a b, a ≠ b → Γ * s ≤ |p a - p b|)
    (hw : 0 < w) (hsize : ∀ c, w * n ≤ (BS23.cluster ℓ c).card)
    (htailA : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ A * s ≤ |z j - p c|).card : ℝ) ≤
      τ A * (BS23.cluster ℓ c).card)
    (htail₁ : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ Γ / 10 * s ≤ |z j - p c|).card : ℝ) ≤
      τ (Γ / 10) * (BS23.cluster ℓ c).card)
    (htail₂ : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ 3 * Γ / 20 * s ≤ |z j - p c|).card :
      ℝ) ≤ τ (3 * Γ / 20) * (BS23.cluster ℓ c).card)
    (htail₃ : ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ 3 * Γ / 10 * s ≤ |z j - p c|).card :
      ℝ) ≤ τ (3 * Γ / 10) * (BS23.cluster ℓ c).card)
    (hθ : 0 < θ) (hθτ : τ (Γ / 10) < θ) (hε : τ A + 3 * k * θ ≤ ε)
    (hεw : ε + τ (3 * Γ / 20) < w) (hH : 0 < H)
    (hgrid : ∃ L ≤ ℓmax, A * s ≤ scale H L ∧ scale H L ≤ Γ * s / 20) :
    ClustersWithin (τ (3 * Γ / 10)) ℓ (List.ofFn (cluster k θ ε H ℓmax z)) := by
  have hpinj : Function.Injective p := fun a b hab ↦ by
    by_contra hne
    have h1 := hsep a b hne
    rw [hab, sub_self, abs_zero] at h1
    obtain ⟨L, -, -, hLΓ⟩ := hgrid
    have := scale_pos hH L
    linarith
  obtain ⟨L, hL, hAL, hLΓ⟩ := hgrid
  -- the chosen scale
  obtain ⟨hlev, hcov⟩ := level_spec hL (coverage_ge hn (scale_pos hH L) hθ hAL htailA hε)
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = scale H (level θ ε H ℓmax z) := ⟨_, rfl⟩
  rw [← hδdef] at hcov
  have hcl : ∀ j, cluster k θ ε H ℓmax z j = labelOfCell k (heavy θ δ z) (cell δ (z j)) := by
    intro j
    rw [hδdef]
    rfl
  have hδ : 0 < δ := hδdef ▸ scale_pos hH _
  have hδΓ : δ ≤ Γ * s / 20 := hδdef ▸ (scale_anti hH.le hlev).trans hLΓ
  -- the groups of the heavy cells
  set S := heavy θ δ z
  have hnear : ∀ Q ∈ S, ∃ c, Near δ Γ s p Q c :=
    fun Q hQ ↦ exists_near_of_mem_heavy hn hδ htail₁ hθτ hQ
  have hex : ∀ Q : ℤ, ∃ c : Fin k, Q ∈ S → Near δ Γ s p Q c := by
    intro Q
    by_cases hQ : Q ∈ S
    · obtain ⟨c, hc⟩ := hnear Q hQ
      exact ⟨c, fun _ ↦ hc⟩
    · exact ⟨⟨0, by omega⟩, fun h ↦ absurd h hQ⟩
  choose g hg using hex
  have hG : Grouped S g p :=
    { inj := hpinj
      surj := fun c ↦ by
        obtain ⟨Q, hQ, hQc⟩ := exists_heavy_near hn hδ hδΓ hsep hcov hw hsize htail₂ hεw hnear c
        exact ⟨Q, hQ, near_unique hδΓ hsep (hg Q hQ) hQc⟩
      ord := fun Q hQ Q' hQ' hlt ↦ lt_of_near hδ hδΓ (hg Q hQ) (hg Q' hQ') (sep_of_lt hsep hlt)
      gap_lt := fun q hq q' hq' b hb b' hb' hbb' hqq' hne ↦ by
        have hlt : p (g b) < p (g b') := by
          rcases lt_trichotomy (p (g b)) (p (g b')) with h1 | h1 | h1
          · exact h1
          · exact absurd (hpinj h1) hne
          · exact absurd (lt_of_near hδ hδΓ (hg b' hb') (hg b hb) (sep_of_lt hsep h1))
              (not_lt.2 hbb'.le)
        have hq'' : Near δ Γ s p q' (g q) := by
          rw [hqq']
          exact hg q' hq'
        exact gap_lt_of_near hδ hδΓ (hg q hq) hq'' (hg b hb) (hg b' hb') (sep_of_lt hsep hlt) }
  -- points close to their center get the rank of their center
  have hlabel : ∀ j, |z j - p (ℓ j)| < 3 * Γ / 10 * s →
      cluster k θ ε H ℓmax z j = rank p (ℓ j) := by
    intro j hj
    rw [hcl]
    apply hG.labelOfCell_eq hk
    intro b hb
    obtain ⟨hbS, b', hb', hne⟩ := Finset.mem_filter.1 hb
    obtain ⟨hb'S, -, -⟩ := (next_eq_some_iff S).1 hb'
    rw [gap_eq_of_next S hb', show b + (b' - b) = b' by ring]
    exact mid_iff hδ hδΓ (hg b hbS) (hg b' hb'S) (sep_of_lt hsep (hG.lt_of_next hbS hb' hne))
      (fun hlt ↦ hG.le_of_next hbS hb' hlt) hj
  -- the permutation: rank ↦ component
  let e : Fin k → Fin k := fun c ↦ ⟨rank p c, rank_lt c⟩
  have he : Function.Bijective e :=
    Finite.injective_iff_bijective.1 fun a b hab ↦ rank_injective hpinj (congrArg Fin.val hab)
  let π := (Equiv.ofBijective e he).symm
  have hπ : ∀ i : Fin k, rank p (π i) = i := fun i ↦
    congrArg Fin.val ((Equiv.ofBijective e he).apply_symm_apply i)
  refine ⟨List.length_ofFn, fun j ↦ ?_, π, ?_⟩
  · rw [outCluster_ofFn, hcl]
    exact labelOfCell_lt _ (by omega) _
  · have key : ∀ i : Fin k, ((BS23.cluster ℓ (π i)).card : ℝ) -
        τ (3 * Γ / 10) * (BS23.cluster ℓ (π i)).card ≤
        (((Finset.univ.filter fun j : Fin n ↦
          outCluster (List.ofFn (cluster k θ ε H ℓmax z)) j = i) ∩
            BS23.cluster ℓ (π i)).card : ℝ) := by
      intro i
      have hsplit := Finset.card_filter_add_card_filter_not (s := BS23.cluster ℓ (π i))
        (fun j ↦ |z j - p (π i)| < 3 * Γ / 10 * s)
      have hfar : ((BS23.cluster ℓ (π i)).filter fun j ↦ ¬ |z j - p (π i)| < 3 * Γ / 10 * s) =
          (BS23.cluster ℓ (π i)).filter fun j ↦ 3 * Γ / 10 * s ≤ |z j - p (π i)| :=
        Finset.filter_congr fun j _ ↦ not_lt
      rw [hfar] at hsplit
      have hsub : ((BS23.cluster ℓ (π i)).filter fun j ↦ |z j - p (π i)| < 3 * Γ / 10 * s) ⊆
          (Finset.univ.filter fun j : Fin n ↦
            outCluster (List.ofFn (cluster k θ ε H ℓmax z)) j = i) ∩ BS23.cluster ℓ (π i) := by
        intro j hj
        obtain ⟨hjc, hjclose⟩ := Finset.mem_filter.1 hj
        have hℓ : ℓ j = π i := (Finset.mem_filter.1 hjc).2
        refine Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hjc⟩
        rw [outCluster_ofFn, hlabel j (by rw [hℓ]; exact hjclose), hℓ]
        exact hπ i
      have h1 : (((BS23.cluster ℓ (π i)).filter fun j ↦ |z j - p (π i)| < 3 * Γ / 10 * s).card :
          ℝ) + ((BS23.cluster ℓ (π i)).filter fun j ↦ 3 * Γ / 10 * s ≤ |z j - p (π i)|).card =
          (BS23.cluster ℓ (π i)).card := by
        exact_mod_cast hsplit
      have h2 := htail₃ (π i)
      have h3 : (((BS23.cluster ℓ (π i)).filter fun j ↦ |z j - p (π i)| < 3 * Γ / 10 * s).card :
          ℝ) ≤ (((Finset.univ.filter fun j : Fin n ↦
            outCluster (List.ofFn (cluster k θ ε H ℓmax z)) j = i) ∩
              BS23.cluster ℓ (π i)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ key i
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      Equiv.sum_comp π (fun c ↦ ((BS23.cluster ℓ c).card : ℝ)), sum_card_cluster] at hsum
    rw [sub_le_comm, le_div_iff₀ (by exact_mod_cast hn)]
    linarith

/-- **The clustering on the line is correct.** The points `z` have labels `ℓ` in `k ≥ 2`
components with centers `p` at least `Γ s` apart, every component holds at least a `w` fraction
of the points, and at most a `τ ρ` fraction of the points of each component is at distance at
least `ρ s` from its center. If light cells are far from the centers (`τ (Γ/10) < θ`), the
coverage is enough at a scale of at least `A s` (`τ A + 3 k θ ≤ ε`), every component keeps
points in heavy cells (`ε + τ (3Γ/20) < w`), and a grid scale lies in `[A s, Γ s / 20]`, then
the output errs on at most a `τ (3Γ/10)` fraction of the points. -/
theorem cluster_clustersWithin {n k : ℕ} (hk : 2 ≤ k) (hn : 0 < n) (z : Fin n → ℝ)
    (ℓ : Fin n → Fin k) (p : Fin k → ℝ) {s Γ w θ ε A H : ℝ} (τ : ℝ → ℝ) {ℓmax : ℕ}
    (hΓ : 0 < Γ) (hsep : ∀ a b, a ≠ b → Γ * s ≤ |p a - p b|)
    (hw : 0 < w) (hsize : ∀ c, w * n ≤ (BS23.cluster ℓ c).card)
    (hA : 0 < A)
    (htail : ∀ ρ, 0 < ρ → ∀ c, (((BS23.cluster ℓ c).filter fun j ↦ ρ * s ≤ |z j - p c|).card :
      ℝ) ≤ τ ρ * (BS23.cluster ℓ c).card)
    (hθ : 0 < θ) (hθτ : τ (Γ / 10) < θ) (hε : τ A + 3 * k * θ ≤ ε)
    (hεw : ε + τ (3 * Γ / 20) < w) (hH : 0 < H)
    (hgrid : ∃ L ≤ ℓmax, A * s ≤ scale H L ∧ scale H L ≤ Γ * s / 20) :
    ClustersWithin (τ (3 * Γ / 10)) ℓ (List.ofFn (cluster k θ ε H ℓmax z)) :=
  cluster_clustersWithin_of_tails hk hn z ℓ p τ hsep hw hsize (htail A hA)
    (htail _ (by positivity)) (htail _ (by positivity)) (htail _ (by positivity)) hθ hθτ hε hεw
    hH hgrid

end BS23.OneDim
