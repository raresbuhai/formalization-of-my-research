module

public import BHSV25.Planted.Uncolor

/-!
# Safe recoloring

The deterministic part of [BHSV25, Lemma B.21] (`BHSV25.Planted.recolor_spec`): if every colored
vertex of `c` has its color under a proper coloring `χ` of `G`, safe recoloring
(`BHSV25.Planted.recolor`) keeps this property and the colored vertices, and at the end every
uncolored vertex `y` misses a color `a ≠ χ(y)` among its neighbors.

An uncolored vertex `y` never sees the color `χ(y)` among its neighbors, so if it misses exactly
one color, that color is `χ(y)`; a round in which no vertex misses exactly one color changes
nothing, and the others color a vertex, so after `n + 1` rounds every uncolored vertex misses
`χ(y)` and another color.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {G : Graph} {k : ℕ}

theorem mem_missing_iff (c : List ℕ) (y : Fin G.1) (a : ℕ) :
    a ∈ missing G.1 k (adjTable G) c y ↔
      a < k ∧ ∀ z : Fin G.1, G.2.Adj y z → c.getD z k ≠ a := by
  rw [missing, List.mem_filter, List.mem_range]
  simp only [Bool.not_eq_true', List.any_eq_false, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq, not_and]
  constructor
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun z hz ↦ h z z.2 ?_⟩
    rw [Alg.adjBit_adjTable]; simpa using hz
  · rintro ⟨ha, h⟩
    refine ⟨ha, fun z hz hadj ↦ h ⟨z, hz⟩ ?_⟩
    have := Alg.adjBit_adjTable G y ⟨z, hz⟩
    simp only at this
    rw [this] at hadj
    simpa using hadj

theorem nodup_missing (c : List ℕ) (y : ℕ) : (missing G.1 k (adjTable G) c y).Nodup :=
  List.nodup_range.filter _

/-- The color `χ(y)` is missing at `y` when every colored vertex has its color under `χ`. -/
theorem mem_missing_self (χ : Fin G.1 → Fin k) (hχ : ∀ u v, G.2.Adj u v → χ u ≠ χ v)
    (c : List ℕ) (hc : ∀ y : Fin G.1, c.getD y k < k → c.getD y k = χ y) (y : Fin G.1) :
    (χ y : ℕ) ∈ missing G.1 k (adjTable G) c y := by
  rw [mem_missing_iff]
  refine ⟨(χ y).2, fun z hz h ↦ ?_⟩
  have hzk : c.getD z k < k := by rw [h]; exact (χ y).2
  rw [hc z hzk] at h
  exact hχ y z hz (Fin.ext h.symm)

/-- `y` can be recolored. -/
def recolorable (n k : ℕ) (adj : List Bool) (c : List ℕ) (y : ℕ) : Bool :=
  decide (k ≤ c.getD y k) && decide ((missing n k adj c y).length = 1)

theorem getD_recolorStep (c : List ℕ) (y : Fin G.1) :
    (recolorStep G.1 k (adjTable G) c).getD y k =
      if recolorable G.1 k (adjTable G) c y then (missing G.1 k (adjTable G) c y).headD k
      else c.getD y k :=
  Net.getD_map_range G.1 _ k y.2

theorem missing_congr {c c' : List ℕ} (h : ∀ z : Fin G.1, c.getD z k = c'.getD z k)
    (y : Fin G.1) : missing G.1 k (adjTable G) c y = missing G.1 k (adjTable G) c' y := by
  unfold missing
  refine List.filter_congr fun a _ ↦ ?_
  have hz' : ∀ z ∈ List.range G.1, c.getD z k = c'.getD z k :=
    fun z hz ↦ h ⟨z, List.mem_range.1 hz⟩
  have : ((List.range G.1).any fun z ↦ Alg.adjBit G.1 (adjTable G) y z && decide (c.getD z k = a)) =
      ((List.range G.1).any fun z ↦
        Alg.adjBit G.1 (adjTable G) y z && decide (c'.getD z k = a)) := by
    rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨z, hz, h'⟩; exact ⟨z, hz, by rw [← hz' z hz]; exact h'⟩
    · rintro ⟨z, hz, h'⟩; exact ⟨z, hz, by rw [hz' z hz]; exact h'⟩
  rw [this]

theorem recolorable_congr {c c' : List ℕ} (h : ∀ z : Fin G.1, c.getD z k = c'.getD z k)
    (y : Fin G.1) :
    recolorable G.1 k (adjTable G) c y = recolorable G.1 k (adjTable G) c' y := by
  rw [recolorable, recolorable, h y, missing_congr h]

theorem headD_missing_lt {c : List ℕ} {y : ℕ}
    (h : (missing G.1 k (adjTable G) c y).length = 1) :
    (missing G.1 k (adjTable G) c y).headD k < k := by
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 h
  have hmem : a ∈ missing G.1 k (adjTable G) c y := by rw [ha]; exact List.mem_singleton_self a
  rw [ha, List.headD_cons]
  rw [missing, List.mem_filter, List.mem_range] at hmem
  exact hmem.1

theorem recolorStep_colored {c : List ℕ} {y : Fin G.1} (hy : c.getD y k < k) :
    (recolorStep G.1 k (adjTable G) c).getD y k = c.getD y k := by
  rw [getD_recolorStep, ite_eq_right]
  simp only [recolorable, Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro h
  exact absurd h (not_le.2 hy)

theorem numCol'_recolorStep_le (c : List ℕ) :
    numCol' G k c ≤ numCol' G k (recolorStep G.1 k (adjTable G) c) := by
  refine card_le_card fun y hy ↦ ?_
  rw [mem_filter] at hy ⊢
  exact ⟨hy.1, by rw [recolorStep_colored hy.2]; exact hy.2⟩

theorem numCol'_recolorStep_lt (c : List ℕ) {y : Fin G.1}
    (hy : recolorable G.1 k (adjTable G) c y = true) :
    numCol' G k c < numCol' G k (recolorStep G.1 k (adjTable G) c) := by
  refine card_lt_card ⟨fun x hx ↦ ?_, fun hsub ↦ ?_⟩
  · rw [mem_filter] at hx ⊢
    exact ⟨hx.1, by rw [recolorStep_colored hx.2]; exact hx.2⟩
  · simp only [recolorable, Bool.and_eq_true, decide_eq_true_eq] at hy
    have h1 : y ∈ univ.filter fun y : Fin G.1 ↦
        (recolorStep G.1 k (adjTable G) c).getD y k < k := by
      rw [mem_filter, getD_recolorStep, ite_eq_left (by
        simp only [recolorable, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hy.1, hy.2⟩)]
      exact ⟨mem_univ _, headD_missing_lt hy.2⟩
    have := hsub h1
    rw [mem_filter] at this
    omega

theorem recolorStep_getD_of_none (c : List ℕ)
    (h : ∀ y : Fin G.1, recolorable G.1 k (adjTable G) c y = false) (y : Fin G.1) :
    (recolorStep G.1 k (adjTable G) c).getD y k = c.getD y k := by
  rw [getD_recolorStep, ite_eq_right (by simp [h y])]

/-- **After `n + 1` rounds no vertex can be recolored.** -/
theorem recolor_none (c : List ℕ) (y : Fin G.1) :
    recolorable G.1 k (adjTable G) (recolor G.1 k (adjTable G) c) y = false := by
  set f := recolorStep G.1 k (adjTable G)
  by_contra hcon
  rw [Bool.not_eq_false] at hcon
  have hpres : ∀ j, (∀ y : Fin G.1, recolorable G.1 k (adjTable G) (f^[j] c) y = false) →
      ∀ y : Fin G.1, recolorable G.1 k (adjTable G) (f^[j + 1] c) y = false := by
    intro j hj y
    rw [Function.iterate_succ_apply', recolorable_congr (recolorStep_getD_of_none _ hj)]
    exact hj y
  have hall : ∀ j ≤ G.1 + 1, ∃ y : Fin G.1,
      recolorable G.1 k (adjTable G) (f^[j] c) y = true := by
    intro j hj
    by_contra hnone
    push Not at hnone
    simp only [Bool.not_eq_true] at hnone
    have : ∀ i, ∀ y : Fin G.1, recolorable G.1 k (adjTable G) (f^[j + i] c) y = false := by
      intro i
      induction i with
      | zero => exact hnone
      | succ i ih => exact hpres (j + i) ih
    have h2 := this (G.1 + 1 - j) y
    rw [show j + (G.1 + 1 - j) = G.1 + 1 by omega] at h2
    rw [recolor] at hcon
    rw [h2] at hcon
    exact Bool.false_ne_true hcon
  have hinc : ∀ j ≤ G.1 + 1, numCol' G k c + j ≤ numCol' G k (f^[j] c) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨y, hy⟩ := hall j (by omega)
      have h1 : numCol' G k (f^[j] c) < numCol' G k (f (f^[j] c)) :=
        numCol'_recolorStep_lt (f^[j] c) hy
      rw [Function.iterate_succ_apply']
      have := ih (by omega)
      omega
  have h1 := hinc (G.1 + 1) le_rfl
  have h2 : numCol' G k (f^[G.1 + 1] c) ≤ G.1 := by
    have := card_le_univ (univ.filter fun y : Fin G.1 ↦ (f^[G.1 + 1] c).getD y k < k)
    rwa [Fintype.card_fin] at this
  omega

theorem eq_of_length_eq_one {l : List ℕ} {a : ℕ} (hl : l.length = 1) (ha : a ∈ l) :
    l.headD 0 = a ∧ l.headD k = a := by
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 hl
  rw [hb, List.mem_singleton] at ha
  rw [hb, ha]
  simp

/-- **Safe recoloring** [BHSV25, Lemma B.21, deterministic part]. -/
theorem recolor_spec (χ : Fin G.1 → Fin k) (hχ : ∀ u v, G.2.Adj u v → χ u ≠ χ v) (c : List ℕ)
    (hc : ∀ y : Fin G.1, c.getD y k < k → c.getD y k = χ y)
    (hck : ∀ y : Fin G.1, c.getD y k ≤ k) :
    (∀ y : Fin G.1, (recolor G.1 k (adjTable G) c).getD y k < k →
      (recolor G.1 k (adjTable G) c).getD y k = χ y) ∧
    (∀ y : Fin G.1, c.getD y k < k → (recolor G.1 k (adjTable G) c).getD y k = c.getD y k) ∧
    (∀ y : Fin G.1, (recolor G.1 k (adjTable G) c).getD y k ≤ k) ∧
    (∀ y : Fin G.1, (recolor G.1 k (adjTable G) c).getD y k = k → ∃ a : Fin k, a ≠ χ y ∧
      ∀ z : Fin G.1, G.2.Adj y z → (recolor G.1 k (adjTable G) c).getD z k ≠ a) := by
  set f := recolorStep G.1 k (adjTable G)
  -- the invariants of the rounds
  have hinv : ∀ j, (∀ y : Fin G.1, (f^[j] c).getD y k < k → (f^[j] c).getD y k = χ y) ∧
      (∀ y : Fin G.1, c.getD y k < k → (f^[j] c).getD y k = c.getD y k) ∧
      (∀ y : Fin G.1, (f^[j] c).getD y k ≤ k) := by
    intro j
    induction j with
    | zero => exact ⟨hc, fun _ _ ↦ rfl, hck⟩
    | succ j ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      rw [Function.iterate_succ_apply']
      refine ⟨fun y hy ↦ ?_, fun y hy ↦ ?_, fun y ↦ ?_⟩
      · rw [getD_recolorStep] at hy ⊢
        split_ifs with hr
        · simp only [recolorable, Bool.and_eq_true, decide_eq_true_eq] at hr
          exact (eq_of_length_eq_one (k := k) hr.2 (mem_missing_self χ hχ _ h1 y)).2
        · rw [ite_eq_right hr] at hy
          exact h1 y hy
      · rw [recolorStep_colored (by rw [h2 y hy]; exact hy), h2 y hy]
      · rw [getD_recolorStep]
        split_ifs with hr
        · simp only [recolorable, Bool.and_eq_true, decide_eq_true_eq] at hr
          exact (headD_missing_lt hr.2).le
        · exact h3 y
  obtain ⟨h1, h2, h3⟩ := hinv (G.1 + 1)
  refine ⟨h1, h2, h3, fun y hy ↦ ?_⟩
  set c' := recolor G.1 k (adjTable G) c with hc'
  have hnr := recolor_none (k := k) c y
  rw [← hc'] at hnr
  have hlen : (missing G.1 k (adjTable G) c' y).length ≠ 1 := by
    intro h
    have : recolorable G.1 k (adjTable G) c' y = true := by
      simp only [recolorable, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hy.ge, h⟩
    rw [hnr] at this
    exact Bool.false_ne_true this
  have hmem := mem_missing_self χ hχ c' h1 y
  -- another missing color
  have hex : ∃ a ∈ missing G.1 k (adjTable G) c' y, a ≠ χ y := by
    by_contra hcon
    push Not at hcon
    have hrep : missing G.1 k (adjTable G) c' y =
        List.replicate (missing G.1 k (adjTable G) c' y).length (χ y : ℕ) :=
      List.eq_replicate_iff.2 ⟨rfl, hcon⟩
    have hnd := nodup_missing (G := G) (k := k) c' y
    rw [hrep, List.nodup_replicate] at hnd
    have hpos : 0 < (missing G.1 k (adjTable G) c' y).length := List.length_pos_of_mem hmem
    omega
  obtain ⟨a, ha, hne⟩ := hex
  rw [mem_missing_iff] at ha
  exact ⟨⟨a, ha.1⟩, fun h ↦ hne (by rw [← h]), fun z hz ↦ ha.2 z hz⟩

end Planted

end BHSV25
