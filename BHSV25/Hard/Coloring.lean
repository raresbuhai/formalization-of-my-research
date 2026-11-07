module

public import BHSV25.Hard.Blowup

/-!
# Colorings of blow-ups

The two cases of the reductions, for a blow-up `H` of a template by a graph `G`
(`BHSV25/Hard/Blowup.lean`).

* **No-instances** (`BHSV25.Hard.Template.numColored_le`): in a cell `u` with `W u u = 1`, the
  vertices are adjacent as in `G`, so each color class of a partial coloring of `H` meets the cell
  in an independent set of `G`. If `G` has no independent set of `s` vertices, a partial
  `k`-coloring colors fewer than `k s` vertices of such a cell.
* **Yes-instances** (`BHSV25.Hard.Template.mono_cover`): labels give each cell two colors `c₁, c₂`
  and say which cells are garbage (`BHSV25.Hard.Template.Labels`). For disjoint independent sets
  `I, J` of `G`, color `(u, v)` by `c₂ u` if `v ∈ J` and by `c₁ u` otherwise
  (`BHSV25.Hard.Template.Labels.chi`). If cells adjacent in `T`, or related by `W`, have disjoint
  colors (unless one is garbage), and cells with `W u u = 1` have `c₁ u ≠ c₂ u`, the
  monochromatic edges are covered by the garbage cells and the vertices of cells with
  `W u u = 1` outside `I ∪ J` (`BHSV25.Hard.Template.Labels.cover`). If every color is as often
  `c₁` as `c₂`, the class of `a` has `n` times as many vertices as cells with `c₁ = a`
  (`BHSV25.Hard.Template.Labels.card_chi`).
-/

@[expose] public section

namespace BHSV25.Hard

open Finset

namespace Template

variable (Tm : Template)

theorem cell_mk {n : ℕ} (a : Fin Tm.C × Fin n) : Tm.cell (finProdFinEquiv a) = a.1 := by
  simp [cell]

theorem vtx_mk {n : ℕ} (a : Fin Tm.C × Fin n) : Tm.vtx (finProdFinEquiv a) = a.2 := by
  simp [vtx]

/-- Counting the vertices of a blow-up cell by cell. -/
theorem card_filter_blowup {n : ℕ} (P : Fin (Tm.C * n) → Prop) [DecidablePred P] :
    ((univ.filter P).card : ℝ) =
      ∑ u, ((univ.filter fun v ↦ P (finProdFinEquiv (u, v))).card : ℝ) := by
  rw [card_filter]
  push_cast
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ ↦ ?_
  rw [card_filter]
  push_cast
  rfl

/-! ### No-instances -/

/-- **No-instances**: if `G` has no independent set of `s` vertices, a partial `k`-coloring of the
blow-up colors at most `n` vertices of each cell with `W u u ≠ 1` and at most `k s` of each
other cell. -/
theorem numColored_le (G : Graph) (k : ℕ) (c : List ℕ)
    (hc : (Tm.blowup G).IsPartialColoring k c) (s : ℝ)
    (hs : ∀ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) → (I.card : ℝ) < s) :
    ((Tm.blowup G).numColored k c : ℝ) ≤
      (univ.filter fun u ↦ Tm.W u u ≠ 1).card * G.1 +
        (univ.filter fun u ↦ Tm.W u u = 1).card * (k * s) := by
  classical
  unfold Graph.numColored
  rw [card_filter_blowup]
  have hcell : ∀ u, ((univ.filter fun v ↦
      (Tm.blowup G).color k c (finProdFinEquiv (u, v)) < k).card : ℝ) ≤
      if Tm.W u u = 1 then k * s else G.1 := by
    intro u
    split_ifs with hu
    · -- the cell is colored like `G`
      have hsub : (univ.filter fun v ↦ (Tm.blowup G).color k c (finProdFinEquiv (u, v)) < k) ⊆
          (range k).biUnion fun a ↦
            univ.filter fun v ↦ (Tm.blowup G).color k c (finProdFinEquiv (u, v)) = a := by
        intro v hv
        simp only [mem_filter, mem_univ, true_and] at hv
        simp [hv]
      have hind : ∀ a ∈ range k, (((univ.filter fun v ↦
          (Tm.blowup G).color k c (finProdFinEquiv (u, v)) = a).card : ℕ) : ℝ) < s := by
        intro a ha
        refine hs _ fun v hv v' hv' hne hadj ↦ ?_
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hv'
        have hH : (Tm.blowup G).2.Adj (finProdFinEquiv (u, v)) (finProdFinEquiv (u, v')) := by
          rw [blowup_adj, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          unfold adj
          rw [ite_eq_left hu]
          exact hadj
        exact hc _ _ hH (by rw [hv]; exact mem_range.1 ha) (by rw [hv, hv'])
      calc ((univ.filter fun v ↦ (Tm.blowup G).color k c (finProdFinEquiv (u, v)) < k).card : ℝ)
          ≤ (((range k).biUnion fun a ↦ univ.filter fun v ↦
              (Tm.blowup G).color k c (finProdFinEquiv (u, v)) = a).card : ℝ) := by
            exact_mod_cast card_le_card hsub
        _ ≤ ∑ a ∈ range k, (((univ.filter fun v ↦
              (Tm.blowup G).color k c (finProdFinEquiv (u, v)) = a).card : ℕ) : ℝ) := by
            exact_mod_cast card_biUnion_le
        _ ≤ ∑ _a ∈ range k, s := sum_le_sum fun a ha ↦ (hind a ha).le
        _ = k * s := by rw [sum_const, card_range, nsmul_eq_mul]
    · exact_mod_cast (card_filter_le _ _).trans (by simp)
  calc ∑ u, ((univ.filter fun v ↦
        (Tm.blowup G).color k c (finProdFinEquiv (u, v)) < k).card : ℝ)
      ≤ ∑ u, (if Tm.W u u = 1 then (k * s : ℝ) else G.1) := sum_le_sum fun u _ ↦ hcell u
    _ = _ := by
        rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, add_comm]

/-! ### Yes-instances -/

/-- **Labels** of the cells of a template: two colors per cell and the garbage cells. -/
structure Labels (k : ℕ) where
  /-- The color of the vertices outside `J`. -/
  c₁ : Fin Tm.C → Fin k
  /-- The color of the vertices in `J`. -/
  c₂ : Fin Tm.C → Fin k
  /-- The garbage cells, whose vertices are given up. -/
  garbage : Fin Tm.C → Prop
  [dec : DecidablePred garbage]

attribute [instance] Labels.dec

namespace Labels

variable {Tm} {k : ℕ} (L : Tm.Labels k)

/-- The colors of two cells are disjoint. -/
def Disj (u u' : Fin Tm.C) : Prop :=
  L.c₁ u ≠ L.c₁ u' ∧ L.c₁ u ≠ L.c₂ u' ∧ L.c₂ u ≠ L.c₁ u' ∧ L.c₂ u ≠ L.c₂ u'

/-- The conditions on labels for the yes-instances. -/
structure Valid : Prop where
  disj_T : ∀ u u', Tm.T u u' = true → L.Disj u u'
  disj_W : ∀ u u', u ≠ u' → Tm.W u u' ≠ 0 → L.garbage u ∨ L.garbage u' ∨ L.Disj u u'
  diag : ∀ u, Tm.W u u = 1 → L.garbage u ∨ L.c₁ u ≠ L.c₂ u

variable {G : Graph} (J : Finset (Fin G.1))

/-- The coloring of the blow-up given by the labels and a set `J` of vertices of `G`. -/
def chi (p : Fin (Tm.C * G.1)) : Fin k :=
  if Tm.vtx p ∈ J then L.c₂ (Tm.cell p) else L.c₁ (Tm.cell p)

open Classical in
/-- The vertices that the coloring gives up: those of garbage cells, and those outside `I ∪ J`
of cells with `W u u = 1`. -/
noncomputable def cover (I : Finset (Fin G.1)) : Finset (Fin (Tm.C * G.1)) :=
  univ.filter fun p ↦ L.garbage (Tm.cell p) ∨
    (Tm.W (Tm.cell p) (Tm.cell p) = 1 ∧ Tm.vtx p ∉ I ∧ Tm.vtx p ∉ J)

theorem chi_mem (p : Fin (Tm.C * G.1)) :
    L.chi J p = L.c₁ (Tm.cell p) ∨ L.chi J p = L.c₂ (Tm.cell p) := by
  unfold chi; split_ifs <;> simp

theorem chi_ne_of_disj {p q : Fin (Tm.C * G.1)} (h : L.Disj (Tm.cell p) (Tm.cell q)) :
    L.chi J p ≠ L.chi J q := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases L.chi_mem J p with hp | hp <;> rcases L.chi_mem J q with hq | hq <;>
    rw [hp, hq] <;> assumption

/-- **The monochromatic edges are covered.** -/
theorem mono_cover (hL : L.Valid) {I : Finset (Fin G.1)}
    (hI : G.2.IsIndepSet (I : Set (Fin G.1))) (hJ : G.2.IsIndepSet (J : Set (Fin G.1)))
    {p q : Fin (Tm.C * G.1)} (hpq : (Tm.blowup G).2.Adj p q) (hχ : L.chi J p = L.chi J q) :
    p ∈ L.cover J I ∨ q ∈ L.cover J I := by
  classical
  by_contra hcon
  simp only [not_or, cover, mem_filter, mem_univ, true_and, not_and, not_not] at hcon
  obtain ⟨⟨hpg, hpI⟩, ⟨hqg, hqI⟩⟩ := hcon
  rw [blowup_adj] at hpq
  change Tm.adj G.2 (Tm.cell p, Tm.vtx p) (Tm.cell q, Tm.vtx q) at hpq
  unfold adj at hpq
  simp only at hpq
  split_ifs at hpq with hW1 hW2
  · -- an edge of `G` inside a cell, or between cells related by `W`
    by_cases hc : Tm.cell p = Tm.cell q
    · have hdiag : Tm.W (Tm.cell p) (Tm.cell p) = 1 := by rw [hc] at hW1 ⊢; exact hW1
      have hne := (hL.diag _ hdiag).resolve_left hpg
      have hpIJ := hpI hdiag
      have hqIJ := hqI (by rw [← hc]; exact hdiag)
      unfold chi at hχ
      rw [hc] at hχ hne
      by_cases hpJ : Tm.vtx p ∈ J <;> by_cases hqJ : Tm.vtx q ∈ J <;>
        simp only [hpJ, hqJ, ite_true, ite_false] at hχ
      · exact hJ hpJ hqJ (G.2.ne_of_adj hpq) hpq
      · exact hne hχ.symm
      · exact hne hχ
      · exact hI (by by_contra h; exact hpJ (hpIJ h)) (by by_contra h; exact hqJ (hqIJ h))
          (G.2.ne_of_adj hpq) hpq
    · rcases hL.disj_W _ _ hc (by rw [hW1]; decide) with h | h | h
      · exact hpg h
      · exact hqg h
      · exact L.chi_ne_of_disj J h hχ
  · exact L.chi_ne_of_disj J (hL.disj_T _ _ hpq.1) hχ
  · exact L.chi_ne_of_disj J (hL.disj_T _ _ hpq) hχ

/-- The size of the cover. -/
theorem card_cover_le (I : Finset (Fin G.1)) :
    ((L.cover J I).card : ℝ) ≤ (univ.filter L.garbage).card * G.1 +
      (univ.filter fun u ↦ Tm.W u u = 1).card *
        ((univ.filter fun v ↦ v ∉ I ∧ v ∉ J).card : ℝ) := by
  classical
  unfold cover
  rw [Tm.card_filter_blowup]
  have hcell : ∀ u, ((univ.filter fun v ↦ L.garbage (Tm.cell (finProdFinEquiv (u, v))) ∨
      (Tm.W (Tm.cell (finProdFinEquiv (u, v))) (Tm.cell (finProdFinEquiv (u, v))) = 1 ∧
        Tm.vtx (finProdFinEquiv (u, v)) ∉ I ∧ Tm.vtx (finProdFinEquiv (u, v)) ∉ J)).card : ℝ)
      ≤ (if L.garbage u then (G.1 : ℝ) else 0) +
        (if Tm.W u u = 1 then ((univ.filter fun v ↦ v ∉ I ∧ v ∉ J).card : ℝ) else 0) := by
    intro u
    simp only [cell_mk, vtx_mk]
    by_cases hg : L.garbage u
    · simp only [hg, true_or, filter_true, card_univ, Fintype.card_fin, ite_true]
      split_ifs <;> simp
    · simp only [hg, false_or, ite_false, zero_add]
      split_ifs with hw
      · simp [hw]
      · simp [hw]
  refine (sum_le_sum fun u _ ↦ hcell u).trans (le_of_eq ?_)
  rw [sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const, nsmul_eq_mul,
    nsmul_eq_mul]

/-- The size of a color class. -/
theorem card_chi (a : Fin k) :
    ((univ.filter fun p ↦ L.chi J p = a).card : ℝ) =
      ∑ u, ((if L.c₁ u = a then (G.1 : ℝ) - J.card else 0) +
        if L.c₂ u = a then (J.card : ℝ) else 0) := by
  classical
  rw [Tm.card_filter_blowup]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [chi, cell_mk, vtx_mk]
  have hsplit : (univ.filter fun v : Fin G.1 ↦ (if v ∈ J then L.c₂ u else L.c₁ u) = a) =
      (univ.filter fun v ↦ v ∉ J ∧ L.c₁ u = a) ∪ (univ.filter fun v ↦ v ∈ J ∧ L.c₂ u = a) := by
    ext v; by_cases hv : v ∈ J <;> simp [hv]
  rw [hsplit, card_union_of_disjoint (disjoint_filter.2 fun v _ h1 h2 ↦ h1.1 h2.1)]
  push_cast
  congr 1
  · split_ifs with h
    · simp only [h, and_true]
      rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]
      simp only [filter_mem_eq_inter, univ_inter]
      rw [Nat.cast_sub (card_le_univ J |>.trans (by simp))]
    · simp [h]
  · split_ifs with h
    · simp [h]
    · simp [h]

/-- **Class sizes**: if every color is as often `c₁` as `c₂`, the class of `a` has `n` times as
many vertices as cells with `c₁ = a`. -/
theorem card_chi_of_sym
    (hsym : ∀ a, (univ.filter fun u ↦ L.c₁ u = a).card = (univ.filter fun u ↦ L.c₂ u = a).card)
    (a : Fin k) :
    ((univ.filter fun p ↦ L.chi J p = a).card : ℝ) =
      G.1 * (univ.filter fun u ↦ L.c₁ u = a).card := by
  rw [L.card_chi J a, sum_add_distrib, ← sum_filter, ← sum_filter, sum_const, sum_const,
    nsmul_eq_mul, nsmul_eq_mul, ← hsym a]
  ring

end Labels

end Template

end BHSV25.Hard
