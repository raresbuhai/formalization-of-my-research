module

public import BHSV25.Hard.LowRankFacts
public import BHSV25.Hard.MachineA
public import BHSV25.Hard.Rate

/-!
# Theorem 1.6: hardness of balanced 3-coloring with small third eigenvalue

[BHSV25, Theorem 8.6], in the form of `BHSV25.threeColoring_lowRank_hardness`
(`BHSV25.Hard.threeColoring_lowRank_hardness`). The reduction is the blow-up of the design of
`BHSV25/Hard/LowRankDesign.lean` by the input graph `G` of the gap problem of Bansal and Khot, at
the precision `a = ⌈log₂ n⌉` growing with the input (`BHSV25.Hard.Design.redA`).

* **Spectrum**: the planted matrix has two components (groups `0, 1` and `2, 3, 4`) and is at most
  `0` on the vectors with zero sum on each, so at most `2` eigenvalues exceed the threshold of the
  template; it vanishes on the vectors with zero sum on each group, so at most `5` are below
  minus the threshold. So `R = 7`, without Theorem 1.7.
* **The threshold** is at most `73 / 2^a ≤ 73 / n` (`BHSV25.Hard.LowRank.threshold_le`), and the
  blow-up has at most `576 m² n⁵` vertices, so the threshold is at most `73 (576 m² / N)^{1/5}`
  on `N` vertices (`BHSV25.Hard.thr_le_rate`), which tends to `0`.
* **Yes-instances**: the labels of `BHSV25/Hard/LowRankFacts.lean` give `3` independent sets of a
  third of the vertices each, up to the absorbers and the vertices outside `I ∪ J`; uncoloring
  vertices of the larger ones gives `3` of the same size (`BHSV25.Hard.exists_equal_classes`).
* **No-instances**: the copies of `G` (two ninths of the vertices) have color classes of fewer
  than `γ' n` vertices, so at most `(7/9 + 2 γ' / 3) N` vertices are colored.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM Cayley Cslib.Complexity Filter Topology

namespace LowRank

theorem err_two (a : ℕ) : err a 2 = 32 * 2 ^ a * 4 ^ a := by
  unfold err
  have : (0 : ℝ) < 2 * 4 ^ a := by positivity
  field_simp
  ring

theorem numEigGT_anti (G : Graph) {x y : ℝ} (h : x ≤ y) : G.numEigGT y ≤ G.numEigGT x :=
  card_le_card fun i hi ↦ by
    simp only [mem_filter, mem_univ, true_and] at hi ⊢; linarith

/-- The spectral threshold of the blow-up, for a graph of maximum degree at most its number of
vertices, is at most `73 / 2^a`. -/
theorem threshold_le {m a n : ℕ} (hm : 1 ≤ m) (hn : 0 < n) (Z : ℝ) :
    (2 * ((9 * m ^ 2 : ℕ) * err a 2 * n + (2 * m + 2) * (1 * n) / 2) + 0 * Z) /
      ((8 * m ^ 2 * (4 ^ a) ^ 2 : ℕ) * n) ≤ 73 / 2 ^ a := by
  rw [zero_mul, add_zero, err_two]
  have hY : (1 : ℝ) ≤ 2 ^ a := one_le_pow₀ (by norm_num)
  have hX : (4 : ℝ) ^ a = 2 ^ a * 2 ^ a := by rw [← mul_pow]; norm_num
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  rw [hX]
  set Y : ℝ := 2 ^ a
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hY4 : Y ≤ Y ^ 4 := by nlinarith [pow_le_pow_right₀ hY (show 1 ≤ 4 by norm_num)]
  have hmm : (2 * (m : ℝ) + 2) ≤ 8 * m ^ 2 := by nlinarith
  have h1 : (2 * (m : ℝ) + 2) * n * Y ≤ 8 * m ^ 2 * n * Y ^ 4 := by
    have := mul_le_mul hmm hY4 (by positivity) (by positivity)
    nlinarith
  nlinarith

/-- The weights of the two components of groups. -/
def wt (l : Fin 2) (i : Fin 5) : ℝ :=
  if l = 0 then (if (i : ℕ) < 2 then 1 else 0) else (if 2 ≤ (i : ℕ) then 1 else 0)

theorem chat_neg (m : ℕ) (X : Fin 5 → ℝ) (hX : ∀ l, ∑ i, wt l i * X i = 0) :
    ∑ i, ∑ j, X i * (design m).Chat i j * X j ≤ 0 := by
  have h0 := hX 0
  have h1 := hX 1
  simp only [wt, Fin.sum_univ_five] at h0 h1
  norm_num at h0 h1
  simp only [Fin.sum_univ_five, Design.Chat, q]
  norm_num
  have hX1 : X 1 = -X 0 := by linarith
  have hX4 : X 4 = -X 2 - X 3 := by linarith
  rw [hX1, hX4]
  nlinarith [sq_nonneg (X 0), sq_nonneg (X 2 + X 3 / 4), sq_nonneg (X 3)]

open Classical in
/-- **The spectrum of the blow-up**: at most two eigenvalues above `θ`, at most seven above `θ`
in absolute value, for every `θ` at least the spectral threshold. -/
theorem spectral {m a : ℕ} (hm : 1 ≤ m) (G : Graph) (hn : 0 < G.1) {η θ : ℝ} (hη0 : 0 ≤ η)
    (hdeg : G.MaxDegreeLE η)
    (hθ : (2 * ((9 * m ^ 2 : ℕ) * err a 2 * G.1 + (2 * m + 2) * (η * G.1) / 2) +
      0 * (Fintype.card ((design m).Cell a) * G.1)) / ((8 * m ^ 2 * (4 ^ a) ^ 2 : ℕ) * G.1) ≤ θ) :
    ((design m).blow a G).numEigGT θ ≤ 2 ∧
      (univ.filter fun i ↦ θ < |((design m).blow a G).eig i|).card ≤ 7 := by
  set D := design m
  have hΔ : ∀ v, ∑ v', ind (G.2.Adj v v') ≤ η * G.1 := fun v ↦ by
    rw [sum_ind_adj_eq_degree]; exact hdeg v
  have hd : 0 < D.deg a := by
    simp only [Design.deg, D]; positivity
  have hΔ0 : 0 ≤ η * G.1 := mul_nonneg hη0 (Nat.cast_nonneg _)
  have h1 := D.numEigGT_blow_le a G hn hd hΔ0 (sum_abs_W0 m) hΔ D.Chat (le_refl 0)
    (fun i j ↦ by simp) wt (chat_neg m)
  have h2 := D.card_eig_blow_lt_neg_le a G hn hd hΔ0 (sum_abs_W0 m) hΔ
  have hc : (Fintype.card D.Ty : ℝ) = ((9 * m ^ 2 : ℕ) : ℝ) := by
    rw [show Fintype.card D.Ty = 9 * m ^ 2 from card_ty m]
  have hx := hθ
  rw [← hc] at hx
  refine ⟨(numEigGT_anti _ hx).trans h1, ?_⟩
  refine (card_abs_eig_le _ θ).trans ?_
  have h3 : (univ.filter fun i ↦ (D.blow a G).eig i < -θ).card ≤ 5 := by
    refine le_trans (card_le_card fun i hi ↦ ?_) h2
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    have : (2 * ((Fintype.card D.Ty : ℝ) * err a D.r * G.1 + (2 * m + 2) * (η * G.1) / 2)) /
        ((D.deg a : ℕ) * G.1) ≤ θ := by
      rw [zero_mul, add_zero] at hx; exact hx
    push_cast at this ⊢
    linarith
  have := (numEigGT_anti _ hx).trans h1
  omega

theorem card_cells_col₁ (m a : ℕ) (c : Fin 3) :
    (univ.filter fun u ↦ ((design m).labels a (fun τ ↦ col₁ τ.1) (fun τ ↦ col₂ τ.1)
      (garb m)).c₁ u = c).card = (2 * 4 ^ a) ^ 2 * (3 * m ^ 2) := by
  rw [← card_col₁ m c]
  exact (design m).card_cells a (fun τ ↦ col₁ τ.1 = c)

theorem card_cells_col₂ (m a : ℕ) (c : Fin 3) :
    (univ.filter fun u ↦ ((design m).labels a (fun τ ↦ col₁ τ.1) (fun τ ↦ col₂ τ.1)
      (garb m)).c₂ u = c).card = (2 * 4 ^ a) ^ 2 * (3 * m ^ 2) := by
  rw [← card_col₂ m c]
  exact (design m).card_cells a (fun τ ↦ col₂ τ.1 = c)

theorem card_cells_garb (m a : ℕ) :
    (univ.filter ((design m).labels a (fun τ ↦ col₁ τ.1) (fun τ ↦ col₂ τ.1)
      (garb m)).garbage).card = (2 * 4 ^ a) ^ 2 * (2 * m) := by
  rw [← card_garb m]
  exact (design m).card_cells a (garb m)

theorem card_cells_total (m a : ℕ) :
    Fintype.card ((design m).Cell a) = 9 * m ^ 2 * (2 * 4 ^ a) ^ 2 := by
  rw [Design.card_cell, show Fintype.card (design m).Ty = 9 * m ^ 2 from card_ty m]

theorem card_outside {n : ℕ} {I J : Finset (Fin n)} (hIJ : Disjoint I J) :
    ((univ.filter fun v ↦ v ∉ I ∧ v ∉ J).card : ℝ) = n - I.card - J.card := by
  have h1 : (univ.filter fun v ↦ v ∉ I ∧ v ∉ J) = (I ∪ J)ᶜ := by
    ext v; simp
  rw [h1, card_compl, card_union_of_disjoint hIJ, Fintype.card_fin]
  have : I.card + J.card ≤ n := by
    rw [← card_union_of_disjoint hIJ]; exact (card_le_univ _).trans (by simp)
  push_cast [this]
  ring

/-- **Yes-instances**: a partial `3`-coloring of the blow-up with classes of a third of the
vertices, up to `ε`. -/
theorem yes_coloring {m a : ℕ} (hm : 1 ≤ m) (G : Graph) {εB ε : ℝ}
    (hcov : 2 / (9 * m) + 2 * εB ≤ ε) {I J : Finset (Fin G.1)} (hIJ : Disjoint I J)
    (hI : G.2.IsIndepSet (I : Set (Fin G.1))) (hJ : G.2.IsIndepSet (J : Set (Fin G.1)))
    (hIc : (1 / 2 - εB) * G.1 ≤ I.card) (hJc : (1 / 2 - εB) * G.1 ≤ J.card) :
    ∃ c, ((design m).blow a G).IsPartialColoring 3 c ∧ ∀ col < 3,
      (1 / 3 - ε) * ((design m).blow a G).1 ≤ ((design m).blow a G).classSize 3 c col := by
  classical
  set D := design m
  set L := D.labels a (fun τ ↦ col₁ τ.1) (fun τ ↦ col₂ τ.1) (garb m)
  have hL : L.Valid := labels_valid m a
  set S := L.cover J I
  set c : List ℕ := List.ofFn fun p : Fin ((D.blow a G).1) ↦ if p ∈ S then 3 else (L.chi J p : ℕ)
  have hcol : ∀ p, (D.blow a G).color 3 c p = if p ∈ S then 3 else (L.chi J p : ℕ) := by
    intro p
    unfold Graph.color
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [p.2, ↓reduceDIte, Option.getD_some, Fin.eta]
  refine ⟨c, fun p q hpq hp ↦ ?_, fun col hcol3 ↦ ?_⟩
  · rw [hcol] at hp ⊢
    rw [hcol]
    have hpS : p ∉ S := by intro h; rw [ite_eq_left h] at hp; exact lt_irrefl _ hp
    rw [ite_eq_right hpS]
    by_cases hqS : q ∈ S
    · rw [ite_eq_left hqS]; exact (L.chi J p).2.ne
    · rw [ite_eq_right hqS]
      intro heq
      rcases L.mono_cover J hL hI hJ hpq (Fin.ext heq) with h | h
      · exact hpS h
      · exact hqS h
  · set a' : Fin 3 := ⟨col, hcol3⟩
    have hsym : ∀ c' : Fin 3, (univ.filter fun u ↦ L.c₁ u = c').card =
        (univ.filter fun u ↦ L.c₂ u = c').card := fun c' ↦ by
      rw [card_cells_col₁, card_cells_col₂]
    have hchi := L.card_chi_of_sym J hsym a'
    rw [card_cells_col₁] at hchi
    have hS := L.card_cover_le J I
    rw [card_cells_garb, card_outside hIJ] at hS
    have hW : ((univ.filter fun u ↦ (D.template a).W u u = 1).card : ℝ) ≤
        9 * m ^ 2 * (2 * 4 ^ a) ^ 2 := by
      have h1 := card_filter_le (univ : Finset (Fin (D.template a).C))
        (fun u ↦ (D.template a).W u u = 1)
      rw [card_univ, Fintype.card_fin] at h1
      have h2 : ((D.template a).C : ℝ) = 9 * m ^ 2 * (2 * 4 ^ a) ^ 2 := by
        exact_mod_cast card_cells_total m a
      calc _ ≤ ((D.template a).C : ℝ) := by exact_mod_cast h1
        _ = _ := h2
    have hsub : (univ.filter fun p ↦ L.chi J p = a') ⊆
        (univ.filter fun p ↦ (D.blow a G).color 3 c p = col) ∪ S := by
      intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      by_cases hpS : p ∈ S
      · exact mem_union_right _ hpS
      · refine mem_union_left _ ?_
        simp only [mem_filter, mem_univ, true_and]
        rw [hcol, ite_eq_right hpS, hp]
    have hcard := (card_le_card hsub).trans (card_union_le _ _)
    have hcard' : ((univ.filter fun p ↦ L.chi J p = a').card : ℝ) ≤
        (D.blow a G).classSize 3 c col + S.card := by exact_mod_cast hcard
    have hN : ((D.blow a G).1 : ℝ) = 9 * m ^ 2 * (2 * 4 ^ a) ^ 2 * G.1 := by
      change ((Fintype.card (D.Cell a) * G.1 : ℕ) : ℝ) = _
      rw [card_cells_total]; push_cast; ring
    rw [hN]
    have hn0 : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    set Γ : ℝ := (2 * 4 ^ a) ^ 2 with hΓdef
    have hΓ : (0 : ℝ) < Γ := by positivity
    have hout : (G.1 : ℝ) - I.card - J.card ≤ 2 * εB * G.1 := by linarith
    have hout0 : (0 : ℝ) ≤ G.1 - I.card - J.card := by
      rw [← card_outside hIJ]; positivity
    have hcov' : 2 * m * G.1 + 9 * m ^ 2 * (2 * εB * G.1) ≤ 9 * m ^ 2 * ε * G.1 := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have h2 : 2 / (9 * (m : ℝ)) * (9 * (m : ℝ) ^ 2) = 2 * m := by field_simp
      have : 2 * (m : ℝ) + 9 * m ^ 2 * (2 * εB) ≤ 9 * m ^ 2 * ε := by
        have h9 : (0 : ℝ) ≤ 9 * m ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hcov h9
        nlinarith
      nlinarith
    push_cast at hchi hS hcard'
    have hgS := mul_le_mul hW hout hout0 (by positivity)
    have hkey := mul_le_mul_of_nonneg_left hcov' hΓ.le
    nlinarith

/-- **No-instances**: at most `(7/9 + 2 γ' / 3) N` vertices of the blow-up are colored. -/
theorem no_bound {m a : ℕ} (G : Graph) {γB : ℝ} (hγ1 : γB ≤ 1 / 3)
    (hno : ∀ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) → (I.card : ℝ) < γB * G.1)
    (c : List ℕ) (hc : ((design m).blow a G).IsPartialColoring 3 c) :
    (((design m).blow a G).numColored 3 c : ℝ) ≤
      (7 / 9 + 2 / 3 * γB) * ((design m).blow a G).1 := by
  set D := design m
  have h0 := (D.template a).numColored_le G 3 c hc (γB * G.1) hno
  have h : ((D.blow a G).numColored 3 c : ℝ) ≤
      (univ.filter fun u ↦ (D.template a).W u u ≠ 1).card * G.1 +
        (univ.filter fun u ↦ (D.template a).W u u = 1).card * (3 * (γB * G.1)) := by
    push_cast at h0; exact h0
  set g := (univ.filter fun u ↦ (D.template a).W u u = 1).card with hgdef
  have hsplit : g + (univ.filter fun u ↦ (D.template a).W u u ≠ 1).card = (D.template a).C := by
    rw [hgdef, card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hg : g = (2 * 4 ^ a) ^ D.r * (univ.filter fun τ : Ty m ↦ W0 m τ τ = 1).card := by
    rw [hgdef, ← D.card_cells a (fun τ ↦ W0 m τ τ = 1)]
    refine congrArg card (Finset.filter_congr fun u _ ↦ ?_)
    simp only [Design.Wc, Design.typ, ite_true]
    exact Iff.rfl
  rw [show D.r = 2 from rfl] at hg
  have hreal := card_real_le m
  have hC : ((D.template a).C : ℝ) = 9 * m ^ 2 * (2 * 4 ^ a) ^ 2 := by
    exact_mod_cast card_cells_total m a
  have hN : ((D.blow a G).1 : ℝ) = 9 * m ^ 2 * (2 * 4 ^ a) ^ 2 * G.1 := by
    change ((Fintype.card (D.Cell a) * G.1 : ℕ) : ℝ) = _
    rw [card_cells_total]; push_cast; ring
  rw [hN]
  have hsplit' : (g : ℝ) + (univ.filter fun u ↦ (D.template a).W u u ≠ 1).card =
      9 * m ^ 2 * (2 * 4 ^ a) ^ 2 := by rw [← hC]; exact_mod_cast hsplit
  have hg' : (2 * m ^ 2 * (2 * 4 ^ a) ^ 2 : ℝ) ≤ g := by
    rw [hg]; push_cast
    have : (2 * m ^ 2 : ℝ) ≤ (univ.filter fun τ : Ty m ↦ W0 m τ τ = 1).card := by
      exact_mod_cast hreal
    nlinarith [pow_pos (show (0 : ℝ) < 2 * 4 ^ a by positivity) 2]
  have hn0 : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
  have h3 : 0 ≤ 1 - 3 * γB := by linarith
  have h4 := mul_le_mul_of_nonneg_right hg' (mul_nonneg hn0 h3)
  have h5 := congrArg (· * (G.1 : ℝ)) hsplit'
  simp only at h5
  nlinarith

end LowRank

/-- **Classes of the same size**: a partial `k`-coloring whose classes have at least `m` vertices
each gives one whose classes have exactly `m`, by uncoloring vertices. -/
theorem exists_equal_classes (H : Graph) {k : ℕ} {c : List ℕ} (hc : H.IsPartialColoring k c)
    {m : ℕ} (hm : ∀ a < k, m ≤ H.classSize k c a) :
    ∃ c', H.IsPartialColoring k c' ∧ (∀ a < k, H.classSize k c' a = m) ∧
      H.numColored k c' = k * m := by
  classical
  have hT : ∀ a, ∃ T : Finset (Fin H.1), T ⊆ univ.filter (H.color k c · = a) ∧
      (a < k → T.card = m) := by
    intro a
    by_cases ha : a < k
    · obtain ⟨T, hTs, hTc⟩ := exists_subset_card_eq (hm a ha)
      exact ⟨T, hTs, fun _ ↦ hTc⟩
    · exact ⟨∅, empty_subset _, fun h ↦ absurd h ha⟩
  choose T hTs hTc using hT
  set c' : List ℕ :=
    List.ofFn fun v : Fin H.1 ↦ if v ∈ T (H.color k c v) then H.color k c v else k
  have hcol : ∀ v, H.color k c' v = if v ∈ T (H.color k c v) then H.color k c v else k := by
    intro v
    unfold Graph.color
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [v.2, ↓reduceDIte, Option.getD_some, Fin.eta]
    rfl
  have hclass : ∀ a < k, univ.filter (H.color k c' · = a) = T a := by
    intro a ha
    ext v
    simp only [mem_filter, mem_univ, true_and, hcol]
    constructor
    · intro h
      by_cases hv : v ∈ T (H.color k c v)
      · rw [ite_eq_left hv] at h
        exact h ▸ hv
      · rw [ite_eq_right hv] at h
        omega
    · intro hv
      have hca : H.color k c v = a := (mem_filter.1 (hTs a hv)).2
      rw [hca, ite_eq_left hv]
  refine ⟨c', fun u v huv hu ↦ ?_, fun a ha ↦ ?_, ?_⟩
  · rw [hcol] at hu ⊢
    rw [hcol]
    by_cases hu' : u ∈ T (H.color k c u)
    · rw [ite_eq_left hu'] at hu ⊢
      by_cases hv' : v ∈ T (H.color k c v)
      · rw [ite_eq_left hv']
        exact hc u v huv hu
      · rw [ite_eq_right hv']
        exact hu.ne
    · rw [ite_eq_right hu'] at hu
      exact absurd hu (lt_irrefl k)
  · unfold Graph.classSize
    rw [hclass a ha, hTc a ha]
  · unfold Graph.numColored
    rw [card_eq_sum_card_fiberwise (f := fun v ↦ H.color k c' v) (t := range k)
      fun v hv ↦ mem_range.2 (mem_filter.1 hv).2]
    have hfib : ∀ a ∈ range k, ((univ.filter fun v ↦ H.color k c' v < k).filter
        fun v ↦ H.color k c' v = a).card = m := by
      intro a ha
      have ha' := mem_range.1 ha
      rw [filter_filter]
      have : (univ.filter fun v ↦ H.color k c' v < k ∧ H.color k c' v = a) =
          univ.filter (H.color k c' · = a) := by
        ext v
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨h ▸ ha', h⟩⟩
      rw [this, hclass a ha', hTc a ha']
    rw [sum_congr rfl hfib, sum_const, card_range, smul_eq_mul]

/-- **The spectral bound in terms of the output alone**: for the template of precision
`⌈log₂ n⌉`, the spectral threshold is at most `73 / 2^a ≤ 73 / n`, and the blow-up has at most
`576 m² n⁵` vertices. -/
theorem thr_le_rate {m : ℕ} (hm : 1 ≤ m) (G : Graph) (hn : 0 < G.1) :
    (2 * ((9 * m ^ 2 : ℕ) * err (Design.prec 0 G.1) 2 * G.1 + (2 * m + 2) * (1 * G.1) / 2) +
      0 * (Fintype.card ((LowRank.design m).Cell (Design.prec 0 G.1)) * G.1)) /
        ((8 * m ^ 2 * (4 ^ Design.prec 0 G.1) ^ 2 : ℕ) * G.1) ≤
      rate 73 (576 * m ^ 2) 5 ((LowRank.design m).redA 0 G).1 := by
  set a := Design.prec 0 G.1 with ha
  have ha' : a = Nat.clog 2 G.1 := by simp [ha, Design.prec]
  obtain ⟨hlo, hhi⟩ := pow_clog_bounds (n := G.1) hn
  rw [← ha'] at hlo hhi
  have h1 := LowRank.threshold_le (a := a) hm hn (Fintype.card ((LowRank.design m).Cell a) * G.1)
  have hn' : (0 : ℝ) < G.1 := by exact_mod_cast hn
  have hlo' : (G.1 : ℝ) ≤ 2 ^ a := by exact_mod_cast hlo
  have hhi' : (2 : ℝ) ^ a ≤ 2 * G.1 := by exact_mod_cast hhi.le
  have h2 : (73 : ℝ) / 2 ^ a ≤ 73 / G.1 := div_le_div_of_nonneg_left (by norm_num) hn' hlo'
  have hN : ((LowRank.design m).redA 0 G).1 = (LowRank.design m).nA 0 G.1 := Design.redA_fst _ _ _
  have hnT : (LowRank.design m).nT = 9 * m ^ 2 := LowRank.card_ty m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hNeq : ((LowRank.design m).nA 0 G.1 : ℝ) =
      (2 * (2 ^ a * 2 ^ a)) ^ 2 * (9 * m ^ 2) * G.1 := by
    simp only [Design.nA, Design.cells, Design.base, hnT, ← ha]
    push_cast
    rfl
  have hNpos : 0 < (LowRank.design m).nA 0 G.1 := by
    have : (0 : ℝ) < (LowRank.design m).nA 0 G.1 := by rw [hNeq]; positivity
    exact_mod_cast this
  have hNb : ((LowRank.design m).nA 0 G.1 : ℝ) ≤ 576 * m ^ 2 * (G.1 : ℝ) ^ 5 := by
    rw [hNeq]
    have hb : 2 * ((2 : ℝ) ^ a * 2 ^ a) ≤ 8 * (G.1 : ℝ) ^ 2 := by nlinarith
    have hb2 : (2 * ((2 : ℝ) ^ a * 2 ^ a)) ^ 2 ≤ 64 * (G.1 : ℝ) ^ 4 := by
      have h0 : (0 : ℝ) ≤ 2 * ((2 : ℝ) ^ a * 2 ^ a) := by positivity
      nlinarith
    have hc : (0 : ℝ) ≤ 9 * m ^ 2 * G.1 := by positivity
    nlinarith
  have h3 := div_le_rate (c := 73) (b := 576 * m ^ 2) (by norm_num) (e := 5) (by norm_num) hn
    hNpos hNb
  rw [hN]
  linarith

/-- Theorem 8.6 for `ε ≤ 2/9 - γ`, where a `(3, ε)`-coloring is a `(3, 2/9 - γ)`-coloring. -/
theorem threeColoring_lowRank_hardness_le (hUGC : UniqueGames.KhotUGC) {ε γ : ℝ} (hε : 0 < ε)
    (hγ : 0 < γ) (hεγ : ε ≤ 2 / 9 - γ) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
        (∃ c, G.IsColoring 3 ε c ∧ ∀ a < 3, G.classSize 3 c a = G.classSize 3 c 0) ∧
        G.numEigGT (f G.1) ≤ 2 ∧ (univ.filter fun i ↦ f G.1 < |G.eig i|).card ≤ 7) 3
          (2 / 9 - γ)) := by
  obtain ⟨ε₀, hε₀, hBK⟩ := bansalKhot hUGC
  set εB := min ε₀ (ε / 24) with hεB
  set γB := min (min ε₀ (γ / 4)) (1 / 4) with hγB
  have hεB0 : 0 < εB := lt_min hε₀ (by positivity)
  have hγB0 : 0 < γB := lt_min (lt_min hε₀ (by positivity)) (by norm_num)
  have hγBγ : γB ≤ γ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hγB1 : γB ≤ 1 / 3 := (min_le_right _ _).trans (by norm_num)
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 1 ≤ m ∧ 2 / (9 * (m : ℝ)) ≤ ε / 6 := by
    obtain ⟨m, hm⟩ := exists_nat_gt (4 / (3 * ε))
    refine ⟨m + 1, by omega, ?_⟩
    have hm' : (4 / (3 * ε) : ℝ) < m + 1 := by linarith
    rw [div_lt_iff₀ (by positivity)] at hm'
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hNP := hBK εB γB 1 hεB0 (min_le_left _ _) hγB0
    ((min_le_left _ _).trans (min_le_left _ _)) one_pos
  set D := LowRank.design m
  refine ⟨rate 73 (576 * m ^ 2) 5, tendsto_rate _ _ (by norm_num), ?_⟩
  refine npHard_of_reduction hεB0.le hγB0 zero_le_one hNP (D.redA 0) (D.redA_polytime 0)
    (fun G hG hn ↦ ?_) fun G hG ↦ ?_
  · obtain ⟨hdeg, I, J, hIJ, hI, hJ, hIc, hJc⟩ := hG
    set a := Design.prec 0 G.1
    have hcov : 2 / (9 * (m : ℝ)) + 2 * εB ≤ ε / 3 := by
      have : εB ≤ ε / 24 := min_le_right _ _
      linarith
    obtain ⟨c, hc, hcls⟩ := LowRank.yes_coloring (a := a) hm1 G hcov hIJ hI hJ hIc hJc
    obtain ⟨c', hc', hcls', hnum⟩ := exists_equal_classes (D.blow a G) hc
      (m := ⌈(1 / 3 - ε / 3) * ((D.blow a G).1 : ℝ)⌉₊) fun col hcol ↦
        Nat.ceil_le.2 (hcls col hcol)
    have hcol' : (D.blow a G).IsColoring 3 ε c' := by
      refine ⟨hc', ?_⟩
      rw [hnum, Nat.cast_mul 3, Nat.cast_ofNat]
      have := Nat.le_ceil ((1 / 3 - ε / 3) * ((D.blow a G).1 : ℝ))
      linarith
    have hspec := LowRank.spectral (a := a) hm1 G hn zero_le_one hdeg (thr_le_rate hm1 G hn)
    exact ⟨⟨⟨_, D.blow_isRegular a G⟩, ⟨c', hcol', fun col hcol ↦
      (hcls' col hcol).trans (hcls' 0 (by norm_num)).symm⟩, hspec.1, hspec.2⟩,
      ⟨c', isColoring_mono hcol' hεγ⟩⟩
  · have hn := pos_of_mem_no hγB0 hG
    obtain ⟨-, -, hno⟩ := hG
    have hC : 0 < Fintype.card (D.Cell (Design.prec 0 G.1)) := by
      rw [LowRank.card_cells_total]; positivity
    exact not_hasColoring_of_le (Nat.mul_pos hC hn) (q := 7 / 9 + 2 / 3 * γB) (by linarith)
      fun c hc ↦ LowRank.no_bound G hγB1 hno c hc

/-- **Theorem 1.6** of [BHSV25] (Theorem 8.6). -/
theorem threeColoring_lowRank_hardness (hUGC : UniqueGames.KhotUGC) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ γ : ℝ, 0 < γ → γ < 2 / 9 →
      ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
        PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
          (∃ c, G.IsColoring 3 ε c ∧ ∀ a < 3, G.classSize 3 c a = G.classSize 3 c 0) ∧
          G.numEigGT (f G.1) ≤ 2 ∧ (univ.filter fun i ↦ f G.1 < |G.eig i|).card ≤ R) 3
            (2 / 9 - γ)) := by
  intro ε hε
  refine ⟨7, fun γ hγ hγ2 ↦ ?_⟩
  have hle : min ε (2 / 9 - γ) ≤ ε := min_le_left _ _
  obtain ⟨f, hf, h⟩ := threeColoring_lowRank_hardness_le hUGC (lt_min hε (by linarith)) hγ
    (min_le_right _ _)
  refine ⟨f, hf, h.mono (fun G hG ↦ ⟨⟨hG.1.1, ?_, hG.1.2.2.1, hG.1.2.2.2⟩, hG.2⟩) fun _ h ↦ h⟩
  obtain ⟨c, hc, hcls⟩ := hG.1.2.1
  exact ⟨c, isColoring_mono hc hle, hcls⟩

end BHSV25.Hard
