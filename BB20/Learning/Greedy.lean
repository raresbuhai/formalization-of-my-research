module

public import BB20.Learning.Progress
public import BB20.Learning.Link

/-!
# The greedy phase

* Combinatorics of `BB20.candList`, `BB20.grow` and `BB20.greedy`: candidates are nonempty sets
  of at most `k` numbers below `n` outside `S ∪ {u}`, every such set is a candidate (as a sorted
  list), and after `n` steps no candidate is above the threshold
  (`BB20.Learning.greedy_fixed`), since each step that adds something adds a new number.
* `BB20.Learning.greedy_spec`: if the empirical proxy is accurate to `τ/2` on sets of size at
  most `L = 2^s · 8/τ²` and the threshold is in `[0.9τ, τ]`, then the final set `S` has at most
  `L` elements and `ν_{u,I|S} ≤ 1.5 τ` for every candidate `I`. Each addition has
  `ν > 0.4 τ` and so raises the potential `Ψ = E[m_S²] ∈ [0, 1]` by more than `0.64 τ²`
  (`BB20.Learning.psi_union_ge`), so there are fewer than `1/(0.64 τ²)` additions, each of at
  most `2^s` variables.
-/

@[expose] public section

namespace BB20.Learning

open Finset

/-! ### Candidates -/

theorem mem_candList {n u k : ℕ} {S : Finset ℕ} {l : List ℕ} :
    l ∈ candList n u k S ↔
      l.Sublist ((List.range n).filter fun i ↦ i ≠ u ∧ i ∉ S) ∧ l ≠ [] ∧ l.length ≤ k := by
  simp [candList, List.mem_filter, List.mem_sublists]

theorem cand_props {n u k : ℕ} {S : Finset ℕ} {l : List ℕ} (hl : l ∈ candList n u k S) :
    l.toFinset.Nonempty ∧ l.toFinset.card ≤ k ∧ ∀ i ∈ l.toFinset, i < n ∧ i ≠ u ∧ i ∉ S := by
  obtain ⟨hsub, hne, hk⟩ := mem_candList.1 hl
  have hnd : l.Nodup := hsub.nodup (List.nodup_range.filter _)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l hne
    exact ⟨a, List.mem_toFinset.2 ha⟩
  · rw [List.toFinset_card_of_nodup hnd]
    exact hk
  · intro i hi
    have := hsub.subset (List.mem_toFinset.1 hi)
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at this
    exact ⟨this.1, this.2.1, this.2.2⟩

theorem sort_mem_candList {n u k : ℕ} {S I : Finset ℕ} (hne : I.Nonempty) (hk : I.card ≤ k)
    (hI : ∀ i ∈ I, i < n ∧ i ≠ u ∧ i ∉ S) : I.sort (· ≤ ·) ∈ candList n u k S := by
  rw [mem_candList]
  refine ⟨?_, ?_, ?_⟩
  · refine List.sublist_of_subperm_of_pairwise (r := (· ≤ ·)) ?_ (pairwise_sort _ _) ?_
    · refine List.subperm_of_subset (sort_nodup _ _) fun i hi ↦ ?_
      have := hI i ((mem_sort _).1 hi)
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨this.1, this.2.1, this.2.2⟩
    · exact (List.pairwise_lt_range.imp le_of_lt).filter _
  · intro h
    obtain ⟨a, ha⟩ := hne
    have : a ∈ I.sort (· ≤ ·) := (mem_sort _).2 ha
    rw [h] at this
    exact List.not_mem_nil this
  · rw [length_sort]
    exact hk

/-! ### Greedy steps -/

section Steps

variable (nh : Finset ℕ → Finset ℕ → ℚ) (n u k : ℕ) (t : ℚ)

theorem grow_cases (S : Finset ℕ) :
    (grow nh n u k t S = S ∧ ∀ l ∈ candList n u k S, ¬ t < nh l.toFinset S) ∨
      ∃ l ∈ candList n u k S, t < nh l.toFinset S ∧ grow nh n u k t S = S ∪ l.toFinset := by
  unfold grow
  rcases h : (candList n u k S).find? (fun l ↦ decide (t < nh l.toFinset S)) with _ | l
  · left
    simp only [h]
    refine ⟨trivial, fun l hl ↦ ?_⟩
    have := List.find?_eq_none.1 h l hl
    simpa using this
  · right
    simp only [h]
    exact ⟨l, List.mem_of_find?_eq_some h, by simpa using List.find?_some h, rfl⟩

theorem iterate_grow_induction (P : Finset ℕ → Prop) (h0 : P ∅)
    (hstep : ∀ S, P S → ∀ l ∈ candList n u k S, t < nh l.toFinset S → P (S ∪ l.toFinset))
    (j : ℕ) : P ((grow nh n u k t)^[j] ∅) := by
  induction j with
  | zero => exact h0
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases grow_cases nh n u k t ((grow nh n u k t)^[j] ∅) with ⟨h, _⟩ | ⟨l, hl, ht, h⟩
    · rw [h]
      exact ih
    · rw [h]
      exact hstep _ ih l hl ht

theorem greedy_induction (P : Finset ℕ → Prop) (h0 : P ∅)
    (hstep : ∀ S, P S → ∀ l ∈ candList n u k S, t < nh l.toFinset S → P (S ∪ l.toFinset)) :
    P (greedy nh n u k t) :=
  iterate_grow_induction nh n u k t P h0 hstep n

theorem greedy_subset : ∀ i ∈ greedy nh n u k t, i < n ∧ i ≠ u := by
  refine greedy_induction nh n u k t (fun S ↦ ∀ i ∈ S, i < n ∧ i ≠ u) (by simp) ?_
  intro S hS l hl _ i hi
  rcases mem_union.1 hi with h | h
  · exact hS i h
  · have := (cand_props hl).2.2 i h
    exact ⟨this.1, this.2.1⟩

/-- After `n` steps, no candidate is above the threshold. -/
theorem greedy_fixed (hu : u < n) :
    ∀ l ∈ candList n u k (greedy nh n u k t), ¬ t < nh l.toFinset (greedy nh n u k t) := by
  have hsub : ∀ j, ∀ i ∈ (grow nh n u k t)^[j] ∅, i < n ∧ i ≠ u := by
    intro j
    refine iterate_grow_induction nh n u k t (fun S ↦ ∀ i ∈ S, i < n ∧ i ≠ u) (by simp) ?_ j
    intro S hS l hl _ i hi
    rcases mem_union.1 hi with h | h
    · exact hS i h
    · have := (cand_props hl).2.2 i h
      exact ⟨this.1, this.2.1⟩
  have key : ∀ j, (∀ l ∈ candList n u k ((grow nh n u k t)^[j] ∅),
      ¬ t < nh l.toFinset ((grow nh n u k t)^[j] ∅)) ∨ j ≤ ((grow nh n u k t)^[j] ∅).card := by
    intro j
    induction j with
    | zero => right; simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      rcases grow_cases nh n u k t ((grow nh n u k t)^[j] ∅) with ⟨h, hno⟩ | ⟨l, hl, ht, h⟩
      · left
        rw [h]
        exact hno
      · right
        rw [h]
        rcases ih with hno | hle
        · exact absurd ht (hno l hl)
        · obtain ⟨⟨a, ha⟩, -, hl'⟩ := cand_props hl
          have haS : a ∉ (grow nh n u k t)^[j] ∅ := (hl' a ha).2.2
          have : ((grow nh n u k t)^[j] ∅).card < ((grow nh n u k t)^[j] ∅ ∪ l.toFinset).card :=
            card_lt_card ⟨subset_union_left, fun h ↦ haS (h (mem_union_right _ ha))⟩
          omega
  rcases key n with h | h
  · exact h
  · exfalso
    have hss : (grow nh n u k t)^[n] ∅ ⊆ (range n).erase u := fun i hi ↦
      mem_erase.2 ⟨(hsub n i hi).2, mem_range.2 (hsub n i hi).1⟩
    have := card_le_card hss
    rw [card_erase_of_mem (mem_range.2 hu), card_range] at this
    omega

end Steps

/-! ### The analysis of the greedy phase -/

variable {n m : ℕ}

/-- **The greedy phase.** If the empirical proxy is accurate to `τ/2` on sets of size at most
`L = 2^s · 8/τ²` and the threshold lies in `[0.9τ, τ]`, then the final set `S` has at most `L`
elements and `ν_{u,I|S} ≤ 1.5 τ` for every `I` of at most `2^s` variables outside `S ∪ {u}`. -/
theorem greedy_spec (R : RBM n m) (u : Fin n) (nh : Finset ℕ → Finset ℕ → ℚ) (s : ℕ) (t : ℚ)
    {τ : ℝ} (hτ : 0 < τ) (ht1 : 9 / 10 * τ ≤ t) (ht2 : (t : ℝ) ≤ τ)
    (hacc : Accurate R u nh (2 ^ s) (2 ^ s * 8 / τ ^ 2) (τ / 2)) :
    ∃ S : Finset (Fin n), S.map Fin.valEmbedding = greedy nh n u (2 ^ s) t ∧ u ∉ S ∧
      (S.card : ℝ) ≤ 2 ^ s * 8 / τ ^ 2 ∧
      ∀ I : Finset (Fin n), u ∉ I → Disjoint I S → I.card ≤ 2 ^ s → R.nu u I S ≤ 3 / 2 * τ := by
  set L : ℝ := 2 ^ s * 8 / τ ^ 2 with hL
  set c : ℝ := 16 / 25 * τ ^ 2 with hc
  have hc0 : 0 < c := by positivity
  -- the invariant
  set P : Finset ℕ → Prop := fun S ↦ ∃ S' : Finset (Fin n), S'.map Fin.valEmbedding = S ∧
    u ∉ S' ∧ ∃ j : ℕ, S'.card ≤ 2 ^ s * j ∧ (j : ℝ) * c ≤ psi R u S' with hP
  have hcardL : ∀ S' : Finset (Fin n), ∀ j : ℕ, S'.card ≤ 2 ^ s * j → (j : ℝ) * c ≤ psi R u S' →
      (S'.card : ℝ) ≤ L := by
    intro S' j h1 h2
    have hj : (j : ℝ) ≤ 25 / (16 * τ ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have := psi_le_one R u S'
      nlinarith
    calc (S'.card : ℝ) ≤ 2 ^ s * j := by exact_mod_cast h1
      _ ≤ 2 ^ s * (25 / (16 * τ ^ 2)) := by gcongr
      _ ≤ 2 ^ s * (8 / τ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg τ]
      _ = L := by rw [hL]; ring
  have hstep : ∀ S, P S → ∀ l ∈ candList n (u : ℕ) (2 ^ s) S, t < nh l.toFinset S →
      P (S ∪ l.toFinset) := by
    rintro S ⟨S', rfl, huS', j, hj1, hj2⟩ l hl ht
    obtain ⟨-, hlk, hlp⟩ := cand_props hl
    set I' := toFin n l.toFinset with hI'
    have hlI : I'.map Fin.valEmbedding = l.toFinset := map_toFin fun a ha ↦ (hlp a ha).1
    have huI : u ∉ I' := fun h ↦ (hlp u (mem_toFin.1 h)).2.1 rfl
    have hdisj : Disjoint I' S' := by
      rw [disjoint_left]
      intro a ha haS
      exact (hlp a (mem_toFin.1 ha)).2.2 (mem_map_of_mem _ haS)
    have hcardI : I'.card ≤ 2 ^ s := by
      rw [← card_map Fin.valEmbedding, hlI]
      exact hlk
    have hacc' := hacc I' S' huI huS' hdisj hcardI (hcardL S' j hj1 hj2)
    rw [hlI] at hacc'
    have hν : 2 / 5 * τ < R.nu u I' S' := by
      have := (abs_le.1 hacc').2
      have ht' : (9 / 10 * τ : ℝ) < nh l.toFinset (S'.map Fin.valEmbedding) :=
        lt_of_le_of_lt ht1 (by exact_mod_cast ht)
      linarith
    have hψ := psi_union_ge R u hdisj
    refine ⟨S' ∪ I', by rw [map_union, hlI], ?_, j + 1, ?_, ?_⟩
    · simp only [mem_union, not_or]
      exact ⟨huS', huI⟩
    · calc (S' ∪ I').card ≤ S'.card + I'.card := card_union_le _ _
        _ ≤ 2 ^ s * j + 2 ^ s := by omega
        _ = 2 ^ s * (j + 1) := by ring
    · rw [union_comm]
      have h4 : c ≤ 4 * R.nu u I' S' ^ 2 := by
        rw [hc]
        nlinarith
      push_cast
      linarith
  have hP0 : P ∅ := ⟨∅, by simp, by simp, 0, by simp, by simp [psi_nonneg]⟩
  obtain ⟨S', hS', huS', j, hj1, hj2⟩ :=
    greedy_induction nh n u (2 ^ s) t P hP0 hstep
  have hSL := hcardL S' j hj1 hj2
  refine ⟨S', hS', huS', hSL, fun I huI hdisj hcard ↦ ?_⟩
  rcases I.eq_empty_or_nonempty with rfl | hne
  · rw [nu_empty]
    positivity
  have hfix := greedy_fixed nh n u (2 ^ s) t u.2
  rw [← hS'] at hfix
  have hmem : (I.map Fin.valEmbedding).sort (· ≤ ·) ∈
      candList n u (2 ^ s) (S'.map Fin.valEmbedding) := by
    refine sort_mem_candList (hne.map) (by rw [card_map]; exact hcard) fun i hi ↦ ?_
    obtain ⟨a, ha, rfl⟩ := mem_map.1 hi
    refine ⟨a.2, fun h ↦ huI (Fin.ext h ▸ ha), fun h ↦ ?_⟩
    obtain ⟨b, hb, hba⟩ := mem_map.1 h
    have : b = a := Fin.ext hba
    exact disjoint_left.1 hdisj ha (this ▸ hb)
  have hle := hfix _ hmem
  rw [sort_toFinset] at hle
  have hacc' := hacc I S' huI huS' hdisj hcard hSL
  have hle' : (nh (I.map Fin.valEmbedding) (S'.map Fin.valEmbedding) : ℝ) ≤ t := by
    exact_mod_cast not_lt.1 hle
  have := (abs_le.1 hacc').1
  linarith

end BB20.Learning
