module

public import ABBKS26.Tree.Tree

/-! Partition bookkeeping for accepted leaves. -/

@[expose] public section

namespace ABBKS26.Select.LearnAux

noncomputable section

open Common _root_.ABBKS26.Tree

variable {n k d : ℕ}

theorem singleton_partition (ω : Fin n → Triple k d) (w Φ : ℝ)
    (S : List (Finset (Fin n))) (hlen : S.length = k)
    (hS : GoodPartition ω w Φ S) :
    ∃ π : Equiv.Perm (Fin k), ∀ a : Fin k,
      leakage ω (S[a.val]'(hlen ▸ a.isLt)) {π a} ≤ Φ ∧
        w * n / 4 ≤ (S[a.val]'(hlen ▸ a.isLt)).card := by
  classical
  obtain ⟨_, I, hI, hd, _, hb⟩ := hS
  let ix (a : Fin k) : Fin S.length := ⟨a.val, hlen ▸ a.isLt⟩
  let f (a : Fin k) : Fin k := (hI (ix a)).choose
  have hf (a : Fin k) : f a ∈ I (ix a) := (hI (ix a)).choose_spec
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    have hi : ix a ≠ ix b := fun he ↦ hne (Fin.ext
      (congrArg (fun i : Fin S.length ↦ i.val) he))
    exact Finset.disjoint_left.mp (hd _ _ hi) (hf a) (hab ▸ hf b)
  let π : Equiv.Perm (Fin k) := Equiv.ofBijective f
    ((Finite.injective_iff_bijective).mp hinj)
  refine ⟨π, fun a ↦ ?_⟩
  have heq : I (ix a) = {π a} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hf a, ?_⟩
    intro j hj
    obtain ⟨b, rfl⟩ := π.surjective j
    by_cases hab : a = b
    · exact hab ▸ rfl
    · exact (Finset.disjoint_left.mp
        (hd _ _ (fun he ↦ hab (Fin.ext
          (congrArg (fun i : Fin S.length ↦ i.val) he)))) hj (hf b)).elim
  simpa only [heq, Fin.getElem_fin, ix] using hb (ix a)

theorem leakage_unique (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I J : Finset (Fin k))
    (hI : leakage ω N I ≤ leakageBudget params η h)
    (hJ : leakage ω N J ≤ leakageBudget params η h) : I = J := by
  classical
  let Φ := leakageBudget params η h
  have hΦ : 0 ≤ Φ := hp.leakageBudget_nonneg mode M ε w η Δ D ω r params h (by omega)
  obtain ⟨hM, _, _, hw, hwj, hε, hη, hη100, _, hg, _, _, hsize, _, _, hparams⟩ := hp
  obtain ⟨hweight, _, _, _, _, _, hs⟩ := hparams h (by omega)
  obtain ⟨_, hstraddle, _, _, _, _, hsmall, _⟩ := hs hh
  have hw1 : w ≤ 1 := by
    let j : Fin k := ⟨0, by omega⟩
    exact (hwj j).trans (hM.sum_w ▸ Finset.single_le_sum
      (fun i _ ↦ hM.nonneg_w i) (Finset.mem_univ j))
  have hn : (0 : ℝ) < n := by
    by_contra hn
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg n)
    norm_num [hn0] at hsize
  have hstraddle' : (0 : ℝ) < (params h).straddle := by exact_mod_cast hstraddle
  rw [hweight] at hsmall
  have hΦsmall : Φ ≤ 1 / 4 := by
    change Φ + _ + _ + _ + _ < _ at hsmall
    linarith
  have hbadsmall : ε + η ≤ w / 4 := by
    change Φ + _ + _ + _ + _ < _ at hsmall
    linarith
  have hc := (good_counts M ε w η D ω hg ⟨hη.le, hη100⟩).1
  have hbad := hg.2.1
  have hbad' : ((corrupted ω).card : ℝ) ≤ w * n / 4 := by
    exact hbad.trans (by nlinarith [mul_le_mul_of_nonneg_right hbadsmall hn.le])
  have hmem (I J : Finset (Fin k)) (hI : leakage ω N I ≤ Φ)
      (hJ : leakage ω N J ≤ Φ) (j : Fin k) (hi : j ∈ I) : j ∈ J := by
    by_contra hj
    have hleft := SoundAux.leakage_component ω N I Φ hI j
    have hright := SoundAux.leakage_component ω N J Φ hJ j
    simp only [hi, hj, ite_true, ite_false] at hleft hright
    have hcard : (cluster (labels ω) j).card ≤
        ((cluster (labels ω) j \ corrupted ω) \ N).card +
          ((cluster (labels ω) j \ corrupted ω) ∩ N).card + (corrupted ω).card := by
      have he := Finset.card_sdiff_add_card_inter
        (cluster (labels ω) j \ corrupted ω) N
      have hb := Finset.card_le_card (show cluster (labels ω) j ⊆
          corrupted ω ∪ (cluster (labels ω) j \ corrupted ω) by
        intro l hl
        by_cases hb : l ∈ corrupted ω <;> simp [hl, hb])
      have hu := Finset.card_union_le (corrupted ω)
        (cluster (labels ω) j \ corrupted ω)
      omega
    have hcard' : ((cluster (labels ω) j).card : ℝ) ≤
        (((cluster (labels ω) j \ corrupted ω) \ N).card : ℝ) +
          ((cluster (labels ω) j \ corrupted ω) ∩ N).card + (corrupted ω).card := by
      exact_mod_cast hcard
    have hmul := mul_le_mul_of_nonneg_right hΦsmall
      (Nat.cast_nonneg (α := ℝ) (cluster (labels ω) j).card)
    have hcount : (0.9 : ℝ) * w * n ≤ (cluster (labels ω) j).card :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hwj j)
        (by norm_num : (0 : ℝ) ≤ 0.9)) hn.le).trans (hc j).1
    nlinarith only [hleft, hright, hcard', hmul, hbad', hcount, mul_pos hw hn]
  exact Finset.ext fun j ↦ ⟨hmem I J hI hJ j, hmem J I hJ hI j⟩

private theorem replace_lengths (x : Fin n → Fin d → ℚ) (C : Candidate n d)
    (j : Fin C.blocks.length) (e : Edge n d) :
    (replaceBlock x C j e).blocks.length = C.blocks.length + 1 ∧
      (replaceBlock x C j e).path.length = C.path.length + 1 := by
  dsimp only [replaceBlock]
  simp only [List.length_append, List.length_take, List.length_cons,
    List.length_nil, List.length_drop]
  have hj := j.isLt
  constructor
  · omega
  · trivial

private theorem levels_shape (ref : Refiner) (href : RefineSpec ref) (mode : Mode)
    (params : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (C : Candidate n d) (hC : C ∈ levels ref mode k params x fuel h) :
    C.blocks.length = h + 1 ∧ C.path.length = h ∧ ∀ e ∈ C.path, e.depth < h := by
  induction h generalizing C with
  | zero =>
    obtain rfl := List.mem_singleton.mp hC
    simp [root]
  | succ h ih =>
    obtain ⟨P, hP, hC⟩ := List.mem_flatMap.mp hC
    split_ifs at hC
    · obtain ⟨hb, hp, hd⟩ := ih P hP
      obtain ⟨j, e, _, he, rfl⟩ := (href mode k params x fuel P).2.1 C hC
      obtain ⟨hb', hp'⟩ := replace_lengths x P j e
      refine ⟨by omega, by omega, ?_⟩
      intro e' he'
      rcases List.mem_append.mp he' with he' | he'
      · exact (hd e' he').trans_le (by omega)
      · obtain rfl := List.mem_singleton.mp he'
        omega
    · simp at hC

private theorem root_good (M : Mixture k d) (w : ℝ) (ω : Fin n → Triple k d)
    (hM : M.Valid) (hw : ∀ j, w ≤ M.w j) (hk : 0 < k) :
    GoodPartition ω w 0 (root n d).blocks := by
  classical
  have hw1 : w ≤ 1 := by
    exact (hw ⟨0, hk⟩).trans (hM.sum_w ▸ Finset.single_le_sum
      (fun j _ ↦ hM.nonneg_w j) (Finset.mem_univ _))
  have hsize : w * n / 4 ≤ (n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hw1 (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hm, Nat.cast_nonneg (α := ℝ) n]
  have hleak : leakage ω Finset.univ Finset.univ ≤ 0 := by
    apply (SoundAux.foldl_max_le_iff _ 0 0).mpr
    refine ⟨le_rfl, ?_⟩
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    change (if j ∈ (Finset.univ : Finset (Fin k)) then _ else _) ≤ 0
    simp only [Finset.mem_univ, ite_true]
    rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)]
    simp
  apply (RefineAux.goodPartition_iff ω w 0 _).mpr
  refine ⟨by simp [root], by simp [root], [Finset.univ], by simp, by simp, ?_⟩
  exact List.Forall₂.cons
    ⟨⟨⟨0, hk⟩, Finset.mem_univ _⟩, hleak, by simpa using hsize⟩ List.Forall₂.nil

private theorem accepted_level_good
    (ref : Refiner) (href : RefineSpec ref) (mode : Mode) (M : Mixture k d)
    (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d) (r : Rounding k d)
    (params : ℕ → StepParams) (fuel : ℕ) (hk : 2 ≤ k)
    (hp : Prepared mode M ε w η Δ D ω r params)
    (hf : localBudget mode k n d params ≤ fuel) (h : ℕ) (hh : h ≤ k - 1)
    (C : Candidate n d)
    (hC : C ∈ levels ref mode k params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel h)
    (ha : Accepted params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) C) :
    GoodPartition ω w (leakageBudget params η h) C.blocks := by
  let x : Fin n → Fin d → ℚ := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  induction h generalizing C with
  | zero =>
    obtain rfl := List.mem_singleton.mp hC
    obtain ⟨hM, _, _, _, hw, _⟩ := hp
    simpa [leakageBudget] using root_good M w ω hM hw (by omega)
  | succ h ih =>
    obtain ⟨P, hP, hC⟩ := List.mem_flatMap.mp hC
    split_ifs at hC with hlt
    · obtain ⟨j, e, he, hd, rfl⟩ := (href mode k params x fuel P).2.1 C hC
      have haP : Accepted params x P := fun e' he' ↦
        ha e' (List.mem_append_left _ he')
      have hg := ih (by omega) P hP haP
      obtain ⟨hb, hpath, hdepths⟩ := levels_shape ref href mode params x fuel h P hP
      have hnew : e ∉ P.path := by
        intro he'
        have := hdepths e he'
        omega
      have hgood : GoodPartition ω w (leakageBudget params η P.path.length) P.blocks := by
        rwa [hpath]
      have hprov := ((href mode k params x fuel P).2.2 M ε w η Δ D ω r rfl hp hf
        hlt (by omega) hgood).1 (replaceBlock x P j e) hC e
          (List.mem_append_right _ (List.mem_singleton_self e)) hnew
      obtain ⟨J, _, hJ, hs⟩ := hprov
      obtain ⟨hS, I, hI, hdis, hcover, hbound⟩ := hgood
      have hleak : leakage ω e.parent (I j) ≤ leakageBudget params η h := by
        rw [he, ← hpath]
        exact (hbound j).1
      have hIJ := leakage_unique mode M ε w η Δ D ω r params hp h (by omega)
        e.parent (I j) J hleak (by simpa only [hpath] using hJ)
      have hs' : ScaleValid M (I j) (params P.path.length) e := by
        simpa only [← hIJ, hd] using hs
      have hv : Verify (params P.path.length) x e := by
        rw [← hd]
        exact ha e (List.mem_append_right _ (List.mem_singleton_self e))
      have hsplit := hp.replace_goodPartition mode M ε w η Δ D ω r params P (by omega)
        I hS hI hdis hcover hbound j e he hs' hv
      simpa only [hpath] using hsplit
    · simp at hC

theorem accepted_leaf_good
    (ref : Refiner) (href : RefineSpec ref) (mode : Mode) (M : Mixture k d)
    (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d) (r : Rounding k d)
    (params : ℕ → StepParams) (fuel : ℕ) (hk : 2 ≤ k)
    (hp : Prepared mode M ε w η Δ D ω r params)
    (hf : localBudget mode k n d params ≤ fuel) (C : Candidate n d)
    (hC : C ∈ leaves ref mode k params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel)
    (ha : Accepted params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) C) :
    GoodPartition ω w (leakageBudget params η (k - 1)) C.blocks := by
  exact accepted_level_good ref href mode M ε w η Δ D ω r params fuel hk hp hf
    (k - 1) le_rfl C (List.mem_filter.mp hC).1 ha

end

end ABBKS26.Select.LearnAux
