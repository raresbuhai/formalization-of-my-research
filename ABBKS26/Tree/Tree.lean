module

public import ABBKS26.Tree.RefineBlocksAuxSpectral
public import ABBKS26.Tree.RefineBlocksAuxGrid
public import ABBKS26.Tree.RefineBlocksAuxBudget

/-!
# The refinement tree

The tree of partial clusterings of [ABBKS26, Algorithms 2 and 4]: every node is refined by
all candidate splits, the size is bounded at every level ([ABBKS26, Lemmas 5.26 and 6.17]),
and on the good event some path of good partial clusterings reaches a leaf ([ABBKS26,
Lemmas 5.27 and 6.18]). The tree is not pruned; selection happens at the end.
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section


open Matrix

open Common
open scoped BigOperators
variable {n k d : ℕ}

def levels (ref : Refiner) (mode : Mode) (k : ℕ) (params : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel : ℕ) : ℕ → List (Candidate n d)
  | 0 => [root n d]
  | h + 1 => (levels ref mode k params x fuel h).flatMap fun C ↦
      if C.blocks.length < k then ref mode k params x fuel C else []

def leaves (ref : Refiner) (mode : Mode) (k : ℕ) (params : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel : ℕ) : List (Candidate n d) :=
  (levels ref mode k params x fuel (k - 1)).filter (fun C ↦ C.blocks.length = k)

def treeCap (mode : Mode) (k : ℕ) (params : ℕ → StepParams) : ℕ :=
  (branchCap mode k params + 1) ^ k


private theorem replaceBlock_lengths (x : Fin n → Fin d → ℚ) (C : Candidate n d)
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

private theorem replays_root (x : Fin n → Fin d → ℚ) : Replays x (root n d) := by
  refine ⟨fun _ ↦ root n d, rfl, rfl, ?_⟩
  intro h
  exact Fin.elim0 h

private theorem replays_replaceBlock (x : Fin n → Fin d → ℚ) (C : Candidate n d)
    (hC : Replays x C) (j : Fin C.blocks.length) (e : Edge n d)
    (he : e.parent = C.blocks[j]) (hd : e.depth = C.path.length) :
    Replays x (replaceBlock x C j e) := by
  obtain ⟨states, hzero, hlast, hsteps⟩ := hC
  change ∃ next : Fin ((C.path ++ [e]).length + 1) → Candidate n d,
    next 0 = root n d ∧
      next (Fin.last (C.path ++ [e]).length) = replaceBlock x C j e ∧
      ∀ h : Fin (C.path ++ [e]).length,
        ∃ a : Fin (next h.castSucc).blocks.length,
          ((C.path ++ [e])[h.val]'h.isLt).parent =
              (next h.castSucc).blocks[a.val]'a.isLt ∧
            ((C.path ++ [e])[h.val]'h.isLt).depth = h.val ∧
            next h.succ = replaceBlock x (next h.castSucc) a
              ((C.path ++ [e])[h.val]'h.isLt)
  let states' (i : Fin ((C.path ++ [e]).length + 1)) : Candidate n d :=
    if hi : i.val < C.path.length + 1 then states ⟨i.val, hi⟩ else replaceBlock x C j e
  refine ⟨states', ?_, ?_, ?_⟩
  · have hlt : (0 : Fin ((C.path ++ [e]).length + 1)).val < C.path.length + 1 := by
      change 0 < C.path.length + 1
      omega
    dsimp only [states']
    rw [dite_eq_left hlt]
    exact hzero
  · simp [states', replaceBlock]
  · intro h
    by_cases hi : h.val < C.path.length
    · let i : Fin C.path.length := ⟨h.val, hi⟩
      have hbefore : states' h.castSucc = states i.castSucc := by
        have hlt : h.castSucc.val < C.path.length + 1 := by
          change h.val < C.path.length + 1
          omega
        dsimp only [states']
        rw [dite_eq_left hlt]
        rfl
      have hafter : states' h.succ = states i.succ := by
        have hlt : h.succ.val < C.path.length + 1 := by
          change h.val + 1 < C.path.length + 1
          omega
        dsimp only [states']
        rw [dite_eq_left hlt]
        rfl
      have hpath : (C.path ++ [e])[h.val]'h.isLt = C.path[i.val]'i.isLt :=
        List.getElem_append_left hi
      rw [hbefore, hafter, hpath]
      exact hsteps i
    · have hv : h.val = C.path.length := by
        have hh := h.isLt
        change h.val < (C.path ++ [e]).length at hh
        simp only [List.length_append, List.length_singleton] at hh
        omega
      have hbefore : states' h.castSucc = C := by
        have hlt : h.castSucc.val < C.path.length + 1 := by
          change h.val < C.path.length + 1
          omega
        dsimp only [states']
        rw [dite_eq_left hlt]
        exact (congrArg states (Fin.ext hv)).trans hlast
      have hafter : states' h.succ = replaceBlock x C j e := by
        have hlt : ¬ h.succ.val < C.path.length + 1 := by
          change ¬ h.val + 1 < C.path.length + 1
          omega
        dsimp only [states']
        rw [dite_eq_right hlt]
      have hpath : (C.path ++ [e])[h.val]'h.isLt = e := by
        rw [List.getElem_append_right (by omega)]
        simp [hv]
      rw [hbefore, hafter, hpath]
      exact ⟨j, he, hd.trans hv.symm, rfl⟩

private theorem levels_history
    (ref : Refiner) (href : RefineSpec ref) (mode : Mode) (k : ℕ)
    (params : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (C : Candidate n d) (hC : C ∈ levels ref mode k params x fuel h) :
    C.blocks.length = h + 1 ∧ Replays x C ∧ C.path.length = h := by
  induction h generalizing C with
  | zero =>
    obtain rfl := List.mem_singleton.mp hC
    exact ⟨rfl, replays_root x, rfl⟩
  | succ h ih =>
    obtain ⟨P, hP, hC⟩ := List.mem_flatMap.mp hC
    split_ifs at hC with hlt
    · obtain ⟨hb, hr, hp⟩ := ih P hP
      obtain ⟨j, e, he, hd, rfl⟩ := (href mode k params x fuel P).2.1 C hC
      obtain ⟨hb', hp'⟩ := replaceBlock_lengths x P j e
      exact ⟨by omega, replays_replaceBlock x P hr j e he hd, by omega⟩
    · simp at hC

/-- Every returned leaf has k blocks and a replayable unfiltered history. -/
theorem leaf_history
    (ref : Refiner) (href : RefineSpec ref) (mode : Mode) (k : ℕ)
    (params : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel : ℕ)
    (C : Candidate n d) (hC : C ∈ leaves ref mode k params x fuel) :
    C.blocks.length = k ∧ Replays x C ∧ C.path.length = k - 1 := by
  obtain ⟨hlevel, hblocks⟩ := List.mem_filter.mp hC
  exact ⟨by simpa using hblocks,
    (levels_history ref href mode k params x fuel (k - 1) C hlevel).2⟩

private theorem root_goodPartition
    (M : Mixture k d) (w : ℝ) (ω : Fin n → Triple k d)
    (hM : M.Valid) (hw : ∀ j, w ≤ M.w j) (hk : 0 < k) :
    GoodPartition ω w 0 (root n d).blocks := by
  classical
  have hw1 : w ≤ 1 := by
    apply (hw ⟨0, hk⟩).trans
    rw [← hM.sum_w]
    exact Finset.single_le_sum (fun j _ ↦ hM.nonneg_w j) (Finset.mem_univ _)
  have hsize : w * n / 4 ≤ (n : ℝ) := by
    have hm := mul_le_mul_of_nonneg_right hw1 (Nat.cast_nonneg (α := ℝ) n)
    nlinarith only [hm, Nat.cast_nonneg (α := ℝ) n]
  have hleak : leakage ω Finset.univ Finset.univ = 0 := by
    have hz (s : List ℝ) (hs : ∀ a ∈ s, a = 0) : s.foldl max 0 = 0 := by
      induction s with
      | nil => rfl
      | cons a s ih =>
        rw [List.foldl_cons, hs a (by simp), max_self]
        exact ih (fun b hb ↦ hs b (by simp [hb]))
    apply hz
    intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    simp
  apply (RefineAux.goodPartition_iff ω w 0 _).mpr
  refine ⟨by simp [root], by simp [root], [Finset.univ], by simp, by simp, ?_⟩
  exact List.Forall₂.cons
    ⟨⟨⟨0, hk⟩, Finset.mem_univ _⟩, hleak.le, by simpa using hsize⟩ List.Forall₂.nil

/-- A prepared good sample has an accepted root-to-leaf path. -/
theorem good_path
    (ref : Refiner) (href : RefineSpec ref) (mode : Mode) (M : Mixture k d)
    (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d) (r : Rounding k d)
    (params : ℕ → StepParams) (fuel : ℕ) (hk : 2 ≤ k)
    (hp : Prepared mode M ε w η Δ D ω r params)
    (hf : localBudget mode k n d params ≤ fuel) :
    ∃ C ∈ leaves ref mode k params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel,
      Accepted params (fun l i ↦ r ((ω l).1, (ω l).2.2) i) C ∧
      GoodPartition ω w (leakageBudget params η (k - 1)) C.blocks := by
  let x : Fin n → Fin d → ℚ := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  have hgood : ∀ h, h ≤ k - 1 → ∃ C ∈ levels ref mode k params x fuel h,
      Accepted params x C ∧ GoodPartition ω w (leakageBudget params η h) C.blocks := by
    intro h
    induction h with
    | zero =>
      intro _
      refine ⟨root n d, by simp [levels], ?_, ?_⟩
      · simp [Accepted, root]
      · obtain ⟨hM, _, _, _, hw, _⟩ := hp
        simpa only [leakageBudget, List.range_zero, List.map_nil, List.sum_nil] using
          root_goodPartition M w ω hM hw (by omega)
    | succ h ih =>
      intro hh
      obtain ⟨C, hC, ha, hg⟩ := ih (by omega)
      obtain ⟨hb, _, hd⟩ := levels_history ref href mode k params x fuel h C hC
      have hlt : C.blocks.length < k := by omega
      have hdepth : C.path.length + 1 = C.blocks.length := by omega
      obtain ⟨_, C', hC', hg', hv⟩ := (href mode k params x fuel C).2.2
        M ε w η Δ D ω r rfl hp hf hlt hdepth (by simpa only [hd] using hg)
      refine ⟨C', List.mem_flatMap.mpr ⟨C, hC, ?_⟩, ?_, ?_⟩
      · simpa only [ite_eq_left hlt] using hC'
      · intro e he
        by_cases heC : e ∈ C.path
        · exact ha e heC
        · exact hv e he heC
      · simpa only [hd] using hg'
  obtain ⟨C, hC, ha, hg⟩ := hgood (k - 1) le_rfl
  have hb := (levels_history ref href mode k params x fuel (k - 1) C hC).1
  refine ⟨C, List.mem_filter.mpr ⟨hC, ?_⟩, ha, hg⟩
  simpa only [decide_eq_true_eq] using (show C.blocks.length = k by omega)

end

end ABBKS26.Tree
