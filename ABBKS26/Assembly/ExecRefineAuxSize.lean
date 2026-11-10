module

public import ABBKS26.Assembly.ExecRefineAuxKernel

/-! Storage bounds for entire unfiltered levels, including persistent parents and paths. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM

private theorem index_size {n : ℕ} (N : Finset (Fin n)) :
    (encIndices (indexList N)).length ≤ indexBits n := by
  have hc : (indexList N).length ≤ n := by
    simpa [indexList] using N.card_le_univ
  have hb : (encIndices (indexList N)).length ≤
      (indexList N).length * (2 * (Nat.log2 n + 1) + 1) := by
    apply length_encList_le
    intro i hi
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
    exact length_encNat_le_log2 (Nat.le_of_lt j.isLt)
  exact hb.trans (Nat.mul_le_mul_right _ hc)

private theorem candidate_size {n d : ℕ} (C : Candidate n d) (k bits : ℕ)
    (hb : C.blocks.length ≤ k) (hp : C.path.length ≤ k)
    (he : ∀ e ∈ C.path, (encEdge (edgeList e)).length ≤ bits) :
    (encCandidate (candidateList C)).length ≤ candidateBits n k bits := by
  have hblocks : (encList encIndices (C.blocks.map indexList)).length ≤
      k * (2 * indexBits n + 1) := by
    apply (length_encList_le _ _ ?_).trans
      (Nat.mul_le_mul_right _ (by simpa only [List.length_map] using hb))
    intro N hN
    obtain ⟨N, _, rfl⟩ := List.mem_map.mp hN
    exact index_size N
  have hpath : (encList encEdge (C.path.map edgeList)).length ≤ k * (2 * bits + 1) := by
    apply (length_encList_le _ _ ?_).trans
      (Nat.mul_le_mul_right _ (by simpa only [List.length_map] using hp))
    intro e he'
    obtain ⟨e, hem, rfl⟩ := List.mem_map.mp he'
    exact he e hem
  simp only [candidateList, encCandidate, length_encPair]
  unfold candidateBits
  omega

private theorem flatMap_length_bound {α β : Type} (xs : List α) (f : α → List β)
    (b : ℕ) (hb : ∀ a ∈ xs, (f a).length ≤ b) :
    (xs.flatMap f).length ≤ xs.length * b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have ha := hb a (by simp)
    have ht := ih (fun a ha ↦ hb a (by simp [ha]))
    omega

private theorem level_count (ref : Refiner) (hs : RefineSpec ref)
    {n d : ℕ} (mode : Mode) (k : ℕ) (ps : ℕ → StepParams)
    (pts : Fin n → Fin d → ℚ) (fuel h : ℕ) :
    (levels ref mode k ps pts fuel h).length ≤ branchCap mode k ps ^ h := by
  induction h with
  | zero => simp [levels]
  | succ h ih =>
    rw [levels, pow_succ]
    apply (flatMap_length_bound _ _ _ ?_).trans (Nat.mul_le_mul_right _ ih)
    intro C _
    split_ifs
    · exact (hs mode k ps pts fuel C).1
    · simp

private theorem level_invariant (run : BlockRefiner) {n d : ℕ}
    (mode : Mode) (k : ℕ) (ps : ℕ → StepParams) (pts : Fin n → Fin d → ℚ)
    (fuel bits : ℕ)
    (he : ∀ h, h < k - 1 → ∀ N e, e ∈ run mode k ps pts fuel h N →
      (encEdge (edgeList e)).length ≤ bits)
    (h : ℕ) (hh : h ≤ k - 1) :
    ∀ C ∈ levels (refinerFromBlocks run) mode k ps pts fuel h,
      C.blocks.length ≤ h + 1 ∧ C.path.length ≤ h ∧
        ∀ e ∈ C.path, (encEdge (edgeList e)).length ≤ bits := by
  induction h with
  | zero =>
    intro C hC
    obtain rfl : C = root n d := by simpa [levels] using hC
    simp [root]
  | succ h ih =>
    intro C' hC'
    obtain ⟨C, hC, hC'⟩ := List.mem_flatMap.mp hC'
    have hc := ih (by omega) C hC
    split_ifs at hC' with hlt
    · dsimp only [refinerFromBlocks] at hC'
      split_ifs at hC' with hg
      · obtain ⟨j, _, hmap⟩ := List.mem_flatMap.mp hC'
        obtain ⟨e, heRun, rfl⟩ := List.mem_map.mp hmap
        have hj : j.val < C.blocks.length := j.isLt
        have hlen : (replaceBlock pts C j e).blocks.length = C.blocks.length + 1 := by
          simp only [replaceBlock, List.length_append, List.length_take,
            List.length_cons, List.length_nil, List.length_drop, Nat.min_eq_left hj.le]
          omega
        refine ⟨by omega, ?_, ?_⟩
        · simpa only [replaceBlock, List.length_append, List.length_singleton] using
            Nat.add_le_add_right hc.2.1 1
        · intro e' he'
          rcases List.mem_append.mp he' with he' | he'
          · exact hc.2.2 e' he'
          · have heq := List.mem_singleton.mp he'
            subst e'
            exact he C.path.length (by omega) C.blocks[j] e heRun
      · simp at hC'
    · simp at hC'

/-- Counts alone do not bound storage. A uniform edge-bit envelope supplies the missing
factor, while all parent subsets have their canonical `Fin n` encoding bound. -/
theorem levels_storage (run : BlockRefiner) (hs : RefineSpec (refinerFromBlocks run))
    {n d : ℕ} (mode : Mode) (k : ℕ) (ps : ℕ → StepParams)
    (pts : Fin n → Fin d → ℚ) (fuel bits : ℕ) (hk : 1 ≤ k)
    (he : ∀ h, h < k - 1 → ∀ N e, e ∈ run mode k ps pts fuel h N →
      (encEdge (edgeList e)).length ≤ bits)
    (h : ℕ) (hh : h ≤ k - 1) :
    (encList encCandidate
      ((levels (refinerFromBlocks run) mode k ps pts fuel h).map candidateList)).length ≤
        levelBits n k (branchCap mode k ps) bits := by
  have hc := level_count (refinerFromBlocks run) hs mode k ps pts fuel h
  have hbranch : 1 ≤ branchCap mode k ps := le_max_left _ _
  have hcount := hc.trans (Nat.pow_le_pow_right hbranch hh)
  have hbound : ∀ L ∈
      (levels (refinerFromBlocks run) mode k ps pts fuel h).map candidateList,
      (encCandidate L).length ≤ candidateBits n k bits := by
    intro L hL
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hL
    obtain ⟨hb, hp, he'⟩ := level_invariant run mode k ps pts fuel bits he h hh C hC
    exact candidate_size C k bits (by omega) (by omega) he'
  unfold levelBits
  exact (length_encList_le encCandidate _ hbound).trans
    (Nat.mul_le_mul_right _ (by simpa only [List.length_map] using hcount))

end ABBKS26.Assembly.Exec.RefineSynth
