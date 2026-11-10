module

public import ABBKS26.Assembly.ExecRefineAuxAgreement
public import ABBKS26.Assembly.ExecRefineAuxKernel
public import ABBKS26.Assembly.ExecRefineAuxPoly

/-! Fuel adequacy and representation of the candidate wrapper. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime

/-- For nontrivial component counts the frozen budget dominates the local budget. -/
theorem local_fuel (mode : Mode) (x : Input) (hk : 2 ≤ x.k) :
    localBudget mode x.k x.points.length (dim x.points)
      (Schedule.params mode x.wmin x.k) ≤ need mode x := by
  rw [need, ite_eq_right (by omega)]
  exact (Nat.le_mul_of_pos_left _ (by omega)).trans
    (Nat.le_mul_of_pos_right _ (by positivity))

/-- The unary scan and the final count cap suffice independently of coefficient lengths. -/
theorem count_fuel (mode : Mode) (k n d : ℕ) (ps : ℕ → StepParams) :
    k ≤ localBudget mode k n d ps ∧ branchCap mode k ps ≤ localBudget mode k n d ps := by
  have hb : 1 ≤ branchCap mode k ps := le_max_left _ _
  have hp : (branchCap mode k ps + 1) ^ (k + 1) ≤ localBudget mode k n d ps := by
    unfold localBudget
    have hn : 0 < (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) :=
      pow_pos (by omega) _
    have hd : 0 < (if mode = .centered then 1 else
        (d + 2) ^ (1000000000 * (Rounding.solverConstant + 1) * (logInv (ps 0).w + 3) ^ 2) *
            (idReserves k ps + 2) ^ (1000000000 * (Rounding.solverConstant + 1) *
              (logInv (ps 0).w + 3) ^ 2)) := by
      split_ifs
      · exact Nat.zero_lt_one
      · exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    exact (Nat.le_mul_of_pos_right _ hn).trans (Nat.le_mul_of_pos_right _ hd)
  constructor
  · calc
      k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self (n := k))
      _ ≤ (branchCap mode k ps + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      _ ≤ (branchCap mode k ps + 1) ^ (k + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ _ := hp
  · exact (Nat.le_succ _).trans ((le_self_pow (by omega) (by omega)).trans hp)

private theorem block_cap (mode : Mode) (k : ℕ) (ps : ℕ → StepParams)
    (h : ℕ) (hh : h < k - 1) :
    stepBranchCap mode k (ps h) ≤ branchCap mode k ps := by
  have hfold (xs : List ℕ) (a b : ℕ) (hb : b ≤ a ∨ b ∈ xs) :
      b ≤ xs.foldl max a := by
    induction xs generalizing a with
    | nil => simpa using hb
    | cons x xs ih =>
      apply ih
      rcases hb with hb | hb
      · exact Or.inl (hb.trans (le_max_left _ _))
      · rcases List.mem_cons.mp hb with rfl | hb
        · exact Or.inl (le_max_right _ _)
        · exact Or.inr hb
  have hc : stepBranchCap mode k (ps h) ≤
      ((List.range (k - 1)).map fun j ↦ stepBranchCap mode k (ps j)).foldl max 0 :=
    hfold _ 0 _ (Or.inr (List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩))
  exact hc.trans ((Nat.le_mul_of_pos_left _ (by omega)).trans (le_max_right 1 _))

/-- Canonical block agreement plus count bounds removes all three wrapper truncations.
No restriction on incoming statistics or history encoding length is used. -/
theorem refine_agrees (B : RefineCode) (run : BlockRefiner)
    (href : ∀ {n d}, @B.ref n d = @refinerFromBlocks run n d) (hspec : RefineSpec B.ref)
    (mode : Mode) (x : Input) (fuel : ℕ) (hf : need mode x ≤ fuel)
    (hcontract : BlockContract mode run)
    (hblock : ∀ h, h < x.k - 1 → ∀ N : Finset (Fin x.points.length),
      B.block mode ((dim x.points, x.k,
        (List.range x.k).map (fun j ↦ paramsList (Schedule.params mode x.wmin x.k j)),
        x.points, h, indexList N), fuel) =
        (run mode x.k (Schedule.params mode x.wmin x.k)
          (inputPoints x) fuel h N).map edgeList)
    (C : Candidate x.points.length (dim x.points)) :
    refineL B mode ((dim x.points, x.k,
      (List.range x.k).map (fun j ↦ paramsList (Schedule.params mode x.wmin x.k j)),
      x.points, candidateList C), fuel) =
      (B.ref mode x.k (Schedule.params mode x.wmin x.k)
        (inputPoints x) fuel C).map candidateList := by
  let ps := Schedule.params mode x.wmin x.k
  by_cases hg : C.blocks.length < x.k ∧ C.path.length + 1 = C.blocks.length
  · have hk : 2 ≤ x.k := by omega
    have hl := (local_fuel mode x hk).trans hf
    have hcount := count_fuel mode x.k x.points.length (dim x.points) ps
    have hscan : C.blocks.length ≤ fuel := (Nat.le_of_lt hg.1).trans (hcount.1.trans hl)
    have hcap : branchCap mode x.k ps ≤ fuel := hcount.2.trans hl
    have hh : C.path.length < x.k - 1 := by omega
    have hin :
        ((List.range C.blocks.length).flatMap fun j ↦
          ((B.block mode ((dim x.points, x.k,
            (List.range x.k).map (fun h ↦ paramsList (ps h)), x.points,
            C.path.length, (candidateList C).1.getD j []), fuel)).take fuel).map
              (replaceL (dim x.points) x.points (candidateList C) j)) =
          (B.ref mode x.k ps (inputPoints x) fuel C).map candidateList := by
      rw [href, refinerFromBlocks, ite_eq_left hg, List.map_flatMap,
        ← List.map_coe_finRange_eq_range (n := C.blocks.length), List.flatMap_map]
      apply List.flatMap_congr
      intro j _
      have hget : (candidateList C).1.getD j.val [] = indexList C.blocks[j] := by
        simp [candidateList, j.isLt]
      rw [hget, hblock C.path.length hh]
      have hb := (hcontract x.k ps (inputPoints x) fuel C.path.length C.blocks[j]).1
      have hbfuel := hb.trans ((block_cap mode x.k ps C.path.length hh).trans hcap)
      rw [List.take_of_length_le (by simpa only [List.length_map] using hbfuel)]
      simp only [List.map_map]
      apply List.map_congr_left
      intro e _
      have hpts : (fun l : Fin x.points.length ↦
          vectorOf (dim x.points) (x.points.getD l.val [])) = inputPoints x := by
        funext l i
        simp [vectorOf, inputPoints, l.isLt]
      simpa only [Function.comp_apply, hpts] using replace_agrees x.points C j.val e
    simp only [refineL, candidateList, List.length_map]
    rw [ite_eq_left hg, min_eq_left hscan]
    have hout : ((B.ref mode x.k ps (inputPoints x) fuel C).map candidateList).length ≤
        fuel := by
      simpa only [List.length_map] using
        ((hspec mode x.k ps (inputPoints x) fuel C).1.trans hcap)
    have htake := congrArg (List.take fuel) hin
    rw [List.take_of_length_le hout] at htake
    simpa only [candidateList, ps] using htake
  · simp only [refineL, candidateList, List.length_map]
    rw [ite_eq_right hg, href, refinerFromBlocks, ite_eq_right hg]
    rfl

end ABBKS26.Assembly.Exec.RefineSynth
