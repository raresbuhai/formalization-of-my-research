module

public import ABBKS26.Assembly.ExecNestedAuxFacts

/-! # Agreement of the capped Gram-block layout -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common MvPolynomial
open SoS.Solver (RawPoly)
open scoped BigOperators

/-- The semantic rational embedding preserves total degree exactly. -/
theorem totalDegree_real {n : ℕ} (p : MvPolynomial (Fin n) ℚ) :
    (SoS.toReal p).totalDegree = p.totalDegree := by
  unfold SoS.toReal totalDegree
  rw [support_map_of_injective p Rat.cast_injective]

/-- The two blocks of family variables use the standard finite sum equivalence. -/
theorem sumIndex_eq (d : ℕ) : Rounding.sumIndex d =
    (finSumFinEquiv : Fin d ⊕ Fin d ≃ Fin (d + d)).symm := by
  funext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · rw [finSumFinEquiv_symm_apply_castAdd]
    simp [Rounding.sumIndex, j.isLt]
  · rw [finSumFinEquiv_symm_apply_natAdd]
    have hj : ¬d + j.val < d := by omega
    simp only [Rounding.sumIndex, Fin.val_natAdd, hj, ↓reduceDIte]
    congr 1
    apply Fin.ext
    simp

/-- Renaming the two family blocks preserves degree. -/
theorem family_degree (d : ℕ) (p : SoS.Solver.RawPoly) :
    (rename (Rounding.sumIndex d) (SoS.toReal (p.toPoly (d + d)))).totalDegree =
      SoS.Poly.degree (2 * d) p := by
  rw [sumIndex_eq, ← renameEquiv_apply, totalDegree_renameEquiv, totalDegree_real,
    ← SoS.Poly.degree_eq_totalDegree, two_mul]

/-- The stated fuel makes every required auxiliary monomial enumeration exact. -/
theorem bases_uncapped (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (r : ℕ) (hr : r ≤ I.degree) :
    SoS.Mono.allB I.fuel I.family.dimension r = SoS.Mono.all I.family.dimension r := by
  have hd := Rounding.RawAux.dimension_le_vars I.family.real I.degree
  have hbase : 2 ≤ Rounding.nestedVars I.family.real I.degree + 2 := by omega
  have hpow : (I.family.dimension + 1) ^ r ≤ I.fuel := by
    apply le_trans _ hfuel
    exact (Nat.pow_le_pow_left (by omega) r).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hrpow : r ≤ 2 ^ r := Nat.lt_two_pow_self.le
  have hrL : r ≤ I.fuel :=
    (hrpow.trans (Nat.pow_le_pow_left hbase r)).trans
      ((Nat.pow_le_pow_right (by omega) (by omega)).trans hfuel)
  exact SoS.Mono.allB_eq hrL hpow

/-- The executable slot labels are the values of the analytic finite labels. -/
theorem slots_agree (I : Rounding.RawInput) :
    slots I = I.family.real.slots.map Fin.val := by
  dsimp only [slots, Rounding.RawFamily.real]
  rw [List.map_filterMap]
  simp only [List.length_map]
  rw [← List.filterMap_eq_filter]
  apply congrArg (fun f ↦ I.family.slots.filterMap f)
  funext a
  by_cases ha : a < I.family.families.length <;> simp [ha]

/-- The constant multiplier is included at the head of both constraint lists. -/
theorem plain_decode (I : Rounding.RawInput) :
    (constant 1 :: I.family.plain).map (fun p ↦
      SoS.toReal (p.toPoly I.family.dimension)) = Rounding.constraintsWithOne I.family.real := by
  simp [Rounding.constraintsWithOne, Rounding.RawFamily.real, constant_toPoly, SoS.toReal]

/-- Raw and analytic plain constraints have the same degree at every index. -/
theorem plain_degree (I : Rounding.RawInput) (j : ℕ) :
    ((Rounding.constraintsWithOne I.family.real)[j]?.getD 0).totalDegree =
      SoS.Poly.degree I.family.dimension ((constant 1 :: I.family.plain).getD j []) := by
  change ((Rounding.constraintsWithOne I.family.real).getD j 0).totalDegree = _
  rw [← plain_decode I]
  have hz : SoS.toReal (SoS.Solver.RawPoly.toPoly I.family.dimension []) = 0 := by
    simp [SoS.Solver.RawPoly.toPoly, SoS.toReal]
  rw [← hz, List.getD_map, totalDegree_real, ← SoS.Poly.degree_eq_totalDegree]

/-- Each in-range plain Gram block has the same number of rows in both layouts. -/
theorem plain_rows (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (j : ℕ) (hj : j < I.family.plain.length + 1) :
    ((plainBases I).getD j []).length = Rounding.gramSize I.family.real I.degree j := by
  have hj' : j < (constant 1 :: I.family.plain).length := by simpa using hj
  rw [plainBases, List.getD_eq_getElem _ _ (by simpa using hj'), List.getElem_map]
  rw [bases_uncapped I hfuel _ (by omega)]
  simp only [Rounding.gramSize, Rounding.monos, List.length_map, plain_degree,
    List.getD_eq_getElem _ _ hj']

/-- Each referenced family block has the same row count in the two layouts. -/
theorem family_rows (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (a : ℕ) (ha : a < I.family.families.length) :
    ((familyBases I).getD a []).length = Rounding.familySize I.family.real I.degree a := by
  rw [familyBases, List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_map]
  rw [bases_uncapped I hfuel _ (by omega)]
  simp only [Rounding.familySize, Rounding.RawFamily.real, List.getElem?_map,
    List.getElem?_eq_getElem ha, Option.map_some, Option.getD_some, family_degree,
    Rounding.monos, List.length_map]

private theorem sum_range_getD {α : Type} (l : List α) (f : α → ℕ) (z : α) :
    ((List.range l.length).map fun i ↦ f (l.getD i z)).sum = (l.map f).sum := by
  rw [SoS.Coords.sum_range_map, SoS.Coords.sum_map_getElem]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem _ _ i.isLt]
  rfl

/-- Total storage for all plain Gram factors matches the analytic prefix sum. -/
theorem plain_total (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    ((plainBases I).map fun M ↦ M.length ^ 2).sum =
      ((List.range (I.family.real.plain.length + 1)).map fun j ↦
        Rounding.gramSize I.family.real I.degree j ^ 2).sum := by
  rw [← sum_range_getD (plainBases I) (fun M ↦ M.length ^ 2) []]
  have hlen : (plainBases I).length = I.family.real.plain.length + 1 := by
    simp [plainBases, Rounding.RawFamily.real]
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  apply congrArg (fun n ↦ n ^ 2)
  exact plain_rows I hfuel j (by simpa [Rounding.RawFamily.real] using List.mem_range.1 hj)

/-- Repeated slots each retain their own Gram and substitution blocks. -/
theorem slot_total (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    ((slots I).map fun s ↦ ((familyBases I).getD s []).length ^ 2 +
      I.family.dimension ^ 2).sum =
    ((List.range I.family.real.slots.length).map fun i ↦
      Rounding.familySize I.family.real I.degree
        (I.family.real.slots[i]?.map Fin.val |>.getD 0) ^ 2 +
          I.family.dimension ^ 2).sum := by
  rw [← sum_range_getD (slots I)
    (fun s ↦ ((familyBases I).getD s []).length ^ 2 + I.family.dimension ^ 2) 0]
  have hlen : (slots I).length = I.family.real.slots.length := by
    rw [slots_agree, List.length_map]
  rw [hlen]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hi' : i < (slots I).length := by rw [hlen]; exact List.mem_range.1 hi
  have hlabel : (I.family.real.slots[i]?.map Fin.val |>.getD 0) =
      (slots I).getD i 0 := by
    rw [slots_agree]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [hlabel]
  have hmem : (slots I).getD i 0 ∈ slots I := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  have hs : (slots I).getD i 0 < I.family.families.length := by
    simpa [slots] using (List.mem_filter.1 hmem).2
  rw [family_rows I hfuel _ hs]

/-- The complete solver-variable count is exactly the analytic count. -/
theorem vars_agree (I : Rounding.RawInput)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    numVars I = Rounding.nestedVars I.family.real I.degree := by
  dsimp only [numVars, slotStart, plainStart]
  simp only [List.take_length]
  rw [plain_total I hfuel, slot_total I hfuel]
  rfl

/-- The even solver degree agrees independently of fuel and validity. -/
theorem degree_agrees (I : Rounding.RawInput) :
    degree I = Rounding.solverDegree I.family.real I.degree := by
  have hf : I.family.real.families.map totalDegree =
      I.family.families.map (SoS.Poly.degree (2 * I.family.dimension)) := by
    simp only [Rounding.RawFamily.real, List.map_map, Function.comp_def]
    apply List.map_congr_left
    intro p _
    exact family_degree _ p
  simp only [degree, Rounding.solverDegree, Rounding.outerDegree, hf]

end ABBKS26.Assembly.Exec.NestedProgram
