module

public import ABBKS26.Assembly.ExecRoundAuxProgram

/-! Discrete invariants for the concrete planner. No solver hypothesis is used here. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundProgram

open Common Rounding

def OnGrid (a : RoundArgs) (v : Vector) : Prop :=
  ∀ q ∈ v, ∃ z : ℤ, q = z / (2 : ℚ) ^ greedyPrecision a

/-- An append history with exactly the rational tests performed by `greedyStep`. -/
inductive GoodBasis (a : RoundArgs) : Points → Prop
  | nil : GoodBasis a []
  | snoc {B : Points} {v : Vector} : GoodBasis a B → acceptable a B v → OnGrid a v →
      GoodBasis a (B ++ [v])

def Safe (a : RoundArgs) (fuel : ℕ) (B : Points) : Prop :=
  B.length ≤ rankCap a.2.2.1 a.2.2.2.1 ∧
    (encPoints B).length ≤ fuel ∧ GoodBasis a B

theorem candidate_grid (a : RoundArgs) (B : Points) (y : List ℤ) :
    OnGrid a (candidate a B y) := by
  intro q hq
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 hq
  exact ⟨_, rfl⟩

theorem safe_nil (a : RoundArgs) (fuel : ℕ) : Safe a fuel [] :=
  ⟨Nat.zero_le _, Nat.zero_le _, .nil⟩

theorem greedyStep_safe (a : RoundArgs) (fuel : ℕ) (M : MatrixL) (s : Bool × Points)
    (hs : Safe a fuel s.2) : Safe a fuel (greedyStep a fuel M s).2 := by
  unfold greedyStep
  split
  · exact hs
  · split
    · exact hs
    · dsimp only
      split
      · exact hs
      · split
        · rename_i h
          refine ⟨?_, h.2, .snoc hs.2.2 h.1 (candidate_grid _ _ _)⟩
          simp only [List.length_append, List.length_singleton]
          omega
        · exact hs

theorem iterate_preserves {α : Type} (f : α → α) (P : α → Prop)
    (hf : ∀ s, P s → P (f s)) (s : α) (hs : P s) (n : ℕ) : P (f^[n] s) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hf _ ih

theorem greedy_safe (a : RoundArgs) (fuel : ℕ) (M : MatrixL) (B : Points)
    (hB : Safe a fuel B) : Safe a fuel (greedy a fuel M B) :=
  iterate_preserves _ (fun s : Bool × Points ↦ Safe a fuel s.2)
    (greedyStep_safe a fuel M) (false, B) hB _

theorem outerStep_safe (a : RoundArgs) (fuel : ℕ) (s : Bool × Points)
    (hs : Safe a fuel s.2) : Safe a fuel (outerStep a fuel s).2 := by
  unfold outerStep
  split
  · exact hs
  · dsimp only
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · exact greedy_safe _ _ _ _ hs

theorem plan_safe (q : RoundArgs × ℕ) : Safe q.1 q.2 (plan q) := by
  unfold plan
  split
  · exact iterate_preserves _ (fun s : Bool × Points ↦ Safe q.1 q.2 s.2)
      (outerStep_safe q.1 q.2) (false, []) (safe_nil _ _) _
  · exact safe_nil _ _

theorem GoodBasis.rows {a : RoundArgs} {B : Points} (hB : GoodBasis a B) :
    ∀ v ∈ B, v.length = a.2.1 := by
  induction hB with
  | nil => simp
  | @snoc B v hB hv _ ih =>
    intro w hw
    rcases List.mem_append.1 hw with hw | hw
    · exact ih w hw
    · have hwv : w = v := by simpa using hw
      exact hwv ▸ hv.1

/-- Decoding and re-encoding a correctly shaped basis changes no stored entry. -/
theorem output_roundtrip (a : RoundArgs) (B : Points)
    (hB : ∀ v ∈ B, v.length = a.2.1) :
    (output a B).basis.map (fun v ↦ List.ofFn v) = B := by
  simp only [output, List.map_map]
  conv_rhs => rw [← List.map_id B]
  apply List.map_congr_left
  intro v hv
  change List.ofFn (vectorOf a.2.1 v) = v
  have hvlen := hB v hv
  apply List.ext_getElem
  · simp [hvlen]
  · intro i hi hj
    simp only [List.getElem_ofFn, vectorOf]
    exact List.getD_eq_getElem _ _ (by simpa [hvlen] using hi)

end ABBKS26.Assembly.Exec.RoundProgram
