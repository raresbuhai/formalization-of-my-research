module

public import ABBKS26.Assembly.Schedule
public import ABBKS26.Assembly.ExecPipeline

/-!
# The algorithm and its budgeted list program

The algorithm of both theorems as a typed pipeline (refinement tree, learning of every
candidate, selection and reclustering), and a list program on rational inputs that computes
it within a budget written in unary, polynomial time on all inputs.
-/

@[expose] public section

namespace ABBKS26.Assembly

noncomputable section


open Matrix

open Common _root_.ABBKS26.Tree Select
variable {n d : ℕ}

structure Program where
  refine : Refiner
  learn : Learner
  tests : TestBuilder
  raw : Input × ℕ → Output

def defaultEstimate (d : ℕ) : Robust.Estimate d := ⟨0, 1⟩

def execute (P : Program) (mode : Mode) (x : Input) (fuel : ℕ) : Output :=
  let n := x.points.length
  let d := dim x.points
  let pts : Fin n → Fin d → ℚ := fun l i ↦ (x.points[l]).getD i 0
  if x.k ≤ 1 then List.replicate n 0 else
  let params := Schedule.params mode x.wmin x.k
  let Cs := leaves P.refine mode x.k params pts fuel
  let learned := learnAll P.learn mode pts fuel Cs
  match select params pts learned with
  | none => List.replicate n 0
  | some L =>
    if L.estimates.length ≠ x.k ∨ L.estimates.any Option.isNone then List.replicate n 0 else
      let E := fun a : Fin x.k ↦ (L.estimates[a.val]?.bind id).getD (defaultEstimate d)
      recluster (fun a b ↦ P.tests mode x.Δ (E a) (E b) fuel) pts

def WellFormed (x : Input) : Prop :=
  0 < x.wmin ∧ x.wmin ≤ 1 ∧ (x.k : ℚ) * x.wmin ≤ 1 ∧ 1 ≤ x.k ∧
    0 < x.δ ∧ ∀ row ∈ x.points, row.length = dim x.points

def budgetNeed (mode : Mode) (x : Input) : ℕ :=
  if x.k ≤ 1 then ((encInput x).length + 2) ^ 100 else
  (Schedule.ledger mode x.wmin x.k + 2) *
    localBudget mode x.k x.points.length (dim x.points) (Schedule.params mode x.wmin x.k) *
      ((encInput x).length + 2) ^ 100

def encPadded : Input × ℕ ↪ List Bool :=
  Encoding.encPair encInput Encoding.encUnary

def ProgramSpec (mode : Mode) (P : Program) : Prop :=
  RefineSpec P.refine ∧ LearnerSpec P.learn ∧ TestSpec P.tests ∧
    Turing.MultiTapeTM.ComputableInPolyTime P.raw encPadded encOutput ∧
    (∀ x fuel, WellFormed x → budgetNeed mode x ≤ fuel →
      P.raw (x, fuel) = execute P mode x fuel) ∧
    (∀ x fuel, x.k ≤ 1 → P.raw (x, fuel) = List.replicate x.points.length 0)

/-- A budgeted rational list program realizes the mathematical pipeline. -/
theorem exists_program
    (mode : Mode) : ∃ P : Program, ProgramSpec mode P := by
  obtain ⟨S, hS⟩ := Exec.exists_schedule_code
  obtain ⟨F, hF⟩ := Exec.exists_frame_code
  obtain ⟨M, hM⟩ := Exec.exists_moment_code
  obtain ⟨N, hN⟩ := Exec.exists_nested_code
  obtain ⟨R, hR⟩ := Exec.exists_round_code N hN
  obtain ⟨B, hB⟩ := Exec.exists_refine_code F hF M hM N hN R hR
  obtain ⟨L, hL⟩ := Exec.exists_learn_code F hF
  obtain ⟨T, hT⟩ := Exec.exists_test_code
  let P : Program := ⟨B.ref, L.learn, T.tests, Exec.runL S B L T mode⟩
  refine ⟨P, hB.contract, hL.contract, hT.contract,
    Exec.run_polytime S hS B hB L hL T hT mode, ?_, ?_⟩
  · intro x fuel hx hf
    have h := Exec.run_agrees S hS B hB L hL T hT mode x fuel hx hf
    apply h.trans
    unfold Exec.pipeline execute
    dsimp only [P]
    unfold Exec.inputPoints Exec.finish defaultEstimate
    dsimp only
    congr 1
    split <;> simp_all only
  · intro x fuel hk
    exact Exec.run_zero S B L T mode x fuel hk

/-- The implementation witness includes an unconditional polynomial-time raw program. -/
def program (mode : Mode) : Program := Classical.choose (exists_program mode)

def algorithm (mode : Mode) (budget : Input → ℕ) (xr : Input × List Bool) : Output :=
  (program mode).raw (xr.1, budget xr.1)

/-- The chosen program satisfies its semantic and unconditional cost contracts. -/
theorem program_spec
    (mode : Mode) : ProgramSpec mode (program mode) := by
  exact Classical.choose_spec (exists_program mode)

private theorem wellFormed_sample
    {k d n : ℕ} (M : Mixture k d) (w Δ δ : ℚ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hw : 0 < w)
    (hwj : ∀ i, (w : ℝ) ≤ M.w i) (hδ : 0 < δ) :
    WellFormed ⟨k, w, Δ, δ, roundedSample r ω⟩ := by
  have hk : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    have hs := hM.sum_w
    simp [hk0] at hs
  have hkw : (k : ℚ) * w ≤ 1 := by
    have hs : (k : ℝ) * w ≤ 1 := by
      calc
        (k : ℝ) * w = ∑ _ : Fin k, (w : ℝ) := by simp
        _ ≤ ∑ i : Fin k, M.w i := Finset.sum_le_sum (fun i _ ↦ hwj i)
        _ = 1 := hM.sum_w
    exact_mod_cast hs
  have hw1 : w ≤ 1 := by
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    nlinarith only [hkw, mul_le_mul_of_nonneg_right hkq hw.le]
  refine ⟨hw, hw1, hkw, hk, hδ, ?_⟩
  intro row hrow
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hrow
  cases n with
  | zero => exact Fin.elim0 j
  | succ n => simp [dim, roundedSample, List.ofFn_succ]

/-- The raw program agrees with the typed pipeline on a rounded valid sample. -/
theorem algorithm_on_sample
    {k d n : ℕ} (mode : Mode) (budget : Input → ℕ) (M : Mixture k d)
    (w Δ δ : ℚ) (ω : Fin n → Triple k d) (r : Rounding k d) (coins : List Bool)
    (hM : M.Valid) (hw : 0 < w) (hwj : ∀ i, (w : ℝ) ≤ M.w i) (hδ : 0 < δ)
    (hb : ∀ x, WellFormed x → budgetNeed mode x ≤ budget x) :
    algorithm mode budget (⟨k, w, Δ, δ, roundedSample r ω⟩, coins) =
      execute (program mode) mode ⟨k, w, Δ, δ, roundedSample r ω⟩
        (budget ⟨k, w, Δ, δ, roundedSample r ω⟩) := by
  have hx := wellFormed_sample M w Δ δ ω r hM hw hwj hδ
  exact (program_spec mode).2.2.2.2.1 _ _ hx (hb _ hx)

end

end ABBKS26.Assembly
