module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecBasis
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecFuel
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecTargets

/-! The capped executable moment, nested-solver, rounder, and spectral-grid pipeline. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecProgram

open Common Centered Rounding _root_.ABBKS26.Tree Sources Builders FrameAux.Linear
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def scale (a : Args) : ℚ :=
  64 * (a.1.1 + 1 : ℚ) ^ 2 + 1 / SpecInput.weight a ^ 2 +
    1 / (12 * SpecInput.delta a ^ 2) + 100 / SpecInput.accuracy a ^ 8 +
      SpecComplement.size a + 4

def certificateNorm (a : Args) : ℚ := scale a ^ 200 + SpecInput.tolerance a

def instanceNorm (a : Args) : ℚ := (a.1.1 + 1 : ℚ) * (1.1 / SpecInput.weight a)

def ball (a : Args) : ℚ :=
  SpecTargets.ball a.1.1 (SpecInput.tolerance a) (certificateNorm a) (instanceNorm a)

theorem scale_polytime : ComputableInPolyTime scale encArgs encRat := by
  have hd := rat_add' (rat_natCast' (unary_to_binary.comp
    (show ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary by fun_prop)))
      (const 1)
  have hw := rat_div' (field_polytime 0) (const 2)
  exact rat_add' (rat_add' (rat_add' (rat_add' (rat_add'
    (rat_mul' (const 64) (rat_pow' hd (const 2)))
    (rat_div' (const 1) (rat_pow' hw (const 2))))
    (rat_div' (const 1) (rat_mul' (const 12) (rat_pow' SpecInput.delta_polytime (const 2)))))
    (rat_div' (const 100) (rat_pow' (field_polytime 10) (const 8))))
    SpecComplement.size_polytime) (const 4)

theorem certificateNorm_polytime : ComputableInPolyTime certificateNorm encArgs encRat :=
  rat_add' (rat_pow' scale_polytime (const 200)) SpecInput.tolerance_polytime

theorem instanceNorm_polytime : ComputableInPolyTime instanceNorm encArgs encRat :=
  rat_mul' (rat_add' (rat_natCast' (unary_to_binary.comp (by fun_prop))) (const 1))
    (rat_div' (const 1.1) (rat_div' (field_polytime 0) (const 2)))

theorem ball_polytime : ComputableInPolyTime ball encArgs encRat :=
  SpecTargets.ball_polytime_of (by fun_prop) SpecInput.tolerance_polytime
    certificateNorm_polytime instanceNorm_polytime

def roundArgs (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (a : Args) : RoundArgs :=
  (SpecSolver.zeroObjective (NC.build (SpecInput.query F MC ball a)), a.1.1,
    SpecFuel.radius a, SpecFuel.rank a, SpecConcentration.norm a)

theorem roundArgs_polytime (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC) :
    ComputableInPolyTime (roundArgs F MC NC) encArgs encRoundArgs :=
  (SpecSolver.build_polytime_of NC hNC
    (SpecInput.query_polytime F hF MC hMC ball ball_polytime)).prod
      ((show ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary by fun_prop).prod
        (SpecFuel.radius_polytime.prod
          (SpecFuel.rank_polytime.prod SpecConcentration.norm_polytime)))

noncomputable def basis (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (a : Args) : Points :=
  SpecSolver.round solverConstant 26 RC (roundArgs F MC NC a, a.2)

theorem basis_polytime (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC)
    (RC : RoundCode) (hRC : RoundSpecL RC) :
    ComputableInPolyTime (basis F MC NC RC) encArgs encPoints := by
  have ht : ComputableInPolyTime
      (SpecSolver.round solverConstant 26 RC ∘
        (fun a ↦ (roundArgs F MC NC a, a.2))) encArgs encPoints :=
    (SpecSolver.round_polytime solverConstant 26 RC hRC).comp
      ((roundArgs_polytime F hF MC hMC NC hNC).prod (snd _ _))
  exact ht

def accuracy (a : Args) : ℚ :=
  SpecInput.accuracy a / (8 * (SpecFuel.dimension a + 1 : ℚ))

theorem accuracy_polytime : ComputableInPolyTime accuracy encArgs encRat :=
  rat_div' (field_polytime 10) (rat_mul' (const 8)
    (rat_add' (rat_natCast' (unary_to_binary.comp SpecFuel.dimension_polytime)) (const 1)))

noncomputable def normalized (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (a : Args) : Points := SpecBasis.run a.1.1 (basis F MC NC RC a) (accuracy a)

theorem normalized_polytime (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC)
    (RC : RoundCode) (hRC : RoundSpecL RC) :
    ComputableInPolyTime (normalized F MC NC RC) encArgs encPoints :=
  SpecBasis.run_polytime_of (by fun_prop) (basis_polytime F hF MC hMC NC hNC RC hRC)
    accuracy_polytime

def transposeFrame (F : FrameCode) (a : Args) : MatrixL :=
  RoundProgram.table a.1.1 fun i j ↦ ent (F.run .centered (FrobFar.callArgs a)).2.1 j i

theorem transposeFrame_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (transposeFrame F) encArgs encMatrix := by
  have hmat : ComputableInPolyTime
      (fun a ↦ (F.run .centered (FrobFar.callArgs a)).2.1) encArgs encMatrix :=
    (fst _ _).comp ((snd _ _).comp
      ((hF.polytime .centered).comp FrobFar.callArgs_polytime))
  unfold transposeFrame
  apply RoundProgram.table_polytime (by fun_prop)
  exact ent' (hmat.comp (fst _ _))
    ((snd encUnary encUnary).comp (snd _ _))
    ((fst encUnary encUnary).comp (snd _ _))

def pull (d : ℕ) (T : MatrixL) (B : Points) : Points := B.map (mulVecL d T)

theorem pull_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {T : α → MatrixL} {B : α → Points}
    (hd : ComputableInPolyTime d enc encUnary)
    (hT : ComputableInPolyTime T enc encMatrix)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun a ↦ pull (d a) (T a) (B a)) enc encPoints :=
  mapWithInput hB (mulVecL' (hd.comp (fst _ _)) (hT.comp (fst _ _)) (snd _ _))

noncomputable def pulled (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (a : Args) : Points :=
  pull a.1.1 (transposeFrame F a) (SpecFuel.grid (normalized F MC NC RC) a)

theorem pulled_polytime (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC)
    (RC : RoundCode) (hRC : RoundSpecL RC) :
    ComputableInPolyTime (pulled F MC NC RC) encArgs encPoints :=
  pull_polytime_of (by fun_prop) (transposeFrame_polytime F hF)
    (SpecFuel.grid_polytime _ (normalized_polytime F hF MC hMC NC hNC RC hRC))

noncomputable def directions (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (a : Args) : Points :=
  if a.1.2.2.2.2.1 < a.1.2.1 then
    pulled F MC NC RC a
  else []

theorem directions_polytime (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC)
    (RC : RoundCode) (hRC : RoundSpecL RC) :
    ComputableInPolyTime (directions F MC NC RC) encArgs encPoints := by
  have hc : ComputableInPolyTime
      (fun a : Args ↦ decide (a.1.2.2.2.2.1 < a.1.2.1)) encArgs encBool := by
    exact binary_lt' (by fun_prop) (by fun_prop)
  have hp := pulled_polytime F hF MC hMC NC hNC RC hRC
  unfold directions
  exact ite_prop hc hp (const [])

theorem count {n d : ℕ} (F : FrameCode) (MC : MomentCode) (NC : NestedCode)
    (RC : RoundCode) (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) :
    let p := SpecGuard.run (directions F MC NC RC) (args k ps x h P, fuel)
    p.1.length * p.2.length ≤ centeredStageCap false k (ps h) := by
  by_cases hh : h < k
  · apply SpecGuard.count _ k ps x fuel h P hh
    have hw : SpecInput.weight (args k ps x h P, fuel) = (ps h).w / 2 := by
      unfold SpecInput.weight
      rw [field_args _ _ _ _ _ _ hh]
      rfl
    have hμ : SpecInput.accuracy (args k ps x h P, fuel) = (ps h).subspaceAccuracy := by
      unfold SpecInput.accuracy
      rw [field_args _ _ _ _ _ _ hh]
      rfl
    have hr : SpecFuel.deviation (args k ps x h P, fuel) =
        10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10 := by
      unfold SpecFuel.deviation
      rw [field_args _ _ _ _ _ _ hh, hw]
      rfl
    have hb := SpecFuel.grid_length (normalized F MC NC RC) (args k ps x h P, fuel)
    rw [hw, hμ, hr] at hb
    dsimp only [directions, args]
    rw [ite_eq_left hh]
    change (pull _ _ _).length ≤ _
    rw [pull, List.length_map]
    dsimp only [args] at hb
    exact hb
  · dsimp only [SpecGuard.run, directions, args]
    rw [ite_eq_right hh]
    simp only [List.map_nil, List.length_nil, Nat.zero_mul, Nat.zero_le]

end ABBKS26.Assembly.Exec.RefineSynth.SpecProgram
