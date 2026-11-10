module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdNorms
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdCoverage

/-! The executable rounded SUB, rational net, and affine mean-statistic pipeline. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdProgram

open Common Matrix Rounding FrameAux.Linear
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def query (MC : MomentCode) (a : Args) : NestedArgs × ℕ :=
  IdSolver.query a.1.1 (8 * IdInput.degree a) (IdReify.system MC a)
    (IdPayload.tolerance a) (IdNorms.ballInput a) a.2

theorem query_polytime (MC : MomentCode) (hMC : MomentSpec MC) :
    ComputableInPolyTime (query MC) encArgs (encPair encNestedArgs encUnary) :=
  IdSolver.query_polytime_of (by fun_prop) (unary_mul' (const 8) IdInput.degree_polytime)
    (IdReify.system_polytime MC hMC) IdPayload.tolerance_polytime
    IdNorms.ballInput_polytime (snd _ _)

def problem (MC : MomentCode) (NC : NestedCode) (a : Args) : SoS.Solver.Problem :=
  SpecSolver.zeroObjective (NC.build (query MC a))

theorem problem_polytime (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) :
    ComputableInPolyTime (problem MC NC) encArgs SoS.Solver.encProblem :=
  SpecSolver.build_polytime_of NC hNC (query_polytime MC hMC)

def grid (MC : MomentCode) (NC : NestedCode) (RC : RoundCode) : Args → Points :=
  IdCoverage.run (problem MC NC) IdNorms.normInput RC

theorem grid_polytime (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) (RC : RoundCode) (hRC : RoundSpecL RC) :
    ComputableInPolyTime (grid MC NC RC) encArgs encPoints :=
  IdCoverage.run_polytime _ _ RC hRC (problem_polytime MC hMC NC hNC)
    IdNorms.normInput_polytime

def transposeFrame (a : Args) : MatrixL :=
  RoundProgram.table a.1.1 fun i j ↦ ent (IdCenter.run a).2.1 j i

theorem transposeFrame_polytime :
    ComputableInPolyTime transposeFrame encArgs encMatrix := by
  unfold transposeFrame
  apply RoundProgram.table_polytime (by fun_prop)
  exact ent' (((fst _ _).comp ((snd _ _).comp IdCenter.run_polytime)).comp (fst _ _))
    ((snd encUnary encUnary).comp (snd _ _))
    ((fst encUnary encUnary).comp (snd _ _))

def statistic (a : Args) (u : Vector) : StatisticL :=
  let b := mulVecL a.1.1 (transposeFrame a) u
  ([], b, -dotL a.1.1 b (IdCenter.run a).2.2.1)

theorem statistic_polytime : ComputableInPolyTime
    (fun q : Args × Vector ↦ statistic q.1 q.2)
    (encPair encArgs encVector) encStatistic := by
  have hd : ComputableInPolyTime (fun q : Args × Vector ↦ q.1.1.1)
      (encPair encArgs encVector) encUnary := by fun_prop
  have hb : ComputableInPolyTime (fun q : Args × Vector ↦
      mulVecL q.1.1.1 (transposeFrame q.1) q.2) (encPair encArgs encVector) encVector :=
    mulVecL' hd (transposeFrame_polytime.comp (fst _ _)) (snd _ _)
  have hc := (((fst _ _).comp ((snd _ _).comp ((snd _ _).comp
    IdCenter.run_polytime))).comp (fst encArgs encVector))
  exact (const []).prod (hb.prod (rat_neg' (dotL' hd hb hc)))

def statistics (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (a : Args) : IdGuard.Statistics :=
  (grid MC NC RC a).map (statistic a)

theorem statistics_polytime (MC : MomentCode) (hMC : MomentSpec MC)
    (NC : NestedCode) (hNC : NestedSpec NC) (RC : RoundCode) (hRC : RoundSpecL RC) :
    ComputableInPolyTime (statistics MC NC RC) encArgs IdGuard.encStatistics :=
  mapWithInput (grid_polytime MC hMC NC hNC RC hRC) statistic_polytime

theorem count {n d : ℕ} (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (k : ℕ) (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    (statistics MC NC RC (args k ps x h P, fuel)).length ≤
      netBound (IdCov.N_pack (ps h).subspaceAccuracy k) (ps h).subspaceAccuracy := by
  have he := IdCoverage.length_run (problem MC NC) IdNorms.normInput RC
    (args k ps x h P, fuel)
  rw [IdFuel.fields k ps x fuel h P hh] at he
  change (grid MC NC RC (args k ps x h P, fuel)).length ≤
    netBound (IdCov.N_pack (ps h).subspaceAccuracy k) (ps h).subspaceAccuracy at he
  simpa only [statistics, List.length_map] using he

noncomputable section

variable {n k d : ℕ}

theorem transpose_rep (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    RepT (transposeFrame (args k ps x h P, fuel))
      (IdFrame.frame (ps h) x fuel P).transformᵀ := by
  rw [IdFrame.frame_agrees ps x fuel h P hh]
  intro i j
  change ent (transposeFrame (args k ps x h P, fuel)) i j =
    (frameOf d (IdCenter.run (args k ps x h P, fuel))).transform j i
  dsimp only [transposeFrame, RoundProgram.table, ent, args, frameOf, matrixOf]
  rw [getD_map_range _ _ i.isLt, getD_map_range _ _ j.isLt]

/-- The raw statistic is precisely the affine pullback of the rational net direction. -/
theorem statistic_decoded (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) (u : Vector) :
    statisticOf d (statistic (args k ps x h P, fuel) u) =
      ABBKS26.RefineAux.meanStatistic (IdFrame.frame (ps h) x fuel P).transform
        (IdFrame.frame (ps h) x fuel P).center (vectorOf d u) := by
  have hb : vectorOf d (mulVecL d (transposeFrame (args k ps x h P, fuel)) u) =
      (IdFrame.frame (ps h) x fuel P).transformᵀ *ᵥ vectorOf d u := by
    funext i
    exact mulVecL_rep (transpose_rep ps x fuel h P hh) (fun _ ↦ rfl) i
  have hc : vectorOf d (IdCenter.run (args k ps x h P, fuel)).2.2.1 =
      (IdFrame.frame (ps h) x fuel P).center := by
    rw [IdFrame.frame_agrees ps x fuel h P hh]
    rfl
  change (⟨matrixOf d [], _, _⟩ : Statistic d) = ⟨0, _, _⟩
  congr 1
  change -dotL d (mulVecL d (transposeFrame (args k ps x h P, fuel)) u)
      (IdCenter.run (args k ps x h P, fuel)).2.2.1 = _
  rw [dotL_eq (fun _ ↦ rfl) (fun _ ↦ rfl)]
  change -(vectorOf d (mulVecL d (transposeFrame (args k ps x h P, fuel)) u) ⬝ᵥ
    vectorOf d (IdCenter.run (args k ps x h P, fuel)).2.2.1) = _
  rw [hb, hc]

end

end ABBKS26.Assembly.Exec.RefineSynth.IdProgram
