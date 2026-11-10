module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecFrame

/-! Executable quartic moments in the shared centered frame. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecMoments

open Common _root_.ABBKS26.Tree Matrix Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

variable {n k d : ℕ}

def applyMatrix (a : ℕ × MatrixL × Points) : Points :=
  a.2.2.map (FrameAux.Linear.mulVecL a.1 a.2.1)

private theorem applyMatrix_polytime : ComputableInPolyTime applyMatrix
    (encPair encUnary (encPair encMatrix encPoints)) encPoints := by
  apply mapWithInput (by fun_prop)
  exact FrameAux.Linear.mulVecL' (by fun_prop) (by fun_prop) (by fun_prop)

private theorem frameMatrix_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (fun a ↦ (F.run .centered (FrobFar.callArgs a)).2.1)
      encArgs encMatrix :=
  (fst _ _).comp ((snd _ _).comp
    ((hF.polytime .centered).comp FrobFar.callArgs_polytime))

private theorem sample_polytime :
    ComputableInPolyTime (fun a : Args ↦ a.1.2.2.2.1) encArgs encPoints := by fun_prop

/-- Transform every sample row; the block indices keep their original meaning. -/
def points (F : FrameCode) (a : Args) : Points :=
  applyMatrix (a.1.1, (F.run .centered (FrobFar.callArgs a)).2.1, a.1.2.2.2.1)

theorem points_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (points F) encArgs encPoints := by
  have hd : ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary := by fun_prop
  exact applyMatrix_polytime.comp
    (hd.prod ((frameMatrix_polytime F hF).prod sample_polytime))

def input (F : FrameCode) (a : Args) : MomentInput :=
  ((points F a, a.1.2.2.2.2.2, [4], field a 0 / 2, field a 14), a.2)

theorem input_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (input F) encArgs encMomentInput := by
  have hi : ComputableInPolyTime (fun a : Args ↦ a.1.2.2.2.2.2) encArgs encIndices := by
    fun_prop
  exact ((points_polytime F hF).prod (hi.prod ((const [4]).prod
    ((rat_div' (field_polytime 0) (const 2)).prod (field_polytime 14))))).prod
      (by fun_prop)

/-- The fourth entry is used, as in `momentProc`; absent entries decode as zero. -/
def run (F : FrameCode) (M : MomentCode) (a : Args) : SoS.Solver.RawPoly :=
  (momentL M (input F a)).getD 4 []

theorem run_polytime (F : FrameCode) (hF : FrameSpec F)
    (M : MomentCode) (hM : MomentSpec M) :
    ComputableInPolyTime (run F M) encArgs SoS.Solver.encRawPoly := by
  exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary
    (encL := encList SoS.Solver.encRawPoly) []
    ((moment_polytime M hM).comp (input_polytime F hF)).tidy (const 4).tidy)

theorem points_agrees (F : FrameCode) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    points F (args k ps x h P, fuel) =
      pointsOf (ABBKS26.RefineAux.affinePoints x
        (SpecFrame.frame F (ps h) x fuel P).transform 0) := by
  rw [SpecFrame.frame_agrees F ps x fuel h P hh]
  dsimp only [points, applyMatrix, args, frameOf, ABBKS26.RefineAux.affinePoints]
  simp only [pointsOf, List.map_ofFn]
  congr 1
  funext l
  apply List.ext_getElem
  · simp [FrameAux.Linear.mulVecL]
  · intro i hi hi'
    have hi : i < d := by simpa using hi'
    simp only [Function.comp_apply, FrameAux.Linear.mulVecL, List.getElem_map,
      List.getElem_range, List.getElem_ofFn, ABBKS26.RefineAux.affinePoints, sub_zero]
    exact FrameAux.Linear.dotL_eq (fun _ ↦ rfl)
      (fun j ↦ by simp [List.getD_eq_getElem?_getD])

theorem input_agrees (F : FrameCode) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    input F (args k ps x h P, fuel) =
      ((pointsOf (ABBKS26.RefineAux.affinePoints x
        (SpecFrame.frame F (ps h) x fuel P).transform 0), indexList P,
        ({4} : Finset ℕ).sort (· ≤ ·), (ps h).w / 2, (ps h).contamination), fuel) := by
  simp only [input, points_agrees F ps x fuel h P hh, field_args _ _ _ _ _ _ hh]
  simp [paramsList, args]

theorem run_agrees (F : FrameCode) (M : MomentCode) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    (run F M (args k ps x h P, fuel)).toPoly d =
      momentProc M (ABBKS26.RefineAux.affinePoints x
        (SpecFrame.frame F (ps h) x fuel P).transform 0) P {4}
        ((ps h).w / 2) (ps h).contamination fuel 4 := by
  rw [run, input_agrees F ps x fuel h P hh]
  rfl

/-- The adequate quartic budget fits the existing centered local allowance. -/
theorem fuel_bound (k n d : ℕ) (ps : ℕ → StepParams) :
    momentFuel n d {4} ≤ localBudget .centered k n d ps := by
  have hb : d + 2 ≤ n + d + 2 := by omega
  have hp : 1 ≤ n + d + 2 := by omega
  have he : 100 * (Rounding.solverConstant + 1) +
      100 * (Rounding.solverConstant + 1) * (4 + 1) ^ 2 ≤
        1000000000 * (Rounding.solverConstant + 1) := by omega
  unfold momentFuel
  simp only [Finset.sup_singleton, id_eq]
  calc
    _ ≤ (n + d + 2) ^ (100 * (Rounding.solverConstant + 1)) *
        (n + d + 2) ^ (100 * (Rounding.solverConstant + 1) * (4 + 1) ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb _)
    _ ≤ (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right hp he
    _ ≤ localBudget .centered k n d ps := by
      simp only [localBudget, ite_true, mul_one]
      exact Nat.le_mul_of_pos_left _ (by positivity)

noncomputable section

theorem eta_contamination (ps : ℕ → StepParams) (M : Mixture k d)
    (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d) (r : Rounding k d)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (h : ℕ) (hh : h < k - 1) :
    8 * η ≤ (ps h).contamination := by
  have hl := hp.leakageBudget_nonneg .centered M ε w η Δ D ω r ps h (by omega)
  have hwcast := hp.weight_at .centered M ε w η Δ D ω r ps h (by omega)
  obtain ⟨_, _, _, hw, _, hε, hη, _, _, _, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨_, hw2, _⟩ := hready h hh
  have hw1 : w ≤ 1 := by
    have hwR := Rat.cast_le (K := ℝ) |>.mpr hw2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hwR
    linarith only [hwR, hwcast]
  obtain ⟨_, hleak, hc, _⟩ := hparams h (by omega)
  have hleak0 : (0 : ℝ) ≤ (ps h).leakage := hl.trans hleak
  have he := (div_le_iff₀ hw).mp hc
  have hn : (0 : ℝ) ≤ 1 / n := by positivity
  have hc0 : (0 : ℝ) ≤ (ps h).contamination := by
    have hnum : 0 ≤ 8 * ((ps h).leakage + ε + η + 1 / n) / w := by positivity
    exact hnum.trans hc
  have hm := mul_le_mul_of_nonneg_left hw1 hc0
  linarith only [he, hm, hleak0, hε, hn]

/-- The specified executable moment call certifies the actual clean-pass model. -/
theorem prepared_certificate (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    let A := ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0
    let Q := (run F MC (args k ps x h P, fuel)).toPoly d
    (SoS.toReal Q).IsHomogeneous 4 ∧
      IsSumSq (MvPolynomial.C ((ps h).momentError : ℝ) * nsq ^ 4 -
        (SoS.toReal Q - Robust.populationMoment A.model 4) ^ 2) := by
  classical
  have hc := SpecFrame.prepared_close F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  have hstep := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, _, hreq, hζ, hζle, hm⟩ := hstep
  have hc' : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      (SpecFrame.frame F (ps h) x fuel P) (((ps h).w / 2 : ℚ) : ℝ)
      (|(ps h).R| : ℚ) (((ps h).isotropy / 10000 : ℚ) : ℝ) :=
    SpecFrame.close_accuracy_mono _ _ _ _ _ _
    (by exact_mod_cast hζ.le) (by exact_mod_cast hζle) hc
  subst x
  let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let Y := SpecFrame.frame F (ps h) x fuel P
  let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let T := Y.transform.map (algebraMap ℚ ℝ)
  let A := ABBKS26.RefineAux.affineReference ref T 0
  have hweight := hp.weight_at .centered M ε w η Δ D ω r ps h (by omega)
  have hw' : (((ps h).w / 2 : ℚ) : ℝ) = w / 2 := by
    rw [Rat.cast_div, Rat.cast_ofNat, hweight]
  obtain ⟨hT, hcov⟩ := hp.frame_population_cov_at .centered M ε w η Δ D ω r ps
    h hh P I hI hl hP Y hc'
  have hv := hp.reference_valid_at .centered M ε w η Δ D ω r ps P I hI
  have hAv : A.Valid (((ps h).w / 2 : ℚ) : ℝ) := by
    rw [hw']
    exact ABBKS26.RefineAux.affineReference_valid ref T 0 _ hv hT
  have hr := hp.reference_resilient_at .centered M ε w η Δ D ω r ps P I hI 8
    (by norm_num) (hp.eight_le_degree .centered M ε w η Δ D ω r ps) (by decide)
  have hAr := ABBKS26.RefineAux.affineReference_resilient ref T 0 8 (η / 10 ^ 8) hT hr
  have he := hp.contamination_at .centered M ε w η Δ D ω r ps h (by omega)
    P I hI hl hP
  have he8 : (ps h).contamination ≤ 1 / 8 := by
    have hb := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith only [hb, hw2]
  have hη := hp.2.2.2.2.2.2.1
  have hη100 := hp.2.2.2.2.2.2.2.1
  have hAc : ∀ j, A.model.mean j = 0 := by
    intro j
    change T *ᵥ (M.μ (ABBKS26.RefineAux.component I j) - 0) = 0
    rw [hp.2.1 _, sub_self, mulVec_zero]
  have hobs : ∀ l i, A.observed l i =
      (ABBKS26.RefineAux.affinePoints x Y.transform 0 l i : ℝ) := by
    simpa only [A, T, Pi.zero_apply, Rat.cast_zero, Pi.zero_def] using
      ABBKS26.RefineAux.affineReference_observed ref x Y.transform 0 (fun _ _ ↦ rfl)
  have hcert := hMC.adequate A (ABBKS26.RefineAux.affinePoints x Y.transform 0) {4}
    ((ps h).w / 2) (ps h).contamination (η / 10 ^ 8) fuel hAv hobs (by simp)
    (by simpa using hAr) (by positivity) (by linarith only [hη100]) he he8
    (fun j ↦ by rw [hAc j]; simp only [sqnorm, dotProduct_zero]; positivity)
    (by rw [hw']; exact hcov) ((fuel_bound k n d ps).trans hf)
  have hηc := eta_contamination ps M ε w η Δ D ω r hp h hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmoment, _⟩ := hm
  have hb := ABBKS26.RefineAux.centered_moment_budget (ps h) η hw
    ⟨hη.le, hη100⟩ hηc hmoment
  obtain ⟨hhom, hsos⟩ := hcert 4 (Finset.mem_singleton_self 4)
  have hblock : A.block = P := rfl
  dsimp only at hhom hsos
  rw [hblock] at hhom hsos
  dsimp only [Y] at hhom hsos
  rw [← run_agrees (k := k) F MC ps x fuel h P (by omega)] at hhom hsos
  refine ⟨hhom, ?_⟩
  have hmono := SoS.isSumSq_C_mul (sub_nonneg.mpr hb)
    (SoS.isSumSq_pow (IsSumSq.sum_sq _ _) 4 : IsSumSq ((nsq : RPoly d) ^ 4))
  convert hmono.add hsos using 1
  simp only [nsq, MvPolynomial.C_sub, sub_mul]
  ring

theorem population_fourth (A : FrameModel k d) (hc : ∀ j, A.mean j = 0) :
    Robust.populationMoment A 4 = Centered.phi4 A := by
  simp only [Robust.populationMoment, Centered.phi4, hc]
  apply Finset.sum_congr rfl
  intro j _
  have hz : lin (0 : Vec d) = 0 := by simp [lin]
  rw [hz]
  norm_num [IdCov.hmom, IdCov.hermCoeff, Finset.sum_range_succ,
    MvPolynomial.C_mul, map_ofNat]
  ring

theorem eta_bounds (w μ : ℚ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hμ : 0 < μ ∧ μ ≤ 1 / 64) :
    0 ≤ Centered.etaStar w μ ∧ Centered.etaStar w μ ≤ 1 := by
  have hw1 : w ≤ 1 := hw.2.trans (by norm_num)
  have hμ1 : μ ≤ 1 := hμ.2.trans (by norm_num)
  have hν0 : 0 ≤ Centered.nu w μ := mul_nonneg hw.1.le (pow_nonneg hμ.1.le 4)
  have hν1 : Centered.nu w μ ≤ 1 := by
    exact (mul_le_of_le_one_right hw.1.le (pow_le_one₀ hμ.1.le hμ1)).trans hw1
  have hδ0 : 0 ≤ Centered.delta w μ := pow_nonneg hν0 8
  have hδ1 : Centered.delta w μ ≤ 1 := pow_le_one₀ hν0 hν1
  constructor
  · unfold Centered.etaStar
    positivity
  · have hb := pow_le_one₀ hδ0 hδ1 (n := 4)
    unfold Centered.etaStar
    linarith only [hb]

/-- The executable quartic has precisely the homogeneity, error, and coefficient magnitude
premises needed before canonical fixed-grid rounding. -/
theorem prepared_quartic (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    let A := ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0
    let Q := (run F MC (args k ps x h P, fuel)).toPoly d
    Q.IsHomogeneous 4 ∧
      IsSumSq (MvPolynomial.C
        (Centered.etaStar ((ps h).w / 2) (ps h).subspaceAccuracy : ℝ) * nsq ^ 4 -
          (SoS.toReal Q - Centered.phi4 A.model) ^ 2) ∧
      ∀ α, |Q.coeff α| ≤ 20 / ((ps h).w / 2) ^ 2 := by
  have hc := prepared_certificate F hF MC hMC ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  have hd := SpecFrame.prepared_data F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  dsimp only at hc hd ⊢
  rw [population_fourth _ hd.2.1] at hc
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, hμ, hμ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, _, _, hη, _⟩ := hm
  rw [hη] at hc
  have hπ : 0 < (ps h).w / 2 ∧ (ps h).w / 2 ≤ 1 / 2 :=
    ⟨by positivity, by linarith only [hw2]⟩
  have hμ64 : (ps h).subspaceAccuracy ≤ 1 / 64 := hμ100.trans (by norm_num)
  have he := eta_bounds ((ps h).w / 2) (ps h).subspaceAccuracy hπ ⟨hμ, hμ64⟩
  have hπR : (((ps h).w / 2 : ℚ) : ℝ) ≤ 1 / 2 := by
    have hc := Rat.cast_le (K := ℝ) |>.mpr hπ.2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc ⊢
    exact hc
  have heR : 0 ≤ (Centered.etaStar ((ps h).w / 2) (ps h).subspaceAccuracy : ℝ) ∧
      (Centered.etaStar ((ps h).w / 2) (ps h).subspaceAccuracy : ℝ) ≤ 1 := by
    exact_mod_cast he
  refine ⟨MvPolynomial.IsHomogeneous.of_map (algebraMap ℚ ℝ).injective hc.1,
    hc.2, ?_⟩
  intro α
  have hb := Centered.coefficient_bound _ _ _ _ _ _ hd hπR heR hc.1 hc.2 α
  rw [SoS.toReal, MvPolynomial.coeff_map] at hb
  change |(((run F MC (args k ps x h P, fuel)).toPoly d).coeff α : ℝ)| ≤
    20 / (((ps h).w / 2 : ℚ) : ℝ) ^ 2 at hb
  exact_mod_cast hb

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecMoments
