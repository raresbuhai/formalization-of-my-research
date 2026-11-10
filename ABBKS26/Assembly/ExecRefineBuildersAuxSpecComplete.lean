module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecGeometry
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecTransport

/-! Separator completeness for the executable centered direction program. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecComplete

open Common Centered Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders FrameAux.Linear

noncomputable section

variable {n k d : ℕ}

theorem prepared_thin (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI)
    (hcard : 2 ≤ I.card) :
    ∃ (i : Fin I.card) (v : Vec d), sqnorm v = 1 ∧
      qform ((ABBKS26.RefineAux.affineReference
        (ABBKS26.RefineAux.roundedReference M ω r P I hI)
        ((SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model.cov i)
          v ≤ 3 * ((ps h).subspaceAccuracy : ℝ) ^ 8 := by
  let T := (SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)
  let G := (ABBKS26.RefineAux.affineReference
    (ABBKS26.RefineAux.roundedReference M ω r P I hI) T 0).model
  have hdata := SpecFrame.prepared_data F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  have hT : T.det ≠ 0 := by
    let i : Fin I.card := ⟨0, by omega⟩
    have hpos := hdata.1.2.2.2 i
    change (T * M.S (ABBKS26.RefineAux.component I i) * Tᵀ).PosDef at hpos
    have hd := hpos.det_pos.ne'
    intro hz
    rw [det_mul, det_mul, det_transpose, hz] at hd
    simp only [zero_mul, mul_zero, ne_eq, not_true_eq_false] at hd
  have hseparated := hp.separated_at .centered M ε w η Δ D ω r ps h (by omega)
  have hsep (a b : Fin I.card) (hab : a ≠ b) :
      CenteredSeparated (ps h).separation (G.cov a) (G.cov b) := by
    apply (Separation.centeredSeparated_congr (isUnit_iff_ne_zero.mpr hT)).mpr
    exact hseparated _ _ ((I.orderEmbOfFin rfl).injective.ne hab)
  exact SpecGeometry.thin G (ps h) k (ps (h + 1))
    (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh) hcard hdata hsep

theorem transpose_rep (F : FrameCode) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    RepT (SpecProgram.transposeFrame F (args k ps x h P, fuel))
      (SpecFrame.frame F (ps h) x fuel P).transformᵀ := by
  rw [SpecFrame.frame_agrees F ps x fuel h P hh]
  intro i j
  change ent (SpecProgram.transposeFrame F (args k ps x h P, fuel)) i j =
    (frameOf d (F.run .centered (FrobFar.callArgs (args k ps x h P, fuel)))).transform j i
  dsimp only [SpecProgram.transposeFrame, RoundProgram.table, ent, args, frameOf, matrixOf]
  rw [getD_map_range _ _ i.isLt, getD_map_range _ _ j.isLt]

theorem rounded_deviations (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI)
    (NC : NestedCode) (MC : MomentCode) (RC : RoundCode)
    (uL : Vector)
    (huL : uL ∈ SpecFuel.grid (SpecProgram.normalized F MC NC RC)
      (args k ps x h P, fuel))
    (hnu : sqnorm (fun c ↦ (vectorOf d uL c : ℝ)) ≤ 4)
    (hnorm : |‖WithLp.toLp 2 (fun c ↦ (vectorOf d uL c : ℝ))‖ - 1| ≤
      ((ps h).subspaceAccuracy : ℝ) / 4)
    (i : Fin I.card) (v : Vec d)
    (ht : qform ((ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((SpecFrame.frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model.cov i)
        v ≤ 3 * ((ps h).subspaceAccuracy : ℝ) ^ 8)
    (hnear : ‖WithLp.toLp 2 (fun c ↦ (vectorOf d uL c : ℝ)) - WithLp.toLp 2 v‖ ≤
      33 * ((ps h).subspaceAccuracy : ℝ)) :
    let a := (args k ps x h P, fuel)
    ∃ bL ∈ SpecProgram.directions F MC NC RC a,
      let b := SpecDirection.rounded (SpecGuard.precision a) (SpecGuard.exponent a)
        (vectorOf d bL)
      let σ := fun j ↦ Real.sqrt (qform (M.S (ABBKS26.RefineAux.component I j))
        (fun c ↦ (b c : ℝ)))
      (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ 2 * (sqrtUp (4 / (ps h).w) : ℝ)) ∧
        (∃ j, σ j ≤ 64 * (4 / (ps h).w : ℝ) * (ps h).subspaceAccuracy) ∧
        (∃ j, 1 / 2 < σ j) := by
  let a := (args k ps x h P, fuel)
  let u := vectorOf d uL
  let T := (SpecFrame.frame F (ps h) x fuel P).transform
  let G := (ABBKS26.RefineAux.affineReference
    (ABBKS26.RefineAux.roundedReference M ω r P I hI) (T.map (algebraMap ℚ ℝ)) 0).model
  let bL := mulVecL d (SpecProgram.transposeFrame F a) uL
  have hb : vectorOf d bL = Tᵀ *ᵥ u := by
    funext c
    exact mulVecL_rep (transpose_rep F ps x fuel h P (by omega)) (fun _ ↦ rfl) c
  have hmag : ∀ c, |vectorOf d bL c| ≤ (2 : ℚ) ^ SpecGuard.exponent a := by
    rw [hb]
    exact SpecDirection.prepared_magnitude F hF ps x fuel h P M ε w η Δ D ω r I hI
      hx hp hf hh hl hP hnf u hnu
  have herror := SpecDirection.prepared_covariance_error ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hh hl hP (vectorOf d bL) hmag
  have hbcast : (fun c ↦ (vectorOf d bL c : ℝ)) =
      (T.map (algebraMap ℚ ℝ))ᵀ *ᵥ (fun c ↦ (u c : ℝ)) := by
    rw [hb, ← transpose_map]
    funext c
    exact (algebraMap ℚ ℝ).map_mulVec Tᵀ u c
  have hform (j : Fin I.card) :
      qform (M.S (ABBKS26.RefineAux.component I j)) (fun c ↦ (vectorOf d bL c : ℝ)) =
        qform (G.cov j) (fun c ↦ (u c : ℝ)) := by
    rw [hbcast]
    exact (Separation.dotProduct_congr_mulVec _ _ _).symm
  have hdata := SpecFrame.prepared_data F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hdev := SpecGeometry.deviations G
    (fun j ↦ M.S (ABBKS26.RefineAux.component I j)) (ps h) hdata ⟨hs.1, hs.2.1⟩
    ⟨hs.2.2.1, hs.2.2.2.1⟩ (fun j ↦ hp.1.posDef _)
    (fun c ↦ (u c : ℝ)) (fun c ↦ (vectorOf d bL c : ℝ))
    (fun c ↦ (SpecDirection.rounded (SpecGuard.precision a) (SpecGuard.exponent a)
      (vectorOf d bL) c : ℝ)) v i ht hnorm hnear hform
    (fun j ↦ herror _ (I.orderEmbOfFin_mem rfl j))
  refine ⟨bL, ?_, hdev⟩
  unfold SpecProgram.directions
  rw [ite_eq_left (show a.1.2.2.2.2.1 < a.1.2.1 by change h < k; omega)]
  exact List.mem_map.mpr ⟨uL, huL, rfl⟩
/-- A rounded variance gap supplies a pair on the fixed window grid that verifies. -/
theorem separator (F : FrameCode) (MC : MomentCode) (NC : NestedCode) (RC : RoundCode)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hcard : 2 ≤ I.card) (bL : Vector)
    (hmem : bL ∈ SpecProgram.directions F MC NC RC (args k ps x h P, fuel))
    (hdev : let a := (args k ps x h P, fuel)
      let b := SpecDirection.rounded (SpecGuard.precision a) (SpecGuard.exponent a)
        (vectorOf d bL)
      let σ := fun j ↦ Real.sqrt (qform (M.S (ABBKS26.RefineAux.component I j))
        (fun c ↦ (b c : ℝ)))
      (∀ j, 0 < σ j) ∧ (∀ j, σ j ≤ 2 * (sqrtUp (4 / (ps h).w) : ℝ)) ∧
        (∃ j, σ j ≤ 64 * (4 / (ps h).w : ℝ) * (ps h).subspaceAccuracy) ∧
        (∃ j, 1 / 2 < σ j)) :
    let a := (args k ps x h P, fuel)
    ∃ q ∈ (SpecGuard.run (SpecProgram.directions F MC NC RC) a).1.map (statisticOf d),
      ∃ t ∈ SpecWindows.run a, Verify (ps h) x (pairEdge .centered h P q t) := by
  let a := (args k ps x h P, fuel)
  let p := ps h
  let b := SpecDirection.rounded (SpecGuard.precision a) (SpecGuard.exponent a)
    (vectorOf d bL)
  let σ := fun j ↦ Real.sqrt (qform (M.S (ABBKS26.RefineAux.component I j))
    (fun c ↦ (b c : ℝ)))
  obtain ⟨hσ, hupper, hsmall, hlarge⟩ := hdev
  obtain ⟨hw, hβ, hK, ht, hbudget, htail⟩ := RefineBlocksAux.centered_budget
    M ε w η Δ D ω r ps hp h hh I.card hcard (by simpa using Finset.card_le_univ I)
  obtain ⟨j, hj, hside, hlo, hhi⟩ := RefineBlocksAux.spectral_grid p σ
    hcard hw hβ hK ht hbudget hupper hsmall hlarge
  let t : ℚ := 2 * sqrtUp (4 / p.w) / 2 ^ j
  let R : ℝ := 8 / p.tail
  have ht0 : 0 < t := by dsimp only [t]; unfold sqrtUp; positivity
  have htail0 : (0 : ℝ) < p.tail := by exact_mod_cast ht.1
  have hR : 1 ≤ R := by
    dsimp only [R]
    rw [le_div_iff₀ htail0]
    have ht1 : (p.tail : ℝ) ≤ 1 := by exact_mod_cast ht.2
    linarith only [ht1]
  have hsq (i : Fin I.card) : σ i ^ 2 =
      qform (M.S (ABBKS26.RefineAux.component I i)) (fun c ↦ (b c : ℝ)) :=
    Real.sq_sqrt (Real.sqrt_pos.mp (hσ i)).le
  have htR : (0 : ℝ) < t := by exact_mod_cast ht0
  have hK0 : (0 : ℝ) < p.K := by exact_mod_cast zero_lt_one.trans_le hK
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hlow (i) (hi : σ i ≤ (t : ℝ) / (2 * p.K * R)) :
      qform (M.S (ABBKS26.RefineAux.component I i)) (fun c ↦ (b c : ℝ)) ≤
        ((t : ℝ) / (2 * p.K * R)) ^ 2 := by
    rw [← hsq]
    exact pow_le_pow_left₀ (hσ i).le hi 2
  have hhigh (i) (hi : (t : ℝ) * p.K * R ≤ σ i) :
      ((t : ℝ) * p.K * R) ^ 2 ≤
        qform (M.S (ABBKS26.RefineAux.component I i)) (fun c ↦ (b c : ℝ)) := by
    rw [← hsq]
    exact pow_le_pow_left₀ (by positivity) hi 2
  have hpre (j : Fin k) (hj : j ∈ I) :
      ∃ i : Fin I.card, ABBKS26.RefineAux.component I i = j := by
    have hj' : j ∈ Set.range (I.orderEmbOfFin rfl) := by
      rw [I.range_orderEmbOfFin]
      exact hj
    exact hj'
  obtain ⟨J, hpop⟩ := RefineAux.buffered_spectral_recorded M I p P η h b t R
    hp.1 hp.2.1 ht0 hK ⟨hp.2.2.2.2.2.2.1.le, hp.2.2.2.2.2.2.2.1⟩ hR htail
    (fun j hj ↦ by
      obtain ⟨i, rfl⟩ := hpre j hj
      exact (hside i).imp (hlow i) (hhigh i))
    (by
      obtain ⟨i, hi⟩ := hlo
      exact ⟨ABBKS26.RefineAux.component I i, I.orderEmbOfFin_mem rfl i, hlow i hi⟩)
    (by
      obtain ⟨i, hi⟩ := hhi
      exact ⟨ABBKS26.RefineAux.component I i, I.orderEmbOfFin_mem rfl i, hhigh i hi⟩)
  let q : Statistic d := ⟨vecMulVec b b, 0, 0⟩
  let win : Window := (t ^ 2, t ^ 2 / p.K ^ 2, t ^ 2 * p.K ^ 2)
  have hdecode : statisticOf d
      (SpecSquare.run d (SpecGuard.precision a) (SpecGuard.exponent a) bL) = q :=
    SpecSquare.decoded d (SpecGuard.precision a) (SpecGuard.exponent a) bL
  have hq : q ∈ (SpecGuard.run (SpecProgram.directions F MC NC RC) a).1.map
      (statisticOf d) := by
    rw [← hdecode]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨bL, hmem, rfl⟩, rfl⟩
  have hwin : win ∈ SpecWindows.run a := by
    rw [SpecWindows.agrees k ps x fuel h P (by omega)]
    apply List.mem_map.mpr
    refine ⟨t ^ 2, List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, rfl⟩
  refine ⟨q, hq, win, hwin, ?_⟩
  rw [hx]
  exact hp.verify_of_bufferedComplete .centered M ε w η Δ D ω r ps h hh
    (pairEdge .centered h P q win) I J hI hl hP hpop
/-- Completeness of the concrete program, including its bounded statistic rounding. -/
theorem complete (F : FrameCode) (hF : FrameSpec F)
    (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode) (hNC : NestedSpec NC)
    (RC : RoundCode) (hRC : RoundSpecL RC) :
    SpecGuard.Complete F (SpecProgram.directions F MC NC RC) := by
  intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP hcard hnf
  obtain ⟨i, v, hv, ht⟩ := prepared_thin F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf hcard
  obtain ⟨uL, huL, hnu, hnorm, hnear⟩ := SpecTransport.prepared_cover F hF MC hMC NC hNC
    RC hRC ps x fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf i v hv ht
  obtain ⟨bL, hmem, hdev⟩ := rounded_deviations F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf NC MC RC uL huL hnu hnorm i v ht hnear
  exact separator F MC NC RC ps x fuel h P M ε w η Δ D ω r I hI hx hp hh hl hP
    hcard bL hmem hdev

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecComplete
