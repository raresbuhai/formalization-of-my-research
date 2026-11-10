module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobFar

/-!
# Clean-frame consequences for the shared executable spectral call

The arbitrary `FrameSpec` supplies both aggregate accuracy and the scheduled component
bound in the non-FAR case. Together these give Theorem Z's `Centered.DataValid` premise.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecFrame

open Common _root_.ABBKS26.Tree Matrix Sources Builders

noncomputable section

variable {n k d : ℕ}

/-- The decoded frame uses precisely the call shared with the Frobenius source. -/
def frame (F : FrameCode) (p : StepParams) (x : Fin n → Fin d → ℚ)
    (fuel : ℕ) (P : Finset (Fin n)) : Robust.FrameResult d :=
  frameProc F d ((P.sort (· ≤ ·)).map fun l ↦ List.ofFn (x l)) .centered
    (p.w / 2) |p.R| p.frameAccuracy fuel

theorem frame_agrees (F : FrameCode) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    frame F (ps h) x fuel P = frameOf d
      (F.run .centered (FrobFar.callArgs (args k ps x h P, fuel))) := by
  rw [FrobFar.callArgs_agrees k ps x fuel h P hh]
  rfl

/-- The shared executable call is close on every prepared non-FAR parent. -/
theorem prepared_close (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      (frame F (ps h) x fuel P) ((ps h).w / 2 : ℚ) (|(ps h).R| : ℚ)
      ((ps h).frameAccuracy : ℝ) := by
  subst x
  let p := ps h
  let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let pts := (P.sort (· ≤ ·)).map fun l ↦
    List.ofFn fun i ↦ r ((ω l).1, (ω l).2.2) i
  have hpts : pts = ABBKS26.RefineAux.blockInput
      (fun l i ↦ r ((ω l).1, (ω l).2.2) i) P := by
    dsimp only [pts, ABBKS26.RefineAux.blockInput]
    rw [← P.listMap_orderEmbOfFin_finRange rfl]
    simp only [List.map_map, List.ofFn_eq_map]
    rfl
  have hlen : pts.length = P.card := by simp [pts]
  have hrep : Robust.Represents ref pts := by
    rw [hpts]
    exact ABBKS26.RefineAux.blockInput_represents M ω r P I hI
  have hcompat := hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh P I hI hl hP
  have hres := hp.reference_resilient_at .centered M ε w η Δ D ω r ps P I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .centered M ε w η Δ D ω r ps)) (by decide)
  have hcont := hp.contamination_at .centered M ε w η Δ D ω r ps h (by omega)
    P I hI hl hP
  obtain ⟨_, hcenter, _, hwR, _, _, _, hη100, _, hg, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, _, hreq, hζ, _⟩ := hready h hh
  have hηζ := (hparams h (by omega)).2.2.2.2.2.1
  have hres' : ref.Resilient 4
      (min (1 / 10 ^ 8) ((p.frameAccuracy : ℝ) ^ 2 / 10 ^ 8)) := by
    apply ABBKS26.RefineAux.resilient_tolerance_mono ref 4 _ _ hres
    apply le_min
    · linarith only [hη100]
    · exact div_le_div_of_nonneg_right hηζ (by norm_num)
  have he : ref.contamination ≤ min (Robust.maxContamination
      (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ)) (((p.w / 2 : ℚ) : ℝ) / 400) := by
    apply le_min hcompat.1.2.2.2.2.2
    apply hcont.trans
    have hb := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hbR : (p.contamination : ℝ) ≤ (p.w : ℝ) / 800 := by exact_mod_cast hb
    push_cast
    simpa only [div_div, show (2 : ℝ) * 400 = 800 by norm_num] using hbR
  have hmax0 : 0 < Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) := by
    unfold Robust.maxContamination Robust.sigmaSq
    have hw' : (0 : ℝ) < p.w := by exact_mod_cast hw
    push_cast
    positivity
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (SoundAux.good_cluster_pos M ε w η D ω hg hI.choose).trans_le
      ((Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n))
  have hP0 : (0 : ℝ) < P.card := (by positivity : 0 < w * n / 4).trans_le hP
  have hn : 2 / Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) ≤
      pts.length := by
    rw [hlen, div_le_iff₀ hmax0]
    have hfinite : 2 / (P.card : ℝ) ≤ ref.contamination :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hb := (div_le_iff₀ hP0).mp (hfinite.trans (he.trans (min_le_left _ _)))
    linarith only [hb]
  have hfu : (pts.length + d + 2) ^ 100 ≤ fuel := by
    apply le_trans _ hf
    have hc : P.card ≤ n := (Finset.card_le_univ P).trans_eq (Fintype.card_fin n)
    rw [hlen]
    calc
      _ ≤ (n + d + 2) ^ 100 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ localBudget .centered k n d ps := by
        simp only [localBudget, ite_true, mul_one]
        exact Nat.le_mul_of_pos_left _ (by positivity)
  have hc := hF.contract.2 ref pts .centered (p.w / 2) |p.R| p.frameAccuracy fuel
    hrep hcompat.1.1 hres' (by positivity) (by linarith only [hw2]) (abs_nonneg _) hζ
    (fun _ j ↦ hcenter _) he hn hfu
  exact hc.1.resolve_left hnf

/-- The larger accuracy used by the existing population lemmas is also available. -/
theorem close_accuracy_mono {m : ℕ} (D : Robust.Reference n m d)
    (Y : Robust.FrameResult d) (π R ζ ζ' : ℝ) (hζ : 0 ≤ ζ) (hζ' : ζ ≤ ζ')
    (hc : Robust.CloseFrame D Y π R ζ) : Robust.CloseFrame D Y π R ζ' := by
  refine ⟨hc.1, hc.2.trans ?_⟩
  apply pow_le_pow_left₀ (by positivity)
  linarith only [hζ']

/-- With the component bound stated explicitly, the shared frame supplies all of
`Centered.DataValid`. No concrete-loop property is assumed of an arbitrary `FrameCode`. -/
theorem prepared_data_of_component_bound (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) (rF : ℝ)
    (hcomp : ∀ j, frobSq ((ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model.cov j - 1) ≤
        rF) :
    Centered.DataValid (ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model
      ((ps h).w / 2 : ℚ) (ps h).isotropy rF := by
  have hc := prepared_close F hF ps x fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP hnf
  have hstep := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, hζ, hζle, hm⟩ := hstep
  have hc' : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      (frame F (ps h) x fuel P) ((ps h).w / 2 : ℚ) (|(ps h).R| : ℚ)
      (((ps h).isotropy / 10000 : ℚ) : ℝ) :=
    close_accuracy_mono _ _ _ _ _ _
      (by exact_mod_cast hζ.le) (by exact_mod_cast hζle) hc
  subst x
  let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let Y := frame F (ps h) (fun l i ↦ r ((ω l).1, (ω l).2.2) i) fuel P
  let T := Y.transform.map (algebraMap ℚ ℝ)
  have hT := (hp.frame_population_cov_at .centered M ε w η Δ D ω r ps h hh P I hI
    hl hP Y hc').1
  have hv := (hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh P I hI hl hP).1.1
  have hvalid := ABBKS26.RefineAux.affineReference_valid ref T 0 _ hv hT
  have hiso := hp.centered_isotropic_at M ε w η Δ D ω r ps h hh P I hI hl hP Y hc'
  have hγsmall : (ps h).isotropy ≤ ((ps h).w / 2) / 20 := by
    obtain ⟨_, _, _, _, _, _, _, _, hγeq, _⟩ := hm
    rw [hγeq]
    exact ABBKS26.RefineAux.centered_gamma_le ((ps h).w / 2) (ps h).subspaceAccuracy
      ⟨by positivity, by linarith only [hw2]⟩ ⟨hβ, by linarith only [hβ100]⟩
  have hγ : (ps h).isotropy ≤ (1 / 10 : ℚ) := by linarith only [hγsmall, hw2]
  have hγR : ((ps h).isotropy : ℝ) ≤ 1 / 10 := by
    have hb := Rat.cast_le (K := ℝ) |>.mpr hγ
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hb
    exact hb
  refine ⟨hvalid.1, ?_, hiso, hγR, hcomp⟩
  intro j
  change T *ᵥ (M.μ (ABBKS26.RefineAux.component I j) - 0) = 0
  rw [hp.2.1 _, sub_self, mulVec_zero]

/-- The executable CLOSE guarantee supplies all data required by the spectral theorem. -/
theorem prepared_data (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI) :
    Centered.DataValid (ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      ((frame F (ps h) x fuel P).transform.map (algebraMap ℚ ℝ)) 0).model
      ((ps h).w / 2 : ℚ) (ps h).isotropy
      ((10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10 : ℚ) : ℝ) := by
  apply prepared_data_of_component_bound F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  subst x
  exact hF.component_bound M ε w η Δ D ω r ps hp h hh fuel hf P I hI hl hP hnf

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecFrame
