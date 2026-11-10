module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdCenter

/-! Prepared accuracy of the executable common-covariance frame and center. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdFrame

open Common Matrix FrameAux.Linear
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

theorem isotropy_le_one (mode : Mode) (k : ℕ) (p next : StepParams)
    (hp : StepReady mode k p next) : p.isotropy ≤ 1 := by
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hp
  have hβ1 : p.subspaceAccuracy ≤ 1 := hβ100.trans (by norm_num)
  cases mode with
  | centered =>
    obtain ⟨_, _, _, _, _, _, _, _, hγ, _⟩ := hm
    rw [hγ]
    have hw1 : p.w / 2 ≤ 1 := by linarith only [hw2]
    have hν : Centered.nu (p.w / 2) p.subspaceAccuracy ≤ 1 := by
      calc
        _ ≤ p.w / 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hβ.le hβ1) (by positivity)
        _ ≤ 1 := by simpa only [mul_one] using hw1
    have hν0 : 0 ≤ Centered.nu (p.w / 2) p.subspaceAccuracy := by
      unfold Centered.nu
      positivity
    have hδ := pow_le_one₀ hν0 hν (n := 8)
    have hδ0 := pow_nonneg hν0 8
    have hγ := pow_le_one₀ hδ0 hδ (n := 2)
    change Centered.delta (p.w / 2) p.subspaceAccuracy ^ 2 ≤ 1 at hγ
    change Centered.delta (p.w / 2) p.subspaceAccuracy ^ 2 / 20 ≤ 1
    linarith only [hγ]
  | identical =>
    obtain ⟨_, _, _, hγ, _⟩ := hm
    rw [hγ]
    have hβ25 : p.subspaceAccuracy / 25 ≤ 1 := by linarith only [hβ1]
    have hpow := pow_le_one₀ (div_nonneg hβ.le (by norm_num)) hβ25 (n := 8)
    change (p.subspaceAccuracy / 25) ^ 8 / 6 ≤ 1
    linarith only [hpow]

theorem eta_contamination
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1) :
    8 * η ≤ (params h).contamination := by
  have hl := hp.leakageBudget_nonneg mode M ε w η Δ D ω r params h (by omega)
  have hwcast := hp.weight_at mode M ε w η Δ D ω r params h (by omega)
  obtain ⟨_, _, _, hw, _, hε, hη, _, _, _, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨_, hw2, _⟩ := hready h hh
  have hw1 : w ≤ 1 := by
    have hwR := Rat.cast_le (K := ℝ) |>.mpr hw2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hwR
    linarith only [hwR, hwcast]
  obtain ⟨_, hleak, hc, _⟩ := hparams h (by omega)
  have hleak0 : (0 : ℝ) ≤ (params h).leakage := hl.trans hleak
  have he := (div_le_iff₀ hw).mp hc
  have hn : (0 : ℝ) ≤ 1 / n := by positivity
  have hc0 : (0 : ℝ) ≤ (params h).contamination := by
    have hnum : 0 ≤ 8 * ((params h).leakage + ε + η + 1 / n) / w := by positivity
    exact hnum.trans hc
  have hm := mul_le_mul_of_nonneg_left hw1 hc0
  linarith only [he, hm, hleak0, hε, hn]


def frame (p : StepParams) (x : Fin n → Fin d → ℚ) (fuel : ℕ)
    (P : Finset (Fin n)) : Robust.FrameResult d :=
  FrameProgram.decode d (FrameProgram.run .identical
    ((d, (P.sort (· ≤ ·)).map fun l ↦ List.ofFn (x l), p.w / 2, |p.R|,
      p.frameAccuracy), fuel))

theorem frame_agrees (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    frame (ps h) x fuel P = FrameProgram.decode d
      (IdCenter.run (args k ps x h P, fuel)) := by
  unfold IdCenter.run
  rw [FrobFar.callArgs_agrees k ps x fuel h P hh]
  rfl

private theorem loop_hypotheses
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card) :
    let p := params h
    let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
    R.Valid (((p.w / 2 : ℚ) : ℝ)) ∧ R.Resilient 4 (1 / 10000) ∧
      ((p.w / 2 : ℚ) : ℝ) ≤ 1 ∧ 0 < ((p.isotropy / 10000 : ℚ) : ℝ) ∧
      R.contamination ≤ min
        (Robust.maxContamination ((p.w / 2 : ℚ) : ℝ) (|p.R| : ℚ))
        (((p.w / 2 : ℚ) : ℝ) / 400) := by
  let p := params h
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  have hweight := hp.weight_at mode M ε w η Δ D ω r params h (by omega)
  have hv := hp.reference_valid_at mode M ε w η Δ D ω r params N I hI
  have hres := hp.reference_resilient_at mode M ε w η Δ D ω r params N I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree mode M ε w η Δ D ω r params)) (by decide)
  have hc := hp.contamination_at mode M ε w η Δ D ω r params h (by omega)
    N I hI hl hN
  change R.contamination ≤ (p.contamination : ℝ) at hc
  obtain ⟨_, _, _, _, _, _, _, hη100, _, _, _, _, _, _, hready, _⟩ := hp
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, hζ, hζle, _⟩ :=
    hready h hh
  have hσeq : p.sigmaSq = 600 / (p.w / 2) ^ 2 + 2 * p.R ^ 2 := hσ
  have hreqσ := hreq.trans (min_le_left _ _)
  have hreqw := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hv' : R.Valid ((p.w / 2 : ℚ) : ℝ) := by
    rw [Rat.cast_div, Rat.cast_ofNat, hweight]
    exact hv
  refine ⟨hv', ?_, ?_, ?_, ?_⟩
  · apply ABBKS26.RefineAux.resilient_tolerance_mono R 4 _ _ hres
    linarith only [hη100]
  · have hhQ : p.w / 2 ≤ 1 := by linarith only [hw2]
    exact_mod_cast hhQ
  · have hpos : 0 < p.isotropy / 10000 := by linarith only [hζ, hζle]
    exact_mod_cast hpos
  · apply le_min
    · apply hc.trans
      unfold Robust.maxContamination
      rw [ABBKS26.RefineAux.frame_sigmaSq p hσeq]
      exact_mod_cast hreqσ
    · apply hc.trans
      have hhR := Rat.cast_le (K := ℝ) |>.mpr hreqw
      push_cast at hhR ⊢
      simpa only [div_div, show (2 : ℝ) * 400 = 800 by norm_num] using hhR


/-- The actual rational filter returns a close frame and an accurate common center. -/
theorem prepared (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    let Y := frame (ps h) x fuel P
    let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
    let T := Y.transform.map (algebraMap ℚ ℝ)
    Robust.CloseFrame ref Y ((ps h).w / 2 : ℚ) (|(ps h).R| : ℚ)
      (((ps h).isotropy / 10000 : ℚ) : ℝ) ∧
      sqnorm (T *ᵥ ((fun i ↦ (Y.center i : ℝ)) - ref.mean)) ≤
        400 * (ps h).contamination := by
  subst x
  let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let p := ps h
  let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let pts := (P.sort (· ≤ ·)).map fun l ↦ List.ofFn (x l)
  let Y := frame p x fuel P
  let T := Y.transform.map (algebraMap ℚ ℝ)
  have hpts : pts = ABBKS26.RefineAux.blockInput x P := by
    dsimp only [pts, ABBKS26.RefineAux.blockInput]
    rw [← P.listMap_orderEmbOfFin_finRange rfl]
    simp only [List.map_map, List.ofFn_eq_map]
    rfl
  have hlen : pts.length = P.card := by simp [pts]
  have hrep : Robust.Represents ref pts := by
    rw [hpts]
    exact ABBKS26.RefineAux.blockInput_represents M ω r P I hI
  obtain ⟨hv, hr, hπ1, _, he⟩ := loop_hypotheses .identical M ε w η Δ D ω r ps hp
    h hh P I hI hl hP
  have hres := hp.reference_resilient_at .identical M ε w η Δ D ω r ps P I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .identical M ε w η Δ D ω r ps)) (by decide)
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, _, _, hζ, hζle, _⟩ := hs
  have hr' : ref.Resilient 4
      (min (1 / 10 ^ 8) ((p.frameAccuracy : ℝ) ^ 2 / 10 ^ 8)) := by
    apply ABBKS26.RefineAux.resilient_tolerance_mono ref 4 _ _ hres
    apply le_min
    · linarith only [hp.2.2.2.2.2.2.2.1]
    · exact div_le_div_of_nonneg_right
        (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h (by omega)).2.2.2.2.2.1 (by norm_num)
  have hmax0 : 0 < Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) := by
    unfold Robust.maxContamination Robust.sigmaSq
    have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw
    push_cast
    positivity
  have hP0 : (0 : ℝ) < P.card := by
    exact lt_of_lt_of_le (by linarith only [hp.2.2.2.2.2.2.2.2.2.2.2.2.1] :
      0 < w * n / 4) hP
  have hn : 2 / Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) ≤
      (pts.length : ℝ) := by
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
      _ ≤ localBudget .identical k n d ps := by
        unfold localBudget
        exact (Nat.le_mul_of_pos_left _ (by positivity)).trans
          (Nat.le_mul_of_pos_right _ (by positivity))
  have hid (i j : Fin I.card) : ref.model.cov i = ref.model.cov j :=
    hp.2.1 _ _
  obtain ⟨idx, hc, hpass, hp'⟩ := IdCenter.clean_pass ref pts (p.w / 2) |p.R|
    p.frameAccuracy fuel hrep hv hr' (by positivity) (by linarith only [hw2])
    (abs_nonneg _) hζ he hn hfu hid
  have hclose : Robust.CloseFrame ref Y (p.w / 2 : ℚ) (|p.R| : ℚ) p.frameAccuracy := by
    change Robust.CloseFrame ref (frame p x fuel P) _ _ _
    unfold frame
    rw [FrameProgram.rounded_frame_agrees]
    refine ⟨hpass, ?_⟩
    exact FrameAux.Linear.normalizedL_pass ref _ _ _ _ _ hc.positive hζ
      hc.covariance_agrees (by
        rw [FrameProgram.liftState, FrameProgram.iterationFrame,
          FrameAux.Linear.matrixOf_whitenL]) hc.invariant hc.normalized he hp'
  have hclose' : Robust.CloseFrame ref Y (p.w / 2 : ℚ) (|p.R| : ℚ)
      (((p.isotropy / 10000 : ℚ) : ℝ)) :=
    SpecFrame.close_accuracy_mono _ _ _ _ _ _
      (by exact_mod_cast hζ.le) (by exact_mod_cast hζle) hclose
  have herr := hp.close_frame_error_at .identical M ε w η Δ D ω r ps h hh
    P I hI hl hP Y hclose'
  have hγ : (p.isotropy : ℝ) ≤ 1 := by
    exact_mod_cast isotropy_le_one .identical k _ _
      (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh)
  have herr' : frobSq (T * ref.cov * Tᵀ - 1) ≤ (1 / 100 : ℝ) ^ 2 := by
    apply herr.trans
    have hγ0 : (0 : ℝ) ≤ (ps h).isotropy := by
      exact_mod_cast (show 0 ≤ (ps h).isotropy by linarith only [hζ, hζle])
    apply pow_le_pow_left₀ (div_nonneg hγ0 (by norm_num))
    linarith only [hγ]
  have hupper := (ABBKS26.RefineAux.empirical_frame_bounds ref.cov T
    hv.2.2.2.2.2.1.posSemidef herr').2
  have hb := IdCenter.center_bound ref pts (p.w / 2) |p.R| p.frameAccuracy fuel
    hrep hv hr' (by positivity) (by linarith only [hw2]) (abs_nonneg _) hζ he hn hfu hid
    T hupper
  have hcont := hp.contamination_at .identical M ε w η Δ D ω r ps h (by omega)
    P I hI hl hP
  exact ⟨hclose', hb.2.trans (mul_le_mul_of_nonneg_left hcont (by norm_num))⟩

end

end ABBKS26.Assembly.Exec.RefineSynth.IdFrame
