module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobFar

/-! Removing affine terms from centered Frobenius certificates. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobPure

open Common _root_.ABBKS26.Tree Matrix Sources Builders
open Turing.MultiTapeTM ComputableInPolyTime

/-- Centered component center gaps depend only on the quadratic part. -/
def pure {d : ℕ} (q : Statistic d) : Statistic d := ⟨q.A, 0, 0⟩

def pureL (d : ℕ) (q : StatisticL) : StatisticL :=
  ((FramePool.canonical d q).1, List.replicate d 0, 0)

theorem pure_symmetric {d : ℕ} (q : Statistic d) (hq : q.Aᵀ = q.A) :
    (pure q).Aᵀ = (pure q).A := hq

theorem pureL_agrees (d : ℕ) (q : StatisticL) :
    pureL d q = statisticList (pure (statisticOf d q)) := by
  rw [pureL, FramePool.canonical_agrees]
  simp only [statisticList, pure]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  · change List.replicate d 0 = List.ofFn (fun _ : Fin d ↦ (0 : ℚ))
    simp

theorem pureL_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {q : α → StatisticL}
    (hd : ComputableInPolyTime d input encUnary)
    (hq : ComputableInPolyTime q input encStatistic) :
    ComputableInPolyTime (fun a ↦ pureL (d a) (q a)) input encStatistic := by
  unfold pureL
  exact ((fst _ _).comp (FramePool.canonical_polytime hd hq)).prod
    ((replicate hd (const 0)).prod (const 0))

/-- Deleting the linear part decreases the actual centered Gaussian variance. -/
theorem variance_le {d : ℕ} (q : Statistic d) (hq : q.Aᵀ = q.A)
    (S : Mat d) (hS : S.PosSemidef) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) := by
  rw [Variance.centered_variance_eq (pure q) (pure_symmetric q hq) S hS,
    Variance.centered_variance_eq q hq S hS]
  have hnonneg := hS.dotProduct_mulVec_nonneg (fun i ↦ (q.b i : ℝ))
  simp only [pure, Pi.zero_apply, Rat.cast_zero]
  change _ + qform S 0 ≤ _ + qform S (fun i ↦ (q.b i : ℝ))
  simp only [qform, mulVec_zero, dotProduct_zero, add_zero, le_add_iff_nonneg_right]
  simpa only [star_trivial] using hnonneg

theorem center_gap {k d : ℕ} (M : FrameModel k d) (q : Statistic d)
    (hcenter : ∀ j, M.mean j = 0) (i j : Fin k) :
    Robust.statCenter M i (FrameProgram.quadOf d (statisticList (pure q))) -
      Robust.statCenter M j (FrameProgram.quadOf d (statisticList (pure q))) =
    Robust.statCenter M i (FrameProgram.quadOf d (statisticList q)) -
      Robust.statCenter M j (FrameProgram.quadOf d (statisticList q)) := by
  simp [Robust.statCenter, FrameProgram.quadOf, statisticList, pure, hcenter, qform]

/-- The replacement program drops both affine parts, preserving original paired flags. -/
def run (F : FrameCode) (a : Args) : PoolL :=
  (FrobFar.run F a).map fun q ↦ (pureL a.1.1 q.1, q.2)

theorem run_polytime (F : FrameCode) (hF : FrameSpec F) :
    ComputableInPolyTime (run F) encArgs encPool := by
  unfold run
  apply mapWithInput (FrobFar.run_polytime F hF)
  exact (pureL_polytime (by fun_prop) (by fun_prop)).prod (by fun_prop)

def pool {n d : ℕ} (F : FrameCode) (p : StepParams) (x : Fin n → Fin d → ℚ)
    (fuel : ℕ) (N : Finset (Fin n)) : List (Statistic d × Bool) :=
  (FrobFar.pool F p x fuel N).map fun q ↦ (pure q.1, q.2)

theorem run_agrees {n d : ℕ} (F : FrameCode) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n)) (hh : h < k) :
    run F (args k ps x h N, fuel) =
      (pool F (ps h) x fuel N).map (fun q ↦ (statisticList q.1, q.2)) := by
  unfold run pool
  rw [FrobFar.run_agrees F k ps x fuel h N hh]
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply]
  refine Prod.ext ?_ rfl
  change pureL d (statisticList q.1) = statisticList (pure q.1)
  rw [pureL_agrees, statistic_roundtrip]

/-- The specified precision must be supported by the reference resilience before the
frame contract can certify every eligible entry of the pure replacement program. -/
theorem specified_variance {n k d : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (D : Robust.Reference n k d) (pts : Points) (π R ζ : ℚ) (fuel : ℕ)
    (hrep : Robust.Represents D pts) (hD : D.Valid π)
    (hres : D.Resilient 4 (min (1 / 10 ^ 8) ((ζ : ℝ) ^ 2 / 10 ^ 8)))
    (hπ : 0 < π) (hπ2 : π ≤ 1 / 2) (hR : 0 ≤ R) (hζ : 0 < ζ)
    (hcenter : ∀ j, D.model.mean j = 0)
    (he : D.contamination ≤ min (Robust.maxContamination π R) ((π : ℝ) / 400))
    (hn : 2 / Robust.maxContamination π R ≤ pts.length)
    (hf : (pts.length + d + 2) ^ 100 ≤ fuel) (q : Statistic d)
    (hq : (q, true) ∈ FramePool.typed d (F.run .centered ((d, pts, π, R, ζ), fuel))) :
    ∀ j, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 (D.model.cov j)) ≤ (20 / (π : ℝ)) ^ 2 := by
  have hc := hF.contract.2 D pts .centered π R ζ fuel hrep hD hres hπ hπ2 hR hζ
    (fun _ ↦ hcenter) he hn hf
  have hS (j : Fin k) := (hD.1.2.2.2 j).posSemidef
  have hv := FrobVariance.specified_variance F hF .centered ((d, pts, π, R, ζ), fuel)
    D.model (20 / (π : ℝ)) hcenter hS hc.2.2 q hq
  have hsym := FrobVariance.paired_symmetric F hF .centered ((d, pts, π, R, ζ), fuel) q hq
  exact fun j ↦ (variance_le q hsym _ (hS j)).trans (hv j)

/-- Prepared precision supplies the resilience required by the specified frame contract.
Every eligible pure statistic is therefore valid, before or after the bit guard. -/
theorem prepared_variance {n k d : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card)
    (q : Statistic d) (hq : (q, true) ∈ pool F (ps h) x fuel N) :
    ∀ j ∈ I, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        (40 / ((ps h).w : ℝ)) ^ 2 := by
  subst x
  let p := ps h
  let ref := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let pts := (N.sort (· ≤ ·)).map fun l ↦
    List.ofFn fun i ↦ r ((ω l).1, (ω l).2.2) i
  have hpts : pts = ABBKS26.RefineAux.blockInput
      (fun l i ↦ r ((ω l).1, (ω l).2.2) i) N := by
    dsimp only [pts, ABBKS26.RefineAux.blockInput]
    rw [← N.listMap_orderEmbOfFin_finRange rfl]
    simp only [List.map_map, List.ofFn_eq_map]
    rfl
  have hlen : pts.length = N.card := by simp [pts]
  have hrep : Robust.Represents ref pts := by
    rw [hpts]
    exact ABBKS26.RefineAux.blockInput_represents M ω r N I hI
  have hvalid := (hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh N I hI hl hN).1.1
  have hres := hp.reference_resilient_at .centered M ε w η Δ D ω r ps N I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .centered M ε w η Δ D ω r ps)) (by decide)
  have hcont := hp.contamination_at .centered M ε w η Δ D ω r ps h (by omega)
    N I hI hl hN
  have hmax := (hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh N I hI hl hN).1.2.2.2.2.2
  obtain ⟨hM, hcenter, _, hwR, _, _, _, hη100, _, hg, _, _, _, _, hready, hparams⟩ := hp
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
    apply le_min hmax
    have hb := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
    apply hcont.trans
    have hbR : (p.contamination : ℝ) ≤ (p.w : ℝ) / 800 := by exact_mod_cast hb
    push_cast
    simpa only [div_div, show (2 : ℝ) * 400 = 800 by norm_num] using hbR
  have hmax0 : 0 < Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) := by
    unfold Robust.maxContamination Robust.sigmaSq
    have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw
    push_cast
    positivity
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (SoundAux.good_cluster_pos M ε w η D ω hg hI.choose).trans_le
      ((Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin n))
  have hN0 : (0 : ℝ) < N.card := (by positivity : 0 < w * n / 4).trans_le hN
  have hn : 2 / Robust.maxContamination (((p.w / 2 : ℚ) : ℝ)) (|p.R| : ℚ) ≤
      pts.length := by
    rw [hlen, div_le_iff₀ hmax0]
    have hfinite : 2 / (N.card : ℝ) ≤ ref.contamination :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hb := (div_le_iff₀ hN0).mp (hfinite.trans hmax)
    linarith only [hb]
  have hfu : (pts.length + d + 2) ^ 100 ≤ fuel := by
    apply le_trans _ hf
    have hc : N.card ≤ n := (Finset.card_le_univ N).trans_eq (Fintype.card_fin n)
    rw [hlen]
    calc
      _ ≤ (n + d + 2) ^ 100 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ localBudget .centered k n d ps := by
        simp only [localBudget, ite_true, mul_one]
        exact Nat.le_mul_of_pos_left _ (by positivity)
  obtain ⟨q', hq', heq⟩ := List.mem_map.mp hq
  have hflag : q'.2 = true := congrArg Prod.snd heq
  have hstat : pure q'.1 = q := congrArg Prod.fst heq
  have hvar := specified_variance F hF ref pts (p.w / 2) |p.R| p.frameAccuracy
    fuel hrep hvalid hres' (by positivity) (by linarith only [hw2]) (abs_nonneg _) hζ
    (fun j ↦ hcenter _) he hn hfu q'.1 (hflag ▸ hq')
  intro j hj
  obtain ⟨l, hl⟩ : ∃ l : Fin I.card, ABBKS26.RefineAux.component I l = j := by
    have hm : j ∈ Set.range (I.orderEmbOfFin rfl) := by
      rw [I.range_orderEmbOfFin]
      exact hj
    exact hm
  subst j
  rw [hcenter _, WithLp.toLp_zero, ← hstat]
  have hb : 20 / (((p.w / 2 : ℚ) : ℝ)) = 40 / (p.w : ℝ) := by push_cast; ring
  simpa only [ref, ABBKS26.RefineAux.roundedReference, ABBKS26.RefineAux.component,
    hb] using hvar l

/-- A FAR witness remains Gaussian-variance-valid after removing all affine coefficients. -/
theorem far_certificate {n k : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (a : FrameArgs × ℕ) (D : Robust.Reference n k a.1.1) (R B : ℝ)
    (hcenter : ∀ j, D.model.mean j = 0) (hS : ∀ j, (D.model.cov j).PosSemidef)
    (hfar : Robust.Far D (frameOf a.1.1 (F.run .centered a)) R B) :
    ∃ q : Statistic a.1.1,
      (q, true) ∈ (FramePool.typed a.1.1 (F.run .centered a)).map
        (fun q ↦ (pure q.1, q.2)) ∧
      (∀ j, ProbabilityTheory.variance
        (fun y : EuclideanSpace ℝ (Fin a.1.1) ↦ q.eval y.ofLp)
        (ProbabilityTheory.multivariateGaussian 0 (D.model.cov j)) ≤ B ^ 2) ∧
      ∃ i j, R ≤ |Robust.statCenter D.model i
        (FrameProgram.quadOf a.1.1 (statisticList q)) -
          Robust.statCenter D.model j (FrameProgram.quadOf a.1.1 (statisticList q))| := by
  obtain ⟨q, hq, hv, i, j, hg⟩ := FrobVariance.far_certificate F hF .centered a D R B
    hcenter hS hfar
  have hsym := FrobVariance.paired_symmetric F hF .centered a q hq
  refine ⟨pure q, List.mem_map.mpr ⟨(q, true), hq, rfl⟩,
    fun j ↦ (variance_le q hsym _ (hS j)).trans (hv j), i, j, ?_⟩
  rwa [center_gap D.model q hcenter]


end ABBKS26.Assembly.Exec.RefineSynth.FrobPure
