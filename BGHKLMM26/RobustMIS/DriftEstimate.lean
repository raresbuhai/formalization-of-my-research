module

public import BGHKLMM26.RobustMIS.Drift
public import BGHKLMM26.RobustMIS.Concentration
public import BGHKLMM26.RobustMIS.StaticDrift
public import Mathlib.Analysis.Convex.Integral

/-!
# The drift estimate

§9.1, Step 1 of `eldan-proof.tex`: `|y'(s)| ≤ K ψ(y(s)) + 2 e^{-πλ²/(8s)}` for `s ∈ (0, 1/2]`,
`K = 160 λ⁻³`, with `y' = E β(s, √s Z)` (`drift_identity`).

Proof sketch: on `𝒢_s = {λ(u(s, √s z)) ≥ λ/2}`, `drift_bound` (applied to `g = flowFun f s x`,
`heatU_mem`) and `(1-s)⁻¹ ≤ 2` give `|β| ≤ K ψ(e)`; off `𝒢_s`, `|β| ≤ 1` (`abs_driftD_le_half`)
and `P(𝒢_sᶜ) ≤ 2e^{-πλ²/(8s)}` (`concentration` with `θ = λ/2`, `|λ(a) - λ(b)| ≤ |a - b|`,
`log(1/(1-s)) ≤ 2s`); Jensen for the concave `ψ` on `[0, e^{-1/2}] ∋ e` (`concaveOn_psiL`,
`epsF_le`, `ConcaveOn.le_map_integral`).

Status: `drift_estimate` is proved from the statements of `StaticDrift`, `Bessel`, `Static`,
`Concentration`, `Flow` (`heatU_mem`), `Quantile` (`continuousOn_qf`) and `Rates`. In Lean the
pointwise bound is `|β| ≤ K ψ(e) + 𝟙_A` with `A = {|u - m| ≥ λ/2} ⊇ 𝒢_sᶜ`
(`DriftEstimate.abs_betaFlow_le`); integrability of `e` and `ψ(e)` comes from measurability of the
parametric integrals `heatU`, `hermite1 ∘ flowFun` (`StronglyMeasurable.integral_prod_right`) and
the continuity of `ψ` at `0` (`ψ(x) ≤ √x`), proved here.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Filter Topology

variable {n : ℕ}

namespace DriftEstimate

theorem lam_pos {m : ℝ} (hm : m ∈ Ioo (0 : ℝ) 1) : 0 < lam m := by
  unfold lam; exact mul_pos hm.1 (by linarith [hm.2])

theorem lam_le_quarter (m : ℝ) : lam m ≤ 1 / 4 := by
  unfold lam; nlinarith [sq_nonneg (m - 1 / 2)]

/-- `1/π ≤ e^{-1/2}`. -/
theorem inv_pi_le_exp : 1 / π ≤ exp (-(1 / 2)) := by
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (exp_pos _)
  have h1 : exp (1 / 2) ≤ exp 1 := exp_le_exp.mpr (by norm_num)
  have h2 : exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  linarith [Real.pi_gt_three]

theorem abs_lam_sub_le {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    |lam a - lam b| ≤ |a - b| := by
  have e : lam a - lam b = (a - b) * (1 - a - b) := by unfold lam; ring
  have h : |1 - a - b| ≤ 1 := abs_le.2 ⟨by linarith [ha.2, hb.2], by linarith [ha.1, hb.1]⟩
  rw [e, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) h

/-- `ψ(x) ≤ √x` on `(0, 1]`. -/
theorem psiL_le_sqrt {x : ℝ} (hx : 0 < x) : psiL x ≤ √x := by
  unfold psiL
  have h1 : Real.log (1 / x) ≤ 1 / x := by
    have := Real.log_le_sub_one_of_pos (one_div_pos.2 hx); linarith
  calc x * √(Real.log (1 / x)) ≤ x * √(1 / x) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hx.le
    _ = √x := by
        rw [Real.sqrt_div' _ hx.le, Real.sqrt_one]
        field_simp
        rw [Real.sq_sqrt hx.le]

theorem continuousOn_psiL : ContinuousOn psiL (Icc 0 (exp (-(1 / 2)))) := by
  intro x hx
  rcases hx.1.eq_or_lt with h | h
  · subst h
    have hψ0 : psiL 0 = 0 := by simp [psiL]
    rw [ContinuousWithinAt, hψ0]
    have hs : Tendsto (fun x : ℝ ↦ √x) (𝓝[Icc 0 (exp (-(1 / 2)))] 0) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Icc 0 (exp (-(1 / 2)))))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs ?_ ?_
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      exact mul_nonneg hy.1 (Real.sqrt_nonneg _)
    · refine eventually_nhdsWithin_of_forall fun y hy ↦ ?_
      rcases hy.1.eq_or_lt with h | h
      · subst h; simp [psiL]
      · exact psiL_le_sqrt h
  · apply ContinuousAt.continuousWithinAt
    unfold psiL
    have h1 : ContinuousAt (fun y : ℝ ↦ 1 / y) x := continuousAt_const.div continuousAt_id h.ne'
    have h2 : ContinuousAt (fun y : ℝ ↦ Real.log (1 / y)) x :=
      (Real.continuousAt_log (one_div_pos.2 h).ne').comp h1
    exact continuousAt_id.mul (Real.continuous_sqrt.continuousAt.comp h2)

theorem measurable_psiL : Measurable psiL := by
  unfold psiL
  exact measurable_id.mul (Real.measurable_log.comp (measurable_const.div measurable_id)).sqrt

theorem measurable_qf : Measurable qf := by
  have e : qf = (Icc (0 : ℝ) 1).piecewise qf (fun _ ↦ 0) := by
    funext a
    by_cases h : a ∈ Icc (0 : ℝ) 1
    · simp [Set.piecewise, h]
    · simp only [Set.piecewise, h, ite_false]
      exact qf_of_not_mem fun h' ↦ h (Ioo_subset_Icc_self h')
  rw [e]
  exact continuousOn_qf.measurable_piecewise continuousOn_const measurableSet_Icc

theorem measurable_heatU (f : Gs n → ℝ) (hf : Measurable f) (s : ℝ) :
    Measurable (heatU f s) := by
  have hm : Measurable fun p : Gs n × Gs n ↦ f (p.1 + √(1 - s) • p.2) := hf.comp (by fun_prop)
  have h : StronglyMeasurable (Function.uncurry fun x y : Gs n ↦ f (x + √(1 - s) • y)) :=
    hm.stronglyMeasurable
  exact (h.integral_prod_right (ν := gm n)).measurable

theorem measurable_hermite1_flowFun (f : Gs n → ℝ) (hf : Measurable f) (s : ℝ) :
    Measurable fun x ↦ hermite1 (flowFun f s x) := by
  have hm : Measurable fun p : Gs n × Gs n ↦ f (p.1 + √(1 - s) • p.2) • p.2 :=
    (hf.comp (by fun_prop)).smul measurable_snd
  have h : StronglyMeasurable
      (Function.uncurry fun x y : Gs n ↦ f (x + √(1 - s) • y) • y) :=
    hm.stronglyMeasurable
  exact (h.integral_prod_right (ν := gm n)).measurable

theorem measurable_eFlow (f : Gs n → ℝ) (hf : Measurable f) (s : ℝ) :
    Measurable (eFlow f s) := by
  have e : eFlow f s = fun x ↦ qf (heatU f s x) ^ 2 - ‖hermite1 (flowFun f s x)‖ ^ 2 := rfl
  rw [e]
  exact ((measurable_qf.comp (measurable_heatU f hf s)).pow_const 2).sub
    ((measurable_hermite1_flowFun f hf s).norm.pow_const 2)

/-- `log(1/(1-s)) ≤ 2s` for `s ∈ (0, 1/2]`. -/
theorem log_inv_one_sub_le {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    Real.log (1 / (1 - s)) ≤ 2 * s := by
  have h1 : 0 < 1 - s := by linarith
  have h := Real.log_le_sub_one_of_pos (one_div_pos.2 h1)
  have h2 : 1 / (1 - s) - 1 = s / (1 - s) := by field_simp; ring
  have h3 : s / (1 - s) ≤ 2 * s := by
    rw [div_le_iff₀ h1]; nlinarith
  linarith

/-- The pointwise bound `|β| ≤ K ψ(e) + 𝟙_A` of Step 1. -/
theorem abs_betaFlow_le (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 2) (x : Gs n) :
    |betaFlow f s x| ≤ 160 / lam (gMean f) ^ 3 * psiL (eFlow f s x) +
      {y : Gs n | lam (gMean f) / 2 ≤ |heatU f s y - gMean f|}.indicator 1 x := by
  have hs1 : s < 1 := by linarith
  have hg := measurable_flowFun f hf s x
  have hg01 := flowFun_mem f h01 s x
  have hu : gMean (flowFun f s x) ∈ Ioo (0 : ℝ) 1 := heatU_mem f hf h01 hm hs1 x
  have hl0 := lam_pos hm
  have he0 : 0 ≤ eFlow f s x := epsF_nonneg _ hg hg01
  have he1 : eFlow f s x ≤ 1 := (epsF_le _ hg01).2.trans (by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three])
  have hψ0 : 0 ≤ psiL (eFlow f s x) := psiL_nonneg ⟨he0, he1⟩
  have hinv : (1 - s)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hinv0 : 0 < (1 - s)⁻¹ := inv_pos.2 (by linarith)
  have hβ : |betaFlow f s x| = (1 - s)⁻¹ * |driftD (flowFun f s x)| := by
    rw [betaFlow, abs_mul, abs_of_pos hinv0]
  rw [hβ]
  by_cases hA : x ∈ {y : Gs n | lam (gMean f) / 2 ≤ |heatU f s y - gMean f|}
  · rw [indicator_of_mem hA, Pi.one_apply]
    have hD := abs_driftD_le_half _ hg hg01
    have : (1 - s)⁻¹ * |driftD (flowFun f s x)| ≤ 2 * (1 / 2) :=
      mul_le_mul hinv hD (abs_nonneg _) (by norm_num)
    have : 0 ≤ 160 / lam (gMean f) ^ 3 * psiL (eFlow f s x) := by positivity
    linarith
  · rw [indicator_of_notMem hA, add_zero]
    simp only [mem_ofPred_eq, not_le] at hA
    -- `λ(u) ≥ λ/2`
    have hlu : lam (gMean f) / 2 ≤ lam (heatU f s x) := by
      have hA' : |heatU f s x - gMean f| < lam (gMean f) / 2 := hA
      have hlam := abs_lam_sub_le (a := heatU f s x) (Ioo_subset_Icc_self hu)
        (Ioo_subset_Icc_self hm)
      have h1 := neg_abs_le (lam (heatU f s x) - lam (gMean f))
      linarith
    have hD := drift_bound _ hg hg01 hu
    have h2 : gMean (flowFun f s x) = heatU f s x := rfl
    rw [h2] at hD
    have hD' : |driftD (flowFun f s x)| ≤ 80 / lam (gMean f) ^ 3 * psiL (eFlow f s x) := by
      refine hD.trans ?_
      have h3 : (lam (gMean f) / 2) ^ 3 ≤ lam (heatU f s x) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hlu 3
      have h4 : 10 * psiL (epsF (flowFun f s x)) / lam (heatU f s x) ^ 3 ≤
          10 * psiL (epsF (flowFun f s x)) / (lam (gMean f) / 2) ^ 3 :=
        div_le_div_of_nonneg_left (by unfold eFlow at hψ0; positivity) (by positivity) h3
      refine h4.trans (le_of_eq ?_)
      unfold eFlow
      field_simp
      ring
    calc (1 - s)⁻¹ * |driftD (flowFun f s x)|
        ≤ 2 * (80 / lam (gMean f) ^ 3 * psiL (eFlow f s x)) :=
          mul_le_mul hinv hD' (abs_nonneg _) (by norm_num)
      _ = 160 / lam (gMean f) ^ 3 * psiL (eFlow f s x) := by ring

end DriftEstimate

/-- **Drift estimate** (§9.1, Step 1). -/
theorem drift_estimate (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 2) :
    |∫ z, betaFlow f s (√s • z) ∂gm n| ≤
      160 / lam (gMean f) ^ 3 * psiL (yFlow f s) +
        2 * exp (-(π * lam (gMean f) ^ 2) / (8 * s)) := by
  have hs1 : s < 1 := by linarith
  have hl0 := DriftEstimate.lam_pos hm
  obtain ⟨A, hA⟩ : ∃ A : Set (Gs n),
      A = {z | lam (gMean f) / 2 ≤ |heatU f s (√s • z) - gMean f|} := ⟨_, rfl⟩
  have hsm : Measurable fun z : Gs n ↦ √s • z := measurable_const_smul _
  have hAm : MeasurableSet A := by
    rw [hA]
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp
      (((DriftEstimate.measurable_heatU f hf s).comp hsm).sub_const _))
  -- the bound on `e`
  have he : ∀ z : Gs n, eFlow f s (√s • z) ∈ Icc 0 (exp (-(1 / 2))) := by
    intro z
    refine ⟨epsF_nonneg _ (measurable_flowFun f hf s _) (flowFun_mem f h01 s _), ?_⟩
    refine (epsF_le _ (flowFun_mem f h01 s _)).2.trans ?_
    refine le_trans ?_ DriftEstimate.inv_pi_le_exp
    exact one_div_le_one_div_of_le Real.pi_pos (by linarith [Real.pi_pos])
  have hem : Measurable fun z : Gs n ↦ eFlow f s (√s • z) :=
    (DriftEstimate.measurable_eFlow f hf s).comp hsm
  have hei : Integrable (fun z : Gs n ↦ eFlow f s (√s • z)) (gm n) := by
    refine Integrable.of_bound hem.aestronglyMeasurable 1 (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (he z).1]
    exact (he z).2.trans (by rw [exp_le_one_iff]; norm_num)
  have hψi : Integrable (psiL ∘ fun z : Gs n ↦ eFlow f s (√s • z)) (gm n) := by
    refine Integrable.of_bound (DriftEstimate.measurable_psiL.comp hem).aestronglyMeasurable 1
      (ae_of_all _ fun z ↦ ?_)
    have h1 : eFlow f s (√s • z) ≤ 1 :=
      (he z).2.trans (by rw [exp_le_one_iff]; norm_num)
    have h0 := psiL_nonneg ⟨(he z).1, h1⟩
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    rcases (he z).1.eq_or_lt with h | h
    · rw [← h]; simp [psiL]
    · exact (DriftEstimate.psiL_le_sqrt h).trans (Real.sqrt_le_one.mpr h1)
  -- Jensen
  have hJ : ∫ z, psiL (eFlow f s (√s • z)) ∂gm n ≤ psiL (yFlow f s) :=
    ConcaveOn.le_map_integral concaveOn_psiL DriftEstimate.continuousOn_psiL isClosed_Icc
      (ae_of_all _ he) hei hψi
  -- concentration
  have hconc := concentration f hf h01 hm ⟨hs0, hs1⟩ (θ := lam (gMean f) / 2) (by positivity)
  rw [← hA] at hconc
  have hexp : exp (-(π * (lam (gMean f) / 2) ^ 2) / Real.log (1 / (1 - s))) ≤
      exp (-(π * lam (gMean f) ^ 2) / (8 * s)) := by
    apply exp_le_exp.mpr
    have hLg : 0 < Real.log (1 / (1 - s)) :=
      Real.log_pos (by rw [lt_div_iff₀ (by linarith)]; linarith)
    have hLs := DriftEstimate.log_inv_one_sub_le hs0 hs
    rw [neg_div, neg_div, neg_le_neg_iff]
    have e : π * (lam (gMean f) / 2) ^ 2 / Real.log (1 / (1 - s)) =
        π * lam (gMean f) ^ 2 / (4 * Real.log (1 / (1 - s))) := by field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  -- assemble
  have hpt : ∀ z : Gs n, |betaFlow f s (√s • z)| ≤
      160 / lam (gMean f) ^ 3 * psiL (eFlow f s (√s • z)) + A.indicator 1 z := by
    intro z
    have h := DriftEstimate.abs_betaFlow_le f hf h01 hm hs0 hs (√s • z)
    have hind : {y : Gs n | lam (gMean f) / 2 ≤ |heatU f s y - gMean f|}.indicator
        (1 : Gs n → ℝ) (√s • z) = A.indicator 1 z := by
      rw [hA]
      by_cases hz : lam (gMean f) / 2 ≤ |heatU f s (√s • z) - gMean f|
      · rw [indicator_of_mem (show √s • z ∈ {y : Gs n | lam (gMean f) / 2 ≤
          |heatU f s y - gMean f|} from hz), indicator_of_mem (show z ∈ {z : Gs n |
          lam (gMean f) / 2 ≤ |heatU f s (√s • z) - gMean f|} from hz)]
        rfl
      · rw [indicator_of_notMem (show √s • z ∉ {y : Gs n | lam (gMean f) / 2 ≤
          |heatU f s y - gMean f|} from hz), indicator_of_notMem (show z ∉ {z : Gs n |
          lam (gMean f) / 2 ≤ |heatU f s (√s • z) - gMean f|} from hz)]
    rw [hind] at h
    exact h
  have hψi' : Integrable (fun z : Gs n ↦ psiL (eFlow f s (√s • z))) (gm n) := hψi
  have hc : Integrable (fun z : Gs n ↦ 160 / lam (gMean f) ^ 3 * psiL (eFlow f s (√s • z)))
      (gm n) := hψi'.const_mul _
  have hI : Integrable (A.indicator (1 : Gs n → ℝ)) (gm n) :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hbi : Integrable (fun z : Gs n ↦
      160 / lam (gMean f) ^ 3 * psiL (eFlow f s (√s • z)) + A.indicator 1 z) (gm n) :=
    hc.add hI
  calc |∫ z, betaFlow f s (√s • z) ∂gm n| ≤ ∫ z, |betaFlow f s (√s • z)| ∂gm n :=
        abs_integral_le_integral_abs
    _ ≤ ∫ z, (160 / lam (gMean f) ^ 3 * psiL (eFlow f s (√s • z)) + A.indicator 1 z) ∂gm n :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) hbi (ae_of_all _ hpt)
    _ = ∫ z, 160 / lam (gMean f) ^ 3 * psiL (eFlow f s (√s • z)) ∂gm n +
          ∫ z, A.indicator (1 : Gs n → ℝ) z ∂gm n := integral_add hc hI
    _ = 160 / lam (gMean f) ^ 3 * ∫ z, psiL (eFlow f s (√s • z)) ∂gm n + (gm n).real A := by
        rw [integral_const_mul, integral_indicator_one hAm]
    _ ≤ 160 / lam (gMean f) ^ 3 * psiL (yFlow f s) +
          2 * exp (-(π * lam (gMean f) ^ 2) / (8 * s)) := by
        gcongr
        exact hconc.trans (by linarith)

end BGHKLMM26.RobustMIS
