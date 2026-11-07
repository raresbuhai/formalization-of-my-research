module

public import BGHKLMM26.RobustMIS.Defs
public import BGHKLMM26.RobustMIS.FlowAux
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The heat flow

Lemma 5.2 (a), (b) of `eldan-proof.tex` (§5): the regularity of the flow
`u(s, x) = E f(x + √(1-s) Z)` for measurable `f : ℝⁿ → [0, 1]`: `u` is `C^∞` on `{s < 1}`, with
`∇u = (1-s)^{-1/2} U`, `∇²u = (1-s)⁻¹ B`, `∂_s u = -½ Δu`; all derivatives of order `≤ k` are
bounded on `[-1, s₁] × ℝⁿ` (`s₁ < 1`; the bounds may depend on `n`); `0 < u < 1` when
`0 < E f < 1`. The dimension-free bounds of Lemma 5.2 (c) are the static lemmas (`Static.lean`,
`Bessel.lean`) applied to `flowFun f s x`. The Gaussian Itô formula (Lemma 5.4) is in `Ito.lean`.

Proof (S4): `u(s, x) = ∫ f(w) p(s, x - w) dw` with the heat kernel
`p(s, z) = (2π(1-s))^{-n/2} e^{-|z|²/(2(1-s))}` (`Flow.heatU_eq_kInt`, from the density of
`stdGaussian`), and the kernel is differentiated under the integral sign. The general machinery is
in `FlowAux.lean`: for a kernel smooth on the open set `{s < 1}` whose derivatives of every order
are locally dominated by integrable functions (`Flow.KDom`), the kernel integral `Flow.kInt` is
`C^∞` with all derivatives computed under the integral (`Flow.hasFTaylorSeriesUpToOn_kInt`). The
derivatives of the heat kernel are bounded by `C e^{-c|z|²}` uniformly for `s` in compacts of
`(-∞, 1)` (`Flow.norm_iteratedFDeriv_kern_le`, by Faà di Bruno for `p = exp ∘ hk`), which gives
the domination and, by translation invariance, the bounds of Lemma 5.2 (b). The heat equations for
`u` and `∂_v u` follow from those of the kernels `p` and `∂_{(0,v)} p` (`Flow.kern_heat`,
`Flow.kernV_heat`, explicit computations) through `Flow.hasDerivAt_kInt_time`; no symmetry of
second derivatives is needed.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Flow
open scoped RealInnerProductSpace ContDiff Topology

variable {n : ℕ}

namespace Flow

section Aux2

variable (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

omit hf h01 in
theorem heatU_eq_slice {s : ℝ} (hs : s < 1) :
    heatU f s = fun y ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kern n) (s, y) :=
  funext fun y ↦ heatU_eq_kInt f hs y

theorem integrable_flowFun_smul_id (s : ℝ) (x : Gs n) :
    Integrable (fun y ↦ flowFun f s x y • y) (gm n) := by
  refine Integrable.mono' (ProbabilityTheory.IsGaussian.integrable_id (μ := gm n)).norm ?_
    (ae_of_all _ fun y ↦ ?_)
  · have hm : Measurable (flowFun f s x) := hf.comp (by fun_prop)
    exact (hm.smul measurable_id).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs]
    have := abs_le_one_of_mem h01 (x + √(1 - s) • y)
    exact mul_le_of_le_one_left (norm_nonneg _) this

omit hf h01 in
theorem kDom_kern_zero :
    KDom (ContinuousLinearMap.inr ℝ ℝ (Gs n)) (Wd n) (kern n) := by
  intro p₀ hp₀
  obtain ⟨ε, hε, bd, hbd, hb⟩ := kDom_kern (n := n) 0 p₀ hp₀
  exact ⟨ε, hε, bd, hbd, fun p hp w ↦ by simpa [norm_iteratedFDeriv_zero] using hb p hp w⟩

end Aux2

end Flow

open Flow

/-! ### The flow `u(s, x) = E f(x + √(1 - s) Z)` (Lemma 5.2) -/

section Flow

variable (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

/-- Lemma 5.2 (a): `u` is `C^∞` on `{s < 1}`. -/
theorem contDiffOn_heatU :
    ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) {p | p.1 < 1} :=
  (taylor_heat hf h01).contDiffOn.congr eqOn_heatU_kInt

/-- Lemma 5.2 (b): the derivatives of `u` of order `≤ k` are bounded on `[-1, s₁] × ℝⁿ`. -/
theorem bounded_iteratedFDeriv_heatU {s₁ : ℝ} (hs₁ : s₁ < 1) (k : ℕ) :
    ∃ M, ∀ p : ℝ × Gs n, p.1 ∈ Icc (-1) s₁ →
      ‖iteratedFDeriv ℝ k (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) p‖ ≤ M := by
  obtain ⟨C, c, hc, hC⟩ := norm_iteratedFDeriv_kern_le (n := n) k hs₁ (a := -1)
  refine ⟨C * ∫ w : Gs n, Real.exp (-c * ‖w‖ ^ 2), fun p hp ↦ ?_⟩
  have hpW : p ∈ Wd n := lt_of_le_of_lt hp.2 hs₁
  rw [iteratedFDeriv_heatU_eq hf h01 k hpW]
  have hcont := continuousOn_iteratedFDeriv (P := ℝ × Gs n) isOpen_Wd contDiffOn_kern k
  refine (norm_kInt_le (fun _ hp w ↦ mem_Wd_sub_inr hp w) (abs_le_one_of_mem h01) hcont
    (kDom_kern k) hpW).trans ?_
  have hint : Integrable (fun w : Gs n ↦ C * Real.exp (-c * ‖p.2 - w‖ ^ 2)) := by
    have := (integrable_exp_neg_mul_sq_norm (n := n) hc).comp_sub_left p.2
    exact this.const_mul C
  have hpt : ∀ w, ‖iteratedFDeriv ℝ k (kern n) (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w)‖ ≤
      C * Real.exp (-c * ‖p.2 - w‖ ^ 2) := fun w ↦ by
    have := hC (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) (by simpa using hp)
    simpa using this
  refine (integral_mono_of_nonneg (ae_of_all _ fun w ↦ norm_nonneg _) hint
    (ae_of_all _ hpt)).trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  exact integral_sub_left_eq_self (fun w : Gs n ↦ Real.exp (-c * ‖w‖ ^ 2)) (μ := volume) p.2

/-- Lemma 5.2 (a): `∇u = (1 - s)^{-1/2} U(s, x)`, `U(s, x) = E[Z f(x + √(1-s) Z)]`. -/
theorem hasFDerivAt_heatU {s : ℝ} (hs : s < 1) (x : Gs n) :
    HasFDerivAt (heatU f s) ((√(1 - s))⁻¹ • innerSL ℝ (hermite1 (flowFun f s x))) x := by
  have hp : ((s, x) : ℝ × Gs n) ∈ Wd n := hs
  have h1' := abs_le_one_of_mem h01
  have hd := differentiableAt_kInt hf h1' contDiffOn_kern kDom_kern hp
  rw [heatU_eq_slice f hs]
  refine (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).congr_fderiv
    (ContinuousLinearMap.ext fun v ↦ ?_)
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply,
    smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [fderiv_kInt_apply hf h1' contDiffOn_kern kDom_kern hp, hermite1,
    real_inner_comm, ← integral_inner (integrable_flowFun_smul_id f hf h01 s x),
    integral_gm_eq_kern _ hs x, ← integral_const_mul]
  have hσ : 0 < 1 - s := by linarith
  have hr : √(1 - s) ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.inr_apply, sub_zero]
  rw [fderiv_kern_apply hs]
  simp only [flowFun, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel, inner_smul_right,
    smul_eq_mul, zero_mul, zero_sub]
  have hσ' : (1 - s)⁻¹ = (√(1 - s))⁻¹ * (√(1 - s))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hσ.le]
  have e1 : ⟪v, w - x⟫ = -⟪x - w, v⟫ := by rw [← neg_sub x w, inner_neg_right, real_inner_comm]
  rw [hσ', e1]
  ring

/-- Lemma 5.2 (a): `∇²u = (1 - s)⁻¹ B(s, x)`, `B(s, x) = E[(Z Zᵀ - I) f(x + √(1-s) Z)]`. -/
theorem iteratedFDeriv_two_heatU {s : ℝ} (hs : s < 1) (x v w : Gs n) :
    iteratedFDeriv ℝ 2 (heatU f s) x ![v, w] = (1 - s)⁻¹ * bForm (flowFun f s x) v w := by
  have hp : ((s, x) : ℝ × Gs n) ∈ Wd n := hs
  have h1' := abs_le_one_of_mem h01
  rw [heatU_eq_slice f hs, iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_slice (fun y ↦ differentiableAt_kInt hf h1' contDiffOn_kern kDom_kern
      (show (s, y) ∈ Wd n from hs))
      (differentiableAt_fderiv_kInt hf h1' contDiffOn_kern kDom_kern hp),
    fderiv_fderiv_kInt_apply hf h1' contDiffOn_kern kDom_kern hp, bForm,
    integral_gm_eq_kern _ hs x, ← integral_const_mul]
  have hσ : 0 < 1 - s := by linarith
  have hr : √(1 - s) ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  refine integral_congr_ae (ae_of_all _ fun w' ↦ ?_)
  simp only [Prod.mk_sub_mk, ContinuousLinearMap.inr_apply, sub_zero]
  rw [fderiv_fderiv_kern_apply hs]
  simp only [flowFun, smul_smul, mul_inv_cancel₀ hr, one_smul, add_sub_cancel, inner_smul_right,
    smul_eq_mul]
  have hσ' : (1 - s)⁻¹ = (√(1 - s))⁻¹ * (√(1 - s))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hσ.le]
  have e1 : ∀ u : Gs n, ⟪u, w' - x⟫ = -⟪x - w', u⟫ := fun u ↦ by
    rw [← neg_sub x w', inner_neg_right, real_inner_comm]
  rw [e1, e1, show ((1 - s) ^ 2)⁻¹ = (1 - s)⁻¹ * (1 - s)⁻¹ by rw [sq, mul_inv], hσ']
  ring

/-- Lemma 5.2 (a): the backward heat equation `∂_s u = -½ Δu`. -/
theorem hasDerivAt_heatU_time {s : ℝ} (hs : s < 1) (x : Gs n) :
    HasDerivAt (fun s ↦ heatU f s x) (-(1 / 2) * Laplacian.laplacian (heatU f s) x) s := by
  have h1' := abs_le_one_of_mem h01
  have h := hasDerivAt_kInt_time hf h1' contDiffOn_kern kDom_kern (fun q hq ↦ kern_heat hq) hs x
  rw [heatU_eq_slice f hs]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hs] with s' hs'
  exact heatU_eq_kInt f hs' x

/-- `U(s, x) = √(1 - s) ∇u(s, x)`, so `e(s, x) = q(u)² - (1 - s) |∇u|²`
(from `hasFDerivAt_heatU`). -/
theorem hermite1_flowFun_eq {s : ℝ} (hs : s < 1) (x : Gs n) :
    hermite1 (flowFun f s x) = √(1 - s) • gradient (heatU f s) x := by
  have hσ : 0 < 1 - s := by linarith
  have hr : √(1 - s) ≠ 0 := (Real.sqrt_pos.2 hσ).ne'
  have h := hasFDerivAt_heatU f hf h01 hs x
  have hg : HasGradientAt (heatU f s) ((√(1 - s))⁻¹ • hermite1 (flowFun f s x)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
  rw [hg.gradient, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem Flow.fderiv_heatU_apply_eq {s : ℝ} (hs : s < 1) (y v : Gs n) :
    fderiv ℝ (heatU f s) y v =
      kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kernV n v) (s, y) := by
  have hp : ((s, y) : ℝ × Gs n) ∈ Wd n := hs
  have h1' := abs_le_one_of_mem h01
  rw [heatU_eq_slice f hs, fderiv_slice (differentiableAt_kInt hf h1' contDiffOn_kern kDom_kern hp)]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.inr_apply]
  rw [fderiv_kInt_apply hf h1' contDiffOn_kern kDom_kern hp, kInt]
  rfl

/-- The space derivatives of `u` satisfy the backward heat equation too:
`∂_s ∂_v u = -½ Δ ∂_v u` (from `contDiffOn_heatU`, `hasDerivAt_heatU_time` and the symmetry of
second derivatives). Used by the drift identity. -/
theorem hasDerivAt_fderiv_heatU_time {s : ℝ} (hs : s < 1) (x v : Gs n) :
    HasDerivAt (fun s ↦ fderiv ℝ (heatU f s) x v)
      (-(1 / 2) * Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y v) x) s := by
  have h1' := abs_le_one_of_mem h01
  have h := hasDerivAt_kInt_time hf h1' (contDiffOn_kernV v) (kDom_kernV v)
    (fun q hq ↦ kernV_heat v hq) hs x
  have e : (fun y ↦ fderiv ℝ (heatU f s) y v) =
      fun y ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kernV n v) (s, y) :=
    funext fun y ↦ fderiv_heatU_apply_eq f hf h01 hs y v
  rw [e]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hs] with s' hs'
  exact fderiv_heatU_apply_eq f hf h01 hs' x v

theorem Flow.heatU_pos (hm : 0 < gMean f) {s : ℝ} (hs : s < 1) (x : Gs n) : 0 < heatU f s x := by
  have h1' := abs_le_one_of_mem h01
  have hint : ∀ p ∈ Wd n,
      Integrable (fun w ↦ f w • kern n (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w)) :=
    fun p hp ↦ integrable_kInt (fun _ hp w ↦ mem_Wd_sub_inr hp w) hf h1'
      contDiffOn_kern.continuousOn kDom_kern_zero hp
  have hnn : ∀ p : ℝ × Gs n, 0 ≤ fun w ↦ f w • kern n (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) :=
    fun p w ↦ smul_nonneg (h01 w).1 (kern_pos _).le
  rw [heatU_eq_kInt f hs x, kInt]
  refine lt_of_le_of_ne (integral_nonneg (hnn _)) fun h0 ↦ ?_
  have hz := (integral_eq_zero_iff_of_nonneg (hnn _) (hint _ hs)).1 h0.symm
  have hf0 : f =ᵐ[volume] 0 := by
    filter_upwards [hz] with w hw
    have := (smul_eq_zero.1 hw).resolve_right (kern_pos _).ne'
    simpa using this
  have hm0 : gMean f = 0 := by
    have e : gMean f = heatU f 0 0 := by
      rw [heatU]; congr 1; funext y; simp [flowFun]
    rw [e, heatU_eq_kInt f (by norm_num : (0 : ℝ) < 1) 0, kInt]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hf0] with w hw
    simp [hw]
  linarith

/-- Lemma 5.2 (a): `0 < u < 1` when `0 < E f < 1`. -/
theorem heatU_mem (hm : gMean f ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s < 1) (x : Gs n) :
    heatU f s x ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨heatU_pos f hf h01 hm.1 hs x, ?_⟩
  have hf' : Measurable (fun y ↦ 1 - f y) := measurable_const.sub hf
  have h01' : ∀ y, 0 ≤ 1 - f y ∧ 1 - f y ≤ 1 := fun y ↦ ⟨by linarith [(h01 y).2], by
    linarith [(h01 y).1]⟩
  have hint : ∀ g : Gs n → ℝ, Measurable g → (∀ y, 0 ≤ g y ∧ g y ≤ 1) → Integrable g (gm n) :=
    fun g hg hg01 ↦ Integrable.mono' (integrable_const 1) hg.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact abs_le_one_of_mem hg01 y)
  have hm' : gMean (fun y ↦ 1 - f y) = 1 - gMean f := by
    rw [gMean, gMean, integral_sub (integrable_const 1) (hint f hf h01)]
    simp
  have hu' : heatU (fun y ↦ 1 - f y) s x = 1 - heatU f s x := by
    rw [heatU, heatU, gMean, gMean]
    simp only [flowFun]
    have hg : Measurable (fun y : Gs n ↦ f (x + √(1 - s) • y)) := hf.comp (by fun_prop)
    rw [integral_sub (integrable_const 1) (hint _ hg fun y ↦ h01 _)]
    simp
  have := heatU_pos (fun y ↦ 1 - f y) hf' h01' (by rw [hm']; linarith [hm.2]) hs x
  linarith

omit hf h01 in
theorem flowFun_zero_zero : flowFun f 0 0 = f := by
  funext y
  simp [flowFun]

omit hf h01 in
theorem heatU_zero_zero : heatU f 0 0 = gMean f := by
  rw [heatU, flowFun_zero_zero]

omit h01 in
theorem measurable_flowFun (s : ℝ) (x : Gs n) : Measurable (flowFun f s x) :=
  hf.comp (by fun_prop)

omit hf in
theorem flowFun_mem (s : ℝ) (x y : Gs n) : 0 ≤ flowFun f s x y ∧ flowFun f s x y ≤ 1 :=
  h01 _

/-! #### Interface: slices of the joint derivatives -/

theorem Flow.differentiableAt_heatU {p : ℝ × Gs n} (hp : p.1 < 1) :
    DifferentiableAt ℝ (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) p :=
  ((contDiffOn_heatU f hf h01).contDiffAt (isOpen_Wd.mem_nhds hp)).differentiableAt (by simp)

/-- `∇_x u(s, x)` is the `x`-part of the joint derivative. -/
theorem Flow.fderiv_heatU_eq {s : ℝ} (hs : s < 1) (x : Gs n) :
    fderiv ℝ (heatU f s) x = (fderiv ℝ (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) (s, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ (Gs n)) :=
  fderiv_slice (U := fun p : ℝ × Gs n ↦ heatU f p.1 p.2)
    (Flow.differentiableAt_heatU f hf h01 (p := (s, x)) hs)

/-- `(s, x) ↦ ∇_x u(s, x)` is `C^∞` on `{s < 1}`. -/
theorem Flow.contDiffOn_fderiv_heatU :
    ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ fderiv ℝ (heatU f p.1) p.2) {p | p.1 < 1} := by
  have h := ((contDiffOn_heatU f hf h01).fderiv_of_isOpen isOpen_Wd (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ ℝ (Gs n)))
  exact h.congr fun p hp ↦ Flow.fderiv_heatU_eq f hf h01 hp p.2

/-- The time derivative of `u` is bounded by the joint first derivative. -/
theorem Flow.abs_deriv_heatU_time_le {s : ℝ} (hs : s < 1) (x : Gs n) :
    |deriv (fun r ↦ heatU f r x) s| ≤
      ‖iteratedFDeriv ℝ 1 (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) (s, x)‖ := by
  have hd := (Flow.differentiableAt_heatU f hf h01 (p := (s, x)) hs).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  rw [show deriv (fun r ↦ heatU f r x) s = _ from hd.deriv, norm_iteratedFDeriv_one]
  refine ((fderiv ℝ (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) (s, x)).le_opNorm _).trans ?_
  simp

/-- The `x`-derivatives of `u` are bounded by the joint derivatives. -/
theorem Flow.norm_iteratedFDeriv_heatU_slice_le {s : ℝ} (hs : s < 1) (x : Gs n) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (heatU f s) x‖ ≤
      ‖iteratedFDeriv ℝ k (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) (s, x)‖ := by
  set U : ℝ × Gs n → ℝ := fun p ↦ heatU f p.1 p.2 with hU
  set U' : ℝ × Gs n → ℝ := fun q ↦ U (q + (s, 0)) with hU'
  set W' : Set (ℝ × Gs n) := {q | q.1 + s < 1} with hW'
  have hW'o : IsOpen W' := isOpen_lt (continuous_fst.add continuous_const) continuous_const
  have hU'c : ContDiffOn ℝ ∞ U' W' :=
    (contDiffOn_heatU f hf h01).comp (contDiff_id.add contDiff_const).contDiffOn
      fun q hq ↦ by simpa [hW'] using hq
  have hpre : (ContinuousLinearMap.inr ℝ ℝ (Gs n)) ⁻¹' W' = univ := by
    ext y; simp [hW', hs]
  have h := (ContinuousLinearMap.inr ℝ ℝ (Gs n)).iteratedFDerivWithin_comp_right hU'c
    hW'o.uniqueDiffOn (by rw [hpre]; exact uniqueDiffOn_univ) (x := x) (by simpa [hW'] using hs)
    (i := k) (by exact_mod_cast le_top)
  rw [hpre, iteratedFDerivWithin_univ,
    iteratedFDerivWithin_of_isOpen k hW'o (by simpa [hW'] using hs)] at h
  have e1 : U' ∘ (ContinuousLinearMap.inr ℝ ℝ (Gs n)) = heatU f s := by
    funext y; simp [hU', hU]
  rw [e1] at h
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    fun _ _ ↦ ContinuousLinearMap.norm_inr_le_one ℝ ℝ (Gs n))).trans (le_of_eq ?_)
  rw [hU', iteratedFDeriv_comp_add_right]
  simp

end Flow

end BGHKLMM26.RobustMIS
