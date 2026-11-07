module

public import BGHKLMM26.RobustMIS.ItoAux
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Auxiliary material for the heat flow (`Flow.lean`)

* **Kernel integrals** `kInt ι g φ p = ∫ g(w) φ(p - ι w) dw` (Lebesgue measure on `ℝⁿ`, `|g| ≤ 1`
  measurable): differentiation under the integral sign (`hasFDerivAt_kInt`) and, for a kernel that
  is `C^∞` on an open set `W` with locally dominated derivatives of every order (`KDom`), smoothness
  with all derivatives computed under the integral (`hasFTaylorSeriesUpToOn_kInt`).
* **The heat kernel** `kern n (s, z) = (2π(1-s))^{-n/2} e^{-|z|²/(2(1-s))}` on `Wd n = {s < 1}`:
  smoothness (`contDiffOn_kern`), Gaussian bounds on all derivatives uniformly for `s ∈ [a, b]`,
  `b < 1` (`norm_iteratedFDeriv_kern_le`, Faà di Bruno for `exp ∘ hk` plus temperate growth of
  `‖z‖²`), hence `KDom` (`kDom_kern`); the change of variables `E Φ(Z) = ∫ p(s, x - w)
  Φ((w - x)/√(1-s)) dw` (`integral_gm_eq_kern`) and `heatU f s x = kInt inr f kern (s, x)`
  (`heatU_eq_kInt`).
* **Explicit derivatives**: `fderiv_kern_apply`, `fderiv_fderiv_kern_apply`, the kernel
  `kernV n v = ∂_{(0,v)} kern` of `∂_v u` and its derivatives, and the backward heat equations
  `kern_heat`, `kernV_heat`.
* **Transfer**: slices `y ↦ U(s, y)` (`fderiv_slice`, `fderiv_fderiv_slice`) and the heat equation
  for kernel integrals of kernels solving it (`hasDerivAt_kInt_time`).

The Gaussian density (`Ito.stdGaussian_density`) is in `ItoAux.lean`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Flow

open MeasureTheory Set Metric Real
open scoped ContDiff Topology RealInnerProductSpace

variable {n : ℕ} {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The kernel integral `p ↦ ∫ g(w) φ(p - ι w) dw`. -/
noncomputable def kInt (ι : Gs n →L[ℝ] P) (g : Gs n → ℝ) (φ : P → V) (p : P) : V :=
  ∫ w, g w • φ (p - ι w)

/-- Local integrable domination of `w ↦ φ(p - ι w)`. -/
def KDom (ι : Gs n →L[ℝ] P) (W : Set P) (φ : P → V) : Prop :=
  ∀ p₀ ∈ W, ∃ ε > 0, ∃ bd : Gs n → ℝ, Integrable bd ∧
    ∀ p ∈ ball p₀ ε, ∀ w, ‖φ (p - ι w)‖ ≤ bd w

theorem curryLeft_integral {m : ℕ}
    (A : Gs n → ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ P) ℝ) :
    (∫ w, A w).curryLeft =
      ∫ w, continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ P) ℝ (A w) := by
  have := LinearIsometry.integral_comp_comm (𝕜 := ℝ)
    (E := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) ↦ P) ℝ)
    (F := P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ P) ℝ) (μ := volume)
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ P) ℝ).toLinearIsometry A
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
  rw [this]
  rfl

theorem curry0_integral (A : Gs n → ContinuousMultilinearMap ℝ (fun _ : Fin 0 ↦ P) ℝ) :
    (∫ w, A w).curry0 = ∫ w, (A w).curry0 := by
  have := (continuousMultilinearCurryFin0 ℝ P ℝ).toLinearIsometry.integral_comp_comm (μ := volume) A
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at this
  simpa using this.symm

section General

variable {ι : Gs n →L[ℝ] P} {W : Set P} (hW : IsOpen W) (hWι : ∀ p ∈ W, ∀ w, p - ι w ∈ W)
  {g : Gs n → ℝ} (hg : Measurable g) (hg1 : ∀ w, |g w| ≤ 1)
include hW hWι hg hg1

omit [CompleteSpace V] hW hg1 in
theorem aestronglyMeasurable_kInt {φ : P → V} (hφ : ContinuousOn φ W) {p : P} (hp : p ∈ W) :
    AEStronglyMeasurable (fun w ↦ g w • φ (p - ι w)) volume := by
  refine hg.aestronglyMeasurable.smul ?_
  exact (hφ.comp_continuous (continuous_const.sub ι.continuous)
    (fun w ↦ hWι p hp w)).aestronglyMeasurable

omit [CompleteSpace V] hW in
theorem integrable_kInt {φ : P → V} (hφ : ContinuousOn φ W) (hd : KDom ι W φ) {p : P}
    (hp : p ∈ W) : Integrable (fun w ↦ g w • φ (p - ι w)) volume := by
  obtain ⟨ε, hε, bd, hbd, hb⟩ := hd p hp
  refine Integrable.mono' hbd (aestronglyMeasurable_kInt hWι hg hφ hp) (ae_of_all _ fun w ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |g w| * ‖φ (p - ι w)‖ ≤ 1 * bd w :=
        mul_le_mul (hg1 w) (hb p (mem_ball_self hε) w) (norm_nonneg _) zero_le_one
    _ = bd w := one_mul _

omit [CompleteSpace V] hW hg in
theorem norm_kInt_le {φ : P → V} (hφ : ContinuousOn φ W) (hd : KDom ι W φ) {p : P}
    (hp : p ∈ W) :
    ‖kInt ι g φ p‖ ≤ ∫ w, ‖φ (p - ι w)‖ := by
  obtain ⟨ε, hε, bd, hbd, hb⟩ := hd p hp
  have hint : Integrable (fun w ↦ ‖φ (p - ι w)‖) volume := by
    refine Integrable.mono' hbd ?_ (ae_of_all _ fun w ↦ ?_)
    · exact (hφ.comp_continuous (continuous_const.sub ι.continuous)
        (fun w ↦ hWι p hp w)).norm.aestronglyMeasurable
    · simpa using hb p (mem_ball_self hε) w
  refine norm_integral_le_of_norm_le hint (ae_of_all _ fun w ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |g w| * ‖φ (p - ι w)‖ ≤ 1 * ‖φ (p - ι w)‖ :=
        mul_le_mul_of_nonneg_right (hg1 w) (norm_nonneg _)
    _ = _ := one_mul _

omit [CompleteSpace V] in
/-- Differentiation under the integral sign for kernel integrals. -/
theorem hasFDerivAt_kInt {φ : P → V} (hφ : DifferentiableOn ℝ φ W)
    (hφc : ContinuousOn (fderiv ℝ φ) W) (hd0 : KDom ι W φ) (hd1 : KDom ι W (fderiv ℝ φ))
    {p₀ : P} (hp₀ : p₀ ∈ W) :
    HasFDerivAt (kInt ι g φ) (kInt ι g (fderiv ℝ φ) p₀) p₀ := by
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.1 hW p₀ hp₀
  obtain ⟨ε₁, hε₁, bd, hbd, hb⟩ := hd1 p₀ hp₀
  have hS : ball p₀ (min ε₀ ε₁) ∈ 𝓝 p₀ := ball_mem_nhds _ (lt_min hε₀ hε₁)
  have hSW : ∀ p ∈ ball p₀ (min ε₀ ε₁), p ∈ W := fun p hp ↦
    hball (ball_subset_ball (min_le_left _ _) hp)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := bd)
    (F := fun p w ↦ g w • φ (p - ι w)) (F' := fun p w ↦ g w • fderiv ℝ φ (p - ι w)) hS ?_
    (integrable_kInt hWι hg hg1 hφ.continuousOn hd0 hp₀)
    (aestronglyMeasurable_kInt hWι hg hφc hp₀) ?_ hbd ?_
  · filter_upwards [hW.mem_nhds hp₀] with p hp
    exact aestronglyMeasurable_kInt hWι hg hφ.continuousOn hp
  · refine ae_of_all _ fun w p hp ↦ ?_
    rw [norm_smul, Real.norm_eq_abs]
    calc |g w| * ‖fderiv ℝ φ (p - ι w)‖ ≤ 1 * bd w :=
          mul_le_mul (hg1 w) (hb p (ball_subset_ball (min_le_right _ _) hp) w) (norm_nonneg _)
            zero_le_one
      _ = bd w := one_mul _
  · refine ae_of_all _ fun w p hp ↦ ?_
    have h1 : HasFDerivAt φ (fderiv ℝ φ (p - ι w)) (p - ι w) :=
      (hφ.differentiableAt (hW.mem_nhds (hWι p (hSW p hp) w))).hasFDerivAt
    have h2 := (h1.comp p ((hasFDerivAt_id p).sub_const (ι w))).const_smul (g w)
    simp only [ContinuousLinearMap.comp_id] at h2
    exact h2

omit hWι hg hg1 in
theorem differentiableOn_iteratedFDeriv {κ : P → ℝ} (hκ : ContDiffOn ℝ ∞ κ W) (m : ℕ) :
    DifferentiableOn ℝ (iteratedFDeriv ℝ m κ) W :=
  (hκ.differentiableOn_iteratedFDerivWithin (m := m) (by exact_mod_cast WithTop.coe_lt_top _)
    hW.uniqueDiffOn).congr fun p hp ↦ (iteratedFDerivWithin_of_isOpen m hW hp).symm

omit hWι hg hg1 in
theorem continuousOn_iteratedFDeriv {κ : P → ℝ} (hκ : ContDiffOn ℝ ∞ κ W) (m : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ m κ) W :=
  (hκ.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top)
    hW.uniqueDiffOn).congr fun p hp ↦ (iteratedFDerivWithin_of_isOpen m hW hp).symm

/-- The kernel integral of a smooth kernel with dominated derivatives is smooth, with the
derivatives computed under the integral sign. -/
theorem hasFTaylorSeriesUpToOn_kInt {κ : P → ℝ} (hκ : ContDiffOn ℝ ∞ κ W)
    (hdom : ∀ m, KDom ι W (iteratedFDeriv ℝ m κ)) :
    HasFTaylorSeriesUpToOn ∞ (kInt ι g κ) (fun p m ↦ kInt ι g (iteratedFDeriv ℝ m κ) p) W := by
  have hder : ∀ m, ∀ p ∈ W, HasFDerivAt (kInt ι g (iteratedFDeriv ℝ m κ))
      (kInt ι g (iteratedFDeriv ℝ (m + 1) κ) p).curryLeft p := by
    intro m p hp
    have hc : ContinuousOn (fderiv ℝ (iteratedFDeriv ℝ m κ)) W := by
      rw [fderiv_iteratedFDeriv]
      exact (LinearIsometryEquiv.continuous _).comp_continuousOn
        (continuousOn_iteratedFDeriv hW hκ (m + 1))
    have hd1 : KDom ι W (fderiv ℝ (iteratedFDeriv ℝ m κ)) := by
      intro p₀ hp₀
      obtain ⟨ε, hε, bd, hbd, hb⟩ := hdom (m + 1) p₀ hp₀
      exact ⟨ε, hε, bd, hbd, fun p hp w ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hb p hp w⟩
    have := hasFDerivAt_kInt hW hWι hg hg1 (differentiableOn_iteratedFDeriv hW hκ m) hc
      (hdom m) hd1 hp
    convert this using 1
    rw [kInt, kInt, fderiv_iteratedFDeriv, curryLeft_integral]
    simp only [Function.comp_apply, map_smul]
  refine ⟨fun p hp ↦ ?_, fun m _ p hp ↦ (hder m p hp).hasFDerivWithinAt,
    fun m _ ↦ fun p hp ↦ (hder m p hp).continuousAt.continuousWithinAt⟩
  rw [kInt, curry0_integral]
  simp [kInt]

end General


theorem one_add_pow_mul_exp_le (N : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C, ∀ t : ℝ, 0 ≤ t → (1 + t) ^ N * exp (-c * t ^ 2) ≤ C * exp (-(c / 2) * t ^ 2) := by
  refine ⟨(N.factorial : ℝ) * exp (1 + 1 / (2 * c)), fun t ht ↦ ?_⟩
  have h1 : (1 + t) ^ N ≤ (N.factorial : ℝ) * exp (1 + t) := by
    have := Real.pow_div_factorial_le_exp (1 + t) (by linarith) N
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  have h2 : exp (1 + t) * exp (-c * t ^ 2) ≤ exp (1 + 1 / (2 * c)) * exp (-(c / 2) * t ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : 0 ≤ (c / 2) * (t - 1 / c) ^ 2 := by positivity
    have e : (c / 2) * (t - 1 / c) ^ 2 = (c / 2) * t ^ 2 - t + 1 / (2 * c) := by
      field_simp; ring
    nlinarith
  calc (1 + t) ^ N * exp (-c * t ^ 2) ≤ (N.factorial : ℝ) * exp (1 + t) * exp (-c * t ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (N.factorial : ℝ) * (exp (1 + t) * exp (-c * t ^ 2)) := by ring
    _ ≤ (N.factorial : ℝ) * (exp (1 + 1 / (2 * c)) * exp (-(c / 2) * t ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

theorem integrable_exp_neg_mul_sq_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun w : Gs n ↦ exp (-c * ‖w‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Gs n) (b := (c : ℂ))
    (by simpa using hc)
    0 0).norm
  refine h.congr (ae_of_all _ fun w ↦ ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp only [neg_mul, Complex.neg_re]
  norm_cast

theorem norm_iteratedFDeriv_comp_fst_le {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ ∞ ψ (Iio 1))
    {p : ℝ × Gs n} (hp : p.1 < 1) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun p : ℝ × Gs n ↦ ψ p.1) p‖ ≤ ‖iteratedFDeriv ℝ i ψ p.1‖ := by
  have hO : IsOpen ((ContinuousLinearMap.fst ℝ ℝ (Gs n)) ⁻¹' Iio 1) :=
    isOpen_Iio.preimage (ContinuousLinearMap.fst ℝ ℝ (Gs n)).continuous
  have h := (ContinuousLinearMap.fst ℝ ℝ (Gs n)).iteratedFDerivWithin_comp_right hψ
    isOpen_Iio.uniqueDiffOn hO.uniqueDiffOn (x := p) hp (i := i) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen i hO hp, iteratedFDerivWithin_of_isOpen i isOpen_Iio hp] at h
  change ‖iteratedFDeriv ℝ i (ψ ∘ (ContinuousLinearMap.fst ℝ ℝ (Gs n))) p‖ ≤ _
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_)
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    (fun _ _ ↦ ContinuousLinearMap.norm_fst_le _ _ _)

theorem norm_iteratedFDeriv_comp_snd_le {q : Gs n → ℝ} (hq : ContDiff ℝ ∞ q)
    (p : ℝ × Gs n) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun p : ℝ × Gs n ↦ q p.2) p‖ ≤ ‖iteratedFDeriv ℝ i q p.2‖ := by
  have h := (ContinuousLinearMap.snd ℝ ℝ (Gs n)).iteratedFDeriv_comp_right hq p (i := i)
    (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ i (q ∘ (ContinuousLinearMap.snd ℝ ℝ (Gs n))) p‖ ≤ _
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine (mul_le_of_le_one_right (norm_nonneg _) ?_)
  exact Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _)
    (fun _ _ ↦ ContinuousLinearMap.norm_snd_le _ _ _)

theorem exists_bound_iteratedFDeriv {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ ∞ ψ (Iio 1)) (m : ℕ)
    {a b : ℝ} (hb : b < 1) :
    ∃ C, ∀ i ≤ m, ∀ s ∈ Icc a b, ‖iteratedFDeriv ℝ i ψ s‖ ≤ C := by
  have hc : ∀ i, ContinuousOn (iteratedFDeriv ℝ i ψ) (Iio 1) := fun i ↦
    (hψ.continuousOn_iteratedFDerivWithin (m := i) (by exact_mod_cast le_top)
      isOpen_Iio.uniqueDiffOn).congr fun p hp ↦
        (iteratedFDerivWithin_of_isOpen i isOpen_Iio hp).symm
  have hs : Icc a b ⊆ Iio 1 := fun s hs ↦ lt_of_le_of_lt hs.2 hb
  have hsum : ContinuousOn (fun s ↦ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i ψ s‖)
      (Icc a b) :=
    continuousOn_finsetSum _ fun i _ ↦ ((hc i).mono hs).norm
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hsum
  refine ⟨C, fun i hi s hs ↦ ?_⟩
  refine le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hC s hs)))
  exact Finset.single_le_sum (f := fun i ↦ ‖iteratedFDeriv ℝ i ψ s‖) (fun _ _ ↦ norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

/-! ### The heat kernel -/

/-- The `s`-part of the log of the heat kernel: `-(n/2) log(2π(1-s))`. -/
noncomputable def psi1 (n : ℕ) (s : ℝ) : ℝ := -((n : ℝ) / 2) * Real.log (2 * π * (1 - s))

/-- `-(2(1-s))⁻¹`. -/
noncomputable def psi2 (s : ℝ) : ℝ := -(2 * (1 - s))⁻¹

/-- The log of the heat kernel: `-(n/2) log(2π(1-s)) - ‖z‖²/(2(1-s))`. -/
noncomputable def hk (n : ℕ) (p : ℝ × Gs n) : ℝ := psi1 n p.1 + ‖p.2‖ ^ 2 * psi2 p.1

/-- The heat kernel `p_{1-s}(z) = (2π(1-s))^{-n/2} e^{-|z|²/(2(1-s))}` as a function of
`(s, z)`. -/
noncomputable def kern (n : ℕ) (p : ℝ × Gs n) : ℝ := Real.exp (hk n p)

/-- The domain `{s < 1}`. -/
def Wd (n : ℕ) : Set (ℝ × Gs n) := {p | p.1 < 1}

theorem isOpen_Wd : IsOpen (Wd n) := isOpen_lt continuous_fst continuous_const

theorem contDiffOn_psi1 : ContDiffOn ℝ ∞ (psi1 n) (Iio 1) := by
  unfold psi1
  refine contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun s hs ↦ ?_)
  have : 0 < 1 - s := by simp only [mem_Iio] at hs; linarith
  positivity

theorem contDiffOn_psi2 : ContDiffOn ℝ ∞ psi2 (Iio 1) := by
  unfold psi2
  refine (ContDiffOn.inv (by fun_prop) fun s hs ↦ ?_).neg
  have : 0 < 1 - s := by simp only [mem_Iio] at hs; linarith
  positivity

theorem contDiffOn_hk : ContDiffOn ℝ ∞ (hk n) (Wd n) := by
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ psi1 n p.1) (Wd n) :=
    contDiffOn_psi1.comp contDiff_fst.contDiffOn fun p hp ↦ hp
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ psi2 p.1) (Wd n) :=
    contDiffOn_psi2.comp contDiff_fst.contDiffOn fun p hp ↦ hp
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp contDiff_snd
  exact h1.add (h3.contDiffOn.mul h2)

theorem contDiffOn_kern : ContDiffOn ℝ ∞ (kern n) (Wd n) :=
  Real.contDiff_exp.comp_contDiffOn contDiffOn_hk

theorem norm_iteratedFDeriv_exp (i : ℕ) (t : ℝ) : ‖iteratedFDeriv ℝ i Real.exp t‖ = Real.exp t := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]

/-- The derivatives of `h` grow at most polynomially in `z`, uniformly for `s ∈ [a, b]`. -/
theorem norm_iteratedFDeriv_hk_le (m : ℕ) {a b : ℝ} (hb : b < 1) :
    ∃ A k, 0 ≤ A ∧ ∀ p : ℝ × Gs n, p.1 ∈ Icc a b → ∀ i ≤ m,
      ‖iteratedFDeriv ℝ i (hk n) p‖ ≤ A * (1 + ‖p.2‖) ^ k := by
  obtain ⟨C1, hC1⟩ := exists_bound_iteratedFDeriv (contDiffOn_psi1 (n := n)) m hb (a := a)
  obtain ⟨C2, hC2⟩ := exists_bound_iteratedFDeriv contDiffOn_psi2 m hb (a := a)
  obtain ⟨k, Cq, hCq0, hCq⟩ :=
    (Function.hasTemperateGrowth_norm_sq (Gs n)).norm_iteratedFDeriv_le_uniform m
  refine ⟨|C1| + 2 ^ m * Cq * |C2|, k, by positivity, fun p hp i hi ↦ ?_⟩
  have hpW : p ∈ Wd n := lt_of_le_of_lt hp.2 hb
  have hk1 : (1 : ℝ) ≤ (1 + ‖p.2‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg p.2])
  have hpsi1 : ContDiffAt ℝ i (fun p : ℝ × Gs n ↦ psi1 n p.1) p :=
    ((contDiffOn_psi1.comp contDiff_fst.contDiffOn fun p hp ↦ hp).contDiffAt
      (isOpen_Wd.mem_nhds hpW)).of_le (by exact_mod_cast le_top)
  have hq2 : ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2) (Wd n) :=
    ((contDiff_norm_sq ℝ).comp contDiff_snd).contDiffOn
  have hpsi2 : ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ psi2 p.1) (Wd n) :=
    contDiffOn_psi2.comp contDiff_fst.contDiffOn fun p hp ↦ hp
  have hprod : ContDiffAt ℝ i (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2 * psi2 p.1) p :=
    ((hq2.mul hpsi2).contDiffAt (isOpen_Wd.mem_nhds hpW)).of_le (by exact_mod_cast le_top)
  have hsplit : hk n = (fun p : ℝ × Gs n ↦ psi1 n p.1) + fun p ↦ ‖p.2‖ ^ 2 * psi2 p.1 := rfl
  rw [hsplit, iteratedFDeriv_add_apply hpsi1 hprod]
  refine (norm_add_le _ _).trans ?_
  have e1 : ‖iteratedFDeriv ℝ i (fun p : ℝ × Gs n ↦ psi1 n p.1) p‖ ≤ |C1| * (1 + ‖p.2‖) ^ k :=
    (norm_iteratedFDeriv_comp_fst_le contDiffOn_psi1 hpW i).trans ((hC1 i hi p.1 hp).trans
      ((le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hk1)))
  have e2 : ‖iteratedFDeriv ℝ i (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2 * psi2 p.1) p‖ ≤
      2 ^ m * Cq * |C2| * (1 + ‖p.2‖) ^ k := by
    rw [← iteratedFDerivWithin_of_isOpen i isOpen_Wd hpW]
    refine (norm_iteratedFDerivWithin_mul_le hq2 hpsi2 isOpen_Wd.uniqueDiffOn hpW
      (by exact_mod_cast le_top)).trans ?_
    have hj : ∀ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2) (Wd n) p‖ *
          ‖iteratedFDerivWithin ℝ (i - j) (fun p : ℝ × Gs n ↦ psi2 p.1) (Wd n) p‖ ≤
        (i.choose j : ℝ) * (Cq * (1 + ‖p.2‖) ^ k * |C2|) := by
      intro j hj
      have hji : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [iteratedFDerivWithin_of_isOpen j isOpen_Wd hpW,
        iteratedFDerivWithin_of_isOpen (i - j) isOpen_Wd hpW]
      have hA : ‖iteratedFDeriv ℝ j (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2) p‖ ≤ Cq * (1 + ‖p.2‖) ^ k :=
        (norm_iteratedFDeriv_comp_snd_le (contDiff_norm_sq ℝ) p j).trans
          (hCq j (hji.trans hi) p.2)
      have hB : ‖iteratedFDeriv ℝ (i - j) (fun p : ℝ × Gs n ↦ psi2 p.1) p‖ ≤ |C2| :=
        (norm_iteratedFDeriv_comp_fst_le contDiffOn_psi2 hpW (i - j)).trans
          ((hC2 (i - j) ((Nat.sub_le i j).trans hi) p.1 hp).trans (le_abs_self _))
      have h0' : 0 ≤ Cq * (1 + ‖p.2‖) ^ k :=
        mul_nonneg hCq0 (pow_nonneg (by linarith [norm_nonneg p.2]) _)
      calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun p : ℝ × Gs n ↦ ‖p.2‖ ^ 2) p‖ *
            ‖iteratedFDeriv ℝ (i - j) (fun p : ℝ × Gs n ↦ psi2 p.1) p‖ ≤
            (i.choose j : ℝ) * (Cq * (1 + ‖p.2‖) ^ k) * |C2| :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)) hB (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) h0')
        _ = _ := by ring
    refine (Finset.sum_le_sum hj).trans ?_
    rw [← Finset.sum_mul]
    have hs : ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) = 2 ^ i := by
      exact_mod_cast Nat.sum_range_choose i
    rw [hs]
    have h2 : (2 : ℝ) ^ i ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hi
    have h0 : 0 ≤ Cq * (1 + ‖p.2‖) ^ k * |C2| :=
      mul_nonneg (mul_nonneg hCq0 (pow_nonneg (by linarith [norm_nonneg p.2]) _)) (abs_nonneg _)
    calc (2 : ℝ) ^ i * (Cq * (1 + ‖p.2‖) ^ k * |C2|) ≤ 2 ^ m * (Cq * (1 + ‖p.2‖) ^ k * |C2|) :=
          mul_le_mul_of_nonneg_right h2 h0
      _ = _ := by ring
  linarith

theorem exp_hk_le {a b : ℝ} (hb : b < 1) {C1 : ℝ} (hC1 : ∀ s ∈ Icc a b, |psi1 n s| ≤ C1)
    (p : ℝ × Gs n) (hp : p.1 ∈ Icc a b) :
    Real.exp (hk n p) ≤ Real.exp C1 * Real.exp (-(1 / (2 * (|1 - a| + 1))) * ‖p.2‖ ^ 2) := by
  rw [hk, Real.exp_add]
  have hs : 0 < 1 - p.1 := by linarith [hp.2]
  have hσ : 1 - p.1 ≤ |1 - a| + 1 := by
    have := le_abs_self (1 - a); linarith [hp.1]
  refine mul_le_mul (Real.exp_le_exp.2 ((le_abs_self _).trans (hC1 p.1 hp)))
    (Real.exp_le_exp.2 ?_) (by positivity) (by positivity)
  have : (2 * (|1 - a| + 1))⁻¹ ≤ (2 * (1 - p.1))⁻¹ := by
    gcongr
  have hz := sq_nonneg ‖p.2‖
  simp only [psi2, one_div]
  nlinarith

/-- The derivatives of the heat kernel are Gaussian-dominated, uniformly for `s ∈ [a, b]`. -/
theorem norm_iteratedFDeriv_kern_le (m : ℕ) {a b : ℝ} (hb : b < 1) :
    ∃ C c, 0 < c ∧ ∀ p : ℝ × Gs n, p.1 ∈ Icc a b →
      ‖iteratedFDeriv ℝ m (kern n) p‖ ≤ C * Real.exp (-c * ‖p.2‖ ^ 2) := by
  obtain ⟨A, k, hA0, hA⟩ := norm_iteratedFDeriv_hk_le (n := n) m hb (a := a)
  obtain ⟨C1, hC1⟩ := exists_bound_iteratedFDeriv (contDiffOn_psi1 (n := n)) 0 hb (a := a)
  have hC1' : ∀ s ∈ Icc a b, |psi1 n s| ≤ C1 := fun s hs ↦ by
    simpa [norm_iteratedFDeriv_zero] using hC1 0 le_rfl s hs
  set σ := |1 - a| + 1 with hσ
  have hσ0 : 0 < σ := by positivity
  obtain ⟨C4, hC4⟩ := one_add_pow_mul_exp_le (k * m) (c := 1 / (2 * σ)) (by positivity)
  refine ⟨(m.factorial : ℝ) * Real.exp C1 * (1 + A) ^ m * C4, 1 / (2 * σ) / 2, by positivity,
    fun p hp ↦ ?_⟩
  have hpW : p ∈ Wd n := lt_of_le_of_lt hp.2 hb
  set D := (1 + A) * (1 + ‖p.2‖) ^ k with hD
  have hk1 : (1 : ℝ) ≤ (1 + ‖p.2‖) ^ k := one_le_pow₀ (by linarith [norm_nonneg p.2])
  have hD1 : 1 ≤ D := by
    rw [hD]; nlinarith
  have hF := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := hk n) (n := m)
    (s := Wd n) (t := univ) (x := p) (N := ∞) Real.contDiff_exp.contDiffOn contDiffOn_hk
    (by exact_mod_cast le_top) uniqueDiffOn_univ isOpen_Wd.uniqueDiffOn (mapsTo_univ _ _) hpW
    (C := Real.exp (hk n p)) (D := D)
    (fun i _ ↦ by rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_exp])
    (fun i hi1 him ↦ by
      rw [iteratedFDerivWithin_of_isOpen i isOpen_Wd hpW]
      refine (hA p hp i him).trans ?_
      calc A * (1 + ‖p.2‖) ^ k ≤ D := by rw [hD]; nlinarith
        _ ≤ D ^ i := le_self_pow₀ hD1 (by omega))
  rw [iteratedFDerivWithin_of_isOpen m isOpen_Wd hpW] at hF
  change ‖iteratedFDeriv ℝ m (Real.exp ∘ hk n) p‖ ≤ _
  refine hF.trans ?_
  have he := exp_hk_le hb hC1' p hp
  have h4 := hC4 ‖p.2‖ (norm_nonneg _)
  rw [← hσ] at he
  have hDm : D ^ m = (1 + A) ^ m * (1 + ‖p.2‖) ^ (k * m) := by
    rw [hD, mul_pow, pow_mul]
  rw [hDm]
  calc (m.factorial : ℝ) * Real.exp (hk n p) * ((1 + A) ^ m * (1 + ‖p.2‖) ^ (k * m))
      ≤ (m.factorial : ℝ) * (Real.exp C1 * Real.exp (-(1 / (2 * σ)) * ‖p.2‖ ^ 2)) *
          ((1 + A) ^ m * (1 + ‖p.2‖) ^ (k * m)) := by gcongr
    _ = (m.factorial : ℝ) * Real.exp C1 * (1 + A) ^ m *
          ((1 + ‖p.2‖) ^ (k * m) * Real.exp (-(1 / (2 * σ)) * ‖p.2‖ ^ 2)) := by ring
    _ ≤ (m.factorial : ℝ) * Real.exp C1 * (1 + A) ^ m *
          (C4 * Real.exp (-(1 / (2 * σ) / 2) * ‖p.2‖ ^ 2)) := by gcongr
    _ = _ := by ring

theorem kDom_kern (m : ℕ) :
    KDom (ContinuousLinearMap.inr ℝ ℝ (Gs n)) (Wd n) (iteratedFDeriv ℝ m (kern n)) := by
  intro p₀ hp₀
  have hp₀' : p₀.1 < 1 := hp₀
  obtain ⟨C, c, hc, hC⟩ := norm_iteratedFDeriv_kern_le (n := n) m (a := p₀.1 - 1)
    (b := (1 + p₀.1) / 2) (by linarith)
  set R := ‖p₀.2‖ + 1
  refine ⟨min 1 ((1 - p₀.1) / 2), lt_min one_pos (by linarith), fun w ↦
    C * Real.exp (c * R ^ 2) * Real.exp (-(c / 2) * ‖w‖ ^ 2), ?_, fun p hp w ↦ ?_⟩
  · exact (integrable_exp_neg_mul_sq_norm (by positivity)).const_mul _
  · rw [mem_ball, Prod.dist_eq, max_lt_iff] at hp
    have h1 : dist p.1 p₀.1 < 1 := lt_of_lt_of_le hp.1 (min_le_left _ _)
    have h1' : dist p.1 p₀.1 < (1 - p₀.1) / 2 := lt_of_lt_of_le hp.1 (min_le_right _ _)
    have h2 : dist p.2 p₀.2 < 1 := lt_of_lt_of_le hp.2 (min_le_left _ _)
    rw [Real.dist_eq, abs_lt] at h1 h1'
    have hpI : (p - (ContinuousLinearMap.inr ℝ ℝ (Gs n)) w).1 ∈
        Icc (p₀.1 - 1) ((1 + p₀.1) / 2) := by
      simp only [Prod.fst_sub, ContinuousLinearMap.inr_apply, sub_zero]
      constructor <;> linarith
    have hC0 : 0 ≤ C := by
      have h := (norm_nonneg _).trans (hC _ hpI)
      by_contra hneg
      rw [not_le] at hneg
      nlinarith [Real.exp_pos (-c * ‖(p - (ContinuousLinearMap.inr ℝ ℝ (Gs n)) w).2‖ ^ 2)]
    refine (hC _ hpI).trans ?_
    simp only [Prod.snd_sub, ContinuousLinearMap.inr_apply]
    have hx : ‖p.2‖ ≤ R := by
      have := norm_le_norm_add_norm_sub' p.2 p₀.2
      rw [dist_eq_norm] at h2
      linarith [norm_sub_rev p.2 p₀.2]
    have hw : ‖w‖ ≤ ‖p.2‖ + ‖p.2 - w‖ := by
      have := norm_sub_le p.2 (p.2 - w)
      simpa using this
    have key : -c * ‖p.2 - w‖ ^ 2 ≤ c * R ^ 2 + -(c / 2) * ‖w‖ ^ 2 := by
      have h3 : ‖w‖ ^ 2 ≤ 2 * ‖p.2 - w‖ ^ 2 + 2 * R ^ 2 := by
        have h4 := pow_le_pow_left₀ (norm_nonneg w) hw 2
        have h5 := pow_le_pow_left₀ (norm_nonneg _) hx 2
        nlinarith [sq_nonneg (‖p.2‖ - ‖p.2 - w‖)]
      nlinarith
    rw [mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 key) hC0

theorem exp_neg_half_mul_log {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Real.exp (-((k : ℝ) / 2) * Real.log t) = (√t)⁻¹ ^ k := by
  rw [← Real.exp_log (Real.sqrt_pos.2 ht), ← Real.exp_neg, ← Real.exp_nat_mul, Real.log_sqrt ht.le]
  congr 1
  ring

/-- Change of variables to Lebesgue measure: `E Φ(Z) = ∫ p_σ(x - w) Φ((w - x)/√σ) dw`. -/
theorem integral_gm_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Φ : Gs n → V) {σ : ℝ} (hσ : 0 < σ) (x : Gs n) :
    ∫ y, Φ y ∂gm n = ∫ w, ((√(2 * π * σ))⁻¹ ^ n * Real.exp (-‖x - w‖ ^ 2 / (2 * σ))) •
      Φ ((√σ)⁻¹ • (w - x)) := by
  set c := (√σ)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hσ)
  have hγ : gm n = volume.withDensity (fun x ↦ ENNReal.ofReal (Ito.stdDensity x)) :=
    Ito.stdGaussian_density
  rw [hγ, integral_withDensity_eq_integral_toReal_smul
    (Ito.measurable_stdDensity.ennreal_ofReal) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (Ito.stdDensity_pos _).le]
  have h1 := Measure.integral_comp_smul (volume : Measure (Gs n))
    (fun y ↦ Ito.stdDensity y • Φ y) c
  have h2 := integral_sub_right_eq_self (μ := (volume : Measure (Gs n)))
    (fun z ↦ Ito.stdDensity (c • z) • Φ (c • z)) x
  rw [finrank_euclideanSpace_fin] at h1
  rw [← h2] at h1
  have hc2 : c ^ 2 = σ⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hσ.le]
  have hK : ∀ w, ((√(2 * π * σ))⁻¹ ^ n * Real.exp (-‖x - w‖ ^ 2 / (2 * σ))) =
      c ^ n * Ito.stdDensity (c • (w - x)) := by
    intro w
    rw [Ito.stdDensity_eq, Fintype.card_fin, norm_smul, Real.norm_eq_abs, abs_of_pos hc0,
      Real.sqrt_mul (by positivity) σ, mul_inv, mul_pow, norm_sub_rev x w]
    have he : -(c * ‖w - x‖) ^ 2 / 2 = -‖w - x‖ ^ 2 / (2 * σ) := by
      rw [mul_pow, hc2]; field_simp
    rw [he, hc]
    ring
  simp_rw [hK, mul_smul]
  rw [integral_smul, h1, smul_smul, abs_inv, abs_of_pos (pow_pos hc0 n),
    mul_inv_cancel₀ (pow_pos hc0 n).ne', one_smul]

/-! ### Explicit derivatives of the heat kernel -/

theorem hasDerivAt_psi1 {s : ℝ} (hs : s < 1) :
    HasDerivAt (psi1 n) ((n : ℝ) / 2 / (1 - s)) s := by
  have h : 0 < 1 - s := by linarith
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h1 : HasDerivAt (fun s : ℝ ↦ 2 * π * (1 - s)) (2 * π * (0 - 1)) s :=
    ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).const_mul (2 * π)
  have h2 : HasDerivAt (psi1 n) (-((n : ℝ) / 2) * ((2 * π * (0 - 1)) / (2 * π * (1 - s)))) s :=
    (h1.log (by positivity)).const_mul (-((n : ℝ) / 2))
  refine h2.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_psi2 {s : ℝ} (hs : s < 1) :
    HasDerivAt psi2 (-(1 / (2 * (1 - s) ^ 2))) s := by
  have h : 0 < 1 - s := by linarith
  have h1 : HasDerivAt (fun s : ℝ ↦ 2 * (1 - s)) (2 * (0 - 1)) s :=
    ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).const_mul 2
  have h2 : HasDerivAt (fun s : ℝ ↦ (-1) * (2 * (1 - s))⁻¹)
      ((-1) * (-(2 * (0 - 1)) / (2 * (1 - s)) ^ 2)) s :=
    (h1.inv (by positivity)).const_mul (-1)
  have h3 : HasDerivAt psi2 ((-1) * (-(2 * (0 - 1)) / (2 * (1 - s)) ^ 2)) s :=
    h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ by simp [psi2])
  refine h3.congr_deriv ?_
  field_simp
  ring

theorem hasFDerivAt_hk {q : ℝ × Gs n} (hq : q.1 < 1) :
    HasFDerivAt (hk n)
      (((n : ℝ) / 2 / (1 - q.1) - ‖q.2‖ ^ 2 / (2 * (1 - q.1) ^ 2)) •
          ContinuousLinearMap.fst ℝ ℝ (Gs n) -
        (1 - q.1)⁻¹ • (innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ (Gs n))) q := by
  have h : 0 < 1 - q.1 := by linarith
  have h1 := (hasDerivAt_psi1 (n := n) hq).hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have h2 := (hasDerivAt_psi2 hq).hasFDerivAt.comp q (hasFDerivAt_fst (p := q))
  have h3 := (hasFDerivAt_snd (p := q)).norm_sq
  have h4 := h1.add (h3.mul h2)
  have h5 := h4.congr_of_eventuallyEq (f₁ := hk n) (Filter.Eventually.of_forall fun p ↦ by
    simp [hk])
  refine h5.congr_fderiv (ContinuousLinearMap.ext fun d ↦ ?_)
  obtain ⟨a, v⟩ := d
  simp [psi2]
  field_simp
  ring


/-- The derivative of `log p` at `q`. -/
noncomputable def Lhk (n : ℕ) (q : ℝ × Gs n) : ℝ × Gs n →L[ℝ] ℝ :=
  ((n : ℝ) / 2 / (1 - q.1) - ‖q.2‖ ^ 2 / (2 * (1 - q.1) ^ 2)) •
    ContinuousLinearMap.fst ℝ ℝ (Gs n) -
  (1 - q.1)⁻¹ • (innerSL ℝ q.2).comp (ContinuousLinearMap.snd ℝ ℝ (Gs n))

theorem Lhk_apply (q : ℝ × Gs n) (a : ℝ) (v : Gs n) :
    Lhk n q (a, v) = a * ((n : ℝ) / 2 / (1 - q.1) - ‖q.2‖ ^ 2 / (2 * (1 - q.1) ^ 2)) -
      (1 - q.1)⁻¹ * ⟪q.2, v⟫ := by
  simp [Lhk]
  ring

theorem hasFDerivAt_kern {q : ℝ × Gs n} (hq : q.1 < 1) :
    HasFDerivAt (kern n) (kern n q • Lhk n q) q :=
  (hasFDerivAt_hk hq).exp

theorem fderiv_kern_apply {q : ℝ × Gs n} (hq : q.1 < 1) (a : ℝ) (v : Gs n) :
    fderiv ℝ (kern n) q (a, v) = kern n q *
      (a * ((n : ℝ) / 2 / (1 - q.1) - ‖q.2‖ ^ 2 / (2 * (1 - q.1) ^ 2)) -
        (1 - q.1)⁻¹ * ⟪q.2, v⟫) := by
  rw [(hasFDerivAt_kern hq).fderiv, smul_apply, Lhk_apply, smul_eq_mul]

/-- `ℓ_w(q) = -(1-s)⁻¹ ⟨z, w⟩`. -/
theorem hasFDerivAt_ell {q : ℝ × Gs n} (hq : q.1 < 1) (w : Gs n) :
    HasFDerivAt (fun q : ℝ × Gs n ↦ -(1 - q.1)⁻¹ * ⟪q.2, w⟫)
      (-(((1 - q.1) ^ 2)⁻¹ * ⟪q.2, w⟫) • ContinuousLinearMap.fst ℝ ℝ (Gs n) -
        (1 - q.1)⁻¹ • (innerSL ℝ w).comp (ContinuousLinearMap.snd ℝ ℝ (Gs n))) q := by
  have h : (1 - q.1) ≠ 0 := by linarith
  have h0 : HasDerivAt (fun s : ℝ ↦ -(1 - s)⁻¹) (-(-(0 - 1) / (1 - q.1) ^ 2)) q.1 :=
    (((hasDerivAt_const q.1 (1 : ℝ)).sub (hasDerivAt_id q.1)).inv h).neg
  have h1 := h0.hasFDerivAt.comp q (hasFDerivAt_fst (𝕜 := ℝ) (p := q))
  have h2 : HasFDerivAt (fun q : ℝ × Gs n ↦ ⟪q.2, w⟫)
      ((innerSL ℝ w).comp (ContinuousLinearMap.snd ℝ ℝ (Gs n))) q := by
    have := ((innerSL ℝ w).comp (ContinuousLinearMap.snd ℝ ℝ (Gs n))).hasFDerivAt (x := q)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ ?_)
    simp [real_inner_comm]
  have h3 := h1.mul h2
  refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun p ↦ by simp)).congr_fderiv
    (ContinuousLinearMap.ext fun d ↦ ?_)
  obtain ⟨a, u⟩ := d
  simp [real_inner_comm]
  field_simp
  ring

theorem hasFDerivAt_r {q : ℝ × Gs n} (hq : q.1 < 1) :
    HasFDerivAt (fun q : ℝ × Gs n ↦ -(1 - q.1)⁻¹)
      (-((1 - q.1) ^ 2)⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Gs n)) q := by
  have h : (1 - q.1) ≠ 0 := by linarith
  have h0 : HasDerivAt (fun s : ℝ ↦ -(1 - s)⁻¹) (-(-(0 - 1) / (1 - q.1) ^ 2)) q.1 :=
    (((hasDerivAt_const q.1 (1 : ℝ)).sub (hasDerivAt_id q.1)).inv h).neg
  have h1 := h0.hasFDerivAt.comp q (hasFDerivAt_fst (𝕜 := ℝ) (p := q))
  refine h1.congr_fderiv (ContinuousLinearMap.ext fun d ↦ ?_)
  obtain ⟨a, u⟩ := d
  simp
  field_simp

theorem differentiableAt_fderiv_kern {q : ℝ × Gs n} (hq : q.1 < 1) :
    DifferentiableAt ℝ (fderiv ℝ (kern n)) q :=
  (((contDiffOn_kern (n := n)).contDiffAt (isOpen_Wd.mem_nhds hq)).fderiv_right
    (m := 1) (by simp)).differentiableAt (by simp)

theorem fderiv_fderiv_apply_eq {F : ℝ × Gs n → ℝ} {q : ℝ × Gs n}
    (hd : DifferentiableAt ℝ (fderiv ℝ F) q) (d₁ d₂ : ℝ × Gs n) :
    fderiv ℝ (fderiv ℝ F) q d₁ d₂ = fderiv ℝ (fun q' ↦ fderiv ℝ F q' d₂) q d₁ := by
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem fderiv_fderiv_kern_apply {q : ℝ × Gs n} (hq : q.1 < 1) (v w : Gs n) :
    fderiv ℝ (fderiv ℝ (kern n)) q (0, v) (0, w) = kern n q *
      (((1 - q.1) ^ 2)⁻¹ * ⟪q.2, v⟫ * ⟪q.2, w⟫ - (1 - q.1)⁻¹ * ⟪v, w⟫) := by
  rw [fderiv_fderiv_apply_eq (differentiableAt_fderiv_kern hq)]
  have heq : (fun q' ↦ fderiv ℝ (kern n) q' (0, w)) =ᶠ[𝓝 q]
      fun q' : ℝ × Gs n ↦ kern n q' * (-(1 - q'.1)⁻¹ * ⟪q'.2, w⟫) := by
    filter_upwards [isOpen_Wd.mem_nhds (show q ∈ Wd n from hq)] with q' hq'
    rw [fderiv_kern_apply hq']
    ring
  rw [heq.fderiv_eq, ((hasFDerivAt_kern hq).fun_mul (hasFDerivAt_ell hq w)).fderiv]
  have h : (1 - q.1) ≠ 0 := by linarith
  simp [Lhk_apply, real_inner_comm]
  field_simp
  ring

/-- The kernel of `∂_v u`: `κ_v(q) = ∂_{(0,v)} p(q)`. -/
noncomputable def kernV (n : ℕ) (v : Gs n) (q : ℝ × Gs n) : ℝ := fderiv ℝ (kern n) q (0, v)

theorem kernV_eventuallyEq {q : ℝ × Gs n} (hq : q.1 < 1) (v : Gs n) :
    kernV n v =ᶠ[𝓝 q] fun q' : ℝ × Gs n ↦ kern n q' * (-(1 - q'.1)⁻¹ * ⟪q'.2, v⟫) := by
  filter_upwards [isOpen_Wd.mem_nhds (show q ∈ Wd n from hq)] with q' hq'
  rw [kernV, fderiv_kern_apply hq']
  ring

theorem fderiv_kernV_apply {q : ℝ × Gs n} (hq : q.1 < 1) (v : Gs n) (a : ℝ) (u : Gs n) :
    fderiv ℝ (kernV n v) q (a, u) = kern n q *
      ((a * ((n : ℝ) / 2 / (1 - q.1) - ‖q.2‖ ^ 2 / (2 * (1 - q.1) ^ 2)) -
          (1 - q.1)⁻¹ * ⟪q.2, u⟫) * (-(1 - q.1)⁻¹ * ⟪q.2, v⟫) +
        (-(((1 - q.1) ^ 2)⁻¹ * ⟪q.2, v⟫) * a - (1 - q.1)⁻¹ * ⟪v, u⟫)) := by
  rw [(kernV_eventuallyEq hq v).fderiv_eq,
    ((hasFDerivAt_kern hq).fun_mul (hasFDerivAt_ell hq v)).fderiv]
  simp [Lhk_apply]
  ring

theorem fderiv_kernV_time {q : ℝ × Gs n} (hq : q.1 < 1) (v : Gs n) :
    fderiv ℝ (kernV n v) q (1, 0) = kern n q * ⟪q.2, v⟫ *
      (-(n : ℝ) / (2 * (1 - q.1) ^ 2) + ‖q.2‖ ^ 2 / (2 * (1 - q.1) ^ 3) - ((1 - q.1) ^ 2)⁻¹) := by
  have h : (1 - q.1) ≠ 0 := by linarith
  rw [fderiv_kernV_apply hq]
  simp only [inner_zero_right, mul_zero, sub_zero, one_mul]
  field_simp
  ring

theorem contDiffOn_kernV (v : Gs n) : ContDiffOn ℝ ∞ (kernV n v) (Wd n) :=
  (contDiffOn_kern.fderiv_of_isOpen isOpen_Wd (m := ∞) (by simp)).clm_apply contDiffOn_const

theorem differentiableAt_fderiv_kernV {q : ℝ × Gs n} (hq : q.1 < 1) (v : Gs n) :
    DifferentiableAt ℝ (fderiv ℝ (kernV n v)) q :=
  (((contDiffOn_kernV v).contDiffAt (isOpen_Wd.mem_nhds hq)).fderiv_right
    (m := 1) (by simp)).differentiableAt (by simp)

theorem fderiv_fderiv_kernV_apply {q : ℝ × Gs n} (hq : q.1 < 1) (v u₁ u₂ : Gs n) :
    fderiv ℝ (fderiv ℝ (kernV n v)) q (0, u₁) (0, u₂) = kern n q *
      ((-(1 - q.1)⁻¹ * ⟪q.2, u₁⟫) * (((1 - q.1) ^ 2)⁻¹ * ⟪q.2, u₂⟫ * ⟪q.2, v⟫ -
          (1 - q.1)⁻¹ * ⟪v, u₂⟫) +
        ((1 - q.1) ^ 2)⁻¹ * ⟪u₂, u₁⟫ * ⟪q.2, v⟫ + ((1 - q.1) ^ 2)⁻¹ * ⟪q.2, u₂⟫ * ⟪v, u₁⟫) := by
  have h : (1 - q.1) ≠ 0 := by linarith
  rw [fderiv_fderiv_apply_eq (differentiableAt_fderiv_kernV hq v)]
  have heq : (fun q' ↦ fderiv ℝ (kernV n v) q' (0, u₂)) =ᶠ[𝓝 q]
      fun q' : ℝ × Gs n ↦ kern n q' * ((-(1 - q'.1)⁻¹ * ⟪q'.2, u₂⟫) *
        (-(1 - q'.1)⁻¹ * ⟪q'.2, v⟫) + (-(1 - q'.1)⁻¹) * ⟪v, u₂⟫) := by
    filter_upwards [isOpen_Wd.mem_nhds (show q ∈ Wd n from hq)] with q' hq'
    rw [fderiv_kernV_apply hq']
    ring
  have hd := (hasFDerivAt_kern hq).fun_mul (((hasFDerivAt_ell hq u₂).fun_mul
    (hasFDerivAt_ell hq v)).fun_add ((hasFDerivAt_r hq).mul_const ⟪v, u₂⟫))
  rw [heq.fderiv_eq, hd.fderiv]
  simp [Lhk_apply]
  field_simp
  ring

theorem sum_inner_basis_mul (z v : Gs n) :
    ∑ i, ⟪z, EuclideanSpace.basisFun (Fin n) ℝ i⟫ * ⟪v, EuclideanSpace.basisFun (Fin n) ℝ i⟫ =
      ⟪z, v⟫ := by
  have := (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner z v
  simpa [real_inner_comm] using this

theorem sum_inner_basis_sq (z : Gs n) :
    ∑ i, ⟪z, EuclideanSpace.basisFun (Fin n) ℝ i⟫ ^ 2 = ‖z‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← sum_inner_basis_mul z z]
  simp [sq]

theorem sum_inner_basis_self :
    ∑ i, ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i⟫ = n := by
  simp

/-- The heat kernel solves the backward heat equation. -/
theorem kern_heat {q : ℝ × Gs n} (hq : q ∈ Wd n) :
    fderiv ℝ (kern n) q (1, 0) = -(1 / 2) * ∑ i,
      fderiv ℝ (fderiv ℝ (kern n)) q (0, EuclideanSpace.basisFun (Fin n) ℝ i)
        (0, EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hq' : q.1 < 1 := hq
  have h : (1 - q.1) ≠ 0 := by linarith
  simp_rw [fderiv_fderiv_kern_apply hq', fderiv_kern_apply hq']
  have e : ∀ i, kern n q * (((1 - q.1) ^ 2)⁻¹ * ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ *
      ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ - (1 - q.1)⁻¹ *
        ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i⟫) =
      kern n q * ((1 - q.1) ^ 2)⁻¹ * ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ ^ 2 -
        kern n q * (1 - q.1)⁻¹ *
          ⟪EuclideanSpace.basisFun (Fin n) ℝ i, EuclideanSpace.basisFun (Fin n) ℝ i⟫ :=
    fun i ↦ by ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, sum_inner_basis_sq,
    sum_inner_basis_self]
  simp only [inner_zero_right, mul_zero, sub_zero, one_mul]
  field_simp
  ring

theorem kernV_heat (v : Gs n) {q : ℝ × Gs n} (hq : q ∈ Wd n) :
    fderiv ℝ (kernV n v) q (1, 0) = -(1 / 2) * ∑ i,
      fderiv ℝ (fderiv ℝ (kernV n v)) q (0, EuclideanSpace.basisFun (Fin n) ℝ i)
        (0, EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hq' : q.1 < 1 := hq
  have h : (1 - q.1) ≠ 0 := by linarith
  simp_rw [fderiv_fderiv_kernV_apply hq', fderiv_kernV_time hq']
  have e : ∀ i, kern n q * ((-(1 - q.1)⁻¹ * ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫) *
        (((1 - q.1) ^ 2)⁻¹ * ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ * ⟪q.2, v⟫ -
          (1 - q.1)⁻¹ * ⟪v, EuclideanSpace.basisFun (Fin n) ℝ i⟫) +
        ((1 - q.1) ^ 2)⁻¹ * ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          EuclideanSpace.basisFun (Fin n) ℝ i⟫ * ⟪q.2, v⟫ +
        ((1 - q.1) ^ 2)⁻¹ * ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ *
          ⟪v, EuclideanSpace.basisFun (Fin n) ℝ i⟫) =
      -(kern n q * ((1 - q.1) ^ 3)⁻¹ * ⟪q.2, v⟫) * ⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ ^ 2 +
        2 * kern n q * ((1 - q.1) ^ 2)⁻¹ * (⟪q.2, EuclideanSpace.basisFun (Fin n) ℝ i⟫ *
          ⟪v, EuclideanSpace.basisFun (Fin n) ℝ i⟫) +
        kern n q * ((1 - q.1) ^ 2)⁻¹ * ⟪q.2, v⟫ * ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
          EuclideanSpace.basisFun (Fin n) ℝ i⟫ := fun i ↦ by
    field_simp
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_inner_basis_sq, sum_inner_basis_mul, sum_inner_basis_self]
  field_simp
  ring

theorem norm_iteratedFDeriv_kernV_le (v : Gs n) (m : ℕ) {q : ℝ × Gs n} (hq : q ∈ Wd n) :
    ‖iteratedFDeriv ℝ m (kernV n v) q‖ ≤
      ‖((0 : ℝ), v)‖ * ‖iteratedFDeriv ℝ (m + 1) (kern n) q‖ := by
  have hc : ContDiffOn ℝ ∞ (fderiv ℝ (kern n)) (Wd n) :=
    contDiffOn_kern.fderiv_of_isOpen isOpen_Wd (m := ∞) (by simp)
  have h := (ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), v)).iteratedFDerivWithin_comp_left (hc q hq)
    isOpen_Wd.uniqueDiffOn hq (i := m) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen m isOpen_Wd hq,
    iteratedFDerivWithin_of_isOpen m isOpen_Wd hq] at h
  change ‖iteratedFDeriv ℝ m ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), v)) ∘
    fderiv ℝ (kern n)) q‖ ≤ _
  rw [h, ← norm_iteratedFDeriv_fderiv]
  refine ((ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), v)).norm_compContinuousMultilinearMap_le
    _).trans ?_
  gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun L ↦ ?_
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact L.le_opNorm _

theorem kDom_kernV (v : Gs n) (m : ℕ) :
    KDom (ContinuousLinearMap.inr ℝ ℝ (Gs n)) (Wd n) (iteratedFDeriv ℝ m (kernV n v)) := by
  intro p₀ hp₀
  obtain ⟨ε, hε, bd, hbd, hb⟩ := kDom_kern (m + 1) p₀ hp₀
  have hp₀' : p₀.1 < 1 := hp₀
  refine ⟨min ε ((1 - p₀.1) / 2), lt_min hε (by linarith), fun w ↦ ‖((0 : ℝ), v)‖ * bd w,
    hbd.const_mul _, fun p hp w ↦ ?_⟩
  have hp1 : p ∈ ball p₀ ε := ball_subset_ball (min_le_left _ _) hp
  have hp2 := mem_ball.1 hp
  rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, abs_lt] at hp2
  have hpW : p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w ∈ Wd n := by
    change p.1 - 0 < 1
    have := hp2.1.2
    have := min_le_right ε ((1 - p₀.1) / 2)
    linarith
  exact (norm_iteratedFDeriv_kernV_le v m hpW).trans
    (mul_le_mul_of_nonneg_left (hb p hp1 w) (norm_nonneg _))

/-! ### Slices and the heat equation for kernel integrals -/

theorem mem_Wd_sub_inr {p : ℝ × Gs n} (hp : p ∈ Wd n) (w : Gs n) :
    p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w ∈ Wd n := by
  simpa [Wd] using hp

theorem fderiv_slice {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {U : ℝ × Gs n → F}
    {s : ℝ} {y : Gs n} (hU : DifferentiableAt ℝ U (s, y)) :
    fderiv ℝ (fun y ↦ U (s, y)) y = (fderiv ℝ U (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Gs n)) :=
  (hU.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)).fderiv

theorem fderiv_fderiv_slice {U : ℝ × Gs n → ℝ} {s : ℝ} {x : Gs n}
    (hU : ∀ y, DifferentiableAt ℝ U (s, y)) (hU' : DifferentiableAt ℝ (fderiv ℝ U) (s, x))
    (v w : Gs n) :
    fderiv ℝ (fderiv ℝ (fun y ↦ U (s, y))) x v w = fderiv ℝ (fderiv ℝ U) (s, x) (0, v) (0, w) := by
  have e : fderiv ℝ (fun y ↦ U (s, y)) =
      fun y ↦ (fderiv ℝ U (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ (Gs n)) :=
    funext fun y ↦ fderiv_slice (hU y)
  rw [e]
  have hc : HasFDerivAt (fun y ↦ fderiv ℝ U (s, y))
      ((fderiv ℝ (fderiv ℝ U) (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Gs n))) x :=
    hU'.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)
  have := hc.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ (Gs n)) x)
  rw [this.fderiv]
  simp

theorem integrable_apply_mlm {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {m : ℕ}
    {A : Gs n → ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ P) ℝ} (hA : Integrable A)
    (v : Fin m → P) : Integrable (fun w ↦ A w v) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ P) ℝ v).integrable_comp hA

section Transfer

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, |f x| ≤ 1)
  {φ : ℝ × Gs n → ℝ} (hφ : ContDiffOn ℝ ∞ φ (Wd n))
  (hdom : ∀ m, KDom (ContinuousLinearMap.inr ℝ ℝ (Gs n)) (Wd n) (iteratedFDeriv ℝ m φ))
include hf h01 hφ hdom

theorem taylor_kInt :
    HasFTaylorSeriesUpToOn ∞ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ)
      (fun p m ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (iteratedFDeriv ℝ m φ) p) (Wd n) :=
  hasFTaylorSeriesUpToOn_kInt isOpen_Wd (fun _ hp w ↦ mem_Wd_sub_inr hp w) hf h01 hφ hdom

theorem iteratedFDeriv_kInt_eq (m : ℕ) {p : ℝ × Gs n} (hp : p ∈ Wd n) :
    iteratedFDeriv ℝ m (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ) p =
      kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (iteratedFDeriv ℝ m φ) p := by
  rw [← iteratedFDerivWithin_of_isOpen m isOpen_Wd hp]
  exact ((taylor_kInt hf h01 hφ hdom).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast le_top) isOpen_Wd.uniqueDiffOn hp).symm

theorem integrable_kInt_apply (m : ℕ) {p : ℝ × Gs n} (hp : p ∈ Wd n) (v : Fin m → ℝ × Gs n) :
    Integrable (fun w ↦
      f w * iteratedFDeriv ℝ m φ (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) v) := by
  have := integrable_kInt (fun _ hp w ↦ mem_Wd_sub_inr hp w) hf h01
    (continuousOn_iteratedFDeriv isOpen_Wd hφ m)
    (hdom m) hp
  simpa using integrable_apply_mlm this v

theorem kInt_iteratedFDeriv_apply (m : ℕ) {p : ℝ × Gs n} (hp : p ∈ Wd n) (v : Fin m → ℝ × Gs n) :
    iteratedFDeriv ℝ m (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ) p v =
      ∫ w, f w * iteratedFDeriv ℝ m φ (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) v := by
  rw [iteratedFDeriv_kInt_eq hf h01 hφ hdom m hp, kInt, ContinuousMultilinearMap.integral_apply]
  · simp
  · exact integrable_kInt (fun _ hp w ↦ mem_Wd_sub_inr hp w) hf h01
      (continuousOn_iteratedFDeriv isOpen_Wd hφ m)
      (hdom m) hp

theorem fderiv_kInt_apply {p : ℝ × Gs n} (hp : p ∈ Wd n) (d : ℝ × Gs n) :
    fderiv ℝ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ) p d =
      ∫ w, f w * fderiv ℝ φ (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) d := by
  have := kInt_iteratedFDeriv_apply hf h01 hφ hdom 1 hp ![d]
  simpa [iteratedFDeriv_one_apply] using this

theorem fderiv_fderiv_kInt_apply {p : ℝ × Gs n} (hp : p ∈ Wd n) (d₁ d₂ : ℝ × Gs n) :
    fderiv ℝ (fderiv ℝ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ)) p d₁ d₂ =
      ∫ w, f w * fderiv ℝ (fderiv ℝ φ) (p - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) d₁ d₂ := by
  have := kInt_iteratedFDeriv_apply hf h01 hφ hdom 2 hp ![d₁, d₂]
  simpa [iteratedFDeriv_two_apply] using this

theorem differentiableAt_kInt {p : ℝ × Gs n} (hp : p ∈ Wd n) :
    DifferentiableAt ℝ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ) p :=
  (((taylor_kInt hf h01 hφ hdom).contDiffOn.contDiffAt (isOpen_Wd.mem_nhds hp)).differentiableAt
    (by simp))

theorem differentiableAt_fderiv_kInt {p : ℝ × Gs n} (hp : p ∈ Wd n) :
    DifferentiableAt ℝ (fderiv ℝ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ)) p :=
  ((((taylor_kInt hf h01 hφ hdom).contDiffOn.contDiffAt (isOpen_Wd.mem_nhds hp)).fderiv_right
    (m := 1) (by simp)).differentiableAt
      (by simp))

/-- If the kernel solves the backward heat equation `∂_s φ = -½ Δ_z φ`, so does its kernel
integral. -/
theorem hasDerivAt_kInt_time
    (hheat : ∀ q ∈ Wd n, fderiv ℝ φ q (1, 0) = -(1 / 2) * ∑ i,
      fderiv ℝ (fderiv ℝ φ) q (0, EuclideanSpace.basisFun (Fin n) ℝ i)
        (0, EuclideanSpace.basisFun (Fin n) ℝ i))
    {s : ℝ} (hs : s < 1) (x : Gs n) :
    HasDerivAt (fun s ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ (s, x))
      (-(1 / 2) * Laplacian.laplacian
        (fun y ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ (s, y)) x) s := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hp : ((s, x) : ℝ × Gs n) ∈ Wd n := hs
  have h1 := (differentiableAt_kInt hf h01 hφ hdom hp).hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s x))
  refine h1.congr_deriv ?_
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hsl : ∀ i, fderiv ℝ (fderiv ℝ fun y ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ (s, y))
      x (b i) (b i) = fderiv ℝ (fderiv ℝ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ)) (s, x)
        (0, b i) (0, b i) := fun i ↦
    fderiv_fderiv_slice (fun y ↦ differentiableAt_kInt hf h01 hφ hdom (show (s, y) ∈ Wd n from hs))
      (differentiableAt_fderiv_kInt hf h01 hφ hdom hp) _ _
  simp_rw [hsl, fderiv_fderiv_kInt_apply hf h01 hφ hdom hp]
  change (fderiv ℝ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f φ) (s, x)) ((1 : ℝ), (0 : Gs n)) = _
  rw [fderiv_kInt_apply hf h01 hφ hdom hp]
  have hint : ∀ i, Integrable (fun w ↦ f w * fderiv ℝ (fderiv ℝ φ)
      ((s, x) - ContinuousLinearMap.inr ℝ ℝ (Gs n) w) (0, b i) (0, b i)) := fun i ↦ by
    simpa [iteratedFDeriv_two_apply] using
      integrable_kInt_apply hf h01 hφ hdom 2 hp ![(0, b i), (0, b i)]
  have hsum := integral_finsetSum (μ := volume) (Finset.univ : Finset (Fin n)) (fun i _ ↦ hint i)
  rw [← hsum, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only
  rw [hheat _ (mem_Wd_sub_inr hp w), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

end Transfer

/-! ### The heat flow as a kernel integral -/

theorem kern_eq {p : ℝ × Gs n} (hp : p.1 < 1) :
    kern n p = (√(2 * π * (1 - p.1)))⁻¹ ^ n * Real.exp (-‖p.2‖ ^ 2 / (2 * (1 - p.1))) := by
  have h : 0 < 1 - p.1 := by linarith
  rw [kern, hk, Real.exp_add, psi1, exp_neg_half_mul_log (by positivity), psi2]
  congr 2
  field_simp

theorem kern_pos (p : ℝ × Gs n) : 0 < kern n p := Real.exp_pos _

/-- `E Φ(Z) = ∫ p_{1-s}(x - w) Φ((w - x)/√(1-s)) dw`. -/
theorem integral_gm_eq_kern {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (Φ : Gs n → V) {s : ℝ} (hs : s < 1) (x : Gs n) :
    ∫ y, Φ y ∂gm n = ∫ w, kern n (s, x - w) • Φ ((√(1 - s))⁻¹ • (w - x)) := by
  rw [integral_gm_eq Φ (by linarith : 0 < 1 - s) x]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  simp only
  rw [kern_eq (by exact hs)]

/-- The heat flow as a kernel integral. -/
theorem heatU_eq_kInt (f : Gs n → ℝ) {s : ℝ} (hs : s < 1) (x : Gs n) :
    heatU f s x = kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kern n) (s, x) := by
  change ∫ y, f (x + √(1 - s) • y) ∂gm n = _
  rw [integral_gm_eq_kern _ hs x, kInt]
  refine integral_congr_ae (ae_of_all _ fun w ↦ ?_)
  have h : √(1 - s) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  simp only [smul_smul, mul_inv_cancel₀ h, one_smul, add_sub_cancel, smul_eq_mul]
  rw [mul_comm]
  congr 2
  ext <;> simp

section Flow

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

omit hf in
theorem abs_le_one_of_mem (x : Gs n) : |f x| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [(h01 x).1, (h01 x).2]

theorem taylor_heat :
    HasFTaylorSeriesUpToOn ∞ (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kern n))
      (fun p m ↦ kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (iteratedFDeriv ℝ m (kern n)) p)
      (Wd n) :=
  hasFTaylorSeriesUpToOn_kInt isOpen_Wd (fun _ hp w ↦ mem_Wd_sub_inr hp w) hf
    (abs_le_one_of_mem h01) contDiffOn_kern kDom_kern

omit hf h01 in
theorem eqOn_heatU_kInt :
    EqOn (fun p : ℝ × Gs n ↦ heatU f p.1 p.2)
      (kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kern n)) (Wd n) :=
  fun p hp ↦ heatU_eq_kInt f hp p.2

theorem iteratedFDeriv_heatU_eq (m : ℕ) {p : ℝ × Gs n} (hp : p ∈ Wd n) :
    iteratedFDeriv ℝ m (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) p =
      kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (iteratedFDeriv ℝ m (kern n)) p := by
  have h1 : (fun p : ℝ × Gs n ↦ heatU f p.1 p.2) =ᶠ[𝓝 p]
      kInt (ContinuousLinearMap.inr ℝ ℝ (Gs n)) f (kern n) :=
    Filter.eventually_of_mem (isOpen_Wd.mem_nhds hp) eqOn_heatU_kInt
  rw [(h1.iteratedFDeriv ℝ m).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen m isOpen_Wd hp]
  exact ((taylor_heat hf h01).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast le_top) isOpen_Wd.uniqueDiffOn hp).symm

end Flow

end BGHKLMM26.RobustMIS.Flow
