module

public import BGHKLMM26.RobustMIS.Flow
public import BGHKLMM26.RobustMIS.Ito
public import BGHKLMM26.RobustMIS.Bessel
public import BGHKLMM26.RobustMIS.DriftAux

/-!
# Concentration of `u(s, √s Z)`

Lemma 8.1 of `eldan-proof.tex` (new; replaces Eldan's Lemma 16, Doob and the strong Markov
property): `P(|u(s, √s Z) - m| ≥ θ) ≤ 2 exp(-π θ² / log(1/(1-s)))` for `s ∈ (0, 1)`.

Proof sketch: for `μ ∈ ℝ` and `c(s) = log(1/(1-s))/(4π)`, `h = exp(μ(u - m) - μ² c(s))` satisfies
`(∂_s + ½Δ) h = h μ² (½|∇u|² - c'(s)) ≤ 0` since `|∇u|² ≤ q(u)²/(1-s) ≤ 1/(2π(1-s))`
(`norm_hermite1_le`, `qf_sq_le`); `gauss_ito` and the mean value inequality give
`E h(s, √s Z) ≤ h(0, 0) = 1`; then Markov (`mul_meas_ge_le_integral`) with `μ = ±θ/(2c(s))`.

Proved (from the sorried flow and Itô lemmas used as black boxes): `Concentration.gen_hF_nonpos`
(the generator of `h` is `≤ 0`), `Concentration.mgf_le` (`E e^{μ(u-m)} ≤ e^{μ² c(s)}`),
`Concentration.tail_le` (Chernoff), `Concentration.concentration'`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Concentration

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open BGHKLMM26.RobustMIS.Drift

variable {n : ℕ}

/-- `c(s) = log(1/(1-s))/(4π)`. -/
noncomputable def cF (s : ℝ) : ℝ := -Real.log (1 - s) / (4 * π)

theorem hasDerivAt_cF {s : ℝ} (hs : s < 1) : HasDerivAt cF (1 / (4 * π * (1 - s))) s := by
  have h1 : (1 : ℝ) - s ≠ 0 := by linarith
  have h : HasDerivAt (fun r ↦ Real.log (1 - r)) (-1 / (1 - s)) s := by
    simpa using ((hasDerivAt_id s).const_sub 1).log h1
  have h2 := h.neg.div_const (4 * π)
  have e : cF = fun r ↦ -Real.log (1 - r) / (4 * π) := rfl
  rw [e]
  convert h2 using 1
  field_simp

theorem cF_nonneg {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) : 0 ≤ cF s := by
  unfold cF
  have : Real.log (1 - s) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have := pi_pos
  apply div_nonneg (by linarith) (by positivity)

theorem cF_pos {s : ℝ} (hs0 : 0 < s) (hs : s < 1) : 0 < cF s := by
  unfold cF
  have : Real.log (1 - s) < 0 := Real.log_neg (by linarith) (by linarith)
  have := pi_pos
  apply div_pos (by linarith) (by positivity)

/-- `h(s, x) = exp(μ(u(s, x) - m) - μ² c(s))`. -/
noncomputable def hF (f : Gs n → ℝ) (μ m : ℝ) (r : ℝ) (x : Gs n) : ℝ :=
  exp (μ * (heatU f r x - m) - μ ^ 2 * cF r)

theorem hasDerivAt_hF_space (μ m r : ℝ) (a : ℝ) :
    HasDerivAt (fun a ↦ exp (μ * (a - m) - μ ^ 2 * cF r))
      (μ * exp (μ * (a - m) - μ ^ 2 * cF r)) a := by
  have h := ((((hasDerivAt_id' a).sub_const m).const_mul μ).sub_const (μ ^ 2 * cF r)).exp
  exact h.congr_deriv (by ring)

section

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

theorem contDiffOn_hF (μ m : ℝ) :
    ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ hF f μ m p.1 p.2) {p | p.1 < 1} := by
  have hU := (contDiffOn_heatU f hf h01).of_le two_le_infty
  have hc : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ cF p.1) {p | p.1 < 1} := by
    unfold cF
    refine ContDiffOn.div_const (ContDiffOn.neg ?_) _
    refine ContDiffOn.log (contDiffOn_const.sub contDiffOn_fst) ?_
    intro p hp
    simp only [mem_ofPred_eq] at hp
    linarith
  exact ((contDiffOn_const.mul (hU.sub contDiffOn_const)).sub (contDiffOn_const.mul hc)).exp

theorem hasDerivAt_hF_time (μ m : ℝ) {r : ℝ} (hr : r < 1) (x : Gs n) :
    HasDerivAt (fun r' ↦ hF f μ m r' x)
      (hF f μ m r x * (μ * (-(1 / 2) * Laplacian.laplacian (heatU f r) x) -
        μ ^ 2 * (1 / (4 * π * (1 - r))))) r := by
  have h := hasDerivAt_heatU_time f hf h01 hr x
  have h2 := (((h.sub_const m).const_mul μ).sub ((hasDerivAt_cF hr).const_mul (μ ^ 2))).exp
  exact h2


theorem hF_le (hm : gMean f ∈ Ioo (0 : ℝ) 1) (μ : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (x : Gs n) : hF f μ (gMean f) r x ≤ exp |μ| := by
  unfold hF
  apply exp_le_exp.2
  have hu := heatU_mem f hf h01 hm hr x
  have hc := cF_nonneg hr0 hr
  have h1 : |heatU f r x - gMean f| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hm.1, hm.2]
  have h2 : μ * (heatU f r x - gMean f) ≤ |μ| := by
    calc μ * (heatU f r x - gMean f) ≤ |μ * (heatU f r x - gMean f)| := le_abs_self _
      _ = |μ| * |heatU f r x - gMean f| := abs_mul _ _
      _ ≤ |μ| * 1 := by gcongr
      _ = |μ| := mul_one _
  nlinarith [mul_nonneg (sq_nonneg μ) hc]

omit hf h01 in
theorem hF_eq (μ m r : ℝ) :
    hF f μ m r = fun y ↦ (fun a ↦ exp (μ * (a - m) - μ ^ 2 * cF r)) (heatU f r y) := rfl

theorem laplacian_hF (μ m : ℝ) {r : ℝ} (hr : r < 1) (x : Gs n) :
    Laplacian.laplacian (hF f μ m r) x =
      μ * (μ * hF f μ m r x) * (‖hermite1 (flowFun f r x)‖ ^ 2 / (1 - r)) +
        μ * hF f μ m r x * Laplacian.laplacian (heatU f r) x := by
  rw [hF_eq, laplacian_comp (EuclideanSpace.basisFun (Fin n) ℝ) (contDiffAt_heatU hf h01 hr x)
    (Eventually.of_forall fun a ↦ hasDerivAt_hF_space μ m r a)
    ((hasDerivAt_hF_space μ m r (heatU f r x)).const_mul μ),
    sum_sq_fderiv_heatU hf h01 hr x]

theorem fderiv_hF (μ m : ℝ) {r : ℝ} (hr : r < 1) (x : Gs n) :
    fderiv ℝ (hF f μ m r) x = (μ * hF f μ m r x) • fderiv ℝ (heatU f r) x := by
  rw [hF_eq, fderiv_comp_apply (contDiffAt_heatU hf h01 hr x)
    (Eventually.of_forall fun a ↦ hasDerivAt_hF_space μ m r a)]

theorem norm_iteratedFDeriv_hF_le (μ m : ℝ) {r : ℝ} (hr : r < 1) (x : Gs n) :
    ‖iteratedFDeriv ℝ 2 (hF f μ m r) x‖ ≤
      |μ * (μ * hF f μ m r x)| * ‖fderiv ℝ (heatU f r) x‖ ^ 2 +
        |μ * hF f μ m r x| * ‖iteratedFDeriv ℝ 2 (heatU f r) x‖ := by
  have h := norm_iteratedFDeriv_two_comp_le (contDiffAt_heatU hf h01 hr x)
    (Eventually.of_forall fun a ↦ hasDerivAt_hF_space μ m r a)
    ((hasDerivAt_hF_space μ m r (heatU f r x)).const_mul μ)
  rw [hF_eq]
  exact h

/-- The generator of `h` is `≤ 0`: `(∂_s + ½Δ) h = h μ² (½|∇u|² - c'(s)) ≤ 0`. -/
theorem gen_hF_nonpos (μ m : ℝ) {r : ℝ} (hr : r < 1) (x : Gs n) :
    deriv (fun r' ↦ hF f μ m r' x) r + 1 / 2 * Laplacian.laplacian (hF f μ m r) x ≤ 0 := by
  have h1 : 0 < 1 - r := by linarith
  rw [(hasDerivAt_hF_time hf h01 μ m hr x).deriv, laplacian_hF hf h01 μ m hr x]
  have hH : ‖hermite1 (flowFun f r x)‖ ^ 2 ≤ 1 / (2 * π) := by
    have e1 := norm_hermite1_le _ (measurable_flowFun f hf r x) (flowFun_mem f h01 r x)
    have e2 := qf_sq_le (gMean (flowFun f r x))
    calc ‖hermite1 (flowFun f r x)‖ ^ 2 ≤ qf (gMean (flowFun f r x)) ^ 2 := by
          gcongr
      _ ≤ _ := e2
  have key : hF f μ m r x * (μ * (-(1 / 2) * Laplacian.laplacian (heatU f r) x) -
        μ ^ 2 * (1 / (4 * π * (1 - r)))) + 1 / 2 * (μ * (μ * hF f μ m r x) *
          (‖hermite1 (flowFun f r x)‖ ^ 2 / (1 - r)) +
            μ * hF f μ m r x * Laplacian.laplacian (heatU f r) x) =
      hF f μ m r x * μ ^ 2 * (‖hermite1 (flowFun f r x)‖ ^ 2 / (1 - r) / 2 -
        1 / (2 * π) / (1 - r) / 2) := by
    field_simp
    ring
  rw [key]
  apply mul_nonpos_of_nonneg_of_nonpos (by unfold hF; positivity)
  rw [sub_nonpos]
  gcongr

theorem hF_bounds (hm : gMean f ∈ Ioo (0 : ℝ) 1) (μ : ℝ) {s : ℝ} (hs : s < 1) :
    ∃ M, ∀ r ∈ Icc 0 s, ∀ x, |hF f μ (gMean f) r x| ≤ M ∧
      |deriv (fun r' ↦ hF f μ (gMean f) r' x) r| ≤ M ∧
      ‖fderiv ℝ (hF f μ (gMean f) r) x‖ ≤ M ∧
      ‖iteratedFDeriv ℝ 2 (hF f μ (gMean f) r) x‖ ≤ M := by
  set m := gMean f
  set E₀ := exp |μ|
  set K := 1 / (1 - s)
  have hs1 : 0 < 1 - s := by linarith
  have hK : 0 ≤ K := by positivity
  have hE : 0 ≤ E₀ := by positivity
  have hμ : 0 ≤ |μ| := abs_nonneg μ
  refine ⟨E₀ + E₀ * (|μ| * n ^ 3 * K + μ ^ 2 * K) + |μ| * E₀ * (1 + K) +
    (μ ^ 2 * E₀ * K + |μ| * E₀ * (n ^ 2 * K)), fun r hr x ↦ ?_⟩
  have hr1 : r < 1 := by linarith [hr.2]
  have hrK : 1 / (1 - r) ≤ K := one_div_le_one_div_of_le hs1 (by linarith [hr.2])
  have hh0 : 0 < hF f μ m r x := exp_pos _
  have hh1 : hF f μ m r x ≤ E₀ := hF_le hf h01 hm μ hr.1 hr1 x
  have hDu2 : ‖fderiv ℝ (heatU f r) x‖ ^ 2 ≤ K :=
    (sq_norm_fderiv_heatU_le' hf h01 hr1 x).trans hrK
  have hDu : ‖fderiv ℝ (heatU f r) x‖ ≤ 1 + K := by
    nlinarith [norm_nonneg (fderiv ℝ (heatU f r) x)]
  have hD2u : ‖iteratedFDeriv ℝ 2 (heatU f r) x‖ ≤ n ^ 2 * K := by
    refine (norm_iteratedFDeriv_two_heatU_le hf h01 hr1 x).trans ?_
    rw [div_eq_mul_one_div]
    gcongr
  have hLu : |Laplacian.laplacian (heatU f r) x| ≤ n ^ 3 * K := by
    refine (abs_laplacian_heatU_le hf h01 hr1 x).trans ?_
    rw [div_eq_mul_one_div]
    gcongr
  have hn3 : (0 : ℝ) ≤ n ^ 3 * K := by positivity
  have hn2 : (0 : ℝ) ≤ n ^ 2 * K := by positivity
  -- the four bounds
  have b1 : |hF f μ m r x| ≤ E₀ := by rw [abs_of_pos hh0]; exact hh1
  have b2 : |deriv (fun r' ↦ hF f μ m r' x) r| ≤ E₀ * (|μ| * n ^ 3 * K + μ ^ 2 * K) := by
    rw [(hasDerivAt_hF_time hf h01 μ m hr1 x).deriv, abs_mul, abs_of_pos hh0]
    have hc : 1 / (4 * π * (1 - r)) ≤ K := by
      refine le_trans ?_ hrK
      have : 0 < 1 - r := by linarith
      apply one_div_le_one_div_of_le this
      nlinarith [pi_gt_three]
    have hc0 : 0 ≤ 1 / (4 * π * (1 - r)) := by
      have : 0 < 1 - r := by linarith
      positivity
    gcongr
    calc |μ * (-(1 / 2) * Laplacian.laplacian (heatU f r) x) - μ ^ 2 * (1 / (4 * π * (1 - r)))|
        ≤ |μ| * |Laplacian.laplacian (heatU f r) x| + μ ^ 2 * (1 / (4 * π * (1 - r))) := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc0, abs_neg,
            abs_of_pos (by norm_num : (0:ℝ) < 1 / 2), abs_of_nonneg (sq_nonneg μ)]
          nlinarith [abs_nonneg (Laplacian.laplacian (heatU f r) x)]
      _ ≤ |μ| * (n ^ 3 * K) + μ ^ 2 * K := by gcongr
      _ = |μ| * n ^ 3 * K + μ ^ 2 * K := by ring
  have b3 : ‖fderiv ℝ (hF f μ m r) x‖ ≤ |μ| * E₀ * (1 + K) := by
    rw [fderiv_hF hf h01 μ m hr1 x, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos hh0]
    gcongr
  have b4 : ‖iteratedFDeriv ℝ 2 (hF f μ m r) x‖ ≤ μ ^ 2 * E₀ * K + |μ| * E₀ * (n ^ 2 * K) := by
    refine (norm_iteratedFDeriv_hF_le hf h01 μ m hr1 x).trans ?_
    simp only [abs_mul, abs_of_pos hh0]
    rw [← mul_assoc, ← sq, sq_abs]
    gcongr
  have p1 : 0 ≤ E₀ * (|μ| * n ^ 3 * K + μ ^ 2 * K) :=
    mul_nonneg hE (add_nonneg (mul_nonneg (mul_nonneg hμ (pow_nonneg (Nat.cast_nonneg n) 3)) hK)
      (mul_nonneg (sq_nonneg μ) hK))
  have p2 : 0 ≤ |μ| * E₀ * (1 + K) := mul_nonneg (mul_nonneg hμ hE) (by linarith)
  have p3 : 0 ≤ μ ^ 2 * E₀ * K + |μ| * E₀ * (n ^ 2 * K) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hE) hK) (mul_nonneg (mul_nonneg hμ hE) hn2)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩


/-- `E exp(μ(u(s, √s Z) - m)) ≤ exp(μ² c(s))`, from `E h(s, √s Z) ≤ h(0, 0) = 1`. -/
theorem mgf_le (hm : gMean f ∈ Ioo (0 : ℝ) 1) (μ : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ∫ z, exp (μ * (heatU f s (√s • z) - gMean f)) ∂gm n ≤ exp (μ ^ 2 * cF s) := by
  set m := gMean f
  have hO : IsOpen {p : ℝ × Gs n | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hsub : Icc 0 s ×ˢ (univ : Set (Gs n)) ⊆ {p : ℝ × Gs n | p.1 < 1} := by
    intro p hp
    simp only [mem_prod, mem_Icc] at hp
    simp only [mem_ofPred_eq]
    linarith [hp.1.2, hs.2]
  obtain ⟨hcont, hderiv⟩ := gauss_ito le_rfl hs.1 (hF f μ m) hO hsub (contDiffOn_hF hf h01 μ m)
    (hF_bounds hf h01 hm μ hs.2)
  have hanti : AntitoneOn (fun r ↦ ∫ z, hF f μ m r (√r • z) ∂gm n) (Icc 0 s) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 s) hcont
    · intro r hr
      rw [interior_Icc] at hr ⊢
      exact (hderiv r hr).hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      apply integral_nonpos
      intro z
      exact gen_hF_nonpos hf h01 μ m (by linarith [hr.2, hs.2]) _
  have h0 : ∫ z, hF f μ m 0 (√0 • z) ∂gm n = 1 := by
    simp [hF, heatU_zero_zero, cF, m]
  have hle := hanti ⟨le_rfl, hs.1.le⟩ ⟨hs.1.le, le_rfl⟩ hs.1.le
  simp only at hle
  rw [h0] at hle
  have e : ∀ z, exp (μ * (heatU f s (√s • z) - m)) = hF f μ m s (√s • z) * exp (μ ^ 2 * cF s) := by
    intro z
    simp only [hF]
    rw [← exp_add]
    ring_nf
  simp_rw [e]
  rw [integral_mul_const]
  calc (∫ z, hF f μ m s (√s • z) ∂gm n) * exp (μ ^ 2 * cF s) ≤ 1 * exp (μ ^ 2 * cF s) := by
        gcongr
    _ = exp (μ ^ 2 * cF s) := one_mul _

/-- The Chernoff bound: `P(θ' ≤ μ (u - m)) ≤ exp(μ² c(s) - θ')`. -/
theorem tail_le (hm : gMean f ∈ Ioo (0 : ℝ) 1) (μ θ' : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    (gm n).real {z | θ' ≤ μ * (heatU f s (√s • z) - gMean f)} ≤ exp (μ ^ 2 * cF s - θ') := by
  set m := gMean f
  have hc : Continuous (heatU f s) := (contDiff_heatU hf h01 hs.2).continuous
  have hmeas : Measurable fun z : Gs n ↦ exp (μ * (heatU f s (√s • z) - m)) := by
    have : Continuous fun z : Gs n ↦ exp (μ * (heatU f s (√s • z) - m)) := by fun_prop
    exact this.measurable
  have hint : Integrable (fun z : Gs n ↦ exp (μ * (heatU f s (√s • z) - m))) (gm n) := by
    refine Gaussian.integrable_of_abs_le hmeas (C := exp |μ|) fun z ↦ ?_
    rw [abs_of_pos (exp_pos _)]
    apply exp_le_exp.2
    have hu := heatU_mem f hf h01 hm hs.2 (√s • z)
    have h1 : |heatU f s (√s • z) - m| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2, hm.1, hm.2]
    calc μ * (heatU f s (√s • z) - m) ≤ |μ * (heatU f s (√s • z) - m)| := le_abs_self _
      _ = |μ| * |heatU f s (√s • z) - m| := abs_mul _ _
      _ ≤ |μ| * 1 := by gcongr
      _ = |μ| := mul_one _
  have hmk := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun z ↦ (exp_pos _).le) hint
    (exp θ')
  have hsub : {z | θ' ≤ μ * (heatU f s (√s • z) - m)} ⊆
      {z | exp θ' ≤ exp (μ * (heatU f s (√s • z) - m))} := fun z hz ↦ exp_le_exp.2 hz
  have h1 := measureReal_mono (μ := gm n) hsub
  have h2 := mgf_le hf h01 hm μ hs
  rw [Real.exp_sub, le_div_iff₀ (exp_pos _)]
  calc (gm n).real {z | θ' ≤ μ * (heatU f s (√s • z) - m)} * exp θ'
      ≤ exp θ' * (gm n).real {z | exp θ' ≤ exp (μ * (heatU f s (√s • z) - m))} := by
        rw [mul_comm]; gcongr
    _ ≤ _ := hmk
    _ ≤ _ := h2

end

/-- **Sub-Gaussian bound** (Lemma 8.1). -/
theorem concentration' {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {θ : ℝ} (hθ : 0 < θ) :
    (gm n).real {z | θ ≤ |heatU f s (√s • z) - gMean f|} ≤
      2 * exp (-(π * θ ^ 2) / Real.log (1 / (1 - s))) := by
  set m := gMean f
  set c := cF s
  have hc : 0 < c := cF_pos hs.1 hs.2
  set μ₀ := θ / (2 * c)
  have hμ₀ : 0 < μ₀ := by positivity
  have hsub : {z | θ ≤ |heatU f s (√s • z) - m|} ⊆
      {z | θ ^ 2 / (2 * c) ≤ μ₀ * (heatU f s (√s • z) - m)} ∪
        {z | θ ^ 2 / (2 * c) ≤ (-μ₀) * (heatU f s (√s • z) - m)} := by
    intro z hz
    simp only [mem_ofPred_eq] at hz
    have e : θ ^ 2 / (2 * c) = μ₀ * θ := by simp only [μ₀]; ring
    rcases le_abs'.1 hz with h | h
    · right
      simp only [mem_ofPred_eq]
      rw [e]
      nlinarith
    · left
      simp only [mem_ofPred_eq]
      rw [e]
      exact mul_le_mul_of_nonneg_left h hμ₀.le
  have hexp : μ₀ ^ 2 * c - θ ^ 2 / (2 * c) = -(π * θ ^ 2) / Real.log (1 / (1 - s)) := by
    have hL : Real.log (1 / (1 - s)) = -Real.log (1 - s) := by
      rw [one_div, Real.log_inv]
    have hc' : c = -Real.log (1 - s) / (4 * π) := rfl
    have hL0 : 0 < -Real.log (1 - s) := by
      have := Real.log_neg (by linarith [hs.2] : (0 : ℝ) < 1 - s) (by linarith [hs.1])
      linarith
    rw [hL]
    simp only [μ₀]
    rw [hc']
    field_simp
    ring
  calc (gm n).real {z | θ ≤ |heatU f s (√s • z) - m|}
      ≤ (gm n).real ({z | θ ^ 2 / (2 * c) ≤ μ₀ * (heatU f s (√s • z) - m)} ∪
        {z | θ ^ 2 / (2 * c) ≤ (-μ₀) * (heatU f s (√s • z) - m)}) := measureReal_mono hsub
    _ ≤ (gm n).real {z | θ ^ 2 / (2 * c) ≤ μ₀ * (heatU f s (√s • z) - m)} +
        (gm n).real {z | θ ^ 2 / (2 * c) ≤ (-μ₀) * (heatU f s (√s • z) - m)} :=
        measureReal_union_le _ _
    _ ≤ exp (μ₀ ^ 2 * c - θ ^ 2 / (2 * c)) + exp ((-μ₀) ^ 2 * c - θ ^ 2 / (2 * c)) :=
        add_le_add (tail_le hf h01 hm _ _ hs) (tail_le hf h01 hm _ _ hs)
    _ = 2 * exp (-(π * θ ^ 2) / Real.log (1 / (1 - s))) := by
        rw [neg_sq, hexp]; ring

end BGHKLMM26.RobustMIS.Concentration

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set

variable {n : ℕ}

/-- **Sub-Gaussian bound** (Lemma 8.1). -/
theorem concentration (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) {θ : ℝ} (hθ : 0 < θ) :
    (gm n).real {z | θ ≤ |heatU f s (√s • z) - gMean f|} ≤
      2 * exp (-(π * θ ^ 2) / Real.log (1 / (1 - s))) :=
  Concentration.concentration' hf h01 hm hs hθ

end BGHKLMM26.RobustMIS
