module

public import BGHKLMM26.RobustMIS.Flow
public import BGHKLMM26.RobustMIS.Ito
public import BGHKLMM26.RobustMIS.Bessel
public import BGHKLMM26.RobustMIS.DriftAux
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The drift identity

§7 of `eldan-proof.tex` (Eldan's Itô computation §3.2, eq. (finald), done analytically): for
measurable `f : ℝⁿ → [0, 1]` with mean in `(0, 1)`, `y(s) = E e(s, √s Z)` is continuous on
`[0, 1)`, `y(0) = ε(f)`, and `y'(s) = E β(s, √s Z)` on `(0, 1)`.

Proof sketch: `e = Q₂(u) - (1-s)|∇u|²` with `Q₂ = q²`, `Q₂' = -2qΨ`, `Q₂'' = 2Ψ² - 2`
(`hasDerivAt_qf`, `hasDerivAt_Psi`); the generator: `(∂_s + ½Δ) Q₂(u) = (Ψ(u)² - 1)|∇u|²` and
`(∂_s + ½Δ)[(1-s)|∇u|²] = -|∇u|² + (1-s)‖∇²u‖²_HS` (using `(∂_s + ½Δ) ∂ₖu = 0`), so
`(∂_s + ½Δ) e = Ψ(u)²|∇u|² - (1-s)‖∇²u‖²_HS = β`; then `gauss_ito` on `[0, s₁]` for every
`s₁ < 1`. The bounds needed by `gauss_ito`: the factors `Ψ(u)` are compensated by `q(u)`
(`qf_mul_abs_Psi_le`, `qf_mul_Psi_sq_le` and `|∇u|² ≤ q(u)²/(1-s)`), the other derivatives of `u`
are bounded by `bounded_iteratedFDeriv_heatU`.

Proved (from the sorried flow, Itô, quantile and static lemmas used as black boxes). In Lean:
`e = q(u)² - (1-s) Σₖ (∂ₖu)²` in the standard basis (`Drift.eFlow_eq_sum`), joint smoothness
from that of `u` and of `(s, x) ↦ ∂ᵥu(s, x)` (`Drift.contDiffOn_partial`); the generator identity
is `Drift.gen_eFlow`, with `Δ` of the two parts from `Drift.laplacian_decomp` and
`Drift.laplacian_comp`; the third space derivatives of `u` (needed for `∇²e` and `∂_s ∂ₖu`) are
bounded through `bounded_iteratedFDeriv_heatU` and `Drift.norm_iteratedFDeriv_slice_le`
(`Drift.eFlow_bounds`). The calculus toolkit is in `DriftAux.lean`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Drift

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace ContDiff

variable {n : ℕ}

/-! ### One-dimensional facts: `Q = q²`, `Q' = -2qΨ`, `Q'' = 2Ψ² - 2` -/

theorem hasDerivAt_qf_sq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun a ↦ qf a ^ 2) (-2 * qf a * Psi a) a :=
  ((hasDerivAt_qf ha).pow 2).congr_deriv (by simp)

theorem hasDerivAt_qf_sq' {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun a ↦ -2 * qf a * Psi a) (2 * Psi a ^ 2 - 2) a := by
  have hq := (qf_pos ha).ne'
  exact (((hasDerivAt_qf ha).const_mul (-2)).mul (hasDerivAt_Psi ha)).congr_deriv
    (by field_simp; ring)

theorem eventually_hasDerivAt_qf_sq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ b in 𝓝 a, HasDerivAt (fun a ↦ qf a ^ 2) (-2 * qf b * Psi b) b := by
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact hasDerivAt_qf_sq hb

theorem hasDerivAt_sq' (a : ℝ) : HasDerivAt (fun a : ℝ ↦ a ^ 2) (2 * a) a :=
  (hasDerivAt_pow 2 a).congr_deriv (by simp)

theorem hasDerivAt_two_mul (a : ℝ) : HasDerivAt (fun a : ℝ ↦ 2 * a) 2 a :=
  ((hasDerivAt_id' a).const_mul 2).congr_deriv (mul_one 2)

theorem abs_neg_two_qf_Psi_le (a : ℝ) : |-2 * qf a * Psi a| ≤ 1 / 2 := by
  rw [abs_mul, abs_mul, abs_of_nonneg (qf_nonneg a)]
  have := qf_mul_abs_Psi_le a
  norm_num
  nlinarith

theorem abs_two_Psi_sq_sub_two_mul_le (a : ℝ) :
    |2 * Psi a ^ 2 - 2| * qf a ^ 2 ≤ 1 := by
  have h1 := qf_mul_abs_Psi_le a
  have h2 := qf_sq_le a
  have h3 : qf a ^ 2 * Psi a ^ 2 ≤ 1 / 16 := by
    have h4 : 0 ≤ qf a * |Psi a| := mul_nonneg (qf_nonneg a) (abs_nonneg _)
    have : (qf a * |Psi a|) ^ 2 ≤ (1 / 4) ^ 2 := by gcongr
    rw [mul_pow, sq_abs] at this
    linarith
  have h5 : 1 / (2 * π) ≤ 1 / 6 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [pi_gt_three]
  calc |2 * Psi a ^ 2 - 2| * qf a ^ 2 ≤ (2 * Psi a ^ 2 + 2) * qf a ^ 2 := by
        gcongr
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (Psi a)]
    _ = 2 * (qf a ^ 2 * Psi a ^ 2) + 2 * qf a ^ 2 := by ring
    _ ≤ 1 := by linarith

/-! ### The space derivatives `g_v = ∂_v u` -/

section Partial

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
include hf h01

theorem contDiff_partial {s : ℝ} (hs : s < 1) (v : Gs n) :
    ContDiff ℝ ∞ (fun y ↦ fderiv ℝ (heatU f s) y v) :=
  ((contDiff_heatU hf h01 hs).fderiv_right (m := ∞) (by exact le_refl _)).clm_apply
    contDiff_const

theorem contDiffAt_partial {s : ℝ} (hs : s < 1) (v x : Gs n) :
    ContDiffAt ℝ 2 (fun y ↦ fderiv ℝ (heatU f s) y v) x :=
  ((contDiff_partial hf h01 hs v).of_le two_le_infty).contDiffAt

theorem fderiv_partial_apply {s : ℝ} (hs : s < 1) (v x w : Gs n) :
    fderiv ℝ (fun y ↦ fderiv ℝ (heatU f s) y v) x w =
      fderiv ℝ (fderiv ℝ (heatU f s)) x w v := by
  have hc : DifferentiableAt ℝ (fderiv ℝ (heatU f s)) x :=
    ((contDiff_heatU hf h01 hs).fderiv_right (m := ∞) (by exact le_refl _)).differentiable
      (by simp) x
  rw [fderiv_clm_apply hc (differentiableAt_const v)]
  simp

theorem norm_fderiv_partial_le {s : ℝ} (hs : s < 1) (v x : Gs n) :
    ‖fderiv ℝ (fun y ↦ fderiv ℝ (heatU f s) y v) x‖ ≤
      ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
  rw [fderiv_partial_apply hf h01 hs, Real.norm_eq_abs]
  calc |fderiv ℝ (fderiv ℝ (heatU f s)) x w v|
      ≤ ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ * ‖w‖ * ‖v‖ := abs_fderiv_fderiv_le _ x w v
    _ = _ := by ring

theorem norm_iteratedFDeriv_partial_le {s : ℝ} (hs : s < 1) (v x : Gs n) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ fderiv ℝ (heatU f s) y v) x‖ ≤
      ‖iteratedFDeriv ℝ 3 (heatU f s) x‖ * ‖v‖ := by
  have e : (fun y ↦ fderiv ℝ (heatU f s) y v) =
      (ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ (heatU f s) := rfl
  have hd : ContDiffAt ℝ 2 (fderiv ℝ (heatU f s)) x :=
    (((contDiff_heatU hf h01 hs).fderiv_right (m := ∞) (by exact le_refl _)).of_le
      two_le_infty).contDiffAt
  rw [e]
  refine ((ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left hd le_rfl).trans ?_
  rw [norm_iteratedFDeriv_fderiv, mul_comm]
  gcongr
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L ↦ by
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact L.le_opNorm v

omit hf h01 in
theorem abs_partial_le {s : ℝ} (v x : Gs n) :
    |fderiv ℝ (heatU f s) x v| ≤ ‖fderiv ℝ (heatU f s) x‖ * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact (fderiv ℝ (heatU f s) x).le_opNorm v

theorem sum_sq_partial {s : ℝ} (hs : s < 1) (x : Gs n) :
    ∑ i, (fderiv ℝ (heatU f s) x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2 =
      ‖fderiv ℝ (heatU f s) x‖ ^ 2 := by
  have h1 : 0 < 1 - s := by linarith
  rw [sum_sq_fderiv_heatU hf h01 hs x, norm_hermite1_eq hf h01 hs, mul_pow, sq_sqrt h1.le]
  field_simp

/-- `e = q(u)² - (1 - s) Σₖ (∂ₖu)²`. -/
theorem eFlow_eq_sum {s : ℝ} (hs : s < 1) (x : Gs n) :
    eFlow f s x = qf (heatU f s x) ^ 2 -
      (1 - s) * ∑ k, (fderiv ℝ (heatU f s) x (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 := by
  rw [eFlow_eq hf h01 hs, sum_sq_partial hf h01 hs]

/-- The joint smoothness of `(s, x) ↦ ∂_v u(s, x)`. -/
theorem contDiffOn_partial (v : Gs n) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Gs n ↦ fderiv ℝ (heatU f p.1) p.2 v) {p | p.1 < 1} := by
  set U := fun p : ℝ × Gs n ↦ heatU f p.1 p.2
  have hO : IsOpen {p : ℝ × Gs n | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have hU := contDiffOn_heatU f hf h01
  have h1 : ContDiffOn ℝ ∞ (fun p ↦ fderiv ℝ U p ((0 : ℝ), v)) {p | p.1 < 1} :=
    (hU.fderiv_of_isOpen hO (m := ∞) (by exact le_refl _)).clm_apply contDiffOn_const
  refine h1.congr fun p hp ↦ ?_
  have hpU : HasFDerivAt U (fderiv ℝ U p) (p.1, p.2) :=
    ((hU.contDiffAt (hO.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have h2 := hpU.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)
  have h3 : heatU f p.1 = U ∘ fun y ↦ (p.1, y) := rfl
  rw [h3, h2.fderiv]
  simp

end Partial


section Gen

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
  (hm : gMean f ∈ Ioo (0 : ℝ) 1)
include hf h01 hm

theorem contDiffOn_eFlow :
    ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ eFlow f p.1 p.2) {p | p.1 < 1} := by
  have hU := (contDiffOn_heatU f hf h01).of_le two_le_infty
  have hQ : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ qf (heatU f p.1 p.2) ^ 2) {p | p.1 < 1} := by
    have h := (contDiffOn_qf.of_le two_le_infty).comp hU
      (fun p hp ↦ heatU_mem f hf h01 hm hp p.2)
    exact h.pow 2
  have hS : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦
      ∑ k, (fderiv ℝ (heatU f p.1) p.2 (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
      {p | p.1 < 1} :=
    ContDiffOn.sum fun k _ ↦ ((contDiffOn_partial hf h01 _).of_le two_le_infty).pow 2
  have h := hQ.sub (((contDiffOn_const (c := (1 : ℝ))).sub contDiffOn_fst).mul hS)
  refine h.congr fun p hp ↦ ?_
  exact eFlow_eq_sum hf h01 hp p.2

theorem hasDerivAt_eFlow_time {s : ℝ} (hs : s < 1) (y : Gs n) :
    HasDerivAt (fun r ↦ eFlow f r y)
      ((-2 * qf (heatU f s y) * Psi (heatU f s y)) *
          (-(1 / 2) * Laplacian.laplacian (heatU f s) y) -
        ((-1) * ∑ k, (fderiv ℝ (heatU f s) y (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 +
          (1 - s) * ∑ k, 2 * fderiv ℝ (heatU f s) y (EuclideanSpace.basisFun (Fin n) ℝ k) *
            (-(1 / 2) * Laplacian.laplacian
              (fun y ↦ fderiv ℝ (heatU f s) y (EuclideanSpace.basisFun (Fin n) ℝ k)) y))) s := by
  have hu := heatU_mem f hf h01 hm hs y
  have h1 := (hasDerivAt_qf_sq hu).comp s (hasDerivAt_heatU_time f hf h01 hs y)
  have h2 := HasDerivAt.fun_sum (u := Finset.univ) fun k _ ↦
    (hasDerivAt_sq' _).comp s (hasDerivAt_fderiv_heatU_time f hf h01 hs y
      (EuclideanSpace.basisFun (Fin n) ℝ k))
  have h3 := h1.sub (((hasDerivAt_id' s).const_sub 1).mul h2)
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hs] with r hr
  exact eFlow_eq_sum hf h01 hr y

theorem laplacian_eFlow {s : ℝ} (hs : s < 1) (y : Gs n) :
    Laplacian.laplacian (eFlow f s) y =
      (2 * Psi (heatU f s y) ^ 2 - 2) *
          ∑ i, (fderiv ℝ (heatU f s) y (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2 +
        (-2 * qf (heatU f s y) * Psi (heatU f s y)) * Laplacian.laplacian (heatU f s) y -
      (1 - s) * ∑ k, (2 * ∑ i, (fderiv ℝ (fderiv ℝ (heatU f s)) y
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2 +
        2 * fderiv ℝ (heatU f s) y (EuclideanSpace.basisFun (Fin n) ℝ k) *
          Laplacian.laplacian
            (fun y ↦ fderiv ℝ (heatU f s) y (EuclideanSpace.basisFun (Fin n) ℝ k)) y) := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hu := heatU_mem f hf h01 hm hs y
  have e : eFlow f s = fun y ↦ qf (heatU f s y) ^ 2 -
      (1 - s) * ∑ k, (fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k y :=
    funext (eFlow_eq_sum hf h01 hs)
  have h1 : ContDiffAt ℝ 2 (fun y ↦ qf (heatU f s y) ^ 2) y :=
    (((contDiffOn_qf.of_le two_le_infty).comp_contDiff
      ((contDiff_heatU hf h01 hs).of_le two_le_infty) (fun x ↦ heatU_mem f hf h01 hm hs x)).pow
      2).contDiffAt
  have h2 : ∀ k, ContDiffAt ℝ 2 ((fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k) y :=
    fun k ↦ (((contDiff_partial hf h01 hs (b k)).of_le two_le_infty).pow 2).contDiffAt
  rw [e, laplacian_decomp (1 - s) h1 h2]
  rw [laplacian_comp b (contDiffAt_heatU hf h01 hs y) (eventually_hasDerivAt_qf_sq hu)
    (hasDerivAt_qf_sq' hu)]
  congr 2
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [laplacian_comp b (contDiffAt_partial hf h01 hs (b k) y)
    (Eventually.of_forall hasDerivAt_sq') (hasDerivAt_two_mul _)]
  simp_rw [fderiv_partial_apply hf h01 hs]

/-- **The generator of `e`**: `(∂_s + ½Δ) e = Ψ(u)²|∇u|² - (1-s)‖∇²u‖²_HS = β`. -/
theorem gen_eFlow {s : ℝ} (hs : s < 1) (y : Gs n) :
    deriv (fun r ↦ eFlow f r y) s + 1 / 2 * Laplacian.laplacian (eFlow f s) y =
      betaFlow f s y := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have h1 : 0 < 1 - s := by linarith
  rw [(hasDerivAt_eFlow_time hf h01 hm hs y).deriv, laplacian_eFlow hf h01 hm hs y]
  -- the static quantities in terms of the derivatives of `u`
  have hH : ‖hermite1 (flowFun f s y)‖ ^ 2 =
      (1 - s) * ∑ i, (fderiv ℝ (heatU f s) y (b i)) ^ 2 := by
    rw [sum_sq_fderiv_heatU hf h01 hs y b]
    field_simp
  have hB : ∀ v w, bForm (flowFun f s y) v w =
      (1 - s) * fderiv ℝ (fderiv ℝ (heatU f s)) y v w := by
    intro v w
    rw [fderiv_fderiv_heatU hf h01 hs]
    field_simp
  have hHS : hs2 (flowFun f s y) =
      (1 - s) ^ 2 * ∑ k, ∑ i, (fderiv ℝ (fderiv ℝ (heatU f s)) y (b i) (b k)) ^ 2 := by
    rw [hs2_eq_orthonormalBasis _ (measurable_flowFun f hf s y) (flowFun_mem f h01 s y) b,
      Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hB]
    ring
  have hsum : ∑ k, (2 * ∑ i, (fderiv ℝ (fderiv ℝ (heatU f s)) y (b i) (b k)) ^ 2 +
        2 * fderiv ℝ (heatU f s) y (b k) *
          Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) y) =
      2 * ∑ k, ∑ i, (fderiv ℝ (fderiv ℝ (heatU f s)) y (b i) (b k)) ^ 2 +
        2 * ∑ k, fderiv ℝ (heatU f s) y (b k) *
          Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) y := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  have hsum' : ∑ k, 2 * fderiv ℝ (heatU f s) y (b k) *
        (-(1 / 2) * Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) y) =
      -∑ k, fderiv ℝ (heatU f s) y (b k) *
          Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) y := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  rw [hsum, hsum']
  simp only [betaFlow, driftD]
  rw [hH, hHS]
  change _ = (1 - s)⁻¹ * (Psi (heatU f s y) ^ 2 * _ - _)
  field_simp
  ring


theorem eFlow_bounds {s₁ : ℝ} (hs₁ : s₁ < 1) :
    ∃ M, ∀ s ∈ Icc 0 s₁, ∀ x, |eFlow f s x| ≤ M ∧ |deriv (fun r ↦ eFlow f r x) s| ≤ M ∧
      ‖fderiv ℝ (eFlow f s) x‖ ≤ M ∧ ‖iteratedFDeriv ℝ 2 (eFlow f s) x‖ ≤ M := by
  obtain ⟨M₃, hM₃0, hM₃⟩ := bounded_iteratedFDeriv_three hf h01 hs₁
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set K := 1 / (1 - s₁)
  have hs1 : 0 < 1 - s₁ := by linarith
  have hK : 0 ≤ K := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set B2 := n ^ 3 * K + K + n * ((1 + K) * (n * M₃))
  set B3 := 1 / 2 * (1 + K) + n * (2 * (1 + K) * (n ^ 2 * K))
  set B4 := (K + 1 / 2 * (n ^ 2 * K)) + n * (2 * (n ^ 2 * K) ^ 2 + 2 * (1 + K) * M₃)
  have hB2 : 0 ≤ B2 := by positivity
  have hB3 : 0 ≤ B3 := by positivity
  have hB4 : 0 ≤ B4 := by positivity
  refine ⟨1 + B2 + B3 + B4, fun s hs x ↦ ?_⟩
  have hs1' : s < 1 := by linarith [hs.2]
  have hs0 : 0 < 1 - s := by linarith
  have hsK : 1 / (1 - s) ≤ K := one_div_le_one_div_of_le hs1 (by linarith [hs.2])
  have h1s : |1 - s| ≤ 1 := by rw [abs_of_pos hs0]; linarith [hs.1]
  have hu := heatU_mem f hf h01 hm hs1' x
  -- static bounds on the derivatives of `u`
  have hDu2 : ‖fderiv ℝ (heatU f s) x‖ ^ 2 ≤ K :=
    (sq_norm_fderiv_heatU_le' hf h01 hs1' x).trans hsK
  have hDu : ‖fderiv ℝ (heatU f s) x‖ ≤ 1 + K := by
    nlinarith [norm_nonneg (fderiv ℝ (heatU f s) x)]
  have hD2u : ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ ≤ n ^ 2 * K := by
    refine (norm_iteratedFDeriv_two_heatU_le hf h01 hs1' x).trans ?_
    rw [div_eq_mul_one_div]
    gcongr
  have hLu : |Laplacian.laplacian (heatU f s) x| ≤ n ^ 3 * K := by
    refine (abs_laplacian_heatU_le hf h01 hs1' x).trans ?_
    rw [div_eq_mul_one_div]
    gcongr
  have hbk : ∀ k, ‖b k‖ = 1 := fun k ↦ b.orthonormal.1 k
  have hg : ∀ k, |fderiv ℝ (heatU f s) x (b k)| ≤ 1 + K := fun k ↦ by
    have h := abs_partial_le (f := f) (s := s) (b k) x
    rw [hbk, mul_one] at h
    linarith
  have hDg : ∀ k, ‖fderiv ℝ (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x‖ ≤ n ^ 2 * K := fun k ↦ by
    have h := norm_fderiv_partial_le hf h01 hs1' (b k) x
    rw [hbk, mul_one] at h
    linarith
  have hD2g : ∀ k, ‖iteratedFDeriv ℝ 2 (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x‖ ≤ M₃ :=
    fun k ↦ by
    have h := norm_iteratedFDeriv_partial_le hf h01 hs1' (b k) x
    rw [hbk, mul_one] at h
    exact h.trans (hM₃ s hs x)
  have hLg : ∀ k, |Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x| ≤ n * M₃ :=
    fun k ↦ by
    refine (abs_laplacian_le b _ x).trans ?_
    simp only [Fintype.card_fin]
    gcongr
    exact hD2g k
  have hqΨ := abs_neg_two_qf_Psi_le (heatU f s x)
  have hS : ∑ i, (fderiv ℝ (heatU f s) x (b i)) ^ 2 ≤ K := by
    rw [sum_sq_partial hf h01 hs1' x]
    exact hDu2
  have hS0 : 0 ≤ ∑ i, (fderiv ℝ (heatU f s) x (b i)) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have e : eFlow f s = fun y ↦ qf (heatU f s y) ^ 2 -
      (1 - s) * ∑ k, (fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k y :=
    funext (eFlow_eq_sum hf h01 hs1')
  have hF1 : ContDiffAt ℝ 2 (fun y ↦ qf (heatU f s y) ^ 2) x :=
    (((contDiffOn_qf.of_le two_le_infty).comp_contDiff
      ((contDiff_heatU hf h01 hs1').of_le two_le_infty)
        (fun x ↦ heatU_mem f hf h01 hm hs1' x)).pow 2).contDiffAt
  have hG : ∀ k, ContDiffAt ℝ 2 ((fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k) x :=
    fun k ↦ (((contDiff_partial hf h01 hs1' (b k)).of_le two_le_infty).pow 2).contDiffAt
  -- the four bounds
  have b1 : |eFlow f s x| ≤ 1 := by
    rw [abs_of_nonneg (eFlow_nonneg hf h01 s x)]
    refine (eFlow_le h01 s x).trans ((qf_sq_le _).trans ?_)
    rw [div_le_one (by positivity)]
    linarith [pi_gt_three]
  have b2 : |deriv (fun r ↦ eFlow f r x) s| ≤ B2 := by
    rw [(hasDerivAt_eFlow_time hf h01 hm hs1' x).deriv]
    have t1 : |(-2 * qf (heatU f s x) * Psi (heatU f s x)) *
        (-(1 / 2) * Laplacian.laplacian (heatU f s) x)| ≤ n ^ 3 * K := by
      have hB : |-(1 / 2) * Laplacian.laplacian (heatU f s) x| =
          1 / 2 * |Laplacian.laplacian (heatU f s) x| := by
        rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [abs_mul, hB]
      have hn3 : 0 ≤ (n : ℝ) ^ 3 * K := by positivity
      calc |-2 * qf (heatU f s x) * Psi (heatU f s x)| *
          (1 / 2 * |Laplacian.laplacian (heatU f s) x|) ≤ 1 / 2 * (1 / 2 * (n ^ 3 * K)) := by
            gcongr
        _ ≤ n ^ 3 * K := by linarith
    have t2 : |(-1) * ∑ k, (fderiv ℝ (heatU f s) x (b k)) ^ 2| ≤ K := by
      rw [abs_mul, abs_neg, abs_one, one_mul, abs_of_nonneg hS0]
      exact hS
    have t3 : |(1 - s) * ∑ k, 2 * fderiv ℝ (heatU f s) x (b k) *
        (-(1 / 2) * Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x)| ≤
          n * ((1 + K) * (n * M₃)) := by
      rw [abs_mul]
      calc |1 - s| * |∑ k, 2 * fderiv ℝ (heatU f s) x (b k) *
            (-(1 / 2) * Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x)|
          ≤ 1 * ∑ _k : Fin n, (1 + K) * (n * M₃) := by
            gcongr
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
            rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
              abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            have := hg k
            have := hLg k
            have := abs_nonneg (fderiv ℝ (heatU f s) x (b k))
            have := abs_nonneg (Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x)
            calc 2 * |fderiv ℝ (heatU f s) x (b k)| *
                (1 / 2 * |Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x|)
                = |fderiv ℝ (heatU f s) x (b k)| *
                    |Laplacian.laplacian (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x| := by ring
              _ ≤ (1 + K) * (n * M₃) := by gcongr
        _ = n * ((1 + K) * (n * M₃)) := by simp
    refine (abs_sub _ _).trans ?_
    refine (add_le_add le_rfl (abs_add_le _ _)).trans ?_
    linarith
  have b3 : ‖fderiv ℝ (eFlow f s) x‖ ≤ B3 := by
    rw [← norm_iteratedFDeriv_one, e]
    refine (norm_iteratedFDeriv_decomp_le (1 - s) (hF1.of_le (by norm_num))
      (fun k ↦ (hG k).of_le (by norm_num))).trans ?_
    rw [norm_iteratedFDeriv_one, fderiv_comp_apply (contDiffAt_heatU hf h01 hs1' x)
      (eventually_hasDerivAt_qf_sq hu), norm_smul, Real.norm_eq_abs]
    have t1 : ∀ k, ‖iteratedFDeriv ℝ 1 ((fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k) x‖ ≤
        2 * (1 + K) * (n ^ 2 * K) := by
      intro k
      rw [norm_iteratedFDeriv_one, fderiv_comp_apply (contDiffAt_partial hf h01 hs1' (b k) x)
        (Eventually.of_forall hasDerivAt_sq'), norm_smul, Real.norm_eq_abs, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := hg k
      have := hDg k
      have := norm_nonneg (fderiv ℝ (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x)
      have := abs_nonneg (fderiv ℝ (heatU f s) x (b k))
      gcongr
    calc |-2 * qf (heatU f s x) * Psi (heatU f s x)| * ‖fderiv ℝ (heatU f s) x‖ +
          (|1 - s| * ∑ k, ‖iteratedFDeriv ℝ 1
            ((fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k) x‖)
        ≤ 1 / 2 * (1 + K) + 1 * ∑ _k : Fin n, 2 * (1 + K) * (n ^ 2 * K) := by
          gcongr
          exact t1 _
      _ = B3 := by simp [B3]
  have b4 : ‖iteratedFDeriv ℝ 2 (eFlow f s) x‖ ≤ B4 := by
    rw [e]
    refine (norm_iteratedFDeriv_decomp_le (1 - s) hF1 hG).trans ?_
    have t0 : ‖iteratedFDeriv ℝ 2 (fun y ↦ qf (heatU f s y) ^ 2) x‖ ≤ K + 1 / 2 * (n ^ 2 * K) := by
      refine (norm_iteratedFDeriv_two_comp_le (contDiffAt_heatU hf h01 hs1' x)
        (eventually_hasDerivAt_qf_sq hu) (hasDerivAt_qf_sq' hu)).trans ?_
      have h2 := abs_two_Psi_sq_sub_two_mul_le (heatU f s x)
      have h3 : |2 * Psi (heatU f s x) ^ 2 - 2| * ‖fderiv ℝ (heatU f s) x‖ ^ 2 ≤ K := by
        calc |2 * Psi (heatU f s x) ^ 2 - 2| * ‖fderiv ℝ (heatU f s) x‖ ^ 2
            ≤ |2 * Psi (heatU f s x) ^ 2 - 2| * (qf (heatU f s x) ^ 2 / (1 - s)) := by
              gcongr
              exact sq_norm_fderiv_heatU_le hf h01 hs1' x
          _ = |2 * Psi (heatU f s x) ^ 2 - 2| * qf (heatU f s x) ^ 2 * (1 / (1 - s)) := by ring
          _ ≤ 1 * K := by gcongr
          _ = K := one_mul K
      have h4 : |-2 * qf (heatU f s x) * Psi (heatU f s x)| *
          ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ ≤ 1 / 2 * (n ^ 2 * K) := by
        gcongr
      linarith
    have t1 : ∀ k, ‖iteratedFDeriv ℝ 2 ((fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k) x‖ ≤
        2 * (n ^ 2 * K) ^ 2 + 2 * (1 + K) * M₃ := by
      intro k
      refine (norm_iteratedFDeriv_two_comp_le (contDiffAt_partial hf h01 hs1' (b k) x)
        (Eventually.of_forall hasDerivAt_sq') (hasDerivAt_two_mul _)).trans ?_
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := hg k
      have := hDg k
      have := hD2g k
      have := norm_nonneg (fderiv ℝ (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x)
      have := abs_nonneg (fderiv ℝ (heatU f s) x (b k))
      have := norm_nonneg (iteratedFDeriv ℝ 2 (fun y ↦ fderiv ℝ (heatU f s) y (b k)) x)
      gcongr
    calc ‖iteratedFDeriv ℝ 2 (fun y ↦ qf (heatU f s y) ^ 2) x‖ +
          (|1 - s| * ∑ k, ‖iteratedFDeriv ℝ 2
            ((fun k y ↦ (fderiv ℝ (heatU f s) y (b k)) ^ 2) k) x‖)
        ≤ (K + 1 / 2 * (n ^ 2 * K)) +
            1 * ∑ _k : Fin n, (2 * (n ^ 2 * K) ^ 2 + 2 * (1 + K) * M₃) := by
          gcongr
          exact t1 _
      _ = B4 := by simp [B4]; ring
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **The drift identity** (Proposition 7.1). -/
theorem drift_identity' :
    ContinuousOn (yFlow f) (Ico 0 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (yFlow f) (∫ z, betaFlow f s (√s • z) ∂gm n) s := by
  have hO : IsOpen {p : ℝ × Gs n | p.1 < 1} := isOpen_lt continuous_fst continuous_const
  have key : ∀ s₁, 0 < s₁ → s₁ < 1 → ContinuousOn (yFlow f) (Icc 0 s₁) ∧
      ∀ s ∈ Ioo 0 s₁, HasDerivAt (yFlow f) (∫ z, betaFlow f s (√s • z) ∂gm n) s := by
    intro s₁ h0 h1
    have hsub : Icc 0 s₁ ×ˢ (univ : Set (Gs n)) ⊆ {p : ℝ × Gs n | p.1 < 1} := by
      intro p hp
      simp only [mem_prod, mem_Icc] at hp
      simp only [mem_ofPred_eq]
      linarith [hp.1.2]
    obtain ⟨hc, hd⟩ := gauss_ito le_rfl h0 (eFlow f) hO hsub (contDiffOn_eFlow hf h01 hm)
      (eFlow_bounds hf h01 hm h1)
    refine ⟨hc, fun s hs ↦ ?_⟩
    have h := hd s hs
    have e : (fun z ↦ deriv (fun r ↦ eFlow f r (√s • z)) s +
        1 / 2 * Laplacian.laplacian (eFlow f s) (√s • z)) = fun z ↦ betaFlow f s (√s • z) := by
      funext z
      exact gen_eFlow hf h01 hm (by linarith [hs.2]) _
    rw [e] at h
    exact h
  constructor
  · intro s hs
    obtain ⟨hc, -⟩ := key ((s + 1) / 2) (by linarith [hs.1]) (by linarith [hs.2])
    have hmem : Icc 0 ((s + 1) / 2) ∈ 𝓝[Ico 0 1] s := by
      refine mem_nhdsWithin.2 ⟨Iio ((s + 1) / 2), isOpen_Iio, by rw [mem_Iio]; linarith [hs.2], ?_⟩
      intro y hy
      exact ⟨hy.2.1, hy.1.le⟩
    exact (hc s ⟨hs.1, by linarith [hs.2]⟩).mono_of_mem_nhdsWithin hmem
  · intro s hs
    exact (key ((s + 1) / 2) (by linarith [hs.1]) (by linarith [hs.2])).2 s
      ⟨hs.1, by linarith [hs.2]⟩

end Gen

end BGHKLMM26.RobustMIS.Drift

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

theorem yFlow_zero (f : Gs n → ℝ) : yFlow f 0 = epsF f := by
  simp [yFlow, eFlow, flowFun_zero_zero]

/-- **The drift identity** (Proposition 7.1). -/
theorem drift_identity (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (yFlow f) (Ico 0 1) ∧
      ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt (yFlow f) (∫ z, betaFlow f s (√s • z) ∂gm n) s :=
  Drift.drift_identity' hf h01 hm

end BGHKLMM26.RobustMIS
