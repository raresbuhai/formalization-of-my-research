module

public import BGHKLMM26.RobustMIS.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# The rates `ψ` and `ω`

Lemma 3.4 (`ψ(x) = x √(log(1/x))`, the inversion of `x / log(1/x)`) and Lemma 1.3 (`ω`, here
`sqrtLog`) of `eldan-proof.tex`, with the concavity of `ω` (audit issue 1; used by `Section 5`
of the paper when averaging Theorem 7.1) and the comparison `ω(η) ≤ √2 √(η log(1/η))` used for
the final form of Theorem 7.1.

Proofs: `ω = √(g̃)` with `g̃(x) = g(min(x, 1))`, `g(y) = y log(e/y) = y - y log y`
(`Rates.gl`; `g = id + negMulLog` is concave on `[0, ∞)` by Mathlib's `concaveOn_negMulLog`, and
nondecreasing on `[0, 1]`). Concavity of `ω` on `[0, ∞)` follows by composing concave
nondecreasing functions (`√`, `g`) with concave ones (`min(·, 1)`), and subadditivity from
concavity and `ω(0) = 0`. Lemma 3.4(a) is proved from `ψ' = √L - 1/(2√L)`, `L = log(1/x)`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open Real Set Filter Topology

namespace Rates

/-- `g(y) = y - y log y`, equal to `y log(e/y)` (`Rates.gl_eq`). -/
noncomputable def gl (y : ℝ) : ℝ := y - y * Real.log y

theorem gl_eq (y : ℝ) : y * Real.log (exp 1 / y) = gl y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [gl]
  · rw [gl, Real.log_div (exp_ne_zero 1) hy, log_exp]; ring

theorem continuous_gl : Continuous gl := continuous_id.sub continuous_mul_log

theorem gl_le_one {y : ℝ} (hy : 0 ≤ y) : gl y ≤ 1 := by
  have := self_sub_one_le_mul_log hy
  unfold gl; linarith

theorem le_gl {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : y ≤ gl y := by
  have := mul_log_nonpos h0 h1
  unfold gl; linarith

theorem gl_nonneg {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : 0 ≤ gl y := h0.trans (le_gl h0 h1)

theorem gl_one : gl 1 = 1 := by simp [gl]

theorem concaveOn_gl : ConcaveOn ℝ (Ici 0) gl := by
  have h := (concaveOn_id (convex_Ici (0 : ℝ))).add concaveOn_negMulLog
  convert h using 1
  ext y; simp [gl, negMulLog]; ring

theorem monotoneOn_gl : MonotoneOn gl (Icc 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun y ↦ -Real.log y) (convex_Icc 0 1)
    continuous_gl.continuousOn (fun y hy ↦ ?_) (fun y hy ↦ ?_)
  · rw [interior_Icc] at hy ⊢
    have h : HasDerivAt gl (1 - (Real.log y + 1)) y :=
      (hasDerivAt_id' y).sub (hasDerivAt_mul_log hy.1.ne')
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  · rw [interior_Icc] at hy
    exact neg_nonneg.2 (log_nonpos hy.1.le hy.2.le)

/-- `g̃(x) = g(min(x, 1))`. -/
noncomputable def gt1 (x : ℝ) : ℝ := gl (min x 1)

theorem clip01_eq {x : ℝ} (hx : 0 ≤ x) : clip01 x = min x 1 := by
  rw [clip01, max_eq_left hx]

theorem clip01_mem (x : ℝ) : clip01 x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

theorem sqrtLog_eq_gl (x : ℝ) : sqrtLog x = √(gl (clip01 x)) := by
  rw [sqrtLog, gl_eq]

theorem sqrtLog_eq_gt1 {x : ℝ} (hx : 0 ≤ x) : sqrtLog x = √(gt1 x) := by
  rw [sqrtLog_eq_gl, clip01_eq hx, gt1]

theorem concaveOn_comp_of_monotoneOn {s t : Set ℝ} {f g : ℝ → ℝ} (hg : ConcaveOn ℝ t g)
    (hg' : MonotoneOn g t) (hf : ConcaveOn ℝ s f) (hmaps : MapsTo f s t) :
    ConcaveOn ℝ s (g ∘ f) :=
  ⟨hf.1, fun _ hx _ hy _ _ ha hb hab ↦
    (hg.2 (hmaps hx) (hmaps hy) ha hb hab).trans
      (hg' (hg.1 (hmaps hx) (hmaps hy) ha hb hab) (hmaps (hf.1 hx hy ha hb hab))
        (hf.2 hx hy ha hb hab))⟩

theorem concaveOn_gt1 : ConcaveOn ℝ (Ici 0) gt1 := by
  have hmin : ConcaveOn ℝ (Ici (0 : ℝ)) (fun x ↦ min x 1) :=
    (concaveOn_id (convex_Ici (0 : ℝ))).inf (concaveOn_const 1 (convex_Ici 0))
  have := concaveOn_comp_of_monotoneOn (concaveOn_gl.subset Icc_subset_Ici_self (convex_Icc 0 1))
    monotoneOn_gl hmin (fun x hx ↦ ⟨le_min hx zero_le_one, min_le_right _ _⟩)
  exact this

theorem gt1_mem {x : ℝ} (hx : 0 ≤ x) : gt1 x ∈ Icc (0 : ℝ) 1 :=
  ⟨gl_nonneg (le_min hx zero_le_one) (min_le_right _ _), gl_le_one (le_min hx zero_le_one)⟩

theorem concaveOn_sqrt_gt1 : ConcaveOn ℝ (Ici 0) (fun x ↦ √(gt1 x)) :=
  concaveOn_comp_of_monotoneOn (g := fun y ↦ √y) strictConcaveOn_sqrt.concaveOn
    (fun _ _ _ _ h ↦ sqrt_le_sqrt h) concaveOn_gt1 (fun _ hx ↦ (gt1_mem hx).1)

end Rates

open Rates

/-! ### Lemma 1.3: `ω` -/

theorem sqrtLog_nonneg (x : ℝ) : 0 ≤ sqrtLog x := Real.sqrt_nonneg _

theorem sqrtLog_zero : sqrtLog 0 = 0 := by
  simp [sqrtLog, clip01]

theorem sqrtLog_of_nonpos {x : ℝ} (hx : x ≤ 0) : sqrtLog x = 0 := by
  simp [sqrtLog, clip01, max_eq_right hx]

theorem sqrtLog_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    sqrtLog x = √(x * Real.log (exp 1 / x)) := by
  rw [sqrtLog, clip01, max_eq_left hx.1, min_eq_left hx.2]

theorem sqrtLog_le_one (x : ℝ) : sqrtLog x ≤ 1 := by
  rw [sqrtLog_eq_gl, sqrt_le_one]
  exact gl_le_one (clip01_mem x).1

theorem monotone_sqrtLog : Monotone sqrtLog := by
  intro x y hxy
  rw [sqrtLog_eq_gl, sqrtLog_eq_gl]
  refine sqrt_le_sqrt (monotoneOn_gl (clip01_mem x) (clip01_mem y) ?_)
  exact min_le_min_right _ (max_le_max_right _ hxy)

theorem continuous_sqrtLog : Continuous sqrtLog := by
  have : sqrtLog = fun x ↦ √(gl (min (max x 0) 1)) := funext fun x ↦ sqrtLog_eq_gl x
  rw [this]
  exact (continuous_gl.comp ((continuous_id.max continuous_const).min continuous_const)).sqrt

/-- `ω` is concave on `[0, ∞)` (audit issue 1). -/
theorem concaveOn_sqrtLog : ConcaveOn ℝ (Ici 0) sqrtLog :=
  concaveOn_sqrt_gt1.congr fun _ hx ↦ (sqrtLog_eq_gt1 hx).symm

/-- `ω` is subadditive on `[0, ∞)`. -/
theorem sqrtLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    sqrtLog (x + y) ≤ sqrtLog x + sqrtLog y := by
  rcases eq_or_lt_of_le (add_nonneg hx hy) with h0 | h0
  · rw [← h0, sqrtLog_zero]; exact add_nonneg (sqrtLog_nonneg _) (sqrtLog_nonneg _)
  have hxy : (0 : ℝ) ≤ x + y := h0.le
  have key : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b →
      a / (a + b) * sqrtLog (a + b) ≤ sqrtLog a := by
    intro a b ha hb hab
    have h := concaveOn_sqrtLog.2 (show a + b ∈ Ici (0 : ℝ) from hab.le)
      (show (0 : ℝ) ∈ Ici 0 from le_rfl) (div_nonneg ha hab.le) (div_nonneg hb hab.le)
      (show a / (a + b) + b / (a + b) = 1 by field_simp)
    simp only [smul_eq_mul, mul_zero, add_zero, sqrtLog_zero] at h
    rwa [div_mul_cancel₀ _ hab.ne'] at h
  have h1 := key hx hy h0
  have h2 := key hy hx (by linarith)
  rw [add_comm y x] at h2
  have : x / (x + y) * sqrtLog (x + y) + y / (x + y) * sqrtLog (x + y) = sqrtLog (x + y) := by
    field_simp
  linarith

/-- `ω(c x) ≤ √(max c 1) ω(x)`. -/
theorem sqrtLog_mul_le {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    sqrtLog (c * x) ≤ √(max c 1) * sqrtLog x := by
  rcases lt_or_ge c 1 with hc1 | hc1
  · rw [max_eq_right hc1.le, sqrt_one, one_mul]
    exact monotone_sqrtLog (by nlinarith)
  rw [max_eq_left hc1, sqrtLog_eq_gt1 hx, sqrtLog_eq_gt1 (mul_nonneg hc.le hx), ← sqrt_mul hc.le]
  refine sqrt_le_sqrt ?_
  -- `g̃(c x) ≤ c g̃(x)`
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [gt1, gt1, min_eq_left hx1]
    rcases le_or_gt (c * x) 1 with hcx | hcx
    · rw [min_eq_left hcx]
      rcases eq_or_lt_of_le hx with h0 | h0
      · rw [← h0]; simp [gl]
      unfold gl
      rw [Real.log_mul hc.ne' h0.ne']
      have := log_nonneg hc1
      nlinarith [mul_nonneg (mul_nonneg hc.le hx) this]
    · rw [min_eq_right hcx.le, gl_one]
      have := le_gl hx hx1
      nlinarith
  · rw [gt1, gt1, min_eq_right hx1.le, min_eq_right (by nlinarith), gl_one]
    linarith

/-- `√(min x 1) ≤ ω(x)`. -/
theorem sqrt_min_le_sqrtLog {x : ℝ} (hx : 0 ≤ x) : √(min x 1) ≤ sqrtLog x := by
  rw [sqrtLog_eq_gt1 hx, gt1]
  exact sqrt_le_sqrt (le_gl (le_min hx zero_le_one) (min_le_right _ _))

/-- For `0 ≤ η ≤ 1/e`: `ω(η) ≤ √2 √(η log(1/η))`. -/
theorem sqrtLog_le_sqrt_log_inv {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ exp (-1)) :
    sqrtLog η ≤ √2 * √(η * Real.log (1 / η)) := by
  have he : exp (-1) < 1 := by rw [← exp_zero]; exact exp_lt_exp.2 (by norm_num)
  rw [sqrtLog_eq ⟨h0, h1.trans he.le⟩, ← sqrt_mul zero_le_two]
  refine sqrt_le_sqrt ?_
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; simp
  have hL : 1 ≤ Real.log (1 / η) := by
    rw [one_div, Real.log_inv, le_neg]
    calc Real.log η ≤ Real.log (exp (-1)) := Real.log_le_log h h1
      _ = -1 := log_exp _
  rw [Real.log_div (exp_ne_zero 1) h.ne', log_exp, one_div, Real.log_inv] at *
  nlinarith

/-! ### Lemma 3.4 -/

theorem psiL_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ psiL x :=
  mul_nonneg hx.1 (sqrt_nonneg _)

/-- Lemma 3.4(b): `x ↦ x / log(1/x)` is increasing on `(0, 1)`. -/
theorem strictMonoOn_div_log : StrictMonoOn (fun x : ℝ ↦ x / Real.log (1 / x)) (Ioo 0 1) := by
  intro x hx y hy hxy
  have hLx : 0 < Real.log (1 / x) := log_pos (one_lt_one_div hx.1 hx.2)
  have hLy : 0 < Real.log (1 / y) := log_pos (one_lt_one_div hy.1 hy.2)
  have hL : Real.log (1 / y) < Real.log (1 / x) :=
    Real.log_lt_log (one_div_pos.2 hy.1) (one_div_lt_one_div_of_lt hx.1 hxy)
  calc x / Real.log (1 / x) < x / Real.log (1 / y) := div_lt_div_of_pos_left hx.1 hLy hL
    _ < y / Real.log (1 / y) := div_lt_div_of_pos_right hxy hLy

/-- Lemma 3.4(c), **inversion**: if `x ∈ (0,1)`, `D ∈ (0,1]` and `x / log(1/x) ≤ D`, then
`x ≤ D log(e/D)`. -/
theorem le_of_div_log_le {x D : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hD : D ∈ Ioc (0 : ℝ) 1)
    (h : x / Real.log (1 / x) ≤ D) : x ≤ D * Real.log (exp 1 / D) := by
  have hLx : 0 < Real.log (1 / x) := log_pos (one_lt_one_div hx.1 hx.2)
  have h' : x ≤ D * Real.log (1 / x) := by rwa [div_le_iff₀ hLx] at h
  have hLD : 0 ≤ Real.log (1 / D) := log_nonneg (one_le_one_div hD.1 hD.2)
  have heD : Real.log (exp 1 / D) = 1 + Real.log (1 / D) := by
    rw [Real.log_div (exp_ne_zero 1) hD.1.ne', log_exp, one_div, Real.log_inv]; ring
  rw [heD]
  rcases le_or_gt x D with hxD | hxD
  · nlinarith [hD.1]
  · have : Real.log (1 / x) < Real.log (1 / D) :=
      Real.log_lt_log (one_div_pos.2 hx.1) (one_div_lt_one_div_of_lt hD.1 hxD)
    nlinarith [hD.1]

/-- Lemma 3.4(d): `√x log(e/x) ≤ 2/√e` on `(0, 1]`. -/
theorem sqrt_mul_log_le {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    √x * Real.log (exp 1 / x) ≤ 2 / √(exp 1) := by
  have hse : 0 < √(exp 1) := sqrt_pos.2 (exp_pos 1)
  have hsx : 0 < √x := sqrt_pos.2 hx.1
  have hu : 0 ≤ √(exp 1) * √x := by positivity
  have h1 := self_sub_one_le_mul_log hu
  rw [Real.log_mul hse.ne' hsx.ne', Real.log_sqrt (exp_pos 1).le, Real.log_sqrt hx.1.le,
    log_exp] at h1
  rw [Real.log_div (exp_ne_zero 1) hx.1.ne', log_exp, le_div_iff₀ hse]
  nlinarith

namespace Rates

theorem psiL_eq (x : ℝ) : psiL x = x * √(-Real.log x) := by
  rw [psiL, one_div, Real.log_inv]

theorem psiL_eq_sqrt {x : ℝ} (hx : 0 ≤ x) : psiL x = √(-(x * (x * Real.log x))) := by
  rw [psiL_eq, show -(x * (x * Real.log x)) = x ^ 2 * (-Real.log x) by ring,
    sqrt_mul (sq_nonneg x), sqrt_sq hx]

theorem continuousOn_psiL : ContinuousOn psiL (Ici 0) := by
  have hc : Continuous fun x : ℝ ↦ √(-(x * (x * Real.log x))) :=
    (continuous_id.mul continuous_mul_log).neg.sqrt
  exact hc.continuousOn.congr fun x hx ↦ psiL_eq_sqrt hx

/-- `ψ'(x) = √L - 1/(2√L)`, `L = log(1/x)`. -/
noncomputable def psiL' (x : ℝ) : ℝ := √(-Real.log x) - 1 / (2 * √(-Real.log x))

theorem hasDerivAt_psiL {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : HasDerivAt psiL (psiL' x) x := by
  have hL : 0 < -Real.log x := neg_pos.2 (log_neg h0 h1)
  have hs : 0 < √(-Real.log x) := sqrt_pos.2 hL
  have h : HasDerivAt (fun x ↦ x * √(-Real.log x))
      (1 * √(-Real.log x) + x * ((-x⁻¹) / (2 * √(-Real.log x)))) x :=
    (hasDerivAt_id' x).mul ((hasDerivAt_log h0.ne').neg.sqrt hL.ne')
  rw [show psiL = fun x ↦ x * √(-Real.log x) from funext psiL_eq]
  refine h.congr_deriv ?_
  unfold psiL'
  field_simp
  ring

theorem exp_neg_half_lt_one : exp (-(1 / 2)) < 1 := by
  rw [← exp_zero]; exact exp_lt_exp.2 (by norm_num)

theorem half_lt_neg_log {x : ℝ} (h0 : 0 < x) (h1 : x < exp (-(1 / 2))) : 1 / 2 < -Real.log x := by
  have := Real.log_lt_log h0 h1
  rw [log_exp] at this
  linarith

end Rates

/-- Lemma 3.4(a): `ψ` is concave on `[0, e^{-1/2}]`. -/
theorem concaveOn_psiL : ConcaveOn ℝ (Icc 0 (exp (-(1 / 2)))) psiL := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
    (continuousOn_psiL.mono Icc_subset_Ici_self) ?_ ?_
  · rw [interior_Icc]
    exact fun x hx ↦ (hasDerivAt_psiL hx.1 (hx.2.trans exp_neg_half_lt_one)).differentiableAt
      |>.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha b hb hab
    rw [(hasDerivAt_psiL ha.1 (ha.2.trans exp_neg_half_lt_one)).deriv,
      (hasDerivAt_psiL hb.1 (hb.2.trans exp_neg_half_lt_one)).deriv]
    have hLa := half_lt_neg_log ha.1 ha.2
    have hLb := half_lt_neg_log hb.1 hb.2
    have hL : -Real.log b ≤ -Real.log a := neg_le_neg (Real.log_le_log ha.1 hab)
    have hs : √(-Real.log b) ≤ √(-Real.log a) := sqrt_le_sqrt hL
    have hsb : 0 < √(-Real.log b) := sqrt_pos.2 (by linarith)
    have h2 : 1 / (2 * √(-Real.log a)) ≤ 1 / (2 * √(-Real.log b)) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    unfold psiL'
    linarith

/-- Lemma 3.4(a): `ψ` is nondecreasing on `[0, e^{-1/2}]`. -/
theorem monotoneOn_psiL : MonotoneOn psiL (Icc 0 (exp (-(1 / 2)))) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := psiL') (convex_Icc _ _)
    (continuousOn_psiL.mono Icc_subset_Ici_self) (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · rw [interior_Icc] at hx ⊢
    exact (hasDerivAt_psiL hx.1 (hx.2.trans exp_neg_half_lt_one)).hasDerivWithinAt
  · rw [interior_Icc] at hx
    have hL := half_lt_neg_log hx.1 hx.2
    have hs : 0 < √(-Real.log x) := sqrt_pos.2 (by linarith)
    have hss := mul_self_sqrt (show 0 ≤ -Real.log x by linarith)
    unfold psiL'
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith

end BGHKLMM26.RobustMIS
