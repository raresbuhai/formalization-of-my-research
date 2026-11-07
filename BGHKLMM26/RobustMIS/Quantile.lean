module

public import BGHKLMM26.RobustMIS.Normal
public import Mathlib.Analysis.Convex.Deriv

/-!
# The Gaussian quantile and the isoperimetric function

Lemma 3.1 (the function `q = φ ∘ Φ⁻¹`) and Lemma 3.2 (its Taylor remainder) of
`eldan-proof.tex` (§3), with the basic facts on `Ψ = Φ⁻¹` (standard fact (S7)).

Material: `Gaussian.Phi` and `Gaussian.exists_Phi_eq` (`Background/GaussianCoins.lean`);
TauCeti's `hasDerivAt_cdf_gaussianReal`, `strictMono_cdf_gaussianReal`; the calculus of `Ψ` and
`q` follows OpenAI's `GaussianPropeller/Quantile.lean` (`hasDerivAt_q`, `hasDerivAt_I`,
`concaveOn_I`; Apache-2.0, openai/math 4eaee87).

Proofs: `Ψ` is continuous on `(0, 1)` as a strictly monotone function with image `ℝ`, hence
differentiable by the inverse function theorem in one variable, and `C^∞` by induction
(`Ψ' = 1/(φ ∘ Ψ)`). Continuity of `q` at `0` uses `Ψ(a) < -M` for `a < Φ(-M)`. Lemma 3.2 is
proved without integrals: with `F(w) = R(s; w)` one has `F'(w) = (s - w)/q(w)`, and each bound
follows by comparing `F` with `-c (s - w)²/λ(w)`, resp. `-c (s - w)²`, through the sign of the
derivative of the difference on each side of `s` (`Quantile.le_of_deriv_sign`); the key identity
for the lower bound is `λ(w) + (s - w)(1 - 2w) = (1 - s) w² + s (1 - w)² ≥ 0`. The case
`s ∈ {0, 1}` follows by continuity.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open Gaussian
open scoped ContDiff

/-! ### The quantile `Ψ = Φ⁻¹` -/

theorem Phi_Psi {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : Phi (Psi a) = a := by
  simp only [Psi, ha, ↓reduceDIte]
  exact Classical.choose_spec (exists_Phi_eq ha)

theorem Psi_Phi (x : ℝ) : Psi (Phi x) = x := by
  have hx : Phi x ∈ Ioo (0 : ℝ) 1 := ⟨Phi_pos x, Phi_lt_one x⟩
  exact strictMono_Phi.injective (Phi_Psi hx)

theorem strictMonoOn_Psi : StrictMonoOn Psi (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  rw [← strictMono_Phi.lt_iff_lt, Phi_Psi ha, Phi_Psi hb]
  exact hab

theorem Psi_le_iff {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (x : ℝ) : x ≤ Psi a ↔ Phi x ≤ a := by
  rw [← strictMono_Phi.le_iff_le, Phi_Psi ha]

theorem Psi_half : Psi (1 / 2) = 0 := by
  rw [← Phi_zero, Psi_Phi]

theorem Psi_one_sub {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : Psi (1 - a) = -Psi a := by
  rw [← Psi_Phi (-Psi a), Phi_neg, Phi_Psi ha]

namespace Quantile

theorem Phi_mem (x : ℝ) : Phi x ∈ Ioo (0 : ℝ) 1 := ⟨Phi_pos x, Phi_lt_one x⟩

theorem one_sub_mem {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : 1 - a ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [ha.2], by linarith [ha.1]⟩

theorem image_Psi : Psi '' Ioo (0 : ℝ) 1 = univ :=
  eq_univ_of_forall fun x ↦ ⟨Phi x, Phi_mem x, Psi_Phi x⟩

theorem continuousAt_Psi {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : ContinuousAt Psi a :=
  strictMonoOn_Psi.continuousAt_of_image_mem_nhds (isOpen_Ioo.mem_nhds ha)
    (by rw [image_Psi]; exact univ_mem)

theorem continuousOn_Psi : ContinuousOn Psi (Ioo (0 : ℝ) 1) :=
  fun _ ha ↦ (continuousAt_Psi ha).continuousWithinAt

theorem qf_eq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : qf a = npdf (Psi a) := by
  simp only [qf, ha, ↓reduceIte]

theorem qf_eventuallyEq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : qf =ᶠ[𝓝 a] fun b ↦ npdf (Psi b) := by
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact qf_eq hb

theorem contDiff_npdf {k : WithTop ℕ∞} : ContDiff ℝ k npdf := by
  rw [show npdf = fun x ↦ (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) from funext Normal.npdf_eq]
  fun_prop

theorem continuous_npdf : Continuous npdf := (contDiff_npdf (k := 0)).continuous

end Quantile

open Quantile

/-- (S7) `Ψ' = 1/φ(Ψ) = 1/q`. -/
theorem hasDerivAt_Psi {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : HasDerivAt Psi (1 / qf a) a := by
  rw [qf_eq ha, one_div]
  refine HasDerivAt.of_local_left_inverse (continuousAt_Psi ha) (hasDerivAt_Phi _)
    (npdf_pos _).ne' ?_
  filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
  exact Phi_Psi hb

/-- `Ψ` is smooth on `(0, 1)` (inverse function theorem, (S7)). -/
theorem contDiffOn_Psi : ContDiffOn ℝ ∞ Psi (Ioo (0 : ℝ) 1) := by
  have hderiv : EqOn (deriv Psi) (fun a ↦ (npdf (Psi a))⁻¹) (Ioo (0 : ℝ) 1) := by
    intro a ha
    rw [(hasDerivAt_Psi ha).deriv, qf_eq ha, one_div]
  have hdiff : DifferentiableOn ℝ Psi (Ioo (0 : ℝ) 1) :=
    fun a ha ↦ (hasDerivAt_Psi ha).differentiableAt.differentiableWithinAt
  rw [contDiffOn_infty]
  intro n
  induction n with
  | zero => exact contDiffOn_zero.2 continuousOn_Psi
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨hdiff, by simp, ?_⟩
    refine ContDiffOn.congr ?_ hderiv
    exact (contDiff_npdf.comp_contDiffOn ih).inv fun a _ ↦ (npdf_pos _).ne'

/-! ### Lemma 3.1: the function `q` -/

theorem qf_pos {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : 0 < qf a := by
  simp only [qf, ha, ↓reduceIte]
  exact gaussianPDFReal_pos _ _ _ one_ne_zero

theorem qf_nonneg (a : ℝ) : 0 ≤ qf a := by
  unfold qf
  split_ifs
  · exact gaussianPDFReal_nonneg _ _ _
  · exact le_rfl

theorem qf_of_not_mem {a : ℝ} (ha : a ∉ Ioo (0 : ℝ) 1) : qf a = 0 := by
  simp only [qf, ha, ↓reduceIte]

theorem qf_half : qf (1 / 2) = (√(2 * π))⁻¹ := by
  rw [qf_eq ⟨by norm_num, by norm_num⟩, Psi_half, Normal.npdf_eq]
  simp

theorem qf_one_sub (a : ℝ) : qf (1 - a) = qf a := by
  by_cases ha : a ∈ Ioo (0 : ℝ) 1
  · rw [qf_eq (one_sub_mem ha), qf_eq ha, Psi_one_sub ha, npdf_neg]
  · have h1 : 1 - a ∉ Ioo (0 : ℝ) 1 := fun h ↦ ha (by simpa using one_sub_mem h)
    rw [qf_of_not_mem ha, qf_of_not_mem h1]

/-- `q ≤ q(1/2) = (2π)^{-1/2}`. -/
theorem qf_le (a : ℝ) : qf a ≤ (√(2 * π))⁻¹ := by
  by_cases ha : a ∈ Ioo (0 : ℝ) 1
  · rw [qf_eq ha]; exact npdf_le _
  · rw [qf_of_not_mem ha]; positivity

theorem qf_sq_le (a : ℝ) : qf a ^ 2 ≤ 1 / (2 * π) := by
  have h := pow_le_pow_left₀ (qf_nonneg a) (qf_le a) 2
  rw [inv_pow, sq_sqrt (by positivity)] at h
  rwa [one_div]

namespace Quantile

theorem npdf_le_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ |y|) : npdf y ≤ npdf x := by
  rw [Normal.npdf_eq, Normal.npdf_eq]
  have : x ^ 2 ≤ y ^ 2 := by rw [← sq_abs y]; exact pow_le_pow_left₀ hx hxy 2
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) (by positivity)

theorem qf_zero : qf 0 = 0 := qf_of_not_mem (by simp)

theorem continuousWithinAt_qf_zero : ContinuousWithinAt qf (Icc 0 1) 0 := by
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨M, hM⟩ :=
    Filter.eventually_atTop.1 (Normal.tendsto_npdf_atTop.eventually (gt_mem_nhds hε))
  refine ⟨Phi (-max M 0), Phi_pos _, fun {a} ha hda ↦ ?_⟩
  rw [qf_zero, Real.dist_eq, sub_zero, abs_of_nonneg (qf_nonneg a)]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ha.1] at hda
  rcases eq_or_lt_of_le ha.1 with h0 | h0
  · rw [← h0, qf_zero]; exact hε
  have ha' : a ∈ Ioo (0 : ℝ) 1 := ⟨h0, hda.trans (Phi_lt_one _)⟩
  have hlt : Psi a < -max M 0 := by
    rw [← strictMono_Phi.lt_iff_lt, Phi_Psi ha']; exact hda
  rw [qf_eq ha']
  calc npdf (Psi a) ≤ npdf (max M 0) :=
        npdf_le_of_le (le_max_right _ _)
          (by rw [abs_of_neg (by linarith [le_max_right M 0])]; linarith)
    _ < ε := hM _ (le_max_left _ _)

end Quantile

theorem continuousOn_qf : ContinuousOn qf (Icc 0 1) := by
  intro a ha
  rcases eq_or_lt_of_le ha.1 with h0 | h0
  · rw [← h0]; exact continuousWithinAt_qf_zero
  rcases eq_or_lt_of_le ha.2 with h1 | h1
  · rw [h1]
    have hm : MapsTo (fun b : ℝ ↦ 1 - b) (Icc 0 1) (Icc 0 1) :=
      fun b hb ↦ ⟨by linarith [hb.2], by linarith [hb.1]⟩
    have h0' : ContinuousWithinAt qf (Icc 0 1) ((fun b : ℝ ↦ 1 - b) 1) := by
      simpa only [sub_self] using continuousWithinAt_qf_zero
    have hc := h0'.comp ((continuous_const.sub continuous_id).continuousWithinAt
      (s := Icc (0 : ℝ) 1) (x := 1)) hm
    have he : (qf ∘ fun b : ℝ ↦ 1 - b) = qf := funext fun b ↦ qf_one_sub b
    rwa [he] at hc
  have ha' : a ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.congr ?_ (qf_eventuallyEq ha').symm
  exact continuous_npdf.continuousAt.comp (continuousAt_Psi ha')

/-- `q' = -Ψ` on `(0, 1)`. -/
theorem hasDerivAt_qf {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : HasDerivAt qf (-Psi a) a := by
  have h := (hasDerivAt_npdf (Psi a)).comp a (hasDerivAt_Psi ha)
  have hq := qf_pos ha
  rw [qf_eq ha] at h hq
  exact (h.congr_deriv (by rw [mul_assoc, mul_one_div_cancel hq.ne', mul_one]))
    |>.congr_of_eventuallyEq (qf_eventuallyEq ha)

/-- `q'' = -1/q` on `(0, 1)`. -/
theorem hasDerivAt_neg_Psi {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun b ↦ -Psi b) (-(1 / qf a)) a :=
  (hasDerivAt_Psi ha).neg

/-- `q = φ ∘ Ψ` is smooth on `(0, 1)` (so are `q²`, `J(s, ·)` compositions in Deficit/Drift). -/
theorem contDiffOn_qf : ContDiffOn ℝ ∞ qf (Ioo (0 : ℝ) 1) :=
  (contDiff_npdf.comp_contDiffOn contDiffOn_Psi).congr fun _ ha ↦ qf_eq ha

theorem concaveOn_qf : ConcaveOn ℝ (Icc 0 1) qf := by
  refine AntitoneOn.concaveOn_of_deriv (convex_Icc 0 1) continuousOn_qf ?_ ?_
  · rw [interior_Icc]
    exact fun a ha ↦ (hasDerivAt_qf ha).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha b hb hab
    rw [(hasDerivAt_qf ha).deriv, (hasDerivAt_qf hb).deriv]
    exact neg_le_neg (strictMonoOn_Psi.monotoneOn ha hb hab)

namespace Quantile

theorem sqrt_two_div_pi : √(2 / π) = 2 * (√(2 * π))⁻¹ := by
  have h : (2:ℝ) / π = (2 * (√(2 * π))⁻¹) ^ 2 := by
    rw [mul_pow, inv_pow, sq_sqrt (by positivity)]
    field_simp
  rw [h]
  exact sqrt_sq (by positivity)

theorem qf_ge_of_le_half {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1 / 2) : √(2 / π) * a ≤ qf a := by
  have h := concaveOn_qf.2 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    (show (1 / 2 : ℝ) ∈ Icc 0 1 from ⟨by norm_num, by norm_num⟩)
    (show 0 ≤ 1 - 2 * a by linarith) (show 0 ≤ 2 * a by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, qf_zero] at h
  rw [qf_half, show 2 * a * (1 / 2) = a by ring] at h
  rw [sqrt_two_div_pi]
  linarith

theorem min_mem_of_mem {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : 1 - a ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith [ha.2], by linarith [ha.1]⟩

theorem lam_le_min {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : lam a ≤ min a (1 - a) := by
  unfold lam
  refine le_min ?_ ?_ <;> nlinarith [ha.1, ha.2]

end Quantile

/-- Lemma 3.1(a): `q(a) ≥ √(2/π) min(a, 1 - a)`. -/
theorem qf_ge_min {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : √(2 / π) * min a (1 - a) ≤ qf a := by
  rcases le_total a (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]; exact qf_ge_of_le_half ha.1 h
  · rw [min_eq_right (by linarith), ← qf_one_sub a]
    exact qf_ge_of_le_half (by linarith [ha.2]) (by linarith)

theorem qf_ge_lam {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) : √(2 / π) * lam a ≤ qf a :=
  (mul_le_mul_of_nonneg_left (lam_le_min ha) (sqrt_nonneg _)).trans (qf_ge_min ha)

namespace Quantile

theorem abs_Psi_le_of_le_half {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (h : a ≤ 1 / 2) :
    |Psi a| ≤ √(2 * Real.log (1 / (2 * a))) := by
  have hy : Psi a ≤ 0 := by
    rw [← Psi_half]
    exact strictMonoOn_Psi.monotoneOn ha ⟨by norm_num, by norm_num⟩ h
  have h1 := Phi_le_exp hy
  rw [Phi_Psi ha] at h1
  have h2 : Real.log (2 * a) ≤ -Psi a ^ 2 / 2 :=
    (Real.log_le_iff_le_exp (by linarith [ha.1])).2 (by linarith)
  apply Real.abs_le_sqrt
  rw [one_div, Real.log_inv]
  linarith

end Quantile

/-- Lemma 3.1(b): `|Ψ(a)| ≤ √(2 log(1/(2 min(a, 1 - a))))`. -/
theorem abs_Psi_le {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    |Psi a| ≤ √(2 * Real.log (1 / (2 * min a (1 - a)))) := by
  rcases le_total a (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]; exact abs_Psi_le_of_le_half ha h
  · rw [min_eq_right (by linarith)]
    have h' := abs_Psi_le_of_le_half (one_sub_mem ha) (by linarith)
    have he := Psi_one_sub (one_sub_mem ha)
    rw [sub_sub_cancel] at he
    rw [he, abs_neg]; exact h'

theorem abs_Psi_le_lam {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    |Psi a| ≤ √(2 * Real.log (1 / lam a)) := by
  refine (abs_Psi_le ha).trans (sqrt_le_sqrt (mul_le_mul_of_nonneg_left ?_ (by norm_num)))
  have hl : 0 < lam a := mul_pos ha.1 (by linarith [ha.2])
  have hm := lam_le_min (Ioo_subset_Icc_self ha)
  have hm0 : 0 < min a (1 - a) := lt_min ha.1 (by linarith [ha.2])
  refine Real.log_le_log (by positivity) ?_
  exact one_div_le_one_div_of_le hl (by linarith)

/-- Lemma 3.1(c): `q |Ψ| ≤ φ(1) < 1/4`. -/
theorem qf_mul_abs_Psi_le (a : ℝ) : qf a * |Psi a| ≤ 1 / 4 := by
  by_cases ha : a ∈ Ioo (0 : ℝ) 1
  · rw [qf_eq ha, mul_comm]
    obtain ⟨h1, h2⟩ := abs_mul_npdf_le (Psi a)
    linarith
  · rw [qf_of_not_mem ha, zero_mul]; norm_num

/-- Lemma 3.1(c): `q Ψ² ≤ 2 φ(√2) < 0.294`. -/
theorem qf_mul_Psi_sq_le (a : ℝ) : qf a * Psi a ^ 2 ≤ 0.294 := by
  by_cases ha : a ∈ Ioo (0 : ℝ) 1
  · rw [qf_eq ha, mul_comm]
    exact sq_mul_npdf_le (Psi a)
  · rw [qf_of_not_mem ha, zero_mul]; norm_num

/-! ### Lemma 3.2: the Taylor remainder of `q` -/

namespace Quantile

/-- Comparison: if `(w - s) D'(w) ≥ 0` on `(0,1)`, then `D(s) ≤ D(h)`. -/
theorem le_of_deriv_sign {D D' : ℝ → ℝ} {s h : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (hh : h ∈ Ioo (0 : ℝ) 1)
    (hD : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt D (D' w) w)
    (hsign : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ (w - s) * D' w) : D s ≤ D h := by
  have hsub : ∀ {x y : ℝ}, x ∈ Ioo (0 : ℝ) 1 → y ∈ Ioo (0 : ℝ) 1 → Icc x y ⊆ Ioo 0 1 :=
    fun hx hy w hw ↦ ⟨hx.1.trans_le hw.1, hw.2.trans_lt hy.2⟩
  have hcont : ∀ {x y : ℝ}, x ∈ Ioo (0 : ℝ) 1 → y ∈ Ioo (0 : ℝ) 1 → ContinuousOn D (Icc x y) :=
    fun hx hy w hw ↦ (hD w (hsub hx hy hw)).continuousAt.continuousWithinAt
  rcases le_total s h with hsh | hhs
  · have hm : MonotoneOn D (Icc s h) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := D') (convex_Icc s h) (hcont hs hh)
        (fun w hw ↦ ?_) (fun w hw ↦ ?_)
      · rw [interior_Icc] at hw ⊢
        exact (hD w (hsub hs hh (Ioo_subset_Icc_self hw))).hasDerivWithinAt
      · rw [interior_Icc] at hw
        exact (mul_nonneg_iff_of_pos_left (sub_pos.2 hw.1)).1
          (hsign w (hsub hs hh (Ioo_subset_Icc_self hw)))
    exact hm ⟨le_rfl, hsh⟩ ⟨hsh, le_rfl⟩ hsh
  · have ha : AntitoneOn D (Icc h s) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := D') (convex_Icc h s) (hcont hh hs)
        (fun w hw ↦ ?_) (fun w hw ↦ ?_)
      · rw [interior_Icc] at hw ⊢
        exact (hD w (hsub hh hs (Ioo_subset_Icc_self hw))).hasDerivWithinAt
      · rw [interior_Icc] at hw
        have := hsign w (hsub hh hs (Ioo_subset_Icc_self hw))
        exact le_of_not_gt fun h' ↦ (mul_neg_of_neg_of_pos (sub_neg.2 hw.2) h').not_ge this
    exact ha ⟨le_rfl, hhs⟩ ⟨hhs, le_rfl⟩ hhs

theorem hasDerivAt_lam (w : ℝ) : HasDerivAt lam (1 - 2 * w) w := by
  have h : HasDerivAt (fun x : ℝ ↦ x * (1 - x)) (1 * (1 - w) + w * (0 - 1)) w :=
    (hasDerivAt_id' w).mul ((hasDerivAt_const w (1 : ℝ)).sub (hasDerivAt_id' w))
  exact h.congr_deriv (by ring)

theorem hasDerivAt_rem (s : ℝ) {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w ↦ qf s - qf w + Psi w * (s - w)) ((s - w) / qf w) w := by
  have h : HasDerivAt (fun w ↦ qf s - qf w + Psi w * (s - w))
      (0 - -Psi w + (1 / qf w * (s - w) + Psi w * (0 - 1))) w :=
    ((hasDerivAt_const w (qf s)).sub (hasDerivAt_qf hw)).add
      ((hasDerivAt_Psi hw).mul ((hasDerivAt_const w s).sub (hasDerivAt_id' w)))
  exact h.congr_deriv (by ring)

theorem hasDerivAt_sub_sq (s w : ℝ) : HasDerivAt (fun w ↦ (s - w) ^ 2) (-(2 * (s - w))) w := by
  have h : HasDerivAt (fun w ↦ (s - w) ^ 2) (((2:ℕ):ℝ) * (s - w) ^ (2 - 1) * (0 - 1)) w :=
    ((hasDerivAt_const w s).sub (hasDerivAt_id' w)).pow 2
  exact h.congr_deriv (by norm_num)

theorem two_mul_sqrt_pi_div_two : 2 * √(π / 2) = √(2 * π) := by
  rw [show (2:ℝ) * π = 2 ^ 2 * (π / 2) by ring, sqrt_mul (by positivity), sqrt_sq (by norm_num)]

theorem sqrt_pi_div_two_mul : √(π / 2) * √(2 / π) = 1 := by
  rw [← sqrt_mul (by positivity), show π / 2 * (2 / π) = 1 by field_simp, sqrt_one]

theorem taylor_lower_Ioo {h s : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    -(√(π / 2) * (s - h) ^ 2 / lam h) ≤ qf s - qf h + Psi h * (s - h) := by
  obtain ⟨c, hc⟩ : ∃ c, c = √(π / 2) := ⟨_, rfl⟩
  rw [← hc]
  have hc0 : 0 ≤ c := hc ▸ sqrt_nonneg _
  let D : ℝ → ℝ := fun w ↦ qf s - qf w + Psi w * (s - w) + c * ((s - w) ^ 2 / lam w)
  let D' : ℝ → ℝ := fun w ↦ (s - w) / qf w +
    c * ((-(2 * (s - w)) * lam w - (s - w) ^ 2 * (1 - 2 * w)) / lam w ^ 2)
  have hD : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt D (D' w) w := by
    intro w hw
    have hl : lam w ≠ 0 := (mul_pos hw.1 (by linarith [hw.2])).ne'
    exact (hasDerivAt_rem s hw).add
      (((hasDerivAt_sub_sq s w).div (hasDerivAt_lam w) hl).const_mul c)
  have hsign : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ (w - s) * D' w := by
    intro w hw
    have hl : 0 < lam w := mul_pos hw.1 (by linarith [hw.2])
    have hq : 0 < qf w := qf_pos hw
    have hqge : √(2 / π) * lam w ≤ qf w := qf_ge_lam (Ioo_subset_Icc_self hw)
    have h1 : 1 / qf w ≤ c / lam w := by
      rw [div_le_div_iff₀ hq hl]
      calc 1 * lam w = c * (√(2 / π) * lam w) := by
            rw [← mul_assoc, hc, sqrt_pi_div_two_mul]
        _ ≤ c * qf w := mul_le_mul_of_nonneg_left hqge hc0
    have hX : 0 ≤ lam w + (s - w) * (1 - 2 * w) := by
      have : lam w + (s - w) * (1 - 2 * w) = (1 - s) * w ^ 2 + s * (1 - w) ^ 2 := by
        unfold lam; ring
      rw [this]
      exact add_nonneg (mul_nonneg (by linarith [hs.2]) (sq_nonneg _))
        (mul_nonneg (by linarith [hs.1]) (sq_nonneg _))
    have key : (w - s) * D' w = (s - w) ^ 2 * ((c / lam w - 1 / qf w) +
        c * (lam w + (s - w) * (1 - 2 * w)) / lam w ^ 2) := by
      simp only [D']
      field_simp
      ring
    rw [key]
    exact mul_nonneg (sq_nonneg _) (add_nonneg (by linarith)
      (div_nonneg (mul_nonneg hc0 hX) (by positivity)))
  have := le_of_deriv_sign hs hh hD hsign
  simp only [D, sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div] at this
  rw [mul_div_assoc]
  linarith

theorem taylor_upper_Ioo {h s : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Ioo (0 : ℝ) 1) :
    qf s - qf h + Psi h * (s - h) ≤ -(√(π / 2) * (s - h) ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c, c = √(π / 2) := ⟨_, rfl⟩
  rw [← hc]
  let D : ℝ → ℝ := fun w ↦ -(c * (s - w) ^ 2) - (qf s - qf w + Psi w * (s - w))
  let D' : ℝ → ℝ := fun w ↦ -(c * -(2 * (s - w))) - (s - w) / qf w
  have hD : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt D (D' w) w := fun w hw ↦
    ((hasDerivAt_sub_sq s w).const_mul c).neg.sub (hasDerivAt_rem s hw)
  have hsign : ∀ w ∈ Ioo (0 : ℝ) 1, 0 ≤ (w - s) * D' w := by
    intro w hw
    have hq : 0 < qf w := qf_pos hw
    have h1 : 2 * c ≤ 1 / qf w := by
      rw [hc, two_mul_sqrt_pi_div_two]
      have := one_div_le_one_div_of_le hq (qf_le w)
      rw [one_div (√(2 * π))⁻¹, inv_inv] at this; exact this
    have key : (w - s) * D' w = (s - w) ^ 2 * (1 / qf w - 2 * c) := by
      simp only [D']
      field_simp
      ring
    rw [key]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have := le_of_deriv_sign hs hh hD hsign
  simp only [D, sub_self, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, neg_zero, add_zero] at this
  linarith

end Quantile

/-- **Lemma 3.2** (cf. Eldan Fact 26): for `h ∈ (0,1)`, `s ∈ [0,1]`, the remainder
`R(s; h) = q(s) - q(h) - q'(h)(s - h)` satisfies `-√(π/2) (s-h)²/λ(h) ≤ R ≤ -√(π/2) (s-h)²`. -/
theorem taylor_qf {h s : ℝ} (hh : h ∈ Ioo (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    -(√(π / 2) * (s - h) ^ 2 / lam h) ≤ qf s - qf h + Psi h * (s - h) ∧
      qf s - qf h + Psi h * (s - h) ≤ -(√(π / 2) * (s - h) ^ 2) := by
  have hcl : s ∈ closure (Ioo (0 : ℝ) 1) := by rw [closure_Ioo zero_ne_one]; exact hs
  have hg : ContinuousOn (fun s ↦ qf s - qf h + Psi h * (s - h)) (Icc 0 1) :=
    (continuousOn_qf.sub continuousOn_const).add (by fun_prop)
  constructor
  · refine ContinuousWithinAt.closure_le (f := fun s ↦ -(√(π / 2) * (s - h) ^ 2 / lam h))
      (g := fun s ↦ qf s - qf h + Psi h * (s - h)) hcl ?_ ?_ fun y hy ↦ taylor_lower_Ioo hh hy
    · exact (by fun_prop : Continuous fun s ↦ -(√(π / 2) * (s - h) ^ 2 / lam h)).continuousWithinAt
    · exact (hg s hs).mono Ioo_subset_Icc_self
  · refine ContinuousWithinAt.closure_le (g := fun s ↦ -(√(π / 2) * (s - h) ^ 2))
      (f := fun s ↦ qf s - qf h + Psi h * (s - h)) hcl ?_ ?_ fun y hy ↦ taylor_upper_Ioo hh hy
    · exact (hg s hs).mono Ioo_subset_Icc_self
    · exact (by fun_prop : Continuous fun s ↦ -(√(π / 2) * (s - h) ^ 2)).continuousWithinAt

end BGHKLMM26.RobustMIS
