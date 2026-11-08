module

public import BGHKLMM26.RobustMIS.SharpBasic

/-!
# The sharp Gaussian lemma: the halfspace and its defect

For a unit vector `u` and `α ∈ ℝ`, the halfspace `H = {α ≤ ⟨u, x⟩}` (`halfInd u α`):
* its mean `1 - Φ(α)`, its stability `Γ_t(1 - Φ(α))`, its first Hermite vector `φ(α) u`, and
  `T_t 𝟙_H(x) = w(⟨u, x⟩)` with `w = wfun t α` increasing;
* for `F : ℝⁿ → [0,1]` with the mean of `H`, the defect `I = ⟨𝟙_H - F, T_t 𝟙_H⟩` as the weighted
  mismatch `E[|F - 𝟙_H| |w(⟨u, x⟩) - w(α)|]`, and the deficit identity
  `Γ_t(E F) - Stab_t(F) = 2 I - Stab_t(F - 𝟙_H)`;
* the transport bound `I ≥ c ‖F - 𝟙_H‖₁²`;
* the slope of `w` near `α`, `w'(α) = t K_t(α, α) φ(α)`, and its gap away from `α`.

All statements are proved. Proofs:
* the law of `⟨u, x⟩` under `γₙ` is `γ₁` (`SharpW.integral_comp_inner`); the part of `F̂⁽¹⁾`
  orthogonal to `u` vanishes by the fiber decomposition `StaticFiber.integral_fiber`;
* `Stab_t(𝟙_H) = E[𝟙{s ≥ α} w(s)]`, and `Γ_t(1 - Φ(α)) = P(X ≤ -α, t X + σ Z ≤ -α)`
  (`GammaCalc.Gam_eq_prod`), which is the same integral after `x ↦ -x`;
* the weighted mismatch: `E(𝟙_H - F) = 0`, and `(𝟙_H - F)(w - w(α)) ≥ 0` pointwise;
* the deficit identity: `nBil_add_self` and `nBil_comm` for `F = 𝟙_H + (F - 𝟙_H)`;
* `|Φ(b) - Φ(a)| ≥ |b - a| min(φ(a), φ(b))` (`SharpW.abs_Phi_sub_ge`, mean value inequality),
  which gives `|w(s) - w(α)| ≥ m ρ` for `|s - α| ≥ ρ`, `ρ ≤ 1`, `|α| ≤ A` with the explicit
  `m = (t/σ) φ((1 + |A|)/σ)` (`SharpW.wfun_gap_aux`); the transport bound takes `ρ = ‖F - 𝟙_H‖₁/2`,
  the slab `|⟨u, x⟩ - α| ≤ ρ` having mass at most `ρ` (`gaussianReal_Icc_le`), and `c = m/4`;
* the strip: `φ(a) = φ(b) exp((b² - a²)/2)` with `|a² - b²| = O(r)` uniformly for `|α| ≤ A`.

Helpers (namespace `SharpW`): `integral_comp_inner`, `measurable_halfInd`, `halfInd_mem`,
`continuous_wfun`, `wfun_mono`, `nBil_halfInd_right` (`⟨f, T_t 𝟙_H⟩ = E[f w(⟨u, x⟩)]`),
`abs_Phi_sub_ge`, `abs_wfun_sub_ge`, `mslope`, `wfun_gap_aux`, `npdf_ratio`, `mehler_diag`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace
open Gaussian

variable {n : ℕ}

namespace SharpW

theorem measurable_halfInd (u : Gs n) (α : ℝ) : Measurable (halfInd u α) :=
  measurable_one.indicator (measurableSet_le measurable_const (by fun_prop))

theorem halfInd_mem (u : Gs n) (α : ℝ) (x : Gs n) : 0 ≤ halfInd u α x ∧ halfInd u α x ≤ 1 := by
  rw [QBath.halfInd_eq]; exact Static1D.ind_mem α _

theorem abs_halfInd_le (u : Gs n) (α : ℝ) (x : Gs n) : |halfInd u α x| ≤ 1 :=
  Static.abs_le_one (halfInd_mem u α) x

theorem abs_sub_halfInd_le {F : Gs n → ℝ} (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (u : Gs n) (α : ℝ)
    (x : Gs n) : |F x - halfInd u α x| ≤ 1 := by
  have h1 := halfInd_mem u α x
  rw [abs_le]; constructor <;> linarith [h01 x]

/-- The law of `⟨u, x⟩` under `γₙ` is `γ₁`. -/
theorem integral_comp_inner {u : Gs n} (hu : ‖u‖ = 1) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f ⟪u, x⟫ ∂gm n = ∫ s, f s ∂gaussianReal 0 1 := by
  rw [← Gaussian.map_inner_stdGaussian hu, integral_map (by fun_prop) hf.aestronglyMeasurable]

/-- `𝟙{α ≤ a + σ b} = 𝟙{(α - a)/σ ≤ b}` for `σ > 0`. -/
theorem ind_affine {σ : ℝ} (hσ : 0 < σ) (α a b : ℝ) :
    (Ici α).indicator (1 : ℝ → ℝ) (a + σ * b) = (Ici ((α - a) / σ)).indicator 1 b := by
  have h : α ≤ a + σ * b ↔ (α - a) / σ ≤ b := by
    rw [div_le_iff₀ hσ]; constructor <;> intro h <;> linarith
  simp only [Set.indicator_apply, mem_Ici, h, Pi.one_apply]

theorem sigma_pos {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) : 0 < √(1 - t ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith)

theorem continuous_wfun (t α : ℝ) : Continuous (wfun t α) := by
  unfold wfun; exact continuous_Phi.comp (by fun_prop)

theorem wfun_mono {t : ℝ} (ht0 : 0 ≤ t) (α : ℝ) : Monotone (wfun t α) := by
  intro s s' h
  exact strictMono_Phi.monotone
    (div_le_div_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _))

theorem wfun_mem (t α s : ℝ) : 0 ≤ wfun t α s ∧ wfun t α s ≤ 1 :=
  ⟨(Phi_pos _).le, (Phi_lt_one _).le⟩

end SharpW

open SharpW

/-- The mean of the halfspace: `γₙ(H) = 1 - Φ(α)`. -/
theorem gMean_halfInd {u : Gs n} (hu : ‖u‖ = 1) (α : ℝ) : gMean (halfInd u α) = 1 - Phi α := by
  unfold gMean
  simp_rw [QBath.halfInd_eq]
  rw [integral_comp_inner hu (Static1D.measurable_ind α), Static1D.integral_ind]

/-- The first Hermite vector of the halfspace: `E[𝟙_H(x) x] = φ(α) u`. -/
theorem hermite1_halfInd {u : Gs n} (hu : ‖u‖ = 1) (α : ℝ) :
    hermite1 (halfInd u α) = npdf α • u := by
  have hH := measurable_halfInd u α
  refine ext_inner_left ℝ fun v ↦ ?_
  rw [QBath.inner_hermite1 _ hH (halfInd_mem u α), real_inner_smul_right]
  obtain ⟨w, hw⟩ : ∃ w : Gs n, w = v - ⟪v, u⟫ • u := ⟨_, rfl⟩
  have huu := StaticFiber.inner_self_of_norm hu
  have hwu : ⟪w, u⟫ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, huu]; ring
  have hsplit : ∀ x, ⟪v, x⟫ * halfInd u α x =
      ⟪v, u⟫ * (⟪u, x⟫ * halfInd u α x) + ⟪w, x⟫ * halfInd u α x := by
    intro x
    rw [hw, inner_sub_left, real_inner_smul_left]; ring
  have i1 := StaticFiber.integrable_inner_mul (v := u) hH (abs_halfInd_le u α)
  have i2 := StaticFiber.integrable_inner_mul (v := w) hH (abs_halfInd_le u α)
  simp_rw [hsplit]
  rw [integral_add (i1.const_mul _) i2, integral_const_mul]
  have e1 : ∫ x, ⟪u, x⟫ * halfInd u α x ∂gm n = npdf α := by
    simp_rw [QBath.halfInd_eq]
    rw [integral_comp_inner hu (f := fun s ↦ s * (Ici α).indicator 1 s)
      (measurable_id.mul (Static1D.measurable_ind α)), Static1D.integral_mul_ind]
  have e2 : ∫ x, ⟪w, x⟫ * halfInd u α x ∂gm n = 0 := by
    rw [StaticFiber.integral_fiber hu i2]
    have : ∀ y, ∫ s, ⟪w, StaticFiber.fpt u y s⟫ * halfInd u α (StaticFiber.fpt u y s)
        ∂gaussianReal 0 1 = ⟪w, y⟫ * (1 - Phi α) := by
      intro y
      simp_rw [StaticFiber.inner_fpt_of_orth hwu, QBath.halfInd_eq,
        StaticFiber.inner_fpt_self hu]
      rw [integral_const_mul, Static1D.integral_ind]
    simp_rw [this]
    rw [integral_mul_const, StaticFiber.integral_inner_gm, zero_mul]
  rw [e1, e2, add_zero, mul_comm]

/-- `T_t 𝟙_H(x) = w(⟨u, x⟩)`. -/
theorem integral_halfInd_noise {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    (α : ℝ) (x : Gs n) :
    ∫ z, halfInd u α (t • x + √(1 - t ^ 2) • z) ∂gm n = wfun t α ⟪u, x⟫ := by
  have hσ := sigma_pos ht0 ht1
  have e : ∀ z, halfInd u α (t • x + √(1 - t ^ 2) • z) =
      (Ici ((α - t * ⟪u, x⟫) / √(1 - t ^ 2))).indicator 1 ⟪u, z⟫ := by
    intro z
    rw [QBath.halfInd_eq, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      ind_affine hσ]
  simp_rw [e]
  rw [integral_comp_inner hu (Static1D.measurable_ind _), Static1D.integral_ind, ← Phi_neg,
    wfun]
  congr 1
  ring

namespace SharpW

/-- `∫ f(x) T_t 𝟙_H(x) dγ = ∫ f(x) w(⟨u, x⟩) dγ`. -/
theorem nBil_halfInd_right {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    (α : ℝ) (f : Gs n → ℝ) :
    nBil t f (halfInd u α) = ∫ x, f x * wfun t α ⟪u, x⟫ ∂gm n := by
  unfold nBil
  simp_rw [integral_const_mul, integral_halfInd_noise ht0 ht1 hu]

/-- `∫ 𝟙{a ≤ c} 𝟙{t a + σ b ≤ c} dγ(b) = 𝟙{a ≤ c} Φ((c - t a)/σ)`. -/
theorem integral_ind_prod {t σ : ℝ} (hσ : 0 < σ) (c a : ℝ) :
    ∫ b, {p : ℝ × ℝ | p.1 ≤ c ∧ t * p.1 + σ * p.2 ≤ c}.indicator 1 (a, b) ∂gaussianReal 0 1 =
      (Iic c).indicator 1 a * Phi ((c - t * a) / σ) := by
  have h : ∀ b, {p : ℝ × ℝ | p.1 ≤ c ∧ t * p.1 + σ * p.2 ≤ c}.indicator 1 (a, b) =
      (Iic c).indicator 1 a * (Iic ((c - t * a) / σ)).indicator (1 : ℝ → ℝ) b := by
    intro b
    have hb : t * a + σ * b ≤ c ↔ b ≤ (c - t * a) / σ := by
      rw [le_div_iff₀ hσ]; constructor <;> intro h <;> linarith
    by_cases ha : a ≤ c
    · simp [Set.indicator_apply, ha, hb]
    · simp [Set.indicator_apply, ha]
  simp_rw [h]
  rw [integral_const_mul, integral_indicator_one measurableSet_Iic, ← cdf_eq_real]
  rfl

end SharpW

/-- The stability of the halfspace: `Stab_t(𝟙_H) = Γ_t(1 - Φ(α))`. -/
theorem gStab_halfInd {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1) (α : ℝ) :
    gStab t (halfInd u α) = Gam t (1 - Phi α) := by
  have hσ := sigma_pos ht0 ht1
  have hw := (continuous_wfun t α).measurable
  rw [gStab_eq_nBil, nBil_halfInd_right ht0 ht1 hu]
  simp_rw [QBath.halfInd_eq]
  rw [integral_comp_inner hu (f := fun s ↦ (Ici α).indicator 1 s * wfun t α s)
    ((Static1D.measurable_ind α).mul hw)]
  have ha : 1 - Phi α ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [Phi_lt_one α], by linarith [Phi_pos α]⟩
  have hPsi : Psi (1 - Phi α) = -α := by rw [← Phi_neg, Psi_Phi]
  rw [GammaCalc.Gam_eq_prod ha, hPsi]
  obtain ⟨S, hS⟩ : ∃ S : Set (ℝ × ℝ),
      S = {p : ℝ × ℝ | p.1 ≤ -α ∧ t * p.1 + √(1 - t ^ 2) * p.2 ≤ -α} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le (f := fun p : ℝ × ℝ ↦ t * p.1 + √(1 - t ^ 2) * p.2) (by fun_prop)
        measurable_const)
  rw [← hS, ← integral_indicator_one hSm,
    integral_prod (S.indicator 1) ((integrable_const (1 : ℝ)).indicator hSm)]
  simp_rw [hS, integral_ind_prod hσ]
  have hm : Measurable fun a : ℝ ↦ (Iic (-α)).indicator 1 a * Phi ((-α - t * a) / √(1 - t ^ 2)) :=
    (measurable_one.indicator measurableSet_Iic).mul (measurable_Phi.comp (by fun_prop))
  rw [← Static1D.integral_comp_neg hm]
  congr 1
  funext s
  have e1 : (Iic (-α)).indicator (1 : ℝ → ℝ) (-s) = (Ici α).indicator 1 s := by
    by_cases h : α ≤ s
    · simp [h]
    · simp [h]
  rw [e1, wfun]
  congr 2
  ring

namespace SharpW

/-- `(𝟙_H - F)(w(⟨u, x⟩) - w(α)) = |F - 𝟙_H| |w(⟨u, x⟩) - w(α)|`: both factors change sign at
`⟨u, x⟩ = α`. -/
theorem mul_wfun_sub_eq {t : ℝ} (ht0 : 0 ≤ t) (u : Gs n) (α : ℝ) {F : Gs n → ℝ}
    (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1) (x : Gs n) :
    (halfInd u α x - F x) * (wfun t α ⟪u, x⟫ - wfun t α α) =
      |F x - halfInd u α x| * |wfun t α ⟪u, x⟫ - wfun t α α| := by
  have hF := h01 x
  rw [QBath.halfInd_eq]
  by_cases h : α ≤ ⟪u, x⟫
  · have hw : wfun t α α ≤ wfun t α ⟪u, x⟫ := wfun_mono ht0 α h
    rw [indicator_of_mem (show ⟪u, x⟫ ∈ Ici α from h), Pi.one_apply,
      abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    ring
  · have hw : wfun t α ⟪u, x⟫ ≤ wfun t α α := wfun_mono ht0 α (not_le.1 h).le
    rw [indicator_of_notMem (show ⟪u, x⟫ ∉ Ici α from h), abs_of_nonneg (by linarith),
      abs_of_nonpos (by linarith)]
    ring

end SharpW

/-- **The defect as a weighted mismatch.** -/
theorem hDefect_eq_weighted {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    (α : ℝ) {F : Gs n → ℝ} (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (hm : gMean F = 1 - Phi α) :
    hDefect t u α F =
      ∫ x, |F x - halfInd u α x| * |wfun t α ⟪u, x⟫ - wfun t α α| ∂gm n := by
  have hH := measurable_halfInd u α
  have hw : Measurable fun x : Gs n ↦ wfun t α ⟪u, x⟫ :=
    (continuous_wfun t α).measurable.comp (by fun_prop)
  have hd : Measurable fun x ↦ halfInd u α x - F x := hH.sub hF
  have hdb : ∀ x, |halfInd u α x - F x| ≤ 1 := fun x ↦ by
    rw [abs_sub_comm]; exact abs_sub_halfInd_le h01 u α x
  have i1 : Integrable (fun x ↦ (halfInd u α x - F x) * wfun t α ⟪u, x⟫) (gm n) :=
    Static.integrable_of_bdd (hd.mul hw) (C := 1) fun x ↦ by
      rw [abs_mul]
      have h1 := (wfun_mem t α ⟪u, x⟫)
      rw [abs_of_nonneg h1.1]
      nlinarith [hdb x, abs_nonneg (halfInd u α x - F x)]
  have i2 : Integrable (fun x ↦ halfInd u α x - F x) (gm n) := Static.integrable_of_bdd hd hdb
  have h0 : ∫ x, (halfInd u α x - F x) ∂gm n = 0 := by
    rw [integral_sub (Static.integrable_of_bdd hH (abs_halfInd_le u α))
      (Static.integrable_of_bdd hF (Static.abs_le_one h01))]
    change gMean (halfInd u α) - gMean F = 0
    rw [gMean_halfInd hu, hm, sub_self]
  rw [hDefect, nBil_halfInd_right (by linarith) ht1 hu]
  simp_rw [← mul_wfun_sub_eq ht0.le u α h01]
  simp_rw [mul_sub]
  rw [integral_sub i1 (i2.mul_const _), integral_mul_const, h0, zero_mul, sub_zero]

/-- **The deficit identity** `Γ_t(E F) - Stab_t(F) = 2 I - Stab_t(F - 𝟙_H)`. -/
theorem gDef_eq_hDefect {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    (α : ℝ) {F : Gs n → ℝ} (hF : Measurable F) (h01 : ∀ x, 0 ≤ F x ∧ F x ≤ 1)
    (hm : gMean F = 1 - Phi α) :
    gDef t F = 2 * hDefect t u α F - gStab t (fun x ↦ F x - halfInd u α x) := by
  have ht : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, ht1.le⟩
  have hH := measurable_halfInd u α
  have hh : Measurable fun x ↦ F x - halfInd u α x := hF.sub hH
  have hexp := nBil_add_self ht hH hh (abs_halfInd_le u α) (abs_sub_halfInd_le h01 u α)
  have e1 : (fun x ↦ halfInd u α x + (F x - halfInd u α x)) = F := by funext x; ring
  rw [e1] at hexp
  have hcomm := nBil_comm ht hH hh (abs_halfInd_le u α) (abs_sub_halfInd_le h01 u α)
  have hneg : hDefect t u α F = -nBil t (fun x ↦ F x - halfInd u α x) (halfInd u α) := by
    unfold hDefect nBil
    rw [← integral_neg]
    congr 1
    funext x
    rw [← integral_neg]
    congr 1
    funext z
    ring
  unfold gDef
  rw [hm, ← gStab_halfInd (by linarith) ht1 hu, gStab_eq_nBil, gStab_eq_nBil, gStab_eq_nBil,
    hexp, hneg, hcomm]
  ring

namespace SharpW

/-- `Φ(b) - Φ(a) ≥ (b - a) min(φ(a), φ(b))` for `a ≤ b`: `φ` is unimodal. -/
theorem Phi_sub_ge {a b : ℝ} (hab : a ≤ b) :
    (b - a) * min (npdf a) (npdf b) ≤ Phi b - Phi a := by
  rw [mul_comm]
  refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv continuous_Phi.continuousOn
    (fun x _ ↦ (hasDerivAt_Phi x).differentiableAt.differentiableWithinAt) (fun x hx ↦ ?_)
    a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  rw [interior_Icc] at hx
  rw [(hasDerivAt_Phi x).deriv]
  rcases le_total 0 x with h | h
  · exact (min_le_right _ _).trans (GammaCalc.npdf_le_npdf (by nlinarith [hx.2]))
  · exact (min_le_left _ _).trans (GammaCalc.npdf_le_npdf (by nlinarith [hx.1]))

/-- `|Φ(b) - Φ(a)| ≥ |b - a| min(φ(a), φ(b))`. -/
theorem abs_Phi_sub_ge (a b : ℝ) : |b - a| * min (npdf a) (npdf b) ≤ |Phi b - Phi a| := by
  rcases le_total a b with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h),
      abs_of_nonneg (sub_nonneg.2 (strictMono_Phi.monotone h))]
    exact Phi_sub_ge h
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h), abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (strictMono_Phi.monotone h)), min_comm]
    exact Phi_sub_ge h

/-- `|w(s) - w(α)| ≥ (t/σ) |s - α| min(φ(a_s), φ(a_α))`, `a_s = (t s - α)/σ`. -/
theorem abs_wfun_sub_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (α s : ℝ) :
    t / √(1 - t ^ 2) * |s - α| *
        min (npdf ((t * α - α) / √(1 - t ^ 2))) (npdf ((t * s - α) / √(1 - t ^ 2))) ≤
      |wfun t α s - wfun t α α| := by
  have hσ := sigma_pos (by linarith) ht1
  have h := abs_Phi_sub_ge ((t * α - α) / √(1 - t ^ 2)) ((t * s - α) / √(1 - t ^ 2))
  have e : |(t * s - α) / √(1 - t ^ 2) - (t * α - α) / √(1 - t ^ 2)| =
      t / √(1 - t ^ 2) * |s - α| := by
    rw [show (t * s - α) / √(1 - t ^ 2) - (t * α - α) / √(1 - t ^ 2) =
        t / √(1 - t ^ 2) * (s - α) by field_simp; ring, abs_mul,
      abs_of_nonneg (div_nonneg ht0 hσ.le)]
  rw [e] at h
  exact h

/-- On `|α| ≤ A`, `|ξ - α| ≤ 1`: `φ((t ξ - α)/σ) ≥ φ((1 + |A|)/σ)`. -/
theorem npdf_ge {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {A α ξ : ℝ} (hα : |α| ≤ A)
    (hξ : |ξ - α| ≤ 1) :
    npdf ((1 + |A|) / √(1 - t ^ 2)) ≤ npdf ((t * ξ - α) / √(1 - t ^ 2)) := by
  have hσ := sigma_pos (by linarith) ht1
  refine GammaCalc.npdf_le_npdf ?_
  rw [div_pow, div_pow]
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  have hA : |α| ≤ |A| := hα.trans (le_abs_self A)
  have h1 : |t * ξ - α| ≤ 1 + |A| := by
    rw [show t * ξ - α = t * (ξ - α) + (t - 1) * α by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonpos (show t - 1 ≤ 0 by linarith)]
    nlinarith [abs_nonneg (ξ - α), abs_nonneg α]
  exact sq_le_sq' (by linarith [neg_abs_le (t * ξ - α)]) (by linarith [le_abs_self (t * ξ - α)])

/-- The slope bound `m(t, A) = (t/σ) φ((1 + |A|)/σ)`. -/
noncomputable def mslope (t A : ℝ) : ℝ := t / √(1 - t ^ 2) * npdf ((1 + |A|) / √(1 - t ^ 2))

theorem mslope_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : ℝ) : 0 < mslope t A :=
  mul_pos (div_pos ht0 (sigma_pos (by linarith) ht1)) (npdf_pos _)

/-- `|w(s) - w(α)| ≥ m ρ` for `ρ ≤ |s - α|`, `0 ≤ ρ ≤ 1`, `|α| ≤ A`. -/
theorem wfun_gap_aux {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A α s ρ : ℝ} (hα : |α| ≤ A)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hs : ρ ≤ |s - α|) :
    mslope t A * ρ ≤ |wfun t α s - wfun t α α| := by
  have hσ := sigma_pos (by linarith) ht1
  have hk : 0 ≤ t / √(1 - t ^ 2) := div_nonneg ht0.le hσ.le
  -- the point at distance `ρ` from `α` on the side of `s`
  have key : ∀ s' : ℝ, |s' - α| = ρ →
      mslope t A * ρ ≤ |wfun t α s' - wfun t α α| := by
    intro s' hs'
    refine le_trans ?_ (abs_wfun_sub_ge ht0.le ht1 α s')
    rw [mslope, hs', mul_right_comm]
    refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) (mul_nonneg hk hρ0)
    · exact npdf_ge ht0.le ht1 hα (by simp)
    · exact npdf_ge ht0.le ht1 hα (by rw [hs']; exact hρ1)
  have hmono := wfun_mono ht0.le α
  rcases le_total α s with h | h
  · rw [abs_of_nonneg (sub_nonneg.2 h)] at hs
    have k := key (α + ρ) (by rw [add_sub_cancel_left, abs_of_nonneg hρ0])
    have h1 : wfun t α α ≤ wfun t α (α + ρ) := hmono (by linarith)
    have h2 : wfun t α (α + ρ) ≤ wfun t α s := hmono (by linarith)
    rw [abs_of_nonneg (by linarith)] at k
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (sub_nonpos.2 h)] at hs
    have k := key (α - ρ) (by rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hρ0])
    have h1 : wfun t α (α - ρ) ≤ wfun t α α := hmono (by linarith)
    have h2 : wfun t α s ≤ wfun t α (α - ρ) := hmono (by linarith)
    rw [abs_of_nonpos (by linarith)] at k
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- `φ(a) = φ(b) exp((b² - a²)/2)`. -/
theorem npdf_ratio (a b : ℝ) : npdf a = npdf b * exp ((b ^ 2 - a ^ 2) / 2) := by
  rw [Normal.npdf_eq, Normal.npdf_eq, mul_assoc, ← exp_add]
  congr 2
  ring

/-- `t K_t(α, α) φ(α) = (t/σ) φ((t α - α)/σ)`: the slope `w'(α)`. -/
theorem mehler_diag {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (α : ℝ) :
    t * mehler t α α * npdf α = t / √(1 - t ^ 2) * npdf ((t * α - α) / √(1 - t ^ 2)) := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hE : (2 * t * α * α - t ^ 2 * (α ^ 2 + α ^ 2)) / (2 * (1 - t ^ 2)) + -α ^ 2 / 2 =
      -((t * α - α) / √(1 - t ^ 2)) ^ 2 / 2 := by
    rw [div_pow, sq_sqrt hq.le]
    field_simp
    ring
  rw [mehler, Normal.npdf_eq, Normal.npdf_eq, ← hE, exp_add]
  ring

/-- `a_s² - a_α² = t e (t e + 2 (t - 1) α)/(1 - t²)`, `e = s - α`, `a_s = (t s - α)/σ`. -/
theorem sq_sub_sq_eq {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (α s : ℝ) :
    ((t * s - α) / √(1 - t ^ 2)) ^ 2 - ((t * α - α) / √(1 - t ^ 2)) ^ 2 =
      t * (s - α) * (t * (s - α) + 2 * (t - 1) * α) / (1 - t ^ 2) := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  rw [div_pow, div_pow, sq_sqrt hq.le]
  field_simp
  ring

end SharpW

/-- **The transport bound** `I ≥ c ‖F - 𝟙_H‖₁²`, uniformly for `|α| ≤ A`. -/
theorem sharp_transport {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : ℝ) :
    ∃ c > 0, ∀ (n : ℕ) (u : Gs n) (α : ℝ), ‖u‖ = 1 → |α| ≤ A →
      ∀ F : Gs n → ℝ, Measurable F → (∀ x, 0 ≤ F x ∧ F x ≤ 1) → gMean F = 1 - Phi α →
        c * (∫ x, |F x - halfInd u α x| ∂gm n) ^ 2 ≤ hDefect t u α F := by
  have hm0 := mslope_pos ht0 ht1 A
  refine ⟨mslope t A / 4, by linarith, ?_⟩
  intro n u α hu hα F hF h01 hm
  rw [hDefect_eq_weighted ht0 ht1 hu α hF h01 hm]
  obtain ⟨ε, hε⟩ : ∃ ε, ε = ∫ x, |F x - halfInd u α x| ∂gm n := ⟨_, rfl⟩
  rw [← hε]
  have hε0 : 0 ≤ ε := hε ▸ integral_nonneg fun _ ↦ abs_nonneg _
  have hε1 : ε ≤ 1 := hε ▸ GaussianLem.integral_abs_sub_halfInd_le F h01 u α
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ε / 2 := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδ]; linarith
  have hmδ : 0 ≤ mslope t A * δ := mul_nonneg hm0.le hδ0
  -- the slab `|⟨u, x⟩ - α| ≤ δ`
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = (Icc (α - δ) (α + δ)).indicator 1 := ⟨_, rfl⟩
  have hgm : Measurable g := hg ▸ measurable_one.indicator measurableSet_Icc
  have hgb : ∀ s, |g s| ≤ 1 := fun s ↦ by
    rw [hg]; by_cases h : s ∈ Icc (α - δ) (α + δ) <;> simp [h]
  have hpt : ∀ x, mslope t A * δ * (|F x - halfInd u α x| - g ⟪u, x⟫) ≤
      |F x - halfInd u α x| * |wfun t α ⟪u, x⟫ - wfun t α α| := by
    intro x
    have hb := abs_sub_halfInd_le h01 u α x
    by_cases hs : ⟪u, x⟫ ∈ Icc (α - δ) (α + δ)
    · rw [hg, indicator_of_mem hs, Pi.one_apply]
      exact (mul_nonpos_of_nonneg_of_nonpos hmδ (by linarith)).trans
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · rw [hg, indicator_of_notMem hs, sub_zero]
      have hfar : δ ≤ |⟪u, x⟫ - α| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hs
        rcases hs with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      calc mslope t A * δ * |F x - halfInd u α x| =
            |F x - halfInd u α x| * (mslope t A * δ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (wfun_gap_aux ht0 ht1 hα hδ0 hδ1 hfar)
            (abs_nonneg _)
  have hdm : Measurable fun x ↦ |F x - halfInd u α x| :=
    continuous_abs.measurable.comp (hF.sub (measurable_halfInd u α))
  have habs : Integrable (fun x ↦ |F x - halfInd u α x|) (gm n) :=
    Static.integrable_of_bdd hdm fun x ↦ by rw [abs_abs]; exact abs_sub_halfInd_le h01 u α x
  have hgi : Integrable (fun x ↦ g ⟪u, x⟫) (gm n) :=
    Static.integrable_of_bdd (hgm.comp (by fun_prop)) fun x ↦ hgb _
  have hw : Measurable fun x : Gs n ↦ wfun t α ⟪u, x⟫ - wfun t α α :=
    ((continuous_wfun t α).measurable.comp (by fun_prop)).sub measurable_const
  have hR : Integrable
      (fun x ↦ |F x - halfInd u α x| * |wfun t α ⟪u, x⟫ - wfun t α α|) (gm n) :=
    Static.integrable_of_bdd (hdm.mul (continuous_abs.measurable.comp hw)) (C := 1) fun x ↦ by
      have h1 := wfun_mem t α ⟪u, x⟫
      have h2 := wfun_mem t α α
      have h3 : |wfun t α ⟪u, x⟫ - wfun t α α| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      rw [abs_mul, abs_abs, abs_abs]
      nlinarith [abs_sub_halfInd_le h01 u α x, abs_nonneg (F x - halfInd u α x),
        abs_nonneg (wfun t α ⟪u, x⟫ - wfun t α α)]
  have hint : ∫ x, mslope t A * δ * (|F x - halfInd u α x| - g ⟪u, x⟫) ∂gm n ≤
      ∫ x, |F x - halfInd u α x| * |wfun t α ⟪u, x⟫ - wfun t α α| ∂gm n :=
    integral_mono ((habs.sub hgi).const_mul (mslope t A * δ)) hR hpt
  rw [integral_const_mul, integral_sub habs hgi, ← hε] at hint
  have hslab : ∫ x, g ⟪u, x⟫ ∂gm n ≤ δ := by
    rw [integral_comp_inner hu hgm, hg, integral_indicator_one measurableSet_Icc]
    refine (gaussianReal_Icc_le (by linarith)).trans ?_
    have := Static1D.inv_sqrt_two_pi_le
    rw [div_eq_mul_inv]
    nlinarith
  calc mslope t A / 4 * ε ^ 2 = mslope t A * δ * (ε - δ) := by rw [hδ]; ring
    _ ≤ mslope t A * δ * (ε - ∫ x, g ⟪u, x⟫ ∂gm n) :=
        mul_le_mul_of_nonneg_left (by linarith) hmδ
    _ ≤ _ := hint

/-- **The slope of `w` near `α`**: `|w(s) - w(α)| ≥ (1 - ε) w'(α) |s - α|` with
`w'(α) = t K_t(α, α) φ(α)`, and `φ(s) ≤ (1 + ε) φ(α)`, for `|s - α| ≤ r`. -/
theorem wfun_strip {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ α s : ℝ, |α| ≤ A → |s - α| ≤ r →
      (1 - ε) * (t * mehler t α α * npdf α) * |s - α| ≤ |wfun t α s - wfun t α α| ∧
        npdf s ≤ (1 + ε) * npdf α := by
  have hq : 0 < 1 - t ^ 2 := by nlinarith
  have hq1 : 1 - t ^ 2 ≤ 1 := by nlinarith
  have hσ := sigma_pos (by linarith) ht1
  obtain ⟨K, hK⟩ : ∃ K, K = 2 * |A| + 1 := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; linarith [abs_nonneg A]
  obtain ⟨η, hη⟩ : ∃ η, η = min ε 1 := ⟨_, rfl⟩
  have hη0 : 0 < η := hη ▸ lt_min hε one_pos
  have hηε : η ≤ ε := hη ▸ min_le_left _ _
  have hη1 : η ≤ 1 := hη ▸ min_le_right _ _
  have hK0 : 0 < K := by linarith
  refine ⟨η * (1 - t ^ 2) / K, by positivity, fun α s hα hs ↦ ?_⟩
  obtain ⟨r, hr⟩ : ∃ r, r = η * (1 - t ^ 2) / K := ⟨_, rfl⟩
  rw [← hr] at hs
  have hrK : r * K = η * (1 - t ^ 2) := by rw [hr]; field_simp
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hηq : η * (1 - t ^ 2) ≤ η := by nlinarith
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hr0 (sub_nonneg.2 hK1)]
  have hA : |α| ≤ |A| := hα.trans (le_abs_self A)
  have he := abs_nonneg (s - α)
  have hbound : |s - α| * (|s - α| + 2 * |α|) ≤ r * K := by
    rw [hK]
    exact mul_le_mul hs (by linarith) (by positivity) hr0
  constructor
  · rw [mehler_diag (by linarith) ht1]
    refine le_trans ?_ (abs_wfun_sub_ge ht0.le ht1 α s)
    have hnum : |t * (s - α) * (t * (s - α) + 2 * (t - 1) * α)| ≤ r * K := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht0.le]
      have h1 : |t * (s - α) + 2 * (t - 1) * α| ≤ |s - α| + 2 * |α| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht0.le, abs_two,
          abs_of_nonpos (show t - 1 ≤ 0 by linarith)]
        nlinarith [abs_nonneg α]
      have h2 : t * |s - α| ≤ |s - α| := by nlinarith
      exact (mul_le_mul h2 h1 (abs_nonneg _) he).trans hbound
    have hle : ((t * s - α) / √(1 - t ^ 2)) ^ 2 - ((t * α - α) / √(1 - t ^ 2)) ^ 2 ≤ η := by
      rw [sq_sub_sq_eq (by linarith) ht1, div_le_iff₀ hq, ← hrK]
      exact (le_abs_self _).trans hnum
    have hexp : 1 - ε ≤ exp ((((t * α - α) / √(1 - t ^ 2)) ^ 2 -
        ((t * s - α) / √(1 - t ^ 2)) ^ 2) / 2) := by
      have := add_one_le_exp ((((t * α - α) / √(1 - t ^ 2)) ^ 2 -
        ((t * s - α) / √(1 - t ^ 2)) ^ 2) / 2)
      linarith
    have hpos := npdf_pos ((t * α - α) / √(1 - t ^ 2))
    have hmin : (1 - ε) * npdf ((t * α - α) / √(1 - t ^ 2)) ≤
        min (npdf ((t * α - α) / √(1 - t ^ 2))) (npdf ((t * s - α) / √(1 - t ^ 2))) := by
      refine le_min (by nlinarith) ?_
      rw [npdf_ratio ((t * s - α) / √(1 - t ^ 2)) ((t * α - α) / √(1 - t ^ 2)), mul_comm]
      exact mul_le_mul_of_nonneg_left hexp hpos.le
    calc (1 - ε) * (t / √(1 - t ^ 2) * npdf ((t * α - α) / √(1 - t ^ 2))) * |s - α| =
          t / √(1 - t ^ 2) * |s - α| * ((1 - ε) * npdf ((t * α - α) / √(1 - t ^ 2))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin (mul_nonneg (div_nonneg ht0.le hσ.le) he)
  · have hy : |(α ^ 2 - s ^ 2) / 2| ≤ η / 2 := by
      rw [show (α ^ 2 - s ^ 2) / 2 = -((s - α) * ((s - α) + 2 * α)) / 2 by ring, abs_div,
        abs_neg, abs_mul, abs_two]
      have h1 : |(s - α) + 2 * α| ≤ |s - α| + 2 * |α| :=
        (abs_add_le _ _).trans (by rw [abs_mul, abs_two])
      have h3 : |s - α| * |(s - α) + 2 * α| ≤ r * K :=
        (mul_le_mul_of_nonneg_left h1 he).trans hbound
      linarith
    have hexp : exp ((α ^ 2 - s ^ 2) / 2) ≤ 1 + ε := by
      have h1 := Real.abs_exp_sub_one_le (x := (α ^ 2 - s ^ 2) / 2) (by linarith)
      have h2 := le_abs_self (exp ((α ^ 2 - s ^ 2) / 2) - 1)
      linarith
    rw [npdf_ratio s α, mul_comm (1 + ε)]
    exact mul_le_mul_of_nonneg_left hexp (npdf_pos α).le

/-- **The gap of `w` away from `α`.** -/
theorem wfun_gap {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (A : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ c > 0, ∀ α s : ℝ, |α| ≤ A → r < |s - α| → c ≤ |wfun t α s - wfun t α α| :=
  ⟨mslope t A * min r 1, mul_pos (mslope_pos ht0 ht1 A) (lt_min hr one_pos),
    fun _ _ hα hs ↦ wfun_gap_aux ht0 ht1 hα (le_min hr.le zero_le_one) (min_le_right _ _)
      ((min_le_left _ _).trans hs.le)⟩

end BGHKLMM26.RobustMIS
