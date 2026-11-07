module

public import BGHKLMM26.RobustMIS.Flow
public import BGHKLMM26.RobustMIS.Ito
public import BGHKLMM26.RobustMIS.GammaCalc
public import BGHKLMM26.RobustMIS.Bessel
public import BGHKLMM26.RobustMIS.DriftAux

/-!
# The deficit identity and Borell's inequality

§6 of `eldan-proof.tex` (new; replaces Eldan's Dambis–Dubins–Schwarz coupling, his Theorem 10
and Lemmas 16, 19, 20, 22): for measurable `f : ℝⁿ → [0, 1]` with mean `m ∈ (0, 1)` and
`t ∈ (0, 1)`,
`Γ_t(m) - Stab_t(f) = ½ ∫₀ᵗ (1-s)⁻¹ E[Γ''_{r(s)}(u(s, √s Z)) e(s, √s Z)] ds`, `r(s) = (t-s)/(1-s)`,
hence (as `Γ''_{r(s)} ≥ 2 κ_{r(s)} ≥ 2 κ_t`) **Borell's inequality with a remainder**
`Δ(f) ≥ κ_t ∫₀ᵗ E e(s, √s Z) ds ≥ 0`.

Proof sketch: `gauss_ito` for `G(s, x) = J(s, u(s, x))`, `J(s, a) = Γ_{r(s)}(a)`, on
`O = (-1, (1+t)/2) × ℝⁿ`; the generator is
`(∂_s + ½Δ) G = J_s + ½ J_aa |∇u|² = -Γ''_{r(s)}(u) e / (2(1-s))` by the backward equations for `u`
(`hasDerivAt_heatU_time`) and `J` (`backward_Gam_path`) and `|∇u|² = |U|²/(1-s)`; the bounds use
`|J_a| ≤ 2`, `q² J_aa ≤ 1/π` (`deriv2_Gam_bounds`), `|∇u|² ≤ q(u)²/(1-s)` (`norm_hermite1_le`),
`‖∇²u‖ ≤ (1-t)⁻¹` (`hs2_le`). Endpoints: `Φ_G(0) = Γ_t(m)`, `Φ_G(t) = E u(t, √t Z)² = Stab_t(f)`
(`gStab_eq_heat`, from (S5): `X = √t W + √(1-t) Z₁`, `Y = √t W + √(1-t) Z₂`; use
`Gaussian.map_add_smul_stdGaussian`).

All statements are proved (from the sorried flow, Itô, `Γ` and static lemmas used as black boxes).
In Lean: `Deficit.integral_rot` (rotation invariance of `γ ⊗ γ`, via
`Gaussian.map_prod_stdGaussian` into `WithLp 2 (ℝⁿ × ℝⁿ)`) and `Deficit.integral_rescale` give
(S5); `Deficit.gen_G` is the generator identity, `Deficit.G_bounds` the bounds for `gauss_ito`
(dimension-dependent bounds `‖∇²u‖ ≤ n²/(1-s)`, `|Δu| ≤ n³/(1-s)` suffice there), and
`Deficit.deficit_aux` the fundamental theorem of calculus (the integrand is `≥ 0`, so it is
integrable by `integrableOn_deriv_of_nonneg`). The calculus toolkit is in `DriftAux.lean`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.Deficit

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped RealInnerProductSpace ContDiff
open BGHKLMM26.RobustMIS.Drift

variable {n : ℕ}

theorem rot_vec {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (z y : Gs n) :
    a • (a • z + b • y) + b • (b • z - a • y) = z := by
  linear_combination (norm := module) hab • z

theorem rot_vec' {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (z y : Gs n) :
    b • (a • z + b • y) - a • (b • z - a • y) = y := by
  linear_combination (norm := module) hab • y

/-- Rotation invariance of `γ ⊗ γ`: `(Z, Y) ↦ (a Z + b Y, b Z - a Y)` for `a² + b² = 1`. -/
theorem integral_rot (F : Gs n × Gs n → ℝ) (hF : Measurable F) {C : ℝ} (hC : ∀ p, |F p| ≤ C)
    {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ z, ∫ y, F (z, y) ∂gm n ∂gm n =
      ∫ x, ∫ w, F (a • x + b • w, b • x - a • w) ∂gm n ∂gm n := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ (Gs n) (Gs n)).symm.toContinuousLinearMap
  let A : Gs n →L[ℝ] (WithLp 2 (Gs n × Gs n)) := e ∘L ((a • ContinuousLinearMap.id ℝ (Gs n)).prod
    (b • ContinuousLinearMap.id ℝ (Gs n)))
  let B : Gs n →L[ℝ] (WithLp 2 (Gs n × Gs n)) := e ∘L ((b • ContinuousLinearMap.id ℝ (Gs n)).prod
    ((-a) • ContinuousLinearMap.id ℝ (Gs n)))
  let A' : WithLp 2 (Gs n × Gs n) → Gs n := fun τ ↦ a • (WithLp.ofLp τ).1 + b • (WithLp.ofLp τ).2
  let B' : WithLp 2 (Gs n × Gs n) → Gs n := fun τ ↦ b • (WithLp.ofLp τ).1 - a • (WithLp.ofLp τ).2
  have hA : ∀ x τ, ⟪A x, τ⟫ = ⟪x, A' τ⟫ := by
    intro x τ
    simp only [A, A', e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.prod_inner_apply]
    simp [inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hB : ∀ x τ, ⟪B x, τ⟫ = ⟪x, B' τ⟫ := by
    intro x τ
    simp only [B, B', e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.prod_inner_apply]
    simp [inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hn : ∀ τ, ‖A' τ‖ ^ 2 + ‖B' τ‖ ^ 2 = ‖τ‖ ^ 2 := by
    intro τ
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [A', B']
    rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
    simp only [WithLp.fst, WithLp.snd]
    linear_combination (‖(WithLp.ofLp τ).1‖ ^ 2 + ‖(WithLp.ofLp τ).2‖ ^ 2) * hab
  have hmap := Gaussian.map_prod_stdGaussian A B A' B' hA hB hn
  have hAB : (fun p : Gs n × Gs n ↦ A p.1 + B p.2) =
      fun p ↦ WithLp.toLp 2 (a • p.1 + b • p.2, b • p.1 - a • p.2) := by
    funext p
    simp only [A, B, e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply]
    rw [← WithLp.toLp_add, Prod.mk_add_mk]
    simp [sub_eq_add_neg]
  rw [hAB] at hmap
  let φ : WithLp 2 (Gs n × Gs n) → ℝ := fun q ↦ F (a • (WithLp.ofLp q).1 + b • (WithLp.ofLp q).2,
    b • (WithLp.ofLp q).1 - a • (WithLp.ofLp q).2)
  have hφm : Measurable φ := by
    refine hF.comp ?_
    have : Continuous fun q : WithLp 2 (Gs n × Gs n) ↦
        (a • (WithLp.ofLp q).1 + b • (WithLp.ofLp q).2,
          b • (WithLp.ofLp q).1 - a • (WithLp.ofLp q).2) := by
      have h1 : Continuous fun q : WithLp 2 (Gs n × Gs n) ↦ WithLp.ofLp q :=
        WithLp.prod_continuous_ofLp 2 _ _
      fun_prop
    exact this.measurable
  have hφ : Integrable φ (stdGaussian (WithLp 2 (Gs n × Gs n))) :=
    Gaussian.integrable_of_abs_le hφm (fun q ↦ hC _)
  have hL : Measurable fun p : Gs n × Gs n ↦
      WithLp.toLp 2 (a • p.1 + b • p.2, b • p.1 - a • p.2) := by
    have : Continuous fun p : Gs n × Gs n ↦
        WithLp.toLp 2 (a • p.1 + b • p.2, b • p.1 - a • p.2) :=
      (WithLp.prod_continuous_toLp 2 _ _).comp (by fun_prop)
    exact this.measurable
  have h1 := Gaussian.integral_eq_of_map_prod hL hmap hφ
  have h2 := Gaussian.integral_stdGaussian_prod hφ
  rw [h1] at h2
  convert h2 using 3 with z y
  simp only [φ, rot_vec hab, rot_vec' hab]


/-- `E g(c Z) = E g(c₁ Z + c₂ Z')` for `c₁² + c₂² = c²`. -/
theorem integral_rescale (g : Gs n → ℝ) (hg : Measurable g) {C : ℝ} (hC : ∀ v, |g v| ≤ C)
    {c₁ c₂ c : ℝ} (hc : 0 < c) (h : c₁ ^ 2 + c₂ ^ 2 = c ^ 2) :
    ∫ v, g (c • v) ∂gm n = ∫ w, ∫ y, g (c₁ • w + c₂ • y) ∂gm n ∂gm n := by
  have hrs : (c₁ / c) ^ 2 + (c₂ / c) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, h, div_self (by positivity)]
  have hmap := Gaussian.map_add_smul_stdGaussian (E := Gs n) hrs
  have hφm : Measurable fun v : Gs n ↦ g (c • v) := hg.comp (continuous_const_smul c).measurable
  have hφ : Integrable (fun v ↦ g (c • v)) (gm n) :=
    Gaussian.integrable_of_abs_le hφm (fun v ↦ hC _)
  rw [Gaussian.integral_eq_of_map_prod (by fun_prop) hmap hφ]
  congr 1
  funext w
  congr 1
  funext y
  simp only
  rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hc.ne', mul_div_cancel₀ _ hc.ne']

/-- (S5): `Stab_t(f) = E[u(t, √t Z)²]`. -/
theorem gStab_eq_heat' {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gStab t f = ∫ z, heatU f t (√t • z) ^ 2 ∂gm n := by
  obtain ⟨a, rfl⟩ : ∃ a, a = √t := ⟨_, rfl⟩
  have ha2 : √t ^ 2 = t := sq_sqrt ht.1.le
  have hb2 : √(1 - t) ^ 2 = 1 - t := sq_sqrt (by linarith [ht.2])
  have hab : √t ^ 2 + √(1 - t) ^ 2 = 1 := by rw [ha2, hb2]; ring
  have hcont : Continuous (heatU f t) := (contDiff_heatU hf h01 ht.2).continuous
  have hu01 : ∀ x, 0 ≤ heatU f t x ∧ heatU f t x ≤ 1 := fun x ↦
    gMean_mem (flowFun f t x) (flowFun_mem f h01 t x)
  -- the common value `E[f(X) E[f(t X + √(1-t²) Z) | X]]`
  have hc : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith [ht.1, ht.2])
  have hc2 : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := sq_sqrt (by nlinarith [ht.1, ht.2])
  have key : ∀ x, ∫ w, heatU f t (√t • (√t • x + √(1 - t) • w)) ∂gm n =
      ∫ v, f (t • x + √(1 - t ^ 2) • v) ∂gm n := by
    intro x
    have hg : Measurable fun v : Gs n ↦ f (t • x + v) := hf.comp (by fun_prop)
    rw [integral_rescale (fun v ↦ f (t • x + v)) hg (C := 1)
      (fun v ↦ by rw [abs_of_nonneg (h01 _).1]; exact (h01 _).2) (c₁ := √t * √(1 - t))
      (c₂ := √(1 - t)) hc (by rw [mul_pow, ha2, hb2, hc2]; ring)]
    congr 1
    funext w
    simp only [heatU, gMean, flowFun]
    congr 1
    funext y
    congr 1
    rw [smul_add, smul_smul, ← sq, ha2, add_assoc, mul_smul]
  -- the left side
  have hL : gStab t f = ∫ x, f x * ∫ v, f (t • x + √(1 - t ^ 2) • v) ∂gm n ∂gm n := by
    unfold gStab
    congr 1
    funext x
    rw [integral_const_mul]
  -- the right side
  let F : Gs n × Gs n → ℝ := fun p ↦ f (√t • p.1 + √(1 - t) • p.2) * heatU f t (√t • p.1)
  have hFm : Measurable F := by
    refine (hf.comp (by fun_prop)).mul ((hcont.comp (by fun_prop)).measurable)
  have hFb : ∀ p, |F p| ≤ 1 := by
    intro p
    simp only [F, abs_mul]
    rw [abs_of_nonneg (h01 _).1, abs_of_nonneg (hu01 _).1]
    nlinarith [(h01 (√t • p.1 + √(1 - t) • p.2)).1, (h01 (√t • p.1 + √(1 - t) • p.2)).2,
      (hu01 (√t • p.1)).1, (hu01 (√t • p.1)).2]
  have hR1 : ∫ z, heatU f t (√t • z) ^ 2 ∂gm n = ∫ z, ∫ y, F (z, y) ∂gm n ∂gm n := by
    congr 1
    funext z
    simp only [F]
    rw [integral_mul_const, sq]
    rfl
  rw [hL, hR1, integral_rot F hFm hFb hab]
  congr 1
  funext x
  simp only [F]
  simp_rw [rot_vec hab]
  rw [← key x, integral_const_mul]



/-- The chain rule for `r ↦ J(r, g(r))` from the partial derivatives of a differentiable `J`. -/
theorem hasDerivAt_comp_prod {J : ℝ × ℝ → ℝ} {s a Js Ja g' : ℝ} {g : ℝ → ℝ}
    (hJ : DifferentiableAt ℝ J (s, a))
    (hs : HasDerivAt (fun r ↦ J (r, a)) Js s) (ha : HasDerivAt (fun b ↦ J (s, b)) Ja a)
    (hg : HasDerivAt g g' s) (hgs : g s = a) :
    HasDerivAt (fun r ↦ J (r, g r)) (Js + Ja * g') s := by
  have hL := hJ.hasFDerivAt
  set L := fderiv ℝ J (s, a)
  have e1 : L (1, 0) = Js := by
    have h := hL.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s a))
    exact h.unique hs
  have e2 : L (0, 1) = Ja := by
    have h := hL.comp_hasDerivAt a ((hasDerivAt_const a s).prodMk (hasDerivAt_id a))
    exact h.unique ha
  have h1 : HasDerivAt (fun r ↦ (r, g r)) ((1 : ℝ), g') s := (hasDerivAt_id s).prodMk hg
  rw [← hgs] at hL
  have h2 := hL.comp_hasDerivAt s h1
  have e3 : L (1, g') = L (1, 0) + g' * L (0, 1) := by
    have : ((1 : ℝ), g') = (1, 0) + g' • ((0 : ℝ), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  rw [e3, e1, e2, mul_comm] at h2
  exact h2

/-- `J(s, a) = Γ_{r(s)}(a)`, `r(s) = (t - s)/(1 - s)`. -/
noncomputable def Jt (t : ℝ) (p : ℝ × ℝ) : ℝ := Gam ((t - p.1) / (1 - p.1)) p.2

theorem rpath_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t) :
    (t - s) / (1 - s) ∈ Ioo (-1 : ℝ) 1 := by
  have h := Gam_path_mem ht hs
  exact ⟨by linarith [h.1], by linarith [h.2, ht.2]⟩

theorem rpath_mem' {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t) :
    (t - s) / (1 - s) ∈ Ico (0 : ℝ) 1 := by
  have h := Gam_path_mem ht hs
  exact ⟨h.1, by linarith [h.2, ht.2]⟩

section

variable {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
  (hm : gMean f ∈ Ioo (0 : ℝ) 1)
include hf h01 hm

theorem hasDerivAt_G_time {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t)
    (x : Gs n) :
    HasDerivAt (fun r ↦ Gam ((t - r) / (1 - r)) (heatU f r x))
      (-(qf (heatU f s x) ^ 2 * deriv (deriv (Gam ((t - s) / (1 - s)))) (heatU f s x) /
          (2 * (1 - s))) +
        deriv (Gam ((t - s) / (1 - s))) (heatU f s x) *
          (-(1 / 2) * Laplacian.laplacian (heatU f s) x)) s := by
  have hs1 : s < 1 := by linarith [hs.2, ht.2]
  have hs2 : s < (1 + t) / 2 := by linarith [hs.2, ht.2]
  have hu := heatU_mem f hf h01 hm hs1 x
  have hr := rpath_mem ht hs
  have hJ : DifferentiableAt ℝ (Jt t) (s, heatU f s x) := by
    have hc := contDiffOn_Gam_path ht
    have hmem : Iio ((1 + t) / 2) ×ˢ Ioo (0 : ℝ) 1 ∈ 𝓝 (s, heatU f s x) :=
      (isOpen_Iio.prod isOpen_Ioo).mem_nhds ⟨hs2, hu⟩
    exact ((hc.contDiffAt hmem).differentiableAt (by norm_num))
  have hJs := backward_Gam_path ht hs2 hu
  have hJa : HasDerivAt (fun b ↦ Jt t (s, b)) (deriv (Gam ((t - s) / (1 - s))) (heatU f s x))
      (heatU f s x) := (hasDerivAt_Gam hr hu).differentiableAt.hasDerivAt
  exact hasDerivAt_comp_prod hJ hJs hJa (hasDerivAt_heatU_time f hf h01 hs1 x) rfl

theorem eventually_hasDerivAt_Gam {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {s : ℝ} (hs : s < 1)
    (x : Gs n) :
    ∀ᶠ a in 𝓝 (heatU f s x), HasDerivAt (Gam r) (deriv (Gam r) a) a := by
  have hu := heatU_mem f hf h01 hm hs x
  filter_upwards [isOpen_Ioo.mem_nhds hu] with a ha
  exact (hasDerivAt_Gam hr ha).differentiableAt.hasDerivAt

theorem laplacian_G {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {s : ℝ} (hs : s < 1) (x : Gs n) :
    Laplacian.laplacian (fun y ↦ Gam r (heatU f s y)) x =
      deriv (deriv (Gam r)) (heatU f s x) * (‖hermite1 (flowFun f s x)‖ ^ 2 / (1 - s)) +
        deriv (Gam r) (heatU f s x) * Laplacian.laplacian (heatU f s) x := by
  have hu := heatU_mem f hf h01 hm hs x
  rw [laplacian_comp (EuclideanSpace.basisFun (Fin n) ℝ) (contDiffAt_heatU hf h01 hs x)
    (eventually_hasDerivAt_Gam hf h01 hm hr hs x)
    (hasDerivAt_deriv_Gam hr hu).differentiableAt.hasDerivAt,
    sum_sq_fderiv_heatU hf h01 hs x]

/-- The generator of `G = J(s, u)`: `(∂_s + ½Δ) G = -Γ''_{r(s)}(u) e / (2(1-s))`. -/
theorem gen_G {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t) (x : Gs n) :
    deriv (fun r ↦ Gam ((t - r) / (1 - r)) (heatU f r x)) s +
        1 / 2 * Laplacian.laplacian (fun y ↦ Gam ((t - s) / (1 - s)) (heatU f s y)) x =
      -(1 / 2) * ((1 - s)⁻¹ * (deriv (deriv (Gam ((t - s) / (1 - s)))) (heatU f s x) *
        eFlow f s x)) := by
  have hs1 : s < 1 := by linarith [hs.2, ht.2]
  have h1 : (1 - s) ≠ 0 := by linarith
  rw [(hasDerivAt_G_time hf h01 hm ht hs x).deriv,
    laplacian_G hf h01 hm (rpath_mem ht hs) hs1 x]
  simp only [eFlow, epsF]
  change _ = -(1 / 2) * ((1 - s)⁻¹ * (deriv (deriv (Gam ((t - s) / (1 - s)))) (heatU f s x) *
        (qf (heatU f s x) ^ 2 - ‖hermite1 (flowFun f s x)‖ ^ 2)))
  field_simp
  ring


theorem deriv_Gam_mem {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {s : ℝ} (hs : s < 1) (x : Gs n) :
    0 < deriv (Gam r) (heatU f s x) ∧ deriv (Gam r) (heatU f s x) < 2 := by
  have hu := heatU_mem f hf h01 hm hs x
  rw [(hasDerivAt_Gam hr hu).deriv]
  exact ⟨by linarith [Gaussian.Phi_pos (kap r * Psi (heatU f s x))],
    by linarith [Gaussian.Phi_lt_one (kap r * Psi (heatU f s x))]⟩

theorem fderiv_G {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {s : ℝ} (hs : s < 1) (x : Gs n) :
    fderiv ℝ (fun y ↦ Gam r (heatU f s y)) x =
      deriv (Gam r) (heatU f s x) • fderiv ℝ (heatU f s) x :=
  fderiv_comp_apply (contDiffAt_heatU hf h01 hs x) (eventually_hasDerivAt_Gam hf h01 hm hr hs x)

theorem norm_iteratedFDeriv_G_le {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {s : ℝ} (hs : s < 1)
    (x : Gs n) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ Gam r (heatU f s y)) x‖ ≤
      |deriv (deriv (Gam r)) (heatU f s x)| * ‖fderiv ℝ (heatU f s) x‖ ^ 2 +
        |deriv (Gam r) (heatU f s x)| * ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ := by
  have hu := heatU_mem f hf h01 hm hs x
  exact norm_iteratedFDeriv_two_comp_le (contDiffAt_heatU hf h01 hs x)
    (eventually_hasDerivAt_Gam hf h01 hm hr hs x)
    (hasDerivAt_deriv_Gam hr hu).differentiableAt.hasDerivAt

theorem G_bounds {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ M, ∀ s ∈ Icc 0 t, ∀ x,
      |Gam ((t - s) / (1 - s)) (heatU f s x)| ≤ M ∧
      |deriv (fun r ↦ Gam ((t - r) / (1 - r)) (heatU f r x)) s| ≤ M ∧
      ‖fderiv ℝ (fun y ↦ Gam ((t - s) / (1 - s)) (heatU f s y)) x‖ ≤ M ∧
      ‖iteratedFDeriv ℝ 2 (fun y ↦ Gam ((t - s) / (1 - s)) (heatU f s y)) x‖ ≤ M := by
  set K := 1 / (1 - t)
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have hK : 0 ≤ K := by positivity
  refine ⟨1 + (K + n ^ 3 * K) + 2 * (1 + K) + (K + 2 * (n ^ 2 * K)), fun s hs x ↦ ?_⟩
  have hs1 : s < 1 := by linarith [hs.2, ht.2]
  have hs0 : 0 < 1 - s := by linarith
  have hsK : 1 / (1 - s) ≤ K := one_div_le_one_div_of_le ht1 (by linarith [hs.2])
  set r := (t - s) / (1 - s)
  have hr := rpath_mem ht hs
  have hr' := rpath_mem' ht hs
  have hu := heatU_mem f hf h01 hm hs1 x
  have hJa := deriv_Gam_mem hf h01 hm hr hs1 x
  obtain ⟨hJ1, hJ2, hJ3⟩ := deriv2_Gam_bounds hr' hu
  have hkap : kap r ≤ 1 := kap_le_one hr'.1
  have hJaa0 : 0 ≤ deriv (deriv (Gam r)) (heatU f s x) := by
    have : 0 ≤ kap r := Real.sqrt_nonneg _
    linarith
  have hqJ : qf (heatU f s x) ^ 2 * deriv (deriv (Gam r)) (heatU f s x) ≤ 1 := by
    refine hJ3.trans ?_
    rw [div_le_one pi_pos]
    linarith [pi_gt_three]
  have hDu2 : ‖fderiv ℝ (heatU f s) x‖ ^ 2 ≤ K :=
    (sq_norm_fderiv_heatU_le' hf h01 hs1 x).trans hsK
  have hDu : ‖fderiv ℝ (heatU f s) x‖ ≤ 1 + K := by
    nlinarith [norm_nonneg (fderiv ℝ (heatU f s) x)]
  have hD2u : ‖iteratedFDeriv ℝ 2 (heatU f s) x‖ ≤ n ^ 2 * K := by
    refine (norm_iteratedFDeriv_two_heatU_le hf h01 hs1 x).trans ?_
    rw [div_eq_mul_one_div]
    gcongr
  have hLu : |Laplacian.laplacian (heatU f s) x| ≤ n ^ 3 * K := by
    refine (abs_laplacian_heatU_le hf h01 hs1 x).trans ?_
    rw [div_eq_mul_one_div]
    gcongr
  have hn2 : (0 : ℝ) ≤ n ^ 2 * K := by positivity
  have hn3 : (0 : ℝ) ≤ n ^ 3 * K := by positivity
  have b1 : |Gam r (heatU f s x)| ≤ 1 := by
    rw [abs_of_nonneg (Gam_nonneg _ _)]
    exact (Gam_le_self ⟨hr.1.le, hr.2.le⟩ hu.1.le).trans hu.2.le
  have b2 : |deriv (fun r ↦ Gam ((t - r) / (1 - r)) (heatU f r x)) s| ≤ K + n ^ 3 * K := by
    rw [(hasDerivAt_G_time hf h01 hm ht hs x).deriv]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_neg, abs_div, abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
      calc qf (heatU f s x) ^ 2 * deriv (deriv (Gam r)) (heatU f s x) / (2 * (1 - s))
          ≤ 1 / (2 * (1 - s)) := by gcongr
        _ ≤ 1 / (1 - s) := by gcongr; linarith
        _ ≤ K := hsK
    · rw [abs_mul, abs_mul, abs_neg, abs_of_pos hJa.1, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc deriv (Gam r) (heatU f s x) * (1 / 2 * |Laplacian.laplacian (heatU f s) x|)
          ≤ 2 * (1 / 2 * (n ^ 3 * K)) := by
            gcongr
            exact hJa.2.le
        _ = n ^ 3 * K := by ring
  have b3 : ‖fderiv ℝ (fun y ↦ Gam r (heatU f s y)) x‖ ≤ 2 * (1 + K) := by
    rw [fderiv_G hf h01 hm hr hs1 x, norm_smul, Real.norm_eq_abs, abs_of_pos hJa.1]
    gcongr
    exact hJa.2.le
  have b4 : ‖iteratedFDeriv ℝ 2 (fun y ↦ Gam r (heatU f s y)) x‖ ≤ K + 2 * (n ^ 2 * K) := by
    refine (norm_iteratedFDeriv_G_le hf h01 hm hr hs1 x).trans (add_le_add ?_ ?_)
    · rw [abs_of_nonneg hJaa0]
      calc deriv (deriv (Gam r)) (heatU f s x) * ‖fderiv ℝ (heatU f s) x‖ ^ 2
          ≤ deriv (deriv (Gam r)) (heatU f s x) * (qf (heatU f s x) ^ 2 / (1 - s)) := by
            gcongr
            exact sq_norm_fderiv_heatU_le hf h01 hs1 x
        _ = qf (heatU f s x) ^ 2 * deriv (deriv (Gam r)) (heatU f s x) * (1 / (1 - s)) := by
            ring
        _ ≤ 1 * K := by gcongr
        _ = K := one_mul K
    · rw [abs_of_pos hJa.1]
      gcongr
      exact hJa.2.le
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith


theorem contDiffOn_G {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ Gam ((t - p.1) / (1 - p.1)) (heatU f p.1 p.2))
      {p | p.1 < (1 + t) / 2} := by
  have hU := (contDiffOn_heatU f hf h01).of_le two_le_infty
  have hsub : {p : ℝ × Gs n | p.1 < (1 + t) / 2} ⊆ {p | p.1 < 1} := by
    intro p hp
    simp only [mem_ofPred_eq] at hp ⊢
    linarith [ht.2]
  have hin : ContDiffOn ℝ 2 (fun p : ℝ × Gs n ↦ (p.1, heatU f p.1 p.2))
      {p | p.1 < (1 + t) / 2} := contDiffOn_fst.prodMk (hU.mono hsub)
  have hmaps : MapsTo (fun p : ℝ × Gs n ↦ (p.1, heatU f p.1 p.2)) {p | p.1 < (1 + t) / 2}
      (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) := by
    intro p hp
    simp only [mem_ofPred_eq] at hp
    exact ⟨hp, heatU_mem f hf h01 hm (by linarith [ht.2]) p.2⟩
  have h := (contDiffOn_Gam_path ht).comp hin hmaps
  exact h

/-- The integrand of the deficit identity. -/
noncomputable def defInt (f : Gs n → ℝ) (t s : ℝ) : ℝ :=
  (1 - s)⁻¹ * ∫ z, deriv (deriv (Gam ((t - s) / (1 - s)))) (heatU f s (√s • z)) *
    eFlow f s (√s • z) ∂gm n

theorem defInt_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t) :
    0 ≤ defInt f t s := by
  have hs1 : s < 1 := by linarith [hs.2, ht.2]
  have hs0 : 0 < 1 - s := by linarith
  unfold defInt
  refine mul_nonneg (inv_nonneg.2 hs0.le) (integral_nonneg fun z ↦ mul_nonneg ?_ ?_)
  · have hu := heatU_mem f hf h01 hm hs1 (√s • z)
    have h := (deriv2_Gam_bounds (rpath_mem' ht hs) hu).1
    have : 0 ≤ kap ((t - s) / (1 - s)) := Real.sqrt_nonneg _
    linarith
  · exact epsF_nonneg _ (measurable_flowFun f hf s _) (flowFun_mem f h01 s _)

theorem deficit_aux {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (defInt f t) volume 0 t ∧
      Gam t (gMean f) - ∫ z, Gam 0 (heatU f t (√t • z)) ∂gm n =
        1 / 2 * ∫ s in (0 : ℝ)..t, defInt f t s := by
  set Φ := fun s ↦ ∫ z, Gam ((t - s) / (1 - s)) (heatU f s (√s • z)) ∂gm n
  have hO : IsOpen {p : ℝ × Gs n | p.1 < (1 + t) / 2} := isOpen_lt continuous_fst continuous_const
  have hsub : Icc 0 t ×ˢ (univ : Set (Gs n)) ⊆ {p : ℝ × Gs n | p.1 < (1 + t) / 2} := by
    intro p hp
    simp only [mem_prod, mem_Icc] at hp
    simp only [mem_ofPred_eq]
    linarith [hp.1.2, ht.2]
  obtain ⟨hcont, hderiv⟩ := gauss_ito le_rfl ht.1
    (fun s x ↦ Gam ((t - s) / (1 - s)) (heatU f s x)) hO hsub (contDiffOn_G hf h01 hm ht)
    (G_bounds hf h01 hm ht)
  have hderiv' : ∀ s ∈ Ioo 0 t, HasDerivAt (fun s ↦ -Φ s) (1 / 2 * defInt f t s) s := by
    intro s hs
    have h := (hderiv s hs).neg
    convert h using 1
    rw [← integral_neg]
    have e : ∀ z : Gs n, -(deriv (fun r ↦ Gam ((t - r) / (1 - r)) (heatU f r (√s • z))) s +
        1 / 2 * Laplacian.laplacian (fun y ↦ Gam ((t - s) / (1 - s)) (heatU f s y)) (√s • z)) =
        1 / 2 * ((1 - s)⁻¹ * (deriv (deriv (Gam ((t - s) / (1 - s)))) (heatU f s (√s • z)) *
          eFlow f s (√s • z))) := by
      intro z
      rw [gen_G hf h01 hm ht (Ioo_subset_Icc_self hs)]
      ring
    simp_rw [e]
    rw [integral_const_mul, integral_const_mul]
    rfl
  have hnn : ∀ s ∈ Ioo 0 t, 0 ≤ 1 / 2 * defInt f t s := fun s hs ↦
    mul_nonneg (by norm_num) (defInt_nonneg hf h01 hm ht (Ioo_subset_Icc_self hs))
  have hint := intervalIntegral.integrableOn_deriv_of_nonneg hcont.neg hderiv' hnn
  have hint' : IntervalIntegrable (fun s ↦ 1 / 2 * defInt f t s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).2 hint
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1.le hcont.neg hderiv'
    hint'
  refine ⟨?_, ?_⟩
  · have := hint'.const_mul 2
    convert this using 1
    funext s
    ring
  · rw [← intervalIntegral.integral_const_mul, hftc]
    have h0 : Φ 0 = Gam t (gMean f) := by
      simp [Φ, heatU_zero_zero]
    have ht' : Φ t = ∫ z, Gam 0 (heatU f t (√t • z)) ∂gm n := by
      change ∫ z, Gam ((t - t) / (1 - t)) (heatU f t (√t • z)) ∂gm n = _
      rw [sub_self, zero_div]
    change _ = -Φ t - -Φ 0
    rw [h0, ht']
    ring

end


theorem yFlow_le_defInt {f : Gs n → ℝ} (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hm : gMean f ∈ Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc 0 t) :
    kap t * yFlow f s ≤ 1 / 2 * defInt f t s := by
  have hs1 : s < 1 := by linarith [hs.2, ht.2]
  have hs0 : 0 < 1 - s := by linarith
  set r := (t - s) / (1 - s)
  have hr := rpath_mem ht hs
  have hr' := rpath_mem' ht hs
  have hkt : kap t ≤ kap r := antitoneOn_kap hr ⟨by linarith [ht.1], ht.2⟩ (Gam_path_mem ht hs).2
  have hk0 : 0 ≤ kap t := Real.sqrt_nonneg _
  have hce := continuous_eFlow hf h01 hm hs1
  have hcu := (contDiff_heatU hf h01 hs1).continuous
  have hem : Measurable fun z : Gs n ↦ eFlow f s (√s • z) :=
    (hce.comp (continuous_const_smul _)).measurable
  have hJm : Measurable fun z : Gs n ↦ deriv (deriv (Gam r)) (heatU f s (√s • z)) :=
    (measurable_deriv _).comp (hcu.comp (continuous_const_smul _)).measurable
  have hJb : ∀ z : Gs n, 0 ≤ deriv (deriv (Gam r)) (heatU f s (√s • z)) ∧
      deriv (deriv (Gam r)) (heatU f s (√s • z)) * eFlow f s (√s • z) ≤ 1 ∧
      2 * kap t ≤ deriv (deriv (Gam r)) (heatU f s (√s • z)) := by
    intro z
    have hu := heatU_mem f hf h01 hm hs1 (√s • z)
    obtain ⟨hJ1, hJ2, hJ3⟩ := deriv2_Gam_bounds hr' hu
    have hkap : kap r ≤ 1 := kap_le_one hr'.1
    have h0 : 0 ≤ deriv (deriv (Gam r)) (heatU f s (√s • z)) := by linarith
    refine ⟨h0, ?_, by linarith⟩
    calc deriv (deriv (Gam r)) (heatU f s (√s • z)) * eFlow f s (√s • z)
        ≤ deriv (deriv (Gam r)) (heatU f s (√s • z)) * qf (heatU f s (√s • z)) ^ 2 := by
          gcongr
          exact eFlow_le h01 s _
      _ = qf (heatU f s (√s • z)) ^ 2 * deriv (deriv (Gam r)) (heatU f s (√s • z)) := by ring
      _ ≤ kap r / π := hJ3
      _ ≤ 1 := by rw [div_le_one pi_pos]; linarith [pi_gt_three]
  have hint1 : Integrable (fun z : Gs n ↦ kap t * eFlow f s (√s • z)) (gm n) := by
    refine Gaussian.integrable_of_abs_le (hem.const_mul _) (C := kap t * 1) fun z ↦ ?_
    rw [abs_mul, abs_of_nonneg hk0, abs_of_nonneg (eFlow_nonneg hf h01 _ _)]
    gcongr
    refine (eFlow_le h01 s _).trans ((qf_sq_le _).trans ?_)
    rw [div_le_one (by positivity)]
    linarith [pi_gt_three]
  have hint2 : Integrable (fun z : Gs n ↦ 1 / 2 * ((1 - s)⁻¹ *
      (deriv (deriv (Gam r)) (heatU f s (√s • z)) * eFlow f s (√s • z)))) (gm n) := by
    refine Gaussian.integrable_of_abs_le ((hJm.mul hem).const_mul _ |>.const_mul _)
      (C := 1 / 2 * ((1 - s)⁻¹ * 1)) fun z ↦ ?_
    have h1 := hJb z
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      abs_of_pos (inv_pos.2 hs0), abs_of_nonneg (mul_nonneg h1.1 (eFlow_nonneg hf h01 _ _))]
    gcongr
    exact h1.2.1
  have e1 : kap t * yFlow f s = ∫ z, kap t * eFlow f s (√s • z) ∂gm n := by
    rw [yFlow, integral_const_mul]
  have e2 : 1 / 2 * defInt f t s = ∫ z, 1 / 2 * ((1 - s)⁻¹ *
      (deriv (deriv (Gam r)) (heatU f s (√s • z)) * eFlow f s (√s • z))) ∂gm n := by
    rw [defInt, integral_const_mul, integral_const_mul]
  rw [e1, e2]
  refine integral_mono hint1 hint2 fun z ↦ ?_
  obtain ⟨hJ0, -, hJ2⟩ := hJb z
  have he := eFlow_nonneg hf h01 s (√s • z)
  have hinv : 1 ≤ (1 - s)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hs0, inv_one]
    linarith [hs.1]
  calc kap t * eFlow f s (√s • z)
      = 1 / 2 * (1 * ((2 * kap t) * eFlow f s (√s • z))) := by ring
    _ ≤ 1 / 2 * ((1 - s)⁻¹ * (deriv (deriv (Gam r)) (heatU f s (√s • z)) *
        eFlow f s (√s • z))) := by
      gcongr

end BGHKLMM26.RobustMIS.Deficit

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- (S5): `Stab_t(f) = E[u(t, √t Z)²]`. -/
theorem gStab_eq_heat {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    gStab t f = ∫ z, heatU f t (√t • z) ^ 2 ∂gm n :=
  Deficit.gStab_eq_heat' ht f hf h01

/-- **The deficit identity** (Proposition 6.1). -/
theorem deficit_identity {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hm : gMean f ∈ Ioo (0 : ℝ) 1) :
    gDef t f = 1 / 2 * ∫ s in (0 : ℝ)..t, (1 - s)⁻¹ *
      ∫ z, deriv (deriv (Gam ((t - s) / (1 - s)))) (heatU f s (√s • z)) *
        eFlow f s (√s • z) ∂gm n := by
  have h := (Deficit.deficit_aux hf h01 hm ht).2
  have e : ∫ z, Gam 0 (heatU f t (√t • z)) ∂gm n = gStab t f := by
    rw [gStab_eq_heat ht f hf h01]
    congr 1
    funext z
    exact Gam_zero_corr (gMean_mem _ (flowFun_mem f h01 t _))
  rw [e] at h
  exact h

/-- **Borell's inequality with a remainder** (Corollary 6.2, Theorem A(a)):
`Δ(f) ≥ κ_t ∫₀ᵗ E e(s, √s Z) ds`. -/
theorem borell_remainder {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hm : gMean f ∈ Ioo (0 : ℝ) 1) :
    kap t * ∫ s in (0 : ℝ)..t, yFlow f s ≤ gDef t f := by
  obtain ⟨hint, -⟩ := Deficit.deficit_aux hf h01 hm ht
  have hdef : gDef t f = 1 / 2 * ∫ s in (0 : ℝ)..t, Deficit.defInt f t s :=
    deficit_identity ht f hf h01 hm
  rw [hdef]
  by_cases hy : IntervalIntegrable (yFlow f) volume 0 t
  · rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on ht.1.le (hy.const_mul _) (hint.const_mul _)
      fun s hs ↦ Deficit.yFlow_le_defInt hf h01 hm ht hs
  · rw [intervalIntegral.integral_undef hy, mul_zero]
    exact mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg ht.1.le
      fun s hs ↦ Deficit.defInt_nonneg hf h01 hm ht hs)

/-- `E e(s, √s Z) ≥ 0`. -/
theorem yFlow_nonneg (f : Gs n → ℝ) (hf : Measurable f) (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (s : ℝ) : 0 ≤ yFlow f s :=
  integral_nonneg fun _ ↦ Drift.eFlow_nonneg hf h01 s _

/-- **Borell's inequality** for functions (Theorem A(a)): `0 ≤ Δ(f) ≤ 1`. -/
theorem gDef_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hm : gMean f ∈ Ioo (0 : ℝ) 1) :
    0 ≤ gDef t f ∧ gDef t f ≤ 1 := by
  constructor
  · refine le_trans ?_ (borell_remainder ht f hf h01 hm)
    exact mul_nonneg (Real.sqrt_nonneg _)
      (intervalIntegral.integral_nonneg ht.1.le fun s _ ↦ yFlow_nonneg f hf h01 s)
  · have h1 : Gam t (gMean f) ≤ gMean f := Gam_le_self ⟨by linarith [ht.1], ht.2.le⟩ hm.1.le
    have h2 : 0 ≤ gStab t f := integral_nonneg fun x ↦ integral_nonneg fun z ↦
      mul_nonneg (h01 _).1 (h01 _).1
    unfold gDef
    linarith [hm.2]

end BGHKLMM26.RobustMIS
