module

public import BGHKLMM26.Model
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Goemans–Williamson minimizer

The ratio `gwRatio ρ = (arccos ρ / π) / ((1 - ρ) / 2)` has exactly one minimizer `ρ*` on
`[-1, 1)` (`BGHKLMM26.GW.exists_unique_isGWMinimizer`).

With `θ = arccos ρ ∈ (0, π]`, the ratio is `(2 / π) g θ` for `g θ = θ / (1 - cos θ)`, whose
derivative is `k θ / (1 - cos θ)²` with `k θ = 1 - cos θ - θ sin θ`. Since `k' θ = -θ cos θ`, `k`
decreases from `k 0 = 0` on `[0, π/2]` and increases to `k π = 2` on `[π/2, π]`, so it has exactly
one zero `θ*`, in `(π/2, π)`. Then `g` decreases on `(0, θ*]` and increases on `[θ*, π]`, and
`ρ* = cos θ*`.
-/

@[expose] public section

namespace BGHKLMM26.GW

open Real Set

/-- `k θ = 1 - cos θ - θ sin θ`, the sign of the derivative of `θ / (1 - cos θ)`. -/
noncomputable def k (θ : ℝ) : ℝ := 1 - cos θ - θ * sin θ

/-- `g θ = θ / (1 - cos θ)`, the ratio in terms of `θ = arccos ρ`, up to the factor `2 / π`. -/
noncomputable def g (θ : ℝ) : ℝ := θ / (1 - cos θ)

theorem hasDerivAt_k (θ : ℝ) : HasDerivAt k (-(θ * cos θ)) θ := by
  have h := ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_cos θ)).sub
    ((hasDerivAt_id θ).mul (hasDerivAt_sin θ))
  convert h using 1
  · funext x
    simp [k]
  · simp only [id]
    ring

theorem k_zero : k 0 = 0 := by simp [k]

theorem k_pi_div_two : k (π / 2) = 1 - π / 2 := by simp [k]

theorem k_pi : k π = 2 := by
  simp [k]
  norm_num

theorem k_strictAntiOn : StrictAntiOn k (Icc 0 (π / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun x _ ↦ (hasDerivAt_k x).continuousAt.continuousWithinAt) fun x hx ↦ ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_k x).deriv]
  have hc : 0 < cos x := cos_pos_of_mem_Ioo ⟨by linarith [hx.1, pi_pos], hx.2⟩
  exact neg_neg_of_pos (mul_pos hx.1 hc)

theorem k_strictMonoOn : StrictMonoOn k (Icc (π / 2) π) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun x _ ↦ (hasDerivAt_k x).continuousAt.continuousWithinAt) fun x hx ↦ ?_
  rw [interior_Icc] at hx
  rw [(hasDerivAt_k x).deriv]
  have hc : cos x < 0 := cos_neg_of_pi_div_two_lt_of_lt hx.1 (by linarith [hx.2, pi_pos])
  have hx0 : 0 < x := by linarith [hx.1, pi_pos]
  nlinarith

/-- `k` has a zero in `(π/2, π)`. -/
theorem exists_k_eq_zero : ∃ θ ∈ Ioo (π / 2) π, k θ = 0 := by
  have hc : ContinuousOn k (Icc (π / 2) π) :=
    fun x _ ↦ (hasDerivAt_k x).continuousAt.continuousWithinAt
  have h0 : (0 : ℝ) ∈ Ioo (k (π / 2)) (k π) := by
    rw [k_pi_div_two, k_pi]
    constructor <;> linarith [pi_gt_three]
  exact intermediate_value_Ioo (by linarith [pi_pos]) hc h0

theorem one_sub_cos_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π) : 0 < 1 - cos θ := by
  have hne : cos θ ≠ 1 := fun h ↦ h0.ne'
    ((cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) (by linarith [pi_pos])).1 h)
  have hle := cos_le_one θ
  have : cos θ < 1 := lt_of_le_of_ne hle hne
  linarith

theorem hasDerivAt_g {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π) :
    HasDerivAt g (k θ / (1 - cos θ) ^ 2) θ := by
  have hne := (one_sub_cos_pos h0 hπ).ne'
  have h := (hasDerivAt_id θ).div ((hasDerivAt_const θ (1 : ℝ)).sub (hasDerivAt_cos θ)) hne
  convert h using 1
  · funext x
    simp [g]
  · simp only [id, k, Pi.sub_apply]
    ring

/-! ### The minimizer `θ*` -/

/-- `θ*`: the zero of `k` in `(π/2, π)`, where `θ / (1 - cos θ)` is smallest. -/
noncomputable def thetaStar : ℝ := Classical.choose exists_k_eq_zero

theorem thetaStar_mem : thetaStar ∈ Ioo (π / 2) π := (Classical.choose_spec exists_k_eq_zero).1

theorem k_thetaStar : k thetaStar = 0 := (Classical.choose_spec exists_k_eq_zero).2

theorem thetaStar_pos : 0 < thetaStar := by linarith [thetaStar_mem.1, pi_pos]

/-- `k < 0` on `(0, θ*)`. -/
theorem k_neg {x : ℝ} (hx : x ∈ Ioo 0 thetaStar) : k x < 0 := by
  by_cases hx2 : x ≤ π / 2
  · have := k_strictAntiOn ⟨le_rfl, by linarith [pi_pos]⟩ ⟨hx.1.le, hx2⟩ hx.1
    rwa [k_zero] at this
  · have := k_strictMonoOn ⟨by linarith, by linarith [hx.2, thetaStar_mem.2]⟩
      ⟨thetaStar_mem.1.le, thetaStar_mem.2.le⟩ hx.2
    rwa [k_thetaStar] at this

/-- `k > 0` on `(θ*, π]`. -/
theorem k_pos {x : ℝ} (hx : x ∈ Ioc thetaStar π) : 0 < k x := by
  have := k_strictMonoOn ⟨thetaStar_mem.1.le, thetaStar_mem.2.le⟩
    ⟨by linarith [hx.1, thetaStar_mem.1], hx.2⟩ hx.1
  rwa [k_thetaStar] at this

/-- `g` decreases on `(0, θ*]`. -/
theorem g_strictAntiOn : StrictAntiOn g (Ioc 0 thetaStar) := by
  have hθ := thetaStar_mem.2.le
  refine strictAntiOn_of_deriv_neg (convex_Ioc _ _) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · exact (hasDerivAt_g hx.1 (hx.2.trans hθ)).continuousAt.continuousWithinAt
  · rw [interior_Ioc] at hx
    rw [(hasDerivAt_g hx.1 (hx.2.le.trans hθ)).deriv]
    exact div_neg_of_neg_of_pos (k_neg hx) (pow_pos (one_sub_cos_pos hx.1 (hx.2.le.trans hθ)) 2)

/-- `g` increases on `[θ*, π]`. -/
theorem g_strictMonoOn : StrictMonoOn g (Icc thetaStar π) := by
  have h0 := thetaStar_pos
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun x hx ↦ ?_) fun x hx ↦ ?_
  · exact (hasDerivAt_g (by linarith [hx.1]) hx.2).continuousAt.continuousWithinAt
  · rw [interior_Icc] at hx
    rw [(hasDerivAt_g (by linarith [hx.1]) hx.2.le).deriv]
    exact div_pos (k_pos ⟨hx.1, hx.2.le⟩)
      (pow_pos (one_sub_cos_pos (by linarith [hx.1]) hx.2.le) 2)

/-- `g` is smallest at `θ*` on `(0, π]`, strictly. -/
theorem g_lt {θ : ℝ} (hθ : θ ∈ Ioc 0 π) (hne : θ ≠ thetaStar) : g thetaStar < g θ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact g_strictAntiOn ⟨hθ.1, hlt.le⟩ ⟨thetaStar_pos, le_rfl⟩ hlt
  · exact g_strictMonoOn ⟨le_rfl, thetaStar_mem.2.le⟩ ⟨hgt.le, hθ.2⟩ hgt

theorem g_le {θ : ℝ} (hθ : θ ∈ Ioc 0 π) : g thetaStar ≤ g θ := by
  by_cases he : θ = thetaStar
  · rw [he]
  · exact (g_lt hθ he).le

/-! ### The minimizer `ρ*` and `α_GW` -/

/-- The ratio in terms of `θ = arccos ρ`. -/
theorem gwRatio_eq {ρ : ℝ} (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1) : gwRatio ρ = 2 / π * g (arccos ρ) := by
  rw [gwRatio, g, cos_arccos h1 h2]
  have := pi_pos
  field_simp

theorem arccos_mem_Ioc {ρ : ℝ} (h : ρ ∈ Ico (-1 : ℝ) 1) : arccos ρ ∈ Ioc 0 π :=
  ⟨arccos_pos.2 h.2, arccos_le_pi ρ⟩

/-- `ρ* = cos θ* ≈ -0.689`, the minimizer of the Goemans–Williamson ratio. -/
noncomputable def rhoStar : ℝ := cos thetaStar

theorem arccos_rhoStar : arccos rhoStar = thetaStar :=
  arccos_cos thetaStar_pos.le thetaStar_mem.2.le

theorem rhoStar_mem : rhoStar ∈ Ico (-1 : ℝ) 1 := by
  have := one_sub_cos_pos thetaStar_pos thetaStar_mem.2.le
  exact ⟨neg_one_le_cos _, by rw [rhoStar]; linarith⟩

theorem two_div_pi_pos : 0 < 2 / π := div_pos two_pos pi_pos

theorem gwRatio_rhoStar : gwRatio rhoStar = 2 / π * g thetaStar := by
  rw [gwRatio_eq rhoStar_mem.1 rhoStar_mem.2.le, arccos_rhoStar]

theorem isGWMinimizer_rhoStar : IsGWMinimizer rhoStar := by
  refine ⟨rhoStar_mem, fun σ hσ ↦ ?_⟩
  rw [gwRatio_rhoStar, gwRatio_eq hσ.1 hσ.2.le]
  exact mul_le_mul_of_nonneg_left (g_le (arccos_mem_Ioc hσ)) two_div_pi_pos.le

/-- **The Goemans–Williamson ratio has exactly one minimizer** on `[-1, 1)`: `ρ* = cos θ*`. -/
theorem exists_unique_isGWMinimizer : ∃! ρ : ℝ, IsGWMinimizer ρ := by
  refine ⟨rhoStar, isGWMinimizer_rhoStar, fun ρ hρ ↦ ?_⟩
  by_contra hne
  have harcρ : arccos ρ ≠ thetaStar := fun h ↦ hne (by
    rw [rhoStar, ← h, cos_arccos hρ.1.1 hρ.1.2.le])
  have h1 := hρ.2 rhoStar rhoStar_mem
  rw [gwRatio_rhoStar, gwRatio_eq hρ.1.1 hρ.1.2.le] at h1
  have := mul_lt_mul_of_pos_left (g_lt (arccos_mem_Ioc hρ.1) harcρ) two_div_pi_pos
  linarith

/-- `α_GW` is the ratio at `ρ*`. -/
theorem alphaGW_eq : alphaGW = gwRatio rhoStar := by
  have h : IsLeast (gwRatio '' Ico (-1 : ℝ) 1) (gwRatio rhoStar) :=
    ⟨⟨rhoStar, rhoStar_mem, rfl⟩, by
      rintro _ ⟨σ, hσ, rfl⟩
      exact isGWMinimizer_rhoStar.2 σ hσ⟩
  exact h.csInf_eq

theorem g_pos {θ : ℝ} (h0 : 0 < θ) (hπ : θ ≤ π) : 0 < g θ :=
  div_pos h0 (one_sub_cos_pos h0 hπ)

theorem alphaGW_pos : 0 < alphaGW := by
  rw [alphaGW_eq, gwRatio_rhoStar]
  exact mul_pos two_div_pi_pos (g_pos thetaStar_pos thetaStar_mem.2.le)

/-- `α_GW < 1`: at `ρ = -1` the ratio is `1`. -/
theorem alphaGW_lt_one : alphaGW < 1 := by
  have hπ : arccos (-1) = π := arccos_neg_one
  have h1 : gwRatio (-1) = 1 := by
    rw [gwRatio, hπ]
    have := pi_pos
    field_simp
    norm_num
  have hne : arccos (-1) ≠ thetaStar := by rw [hπ]; exact thetaStar_mem.2.ne'
  have := mul_lt_mul_of_pos_left (g_lt (arccos_mem_Ioc ⟨le_rfl, by norm_num⟩) hne)
    two_div_pi_pos
  rw [← gwRatio_rhoStar, ← gwRatio_eq le_rfl (by norm_num), h1] at this
  rw [alphaGW_eq]
  exact this

/-! ### The window `[-4/5, -1/2]` around `ρ*` -/

/-- `arccos (-1/2) = 2π/3`. -/
theorem arccos_neg_half : arccos (-(1 / 2)) = 2 * π / 3 := by
  have h : cos (2 * π / 3) = -(1 / 2) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
  rw [← h, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- `θ₁ = arccos (-4/5) < 3`. -/
theorem arccos_neg_four_fifths_lt : arccos (-(4 / 5)) < 3 := by
  have h3 : cos 3 < -(4 / 5) := by
    have h := one_sub_sq_div_two_le_cos (x := π - 3)
    rw [cos_pi_sub] at h
    have hπ1 := pi_gt_three
    have hπ2 := pi_lt_d2
    nlinarith
  have := arccos_lt_arccos (by linarith [neg_one_le_cos 3]) h3 (by norm_num)
  rwa [arccos_cos (by norm_num) (by linarith [pi_gt_three])] at this

/-- `θ* > 2π/3`, so `ρ* < -1/2`: `k (2π/3) = 3/2 - π / √3 < 0`. -/
theorem two_pi_div_three_lt_thetaStar : 2 * π / 3 < thetaStar := by
  have hk : k (2 * π / 3) < 0 := by
    have hc : cos (2 * π / 3) = -(1 / 2) := by
      rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
    have hs : sin (2 * π / 3) = √3 / 2 := by
      rw [show 2 * π / 3 = π - π / 3 by ring, sin_pi_sub, sin_pi_div_three]
    rw [k, hc, hs]
    have h3 : (1.7 : ℝ) < √3 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    nlinarith [pi_gt_three]
  by_contra hle
  rw [not_lt] at hle
  have hmem : 2 * π / 3 ∈ Icc (π / 2) π := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have := k_strictMonoOn.le_iff_le ⟨thetaStar_mem.1.le, thetaStar_mem.2.le⟩ hmem |>.2 hle
  rw [k_thetaStar] at this
  linarith

/-- `θ* < arccos (-4/5)`, so `ρ* > -4/5`: `k (arccos (-4/5)) = 9/5 - (3/5) arccos (-4/5) > 0`. -/
theorem thetaStar_lt_arccos : thetaStar < arccos (-(4 / 5)) := by
  have hmem : arccos (-(4 / 5)) ∈ Icc (π / 2) π :=
    ⟨pi_div_two_le_arccos.2 (by norm_num), arccos_le_pi _⟩
  have hk : 0 < k (arccos (-(4 / 5))) := by
    rw [k, cos_arccos (by norm_num) (by norm_num), sin_arccos]
    have hs : √(1 - (-(4 / 5) : ℝ) ^ 2) = 3 / 5 := by
      rw [show (1 : ℝ) - (-(4 / 5)) ^ 2 = (3 / 5) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [hs]
    nlinarith [arccos_neg_four_fifths_lt]
  rw [← k_thetaStar] at hk
  exact (k_strictMonoOn.lt_iff_lt ⟨thetaStar_mem.1.le, thetaStar_mem.2.le⟩ hmem).1 hk

/-- **`-4/5 < ρ* < -1/2`.** -/
theorem rhoStar_mem_window : rhoStar ∈ Ioo (-(4 / 5) : ℝ) (-(1 / 2)) := by
  constructor
  · have := cos_lt_cos_of_nonneg_of_le_pi thetaStar_pos.le (arccos_le_pi _) thetaStar_lt_arccos
    rwa [cos_arccos (by norm_num) (by norm_num)] at this
  · have := cos_lt_cos_of_nonneg_of_le_pi (by positivity) thetaStar_mem.2.le
      two_pi_div_three_lt_thetaStar
    rwa [show cos (2 * π / 3) = -(1 / 2) by
      rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]] at this

/-- **The gap outside the window** [BGHKLMM26, proof of Lemma 3.3]: for `σ ∈ [-1, 1)` outside
`(-4/5, -1/2)`, the ratio is at least `α_GW + κ` for one `κ > 0`. -/
theorem exists_gap : ∃ κ : ℝ, 0 < κ ∧ ∀ σ ∈ Ico (-1 : ℝ) 1, σ ≤ -(4 / 5) ∨ -(1 / 2) ≤ σ →
    alphaGW + κ ≤ gwRatio σ := by
  have h1 : 2 * π / 3 ∈ Ioc 0 thetaStar :=
    ⟨by positivity, two_pi_div_three_lt_thetaStar.le⟩
  have h2 : arccos (-(4 / 5)) ∈ Icc thetaStar π := ⟨thetaStar_lt_arccos.le, arccos_le_pi _⟩
  have hg1 : g thetaStar < g (2 * π / 3) :=
    g_strictAntiOn h1 ⟨thetaStar_pos, le_rfl⟩ two_pi_div_three_lt_thetaStar
  have hg2 : g thetaStar < g (arccos (-(4 / 5))) :=
    g_strictMonoOn ⟨le_rfl, thetaStar_mem.2.le⟩ h2 thetaStar_lt_arccos
  refine ⟨2 / π * min (g (2 * π / 3) - g thetaStar) (g (arccos (-(4 / 5))) - g thetaStar),
    mul_pos two_div_pi_pos (lt_min (by linarith) (by linarith)), fun σ hσ hout ↦ ?_⟩
  rw [alphaGW_eq, gwRatio_rhoStar, gwRatio_eq hσ.1 hσ.2.le, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ two_div_pi_pos.le
  have hθ := arccos_mem_Ioc hσ
  rcases hout with hlo | hhi
  · -- `arccos σ ≥ arccos (-4/5) > θ*`, where `g` increases.
    have hge : arccos (-(4 / 5)) ≤ arccos σ :=
      strictAntiOn_arccos.antitoneOn ⟨hσ.1, hσ.2.le⟩ ⟨by norm_num, by norm_num⟩ hlo
    have := g_strictMonoOn.monotoneOn h2 ⟨h2.1.trans hge, hθ.2⟩ hge
    linarith [min_le_right (g (2 * π / 3) - g thetaStar) (g (arccos (-(4 / 5))) - g thetaStar)]
  · -- `arccos σ ≤ 2π/3 < θ*`, where `g` decreases.
    have hle : arccos σ ≤ 2 * π / 3 := by
      rw [← arccos_neg_half]
      exact strictAntiOn_arccos.antitoneOn ⟨by norm_num, by norm_num⟩ ⟨hσ.1, hσ.2.le⟩ hhi
    have := g_strictAntiOn.antitoneOn ⟨hθ.1, hle.trans h1.2⟩ h1 hle
    linarith [min_le_left (g (2 * π / 3) - g thetaStar) (g (arccos (-(4 / 5))) - g thetaStar)]

end BGHKLMM26.GW
