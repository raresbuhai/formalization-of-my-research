module

public import BGHKLMM26.RobustMIS.Gaussian
public import BGHKLMM26.RobustMIS.Truncation
public import BGHKLMM26.RobustMIS.Rates
public import BGHKLMM26.RobustMIS.MultilinearGauss
public import BGHKLMM26.RobustMIS.GaussL2
public import BGHKLMM26.RobustMIS.NoiseLTF
public import BGHKLMM26.RobustMIS.BackToCube

/-!
# From Gaussian space to the cube

[BGHKLMM26, Lemmas `smoothed-boolean-transfer`, `smoothing-removal` and Corollary
`positive-transfer`], with Eldan's estimate (changes (P1)–(P3) of `eldan-proof.tex`): for
`t ∈ (0, 1)`, a table `u : {0,1}^R → [0, 1]` with mean in `[1/4, 3/4]` and small influences is
within `C ω([Γ_t(E u) - Stab_t(u)]⁺) + o_{τ↓0}(1)` of an LTF.

**Deviation from the paper's route** (recorded in `README.md`): the paper moves from Gaussian
space back to the cube through the `L¹` invariance for `q = u - L_λ` (which needs the influences
of `L_λ`, via the anti-concentration of [MORS10]) and the Gaussian approximation of regular LTFs
(Claim `MN-ltf-smoothing`, i.e. Mossel–Neeman's Lemma 7.3), and it removes the smoothing with
Peres's theorem. Here a single tool, the invariance principle for a *pair* of polynomials
(`invariance`), applied to `(T_r u, ⟨w, x⟩)` with the test function `|a - χ_s(b)| + tent_s(b)`
(`χ_s` a ramp of width `s` at the threshold), compares `E_cube |T_r u - L|` with
`E_γ |P_{u,r} - H|` directly (`cube_ltf_le_gauss`); and the smoothing is removed with
`‖u - L‖₁ ≤ ‖T_r u - L‖₁ + 2‖L - T_r L‖₁` (from the paper's proof of `smoothing-removal`) and the
elementary bound `‖L - T_r L‖₁ ≤ 4 (1-r)^{1/3} + o_{μ↓0}(1)` for regular LTFs (Chebyshev and
anti-concentration, the latter again from `invariance`), instead of Peres's `O(√(1-r))`. Since
`r` is chosen as a function of the error `ξ` only, the rate in `1 - r` does not matter.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic BGHKLMM26.Hard

variable {R : ℕ}

/-- `Stab_t(u) - Stab_{t r²}(u) ≤ 2(1 - r)/(1 - t)` (Lemma `boolean-smoothing-facts` (c)). -/
theorem stability_sub_stability_mul_le {t r : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (u : Cube (Fin R) → ℝ) (h01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1) :
    stability t u - stability (t * r ^ 2) u ≤ 2 * (1 - r) / (1 - t) := by
  have e : stability (t * r ^ 2) u = stability t (noise r u) := by
    rw [stability_noise, stability]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [mul_pow, pow_mul]
  rw [e]
  exact stability_sub_noise_le t r _ u (fun x ↦ ⟨by linarith [(h01 x).1], (h01 x).2⟩)
    (div_nonneg (by linarith) (by linarith)) (multiplier_le t r ht0 ht1 hr0 hr1)

namespace Transfer

theorem sqrtLog_max_zero (x : ℝ) : sqrtLog (max x 0) = sqrtLog x := by
  unfold sqrtLog clip01
  rw [max_eq_left (le_max_right x 0)]

/-- `E|f| ≤ ρ` when `E f² ≤ ρ²` (`|a| ≤ a²/(2ρ) + ρ/2`). -/
theorem integral_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf : Integrable (fun x ↦ f x ^ 2) μ) {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∫ x, f x ^ 2 ∂μ ≤ ρ ^ 2) : ∫ x, |f x| ∂μ ≤ ρ := by
  have hpt : ∀ x, |f x| ≤ f x ^ 2 / (2 * ρ) + ρ / 2 := fun x ↦ by
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity), ← sq_abs (f x)]
    nlinarith [sq_nonneg (|f x| - ρ)]
  have hint : Integrable (fun x ↦ f x ^ 2 / (2 * ρ) + ρ / 2) μ :=
    (hf.div_const _).add (integrable_const _)
  calc ∫ x, |f x| ∂μ ≤ ∫ x, (f x ^ 2 / (2 * ρ) + ρ / 2) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun x ↦ abs_nonneg _) hint (ae_of_all _ hpt)
    _ = (∫ x, f x ^ 2 ∂μ) / (2 * ρ) + ρ / 2 := by
        rw [integral_add (hf.div_const _) (integrable_const _), integral_div, integral_const,
          probReal_univ, one_smul]
    _ ≤ ρ ^ 2 / (2 * ρ) + ρ / 2 := by gcongr
    _ = ρ := by field_simp; ring

/-- `𝟙{θ c ≤ ⟨v, x⟩} = 𝟙{θ ≤ ⟨c⁻¹ v, x⟩}` for `c > 0`. -/
theorem halfInd_mul {n : ℕ} (v : Gs n) (θ : ℝ) {c : ℝ} (hc : 0 < c) :
    halfInd v (θ * c) = halfInd (c⁻¹ • v) θ := by
  unfold halfInd
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, real_inner_smul_left]
  rw [le_inv_mul_iff₀ hc, mul_comm]

/-! ### Arithmetic -/

theorem arith_regular {E I J ρ ξ CG ω ωD ω4 ωr A K : ℝ} (hCG : 0 < CG) (hA : 1 ≤ A)
    (hK : 0 ≤ K) (hωD : 0 ≤ ωD) (hωr : 0 ≤ ωr) (hB : E ≤ I + 2 * (ξ / 8) + ξ / 8)
    (htri : I ≤ ρ + J) (hL : J ≤ CG * ω) (hω : ω ≤ ωD + ω4 + A * ωr) (h4 : ω4 < ξ / (4 * CG))
    (hρ : ρ ≤ ξ / 4) (hξ : 0 ≤ ξ) : E ≤ (CG + K) * A * ωD + (CG + K) * A * ωr + ξ := by
  have h1 : CG * ω ≤ CG * ωD + CG * ω4 + CG * A * ωr := by
    have := mul_le_mul_of_nonneg_left hω hCG.le
    linarith only [this]
  have h2 : CG * ω4 ≤ ξ / 4 := by
    have := mul_le_mul_of_nonneg_left h4.le hCG.le
    have e : CG * (ξ / (4 * CG)) = ξ / 4 := by field_simp
    linarith only [this, e]
  have hCA : CG ≤ (CG + K) * A := by
    have : CG * 1 ≤ CG * A := mul_le_mul_of_nonneg_left hA hCG.le
    have : 0 ≤ K * A := mul_nonneg hK (by linarith)
    linarith only [this, ‹CG * 1 ≤ CG * A›]
  have h3 : CG * ωD ≤ (CG + K) * A * ωD := mul_le_mul_of_nonneg_right hCA hωD
  have h5 : CG * A * ωr ≤ (CG + K) * A * ωr := by
    have : CG * A ≤ (CG + K) * A := by
      have : 0 ≤ K * A := mul_nonneg hK (by linarith)
      linarith only [this]
    exact mul_le_mul_of_nonneg_right this hωr
  linarith only [hB, htri, hL, h1, h2, h3, h5, hρ, hξ]

theorem arith_const {E ωδ ω ωD ω4 ωr A CG ξ : ℝ} (hωδ : 0 < ωδ) (hA : 1 ≤ A) (hCG : 0 < CG)
    (hωD : 0 ≤ ωD) (hωr : 0 ≤ ωr) (hξ : 0 < ξ) (hE : E ≤ 1) (h1 : ωδ ≤ ω)
    (hω : ω ≤ ωD + ω4 + A * ωr) (h4 : ω4 < ωδ / 2) :
    E ≤ (CG + 2 / ωδ) * A * ωD + (CG + 2 / ωδ) * A * ωr + ξ := by
  have hAD : ωD ≤ A * ωD := le_mul_of_one_le_left hωD hA
  have h2 : ωδ / 2 ≤ A * (ωD + ωr) := by linarith only [hAD, h1, hω, h4]
  have h3 : 1 ≤ 2 / ωδ * (A * (ωD + ωr)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hωδ]; linarith only [h2]
  have h4 : 0 ≤ CG * (A * (ωD + ωr)) :=
    mul_nonneg hCG.le (mul_nonneg (by linarith) (by linarith))
  have h5 : 2 / ωδ * (A * (ωD + ωr)) + CG * (A * (ωD + ωr)) =
      (CG + 2 / ωδ) * A * ωD + (CG + 2 / ωδ) * A * ωr := by ring
  linarith only [h3, h4, h5, hE, hξ]

/-- The rate: `Δ ≤ D⁺ + 4ρ + c(1 - r)` gives `ω(Δ) ≤ ω(D) + ω(4ρ) + √(max c 1) ω(1 - r)`. -/
theorem rate_bound {c r ρ D Δ : ℝ} (hc : 0 < c) (hr1 : r < 1) (hρ0 : 0 ≤ ρ)
    (h : Δ ≤ max D 0 + 4 * ρ + c * (1 - r)) :
    sqrtLog Δ ≤ sqrtLog D + sqrtLog (4 * ρ) + √(max c 1) * sqrtLog (1 - r) := by
  have e1 := sqrtLog_add_le (add_nonneg (le_max_right D 0) (by positivity : 0 ≤ 4 * ρ))
    (mul_nonneg hc.le (by linarith : 0 ≤ 1 - r))
  have e2 := sqrtLog_add_le (le_max_right D 0) (by positivity : 0 ≤ 4 * ρ)
  have e3 := sqrtLog_mul_le hc (by linarith : 0 ≤ 1 - r)
  rw [sqrtLog_max_zero] at e2
  linarith only [monotone_sqrtLog h, e1, e2, e3]

/-! ### The truncated extension -/

theorem continuous_clamp_gaussExt (r : ℝ) (u : Cube (Fin R) → ℝ) :
    Continuous (fun G ↦ clamp01 (gaussExt r u G)) := by
  have := continuous_mlEval (R := R) (smoothC r (coefficient u))
  unfold clamp01 gaussExt; fun_prop

theorem memLp_gaussExt (r : ℝ) (u : Cube (Fin R) → ℝ) : MemLp (gaussExt r u) 2 (gm R) :=
  memLp_mlEval _ 2 (by simp)

theorem memLp_clamp_gaussExt (r : ℝ) (u : Cube (Fin R) → ℝ) :
    MemLp (fun G ↦ clamp01 (gaussExt r u G)) 2 (gm R) :=
  Gaussian.memLp_two_of_abs_le (continuous_clamp_gaussExt r u).measurable (C := 1)
    (fun x ↦ by
      rw [abs_le]
      constructor <;> linarith [NoiseLTF.clamp01_nonneg (gaussExt r u x),
        NoiseLTF.clamp01_le_one (gaussExt r u x)])

/-- The mean and the deficit of `F = clamp01 ∘ P_{u,r}`, if `‖P - F‖₂ ≤ ρ`. -/
theorem clamp_mean_deficit {t r ρ : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hρ0 : 0 < ρ) (u : Cube (Fin R) → ℝ) (h01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1)
    (hFP : √(∫ x, (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2 ∂gm R) ≤ ρ) :
    |gMean (fun G ↦ clamp01 (gaussExt r u G)) - 𝔼 x, u x| ≤ ρ ∧
      gDef t (fun G ↦ clamp01 (gaussExt r u G)) ≤
        max (Gam t (𝔼 x, u x) - stability t u) 0 + 4 * ρ + 2 / (1 - t) * (1 - r) := by
  have hPm := memLp_gaussExt r u
  have hFm := memLp_clamp_gaussExt r u
  have hmean : |gMean (fun G ↦ clamp01 (gaussExt r u G)) - 𝔼 x, u x| ≤ ρ := by
    rw [← gMean_gaussExt r u]; exact (abs_gMean_sub_le _ _ hFm hPm).trans hFP
  refine ⟨hmean, ?_⟩
  have htI : t ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, ht1.le⟩
  have hG1 := abs_Gam_sub_le htI (gMean (fun G ↦ clamp01 (gaussExt r u G))) (𝔼 x, u x)
  have hS1 := abs_gStab_sub_le htI _ (gaussExt r u) hFm hPm
  have hF2 : ∫ x, clamp01 (gaussExt r u x) ^ 2 ∂gm R ≤ 1 := by
    calc ∫ x, clamp01 (gaussExt r u x) ^ 2 ∂gm R ≤ ∫ _x, (1 : ℝ) ∂gm R :=
          integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _) (integrable_const _)
            (ae_of_all _ fun x ↦ pow_le_one₀ (NoiseLTF.clamp01_nonneg _)
              (NoiseLTF.clamp01_le_one _))
      _ = 1 := by simp
  have hP2 : ∫ x, gaussExt r u x ^ 2 ∂gm R ≤ 1 :=
    integral_gaussExt_sq_le (by rw [abs_of_pos hr0]; exact hr1.le) u h01
  have hsq : √(∫ x, clamp01 (gaussExt r u x) ^ 2 ∂gm R) + √(∫ x, gaussExt r u x ^ 2 ∂gm R) ≤ 2 :=
    by linarith [Real.sqrt_le_one.2 hF2, Real.sqrt_le_one.2 hP2]
  have hS2 : |gStab t (fun G ↦ clamp01 (gaussExt r u G)) - stability (t * r ^ 2) u| ≤ 2 * ρ := by
    rw [← gStab_gaussExt htI]
    refine hS1.trans ?_
    calc _ ≤ ρ * 2 := mul_le_mul hFP hsq (by positivity) hρ0.le
      _ = 2 * ρ := mul_comm _ _
  have hstab := stability_sub_stability_mul_le ht0.le ht1 hr0.le hr1.le u h01
  unfold gDef
  have h1 : Gam t (gMean (fun G ↦ clamp01 (gaussExt r u G))) ≤ Gam t (𝔼 x, u x) + 2 * ρ := by
    have := (le_abs_self _).trans hG1
    have := (le_abs_self _).trans hmean
    linarith
  have h2 : stability (t * r ^ 2) u - 2 * ρ ≤ gStab t (fun G ↦ clamp01 (gaussExt r u G)) := by
    linarith [(abs_le.1 hS2).1]
  have h3 : 2 * (1 - r) / (1 - t) = 2 / (1 - t) * (1 - r) := by ring
  linarith [le_max_left (Gam t (𝔼 x, u x) - stability t u) 0]

/-- The normal `F̂/|F̂|` is regular: its coordinates are `≤ (√τ + ρ)/c₀`. -/
theorem coord_sq_le {r c₀ μ' ρ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hc₀ : 0 < c₀) (hμ' : 0 < μ')
    (u : Cube (Fin R) → ℝ) (hinf : ∀ i, influence i u ≤ (c₀ * √μ' / 2) ^ 2)
    (hρc : ρ ≤ c₀ * √μ' / 2)
    (hFP : √(∫ x, (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2 ∂gm R) ≤ ρ)
    (hc0F : c₀ ≤ ‖hermite1 (fun G ↦ clamp01 (gaussExt r u G))‖) (i : Fin R) :
    (‖hermite1 (fun G ↦ clamp01 (gaussExt r u G))‖⁻¹ •
      hermite1 (fun G ↦ clamp01 (gaussExt r u G))) i ^ 2 ≤ μ' := by
  have hPm := memLp_gaussExt r u
  have hFm := memLp_clamp_gaussExt r u
  obtain ⟨v, hv⟩ : ∃ v, v = hermite1 (fun G ↦ clamp01 (gaussExt r u G)) := ⟨_, rfl⟩
  rw [← hv] at hc0F ⊢
  have hv0 : 0 < ‖v‖ := hc₀.trans_le hc0F
  have hPi : hermite1 (gaussExt r u) i = r * coefficient u (fun j ↦ decide (j = i)) := by
    rw [hermite1_apply _ hPm, integral_gaussExt_mul_coord]
  have h1 := abs_hermite1_sub_le _ (gaussExt r u) hFm hPm i
  rw [hPi, ← hv] at h1
  have hcu : |coefficient u (fun j ↦ decide (j = i))| ≤ c₀ * √μ' / 2 := by
    rw [← Real.sqrt_sq_eq_abs]
    calc √(coefficient u (fun j ↦ decide (j = i)) ^ 2) ≤ √((c₀ * √μ' / 2) ^ 2) :=
          Real.sqrt_le_sqrt ((coefficient_single_sq_le u i).trans (hinf i))
      _ = c₀ * √μ' / 2 := Real.sqrt_sq (by positivity)
  have h2 : |r * coefficient u (fun j ↦ decide (j = i))| ≤ c₀ * √μ' / 2 := by
    rw [abs_mul, abs_of_pos hr0]
    calc r * |coefficient u (fun j ↦ decide (j = i))|
        ≤ 1 * |coefficient u (fun j ↦ decide (j = i))| :=
          mul_le_mul_of_nonneg_right hr1.le (abs_nonneg _)
      _ ≤ c₀ * √μ' / 2 := by rw [one_mul]; exact hcu
  have hvi : |v i| ≤ c₀ * √μ' := by
    have := abs_sub_abs_le_abs_sub (v i) (r * coefficient u (fun j ↦ decide (j = i)))
    linarith
  have hle : ‖v‖⁻¹ * |v i| ≤ √μ' := by
    rw [inv_mul_le_iff₀ hv0]
    exact hvi.trans (mul_le_mul_of_nonneg_right hc0F (Real.sqrt_nonneg _))
  calc (‖v‖⁻¹ • v) i ^ 2 = (‖v‖⁻¹ * |v i|) ^ 2 := by
        rw [PiLp.smul_apply, smul_eq_mul, mul_pow, mul_pow, sq_abs]
    _ ≤ √μ' ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    _ = μ' := Real.sq_sqrt hμ'.le

/-- `‖P - H‖₁ ≤ ρ + ‖F - H‖₁` for `F = clamp01 ∘ P`, `‖P - F‖₂ ≤ ρ`. -/
theorem integral_abs_sub_halfInd_le {r ρ : ℝ} (hρ0 : 0 < ρ) (u : Cube (Fin R) → ℝ)
    (hPF2 : ∫ x, (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2 ∂gm R ≤ ρ ^ 2)
    (w : Gs R) (θ : ℝ) :
    ∫ x, |gaussExt r u x - halfInd w θ x| ∂gm R ≤
      ρ + ∫ x, |clamp01 (gaussExt r u x) - halfInd w θ x| ∂gm R := by
  have hPm := memLp_gaussExt r u
  have hFm := memLp_clamp_gaussExt r u
  have hHm : Integrable (halfInd w θ) (gm R) :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_le measurable_const (by fun_prop))
  have hFi := hFm.integrable one_le_two
  have hPi := hPm.integrable one_le_two
  have hPF1 : ∫ x, |gaussExt r u x - clamp01 (gaussExt r u x)| ∂gm R ≤ ρ := by
    refine integral_abs_le (f := fun x ↦ gaussExt r u x - clamp01 (gaussExt r u x))
      (hPm.sub hFm).integrable_sq hρ0 ?_
    have : (fun x ↦ (gaussExt r u x - clamp01 (gaussExt r u x)) ^ 2) =
        fun x ↦ (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2 := by
      funext x; ring
    rw [this]; exact hPF2
  have hadd : ∫ x, (|gaussExt r u x - clamp01 (gaussExt r u x)| +
      |clamp01 (gaussExt r u x) - halfInd w θ x|) ∂gm R =
      ∫ x, |gaussExt r u x - clamp01 (gaussExt r u x)| ∂gm R +
        ∫ x, |clamp01 (gaussExt r u x) - halfInd w θ x| ∂gm R :=
    integral_add (hPi.sub hFi).abs (hFi.sub hHm).abs
  have htri : ∫ x, |gaussExt r u x - halfInd w θ x| ∂gm R ≤
      ∫ x, (|gaussExt r u x - clamp01 (gaussExt r u x)| +
        |clamp01 (gaussExt r u x) - halfInd w θ x|) ∂gm R :=
    integral_mono_of_nonneg (ae_of_all _ fun x ↦ abs_nonneg _)
      ((hPi.sub hFi).abs.add (hFi.sub hHm).abs) (ae_of_all _ fun x ↦ abs_sub_le _ _ _)
  linarith

end Transfer

open Transfer in
/-- **Smoothed transfer** (Lemma `smoothed-boolean-transfer` with (P1)): for `t ∈ (0, 1)` there
is `C` such that for every `r ∈ (0, 1)`, `ξ, μ > 0` and influences small enough, some LTF `L`,
constant or regular (unit normal with `max wᵢ² ≤ μ`), has
`‖T_r u - L‖₁ ≤ C ω(Γ_t(E u) - Stab_t(u)) + C ω(1 - r) + ξ`.

Proof (the paper's proof with (P1)), with `C = (C_G + 2/ω(δ₀)) √(max (2/(1-t)) 1)`:
`P = P_{u,r}`, `F = clamp01 ∘ P`, `ρ_τ = ‖P - F‖₂ → 0` (`truncation`); `|E F - E u| ≤ ρ_τ`
(`gMean_gaussExt`, `abs_gMean_sub_le`), so `E F ∈ [1/5, 4/5]`;
`Δ' = Γ_t(E F) - Stab_t(F) ≤ D⁺ + 4ρ_τ + 2(1-r)/(1-t)` (`abs_Gam_sub_le`, `abs_gStab_sub_le`,
`gStab_gaussExt`, `integral_gaussExt_sq_le`, `stability_sub_stability_mul_le`;
`Transfer.clamp_mean_deficit`). If `Δ' > δ₀` (constants of `gaussian_main` for `[1/5, 4/5]`),
take `L` constant: `1 ≤ (ω(D) + ω(4ρ_τ) + √(max (2/(1-t)) 1) ω(1-r)) / ω(δ₀)`
(`sqrtLog_add_le`, `sqrtLog_mul_le`, `monotone_sqrtLog`). Otherwise `gaussian_main` gives
`|F̂| ≥ c₀` and `E_γ|F - H| ≤ C_G ω(Δ')` for `H = halfInd w θ`, `w = F̂/|F̂|`, `θ = -Ψ(E F)`;
`|F̂ᵢ| ≤ r |û({i})| + ρ_τ ≤ √τ + ρ_τ` (`integral_gaussExt_mul_coord`, `abs_hermite1_sub_le`,
`coefficient_single_sq_le`; `Transfer.coord_sq_le`), so `wᵢ² ≤ ((√τ + ρ_τ)/c₀)²` is small; and
`cube_ltf_le_gauss` with `‖P - H‖₁ ≤ ‖P - F‖₁ + ‖F - H‖₁ ≤ ρ_τ + C_G ω(Δ')`. -/
theorem smoothed_transfer {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → r < 1 → ∀ ξ > 0, ∀ μ > 0, ∃ τ > 0,
      ∀ (R : ℕ) (u : Cube (Fin R) → ℝ), (∀ x, 0 ≤ u x ∧ u x ≤ 1) →
        1 / 4 ≤ (𝔼 x, u x) → (𝔼 x, u x) ≤ 3 / 4 → (∀ i, influence i u ≤ τ) →
        ∃ L : Cube (Fin R) → Bool,
          ((∃ b, ∀ x, L x = b) ∨ ∃ (w : Gs R) (θ : ℝ), ‖w‖ = 1 ∧ (∀ i, w i ^ 2 ≤ μ) ∧
            ∀ x, L x = decide (θ ≤ ∑ i, w i * bitSign (x i))) ∧
          (𝔼 x, |noise r u x - bitVal (L x)|) ≤
            C * sqrtLog (Gam t (𝔼 x, u x) - stability t u) + C * sqrtLog (1 - r) + ξ := by
  obtain ⟨CG, c₀, δ₀, hCG, hc₀, hδ₀, hGM⟩ :=
    gaussian_main ht0 ht1 (a := 1 / 5) (b := 4 / 5) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A, A = √(max (2 / (1 - t)) 1) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by rw [hA]; exact Real.one_le_sqrt.2 (le_max_right _ _)
  have hωδ : 0 < sqrtLog δ₀ :=
    (Real.sqrt_pos.2 (lt_min hδ₀ one_pos)).trans_le (sqrt_min_le_sqrtLog hδ₀.le)
  have hC : 0 < (CG + 2 / sqrtLog δ₀) * A := by positivity
  refine ⟨(CG + 2 / sqrtLog δ₀) * A, hC, fun r hr0 hr1 ξ hξ μ hμ ↦ ?_⟩
  -- continuity of `ω` at `0`
  obtain ⟨η, hη, hηω⟩ : ∃ η > 0, ∀ x, |x| < η →
      sqrtLog x < min (sqrtLog δ₀ / 2) (ξ / (4 * CG)) := by
    have hc := continuous_sqrtLog.continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨η, hη, hη'⟩ := hc _ (lt_min (half_pos hωδ) (by positivity : 0 < ξ / (4 * CG)))
    refine ⟨η, hη, fun x hx ↦ ?_⟩
    have h1 := hη' (x := x) (by simpa [Real.dist_eq] using hx)
    rwa [Real.dist_eq, sqrtLog_zero, sub_zero, abs_of_nonneg (sqrtLog_nonneg x)] at h1
  obtain ⟨τ₂, hτ₂, hBC⟩ := cube_ltf_le_gauss hr0 hr1 (s := ξ / 8) (ε := ξ / 8) (by positivity)
    (by positivity)
  obtain ⟨μ', hμ'⟩ : ∃ μ', μ' = min μ τ₂ := ⟨_, rfl⟩
  have hμ'0 : 0 < μ' := hμ' ▸ lt_min hμ hτ₂
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = min (min (1 / 20) (η / 8)) (min (ξ / 4) (c₀ * √μ' / 2)) :=
    ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by
    rw [hρ]
    exact lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (by positivity))
  have hρ1 : ρ ≤ 1 / 20 := hρ ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρη : ρ ≤ η / 8 := hρ ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρξ : ρ ≤ ξ / 4 := hρ ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hρc : ρ ≤ c₀ * √μ' / 2 := hρ ▸ (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨τ₁, hτ₁, hTr⟩ := truncation hr0 hr1 (ε := ρ ^ 2) (by positivity)
  refine ⟨min (min τ₁ τ₂) ((c₀ * √μ' / 2) ^ 2), by positivity,
    fun R u h01 hm1 hm2 hinf ↦ ?_⟩
  have hinf1 : ∀ i, influence i u ≤ τ₁ :=
    fun i ↦ (hinf i).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hinf2 : ∀ i, influence i u ≤ τ₂ :=
    fun i ↦ (hinf i).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hinf3 : ∀ i, influence i u ≤ (c₀ * √μ' / 2) ^ 2 :=
    fun i ↦ (hinf i).trans (min_le_right _ _)
  -- the truncation `F = clamp01 ∘ P_{u,r}`
  have hFc := continuous_clamp_gaussExt r u
  have hF01 : ∀ x, 0 ≤ clamp01 (gaussExt r u x) ∧ clamp01 (gaussExt r u x) ≤ 1 :=
    fun x ↦ ⟨NoiseLTF.clamp01_nonneg _, NoiseLTF.clamp01_le_one _⟩
  have hPF2 : ∫ x, (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2 ∂gm R ≤ ρ ^ 2 := by
    have : (fun x ↦ (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2) =
        fun x ↦ (gaussExt r u x - clamp01 (gaussExt r u x)) ^ 2 := by
      funext x; ring
    rw [this]; exact hTr R u h01 hinf1
  have hFP : √(∫ x, (clamp01 (gaussExt r u x) - gaussExt r u x) ^ 2 ∂gm R) ≤ ρ :=
    (Real.sqrt_le_sqrt hPF2).trans_eq (Real.sqrt_sq hρ0.le)
  obtain ⟨hmean, hdef⟩ := clamp_mean_deficit ht0 ht1 hr0 hr1 hρ0 u h01 hFP
  have hmF1 : 1 / 5 ≤ gMean (fun G ↦ clamp01 (gaussExt r u G)) := by
    linarith [(abs_le.1 hmean).1]
  have hmF2 : gMean (fun G ↦ clamp01 (gaussExt r u G)) ≤ 4 / 5 := by
    linarith [(abs_le.1 hmean).2]
  have hω := rate_bound (div_pos two_pos (by linarith : 0 < 1 - t)) hr1 hρ0.le hdef
  rw [← hA] at hω
  have h4ρ : sqrtLog (4 * ρ) < min (sqrtLog δ₀ / 2) (ξ / (4 * CG)) :=
    hηω _ (by rw [abs_of_pos (by positivity)]; linarith)
  have hGMF := hGM R _ hFc.measurable hF01 hmF1 hmF2
  by_cases hsmall : gDef t (fun G ↦ clamp01 (gaussExt r u G)) ≤ δ₀
  · -- a regular LTF
    obtain ⟨hc0F, hL1⟩ := hGMF.2 hsmall
    have hv0 : 0 < ‖hermite1 (fun G ↦ clamp01 (gaussExt r u G))‖ := hc₀.trans_le hc0F
    obtain ⟨w, hw⟩ : ∃ w : Gs R, w = ‖hermite1 (fun G ↦ clamp01 (gaussExt r u G))‖⁻¹ •
        hermite1 (fun G ↦ clamp01 (gaussExt r u G)) := ⟨_, rfl⟩
    obtain ⟨θ, hθ⟩ : ∃ θ, θ = -Psi (gMean (fun G ↦ clamp01 (gaussExt r u G))) := ⟨_, rfl⟩
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv0.ne']
    rw [halfInd_mul _ _ hv0, ← hw, ← hθ] at hL1
    have hcoord : ∀ i, w i ^ 2 ≤ μ' := fun i ↦
      hw ▸ coord_sq_le hr0 hr1 hc₀ hμ'0 u hinf3 hρc hFP hc0F i
    have hwμ : ∀ i, w i ^ 2 ≤ μ := fun i ↦ (hcoord i).trans (hμ' ▸ min_le_left _ _)
    have hwτ : ∀ i, w i ^ 2 ≤ τ₂ := fun i ↦ (hcoord i).trans (hμ' ▸ min_le_right _ _)
    refine ⟨fun x ↦ decide (θ ≤ ∑ i, w i * bitSign (x i)),
      Or.inr ⟨w, θ, hwn, hwμ, fun x ↦ rfl⟩, ?_⟩
    exact arith_regular hCG hA1 (div_pos two_pos hωδ).le (sqrtLog_nonneg _) (sqrtLog_nonneg _)
      (hBC R u h01 hinf2 w θ hwn hwτ) (integral_abs_sub_halfInd_le hρ0 u hPF2 w θ) hL1 hω
      (h4ρ.trans_le (min_le_right _ _)) hρξ hξ.le
  · -- a constant
    refine ⟨fun _ ↦ false, Or.inl ⟨false, fun _ ↦ rfl⟩, ?_⟩
    have hT := noise_mem (by linarith) hr1.le h01
    have hle1 : (𝔼 x, |noise r u x - bitVal ((fun _ : Cube (Fin R) ↦ false) x)|) ≤ 1 := by
      calc (𝔼 x, |noise r u x - bitVal ((fun _ : Cube (Fin R) ↦ false) x)|)
          ≤ 𝔼 _x : Cube (Fin R), (1 : ℝ) := Finset.expect_le_expect fun x _ ↦ by
            simp only [bitVal, Bool.false_eq_true, ite_false, sub_zero]
            rw [abs_of_nonneg (hT x).1]; exact (hT x).2
        _ = 1 := by simp
    exact arith_const hωδ hA1 hCG (sqrtLog_nonneg _) (sqrtLog_nonneg _) hξ hle1
      (monotone_sqrtLog (not_le.1 hsmall).le) hω (h4ρ.trans_le (min_le_left _ _))


/-- **Corollary `positive-transfer`** (with (P3)): `dist(u, ℒ_R) ≤ C ω([Γ_t(E u) - Stab_t(u)]⁺) +
o_{τ↓0}(1)` for `u : {0,1}^R → [0,1]` with `E u ∈ [1/4, 3/4]`. -/
theorem positive_transfer {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ C > 0, ∀ ξ > 0, ∃ τ > 0, ∀ (R : ℕ) (u : Cube (Fin R) → ℝ), (∀ x, 0 ≤ u x ∧ u x ≤ 1) →
      1 / 4 ≤ (𝔼 x, u x) → (𝔼 x, u x) ≤ 3 / 4 → (∀ i, influence i u ≤ τ) →
        ltfDist u ≤ C * sqrtLog (Gam t (𝔼 x, u x) - stability t u) + ξ := by
  obtain ⟨C, hC, hST⟩ := smoothed_transfer ht0 ht1
  refine ⟨C, hC, fun ξ hξ ↦ ?_⟩
  -- The smoothing `r = 1 - κ`, close enough to `1`.
  obtain ⟨δ, hδ, hδω⟩ : ∃ δ > 0, ∀ x, |x| < δ → C * sqrtLog x < ξ / 4 := by
    have hc := continuous_sqrtLog.continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hδ'⟩ := hc (ξ / (4 * C)) (by positivity)
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    have h1 := hδ' (x := x) (by simpa [Real.dist_eq] using hx)
    rw [Real.dist_eq, sqrtLog_zero, sub_zero, abs_of_nonneg (sqrtLog_nonneg x)] at h1
    calc C * sqrtLog x < C * (ξ / (4 * C)) := mul_lt_mul_of_pos_left h1 hC
      _ = ξ / 4 := by field_simp
  set κ : ℝ := min (min (δ / 2) ((ξ / 32) ^ 3)) (1 / 2) with hκ
  have hκ0 : 0 < κ := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hκδ : κ < δ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hκξ : κ ≤ (ξ / 32) ^ 3 := (min_le_left _ _).trans (min_le_right _ _)
  have hκ2 : κ ≤ 1 / 2 := min_le_right _ _
  have hr0 : 0 < 1 - κ := by linarith
  have hr1 : 1 - κ < 1 := by linarith
  have hω : C * sqrtLog (1 - (1 - κ)) < ξ / 4 := by
    rw [sub_sub_cancel]; exact hδω κ (by rw [abs_of_pos hκ0]; exact hκδ)
  have hpow : (1 - (1 - κ)) ^ (1 / 3 : ℝ) ≤ ξ / 32 := by
    rw [sub_sub_cancel]
    calc κ ^ (1 / 3 : ℝ) ≤ ((ξ / 32) ^ 3) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow hκ0.le hκξ (by norm_num)
      _ = ξ / 32 := by
        rw [show (1 / 3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  obtain ⟨μ, hμ, hreg⟩ := regular_ltf_noise hr0.le hr1 (ε := ξ / 8) (by positivity)
  obtain ⟨τ, hτ, hτ'⟩ := hST (1 - κ) hr0 hr1 (ξ / 4) (by positivity) μ hμ
  refine ⟨τ, hτ, fun R u h01 hm1 hm2 hinf ↦ ?_⟩
  obtain ⟨L, hLform, hLbound⟩ := hτ' R u h01 hm1 hm2 hinf
  have hLTF : IsLTF L := by
    rcases hLform with ⟨b, hb⟩ | ⟨w, θ, -, -, hw⟩
    · obtain rfl : L = fun _ ↦ b := funext hb
      exact isLTF_const R b
    · exact ⟨fun i ↦ w i, θ, hw⟩
  have hrpow : 0 ≤ (1 - (1 - κ)) ^ (1 / 3 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hnoiseL : (𝔼 x, |bitVal (L x) - noise (1 - κ) (fun y ↦ bitVal (L y)) x|) ≤
      4 * (1 - (1 - κ)) ^ (1 / 3 : ℝ) + ξ / 8 := by
    rcases hLform with ⟨b, hb⟩ | ⟨w, θ, hw1, hwμ, hw⟩
    · obtain rfl : L = fun _ ↦ b := funext hb
      have hc : ∀ x, noise (1 - κ) (fun _ : Cube (Fin R) ↦ bitVal b) x = bitVal b := by
        intro x
        rw [noise_eq_sum, ← Finset.sum_mul, sum_flipWeight, one_mul]
      simp only [hc, sub_self, abs_zero, Finset.expect_const_zero]
      positivity
    · obtain rfl : L = fun x ↦ decide (θ ≤ ∑ i, w i * bitSign (x i)) := funext hw
      exact hreg R w θ hw1 hwμ
  calc ltfDist u ≤ 𝔼 x, |u x - bitVal (L x)| := ltfDist_le u hLTF
    _ ≤ (𝔼 x, |noise (1 - κ) u x - bitVal (L x)|) +
          2 * 𝔼 x, |bitVal (L x) - noise (1 - κ) (fun y ↦ bitVal (L y)) x| :=
        smoothing_removal hr0.le hr1.le u h01 L
    _ ≤ (C * sqrtLog (Gam t (𝔼 x, u x) - stability t u) + C * sqrtLog (1 - (1 - κ)) + ξ / 4) +
          2 * (4 * (1 - (1 - κ)) ^ (1 / 3 : ℝ) + ξ / 8) := by gcongr
    _ ≤ C * sqrtLog (Gam t (𝔼 x, u x) - stability t u) + ξ := by linarith

end BGHKLMM26.RobustMIS
