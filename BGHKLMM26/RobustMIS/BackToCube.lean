module

public import BGHKLMM26.RobustMIS.Invariance
public import BGHKLMM26.RobustMIS.Multilinear
public import BGHKLMM26.RobustMIS.NoiseLTF
public import BGHKLMM26.RobustMIS.Truncation
public import BGHKLMM26.Hardness.Defs

/-!
# From Gaussian space back to the cube

`cube_ltf_le_gauss`: for a regular LTF `L = 𝟙{θ ≤ ⟨w, σ(x)⟩}` and its Gaussian counterpart
`H = 𝟙{θ ≤ ⟨w, G⟩}`, `E_cube |T_r u - L| ≤ E_γ |P_{u,r} - H| + 2s + o_{τ↓0}(1)`. This replaces,
in the proof of Lemma `smoothed-boolean-transfer`, both the Gaussian approximation of regular LTFs
(Claim `MN-ltf-smoothing`, i.e. Mossel–Neeman's Lemma 7.3) and the `L¹` invariance for
`u - L_λ` with the MORS10 anti-concentration (deviation recorded in `README.md`).

Auxiliary material (namespace `BackToCube`): the ramp `χ_s`, the test function
`testFn θ s a b = |a - χ_s(b)| + tent_s(b)` (`lipPair_testFn`), and its Gaussian bound
`integral_testFn_le`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic BGHKLMM26.Hard

variable {R : ℕ}

namespace BackToCube

open NoiseLTF

/-- The ramp `χ_s(b) = clamp01((b - θ + s)/s)`: `0` below `θ - s`, `1` above `θ`. -/
noncomputable def ramp (θ s b : ℝ) : ℝ := clamp01 ((b - θ + s) / s)

theorem abs_ramp_sub_le {θ s : ℝ} (hs : 0 < s) (b b' : ℝ) :
    |ramp θ s b - ramp θ s b'| ≤ 1 / s * |b - b'| := by
  refine (abs_clamp01_sub_le _ _).trans (le_of_eq ?_)
  rw [show (b - θ + s) / s - (b' - θ + s) / s = (b - b') / s by ring, abs_div, abs_of_pos hs]
  ring

theorem ramp_of_le {θ s b : ℝ} (hs : 0 < s) (h : θ ≤ b) : ramp θ s b = 1 :=
  clamp01_of_one_le ((le_div_iff₀ hs).2 (by linarith))

theorem ramp_of_le' {θ s b : ℝ} (hs : 0 < s) (h : b ≤ θ - s) : ramp θ s b = 0 :=
  clamp01_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le)

/-- On the cube: `|χ_s(b) - 𝟙{θ ≤ b}| ≤ tent_s(b)`. -/
theorem abs_ramp_sub_bitVal_le {θ s : ℝ} (hs : 0 < s) (b : ℝ) :
    |ramp θ s b - bitVal (decide (θ ≤ b))| ≤ tent θ s b := by
  rcases le_or_gt θ b with h | h
  · rw [ramp_of_le hs h, decide_eq_true h]
    simp [bitVal, tent_nonneg]
  rcases le_or_gt b (θ - s) with h' | h'
  · rw [ramp_of_le' hs h', decide_eq_false (not_le.2 h)]
    simp [bitVal, tent_nonneg]
  · rw [decide_eq_false (not_le.2 h), tent_eq_one hs (by rw [abs_le]; constructor <;> linarith)]
    simp only [bitVal, Bool.false_eq_true, ite_false, sub_zero]
    rw [ramp, abs_of_nonneg (clamp01_nonneg _)]
    exact clamp01_le_one _

/-- On Gaussian space: `|𝟙{θ ≤ b} - χ_s(b)| ≤ 𝟙{θ - s ≤ b ≤ θ}`. -/
theorem abs_bitVal_sub_ramp_le {θ s : ℝ} (hs : 0 < s) (b : ℝ) :
    |bitVal (decide (θ ≤ b)) - ramp θ s b| ≤ (Icc (θ - s) θ).indicator 1 b := by
  rcases le_or_gt θ b with h | h
  · rw [ramp_of_le hs h, decide_eq_true h]
    simp only [bitVal, ite_true, sub_self, abs_zero]
    exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  rcases le_or_gt b (θ - s) with h' | h'
  · rw [ramp_of_le' hs h', decide_eq_false (not_le.2 h)]
    simp only [bitVal, Bool.false_eq_true, ite_false, sub_zero, abs_zero]
    exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  · rw [decide_eq_false (not_le.2 h), indicator_of_mem (by constructor <;> linarith)]
    simp only [bitVal, Bool.false_eq_true, ite_false, zero_sub, abs_neg, Pi.one_apply]
    rw [ramp, abs_of_nonneg (clamp01_nonneg _)]
    exact clamp01_le_one _

theorem halfInd_eq (w : Gs R) (θ : ℝ) (G : Gs R) :
    halfInd w θ G = bitVal (decide (θ ≤ ⟪w, G⟫)) := by
  unfold halfInd bitVal
  by_cases h : θ ≤ ⟪w, G⟫
  · rw [indicator_of_mem (show G ∈ {x | θ ≤ ⟪w, x⟫} from h), decide_eq_true h]; rfl
  · rw [indicator_of_notMem (show G ∉ {x | θ ≤ ⟪w, x⟫} from h), decide_eq_false h]; rfl

/-- `E_γ φ(⟨w, G⟩) ≤ (b - a)/√(2π)` for `0 ≤ φ ≤ 𝟙_{[a, b]}`. -/
theorem integral_comp_inner_le {w : Gs R} (hw : ‖w‖ = 1) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {a b : ℝ} (hab : a ≤ b) (h0 : ∀ y, 0 ≤ φ y) (h1 : ∀ y, φ y ≤ (Icc a b).indicator 1 y) :
    ∫ G, φ ⟪w, G⟫ ∂gm R ≤ (b - a) / √(2 * π) := by
  rw [integral_comp_inner hw hφ.aestronglyMeasurable]
  have hint : Integrable ((Icc a b).indicator (1 : ℝ → ℝ)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  calc ∫ y, φ y ∂gaussianReal 0 1 ≤ ∫ y, (Icc a b).indicator 1 y ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (ae_of_all _ h0) hint (ae_of_all _ h1)
    _ = (gaussianReal 0 1).real (Icc a b) := integral_indicator_one measurableSet_Icc
    _ ≤ (b - a) / √(2 * π) := gaussianReal_Icc_le hab

/-- The test function `Ψ_s(a, b) = |a - χ_s(b)| + tent_s(b)`. -/
noncomputable def testFn (θ s a b : ℝ) : ℝ := |a - ramp θ s b| + tent θ s b

theorem lipPair_testFn {θ s : ℝ} (hs : 0 < s) : LipPair (testFn θ s) (max 1 (2 / s)) := by
  intro a b a' b'
  have h1 := abs_ramp_sub_le (θ := θ) hs b b'
  have h2 := abs_tent_sub_le (θ := θ) hs b b'
  have h3 : |(|a - ramp θ s b|) - (|a' - ramp θ s b'|)| ≤
      |a - a'| + |ramp θ s b - ramp θ s b'| := by
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [show a - ramp θ s b - (a' - ramp θ s b') = (a - a') - (ramp θ s b - ramp θ s b') by ring]
    exact abs_sub _ _
  have hK1 : 1 ≤ max 1 (2 / s) := le_max_left _ _
  have hK2 : 2 / s ≤ max 1 (2 / s) := le_max_right _ _
  unfold testFn
  calc |(|a - ramp θ s b|) + tent θ s b - (|a' - ramp θ s b'| + tent θ s b')|
      ≤ |(|a - ramp θ s b|) - (|a' - ramp θ s b'|)| + |tent θ s b - tent θ s b'| := by
        rw [show |a - ramp θ s b| + tent θ s b - (|a' - ramp θ s b'| + tent θ s b') =
          (|a - ramp θ s b| - |a' - ramp θ s b'|) + (tent θ s b - tent θ s b') by ring]
        exact abs_add_le _ _
    _ ≤ |a - a'| + 2 / s * |b - b'| := by
        have : 1 / s * |b - b'| + 1 / s * |b - b'| = 2 / s * |b - b'| := by ring
        linarith
    _ ≤ max 1 (2 / s) * |a - a'| + max 1 (2 / s) * |b - b'| := by
        gcongr
        · exact le_mul_of_one_le_left (abs_nonneg _) hK1
    _ = max 1 (2 / s) * (|a - a'| + |b - b'|) := by ring

/-- The Gaussian side: `E_γ Ψ_s(P, ⟨w, G⟩) ≤ E_γ |P - H| + 2s`. -/
theorem integral_testFn_le {w : Gs R} (hw : ‖w‖ = 1) (θ : ℝ) {s : ℝ} (hs : 0 < s)
    (c : Cube (Fin R) → ℝ) :
    ∫ G, testFn θ s (mlEval c G) (∑ i, w i * G i) ∂gm R ≤
      ∫ G, |mlEval c G - halfInd w θ G| ∂gm R + 2 * s := by
  simp_rw [← inner_eq_sum]
  have hmeasH : MeasurableSet {x : Gs R | θ ≤ ⟪w, x⟫} :=
    measurableSet_le measurable_const (by fun_prop)
  have hHint : Integrable (halfInd w θ) (gm R) := (integrable_const (1 : ℝ)).indicator hmeasH
  have hPint : Integrable (fun G : Gs R ↦ mlEval c G) (gm R) :=
    (memLp_mlEval (R := R) c 1 (by simp)).integrable le_rfl
  have hi1 : Integrable (fun G : Gs R ↦ |mlEval c G - halfInd w θ G|) (gm R) :=
    (hPint.sub hHint).abs
  have hmI : Measurable ((Icc (θ - s) θ).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Icc
  have hi2 : Integrable (fun G : Gs R ↦ (Icc (θ - s) θ).indicator (1 : ℝ → ℝ) ⟪w, G⟫) (gm R) := by
    refine (integrable_const (1 : ℝ)).mono' (hmI.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun G ↦ ?_)
    rw [Real.norm_eq_abs]
    by_cases h : ⟪w, G⟫ ∈ Icc (θ - s) θ
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  have htc : Continuous (tent θ s) := by unfold tent clamp01; fun_prop
  have hi3 : Integrable (fun G : Gs R ↦ tent θ s ⟪w, G⟫) (gm R) := by
    refine (integrable_const (1 : ℝ)).mono' (htc.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun G ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg _ _ _)]
    exact tent_le_one _ _ _
  have hpt : ∀ G : Gs R, testFn θ s (mlEval c G) ⟪w, G⟫ ≤ |mlEval c G - halfInd w θ G| +
      (Icc (θ - s) θ).indicator (1 : ℝ → ℝ) ⟪w, G⟫ + tent θ s ⟪w, G⟫ := by
    intro G
    unfold testFn
    have := abs_bitVal_sub_ramp_le (θ := θ) hs ⟪w, G⟫
    rw [← halfInd_eq] at this
    have := abs_sub_le (mlEval c G) (halfInd w θ G) (ramp θ s ⟪w, G⟫)
    linarith
  have hmono : ∫ G, testFn θ s (mlEval c G) ⟪w, G⟫ ∂gm R ≤
      ∫ G, (|mlEval c G - halfInd w θ G| + (Icc (θ - s) θ).indicator (1 : ℝ → ℝ) ⟪w, G⟫ +
        tent θ s ⟪w, G⟫) ∂gm R :=
    integral_mono_of_nonneg
      (ae_of_all _ fun G ↦ add_nonneg (abs_nonneg _) (tent_nonneg θ s ⟪w, G⟫))
      ((hi1.add hi2).add hi3) (ae_of_all _ hpt)
  have hsplit : ∫ G, (|mlEval c G - halfInd w θ G| + (Icc (θ - s) θ).indicator (1 : ℝ → ℝ)
      ⟪w, G⟫ + tent θ s ⟪w, G⟫) ∂gm R = ∫ G, |mlEval c G - halfInd w θ G| ∂gm R +
      ∫ G, (Icc (θ - s) θ).indicator (1 : ℝ → ℝ) ⟪w, G⟫ ∂gm R + ∫ G, tent θ s ⟪w, G⟫ ∂gm R := by
    rw [integral_add, integral_add]
    · exact hi1
    · exact hi2
    · exact hi1.add hi2
    · exact hi3
  rw [hsplit] at hmono
  have hb2 := integral_comp_inner_le (R := R) hw hmI (by linarith : θ - s ≤ θ)
    (fun y ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) y) (fun y ↦ le_rfl)
  have hb3 := integral_comp_inner_le (R := R) hw htc.measurable
    (by linarith : θ - 2 * s ≤ θ + 2 * s) (tent_nonneg θ s) (tent_le_indicator hs)
  have hpi : 5 / 2 ≤ √(2 * π) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_d2])
  have hsq : 0 < √(2 * π) := by positivity
  have h5 : (θ - (θ - s)) / √(2 * π) + (θ + 2 * s - (θ - 2 * s)) / √(2 * π) ≤ 2 * s := by
    rw [← add_div, div_le_iff₀ hsq]
    nlinarith
  linarith

end BackToCube

open BackToCube NoiseLTF in
/-- **The cube versus Gaussian space, for a regular LTF**: for `r ∈ (0, 1)`, `s, ε > 0` and
influences small enough, `E_cube |T_r u - L| ≤ E_γ |P_{u,r} - H| + 2s + ε` with
`L = 𝟙{θ ≤ ⟨w, σ(x)⟩}` and `H = 𝟙{θ ≤ ⟨w, G⟩}`. Proof: `|T_r u - L| ≤ Ψ_s(T_r u, ℓ)` with
`Ψ_s(a, b) = |a - χ_s(b)| + tent_s(b)`, `χ_s(b) = clamp01((b - θ + s)/s)`,
`tent_s(b) = clamp01(2 - |b - θ|/s)` (Lipschitz with constant `max 1 (2/s)`); `invariance` with
`c = û`, `e = linC (w / r)` (`smoothC_linC`, `inflC_linC`, `sum_linC_sq`); on Gaussian space
`Ψ_s(P, ℓ) ≤ |P - H| + 𝟙{θ - s ≤ ℓ ≤ θ} + tent_s(ℓ)` with `ℓ = ⟨w, G⟩ ∼ N(0,1)`
(`Gaussian.map_inner_stdGaussian`), whose last two terms have mass `≤ 5s/√(2π) ≤ 2s`. -/
theorem cube_ltf_le_gauss {r s ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hε : 0 < ε) :
    ∃ τ > 0, ∀ (R : ℕ) (u : Cube (Fin R) → ℝ), (∀ x, 0 ≤ u x ∧ u x ≤ 1) →
      (∀ i, influence i u ≤ τ) → ∀ (w : Gs R) (θ : ℝ), ‖w‖ = 1 → (∀ i, w i ^ 2 ≤ τ) →
        (𝔼 x, |noise r u x - bitVal (decide (θ ≤ ∑ i, w i * bitSign (x i)))|) ≤
          ∫ G, |gaussExt r u G - halfInd w θ G| ∂gm R + 2 * s + ε := by
  obtain ⟨τ₀, hτ₀, hinv⟩ := invariance (M := max 1 (1 / r ^ 2)) (K := max 1 (2 / s)) hr0 hr1 hε
  refine ⟨τ₀ * r ^ 2, by positivity, fun R u h01 hinf w θ hw hwτ ↦ ?_⟩
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hw2 : ∑ i, w i ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hw, one_pow]
  obtain ⟨c, hc⟩ : ∃ c, c = coefficient u := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Cube (Fin R) → ℝ, e = linC (fun i ↦ w i / r) := ⟨_, rfl⟩
  have hcs : ∑ s, c s ^ 2 ≤ max 1 (1 / r ^ 2) :=
    (hc ▸ Truncation.sum_coefficient_sq_le u h01).trans (le_max_left _ _)
  have hes : ∑ s, e s ^ 2 ≤ max 1 (1 / r ^ 2) := by
    rw [he, sum_linC_sq]
    simp_rw [div_pow, ← Finset.sum_div, hw2]
    exact le_max_right _ _
  have hcinf : ∀ i, inflC c i ≤ τ₀ := fun i ↦ by
    rw [hc, ← influence_eq_inflC]
    exact (hinf i).trans (by nlinarith)
  have heinf : ∀ i, inflC e i ≤ τ₀ := fun i ↦ by
    rw [he, inflC_linC, div_pow, div_le_iff₀ (by positivity)]
    exact hwτ i
  have h := hinv R c e hcs hes hcinf heinf _ (lipPair_testFn (θ := θ) hs)
  have hse : smoothC r e = linC (fun i ↦ w i) := by
    rw [he, smoothC_linC]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [hse, hc] at h
  simp only [mlEval_linC, mlEval_smoothC_bitVec] at h
  have hcube : (𝔼 x, |noise r u x - bitVal (decide (θ ≤ ∑ i, w i * bitSign (x i)))|) ≤
      𝔼 x, testFn θ s (noise r u x) (∑ i, w i * bitVec x i) := by
    refine Finset.expect_le_expect fun x _ ↦ ?_
    unfold testFn
    have h1 := abs_sub_le (noise r u x) (ramp θ s (∑ i, w i * bitSign (x i)))
      (bitVal (decide (θ ≤ ∑ i, w i * bitSign (x i))))
    have h2 := abs_ramp_sub_bitVal_le (θ := θ) hs (∑ i, w i * bitSign (x i))
    exact h1.trans (by unfold bitVec; linarith)
  have hgauss := integral_testFn_le hw θ hs (smoothC r (coefficient u))
  have hgE : ∫ G, |mlEval (smoothC r (coefficient u)) G - halfInd w θ G| ∂gm R =
      ∫ G, |gaussExt r u G - halfInd w θ G| ∂gm R := rfl
  linarith [(abs_le.1 h).2]

end BGHKLMM26.RobustMIS
