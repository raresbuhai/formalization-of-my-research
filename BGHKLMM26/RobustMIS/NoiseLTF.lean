module

public import BGHKLMM26.RobustMIS.Invariance
public import BGHKLMM26.RobustMIS.Normal
public import BGHKLMM26.Hardness.LTF

/-!
# Smoothing removal

* `smoothing_removal`: `‖u - L‖₁ ≤ ‖T_r u - L‖₁ + 2‖L - T_r L‖₁` for `u : {0,1}^R → [0,1]` and a
  Boolean `L` (from the paper's proof of Lemma `smoothing-removal`).
* `regular_ltf_noise`: `‖L - T_r L‖₁ ≤ 4(1 - r)^{1/3} + o_{μ↓0}(1)` for an LTF with unit normal and
  `max wᵢ² ≤ μ`. This replaces Peres's theorem (deviation recorded in `README.md`).

Auxiliary material (namespace `NoiseLTF`), also used by `BackToCube` and `Transfer`: the clamp
`clamp01` and the tent `NoiseLTF.tent θ s b = clamp01 (2 - |b - θ|/s)` (Lipschitz bounds), the
Gaussian mass of a tent (`NoiseLTF.integral_tent_le`, via `Gaussian.map_inner_stdGaussian` and
`gaussianReal_Icc_le`), and the anti-concentration of regular linear forms on the cube
(`NoiseLTF.anticonc`, from `invariance`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic BGHKLMM26.Hard

variable {R : ℕ}

namespace NoiseLTF

/-! ### Smoothing removal -/

theorem abs_sub_bitVal_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (c : Bool) :
    |a - bitVal c| = a + bitVal c - 2 * (a * bitVal c) := by
  rw [abs_sub_bitVal ha0 ha1]
  cases c <;> simp [bitVal]; ring

/-- Self-adjointness of `T_r`. -/
theorem expect_noise_mul (r : ℝ) (f g : Cube (Fin R) → ℝ) :
    (𝔼 x, noise r f x * g x) = 𝔼 x, f x * noise r g x := by
  rw [← walsh_inner, ← walsh_inner]
  simp_rw [coefficient_noise]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  ring

end NoiseLTF

open NoiseLTF in
/-- **Smoothing removal** (from the proof of Lemma `smoothing-removal`):
`‖u - L‖₁ ≤ ‖T_r u - L‖₁ + 2 ‖L - T_r L‖₁`. Proof: `|a - L| = a + L - 2aL` for `a ∈ [0,1]`
(`abs_sub_bitVal`, `noise_mem`), `E T_r u = E u` (`noise_mean`), and
`E[(T_r u) L] = E[u T_r L]` (self-adjointness, `walsh_inner`, `coefficient_noise`). -/
theorem smoothing_removal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (u : Cube (Fin R) → ℝ)
    (h01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1) (L : Cube (Fin R) → Bool) :
    (𝔼 x, |u x - bitVal (L x)|) ≤ (𝔼 x, |noise r u x - bitVal (L x)|) +
      2 * 𝔼 x, |bitVal (L x) - noise r (fun y ↦ bitVal (L y)) x| := by
  have hT := noise_mem (by linarith) hr1 h01
  have e1 : (𝔼 x, |u x - bitVal (L x)|) =
      𝔼 x, (u x + bitVal (L x) - 2 * (u x * bitVal (L x))) :=
    Finset.expect_congr rfl fun x _ ↦ abs_sub_bitVal_eq (h01 x).1 (h01 x).2 _
  have e2 : (𝔼 x, |noise r u x - bitVal (L x)|) =
      𝔼 x, (noise r u x + bitVal (L x) - 2 * (noise r u x * bitVal (L x))) :=
    Finset.expect_congr rfl fun x _ ↦ abs_sub_bitVal_eq (hT x).1 (hT x).2 _
  rw [e1, e2]
  simp only [Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect]
  rw [noise_mean, expect_noise_mul]
  have h3 : (𝔼 x, u x * noise r (fun y ↦ bitVal (L y)) x) - 𝔼 x, u x * bitVal (L x) ≤
      𝔼 x, |bitVal (L x) - noise r (fun y ↦ bitVal (L y)) x| := by
    rw [← Finset.expect_sub_distrib]
    refine Finset.expect_le_expect fun x _ ↦ ?_
    rw [← mul_sub]
    calc u x * (noise r (fun y ↦ bitVal (L y)) x - bitVal (L x))
        ≤ |u x * (noise r (fun y ↦ bitVal (L y)) x - bitVal (L x))| := le_abs_self _
      _ = u x * |bitVal (L x) - noise r (fun y ↦ bitVal (L y)) x| := by
          rw [abs_mul, abs_of_nonneg (h01 x).1, abs_sub_comm]
      _ ≤ 1 * |bitVal (L x) - noise r (fun y ↦ bitVal (L y)) x| :=
          mul_le_mul_of_nonneg_right (h01 x).2 (abs_nonneg _)
      _ = _ := one_mul _
  linarith

namespace NoiseLTF

/-! ### Clamps and tents -/

theorem clamp01_nonneg (a : ℝ) : 0 ≤ clamp01 a := le_max_left _ _

theorem clamp01_le_one (a : ℝ) : clamp01 a ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem clamp01_of_one_le {a : ℝ} (h : 1 ≤ a) : clamp01 a = 1 := by
  rw [clamp01, min_eq_left h, max_eq_right zero_le_one]

theorem clamp01_of_nonpos {a : ℝ} (h : a ≤ 0) : clamp01 a = 0 := by
  rw [clamp01, max_eq_left]
  exact (min_le_right _ _).trans h

theorem abs_clamp01_sub_le (a b : ℝ) : |clamp01 a - clamp01 b| ≤ |a - b| := by
  unfold clamp01
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le (by simp) ?_)
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (by simp) le_rfl)

/-- The tent `clamp01 (2 - |b - θ|/s)`: `1` on `[θ - s, θ + s]`, `0` off `(θ - 2s, θ + 2s)`. -/
noncomputable def tent (θ s b : ℝ) : ℝ := clamp01 (2 - |b - θ| / s)

theorem tent_nonneg (θ s b : ℝ) : 0 ≤ tent θ s b := clamp01_nonneg _

theorem tent_le_one (θ s b : ℝ) : tent θ s b ≤ 1 := clamp01_le_one _

theorem tent_eq_one {θ s b : ℝ} (hs : 0 < s) (h : |b - θ| ≤ s) : tent θ s b = 1 := by
  refine clamp01_of_one_le ?_
  have : |b - θ| / s ≤ 1 := (div_le_one hs).2 h
  linarith

theorem abs_tent_sub_le {θ s : ℝ} (hs : 0 < s) (b b' : ℝ) :
    |tent θ s b - tent θ s b'| ≤ 1 / s * |b - b'| := by
  refine (abs_clamp01_sub_le _ _).trans ?_
  rw [show 2 - |b - θ| / s - (2 - |b' - θ| / s) = -((|b - θ| - |b' - θ|) / s) by ring, abs_neg,
    abs_div, abs_of_pos hs, div_eq_mul_inv, one_div, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [show b - θ - (b' - θ) = b - b' by ring]

theorem tent_le_indicator {θ s : ℝ} (hs : 0 < s) (b : ℝ) :
    tent θ s b ≤ (Icc (θ - 2 * s) (θ + 2 * s)).indicator 1 b := by
  by_cases h : b ∈ Icc (θ - 2 * s) (θ + 2 * s)
  · rw [indicator_of_mem h]; exact tent_le_one _ _ _
  · rw [indicator_of_notMem h]
    refine le_of_eq (clamp01_of_nonpos ?_)
    have : 2 * s < |b - θ| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have : 2 ≤ |b - θ| / s := by rw [le_div_iff₀ hs]; linarith
    linarith

/-! ### Gaussian side -/

theorem inner_eq_sum (w G : Gs R) : ⟪w, G⟫ = ∑ i, w i * G i := by
  simp [PiLp.inner_apply, mul_comm]

/-- `E_γ φ(⟨w, G⟩) = E φ(N(0,1))` for a unit vector `w`. -/
theorem integral_comp_inner {w : Gs R} (hw : ‖w‖ = 1) {φ : ℝ → ℝ}
    (hφ : AEStronglyMeasurable φ (gaussianReal 0 1)) :
    ∫ G, φ ⟪w, G⟫ ∂gm R = ∫ y, φ y ∂gaussianReal 0 1 := by
  rw [← Gaussian.map_inner_stdGaussian hw] at hφ ⊢
  rw [integral_map (by fun_prop) hφ]

/-- The Gaussian mass of the tent: `E_γ tent(⟨w, G⟩) ≤ 4s/√(2π) ≤ 2s`. -/
theorem integral_tent_le {w : Gs R} (hw : ‖w‖ = 1) (θ : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ G, tent θ s ⟪w, G⟫ ∂gm R ≤ 2 * s := by
  have hc : Continuous (tent θ s) := by unfold tent clamp01; fun_prop
  rw [integral_comp_inner hw hc.aestronglyMeasurable]
  have hint : Integrable ((Icc (θ - 2 * s) (θ + 2 * s)).indicator (1 : ℝ → ℝ))
      (gaussianReal 0 1) := (integrable_const (1 : ℝ)).indicator measurableSet_Icc
  calc ∫ y, tent θ s y ∂gaussianReal 0 1
      ≤ ∫ y, (Icc (θ - 2 * s) (θ + 2 * s)).indicator 1 y ∂gaussianReal 0 1 :=
        integral_mono_of_nonneg (ae_of_all _ fun y ↦ tent_nonneg _ _ _) hint
          (ae_of_all _ fun y ↦ tent_le_indicator hs y)
    _ = (gaussianReal 0 1).real (Icc (θ - 2 * s) (θ + 2 * s)) :=
        integral_indicator_one measurableSet_Icc
    _ ≤ (θ + 2 * s - (θ - 2 * s)) / √(2 * π) := gaussianReal_Icc_le (by linarith)
    _ ≤ 2 * s := by
        rw [div_le_iff₀ (by positivity)]
        have h2 : 2 ≤ √(2 * π) := Real.le_sqrt_of_sq_le (by nlinarith [Real.pi_gt_three])
        nlinarith

/-- **Anti-concentration of regular linear forms** (from `invariance` at smoothing `1/2`):
`E_cube tent(⟨w, σ(x)⟩) ≤ 2s + ε` for `‖w‖ = 1`, `max wᵢ² ≤ μ` small. -/
theorem anticonc {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    ∃ μ > 0, ∀ (R : ℕ) (w : Gs R) (θ : ℝ), ‖w‖ = 1 → (∀ i, w i ^ 2 ≤ μ) →
      (𝔼 x : Cube (Fin R), tent θ s (∑ i, w i * bitSign (x i))) ≤ 2 * s + ε := by
  obtain ⟨τ, hτ, hinv⟩ := invariance (r := 1 / 2) (M := 4) (K := 1 / s) (by norm_num)
    (by norm_num) hε
  refine ⟨τ / 4, by positivity, fun R w θ hw hwμ ↦ ?_⟩
  have hw2 : ∑ i, w i ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hw, one_pow]
  have he : smoothC (1 / 2) (linC (fun i ↦ 2 * w i)) = linC (fun i ↦ w i) := by
    rw [smoothC_linC]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsum0 : ∑ s : Cube (Fin R), (0 : Cube (Fin R) → ℝ) s ^ 2 ≤ 4 := by simp
  have hsume : ∑ s, linC (fun i ↦ 2 * w i) s ^ 2 ≤ 4 := by
    rw [sum_linC_sq]
    simp_rw [mul_pow, ← Finset.mul_sum, hw2]
    norm_num
  have hinf0 : ∀ i, inflC (0 : Cube (Fin R) → ℝ) i ≤ τ := fun i ↦ by
    simp only [inflC, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sum_const_zero]
    positivity
  have hinfe : ∀ i, inflC (linC (fun i ↦ 2 * w i)) i ≤ τ := fun i ↦ by
    rw [inflC_linC]
    nlinarith [hwμ i]
  have hΨ : LipPair (fun _ b ↦ tent θ s b) (1 / s) := fun a b a' b' ↦
    (abs_tent_sub_le hs b b').trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (abs_nonneg _)) (by positivity))
  have h := hinv R 0 _ hsum0 hsume hinf0 hinfe _ hΨ
  simp only [he, mlEval_linC] at h
  have hG : ∫ G, tent θ s (∑ i, w i * G i) ∂gm R ≤ 2 * s := by
    simp_rw [← inner_eq_sum]
    exact integral_tent_le hw θ hs
  have hcube : (𝔼 x : Cube (Fin R), tent θ s (∑ i, w i * bitSign (x i))) =
      𝔼 x : Cube (Fin R), tent θ s (∑ i, w i * bitVec x i) := rfl
  rw [hcube]
  linarith [(abs_le.1 h).2]

/-! ### Chebyshev on the cube -/

/-- `T_r ℓ = r ℓ` for a linear form `ℓ`. -/
theorem noise_lin (r : ℝ) (w : Fin R → ℝ) (x : Cube (Fin R)) :
    noise r (fun y ↦ ∑ i, w i * bitSign (y i)) x = r * ∑ i, w i * bitSign (x i) := by
  have hf : (fun y : Cube (Fin R) ↦ ∑ i, w i * bitSign (y i)) =
      fun y ↦ mlEval (linC w) (bitVec y) := by
    funext y; rw [mlEval_linC]; rfl
  have hc : coefficient (fun y : Cube (Fin R) ↦ mlEval (linC w) (bitVec y)) = linC w :=
    funext (coefficient_mlEval _)
  rw [← mlEval_smoothC_bitVec, hf, hc, smoothC_linC, mlEval_linC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [Pi.smul_apply, smul_eq_mul, bitVec]
  ring

theorem expect_lin_sq (w : Fin R → ℝ) :
    (𝔼 x : Cube (Fin R), (∑ i, w i * bitSign (x i)) ^ 2) = ∑ i, w i ^ 2 := by
  have : ∀ x : Cube (Fin R), ∑ i, w i * bitSign (x i) = mlEval (linC w) (bitVec x) :=
    fun x ↦ by rw [mlEval_linC]; rfl
  simp_rw [this, expect_mlEval_sq, sum_linC_sq]

/-- `E ∑_z w(z) (ℓ(x) - ℓ(x ⊕ z))² = 2 (1 - r) ‖w‖²`. -/
theorem expect_flip_sq (r : ℝ) (w : Fin R → ℝ) :
    (𝔼 x : Cube (Fin R), ∑ z, flipWeight r z *
      ((∑ i, w i * bitSign (x i)) - ∑ i, w i * bitSign (cubeXor x z i)) ^ 2) =
        2 * (1 - r) * ∑ i, w i ^ 2 := by
  obtain ⟨g, hg⟩ : ∃ g : Cube (Fin R) → ℝ, g = fun y ↦ ∑ i, w i * bitSign (y i) := ⟨_, rfl⟩
  have hgx : ∀ x, ∑ i, w i * bitSign (x i) = g x := fun x ↦ by rw [hg]
  have hpt : ∀ x : Cube (Fin R), ∑ z, flipWeight r z * (g x - g (cubeXor x z)) ^ 2 =
      g x ^ 2 - 2 * r * g x ^ 2 + noise r (fun y ↦ g y ^ 2) x := by
    intro x
    have e : ∑ z, flipWeight r z * (g x - g (cubeXor x z)) ^ 2 =
        g x ^ 2 * ∑ z : Cube (Fin R), flipWeight r z -
          2 * g x * ∑ z, flipWeight r z * g (cubeXor x z) +
          ∑ z, flipWeight r z * g (cubeXor x z) ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      ring
    rw [e, sum_flipWeight, ← noise_eq_sum, ← noise_eq_sum (f := fun y ↦ g y ^ 2), hg, noise_lin]
    ring
  simp_rw [hgx, hpt]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, noise_mean, ← Finset.mul_expect]
  have := expect_lin_sq w
  simp_rw [hgx] at this
  rw [this]
  ring

theorem abs_bitVal_sub_le_one (p q : Bool) : |bitVal p - bitVal q| ≤ 1 := by
  cases p <;> cases q <;> simp [bitVal]

/-- Pointwise: `|L(a) - L(b)| ≤ tent_s(a) + (a - b)²/s²` for `L = 𝟙{θ ≤ ·}`. -/
theorem abs_bitVal_decide_sub_le {θ s : ℝ} (hs : 0 < s) (a b : ℝ) :
    |bitVal (decide (θ ≤ a)) - bitVal (decide (θ ≤ b))| ≤ tent θ s a + (a - b) ^ 2 / s ^ 2 := by
  have h1 := abs_bitVal_sub_le_one (decide (θ ≤ a)) (decide (θ ≤ b))
  have hq : 0 ≤ (a - b) ^ 2 / s ^ 2 := by positivity
  by_cases ha : |a - θ| ≤ s
  · rw [tent_eq_one hs ha]; linarith
  by_cases hab : s ≤ |a - b|
  · have : 1 ≤ (a - b) ^ 2 / s ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul, ← sq_abs (a - b)]
      exact pow_le_pow_left₀ hs.le hab 2
    linarith [tent_nonneg θ s a]
  · rw [not_le] at ha hab
    have e : decide (θ ≤ a) = decide (θ ≤ b) := by
      rcases le_or_gt θ a with h | h
      · rw [abs_of_nonneg (by linarith)] at ha
        have : a - b < s := (le_abs_self _).trans_lt hab
        simp only [decide_eq_decide]
        constructor <;> intro <;> linarith
      · rw [abs_of_neg (by linarith)] at ha
        have : b - a < s := (neg_le_abs (a - b)).trans_lt hab |>.trans_le' (by linarith)
        simp only [decide_eq_decide]
        constructor <;> intro <;> linarith
    rw [e, sub_self, abs_zero]
    linarith [tent_nonneg θ s a]

/-- `E|f - T_r f| ≤ E tent_s(ℓ) + E ∑_z w(z) (ℓ(x) - ℓ(x ⊕ z))² / s²` for `f = 𝟙{θ ≤ ℓ}`. -/
theorem expect_abs_sub_noise_le {r θ s : ℝ} (hr0 : -1 ≤ r) (hr1 : r ≤ 1) (hs : 0 < s)
    (ℓ : Cube (Fin R) → ℝ) :
    (𝔼 x, |bitVal (decide (θ ≤ ℓ x)) - noise r (fun y ↦ bitVal (decide (θ ≤ ℓ y))) x|) ≤
      (𝔼 x, tent θ s (ℓ x)) +
        (𝔼 x, ∑ z, flipWeight r z * (ℓ x - ℓ (cubeXor x z)) ^ 2) / s ^ 2 := by
  have hpt : ∀ x, |bitVal (decide (θ ≤ ℓ x)) - noise r (fun y ↦ bitVal (decide (θ ≤ ℓ y))) x| ≤
      tent θ s (ℓ x) + (∑ z, flipWeight r z * (ℓ x - ℓ (cubeXor x z)) ^ 2) / s ^ 2 := by
    intro x
    rw [noise_eq_sum]
    have e : bitVal (decide (θ ≤ ℓ x)) -
        ∑ z, flipWeight r z * bitVal (decide (θ ≤ ℓ (cubeXor x z))) =
        ∑ z, flipWeight r z * (bitVal (decide (θ ≤ ℓ x)) -
          bitVal (decide (θ ≤ ℓ (cubeXor x z)))) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_flipWeight, one_mul]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ z, |flipWeight r z * (bitVal (decide (θ ≤ ℓ x)) -
          bitVal (decide (θ ≤ ℓ (cubeXor x z))))|
        ≤ ∑ z, flipWeight r z * (tent θ s (ℓ x) + (ℓ x - ℓ (cubeXor x z)) ^ 2 / s ^ 2) := by
          refine Finset.sum_le_sum fun z _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (flipWeight_nonneg hr0 hr1 z)]
          exact mul_le_mul_of_nonneg_left (abs_bitVal_decide_sub_le hs _ _)
            (flipWeight_nonneg hr0 hr1 z)
      _ = tent θ s (ℓ x) + (∑ z, flipWeight r z * (ℓ x - ℓ (cubeXor x z)) ^ 2) / s ^ 2 := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_flipWeight, one_mul,
            Finset.sum_div, mul_div_assoc]
  refine (Finset.expect_le_expect fun x _ ↦ hpt x).trans (le_of_eq ?_)
  rw [Finset.expect_add_distrib, Finset.expect_div]

end NoiseLTF

open NoiseLTF in
/-- **Noise sensitivity of regular LTFs**: for `‖w‖ = 1` with `max wᵢ² ≤ μ` small,
`‖L - T_r L‖₁ ≤ 4 (1 - r)^{1/3} + ε`. Proof: `|L(x) - T_r L(x)| ≤ ∑_z w(z) |L(x) - L(x ⊕ z)|`
(`noise_eq_sum`); `|L(x) - L(y)| ≤ tent_s(ℓ(x)) + (ℓ(x) - ℓ(y))²/s²`;
`E ∑_z w(z) (ℓ(x) - ℓ(x ⊕ z))² = 2(1 - r)` (`T_r ℓ = r ℓ`); and the anti-concentration
`E tent_s(ℓ) ≤ 2s + ε` for `μ` small (`anticonc`: `invariance` at the fixed smoothing `1/2` with
`c = 0`, `e = linC (2 • w)`, and `Gaussian.map_inner_stdGaussian`); `s = (1 - r)^{1/3}`. -/
theorem regular_ltf_noise {r ε : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ μ > 0, ∀ (R : ℕ) (w : Gs R) (θ : ℝ), ‖w‖ = 1 → (∀ i, w i ^ 2 ≤ μ) →
      (𝔼 x : Cube (Fin R), |bitVal (decide (θ ≤ ∑ i, w i * bitSign (x i))) -
        noise r (fun y ↦ bitVal (decide (θ ≤ ∑ i, w i * bitSign (y i)))) x|) ≤
          4 * (1 - r) ^ (1 / 3 : ℝ) + ε := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = (1 - r) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hs : 0 < s := hs_def ▸ Real.rpow_pos_of_pos (by linarith) _
  have hs3 : s ^ 3 = 1 - r := by
    rw [hs_def, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
  obtain ⟨μ, hμ, hac⟩ := anticonc hs hε
  refine ⟨μ, hμ, fun R w θ hw hwμ ↦ ?_⟩
  rw [← hs_def]
  have hw2 : ∑ i, w i ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hw, one_pow]
  refine (expect_abs_sub_noise_le (by linarith) hr1.le hs
    (fun x ↦ ∑ i, w i * bitSign (x i))).trans ?_
  rw [expect_flip_sq r (fun i ↦ w i), hw2, mul_one]
  have h1 := hac R w θ hw hwμ
  have h2 : 2 * (1 - r) / s ^ 2 = 2 * s := by
    rw [← hs3]; field_simp
  linarith

end BGHKLMM26.RobustMIS
