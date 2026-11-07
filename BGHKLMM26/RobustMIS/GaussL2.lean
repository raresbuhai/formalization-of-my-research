module

public import BGHKLMM26.RobustMIS.MultilinearGauss
public import Background.GaussianCalculus

/-!
# `L²` continuity of Gaussian quantities

Coordinates of the first Hermite vector, and the bounds `|F̂ᵢ - Ĝᵢ| ≤ ‖F - G‖₂`,
`|E F - E G| ≤ ‖F - G‖₂`, `|Stab_t F - Stab_t G| ≤ ‖F - G‖₂ (‖F‖₂ + ‖G‖₂)` (Cauchy–Schwarz; `X` and
`t X + √(1-t²) Z` are both standard Gaussian for `|t| ≤ 1`).

Material: `Gaussian.sq_integral_mul_le`, `Gaussian.map_add_smul_stdGaussian`,
`Gaussian.integral_stdGaussian_prod` (`Background/GaussianCalculus.lean`);
`ContinuousLinearMap.integral_comp_comm` (for `hermite1_apply`).

All statements are proved. Helpers (namespace `GaussL2`): `abs_integral_mul_le`
(`|∫ f g| ≤ ‖f‖₂ ‖g‖₂`), `abs_sub_integral_mul_le`, `integral_coord_sq` (`E Gᵢ² = 1`) and
`memLp_coord` (from `MultilinearGauss.lean`), `map_fst_gm`, `map_rot_gm`, `memLp_comp_of_map`,
`integral_comp_of_map`, and `gStab_eq_prod` (`Stab_t F` as one integral over `γ ⊗ γ`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

namespace GaussL2

/-- Cauchy–Schwarz, `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`. -/
theorem abs_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (integral_nonneg fun x ↦ sq_nonneg _)]
  exact Real.sqrt_le_sqrt (Gaussian.sq_integral_mul_le hf hg)

theorem integral_coord_sq {n : ℕ} (i : Fin n) : ∫ x, x i ^ 2 ∂gm n = 1 := by
  have h := integral_mlEval_mul_coord (MultilinearGauss.indC (Multilinear.single i)) i
  simp_rw [MultilinearGauss.mlEval_indC, MultilinearGauss.mono_single,
    MultilinearGauss.indC] at h
  simpa [sq] using h

theorem memLp_coord {n : ℕ} (i : Fin n) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun x : Gs n ↦ x i) p (gm n) := by
  have h := memLp_mlEval (MultilinearGauss.indC (Multilinear.single i)) p hp
  simp_rw [MultilinearGauss.mlEval_indC, MultilinearGauss.mono_single] at h
  exact h

variable {n : ℕ}

theorem map_fst_gm : ((gm n).prod (gm n)).map Prod.fst = gm n := by
  rw [Measure.map_fst_prod]
  simp

theorem map_rot_gm {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ((gm n).prod (gm n)).map (fun p ↦ t • p.1 + √(1 - t ^ 2) • p.2) = gm n := by
  have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  exact Gaussian.map_add_smul_stdGaussian (by rw [Real.sq_sqrt h1]; ring)

theorem memLp_comp_of_map {α : Type*} [MeasurableSpace α] {μ : Measure α} {L : α → Gs n}
    (hL : Measurable L) (h : μ.map L = gm n) {F : Gs n → ℝ} (hF : MemLp F 2 (gm n)) :
    MemLp (fun a ↦ F (L a)) 2 μ := by
  rw [← h] at hF
  exact (memLp_map_measure_iff hF.aestronglyMeasurable hL.aemeasurable).1 hF

theorem integral_comp_of_map {α : Type*} [MeasurableSpace α] {μ : Measure α} {L : α → Gs n}
    (hL : Measurable L) (h : μ.map L = gm n) {Φ : Gs n → ℝ}
    (hΦ : AEStronglyMeasurable Φ (gm n)) : ∫ a, Φ (L a) ∂μ = ∫ x, Φ x ∂gm n := by
  rw [← h] at hΦ ⊢
  rw [integral_map hL.aemeasurable hΦ]

theorem measurable_rot (t : ℝ) :
    Measurable (fun p : Gs n × Gs n ↦ t • p.1 + √(1 - t ^ 2) • p.2) := by
  fun_prop

theorem gStab_eq_prod {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F : Gs n → ℝ} (hF : MemLp F 2 (gm n)) :
    gStab t F = ∫ p, F p.1 * F (t • p.1 + √(1 - t ^ 2) • p.2) ∂(gm n).prod (gm n) := by
  unfold gStab
  rw [integral_prod]
  exact (memLp_comp_of_map measurable_fst map_fst_gm hF).integrable_mul
    (memLp_comp_of_map (measurable_rot t) (map_rot_gm ht) hF)

/-- `|E[f₁ f₂] - E[g₁ g₂]| ≤ ‖f₁ - g₁‖ ‖f₂‖ + ‖g₁‖ ‖f₂ - g₂‖`. -/
theorem abs_sub_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ g₁ f₂ g₂ : α → ℝ} (hf₁ : MemLp f₁ 2 μ) (hg₁ : MemLp g₁ 2 μ) (hf₂ : MemLp f₂ 2 μ)
    (hg₂ : MemLp g₂ 2 μ) :
    |∫ a, f₁ a * f₂ a ∂μ - ∫ a, g₁ a * g₂ a ∂μ| ≤
      √(∫ a, (f₁ a - g₁ a) ^ 2 ∂μ) * √(∫ a, f₂ a ^ 2 ∂μ) +
        √(∫ a, g₁ a ^ 2 ∂μ) * √(∫ a, (f₂ a - g₂ a) ^ 2 ∂μ) := by
  have hd₁ : MemLp (fun a ↦ f₁ a - g₁ a) 2 μ := hf₁.sub hg₁
  have hd₂ : MemLp (fun a ↦ f₂ a - g₂ a) 2 μ := hf₂.sub hg₂
  have i1 : Integrable (fun a ↦ f₁ a * f₂ a) μ := hf₁.integrable_mul hf₂
  have i2 : Integrable (fun a ↦ g₁ a * g₂ a) μ := hg₁.integrable_mul hg₂
  have i3 : Integrable (fun a ↦ (f₁ a - g₁ a) * f₂ a) μ := hd₁.integrable_mul hf₂
  have i4 : Integrable (fun a ↦ g₁ a * (f₂ a - g₂ a)) μ := hg₁.integrable_mul hd₂
  have e : ∫ a, f₁ a * f₂ a ∂μ - ∫ a, g₁ a * g₂ a ∂μ =
      ∫ a, (f₁ a - g₁ a) * f₂ a ∂μ + ∫ a, g₁ a * (f₂ a - g₂ a) ∂μ := by
    rw [← integral_sub i1 i2, ← integral_add i3 i4]
    congr 1
    funext a
    ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (abs_integral_mul_le hd₁ hf₂)
    (abs_integral_mul_le hg₁ hd₂))

end GaussL2

open GaussL2

theorem hermite1_apply {n : ℕ} (F : Gs n → ℝ) (hF : MemLp F 2 (gm n)) (i : Fin n) :
    hermite1 F i = ∫ x, F x * x i ∂gm n := by
  have hint : Integrable (fun x ↦ F x • x) (gm n) :=
    memLp_one_iff_integrable.1 (hF.smul (IsGaussian.memLp_two_id (μ := gm n)))
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
  simp only [EuclideanSpace.proj, PiLp.proj_apply, map_smul, smul_eq_mul] at h
  unfold hermite1
  rw [← h]

theorem abs_hermite1_sub_le {n : ℕ} (F G : Gs n → ℝ) (hF : MemLp F 2 (gm n))
    (hG : MemLp G 2 (gm n)) (i : Fin n) :
    |hermite1 F i - hermite1 G i| ≤ √(∫ x, (F x - G x) ^ 2 ∂gm n) := by
  have hc := memLp_coord i 2 (by simp)
  have h1 : Integrable (fun x : Gs n ↦ F x * x i) (gm n) := hF.integrable_mul hc
  have h2 : Integrable (fun x : Gs n ↦ G x * x i) (gm n) := hG.integrable_mul hc
  rw [hermite1_apply F hF, hermite1_apply G hG, ← integral_sub h1 h2]
  simp_rw [← sub_mul]
  have := abs_integral_mul_le (hF.sub hG) hc
  rwa [integral_coord_sq, Real.sqrt_one, mul_one] at this

theorem abs_gMean_sub_le {n : ℕ} (F G : Gs n → ℝ) (hF : MemLp F 2 (gm n))
    (hG : MemLp G 2 (gm n)) :
    |gMean F - gMean G| ≤ √(∫ x, (F x - G x) ^ 2 ∂gm n) := by
  unfold gMean
  rw [← integral_sub (hF.integrable one_le_two) (hG.integrable one_le_two)]
  have := abs_integral_mul_le (hF.sub hG) (memLp_const (1 : ℝ) (μ := gm n) (p := 2))
  simpa using this

theorem abs_gStab_sub_le {n : ℕ} {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (F G : Gs n → ℝ)
    (hF : MemLp F 2 (gm n)) (hG : MemLp G 2 (gm n)) :
    |gStab t F - gStab t G| ≤
      √(∫ x, (F x - G x) ^ 2 ∂gm n) * (√(∫ x, F x ^ 2 ∂gm n) + √(∫ x, G x ^ 2 ∂gm n)) := by
  rw [gStab_eq_prod ht hF, gStab_eq_prod ht hG]
  have hL := measurable_rot (n := n) t
  have hmap := map_rot_gm (n := n) ht
  have key := abs_sub_integral_mul_le (memLp_comp_of_map measurable_fst map_fst_gm hF)
    (memLp_comp_of_map measurable_fst map_fst_gm hG) (memLp_comp_of_map hL hmap hF)
    (memLp_comp_of_map hL hmap hG)
  have hD : AEStronglyMeasurable (fun x ↦ (F x - G x) ^ 2) (gm n) :=
    (hF.sub hG).aestronglyMeasurable.pow 2
  rw [integral_comp_of_map (Φ := fun x ↦ (F x - G x) ^ 2) measurable_fst map_fst_gm hD,
    integral_comp_of_map (Φ := fun x ↦ F x ^ 2) hL hmap (hF.aestronglyMeasurable.pow 2),
    integral_comp_of_map (Φ := fun x ↦ G x ^ 2) measurable_fst map_fst_gm
      (hG.aestronglyMeasurable.pow 2),
    integral_comp_of_map (Φ := fun x ↦ (F x - G x) ^ 2) hL hmap hD] at key
  linarith

end BGHKLMM26.RobustMIS
