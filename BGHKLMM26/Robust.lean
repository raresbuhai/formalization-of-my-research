module

public import BGHKLMM26.Factor
public import Mathlib.Probability.Moments.Variance

/-!
# Robustness of the roundings

A machine computes the arguments of the rounding's signs only approximately. A sign can differ
from the ideal one only if the ideal argument is close to `0`, which is unlikely: the argument is
`⟨vᵢ, g⟩` plus a function of the part of `g` orthogonal to `vᵢ`, and `⟨vᵢ, g⟩` is a standard
Gaussian independent of that part (`BGHKLMM26.Robust.measureReal_abs_inner_add_le`). Outside a
Gaussian tail (`BGHKLMM26.Robust.measureReal_le_abs_le`) the approximations are accurate. A
different output costs at most the total weight (`BGHKLMM26.Robust.satWeight_ge`).
-/

@[expose] public section

namespace BGHKLMM26.Robust

open MeasureTheory ProbabilityTheory Real Gaussian Set
open scoped RealInnerProductSpace

/-- **Anti-concentration**: for a unit vector `w` and `F` invariant along `w`,
`P(|⟨w, g⟩ + F(g)| ≤ δ) ≤ δ`. -/
theorem measureReal_abs_inner_add_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {w : E} (hw : ‖w‖ = 1)
    {F : E → ℝ} (hF : Measurable F) (hinv : ∀ y (c : ℝ), F (y + c • w) = F y) {δ : ℝ}
    (hδ : 0 ≤ δ) : (stdGaussian E).real {g | |⟪w, g⟫ + F g| ≤ δ} ≤ δ := by
  set S := {g : E | |⟪w, g⟫ + F g| ≤ δ} with hSdef
  have hS : MeasurableSet S := measurableSet_le (f := fun g ↦ |⟪w, g⟫ + F g|) (by fun_prop)
    measurable_const
  have hb : ∀ g, |S.indicator (1 : E → ℝ) g| ≤ 1 := by
    intro g; simp only [indicator]; split_ifs <;> simp
  rw [← integral_indicator_one hS, integral_split hw (measurable_one.indicator hS) hb]
  have hin : ∀ g : E, ∫ z, S.indicator (1 : E → ℝ) (perp w g + z • w) ∂gaussianReal 0 1 =
      (gaussianReal 0 1).real {z | |z - -F (perp w g)| ≤ δ} := by
    intro g
    rw [← integral_indicator_one (measurableSet_le (by fun_prop) measurable_const)]
    congr 1
    funext z
    have hz : ⟪w, perp w g + z • w⟫ = z := by
      rw [inner_add_right, inner_perp hw, inner_smul_right, real_inner_self_eq_norm_sq, hw]
      ring
    simp only [hSdef, indicator, mem_ofPred_eq, hz, hinv, sub_neg_eq_add, Pi.one_apply]
  simp_rw [hin]
  calc ∫ g, (gaussianReal 0 1).real {z | |z - -F (perp w g)| ≤ δ} ∂stdGaussian E
      ≤ ∫ _g, δ ∂stdGaussian E := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ measureReal_nonneg)
          (integrable_const _) (ae_of_all _ fun g ↦ gaussianReal_abs_sub_le _ hδ)
    _ = δ := by simp

/-- **Chebyshev's bound** for a standard Gaussian: `P(|X| ≥ R) ≤ 1/R²`. -/
theorem measureReal_le_abs_le {R : ℝ} (hR : 0 < R) :
    (gaussianReal 0 1).real {x | R ≤ |x|} ≤ 1 / R ^ 2 := by
  have h := meas_ge_le_variance_div_sq (μ := gaussianReal 0 1) (X := id)
    (memLp_id_gaussianReal 2) hR
  simp only [id, integral_id_gaussianReal, sub_zero, variance_id_gaussianReal,
    NNReal.coe_one] at h
  rw [measureReal_def]
  calc ((gaussianReal 0 1) {x | R ≤ |x|}).toReal ≤ (ENNReal.ofReal (1 / R ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = 1 / R ^ 2 := ENNReal.toReal_ofReal (by positivity)

/-- **A different output costs at most the total weight**: if `y` agrees with `x` on the variables
`i < n`, the satisfied weights agree; otherwise `y` loses at most `W`. -/
theorem satWeight_ge {I : Instance} (hI : Valid I) (x y : ℕ → Bool) :
    satWeight I x - totalWeight I * (if ∀ i < I.1, x i = y i then 0 else 1) ≤ satWeight I y := by
  have hnn : ∀ z : ℕ → Bool, 0 ≤ satWeight I z := fun z ↦ List.sum_nonneg fun a ha ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    split_ifs
    · exact_mod_cast (hI.1 c hc).2.2
    · exact le_rfl
  have hle : ∀ z : ℕ → Bool, satWeight I z ≤ totalWeight I := fun z ↦ by
    unfold satWeight totalWeight
    refine List.sum_le_sum fun c hc ↦ ?_
    split_ifs
    · exact le_rfl
    · exact_mod_cast (hI.1 c hc).2.2
  split_ifs with h
  · have : satWeight I x = satWeight I y := by
      unfold satWeight
      congr 1
      refine List.map_congr_left fun c hc ↦ ?_
      obtain ⟨hij, hj, -⟩ := hI.1 c hc
      rw [h _ (hij.trans hj), h _ hj]
    linarith
  · have := hnn y
    have := hle x
    linarith

end BGHKLMM26.Robust
