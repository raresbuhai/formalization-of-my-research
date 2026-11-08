module

public import BHJK25.Spectral.Basic
public import BHJK25.Spectral.Legendre.Expansion
public import Mathlib.RingTheory.Polynomial.ShiftedLegendre

/-!
# A univariate inequality from Legendre polynomials

For a polynomial `p` of degree at most `d` and `0 ≤ t ≤ 1 / (2 d (d + 1))`,
`p(t) - E_{μ_γ} p ≤ (1/√(1 - γ) + 10 d³ t / √γ) √(Var_{μ_γ} p)` [BHJK25, proof of Lemma 3.10]:
`p(0)` is controlled by the atom of `μ_γ` at `0`, and `p(t) - p(0)` by the `L²` norm of `p` on
`[-1, 0]`, through the expansion of `p` in shifted Legendre polynomials
(`BHJK25.Spectral.LegendreAux.abs_eval_neg_sub_eval_zero_le`).
-/

@[expose] public section

namespace BHJK25.Spectral

open MeasureTheory ProbabilityTheory Polynomial

namespace LegendreAux

theorem integrable_eigLaw (γ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f (eigLaw γ) :=
  ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top).add_measure
    (hf.integrableOn_Icc.smul_measure ENNReal.ofReal_ne_top)

/-- The integral of a continuous function against `μ_γ`. -/
theorem integral_eigLaw {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(eigLaw γ) = (1 - γ) * f 0 + γ * ∫ x in (-1 : ℝ)..0, f x := by
  rw [eigLaw, integral_add_measure
      ((integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)
      (hf.integrableOn_Icc.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hγ0, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), smul_eq_mul, smul_eq_mul]

/-- The `L²[-1, 0]` norm of `H` is the `L²[0, 1]` norm of `x ↦ H(-x)`. -/
theorem ip_comp_neg (H : ℝ[X]) :
    ip (H.comp (-X)) (H.comp (-X)) = ∫ x in (-1 : ℝ)..0, H.eval x ^ 2 := by
  rw [ip, ← neg_zero, ← intervalIntegral.integral_comp_neg]
  simp [sq]

end LegendreAux

open LegendreAux in
/-- [BHJK25, proof of Lemma 3.10] For `0 < γ < 1`, `0 ≤ t ≤ 1 / (2d(d + 1))` and a polynomial `p`
of degree at most `d`, `p(t) - E_{μ_γ} p ≤ (1/√(1 - γ) + 10 d³ t / √γ) √(Var_{μ_γ} p)`. -/
theorem legendre_bound {γ t : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) {d : ℕ} (ht0 : 0 ≤ t)
    (ht : t * (2 * d * (d + 1)) ≤ 1) (p : ℝ[X]) (hp : p.natDegree ≤ d) :
    p.eval t - ∫ x, p.eval x ∂(eigLaw γ) ≤
      (1 / √(1 - γ) + 10 * d ^ 3 * t / √γ) * √(variance (fun x ↦ p.eval x) (eigLaw γ)) := by
  set c := ∫ x, p.eval x ∂(eigLaw γ)
  set V := variance (fun x ↦ p.eval x) (eigLaw γ) with hVdef
  set H : ℝ[X] := p - C c
  set B := ∫ x in (-1 : ℝ)..0, H.eval x ^ 2
  have hH : ∀ x, H.eval x = p.eval x - c := fun x ↦ by simp [H]
  have hV : V = (1 - γ) * (p.eval 0 - c) ^ 2 + γ * B := by
    rw [hVdef, variance_eq_integral p.continuous.aemeasurable,
      integral_eigLaw hγ0.le hγ1.le (by fun_prop)]
    simp only [B, hH]
    rfl
  have hB0 : 0 ≤ B := intervalIntegral.integral_nonneg (by norm_num) fun x _ ↦ sq_nonneg _
  have hγ1' : 0 < 1 - γ := by linarith
  -- the atom at `0`
  have hA : |p.eval 0 - c| ≤ √V / √(1 - γ) := by
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_div' _ hγ1'.le]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ hγ1']
    nlinarith [mul_nonneg hγ0.le hB0]
  have hBV : √B ≤ √V / √γ := by
    rw [← Real.sqrt_div' _ hγ0.le]
    refine Real.sqrt_le_sqrt ?_
    rw [le_div_iff₀ hγ0]
    nlinarith [mul_nonneg hγ1'.le (sq_nonneg (p.eval 0 - c))]
  -- the difference `p(t) - p(0)`
  have hdiff : |p.eval t - p.eval 0| ≤ 10 * d ^ 3 * t * √B := by
    have hdeg : (H.comp (-X)).natDegree ≤ d := by
      refine natDegree_comp_le.trans ?_
      rw [natDegree_neg, natDegree_X, mul_one, natDegree_sub_C]
      exact hp
    have := abs_eval_neg_sub_eval_zero_le (H.comp (-X)) hdeg ht0 ht
    rw [ip_comp_neg] at this
    simpa [hH, B] using this
  have hd0 : 0 ≤ 10 * (d : ℝ) ^ 3 * t := by positivity
  calc p.eval t - c = (p.eval 0 - c) + (p.eval t - p.eval 0) := by ring
    _ ≤ |p.eval 0 - c| + |p.eval t - p.eval 0| := add_le_add (le_abs_self _) (le_abs_self _)
    _ ≤ √V / √(1 - γ) + 10 * d ^ 3 * t * (√V / √γ) :=
        add_le_add hA (hdiff.trans (mul_le_mul_of_nonneg_left hBV hd0))
    _ = (1 / √(1 - γ) + 10 * d ^ 3 * t / √γ) * √V := by ring

end BHJK25.Spectral
