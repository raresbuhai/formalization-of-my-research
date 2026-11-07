module

public import BGHKLMM26.RobustMIS.Gamma

/-!
# The quadrant function `Γ_r`: calculus

Lemma 3.3 of `eldan-proof.tex`: the conditional representation `Γ_r(a) = Λ̃(r, Ψ(a))`, the
derivatives `Γ_r' = 2Φ(κ_r Ψ)`, `Γ_r'' = 2κ_r φ(κ_r Ψ)/q`, `∂_r Γ_r = q φ(κ_r Ψ)/σ_r`, the bounds
for `r ∈ [0, 1)`, the backward equation for `J(s, a) = Γ_{(t-s)/(1-s)}(a)`; and the quadratic bound
at `1/2` (Lemma `gaussian-facts` (d) of the paper).

Proof sketch (Lemma 3.3): completing the square
`φ(x) φ((y - r x)/σ_r) = φ(y) φ((x - r y)/σ_r)`; Leibniz' rule for `∂_y Λ̃`, dominated
differentiation for `∂_r Λ̃`; the chain rule with `Ψ' = 1/q` (`hasDerivAt_Psi`); for (d),
`r'(s) = -(1 - r)/(1 - s)` and `(1 - r)/σ_r = κ_r`.

All statements are proved. Route (no differentiation under the integral sign): by exchangeability
of `corrPair r` (`Gamma.corrPair_map_swap`) and Fubini, `Γ_r(a) = 2 P(X ≤ Ψ(a), Y ≤ X) =
∫_{-∞}^{Ψ(a)} 2 φ(x) Φ(κ_r x) dx`, which TauCeti's skew-normal identity turns into the closed form
`Γ_r(a) = a - 2 T(Ψ(a), κ_r)` with Owen's `T` function (`GammaCalc.Gam_eq_owensT`). The
derivatives of `Γ` are then the chain rule applied to TauCeti's `Real.hasDerivAt_owensT_left`,
`Real.hasDerivAt_owensT_right` and `hasDerivAt_Psi`; smoothness of `J` follows from `T ∈ C²`
(`GammaCalc.contDiff_owensT`, from its partial derivatives via Mathlib's
`hasStrictFDerivAt_uncurry_coprod`), `contDiffOn_Psi` and the smoothness of `κ`. The quadratic
bound uses `0 ≤ Γ_t'' ≤ 4` on `[1/4, 3/4]` (`qf_ge_min`) and the mean value theorem twice.
Auxiliary lemmas are in the namespace `BGHKLMM26.RobustMIS.GammaCalc`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.GammaCalc

open MeasureTheory ProbabilityTheory Real Set
open Gaussian

theorem cdf_eq_Phi (x : ℝ) : cdf (gaussianReal 0 1) x = Phi x := rfl

/-- **Fubini**: `P(X ≤ y, Z ≤ α X + β) = ∫_{-∞}^y φ(x) Φ(α x + β) dx` for independent standard
Gaussians `X, Z`. -/
theorem prod_real_le_affine (y α β : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | p.1 ≤ y ∧ p.2 ≤ α * p.1 + β} = ∫ x in Iic y, npdf x * Phi (α * x + β) := by
  set S := {p : ℝ × ℝ | p.1 ≤ y ∧ p.2 ≤ α * p.1 + β} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd (by fun_prop))
  have hint : Integrable (S.indicator (fun _ ↦ (1 : ℝ)))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS]
  change ∫ p, S.indicator (fun _ ↦ (1 : ℝ)) p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  rw [integral_prod _ hint]
  have hin : ∀ x : ℝ, ∫ z, S.indicator (fun _ ↦ (1 : ℝ)) (x, z) ∂(gaussianReal 0 1) =
      (Iic y).indicator (fun x ↦ Phi (α * x + β)) x := by
    intro x
    by_cases hx : x ≤ y
    · rw [indicator_of_mem (show x ∈ Iic y from hx)]
      have : (fun z ↦ S.indicator (fun _ ↦ (1 : ℝ)) (x, z)) =
          (Iic (α * x + β)).indicator 1 := by
        funext z
        simp only [hSdef, indicator, mem_ofPred_eq, mem_Iic, hx, true_and, Pi.one_apply]
      rw [this, integral_indicator_one measurableSet_Iic, ← cdf_eq_real]
      rfl
    · rw [indicator_of_notMem (show x ∉ Iic y from hx)]
      have : (fun z ↦ S.indicator (fun _ ↦ (1 : ℝ)) (x, z)) = fun _ ↦ 0 := by
        funext z
        simp only [hSdef, indicator, mem_ofPred_eq, hx, false_and, ite_false]
      rw [this, integral_zero]
  simp_rw [hin]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have h1 : (fun x : ℝ ↦ gaussianPDFReal 0 1 x • (Iic y).indicator (fun x ↦ Phi (α * x + β)) x) =
      (Iic y).indicator (fun t ↦ npdf t * Phi (α * t + β)) := by
    funext x
    by_cases hx : x ≤ y
    · simp [indicator, hx]
    · simp [indicator, hx]
  rw [h1, integral_indicator measurableSet_Iic]

theorem sigma_pos {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) : 0 < √(1 - r ^ 2) :=
  Real.sqrt_pos.2 (by nlinarith [hr.1, hr.2])

theorem setOf_Phi_le {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (x : ℝ) : Phi x ≤ a ↔ x ≤ Psi a :=
  (Psi_le_iff ha x).symm

/-- `Γ_r(a)` as a probability for the underlying independent pair. -/
theorem Gam_eq_prod {r : ℝ} {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Gam r a = ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | p.1 ≤ Psi a ∧ r * p.1 + √(1 - r ^ 2) * p.2 ≤ Psi a} := by
  have hm := measurable_corrPairMap r
  rw [Gam, corrPair, map_measureReal_apply hm (Gamma.measurableSet_Gam a)]
  congr 1
  ext p
  simp only [mem_preimage, mem_ofPred_eq, setOf_Phi_le ha]

theorem kap_eq {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) : kap r = (1 - r) / √(1 - r ^ 2) := by
  have hσ := sigma_pos hr
  have h1 : 0 < 1 + r := by linarith [hr.1]
  have h2 : 0 < 1 - r := by linarith [hr.2]
  rw [kap, eq_div_iff hσ.ne', ← Real.sqrt_mul (div_pos h2 h1).le,
    show (1 - r) / (1 + r) * (1 - r ^ 2) = (1 - r) ^ 2 by field_simp; ring,
    Real.sqrt_sq h2.le]

theorem corrPair_diag_null {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    corrPair r {p : ℝ × ℝ | p.1 = p.2} = 0 := by
  have hm := measurable_corrPairMap r
  rw [corrPair, Measure.map_apply hm (measurableSet_eq_fun measurable_fst measurable_snd)]
  have e : (fun p : ℝ × ℝ ↦ (p.1, r * p.1 + √(1 - r ^ 2) * p.2)) ⁻¹' {p | p.1 = p.2} =
      {p : ℝ × ℝ | (r - 1) * p.1 + √(1 - r ^ 2) * p.2 = 0} := by
    ext p
    simp only [mem_preimage, mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  rw [e]
  exact prod_line_null (Or.inr (sigma_pos hr).ne')

/-- **Exchangeability**: `Γ_r(a) = 2 P(X ≤ Ψ(a), Y ≤ X) = 2 ∫_{-∞}^{Ψ(a)} φ(x) Φ(κ_r x) dx`. -/
theorem Gam_eq_two_mul {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Gam r a = 2 * ∫ x in Iic (Psi a), npdf x * Phi (kap r * x) := by
  have hσ := sigma_pos hr
  have hA : {p : ℝ × ℝ | Phi p.1 ≤ a ∧ Phi p.2 ≤ a} = {p | p.1 ≤ Psi a ∧ p.2 ≤ Psi a} := by
    ext p
    simp only [mem_ofPred_eq, setOf_Phi_le ha]
  have hSm : MeasurableSet {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1} :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hTm : MeasurableSet {p : ℝ × ℝ | p.2 ≤ Psi a ∧ p.1 ≤ p.2} :=
    (measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hST : {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1} ∪ {p : ℝ × ℝ | p.2 ≤ Psi a ∧ p.1 ≤ p.2} =
      {p | p.1 ≤ Psi a ∧ p.2 ≤ Psi a} := by
    ext p
    simp only [mem_union, mem_ofPred_eq]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2.trans h1⟩
      · exact ⟨h2.trans h1, h1⟩
    · rintro ⟨h1, h2⟩
      rcases le_total p.2 p.1 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h2, h⟩
  have hI : (corrPair r).real
      ({p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1} ∩ {p : ℝ × ℝ | p.2 ≤ Psi a ∧ p.1 ≤ p.2}) = 0 := by
    refine measureReal_mono_null (s₂ := {p : ℝ × ℝ | p.1 = p.2}) ?_ ?_
    · rintro p ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact le_antisymm h2 h1
    · rw [measureReal_def, corrPair_diag_null hr, ENNReal.toReal_zero]
  have hswap : (corrPair r).real {p : ℝ × ℝ | p.2 ≤ Psi a ∧ p.1 ≤ p.2} =
      (corrPair r).real {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1} := by
    conv_lhs => rw [← Gamma.corrPair_map_swap ⟨hr.1.le, hr.2.le⟩]
    rw [map_measureReal_apply measurable_swap hTm]
    rfl
  have hS : (corrPair r).real {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1} =
      ∫ x in Iic (Psi a), npdf x * Phi (kap r * x) := by
    rw [corrPair, map_measureReal_apply (measurable_corrPairMap r) hSm]
    have e : (fun p : ℝ × ℝ ↦ (p.1, r * p.1 + √(1 - r ^ 2) * p.2)) ⁻¹'
        {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1} =
        {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ kap r * p.1 + 0} := by
      ext p
      simp only [mem_preimage, mem_ofPred_eq, add_zero]
      rw [kap_eq hr, div_mul_eq_mul_div, le_div_iff₀ hσ]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [e, prod_real_le_affine]
    simp only [add_zero]
  have hU := measureReal_union_add_inter (μ := corrPair r)
    (s := {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ p.1}) hTm
  rw [hST, hI, hswap, hS] at hU
  rw [Gam, hA, ← hS]
  rw [hS]
  linarith

/-- **The closed form** through Owen's `T` function: `Γ_r(a) = a - 2 T(Ψ(a), κ_r)`. -/
theorem Gam_eq_owensT {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Gam r a = a - 2 * Real.owensT (Psi a) (kap r) := by
  rw [Gam_eq_two_mul hr ha, ← integral_const_mul]
  have := TauCeti.Probability.integral_Iic_two_mul_gaussianPDFReal_mul_cdf_gaussianReal
    (kap r) (Psi a)
  rw [cdf_eq_Phi, Phi_Psi ha] at this
  rw [← this]
  congr 1
  funext t
  rw [cdf_eq_Phi]
  ring

/-! ### Calculus facts on `φ`, `Φ`, `κ` -/

theorem npdf_eq (y : ℝ) : npdf y = (√(2 * π))⁻¹ * exp (-(y ^ 2 / 2)) :=
  TauCeti.Probability.gaussianPDFReal_zero_one y

theorem qf_eq {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) : qf a = npdf (Psi a) := by
  simp [qf, ha]

theorem hasDerivAt_Phi' (x : ℝ) : HasDerivAt Phi (npdf x) x :=
  TauCeti.Probability.hasDerivAt_cdf_gaussianReal 0 one_ne_zero x

theorem npdf_le_npdf {x y : ℝ} (h : y ^ 2 ≤ x ^ 2) : npdf x ≤ npdf y := by
  rw [npdf_eq, npdf_eq]
  gcongr

theorem npdf_le' (y : ℝ) : npdf y ≤ (√(2 * π))⁻¹ := by
  rw [npdf_eq]
  exact mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 (by nlinarith [sq_nonneg y]))

theorem inv_sqrt_two_pi_sq : (√(2 * π))⁻¹ * (√(2 * π))⁻¹ = 1 / (2 * π) := by
  rw [← mul_inv, mul_self_sqrt (by positivity), one_div]

theorem kap_sq {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) : kap r ^ 2 = (1 - r) / (1 + r) :=
  Real.sq_sqrt (div_pos (by linarith [hr.2]) (by linarith [hr.1])).le

theorem hasDerivAt_kap {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt kap (-1 / ((1 + r) ^ 2 * kap r)) r := by
  have h1 : 0 < 1 + r := by linarith [hr.1]
  have h2 : 0 < 1 - r := by linarith [hr.2]
  have hf : HasDerivAt (fun x ↦ (1 - x) / (1 + x))
      (((0 - 1) * (1 + r) - (1 - r) * (0 + 1)) / (1 + r) ^ 2) r :=
    ((hasDerivAt_const r 1).sub (hasDerivAt_id r)).div
      ((hasDerivAt_const r 1).add (hasDerivAt_id r)) h1.ne'
  have hk := hf.sqrt (div_pos h2 h1).ne'
  have hk0 : 0 < kap r := kap_pos hr
  refine hk.congr_deriv ?_
  rw [show √((1 - r) / (1 + r)) = kap r from rfl]
  field_simp
  ring

theorem path_mem {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s < (1 + t) / 2) :
    (t - s) / (1 - s) ∈ Ioo (-1 : ℝ) 1 := by
  have h1s : 0 < 1 - s := by linarith [ht.2]
  constructor
  · rw [lt_div_iff₀ h1s]
    linarith
  · rw [div_lt_one h1s]
    linarith [ht.2]

/-! ### Smoothness -/

section Smooth

open scoped ContDiff

/-- A function on `ℝ²` whose two partial derivatives are `C^n` is `C^{n+1}`. -/
theorem contDiff_succ_of_partials {n : ℕ} {f : ℝ × ℝ → ℝ} {g₁ g₂ : ℝ × ℝ → ℝ}
    (h₁ : ∀ p : ℝ × ℝ, HasDerivAt (fun x ↦ f (x, p.2)) (g₁ p) p.1)
    (h₂ : ∀ p : ℝ × ℝ, HasDerivAt (fun y ↦ f (p.1, y)) (g₂ p) p.2)
    (hg₁ : ContDiff ℝ n g₁) (hg₂ : ContDiff ℝ n g₂) : ContDiff ℝ (n + 1) f := by
  rw [contDiff_succ_iff_hasFDerivAt]
  refine ⟨fun p ↦ g₁ p • ContinuousLinearMap.fst ℝ ℝ ℝ + g₂ p • ContinuousLinearMap.snd ℝ ℝ ℝ,
    (hg₁.smul contDiff_const).add (hg₂.smul contDiff_const), fun u ↦ ?_⟩
  have hc : ∀ g : ℝ × ℝ → ℝ, Continuous g →
      Continuous fun p : ℝ × ℝ ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g p) := by
    intro g hg
    exact (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp hg
  have := hasStrictFDerivAt_uncurry_coprod (u := u) (f := fun x y ↦ f (x, y))
    (f₁ := fun x y ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g₁ (x, y)))
    (f₂ := fun x y ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g₂ (x, y)))
    (Filter.Eventually.of_forall fun v ↦ (h₁ v).hasFDerivAt)
    (Filter.Eventually.of_forall fun v ↦ (h₂ v).hasFDerivAt)
    (hc g₁ hg₁.continuous).continuousAt (hc g₂ hg₂.continuous).continuousAt
  have e2 : ((↿fun x y ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g₁ (x, y))) u).coprod
      ((↿fun x y ↦ ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g₂ (x, y))) u) =
      g₁ u • ContinuousLinearMap.fst ℝ ℝ ℝ + g₂ u • ContinuousLinearMap.snd ℝ ℝ ℝ := by
    refine ContinuousLinearMap.ext fun p ↦ ?_
    change (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g₁ (u.1, u.2))).coprod
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (g₂ (u.1, u.2))) p = _
    simp [mul_comm]
  rw [e2] at this
  exact this.hasFDerivAt

theorem contDiff_npdf : ContDiff ℝ ∞ npdf := by
  have : npdf = fun y ↦ (√(2 * π))⁻¹ * exp (-(y ^ 2 / 2)) := funext npdf_eq
  rw [this]
  fun_prop

theorem contDiff_Phi : ContDiff ℝ ∞ Phi := by
  have hd : deriv Phi = npdf := funext fun x ↦ (hasDerivAt_Phi' x).deriv
  rw [contDiff_infty_iff_deriv, hd]
  exact ⟨fun x ↦ (hasDerivAt_Phi' x).differentiableAt, contDiff_npdf⟩

/-- Owen's `T` function is `C²` on `ℝ²`. -/
theorem contDiff_owensT : ContDiff ℝ 2 (fun p : ℝ × ℝ ↦ Real.owensT p.1 p.2) := by
  have h := contDiff_succ_of_partials (n := 1) (f := fun p : ℝ × ℝ ↦ Real.owensT p.1 p.2)
    (g₁ := fun p ↦ -(npdf p.1 * (Phi (p.2 * p.1) - 1 / 2)))
    (g₂ := fun p ↦ exp (-p.1 ^ 2 * (1 + p.2 ^ 2) / 2) / (2 * π * (1 + p.2 ^ 2)))
    (fun p ↦ Real.hasDerivAt_owensT_left p.1 p.2) (fun p ↦ Real.hasDerivAt_owensT_right p.1 p.2)
    ?_ ?_
  · exact h
  · have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ npdf p.1) :=
      (contDiff_npdf.of_le (by exact_mod_cast le_top)).comp contDiff_fst
    have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ Phi (p.2 * p.1)) :=
      (contDiff_Phi.of_le (by exact_mod_cast le_top)).comp (contDiff_snd.mul contDiff_fst)
    exact (h1.mul (h2.sub contDiff_const)).neg
  · exact ContDiff.div (by fun_prop) (by fun_prop) fun p ↦ by positivity

/-- `κ` is smooth on `(-1, 1)`. -/
theorem contDiffOn_kap : ContDiffOn ℝ ∞ kap (Ioo (-1 : ℝ) 1) := by
  have : ContDiffOn ℝ ∞ (fun x : ℝ ↦ (1 - x) / (1 + x)) (Ioo (-1 : ℝ) 1) :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun x hx ↦ by linarith [hx.1]
  exact this.sqrt fun x hx ↦ (div_pos (by linarith [hx.2]) (by linarith [hx.1])).ne'

end Smooth

end BGHKLMM26.RobustMIS.GammaCalc

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open Gaussian

/-- The conditional representation: `Γ_r(a) = ∫_{-∞}^{Ψ(a)} φ(x) Φ((Ψ(a) - r x)/σ_r) dx`. -/
theorem Gam_eq_integral {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Gam r a = ∫ x in Iic (Psi a), npdf x * Phi ((Psi a - r * x) / √(1 - r ^ 2)) := by
  have hσ := GammaCalc.sigma_pos hr
  rw [GammaCalc.Gam_eq_prod ha]
  have e : {p : ℝ × ℝ | p.1 ≤ Psi a ∧ r * p.1 + √(1 - r ^ 2) * p.2 ≤ Psi a} =
      {p : ℝ × ℝ | p.1 ≤ Psi a ∧ p.2 ≤ (-r / √(1 - r ^ 2)) * p.1 + Psi a / √(1 - r ^ 2)} := by
    ext p
    simp only [mem_ofPred_eq]
    have : r * p.1 + √(1 - r ^ 2) * p.2 ≤ Psi a ↔
        p.2 ≤ (-r / √(1 - r ^ 2)) * p.1 + Psi a / √(1 - r ^ 2) := by
      rw [show (-r / √(1 - r ^ 2)) * p.1 + Psi a / √(1 - r ^ 2) = (Psi a - r * p.1) / √(1 - r ^ 2)
        by field_simp; ring, le_div_iff₀ hσ]
      constructor <;> intro h <;> linarith
    rw [this]
  rw [e, GammaCalc.prod_real_le_affine]
  congr 1
  funext x
  congr 2
  field_simp
  ring

open Filter Topology in
/-- Lemma 3.3(b): `Γ_r'(a) = 2 Φ(κ_r Ψ(a))`. -/
theorem hasDerivAt_Gam {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (Gam r) (2 * Phi (kap r * Psi a)) a := by
  have hev : Gam r =ᶠ[𝓝 a] fun b ↦ b - 2 * Real.owensT (Psi b) (kap r) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact GammaCalc.Gam_eq_owensT hr hb
  have hT := (Real.hasDerivAt_owensT_left (Psi a) (kap r)).comp a (hasDerivAt_Psi ha)
  have h := (hasDerivAt_id a).sub (hT.const_mul 2)
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  have hq0 : npdf (Psi a) ≠ 0 := (npdf_pos _).ne'
  rw [GammaCalc.qf_eq ha, GammaCalc.cdf_eq_Phi]
  field_simp
  ring

open Filter Topology in
/-- Lemma 3.3(b): `Γ_r''(a) = 2 κ_r φ(κ_r Ψ(a)) / q(a)`. -/
theorem hasDerivAt_deriv_Gam {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (Gam r)) (2 * kap r * npdf (kap r * Psi a) / qf a) a := by
  have hev : deriv (Gam r) =ᶠ[𝓝 a] fun b ↦ 2 * Phi (kap r * Psi b) := by
    filter_upwards [isOpen_Ioo.mem_nhds ha] with b hb
    exact (hasDerivAt_Gam hr hb).deriv
  have h := ((GammaCalc.hasDerivAt_Phi' (kap r * Psi a)).comp a
    ((hasDerivAt_Psi ha).const_mul (kap r))).const_mul 2
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  field_simp

open Filter Topology in
/-- Lemma 3.3(b): `∂_r Γ_r(a) = q(a) φ(κ_r Ψ(a)) / σ_r`. -/
theorem hasDerivAt_Gam_corr {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r ↦ Gam r a) (qf a * npdf (kap r * Psi a) / √(1 - r ^ 2)) r := by
  have hev : (fun s ↦ Gam s a) =ᶠ[𝓝 r] fun s ↦ a - 2 * Real.owensT (Psi a) (kap s) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with s hs
    exact GammaCalc.Gam_eq_owensT hs ha
  have hT := (Real.hasDerivAt_owensT_right (Psi a) (kap r)).comp r (GammaCalc.hasDerivAt_kap hr)
  have h := (hT.const_mul 2).const_sub a
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  have h1 : 0 < 1 + r := by linarith [hr.1]
  have hk0 : 0 < kap r := kap_pos hr
  have h1k : 1 + kap r ^ 2 = 2 / (1 + r) := by
    rw [GammaCalc.kap_sq hr]
    field_simp
    ring
  have hσ : √(1 - r ^ 2) = (1 + r) * kap r := by
    have hσ0 := GammaCalc.sigma_pos hr
    rw [GammaCalc.kap_eq hr]
    field_simp
    rw [Real.sq_sqrt (by nlinarith [hr.1, hr.2])]
    ring
  have hexp : exp (-Psi a ^ 2 * (1 + kap r ^ 2) / 2) =
      exp (-(Psi a ^ 2 / 2)) * exp (-((kap r * Psi a) ^ 2 / 2)) := by
    rw [← exp_add]
    ring_nf
  rw [GammaCalc.qf_eq ha, GammaCalc.npdf_eq, GammaCalc.npdf_eq, hσ, hexp, h1k]
  field_simp
  exact Real.sq_sqrt (by positivity)

/-- Lemma 3.3(c): for `r ∈ [0, 1)`, `Γ_r'' ≥ 2 κ_r` and `0 < q² Γ_r'' ≤ κ_r / π`. -/
theorem deriv2_Gam_bounds {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    2 * kap r ≤ deriv (deriv (Gam r)) a ∧ 0 < qf a ^ 2 * deriv (deriv (Gam r)) a ∧
      qf a ^ 2 * deriv (deriv (Gam r)) a ≤ kap r / π := by
  have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
  rw [(hasDerivAt_deriv_Gam hr' ha).deriv, GammaCalc.qf_eq ha]
  have hk0 : 0 < kap r := kap_pos hr'
  have hk1 : kap r ≤ 1 := kap_le_one hr.1
  have hq0 : 0 < npdf (Psi a) := npdf_pos _
  have hφ0 : 0 < npdf (kap r * Psi a) := npdf_pos _
  have hφq : npdf (Psi a) ≤ npdf (kap r * Psi a) := by
    apply GammaCalc.npdf_le_npdf
    rw [mul_pow]
    have : kap r ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (Psi a)]
  have hsimp : npdf (Psi a) ^ 2 * (2 * kap r * npdf (kap r * Psi a) / npdf (Psi a)) =
      2 * kap r * (npdf (Psi a) * npdf (kap r * Psi a)) := by
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ hq0]
    have := mul_le_mul_of_nonneg_left hφq (by linarith : (0 : ℝ) ≤ 2 * kap r)
    linarith
  · rw [hsimp]
    positivity
  · rw [hsimp]
    have h1 : npdf (Psi a) * npdf (kap r * Psi a) ≤ 1 / (2 * π) := by
      rw [← GammaCalc.inv_sqrt_two_pi_sq]
      exact mul_le_mul (GammaCalc.npdf_le' _) (GammaCalc.npdf_le' _) hφ0.le (by positivity)
    calc 2 * kap r * (npdf (Psi a) * npdf (kap r * Psi a)) ≤ 2 * kap r * (1 / (2 * π)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = kap r / π := by
          field_simp

/-- Lemma 3.3(c): `0 < ∂_r Γ_r(a) ≤ 1/(2π σ_r)` for `r ∈ [0, 1)`. -/
theorem deriv_Gam_corr_bounds {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) {a : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) :
    0 < qf a * npdf (kap r * Psi a) / √(1 - r ^ 2) ∧
      qf a * npdf (kap r * Psi a) / √(1 - r ^ 2) ≤ 1 / (2 * π * √(1 - r ^ 2)) := by
  have hr' : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
  have hσ := GammaCalc.sigma_pos hr'
  rw [GammaCalc.qf_eq ha]
  have hq0 : 0 < npdf (Psi a) := npdf_pos _
  have hφ0 : 0 < npdf (kap r * Psi a) := npdf_pos _
  refine ⟨by positivity, ?_⟩
  have h1 : npdf (Psi a) * npdf (kap r * Psi a) ≤ 1 / (2 * π) := by
    rw [← GammaCalc.inv_sqrt_two_pi_sq]
    exact mul_le_mul (GammaCalc.npdf_le' _) (GammaCalc.npdf_le' _) hφ0.le (by positivity)
  rw [show 1 / (2 * π * √(1 - r ^ 2)) = 1 / (2 * π) / √(1 - r ^ 2) by rw [div_div]]
  exact div_le_div_of_nonneg_right h1 hσ.le

/-- Lemma 3.3(d), **the backward equation** `∂_s J = -q² ∂_a² J / (2(1 - s))`. -/
theorem backward_Gam_path {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s < (1 + t) / 2)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ Gam ((t - s) / (1 - s)) a)
      (-(qf a ^ 2 * deriv (deriv (Gam ((t - s) / (1 - s)))) a / (2 * (1 - s)))) s := by
  have h1s : 0 < 1 - s := by linarith [ht.2]
  have hρ := GammaCalc.path_mem ht hs
  have hρd : HasDerivAt (fun s ↦ (t - s) / (1 - s))
      (((0 - 1) * (1 - s) - (t - s) * (0 - 1)) / (1 - s) ^ 2) s :=
    ((hasDerivAt_const s t).sub (hasDerivAt_id s)).div
      ((hasDerivAt_const s 1).sub (hasDerivAt_id s)) h1s.ne'
  have h := (hasDerivAt_Gam_corr hρ ha).comp s hρd
  rw [(hasDerivAt_deriv_Gam hρ ha).deriv]
  refine h.congr_deriv ?_
  have hk0 : 0 < kap ((t - s) / (1 - s)) := kap_pos hρ
  have hσ0 := GammaCalc.sigma_pos hρ
  have hke := GammaCalc.kap_eq hρ
  have hq0 : 0 < qf a := qf_pos ha
  generalize kap ((t - s) / (1 - s)) = k at hk0 hke ⊢
  generalize √(1 - ((t - s) / (1 - s)) ^ 2) = σ at hσ0 hke ⊢
  have hkσ : k * σ * (1 - s) = 1 - t := by
    rw [hke]
    field_simp
    ring
  have hnum : (0 - 1) * (1 - s) - (t - s) * (0 - 1) = -(k * σ * (1 - s)) := by
    linear_combination hkσ
  rw [hnum]
  field_simp

open scoped ContDiff in
/-- Lemma 3.3(d): `J(s, a) = Γ_{r(s)}(a)`, `r(s) = (t - s)/(1 - s)`, is smooth on
`(-∞, (1+t)/2) × (0, 1)`. -/
theorem contDiffOn_Gam_path {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ Gam ((t - p.1) / (1 - p.1)) p.2)
      (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hρ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ (t - p.1) / (1 - p.1))
      (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) := by
    refine ContDiffOn.div (by fun_prop) (by fun_prop) fun p hp ↦ ?_
    have h1 : p.1 < (1 + t) / 2 := hp.1
    linarith [ht.2]
  have hmapρ : MapsTo (fun p : ℝ × ℝ ↦ (t - p.1) / (1 - p.1)) (Iio ((1 + t) / 2) ×ˢ Ioo 0 1)
      (Ioo (-1) 1) := fun p hp ↦ GammaCalc.path_mem ht hp.1
  have hκ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ kap ((t - p.1) / (1 - p.1)))
      (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) :=
    (GammaCalc.contDiffOn_kap.of_le h2).comp hρ hmapρ
  have hΨ : ContDiffOn ℝ 2 (fun p : ℝ × ℝ ↦ Psi p.2) (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) :=
    (contDiffOn_Psi.of_le h2).comp contDiff_snd.contDiffOn
      (fun p hp ↦ hp.2)
  have hT : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ ↦ Real.owensT (Psi p.2) (kap ((t - p.1) / (1 - p.1))))
      (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) :=
    GammaCalc.contDiff_owensT.comp_contDiffOn (hΨ.prodMk hκ)
  have h : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ ↦ p.2 - 2 * Real.owensT (Psi p.2) (kap ((t - p.1) / (1 - p.1))))
      (Iio ((1 + t) / 2) ×ˢ Ioo 0 1) :=
    contDiff_snd.contDiffOn.sub (contDiffOn_const.mul hT)
  refine h.congr fun p hp ↦ ?_
  exact GammaCalc.Gam_eq_owensT (GammaCalc.path_mem ht hp.1) hp.2

/-- `Γ_t'(1/2) = 2 Φ(0) = 1`. -/
theorem GammaCalc.deriv_Gam_half {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    deriv (Gam t) (1 / 2) = 1 := by
  rw [(hasDerivAt_Gam ht ⟨by norm_num, by norm_num⟩).deriv]
  have hP0 : Phi 0 = 1 / 2 := TauCeti.Probability.cdf_gaussianReal_self 0 (by norm_num)
  have hΨ : Psi (1 / 2) = 0 := by rw [← hP0, Psi_Phi]
  rw [hΨ, mul_zero, hP0]
  norm_num

/-- `0 ≤ Γ_t'' ≤ 4` on `[1/4, 3/4]` for `t ∈ [0, 1)`. -/
theorem GammaCalc.deriv2_Gam_le_four {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {x : ℝ}
    (hx : x ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
    deriv (deriv (Gam t)) x ≤ 4 ∧ 0 ≤ deriv (deriv (Gam t)) x := by
  have ht : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [(hasDerivAt_deriv_Gam ht hx').deriv]
  have hq := qf_ge_min (a := x) ⟨hx'.1.le, hx'.2.le⟩
  have hmin : 1 / 4 ≤ min x (1 - x) := le_min hx.1 (by linarith [hx.2])
  have hq0 : 0 < qf x := qf_pos hx'
  have hk0 := kap_pos ht
  have hk1 := kap_le_one ht0
  have hφ := GammaCalc.npdf_le' (kap t * Psi x)
  have hφ0 := npdf_pos (kap t * Psi x)
  have hA : 0 < √(2 / π) := Real.sqrt_pos.2 (by positivity)
  have hsq : √(2 * π) * √(2 / π) = 2 := by
    rw [← Real.sqrt_mul (by positivity), show 2 * π * (2 / π) = 2 ^ 2 by field_simp,
      Real.sqrt_sq (by norm_num)]
  have h2 : 2 * (√(2 * π))⁻¹ = √(2 / π) := by
    have : √(2 * π) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
    field_simp
    linarith
  constructor
  · rw [div_le_iff₀ hq0]
    have e1 : kap t * npdf (kap t * Psi x) ≤ npdf (kap t * Psi x) := by nlinarith
    have e2 : √(2 / π) * (1 / 4) ≤ √(2 / π) * min x (1 - x) :=
      mul_le_mul_of_nonneg_left hmin hA.le
    nlinarith
  · exact div_nonneg (by positivity) hq0.le

/-- `|Γ_t'(x) - 1| ≤ 4 |x - 1/2|` on `[1/4, 3/4]`. -/
theorem GammaCalc.abs_deriv_Gam_sub_one_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {x : ℝ}
    (hx : x ∈ Icc (1 / 4 : ℝ) (3 / 4)) : |deriv (Gam t) x - 1| ≤ 4 * |x - 1 / 2| := by
  have ht : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (Gam t))
    (s := Icc (1 / 4 : ℝ) (3 / 4)) (C := 4)
    (fun y hy ↦ (hasDerivAt_deriv_Gam ht
      ⟨by linarith [hy.1], by linarith [hy.2]⟩).differentiableAt)
    (fun y hy ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (GammaCalc.deriv2_Gam_le_four ht0 ht1 hy).2]
      exact (GammaCalc.deriv2_Gam_le_four ht0 ht1 hy).1)
    (convex_Icc _ _) (⟨by norm_num, by norm_num⟩ : (1 / 2 : ℝ) ∈ Icc (1 / 4) (3 / 4)) hx
  rw [GammaCalc.deriv_Gam_half ht] at h
  simpa [Real.norm_eq_abs] using h

/-- The second-order Taylor bound at `1/2`: `Γ_t(x) ≤ Γ_t(1/2) + (x - 1/2) + 4 (x - 1/2)²` on
`[1/4, 3/4]`. -/
theorem GammaCalc.Gam_le_taylor {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {x : ℝ}
    (hx : x ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
    Gam t x ≤ Gam t (1 / 2) + (x - 1 / 2) + 4 * (x - 1 / 2) ^ 2 := by
  have ht : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, ht1⟩
  have hD : ∀ y ∈ Icc (1 / 4 : ℝ) (3 / 4), HasDerivAt (Gam t) (deriv (Gam t) y) y :=
    fun y hy ↦ (hasDerivAt_Gam ht
      ⟨by linarith [hy.1], by linarith [hy.2]⟩).differentiableAt.hasDerivAt
  rcases lt_trichotomy x (1 / 2) with hlt | heq | hgt
  · have hsub : Icc x (1 / 2) ⊆ Icc (1 / 4 : ℝ) (3 / 4) :=
      fun y hy ↦ ⟨by linarith [hx.1, hy.1], by linarith [hy.2]⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Gam t) (deriv (Gam t)) hlt
      (fun y hy ↦ (hD y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hD y (hsub (Ioo_subset_Icc_self hy)))
    rw [eq_div_iff (by linarith)] at hcd
    have hb := GammaCalc.abs_deriv_Gam_sub_one_le ht0 ht1 (hsub (Ioo_subset_Icc_self hc))
    rw [abs_of_neg (by linarith [hc.2] : c - 1 / 2 < 0)] at hb
    have hlow : 1 - 4 * (1 / 2 - x) ≤ deriv (Gam t) c := by
      linarith [(abs_le.1 hb).1, hc.1]
    nlinarith [mul_le_mul_of_nonneg_right hlow (by linarith : (0 : ℝ) ≤ 1 / 2 - x)]
  · subst heq
    simp
  · have hsub : Icc (1 / 2) x ⊆ Icc (1 / 4 : ℝ) (3 / 4) :=
      fun y hy ↦ ⟨by linarith [hy.1], by linarith [hx.2, hy.2]⟩
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (Gam t) (deriv (Gam t)) hgt
      (fun y hy ↦ (hD y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hD y (hsub (Ioo_subset_Icc_self hy)))
    rw [eq_div_iff (by linarith)] at hcd
    have hb := GammaCalc.abs_deriv_Gam_sub_one_le ht0 ht1 (hsub (Ioo_subset_Icc_self hc))
    rw [abs_of_pos (by linarith [hc.1] : 0 < c - 1 / 2)] at hb
    have hup : deriv (Gam t) c ≤ 1 + 4 * (x - 1 / 2) := by
      linarith [(abs_le.1 hb).2, hc.2]
    nlinarith [mul_le_mul_of_nonneg_right hup (by linarith : (0 : ℝ) ≤ x - 1 / 2)]

/-- **The quadratic bound** (Lemma `gaussian-facts` (d), one-sided, in terms of `Γ`):
`Γ_t((1+m)/2) ≤ Γ_t(1/2) + m/2 + C m²` for `m ∈ [-1, 1]`, i.e.
`Γ^±_t(m) - Γ^±_t(0) ≤ 4 C m²`. (Proof: `Γ_t'(1/2) = 1`; `Γ_t''` is bounded on `[1/4, 3/4]`;
for `|m| ≥ 1/2` use the Lipschitz bound.) -/
theorem Gam_quadratic {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m ∈ Icc (-1 : ℝ) 1,
      Gam t ((1 + m) / 2) ≤ Gam t (1 / 2) + m / 2 + C * m ^ 2 := by
  refine ⟨3, by norm_num, fun m hm ↦ ?_⟩
  have e : (1 + m) / 2 - 1 / 2 = m / 2 := by ring
  rcases le_or_gt |m| (1 / 2) with hs | hs
  · have hx : (1 + m) / 2 ∈ Icc (1 / 4 : ℝ) (3 / 4) := by
      constructor <;> linarith [(abs_le.1 hs).1, (abs_le.1 hs).2]
    have h := GammaCalc.Gam_le_taylor ht0 ht1 hx
    rw [e] at h
    nlinarith [sq_nonneg m]
  · have hL := abs_Gam_sub_le (r := t) ⟨by linarith, ht1.le⟩ ((1 + m) / 2) (1 / 2)
    rw [e, abs_div, abs_two] at hL
    have h1 := (abs_le.1 hL).2
    have hm2 : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
    nlinarith [neg_abs_le m, abs_nonneg m, mul_nonneg (sub_nonneg.2 hs.le) (abs_nonneg m)]

end BGHKLMM26.RobustMIS
