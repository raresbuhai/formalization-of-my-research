module

public import BGHKLMM26.Strip
public import BGHKLMM26.Baseline
public import BGHKLMM26.Model
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Lower bounding the gain

[BGHKLMM26, Section 3.4]. Moving `xᵢ = sgn⟨vᵢ, g⟩` to `sgn(⟨vᵢ, g⟩ + λ fᵢ)` changes the sign only
on a strip `|⟨vᵢ, g⟩| ≤ λ |fᵢ|`. Conditioning on the part of `g` orthogonal to `vᵢ`, the change
seen by a neighbour `j` is an integral over that strip [BGHKLMM26, Lemma 3.16]; it is
`λ φ(0) fᵢ sgn(hᵢⱼ)` up to errors controlled by the strip lemmas.

The paper writes the change exactly as an oriented integral `∫₀^{λ fᵢ} φ(t) sgn(σ hᵢⱼ - ρ t) dt`
and splits it in three parts. We bound it directly against Lebesgue measure: with
`D(x) = sgn(x + c) - sgn x`, `∫ D = 2c`, `D` vanishes off `[-|c|, |c|]`, and the density and the
sign are nearly constant there (`BGHKLMM26.integral_sgn_sub_mul_ge`).
-/

@[expose] public section

namespace BGHKLMM26

open MeasureTheory ProbabilityTheory Real Gaussian Set
open scoped RealInnerProductSpace

/-! ### One dimension -/

section OneDim

/-- `φ(0) = 1/√(2π)`, the standard Gaussian density at `0`. -/
noncomputable def phi0 : ℝ := (√(2 * π))⁻¹

theorem phi0_pos : 0 < phi0 := by unfold phi0; positivity

theorem gaussianPDFReal_eq (x : ℝ) : gaussianPDFReal 0 1 x = phi0 * rexp (-x ^ 2 / 2) := by
  simp [gaussianPDFReal, phi0]

theorem gaussianPDFReal_le_phi0 (x : ℝ) : gaussianPDFReal 0 1 x ≤ phi0 := by
  rw [gaussianPDFReal_eq]
  exact mul_le_of_le_one_right phi0_pos.le (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x]))

theorem abs_gaussianPDFReal_sub_phi0 (x : ℝ) :
    |gaussianPDFReal 0 1 x - phi0| ≤ phi0 * x ^ 2 / 2 := by
  rw [gaussianPDFReal_eq, abs_sub_comm, abs_of_nonneg (by
    have := mul_le_of_le_one_right phi0_pos.le
      (Real.exp_le_one_iff.2 (show -x ^ 2 / 2 ≤ 0 by nlinarith [sq_nonneg x]))
    linarith)]
  have := Real.add_one_le_exp (-x ^ 2 / 2)
  nlinarith [phi0_pos]

/-- The change of a sign under a shift by `c`. -/
theorem sgn_add_sub_sgn (c x : ℝ) :
    sgn (x + c) - sgn x = 2 * (Ico (-c) 0).indicator 1 x - 2 * (Ico 0 (-c)).indicator 1 x := by
  unfold sgn
  simp only [indicator, mem_Ico, Pi.one_apply]
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 (x + c) with hxc | hxc
  · rw [ite_eq_left hxc, ite_eq_left hx, ite_eq_right (fun h ↦ by linarith [h.2]),
      ite_eq_right (fun h ↦ by linarith [h.2])]
    norm_num
  · rw [ite_eq_right (not_le.2 hxc), ite_eq_left hx, ite_eq_right (fun h ↦ by linarith [h.2]),
      ite_eq_left ⟨hx, by linarith⟩]
    norm_num
  · rw [ite_eq_left hxc, ite_eq_right (not_le.2 hx), ite_eq_left ⟨by linarith, hx⟩,
      ite_eq_right (fun h ↦ by linarith [h.1])]
    norm_num
  · rw [ite_eq_right (not_le.2 hxc), ite_eq_right (not_le.2 hx),
      ite_eq_right (fun h ↦ by linarith [h.1]),
      ite_eq_right (fun h ↦ by linarith [h.1])]
    norm_num

theorem abs_sgn_add_sub_sgn_le (c x : ℝ) :
    |sgn (x + c) - sgn x| ≤ 2 * (Icc (-|c|) |c|).indicator 1 x := by
  rw [sgn_add_sub_sgn]
  simp only [indicator, mem_Ico, mem_Icc, Pi.one_apply]
  have hc := le_abs_self c
  have hc' := neg_abs_le c
  by_cases h1 : -c ≤ x ∧ x < 0 <;> by_cases h2 : 0 ≤ x ∧ x < -c
  · exfalso; linarith [h1.2, h2.1]
  · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left ⟨by linarith [h1.1], by linarith [h1.2]⟩]
    norm_num
  · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left ⟨by linarith [h2.1], by linarith [h2.2]⟩]
    norm_num
  · rw [ite_eq_right h1, ite_eq_right h2]
    norm_num
    split_ifs <;> norm_num

theorem integrable_sgn_add_sub_sgn (c : ℝ) : Integrable fun x ↦ sgn (x + c) - sgn x := by
  refine Integrable.mono' (g := fun x ↦ 2 * (Icc (-|c|) |c|).indicator 1 x) ?_ (by fun_prop) ?_
  · exact ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc).const_mul 2
  · exact ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact abs_sgn_add_sub_sgn_le c x

/-- `∫ (sgn(x + c) - sgn x) dx = 2c`. -/
theorem integral_sgn_add_sub_sgn (c : ℝ) : ∫ x, (sgn (x + c) - sgn x) = 2 * c := by
  simp_rw [sgn_add_sub_sgn]
  have h1 : Integrable fun x : ℝ ↦ 2 * (Ico (-c) 0).indicator (1 : ℝ → ℝ) x :=
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Ico).const_mul 2
  have h2 : Integrable fun x : ℝ ↦ 2 * (Ico 0 (-c)).indicator (1 : ℝ → ℝ) x :=
    ((integrableOn_const (by simp)).integrable_indicator measurableSet_Ico).const_mul 2
  rw [integral_sub h1 h2, integral_const_mul, integral_const_mul,
    integral_indicator_one measurableSet_Ico, integral_indicator_one measurableSet_Ico,
    Real.volume_real_Ico, Real.volume_real_Ico]
  rcases le_total 0 c with hc | hc
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

/-- **The change of a sign on a strip** [BGHKLMM26, Lemmas 3.16–3.18, in one dimension]: for a
standard Gaussian `X`, a shift `c`, and `S` with `|S| ≤ 1` that equals `s₀` on `[-|c|, |c|]` unless
`P` holds, `E (sgn(X + c) - sgn X) S(X) ≥ 2 c φ(0) s₀ - φ(0) (|c|³ + 8 |c| [P])`. -/
theorem integral_sgn_sub_mul_ge {S : ℝ → ℝ} (hS : Measurable S) (hSb : ∀ x, |S x| ≤ 1)
    {s₀ : ℝ} (hs₀ : |s₀| ≤ 1) (c : ℝ) (P : Prop) [Decidable P]
    (hP : ¬P → ∀ x, |x| ≤ |c| → S x = s₀) :
    2 * c * phi0 * s₀ - phi0 * (|c| ^ 3 + 8 * |c| * (if P then 1 else 0)) ≤
      ∫ x, (sgn (x + c) - sgn x) * S x ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp only [smul_eq_mul]
  set a := |c| with hadef
  have ha : 0 ≤ a := abs_nonneg c
  set e : ℝ := if P then 1 else 0 with hedef
  have he0 : 0 ≤ e := by rw [hedef]; split_ifs <;> norm_num
  set D : ℝ → ℝ := fun x ↦ sgn (x + c) - sgn x with hDdef
  set R : ℝ → ℝ := fun x ↦ gaussianPDFReal 0 1 x * S x - phi0 * s₀ with hRdef
  have hDi : Integrable D := integrable_sgn_add_sub_sgn c
  -- `|R| ≤ φ(0) x²/2 + 2 φ(0) e` on `[-a, a]`.
  have hR : ∀ x, |x| ≤ a → |R x| ≤ phi0 * x ^ 2 / 2 + 2 * phi0 * e := by
    intro x hx
    have h1 := abs_gaussianPDFReal_sub_phi0 x
    have hφ0 : 0 ≤ gaussianPDFReal 0 1 x := gaussianPDFReal_nonneg 0 1 x
    have hφ1 := gaussianPDFReal_le_phi0 x
    by_cases hPc : P
    · have he1 : e = 1 := by rw [hedef, ite_eq_left hPc]
      rw [he1]
      calc |R x| = |gaussianPDFReal 0 1 x * (S x - s₀) + (gaussianPDFReal 0 1 x - phi0) * s₀| := by
            rw [hRdef]
            ring_nf
        _ ≤ |gaussianPDFReal 0 1 x * (S x - s₀)| + |(gaussianPDFReal 0 1 x - phi0) * s₀| :=
            abs_add_le _ _
        _ ≤ phi0 * 2 + phi0 * x ^ 2 / 2 * 1 := by
            rw [abs_mul, abs_mul, abs_of_nonneg hφ0]
            have h2 : |S x - s₀| ≤ 2 := (abs_sub _ _).trans (by linarith [hSb x, hs₀])
            exact add_le_add (mul_le_mul hφ1 h2 (abs_nonneg _) phi0_pos.le)
              (mul_le_mul h1 hs₀ (abs_nonneg _)
                (div_nonneg (mul_nonneg phi0_pos.le (sq_nonneg x)) (by norm_num)))
        _ = _ := by ring
    · have hSx := hP hPc x hx
      calc |R x| = |(gaussianPDFReal 0 1 x - phi0) * s₀| := by
            change |gaussianPDFReal 0 1 x * S x - phi0 * s₀| = _
            rw [hSx]
            ring_nf
        _ ≤ phi0 * x ^ 2 / 2 * 1 := by
            rw [abs_mul]
            exact mul_le_mul h1 hs₀ (abs_nonneg _)
              (div_nonneg (mul_nonneg phi0_pos.le (sq_nonneg x)) (by norm_num))
        _ ≤ _ := by have := phi0_pos; nlinarith
  -- The error is supported on `[-a, a]`.
  set B : ℝ → ℝ := fun x ↦ (Icc (-a) a).indicator
    (fun x ↦ 2 * (phi0 * x ^ 2 / 2 + 2 * phi0 * e)) x with hBdef
  have hBi : Integrable B := by
    refine (Continuous.integrableOn_Icc (by fun_prop)).integrable_indicator measurableSet_Icc
  have hDR : ∀ x, |D x * R x| ≤ B x := by
    intro x
    by_cases hx : |x| ≤ a
    · have hxI : x ∈ Icc (-a) a := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
      simp only [hBdef]
      rw [indicator_of_mem hxI, abs_mul]
      have hD := abs_sgn_add_sub_sgn_le c x
      rw [← hadef, indicator_of_mem hxI, Pi.one_apply, mul_one] at hD
      exact mul_le_mul hD (hR x hx) (abs_nonneg _) (by norm_num)
    · have hD : D x = 0 := by
        have := abs_sgn_add_sub_sgn_le c x
        have hxI : x ∉ Icc (-|c|) |c| := by
          rintro ⟨h1, h2⟩
          exact hx (abs_le.2 ⟨h1, h2⟩)
        rw [indicator_of_notMem hxI, mul_zero] at this
        exact abs_nonpos_iff.1 this
      rw [hD, zero_mul, abs_zero]
      exact indicator_nonneg (fun x _ ↦ mul_nonneg (by norm_num) (add_nonneg
        (div_nonneg (mul_nonneg phi0_pos.le (sq_nonneg x)) (by norm_num))
        (mul_nonneg (mul_nonneg (by norm_num) phi0_pos.le) he0))) x
  have hDRi : Integrable fun x ↦ D x * R x :=
    hBi.mono' (by fun_prop) (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hDR x)
  have hsplit : ∀ x, gaussianPDFReal 0 1 x * ((sgn (x + c) - sgn x) * S x) =
      phi0 * s₀ * D x + D x * R x := by
    intro x
    simp only [hRdef, hDdef]
    ring
  simp_rw [hsplit]
  rw [integral_add (hDi.const_mul _) hDRi, integral_const_mul, integral_sgn_add_sub_sgn]
  have hint : ∫ x, B x = phi0 * (2 * a ^ 3 / 3) + 8 * phi0 * e * a := by
    rw [hBdef, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
    have hfun : (fun x : ℝ ↦ 2 * (phi0 * x ^ 2 / 2 + 2 * phi0 * e)) =
        fun x ↦ phi0 * x ^ 2 + 4 * phi0 * e := by
      funext x
      ring
    rw [hfun, intervalIntegral.integral_add (f := fun x ↦ phi0 * x ^ 2)
      (g := fun _ ↦ 4 * phi0 * e)
      ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul, integral_pow,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have herr : -(phi0 * (a ^ 3 + 8 * a * e)) ≤ ∫ x, D x * R x := by
    have h1 : |∫ x, D x * R x| ≤ ∫ x, B x :=
      (abs_integral_le_integral_abs).trans (integral_mono hDRi.abs hBi hDR)
    rw [hint] at h1
    have := neg_abs_le (∫ x, D x * R x)
    have h3 : phi0 * (2 * a ^ 3 / 3) + 8 * phi0 * e * a ≤ phi0 * (a ^ 3 + 8 * a * e) := by
      have := phi0_pos
      nlinarith [pow_nonneg ha 3]
    linarith
  linarith

end OneDim

/-! ### One edge -/

section Edge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem sgn_mul_self_eq {bs y : ℝ} (hbs : bs = 1 ∨ bs = -1) (hy : y ≠ 0) :
    bs * sgn (bs * y) = sgn y := by
  rcases hbs with rfl | rfl
  · simp
  · unfold sgn
    rcases lt_or_gt_of_ne hy with h | h
    · rw [ite_eq_left (by linarith), ite_eq_right (by linarith)]
      norm_num
    · rw [ite_eq_right (by linarith), ite_eq_left h.le]
      norm_num

theorem abs_bs_mul_sgn {bs y : ℝ} (hbs : bs = 1 ∨ bs = -1) : |bs * sgn y| = 1 := by
  rcases hbs with rfl | rfl <;> simp [abs_sgn]

/-- **The change seen across one edge** [BGHKLMM26, Lemmas 3.16–3.18]. Let `v₁, u` be orthonormal,
`ρ² ≤ 16/25`, `v₂ = ρ v₁ + √(1 - ρ²) u`, and `F` with `|F| ≤ 1` invariant along `v₁`. Moving
`sgn⟨v₁, g⟩` to `sgn(⟨v₁, g⟩ + t F)` changes its correlation with the sign `bs sgn(bs ⟨v₂, g⟩)` by
at least `E [2 t φ(0) F sgn⟨u, g⟩ - φ(0) (t³ |F|³ + 8 t |F| [|⟨u, g⟩| ≤ 4/3 t |F|])]`. -/
theorem edge_term {v₁ u : E} (hv₁ : ‖v₁‖ = 1) (hv₁u : ⟪v₁, u⟫ = 0) {ρ : ℝ}
    (hρ : ρ ^ 2 ≤ 16 / 25) {bs : ℝ} (hbs : bs = 1 ∨ bs = -1) {F : E → ℝ} (hF : Measurable F)
    (hFb : ∀ g, |F g| ≤ 1) (hFinv : ∀ y (c : ℝ), F (y + c • v₁) = F y) {t : ℝ} (ht : 0 ≤ t) :
    ∫ g, (2 * t * phi0 * F g * sgn ⟪u, g⟫ - phi0 * (t ^ 3 * |F g| ^ 3 +
        8 * t * |F g| * {g | |⟪u, g⟫| ≤ 4 / 3 * (t * |F g|)}.indicator 1 g)) ∂stdGaussian E ≤
      ∫ g, (sgn (⟪v₁, g⟫ + t * F g) - sgn ⟪v₁, g⟫) *
        (bs * sgn (bs * ⟪ρ • v₁ + √(1 - ρ ^ 2) • u, g⟫)) ∂stdGaussian E := by
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : 3 / 5 ≤ σ := by
    rw [hσdef, show (3 / 5 : ℝ) = √((3 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h11 : ⟪v₁, v₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv₁, one_pow]
  have huv : ⟪u, v₁⟫ = 0 := by rw [real_inner_comm]; exact hv₁u
  have hφ0 := phi0_pos
  set B : Set E := {g | |⟪u, g⟫| ≤ 4 / 3 * (t * |F g|)} with hBdef
  have hBm : MeasurableSet B :=
    measurableSet_le (f := fun g ↦ |⟪u, g⟫|) (by fun_prop) (by fun_prop)
  -- The lower bound, as a function of `g`; it is invariant along `v₁`.
  set ℓ : E → ℝ := fun g ↦ 2 * t * phi0 * F g * sgn ⟪u, g⟫ - phi0 * (t ^ 3 * |F g| ^ 3 +
    8 * t * |F g| * B.indicator 1 g) with hℓdef
  set Φ : E → ℝ := fun g ↦ (sgn (⟪v₁, g⟫ + t * F g) - sgn ⟪v₁, g⟫) *
    (bs * sgn (bs * ⟪ρ • v₁ + σ • u, g⟫)) with hΦdef
  have hℓm : Measurable ℓ := by
    rw [hℓdef]
    have := measurable_one.indicator hBm (f := (1 : E → ℝ))
    fun_prop
  have hΦm : Measurable Φ := by rw [hΦdef]; fun_prop
  have hind : ∀ g, |B.indicator (1 : E → ℝ) g| ≤ 1 := by
    intro g
    simp only [indicator]
    split_ifs <;> simp
  have hℓb : ∀ g, |ℓ g| ≤ 2 * t * phi0 + phi0 * (t ^ 3 + 8 * t) := by
    intro g
    have h1 := hFb g
    have h2 := hind g
    have h3 : |sgn ⟪u, g⟫| = 1 := abs_sgn _
    have h4 : |F g| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) h1
    have h5 : 0 ≤ B.indicator (1 : E → ℝ) g := indicator_nonneg (fun _ _ ↦ zero_le_one) g
    have h6 : B.indicator (1 : E → ℝ) g ≤ 1 := (le_abs_self _).trans h2
    have hnn : 0 ≤ t ^ 3 * |F g| ^ 3 + 8 * t * |F g| * B.indicator 1 g :=
      add_nonneg (mul_nonneg (pow_nonneg ht 3) (pow_nonneg (abs_nonneg _) 3))
        (mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) h5)
    have hle : t ^ 3 * |F g| ^ 3 + 8 * t * |F g| * B.indicator 1 g ≤ t ^ 3 + 8 * t := by
      have : t * |F g| * B.indicator (1 : E → ℝ) g ≤ t := by
        calc t * |F g| * B.indicator (1 : E → ℝ) g ≤ t * 1 * 1 := by gcongr
          _ = t := by ring
      nlinarith [pow_nonneg ht 3]
    have h2t : 0 ≤ 2 * t * phi0 := mul_nonneg (by positivity) hφ0.le
    have e1 : |2 * t * phi0 * F g * sgn ⟪u, g⟫| ≤ 2 * t * phi0 := by
      rw [abs_mul, h3, mul_one, abs_mul, abs_of_nonneg h2t]
      exact mul_le_of_le_one_right h2t h1
    have e2 : |phi0 * (t ^ 3 * |F g| ^ 3 + 8 * t * |F g| * B.indicator 1 g)| ≤
        phi0 * (t ^ 3 + 8 * t) := by
      rw [abs_mul, abs_of_pos hφ0, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left hle hφ0.le
    rw [hℓdef]
    exact (abs_sub _ _).trans (add_le_add e1 e2)
  have hΦb : ∀ g, |Φ g| ≤ 2 := by
    intro g
    rw [hΦdef, abs_mul, abs_bs_mul_sgn hbs, mul_one]
    exact (abs_sub _ _).trans (by rw [abs_sgn, abs_sgn]; norm_num)
  -- Split along `v₁` and bound each slice with the one-dimensional estimate.
  rw [integral_split hv₁ hℓm hℓb, integral_split hv₁ hΦm hΦb]
  refine integral_mono ?_ ?_ fun g₂ ↦ ?_
  · refine integrable_of_abs_le (C := 2 * t * phi0 + phi0 * (t ^ 3 + 8 * t)) ?_ fun g₂ ↦ ?_
    · have : StronglyMeasurable (fun p : E × ℝ ↦ ℓ (perp v₁ p.1 + p.2 • v₁)) :=
        (hℓm.comp (by fun_prop)).stronglyMeasurable
      exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    · refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ z, |ℓ (perp v₁ g₂ + z • v₁)| ∂gaussianReal 0 1
          ≤ ∫ z, (2 * t * phi0 + phi0 * (t ^ 3 + 8 * t)) ∂gaussianReal 0 1 :=
            integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
              (ae_of_all _ fun _ ↦ hℓb _)
        _ = _ := by simp
  · refine integrable_of_abs_le (C := 2) ?_ fun g₂ ↦ ?_
    · have : StronglyMeasurable (fun p : E × ℝ ↦ Φ (perp v₁ p.1 + p.2 • v₁)) :=
        (hΦm.comp (by fun_prop)).stronglyMeasurable
      exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    · refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ z, |Φ (perp v₁ g₂ + z • v₁)| ∂gaussianReal 0 1
          ≤ ∫ z, (2 : ℝ) ∂gaussianReal 0 1 :=
            integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
              (ae_of_all _ fun _ ↦ hΦb _)
        _ = _ := by simp
  -- In the slice through `y = perp v₁ g₂`.
  set y := perp v₁ g₂ with hydef
  set H := ⟪u, y⟫ with hHdef
  have hpt : ∀ z : ℝ, ⟪v₁, y + z • v₁⟫ = z ∧ F (y + z • v₁) = F y ∧
      ⟪u, y + z • v₁⟫ = H ∧ ⟪ρ • v₁ + σ • u, y + z • v₁⟫ = ρ * z + σ * H := by
    intro z
    have hv₁y : ⟪v₁, y⟫ = 0 := inner_perp hv₁ g₂
    refine ⟨?_, hFinv y z, ?_, ?_⟩
    · rw [inner_add_right, hv₁y, inner_smul_right, h11]; ring
    · rw [inner_add_right, inner_smul_right, huv]; ring
    · rw [inner_add_left, inner_smul_left, inner_smul_left, inner_add_right, inner_add_right,
        inner_smul_right, inner_smul_right, hv₁y, h11, huv, ← hHdef]
      simp only [conj_trivial]
      ring
  have hℓc : ∀ z : ℝ, ℓ (y + z • v₁) = ℓ y := by
    intro z
    have := hpt z
    have h0 := hpt 0
    simp only [zero_smul, add_zero] at h0
    simp only [hℓdef, hBdef, indicator, mem_ofPred_eq, this.2.1, this.2.2.1, h0.2.2.1,
      Pi.one_apply]
  simp_rw [hℓc, integral_const, probReal_univ, one_smul]
  have hΦc : ∀ z : ℝ, Φ (y + z • v₁) =
      (sgn (z + t * F y) - sgn z) * (bs * sgn (bs * (ρ * z + σ * H))) := by
    intro z
    obtain ⟨h1, h2, -, h4⟩ := hpt z
    simp only [hΦdef, h1, h2, h4]
  simp_rw [hΦc]
  -- The one-dimensional estimate with `c = t F y`, `s₀ = sgn H`, `P = |H| ≤ 4/3 |c|`.
  have hS : Measurable fun z : ℝ ↦ bs * sgn (bs * (ρ * z + σ * H)) := by fun_prop
  have hSb : ∀ z : ℝ, |bs * sgn (bs * (ρ * z + σ * H))| ≤ 1 :=
    fun z ↦ (abs_bs_mul_sgn hbs).le
  have h1d := integral_sgn_sub_mul_ge hS hSb (s₀ := sgn H) (abs_sgn H).le (t * F y)
    (|H| ≤ 4 / 3 * |t * F y|) (fun hP z hz ↦ by
      have hP' : 4 / 3 * |t * F y| < |H| := not_le.1 hP
      have hρz : |ρ * z| < σ * |H| := by
        have hρ' : |ρ| ≤ 4 / 5 := by
          rw [← abs_of_pos (show (0 : ℝ) < 4 / 5 by norm_num)]
          exact sq_le_sq.1 (by norm_num; linarith)
        calc |ρ * z| = |ρ| * |z| := abs_mul _ _
          _ ≤ 4 / 5 * |t * F y| := by gcongr
          _ = 3 / 5 * (4 / 3 * |t * F y|) := by ring
          _ < 3 / 5 * |H| := by linarith
          _ ≤ σ * |H| := by gcongr
      have hne : ρ * z + σ * H ≠ 0 := by
        intro h0
        have : |ρ * z| = σ * |H| := by
          rw [show ρ * z = -(σ * H) by linarith, abs_neg, abs_mul, abs_of_pos (by linarith)]
        linarith
      rw [sgn_mul_self_eq hbs hne]
      -- `ρ z + σ H` has the sign of `H`.
      unfold sgn
      rcases le_or_gt 0 H with hH | hH
      · rw [ite_eq_left hH, ite_eq_left]
        have := neg_abs_le (ρ * z)
        rw [abs_of_nonneg hH] at hρz
        nlinarith
      · rw [ite_eq_right (not_le.2 hH), ite_eq_right]
        have := le_abs_self (ρ * z)
        rw [abs_of_neg hH] at hρz
        nlinarith)
  refine le_trans (le_of_eq ?_) h1d
  have hFy : F y = F g₂ := by
    rw [hydef, perp, sub_eq_add_neg, ← neg_smul, hFinv]
  simp only [hℓdef, hBdef, indicator, mem_ofPred_eq, ← hHdef, abs_mul, abs_of_nonneg ht,
    Pi.one_apply]
  split_ifs <;> ring

end Edge

/-! ### The bounds per edge and per pair -/

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem vote_add_smul {p : ι → ℝ} {u : ι → E} {v₁ : E} (huv : ∀ k, ⟪u k, v₁⟫ = 0) (a : ℝ)
    (y : E) (c : ℝ) : vote p u a (y + c • v₁) = vote p u a y := by
  simp [vote, inner_add_right, inner_smul_right, huv]

/-- **One edge, with the strip lemma** [BGHKLMM26, Lemmas 3.16–3.18]: the change across an edge
is at least `2 t φ(0) E f sgn⟨w, g⟩ - φ(0) (t³ + 32 t² / √(1 - r²)) a` for the smoothed vote
`f = f_(r²)` and its energy `a = E f ψ`. -/
theorem dir_bound {p : ι → ℝ} {u : ι → E} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k ≤ 1)
    (hu : ∀ k, ‖u k‖ = 1) {v₁ w : E} (hv₁ : ‖v₁‖ = 1) (huv : ∀ k, ⟪u k, v₁⟫ = 0)
    (hw : ‖w‖ = 1) (hv₁w : ⟪v₁, w⟫ = 0) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 16 / 25) {bs : ℝ}
    (hbs : bs = 1 ∨ bs = -1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ √(1 - r ^ 2) / 100) :
    2 * t * phi0 * (∫ g, vote p u (r * r) g * sgn ⟪w, g⟫ ∂stdGaussian E) -
        phi0 * (t ^ 3 + 32 * t ^ 2 * (√(1 - r ^ 2))⁻¹) *
          ∫ g, vote p u (r * r) g * vote p u 1 g ∂stdGaussian E ≤
      ∫ g, (sgn (⟪v₁, g⟫ + t * vote p u (r * r) g) - sgn ⟪v₁, g⟫) *
        (bs * sgn (bs * ⟪ρ • v₁ + √(1 - ρ ^ 2) • w, g⟫)) ∂stdGaussian E := by
  set F := vote p u (r * r) with hFdef
  set h := vote p u r with hhdef
  set a := ∫ g, F g * vote p u 1 g ∂stdGaussian E with hadef
  set τ := √(1 - r ^ 2) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 (by nlinarith)
  have hτ2 : τ ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  have hFm : Measurable F := measurable_vote p u _
  have hFb : ∀ g, |F g| ≤ 1 := abs_vote_le hp0 hp1 u _
  have hhm : Measurable h := measurable_vote p u _
  have hhb : ∀ g, |h g| ≤ 1 := abs_vote_le hp0 hp1 u _
  have hFou : ∀ g, F g = ou r h g := vote_eq_ou p hu hr0.le hr1.le
  have hrr1 : r * r < 1 := by nlinarith
  have ha : ∫ g, h g ^ 2 ∂stdGaussian E = a := integral_vote_sq p hu hr0.le hr1.le
  have hedge := edge_term hv₁ hv₁w hρ hbs hFm hFb (vote_add_smul huv _) ht0
  refine le_trans ?_ hedge
  set B : Set E := {g | |⟪w, g⟫| ≤ 4 / 3 * (t * |F g|)} with hBdef
  have hBm : MeasurableSet B :=
    measurableSet_le (f := fun g ↦ |⟪w, g⟫|) (by fun_prop) (by fun_prop)
  have hind : ∀ g, |B.indicator (1 : E → ℝ) g| ≤ 1 := by
    intro g
    simp only [indicator]
    split_ifs <;> simp
  have hI1 : Integrable (fun g ↦ F g * sgn ⟪w, g⟫) (stdGaussian E) :=
    integrable_of_abs_le (C := 1) (by fun_prop) fun g ↦ by
      rw [abs_mul, abs_sgn, mul_one]; exact hFb g
  have hI2 : Integrable (fun g ↦ |F g| ^ 3) (stdGaussian E) :=
    integrable_of_abs_le (C := 1) (by fun_prop) fun g ↦ by
      rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (abs_nonneg _) (hFb g)
  have hI3 : Integrable (fun g ↦ |F g| * B.indicator 1 g) (stdGaussian E) :=
    integrable_of_abs_le (C := 1) ((continuous_abs.measurable.comp hFm).mul
      (measurable_one.indicator hBm)) fun g ↦ by
      rw [abs_mul, abs_abs]
      calc |F g| * |B.indicator 1 g| ≤ 1 * 1 := mul_le_mul (hFb g) (hind g) (abs_nonneg _)
            zero_le_one
        _ = 1 := one_mul 1
  -- `E |f|³ ≤ E f² ≤ a` and the one-strip bound `E |f| [strip] ≤ 4 t a / τ`.
  have hcube : ∫ g, |F g| ^ 3 ∂stdGaussian E ≤ a := by
    refine le_trans ?_ (integral_vote_sq_le p hu (by positivity) hrr1)
    refine integral_mono hI2 (integrable_of_abs_le (C := 1) (by fun_prop) fun g ↦ ?_) fun g ↦ ?_
    · rw [abs_mul]
      calc |F g| * |F g| ≤ 1 * 1 := mul_le_mul (hFb g) (hFb g) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · have h1 := hFb g
      have : |F g| ^ 3 ≤ |F g| ^ 2 := pow_le_pow_of_le_one (abs_nonneg _) h1 (by norm_num)
      rw [sq_abs] at this
      simpa [sq] using this
  have hstrip : ∫ g, |F g| * B.indicator 1 g ∂stdGaussian E ≤ 4 * t * τ⁻¹ * a := by
    have := one_strip hr0 hr1 hhm hhb hw (t := 4 / 3 * t) (by positivity) (by
      have h1 : (4 / 3 * t) ^ 2 ≤ τ ^ 2 := by
        have : 4 / 3 * t ≤ τ := by linarith
        exact pow_le_pow_left₀ (by positivity) this 2
      rw [← hτ2]
      nlinarith [sq_nonneg (4 / 3 * t)])
    rw [ha] at this
    have heq : (fun g ↦ |F g| * B.indicator 1 g) = fun g ↦
        |ou r h g| * {g | |⟪w, g⟫| ≤ 4 / 3 * t * |ou r h g|}.indicator 1 g := by
      funext g
      simp only [hBdef, hFou, mul_assoc]
    rw [heq]
    calc _ ≤ 3 * (4 / 3 * t) * (τ⁻¹ * a) := this
      _ = 4 * t * τ⁻¹ * a := by ring
  have hlin : ∫ g, (2 * t * phi0 * F g * sgn ⟪w, g⟫ - phi0 * (t ^ 3 * |F g| ^ 3 +
      8 * t * |F g| * B.indicator 1 g)) ∂stdGaussian E =
      2 * t * phi0 * (∫ g, F g * sgn ⟪w, g⟫ ∂stdGaussian E) -
        phi0 * (t ^ 3 * ∫ g, |F g| ^ 3 ∂stdGaussian E +
          8 * t * ∫ g, |F g| * B.indicator 1 g ∂stdGaussian E) := by
    have e1 : ∀ g, 2 * t * phi0 * F g * sgn ⟪w, g⟫ = 2 * t * phi0 * (F g * sgn ⟪w, g⟫) := by
      intro g; ring
    have e2 : ∀ g, phi0 * (t ^ 3 * |F g| ^ 3 + 8 * t * |F g| * B.indicator 1 g) =
        phi0 * (t ^ 3 * |F g| ^ 3 + 8 * t * (|F g| * B.indicator 1 g)) := by
      intro g; ring
    simp_rw [e1, e2]
    have hJ : Integrable (fun g ↦ phi0 * (t ^ 3 * |F g| ^ 3 + 8 * t * (|F g| * B.indicator 1 g)))
        (stdGaussian E) := ((hI2.const_mul (t ^ 3)).add (hI3.const_mul (8 * t))).const_mul phi0
    rw [integral_sub (hI1.const_mul _) hJ, integral_const_mul, integral_const_mul,
      integral_add (hI2.const_mul _) (hI3.const_mul _), integral_const_mul, integral_const_mul]
  rw [hlin]
  have hφ := phi0_pos
  have ha0 : 0 ≤ a := by rw [← ha]; exact integral_nonneg fun _ ↦ sq_nonneg _
  have : t ^ 3 * ∫ g, |F g| ^ 3 ∂stdGaussian E +
      8 * t * ∫ g, |F g| * B.indicator 1 g ∂stdGaussian E ≤
      (t ^ 3 + 32 * t ^ 2 * τ⁻¹) * a := by
    have h1 : t ^ 3 * ∫ g, |F g| ^ 3 ∂stdGaussian E ≤ t ^ 3 * a :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    have h2 : 8 * t * ∫ g, |F g| * B.indicator 1 g ∂stdGaussian E ≤ 8 * t * (4 * t * τ⁻¹ * a) :=
      mul_le_mul_of_nonneg_left hstrip (by positivity)
    nlinarith
  nlinarith

/-- A sign moved by `t F` changes only if `|X| ≤ t |F|`. -/
theorem sgn_sub_ne_zero {X F t : ℝ} (ht : 0 ≤ t) (h : sgn (X + t * F) - sgn X ≠ 0) :
    |X| ≤ t * |F| := by
  unfold sgn at h
  by_cases hX : 0 ≤ X <;> by_cases hXF : 0 ≤ X + t * F
  · simp [hX, hXF] at h
  · rw [abs_of_nonneg hX]
    have := neg_abs_le F
    nlinarith
  · rw [abs_of_neg (not_le.1 hX)]
    have := le_abs_self F
    nlinarith
  · simp [hX, hXF] at h

/-- **One pair, with the two-strip lemma** [BGHKLMM26, Lemma 3.19]: the joint change of the two
endpoints of an edge costs at most `20 t² (aᵢ + aⱼ) / √(1 - r²)`. -/
theorem pair_bound {p₁ : ι → ℝ} {u₁ : ι → E} (hp₁0 : ∀ k, 0 ≤ p₁ k) (hp₁1 : ∑ k, p₁ k ≤ 1)
    (hu₁ : ∀ k, ‖u₁ k‖ = 1) {p₂ : κ → ℝ} {u₂ : κ → E} (hp₂0 : ∀ k, 0 ≤ p₂ k)
    (hp₂1 : ∑ k, p₂ k ≤ 1) (hu₂ : ∀ k, ‖u₂ k‖ = 1) {v₁ w : E} (hv₁ : ‖v₁‖ = 1)
    (hw : ‖w‖ = 1) (hv₁w : ⟪v₁, w⟫ = 0) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 16 / 25)
    (huv₁ : ∀ k, ⟪u₁ k, v₁⟫ = 0) (huv₂ : ∀ k, ⟪u₂ k, ρ • v₁ + √(1 - ρ ^ 2) • w⟫ = 0)
    {bs : ℝ} (hbs : bs = 1 ∨ bs = -1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ √(1 - r ^ 2) / 100) :
    -(20 * t ^ 2 * (√(1 - r ^ 2))⁻¹ *
        ((∫ g, vote p₁ u₁ (r * r) g * vote p₁ u₁ 1 g ∂stdGaussian E) +
          ∫ g, vote p₂ u₂ (r * r) g * vote p₂ u₂ 1 g ∂stdGaussian E)) ≤
      ∫ g, bs * ((sgn (⟪v₁, g⟫ + t * vote p₁ u₁ (r * r) g) - sgn ⟪v₁, g⟫) *
        (sgn (⟪bs • (ρ • v₁ + √(1 - ρ ^ 2) • w), g⟫ + t * vote p₂ u₂ (r * r) g) -
          sgn ⟪bs • (ρ • v₁ + √(1 - ρ ^ 2) • w), g⟫)) ∂stdGaussian E := by
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : 3 / 5 ≤ σ := by
    rw [hσdef, show (3 / 5 : ℝ) = √((3 / 5) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  set v₂ := ρ • v₁ + σ • w with hv₂def
  set τ := √(1 - r ^ 2) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 (by nlinarith)
  have hτ2 : τ ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  set F₁ := vote p₁ u₁ (r * r) with hF₁def
  set F₂ := vote p₂ u₂ (r * r) with hF₂def
  set h₁ := vote p₁ u₁ r
  set h₂ := vote p₂ u₂ r
  have hF₁ou : ∀ g, F₁ g = ou r h₁ g := vote_eq_ou p₁ hu₁ hr0.le hr1.le
  have hF₂ou : ∀ g, F₂ g = ou r h₂ g := vote_eq_ou p₂ hu₂ hr0.le hr1.le
  have ha₁ : ∫ g, h₁ g ^ 2 ∂stdGaussian E = ∫ g, F₁ g * vote p₁ u₁ 1 g ∂stdGaussian E :=
    integral_vote_sq p₁ hu₁ hr0.le hr1.le
  have ha₂ : ∫ g, h₂ g ^ 2 ∂stdGaussian E = ∫ g, F₂ g * vote p₂ u₂ 1 g ∂stdGaussian E :=
    integral_vote_sq p₂ hu₂ hr0.le hr1.le
  have hbs2 : bs * bs = 1 := by rcases hbs with rfl | rfl <;> norm_num
  have habs : ∀ g, |⟪bs • v₂, g⟫| = |⟪v₂, g⟫| := by
    intro g
    rw [inner_smul_left, conj_trivial, abs_mul]
    rcases hbs with rfl | rfl <;> simp
  set S := {g : E | |⟪v₁, g⟫| ≤ t * |ou r h₁ g| ∧ |⟪v₂, g⟫| ≤ t * |ou r h₂ g|} with hSdef
  have hSm : MeasurableSet S :=
    (measurableSet_le (f := fun g ↦ |⟪v₁, g⟫|) (by fun_prop)
      (measurable_const.mul (continuous_abs.measurable.comp
        (measurable_ou (measurable_vote p₁ u₁ r))))).inter
      (measurableSet_le (f := fun g ↦ |⟪v₂, g⟫|) (by fun_prop)
        (measurable_const.mul (continuous_abs.measurable.comp
          (measurable_ou (measurable_vote p₂ u₂ r)))))
  -- Pointwise: the integrand is at least `-4 [S]`.
  have hpt : ∀ g, -(4 * S.indicator (1 : E → ℝ) g) ≤
      bs * ((sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫) *
        (sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫)) := by
    intro g
    by_cases h1 : sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫ = 0
    · rw [h1]; simp [indicator_nonneg]
    by_cases h2 : sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫ = 0
    · rw [h2]; simp [indicator_nonneg]
    have hg : g ∈ S := by
      refine ⟨?_, ?_⟩
      · rw [← hF₁ou]; exact sgn_sub_ne_zero ht0 h1
      · rw [← hF₂ou, ← habs]; exact sgn_sub_ne_zero ht0 h2
    rw [indicator_of_mem hg, Pi.one_apply, mul_one]
    have hb : |bs * ((sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫) *
        (sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫))| ≤ 4 := by
      rw [abs_mul, abs_mul, show |bs| = 1 by rcases hbs with rfl | rfl <;> norm_num, one_mul]
      have e1 : |sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫| ≤ 2 :=
        (abs_sub _ _).trans (by rw [abs_sgn, abs_sgn]; norm_num)
      have e2 : |sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫| ≤ 2 :=
        (abs_sub _ _).trans (by rw [abs_sgn, abs_sgn]; norm_num)
      nlinarith [abs_nonneg (sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫),
        abs_nonneg (sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫)]
    exact neg_le_of_abs_le hb
  have hint : Integrable (fun g ↦ bs * ((sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫) *
      (sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫))) (stdGaussian E) := by
    refine integrable_of_abs_le (C := 4) (by
      have := measurable_vote p₁ u₁ (r * r)
      have := measurable_vote p₂ u₂ (r * r)
      fun_prop) fun g ↦ ?_
    rw [abs_mul, abs_mul, show |bs| = 1 by rcases hbs with rfl | rfl <;> norm_num, one_mul]
    have e1 : |sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫| ≤ 2 :=
      (abs_sub _ _).trans (by rw [abs_sgn, abs_sgn]; norm_num)
    have e2 : |sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫| ≤ 2 :=
      (abs_sub _ _).trans (by rw [abs_sgn, abs_sgn]; norm_num)
    nlinarith [abs_nonneg (sgn (⟪v₁, g⟫ + t * F₁ g) - sgn ⟪v₁, g⟫),
      abs_nonneg (sgn (⟪bs • v₂, g⟫ + t * F₂ g) - sgn ⟪bs • v₂, g⟫)]
  have hSi : Integrable (fun g ↦ -(4 * S.indicator (1 : E → ℝ) g)) (stdGaussian E) :=
    (((integrable_const (1 : ℝ)).indicator hSm).const_mul 4).neg
  have hlow := integral_mono hSi hint hpt
  rw [integral_neg, integral_const_mul, integral_indicator_one hSm] at hlow
  -- The two-strip lemma.
  have hstrip := two_strip hr0 hr1 (measurable_vote p₁ u₁ r) (measurable_vote p₂ u₂ r)
    (abs_vote_le hp₁0 hp₁1 u₁ r) (abs_vote_le hp₂0 hp₂1 u₂ r) hv₁ hw hv₁w
    (show ρ ^ 2 < 1 by linarith) (vote_add_smul huv₁ r) (vote_add_smul huv₂ r) ht0 (by
      have hσ0 : 0 < σ := by linarith
      have h1 : 2 * t / σ ≤ τ := by
        rw [div_le_iff₀ hσ0]
        nlinarith
      have h2 : (2 * t / σ) ^ 2 ≤ τ ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      rw [← hτ2]
      nlinarith [sq_nonneg (2 * t / σ)])
  rw [ha₁, ha₂] at hstrip
  refine le_trans ?_ hlow
  have hσ0 : 0 < σ := by linarith
  have hA : 0 ≤ (∫ g, F₁ g * vote p₁ u₁ 1 g ∂stdGaussian E) +
      ∫ g, F₂ g * vote p₂ u₂ 1 g ∂stdGaussian E := by
    rw [← ha₁, ← ha₂]
    exact add_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  have h3 : 3 * t ^ 2 / σ ≤ 5 * t ^ 2 := by
    rw [div_le_iff₀ hσ0]
    nlinarith [sq_nonneg t]
  have h4 : 3 * t ^ 2 / σ * (τ⁻¹ * ((∫ g, F₁ g * vote p₁ u₁ 1 g ∂stdGaussian E) +
      ∫ g, F₂ g * vote p₂ u₂ 1 g ∂stdGaussian E)) ≤
      5 * t ^ 2 * (τ⁻¹ * ((∫ g, F₁ g * vote p₁ u₁ 1 g ∂stdGaussian E) +
        ∫ g, F₂ g * vote p₂ u₂ 1 g ∂stdGaussian E)) :=
    mul_le_mul_of_nonneg_right h3 (by positivity)
  nlinarith

end Bounds

/-! ### The rounding -/

section Rounding

open GW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : ℕ → E)

/-- `ρᵢⱼ = b ⟨vᵢ, vⱼ⟩` for a constraint `xᵢ xⱼ = b`. -/
noncomputable def rho (i j : ℕ) (b : Bool) : ℝ := bsign b * ⟪v i, v j⟫

/-- The direction `u_{i→j} = (b vⱼ - ρᵢⱼ vᵢ) / √(1 - ρᵢⱼ²)`, so that `hᵢⱼ = ⟨u_{i→j}, g⟩`. -/
noncomputable def dirVec (i j : ℕ) (b : Bool) : E :=
  (√(1 - rho v i j b ^ 2))⁻¹ • (bsign b • v j - rho v i j b • v i)

/-- The out-edges `(j, b, w)` of `i` among the constraints `T`: one for each constraint on
`{i, j}`. -/
def outEdges (T : List Constraint) (i : ℕ) : List (ℕ × Bool × ℚ) :=
  T.filterMap fun c ↦ if c.1.1 = i then some (c.1.2, c.2.1, c.2.2)
    else if c.1.2 = i then some (c.1.1, c.2.1, c.2.2) else none

/-- The weighted degree `Wᵢ` of `i` in `T`. -/
noncomputable def wdeg (T : List Constraint) (i : ℕ) : ℝ :=
  ((outEdges T i).map fun e ↦ (e.2.2 : ℝ)).sum

/-- The weights `pₖ = wₖ / Wᵢ` of the out-edges of `i`. -/
noncomputable def outW (T : List Constraint) (i : ℕ) (k : Fin (outEdges T i).length) : ℝ :=
  ((outEdges T i)[k.1].2.2 : ℝ) / wdeg T i

/-- The directions `u_{i→j}` of the out-edges of `i`. -/
noncomputable def outU (T : List Constraint) (i : ℕ) (k : Fin (outEdges T i).length) : E :=
  dirVec v i (outEdges T i)[k.1].1 (outEdges T i)[k.1].2.1

/-- The smoothed vote `fᵢ = U_a ψᵢ` of `i` [BGHKLMM26, Algorithm 1, line 6]. -/
noncomputable def fvote [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : List Constraint) (a : ℝ) (i : ℕ) (g : E) : ℝ :=
  vote (outW T i) (outU v T i) a g

/-- Hyperplane rounding `x⁰ᵢ = [⟨vᵢ, g⟩ ≥ 0]`. -/
noncomputable def round0 (g : E) (i : ℕ) : Bool := decide (0 ≤ ⟪v i, g⟫)

/-- The shifted rounding `x^λᵢ = [⟨vᵢ, g⟩ + λ fᵢ ≥ 0]` [BGHKLMM26, Algorithm 1, line 7], with
`fᵢ = U_η ψᵢ`. -/
noncomputable def roundL [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : List Constraint) (η t : ℝ) (g : E) (i : ℕ) : Bool :=
  decide (0 ≤ ⟪v i, g⟫ + t * fvote v T η i g)

/-- The value of a rounding by signs: a constraint `xᵢ xⱼ = b` of weight `w` contributes
`w (1 + b sgn Aᵢ sgn Aⱼ) / 2`. -/
theorem sat_decide (A : ℕ → ℝ) (c : Constraint) :
    (if decide (decide (0 ≤ A c.1.1) = decide (0 ≤ A c.1.2)) = c.2.1 then (c.2.2 : ℝ) else 0) =
      c.2.2 / 2 * (1 + bsign c.2.1 * sgn (A c.1.1) * sgn (A c.1.2)) := by
  unfold sgn bsign
  by_cases h1 : 0 ≤ A c.1.1 <;> by_cases h2 : 0 ≤ A c.1.2 <;> cases c.2.1 <;>
    simp [h1, h2] <;> ring

theorem satWeight_decide (n : ℕ) (T : List Constraint) (A : ℕ → ℝ) :
    satWeight (n, T) (fun i ↦ decide (0 ≤ A i)) =
      (T.map fun c ↦ (c.2.2 : ℝ) / 2 * (1 + bsign c.2.1 * sgn (A c.1.1) * sgn (A c.1.2))).sum := by
  unfold satWeight
  congr 1
  exact List.map_congr_left fun c _ ↦ sat_decide A c

/-- **Double counting** the directed edges: summing over the out-edges of every vertex `i < n`
counts each constraint once in each direction. -/
theorem sum_outEdges (n : ℕ) (T : List Constraint)
    (hT : ∀ c ∈ T, c.1.1 < c.1.2 ∧ c.1.2 < n) (Q : ℕ → ℕ × Bool × ℚ → ℝ) :
    ∑ i ∈ Finset.range n, ((outEdges T i).map (Q i)).sum =
      (T.map fun c ↦ Q c.1.1 (c.1.2, c.2.1, c.2.2) + Q c.1.2 (c.1.1, c.2.1, c.2.2)).sum := by
  induction T with
  | nil => simp [outEdges]
  | cons c T ih =>
    have hc := hT c List.mem_cons_self
    have hstep : ∀ i, ((outEdges (c :: T) i).map (Q i)).sum =
        ((if c.1.1 = i then Q i (c.1.2, c.2.1, c.2.2) else 0) +
          (if c.1.2 = i then Q i (c.1.1, c.2.1, c.2.2) else 0)) +
          ((outEdges T i).map (Q i)).sum := by
      intro i
      simp only [outEdges, List.filterMap_cons]
      by_cases h1 : c.1.1 = i
      · have h2 : c.1.2 ≠ i := by omega
        simp [h1, h2]
      · by_cases h2 : c.1.2 = i <;> simp [h1, h2]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
      ih fun c' hc' ↦ hT c' (List.mem_cons_of_mem _ hc'), List.map_cons, List.sum_cons,
      ite_eq_left (Finset.mem_range.2 (by omega)), ite_eq_left (Finset.mem_range.2 hc.2)]

/-- The direction `u_{i→j}` is a unit vector orthogonal to `vᵢ`, with
`b vⱼ = ρᵢⱼ vᵢ + √(1 - ρᵢⱼ²) u_{i→j}` [BGHKLMM26, Lemmas 3.6–3.8]. -/
theorem dirVec_spec {i j : ℕ} (b : Bool) (hi : ‖v i‖ = 1) (hj : ‖v j‖ = 1)
    (hρ : rho v i j b ^ 2 < 1) :
    ‖dirVec v i j b‖ = 1 ∧ ⟪v i, dirVec v i j b⟫ = 0 ∧
      bsign b • v j = rho v i j b • v i + √(1 - rho v i j b ^ 2) • dirVec v i j b := by
  set ρ := rho v i j b with hρdef
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by linarith)
  have hσ2 : σ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hb2 : bsign b ^ 2 = 1 := by cases b <;> simp [bsign]
  have hii : ⟪v i, v i⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hi, one_pow]
  have hjj : ⟪v j, v j⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hj, one_pow]
  have hρ' : ρ = bsign b * ⟪v i, v j⟫ := rfl
  set w := bsign b • v j - ρ • v i with hwdef
  have hw2 : ⟪w, w⟫ = σ ^ 2 := by
    rw [hwdef, hσ2]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hii, hjj,
      conj_trivial, real_inner_comm (v i) (v j)]
    rw [hρ']
    linear_combination hb2
  have hiw : ⟪v i, w⟫ = 0 := by
    rw [hwdef]
    simp only [inner_sub_right, inner_smul_right, hii, hρ']
    ring
  have hdir : dirVec v i j b = σ⁻¹ • w := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hdir, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hσ]
    have : ‖w‖ = σ := by
      rw [← Real.sqrt_sq (norm_nonneg w), ← real_inner_self_eq_norm_sq, hw2,
        Real.sqrt_sq hσ.le]
    rw [this, inv_mul_cancel₀ hσ.ne']
  · rw [hdir, inner_smul_right, hiw, mul_zero]
  · rw [hdir, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul, hwdef]
    abel

theorem rho_comm (i j : ℕ) (b : Bool) : rho v i j b = rho v j i b := by
  simp [rho, real_inner_comm]

theorem mem_outEdges {T : List Constraint} {i : ℕ} {e : ℕ × Bool × ℚ} (he : e ∈ outEdges T i) :
    ∃ c ∈ T, (c.1.1 = i ∧ e = (c.1.2, c.2.1, c.2.2)) ∨ (c.1.2 = i ∧ e = (c.1.1, c.2.1, c.2.2)) := by
  simp only [outEdges, List.mem_filterMap] at he
  obtain ⟨c, hc, hce⟩ := he
  refine ⟨c, hc, ?_⟩
  by_cases h1 : c.1.1 = i
  · rw [ite_eq_left h1, Option.some.injEq] at hce
    exact Or.inl ⟨h1, hce.symm⟩
  · rw [ite_eq_right h1] at hce
    by_cases h2 : c.1.2 = i
    · rw [ite_eq_left h2, Option.some.injEq] at hce
      exact Or.inr ⟨h2, hce.symm⟩
    · rw [ite_eq_right h2] at hce
      exact absurd hce (by simp)

theorem wdeg_nonneg {T : List Constraint} (hT : ∀ c ∈ T, 0 ≤ c.2.2) (i : ℕ) : 0 ≤ wdeg T i := by
  unfold wdeg
  refine List.sum_nonneg fun x hx ↦ ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  obtain ⟨c, hc, h | h⟩ := mem_outEdges he <;> rw [h.2] <;> exact_mod_cast hT c hc

theorem outEdges_w_nonneg {T : List Constraint} (hT : ∀ c ∈ T, 0 ≤ c.2.2) {i : ℕ}
    {e : ℕ × Bool × ℚ} (he : e ∈ outEdges T i) : (0 : ℝ) ≤ e.2.2 := by
  obtain ⟨c, hc, h | h⟩ := mem_outEdges he <;> rw [h.2] <;> exact_mod_cast hT c hc

theorem outW_nonneg {T : List Constraint} (hT : ∀ c ∈ T, 0 ≤ c.2.2) (i : ℕ)
    (k : Fin (outEdges T i).length) : 0 ≤ outW T i k :=
  div_nonneg (outEdges_w_nonneg hT (List.getElem_mem _)) (wdeg_nonneg hT i)

theorem sum_outW (T : List Constraint) (i : ℕ) :
    ∑ k, outW T i k = if wdeg T i = 0 then 0 else 1 := by
  simp only [outW]
  rw [← Finset.sum_div, Fin.sum_univ_fun_getElem (outEdges T i) (fun e ↦ (e.2.2 : ℝ))]
  change wdeg T i / wdeg T i = _
  split_ifs with h
  · rw [h, div_zero]
  · exact div_self h

theorem sum_outW_le (T : List Constraint) (i : ℕ) :
    ∑ k, outW T i k ≤ 1 := by
  rw [sum_outW]
  split_ifs <;> norm_num

/-- If `Wᵢ = 0`, every out-edge of `i` has weight `0`. -/
theorem w_eq_zero_of_wdeg {T : List Constraint} (hT : ∀ c ∈ T, 0 ≤ c.2.2) {i : ℕ}
    (h : wdeg T i = 0) {e : ℕ × Bool × ℚ} (he : e ∈ outEdges T i) : (e.2.2 : ℝ) = 0 := by
  unfold wdeg at h
  have hnn : ∀ x ∈ (outEdges T i).map fun e ↦ (e.2.2 : ℝ), 0 ≤ x := fun x hx ↦ by
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hx
    exact outEdges_w_nonneg hT he'
  have := List.single_le_sum hnn _ (List.mem_map_of_mem (f := fun e ↦ (e.2.2 : ℝ)) he)
  rw [h] at this
  exact le_antisymm this (outEdges_w_nonneg hT he)

/-- `∑ₑ wₑ φ(e) = Wᵢ ∑ₖ pₖ φ(eₖ)`. -/
theorem sum_outEdges_w {T : List Constraint} (hT : ∀ c ∈ T, 0 ≤ c.2.2) (i : ℕ)
    (φ : ℕ × Bool × ℚ → ℝ) :
    ((outEdges T i).map fun e ↦ (e.2.2 : ℝ) * φ e).sum =
      wdeg T i * ∑ k, outW T i k * φ (outEdges T i)[k.1] := by
  by_cases h : wdeg T i = 0
  · rw [h, zero_mul]
    refine List.sum_eq_zero fun x hx ↦ ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    rw [w_eq_zero_of_wdeg hT h he, zero_mul]
  · rw [Finset.mul_sum, ← Fin.sum_univ_fun_getElem (outEdges T i) (fun e ↦ (e.2.2 : ℝ) * φ e)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [outW]
    field_simp

end Rounding

/-! ### The gain [BGHKLMM26, Theorem 3.2] -/

section Gain

open GW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (v : ℕ → E)

omit [BorelSpace E] in
theorem integral_list_sum {α : Type*} (l : List α) (F : α → E → ℝ)
    (hF : ∀ c ∈ l, Integrable (F c) (stdGaussian E)) :
    ∫ g, (l.map fun c ↦ F c g).sum ∂stdGaussian E =
      (l.map fun c ↦ ∫ g, F c g ∂stdGaussian E).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    have hl : ∀ c ∈ l, Integrable (F c) (stdGaussian E) :=
      fun c' hc' ↦ hF c' (List.mem_cons_of_mem _ hc')
    have hint : Integrable (fun g ↦ (l.map fun c ↦ F c g).sum) (stdGaussian E) := by
      clear ih
      induction l with
      | nil => simp
      | cons c' l' ih' =>
        simp only [List.map_cons, List.sum_cons]
        exact (hl c' List.mem_cons_self).add
          (ih' (fun c'' hc'' ↦ hF c'' (by
            rcases List.mem_cons.1 hc'' with h | h
            · exact h ▸ List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
            (fun c'' hc'' ↦ hl c'' (List.mem_cons_of_mem _ hc'')))
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hF c List.mem_cons_self) hint, ih hl]

/-- The energy `aᵢ = E fᵢ ψᵢ` of vertex `i`. -/
noncomputable def energy (T : List Constraint) (η : ℝ) (i : ℕ) : ℝ :=
  ∫ g, fvote v T η i g * fvote v T 1 i g ∂stdGaussian E

/-- The lower bound on the gain from the out-edge `e = (j, b, w)` of `i`: the edge's main term
`λ φ(0) E fᵢ sgn hᵢⱼ`, its error terms, and half of the edge's pair term. -/
noncomputable def gainQ (T : List Constraint) (r t : ℝ) (i : ℕ) (e : ℕ × Bool × ℚ) : ℝ :=
  (e.2.2 : ℝ) / 2 * (2 * t * phi0 * ∫ g, fvote v T (r * r) i g * sgn ⟪dirVec v i e.1 e.2.1, g⟫
      ∂stdGaussian E -
    (phi0 * (t ^ 3 + 32 * t ^ 2 * (√(1 - r ^ 2))⁻¹) + 20 * t ^ 2 * (√(1 - r ^ 2))⁻¹) *
      energy v T (r * r) i)

theorem bsign_cases (b : Bool) : bsign b = 1 ∨ bsign b = -1 := by cases b <;> simp [bsign]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The out-edge directions of a vertex are unit vectors orthogonal to it. -/
theorem outU_spec {n : ℕ} {T : List Constraint}
    (hT : ∀ c ∈ T, c.1.1 < c.1.2 ∧ c.1.2 < n ∧ 0 ≤ c.2.2) (hv : ∀ i < n, ‖v i‖ = 1)
    (hρ : ∀ c ∈ T, rho v c.1.1 c.1.2 c.2.1 ^ 2 ≤ 16 / 25) (i : ℕ)
    (k : Fin (outEdges T i).length) : ‖outU v T i k‖ = 1 ∧ ⟪outU v T i k, v i⟫ = 0 := by
  have he : (outEdges T i)[k.1] ∈ outEdges T i := List.getElem_mem _
  obtain ⟨c, hc, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := mem_outEdges he
  · obtain ⟨hij, hjn, -⟩ := hT c hc
    have hspec := dirVec_spec v c.2.1 (hv i (h1 ▸ hij.trans hjn)) (hv _ hjn)
      (by rw [← h1]; linarith [hρ c hc])
    simp only [outU, h2]
    exact ⟨hspec.1, by rw [real_inner_comm]; exact hspec.2.1⟩
  · obtain ⟨hij, hjn, -⟩ := hT c hc
    have hspec := dirVec_spec v c.2.1 (hv i (h1 ▸ hjn)) (hv _ (hij.trans hjn))
      (by rw [← h1, ← rho_comm]; linarith [hρ c hc])
    simp only [outU, h2]
    exact ⟨hspec.1, by rw [real_inner_comm]; exact hspec.2.1⟩

/-- **The gain on one constraint** [BGHKLMM26, Lemmas 3.16–3.19]: the change of the expected
weight of `c = (xᵢ xⱼ = b, w)` is at least the lower bounds of its two directed edges. -/
theorem constraint_gain {n : ℕ} {T : List Constraint}
    (hT : ∀ c ∈ T, c.1.1 < c.1.2 ∧ c.1.2 < n ∧ 0 ≤ c.2.2) (hv : ∀ i < n, ‖v i‖ = 1)
    (hρ : ∀ c ∈ T, rho v c.1.1 c.1.2 c.2.1 ^ 2 ≤ 16 / 25) {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (ht0 : 0 ≤ t) (ht : t ≤ √(1 - r ^ 2) / 100) {c : Constraint} (hc : c ∈ T) :
    gainQ v T r t c.1.1 (c.1.2, c.2.1, c.2.2) + gainQ v T r t c.1.2 (c.1.1, c.2.1, c.2.2) ≤
      (∫ g, (c.2.2 : ℝ) / 2 * (1 + bsign c.2.1 *
        sgn (⟪v c.1.1, g⟫ + t * fvote v T (r * r) c.1.1 g) *
        sgn (⟪v c.1.2, g⟫ + t * fvote v T (r * r) c.1.2 g)) ∂stdGaussian E) -
      ∫ g, (c.2.2 : ℝ) / 2 * (1 + bsign c.2.1 * sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫)
        ∂stdGaussian E := by
  obtain ⟨hij, hjn, hw0⟩ := hT c hc
  set i := c.1.1 with hidef
  set j := c.1.2 with hjdef
  set b := c.2.1 with hbdef
  set w : ℝ := (c.2.2 : ℝ) with hwdef
  have hw0' : 0 ≤ w := by rw [hwdef]; exact_mod_cast hw0
  set bs := bsign b with hbsdef
  have hbs : bs = 1 ∨ bs = -1 := bsign_cases b
  have hbs2 : bs * bs = 1 := by rcases hbs with h | h <;> rw [h] <;> norm_num
  have hi : ‖v i‖ = 1 := hv i (hij.trans hjn)
  have hj : ‖v j‖ = 1 := hv j hjn
  set ρ := rho v i j b with hρdef
  have hρc : ρ ^ 2 ≤ 16 / 25 := hρ c hc
  have hρ' : rho v j i b = ρ := (rho_comm v i j b).symm
  obtain ⟨hu1, hvu1, hdec1⟩ := dirVec_spec v b hi hj (by linarith)
  obtain ⟨hu2, hvu2, hdec2⟩ := dirVec_spec v b hj hi (by rw [hρ']; linarith)
  rw [hρ'] at hdec2
  set u := dirVec v i j b with hudef
  set u' := dirVec v j i b with hu'def
  have hTw : ∀ c ∈ T, 0 ≤ c.2.2 := fun c hc ↦ (hT c hc).2.2
  have hspec := outU_spec v hT hv hρ
  -- The two directed edges and the pair.
  have hdir1 := dir_bound (outW_nonneg hTw i) (sum_outW_le T i) (fun k ↦ (hspec i k).1) hi
    (fun k ↦ (hspec i k).2) hu1 hvu1 hρc hbs hr0 hr1 ht0 ht
  have hdir2 := dir_bound (outW_nonneg hTw j) (sum_outW_le T j) (fun k ↦ (hspec j k).1) hj
    (fun k ↦ (hspec j k).2) hu2 hvu2 hρc hbs hr0 hr1 ht0 ht
  have hpair := pair_bound (outW_nonneg hTw i) (sum_outW_le T i) (fun k ↦ (hspec i k).1)
    (outW_nonneg hTw j) (sum_outW_le T j) (fun k ↦ (hspec j k).1) hi hu1 hvu1 hρc
    (fun k ↦ (hspec i k).2) (fun k ↦ by
      rw [← hdec1, inner_smul_right, (hspec j k).2, mul_zero]) hbs hr0 hr1 ht0 ht
  have hk1 : ∀ g, bs * ⟪ρ • v i + √(1 - ρ ^ 2) • u, g⟫ = ⟪v j, g⟫ := by
    intro g
    rw [← hdec1, inner_smul_left, conj_trivial, ← mul_assoc, hbs2, one_mul]
  have hk2 : ∀ g, bs * ⟪ρ • v j + √(1 - ρ ^ 2) • u', g⟫ = ⟪v i, g⟫ := by
    intro g
    rw [← hdec2, inner_smul_left, conj_trivial, ← mul_assoc, hbs2, one_mul]
  have hk3 : bs • (ρ • v i + √(1 - ρ ^ 2) • u) = v j := by rw [← hdec1, smul_smul, hbs2, one_smul]
  simp_rw [hk1] at hdir1
  simp_rw [hk2] at hdir2
  rw [hk3] at hpair
  -- Integrability of the three pieces and the identity between them.
  simp only [gainQ, energy, fvote]
  rw [← hwdef]
  set Fi := vote (outW T i) (outU v T i) (r * r) with hFi
  set Fj := vote (outW T j) (outU v T j) (r * r) with hFj
  have hFim : Measurable Fi := measurable_vote _ _ _
  have hFjm : Measurable Fj := measurable_vote _ _ _
  have hbsb : |bs| = 1 := by rcases hbs with h | h <;> rw [h] <;> norm_num
  have hd : ∀ x y, |sgn x - sgn y| ≤ 2 := fun x y ↦
    (abs_sub _ _).trans (by rw [abs_sgn, abs_sgn]; norm_num)
  have hI1 : Integrable (fun g ↦ (sgn (⟪v i, g⟫ + t * Fi g) - sgn ⟪v i, g⟫) *
      (bs * sgn ⟪v j, g⟫)) (stdGaussian E) :=
    integrable_of_abs_le (C := 2) (by fun_prop) fun g ↦ by
      rw [abs_mul, abs_mul, hbsb, abs_sgn, one_mul, mul_one]; exact hd _ _
  have hI2 : Integrable (fun g ↦ (sgn (⟪v j, g⟫ + t * Fj g) - sgn ⟪v j, g⟫) *
      (bs * sgn ⟪v i, g⟫)) (stdGaussian E) :=
    integrable_of_abs_le (C := 2) (by fun_prop) fun g ↦ by
      rw [abs_mul, abs_mul, hbsb, abs_sgn, one_mul, mul_one]; exact hd _ _
  have hI3 : Integrable (fun g ↦ bs * ((sgn (⟪v i, g⟫ + t * Fi g) - sgn ⟪v i, g⟫) *
      (sgn (⟪v j, g⟫ + t * Fj g) - sgn ⟪v j, g⟫))) (stdGaussian E) :=
    integrable_of_abs_le (C := 4) (by fun_prop) fun g ↦ by
      rw [abs_mul, abs_mul, hbsb, one_mul]
      have h1 := hd (⟪v i, g⟫ + t * Fi g) ⟪v i, g⟫
      have h2 := hd (⟪v j, g⟫ + t * Fj g) ⟪v j, g⟫
      nlinarith [abs_nonneg (sgn (⟪v i, g⟫ + t * Fi g) - sgn ⟪v i, g⟫),
        abs_nonneg (sgn (⟪v j, g⟫ + t * Fj g) - sgn ⟪v j, g⟫)]
  have hP : ∀ x y : ℝ, |w / 2 * (1 + bs * sgn x * sgn y)| ≤ w := by
    intro x y
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have : |1 + bs * sgn x * sgn y| ≤ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, hbsb, abs_sgn, abs_sgn]
      norm_num
    nlinarith
  have hP1 : Integrable (fun g ↦ w / 2 * (1 + bs * sgn (⟪v i, g⟫ + t * Fi g) *
      sgn (⟪v j, g⟫ + t * Fj g))) (stdGaussian E) :=
    integrable_of_abs_le (C := w) (by fun_prop) fun g ↦ hP _ _
  have hP0 : Integrable (fun g ↦ w / 2 * (1 + bs * sgn ⟪v i, g⟫ * sgn ⟪v j, g⟫))
      (stdGaussian E) :=
    integrable_of_abs_le (C := w) (by fun_prop) fun g ↦ hP _ _
  rw [← integral_sub hP1 hP0]
  have hpt : (fun g ↦ w / 2 * (1 + bs * sgn (⟪v i, g⟫ + t * Fi g) * sgn (⟪v j, g⟫ + t * Fj g)) -
      w / 2 * (1 + bs * sgn ⟪v i, g⟫ * sgn ⟪v j, g⟫)) = fun g ↦ w / 2 *
      ((sgn (⟪v i, g⟫ + t * Fi g) - sgn ⟪v i, g⟫) * (bs * sgn ⟪v j, g⟫) +
        (sgn (⟪v j, g⟫ + t * Fj g) - sgn ⟪v j, g⟫) * (bs * sgn ⟪v i, g⟫) +
        bs * ((sgn (⟪v i, g⟫ + t * Fi g) - sgn ⟪v i, g⟫) *
          (sgn (⟪v j, g⟫ + t * Fj g) - sgn ⟪v j, g⟫))) := by
    funext g
    ring
  have hI12 : Integrable (fun g ↦ (sgn (⟪v i, g⟫ + t * Fi g) - sgn ⟪v i, g⟫) *
      (bs * sgn ⟪v j, g⟫) + (sgn (⟪v j, g⟫ + t * Fj g) - sgn ⟪v j, g⟫) * (bs * sgn ⟪v i, g⟫))
      (stdGaussian E) := hI1.add hI2
  rw [hpt, integral_const_mul, integral_add hI12 hI3, integral_add hI1 hI2]
  have hw2 : 0 ≤ w / 2 := by positivity
  have key := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hdir1 hdir2) hpair) hw2
  have hτ := Real.sqrt_nonneg (1 - r ^ 2)
  linarith

theorem phi0_ge : (0.39 : ℝ) ≤ phi0 := by
  unfold phi0
  rw [le_inv_comm₀ (by norm_num) (by positivity), Real.sqrt_le_left (by norm_num)]
  nlinarith [pi_lt_d2]

/-- **The gain at one vertex** [BGHKLMM26, Lemma 3.20 and Lemma 3.10]: the lower bounds of the
out-edges of `i` sum to `Wᵢ aᵢ (λ φ(0) - …) ≥ λ Wᵢ / (500 d √L)`. -/
theorem vertex_gain {n d : ℕ} {T : List Constraint}
    (hT : ∀ c ∈ T, c.1.1 < c.1.2 ∧ c.1.2 < n ∧ 0 ≤ c.2.2) (hv : ∀ i < n, ‖v i‖ = 1)
    (hρ : ∀ c ∈ T, rho v c.1.1 c.1.2 c.2.1 ^ 2 ≤ 16 / 25)
    (hdeg : ∀ i, (outEdges T i).length ≤ d)
    (hβ : ∀ i, ∀ k k' : Fin (outEdges T i).length, k ≠ k' →
      -(1 / 2) ≤ ⟪outU v T i k, outU v T i k'⟫)
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht : t ≤ √(1 - r ^ 2) / 100)
    {L : ℕ} (hL : 1 ≤ L) (hβL : (1 / 2 : ℝ) ^ (2 * L + 1) ≤ 1 / (2 * d))
    (hηL : 1 / 2 ≤ (r * r) ^ (4 * L + 1)) (i : ℕ) :
    t * wdeg T i / (500 * d * √L) ≤ ((outEdges T i).map (gainQ v T r t i)).sum := by
  have hTw : ∀ c ∈ T, 0 ≤ c.2.2 := fun c hc ↦ (hT c hc).2.2
  have hspec := outU_spec v hT hv hρ
  set τ := √(1 - r ^ 2) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 (by nlinarith)
  have hτ1 : τ ≤ 1 := by rw [hτdef, Real.sqrt_le_one]; nlinarith
  set a := energy v T (r * r) i with hadef
  set W := wdeg T i with hWdef
  have hW0 : 0 ≤ W := wdeg_nonneg hTw i
  set K := phi0 * (t ^ 3 + 32 * t ^ 2 * τ⁻¹) + 20 * t ^ 2 * τ⁻¹ with hKdef
  have ha0 : 0 ≤ a := by
    rw [hadef, energy]
    simp only [fvote]
    rw [← integral_vote_sq _ (fun k ↦ (hspec i k).1) hr0.le hr1.le]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  -- `∑ₑ gainQ = W a (t φ(0) - K/2)`.
  have hsum : ((outEdges T i).map (gainQ v T r t i)).sum = W * a * (t * phi0 - K / 2) := by
    have h1 : ∀ e : ℕ × Bool × ℚ, gainQ v T r t i e = (e.2.2 : ℝ) * ((t * phi0) *
        ∫ g, fvote v T (r * r) i g * sgn ⟪dirVec v i e.1 e.2.1, g⟫ ∂stdGaussian E - K / 2 * a) := by
      intro e
      simp only [gainQ, hKdef, hadef, hτdef]
      ring
    rw [show gainQ v T r t i = _ from funext h1, sum_outEdges_w hTw i]
    have h2 : ∑ k, outW T i k * (t * phi0 * ∫ g, fvote v T (r * r) i g *
        sgn ⟪dirVec v i (outEdges T i)[k.1].1 (outEdges T i)[k.1].2.1, g⟫ ∂stdGaussian E -
          K / 2 * a) = t * phi0 * a - (∑ k, outW T i k) * (K / 2 * a) := by
      have hint : ∀ k : Fin (outEdges T i).length, Integrable (fun g ↦ outW T i k *
          (fvote v T (r * r) i g * sgn ⟪outU v T i k, g⟫)) (stdGaussian E) := by
        intro k
        refine (integrable_of_abs_le (C := 1) ?_ fun g ↦ ?_).const_mul _
        · exact (measurable_vote _ _ _).mul (by fun_prop)
        · rw [abs_mul, abs_sgn, mul_one]
          exact abs_vote_le (outW_nonneg hTw i) (sum_outW_le T i) _ _ _
      have hA : a = ∫ g, ∑ k, outW T i k * (fvote v T (r * r) i g * sgn ⟪outU v T i k, g⟫)
          ∂stdGaussian E := by
        rw [hadef, energy]
        congr 1
        funext g
        rw [fvote, fvote, vote_one, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
      have hA' : t * phi0 * a = ∑ k, outW T i k * (t * phi0 * ∫ g, fvote v T (r * r) i g *
          sgn ⟪outU v T i k, g⟫ ∂stdGaussian E) := by
        rw [hA, integral_finsetSum _ fun k _ ↦ hint k, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [integral_const_mul]
        ring
      rw [hA', Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [outU]
      ring
    rw [h2, sum_outW T i]
    split_ifs with hW
    · have hW' : W = 0 := hW
      simp [hW', hW]
    · ring
  rw [hsum]
  -- `t φ(0) - K/2 ≥ t/5` and `a ≥ 1/(100 d √L)` when `W > 0`.
  have htτ : t * τ⁻¹ ≤ 1 / 100 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hτ]
    linarith
  have ht1 : t ≤ 1 / 100 := by linarith
  have hφ := phi0_ge
  have hK : K / 2 ≤ t * (0.161 * phi0 + 0.1) := by
    have h1 : t ^ 3 ≤ t * (1 / 10000) := by
      have : t ^ 2 ≤ 1 / 10000 := by nlinarith
      nlinarith
    have h2 : t ^ 2 * τ⁻¹ ≤ t * (1 / 100) := by
      rw [sq, mul_assoc]
      exact mul_le_mul_of_nonneg_left htτ ht0
    rw [hKdef]
    nlinarith [phi0_pos]
  have hcoef : t / 5 ≤ t * phi0 - K / 2 := by nlinarith
  by_cases hW : W = 0
  · rw [hW]
    simp
  have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
  have hd1 : (1 : ℝ) ≤ d := by
    have hβL' := hβL
    by_contra h
    have hd0 : (d : ℝ) < 1 := not_le.1 h
    have : (d : ℝ) = 0 := by
      have : d = 0 := by exact_mod_cast (show d < 1 by exact_mod_cast hd0) |> Nat.lt_one_iff.1
      exact_mod_cast this
    rw [this, mul_zero, div_zero] at hβL'
    exact absurd hβL' (not_le.2 (by positivity))
  have hen := energy_ge (p := outW T i) (u := outU v T i) (E := E) (outW_nonneg hTw i)
    (by rw [sum_outW, ite_eq_right hW]) (fun k ↦ (hspec i k).1) (d := d)
    (by rw [Fintype.card_fin]; exact hdeg i) (β := 1 / 2) (by norm_num) (hβ i) hL hβL
    (by positivity) (by nlinarith) hηL
  have ha : 1 / (100 * d * √L) ≤ a := hen
  have hsL : 0 < √(L : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hL)
  calc t * W / (500 * d * √L) = W * (1 / (100 * d * √L)) * (t / 5) := by field_simp; ring
    _ ≤ W * a * (t * phi0 - K / 2) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left ha hW0) hcoef (by positivity)
        positivity

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem list_sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun c ↦ f c - g c).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem list_sum_map_two {α : Type*} (l : List α) (f : α → ℝ) :
    (l.map fun c ↦ f c + f c).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- **The gain** [BGHKLMM26, Theorem 3.2]. Let `T` be constraints `xᵢ xⱼ = b` on pairs `i < j < n`
with weights `w ≥ 0`, each vertex in at most `d` of them, and `vᵢ` unit vectors with
`ρᵢⱼ² ≤ (4/5)²` on `T` and `⟨u_{i→j}, u_{i→k}⟩ ≥ -1/2` for distinct out-edges. If
`0 < r < 1`, `0 ≤ λ ≤ √(1 - r²) / 100`, `(1/2)^(2L+1) ≤ 1/(2d)` and `(r²)^(4L+1) ≥ 1/2`, then the
rounding `x^λ` with `fᵢ = U_(r²) ψᵢ` gains at least `λ W_T / (250 d √L)` over hyperplane rounding
on `T`, where `W_T` is the total weight of `T`. -/
theorem gain {n d : ℕ} {T : List Constraint}
    (hT : ∀ c ∈ T, c.1.1 < c.1.2 ∧ c.1.2 < n ∧ 0 ≤ c.2.2) (hv : ∀ i < n, ‖v i‖ = 1)
    (hρ : ∀ c ∈ T, rho v c.1.1 c.1.2 c.2.1 ^ 2 ≤ 16 / 25)
    (hdeg : ∀ i, (outEdges T i).length ≤ d)
    (hβ : ∀ i, ∀ k k' : Fin (outEdges T i).length, k ≠ k' →
      -(1 / 2) ≤ ⟪outU v T i k, outU v T i k'⟫)
    {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (ht0 : 0 ≤ t) (ht : t ≤ √(1 - r ^ 2) / 100)
    {L : ℕ} (hL : 1 ≤ L) (hβL : (1 / 2 : ℝ) ^ (2 * L + 1) ≤ 1 / (2 * d))
    (hηL : 1 / 2 ≤ (r * r) ^ (4 * L + 1)) :
    ∫ g, satWeight (n, T) (round0 v g) ∂stdGaussian E +
        t * (T.map fun c ↦ (c.2.2 : ℝ)).sum / (250 * d * √L) ≤
      ∫ g, satWeight (n, T) (roundL v T (r * r) t g) ∂stdGaussian E := by
  have h0 : ∀ g, satWeight (n, T) (round0 v g) = (T.map fun c ↦ (c.2.2 : ℝ) / 2 *
      (1 + bsign c.2.1 * sgn ⟪v c.1.1, g⟫ * sgn ⟪v c.1.2, g⟫)).sum :=
    fun g ↦ satWeight_decide n T (fun i ↦ ⟪v i, g⟫)
  have hl : ∀ g, satWeight (n, T) (roundL v T (r * r) t g) = (T.map fun c ↦ (c.2.2 : ℝ) / 2 *
      (1 + bsign c.2.1 * sgn (⟪v c.1.1, g⟫ + t * fvote v T (r * r) c.1.1 g) *
        sgn (⟪v c.1.2, g⟫ + t * fvote v T (r * r) c.1.2 g))).sum :=
    fun g ↦ satWeight_decide n T (fun i ↦ ⟪v i, g⟫ + t * fvote v T (r * r) i g)
  simp_rw [h0, hl]
  have hP : ∀ (c : Constraint) (x y : ℝ), |(c.2.2 : ℝ) / 2 * (1 + bsign c.2.1 * sgn x * sgn y)|
      ≤ |(c.2.2 : ℝ)| := by
    intro c x y
    rw [abs_mul, abs_div, abs_two]
    have : |1 + bsign c.2.1 * sgn x * sgn y| ≤ 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_sgn, abs_sgn]
      rcases bsign_cases c.2.1 with h | h <;> rw [h] <;> norm_num
    nlinarith [abs_nonneg (c.2.2 : ℝ)]
  have hfm : ∀ i, Measurable (fvote v T (r * r) i) := fun i ↦ measurable_vote _ _ _
  rw [integral_list_sum _ _ fun c _ ↦ integrable_of_abs_le (by fun_prop) fun g ↦ hP c _ _,
    integral_list_sum _ _ fun c _ ↦ integrable_of_abs_le (by
      have := hfm c.1.1
      have := hfm c.1.2
      fun_prop) fun g ↦ hP c _ _]
  -- Per constraint, then per vertex.
  have hc := List.sum_le_sum (l := T) fun c hc ↦ constraint_gain v hT hv hρ hr0 hr1 ht0 ht hc
  rw [list_sum_map_sub, ← sum_outEdges n T (fun c hc ↦ ⟨(hT c hc).1, (hT c hc).2.1⟩)
    (gainQ v T r t)] at hc
  have hv' := Finset.sum_le_sum fun i (_ : i ∈ Finset.range n) ↦
    vertex_gain v hT hv hρ hdeg hβ hr0 hr1 ht0 ht hL hβL hηL i
  have hW : ∑ i ∈ Finset.range n, wdeg T i = 2 * (T.map fun c ↦ (c.2.2 : ℝ)).sum := by
    have := sum_outEdges n T (fun c hc ↦ ⟨(hT c hc).1, (hT c hc).2.1⟩)
      (fun _ e ↦ (e.2.2 : ℝ))
    simp only [wdeg]
    rw [this]
    exact list_sum_map_two T fun c ↦ (c.2.2 : ℝ)
  have hfin : ∑ i ∈ Finset.range n, t * wdeg T i / (500 * d * √L) =
      t * (T.map fun c ↦ (c.2.2 : ℝ)).sum / (250 * d * √L) := by
    rw [← Finset.sum_div, ← Finset.mul_sum, hW]
    by_cases hd : (d : ℝ) = 0
    · simp [hd]
    by_cases hL0 : √(L : ℝ) = 0
    · simp [hL0]
    field_simp
    ring
  linarith

end Gain

end BGHKLMM26
