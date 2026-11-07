module

public import BGHKLMM26.Energy
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Gaussian estimates: strips

[BGHKLMM26, Section 3.3]. For a function `h` with `|h| ≤ 1` and `0 < r < 1`, let
`F = U_r h`, `F(g) = E h(r g + √(1 - r²) g')` (`BGHKLMM26.ou`). The smoothed vote is of this form:
`f_η = U_r f_r` for `r = √η`, and `E f_r² = E f_η ψ = a` (`BGHKLMM26.vote_eq_ou`,
`BGHKLMM26.integral_vote_sq_sqrt`).

The paper bounds `E_Y sup_{|x| ≤ s} F(x, Y)²` by the Mehler kernel [BGHKLMM26, Lemma 3.13]. We use a
measurable majorant instead of the supremum: for a unit vector `w`,
`F(g)² ≤ exp (r² ⟨w, g⟩² / (1 - r²)) m(g - ⟨w, g⟩ w)` with `m(y) = E h(r y + √(1 - r²) g')²`
(`BGHKLMM26.sq_ou_le`, Cauchy–Schwarz against the Cameron–Martin density), and
`E m(g - ⟨w, g⟩ w) ≤ E h² / √(1 - r²)` (`BGHKLMM26.integral_slice_perp_le`, compressing the `w`
direction). The strip lemmas follow:

* one strip [BGHKLMM26, Lemma 3.14]: `E |F| [|⟨w, g⟩| ≤ t |F|] ≤ 3 t E h² / √(1 - r²)`
  (`BGHKLMM26.one_strip`);
* two strips [BGHKLMM26, Lemma 3.15]: for `h₁, h₂` invariant along `v₁, v₂`,
  `P(|⟨v₁, g⟩| ≤ t |F₁|, |⟨v₂, g⟩| ≤ t |F₂|) ≤ 3 t² (E h₁² + E h₂²) / (σ √(1 - r²))`
  (`BGHKLMM26.two_strip`).
-/

@[expose] public section

namespace BGHKLMM26

open MeasureTheory ProbabilityTheory Real Gaussian Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Splitting along a unit vector -/

section Split

/-- The component of `g` orthogonal to `w`. -/
def perp (w g : E) : E := g - ⟪w, g⟫ • w

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_add_inner (w g : E) : perp w g + ⟪w, g⟫ • w = g := by
  simp [perp]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_add_smul {w : E} (hw : ‖w‖ = 1) (g : E) (z : ℝ) : perp w (g + z • w) = perp w g := by
  have hww : ⟪w, w⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hw, one_pow]
  simp only [perp, inner_add_right, inner_smul_right, hww, mul_one, add_smul]
  abel

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_perp {w : E} (hw : ‖w‖ = 1) (g : E) : ⟪w, perp w g⟫ = 0 := by
  simp [perp, inner_sub_right, inner_smul_right, hw]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem inner_perp_of_inner_eq_zero {w v : E} (h : ⟪v, w⟫ = 0) (g : E) :
    ⟪v, perp w g⟫ = ⟪v, g⟫ := by
  simp [perp, inner_sub_right, inner_smul_right, h]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[fun_prop]
theorem continuous_perp (w : E) : Continuous (perp w) := by
  unfold perp
  fun_prop

omit [FiniteDimensional ℝ E] in
@[fun_prop]
theorem measurable_perp (w : E) : Measurable (perp w) := (continuous_perp w).measurable

/-- **Splitting a standard Gaussian along a unit vector `w`**: `g = (g - ⟨w, g⟩ w) + ⟨w, g⟩ w`,
where the two parts are independent and `⟨w, g⟩` is a standard Gaussian. -/
theorem integral_split {w : E} (hw : ‖w‖ = 1) {φ : E → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hb : ∀ x, |φ x| ≤ C) :
    ∫ x, φ x ∂stdGaussian E =
      ∫ g, ∫ z, φ (perp w g + z • w) ∂gaussianReal 0 1 ∂stdGaussian E := by
  set K : Submodule ℝ E := ℝ ∙ w
  have hK : ∀ g, K.starProjection g = ⟪w, g⟫ • w := by
    intro g
    rw [Submodule.starProjection_singleton, hw]
    simp
  have hKp : ∀ g, Kᗮ.starProjection g = perp w g := by
    intro g
    rw [Submodule.starProjection_orthogonal_val, hK, perp]
  have hmap : ((stdGaussian E).prod (stdGaussian E)).map
      (fun p ↦ Kᗮ.starProjection p.1 + K.starProjection p.2) = stdGaussian E :=
    map_prod_stdGaussian _ _ Kᗮ.starProjection K.starProjection
      (fun x t ↦ Kᗮ.inner_starProjection_left_eq_right x t)
      (fun x t ↦ K.inner_starProjection_left_eq_right x t)
      (fun t ↦ by rw [add_comm]; exact (K.norm_sq_eq_add_norm_sq_starProjection t).symm)
  rw [integral_eq_of_map_prod (by fun_prop) hmap (integrable_of_abs_le hφ hb)]
  congr 1
  funext g
  simp only [hK, hKp]
  have h := integral_map (μ := stdGaussian E) (φ := fun g₂ ↦ ⟪w, g₂⟫)
    (f := fun z ↦ φ (perp w g + z • w)) (by fun_prop)
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [map_inner_stdGaussian hw] at h
  exact h.symm

end Split

/-! ### The Ornstein–Uhlenbeck operator and slice energies -/

section OU

/-- `U_r h (g) = E h(r g + √(1 - r²) g')`. -/
noncomputable def ou (r : ℝ) (h : E → ℝ) (g : E) : ℝ :=
  ∫ g', h (r • g + √(1 - r ^ 2) • g') ∂stdGaussian E

/-- The slice energy `m(y) = E h(r y + √(1 - r²) g')²`. -/
noncomputable def slice (r : ℝ) (h : E → ℝ) (y : E) : ℝ :=
  ∫ g', h (r • y + √(1 - r ^ 2) • g') ^ 2 ∂stdGaussian E

variable {r : ℝ} {h : E → ℝ}

@[fun_prop]
theorem measurable_ou (hh : Measurable h) : Measurable (ou r h) := by
  have : StronglyMeasurable (fun p : E × E ↦ h (r • p.1 + √(1 - r ^ 2) • p.2)) :=
    (by fun_prop : Measurable _).stronglyMeasurable
  exact (this.integral_prod_right' (ν := stdGaussian E)).measurable

@[fun_prop]
theorem measurable_slice (hh : Measurable h) : Measurable (slice r h) := by
  have : StronglyMeasurable (fun p : E × E ↦ h (r • p.1 + √(1 - r ^ 2) • p.2) ^ 2) :=
    (by fun_prop : Measurable _).stronglyMeasurable
  exact (this.integral_prod_right' (ν := stdGaussian E)).measurable

omit [BorelSpace E] in
theorem abs_ou_le (hb : ∀ y, |h y| ≤ 1) (g : E) : |ou r h g| ≤ 1 := by
  unfold ou
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ g', |h (r • g + √(1 - r ^ 2) • g')| ∂stdGaussian E ≤ ∫ g', (1 : ℝ) ∂stdGaussian E :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
          (ae_of_all _ fun _ ↦ hb _)
    _ = 1 := by simp

omit [BorelSpace E] in
theorem slice_nonneg (y : E) : 0 ≤ slice r h y :=
  integral_nonneg fun _ ↦ sq_nonneg _

omit [BorelSpace E] in
theorem slice_le_one (hb : ∀ y, |h y| ≤ 1) (y : E) : slice r h y ≤ 1 := by
  unfold slice
  calc ∫ g', h (r • y + √(1 - r ^ 2) • g') ^ 2 ∂stdGaussian E ≤ ∫ g', (1 : ℝ) ∂stdGaussian E :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _)
          (ae_of_all _ fun g' ↦ by
            have := hb (r • y + √(1 - r ^ 2) • g')
            nlinarith [abs_nonneg (h (r • y + √(1 - r ^ 2) • g')),
              sq_abs (h (r • y + √(1 - r ^ 2) • g'))])
    _ = 1 := by simp

/-- **The Ornstein–Uhlenbeck operator, along a direction** [BGHKLMM26, Lemma 3.13, Equation (1)]:
for a unit vector `w`, `(U_r h)(g)² ≤ exp (r² ⟨w, g⟩² / (1 - r²)) m(g - ⟨w, g⟩ w)`. -/
theorem sq_ou_le (hr0 : 0 < r) (hr1 : r < 1) (hh : Measurable h) (hb : ∀ y, |h y| ≤ 1)
    {w : E} (hw : ‖w‖ = 1) (g : E) :
    ou r h g ^ 2 ≤ rexp (r ^ 2 * ⟪w, g⟫ ^ 2 / (1 - r ^ 2)) * slice r h (perp w g) := by
  set τ := √(1 - r ^ 2) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 (by nlinarith)
  have hτ2 : τ ^ 2 = 1 - r ^ 2 := Real.sq_sqrt (by nlinarith)
  set x := ⟪w, g⟫ with hxdef
  set y := perp w g with hydef
  set c := r * x / τ with hcdef
  have hτc : τ * c = r * x := by rw [hcdef]; field_simp
  have hg : ∀ g', r • g + τ • g' = r • y + τ • (g' + c • w) := by
    intro g'
    have : g = y + x • w := (perp_add_inner w g).symm
    conv_lhs => rw [this]
    rw [smul_add, smul_add, smul_smul, smul_smul, hτc]
    abel
  -- `ou r h g = E φ(g' + c w)` for `φ(g') = h(r y + τ g')`.
  set φ : E → ℝ := fun g' ↦ h (r • y + τ • g') with hφdef
  have hφm : Measurable φ := by fun_prop
  have hou : ou r h g = ∫ g', φ (g' + c • w) ∂stdGaussian E := by
    unfold ou
    congr 1
    funext g'
    rw [hg g']
  -- Split along `w`.
  have hsplit := integral_split hw (φ := fun g' ↦ φ (g' + c • w)) (by fun_prop)
    (C := 1) (fun x ↦ hb _)
  set I : E → ℝ := fun g₂ ↦ ∫ z, φ (perp w g₂ + z • w + c • w) ∂gaussianReal 0 1 with hIdef
  have hIm : Measurable I := by
    have : StronglyMeasurable (fun p : E × ℝ ↦ φ (perp w p.1 + p.2 • w + c • w)) :=
      (by fun_prop : Measurable _).stronglyMeasurable
    exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hIb : ∀ g₂, |I g₂| ≤ 1 := by
    intro g₂
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ z, |φ (perp w g₂ + z • w + c • w)| ∂gaussianReal 0 1
        ≤ ∫ z, (1 : ℝ) ∂gaussianReal 0 1 :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
            (ae_of_all _ fun _ ↦ hb _)
      _ = 1 := by simp
  rw [hou, hsplit]
  -- Jensen, then Cauchy–Schwarz against the Cameron–Martin density in each slice.
  have hJ : (∫ g₂, I g₂ ∂stdGaussian E) ^ 2 ≤ ∫ g₂, I g₂ ^ 2 ∂stdGaussian E := by
    have := sq_integral_mul_le (μ := stdGaussian E) (memLp_two_of_abs_le hIm hIb)
      (memLp_two_of_abs_le (f := fun _ ↦ (1 : ℝ)) measurable_const (C := 1) (fun _ ↦ by simp))
    simpa using this
  have hslice : ∀ g₂, I g₂ ^ 2 ≤
      rexp (c ^ 2) * ∫ z, φ (perp w g₂ + z • w) ^ 2 ∂gaussianReal 0 1 := by
    intro g₂
    have := sq_integral_add_const_le (φ := fun z ↦ φ (perp w g₂ + z • w)) (by fun_prop)
      (C := 1) (fun _ ↦ hb _) c
    simpa [hIdef, add_smul, add_assoc] using this
  have hback := integral_split hw (φ := fun g' ↦ φ g' ^ 2) (by fun_prop) (C := 1)
    (fun x ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hb (r • y + τ • x)
      nlinarith [abs_nonneg (h (r • y + τ • x)), sq_abs (h (r • y + τ • x))])
  have hint : Integrable (fun g₂ ↦ ∫ z, φ (perp w g₂ + z • w) ^ 2 ∂gaussianReal 0 1)
      (stdGaussian E) := by
    refine integrable_of_abs_le (C := 1) ?_ fun g₂ ↦ ?_
    · have : StronglyMeasurable (fun p : E × ℝ ↦ φ (perp w p.1 + p.2 • w) ^ 2) :=
        (by fun_prop : Measurable _).stronglyMeasurable
      exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    · rw [abs_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
      calc ∫ z, φ (perp w g₂ + z • w) ^ 2 ∂gaussianReal 0 1 ≤ ∫ z, (1 : ℝ) ∂gaussianReal 0 1 :=
            integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _)
              (ae_of_all _ fun z ↦ by
                have := hb (r • y + τ • (perp w g₂ + z • w))
                nlinarith [abs_nonneg (h (r • y + τ • (perp w g₂ + z • w))),
                  sq_abs (h (r • y + τ • (perp w g₂ + z • w)))])
        _ = 1 := by simp
  calc (∫ g₂, I g₂ ∂stdGaussian E) ^ 2 ≤ ∫ g₂, I g₂ ^ 2 ∂stdGaussian E := hJ
    _ ≤ ∫ g₂, rexp (c ^ 2) * ∫ z, φ (perp w g₂ + z • w) ^ 2 ∂gaussianReal 0 1 ∂stdGaussian E :=
        integral_mono (memLp_two_of_abs_le hIm hIb).integrable_sq (hint.const_mul _) hslice
    _ = rexp (c ^ 2) * ∫ g', φ g' ^ 2 ∂stdGaussian E := by rw [integral_const_mul, hback]
    _ = rexp (r ^ 2 * x ^ 2 / (1 - r ^ 2)) * slice r h y := by
        congr 1
        rw [hcdef, div_pow, mul_pow, hτ2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_smul_add (w : E) (a b : ℝ) (y y' : E) :
    a • perp w y + b • perp w y' = perp w (a • y + b • y') := by
  simp only [perp, inner_add_right, inner_smul_right, smul_sub, add_smul, smul_smul]
  abel

/-- **Compressing one direction** [BGHKLMM26, Lemma 3.13]: for a unit vector `w`,
`E m(g - ⟨w, g⟩ w) ≤ E h² / √(1 - r²)`. -/
theorem integral_slice_perp_le (hr0 : 0 < r) (hr1 : r < 1) (hh : Measurable h)
    (hb : ∀ y, |h y| ≤ 1) {w : E} (hw : ‖w‖ = 1) :
    ∫ g, slice r h (perp w g) ∂stdGaussian E ≤
      (√(1 - r ^ 2))⁻¹ * ∫ g, h g ^ 2 ∂stdGaussian E := by
  set τ := √(1 - r ^ 2) with hτdef
  have hτ : 0 < τ := Real.sqrt_pos.2 (by nlinarith)
  have hτ1 : τ ≤ 1 := by
    rw [hτdef, Real.sqrt_le_one]
    nlinarith
  have hh2 : ∀ y, |h y ^ 2| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (sq_nonneg _)]
    have := hb y
    nlinarith [abs_nonneg (h y), sq_abs (h y)]
  -- `Ψ(y) = E_z h(perp w y + τ z w)²`.
  set Ψ : E → ℝ := fun y ↦ ∫ z, h (perp w y + (τ * z) • w) ^ 2 ∂gaussianReal 0 1 with hΨdef
  have hΨm : Measurable Ψ := by
    have : StronglyMeasurable (fun p : E × ℝ ↦ h (perp w p.1 + (τ * p.2) • w) ^ 2) :=
      (by fun_prop : Measurable _).stronglyMeasurable
    exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hΨb : ∀ y, |Ψ y| ≤ 1 := by
    intro y
    rw [abs_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
    calc Ψ y ≤ ∫ z, (1 : ℝ) ∂gaussianReal 0 1 :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _)
            (ae_of_all _ fun z ↦ (le_abs_self _).trans (hh2 _))
      _ = 1 := by simp
  -- Each slice energy is `Ψ` at the rotated point `r g + τ g₂`, averaged over `g₂`.
  have hslice : ∀ g, slice r h (perp w g) =
      ∫ g₂, Ψ (r • g + τ • g₂) ∂stdGaussian E := by
    intro g
    unfold slice
    rw [integral_split hw (φ := fun g' ↦ h (r • perp w g + τ • g') ^ 2) (by fun_prop) (C := 1)
      (fun _ ↦ hh2 _)]
    congr 1
    funext g₂
    simp only [hΨdef]
    congr 1
    funext z
    congr 2
    rw [smul_add, ← add_assoc, perp_smul_add, smul_smul]
  simp_rw [hslice]
  have hrot := map_add_smul_stdGaussian (E := E) (r := r) (s := τ) (by
    rw [hτdef, Real.sq_sqrt (by nlinarith)]
    ring)
  rw [← integral_eq_of_map_prod (by fun_prop) hrot (integrable_of_abs_le hΨm hΨb)]
  -- Compress the `w` direction in each slice.
  rw [integral_split hw (φ := fun g ↦ h g ^ 2) (by fun_prop) (C := 1) hh2, ← integral_const_mul]
  refine integral_mono (integrable_of_abs_le hΨm hΨb) ?_ fun y ↦ ?_
  · refine Integrable.const_mul ?_ _
    refine integrable_of_abs_le (C := 1) ?_ fun y ↦ ?_
    · have : StronglyMeasurable (fun p : E × ℝ ↦ h (perp w p.1 + p.2 • w) ^ 2) :=
        (by fun_prop : Measurable _).stronglyMeasurable
      exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    · rw [abs_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)]
      calc ∫ z, h (perp w y + z • w) ^ 2 ∂gaussianReal 0 1 ≤ ∫ z, (1 : ℝ) ∂gaussianReal 0 1 :=
            integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _)
              (ae_of_all _ fun z ↦ (le_abs_self _).trans (hh2 _))
        _ = 1 := by simp
  · exact integral_const_mul_le (φ := fun z ↦ h (perp w y + z • w) ^ 2) (by fun_prop)
      (fun _ ↦ sq_nonneg _) (C := 1) (fun _ ↦ (le_abs_self _).trans (hh2 _)) hτ hτ1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem perp_perp {w : E} (hw : ‖w‖ = 1) (g : E) : perp w (perp w g) = perp w g := by
  conv_lhs => rw [perp, inner_perp hw, zero_smul, sub_zero]

/-- The majorant `M(y) = min 1 √(3 m(y))` of `|U_r h|` on a strip. -/
noncomputable def major (r : ℝ) (h : E → ℝ) (y : E) : ℝ := min 1 √(3 * slice r h y)

omit [BorelSpace E] in
theorem major_nonneg {y : E} : 0 ≤ major r h y := le_min zero_le_one (Real.sqrt_nonneg _)

omit [BorelSpace E] in
theorem major_le_one {y : E} : major r h y ≤ 1 := min_le_left _ _

omit [BorelSpace E] in
theorem sq_major_le (y : E) : major r h y ^ 2 ≤ 3 * slice r h y := by
  calc major r h y ^ 2 ≤ (√(3 * slice r h y)) ^ 2 :=
        pow_le_pow_left₀ major_nonneg (min_le_right _ _) 2
    _ = 3 * slice r h y := Real.sq_sqrt (by have := slice_nonneg (r := r) (h := h) y; linarith)

@[fun_prop]
theorem measurable_major (hh : Measurable h) : Measurable (major r h) := by
  unfold major
  exact measurable_const.min (((measurable_slice hh).const_mul 3).sqrt)

/-- On a strip of width `s` with `r² s² ≤ 1 - r²`, `|U_r h| ≤ M(g - ⟨w, g⟩ w)`. -/
theorem abs_ou_le_major (hr0 : 0 < r) (hr1 : r < 1) (hh : Measurable h) (hb : ∀ y, |h y| ≤ 1)
    {w : E} (hw : ‖w‖ = 1) {s : ℝ} (hs : r ^ 2 * s ^ 2 ≤ 1 - r ^ 2) {g : E}
    (hg : |⟪w, g⟫| ≤ s) : |ou r h g| ≤ major r h (perp w g) := by
  have hF1 := abs_ou_le (r := r) hb g
  have hsq := sq_ou_le hr0 hr1 hh hb hw g
  have hexp : rexp (r ^ 2 * ⟪w, g⟫ ^ 2 / (1 - r ^ 2)) ≤ 3 := by
    have : r ^ 2 * ⟪w, g⟫ ^ 2 / (1 - r ^ 2) ≤ 1 := by
      rw [div_le_one (by nlinarith)]
      have : ⟪w, g⟫ ^ 2 ≤ s ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hg 2
      nlinarith
    calc _ ≤ rexp 1 := Real.exp_le_exp.2 this
      _ ≤ 3 := Real.exp_one_lt_three.le
  refine le_min hF1 ?_
  rw [← Real.sqrt_sq (abs_nonneg (ou r h g))]
  refine Real.sqrt_le_sqrt ?_
  rw [sq_abs]
  calc ou r h g ^ 2 ≤ rexp (r ^ 2 * ⟪w, g⟫ ^ 2 / (1 - r ^ 2)) * slice r h (perp w g) := hsq
    _ ≤ 3 * slice r h (perp w g) := mul_le_mul_of_nonneg_right hexp (slice_nonneg _)

/-- `E M(g - ⟨w, g⟩ w)² ≤ 3 E h² / √(1 - r²)`. -/
theorem integral_sq_major_le (hr0 : 0 < r) (hr1 : r < 1) (hh : Measurable h)
    (hb : ∀ y, |h y| ≤ 1) {w : E} (hw : ‖w‖ = 1) :
    ∫ g, major r h (perp w g) ^ 2 ∂stdGaussian E ≤
      3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h g ^ 2 ∂stdGaussian E) := by
  have hm : Measurable fun g ↦ slice r h (perp w g) := (measurable_slice hh).comp (by fun_prop)
  calc ∫ g, major r h (perp w g) ^ 2 ∂stdGaussian E
      ≤ ∫ g, 3 * slice r h (perp w g) ∂stdGaussian E := by
        refine integral_mono (integrable_of_abs_le (C := 1) (by
            exact ((measurable_major hh).comp (by fun_prop)).pow_const 2) fun g ↦ ?_)
          ((integrable_of_abs_le hm (C := 1) fun g ↦ by
            rw [abs_of_nonneg (slice_nonneg _)]
            exact slice_le_one hb _).const_mul 3) fun g ↦ sq_major_le _
        rw [abs_of_nonneg (sq_nonneg _)]
        exact pow_le_one₀ major_nonneg major_le_one
    _ = 3 * ∫ g, slice r h (perp w g) ∂stdGaussian E := integral_const_mul _ _
    _ ≤ _ := by
        gcongr
        exact integral_slice_perp_le hr0 hr1 hh hb hw

end OU

/-! ### Strips -/

section Strips

variable {r : ℝ} {h : E → ℝ}

/-- **One strip** [BGHKLMM26, Lemma 3.14]: for a unit vector `w` and `t ≥ 0` with
`r² t² ≤ 1 - r²`, `E |F| [|⟨w, g⟩| ≤ t |F|] ≤ 3 t E h² / √(1 - r²)` for `F = U_r h`. -/
theorem one_strip (hr0 : 0 < r) (hr1 : r < 1) (hh : Measurable h) (hb : ∀ y, |h y| ≤ 1)
    {w : E} (hw : ‖w‖ = 1) {t : ℝ} (ht0 : 0 ≤ t) (ht : r ^ 2 * t ^ 2 ≤ 1 - r ^ 2) :
    ∫ g, |ou r h g| * {g | |⟪w, g⟫| ≤ t * |ou r h g|}.indicator 1 g ∂stdGaussian E ≤
      3 * t * ((√(1 - r ^ 2))⁻¹ * ∫ g, h g ^ 2 ∂stdGaussian E) := by
  set M : E → ℝ := fun g ↦ major r h (perp w g) with hMdef
  have hMm : Measurable M := (measurable_major hh).comp (by fun_prop)
  set B := {g : E | |⟪w, g⟫| ≤ t * M g} with hBdef
  have hBm : MeasurableSet B :=
    measurableSet_le (f := fun g ↦ |⟪w, g⟫|) (by fun_prop) (by fun_prop)
  -- Pointwise domination by the majorant.
  have hpt : ∀ g, |ou r h g| * {g | |⟪w, g⟫| ≤ t * |ou r h g|}.indicator 1 g ≤
      M g * B.indicator 1 g := by
    intro g
    by_cases hE : |⟪w, g⟫| ≤ t * |ou r h g|
    · have hX : |⟪w, g⟫| ≤ t := hE.trans (mul_le_of_le_one_right ht0 (abs_ou_le hb g))
      have hFM := abs_ou_le_major hr0 hr1 hh hb hw ht hX
      rw [indicator_of_mem (show g ∈ {g | |⟪w, g⟫| ≤ t * |ou r h g|} from hE),
        indicator_of_mem (show g ∈ B from hE.trans (mul_le_mul_of_nonneg_left hFM ht0))]
      simpa using hFM
    · rw [indicator_of_notMem (show g ∉ {g | |⟪w, g⟫| ≤ t * |ou r h g|} from hE), mul_zero]
      exact mul_nonneg major_nonneg (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have hFm : Measurable fun g ↦ |ou r h g| *
      {g | |⟪w, g⟫| ≤ t * |ou r h g|}.indicator (1 : E → ℝ) g := by
    refine (by fun_prop : Measurable fun g ↦ |ou r h g|).mul (measurable_one.indicator ?_)
    exact measurableSet_le (f := fun g ↦ |⟪w, g⟫|) (by fun_prop) (by fun_prop)
  have hGm : Measurable fun g ↦ M g * B.indicator (1 : E → ℝ) g :=
    hMm.mul (measurable_one.indicator hBm)
  have hGb : ∀ g, |M g * B.indicator (1 : E → ℝ) g| ≤ 1 := by
    intro g
    rw [abs_mul, abs_of_nonneg major_nonneg]
    calc M g * |B.indicator 1 g| ≤ 1 * 1 := by
          refine mul_le_mul major_le_one ?_ (abs_nonneg _) zero_le_one
          simp only [indicator]
          split_ifs <;> simp
      _ = 1 := one_mul 1
  calc ∫ g, |ou r h g| * {g | |⟪w, g⟫| ≤ t * |ou r h g|}.indicator 1 g ∂stdGaussian E
      ≤ ∫ g, M g * B.indicator 1 g ∂stdGaussian E := by
        refine integral_mono (integrable_of_abs_le hFm (C := 1) fun g ↦ ?_)
          (integrable_of_abs_le hGm hGb) hpt
        rw [abs_mul, abs_abs]
        calc |ou r h g| * |{g | |⟪w, g⟫| ≤ t * |ou r h g|}.indicator 1 g| ≤ 1 * 1 := by
              refine mul_le_mul (abs_ou_le hb g) ?_ (abs_nonneg _) zero_le_one
              simp only [indicator]
              split_ifs <;> simp
          _ = 1 := one_mul 1
    _ = ∫ g, ∫ z, M g * {z : ℝ | |z| ≤ t * M g}.indicator 1 z ∂gaussianReal 0 1
          ∂stdGaussian E := by
        rw [integral_split hw hGm hGb]
        congr 1
        funext g
        congr 1
        funext z
        have hperp : perp w (perp w g + z • w) = perp w g := by
          rw [perp_add_smul hw, perp_perp hw]
        have hin : ⟪w, perp w g + z • w⟫ = z := by
          rw [inner_add_right, inner_perp hw, inner_smul_right, real_inner_self_eq_norm_sq, hw]
          ring
        simp only [hMdef, hBdef, indicator, mem_ofPred_eq, hperp, hin, Pi.one_apply]
    _ ≤ ∫ g, t * M g ^ 2 ∂stdGaussian E := by
        refine integral_mono ?_ ?_ fun g ↦ ?_
        · refine integrable_of_abs_le (C := 1) ?_ fun g ↦ ?_
          · have : StronglyMeasurable (fun p : E × ℝ ↦ M p.1 *
                {z : ℝ | |z| ≤ t * M p.1}.indicator (1 : ℝ → ℝ) p.2) := by
              refine Measurable.stronglyMeasurable ?_
              have hs : MeasurableSet {p : E × ℝ | |p.2| ≤ t * M p.1} :=
                measurableSet_le (f := fun p : E × ℝ ↦ |p.2|) (by fun_prop)
                  (measurable_const.mul (hMm.comp measurable_fst))
              have he : (fun p : E × ℝ ↦ {z : ℝ | |z| ≤ t * M p.1}.indicator (1 : ℝ → ℝ) p.2) =
                  {p : E × ℝ | |p.2| ≤ t * M p.1}.indicator 1 := by
                funext p
                simp [indicator]
              have hm2 : Measurable fun p : E × ℝ ↦
                  {z : ℝ | |z| ≤ t * M p.1}.indicator (1 : ℝ → ℝ) p.2 := by
                rw [he]
                exact measurable_one.indicator hs
              exact (hMm.comp measurable_fst).mul hm2
            exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
          · rw [integral_const_mul, integral_indicator_one (measurableSet_le (by fun_prop)
              measurable_const), abs_mul, abs_of_nonneg major_nonneg,
              abs_of_nonneg measureReal_nonneg]
            have h1 : (gaussianReal 0 1).real {z : ℝ | |z| ≤ t * M g} ≤ 1 := by
              rw [← probReal_univ (μ := gaussianReal 0 1)]
              exact measureReal_mono (subset_univ _)
            calc M g * (gaussianReal 0 1).real {z : ℝ | |z| ≤ t * M g} ≤ 1 * 1 :=
                  mul_le_mul major_le_one h1 measureReal_nonneg zero_le_one
              _ = 1 := one_mul 1
        · exact (integrable_of_abs_le (C := 1) (hMm.pow_const 2) fun g ↦ by
            rw [abs_of_nonneg (sq_nonneg _)]
            exact pow_le_one₀ major_nonneg major_le_one).const_mul t
        · rw [integral_const_mul, integral_indicator_one (measurableSet_le (by fun_prop)
            measurable_const)]
          have hac := gaussianReal_abs_sub_le 0 (mul_nonneg ht0 (major_nonneg (r := r) (h := h)
            (y := perp w g)))
          simp only [sub_zero] at hac
          calc M g * (gaussianReal 0 1).real {z : ℝ | |z| ≤ t * M g} ≤ M g * (t * M g) :=
                mul_le_mul_of_nonneg_left hac major_nonneg
            _ = t * M g ^ 2 := by ring
    _ = t * ∫ g, M g ^ 2 ∂stdGaussian E := integral_const_mul _ _
    _ ≤ t * (3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h g ^ 2 ∂stdGaussian E)) :=
        mul_le_mul_of_nonneg_left (integral_sq_major_le hr0 hr1 hh hb hw) ht0
    _ = _ := by ring

omit [BorelSpace E] in
/-- A function invariant along `v` has slice energies invariant along `v`. -/
theorem slice_add_smul {v : E} (hinv : ∀ y (c : ℝ), h (y + c • v) = h y) (y : E) (c : ℝ) :
    slice r h (y + c • v) = slice r h y := by
  unfold slice
  congr 1
  funext g'
  rw [show r • (y + c • v) + √(1 - r ^ 2) • g' = (r • y + √(1 - r ^ 2) • g') + (r * c) • v by
    rw [smul_add, smul_smul]; abel, hinv]

omit [BorelSpace E] in
theorem major_add_smul {v : E} (hinv : ∀ y (c : ℝ), h (y + c • v) = h y) (y : E) (c : ℝ) :
    major r h (y + c • v) = major r h y := by
  simp only [major, slice_add_smul hinv]

/-- **Two transverse strips** [BGHKLMM26, Lemma 3.15]. Let `v₁, u` be orthonormal, `ρ² < 1`,
`σ = √(1 - ρ²)` and `v₂ = ρ v₁ + σ u`. If `h₁` is invariant along `v₁` and `h₂` along `v₂`, then
for `t ≥ 0` with `r² (2t/σ)² ≤ 1 - r²`,
`P(|⟨v₁, g⟩| ≤ t |U_r h₁|, |⟨v₂, g⟩| ≤ t |U_r h₂|) ≤ 3 t² (E h₁² + E h₂²) / (σ √(1 - r²))`. -/
theorem two_strip (hr0 : 0 < r) (hr1 : r < 1) {h₁ h₂ : E → ℝ} (hh₁ : Measurable h₁)
    (hh₂ : Measurable h₂) (hb₁ : ∀ y, |h₁ y| ≤ 1) (hb₂ : ∀ y, |h₂ y| ≤ 1) {v₁ u : E}
    (hv₁ : ‖v₁‖ = 1) (hu : ‖u‖ = 1) (hv₁u : ⟪v₁, u⟫ = 0) {ρ : ℝ} (hρ : ρ ^ 2 < 1)
    (hinv₁ : ∀ y (c : ℝ), h₁ (y + c • v₁) = h₁ y)
    (hinv₂ : ∀ y (c : ℝ), h₂ (y + c • (ρ • v₁ + √(1 - ρ ^ 2) • u)) = h₂ y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : r ^ 2 * (2 * t / √(1 - ρ ^ 2)) ^ 2 ≤ 1 - r ^ 2) :
    (stdGaussian E).real {g | |⟪v₁, g⟫| ≤ t * |ou r h₁ g| ∧
        |⟪ρ • v₁ + √(1 - ρ ^ 2) • u, g⟫| ≤ t * |ou r h₂ g|} ≤
      3 * t ^ 2 / √(1 - ρ ^ 2) *
        ((√(1 - r ^ 2))⁻¹ * (∫ g, h₁ g ^ 2 ∂stdGaussian E + ∫ g, h₂ g ^ 2 ∂stdGaussian E)) := by
  set σ := √(1 - ρ ^ 2) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by linarith)
  have hσ2 : σ ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have hρ1 : |ρ| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]
    linarith
  set v₂ := ρ • v₁ + σ • u with hv₂def
  set u' := σ • v₁ - ρ • u with hu'def
  have h11 : ⟪v₁, v₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hv₁, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have huv : ⟪u, v₁⟫ = 0 := by rw [real_inner_comm]; exact hv₁u
  have hu' : ‖u'‖ = 1 := by
    have : ‖u'‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hu'def]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h11, huu,
        hv₁u, huv, conj_trivial]
      nlinarith
    nlinarith [norm_nonneg u']
  have hv₂g : ∀ g, ⟪v₂, g⟫ = ρ * ⟪v₁, g⟫ + σ * ⟪u, g⟫ := by
    intro g
    simp [hv₂def, inner_add_left, inner_smul_left]
  have hu'g : ∀ g, ⟪u', g⟫ = σ * ⟪v₁, g⟫ - ρ * ⟪u, g⟫ := by
    intro g
    simp [hu'def, inner_sub_left, inner_smul_left]
  -- The part `Z g` of `g` orthogonal to `v₁, u` (equivalently to `v₁, v₂`).
  set Z : E → E := fun g ↦ g - ⟪v₁, g⟫ • v₁ - ⟪u, g⟫ • u with hZdef
  have hZm : Continuous Z := by rw [hZdef]; fun_prop
  have hZv : ∀ y (c : ℝ), Z (y + c • v₁) = Z y := by
    intro y c
    simp only [hZdef, inner_add_right, inner_smul_right, h11, huv, mul_zero, add_zero, mul_one,
      add_smul]
    abel
  have hZu : ∀ y (c : ℝ), Z (y + c • u) = Z y := by
    intro y c
    simp only [hZdef, inner_add_right, inner_smul_right, huu, hv₁u, mul_zero, add_zero, mul_one,
      add_smul]
    abel
  have hZZ : ∀ y, Z (Z y) = Z y := by
    intro y
    conv_lhs => rw [show Z y = (y + (-⟪v₁, y⟫) • v₁) + (-⟪u, y⟫) • u by
      simp only [hZdef, neg_smul]; abel]
    rw [hZu, hZv]
  have hperpu : ∀ g, perp u g = Z g + ⟪v₁, g⟫ • v₁ := by
    intro g
    simp only [perp, hZdef]
    abel
  have hperpu' : ∀ g, perp u' g = Z g + ⟪v₂, g⟫ • v₂ := by
    intro g
    rw [perp, hu'g, hv₂g]
    simp only [hZdef, hu'def, hv₂def]
    linear_combination (norm := module) hσ2 • (-(⟪v₁, g⟫ • v₁ + ⟪u, g⟫ • u))
  -- On the event, `|F₁| ≤ M₁(Z g)` and `|F₂| ≤ M₂(Z g)`.
  set M₁ : E → ℝ := fun g ↦ major r h₁ (Z g) with hM₁def
  set M₂ : E → ℝ := fun g ↦ major r h₂ (Z g) with hM₂def
  have hM₁m : Measurable M₁ := (measurable_major hh₁).comp hZm.measurable
  have hM₂m : Measurable M₂ := (measurable_major hh₂).comp hZm.measurable
  have hinv₂' : ∀ y (c : ℝ), h₂ (y + c • v₂) = h₂ y := hinv₂
  set B := {g : E | |⟪v₁, g⟫| ≤ t * M₁ g ∧ |⟪v₂, g⟫| ≤ t * M₂ g} with hBdef
  have hBm : MeasurableSet B :=
    (measurableSet_le (f := fun g ↦ |⟪v₁, g⟫|) (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (f := fun g ↦ |⟪v₂, g⟫|) (by fun_prop) (by fun_prop))
  have hsub : {g | |⟪v₁, g⟫| ≤ t * |ou r h₁ g| ∧ |⟪v₂, g⟫| ≤ t * |ou r h₂ g|} ⊆ B := by
    rintro g ⟨hX, hY⟩
    have hX' : |⟪v₁, g⟫| ≤ t := hX.trans (mul_le_of_le_one_right ht0 (abs_ou_le hb₁ g))
    have hY' : |⟪v₂, g⟫| ≤ t := hY.trans (mul_le_of_le_one_right ht0 (abs_ou_le hb₂ g))
    have hH : |⟪u, g⟫| ≤ 2 * t / σ := by
      rw [le_div_iff₀ hσ]
      have : σ * ⟪u, g⟫ = ⟪v₂, g⟫ - ρ * ⟪v₁, g⟫ := by rw [hv₂g]; ring
      calc |⟪u, g⟫| * σ = |⟪v₂, g⟫ - ρ * ⟪v₁, g⟫| := by
            rw [← this, abs_mul, abs_of_pos hσ, mul_comm]
        _ ≤ |⟪v₂, g⟫| + |ρ| * |⟪v₁, g⟫| := by
            rw [← abs_mul]
            exact abs_sub _ _
        _ ≤ t + 1 * t := by gcongr
        _ = 2 * t := by ring
    have hQ : |⟪u', g⟫| ≤ 2 * t / σ := by
      rw [le_div_iff₀ hσ]
      have : σ * ⟪u', g⟫ = ⟪v₁, g⟫ - ρ * ⟪v₂, g⟫ := by
        rw [hu'g, hv₂g]
        linear_combination ⟪v₁, g⟫ * hσ2
      calc |⟪u', g⟫| * σ = |⟪v₁, g⟫ - ρ * ⟪v₂, g⟫| := by
            rw [← this, abs_mul, abs_of_pos hσ, mul_comm]
        _ ≤ |⟪v₁, g⟫| + |ρ| * |⟪v₂, g⟫| := by
            rw [← abs_mul]
            exact abs_sub _ _
        _ ≤ t + 1 * t := by gcongr
        _ = 2 * t := by ring
    have hF₁ := abs_ou_le_major hr0 hr1 hh₁ hb₁ hu ht hH
    have hF₂ := abs_ou_le_major hr0 hr1 hh₂ hb₂ hu' ht hQ
    rw [hperpu, major_add_smul hinv₁] at hF₁
    rw [hperpu', major_add_smul hinv₂'] at hF₂
    exact ⟨hX.trans (mul_le_mul_of_nonneg_left hF₁ ht0),
      hY.trans (mul_le_mul_of_nonneg_left hF₂ ht0)⟩
  -- Integrate `B`: split along `u`, then along `v₁`.
  set S : E → Set (ℝ × ℝ) := fun g ↦
    {p | |p.1| ≤ t * M₁ g ∧ |ρ * p.1 + σ * p.2| ≤ t * M₂ g} with hSdef
  have hpoint : ∀ g₃ x h', B.indicator (1 : E → ℝ) (perp u (perp v₁ g₃ + x • v₁) + h' • u) =
      (S g₃).indicator 1 (x, h') := by
    intro g₃ x h'
    set q := perp u (perp v₁ g₃ + x • v₁) + h' • u with hqdef
    have hq1 : ⟪v₁, q⟫ = x := by
      rw [hqdef, inner_add_right, inner_perp_of_inner_eq_zero hv₁u, inner_add_right,
        inner_perp hv₁, inner_smul_right, inner_smul_right, h11, hv₁u]
      ring
    have hq2 : ⟪u, q⟫ = h' := by
      rw [hqdef, inner_add_right, inner_perp hu, inner_smul_right, huu]
      ring
    have hqZ : Z q = Z g₃ := by
      rw [hqdef, hZu, hperpu, hZv, hZZ, hZv]
      unfold perp
      rw [sub_eq_add_neg, ← neg_smul, hZv]
    simp only [hBdef, hSdef, indicator, mem_ofPred_eq, hM₁def, hM₂def, hv₂g, hq1, hq2, hqZ,
      Pi.one_apply]
  have hBb : ∀ g, |B.indicator (1 : E → ℝ) g| ≤ 1 := by
    intro g
    simp only [indicator]
    split_ifs <;> simp
  have hΦm : Measurable fun g₂ ↦ ∫ h', B.indicator (1 : E → ℝ) (perp u g₂ + h' • u)
      ∂gaussianReal 0 1 := by
    have : StronglyMeasurable (fun p : E × ℝ ↦ B.indicator (1 : E → ℝ) (perp u p.1 + p.2 • u)) :=
      ((measurable_one.indicator hBm).comp (by fun_prop)).stronglyMeasurable
    exact (this.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hΦb : ∀ g₂, |∫ h', B.indicator (1 : E → ℝ) (perp u g₂ + h' • u) ∂gaussianReal 0 1| ≤ 1 := by
    intro g₂
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ h', |B.indicator (1 : E → ℝ) (perp u g₂ + h' • u)| ∂gaussianReal 0 1
        ≤ ∫ h', (1 : ℝ) ∂gaussianReal 0 1 :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
            (ae_of_all _ fun _ ↦ hBb _)
      _ = 1 := by simp
  have hSm : ∀ g, MeasurableSet (S g) := by
    intro g
    exact (measurableSet_le (f := fun p : ℝ × ℝ ↦ |p.1|) (by fun_prop) measurable_const).inter
      (measurableSet_le (f := fun p : ℝ × ℝ ↦ |ρ * p.1 + σ * p.2|) (by fun_prop)
        measurable_const)
  have hBint : (stdGaussian E).real B = ∫ g₃, ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      (S g₃) ∂stdGaussian E := by
    rw [← integral_indicator_one hBm, integral_split hu (measurable_one.indicator hBm) hBb,
      integral_split hv₁ hΦm hΦb]
    congr 1
    funext g₃
    simp_rw [hpoint]
    have hI : Integrable ((S g₃).indicator (1 : ℝ × ℝ → ℝ))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := (integrable_const 1).indicator (hSm g₃)
    rw [← integral_prod _ hI, integral_indicator_one (hSm g₃)]
  -- The box bound in each slice, then the majorants' energies.
  have hbox : ∀ g, ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (S g) ≤
      t ^ 2 / σ * ((M₁ g ^ 2 + M₂ g ^ 2) / 2) := by
    intro g
    have := prod_box_le ρ hσ (mul_nonneg ht0 (major_nonneg (r := r) (h := h₁) (y := Z g)))
      (mul_nonneg ht0 (major_nonneg (r := r) (h := h₂) (y := Z g)))
    refine this.trans ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hσ]
    nlinarith [sq_nonneg (M₁ g - M₂ g), sq_nonneg t]
  have hE₁ : ∫ g, M₁ g ^ 2 ∂stdGaussian E ≤
      3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h₁ g ^ 2 ∂stdGaussian E) := by
    have h := integral_sq_major_le hr0 hr1 hh₁ hb₁ hu
    have : ∫ g, M₁ g ^ 2 ∂stdGaussian E = ∫ g, major r h₁ (perp u g) ^ 2 ∂stdGaussian E := by
      congr 1
      funext g
      rw [hperpu, major_add_smul hinv₁]
    rw [this]
    exact h
  have hE₂ : ∫ g, M₂ g ^ 2 ∂stdGaussian E ≤
      3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h₂ g ^ 2 ∂stdGaussian E) := by
    have h := integral_sq_major_le hr0 hr1 hh₂ hb₂ hu'
    have : ∫ g, M₂ g ^ 2 ∂stdGaussian E = ∫ g, major r h₂ (perp u' g) ^ 2 ∂stdGaussian E := by
      congr 1
      funext g
      rw [hperpu', major_add_smul hinv₂']
    rw [this]
    exact h
  have hMi : ∀ M : E → ℝ, Measurable M → (∀ g, 0 ≤ M g) → (∀ g, M g ≤ 1) →
      Integrable (fun g ↦ M g ^ 2) (stdGaussian E) := by
    intro M hm h0 h1
    exact integrable_of_abs_le (C := 1) (hm.pow_const 2) fun g ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (h0 g) (h1 g)
  have hI₁ := hMi M₁ hM₁m (fun _ ↦ major_nonneg) (fun _ ↦ major_le_one)
  have hI₂ := hMi M₂ hM₂m (fun _ ↦ major_nonneg) (fun _ ↦ major_le_one)
  calc (stdGaussian E).real {g | |⟪v₁, g⟫| ≤ t * |ou r h₁ g| ∧ |⟪v₂, g⟫| ≤ t * |ou r h₂ g|}
      ≤ (stdGaussian E).real B := measureReal_mono hsub
    _ = ∫ g₃, ((gaussianReal 0 1).prod (gaussianReal 0 1)).real (S g₃) ∂stdGaussian E := hBint
    _ ≤ ∫ g, t ^ 2 / σ * ((M₁ g ^ 2 + M₂ g ^ 2) / 2) ∂stdGaussian E := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ measureReal_nonneg) ?_
          (ae_of_all _ hbox)
        exact ((hI₁.add hI₂).div_const 2).const_mul _
    _ = t ^ 2 / σ * ((∫ g, M₁ g ^ 2 ∂stdGaussian E + ∫ g, M₂ g ^ 2 ∂stdGaussian E) / 2) := by
        rw [integral_const_mul, integral_div, integral_add hI₁ hI₂]
    _ ≤ t ^ 2 / σ * ((3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h₁ g ^ 2 ∂stdGaussian E) +
          3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h₂ g ^ 2 ∂stdGaussian E)) / 2) := by gcongr
    _ ≤ _ := by
        have hA : 0 ≤ (√(1 - r ^ 2))⁻¹ * (∫ g, h₁ g ^ 2 ∂stdGaussian E +
            ∫ g, h₂ g ^ 2 ∂stdGaussian E) := by
          have : 0 ≤ ∫ g, h₁ g ^ 2 ∂stdGaussian E := integral_nonneg fun _ ↦ sq_nonneg _
          have : 0 ≤ ∫ g, h₂ g ^ 2 ∂stdGaussian E := integral_nonneg fun _ ↦ sq_nonneg _
          positivity
        have ht2 : 0 ≤ t ^ 2 / σ := by positivity
        have : t ^ 2 / σ * ((3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h₁ g ^ 2 ∂stdGaussian E) +
            3 * ((√(1 - r ^ 2))⁻¹ * ∫ g, h₂ g ^ 2 ∂stdGaussian E)) / 2) =
            t ^ 2 / σ * (3 / 2 * ((√(1 - r ^ 2))⁻¹ * (∫ g, h₁ g ^ 2 ∂stdGaussian E +
              ∫ g, h₂ g ^ 2 ∂stdGaussian E))) := by ring
        rw [this, show 3 * t ^ 2 / σ = t ^ 2 / σ * 3 by ring, mul_assoc]
        gcongr
        nlinarith

end Strips

/-! ### Smoothed votes as Ornstein–Uhlenbeck images -/

section Votes

variable {ι : Type*} [Fintype ι]

/-- `f_η = U_r f_r` for `η = r²`: `s_(r²)(t) = E s_r(r t + √(1 - r²) z)` termwise. -/
theorem vote_eq_ou (p : ι → ℝ) {u : ι → E} (hu : ∀ k, ‖u k‖ = 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (g : E) : vote p u (r * r) g = ou r (vote p u r) g := by
  unfold ou vote
  rw [integral_finsetSum _ fun k _ ↦ (integrable_of_abs_le (C := 1) (by fun_prop)
    fun _ ↦ abs_smoothSign_le _ _).const_mul _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul]
  congr 1
  have h := integral_map (μ := stdGaussian E) (φ := fun g' ↦ ⟪u k, g'⟫)
    (f := fun z ↦ smoothSign r (r * ⟪u k, g⟫ + √(1 - r ^ 2) * z)) (by fun_prop)
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [map_inner_stdGaussian (hu k)] at h
  rw [← integral_smoothSign hr0 hr1 hr0 hr1, h]
  congr 1
  funext g'
  simp [inner_add_right, inner_smul_right]

/-- `E f_r² = E f_(r²) ψ`: the energy of `U_r ψ` is the correlation of `U_(r²) ψ` with `ψ`. -/
theorem integral_vote_sq (p : ι → ℝ) {u : ι → E} (hu : ∀ k, ‖u k‖ = 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) :
    ∫ g, vote p u r g ^ 2 ∂stdGaussian E =
      ∫ g, vote p u (r * r) g * vote p u 1 g ∂stdGaussian E := by
  simp_rw [sq]
  rw [integral_vote_mul_vote p hu hr0 hr1 hr0 hr1,
    integral_vote_mul_vote p hu (mul_nonneg hr0 hr0) (by nlinarith) zero_le_one le_rfl,
    mul_one]

end Votes

end BGHKLMM26
