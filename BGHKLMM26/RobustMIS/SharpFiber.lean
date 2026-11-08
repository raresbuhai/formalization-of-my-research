module

public import BGHKLMM26.RobustMIS.SharpDefs
public import BGHKLMM26.RobustMIS.Gaussian
public import BGHKLMM26.RobustMIS.GaussL2

/-!
# The sharp Gaussian lemma: the noise form along a direction

For a unit vector `u`, write `x = s u + (y - ⟨u, y⟩ u)` (`StaticFiber.fpt u y s`, `s ∼ γ₁`,
`y ∼ γₙ`). Along `u` the noise operator has the Mehler kernel: `E f(t s + √(1 - t²) G) =
∫ f(s') K_t(s, s') dγ(s')` (`mehler_integral`), and `K_t = K_t(α, α) (1 ± ε)` near `(α, α)`,
uniformly for `|α| ≤ A` (`mehler_near`). For `φ` supported in the strip `|⟨u, x⟩ - α| ≤ r`, on
whose square `K_t = K_t(α, α) (1 ± ε)`, this collapses the strip to the fiber masses
`gfib φ u y = ∫ φ(fpt u y s) dγ(s)`:
`Q(φ) ≤ K_t(α, α) Q(gfib φ) + ε K_t(α, α) Q(gfib |φ|)` (`nBil_strip_le`).

Also: the mean and the first Hermite vector of `gfib φ u` (the projection of that of `φ` on `u⊥`)
for signed bounded `φ` (`integral_gfib_signed`, `hermite1_gfib`).

Proofs (helpers in namespace `SharpM`): `mehler_integral` pushes `γ₁` forward to `N(t s, 1 - t²)`
and compares densities (`gaussianPDFReal_eq_mehler`); `mehler_near` bounds the change of the
exponent (`abs_expo_sub_le`) and uses `|e^δ - 1| ≤ 2 |δ|`. For `nBil_strip_le`, with
`T φ(x) = E φ(t x + √(1 - t²) Z)` (`tOp`) and `k = K_t(α, α)`: `Q(φ) = ∫ φ T φ` (`nBil_eq_tOp`);
at `x = fpt u y s`, the fiber decomposition of `Z` and the linearity of `fpt` (`smul_fpt_add`) give
`T φ(x) = ∫∫ φ(fpt u (t y + √(1 - t²) y') (t s + √(1 - t²) s'')) dγ(s'') dγₙ(y')` (`tOp_fpt`), and
the Mehler kernel turns the inner integral into `∫ φ(fpt u Y s') K_t(s, s') dγ(s')`. Wherever the
integrand is nonzero both `s` and `s'` are in the strip, so `|T φ(x) - k T g̃(y)| ≤ ε k T |φ|~(y)`
(`strip_fiber_le`, `strip_tOp_le`) and pointwise `φ T φ ≤ k (T g̃) φ + ε k (T |φ|~) |φ|`
(`strip_point_le`); integrate over `s`, then over `y`. For `hermite1_gfib`:
`∫ ⟨v, y⟩ g̃ = ⟨v, F̂⁽¹⁾⟩` for `v ⊥ u` (`integral_inner_mul_gfib_orth`) and `∫ ⟨u, y⟩ g̃ = 0`, as
`g̃` is constant along `u` (`integral_inner_self_mul_gfib`).
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace
open Gaussian StaticFiber

variable {n : ℕ}

namespace SharpM

/-- The Gaussian density of `N(t s, 1 - t²)` is `φ(s') K_t(s, s')`. -/
theorem gaussianPDFReal_eq_mehler {t : ℝ} (ht : 0 < 1 - t ^ 2) (s x : ℝ) :
    gaussianPDFReal (t * s) (1 - t ^ 2).toNNReal x = npdf x * mehler t s x := by
  simp only [gaussianPDFReal, Real.coe_toNNReal _ ht.le, NNReal.coe_one, mehler]
  have h2 : √(2 * π * (1 - t ^ 2)) = √(2 * π * 1) * √(1 - t ^ 2) := by
    rw [mul_one, Real.sqrt_mul (by positivity)]
  have he : rexp (-(x - t * s) ^ 2 / (2 * (1 - t ^ 2))) =
      rexp (-(x - 0) ^ 2 / (2 * 1)) *
        rexp ((2 * t * s * x - t ^ 2 * (s ^ 2 + x ^ 2)) / (2 * (1 - t ^ 2))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h2, he, mul_inv]
  ring

end SharpM

/-- **The Mehler kernel** is the density of `t s + √(1 - t²) G` with respect to `γ₁`. -/
theorem mehler_integral {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {f : ℝ → ℝ} (hf : Measurable f)
    (s : ℝ) :
    ∫ z, f (t * s + √(1 - t ^ 2) * z) ∂gaussianReal 0 1 =
      ∫ s', f s' * mehler t s s' ∂gaussianReal 0 1 := by
  have hσ2 : 0 < 1 - t ^ 2 := by nlinarith
  have hmap : (gaussianReal 0 1).map (fun z ↦ t * s + √(1 - t ^ 2) * z) =
      gaussianReal (t * s) (1 - t ^ 2).toNNReal := by
    rw [show (fun z ↦ t * s + √(1 - t ^ 2) * z) = (t * s + ·) ∘ (√(1 - t ^ 2) * ·) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_const_add]
    congr 1
    · ring
    · ext
      simp [Real.sq_sqrt hσ2.le, Real.coe_toNNReal _ hσ2.le]
  have hv : (1 - t ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero]
    linarith
  have h := integral_map (μ := gaussianReal 0 1) (φ := fun z ↦ t * s + √(1 - t ^ 2) * z)
    (f := f) (by fun_prop) hf.aestronglyMeasurable
  rw [hmap] at h
  rw [← h, integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq]
  congr 1
  funext x
  rw [SharpM.gaussianPDFReal_eq_mehler hσ2, smul_eq_mul]
  ring

namespace SharpM

/-- `c e^a - c e^b = c e^b (e^(a - b) - 1)`. -/
theorem mul_exp_sub (c a b : ℝ) : c * rexp a - c * rexp b = c * rexp b * (rexp (a - b) - 1) := by
  rw [mul_sub, mul_one, mul_assoc, ← Real.exp_add, add_sub_cancel]

/-- `K_t(s, s') - K_t(α, α) = K_t(α, α) (e^δ - 1)`. -/
theorem mehler_sub (t s s' α : ℝ) :
    mehler t s s' - mehler t α α = mehler t α α *
      (rexp ((2 * t * s * s' - t ^ 2 * (s ^ 2 + s' ^ 2)) / (2 * (1 - t ^ 2)) -
        (2 * t * α * α - t ^ 2 * (α ^ 2 + α ^ 2)) / (2 * (1 - t ^ 2))) - 1) := by
  unfold mehler
  exact mul_exp_sub _ _ _

/-- The Mehler kernel is positive. -/
theorem mehler_pos {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (s s' : ℝ) : 0 < mehler t s s' := by
  have hσ2 : 0 < 1 - t ^ 2 := by nlinarith
  unfold mehler
  have := Real.sqrt_pos.2 hσ2
  positivity

/-- The exponent of the Mehler kernel is locally Lipschitz. -/
theorem abs_expo_sub_le {t α s s' A r : ℝ} (ht : |t| ≤ 1) (hα : |α| ≤ A) (hr : r ≤ 1)
    (hs : |s - α| ≤ r) (hs' : |s' - α| ≤ r) :
    |(2 * t * s * s' - t ^ 2 * (s ^ 2 + s' ^ 2)) - (2 * t * α * α - t ^ 2 * (α ^ 2 + α ^ 2))| ≤
      (8 * A + 4) * r := by
  have hA : 0 ≤ A := (abs_nonneg α).trans hα
  have hr0 : 0 ≤ r := (abs_nonneg _).trans hs
  have hsA : |s| ≤ A + 1 := by
    have := abs_sub_abs_le_abs_sub s α
    linarith
  have hs'A : |s'| ≤ A + 1 := by
    have := abs_sub_abs_le_abs_sub s' α
    linarith
  have hP : |s * s' - α ^ 2| ≤ (2 * A + 1) * r := by
    rw [show s * s' - α ^ 2 = s * (s' - α) + α * (s - α) by ring]
    calc _ ≤ |s * (s' - α)| + |α * (s - α)| := abs_add_le _ _
      _ = |s| * |s' - α| + |α| * |s - α| := by rw [abs_mul, abs_mul]
      _ ≤ (A + 1) * r + A * r :=
          add_le_add (mul_le_mul hsA hs' (abs_nonneg _) (by linarith))
            (mul_le_mul hα hs (abs_nonneg _) hA)
      _ = _ := by ring
  have hQ : ∀ x, |x - α| ≤ r → |x| ≤ A + 1 → |x ^ 2 - α ^ 2| ≤ (2 * A + 1) * r := by
    intro x hx hxA
    rw [show x ^ 2 - α ^ 2 = (x + α) * (x - α) by ring, abs_mul]
    have : |x + α| ≤ 2 * A + 1 := (abs_add_le _ _).trans (by linarith)
    exact mul_le_mul this hx (abs_nonneg _) (by linarith)
  have ht2 : |t ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) ht
  rw [show (2 * t * s * s' - t ^ 2 * (s ^ 2 + s' ^ 2)) -
      (2 * t * α * α - t ^ 2 * (α ^ 2 + α ^ 2)) =
      2 * (t * (s * s' - α ^ 2)) - (t ^ 2 * (s ^ 2 - α ^ 2) + t ^ 2 * (s' ^ 2 - α ^ 2)) by ring]
  have h1 : |t * (s * s' - α ^ 2)| ≤ (2 * A + 1) * r := by
    rw [abs_mul]
    calc _ ≤ 1 * ((2 * A + 1) * r) := mul_le_mul ht hP (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h2 : |t ^ 2 * (s ^ 2 - α ^ 2)| ≤ (2 * A + 1) * r := by
    rw [abs_mul]
    calc _ ≤ 1 * ((2 * A + 1) * r) :=
          mul_le_mul ht2 (hQ s hs hsA) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have h3 : |t ^ 2 * (s' ^ 2 - α ^ 2)| ≤ (2 * A + 1) * r := by
    rw [abs_mul]
    calc _ ≤ 1 * ((2 * A + 1) * r) :=
          mul_le_mul ht2 (hQ s' hs' hs'A) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have e1 : |2 * (t * (s * s' - α ^ 2))| = 2 * |t * (s * s' - α ^ 2)| := by
    rw [abs_mul, abs_two]
  calc _ ≤ |2 * (t * (s * s' - α ^ 2))| +
        |t ^ 2 * (s ^ 2 - α ^ 2) + t ^ 2 * (s' ^ 2 - α ^ 2)| := abs_sub _ _
    _ ≤ _ := by linarith [abs_add_le (t ^ 2 * (s ^ 2 - α ^ 2)) (t ^ 2 * (s' ^ 2 - α ^ 2))]

end SharpM

/-- `K_t(s, s') = K_t(α, α) (1 ± ε)` for `s, s'` near `α`, uniformly for `|α| ≤ A`. -/
theorem mehler_near {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ α s s' : ℝ, |α| ≤ A → |s - α| ≤ r → |s' - α| ≤ r →
      |mehler t s s' - mehler t α α| ≤ ε * mehler t α α := by
  have hD : 0 < 2 * (1 - t ^ 2) := by nlinarith
  have hL : 0 < 8 * |A| + 4 := by positivity
  have hm : 0 < min 1 (ε / 2) := lt_min one_pos (by positivity)
  refine ⟨min 1 (min 1 (ε / 2) * (2 * (1 - t ^ 2)) / (8 * |A| + 4)), by positivity, ?_⟩
  intro α s s' hα hs hs'
  have hr1 := min_le_left 1 (min 1 (ε / 2) * (2 * (1 - t ^ 2)) / (8 * |A| + 4))
  have hr2 := min_le_right 1 (min 1 (ε / 2) * (2 * (1 - t ^ 2)) / (8 * |A| + 4))
  have ht : |t| ≤ 1 := abs_le.2 ⟨ht0.le, ht1.le⟩
  have hN := SharpM.abs_expo_sub_le ht (hα.trans (le_abs_self A)) hr1 hs hs'
  have hδ : |((2 * t * s * s' - t ^ 2 * (s ^ 2 + s' ^ 2)) -
      (2 * t * α * α - t ^ 2 * (α ^ 2 + α ^ 2))) / (2 * (1 - t ^ 2))| ≤ min 1 (ε / 2) := by
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    calc _ ≤ (8 * |A| + 4) * min 1 (min 1 (ε / 2) * (2 * (1 - t ^ 2)) / (8 * |A| + 4)) := hN
      _ ≤ (8 * |A| + 4) * (min 1 (ε / 2) * (2 * (1 - t ^ 2)) / (8 * |A| + 4)) :=
          mul_le_mul_of_nonneg_left hr2 hL.le
      _ = _ := by field_simp
  have he := Real.abs_exp_sub_one_le (hδ.trans (min_le_left _ _))
  rw [SharpM.mehler_sub, div_sub_div_same, abs_mul, abs_of_pos (SharpM.mehler_pos ht0 ht1 α α),
    mul_comm ε]
  apply mul_le_mul_of_nonneg_left _ (SharpM.mehler_pos ht0 ht1 α α).le
  linarith [min_le_right 1 (ε / 2)]

namespace SharpM

/-- `|∫ f dμ| ≤ C` for `|f| ≤ C` and a probability measure `μ`. -/
theorem abs_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂μ| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at h

/-- `|a b| ≤ 1` for `|a|, |b| ≤ 1`. -/
theorem abs_mul_le_one {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a * b| ≤ 1 := by
  rw [abs_mul]
  calc |a| * |b| ≤ 1 * 1 := mul_le_mul ha hb (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Parametric integrals of jointly measurable functions are measurable. -/
theorem measurable_integral_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ν : Measure β} [SFinite ν] {F : α × β → ℝ} (hF : Measurable F) :
    Measurable (fun a ↦ ∫ b, F (a, b) ∂ν) :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

/-- `K_t(s, ·)` is integrable against `γ₁` (its integral is `1`). -/
theorem integrable_mehler {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) (s : ℝ) :
    Integrable (fun s' ↦ mehler t s s') (gaussianReal 0 1) := by
  have h := mehler_integral ht0 ht1 (f := fun _ ↦ (1 : ℝ)) measurable_const s
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, one_mul] at h
  apply Integrable.of_integral_ne_zero
  rw [← h]
  exact one_ne_zero

/-- `|g̃| ≤ C` for `|φ| ≤ C`. -/
theorem abs_gfib_le {φ : Gs n → ℝ} {u : Gs n} {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) (y : Gs n) :
    |gfib φ u y| ≤ C :=
  abs_integral_le fun _ ↦ hφC _

/-- The fiber of a fiber point is the same fiber. -/
theorem fpt_fpt {u : Gs n} (hu : ‖u‖ = 1) (y : Gs n) (s s' : ℝ) :
    fpt u (fpt u y s) s' = fpt u y s' := by
  change s' • u + (fpt u y s - ⟪u, fpt u y s⟫ • u) = _
  rw [inner_fpt_self hu]
  simp only [fpt]
  abel

/-- `g̃` is constant along `u`. -/
theorem gfib_fpt {u : Gs n} (hu : ‖u‖ = 1) (φ : Gs n → ℝ) (y : Gs n) (s : ℝ) :
    gfib φ u (fpt u y s) = gfib φ u y := by
  unfold gfib
  simp_rw [fpt_fpt hu]

/-- `fpt u` is linear in `(y, s)`. -/
theorem smul_fpt_add (u y y' : Gs n) (a b s s' : ℝ) :
    a • fpt u y s + b • fpt u y' s' = fpt u (a • y + b • y') (a * s + b * s') := by
  simp only [fpt, inner_add_right, inner_smul_right, smul_add, smul_sub, add_smul, mul_smul]
  abel

/-- `T φ(x) = E φ(t x + c Z)`. -/
noncomputable def tOp (t c : ℝ) (φ : Gs n → ℝ) (x : Gs n) : ℝ := ∫ z, φ (t • x + c • z) ∂gm n

theorem measurable_tOp (t c : ℝ) {φ : Gs n → ℝ} (hφ : Measurable φ) :
    Measurable (tOp t c φ) :=
  measurable_integral_right (F := fun p : Gs n × Gs n ↦ φ (t • p.1 + c • p.2))
    (hφ.comp (by fun_prop))

theorem abs_tOp_le (t c : ℝ) {φ : Gs n → ℝ} {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) (x : Gs n) :
    |tOp t c φ x| ≤ C :=
  abs_integral_le fun _ ↦ hφC _

/-- `Q(F, G) = ∫ F T G`. -/
theorem nBil_eq_tOp (t : ℝ) (F G : Gs n → ℝ) :
    nBil t F G = ∫ x, F x * tOp t (√(1 - t ^ 2)) G x ∂gm n := by
  unfold nBil tOp
  congr 1
  funext x
  rw [integral_const_mul]

/-- `T φ` on a fiber point, by the fiber decomposition of the noise. -/
theorem tOp_fpt {u : Gs n} (hu : ‖u‖ = 1) (t c : ℝ) {φ : Gs n → ℝ} (hφ : Measurable φ)
    {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) (y : Gs n) (s : ℝ) :
    tOp t c φ (fpt u y s) =
      ∫ y', ∫ s'', φ (fpt u (t • y + c • y') (t * s + c * s'')) ∂gaussianReal 0 1 ∂gm n := by
  unfold tOp
  rw [integral_fiber hu (φ := fun z ↦ φ (t • fpt u y s + c • z))
    (Gaussian.integrable_of_abs_le (hφ.comp (by fun_prop)) fun _ ↦ hφC _)]
  simp_rw [smul_fpt_add]

/-- One fiber of the strip: for `s` in the strip, `|E φ(fpt u Y (t s + √(1 - t²) G)) - k g̃(Y)| ≤
ε k |φ|~(Y)`, `k = K_t(α, α)`. -/
theorem strip_fiber_le {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    {α r ε : ℝ}
    (hK : ∀ s s', |s - α| ≤ r → |s' - α| ≤ r →
      |mehler t s s' - mehler t α α| ≤ ε * mehler t α α)
    {φ : Gs n → ℝ} (hφ : Measurable φ) (hφ1 : ∀ x, |φ x| ≤ 1)
    (hsupp : ∀ x, r < |⟪u, x⟫ - α| → φ x = 0) (Y : Gs n) {s : ℝ} (hs : |s - α| ≤ r) :
    |∫ s'', φ (fpt u Y (t * s + √(1 - t ^ 2) * s'')) ∂gaussianReal 0 1 -
        mehler t α α * gfib φ u Y| ≤ ε * mehler t α α * gfib (fun x ↦ |φ x|) u Y := by
  have hm : Measurable (fun s' ↦ φ (fpt u Y s')) := hφ.comp (measurable_fpt_left u Y)
  have hM := mehler_integral ht0 ht1 hm s
  have hi0 : Integrable (fun s' ↦ φ (fpt u Y s')) (gaussianReal 0 1) :=
    Gaussian.integrable_of_abs_le hm fun _ ↦ hφ1 _
  have hi1 : Integrable (fun s' ↦ φ (fpt u Y s') * mehler t s s') (gaussianReal 0 1) :=
    (integrable_mehler ht0 ht1 s).bdd_mul hm.aestronglyMeasurable
      (ae_of_all _ fun _ ↦ by rw [Real.norm_eq_abs]; exact hφ1 _)
  have hi2 : Integrable (fun s' ↦ φ (fpt u Y s') * mehler t α α) (gaussianReal 0 1) :=
    hi0.mul_const _
  rw [hM, show gfib φ u Y = ∫ s', φ (fpt u Y s') ∂gaussianReal 0 1 from rfl,
    mul_comm (mehler t α α), ← integral_mul_const, ← integral_sub hi1 hi2,
    show gfib (fun x ↦ |φ x|) u Y = ∫ s', |φ (fpt u Y s')| ∂gaussianReal 0 1 from rfl,
    ← integral_const_mul]
  refine (Real.norm_eq_abs _).symm.trans_le
    (norm_integral_le_of_norm_le (hi0.abs.const_mul _) (ae_of_all _ fun s' ↦ ?_))
  rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
  by_cases h : r < |s' - α|
  · have h0 : φ (fpt u Y s') = 0 := hsupp _ (by rwa [inner_fpt_self hu])
    simp [h0]
  · push Not at h
    rw [mul_comm (ε * mehler t α α)]
    exact mul_le_mul_of_nonneg_left (hK s s' hs h) (abs_nonneg _)

/-- For `s` in the strip, `|T φ(fpt u y s) - k T g̃(y)| ≤ ε k T |φ|~(y)`. -/
theorem strip_tOp_le {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    {α r ε : ℝ}
    (hK : ∀ s s', |s - α| ≤ r → |s' - α| ≤ r →
      |mehler t s s' - mehler t α α| ≤ ε * mehler t α α)
    {φ : Gs n → ℝ} (hφ : Measurable φ) (hφ1 : ∀ x, |φ x| ≤ 1)
    (hsupp : ∀ x, r < |⟪u, x⟫ - α| → φ x = 0) (y : Gs n) {s : ℝ} (hs : |s - α| ≤ r) :
    |tOp t (√(1 - t ^ 2)) φ (fpt u y s) - mehler t α α * tOp t (√(1 - t ^ 2)) (gfib φ u) y| ≤
      ε * mehler t α α * tOp t (√(1 - t ^ 2)) (gfib (fun x ↦ |φ x|) u) y := by
  have hmY : Measurable (fun y' : Gs n ↦ t • y + √(1 - t ^ 2) • y') := by fun_prop
  have hφa : Measurable (fun x ↦ |φ x|) := by fun_prop
  have hMm : Measurable (fun y' ↦ ∫ s'', φ (fpt u (t • y + √(1 - t ^ 2) • y')
      (t * s + √(1 - t ^ 2) * s'')) ∂gaussianReal 0 1) :=
    measurable_fiberInt (F := fun y' s'' ↦ φ (fpt u (t • y + √(1 - t ^ 2) • y')
      (t * s + √(1 - t ^ 2) * s''))) (hφ.comp ((continuous_fpt u).measurable.comp
        (by fun_prop : Measurable fun p : Gs n × ℝ ↦
          (t • y + √(1 - t ^ 2) • p.1, t * s + √(1 - t ^ 2) * p.2))))
  have hi1 : Integrable (fun y' ↦ ∫ s'', φ (fpt u (t • y + √(1 - t ^ 2) • y')
      (t * s + √(1 - t ^ 2) * s'')) ∂gaussianReal 0 1) (gm n) :=
    Gaussian.integrable_of_abs_le hMm fun _ ↦ abs_integral_le fun _ ↦ hφ1 _
  have hi2 : Integrable (fun y' ↦ mehler t α α * gfib φ u (t • y + √(1 - t ^ 2) • y')) (gm n) :=
    (Gaussian.integrable_of_abs_le ((measurable_gfib hφ).comp hmY)
      fun _ ↦ abs_gfib_le hφ1 _).const_mul _
  have hi3 : Integrable (fun y' ↦ ε * mehler t α α *
      gfib (fun x ↦ |φ x|) u (t • y + √(1 - t ^ 2) • y')) (gm n) :=
    (Gaussian.integrable_of_abs_le ((measurable_gfib hφa).comp hmY)
      fun _ ↦ abs_gfib_le (fun x ↦ by rw [abs_abs]; exact hφ1 x) _).const_mul _
  rw [tOp_fpt hu t _ hφ hφ1 y s]
  unfold tOp
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub hi1 hi2]
  exact (Real.norm_eq_abs _).symm.trans_le (norm_integral_le_of_norm_le hi3
    (ae_of_all _ fun y' ↦ by
      rw [Real.norm_eq_abs]; exact strip_fiber_le ht0 ht1 hu hK hφ hφ1 hsupp _ hs))

/-- The pointwise strip bound
`φ T φ ≤ k (T g̃)(y) φ + ε k (T |φ|~)(y) |φ|` at `x = fpt u y s`. -/
theorem strip_point_le {t : ℝ} (ht0 : -1 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    {α r ε : ℝ}
    (hK : ∀ s s', |s - α| ≤ r → |s' - α| ≤ r →
      |mehler t s s' - mehler t α α| ≤ ε * mehler t α α)
    {φ : Gs n → ℝ} (hφ : Measurable φ) (hφ1 : ∀ x, |φ x| ≤ 1)
    (hsupp : ∀ x, r < |⟪u, x⟫ - α| → φ x = 0) (y : Gs n) (s : ℝ) :
    φ (fpt u y s) * tOp t (√(1 - t ^ 2)) φ (fpt u y s) ≤
      mehler t α α * tOp t (√(1 - t ^ 2)) (gfib φ u) y * φ (fpt u y s) +
        ε * mehler t α α * tOp t (√(1 - t ^ 2)) (gfib (fun x ↦ |φ x|) u) y *
          |φ (fpt u y s)| := by
  by_cases h : r < |s - α|
  · have h0 : φ (fpt u y s) = 0 := hsupp _ (by rwa [inner_fpt_self hu])
    simp [h0]
  · push Not at h
    have hb := strip_tOp_le ht0 ht1 hu hK hφ hφ1 hsupp y h
    have h2 : φ (fpt u y s) * (tOp t (√(1 - t ^ 2)) φ (fpt u y s) -
        mehler t α α * tOp t (√(1 - t ^ 2)) (gfib φ u) y) ≤
        |φ (fpt u y s)| *
          (ε * mehler t α α * tOp t (√(1 - t ^ 2)) (gfib (fun x ↦ |φ x|) u) y) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _))
    linarith

end SharpM

/-- **The strip bound**: for `φ` supported in the strip `|⟨u, x⟩ - α| ≤ r` on whose square the
Mehler kernel is within `ε K_t(α, α)` of `K_t(α, α)`,
`Q(φ) ≤ K_t(α, α) Q(gfib φ) + ε K_t(α, α) Q(gfib |φ|)`. -/
theorem nBil_strip_le {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {u : Gs n} (hu : ‖u‖ = 1)
    {α r ε : ℝ}
    (hK : ∀ s s', |s - α| ≤ r → |s' - α| ≤ r →
      |mehler t s s' - mehler t α α| ≤ ε * mehler t α α)
    {φ : Gs n → ℝ} (hφ : Measurable φ) (hφ1 : ∀ x, |φ x| ≤ 1)
    (hsupp : ∀ x, r < |⟪u, x⟫ - α| → φ x = 0) :
    nBil t φ φ ≤ mehler t α α * nBil t (gfib φ u) (gfib φ u) +
      ε * mehler t α α * nBil t (gfib (fun x ↦ |φ x|) u) (gfib (fun x ↦ |φ x|) u) := by
  have ht0' : -1 < t := by linarith
  have hT := SharpM.measurable_tOp t (√(1 - t ^ 2)) hφ
  have hTb := SharpM.abs_tOp_le t (√(1 - t ^ 2)) hφ1
  have hφa : Measurable (fun x ↦ |φ x|) := by fun_prop
  have hφa1 : ∀ x, |(fun x ↦ |φ x|) x| ≤ 1 := fun x ↦ by rw [abs_abs]; exact hφ1 x
  have hg := measurable_gfib (u := u) hφ
  have hga := measurable_gfib (u := u) hφa
  have hgb := SharpM.abs_gfib_le (u := u) hφ1
  have hgab := SharpM.abs_gfib_le (u := u) hφa1
  have hi0 : Integrable (fun y ↦ gfib φ u y * SharpM.tOp t (√(1 - t ^ 2)) (gfib φ u) y)
      (gm n) :=
    Gaussian.integrable_of_abs_le (hg.mul (SharpM.measurable_tOp t _ hg))
      fun y ↦ SharpM.abs_mul_le_one (hgb y) (SharpM.abs_tOp_le t _ hgb y)
  have hi1 : Integrable (fun y ↦ gfib (fun x ↦ |φ x|) u y *
      SharpM.tOp t (√(1 - t ^ 2)) (gfib (fun x ↦ |φ x|) u) y) (gm n) :=
    Gaussian.integrable_of_abs_le (hga.mul (SharpM.measurable_tOp t _ hga))
      fun y ↦ SharpM.abs_mul_le_one (hgab y) (SharpM.abs_tOp_le t _ hgab y)
  rw [SharpM.nBil_eq_tOp, SharpM.nBil_eq_tOp, SharpM.nBil_eq_tOp,
    integral_fiber hu (φ := fun x ↦ φ x * SharpM.tOp t (√(1 - t ^ 2)) φ x)
      (Gaussian.integrable_of_abs_le (hφ.mul hT) fun x ↦ SharpM.abs_mul_le_one (hφ1 x) (hTb x)),
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi0.const_mul _) (hi1.const_mul _)]
  refine integral_mono ?_ ((hi0.const_mul _).add (hi1.const_mul _)) fun y ↦ ?_
  · exact Gaussian.integrable_of_abs_le
      (measurable_fiberInt (F := fun y s ↦ φ (fpt u y s) * SharpM.tOp t (√(1 - t ^ 2)) φ
        (fpt u y s)) ((hφ.mul hT).comp (continuous_fpt u).measurable))
      fun y ↦ SharpM.abs_integral_le fun s ↦ SharpM.abs_mul_le_one (hφ1 _) (hTb _)
  · have hm1 : Measurable (fun s ↦ φ (fpt u y s)) := hφ.comp (measurable_fpt_left u y)
    have hi : Integrable (fun s ↦ φ (fpt u y s)) (gaussianReal 0 1) :=
      Gaussian.integrable_of_abs_le hm1 fun _ ↦ hφ1 _
    calc ∫ s, φ (fpt u y s) * SharpM.tOp t (√(1 - t ^ 2)) φ (fpt u y s) ∂gaussianReal 0 1
        ≤ ∫ s, (mehler t α α * SharpM.tOp t (√(1 - t ^ 2)) (gfib φ u) y * φ (fpt u y s) +
            ε * mehler t α α * SharpM.tOp t (√(1 - t ^ 2)) (gfib (fun x ↦ |φ x|) u) y *
              |φ (fpt u y s)|) ∂gaussianReal 0 1 :=
          integral_mono (Gaussian.integrable_of_abs_le
            ((hφ.mul hT).comp (measurable_fpt_left u y))
            fun s ↦ SharpM.abs_mul_le_one (hφ1 _) (hTb _))
            ((hi.const_mul _).add (hi.abs.const_mul _))
            fun s ↦ SharpM.strip_point_le ht0' ht1 hu hK hφ hφ1 hsupp y s
      _ = mehler t α α * (gfib φ u y * SharpM.tOp t (√(1 - t ^ 2)) (gfib φ u) y) +
            ε * mehler t α α * (gfib (fun x ↦ |φ x|) u y *
              SharpM.tOp t (√(1 - t ^ 2)) (gfib (fun x ↦ |φ x|) u) y) := by
          rw [integral_add (hi.const_mul _) (hi.abs.const_mul _), integral_const_mul,
            integral_const_mul, show gfib φ u y = ∫ s, φ (fpt u y s) ∂gaussianReal 0 1 from rfl,
            show gfib (fun x ↦ |φ x|) u y = ∫ s, |φ (fpt u y s)| ∂gaussianReal 0 1 from rfl]
          ring

/-- The mean of the fiber masses, for signed bounded `φ`. -/
theorem integral_gfib_signed {u : Gs n} (hu : ‖u‖ = 1) {φ : Gs n → ℝ} (hφ : Measurable φ)
    {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) :
    ∫ y, gfib φ u y ∂gm n = ∫ x, φ x ∂gm n := by
  rw [integral_fiber hu (Gaussian.integrable_of_abs_le hφ hφC)]
  rfl

namespace SharpM

/-- `∫ ⟨v, y⟩ g̃(y) = ⟨v, F̂⁽¹⁾⟩` for `v ⊥ u`, for signed bounded `φ`. -/
theorem integral_inner_mul_gfib_orth {u : Gs n} (hu : ‖u‖ = 1) {φ : Gs n → ℝ}
    (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) {v : Gs n} (hv : ⟪v, u⟫ = 0) :
    ∫ y, ⟪v, y⟫ * gfib φ u y ∂gm n = ⟪v, hermite1 φ⟫ := by
  rw [hermite1, inner_integral_smul hφ hφC v, integral_fiber hu (integrable_inner_mul hφ hφC)]
  congr 1
  funext y
  unfold gfib
  rw [← integral_const_mul]
  congr 1
  funext s
  rw [inner_fpt_of_orth hv]

/-- `∫ ⟨u, y⟩ g̃(y) = 0`: `g̃` does not depend on `⟨u, y⟩`. -/
theorem integral_inner_self_mul_gfib {u : Gs n} (hu : ‖u‖ = 1) {φ : Gs n → ℝ}
    (hφ : Measurable φ) {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) :
    ∫ y, ⟪u, y⟫ * gfib φ u y ∂gm n = 0 := by
  rw [integral_fiber hu (integrable_inner_mul (measurable_gfib hφ) (abs_gfib_le hφC))]
  have h : ∀ y, ∫ s, ⟪u, fpt u y s⟫ * gfib φ u (fpt u y s) ∂gaussianReal 0 1 = 0 := by
    intro y
    simp_rw [inner_fpt_self hu, gfib_fpt hu]
    rw [integral_mul_const, integral_id_gaussianReal, zero_mul]
  simp_rw [h, integral_zero]

end SharpM

/-- The first Hermite vector of the fiber masses is that of `φ` projected on `u⊥`. -/
theorem hermite1_gfib {u : Gs n} (hu : ‖u‖ = 1) {φ : Gs n → ℝ} (hφ : Measurable φ)
    {C : ℝ} (hφC : ∀ x, |φ x| ≤ C) :
    hermite1 (gfib φ u) = hermite1 φ - ⟪u, hermite1 φ⟫ • u := by
  have hgm := measurable_gfib (u := u) hφ
  have hgC : ∀ y, |gfib φ u y| ≤ C := SharpM.abs_gfib_le hφC
  have hu2 := inner_self_of_norm hu
  apply ext_inner_left ℝ
  intro v
  have hw : ⟪v - ⟪u, v⟫ • u, u⟫ = 0 := by
    rw [inner_sub_left, inner_smul_left, hu2, real_inner_comm]
    simp
  have hsplit : ∀ y, ⟪v, y⟫ * gfib φ u y =
      ⟪v - ⟪u, v⟫ • u, y⟫ * gfib φ u y + ⟪u, v⟫ * (⟪u, y⟫ * gfib φ u y) := by
    intro y
    rw [inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
    ring
  have hH := SharpM.integral_inner_mul_gfib_orth hu hφ hφC hw
  rw [inner_sub_left, inner_smul_left] at hH
  rw [show hermite1 (gfib φ u) = ∫ x, gfib φ u x • x ∂gm n from rfl,
    inner_integral_smul hgm hgC v]
  simp_rw [hsplit]
  rw [integral_add (integrable_inner_mul hgm hgC) ((integrable_inner_mul hgm hgC).const_mul _),
    integral_const_mul, SharpM.integral_inner_self_mul_gfib hu hφ hφC, hH, inner_sub_right,
    inner_smul_right, real_inner_comm u v]
  simp only [conj_trivial]
  ring

end BGHKLMM26.RobustMIS
