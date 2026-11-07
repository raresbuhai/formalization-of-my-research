module

public import BGHKLMM26.RobustMIS.Static1D
public import Background.GaussianCalculus

/-!
# Static Gaussian lemmas in `ℝⁿ`: marginals and the bathtub bound

For measurable `g : ℝⁿ → [0, 1]` (§4 of `eldan-proof.tex`):

* the **marginal** of `g γₙ` along a unit vector `u` (Lemma 4.3 (i)): a measurable
  `f₁ : ℝ → [0, 1]` with `E[φ(⟨u, X⟩) g(X)] = ∫ φ f₁ dγ₁`;
* the **bathtub** bound `|U| ≤ q(S)` (Lemma 4.2), hence `0 ≤ ε(g) ≤ q(S)² ≤ 1/(2π)`.

The Bessel bounds are in `Bessel.lean`.

All statements are proved. The marginal is `f₁(s) = E g(s u + P_{u^⊥} Y)`: by
`Gaussian.map_proj_stdGaussian` (for the line `ℝ u`) a standard Gaussian is `P_u X + P_{u^⊥} Y`
with `X, Y` independent, and `⟨u, X⟩ ~ γ₁` (`Gaussian.map_inner_stdGaussian`). The bathtub bound
applies `bathtub1d` to the marginal along `U/|U|`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

namespace Static

theorem memLp_inner (u : Gs n) : MemLp (fun x : Gs n ↦ ⟪u, x⟫) 2 (gm n) :=
  IsGaussian.memLp_two_id.const_inner u

theorem integrable_inner_sq (u : Gs n) : Integrable (fun x : Gs n ↦ ⟪u, x⟫ ^ 2) (gm n) :=
  (memLp_inner u).integrable_sq

theorem integrable_of_bdd {g : Gs n → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Integrable g (gm n) :=
  (integrable_const C).mono' hg.aestronglyMeasurable (ae_of_all _ fun x ↦ by
    rw [Real.norm_eq_abs]; exact hC x)

theorem abs_le_one {g : Gs n → ℝ} (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (x : Gs n) : |g x| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith [h01 x]

/-- Integrability of `φ(⟨u, x⟩) g(x)` for `φ` of quadratic growth and bounded `g`. -/
theorem integrable_comp_inner_mul {g : Gs n → ℝ} (hg : Measurable g)
    (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (u : Gs n) {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ s, |φ s| ≤ C * (1 + s ^ 2)) :
    Integrable (fun x ↦ φ ⟪u, x⟫ * g x) (gm n) := by
  refine Integrable.mono' ((integrable_const C).add ((integrable_inner_sq u).const_mul C))
    ((hφ.comp (by fun_prop)).mul hg).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hC ⟪u, x⟫
  have h2 := abs_le_one h01 x
  calc |φ ⟪u, x⟫| * |g x| ≤ (C * (1 + ⟪u, x⟫ ^ 2)) * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = C + C * ⟪u, x⟫ ^ 2 := by ring

end Static

open Static

/-- **The marginal along a unit vector** (Lemma 4.3 (i)): `f₁(s) = E[g(s u + Y)]`, `Y` a standard
Gaussian on `u^⊥`. -/
theorem exists_marginal (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (u : Gs n) (hu : ‖u‖ = 1) :
    ∃ f₁ : ℝ → ℝ, Measurable f₁ ∧ (∀ s, 0 ≤ f₁ s ∧ f₁ s ≤ 1) ∧
      ∀ φ : ℝ → ℝ, Measurable φ → (∃ C, ∀ s, |φ s| ≤ C * (1 + s ^ 2)) →
        ∫ x, φ ⟪u, x⟫ * g x ∂gm n = ∫ s, φ s * f₁ s ∂gaussianReal 0 1 := by
  refine ⟨fun s ↦ ∫ y, g (s • u + (ℝ ∙ u)ᗮ.starProjection y) ∂gm n, ?_, fun s ↦ ⟨?_, ?_⟩, ?_⟩
  · have : StronglyMeasurable (Function.uncurry fun (s : ℝ) (y : Gs n) ↦
        g (s • u + (ℝ ∙ u)ᗮ.starProjection y)) :=
      (hg.comp (by fun_prop)).stronglyMeasurable
    exact this.integral_prod_right.measurable
  · exact integral_nonneg fun y ↦ (h01 _).1
  · calc ∫ y, g (s • u + (ℝ ∙ u)ᗮ.starProjection y) ∂gm n ≤ ∫ _y, (1 : ℝ) ∂gm n :=
          integral_mono_of_nonneg (ae_of_all _ fun y ↦ (h01 _).1) (integrable_const _)
            (ae_of_all _ fun y ↦ (h01 _).2)
      _ = 1 := by simp
  · rintro φ hφ ⟨C, hC⟩
    have hmap := Gaussian.map_proj_stdGaussian (E := Gs n) (ℝ ∙ u)
    have hint := integrable_comp_inner_mul hg h01 u hφ hC
    rw [Gaussian.integral_eq_of_map_prod (by fun_prop) hmap hint]
    have h2 : ∀ a, (ℝ ∙ u).starProjection a = ⟪u, a⟫ • u :=
      Submodule.starProjection_unit_singleton ℝ hu
    have h1 : ∀ a b : Gs n,
        ⟪u, (ℝ ∙ u).starProjection a + (ℝ ∙ u)ᗮ.starProjection b⟫ = ⟪u, a⟫ := by
      intro a b
      rw [inner_add_right, h2, real_inner_smul_right, real_inner_self_eq_norm_sq, hu,
        Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u)
          ((ℝ ∙ u)ᗮ.starProjection_apply_mem b)]
      ring
    simp only [h1]
    simp only [h2, integral_const_mul]
    rw [← Gaussian.map_inner_stdGaussian hu, integral_map (by fun_prop)]
    have hf₁ : Measurable fun s : ℝ ↦ ∫ y, g (s • u + (ℝ ∙ u)ᗮ.starProjection y) ∂gm n := by
      have : StronglyMeasurable (Function.uncurry fun (s : ℝ) (y : Gs n) ↦
          g (s • u + (ℝ ∙ u)ᗮ.starProjection y)) :=
        (hg.comp (by fun_prop)).stronglyMeasurable
      exact this.integral_prod_right.measurable
    exact (hφ.mul hf₁).aestronglyMeasurable

theorem gMean_mem (g : Gs n → ℝ) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    gMean g ∈ Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg fun x ↦ (h01 x).1, ?_⟩
  calc gMean g ≤ ∫ _x, (1 : ℝ) ∂gm n :=
        integral_mono_of_nonneg (ae_of_all _ fun x ↦ (h01 x).1) (integrable_const _)
          (ae_of_all _ fun x ↦ (h01 x).2)
    _ = 1 := by simp

/-- **Bathtub** (Lemma 4.2): `|U| ≤ q(S)`. -/
theorem norm_hermite1_le (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    ‖hermite1 g‖ ≤ qf (gMean g) := by
  by_cases h0 : hermite1 g = 0
  · rw [h0, norm_zero]; exact qf_nonneg _
  have hpos : 0 < ‖hermite1 g‖ := norm_pos_iff.2 h0
  obtain ⟨u, hu⟩ : ∃ u : Gs n, u = ‖hermite1 g‖⁻¹ • hermite1 g := ⟨_, rfl⟩
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  obtain ⟨f₁, hf₁, hf01, hφ⟩ := exists_marginal g hg h01 u hun
  have hint : Integrable (fun x : Gs n ↦ g x • x) (gm n) := by
    refine Integrable.mono' (IsGaussian.integrable_id.norm)
      (hg.smul measurable_id).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have := abs_le_one h01 x
    simp only [id]
    nlinarith [norm_nonneg x]
  have hU : ‖hermite1 g‖ = ∫ x, ⟪u, x⟫ * g x ∂gm n := by
    have : ∫ x, ⟪u, g x • x⟫ ∂gm n = ⟪u, hermite1 g⟫ := integral_inner hint u
    rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq] at this
    have e : ‖hermite1 g‖ = ‖hermite1 g‖⁻¹ * ‖hermite1 g‖ ^ 2 := by
      field_simp
    rw [e, ← this, ← hu]
    congr 1; funext x
    rw [real_inner_smul_right, mul_comm]
  have hS : gMean g = ∫ s, f₁ s ∂gaussianReal 0 1 := by
    have := hφ (fun _ ↦ 1) measurable_const ⟨1, fun s ↦ by rw [abs_one]; nlinarith [sq_nonneg s]⟩
    simpa [gMean] using this
  have hU' : ‖hermite1 g‖ = ∫ s, s * f₁ s ∂gaussianReal 0 1 := by
    rw [hU]
    exact hφ id measurable_id ⟨1, fun s ↦ by simp only [id]; nlinarith [abs_nonneg s, sq_abs s]⟩
  rw [hU', hS]
  exact (le_abs_self _).trans (bathtub1d f₁ hf₁ hf01)

theorem epsF_nonneg (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    0 ≤ epsF g := by
  have := norm_hermite1_le g hg h01
  have h0 := norm_nonneg (hermite1 g)
  unfold epsF
  nlinarith

theorem epsF_le (g : Gs n → ℝ) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    epsF g ≤ qf (gMean g) ^ 2 ∧ epsF g ≤ 1 / (2 * π) := by
  have _h := h01
  have h1 : epsF g ≤ qf (gMean g) ^ 2 := by
    unfold epsF; nlinarith [sq_nonneg ‖hermite1 g‖]
  exact ⟨h1, h1.trans (qf_sq_le _)⟩

end BGHKLMM26.RobustMIS
