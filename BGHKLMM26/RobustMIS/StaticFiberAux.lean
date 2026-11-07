module

public import BGHKLMM26.RobustMIS.Defs
public import Background.GaussianCalculus

/-!
# Fiber decomposition of the standard Gaussian along a unit vector

Helper material for `StaticFiber.lean` (Lemma 4.3 of `eldan-proof.tex`, standard fact (S1)): for
a unit vector `u`, the map `(y, s) ↦ s u + (y - ⟨u, y⟩ u)` pushes `γₙ ⊗ γ₁` forward to `γₙ`
(`map_fiber`), so `∫ φ dγₙ = ∫∫ φ(s u + P y) dγ₁(s) dγₙ(y)` (`integral_fiber`), and the Gaussian
moments `∫ ⟨v, x⟩ = 0`, `∫ ⟨v, x⟩⟨w, x⟩ = ⟨v, w⟩` with the integrability facts used there.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS.StaticFiber

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- The point `s u + (y - ⟨u, y⟩ u)` of the fiber over `y`. -/
noncomputable def fpt (u y : Gs n) (s : ℝ) : Gs n := s • u + (y - ⟪u, y⟫ • u)

theorem continuous_fpt (u : Gs n) : Continuous (fun p : Gs n × ℝ ↦ fpt u p.1 p.2) := by
  unfold fpt; fun_prop

theorem inner_self_of_norm {u : Gs n} (hu : ‖u‖ = 1) : ⟪u, u⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, hu, one_pow]

theorem inner_fpt_self {u : Gs n} (hu : ‖u‖ = 1) (y : Gs n) (s : ℝ) : ⟪u, fpt u y s⟫ = s := by
  simp [fpt, inner_add_right, inner_sub_right, inner_smul_right, hu]

theorem inner_fpt_of_orth {u v : Gs n} (hv : ⟪v, u⟫ = 0) (y : Gs n) (s : ℝ) :
    ⟪v, fpt u y s⟫ = ⟪v, y⟫ := by
  simp [fpt, inner_add_right, inner_sub_right, inner_smul_right, hv]

/-- The rank-one projection onto `u`. -/
noncomputable def projL (u : Gs n) : Gs n →L[ℝ] Gs n := (innerSL ℝ u).smulRight u

theorem projL_apply (u x : Gs n) : projL u x = ⟪u, x⟫ • u := by
  simp [projL]

theorem map_split {u : Gs n} (hu : ‖u‖ = 1) :
    ((gm n).prod (gm n)).map (fun p ↦ (p.1 - ⟪u, p.1⟫ • u) + ⟪u, p.2⟫ • u) = gm n := by
  have hu2 := inner_self_of_norm hu
  have := Gaussian.map_prod_stdGaussian (E := Gs n) (F := Gs n)
    (ContinuousLinearMap.id ℝ _ - projL u) (projL u)
    (fun t ↦ t - ⟪u, t⟫ • u) (fun t ↦ ⟪u, t⟫ • u) ?_ ?_ ?_
  · simpa [projL_apply] using this
  · intro x t
    simp only [sub_apply, ContinuousLinearMap.id_apply, projL_apply,
      inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, real_inner_comm,
      conj_trivial]
    ring
  · intro x t
    simp only [projL_apply, inner_smul_left, inner_smul_right, real_inner_comm, conj_trivial]
    ring
  · intro t
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      real_inner_comm, hu2, conj_trivial]
    ring

theorem map_fiber {u : Gs n} (hu : ‖u‖ = 1) :
    ((gm n).prod (gaussianReal 0 1)).map (fun p ↦ fpt u p.1 p.2) = gm n := by
  have hm : Measurable (fun x : Gs n ↦ ⟪u, x⟫) := by fun_prop
  have h1 := Measure.map_prod_map (gm n) (gm n) measurable_id hm
  rw [Measure.map_id, Gaussian.map_inner_stdGaussian hu] at h1
  rw [h1, Measure.map_map (continuous_fpt u).measurable (measurable_id.prodMap hm)]
  convert map_split hu using 2
  funext p
  simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd, fpt]
  abel

/-- **Fiber decomposition** of `γₙ` along a unit vector `u`. -/
theorem integral_fiber {u : Gs n} (hu : ‖u‖ = 1) {φ : Gs n → ℝ} (hφ : Integrable φ (gm n)) :
    ∫ x, φ x ∂gm n = ∫ y, ∫ s, φ (fpt u y s) ∂gaussianReal 0 1 ∂gm n :=
  Gaussian.integral_eq_of_map_prod (continuous_fpt u).measurable (map_fiber hu) hφ

/-- Fiber integrals of measurable functions are measurable. -/
theorem measurable_fiberInt {F : Gs n → ℝ → ℝ}
    (hF : Measurable (fun p : Gs n × ℝ ↦ F p.1 p.2)) :
    Measurable (fun y ↦ ∫ s, F y s ∂gaussianReal 0 1) :=
  (hF.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable

/-! ### Gaussian moments -/

theorem memLp_inner (v : Gs n) : MemLp (fun x ↦ ⟪v, x⟫) 2 (gm n) :=
  (IsGaussian.memLp_two_id (μ := gm n)).const_inner v

theorem integrable_inner (v : Gs n) : Integrable (fun x ↦ ⟪v, x⟫) (gm n) :=
  (memLp_inner v).integrable one_le_two

theorem integral_inner_gm (v : Gs n) : ∫ x, ⟪v, x⟫ ∂gm n = 0 := by
  have h := integral_inner (𝕜 := ℝ) (f := fun x : Gs n ↦ x)
    (IsGaussian.integrable_id (μ := gm n)) v
  have h0 : ∫ x, x ∂gm n = 0 := integral_id_stdGaussian
  rw [h, h0, inner_zero_right]

theorem integrable_inner_mul_inner (v w : Gs n) :
    Integrable (fun x ↦ ⟪v, x⟫ * ⟪w, x⟫) (gm n) :=
  (memLp_inner v).integrable_mul (memLp_inner w)

theorem integral_inner_mul_inner (v w : Gs n) : ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂gm n = ⟪v, w⟫ := by
  have h := covarianceBilin_apply (IsGaussian.memLp_two_id (μ := gm n)) v w
  rw [covarianceBilin_stdGaussian] at h
  have h0 : (gm n)[id] = 0 := integral_id_stdGaussian
  simp only [h0, sub_zero] at h
  exact h.symm

/-- A bounded measurable function times `⟨v, x⟩` is integrable. -/
theorem integrable_inner_mul {v : Gs n} {c : Gs n → ℝ} (hc : Measurable c) {C : ℝ}
    (hC : ∀ x, |c x| ≤ C) : Integrable (fun x ↦ ⟪v, x⟫ * c x) (gm n) :=
  (integrable_inner v).mul_bdd hc.aestronglyMeasurable (ae_of_all _ fun x ↦ hC x)

/-- A bounded measurable function times `⟨v, x⟩⟨w, x⟩ - k` is integrable. -/
theorem integrable_quad_mul {v w : Gs n} (k : ℝ) {c : Gs n → ℝ} (hc : Measurable c) {C : ℝ}
    (hC : ∀ x, |c x| ≤ C) : Integrable (fun x ↦ (⟪v, x⟫ * ⟪w, x⟫ - k) * c x) (gm n) :=
  ((integrable_inner_mul_inner v w).sub (integrable_const k)).mul_bdd hc.aestronglyMeasurable
    (ae_of_all _ fun x ↦ hC x)

/-- A bounded measurable function times `x` is integrable. -/
theorem integrable_smul_id {c : Gs n → ℝ} (hc : Measurable c) {C : ℝ} (hC : ∀ x, |c x| ≤ C) :
    Integrable (fun x ↦ c x • x) (gm n) :=
  (IsGaussian.integrable_id (μ := gm n)).bdd_smul C hc.aestronglyMeasurable
    (ae_of_all _ fun x ↦ hC x)

theorem inner_integral_smul {c : Gs n → ℝ} (hc : Measurable c) {C : ℝ} (hC : ∀ x, |c x| ≤ C)
    (v : Gs n) : ⟪v, ∫ x, c x • x ∂gm n⟫ = ∫ x, ⟪v, x⟫ * c x ∂gm n := by
  rw [← integral_inner (integrable_smul_id hc hC) v]
  congr 1
  funext x
  rw [inner_smul_right, mul_comm]

/-- `∫ (⟨v, x⟩⟨w, x⟩ - ⟨v, w⟩) dγ = 0`. -/
theorem integral_quad_gm (v w : Gs n) : ∫ x, (⟪v, x⟫ * ⟪w, x⟫ - ⟪v, w⟫) ∂gm n = 0 := by
  rw [integral_sub (integrable_inner_mul_inner v w) (integrable_const _),
    integral_inner_mul_inner]
  simp

end BGHKLMM26.RobustMIS.StaticFiber
