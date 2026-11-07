module

public import BGHKLMM26.RobustMIS.Multilinear

/-!
# Multilinear polynomials on Gaussian space

The multilinear monomials `∏_{i∈S} Gᵢ` are orthonormal in `L²(γ)` (`E[G^S G^T] = [S = T]`, by
independence of the coordinates), so for `p = mlEval c`: `E[p q] = ∑ c_S d_S`, `E p = c_∅`,
`E[p Gᵢ] = c_{{i}}`, and `Stab_t(p) = ∑ t^|S| c_S²` (`E[X^S Y^T] = t^|S| [S = T]` for
`Y = tX + √(1-t²) Z`); consequences for `P_{u,r} = gaussExt r u`.

Material: Mathlib's `map_pi_eq_stdGaussian` (coordinates of `stdGaussian` are i.i.d.),
`integral_fintype_prod_eq_prod`, `Measure.pi`; `Gaussian.map_add_smul_stdGaussian`
(`Background/GaussianCalculus.lean`) for the pair `(X, Y)`.

All statements are proved. The work is done for an arbitrary product `Measure.pi ν` of
probability laws on `ℝ` (namespace `MultilinearGauss`, reused by `Bonami.lean`): the monomials
`mono s x = ∏_{i∈S} xᵢ` and `indC s` (`mlEval (indC s) = mono s`), `mlEval_mul_arg`
(`p(t x) = (T_t p)(x)`), `continuous_mlEval'`; under centered laws with unit variance,
`integral_mono_mul_mono` and `integral_mlEval_mul_pi'` (orthonormality), `integral_mlEval_affine`
(`E_z p(a + b z) = p(a)`: averaging out independent centered noise), `memLp_mlEval_pi'`. The
Gaussian case goes through `integral_gm` (`∫ F dγ = ∫ F(toLp x) d(⊗ N(0,1))`, from
`map_pi_eq_stdGaussian`). `gStab_mlEval` does not need `t ∈ [-1, 1]`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

namespace MultilinearGauss

/-! ### Monomials -/

/-- The monomial `x^S = ∏_{i ∈ S} xᵢ`. -/
noncomputable def mono (s : Cube (Fin R)) (x : Fin R → ℝ) : ℝ := ∏ i, if s i then x i else 1

theorem mlEval_eq_sum (c : Cube (Fin R) → ℝ) (x : Fin R → ℝ) :
    mlEval c x = ∑ s, c s * mono s x := rfl

/-- The coefficient vector of the monomial `x^S`. -/
noncomputable def indC (s₀ : Cube (Fin R)) : Cube (Fin R) → ℝ := fun s ↦ if s = s₀ then 1 else 0

theorem mlEval_indC (s₀ : Cube (Fin R)) (x : Fin R → ℝ) : mlEval (indC s₀) x = mono s₀ x := by
  simp [mlEval_eq_sum, indC]

theorem mono_single (i : Fin R) (x : Fin R → ℝ) : mono (Multilinear.single i) x = x i := by
  unfold mono Multilinear.single
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

@[simp] theorem mono_zero (x : Fin R → ℝ) : mono (fun _ ↦ false) x = 1 := by
  simp [mono]

theorem sum_mul_indC (c : Cube (Fin R) → ℝ) (s₀ : Cube (Fin R)) :
    ∑ s, c s * indC s₀ s = c s₀ := by
  simp [indC]

theorem mono_mul_arg (t : ℝ) (s : Cube (Fin R)) (x : Fin R → ℝ) :
    mono s (fun i ↦ t * x i) = t ^ sdeg s * mono s x := by
  unfold mono
  rw [pow_degree, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases s i <;> simp

theorem mlEval_mul_arg (t : ℝ) (c : Cube (Fin R) → ℝ) (x : Fin R → ℝ) :
    mlEval c (fun i ↦ t * x i) = mlEval (smoothC t c) x := by
  simp_rw [mlEval_eq_sum, mono_mul_arg, smoothC]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  ring

theorem continuous_mono (s : Cube (Fin R)) : Continuous (mono s) := by
  unfold mono
  refine continuous_finsetProd _ fun i _ ↦ ?_
  cases s i
  · exact continuous_const
  · exact continuous_apply i

theorem continuous_mlEval' (c : Cube (Fin R) → ℝ) : Continuous (mlEval c) := by
  rw [show mlEval c = fun x ↦ ∑ s, c s * mono s x from rfl]
  exact continuous_finsetSum _ fun s _ ↦ continuous_const.mul (continuous_mono s)

/-! ### Product measures -/

variable (ν : Fin R → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]

theorem integrable_id_of_sq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : Integrable (fun y ↦ y ^ 2) μ) : Integrable (fun y ↦ y) μ :=
  ((memLp_two_iff_integrable_sq aestronglyMeasurable_id).2 h).integrable one_le_two

theorem mono_mul_mono_eq (s t : Cube (Fin R)) (x : Fin R → ℝ) :
    mono s x * mono t x =
      ∏ i, (if s i then x i else 1) * (if t i then x i else 1) := by
  unfold mono
  rw [Finset.prod_mul_distrib]

theorem integrable_mono_mul_mono (h2 : ∀ i, Integrable (fun y ↦ y ^ 2) (ν i))
    (s t : Cube (Fin R)) :
    Integrable (fun x ↦ mono s x * mono t x) (Measure.pi ν) := by
  simp_rw [mono_mul_mono_eq]
  refine Integrable.fintype_prod
    (f := fun i y ↦ (if s i then y else 1) * (if t i then y else 1)) fun i ↦ ?_
  have h1 := integrable_id_of_sq (h2 i)
  cases s i <;> cases t i
  · simp
  · simpa using h1
  · simpa using h1
  · simpa [← sq] using h2 i

theorem integral_mono_mul_mono
    (m1 : ∀ i, ∫ y, y ∂ν i = 0) (m2 : ∀ i, ∫ y, y ^ 2 ∂ν i = 1) (s t : Cube (Fin R)) :
    ∫ x, mono s x * mono t x ∂Measure.pi ν = if s = t then 1 else 0 := by
  simp_rw [mono_mul_mono_eq]
  rw [integral_fintype_prod_eq_prod
    (f := fun i y ↦ (if s i then y else 1) * (if t i then y else 1))]
  have key : ∀ i, ∫ y, (if s i then y else 1) * (if t i then y else 1) ∂ν i =
      if s i = t i then 1 else 0 := by
    intro i
    cases s i <;> cases t i
    · simp
    · simpa using m1 i
    · simpa using m1 i
    · simpa [← sq] using m2 i
  simp_rw [key]
  rw [Finset.prod_boole]
  simp [funext_iff]

theorem integral_mlEval_mul_pi' (h2 : ∀ i, Integrable (fun y ↦ y ^ 2) (ν i))
    (m1 : ∀ i, ∫ y, y ∂ν i = 0) (m2 : ∀ i, ∫ y, y ^ 2 ∂ν i = 1) (c d : Cube (Fin R) → ℝ) :
    ∫ x, mlEval c x * mlEval d x ∂Measure.pi ν = ∑ s, c s * d s := by
  have hexp : ∀ x, mlEval c x * mlEval d x =
      ∑ s, ∑ t, c s * d t * (mono s x * mono t x) := by
    intro x
    rw [mlEval_eq_sum, mlEval_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun t _ ↦ ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun s _ ↦ integrable_finsetSum _ fun t _ ↦
    (integrable_mono_mul_mono ν h2 s t).const_mul _]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [integral_finsetSum _ fun t _ ↦ (integrable_mono_mul_mono ν h2 s t).const_mul _]
  simp_rw [integral_const_mul, integral_mono_mul_mono ν m1 m2]
  simp

theorem integrable_mono_affine (h1 : ∀ i, Integrable (fun y ↦ y) (ν i)) (a b : Fin R → ℝ)
    (s : Cube (Fin R)) :
    Integrable (fun z ↦ mono s (fun i ↦ a i + b i * z i)) (Measure.pi ν) := by
  unfold mono
  refine Integrable.fintype_prod (f := fun i y ↦ if s i then a i + b i * y else 1) fun i ↦ ?_
  cases s i
  · simp
  · simpa using (integrable_const (a i)).add ((h1 i).const_mul (b i))

theorem integral_mono_affine (h1 : ∀ i, Integrable (fun y ↦ y) (ν i))
    (m1 : ∀ i, ∫ y, y ∂ν i = 0) (a b : Fin R → ℝ) (s : Cube (Fin R)) :
    ∫ z, mono s (fun i ↦ a i + b i * z i) ∂Measure.pi ν = mono s a := by
  unfold mono
  rw [integral_fintype_prod_eq_prod (f := fun i y ↦ if s i then a i + b i * y else 1)]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases s i
  · simp
  · simp only [ite_true]
    rw [integral_add (integrable_const _) ((h1 i).const_mul _), integral_const_mul, m1 i]
    simp

/-- Averaging out independent centered noise does not change a multilinear polynomial. -/
theorem integral_mlEval_affine (h1 : ∀ i, Integrable (fun y ↦ y) (ν i))
    (m1 : ∀ i, ∫ y, y ∂ν i = 0) (a b : Fin R → ℝ) (c : Cube (Fin R) → ℝ) :
    ∫ z, mlEval c (fun i ↦ a i + b i * z i) ∂Measure.pi ν = mlEval c a := by
  simp_rw [mlEval_eq_sum]
  rw [integral_finsetSum _ fun s _ ↦ (integrable_mono_affine ν h1 a b s).const_mul _]
  simp_rw [integral_const_mul, integral_mono_affine ν h1 m1]

theorem memLp_mono_pi {p : ENNReal} (hp0 : p ≠ 0) (hp : p ≠ ⊤) (h : ∀ i, MemLp (fun y ↦ y) p (ν i))
    (s : Cube (Fin R)) : MemLp (mono s) p (Measure.pi ν) := by
  rw [← integrable_norm_rpow_iff (continuous_mono s).aestronglyMeasurable hp0 hp]
  have he : (fun x ↦ ‖mono s x‖ ^ p.toReal) =
      fun x ↦ ∏ i, ‖(if s i then x i else 1)‖ ^ p.toReal := by
    funext x
    unfold mono
    rw [norm_prod, Real.finsetProd_rpow _ _ fun i _ ↦ norm_nonneg _]
  rw [he]
  refine Integrable.fintype_prod (f := fun i y ↦ ‖(if s i then y else 1)‖ ^ p.toReal) fun i ↦ ?_
  cases s i
  · simp
  · simpa using (integrable_norm_rpow_iff aestronglyMeasurable_id hp0 hp).2 (h i)

theorem memLp_mlEval_pi' {p : ENNReal} (hp : p ≠ ⊤) (h : ∀ i, MemLp (fun y ↦ y) p (ν i))
    (c : Cube (Fin R) → ℝ) : MemLp (mlEval c) p (Measure.pi ν) := by
  by_cases hp0 : p = 0
  · subst hp0
    exact memLp_zero_iff_aestronglyMeasurable.2 (continuous_mlEval' c).aestronglyMeasurable
  rw [show mlEval c = fun x ↦ ∑ s, c s * mono s x from rfl]
  exact memLp_finsetSum _ fun s _ ↦ (memLp_mono_pi ν hp0 hp h s).const_mul _

/-! ### The standard Gaussian -/

theorem gaussianReal_integrable_sq : Integrable (fun y : ℝ ↦ y ^ 2) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal' 2 (by simp)).integrable_sq

theorem gaussianReal_integrable_id : Integrable (fun y : ℝ ↦ y) (gaussianReal 0 1) :=
  integrable_id_of_sq gaussianReal_integrable_sq

theorem gaussianReal_m1 : ∫ y, y ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal

theorem gaussianReal_m2 : ∫ y, y ^ 2 ∂gaussianReal 0 1 = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (X := fun x : ℝ ↦ x) measurable_id'.aemeasurable] at h
  simpa using h

/-- Integrals against `γ` as integrals against the product of the coordinate laws. -/
theorem integral_gm (F : Gs R → ℝ) :
    ∫ G, F G ∂gm R = ∫ x, F (WithLp.toLp 2 x) ∂Measure.pi (fun _ ↦ gaussianReal 0 1) := by
  rw [gm, ← map_pi_eq_stdGaussian, ← MeasurableEquiv.coe_toLp, integral_map_equiv]

end MultilinearGauss

open MultilinearGauss

theorem memLp_mlEval (c : Cube (Fin R) → ℝ) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (fun G : Gs R ↦ mlEval c G) p (gm R) := by
  have hmeas : AEStronglyMeasurable (fun G : Gs R ↦ mlEval c G)
      ((Measure.pi (fun _ ↦ gaussianReal 0 1)).map (WithLp.toLp 2)) :=
    ((continuous_mlEval' c).comp (PiLp.continuous_ofLp _ _)).aestronglyMeasurable
  rw [gm, ← map_pi_eq_stdGaussian, memLp_map_measure_iff hmeas (by fun_prop)]
  exact memLp_mlEval_pi' _ hp (fun _ ↦ memLp_id_gaussianReal' p hp) c

theorem continuous_mlEval (c : Cube (Fin R) → ℝ) : Continuous (fun G : Gs R ↦ mlEval c G) :=
  (continuous_mlEval' c).comp (PiLp.continuous_ofLp _ _)

/-- Orthonormality of the multilinear monomials under `γ`. -/
theorem integral_mlEval_mul (c d : Cube (Fin R) → ℝ) :
    ∫ G, mlEval c G * mlEval d G ∂gm R = ∑ s, c s * d s := by
  rw [integral_gm]
  exact integral_mlEval_mul_pi' _ (fun _ ↦ gaussianReal_integrable_sq) (fun _ ↦ gaussianReal_m1)
    (fun _ ↦ gaussianReal_m2) c d

theorem integral_mlEval_sq (c : Cube (Fin R) → ℝ) :
    ∫ G, mlEval c G ^ 2 ∂gm R = ∑ s, c s ^ 2 := by
  simp_rw [sq]
  exact integral_mlEval_mul c c

theorem gMean_mlEval (c : Cube (Fin R) → ℝ) :
    gMean (fun G : Gs R ↦ mlEval c G) = c (fun _ ↦ false) := by
  have h := integral_mlEval_mul c (indC (fun _ ↦ false))
  simp_rw [mlEval_indC, mono_zero, mul_one, sum_mul_indC] at h
  exact h

theorem integral_mlEval_mul_coord (c : Cube (Fin R) → ℝ) (i : Fin R) :
    ∫ G, mlEval c G * G i ∂gm R = c (fun j ↦ decide (j = i)) := by
  have h := integral_mlEval_mul c (indC (Multilinear.single i))
  simp_rw [mlEval_indC, mono_single, sum_mul_indC] at h
  exact h

/-- `Stab_t(p) = ∑_S t^|S| c_S²` on Gaussian space. -/
theorem gStab_mlEval {t : ℝ} (_ht : t ∈ Icc (-1 : ℝ) 1) (c : Cube (Fin R) → ℝ) :
    gStab t (fun G : Gs R ↦ mlEval c G) = ∑ s, t ^ sdeg s * c s ^ 2 := by
  unfold gStab
  beta_reduce
  have hin : ∀ x : Gs R,
      ∫ z, mlEval c x * mlEval c (WithLp.ofLp (t • x + √(1 - t ^ 2) • z)) ∂gm R =
      mlEval c x * mlEval (smoothC t c) x := by
    intro x
    rw [integral_const_mul, integral_gm]
    congr 1
    have : ∀ z : Fin R → ℝ, mlEval c (WithLp.ofLp (t • x + √(1 - t ^ 2) • WithLp.toLp 2 z)) =
        mlEval c (fun i ↦ t * x i + √(1 - t ^ 2) * z i) := fun z ↦ rfl
    simp_rw [this]
    rw [integral_mlEval_affine _ (fun _ ↦ gaussianReal_integrable_id) (fun _ ↦ gaussianReal_m1)
      (fun i ↦ t * x i) (fun _ ↦ √(1 - t ^ 2)) c]
    exact mlEval_mul_arg t c x
  rw [integral_congr_ae (ae_of_all _ hin), integral_mlEval_mul]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smoothC]
  ring

/-- The Gaussian stability of `P_{u,r}` is the Boolean stability `Stab_{t r²}(u)`. -/
theorem gStab_gaussExt {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (r : ℝ) (u : Cube (Fin R) → ℝ) :
    gStab t (gaussExt r u) = stability (t * r ^ 2) u := by
  unfold gaussExt
  rw [gStab_mlEval ht, stability]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smoothC]
  ring

theorem gMean_gaussExt (r : ℝ) (u : Cube (Fin R) → ℝ) : gMean (gaussExt r u) = 𝔼 x, u x := by
  unfold gaussExt
  rw [gMean_mlEval]
  unfold smoothC coefficient
  simp only [degree_zero, pow_zero, one_mul, walsh_zero, mul_one]

theorem integral_gaussExt_sq_le {r : ℝ} (hr : |r| ≤ 1) (u : Cube (Fin R) → ℝ)
    (h01 : ∀ x, 0 ≤ u x ∧ u x ≤ 1) : ∫ G, gaussExt r u G ^ 2 ∂gm R ≤ 1 := by
  unfold gaussExt
  rw [integral_mlEval_sq]
  calc ∑ s, smoothC r (coefficient u) s ^ 2 ≤ ∑ s, coefficient u s ^ 2 := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        simp only [smoothC]
        rw [mul_pow, ← pow_mul, mul_comm (sdeg s) 2, pow_mul]
        have h1 : (r ^ 2) ^ sdeg s ≤ 1 :=
          pow_le_one₀ (sq_nonneg r) (by nlinarith [abs_le.mp hr, sq_abs r])
        nlinarith [sq_nonneg (coefficient u s)]
    _ = 𝔼 x, u x ^ 2 := walsh_parseval u
    _ ≤ 1 := by
        apply Finset.expect_le Finset.univ_nonempty
        intro x _
        obtain ⟨h0, h1⟩ := h01 x
        nlinarith

theorem integral_gaussExt_mul_coord (r : ℝ) (u : Cube (Fin R) → ℝ) (i : Fin R) :
    ∫ G, gaussExt r u G * G i ∂gm R = r * coefficient u (fun j ↦ decide (j = i)) := by
  unfold gaussExt
  rw [integral_mlEval_mul_coord]
  simp only [smoothC]
  rw [show (fun j ↦ decide (j = i)) = Multilinear.single i from rfl, Multilinear.sdeg_single,
    pow_one]

end BGHKLMM26.RobustMIS
