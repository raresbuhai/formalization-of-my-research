module

public import BGHKLMM26.RobustMIS.SharpDefs
public import BGHKLMM26.RobustMIS.GaussL2
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Pi.Parseval

/-!
# The sharp Gaussian lemma: the spectral gap of the noise operator

The Hermite polynomials diagonalize the noise operator: `T_t` multiplies the Hermite polynomials of
degree `k` by `t^k`. So for bounded `g`, with `c₀ = E g` and `c₁ = F̂⁽¹⁾(g) = E[g(x) x]`,
`⟨g, T_t g⟩ = ∑_a t^{|a|} ĝ(a)²` lies between `c₀² + t |c₁|²` and
`c₀² + t |c₁|² + t² (E g² - c₀² - |c₁|²)` for `0 ≤ t ≤ 1`: the levels above one are damped by at
least `t²`.

The proof (helpers in the namespace `SharpH`):

* **One dimension**: Stein's identity `E[G q(G)] = E[q'(G)]` for polynomials `q`
  (`SharpH.stein_poly`, integration by parts against the density), and by induction with
  `H_{k+2} = X H_{k+1} - (k + 1) H_k` and `H_{k+1}' = (k + 1) H_k` the eigenrelation
  `E Hₖ(t y + s G) = tᵏ Hₖ(y)` for `t² + s² = 1` (`SharpH.integral_hermR_affine`).
* **The Hermite basis of `L²(γₙ)`**: TauCeti's `TauCeti.gaussianHermitePiBasis`, the Hilbert basis
  `Ψ_a(x) = ∏ᵢ H_{aᵢ}(xᵢ)/√(aᵢ!)` of `L²` of the product of standard Gaussians, transported to
  `gm n` by `map_pi_eq_stdGaussian`. This gives Parseval's identity
  `E[F H] = ∑_a ⟨Ψ_a, F⟩ ⟨Ψ_a, H⟩` (`SharpH.hasSum_parseval`) and, by Fubini over the coordinates,
  `T_t Ψ_a = t^{|a|} Ψ_a` (`SharpH.integral_hermPi_rot`).
* **Self-adjointness** `⟨F, T_t H⟩ = ⟨H, T_t F⟩` for `F, H ∈ L²(γₙ)` (`SharpH.integral_rot_swap`),
  from the invariance of `γₙ ⊗ γₙ` under `(x, z) ↦ (t x + s z, s x - t z)`
  (`SharpH.map_rot_prod`). Hence `⟨Ψ_a, T_t g⟩ = t^{|a|} ⟨Ψ_a, g⟩` (`SharpH.coef_noiseOp`) and
  `⟨g, T_t g⟩ = ∑_a t^{|a|} ĝ(a)²` (`SharpH.hasSum_nBil`).
* **The degrees zero and one**: `Ψ_0 = 1` and `Ψ_{eⱼ}(x) = xⱼ`, so `ĝ(0) = E g` and
  `∑ⱼ ĝ(eⱼ)² = |F̂⁽¹⁾(g)|²`; every other multi-index has `|a| ≥ 2` (`SharpH.two_le_of_notMem`),
  where `t^{|a|} ≤ t²`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

namespace SharpH

open Polynomial TauCeti

theorem integrable_eval (q : ℝ[X]) : Integrable (fun x ↦ q.eval x) (gaussianReal 0 1) :=
  (memLp_two_eval_gaussianReal 0 1 q).integrable one_le_two

theorem integrable_pdf_eval (q : ℝ[X]) :
    Integrable (fun x ↦ gaussianPDFReal 0 1 x • q.eval x) :=
  (TauCeti.Probability.integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul
    one_ne_zero).1 (integrable_eval q)

/-- **Stein's identity** for polynomials: `E[G q(G)] = E[q'(G)]`. -/
theorem stein_poly (q : ℝ[X]) :
    ∫ w, w * q.eval w ∂gaussianReal 0 1 = ∫ w, (derivative q).eval w ∂gaussianReal 0 1 := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  have hd : ∀ x, HasDerivAt (fun x ↦ gaussianPDFReal 0 1 x * q.eval x)
      (gaussianPDFReal 0 1 x • (derivative q).eval x -
        gaussianPDFReal 0 1 x • (X * q).eval x) x := by
    intro x
    convert (Probability.hasDerivAt_gaussianPDFReal 0 1 x).mul (q.hasDerivAt x) using 1
    simp only [smul_eq_mul, eval_mul, eval_X, NNReal.coe_one, sub_zero, div_one]
    ring
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hd
    ((integrable_pdf_eval _).sub (integrable_pdf_eval _))
    (by simpa only [smul_eq_mul] using integrable_pdf_eval q)
  rw [integral_sub (integrable_pdf_eval _) (integrable_pdf_eval _), sub_eq_zero] at h0
  simpa only [eval_mul, eval_X] using h0.symm

theorem integrable_eval_affine (P : ℝ[X]) (a s : ℝ) :
    Integrable (fun w ↦ P.eval (a + s * w)) (gaussianReal 0 1) :=
  (integrable_eval (P.comp (C a + C s * X))).congr (ae_of_all _ fun w ↦ by simp [eval_comp])

theorem integrable_mul_eval_affine (P : ℝ[X]) (a s : ℝ) :
    Integrable (fun w ↦ w * P.eval (a + s * w)) (gaussianReal 0 1) :=
  (integrable_eval (X * P.comp (C a + C s * X))).congr (ae_of_all _ fun w ↦ by simp [eval_comp])

/-- Stein's identity along an affine map: `E[G P(a + s G)] = s E[P'(a + s G)]`. -/
theorem stein_affine (P : ℝ[X]) (a s : ℝ) :
    ∫ w, w * P.eval (a + s * w) ∂gaussianReal 0 1 =
      s * ∫ w, (derivative P).eval (a + s * w) ∂gaussianReal 0 1 := by
  have h := stein_poly (P.comp (C a + C s * X))
  simp only [eval_comp, derivative_comp, eval_mul, eval_add, eval_C, eval_X, derivative_add,
    derivative_C, derivative_mul, derivative_X, zero_add, mul_one, zero_mul] at h
  rw [h, integral_const_mul]

/-- The probabilists' Hermite polynomial `Hₖ` as a real polynomial. -/
noncomputable def hermR (k : ℕ) : ℝ[X] := (hermite k).map (Int.castRingHom ℝ)

theorem eval_hermR (k : ℕ) (x : ℝ) : (hermR k).eval x = aeval x (hermite k) := by
  rw [hermR, ← algebraMap_int_eq, eval_map_algebraMap]

theorem eval_hermR_add_two (k : ℕ) (u : ℝ) :
    (hermR (k + 2)).eval u = u * (hermR (k + 1)).eval u - (k + 1) * (hermR k).eval u := by
  simp only [eval_hermR, hermite_add_two, map_sub, map_mul, aeval_X, nsmul_eq_mul,
    map_natCast]
  push_cast
  ring

theorem eval_derivative_hermR_succ (k : ℕ) (u : ℝ) :
    (derivative (hermR (k + 1))).eval u = (k + 1) * (hermR k).eval u := by
  rw [hermR, derivative_map, derivative_hermite_succ, eval_map, ← algebraMap_int_eq,
    ← aeval_def, eval_hermR]
  simp only [nsmul_eq_mul, map_mul, map_natCast]
  push_cast
  ring

/-- **The one-dimensional eigenrelation**: `E Hₖ(t y + s G) = tᵏ Hₖ(y)` for `t² + s² = 1`. -/
theorem integral_hermR_affine {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) (y : ℝ) (k : ℕ) :
    ∫ w, (hermR k).eval (t * y + s * w) ∂gaussianReal 0 1 = t ^ k * (hermR k).eval y := by
  suffices h : ∀ k : ℕ,
      (∫ w, (hermR k).eval (t * y + s * w) ∂gaussianReal 0 1 =
        t ^ k * (hermR k).eval y) ∧
      (∫ w, (hermR (k + 1)).eval (t * y + s * w) ∂gaussianReal 0 1 =
        t ^ (k + 1) * (hermR (k + 1)).eval y) from (h k).1
  intro k
  induction k with
  | zero =>
    refine ⟨by simp [hermR], ?_⟩
    simp only [hermR, hermite_one, Polynomial.map_X, eval_X, zero_add, pow_one]
    rw [integral_add (integrable_const _) (IsGaussian.integrable_fun_id.const_mul s),
      integral_const_mul s, integral_id_gaussianReal]
    simp
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hrec := eval_hermR_add_two k
    have hst := stein_affine (hermR (k + 1)) (t * y) s
    simp only [eval_derivative_hermR_succ] at hst
    rw [integral_const_mul, ih.1] at hst
    simp_rw [hrec]
    have e : ∀ w, (t * y + s * w) * (hermR (k + 1)).eval (t * y + s * w) -
        (k + 1) * (hermR k).eval (t * y + s * w) =
        (t * y) * (hermR (k + 1)).eval (t * y + s * w) +
          s * (w * (hermR (k + 1)).eval (t * y + s * w)) -
            (k + 1) * (hermR k).eval (t * y + s * w) := fun w ↦ by ring
    simp_rw [e]
    have i1 := (integrable_eval_affine (hermR (k + 1)) (t * y) s).const_mul (t * y)
    have i2 := (integrable_mul_eval_affine (hermR (k + 1)) (t * y) s).const_mul s
    have i3 := (integrable_eval_affine (hermR k) (t * y) s).const_mul (k + 1 : ℝ)
    have i12 : Integrable (fun w : ℝ ↦ t * y * eval (t * y + s * w) (hermR (k + 1)) +
        s * (w * eval (t * y + s * w) (hermR (k + 1)))) (gaussianReal 0 1) := i1.add i2
    rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, ih.2, hst, ih.1]
    linear_combination ((k + 1 : ℝ) * t ^ k * (hermR k).eval y) * hts

/-! ### Multivariate Hermite polynomials on `Gs n` -/

/-- The normalized Hermite polynomial `hₖ(u) = Hₖ(u)/√(k!)`. -/
noncomputable def herm (k : ℕ) (u : ℝ) : ℝ := aeval u (hermite k) / √(k.factorial : ℝ)

/-- The multivariate Hermite polynomial `Ψ_a(y) = ∏ᵢ h_{aᵢ}(yᵢ)`. -/
noncomputable def hermPi (a : Fin n → ℕ) (y : Gs n) : ℝ := ∏ i, herm (a i) (y i)

theorem integral_herm_affine {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) (k : ℕ) (y : ℝ) :
    ∫ w, herm k (t * y + s * w) ∂gaussianReal 0 1 = t ^ k * herm k y := by
  simp only [herm, ← eval_hermR]
  rw [integral_div, integral_hermR_affine hts, mul_div_assoc]

theorem continuous_hermPi (a : Fin n → ℕ) : Continuous (hermPi a) := by
  unfold hermPi herm
  fun_prop

theorem map_pi_gm :
    (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map (WithLp.toLp 2) = gm n :=
  map_pi_eq_stdGaussian

theorem measurable_toLp : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → Gs n) :=
  (PiLp.continuous_toLp 2 _).measurable

theorem integral_gm {Φ : Gs n → ℝ} (hΦ : AEStronglyMeasurable Φ (gm n)) :
    ∫ y, Φ y ∂gm n = ∫ x, Φ (WithLp.toLp 2 x) ∂Measure.pi fun _ : Fin n ↦ gaussianReal 0 1 := by
  rw [← map_pi_gm] at hΦ ⊢
  rw [integral_map measurable_toLp.aemeasurable hΦ]

theorem memLp_pi {F : Gs n → ℝ} (hF : MemLp F 2 (gm n)) :
    MemLp (fun x ↦ F (WithLp.toLp 2 x)) 2 (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) := by
  rw [← map_pi_gm] at hF
  exact (memLp_map_measure_iff hF.aestronglyMeasurable measurable_toLp.aemeasurable).1 hF

theorem memLp_hermPi (a : Fin n → ℕ) : MemLp (hermPi a) 2 (gm n) := by
  have h := (Lp.memLp (gaussianHermitePiBasis ℝ (Fin n) a)).ae_eq
    (coeFn_gaussianHermitePiBasis ℝ (Fin n) a)
  rw [← map_pi_gm, memLp_map_measure_iff (continuous_hermPi a).aestronglyMeasurable
    measurable_toLp.aemeasurable]
  convert h using 1
  funext x
  simp [hermPi, herm]

/-- The coordinates of an `L²(γₙ)` function in the Hermite basis are its integrals against `Ψ_a`. -/
theorem inner_basis_toLp {K : Gs n → ℝ} (hK : MemLp K 2 (gm n)) (a : Fin n → ℕ) :
    inner ℝ (gaussianHermitePiBasis ℝ (Fin n) a) (memLp_pi hK).toLp =
      ∫ y, hermPi a y * K y ∂gm n := by
  rw [← HilbertBasis.repr_apply_apply, gaussianHermitePiBasis_repr_apply,
    integral_gm (Φ := fun y ↦ hermPi a y * K y)
      (((continuous_hermPi a).aestronglyMeasurable).mul hK.aestronglyMeasurable)]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_pi hK).coeFn_toLp] with x hx
  rw [hx]
  simp [hermPi, herm]

/-- **Parseval's identity** in the Hermite basis of `L²(γₙ)`, in polarized form. -/
theorem hasSum_parseval {F H : Gs n → ℝ} (hF : MemLp F 2 (gm n)) (hH : MemLp H 2 (gm n)) :
    HasSum (fun a ↦ (∫ y, hermPi a y * F y ∂gm n) * ∫ y, hermPi a y * H y ∂gm n)
      (∫ y, F y * H y ∂gm n) := by
  have key := (gaussianHermitePiBasis ℝ (Fin n)).hasSum_inner_mul_inner (memLp_pi hF).toLp
    (memLp_pi hH).toLp
  convert key using 1
  · funext a
    rw [real_inner_comm, inner_basis_toLp hF, inner_basis_toLp hH]
  · rw [MeasureTheory.L2.inner_def, integral_gm (Φ := fun y ↦ F y * H y)
      (hF.aestronglyMeasurable.mul hH.aestronglyMeasurable)]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_pi hF).coeFn_toLp, (memLp_pi hH).coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2]
    simp [mul_comm]

/-- **The eigenrelation** `T_t Ψ_a = t^{|a|} Ψ_a` for `t² + s² = 1`. -/
theorem integral_hermPi_rot {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) (a : Fin n → ℕ) (y : Gs n) :
    ∫ z, hermPi a (t • y + s • z) ∂gm n = t ^ (∑ i, a i) * hermPi a y := by
  rw [integral_gm (Φ := fun z ↦ hermPi a (t • y + s • z))
    ((continuous_hermPi a).comp (by fun_prop)).aestronglyMeasurable]
  have e : ∀ x : Fin n → ℝ, hermPi a (t • y + s • WithLp.toLp 2 x) =
      ∏ i, herm (a i) (t * y i + s * x i) := fun x ↦ rfl
  simp_rw [e]
  rw [integral_fintype_prod_eq_prod (fun i u ↦ herm (a i) (t * y i + s * u))]
  simp_rw [integral_herm_affine hts]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

theorem herm_zero (u : ℝ) : herm 0 u = 1 := by simp [herm]

theorem herm_one (u : ℝ) : herm 1 u = u := by simp [herm]

theorem hermPi_zero (y : Gs n) : hermPi 0 y = 1 := by simp [hermPi, herm_zero]

theorem hermPi_single (j : Fin n) (y : Gs n) : hermPi (Pi.single j 1) y = y j := by
  unfold hermPi
  rw [Finset.prod_eq_single j (fun i _ hij ↦ by rw [Pi.single_eq_of_ne hij, herm_zero])
    (fun h ↦ absurd (Finset.mem_univ j) h), Pi.single_eq_same, herm_one]

/-! ### Self-adjointness of the noise operator -/

theorem rot_fst {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) (x z : Gs n) :
    t • (t • x + s • z) + s • (s • x - t • z) = x := by
  linear_combination (norm := module) hts • x

/-- `(X, Z) ↦ (t X + s Z, s X - t Z)` preserves `γ ⊗ γ` for `t² + s² = 1`. -/
theorem map_rot_prod {t s : ℝ} (hts : t ^ 2 + s ^ 2 = 1) :
    ((gm n).prod (gm n)).map (fun p ↦ (t • p.1 + s • p.2, s • p.1 - t • p.2)) =
      (gm n).prod (gm n) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ (Gs n) (Gs n)).symm.toContinuousLinearMap
  let A : Gs n →L[ℝ] (WithLp 2 (Gs n × Gs n)) := e ∘L ((t • ContinuousLinearMap.id ℝ (Gs n)).prod
    (s • ContinuousLinearMap.id ℝ (Gs n)))
  let B : Gs n →L[ℝ] (WithLp 2 (Gs n × Gs n)) := e ∘L ((s • ContinuousLinearMap.id ℝ (Gs n)).prod
    ((-t) • ContinuousLinearMap.id ℝ (Gs n)))
  let A' : WithLp 2 (Gs n × Gs n) → Gs n := fun τ ↦ t • (WithLp.ofLp τ).1 + s • (WithLp.ofLp τ).2
  let B' : WithLp 2 (Gs n × Gs n) → Gs n := fun τ ↦ s • (WithLp.ofLp τ).1 - t • (WithLp.ofLp τ).2
  have hA : ∀ x τ, ⟪A x, τ⟫ = ⟪x, A' τ⟫ := by
    intro x τ
    simp only [A, A', e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.prod_inner_apply]
    simp [inner_add_right, real_inner_smul_left, real_inner_smul_right]
  have hB : ∀ x τ, ⟪B x, τ⟫ = ⟪x, B' τ⟫ := by
    intro x τ
    simp only [B, B', e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
      WithLp.prod_inner_apply]
    simp [inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hnorm : ∀ τ, ‖A' τ‖ ^ 2 + ‖B' τ‖ ^ 2 = ‖τ‖ ^ 2 := by
    intro τ
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp only [A', B']
    rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, norm_smul, norm_smul,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, mul_pow, mul_pow, sq_abs, sq_abs]
    simp only [WithLp.fst, WithLp.snd]
    linear_combination (‖(WithLp.ofLp τ).1‖ ^ 2 + ‖(WithLp.ofLp τ).2‖ ^ 2) * hts
  have hmap := Gaussian.map_prod_stdGaussian A B A' B' hA hB hnorm
  have hAB : (fun p : Gs n × Gs n ↦ A p.1 + B p.2) =
      fun p ↦ WithLp.toLp 2 (t • p.1 + s • p.2, s • p.1 - t • p.2) := by
    funext p
    simp only [A, B, e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply]
    rw [← WithLp.toLp_add, Prod.mk_add_mk]
    simp [sub_eq_add_neg]
  rw [hAB, ← Gaussian.stdGaussian_prod] at hmap
  have hto : Measurable (WithLp.toLp 2 : Gs n × Gs n → WithLp 2 (Gs n × Gs n)) :=
    (WithLp.prod_continuous_toLp 2 _ _).measurable
  have hof : Measurable (WithLp.ofLp : WithLp 2 (Gs n × Gs n) → Gs n × Gs n) :=
    (WithLp.prod_continuous_ofLp 2 _ _).measurable
  have hR : Measurable (fun p : Gs n × Gs n ↦ (t • p.1 + s • p.2, s • p.1 - t • p.2)) := by
    fun_prop
  have h := congrArg (Measure.map WithLp.ofLp) hmap
  rw [Measure.map_map (f := fun p : Gs n × Gs n ↦
      WithLp.toLp 2 (t • p.1 + s • p.2, s • p.1 - t • p.2)) hof (hto.comp hR),
    Measure.map_map hof hto] at h
  simp only [Function.comp_def, Measure.map_id'] at h
  exact h

/-- **Self-adjointness of the noise operator**: `⟨F, T_t H⟩ = ⟨H, T_t F⟩` for `F, H ∈ L²(γₙ)`. -/
theorem integral_rot_swap {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {F H : Gs n → ℝ}
    (hF : MemLp F 2 (gm n)) (hH : MemLp H 2 (gm n)) :
    ∫ x, ∫ z, F x * H (t • x + √(1 - t ^ 2) • z) ∂gm n ∂gm n =
      ∫ x, ∫ z, H x * F (t • x + √(1 - t ^ 2) • z) ∂gm n ∂gm n := by
  have hts : t ^ 2 + √(1 - t ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by nlinarith [ht.1, ht.2])]
    ring
  have hR := map_rot_prod (n := n) hts
  have i1 : Integrable (fun p : Gs n × Gs n ↦ F p.1 * H (t • p.1 + √(1 - t ^ 2) • p.2))
      ((gm n).prod (gm n)) :=
    (GaussL2.memLp_comp_of_map measurable_fst GaussL2.map_fst_gm hF).integrable_mul
      (GaussL2.memLp_comp_of_map (GaussL2.measurable_rot t) (GaussL2.map_rot_gm ht) hH)
  have i2 : Integrable (fun p : Gs n × Gs n ↦ H p.1 * F (t • p.1 + √(1 - t ^ 2) • p.2))
      ((gm n).prod (gm n)) :=
    (GaussL2.memLp_comp_of_map measurable_fst GaussL2.map_fst_gm hH).integrable_mul
      (GaussL2.memLp_comp_of_map (GaussL2.measurable_rot t) (GaussL2.map_rot_gm ht) hF)
  rw [← integral_prod _ i1, ← integral_prod _ i2]
  have hRm : Measurable (fun p : Gs n × Gs n ↦
      (t • p.1 + √(1 - t ^ 2) • p.2, √(1 - t ^ 2) • p.1 - t • p.2)) := by
    fun_prop
  conv_lhs => rw [← hR]
  rw [integral_map hRm.aemeasurable (by rw [hR]; exact i1.aestronglyMeasurable)]
  congr 1
  funext p
  rw [rot_fst hts, mul_comm]

/-! ### The noise operator in the Hermite basis -/

/-- The noise operator `T_t g(x) = E g(t x + √(1 - t²) Z)`. -/
noncomputable def noiseOp (t : ℝ) (g : Gs n → ℝ) (x : Gs n) : ℝ :=
  ∫ z, g (t • x + √(1 - t ^ 2) • z) ∂gm n

theorem measurable_noiseOp (t : ℝ) {g : Gs n → ℝ} (hg : Measurable g) :
    Measurable (noiseOp t g) :=
  ((hg.comp (GaussL2.measurable_rot t)).stronglyMeasurable.integral_prod_right').measurable

theorem abs_noiseOp_le (t : ℝ) {g : Gs n → ℝ} {C : ℝ} (hgC : ∀ x, |g x| ≤ C) (x : Gs n) :
    |noiseOp t g x| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := gm n)
    (f := fun z ↦ g (t • x + √(1 - t ^ 2) • z)) (C := C) (ae_of_all _ fun z ↦ by
      simpa only [Real.norm_eq_abs] using hgC _)
  simpa [noiseOp] using h

theorem nBil_eq (t : ℝ) (g : Gs n → ℝ) : nBil t g g = ∫ x, g x * noiseOp t g x ∂gm n := by
  unfold nBil noiseOp
  congr 1
  funext x
  rw [integral_const_mul]

/-- `⟨Ψ_a, T_t g⟩ = t^{|a|} ⟨Ψ_a, g⟩`. -/
theorem coef_noiseOp {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {g : Gs n → ℝ} (hg : MemLp g 2 (gm n))
    (a : Fin n → ℕ) :
    ∫ y, hermPi a y * noiseOp t g y ∂gm n = t ^ (∑ i, a i) * ∫ y, hermPi a y * g y ∂gm n := by
  have hts : t ^ 2 + √(1 - t ^ 2) ^ 2 = 1 := by
    rw [Real.sq_sqrt (by nlinarith [ht.1, ht.2])]
    ring
  calc ∫ y, hermPi a y * noiseOp t g y ∂gm n
      = ∫ y, ∫ z, hermPi a y * g (t • y + √(1 - t ^ 2) • z) ∂gm n ∂gm n := by
        congr 1
        funext y
        rw [noiseOp, integral_const_mul]
    _ = ∫ y, ∫ z, g y * hermPi a (t • y + √(1 - t ^ 2) • z) ∂gm n ∂gm n :=
        integral_rot_swap ht (memLp_hermPi a) hg
    _ = ∫ y, t ^ (∑ i, a i) * (hermPi a y * g y) ∂gm n := by
        congr 1
        funext y
        rw [integral_const_mul, integral_hermPi_rot hts]
        ring
    _ = _ := integral_const_mul _ _

/-! ### Splitting off the degrees zero and one -/

section Split

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The multi-indices of degree at most one: `0` and the unit vectors. -/
def lowIdx (ι : Type*) [Fintype ι] [DecidableEq ι] : Finset (ι → ℕ) :=
  insert 0 (Finset.univ.image fun j ↦ Pi.single j 1)

theorem sum_lowIdx (φ : (ι → ℕ) → ℝ) :
    ∑ a ∈ lowIdx ι, φ a = φ 0 + ∑ j, φ (Pi.single j 1) := by
  rw [lowIdx, Finset.sum_insert, Finset.sum_image]
  · intro i _ j _ hij
    by_contra h
    have := congrFun hij i
    simp [h] at this
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    have := congrFun hj j
    simp at this

theorem zero_mem_lowIdx : (0 : ι → ℕ) ∈ lowIdx ι := Finset.mem_insert_self _ _

theorem single_mem_lowIdx (j : ι) : (Pi.single j 1 : ι → ℕ) ∈ lowIdx ι :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ j))

theorem two_le_of_notMem {a : ι → ℕ} (ha : a ∉ lowIdx ι) : 2 ≤ ∑ i, a i := by
  by_contra h
  apply ha
  by_cases h0 : ∀ i, a i = 0
  · have : a = 0 := funext h0
    rw [this]
    exact zero_mem_lowIdx
  obtain ⟨j, hj⟩ := not_forall.mp h0
  have hle : ∀ i, a i ≤ ∑ i, a i := fun i ↦ Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ i)
  have haj : a j = 1 := by have := hle j; omega
  have hai : ∀ i, i ≠ j → a i = 0 := by
    intro i hij
    have h2 : a i + a j ≤ ∑ i, a i := by
      rw [← Finset.sum_pair hij]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    omega
  have : a = Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [haj]
    · simp [hij, hai i hij]
  rw [this]
  exact single_mem_lowIdx j

theorem sum_single (j : ι) : ∑ i, (Pi.single j 1 : ι → ℕ) i = 1 := by
  simp [Finset.sum_pi_single']

/-- The levels zero and one bound the sum from below. -/
theorem sq_add_le_of_hasSum {c : (ι → ℕ) → ℝ} {t B : ℝ} (ht0 : 0 ≤ t)
    (hB : HasSum (fun a ↦ c a * (t ^ (∑ i, a i) * c a)) B) :
    c 0 ^ 2 + t * ∑ j, c (Pi.single j 1) ^ 2 ≤ B := by
  have h := sum_le_hasSum (lowIdx ι) (fun a _ ↦ by
    rw [mul_left_comm]
    exact mul_nonneg (pow_nonneg ht0 _) (mul_self_nonneg _)) hB
  rw [sum_lowIdx] at h
  simp only [Pi.zero_apply, Finset.sum_const_zero, pow_zero, sum_single, pow_one] at h
  calc c 0 ^ 2 + t * ∑ j, c (Pi.single j 1) ^ 2
      = c 0 * (1 * c 0) + ∑ j, c (Pi.single j 1) * (t * c (Pi.single j 1)) := by
        rw [Finset.mul_sum]
        congr 1
        · ring
        · exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ ≤ B := h

/-- The levels above one are damped by at least `t²`. -/
theorem le_of_hasSum_sq {c : (ι → ℕ) → ℝ} {t A B : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hA : HasSum (fun a ↦ c a * c a) A) (hB : HasSum (fun a ↦ c a * (t ^ (∑ i, a i) * c a)) B) :
    B ≤ t ^ 2 * A + (1 - t ^ 2) * c 0 ^ 2 + (t - t ^ 2) * ∑ j, c (Pi.single j 1) ^ 2 := by
  obtain ⟨d, hd⟩ : ∃ d : (ι → ℕ) → ℝ, d = fun a ↦
      if a ∈ lowIdx ι then c a * (t ^ (∑ i, a i) * c a) - t ^ 2 * (c a * c a) else 0 :=
    ⟨_, rfl⟩
  have hD : HasSum d (∑ a ∈ lowIdx ι, d a) :=
    hasSum_sum_of_ne_finset_zero fun a ha ↦ by simp [hd, ha]
  have hle : ∀ a, c a * (t ^ (∑ i, a i) * c a) ≤ t ^ 2 * (c a * c a) + d a := by
    intro a
    by_cases ha : a ∈ lowIdx ι
    · simp [hd, ha]
    · simp only [hd, ha, ite_false, add_zero]
      have h1 : t ^ (∑ i, a i) ≤ t ^ 2 := pow_le_pow_of_le_one ht0 ht1 (two_le_of_notMem ha)
      nlinarith [mul_self_nonneg (c a)]
  have h := hasSum_le hle hB ((hA.mul_left (t ^ 2)).add hD)
  have h0 : d 0 = (1 - t ^ 2) * c 0 ^ 2 := by
    simp only [hd, zero_mem_lowIdx, ite_true, Pi.zero_apply, Finset.sum_const_zero, pow_zero]
    ring
  have h1 : ∀ j, d (Pi.single j 1) = (t - t ^ 2) * c (Pi.single j 1) ^ 2 := by
    intro j
    simp only [hd, single_mem_lowIdx, ite_true, sum_single, pow_one]
    ring
  rw [sum_lowIdx, h0, Finset.sum_congr rfl fun j _ ↦ h1 j, ← Finset.mul_sum] at h
  linarith

end Split

/-! ### The coefficients of a bounded function -/

/-- Parseval: `E g² = ∑_a ĝ(a)²`. -/
theorem hasSum_sq {g : Gs n → ℝ} (hg : MemLp g 2 (gm n)) :
    HasSum (fun a ↦ (∫ y, hermPi a y * g y ∂gm n) * ∫ y, hermPi a y * g y ∂gm n)
      (∫ x, g x ^ 2 ∂gm n) := by
  simpa only [sq] using hasSum_parseval hg hg

/-- `⟨g, T_t g⟩ = ∑_a t^{|a|} ĝ(a)²`. -/
theorem hasSum_nBil {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) {g : Gs n → ℝ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    HasSum (fun a ↦ (∫ y, hermPi a y * g y ∂gm n) *
      (t ^ (∑ i, a i) * ∫ y, hermPi a y * g y ∂gm n)) (nBil t g g) := by
  have hg2 := Gaussian.memLp_two_of_abs_le (μ := gm n) hg hgC
  have hT := Gaussian.memLp_two_of_abs_le (μ := gm n) (measurable_noiseOp t hg)
    (abs_noiseOp_le t hgC)
  have h := hasSum_parseval hg2 hT
  rw [← nBil_eq] at h
  simpa only [coef_noiseOp ht hg2] using h

/-- `ĝ(0) = E g`. -/
theorem coef_zero (g : Gs n → ℝ) : ∫ y, hermPi 0 y * g y ∂gm n = gMean g := by
  simp [hermPi_zero, gMean]

/-- `∑ⱼ ĝ(eⱼ)² = |F̂⁽¹⁾(g)|²`. -/
theorem sum_coef_single {g : Gs n → ℝ} (hg : MemLp g 2 (gm n)) :
    ∑ j, (∫ y, hermPi (Pi.single j 1) y * g y ∂gm n) ^ 2 = ‖hermite1 g‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hermite1_apply g hg j]
  simp_rw [hermPi_single, mul_comm]

end SharpH

open SharpH

/-- **The spectral gap**: `⟨g, T_t g⟩ ≤ t² E g² + (1 - t²) (E g)² + (t - t²) |F̂⁽¹⁾(g)|²`. -/
theorem nBil_le_hermite {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {g : Gs n → ℝ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    nBil t g g ≤ t ^ 2 * ∫ x, g x ^ 2 ∂gm n + (1 - t ^ 2) * gMean g ^ 2 +
      (t - t ^ 2) * ‖hermite1 g‖ ^ 2 := by
  have hg2 := Gaussian.memLp_two_of_abs_le (μ := gm n) hg hgC
  have h := le_of_hasSum_sq (c := fun a ↦ ∫ y, hermPi a y * g y ∂gm n) ht0 ht1 (hasSum_sq hg2)
    (hasSum_nBil ⟨by linarith, ht1⟩ hg hgC)
  rwa [coef_zero, sum_coef_single hg2] at h

/-- **The low levels**: `⟨g, T_t g⟩ ≥ (E g)² + t |F̂⁽¹⁾(g)|²`. -/
theorem hermite_le_nBil {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {g : Gs n → ℝ} (hg : Measurable g)
    {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    gMean g ^ 2 + t * ‖hermite1 g‖ ^ 2 ≤ nBil t g g := by
  have hg2 := Gaussian.memLp_two_of_abs_le (μ := gm n) hg hgC
  have h := sq_add_le_of_hasSum (c := fun a ↦ ∫ y, hermPi a y * g y ∂gm n) ht0
    (hasSum_nBil ⟨by linarith, ht1⟩ hg hgC)
  rwa [coef_zero, sum_coef_single hg2] at h

end BGHKLMM26.RobustMIS
