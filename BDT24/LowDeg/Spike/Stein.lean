module

public import BDT24.LowDeg.Defs
public import TauCeti.Probability.Distributions.Gaussian.Moments
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Gaussian integration by parts for polynomials

Facts used in `BDT24/LowDeg/Spike.lean`:

* `BDT24.LowDeg.SK.skMom_succ`: the moments `M n = E g^n` of a standard Gaussian satisfy
  `M (n + 1) = n M (n - 1)`.
* `BDT24.LowDeg.SK.skStein_std`: for independent standard Gaussians `g` and a polynomial `q`,
  `E[g_m q(g)] = E[∂_m q(g)]` (on monomials, this is the recursion of the moments).
* `BDT24.LowDeg.SK.skStein`: for `z ~ N(0, S)` with `S` positive semidefinite and a polynomial `f`,
  `E[z_j f(z)] = ∑_l S_{jl} E[∂_l f(z)]`. Since `z = A g` for `A = √S`, this follows from the
  standard case and the chain rule `∂_m (f ∘ A) = ∑_l A_{lm} (∂_l f) ∘ A`
  (`BDT24.LowDeg.SK.skPderiv_lin`).
* Polynomials are integrable under products of standard Gaussians and under multivariate
  Gaussians (`BDT24.LowDeg.SK.skInt_eval`, `BDT24.LowDeg.SK.skInt_mvG`).
-/

@[expose] public section

namespace BDT24.LowDeg.SK

open MeasureTheory ProbabilityTheory MvPolynomial Matrix WithLp
open scoped MatrixOrder

/-! ### Moments of a standard Gaussian -/

/-- The moment `E g^n` of a standard Gaussian. -/
noncomputable def skMom (n : ℕ) : ℝ := ∫ u, u ^ n ∂gaussianReal 0 1

/-- The even moments of a standard Gaussian: `E g^(2t) = (2t - 1)!!`. -/
theorem skMom_two_mul (t : ℕ) : skMom (2 * t) = ((2 * t - 1).doubleFactorial : ℝ) := by
  have h := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 1 t
  simpa [skMom] using h

/-- The odd moments of a standard Gaussian vanish. -/
theorem skMom_two_mul_add_one (t : ℕ) : skMom (2 * t + 1) = 0 := by
  have h := TauCeti.Probability.centralMoment_id_two_mul_add_one_gaussianReal 0 1 t
  simpa [centralMoment, skMom] using h

/-- `E g^0 = 1`. -/
theorem skMom_zero : skMom 0 = 1 := by
  simpa using skMom_two_mul 0

/-- **The recursion of the Gaussian moments**: `E g^(n+1) = n E g^(n-1)`. -/
theorem skMom_succ (n : ℕ) : skMom (n + 1) = n * skMom (n - 1) := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [skMom_two_mul_add_one]
    rcases t with _ | t
    · simp
    · rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, skMom_two_mul_add_one, mul_zero]
  · rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, show 2 * t + 1 - 1 = 2 * t by omega,
      skMom_two_mul, skMom_two_mul, show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
    rcases t with _ | t
    · simp
    · rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, Nat.doubleFactorial_add_two,
        show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
      push_cast
      ring

/-! ### Independent standard Gaussians -/

variable {ι : Type*} [Fintype ι]

/-- Independent standard Gaussians indexed by `ι`. -/
noncomputable abbrev skStd (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι ↦ gaussianReal 0 1

/-- A monomial evaluates to the product of powers. -/
theorem skEval_monomial (g : ι → ℝ) (b : ι →₀ ℕ) (c : ℝ) :
    eval g (monomial b c) = c * ∏ l, g l ^ b l := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]

/-- A product of powers of independent standard Gaussians is integrable. -/
theorem skInt_prod_pow (b : ι → ℕ) : Integrable (fun g ↦ ∏ l, g l ^ b l) (skStd ι) :=
  Integrable.fintype_prod (f := fun l (u : ℝ) ↦ u ^ b l) fun l ↦
    TauCeti.integrable_pow_gaussianReal 0 1 (b l)

/-- **Polynomials of independent standard Gaussians are integrable.** -/
theorem skInt_eval (p : MvPolynomial ι ℝ) : Integrable (fun g ↦ eval g p) (skStd ι) := by
  simp_rw [eval_eq']
  exact integrable_finsetSum _ fun d _ ↦ (skInt_prod_pow d).const_mul _

/-- The expectation of a monomial of independent standard Gaussians is a product of moments. -/
theorem skIntegral_monomial (b : ι →₀ ℕ) (c : ℝ) :
    ∫ g, eval g (monomial b c) ∂skStd ι = c * ∏ l, skMom (b l) := by
  simp_rw [skEval_monomial]
  rw [integral_const_mul]
  congr 1
  exact integral_fintype_prod_eq_prod (fun l (u : ℝ) ↦ u ^ b l)

/-- The expectation of a sum of polynomials. -/
theorem skIntegral_add (p q : MvPolynomial ι ℝ) :
    ∫ g, eval g (p + q) ∂skStd ι = ∫ g, eval g p ∂skStd ι + ∫ g, eval g q ∂skStd ι := by
  simp_rw [map_add]
  exact integral_add (skInt_eval p) (skInt_eval q)

/-- The product of moments shifted up at `m` is `b m` times the product shifted down at `m`. -/
theorem skProd_mom_shift (b : ι →₀ ℕ) (m : ι) :
    ∏ l, skMom ((Finsupp.single m 1 + b : ι →₀ ℕ) l) =
      (b m : ℝ) * ∏ l, skMom ((b - Finsupp.single m 1 : ι →₀ ℕ) l) := by
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase _ (fun l ↦ skMom ((b - Finsupp.single m 1 : ι →₀ ℕ) l))
      (Finset.mem_univ m)]
  have h : ∏ l ∈ Finset.univ.erase m, skMom ((Finsupp.single m 1 + b : ι →₀ ℕ) l) =
      ∏ l ∈ Finset.univ.erase m, skMom ((b - Finsupp.single m 1 : ι →₀ ℕ) l) := by
    refine Finset.prod_congr rfl fun l hl ↦ ?_
    have hlm : l ≠ m := Finset.ne_of_mem_erase hl
    simp [Ne.symm hlm]
  rw [h, ← mul_assoc]
  congr 1
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.tsub_apply]
  rw [add_comm, skMom_succ]

/-- **Gaussian integration by parts** for independent standard Gaussians:
`E[g_m q(g)] = E[∂_m q(g)]` for a polynomial `q`. -/
theorem skStein_std (m : ι) (q : MvPolynomial ι ℝ) :
    ∫ g, eval g (X m * q) ∂skStd ι = ∫ g, eval g (pderiv m q) ∂skStd ι := by
  induction q using MvPolynomial.induction_on' with
  | monomial b c =>
    rw [X, monomial_mul_monomial, pderiv_monomial, skIntegral_monomial, skIntegral_monomial,
      skProd_mom_shift]
    ring
  | add p q hp hq =>
    rw [mul_add, map_add, skIntegral_add, skIntegral_add, hp, hq]

/-! ### Linear changes of variables -/

/-- The linear change of variables `X_j ↦ ∑_l A_{jl} X_l` by a matrix `A`. -/
noncomputable def skLin (A : Matrix ι ι ℝ) : MvPolynomial ι ℝ →ₐ[ℝ] MvPolynomial ι ℝ :=
  bind₁ fun j ↦ ∑ l, C (A j l) * X l

/-- Evaluating after the change of variables is evaluating at `A g`. -/
theorem skEval_lin (A : Matrix ι ι ℝ) (g : ι → ℝ) (p : MvPolynomial ι ℝ) :
    eval g (skLin A p) = eval (A *ᵥ g) p := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, skLin, aeval_bind₁]
  congr 2
  funext j
  simp [mulVec, dotProduct]

/-- The image of a variable under the change of variables. -/
theorem skLin_X (A : Matrix ι ι ℝ) (j : ι) : skLin A (X j) = ∑ l, C (A j l) * X l := by
  simp [skLin]

/-- The partial derivative of a linear form. -/
theorem skPderiv_linForm (A : Matrix ι ι ℝ) (j m : ι) :
    pderiv m (∑ l, C (A j l) * X l) = C (A j m) := by
  classical
  simp [map_sum, pderiv_X, Pi.single_apply]

/-- **The chain rule** for a linear change of variables:
`∂_m (f ∘ A) = ∑_l A_{lm} (∂_l f) ∘ A`. -/
theorem skPderiv_lin (A : Matrix ι ι ℝ) (m : ι) (p : MvPolynomial ι ℝ) :
    pderiv m (skLin A p) = ∑ l, C (A l m) * skLin A (pderiv l p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [skLin]
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    rw [map_mul, Derivation.leibniz, hp, skLin_X, skPderiv_linForm]
    simp only [Derivation.leibniz, map_add, map_mul, skLin_X, pderiv_X, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Pi.single_apply]
    congr 1
    · simp only [apply_ite (skLin A), map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ ↦ by ring

/-! ### Multivariate Gaussians -/

omit [Fintype ι] in
/-- A polynomial in the coordinates of `EuclideanSpace` is continuous. -/
theorem skCont_eval (p : MvPolynomial ι ℝ) :
    Continuous fun z : EuclideanSpace ℝ ι ↦ eval z.ofLp p :=
  (MvPolynomial.continuous_eval p).comp (PiLp.continuous_ofLp 2 _)

/-- A multivariate Gaussian is the image of independent standard Gaussians under `√S`. -/
theorem skMvG_eq [DecidableEq ι] (S : Matrix ι ι ℝ) :
    multivariateGaussian 0 S = (skStd ι).map fun g ↦ toLp 2 (CFC.sqrt S *ᵥ g) := by
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext g
  simp

/-- **Polynomials are integrable under a multivariate Gaussian.** -/
theorem skInt_mvG [DecidableEq ι] (S : Matrix ι ι ℝ) (p : MvPolynomial ι ℝ) :
    Integrable (fun z : EuclideanSpace ℝ ι ↦ eval z.ofLp p) (multivariateGaussian 0 S) := by
  rw [skMvG_eq, integrable_map_measure (skCont_eval p).aestronglyMeasurable (by fun_prop)]
  have h : ((fun z : EuclideanSpace ℝ ι ↦ eval z.ofLp p) ∘ fun g ↦ toLp 2 (CFC.sqrt S *ᵥ g)) =
      fun g ↦ eval g (skLin (CFC.sqrt S) p) := by
    funext g
    simp [skEval_lin]
  rw [h]
  exact skInt_eval _

/-- An expectation under a multivariate Gaussian, after the change of variables by `√S`. -/
theorem skIntegral_mvG [DecidableEq ι] (S : Matrix ι ι ℝ) (p : MvPolynomial ι ℝ) :
    ∫ z, eval z.ofLp p ∂multivariateGaussian 0 S =
      ∫ g, eval g (skLin (CFC.sqrt S) p) ∂skStd ι := by
  rw [skMvG_eq, integral_map (by fun_prop) (skCont_eval p).aestronglyMeasurable]
  simp [skEval_lin]

/-- The expectation of a sum, with constant coefficients. -/
theorem skIntegral_sum_C (s : Finset ι) (c : ι → ℝ) (p : ι → MvPolynomial ι ℝ) :
    ∫ g, eval g (∑ l ∈ s, C (c l) * p l) ∂skStd ι =
      ∑ l ∈ s, c l * ∫ g, eval g (p l) ∂skStd ι := by
  simp_rw [map_sum, map_mul, eval_C]
  rw [integral_finsetSum _ fun l _ ↦ (skInt_eval (p l)).const_mul (c l)]
  simp_rw [integral_const_mul]

/-- **Gaussian integration by parts** (Stein's identity) for `z ~ N(0, S)`:
`E[z_j f(z)] = ∑_l S_{jl} E[∂_l f(z)]` for a polynomial `f`. -/
theorem skStein [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (j : ι)
    (f : MvPolynomial ι ℝ) :
    ∫ z, eval z.ofLp (X j * f) ∂multivariateGaussian 0 S =
      ∑ l, S j l * ∫ z, eval z.ofLp (pderiv l f) ∂multivariateGaussian 0 S := by
  have hAA : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S (nonneg_iff_posSemidef.2 hS)
  have hsym : ∀ a b, CFC.sqrt S a b = CFC.sqrt S b a := fun a b ↦ by
    have h := (nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg S)).isHermitian.eq
    simpa [conjTranspose_apply] using (congrFun (congrFun h a) b).symm
  simp_rw [skIntegral_mvG]
  generalize CFC.sqrt S = A at hAA hsym
  subst hAA
  rw [map_mul, skLin_X, Finset.sum_mul]
  simp_rw [mul_assoc]
  rw [skIntegral_sum_C]
  simp_rw [skStein_std, skPderiv_lin, skIntegral_sum_C, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [hsym l m]
  ring

end BDT24.LowDeg.SK
