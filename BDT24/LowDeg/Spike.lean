module

public import BDT24.LowDeg.Defs
import BDT24.LowDeg.Spike.Herm
import BDT24.Prob.Gauss.Spike
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The laws of the samples of negative sparse PCA

* The coordinates of the null sample are independent standard Gaussians
  (`BDT24.LowDeg.map_sampleCoords_nullSample`): reading `n (d+1)` standard Gaussians as `n`
  points (`BDT24.LowDeg.SK.skRows`) gives `n` independent `N(0, I_{d+1})` points.
* The planted sample is a probability measure under which polynomials in the coordinates are
  integrable, and integrals against it are averages over the sign patterns
  (`BDT24.LowDeg.integral_plantedSample`).
* **Hermite coefficients** (`BDT24.LowDeg.integral_hermiteMv_planted`): given the sign pattern,
  the points are independent, so `E H_α = ∏ᵢ E H_{αᵢ}` over the points. For one point
  `z ~ N(0, S)` with `S = I - θ x xᵀ` (unit `x`, `0 ≤ θ ≤ 1`, so `S` is positive semidefinite),
  Gaussian integration by parts `E[z_j f(z)] = ∑_l S_{jl} E[∂_l f(z)]` for polynomials `f`
  (`BDT24.LowDeg.SK.skStein`, from `z = √S g` with `g` standard and the moment recursion
  `E g^(n+1) = n E g^(n-1)`), with `H_{a + e_j} = X_j H_a - ∂_j H_a` and
  `∂_l H_a = a_l H_{a - e_l}`, gives `E H_{a + e_j} = -θ x_j ∑_l a_l x_l E H_{a - e_l}`. So
  `E H_a = c_{|a|} x^a` with `c_0 = 1`, `c_1 = 0` and `c_{K+1} = -θ K c_{K-1}`, that is
  `E H_a = (-θ)^m (2m - 1)!! x^a` for `|a| = 2m` and `0` for odd `|a|`
  (`BDT24.LowDeg.SK.skEH_spiked`).
* **Pairing two spikes** (`BDT24.LowDeg.sum_hermCoef_pair`): by the multinomial theorem
  (`Finset.sum_pow_eq_sum_piAntidiag`), `∑_{|a| = 2L} x^a y^a / a! = ⟨x, y⟩^(2L) / (2L)!`.
-/

@[expose] public section

namespace BDT24.LowDeg

open MeasureTheory ProbabilityTheory

namespace SK

open MvPolynomial

/-- Reading `n m` coordinates as `n` points of `ℝ^m`: coordinate `j` of point `i` is entry
`(i, j)`. -/
noncomputable def skRows (n m : ℕ) : (Fin n × Fin m → ℝ) ≃ᵐ (Fin n → EuclideanSpace ℝ (Fin m)) :=
  (MeasurableEquiv.curry (Fin n) (Fin m) ℝ).trans
    (MeasurableEquiv.piCongrRight fun _ ↦ MeasurableEquiv.toLp 2 (Fin m → ℝ))

/-- The coordinates of the points are the inverse of `BDT24.LowDeg.SK.skRows`. -/
theorem skRows_symm (n m : ℕ) : ⇑(skRows n m).symm = sampleCoords := rfl

/-- A product measure on `ι × κ`, curried, is a product of product measures (as in
`BDT24/Alg/Coins/Gauss.lean`). -/
theorem skPi_map_curry {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : ι × κ ↦ μ).map (MeasurableEquiv.curry ι κ X) =
      Measure.pi fun _ : ι ↦ Measure.pi fun _ : κ ↦ μ := by
  have h := Measure.infinitePi_map_curry (fun (_ : ι) (_ : κ) ↦ μ)
  simp only [Measure.infinitePi_eq_pi] at h
  exact h

/-- `n m` independent standard Gaussians, as `n` points, are `n` independent `N(0, I_m)`
points. -/
theorem skMP_rows (n m : ℕ) :
    MeasurePreserving (skRows n m) (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  have h2 : MeasurePreserving (MeasurableEquiv.curry (Fin n) (Fin m) ℝ)
      (Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin m ↦ gaussianReal 0 1) :=
    ⟨(MeasurableEquiv.curry (Fin n) (Fin m) ℝ).measurable, skPi_map_curry _⟩
  have h3 : MeasurePreserving
      (MeasurableEquiv.piCongrRight fun _ : Fin n ↦ MeasurableEquiv.toLp 2 (Fin m → ℝ))
      (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin m ↦ gaussianReal 0 1)
      (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)) := by
    refine measurePreserving_pi _ _ fun _ ↦ ⟨(MeasurableEquiv.toLp 2 (Fin m → ℝ)).measurable, ?_⟩
    rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]
  exact h3.comp h2

/-- The coordinates of `n` independent `N(0, I_m)` points are independent standard Gaussians. -/
theorem skMap_rows (n m : ℕ) :
    (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ)).map
      sampleCoords = Measure.pi fun _ : Fin n × Fin m ↦ gaussianReal 0 1 := by
  rw [← skRows_symm]
  exact ((skMP_rows n m).symm (skRows n m)).map_eq

/-- With `k ≤ d`, there is a sign pattern with exactly `k` nonzero entries. -/
theorem skSigns_nonempty {d k : ℕ} (hkd : k ≤ d) : (spikeSigns d k).Nonempty := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin d)))
    (by simpa using hkd)
  refine ⟨fun i ↦ if i ∈ t then 1 else 0, ?_⟩
  simp only [spikeSigns, Finset.mem_filter, Finset.mem_univ, true_and]
  convert ht using 2
  ext i
  by_cases hi : i ∈ t <;> simp [hi]

/-- A multivariate Hermite polynomial evaluates to the product of one-variable Hermite
polynomials. -/
theorem skEval_hermiteMv {ι : Type*} [Fintype ι] (a : ι → ℕ) (s : ι → ℝ) :
    eval s (hermiteMv a) = ∏ i, Polynomial.aeval (s i) (Polynomial.hermite (a i)) := by
  rw [hermiteMv, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.aeval_def, eval_X]
  congr 1
  exact RingHom.ext_int _ _

/-- Polynomials in the coordinates of `n` independent multivariate Gaussian points are
integrable. -/
theorem skInt_pi {n m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (f : MvPolynomial (Fin n × Fin m) ℝ) :
    Integrable (fun ω ↦ eval (sampleCoords ω) f)
      (Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S) := by
  simp_rw [eval_eq']
  refine integrable_finsetSum _ fun d _ ↦ Integrable.const_mul ?_ _
  have h : (fun ω : Fin n → EuclideanSpace ℝ (Fin m) ↦ ∏ ij, sampleCoords ω ij ^ d ij) =
      fun ω ↦ ∏ i, eval (ω i).ofLp (∏ j, X j ^ d (i, j)) := by
    funext ω
    rw [Fintype.prod_prod_type]
    simp [sampleCoords, map_prod]
  rw [h]
  exact Integrable.fintype_prod
    (f := fun i (z : EuclideanSpace ℝ (Fin m)) ↦ eval z.ofLp (∏ j, X j ^ d (i, j)))
    fun i ↦ skInt_mvG S _

end SK

theorem measurable_sampleCoords {n m : ℕ} :
    Measurable (sampleCoords : (Fin n → EuclideanSpace ℝ (Fin m)) → Fin n × Fin m → ℝ) := by
  rw [← SK.skRows_symm]
  exact (SK.skRows n m).symm.measurable

/-- The coordinates of the null sample are independent standard Gaussians. -/
theorem map_sampleCoords_nullSample (n d : ℕ) :
    (nullSample n d).map sampleCoords = Measure.pi fun _ : Fin n × Fin (d + 1) ↦ gaussianReal 0 1 :=
  SK.skMap_rows n (d + 1)

theorem isProbabilityMeasure_plantedSample {n d k : ℕ} (hkd : k ≤ d) (θ : ℝ) :
    IsProbabilityMeasure (plantedSample n d k θ) := by
  have hc : ((spikeSigns d k).card : ENNReal) ≠ 0 := by
    simpa using (SK.skSigns_nonempty hkd).card_pos.ne'
  constructor
  simp only [plantedSample, Measure.smul_apply, Measure.finsetSum_apply, measure_univ,
    Finset.sum_const, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hc (ENNReal.natCast_ne_top _)

/-- Polynomials in the coordinates are integrable under the planted sample. -/
theorem integrable_plantedSample {n d k : ℕ} (θ : ℝ)
    (f : MvPolynomial (Fin n × Fin (d + 1)) ℝ) :
    Integrable (fun ω ↦ MvPolynomial.eval (sampleCoords ω) f) (plantedSample n d k θ) := by
  unfold plantedSample
  rcases (spikeSigns d k).eq_empty_or_nonempty with h | h
  · simp [h]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (by simpa using h.card_pos.ne'))
  exact integrable_finsetSum_measure.2 fun v _ ↦ SK.skInt_pi _ f

/-- Integrals against the planted sample are averages over the sign patterns. -/
theorem integral_plantedSample {n d k : ℕ} (θ : ℝ)
    (f : MvPolynomial (Fin n × Fin (d + 1)) ℝ) :
    ∫ ω, MvPolynomial.eval (sampleCoords ω) f ∂(plantedSample n d k θ) =
      (∑ v ∈ spikeSigns d k, ∫ ω, MvPolynomial.eval (sampleCoords ω) f
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (spikedCov θ (spikeVector k v)))) /
        (spikeSigns d k).card := by
  unfold plantedSample
  rw [integral_smul_measure, integral_finsetSum_measure fun v _ ↦ SK.skInt_pi _ f,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul, inv_mul_eq_div]

/-- **The Hermite coefficients of the planted sample with a fixed spike.** -/
theorem integral_hermiteMv_planted {n d k : ℕ} {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {v : Fin d → SignType} (hv : v ∈ spikeSigns d k) (α : Fin n × Fin (d + 1) → ℕ) :
    ∫ ω, MvPolynomial.eval (sampleCoords ω) (hermiteMv α)
        ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 (spikedCov θ (spikeVector k v))) =
      ∏ i, hermCoef θ (spikeVector k v) (fun j ↦ α (i, j)) := by
  have hx : spikeVector k v ⬝ᵥ spikeVector k v = 1 := by
    rw [Prob.G.spikeVector_eq, smul_dotProduct, dotProduct_smul,
      Prob.G.spikeDir_dotProduct_self hv, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow,
      Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by positivity)
  have hS : (spikedCov θ (spikeVector k v)).PosSemidef := by
    have h := Prob.G.posSemidef_smul_one_sub (spikeVector k v) (r := 1) hθ0 (by rw [hx]; linarith)
    rwa [one_smul] at h
  have h1 : ∀ ω : Fin n → EuclideanSpace ℝ (Fin (d + 1)),
      MvPolynomial.eval (sampleCoords ω) (hermiteMv α) =
        ∏ i, MvPolynomial.eval (ω i).ofLp (hermiteMv fun j ↦ α (i, j)) := fun ω ↦ by
    simp_rw [SK.skEval_hermiteMv]
    rw [Fintype.prod_prod_type]
    rfl
  simp_rw [h1]
  rw [integral_fintype_prod_eq_prod (fun i (z : EuclideanSpace ℝ (Fin (d + 1))) ↦
    MvPolynomial.eval z.ofLp (hermiteMv fun j ↦ α (i, j)))]
  exact Finset.prod_congr rfl fun i _ ↦ SK.skEH_spiked hS _

/-- **Pairing the Hermite coefficients of two spikes** in degree `2L`. -/
theorem sum_hermCoef_pair {m : ℕ} (θ : ℝ) (x y : Fin m → ℝ) (L : ℕ) :
    ∑ a ∈ Finset.Nat.antidiagonalTuple m (2 * L),
        hermCoef θ x a * hermCoef θ y a / multiFact a =
      θ ^ (2 * L) * ((2 * L - 1).doubleFactorial : ℝ) ^ 2 / (2 * L).factorial *
        (∑ j, x j * y j) ^ (2 * L) := by
  have hset : Finset.Nat.antidiagonalTuple m (2 * L) = Finset.univ.piAntidiag (2 * L) := by
    ext a
    simp [Finset.Nat.mem_antidiagonalTuple, Finset.mem_piAntidiag]
  rw [Finset.sum_pow_eq_sum_piAntidiag, ← hset, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finset.Nat.mem_antidiagonalTuple] at ha
  have hfact : (Nat.multinomial Finset.univ a : ℝ) * multiFact a = (2 * L).factorial := by
    have h := Nat.multinomial_spec Finset.univ a
    rw [ha] at h
    unfold multiFact
    rw [mul_comm]
    exact_mod_cast h
  have hpos : multiFact a ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ ↦ by positivity
  have hm : (Nat.multinomial Finset.univ a : ℝ) = (2 * L).factorial / multiFact a := by
    rw [← hfact, mul_div_cancel_right₀ _ hpos]
  have hL : 2 * L / 2 = L := by omega
  have hθ : (-θ) ^ L * (-θ) ^ L = θ ^ (2 * L) := by
    rw [← mul_pow, neg_mul_neg, pow_mul, sq]
  simp only [hermCoef, ha, even_two_mul, ite_true, hL, hm, mul_pow, Finset.prod_mul_distrib]
  field_simp
  rw [← hθ]
  ring

end BDT24.LowDeg
