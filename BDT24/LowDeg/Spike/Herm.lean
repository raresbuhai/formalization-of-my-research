module

public import BDT24.LowDeg.Spike.Stein
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Hermite coefficients of a Gaussian with covariance `I - θ x xᵀ`

* `BDT24.LowDeg.SK.skHermiteMv_succ`: `H_{a + e_j} = X_j H_a - ∂_j H_a` (from
  `He_{n+1} = X He_n - He_n'`), and `BDT24.LowDeg.SK.skPderiv_hermiteMv'`:
  `∂_l H_a = a_l H_{a - e_l}` (from `He_n' = n He_{n-1}`).
* `BDT24.LowDeg.SK.skEH_succ`: with Stein's identity, for `z ~ N(0, S)`,
  `E H_{a + e_j}(z) = ∑_l (S - I)_{jl} a_l E H_{a - e_l}(z)`.
* `BDT24.LowDeg.SK.skEH_spiked`: for `S = I - θ x xᵀ` positive semidefinite, `(S - I)_{jl} =
  -θ x_j x_l`, so `E H_a = c_{|a|} x^a` with `c_{K+1} = -θ K c_{K-1}`, `c_0 = 1`, `c_1 = 0`; this
  is `BDT24.LowDeg.hermCoef`.
-/

@[expose] public section

namespace BDT24.LowDeg.SK

open MeasureTheory ProbabilityTheory MvPolynomial Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Derivatives and recursion of the multivariate Hermite polynomials -/

/-- The factors of `H_a` other than the one at `l`. -/
noncomputable def skRest (a : ι → ℕ) (l : ι) : MvPolynomial ι ℝ :=
  ∏ i ∈ Finset.univ.erase l, Polynomial.aeval (X i : MvPolynomial ι ℝ) (Polynomial.hermite (a i))

/-- `H_a` is its factor at `l` times the others. -/
theorem skHermiteMv_split (a : ι → ℕ) (l : ι) :
    hermiteMv a = Polynomial.aeval (X l : MvPolynomial ι ℝ) (Polynomial.hermite (a l)) *
      skRest a l :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ l)).symm

/-- The other factors do not see the index at `l`. -/
theorem skRest_update (a : ι → ℕ) (l : ι) (n : ℕ) : skRest (Function.update a l n) l = skRest a l :=
  Finset.prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

omit [Fintype ι] in
/-- The chain rule for a partial derivative of a polynomial in one variable. -/
theorem skPderiv_aeval (l i : ι) (P : Polynomial ℤ) :
    pderiv l (Polynomial.aeval (X i : MvPolynomial ι ℝ) P) =
      Polynomial.aeval (X i : MvPolynomial ι ℝ) (Polynomial.derivative P) *
        Pi.single (M := fun _ ↦ MvPolynomial ι ℝ) l 1 i := by
  rw [← Derivation.restrictScalars_apply ℤ, Derivation.map_aeval, Derivation.restrictScalars_apply,
    pderiv_X, smul_eq_mul]

/-- The other factors do not depend on `X_l`. -/
theorem skPderiv_rest (a : ι → ℕ) (l : ι) : pderiv l (skRest a l) = 0 := by
  refine Finset.prod_induction _ (fun p ↦ pderiv l p = 0) (fun p q hp hq ↦ ?_) (by simp)
    fun i hi ↦ ?_
  · rw [Derivation.leibniz, hp, hq, smul_zero, smul_zero, add_zero]
  · rw [skPderiv_aeval, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi), mul_zero]

/-- The partial derivative of `H_a` at `l`: `He_{a_l}'(X_l)` times the other factors. -/
theorem skPderiv_hermiteMv (a : ι → ℕ) (l : ι) :
    pderiv l (hermiteMv a) =
      Polynomial.aeval (X l : MvPolynomial ι ℝ) (Polynomial.derivative (Polynomial.hermite (a l))) *
        skRest a l := by
  rw [skHermiteMv_split a l, Derivation.leibniz, skPderiv_rest, skPderiv_aeval,
    Pi.single_eq_same, smul_zero, zero_add, smul_eq_mul, mul_one, mul_comm]

/-- **The partial derivatives of `H_a`**: `∂_l H_a = a_l H_{a - e_l}`. -/
theorem skPderiv_hermiteMv' (a : ι → ℕ) (l : ι) :
    pderiv l (hermiteMv a) = C (a l : ℝ) * hermiteMv (Function.update a l (a l - 1)) := by
  rw [skPderiv_hermiteMv, skHermiteMv_split (Function.update a l (a l - 1)) l, skRest_update,
    Function.update_self, Polynomial.derivative_hermite, map_nsmul, nsmul_eq_mul, map_natCast,
    mul_assoc]

/-- **The recursion of `H_a`**: `H_{a + e_j} = X_j H_a - ∂_j H_a`. -/
theorem skHermiteMv_succ (a : ι → ℕ) (j : ι) :
    hermiteMv (Function.update a j (a j + 1)) = X j * hermiteMv a - pderiv j (hermiteMv a) := by
  rw [skHermiteMv_split (Function.update a j (a j + 1)) j, skRest_update, Function.update_self,
    Polynomial.hermite_succ, map_sub, map_mul, Polynomial.aeval_X, skPderiv_hermiteMv,
    skHermiteMv_split a j]
  ring

omit [DecidableEq ι] in
/-- `H_0 = 1`. -/
theorem skHermiteMv_zero : hermiteMv (0 : ι → ℕ) = 1 := by
  simp [hermiteMv]

/-! ### Expectations of the Hermite polynomials -/

/-- The expectation `E H_a(z)` for `z ~ N(0, S)`. -/
noncomputable def skEH (S : Matrix ι ι ℝ) (a : ι → ℕ) : ℝ :=
  ∫ z, eval z.ofLp (hermiteMv a) ∂multivariateGaussian 0 S

/-- **The recursion of the Hermite coefficients**:
`E H_{a + e_j}(z) = ∑_l (S - I)_{jl} a_l E H_{a - e_l}(z)` for `z ~ N(0, S)`. -/
theorem skEH_succ {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (a : ι → ℕ) (j : ι) :
    skEH S (Function.update a j (a j + 1)) =
      ∑ l, (S j l - if j = l then 1 else 0) * a l * skEH S (Function.update a l (a l - 1)) := by
  have hd : ∀ l, ∫ z, eval z.ofLp (pderiv l (hermiteMv a)) ∂multivariateGaussian 0 S =
      a l * skEH S (Function.update a l (a l - 1)) := fun l ↦ by
    simp_rw [skPderiv_hermiteMv', map_mul, eval_C]
    exact integral_const_mul _ _
  rw [skEH, skHermiteMv_succ]
  simp_rw [map_sub]
  rw [integral_sub (skInt_mvG S _) (skInt_mvG S _), skStein hS, hd]
  simp_rw [hd, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_assoc]

/-- `E H_0 = 1`. -/
theorem skEH_zero (S : Matrix ι ι ℝ) : skEH S 0 = 1 := by
  simp [skEH, skHermiteMv_zero]

/-! ### The spiked covariance -/

/-- The coefficient `c_K = (-θ)^(K/2) (K - 1)!!` for even `K`, `0` for odd `K`. -/
noncomputable def skC (θ : ℝ) (K : ℕ) : ℝ :=
  if Even K then (-θ) ^ (K / 2) * ((K - 1).doubleFactorial : ℝ) else 0

/-- `BDT24.LowDeg.hermCoef` is `c_{|a|} x^a`. -/
theorem skHermCoef_eq {m : ℕ} (θ : ℝ) (x : Fin m → ℝ) (a : Fin m → ℕ) :
    hermCoef θ x a = skC θ (∑ j, a j) * ∏ j, x j ^ a j := by
  unfold hermCoef skC
  split_ifs <;> simp

/-- **The recursion of the coefficients**: `c_{K+1} = -θ K c_{K-1}`. -/
theorem skC_succ (θ : ℝ) (K : ℕ) : skC θ (K + 1) = -θ * K * skC θ (K - 1) := by
  obtain ⟨t, rfl | rfl⟩ := Nat.even_or_odd' K
  · have h1 : ¬ Even (2 * t + 1) := Nat.not_even_two_mul_add_one t
    rcases t with _ | t
    · simp [skC]
    · have h2 : ¬ Even (2 * (t + 1) - 1) := by
        rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
        exact Nat.not_even_two_mul_add_one t
      simp [skC, h1, h2]
  · have h1 : Even (2 * t + 1 + 1) := ⟨t + 1, by ring⟩
    have h2 : Even (2 * t + 1 - 1) := ⟨t, by omega⟩
    simp only [skC, h1, h2, ite_true]
    rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega, show 2 * t + 1 - 1 = 2 * t by omega,
      show (2 * t) / 2 = t by omega, show 2 * t + 1 + 1 - 1 = 2 * t + 1 by omega]
    rcases t with _ | t
    · simp
    · rw [show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by ring, Nat.doubleFactorial_add_two,
        show 2 * (t + 1) - 1 = 2 * t + 1 by omega]
      push_cast
      ring

/-- A product over an updated multi-index: the factor at `l` times the others. -/
theorem skProd_update {R : Type*} [CommMonoid R] (f : ι → ℕ → R) (a : ι → ℕ) (l : ι) (n : ℕ) :
    ∏ i, f i (Function.update a l n i) = f l n * ∏ i ∈ Finset.univ.erase l, f i (a i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- A sum over an updated multi-index: the entry at `l` plus the others. -/
theorem skSum_update (a : ι → ℕ) (l : ι) (n : ℕ) :
    ∑ i, Function.update a l n i = n + ∑ i ∈ Finset.univ.erase l, a i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l), Function.update_self]
  congr 1
  exact Finset.sum_congr rfl fun i hi ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- A nonzero multi-index of total degree `K + 1` is `a' + e_j` for some `a'` of degree `K`. -/
theorem skExists_pred {a : ι → ℕ} {K : ℕ} (ha : ∑ i, a i = K + 1) :
    ∃ a' : ι → ℕ, ∃ j, a = Function.update a' j (a' j + 1) ∧ ∑ i, a' i = K := by
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at ha
  refine ⟨Function.update a j (a j - 1), j, ?_, ?_⟩
  · funext i
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      omega
    · simp [Function.update_of_ne hij]
  · have h1 := skSum_update a j (a j - 1)
    have h2 := Finset.add_sum_erase Finset.univ a (Finset.mem_univ j)
    omega

/-- The entries of `I - θ x xᵀ - I`. -/
theorem skSpiked_apply {m : ℕ} (θ : ℝ) (x : Fin m → ℝ) (j l : Fin m) :
    (1 - θ • vecMulVec x x) j l - (if j = l then 1 else 0) = -θ * x j * x l := by
  rw [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-- One term of the recursion for `I - θ x xᵀ`, given the coefficients in degree `K - 1`. -/
theorem skSpiked_term {m : ℕ} {θ : ℝ} {x : Fin m → ℝ} {K : ℕ} {a : Fin m → ℕ}
    (ha : ∑ i, a i = K) (j l : Fin m)
    (ih : ∀ b : Fin m → ℕ, ∑ i, b i = K - 1 →
      skEH (1 - θ • vecMulVec x x) b = skC θ (K - 1) * ∏ i, x i ^ b i) :
    ((1 - θ • vecMulVec x x) j l - if j = l then 1 else 0) * a l *
        skEH (1 - θ • vecMulVec x x) (Function.update a l (a l - 1)) =
      -θ * x j * (skC θ (K - 1) * ∏ i, x i ^ a i) * a l := by
  rw [skSpiked_apply]
  by_cases hl : a l = 0
  · simp [hl]
  have hsl : ∑ i, Function.update a l (a l - 1) i = K - 1 := by
    have h1 := skSum_update a l (a l - 1)
    have h2 := Finset.add_sum_erase Finset.univ a (Finset.mem_univ l)
    omega
  rw [ih _ hsl, skProd_update (fun i n ↦ x i ^ n),
    ← Finset.mul_prod_erase Finset.univ (fun i ↦ x i ^ a i) (Finset.mem_univ l)]
  obtain ⟨r, hr⟩ : ∃ r, a l = r + 1 := ⟨a l - 1, by omega⟩
  rw [hr, Nat.add_sub_cancel, pow_succ]
  ring

/-- **The Hermite coefficients of `N(0, I - θ x xᵀ)`**: `E H_a = c_{|a|} x^a`, which is
`BDT24.LowDeg.hermCoef θ x a`. -/
theorem skEH_spiked {m : ℕ} {θ : ℝ} {x : Fin m → ℝ} (hS : (1 - θ • vecMulVec x x).PosSemidef)
    (a : Fin m → ℕ) : skEH (1 - θ • vecMulVec x x) a = hermCoef θ x a := by
  rw [skHermCoef_eq]
  suffices h : ∀ K, ∀ a : Fin m → ℕ, ∑ j, a j = K →
      skEH (1 - θ • vecMulVec x x) a = skC θ K * ∏ j, x j ^ a j from h _ a rfl
  intro K
  induction K using Nat.strong_induction_on with
  | _ K ih =>
  intro a ha
  rcases K with _ | K
  · have h0 : a = 0 := funext fun j ↦ (Finset.sum_eq_zero_iff.1 ha) j (Finset.mem_univ j)
    subst h0
    simp [skEH_zero, skC]
  obtain ⟨a', j, rfl, hsum⟩ := skExists_pred ha
  rw [skEH_succ hS]
  simp_rw [skSpiked_term hsum j _ (ih (K - 1) (by omega))]
  rw [← Finset.mul_sum, skC_succ, skProd_update (fun i n ↦ x i ^ n),
    ← Finset.mul_prod_erase Finset.univ (fun i ↦ x i ^ a' i) (Finset.mem_univ j), pow_succ]
  have hK : ∑ i, (a' i : ℝ) = K := by exact_mod_cast hsum
  rw [hK]
  ring

end BDT24.LowDeg.SK
