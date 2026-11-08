module

public import BHJK25.Spectral.LDA.Moments
public import BHJK25.Spectral.Proj
public import Mathlib.Algebra.MvPolynomial.Polynomial

/-!
# The projections of a polynomial in `U diag(λ) Uᵀ`

For a polynomial `f` of degree `d` in the entries of `U diag(λ) Uᵀ`, the function
`φ(λ, U) = f(U diag(λ) Uᵀ)` (`BHJK25.Spectral.LDAAux.phi`):

* is a polynomial of degree at most `d` in each coordinate `λᵢ`, since every entry
  `∑ₖ U_ak λₖ U_bk` is affine in `λᵢ`; so are its projections (`BHJK25.Spectral.proj`);
* does not change when the coordinates of `λ` and the columns of `U` are permuted together, and
  the law of `(λ, U)` does not either when `λ` has independent identically distributed
  coordinates; so its projections on all coordinates are the same.
-/

@[expose] public section

namespace BHJK25.Spectral.LDAAux

open MeasureTheory ProbabilityTheory Polynomial

/-- A polynomial of degree `d` evaluated on an affine line is a polynomial of degree at most `d`
in the parameter. -/
theorem exists_poly_affine {σ : Type*} (f : MvPolynomial σ ℝ) (A B : σ → ℝ) :
    ∃ P : ℝ[X], P.natDegree ≤ f.totalDegree ∧
      ∀ x, MvPolynomial.eval (fun s ↦ B s * x + A s) f = P.eval x := by
  set g : σ → ℝ[X] := fun s ↦ C (B s) * X + C (A s)
  refine ⟨MvPolynomial.eval₂ C g f, ?_, fun x ↦ ?_⟩
  · rw [MvPolynomial.eval₂_eq]
    refine natDegree_sum_le_of_forall_le _ _ fun d hd ↦ ?_
    refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    refine le_trans (Finset.sum_le_sum fun s _ ↦ natDegree_pow_le) ?_
    exact le_trans (Finset.sum_le_sum fun s _ ↦
      mul_le_of_le_one_right (Nat.zero_le _) natDegree_linear_le) (MvPolynomial.le_totalDegree hd)
  · rw [MvPolynomial.polynomial_eval_eval₂]
    have h : (evalRingHom x).comp C = RingHom.id ℝ := by
      ext a
      simp
    rw [h]
    simp only [g, eval_add, eval_mul, eval_C, eval_X]
    rfl

variable {n m : ℕ}

/-- The entries of `U diag(λ) Uᵀ` are affine in `λᵢ`. -/
theorem specMap_update (lam : Fin m → ℝ) (U : Fin n → Fin m → ℝ) (i : Fin m) (x : ℝ)
    (a b : Fin n) :
    specMap n m (Function.update lam i x, U) a b =
      U a i * U b i * x + specMap n m (Function.update lam i 0, U) a b := by
  rw [specMap_apply, specMap_apply]
  have h : ∀ k, U a k * Function.update lam i x k * U b k =
      (if k = i then U a i * U b i * x else 0) + U a k * Function.update lam i 0 k * U b k := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, ite_true, mul_zero]
      ring
    · simp only [Function.update_of_ne hk, hk, ite_false, zero_add]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- `φ(λ, U)` is a polynomial of degree at most `deg f` in each coordinate of `λ`. -/
theorem phi_update_poly (f : MvPolynomial (Fin n × Fin n) ℝ)
    (p : (Fin m → ℝ) × (Fin n → Fin m → ℝ)) (i : Fin m) :
    ∃ P : ℝ[X], P.natDegree ≤ f.totalDegree ∧
      ∀ x, phi f (Function.update p.1 i x, p.2) = P.eval x := by
  obtain ⟨P, hP, hPx⟩ := exists_poly_affine f
    (fun s ↦ specMap n m (Function.update p.1 i 0, p.2) s.1 s.2) (fun s ↦ p.2 s.1 i * p.2 s.2 i)
  refine ⟨P, hP, fun x ↦ ?_⟩
  rw [← hPx]
  have h : entries (specMap n m (Function.update p.1 i x, p.2)) =
      fun s ↦ p.2 s.1 i * p.2 s.2 i * x + specMap n m (Function.update p.1 i 0, p.2) s.1 s.2 :=
    funext fun s ↦ specMap_update p.1 p.2 i x s.1 s.2
  unfold phi
  rw [h]

/-- Permuting the coordinates of `λ` and the columns of `U` together does not change
`U diag(λ) Uᵀ`. -/
theorem specMap_perm (σ : Equiv.Perm (Fin m)) (lam : Fin m → ℝ) (U : Fin n → Fin m → ℝ)
    (i : Fin m) (x : ℝ) :
    specMap n m (Function.update (fun k ↦ lam (σ k)) i x, fun a k ↦ U a (σ k)) =
      specMap n m (Function.update lam (σ i) x, U) := by
  ext a b
  rw [specMap_apply, specMap_apply,
    ← Equiv.sum_comp σ (fun k ↦ U a k * Function.update lam (σ i) x k * U b k)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Function.update_apply, σ.injective.eq_iff]

/-- Permuting the coordinates of a vector with independent identically distributed coordinates
does not change its law. -/
theorem measurePreserving_pi_perm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ : Equiv.Perm (Fin m)) :
    MeasurePreserving (fun lam : Fin m → ℝ ↦ fun k ↦ lam (σ k)) (Measure.pi fun _ ↦ μ)
      (Measure.pi fun _ ↦ μ) := by
  have h := measurePreserving_arrowCongr' (fun _ : Fin m ↦ μ) (fun _ : Fin m ↦ μ) σ.symm
    (MeasurableEquiv.refl ℝ) (fun _ ↦ MeasurePreserving.id μ)
  convert h using 1
  funext lam k
  rfl

/-- Permuting the coordinates of `λ` and the columns of `U` together does not change the law of
`(λ, U)`. -/
theorem measurePreserving_perm (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (σ : Equiv.Perm (Fin m)) :
    MeasurePreserving
      (fun p : (Fin m → ℝ) × (Fin n → Fin m → ℝ) ↦ ((fun k ↦ p.1 (σ k)), fun a k ↦ p.2 a (σ k)))
      ((Measure.pi fun _ ↦ μ).prod (gaussMat n m)) ((Measure.pi fun _ ↦ μ).prod (gaussMat n m)) :=
  (measurePreserving_pi_perm μ σ).prod ⟨by fun_prop, gaussMat_map_colPerm σ⟩

/-- The projections of `φ` on all coordinates are the same. -/
theorem proj_phi_eq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f : MvPolynomial (Fin n × Fin n) ℝ) (i j : Fin m) :
    proj μ (gaussMat n m) (phi f) i = proj μ (gaussMat n m) (phi f) j := by
  funext x
  have hT := measurePreserving_perm (n := n) μ (Equiv.swap i j)
  have hcont : Continuous fun p : (Fin m → ℝ) × (Fin n → Fin m → ℝ) ↦
      phi f (Function.update p.1 i x, p.2) :=
    (continuous_phi f).comp (by fun_prop)
  unfold proj
  conv_lhs => rw [← hT.map_eq]
  rw [integral_map hT.measurable.aemeasurable hcont.aestronglyMeasurable]
  congr 1
  funext p
  unfold phi
  rw [specMap_perm (Equiv.swap i j) p.1 p.2 i x, Equiv.swap_apply_left]

end BHJK25.Spectral.LDAAux
