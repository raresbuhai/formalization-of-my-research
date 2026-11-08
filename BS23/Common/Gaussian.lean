module

public import BS23.Common.Good
public import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Moments of the standard Gaussian

The monomial moments `E ∏ᵢ Gᵢ^αᵢ` of a standard Gaussian vector `G` are `gaussMomMulti α`, from
the one-dimensional moments `E Z^p = (p-1)‼` (`p` even) and `0` (`p` odd) of TauCeti. The vector
is either the product `Measure.pi (fun _ ↦ gaussianReal 0 1)` on `Fin d → ℝ` or Mathlib's
`stdGaussian` on `EuclideanSpace ℝ (Fin d)`, which is its image under `toLp`
(`map_pi_eq_stdGaussian`).

* `BS23.integral_prod_pow_pi`, `BS23.integral_prod_pow_stdGaussian`: `E G^α = gaussMomMulti α`.
* `BS23.integrable_prod_pow_pi`, `BS23.integrable_prod_pow_stdGaussian`: the monomials are
  integrable.
* `BS23.gaussMomMulti_two_mul_le`: `E G^{2α} ≤ (2D)^D` for `|α| ≤ D`.
-/

@[expose] public section

namespace BS23

open MeasureTheory ProbabilityTheory

/-! ### One dimension -/

/-- Every power is integrable for the standard Gaussian. -/
theorem integrable_pow_gaussianReal (p : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ p) (gaussianReal 0 1) := by
  have h : Integrable (fun x : ℝ ↦ ‖x‖ ^ p) (gaussianReal 0 1) := by
    simpa using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) (p : ENNReal) (by simp)).integrable_norm_pow'
  rw [← integrable_norm_iff (continuous_pow p).aestronglyMeasurable]
  simpa only [norm_pow] using h

/-- `E Z^p = gaussMom p` for a standard Gaussian `Z`. -/
theorem integral_pow_gaussianReal (p : ℕ) :
    ∫ x, x ^ p ∂(gaussianReal 0 1) = (gaussMom p : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' p
  · have h := TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 1 m
    simp only [sub_zero, NNReal.coe_one, one_pow, one_mul] at h
    rw [h, gaussMom, ite_eq_left (even_two_mul m)]
  · have h := TauCeti.Probability.centralMoment_id_two_mul_add_one_gaussianReal 0 1 m
    simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_gaussianReal,
      sub_zero] at h
    rw [h, gaussMom, ite_eq_right (Nat.not_even_two_mul_add_one m), Nat.cast_zero]

/-! ### Products -/

variable {d : ℕ}

/-- The monomials are integrable for the product of standard Gaussians. -/
theorem integrable_prod_pow_pi (α : Fin d → ℕ) :
    Integrable (fun x : Fin d → ℝ ↦ ∏ i, x i ^ α i) (Measure.pi fun _ ↦ gaussianReal 0 1) :=
  Integrable.fintype_prod (f := fun i (x : ℝ) ↦ x ^ α i) fun i ↦ integrable_pow_gaussianReal (α i)

/-- `E G^α = gaussMomMulti α` for the product of standard Gaussians. -/
theorem integral_prod_pow_pi (α : Fin d → ℕ) :
    ∫ x, ∏ i, x i ^ α i ∂(Measure.pi fun _ ↦ gaussianReal 0 1) = (gaussMomMulti α : ℝ) := by
  rw [integral_fintype_prod_eq_prod (f := fun i (x : ℝ) ↦ x ^ α i)]
  simp only [integral_pow_gaussianReal, gaussMomMulti, Nat.cast_prod]

/-- The monomials are integrable for the standard Gaussian on `EuclideanSpace ℝ (Fin d)`. -/
theorem integrable_prod_pow_stdGaussian (α : Fin d → ℕ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) ↦ ∏ i, x i ^ α i)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rw [← map_pi_eq_stdGaussian, integrable_map_measure (by fun_prop) (by fun_prop)]
  exact integrable_prod_pow_pi α

/-- `E G^α = gaussMomMulti α` for the standard Gaussian on `EuclideanSpace ℝ (Fin d)`. -/
theorem integral_prod_pow_stdGaussian (α : Fin d → ℕ) :
    ∫ x, ∏ i, x i ^ α i ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) = (gaussMomMulti α : ℝ) := by
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  exact integral_prod_pow_pi α

/-! ### Even moments -/

/-- `(2b+1)‼ ≤ (2b+1)^(b+1)`. -/
theorem doubleFactorial_le_pow (b : ℕ) :
    Nat.doubleFactorial (2 * b + 1) ≤ (2 * b + 1) ^ (b + 1) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [show 2 * (b + 1) + 1 = 2 * b + 1 + 2 by ring, Nat.doubleFactorial_add_two]
    calc (2 * b + 1 + 2) * Nat.doubleFactorial (2 * b + 1)
        ≤ (2 * b + 1 + 2) * (2 * b + 1) ^ (b + 1) := Nat.mul_le_mul_left _ ih
      _ ≤ (2 * b + 1 + 2) * (2 * b + 1 + 2) ^ (b + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      _ = (2 * b + 1 + 2) ^ (b + 1 + 1) := by ring

/-- `E Z^{2a} = (2a-1)‼ ≤ (2a)^a`. -/
theorem gaussMom_two_mul_le (a : ℕ) : gaussMom (2 * a) ≤ (2 * a) ^ a := by
  rw [gaussMom, ite_eq_left (even_two_mul a)]
  cases a with
  | zero => simp
  | succ b =>
    rw [show 2 * (b + 1) - 1 = 2 * b + 1 by omega]
    exact (doubleFactorial_le_pow b).trans (Nat.pow_le_pow_left (by omega) _)

/-- **Even moments of a standard Gaussian vector.** For a multi-index `α` of total degree at
most `D`, `E G^{2α} = gaussMomMulti (2α) ≤ (2D)^D`. -/
theorem gaussMomMulti_two_mul_le {α : Fin d → ℕ} {D : ℕ} (hα : ∑ i, α i ≤ D) :
    gaussMomMulti (fun i ↦ 2 * α i) ≤ (2 * D) ^ D := by
  have hle : ∀ i, α i ≤ D := fun i ↦
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (α j)) (Finset.mem_univ i)).trans hα
  calc gaussMomMulti (fun i ↦ 2 * α i) = ∏ i, gaussMom (2 * α i) := rfl
    _ ≤ ∏ i, (2 * D) ^ α i := Finset.prod_le_prod fun i _ ↦
        (gaussMom_two_mul_le (α i)).trans (Nat.pow_le_pow_left (by linarith [hle i]) _)
    _ = (2 * D) ^ ∑ i, α i := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 * D) ^ D := by
        rcases Nat.eq_zero_or_pos D with rfl | hD
        · simp [Nat.le_zero.mp hα]
        · exact Nat.pow_le_pow_right (by omega) hα

/-- `gaussMomMulti_two_mul_le` in `ℝ`. -/
theorem gaussMomMulti_two_mul_le_real {α : Fin d → ℕ} {D : ℕ} (hα : ∑ i, α i ≤ D) :
    (gaussMomMulti (fun i ↦ 2 * α i) : ℝ) ≤ (2 * D : ℝ) ^ D := by
  exact_mod_cast gaussMomMulti_two_mul_le hα

end BS23
