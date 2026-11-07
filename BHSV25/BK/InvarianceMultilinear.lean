module

public import BHSV25.BK.InvarianceDefs

/-!
# Multilinear polynomials on the cube and under product laws

Copied from `BGHKLMM26/RobustMIS/{Multilinear,MultilinearGauss}.lean` (papers do not import each
other), with the namespace changed to `BHSV25.BK.Aint` and only the parts used here kept.

* On the cube: `mlEval (coefficient f) (bitVec x) = f x` (Walsh inversion) and
  `mlEval (smoothC r (coefficient f)) (bitVec x) = noise r f x` (OpenAI's noise operator).
* Under a product `Measure.pi ν` of centered laws with unit variance (namespace
  `MultilinearGauss`): the monomials `mono s x = ∏_{i∈S} xᵢ` are orthonormal
  (`integral_mlEval_mul_pi'`), `p(t x) = (T_t p)(x)` (`mlEval_mul_arg`), `continuous_mlEval'`,
  and `memLp_mlEval_pi'`.
-/

@[expose] public section

namespace BHSV25.BK.Aint

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R : ℕ}

namespace Multilinear
/-- `mlEval c ∘ bitVec` as a Walsh expansion. -/
theorem mlEval_bitVec_eq_sum (c : Cube (Fin R) → ℝ) (x : Cube (Fin R)) :
    mlEval c (bitVec x) = ∑ s, c s * walsh s x := by
  rw [mlEval]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  unfold walsh bitVec
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases s i <;> simp [bitSign]


end Multilinear

open Multilinear

/-- Walsh inversion: `f(x) = ∑_S f̂(S) χ_S(x)`. -/
theorem mlEval_bitVec (f : Cube (Fin R) → ℝ) (x : Cube (Fin R)) :
    mlEval (coefficient f) (bitVec x) = f x := by
  rw [← walsh_inversion f x, mlEval]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  unfold walsh bitVec
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases s i <;> simp [bitSign]

/-- The noise operator is `smoothC` on coefficients. -/
theorem mlEval_smoothC_bitVec (r : ℝ) (f : Cube (Fin R) → ℝ) (x : Cube (Fin R)) :
    mlEval (smoothC r (coefficient f)) (bitVec x) = noise r f x := by
  rw [noise, mlEval]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  congr 1
  unfold walsh bitVec
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  cases s i <;> simp [bitSign]

/-- The Walsh coefficients of a multilinear polynomial on the cube are its coefficients. -/
theorem coefficient_mlEval (c : Cube (Fin R) → ℝ) (s : Cube (Fin R)) :
    coefficient (fun x ↦ mlEval c (bitVec x)) s = c s := by
  unfold coefficient
  simp_rw [mlEval_bitVec_eq_sum, Finset.sum_mul]
  rw [Finset.expect_sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_expect, walsh_orthogonality]
  simp

/-- Parseval on the cube. -/
theorem expect_mlEval_sq (c : Cube (Fin R) → ℝ) :
    (𝔼 x, mlEval c (bitVec x) ^ 2) = ∑ s, c s ^ 2 := by
  rw [← walsh_parseval]
  simp_rw [coefficient_mlEval]
namespace MultilinearGauss

/-! ### Monomials -/

/-- The monomial `x^S = ∏_{i ∈ S} xᵢ`. -/
noncomputable def mono (s : Cube (Fin R)) (x : Fin R → ℝ) : ℝ := ∏ i, if s i then x i else 1

theorem mlEval_eq_sum (c : Cube (Fin R) → ℝ) (x : Fin R → ℝ) :
    mlEval c x = ∑ s, c s * mono s x := rfl


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

end MultilinearGauss

end BHSV25.BK.Aint
