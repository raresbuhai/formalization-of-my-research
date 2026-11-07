module

public import BGHKLMM26.RobustMIS.Defs

/-!
# Multilinear polynomials on the cube

The dictionary between a function `f` on the cube, its Walsh coefficients, and the multilinear
polynomial with these coefficients evaluated on `{±1}^R`: `mlEval (coefficient f) (bitVec x) = f x`
(Walsh inversion), the noise operator is `smoothC`, Parseval, influences; linear forms (`linC`).
The Gaussian side is in `MultilinearGauss.lean`.

Material: `Imported/OAI/Computability/MaxCut/Walsh.lean` (`walsh_inversion`, `walsh_parseval`,
`walsh_inner`, `walsh_orthogonality`), `Estimates/Degree.lean` (`noise`, `coefficient_noise`).

All statements are proved. Helpers (namespace `Multilinear`): `mlEval_bitVec_eq_sum` (Walsh
expansion of `mlEval c ∘ bitVec`), the singleton `single i` (`= fun j ↦ decide (j = i)`) with
`single_injective`, `sdeg_single`, and `linC_apply`, `linC_single`, `linC_sq`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped RealInnerProductSpace BigOperators
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

/-- The singleton `{i}` as a cube point. -/
abbrev single (i : Fin R) : Cube (Fin R) := fun j ↦ decide (j = i)

theorem single_injective : Function.Injective (single (R := R)) := by
  intro i j h
  have := congrFun h i
  simp only [single, decide_true] at this
  exact of_decide_eq_true this.symm

theorem sdeg_single (i : Fin R) : sdeg (single i) = 1 := by
  simp [sdeg, OAI.OptimalMaxCut.Analytic.degree, single, Finset.filter_eq']

theorem linC_apply (w : Fin R → ℝ) (s : Cube (Fin R)) :
    linC w s = ∑ i, if s = single i then w i else 0 := rfl

theorem linC_single (w : Fin R → ℝ) (i : Fin R) : linC w (single i) = w i := by
  rw [linC_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : single i ≠ single j := fun h ↦ hj (single_injective h).symm
    simp [this]
  · simp

theorem linC_sq (w : Fin R → ℝ) (s : Cube (Fin R)) :
    linC w s ^ 2 = ∑ i, if s = single i then w i ^ 2 else 0 := by
  by_cases h : ∃ i, s = single i
  · obtain ⟨i, rfl⟩ := h
    rw [linC_single, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : single i ≠ single j := fun h ↦ hj (single_injective h).symm
      simp [this]
    · simp
  · push Not at h
    simp [linC_apply, h]

end Multilinear

open Multilinear

/-! ### On the cube -/

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

theorem influence_eq_inflC (f : Cube (Fin R) → ℝ) (i : Fin R) :
    influence i f = inflC (coefficient f) i := rfl

theorem inflC_smoothC_le {r : ℝ} (hr : |r| ≤ 1) (c : Cube (Fin R) → ℝ) (i : Fin R) :
    inflC (smoothC r c) i ≤ inflC c i := by
  unfold inflC smoothC
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [mul_pow, ← pow_mul]
  have h1 : r ^ (sdeg s * 2) ≤ 1 := by
    rw [mul_comm, pow_mul]
    exact pow_le_one₀ (sq_nonneg r) (by nlinarith [abs_le.mp hr, sq_abs r])
  nlinarith [sq_nonneg (c s)]

/-- `|û({i})|² ≤ Inf_i(u)`. -/
theorem coefficient_single_sq_le (u : Cube (Fin R) → ℝ) (i : Fin R) :
    coefficient u (fun j ↦ decide (j = i)) ^ 2 ≤ influence i u := by
  unfold influence
  exact Finset.single_le_sum (f := fun s ↦ coefficient u s ^ 2) (fun _ _ ↦ sq_nonneg _)
    (by simp)

/-! ### Linear forms -/

theorem mlEval_linC (w : Fin R → ℝ) (x : Fin R → ℝ) : mlEval (linC w) x = ∑ i, w i * x i := by
  unfold mlEval
  simp_rw [linC_apply, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, single]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem smoothC_linC (r : ℝ) (w : Fin R → ℝ) : smoothC r (linC w) = linC (r • w) := by
  funext s
  unfold smoothC
  simp_rw [linC_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : s = single i
  · subst h
    simp [sdeg_single]
  · simp [h]

theorem inflC_linC (w : Fin R → ℝ) (i : Fin R) : inflC (linC w) i = w i ^ 2 := by
  unfold inflC
  simp_rw [linC_sq]
  rw [Finset.sum_comm, Finset.sum_eq_single i]
  · rw [Finset.sum_ite_eq']
    simp
  · intro j _ hj
    refine Finset.sum_eq_zero fun s hs ↦ ?_
    have : s ≠ single j := by
      rintro rfl
      simp [single] at hs
      exact hj hs.symm
    simp [this]
  · simp

theorem sum_linC_sq (w : Fin R → ℝ) : ∑ s, linC w s ^ 2 = ∑ i, w i ^ 2 := by
  simp_rw [linC_sq]
  rw [Finset.sum_comm]
  simp

end BGHKLMM26.RobustMIS
