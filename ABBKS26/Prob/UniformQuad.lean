module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Algebra.Order.Round

/-!
# Quadratic polynomials on `ℝ^d` by their coefficients

A quadratic polynomial `q(g) = gᵀ A g + ⟨b, g⟩ + c` on `ℝ^d` (`ABBKS26.Unif.Quad`), its value
(`ABBKS26.Unif.Quad.eval`) and the squared norm of its coefficients
`‖A‖_F² + ‖b‖² + c²` (`ABBKS26.Unif.Quad.normSq`).

* `ABBKS26.Unif.Quad.abs_eval_le`: if every coefficient is at most `M` in absolute value and
  `‖g‖ ≤ R`, then `|q(g)| ≤ M (dR + 1)²`. With `q - q'` in place of `q`, this is the Lipschitz
  bound in the coefficients used for nets (`ABBKS26.Unif.Quad.eval_sub`).
* `ABBKS26.Unif.Quad.abs_eval_sub_le`: if `‖A‖_F² + ‖b‖² + c² ≤ 1` then
  `|q(g') - q(g)| ≤ θ (2‖g‖ + 1) + θ²` for `‖g' - g‖ ≤ θ` (robustness to rounding).
* `ABBKS26.Unif.floor_mem_Icc`, `ABBKS26.Unif.ceil_mem_Icc`: rounding to a grid of mesh `h`.
-/

@[expose] public section

namespace ABBKS26.Unif

open Finset

variable {d : ℕ}

/-- A **quadratic polynomial** `q(g) = gᵀ A g + ⟨b, g⟩ + c` on `ℝ^d`, by its coefficients. -/
structure Quad (d : ℕ) where
  /-- The quadratic part. -/
  A : Matrix (Fin d) (Fin d) ℝ
  /-- The linear part. -/
  b : Fin d → ℝ
  /-- The constant term. -/
  c : ℝ

namespace Quad

/-- The value `q(g) = ∑ᵢⱼ Aᵢⱼ gᵢ gⱼ + ∑ᵢ bᵢ gᵢ + c`. -/
noncomputable def eval (q : Quad d) (g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, q.A i j * (g i * g j) + ∑ i, q.b i * g i + q.c

/-- The squared norm of the coefficients, `‖A‖_F² + ‖b‖² + c²`. -/
def normSq (q : Quad d) : ℝ :=
  ∑ i, ∑ j, q.A i j ^ 2 + ∑ i, q.b i ^ 2 + q.c ^ 2

/-- The coefficientwise difference. -/
instance : Sub (Quad d) := ⟨fun p q ↦ ⟨p.A - q.A, p.b - q.b, p.c - q.c⟩⟩

@[simp] theorem sub_A (p q : Quad d) : (p - q).A = p.A - q.A := rfl
@[simp] theorem sub_b (p q : Quad d) : (p - q).b = p.b - q.b := rfl
@[simp] theorem sub_c (p q : Quad d) : (p - q).c = p.c - q.c := rfl

open Matrix in
theorem eval_eq_dotProduct (q : Quad d) (g : EuclideanSpace ℝ (Fin d)) :
    q.eval g = g.ofLp ⬝ᵥ (q.A *ᵥ g.ofLp) + q.b ⬝ᵥ g.ofLp + q.c := by
  simp only [eval, dotProduct, Matrix.mulVec, mul_sum]
  congr 2
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

theorem eval_sub (p q : Quad d) (g : EuclideanSpace ℝ (Fin d)) :
    (p - q).eval g = p.eval g - q.eval g := by
  simp only [eval, sub_A, sub_b, sub_c, Matrix.sub_apply, Pi.sub_apply, sub_mul, sum_sub_distrib]
  ring

theorem continuous_eval (q : Quad d) : Continuous q.eval := by
  unfold eval
  fun_prop

theorem measurable_eval (q : Quad d) : Measurable q.eval :=
  q.continuous_eval.measurable

theorem abs_apply_le_norm (g : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |g i| ≤ ‖g‖ := by
  simpa using PiLp.norm_apply_le g i

/-- `|q(g)| ≤ M (dR + 1)²` when every coefficient is at most `M` in absolute value and
`‖g‖ ≤ R`. -/
theorem abs_eval_le {q : Quad d} {M R : ℝ} (hA : ∀ i j, |q.A i j| ≤ M) (hb : ∀ i, |q.b i| ≤ M)
    (hc : |q.c| ≤ M) {g : EuclideanSpace ℝ (Fin d)} (hg : ‖g‖ ≤ R) :
    |q.eval g| ≤ M * (d * R + 1) ^ 2 := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hc
  have hR : 0 ≤ R := (norm_nonneg _).trans hg
  have hgi : ∀ i, |g i| ≤ R := fun i ↦ (abs_apply_le_norm g i).trans hg
  have h1 : |∑ i, ∑ j, q.A i j * (g i * g j)| ≤ d * d * (M * R ^ 2) := by
    calc |∑ i, ∑ j, q.A i j * (g i * g j)| ≤ ∑ i, ∑ j, |q.A i j * (g i * g j)| :=
          (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, M * R ^ 2 := by
          refine sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ ?_
          rw [abs_mul, abs_mul, sq]
          have := hgi i
          have := hgi j
          gcongr
          exact hA i j
      _ = d * d * (M * R ^ 2) := by simp [mul_assoc]
  have h2 : |∑ i, q.b i * g i| ≤ d * (M * R) := by
    calc |∑ i, q.b i * g i| ≤ ∑ i, |q.b i * g i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, M * R := by
          refine sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          gcongr
          exacts [hb i, hgi i]
      _ = d * (M * R) := by simp
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc |q.eval g| ≤ |∑ i, ∑ j, q.A i j * (g i * g j)| + |∑ i, q.b i * g i| + |q.c| := by
        unfold eval
        exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ d * d * (M * R ^ 2) + d * (M * R) + M := by gcongr
    _ ≤ M * (d * R + 1) ^ 2 := by nlinarith [mul_nonneg hM (mul_nonneg hd hR)]

theorem sq_le_normSq_A (q : Quad d) (i j : Fin d) : q.A i j ^ 2 ≤ q.normSq := by
  have h1 : q.A i j ^ 2 ≤ ∑ j, q.A i j ^ 2 :=
    single_le_sum (f := fun j ↦ q.A i j ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ j)
  have h2 : ∑ j, q.A i j ^ 2 ≤ ∑ i, ∑ j, q.A i j ^ 2 :=
    single_le_sum (f := fun i ↦ ∑ j, q.A i j ^ 2)
      (fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ i)
  have h3 : 0 ≤ ∑ i, q.b i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold normSq
  nlinarith [sq_nonneg q.c]

theorem sq_le_normSq_b (q : Quad d) (i : Fin d) : q.b i ^ 2 ≤ q.normSq := by
  have h1 : q.b i ^ 2 ≤ ∑ i, q.b i ^ 2 :=
    single_le_sum (f := fun i ↦ q.b i ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i)
  have h3 : 0 ≤ ∑ i, ∑ j, q.A i j ^ 2 := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold normSq
  nlinarith [sq_nonneg q.c]

theorem sq_le_normSq_c (q : Quad d) : q.c ^ 2 ≤ q.normSq := by
  have h2 : 0 ≤ ∑ i, q.b i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  have h3 : 0 ≤ ∑ i, ∑ j, q.A i j ^ 2 := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold normSq
  linarith

theorem sumSq_A_le_normSq (q : Quad d) : ∑ i, ∑ j, q.A i j ^ 2 ≤ q.normSq := by
  have h2 : 0 ≤ ∑ i, q.b i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold normSq
  nlinarith [sq_nonneg q.c]

theorem sumSq_b_le_normSq (q : Quad d) : ∑ i, q.b i ^ 2 ≤ q.normSq := by
  have h3 : 0 ≤ ∑ i, ∑ j, q.A i j ^ 2 := sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _
  unfold normSq
  nlinarith [sq_nonneg q.c]

theorem abs_A_le_one {q : Quad d} (hq : q.normSq ≤ 1) (i j : Fin d) : |q.A i j| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 (by nlinarith [q.sq_le_normSq_A i j])

theorem abs_b_le_one {q : Quad d} (hq : q.normSq ≤ 1) (i : Fin d) : |q.b i| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 (by nlinarith [q.sq_le_normSq_b i])

theorem abs_c_le_one {q : Quad d} (hq : q.normSq ≤ 1) : |q.c| ≤ 1 :=
  abs_le_one_iff_mul_self_le_one.2 (by nlinarith [q.sq_le_normSq_c])

/-- A normalized quadratic is at most `(dR + 1)²` in absolute value on the ball of radius `R`. -/
theorem abs_eval_le_of_normSq_le {q : Quad d} (hq : q.normSq ≤ 1) {R : ℝ}
    {g : EuclideanSpace ℝ (Fin d)} (hg : ‖g‖ ≤ R) : |q.eval g| ≤ (d * R + 1) ^ 2 := by
  simpa using abs_eval_le (abs_A_le_one hq) (abs_b_le_one hq) (abs_c_le_one hq) hg

/-- Cauchy–Schwarz for a matrix of Frobenius norm at most `1`: `|xᵀ A y| ≤ ‖x‖ ‖y‖`. -/
theorem abs_bilin_le {A : Matrix (Fin d) (Fin d) ℝ} (hA : ∑ i, ∑ j, A i j ^ 2 ≤ 1)
    (x y : EuclideanSpace ℝ (Fin d)) : |∑ i, ∑ j, A i j * (x i * y j)| ≤ ‖x‖ * ‖y‖ := by
  have key := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin d × Fin d)) (fun p ↦ A p.1 p.2)
    (fun p ↦ x p.1 * y p.2)
  simp only [← univ_product_univ, sum_product, mul_pow] at key
  rw [← sum_mul_sum] at key
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  refine key.trans ?_
  have : 0 ≤ (∑ i, x i ^ 2) * ∑ j, y j ^ 2 :=
    mul_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (sum_nonneg fun _ _ ↦ sq_nonneg _)
  nlinarith

/-- Cauchy–Schwarz for a vector of norm at most `1`: `|⟨b, x⟩| ≤ ‖x‖`. -/
theorem abs_lin_le {b : Fin d → ℝ} (hb : ∑ i, b i ^ 2 ≤ 1) (x : EuclideanSpace ℝ (Fin d)) :
    |∑ i, b i * x i| ≤ ‖x‖ := by
  have key := sum_mul_sq_le_sq_mul_sq univ b (fun i ↦ x i)
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [EuclideanSpace.real_norm_sq_eq]
  refine key.trans ?_
  have : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

theorem eval_add_sub_eval (q : Quad d) (x e : EuclideanSpace ℝ (Fin d)) :
    q.eval (x + e) - q.eval x = ∑ i, ∑ j, q.A i j * (x i * e j) +
      ∑ i, ∑ j, q.A i j * (e i * x j) + ∑ i, ∑ j, q.A i j * (e i * e j) +
      ∑ i, q.b i * e i := by
  have h1 : ∑ i, ∑ j, q.A i j * ((x i + e i) * (x j + e j)) = ∑ i, ∑ j, q.A i j * (x i * x j) +
      ∑ i, ∑ j, q.A i j * (x i * e j) + ∑ i, ∑ j, q.A i j * (e i * x j) +
      ∑ i, ∑ j, q.A i j * (e i * e j) := by
    simp only [← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  have h2 : ∑ i, q.b i * (x i + e i) = ∑ i, q.b i * x i + ∑ i, q.b i * e i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  simp only [eval, PiLp.add_apply, h1, h2]
  ring

/-- **Robustness to perturbations**: for `‖A‖_F² + ‖b‖² + c² ≤ 1`,
`|q(x + e) - q(x)| ≤ ‖e‖ (2‖x‖ + 1) + ‖e‖²`. -/
theorem abs_eval_add_sub_le {q : Quad d} (hq : q.normSq ≤ 1) (x e : EuclideanSpace ℝ (Fin d)) :
    |q.eval (x + e) - q.eval x| ≤ ‖e‖ * (2 * ‖x‖ + 1) + ‖e‖ ^ 2 := by
  rw [eval_add_sub_eval]
  have hA := q.sumSq_A_le_normSq.trans hq
  have hb := q.sumSq_b_le_normSq.trans hq
  have h1 := abs_bilin_le hA x e
  have h2 := abs_bilin_le hA e x
  have h3 := abs_bilin_le hA e e
  have h4 := abs_lin_le hb e
  set u := ∑ i, ∑ j, q.A i j * (x i * e j)
  set v := ∑ i, ∑ j, q.A i j * (e i * x j)
  set w := ∑ i, ∑ j, q.A i j * (e i * e j)
  set z := ∑ i, q.b i * e i
  have := abs_add_le (u + v + w) z
  have := abs_add_le (u + v) w
  have := abs_add_le u v
  nlinarith

/-- **Robustness to perturbations**: for `‖A‖_F² + ‖b‖² + c² ≤ 1` and `‖y - x‖ ≤ θ`,
`|q(y) - q(x)| ≤ θ (2‖x‖ + 1) + θ²`. -/
theorem abs_eval_sub_le {q : Quad d} (hq : q.normSq ≤ 1) {x y : EuclideanSpace ℝ (Fin d)}
    {θ : ℝ} (h : ‖y - x‖ ≤ θ) : |q.eval y - q.eval x| ≤ θ * (2 * ‖x‖ + 1) + θ ^ 2 := by
  have := abs_eval_add_sub_le hq x (y - x)
  rw [add_sub_cancel] at this
  refine this.trans ?_
  have : 0 ≤ ‖y - x‖ := norm_nonneg _
  gcongr

end Quad

/-! ### Rounding to a grid -/

theorem floor_mem_Icc {x X h : ℝ} {K : ℕ} (hh : 0 < h) (hx : |x| ≤ X) (hK : X / h ≤ K) :
    ⌊x / h⌋ ∈ Finset.Icc (-(K : ℤ)) K := by
  have h1 : x / h ≤ X / h := div_le_div_of_nonneg_right ((le_abs_self x).trans hx) hh.le
  have h2 : -X / h ≤ x / h := div_le_div_of_nonneg_right (neg_le.1 ((neg_le_abs x).trans hx)) hh.le
  rw [neg_div] at h2
  rw [Finset.mem_Icc]
  constructor
  · have : ((-(K : ℤ) - 1 : ℤ) : ℝ) < ⌊x / h⌋ := by
      push_cast
      linarith [Int.sub_one_lt_floor (x / h)]
    have := Int.cast_lt.1 this
    omega
  · have : ((⌊x / h⌋ : ℤ) : ℝ) ≤ ((K : ℤ) : ℝ) := by
      push_cast
      linarith [Int.floor_le (x / h)]
    exact Int.cast_le.1 this

theorem ceil_mem_Icc {x X h : ℝ} {K : ℕ} (hh : 0 < h) (hx : |x| ≤ X) (hK : X / h ≤ K) :
    ⌈x / h⌉ ∈ Finset.Icc (-(K : ℤ)) K := by
  have h1 : x / h ≤ X / h := div_le_div_of_nonneg_right ((le_abs_self x).trans hx) hh.le
  have h2 : -X / h ≤ x / h := div_le_div_of_nonneg_right (neg_le.1 ((neg_le_abs x).trans hx)) hh.le
  rw [neg_div] at h2
  rw [Finset.mem_Icc]
  constructor
  · have : ((-(K : ℤ) : ℤ) : ℝ) ≤ ⌈x / h⌉ := by
      push_cast
      linarith [Int.le_ceil (x / h)]
    exact Int.cast_le.1 this
  · have : ((⌈x / h⌉ : ℤ) : ℝ) < ((K + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [Int.ceil_lt_add_one (x / h)]
    have := Int.cast_lt.1 this
    omega

theorem mul_floor_le {x h : ℝ} (hh : 0 < h) : h * ⌊x / h⌋ ≤ x := by
  have := Int.floor_le (x / h)
  rw [le_div_iff₀ hh] at this
  linarith

theorem lt_mul_floor_add {x h : ℝ} (hh : 0 < h) : x < h * ⌊x / h⌋ + h := by
  have := Int.lt_floor_add_one (x / h)
  rw [div_lt_iff₀ hh] at this
  linarith

theorem le_mul_ceil {x h : ℝ} (hh : 0 < h) : x ≤ h * ⌈x / h⌉ := by
  have := Int.le_ceil (x / h)
  rw [div_le_iff₀ hh] at this
  linarith

theorem mul_ceil_lt_add {x h : ℝ} (hh : 0 < h) : h * ⌈x / h⌉ < x + h := by
  have := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (x / h)) hh
  rw [mul_add, mul_div_cancel₀ _ hh.ne'] at this
  linarith

end ABBKS26.Unif
