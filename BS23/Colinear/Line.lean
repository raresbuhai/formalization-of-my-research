module

public import BS23.Colinear.Alg
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# The empirical Hermite moment along a line

For points `Y`, a base point `v` and a direction `θ`, the function `t ↦ P̂_m(v + t θ)`
(`BS23.Colinear.phat`) is a real polynomial of degree at most `m`
(`BS23.Colinear.exists_poly_phat_line`), and its derivative at `0` is `⟨∇P̂_m(v), θ⟩`
(`BS23.Colinear.hasDerivAt_phat_line`, with `∇P̂_m = BS23.Colinear.gradPhat`).

The derivative at `0` of a polynomial `P` of degree at most `m` is a fixed combination of its
values at `0, 1, …, m` (`BS23.Colinear.derivative_eval_zero_eq_sum`):
`P'(0) = ∑_{j ≤ m} L_{m,j} P(j)`, with `L_{m,j} = (-1)^(j+1) C(m,j) / j` for `j ≥ 1` and
`L_{m,0} = -∑_{j=1}^m L_{m,j} = -H_m` (the derivatives at `0` of the Lagrange basis on the nodes
`0..m`; `BS23.Colinear.derivWeight_zero`). All `|L_{m,j}| ≤ 2^m`, so values bounded by `B` on
the nodes bound `|P'(0)|` by `(m+1) 2^m B` (`BS23.Colinear.abs_deriv_le_of_poly`,
`BS23.Colinear.abs_sub_deriv_le_of_poly`, `BS23.Colinear.abs_gradPhat_sub_le`).
-/

@[expose] public section

namespace BS23.Colinear

open Matrix Finset Polynomial

variable {n d : ℕ}

/-! ### Derivatives of Hermite polynomials -/

theorem hermCoeff_eq_zero_of_lt {m i : ℕ} (h : m < 2 * i) : hermCoeff m i = 0 := by
  simp [hermCoeff, Nat.choose_eq_zero_of_lt h]

/-- A sum of terms vanishing for `m < 2 i` may be taken over any range containing `m / 2`. -/
theorem sum_range_half_eq {M : Type*} [AddCommMonoid M] {m N : ℕ} (hN : m / 2 + 1 ≤ N)
    (f : ℕ → M) (hf : ∀ i, m < 2 * i → f i = 0) :
    ∑ i ∈ range (m / 2 + 1), f i = ∑ i ∈ range N, f i := by
  refine sum_subset (range_subset_range.2 hN) fun i _ hi ↦ hf i ?_
  simp only [mem_range, not_lt] at hi
  omega

theorem hermite_eq_sum_range {m N : ℕ} (hN : m / 2 + 1 ≤ N) (x q : ℝ) :
    hermite m x q =
      ∑ i ∈ range N, (-1) ^ i * (hermCoeff m i : ℝ) * x ^ (m - 2 * i) * q ^ i :=
  sum_range_half_eq hN _ fun i hi ↦ by simp [hermCoeff_eq_zero_of_lt hi]

theorem hermCoeff_mul_sub (m i : ℕ) :
    hermCoeff m i * (m - 2 * i) = m * hermCoeff (m - 1) i := by
  cases m with
  | zero => simp
  | succ k =>
    have h := Nat.choose_mul_succ_eq k (2 * i)
    simp only [hermCoeff, Nat.add_sub_cancel]
    rw [mul_right_comm, ← h]
    ring

theorem two_mul_hermCoeff_succ (m i : ℕ) :
    2 * (hermCoeff m (i + 1) : ℝ) * (i + 1) = m * (m - 1) * hermCoeff (m - 2) i := by
  rcases m with _ | _ | k
  · simp [hermCoeff_eq_zero_of_lt (show 0 < 2 * (i + 1) by omega)]
  · simp [hermCoeff_eq_zero_of_lt (show 1 < 2 * (i + 1) by omega)]
  · have hdf : Nat.doubleFactorial (2 * (i + 1) - 1) =
        (2 * i + 1) * Nat.doubleFactorial (2 * i - 1) := by
      rcases i with _ | j
      · simp
      · rw [show 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 by omega, Nat.doubleFactorial_add_two,
          show 2 * (j + 1) - 1 = 2 * j + 1 by omega]
        ring
    have h1' : ((k + 1 + 1 : ℕ) : ℝ) * ((k + 1).choose (2 * i + 1) : ℝ) =
        ((k + 1 + 1).choose (2 * i + 1 + 1) : ℝ) * ((2 * i + 1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq (k + 1) (2 * i + 1)
    have h2' : ((k + 1 : ℕ) : ℝ) * (k.choose (2 * i) : ℝ) =
        ((k + 1).choose (2 * i + 1) : ℝ) * ((2 * i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq k (2 * i)
    rw [hermCoeff, hermCoeff, hdf, show 2 * (i + 1) = 2 * i + 1 + 1 by ring,
      show k + 1 + 1 - 2 = k by omega]
    push_cast at h1' h2' ⊢
    linear_combination (-(2 * (i : ℝ) + 1) * (Nat.doubleFactorial (2 * i - 1) : ℝ)) * h1' -
      ((k : ℝ) + 2) * (Nat.doubleFactorial (2 * i - 1) : ℝ) * h2'

/-- `∂ₓ He_m(x; q) = m He_{m-1}(x; q)`, written as the termwise derivative. -/
theorem sum_hermite_dx (m : ℕ) (x q : ℝ) :
    ∑ i ∈ range (m / 2 + 1),
        (-1) ^ i * (hermCoeff m i : ℝ) * ((m - 2 * i : ℕ) : ℝ) * x ^ (m - 2 * i - 1) * q ^ i =
      m * hermite (m - 1) x q := by
  rw [sum_range_half_eq (N := m + 1) (by omega) _
      (fun i hi ↦ by simp [hermCoeff_eq_zero_of_lt hi]),
    hermite_eq_sum_range (N := m + 1) (by omega), mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  have key : (hermCoeff m i : ℝ) * ((m - 2 * i : ℕ) : ℝ) = m * hermCoeff (m - 1) i := by
    exact_mod_cast hermCoeff_mul_sub m i
  rw [show m - 2 * i - 1 = m - 1 - 2 * i by omega]
  linear_combination (-1) ^ i * x ^ (m - 1 - 2 * i) * q ^ i * key

/-- `∂_q He_m(x; q) = -(m (m-1) / 2) He_{m-2}(x; q)`, written as the termwise derivative. -/
theorem sum_hermite_dq (m : ℕ) (x q : ℝ) :
    m * (m - 1) / 2 * hermite (m - 2) x q =
      -∑ i ∈ range (m / 2 + 1),
        (-1) ^ i * (hermCoeff m i : ℝ) * x ^ (m - 2 * i) * ((i : ℝ) * q ^ (i - 1)) := by
  rw [sum_range_half_eq (N := m + 2) (by omega) _
      (fun i hi ↦ by simp [hermCoeff_eq_zero_of_lt hi]), sum_range_succ',
    hermite_eq_sum_range (N := m + 1) (by omega), mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  have key := two_mul_hermCoeff_succ m i
  rw [show m - 2 * (i + 1) = m - 2 - 2 * i by omega, Nat.add_sub_cancel]
  push_cast
  linear_combination -((-1) ^ i * x ^ (m - 2 - 2 * i) * q ^ i / 2) * key

/-- The chain rule for `He_m(x(t); q(t))`. -/
theorem hasDerivAt_hermite (m : ℕ) {x q : ℝ → ℝ} {x' q' s : ℝ} (hx : HasDerivAt x x' s)
    (hq : HasDerivAt q q' s) :
    HasDerivAt (fun t ↦ hermite m (x t) (q t))
      (m * hermite (m - 1) (x s) (q s) * x' -
        m * (m - 1) / 2 * hermite (m - 2) (x s) (q s) * q') s := by
  have h := HasDerivAt.sum (u := range (m / 2 + 1))
    (A := fun i t ↦ (-1) ^ i * (hermCoeff m i : ℝ) * x t ^ (m - 2 * i) * q t ^ i)
    fun i _ ↦ ((hx.fun_pow (m - 2 * i)).const_mul ((-1) ^ i * (hermCoeff m i : ℝ))).mul
      (hq.fun_pow i)
  convert h using 1
  · funext t
    simp only [hermite, Finset.sum_apply]
  rw [← sum_hermite_dx, sum_hermite_dq, neg_mul, sub_neg_eq_add, sum_mul, sum_mul,
    ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-! ### The empirical Hermite moment along a line -/

theorem dotProduct_line (w v θ : Fin d → ℝ) (t : ℝ) :
    w ⬝ᵥ (v + t • θ) = (w ⬝ᵥ θ) * t + w ⬝ᵥ v := by
  rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

theorem quad_line (C : Matrix (Fin d) (Fin d) ℝ) (v θ : Fin d → ℝ) (t : ℝ) :
    quad C (v + t • θ) =
      quad C θ * t ^ 2 + (v ⬝ᵥ (C *ᵥ θ) + θ ⬝ᵥ (C *ᵥ v)) * t + quad C v := by
  simp only [quad, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  ring

theorem empCov_transpose (Y : Fin n → Fin d → ℝ) : (empCov Y)ᵀ = empCov Y := by
  ext a b
  simp only [transpose_apply, empCov, mul_comm]

/-- `P̂_m(v + t θ)` is a polynomial of degree at most `m` in `t`. -/
theorem exists_poly_phat_line (m : ℕ) (Y : Fin n → Fin d → ℝ) (v θ : Fin d → ℝ) :
    ∃ P : ℝ[X], P.natDegree ≤ m ∧ ∀ t, P.eval t = phat m Y (v + t • θ) := by
  set q2 := quad (empCov Y) θ
  set q1 := v ⬝ᵥ (empCov Y *ᵥ θ) + θ ⬝ᵥ (empCov Y *ᵥ v)
  set q0 := quad (empCov Y) v
  let xj : Fin n → ℝ[X] := fun j ↦
    C ((Y j - mean Y) ⬝ᵥ θ) * X + C ((Y j - mean Y) ⬝ᵥ v)
  let qp : ℝ[X] := C q2 * X ^ 2 + C q1 * X + C q0
  refine ⟨C (n : ℝ)⁻¹ * ∑ j, hermite m (xj j) qp, ?_, fun t ↦ ?_⟩
  · refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun j _ ↦ ?_)
    refine natDegree_sum_le_of_forall_le _ _ fun i hi ↦ ?_
    have hi : 2 * i ≤ m := by simp only [mem_range] at hi; omega
    have hx : (xj j).natDegree ≤ 1 := natDegree_linear_le
    have hq : qp.natDegree ≤ 2 := natDegree_quadratic_le
    have hc : ((-1 : ℝ[X]) ^ i * (hermCoeff m i : ℝ[X])).natDegree ≤ 0 := by
      rw [show ((-1 : ℝ[X]) ^ i * (hermCoeff m i : ℝ[X])) =
          C ((-1 : ℝ) ^ i * (hermCoeff m i : ℝ)) by simp]
      exact (natDegree_C _).le
    refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le hc
      (natDegree_pow_le_of_le (m - 2 * i) hx)) (natDegree_pow_le_of_le i hq)).trans ?_
    omega
  · simp only [phat, dotProduct_line, quad_line, eval_mul, eval_C, eval_finsetSum, hermite,
      eval_pow, eval_neg, eval_one, eval_natCast, eval_add, eval_X, xj, qp, q0, q1, q2]
    rw [div_eq_inv_mul]

/-- The derivative of `t ↦ P̂_m(v + t θ)` at `0` is `⟨∇P̂_m(v), θ⟩`. -/
theorem hasDerivAt_phat_line (m : ℕ) (Y : Fin n → Fin d → ℝ) (v θ : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ ↦ phat m Y (v + t • θ)) (gradPhat m Y v ⬝ᵥ θ) 0 := by
  set Cv := empCov Y *ᵥ v
  set q2 := quad (empCov Y) θ
  set q1 := v ⬝ᵥ (empCov Y *ᵥ θ) + θ ⬝ᵥ (empCov Y *ᵥ v)
  set q0 := quad (empCov Y) v
  have hq1 : q1 = 2 * (Cv ⬝ᵥ θ) := by
    simp only [q1, Cv, dotProduct_mulVec, ← mulVec_transpose, empCov_transpose,
      dotProduct_comm θ]
    ring
  have hf : (fun t : ℝ ↦ phat m Y (v + t • θ)) = fun t ↦
      (∑ j, hermite m (((Y j - mean Y) ⬝ᵥ θ) * t + (Y j - mean Y) ⬝ᵥ v)
        (q2 * t ^ 2 + q1 * t + q0)) / n := by
    funext t
    simp only [phat, dotProduct_line, quad_line, q0, q1, q2]
  have hq : HasDerivAt (fun t : ℝ ↦ q2 * t ^ 2 + q1 * t + q0) q1 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).fun_pow 2).const_mul q2).add
      ((hasDerivAt_id (0 : ℝ)).const_mul q1) |>.add_const q0
    simpa using this
  have hj : ∀ j ∈ (univ : Finset (Fin n)), HasDerivAt
      (fun t ↦ hermite m (((Y j - mean Y) ⬝ᵥ θ) * t + (Y j - mean Y) ⬝ᵥ v)
        (q2 * t ^ 2 + q1 * t + q0))
      (m * hermite (m - 1) ((Y j - mean Y) ⬝ᵥ v) q0 * ((Y j - mean Y) ⬝ᵥ θ) -
        m * (m - 1) / 2 * hermite (m - 2) ((Y j - mean Y) ⬝ᵥ v) q0 * q1) 0 := by
    intro j _
    have hx : HasDerivAt (fun t : ℝ ↦ ((Y j - mean Y) ⬝ᵥ θ) * t + (Y j - mean Y) ⬝ᵥ v)
        ((Y j - mean Y) ⬝ᵥ θ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ((Y j - mean Y) ⬝ᵥ θ)).add_const
        ((Y j - mean Y) ⬝ᵥ v)
    simpa using hasDerivAt_hermite m hx hq
  rw [hf]
  convert (HasDerivAt.sum hj).div_const (n : ℝ) using 1
  · funext t
    simp only [Finset.sum_apply]
  rw [hq1]
  calc gradPhat m Y v ⬝ᵥ θ
      = ∑ j, ∑ a, ((m * hermite (m - 1) ((Y j - mean Y) ⬝ᵥ v) q0) *
            ((Y j a - mean Y a) * θ a) -
          (m * (m - 1)) * hermite (m - 2) ((Y j - mean Y) ⬝ᵥ v) q0 * (Cv a * θ a)) / n := by
        simp only [dotProduct, gradPhat, sum_div, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun j _ ↦ sum_congr rfl fun a _ ↦ ?_
        simp only [Pi.sub_apply, q0, Cv]
        ring
    _ = _ := by
        rw [sum_div]
        refine sum_congr rfl fun j _ ↦ ?_
        rw [← sum_div, sum_sub_distrib, ← mul_sum, ← mul_sum]
        simp only [dotProduct, Pi.sub_apply]
        ring

/-! ### The derivative at `0` from the values at `0, 1, …, m` -/

/-- The weight `(-1)^(j+1) C(m, j) / j` of the value at a node `j ≥ 1`. -/
noncomputable def lagWeight (m j : ℕ) : ℝ := (-1) ^ (j + 1) * (m.choose j : ℝ) / j

/-- The weights of `P'(0) = ∑_{j ≤ m} L_{m,j} P(j)` for `deg P ≤ m`:
`L_{m,j} = (-1)^(j+1) C(m,j) / j` for `j ≥ 1`, and `L_{m,0} = -∑_{j=1}^m L_{m,j}`, which is
`-H_m` (`BS23.Colinear.derivWeight_zero`). -/
noncomputable def derivWeight (m j : ℕ) : ℝ :=
  if j = 0 then -∑ i ∈ range m, lagWeight m (i + 1) else lagWeight m j

/-- `∑_{j ≤ m} (-1)^j C(m, j) j^p = 0` for `p < m` (the `m`-th difference of `x^p`). -/
theorem sum_neg_one_pow_choose_mul_pow {m p : ℕ} (hp : p < m) :
    ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) * (j : ℝ) ^ p = 0 := by
  have h := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hp) 0
  rw [fwdDiff_iter_eq_sum_shift] at h
  simp only [zero_add, nsmul_eq_mul, mul_one, Pi.zero_apply, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast] at h
  calc ∑ j ∈ range (m + 1), (-1 : ℝ) ^ j * (m.choose j : ℝ) * (j : ℝ) ^ p
      = (-1) ^ m * ∑ j ∈ range (m + 1), (-1 : ℝ) ^ (m - j) * (m.choose j : ℝ) * (j : ℝ) ^ p := by
        rw [mul_sum]
        refine sum_congr rfl fun j hj ↦ ?_
        have hjm : j ≤ m := by simp only [mem_range] at hj; omega
        have hsq : ((-1 : ℝ) ^ (m - j)) * (-1) ^ (m - j) = 1 := by
          rw [← mul_pow]; norm_num
        have hpow : (-1 : ℝ) ^ m = (-1) ^ (m - j) * (-1) ^ j := by
          rw [← pow_add, Nat.sub_add_cancel hjm]
        rw [hpow]
        linear_combination (-(-1 : ℝ) ^ j * (m.choose j : ℝ) * (j : ℝ) ^ p) * hsq
    _ = 0 := by rw [h, mul_zero]

/-- `∑_{j=1}^m (-1)^(j+1) C(m, j) / j = H_m`, so `L_{m,0} = -H_m`. -/
theorem sum_lagWeight (m : ℕ) :
    ∑ i ∈ range m, lagWeight m (i + 1) = ∑ i ∈ range m, 1 / ((i : ℝ) + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have halt := sum_neg_one_pow_choose_mul_pow (m := m + 1) (p := 0) (Nat.succ_pos m)
    rw [sum_range_succ'] at halt
    simp only [pow_zero, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_succ, mul_neg,
      neg_mul, sum_neg_distrib] at halt
    have hsplit : ∀ i ∈ range (m + 1), lagWeight (m + 1) (i + 1) =
        lagWeight m (i + 1) + (-1) ^ i * ((m + 1).choose (i + 1) : ℝ) / ((m : ℝ) + 1) := by
      intro i _
      have h' : ((m : ℝ) + 1) * (m.choose i : ℝ) =
          ((m + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) := by
        exact_mod_cast Nat.add_one_mul_choose_eq m i
      have h'' : ((m + 1).choose (i + 1) : ℝ) / ((m : ℝ) + 1) =
          (m.choose i : ℝ) / ((i : ℝ) + 1) := by
        rw [div_eq_div_iff (by positivity) (by positivity)]
        linarith
      rw [mul_div_assoc, h'']
      simp only [lagWeight, Nat.choose_succ_succ', Nat.cast_add, Nat.cast_one]
      ring
    rw [sum_congr rfl hsplit, sum_add_distrib, sum_range_succ (fun i ↦ lagWeight m (i + 1)), ih,
      ← sum_div, sum_range_succ (fun i ↦ 1 / ((i : ℝ) + 1))]
    have hzero : lagWeight m (m + 1) = 0 := by simp [lagWeight, Nat.choose_succ_self]
    have hone : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((m + 1).choose (i + 1) : ℝ) = 1 := by
      linarith
    rw [hzero, hone]
    ring

/-- `L_{m,0} = -H_m = -∑_{i=1}^m 1/i`. -/
theorem derivWeight_zero (m : ℕ) : derivWeight m 0 = -∑ i ∈ range m, 1 / ((i : ℝ) + 1) := by
  simp only [derivWeight, ↓reduceIte, sum_lagWeight]

/-- The moments of the weights: `∑_{j ≤ m} L_{m,j} j^k` is `1` for `k = 1` and `0` for the other
`k ≤ m`. -/
theorem sum_derivWeight_mul_pow {m k : ℕ} (hk : k ≤ m) :
    ∑ j ∈ range (m + 1), derivWeight m j * (j : ℝ) ^ k = if k = 1 then 1 else 0 := by
  rw [sum_range_succ']
  simp only [derivWeight, Nat.add_one_ne_zero, ↓reduceIte, Nat.cast_zero]
  rcases k with _ | p
  · simp
  · have h := sum_neg_one_pow_choose_mul_pow (show p < m by omega)
    rw [sum_range_succ'] at h
    rw [zero_pow (Nat.add_one_ne_zero p), mul_zero, add_zero]
    have hterm : ∀ i ∈ range m, lagWeight m (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (p + 1) =
        -((-1 : ℝ) ^ (i + 1) * (m.choose (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) ^ p) := by
      intro i _
      have hi : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [lagWeight, pow_succ]
      field_simp
      ring
    rw [sum_congr rfl hterm, sum_neg_distrib]
    simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.cast_zero,
      one_mul] at h
    rw [eq_neg_of_add_eq_zero_left h, neg_neg]
    rcases p with _ | p <;> simp

/-- **The derivative at `0` from the values at `0, 1, …, m`**: for `deg P ≤ m`,
`P'(0) = ∑_{j ≤ m} L_{m,j} P(j)`. -/
theorem derivative_eval_zero_eq_sum {m : ℕ} {P : ℝ[X]} (hP : P.natDegree ≤ m) :
    P.derivative.eval 0 = ∑ j ∈ range (m + 1), derivWeight m j * P.eval (j : ℝ) := by
  have hlt : P.natDegree < m + 1 := by omega
  simp_rw [eval_eq_sum_range' hlt, mul_sum]
  rw [sum_comm]
  have : ∀ k ∈ range (m + 1), ∑ j ∈ range (m + 1), derivWeight m j * (P.coeff k * (j : ℝ) ^ k) =
      P.coeff k * (if k = 1 then 1 else 0) := by
    intro k hk
    rw [← sum_derivWeight_mul_pow (m := m) (k := k) (by simp only [mem_range] at hk; omega),
      mul_sum]
    exact sum_congr rfl fun j _ ↦ by ring
  rw [sum_congr rfl this]
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_range]
  rw [← coeff_zero_eq_eval_zero, coeff_derivative]
  split_ifs with h
  · simp
  · simp only [zero_add, Nat.cast_zero, mul_one]
    exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem abs_lagWeight_le (m j : ℕ) : |lagWeight m j| ≤ m.choose j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [lagWeight]
  · rw [lagWeight, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
      Nat.abs_cast]
    exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hj)

/-- All the weights are at most `2^m` in absolute value. -/
theorem abs_derivWeight_le (m j : ℕ) : |derivWeight m j| ≤ 2 ^ m := by
  unfold derivWeight
  split_ifs
  · rw [abs_neg]
    calc |∑ i ∈ range m, lagWeight m (i + 1)|
        ≤ ∑ i ∈ range m, |lagWeight m (i + 1)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range m, (m.choose (i + 1) : ℝ) :=
          sum_le_sum fun i _ ↦ abs_lagWeight_le m (i + 1)
      _ ≤ 2 ^ m := by
          have h := Nat.sum_range_choose m
          rw [sum_range_succ'] at h
          have : ∑ i ∈ range m, m.choose (i + 1) ≤ 2 ^ m := by omega
          exact_mod_cast this
  · exact (abs_lagWeight_le m j).trans (by exact_mod_cast Nat.choose_le_two_pow m j)

/-- Values bounded by `B` at `0, 1, …, m` bound the derivative at `0` of a polynomial of degree
at most `m` by `(m + 1) 2^m B`. -/
theorem abs_derivative_eval_zero_le {m : ℕ} {P : ℝ[X]} (hP : P.natDegree ≤ m) {B : ℝ}
    (hB : ∀ j : ℕ, j ≤ m → |P.eval (j : ℝ)| ≤ B) :
    |P.derivative.eval 0| ≤ (m + 1) * 2 ^ m * B := by
  rw [derivative_eval_zero_eq_sum hP]
  calc |∑ j ∈ range (m + 1), derivWeight m j * P.eval (j : ℝ)|
      ≤ ∑ j ∈ range (m + 1), |derivWeight m j * P.eval (j : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range (m + 1), 2 ^ m * B := sum_le_sum fun j hj ↦ by
        rw [abs_mul]
        exact mul_le_mul (abs_derivWeight_le m j)
          (hB j (by simp only [mem_range] at hj; omega)) (abs_nonneg _) (by positivity)
    _ = (m + 1) * 2 ^ m * B := by
        rw [sum_const, card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### Functions that are polynomials along the line -/

/-- If `F` agrees with a polynomial of degree at most `m`, has derivative `F'` at `0`, and
`|F j| ≤ B` for `j = 0, 1, …, m`, then `|F'| ≤ (m + 1) 2^m B`. -/
theorem abs_deriv_le_of_poly {m : ℕ} {F : ℝ → ℝ} {F' B : ℝ}
    (hpoly : ∃ P : ℝ[X], P.natDegree ≤ m ∧ ∀ t, P.eval t = F t) (hF : HasDerivAt F F' 0)
    (hB : ∀ j : ℕ, j ≤ m → |F j| ≤ B) :
    |F'| ≤ (m + 1) * 2 ^ m * B := by
  obtain ⟨P, hPm, hPF⟩ := hpoly
  have hFP : F = fun t ↦ P.eval t := funext fun t ↦ (hPF t).symm
  have hD : F' = P.derivative.eval 0 := hF.unique (hFP ▸ P.hasDerivAt 0)
  rw [hD]
  exact abs_derivative_eval_zero_le hPm fun j hj ↦ (hPF j).symm ▸ hB j hj

/-- The version for differences: if `F₁, F₂` agree with polynomials of degree at most `m`, have
derivatives `D₁, D₂` at `0`, and `|F₁ j - F₂ j| ≤ B` for `j = 0, 1, …, m`, then
`|D₁ - D₂| ≤ (m + 1) 2^m B`. -/
theorem abs_sub_deriv_le_of_poly {m : ℕ} {F₁ F₂ : ℝ → ℝ} {D₁ D₂ B : ℝ}
    (h₁ : ∃ P : ℝ[X], P.natDegree ≤ m ∧ ∀ t, P.eval t = F₁ t)
    (h₂ : ∃ P : ℝ[X], P.natDegree ≤ m ∧ ∀ t, P.eval t = F₂ t)
    (hD₁ : HasDerivAt F₁ D₁ 0) (hD₂ : HasDerivAt F₂ D₂ 0)
    (hB : ∀ j : ℕ, j ≤ m → |F₁ j - F₂ j| ≤ B) :
    |D₁ - D₂| ≤ (m + 1) * 2 ^ m * B := by
  obtain ⟨P₁, hP₁, hPF₁⟩ := h₁
  obtain ⟨P₂, hP₂, hPF₂⟩ := h₂
  refine abs_deriv_le_of_poly (F := fun t ↦ F₁ t - F₂ t)
    ⟨P₁ - P₂, (natDegree_sub_le _ _).trans (max_le hP₁ hP₂), fun t ↦ ?_⟩ (hD₁.sub hD₂) hB
  rw [eval_sub, hPF₁, hPF₂]

/-- **The gradient of `P̂_m` from values on a line**: if `F` agrees with a polynomial of degree
at most `m`, has derivative `D` at `0`, and is within `B` of `t ↦ P̂_m(v + t θ)` at
`t = 0, 1, …, m`, then `|⟨∇P̂_m(v), θ⟩ - D| ≤ (m + 1) 2^m B`. -/
theorem abs_gradPhat_sub_le {m : ℕ} (Y : Fin n → Fin d → ℝ) (v θ : Fin d → ℝ) {F : ℝ → ℝ}
    {D B : ℝ} (hF : ∃ P : ℝ[X], P.natDegree ≤ m ∧ ∀ t, P.eval t = F t) (hD : HasDerivAt F D 0)
    (hB : ∀ j : ℕ, j ≤ m → |phat m Y (v + (j : ℝ) • θ) - F j| ≤ B) :
    |gradPhat m Y v ⬝ᵥ θ - D| ≤ (m + 1) * 2 ^ m * B :=
  abs_sub_deriv_le_of_poly (exists_poly_phat_line m Y v θ) hF (hasDerivAt_phat_line m Y v θ)
    hD hB

end BS23.Colinear
