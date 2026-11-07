module

public import Background.SumOfSquares.Moments
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# A distribution with a well-conditioned moment matrix

The uniform distribution on the grid `{0, 1, …, d}^σ`. Its moment matrix in degree `2d` is
positive definite with an explicit margin: `Ẽ[g²] ≥ λ ‖g‖₂²` for every polynomial `g` of degree at
most `d` (`SoS.minEigGE_gridMoment`), where `λ = SoS.gridEig |σ| d` has `log (1/λ)` polynomial in
`|σ|` and `d`. Its moments are rational and easy to compute:
`Ẽ[xᵐ] = ∏ i, (∑ t ≤ d, t^(mᵢ)) / (d + 1)` (`SoS.gridMoment`).

The sum-of-squares algorithm needs such a distribution for two things. The ellipsoid method only
produces moments whose moment matrices are approximately positive semidefinite, `≥ -τ`; adding
`τ / λ` times the grid moments makes them exactly positive semidefinite
(`SoS.MinEigGE.isPSD_add_smul`). This turns the algorithm's output into a pseudo-expectation, and
its auxiliary sequences into the positive semidefinite sequences of `SoS.approxNonneg_iff`.

The bound comes from interpolation. A polynomial of degree at most `d` is determined by its values
on the grid, and each coefficient is a combination of them (`SoS.coeff_eq_sum_grid`) whose weights
are products of entries of the inverse of the Vandermonde matrix of `0, 1, …, d`. Those entries
are cofactors divided by the determinant, a product of positive integers, so they are at most
`(d + 1)! (d + 1)^(d (d + 1))` (`SoS.abs_interpWeight_le`).
-/

@[expose] public section

namespace SoS

open MvPolynomial Matrix

/-! ### Interpolation at `0, 1, …, d` -/

/-- The Vandermonde matrix of the nodes `0, 1, …, d`: the row of `t` is `(1, t, t², …, t^d)`. -/
noncomputable def gridVandermonde (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  vandermonde fun t ↦ ((t : ℕ) : ℝ)

/-- The determinant is `∏_{s < t} (t - s)`, a product of positive integers. -/
theorem one_le_det_gridVandermonde (d : ℕ) : 1 ≤ (gridVandermonde d).det := by
  rw [gridVandermonde, det_vandermonde]
  refine Finset.one_le_prod₀ fun i _ ↦ Finset.one_le_prod₀ fun j hj ↦ ?_
  have hij : (i : ℕ) + 1 ≤ j := Finset.mem_Ioi.1 hj
  have : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
  linarith

/-- The weights recovering the coefficient of `x^a` of a polynomial of degree at most `d` from its
values at `t = 0, 1, …, d`: a row of the inverse of the Vandermonde matrix (`0` for `a > d`). -/
noncomputable def interpWeight (d a : ℕ) (t : Fin (d + 1)) : ℝ :=
  if h : a < d + 1 then (gridVandermonde d)⁻¹ ⟨a, h⟩ t else 0

/-- The weights recover coefficients: `∑ t, c a t * t^b = [a = b]` for `a, b ≤ d`. -/
theorem sum_interpWeight_mul_pow {d a b : ℕ} (ha : a ≤ d) (hb : b ≤ d) :
    ∑ t, interpWeight d a t * ((t : ℕ) : ℝ) ^ b = if a = b then 1 else 0 := by
  have hdet : IsUnit (gridVandermonde d).det :=
    isUnit_iff_ne_zero.2 (ne_of_gt (zero_lt_one.trans_le (one_le_det_gridVandermonde d)))
  have key := congrFun (congrFun (nonsing_inv_mul _ hdet) ⟨a, by omega⟩) ⟨b, by omega⟩
  have ha' : a < d + 1 := by omega
  simp only [Matrix.mul_apply, Matrix.one_apply, Fin.mk.injEq, gridVandermonde,
    vandermonde_apply] at key
  simpa [interpWeight, ha', gridVandermonde] using key

/-- A bound on the interpolation weights: `(d + 1)! (d + 1)^(d (d + 1))`. -/
def interpBound (d : ℕ) : ℕ := (d + 1).factorial * ((d + 1) ^ d) ^ (d + 1)

theorem abs_interpWeight_le (d a : ℕ) (t : Fin (d + 1)) :
    |interpWeight d a t| ≤ interpBound d := by
  unfold interpWeight
  split_ifs with h
  · -- The entry is a cofactor divided by the determinant, which is at least `1`.
    have hdet := one_le_det_gridVandermonde d
    have hadj : |adjugate (gridVandermonde d) ⟨a, h⟩ t| ≤ interpBound d := by
      rw [adjugate_apply]
      have hent : ∀ i j, |(gridVandermonde d).updateRow t (Pi.single ⟨a, h⟩ 1) i j| ≤
          (((d + 1) ^ d : ℕ) : ℝ) := by
        intro i j
        have h1 : (1 : ℝ) ≤ (((d + 1) ^ d : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_le_pow _ _ (Nat.succ_pos d)
        rw [updateRow_apply]
        split_ifs
        · rcases eq_or_ne j ⟨a, h⟩ with rfl | hj
          · simpa using h1
          · rw [Pi.single_eq_of_ne hj, abs_zero]
            positivity
        · rw [gridVandermonde, vandermonde_apply, abs_pow, Nat.abs_cast]
          have hi : ((i : ℕ) : ℝ) ≤ d + 1 := by exact_mod_cast i.2.le
          calc ((i : ℕ) : ℝ) ^ (j : ℕ) ≤ ((d : ℝ) + 1) ^ (j : ℕ) :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) hi _
            _ ≤ ((d : ℝ) + 1) ^ d := pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.1 j.2)
            _ = (((d + 1) ^ d : ℕ) : ℝ) := by push_cast; ring
      have := det_le (abv := AbsoluteValue.abs) hent
      simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at this
      refine this.trans (le_of_eq ?_)
      simp [interpBound]
    rw [inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', abs_mul, abs_inv,
      abs_of_pos (zero_lt_one.trans_le hdet)]
    calc (gridVandermonde d).det⁻¹ * |adjugate (gridVandermonde d) ⟨a, h⟩ t|
        ≤ 1 * |adjugate (gridVandermonde d) ⟨a, h⟩ t| :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hdet) (abs_nonneg _)
      _ ≤ interpBound d := by rw [one_mul]; exact hadj
  · simp

/-! ### Interpolation on the grid -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The grid point `x ∈ {0, …, d}^σ`, as a point of `ℝ^σ`. -/
def gridPoint {d : ℕ} (x : σ → Fin (d + 1)) : σ → ℝ := fun i ↦ ((x i : ℕ) : ℝ)

/-- **Interpolation on the grid.** Each coefficient of a polynomial of degree at most `d` is a
combination of its values on the grid `{0, …, d}^σ`, with weights products of interpolation
weights. -/
theorem coeff_eq_sum_grid {d : ℕ} {g : MvPolynomial σ ℝ} (hg : g.totalDegree ≤ d)
    {α : σ →₀ ℕ} (hα : α.degree ≤ d) :
    g.coeff α = ∑ x : σ → Fin (d + 1),
      (∏ i, interpWeight d (α i) (x i)) * eval (gridPoint x) g := by
  classical
  simp_rw [eval_eq', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hβ : ∀ β ∈ g.support, ∑ x : σ → Fin (d + 1),
      (∏ i, interpWeight d (α i) (x i)) * (g.coeff β * ∏ i, gridPoint x i ^ β i) =
        if α = β then g.coeff β else 0 := by
    intro β hβ
    have hβd : β.degree ≤ d := (le_totalDegree hβ).trans hg
    calc _ = g.coeff β * ∑ x : σ → Fin (d + 1),
          ∏ i, interpWeight d (α i) (x i) * ((x i : ℕ) : ℝ) ^ β i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ ↦ ?_
          rw [Finset.prod_mul_distrib]
          simp only [gridPoint]
          ring
      _ = g.coeff β * ∏ i, ∑ t, interpWeight d (α i) t * ((t : ℕ) : ℝ) ^ β i := by
          rw [Fintype.prod_sum]
      _ = g.coeff β * ∏ i, (if α i = β i then 1 else 0) := by
          congr 1
          exact Finset.prod_congr rfl fun i _ ↦ sum_interpWeight_mul_pow
            ((Finsupp.le_degree i α).trans hα) ((Finsupp.le_degree i β).trans hβd)
      _ = _ := by
          by_cases h : α = β
          · simp [h]
          · obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
              by_contra! h'
              exact h (Finsupp.ext h')
            rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
            simp [h]
  rw [Finset.sum_congr rfl hβ, Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact notMem_support_iff.1 h

/-- The coefficients of a polynomial of degree at most `d` are bounded by its values on the grid:
`‖g‖₂² ≤ (|σ| + 1)^d C^(2|σ|) (d + 1)^|σ| ∑ₓ g(x)²`, where `C = SoS.interpBound d`. -/
theorem coeffNorm_sq_le_sum_grid {d : ℕ} {g : MvPolynomial σ ℝ} (hg : g.totalDegree ≤ d) :
    coeffNorm g ^ 2 ≤ ((Fintype.card σ + 1) ^ d * interpBound d ^ (2 * Fintype.card σ) *
      (d + 1) ^ Fintype.card σ : ℕ) * ∑ x : σ → Fin (d + 1), eval (gridPoint x) g ^ 2 := by
  classical
  set n := Fintype.card σ
  set S := ∑ x : σ → Fin (d + 1), eval (gridPoint x) g ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  -- Each coefficient: `g_α² ≤ C^(2n) (d + 1)^n S`.
  have hcoeff : ∀ α ∈ g.support,
      g.coeff α ^ 2 ≤ (interpBound d : ℝ) ^ (2 * n) * ((d : ℝ) + 1) ^ n * S := by
    intro α hα
    rw [coeff_eq_sum_grid hg ((le_totalDegree hα).trans hg)]
    have h1 : |∑ x : σ → Fin (d + 1), (∏ i, interpWeight d (α i) (x i)) * eval (gridPoint x) g|
        ≤ (interpBound d : ℝ) ^ n * ∑ x : σ → Fin (d + 1), |eval (gridPoint x) g| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ ↦ ?_
      rw [abs_mul, Finset.abs_prod]
      gcongr
      calc ∏ i, |interpWeight d (α i) (x i)| ≤ ∏ _i : σ, (interpBound d : ℝ) :=
            Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ abs_interpWeight_le _ _ _
        _ = _ := by simp [n]
    have h2 : (∑ x : σ → Fin (d + 1), |eval (gridPoint x) g|) ^ 2 ≤ ((d : ℝ) + 1) ^ n * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun x : σ → Fin (d + 1) ↦ |eval (gridPoint x) g|)
      simpa [sq_abs, n, S] using this
    have hsum0 : 0 ≤ ∑ x : σ → Fin (d + 1), |eval (gridPoint x) g| :=
      Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    calc _ = |∑ x : σ → Fin (d + 1), (∏ i, interpWeight d (α i) (x i)) *
          eval (gridPoint x) g| ^ 2 := (sq_abs _).symm
      _ ≤ ((interpBound d : ℝ) ^ n * ∑ x : σ → Fin (d + 1), |eval (gridPoint x) g|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (interpBound d : ℝ) ^ (2 * n) * (∑ x : σ → Fin (d + 1), |eval (gridPoint x) g|) ^ 2 := by
          ring
      _ ≤ (interpBound d : ℝ) ^ (2 * n) * (((d : ℝ) + 1) ^ n * S) := by gcongr
      _ = (interpBound d : ℝ) ^ (2 * n) * ((d : ℝ) + 1) ^ n * S := by ring
  -- Sum over the support, which has at most `(n + 1)^d` monomials.
  have hcard : (g.support.card : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
    have := (card_support_le g).trans (Nat.pow_le_pow_right (Nat.succ_pos n) hg)
    exact_mod_cast this
  rw [coeffNorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]
  calc ∑ α ∈ g.support, g.coeff α ^ 2
      ≤ ∑ _α ∈ g.support, (interpBound d : ℝ) ^ (2 * n) * ((d : ℝ) + 1) ^ n * S :=
        Finset.sum_le_sum hcoeff
    _ = g.support.card * ((interpBound d : ℝ) ^ (2 * n) * ((d : ℝ) + 1) ^ n * S) := by simp
    _ ≤ ((n : ℝ) + 1) ^ d * ((interpBound d : ℝ) ^ (2 * n) * ((d : ℝ) + 1) ^ n * S) := by
        gcongr
    _ = _ := by push_cast; ring

/-! ### The moments of the grid -/

/-- The moments of the uniform distribution on the grid `{0, …, d}^σ`:
`Ẽ[xᵐ] = ∏ i, (∑ t ≤ d, t^(mᵢ)) / (d + 1)`. They are rational, and easy to compute. -/
def gridMoment (d : ℕ) (m : σ →₀ ℕ) : ℚ :=
  ∏ i, (∑ t ∈ Finset.range (d + 1), (t : ℚ) ^ m i) / (d + 1)

/-- The Riesz functional of the grid moments is the average over the grid. -/
theorem riesz_gridMoment_apply (d : ℕ) (f : MvPolynomial σ ℝ) :
    riesz (fun m ↦ (gridMoment d m : ℝ)) f =
      (∑ x : σ → Fin (d + 1), eval (gridPoint x) f) / ((d : ℝ) + 1) ^ Fintype.card σ := by
  classical
  rw [riesz_apply]
  simp_rw [eval_eq']
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [← Finset.mul_sum, mul_div_assoc]
  congr 1
  -- `∑ₓ ∏ i, xᵢ^(mᵢ) = ∏ i, ∑ t, t^(mᵢ)`.
  have hprod : ∑ x : σ → Fin (d + 1), ∏ i, gridPoint x i ^ m i =
      ∏ i, ∑ t ∈ Finset.range (d + 1), (t : ℝ) ^ m i := by
    have hfin : ∀ i, ∑ t ∈ Finset.range (d + 1), (t : ℝ) ^ m i =
        ∑ t : Fin (d + 1), ((t : ℕ) : ℝ) ^ m i :=
      fun i ↦ (Fin.sum_univ_eq_sum_range (fun t ↦ (t : ℝ) ^ m i) _).symm
    simp_rw [hfin, Fintype.prod_sum]
    rfl
  rw [hprod, gridMoment]
  push_cast
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]

omit [DecidableEq σ] in
@[simp] theorem gridMoment_zero (d : ℕ) : gridMoment (σ := σ) d 0 = 1 := by
  simp only [gridMoment, Finsupp.coe_zero, Pi.zero_apply, pow_zero, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.prod_eq_one]
  intro i _
  have : (d : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  exact div_self this

omit [DecidableEq σ] in
/-- The grid moments are at most `d^|m|`. -/
theorem abs_gridMoment_le (d : ℕ) (m : σ →₀ ℕ) : |(gridMoment d m : ℝ)| ≤ (d : ℝ) ^ m.degree := by
  have hfac : ∀ i, 0 ≤ (∑ t ∈ Finset.range (d + 1), (t : ℝ) ^ m i) / ((d : ℝ) + 1) ∧
      (∑ t ∈ Finset.range (d + 1), (t : ℝ) ^ m i) / ((d : ℝ) + 1) ≤ (d : ℝ) ^ m i := by
    intro i
    have hd : (0 : ℝ) < d + 1 := by positivity
    refine ⟨div_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity) hd.le, ?_⟩
    rw [div_le_iff₀ hd]
    calc ∑ t ∈ Finset.range (d + 1), (t : ℝ) ^ m i ≤ ∑ _t ∈ Finset.range (d + 1), (d : ℝ) ^ m i :=
          Finset.sum_le_sum fun t ht ↦ pow_le_pow_left₀ (Nat.cast_nonneg _)
            (by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)) _
      _ = (d : ℝ) ^ m i * (d + 1) := by simp [mul_comm]
  have hcast : (gridMoment d m : ℝ) =
      ∏ i, (∑ t ∈ Finset.range (d + 1), (t : ℝ) ^ m i) / ((d : ℝ) + 1) := by
    simp [gridMoment]
  rw [hcast, abs_of_nonneg (Finset.prod_nonneg fun i _ ↦ (hfac i).1), Finsupp.degree_eq_sum,
    ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ ↦ (hfac i).1) fun i _ ↦ (hfac i).2

/-- A lower bound on the smallest eigenvalue of the grid's moment matrix in degree `2d`, for `n`
variables: `1 / ((n + 1)^d C^(2n) (d + 1)^(2n))`, where `C = SoS.interpBound d`. -/
def gridEig (n d : ℕ) : ℚ :=
  1 / ((n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ (2 * n) : ℕ)

theorem gridEig_pos (n d : ℕ) : 0 < gridEig n d := by
  have : 0 < interpBound d := by unfold interpBound; positivity
  unfold gridEig
  positivity

omit [DecidableEq σ] in
/-- **The grid's moment matrix is well conditioned**: `Ẽ[g²] ≥ λ ‖g‖₂²` for every polynomial `g` of
degree at most `d`, where `Ẽ` is the average over the grid `{0, …, d}^σ` and `λ = SoS.gridEig`. -/
theorem minEigGE_gridMoment (d : ℕ) :
    MinEigGE (riesz fun m ↦ (gridMoment (σ := σ) d m : ℝ)) (2 * d)
      (gridEig (Fintype.card σ) d) := by
  classical
  intro g hg
  have hgd : g.totalDegree ≤ d := by omega
  set n := Fintype.card σ
  have hbound := coeffNorm_sq_le_sum_grid hgd
  rw [riesz_gridMoment_apply]
  simp_rw [eval_mul, ← sq]
  set S := ∑ x : σ → Fin (d + 1), eval (gridPoint x) g ^ 2
  have hC : 0 < interpBound d := by unfold interpBound; positivity
  have hD : (0 : ℝ) < ((d : ℝ) + 1) ^ n := by positivity
  have hK : (0 : ℝ) < (((n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ n : ℕ) : ℝ) := by
    exact_mod_cast (by positivity : 0 < (n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ n)
  have heig : (gridEig n d : ℝ) = 1 /
      ((((n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ n : ℕ) : ℝ) * ((d : ℝ) + 1) ^ n) := by
    simp only [gridEig]
    push_cast
    ring
  rw [heig, le_div_iff₀ hD, div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div,
    div_le_iff₀ (mul_pos hK hD)]
  calc coeffNorm g ^ 2 * ((d : ℝ) + 1) ^ n
      ≤ (((n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ n : ℕ) : ℝ) * S *
          ((d : ℝ) + 1) ^ n := mul_le_mul_of_nonneg_right hbound hD.le
    _ = S * ((((n + 1) ^ d * interpBound d ^ (2 * n) * (d + 1) ^ n : ℕ) : ℝ) *
          ((d : ℝ) + 1) ^ n) := by ring

end SoS
