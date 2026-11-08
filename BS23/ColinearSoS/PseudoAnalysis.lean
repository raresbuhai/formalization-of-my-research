module

public import BS23.ColinearSoS.Bernstein
public import BS23.ColinearSoS.Ratios
public import BS23.ColinearSoS.Frame
public import BS23.ColinearSoS.Poly
public import Background.SumOfSquares.PowerSOS

/-!
# The pseudo-expectation analysis

What the pseudo-expectations found by the sum-of-squares programs of the algorithm for
[BS23, Theorem 1.2] say about the direction of the means, in an abstract setting
(`BS23.ColinearSoS.PseudoHyp`). `Ẽ` has degree `2m` and satisfies the constraint `vᵀDv = 1`
(`D = diag κ`, `1/2 < κᵢ ≤ 2`) up to `η₀` with sum-of-squares multipliers, and
`|Ẽ f| ≤ ‖f‖₁ 258^m` (from the ball `‖v‖² ≤ 256`). The frame: `cw ≻ 0` is `δc`-close to `D`,
`uᵀ cw⁻¹ u = 1`, `G = cw - uuᵀ ⪰ 0`, and the objective `Φ` is within `e` in `‖·‖₁` of the
population moment polynomial `Φ_{2m} = ∑_c w_c hmom (2m) (a_c x) (y + σ² x²)`, where
`x = ⟨u, v⟩` and `y = vᵀGv`, so that `vᵀ cw v = x² + y`. Write `λ_l = Ẽ[x^{2l} y^{m-l}]`,
`β_l = nbeta w a σ² m l` and `M_{2m} = lineMom w a σ² m = β_m`. The error terms are
`errQ = η₀ m (2d + 1)^m`, `errN = 2 (m δc + errQ)`, `errY = 3d² errQ + 2 m δc (1 + errN)` and
`errD = 2 (1 + errN) (2 m δc + γ + 2 e 258^m + errN) + errY` (`BS23.ColinearSoS.PAn.errQ`, …).

* **Normalization** (`BS23.ColinearSoS.PseudoHyp.abs_N_sub_one_le`):
  `N = Ẽ (vᵀ cw v)^m = ∑_l C(m, l) λ_l` has `|N - 1| ≤ errN`. The constraint with the
  multipliers `(vᵀDv)^i` gives `Ẽ[g (vᵀDv)^j] ≈ Ẽ g` for sums of squares `g`
  (`BS23.ColinearSoS.PseudoHyp.abs_E_mul_QD_pow_sub_le`, by telescoping), and
  `(1 - δc)^m (vᵀ cw v)^m ≼ (vᵀDv)^m ≼ (1 + δc)^m (vᵀ cw v)^m` (`SoS.isSumSq_pow_sub_pow`).
* **The defect** (`BS23.ColinearSoS.PseudoHyp.E_G_le_sum`):
  `Ẽ y ≈ Ẽ[y (vᵀDv)^(m-1)] ≲ Ẽ[y (x² + y)^(m-1)] ≤ ∑_{l < m} C(m, l) λ_l`, up to `errY`.
* **The point** `v* = c cw⁻¹ u` with `v*ᵀDv* = 1` (`BS23.ColinearSoS.PseudoHyp.exists_point`) is
  feasible, and `Φ_{2m}(v*) = c^{2m} M_{2m}` since `v*ᵀGv* = 0`; `c^{2m}` is within `2 m δc`
  of `1`.
* **Case U** (`BS23.ColinearSoS.PseudoHyp.defect_le_of_max`): if `M_{2m} ≥ (4m)^m` and `Ẽ` is
  `γ`-optimal for maximizing `Ẽ Φ`, then `Ẽ y ≤ errD`. Indeed
  `Ẽ Φ_{2m} = ∑_l C(m, l) λ_l β_l ≥ (1 - ε) N β_m` while `β_l ≤ β_m / 2` for `l < m`
  (`BS23.ColinearSoS.nbeta_mul_two_pow_le`), so the mass `∑_{l < m} C(m, l) λ_l` is small
  (`BS23.ColinearSoS.select_max`, `BS23.ColinearSoS.PAn.mass_le_of_max`).
* **Case L** (`BS23.ColinearSoS.PseudoHyp.defect_le_of_min`): the same for minimizing, when all
  `a_c² ≤ A²`, `σ² ≤ 1/16` and `m ≥ 5A² + 8` (`BS23.ColinearSoS.two_mul_nbeta_le`,
  `BS23.ColinearSoS.select_min`, `BS23.ColinearSoS.PAn.mass_le_of_min`).
* **The test** for the upper program (`BS23.ColinearSoS.PseudoHyp.lineMom_ge_of_test`,
  `BS23.ColinearSoS.PseudoHyp.lineMom_le_of_test`): `Ẽ Φ ≥ (5m)^m` implies `M_{2m} ≥ (4m)^m`
  (otherwise all `β_l ≤ (4m)^m`), and `Ẽ Φ < (5m)^m` implies `M_{2m} ≤ 3 (5m)^m` (compare with
  `Φ(v*)`).
* **Rounding** (`BS23.ColinearSoS.secondMom`, `BS23.ColinearSoS.PseudoHyp.column_facts`):
  `M = Ẽ[vvᵀ] ⪰ 0`, `tr(GM) = Ẽ y`, `uᵀMu = Ẽ x² = Ẽ[vᵀ cw v] - Ẽ y ≥ 1/2` and
  `tr M = Ẽ ‖v‖² ≥ Ẽ[vᵀDv] / 2 ≥ 1/4`. So for `j` maximizing `M_jj` (then `M_jj ≥ 1/(4d)`) and a
  defect `Ẽ y ≤ δ'` with `δ' ≤ 1/(10⁴ d)`, `δ' ≤ 3σ²/8`, the column `â = M e_j` has
  `âᵀGâ ≤ 3σ² ⟨u, â⟩²` and `⟨u, â⟩ ≠ 0` (`BS23.ColinearSoS.column_perp_le`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open Finset MvPolynomial Matrix SoS Colinear

namespace PAn

variable {d : ℕ}

/-! ### Quadratic-form polynomials -/

/-- `quadPoly` is additive. -/
theorem quadPoly_add (A B : Matrix (Fin d) (Fin d) ℝ) :
    quadPoly (A + B) = quadPoly A + quadPoly B := by
  simp only [quadPoly, ← sum_add_distrib]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by rw [Matrix.add_apply, map_add]; ring

/-- `quadPoly` commutes with subtraction. -/
theorem quadPoly_sub (A B : Matrix (Fin d) (Fin d) ℝ) :
    quadPoly (A - B) = quadPoly A - quadPoly B := by
  simp only [quadPoly, ← sum_sub_distrib]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by rw [Matrix.sub_apply, map_sub]; ring

/-- `quadPoly (c • A) = c · quadPoly A`. -/
theorem quadPoly_smul (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) :
    quadPoly (c • A) = C c * quadPoly A := by
  simp only [quadPoly, mul_sum]
  exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by
    rw [Matrix.smul_apply, smul_eq_mul, map_mul]; ring

/-- `quadPoly 0 = 0`. -/
theorem quadPoly_zero : quadPoly (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  simp [quadPoly]

/-- `quadPoly` commutes with finite sums. -/
theorem quadPoly_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℝ) :
    quadPoly (∑ i ∈ s, A i) = ∑ i ∈ s, quadPoly (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [quadPoly_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, quadPoly_add, ih]

/-- `vᵀ (abᵀ) v = ⟨a, v⟩⟨b, v⟩` as polynomials. -/
theorem quadPoly_vecMulVec (a b : Fin d → ℝ) :
    quadPoly (vecMulVec a b) = Separating.lin a * Separating.lin b := by
  rw [quadPoly, Separating.lin, Separating.lin, sum_mul]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [mul_sum]
  exact sum_congr rfl fun j _ ↦ by rw [vecMulVec_apply, map_mul]; ring

/-- `vᵀ diag(κ) v = ∑ᵢ κᵢ vᵢ²` as polynomials. -/
theorem quadPoly_diagonal (κ : Fin d → ℝ) :
    quadPoly (diagonal κ) = ∑ i, C (κ i) * X i ^ 2 := by
  simp [quadPoly, diagonal_apply, sq, mul_assoc, apply_ite C, ite_mul]

/-- A quadratic form has degree at most `2`. -/
theorem totalDegree_quadPoly_le (S : Matrix (Fin d) (Fin d) ℝ) :
    (quadPoly S).totalDegree ≤ 2 := by
  refine totalDegree_finsetSum_le fun a _ ↦ totalDegree_finsetSum_le fun b _ ↦ ?_
  refine (totalDegree_mul _ _).trans ?_
  refine (add_le_add ((totalDegree_mul _ _).trans (add_le_add (totalDegree_C _).le
    (totalDegree_X a).le)) (totalDegree_X b).le).trans ?_
  norm_num

/-- A linear form has degree at most `1`. -/
theorem totalDegree_lin_le (u : Fin d → ℝ) : (Separating.lin u).totalDegree ≤ 1 :=
  (Separating.isHomogeneous_lin u).totalDegree_le

/-- `‖vᵀSv‖₁ ≤ ∑_{a,b} |S_ab|`. -/
theorem coeffNorm1_quadPoly_le (S : Matrix (Fin d) (Fin d) ℝ) :
    coeffNorm1 (quadPoly S) ≤ ∑ a, ∑ b, |S a b| := by
  refine (coeffNorm1_sum_le _ _).trans (sum_le_sum fun a _ ↦ (coeffNorm1_sum_le _ _).trans
    (sum_le_sum fun b _ ↦ ?_))
  rw [mul_assoc, coeffNorm1_C_mul]
  have h1 : coeffNorm1 (X a * X b : MvPolynomial (Fin d) ℝ) ≤ 1 :=
    (coeffNorm1_mul_le _ _).trans (by rw [coeffNorm1_X, coeffNorm1_X, one_mul])
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-- The quadratic-form polynomial of a positive semidefinite matrix is a sum of squares. -/
theorem isSumSq_quadPoly {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosSemidef) :
    IsSumSq (quadPoly S) := by
  obtain ⟨n, b, rfl⟩ := Rounding.exists_eq_sum_vecMulVec hS
  rw [quadPoly_sum]
  exact IsSumSq.sum fun i _ ↦ by rw [quadPoly_vecMulVec]; exact IsSumSq.mul_self _

/-- A symmetric matrix with nonnegative quadratic form is positive semidefinite. -/
theorem posSemidef_of_quad_nonneg {S : Matrix (Fin d) (Fin d) ℝ} (hS : Sᵀ = S)
    (h : ∀ v, 0 ≤ quad S v) : S.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hS]
  · rw [star_trivial]
    exact h x

/-- Comparison of quadratic forms of symmetric matrices as a sum-of-squares certificate. -/
theorem isSumSq_quadPoly_sub {A B : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (hB : Bᵀ = B)
    (h : ∀ v, quad A v ≤ quad B v) : IsSumSq (quadPoly B - quadPoly A) := by
  rw [← quadPoly_sub]
  refine isSumSq_quadPoly (posSemidef_of_quad_nonneg (by rw [transpose_sub, hA, hB]) fun v ↦ ?_)
  rw [quad_sub_apply]
  linarith [h v]

/-- `vᵀ (cA) v = c vᵀAv`. -/
theorem quad_smul_matrix (c : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    quad (c • A) v = c * quad A v := by
  simp [quad, smul_mulVec, dotProduct_smul]

/-- `vᵀ diag(κ) v = ∑ᵢ κᵢ vᵢ²`. -/
theorem quad_diagonal (κ : Fin d → ℝ) (v : Fin d → ℝ) :
    quad (diagonal κ) v = ∑ i, κ i * v i ^ 2 := by
  simp only [quad, mulVec_diagonal, dotProduct]
  exact sum_congr rfl fun i _ ↦ by ring

/-! ### Degrees of the moment polynomials -/

/-- `hmom r A V` has degree at most `r` when `deg A ≤ 1` and `deg V ≤ 2`. -/
theorem totalDegree_hmom_le {σ : Type*} {A V : MvPolynomial σ ℝ} (hA : A.totalDegree ≤ 1)
    (hV : V.totalDegree ≤ 2) (r : ℕ) : (hmom r A V).totalDegree ≤ r := by
  unfold hmom
  refine totalDegree_finsetSum_le fun i hi ↦ ?_
  have hi : i ≤ r / 2 := Nat.lt_succ_iff.1 (mem_range.1 hi)
  refine (totalDegree_mul _ _).trans ?_
  refine (add_le_add ((totalDegree_mul _ _).trans (add_le_add_right
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hA)) _))
    ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hV))).trans ?_
  rw [← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), totalDegree_C]
  omega

/-- The population moment polynomial of order `r` has degree at most `r`. -/
theorem totalDegree_popPoly_le {k : ℕ} (w a : Fin k → ℝ) (u : Fin d → ℝ)
    (S : Matrix (Fin d) (Fin d) ℝ) (r : ℕ) : (popPoly w a u S r).totalDegree ≤ r := by
  refine totalDegree_finsetSum_le fun c _ ↦ (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine totalDegree_hmom_le ((totalDegree_mul _ _).trans ?_) (totalDegree_quadPoly_le S) r
  rw [totalDegree_C, zero_add]
  exact totalDegree_lin_le u

/-! ### Elementary inequalities -/

/-- With `n δ ≤ 1/2`: `1 - nδ ≤ (1 - δ)^n`, `(1 + δ)^n ≤ 1 + 2nδ` and
`(1 - δ)^(-n) ≤ 1 + 2nδ`. -/
theorem pow_bounds {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {n : ℕ} (h : n * δ ≤ 1 / 2) :
    1 - n * δ ≤ (1 - δ) ^ n ∧ (1 + δ) ^ n ≤ 1 + 2 * n * δ ∧
      ((1 - δ) ^ n)⁻¹ ≤ 1 + 2 * n * δ := by
  have hB : 1 - n * δ ≤ (1 - δ) ^ n := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) n
    rw [← sub_eq_add_neg] at this
    linarith
  have hpos : 0 < 1 - n * δ := by linarith
  have hP : 0 < (1 - δ) ^ n := hpos.trans_le hB
  have hinv : ((1 - δ) ^ n)⁻¹ ≤ 1 + 2 * n * δ := by
    rw [inv_le_iff_one_le_mul₀ hP]
    have hx : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) h0
    calc (1 : ℝ) ≤ (1 + 2 * n * δ) * (1 - n * δ) := by nlinarith
      _ ≤ (1 + 2 * n * δ) * (1 - δ) ^ n := mul_le_mul_of_nonneg_left hB (by positivity)
  refine ⟨hB, ?_, hinv⟩
  have hprod : (1 + δ) ^ n * (1 - δ) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  calc (1 + δ) ^ n = (1 + δ) ^ n * (1 - δ) ^ n * ((1 - δ) ^ n)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hP.ne', mul_one]
    _ ≤ 1 * ((1 - δ) ^ n)⁻¹ := mul_le_mul_of_nonneg_right hprod (inv_nonneg.2 hP.le)
    _ ≤ 1 + 2 * n * δ := by rw [one_mul]; exact hinv

/-- `(1 + x)⁻¹ ≥ 1 - x` for `x ≥ 0`. -/
theorem one_sub_le_inv {x : ℝ} (hx : 0 ≤ x) : 1 - x ≤ (1 + x)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- Monotonicity of a pseudo-expectation along a sum-of-squares certificate. -/
theorem apply_le_apply {σ : Type*} {ℓ : ℕ} (E : PseudoExpectation σ ℓ) {f g : MvPolynomial σ ℝ}
    (hfg : IsSumSq (g - f)) (hdeg : (g - f).totalDegree ≤ ℓ) : E f ≤ E g := by
  have := E.nonneg_of_isSumSq hfg hdeg
  rw [E.map_sub] at this
  linarith

/-- `eᵢᵀ S eⱼ = S i j`. -/
theorem single_dotProduct_mulVec_single (S : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    (Pi.single i 1 : Fin d → ℝ) ⬝ᵥ (S *ᵥ Pi.single j 1) = S i j := by
  rw [single_one_dotProduct, mulVec_single_one, col_apply]

/-- `c vᵀSv` has degree at most `2`. -/
theorem totalDegree_C_mul_quadPoly_le (c : ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    (C c * quadPoly S).totalDegree ≤ 2 :=
  (totalDegree_mul _ _).trans (by rw [totalDegree_C, zero_add]; exact totalDegree_quadPoly_le S)

/-- `vᵀ (S - uuᵀ) v = vᵀSv - ⟨u, v⟩²`. -/
theorem quad_sub_vecMulVec (S : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) :
    quad (S - vecMulVec u u) v = quad S v - (u ⬝ᵥ v) ^ 2 := by
  rw [quad_sub_apply, Fr.quad_vecMulVec]

/-- `vᵀ S v = ⟨u, v⟩² + vᵀ (S - uuᵀ) v` as polynomials. -/
theorem quadPoly_eq_sq_add (S : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) :
    quadPoly S = Separating.lin u ^ 2 + quadPoly (S - vecMulVec u u) := by
  rw [quadPoly_sub, quadPoly_vecMulVec]
  ring

/-- `T^j - S^j` has degree at most `2j` when `S`, `T` have degree at most `2`. -/
theorem totalDegree_pow_sub_pow_le' {S T : MvPolynomial (Fin d) ℝ} (hS : S.totalDegree ≤ 2)
    (hT : T.totalDegree ≤ 2) (j : ℕ) : (T ^ j - S ^ j).totalDegree ≤ 2 * j :=
  (totalDegree_pow_sub_pow_le S T j).trans (by
    have := Nat.mul_le_mul_left j (max_le hS hT); omega)

/-! ### The selection arithmetic -/

/-- `∑_{l < m} C(m, l) λ_l ≤ ∑_{l ≤ m} C(m, l) λ_l` for `λ ≥ 0`. -/
theorem sum_range_le_sum_range_succ {m : ℕ} {lam : ℕ → ℝ} (hlam : ∀ l ≤ m, 0 ≤ lam l) :
    ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤ ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l := by
  rw [sum_range_succ]
  have := mul_nonneg (Nat.cast_nonneg (m.choose m) : (0 : ℝ) ≤ _) (hlam m le_rfl)
  linarith

/-- `∑_{l ≤ m} C(m, l) λ_l ≥ 0` for `λ ≥ 0`. -/
theorem sum_choose_mul_nonneg {m : ℕ} {lam : ℕ → ℝ} (hlam : ∀ l ≤ m, 0 ≤ lam l) :
    0 ≤ ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l :=
  sum_nonneg fun l hl ↦ mul_nonneg (Nat.cast_nonneg _)
    (hlam l (Nat.lt_succ_iff.1 (mem_range.1 hl)))

/-- **The arithmetic of the upper program.** With `N = ∑_l C(m, l) λ_l ≤ 1 + ε_N`, `β_m ≥ 1`,
`β_l ≤ β_m / 2` for `l < m` and `∑_l C(m, l) λ_l β_l ≥ t β_m - err` with `t ≥ 1 - x`, the mass
`∑_{l < m} C(m, l) λ_l` is at most `2 (1 + ε_N) (x + err + ε_N)`. -/
theorem mass_le_of_max {m : ℕ} {lam β : ℕ → ℝ} (hlam : ∀ l ≤ m, 0 ≤ lam l) (hβm : 1 ≤ β m)
    (hβ : ∀ l < m, β l ≤ β m / 2) {t x err εN : ℝ} (hx : 0 ≤ x) (herr : 0 ≤ err)
    (hεN : 0 ≤ εN) (hN : ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l ≤ 1 + εN)
    (ht : 1 - x ≤ t)
    (hmain : t * β m - err ≤ ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l * β l) :
    ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤ 2 * (1 + εN) * (x + err + εN) := by
  have hN0 := sum_choose_mul_nonneg hlam
  have hsub := sum_range_le_sum_range_succ hlam
  set N := ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l with hNdef
  set ε := x + err + εN with hε
  have hε0 : 0 ≤ ε := by linarith
  have key : ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤ 2 * ε * N := by
    by_cases h1 : ε ≤ 1
    · refine select_max (fun l hl ↦ hlam l hl.le) (by linarith) hβ ?_
      have A0 := mul_le_mul_of_nonneg_left hN (by linarith : 0 ≤ 1 - ε)
      have A1 := mul_nonneg hε0 hεN
      have A : (1 - ε) * N ≤ 1 - x - err := by linarith
      have B := mul_le_mul_of_nonneg_right A (by linarith : 0 ≤ β m)
      have C1 := mul_le_mul_of_nonneg_right ht (by linarith : 0 ≤ β m)
      have C2 : err ≤ err * β m := le_mul_of_one_le_right herr hβm
      linarith
    · push Not at h1
      have := mul_le_mul_of_nonneg_right h1.le hN0
      linarith
  calc _ ≤ 2 * ε * N := key
    _ ≤ 2 * ε * (1 + εN) := mul_le_mul_of_nonneg_left hN (by positivity)
    _ = _ := by rw [hε]; ring

/-- **The arithmetic of the lower program.** With `1 - ε_N ≤ N ≤ 1 + ε_N`, `β_m ≥ 1`,
`β_l ≥ 2 β_m` for `l < m` and `∑_l C(m, l) λ_l β_l ≤ t β_m + err` with `t ≤ 1 + x`, the mass
`∑_{l < m} C(m, l) λ_l` is at most `2 (1 + ε_N) (x + err + ε_N)`. -/
theorem mass_le_of_min {m : ℕ} {lam β : ℕ → ℝ} (hlam : ∀ l ≤ m, 0 ≤ lam l) (hβm : 1 ≤ β m)
    (hβ : ∀ l < m, 2 * β m ≤ β l) {t x err εN : ℝ} (hx : 0 ≤ x) (herr : 0 ≤ err)
    (hεN : 0 ≤ εN) (hN1 : 1 - εN ≤ ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l)
    (hN2 : ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l ≤ 1 + εN) (ht : t ≤ 1 + x)
    (hmain : ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l * β l ≤ t * β m + err) :
    ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤ 2 * (1 + εN) * (x + err + εN) := by
  have hN0 := sum_choose_mul_nonneg hlam
  have hsub := sum_range_le_sum_range_succ hlam
  set N := ∑ l ∈ range (m + 1), (m.choose l : ℝ) * lam l with hNdef
  set ε := 2 * (x + err + εN) with hε
  have hε0 : 0 ≤ ε := by linarith
  have key : ∑ l ∈ range m, (m.choose l : ℝ) * lam l ≤ ε * N := by
    by_cases h1 : εN ≤ 1 / 2
    · refine select_min (fun l hl ↦ hlam l hl.le) (by linarith) hβ ?_
      have A0 := mul_le_mul_of_nonneg_left hN1 (by linarith : 0 ≤ 1 + ε)
      have A1 := mul_le_mul_of_nonneg_left h1 hε0
      have A : 1 + x + err ≤ (1 + ε) * N := by linarith
      have B := mul_le_mul_of_nonneg_right A (by linarith : 0 ≤ β m)
      have C1 := mul_le_mul_of_nonneg_right ht (by linarith : 0 ≤ β m)
      have C2 : err ≤ err * β m := le_mul_of_one_le_right herr hβm
      linarith
    · push Not at h1
      have := mul_le_mul_of_nonneg_right (show 1 ≤ ε by linarith) hN0
      linarith
  calc _ ≤ ε * N := key
    _ ≤ ε * (1 + εN) := mul_le_mul_of_nonneg_left hN2 hε0
    _ = _ := by rw [hε]; ring

/-! ### The error terms -/

/-- The error of the equality constraint `vᵀDv = 1` after multiplying by `(vᵀDv)^i`, `i ≤ m`:
`η₀ m (2d + 1)^m`. -/
noncomputable def errQ (η₀ : ℝ) (m d : ℕ) : ℝ := η₀ * m * (2 * d + 1) ^ m

/-- The error of the normalization `Ẽ (vᵀ cw v)^m ≈ 1`: `2 (m δc + errQ)`. -/
noncomputable def errN (η₀ δc : ℝ) (m d : ℕ) : ℝ := 2 * (m * δc + errQ η₀ m d)

/-- The error in `Ẽ[vᵀGv] ≤ Ẽ[vᵀGv (vᵀ cw v)^(m-1)] + errY`: `3 d² errQ + 2 m δc (1 + errN)`. -/
noncomputable def errY (η₀ δc : ℝ) (m d : ℕ) : ℝ :=
  3 * d ^ 2 * errQ η₀ m d + 2 * m * δc * (1 + errN η₀ δc m d)

/-- The bound on the defect `Ẽ[vᵀGv]` in both programs:
`2 (1 + errN) (2 m δc + γ + 2 e 258^m + errN) + errY`. -/
noncomputable def errD (η₀ δc e γ : ℝ) (m d : ℕ) : ℝ :=
  2 * (1 + errN η₀ δc m d) * (2 * m * δc + γ + 2 * e * 258 ^ m + errN η₀ δc m d) +
    errY η₀ δc m d

end PAn

open PAn

/-! ### The pseudo-moment matrix -/

/-- The pseudo-moment matrix `Ẽ[vvᵀ]`, with entries `Ẽ[vᵢ vⱼ]`. -/
noncomputable def secondMom {d ℓ : ℕ} (E : PseudoExpectation (Fin d) ℓ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j ↦ E (X i * X j)

section SecondMom

variable {d ℓ : ℕ} (E : PseudoExpectation (Fin d) ℓ)

/-- The entries `Ẽ[vᵢ vⱼ]`. -/
theorem secondMom_apply (i j : Fin d) : secondMom E i j = E (X i * X j) := rfl

/-- `tr(S Ẽ[vvᵀ]) = Ẽ[vᵀSv]`. -/
theorem trace_mul_secondMom (S : Matrix (Fin d) (Fin d) ℝ) :
    (S * secondMom E).trace = E (quadPoly S) := by
  rw [Matrix.trace, quadPoly, E.map_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, E.map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [secondMom_apply, mul_assoc, E.map_C_mul, mul_comm (X j) (X i)]

/-- `xᵀ Ẽ[vvᵀ] y = Ẽ[⟨x, v⟩⟨y, v⟩]`. -/
theorem dotProduct_secondMom_mulVec (x y : Fin d → ℝ) :
    x ⬝ᵥ (secondMom E *ᵥ y) = E (Separating.lin x * Separating.lin y) := by
  rw [Separating.lin, Separating.lin, sum_mul, E.map_sum, dotProduct]
  refine sum_congr rfl fun i _ ↦ ?_
  simp only [mulVec, dotProduct, mul_sum, E.map_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [secondMom_apply, show C (x i) * X i * (C (y j) * X j) = C (x i * y j) * (X i * X j) by
    rw [C_mul]; ring, E.map_C_mul]
  ring

/-- `Ẽ[vvᵀ]` is positive semidefinite. -/
theorem secondMom_posSemidef (hℓ : 2 ≤ ℓ) : (secondMom E).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x ↦ ?_
  · exact IsHermitian.ext fun i j ↦ by rw [star_trivial, secondMom_apply, secondMom_apply, mul_comm]
  · rw [star_trivial, dotProduct_secondMom_mulVec]
    exact E.map_mul_self_nonneg ((Nat.mul_le_mul_left 2 (totalDegree_lin_le x)).trans hℓ)

/-- `tr Ẽ[vvᵀ] = Ẽ ‖v‖²`. -/
theorem sum_secondMom_diag : ∑ i, secondMom E i i = E (quadPoly 1) := by
  rw [← trace_mul_secondMom, one_mul]
  rfl

end SecondMom

/-! ### The hypotheses -/

/-- **The setting of the pseudo-expectation analysis** for [BS23, Theorem 1.2], abstracted from
the algorithm and the sample. `E` is a pseudo-expectation of degree `2m` on polynomials in the
direction `v ∈ ℝ^d`, `D = diag κ` with `1/2 < κᵢ ≤ 2`, and:
* `E` satisfies the equality constraint `vᵀDv = 1` up to `η₀` against every sum-of-squares
  multiplier, measured by coefficient norms (two-sided), and `|Ẽ f| ≤ ‖f‖₁ 258^m` for
  `deg f ≤ 2m` (from the ball constraint);
* the frame: `cw ≻ 0`, `uᵀ cw⁻¹ u = 1`, `G = cw - uuᵀ`, the one-dimensional mixture
  `∑_c w_c N(a_c, σ²)` of variance `1`, and the noise form `vᵀ SWq v = vᵀGv + σ² ⟨u, v⟩²`;
* `cw` and `D` are close: `(1 - δc) vᵀ cw v ≤ vᵀDv ≤ (1 + δc) vᵀ cw v` with `0 ≤ δc ≤ 1/(8m)`;
* `Φ` (the empirical moment polynomial) has degree at most `2m` and is within `e`, in `‖·‖₁`, of
  the population moment polynomial `popPoly w a u SWq (2m)`. -/
structure PseudoHyp {k d m : ℕ} (E : PseudoExpectation (Fin d) (2 * m)) (κ : Fin d → ℝ)
    (cw : Matrix (Fin d) (Fin d) ℝ) (u : Fin d → ℝ) (w a : Fin k → ℝ) (σ2 : ℝ)
    (SWq : Matrix (Fin d) (Fin d) ℝ) (Φ : MvPolynomial (Fin d) ℝ) (η₀ δc e : ℝ) : Prop where
  one_le_m : 1 ≤ m
  kappa_gt : ∀ i, 1 / 2 < κ i
  kappa_le : ∀ i, κ i ≤ 2
  eta_nonneg : 0 ≤ η₀
  eq_approx : ∀ g : MvPolynomial (Fin d) ℝ, IsSumSq g → g.totalDegree + 2 ≤ 2 * m →
    |E (g * (quadPoly (diagonal κ) - 1))| ≤
      η₀ * coeffNorm g * coeffNorm (quadPoly (diagonal κ) - 1)
  abs_E_le : ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ 2 * m →
    |E f| ≤ coeffNorm1 f * 258 ^ m
  cw_posDef : cw.PosDef
  u_cw_inv : u ⬝ᵥ (cw⁻¹ *ᵥ u) = 1
  w_nonneg : ∀ c, 0 ≤ w c
  sum_w : ∑ c, w c = 1
  sigma_nonneg : 0 ≤ σ2
  var_eq : ∑ c, w c * a c ^ 2 + σ2 = 1
  quad_SWq : ∀ v, quad SWq v = quad (cw - vecMulVec u u) v + σ2 * (u ⬝ᵥ v) ^ 2
  cmp_lower : ∀ v, (1 - δc) * quad cw v ≤ quad (diagonal κ) v
  cmp_upper : ∀ v, quad (diagonal κ) v ≤ (1 + δc) * quad cw v
  delta_nonneg : 0 ≤ δc
  delta_le : δc ≤ 1 / (8 * m)
  totalDegree_Phi_le : Φ.totalDegree ≤ 2 * m
  Phi_close : coeffNorm1 (Φ - popPoly w a u SWq (2 * m)) ≤ e

namespace PseudoHyp

variable {k d m : ℕ} {E : PseudoExpectation (Fin d) (2 * m)} {κ : Fin d → ℝ}
  {cw : Matrix (Fin d) (Fin d) ℝ} {u : Fin d → ℝ} {w a : Fin k → ℝ} {σ2 : ℝ}
  {SWq : Matrix (Fin d) (Fin d) ℝ} {Φ : MvPolynomial (Fin d) ℝ} {η₀ δc e : ℝ}
  (h : PseudoHyp E κ cw u w a σ2 SWq Φ η₀ δc e)
include h

/-! #### Basic consequences -/

/-- `m > 0`. -/
theorem m_pos : (0 : ℝ) < m := by exact_mod_cast h.one_le_m

/-- `m δc ≤ 1/8`. -/
theorem mdelta_le : (m : ℝ) * δc ≤ 1 / 8 := by
  have h1 := h.delta_le
  rw [le_div_iff₀ (by linarith [h.m_pos])] at h1
  linarith

/-- `δc ≤ 1/8`. -/
theorem delta_le_eighth : δc ≤ 1 / 8 :=
  (le_mul_of_one_le_left h.delta_nonneg (by exact_mod_cast h.one_le_m)).trans h.mdelta_le

/-- `e ≥ 0`. -/
theorem e_nonneg : 0 ≤ e := (coeffNorm1_nonneg _).trans h.Phi_close

/-- `errQ ≥ 0`. -/
theorem errQ_nonneg : 0 ≤ errQ η₀ m d := by
  unfold errQ
  have := h.eta_nonneg
  positivity

/-- `errN ≥ 0`. -/
theorem errN_nonneg : 0 ≤ errN η₀ δc m d := by
  unfold errN
  have := h.errQ_nonneg
  have := h.delta_nonneg
  positivity

/-- `cw` is symmetric. -/
theorem cw_transpose : cwᵀ = cw := transpose_eq_of_posDef h.cw_posDef

/-- `vᵀGv ≥ 0` (Cauchy–Schwarz for `cw`, with `uᵀ cw⁻¹ u = 1`). -/
theorem quad_G_nonneg (v : Fin d → ℝ) : 0 ≤ quad (cw - vecMulVec u u) v := by
  have h1 := sq_dotProduct_le_quad_mul h.cw_posDef v u
  rw [h.u_cw_inv, mul_one, dotProduct_comm v u] at h1
  rw [quad_sub_vecMulVec]
  linarith

/-- `G = cw - uuᵀ ⪰ 0`. -/
theorem G_posSemidef : (cw - vecMulVec u u).PosSemidef :=
  posSemidef_of_quad_nonneg (by rw [transpose_sub, h.cw_transpose, transpose_vecMulVec])
    h.quad_G_nonneg

/-- `vᵀ cw v` is a sum of squares. -/
theorem isSumSq_cw : IsSumSq (quadPoly cw) := isSumSq_quadPoly h.cw_posDef.posSemidef

/-- `vᵀGv` is a sum of squares. -/
theorem isSumSq_G : IsSumSq (quadPoly (cw - vecMulVec u u)) := isSumSq_quadPoly h.G_posSemidef

/-- `vᵀDv` is a sum of squares. -/
theorem isSumSq_QD : IsSumSq (quadPoly (diagonal κ)) := by
  refine isSumSq_quadPoly (posSemidef_of_quad_nonneg (diagonal_transpose κ) fun v ↦ ?_)
  rw [quad_diagonal]
  exact sum_nonneg fun i _ ↦ mul_nonneg (by linarith [h.kappa_gt i]) (sq_nonneg _)

/-- `vᵀ SWq v = vᵀGv + σ² ⟨u, v⟩²` as polynomials. -/
theorem quadPoly_SWq :
    quadPoly SWq = quadPoly (cw - vecMulVec u u) + C σ2 * Separating.lin u ^ 2 := by
  refine MvPolynomial.funext fun v ↦ ?_
  simp only [eval_quadPoly, map_add, map_mul, eval_C, map_pow, eval_lin, h.quad_SWq]

/-- The population polynomial in the form of the moment equality. -/
theorem popPoly_eq : popPoly w a u SWq (2 * m) =
    ∑ c, C (w c) * hmom (2 * m) (C (a c) * Separating.lin u)
      (quadPoly (cw - vecMulVec u u) + C σ2 * Separating.lin u ^ 2) := by
  rw [popPoly, h.quadPoly_SWq]

/-- `Ẽ Φ_{2m} = ∑_l C(m, l) λ_l β_l`. -/
theorem E_popPoly : E (popPoly w a u SWq (2 * m)) =
    ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
      E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) *
        nbeta w a σ2 m l := by
  rw [h.popPoly_eq, apply_sum_hmom']

omit h in
/-- `N = Ẽ (vᵀ cw v)^m = ∑_l C(m, l) λ_l`. -/
theorem E_cw_pow : E (quadPoly cw ^ m) =
    ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
      E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) := by
  rw [quadPoly_eq_sq_add cw u, apply_add_sq_pow]

/-- `λ_l = Ẽ[⟨u, v⟩^{2l} (vᵀGv)^{m-l}] ≥ 0`. -/
theorem lam_nonneg' {l : ℕ} (hl : l ≤ m) :
    0 ≤ E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) :=
  lam_nonneg E (totalDegree_lin_le u) h.isSumSq_G (totalDegree_quadPoly_le _) le_rfl hl

/-- `N ≥ 0`. -/
theorem E_cw_pow_nonneg : 0 ≤ E (quadPoly cw ^ m) := by
  refine E.nonneg_of_isSumSq (isSumSq_pow h.isSumSq_cw m) ?_
  exact (totalDegree_pow _ _).trans (by
    have := Nat.mul_le_mul_left m (totalDegree_quadPoly_le cw); omega)

/-! #### Comparison of `cw` and `D` -/

/-- `(1 - δc) vᵀ cw v ≼ vᵀDv`. -/
theorem isSumSq_QD_sub : IsSumSq (quadPoly (diagonal κ) - C (1 - δc) * quadPoly cw) := by
  rw [← quadPoly_smul]
  refine isSumSq_quadPoly_sub (by rw [transpose_smul, h.cw_transpose]) (diagonal_transpose κ)
    fun v ↦ ?_
  rw [quad_smul_matrix]
  exact h.cmp_lower v

/-- `vᵀDv ≼ (1 + δc) vᵀ cw v`. -/
theorem isSumSq_sub_QD : IsSumSq (C (1 + δc) * quadPoly cw - quadPoly (diagonal κ)) := by
  rw [← quadPoly_smul]
  refine isSumSq_quadPoly_sub (diagonal_transpose κ) (by rw [transpose_smul, h.cw_transpose])
    fun v ↦ ?_
  rw [quad_smul_matrix]
  exact h.cmp_upper v

/-- `(1 - δc)^m N ≤ Ẽ (vᵀDv)^m`. -/
theorem E_QD_pow_ge :
    (1 - δc) ^ m * E (quadPoly cw ^ m) ≤ E (quadPoly (diagonal κ) ^ m) := by
  have hX : IsSumSq (C (1 - δc) * quadPoly cw) :=
    isSumSq_C_mul (by linarith [h.delta_le_eighth]) h.isSumSq_cw
  have h2 := apply_le_apply E (isSumSq_pow_sub_pow hX h.isSumSq_QD_sub m)
    (totalDegree_pow_sub_pow_le' (totalDegree_C_mul_quadPoly_le _ _) (totalDegree_quadPoly_le _) m)
  rwa [mul_pow, ← C_pow, E.map_C_mul] at h2

/-- `Ẽ (vᵀDv)^m ≤ (1 + δc)^m N`. -/
theorem E_QD_pow_le :
    E (quadPoly (diagonal κ) ^ m) ≤ (1 + δc) ^ m * E (quadPoly cw ^ m) := by
  have h2 := apply_le_apply E (isSumSq_pow_sub_pow h.isSumSq_QD h.isSumSq_sub_QD m)
    (totalDegree_pow_sub_pow_le' (totalDegree_quadPoly_le _) (totalDegree_C_mul_quadPoly_le _ _) m)
  rwa [mul_pow, ← C_pow, E.map_C_mul] at h2

/-- `Ẽ[vᵀGv (vᵀDv)^(m-1)] ≤ (1 + δc)^(m-1) Ẽ[vᵀGv (vᵀ cw v)^(m-1)]`. -/
theorem E_G_mul_QD_pow_le :
    E (quadPoly (cw - vecMulVec u u) * quadPoly (diagonal κ) ^ (m - 1)) ≤
      (1 + δc) ^ (m - 1) * E (quadPoly (cw - vecMulVec u u) * quadPoly cw ^ (m - 1)) := by
  have hs := h.isSumSq_G.mul (isSumSq_pow_sub_pow h.isSumSq_QD h.isSumSq_sub_QD (m - 1))
  have hd := totalDegree_pow_sub_pow_le' (totalDegree_quadPoly_le (diagonal κ))
    (totalDegree_C_mul_quadPoly_le (1 + δc) cw) (m - 1)
  have h2 := apply_le_apply E (f := quadPoly (cw - vecMulVec u u) *
    quadPoly (diagonal κ) ^ (m - 1)) (g := quadPoly (cw - vecMulVec u u) *
      (C (1 + δc) * quadPoly cw) ^ (m - 1)) (by rw [← mul_sub]; exact hs) (by
        rw [← mul_sub]
        refine (totalDegree_mul _ _).trans ?_
        have := totalDegree_quadPoly_le (cw - vecMulVec u u)
        have := h.one_le_m
        omega)
  rwa [mul_pow, ← C_pow, mul_left_comm, E.map_C_mul] at h2

/-- `Ẽ[vᵀGv (vᵀ cw v)^(m-1)] ≤ N`. -/
theorem E_G_mul_cw_pow_le :
    E (quadPoly (cw - vecMulVec u u) * quadPoly cw ^ (m - 1)) ≤ E (quadPoly cw ^ m) := by
  have hm := h.one_le_m
  have e1 : quadPoly cw ^ m - quadPoly (cw - vecMulVec u u) * quadPoly cw ^ (m - 1) =
      Separating.lin u ^ 2 * quadPoly cw ^ (m - 1) := by
    have e0 : quadPoly cw ^ m = quadPoly cw ^ (m - 1) * quadPoly cw := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    rw [e0]
    generalize quadPoly cw ^ (m - 1) = P
    rw [quadPoly_eq_sq_add cw u]
    ring
  refine apply_le_apply E ?_ ?_
  · rw [e1]
    exact (isSumSq_sq _).mul (isSumSq_pow h.isSumSq_cw _)
  · rw [e1]
    refine (totalDegree_mul _ _).trans ?_
    have h1 := (totalDegree_pow (Separating.lin u) 2).trans
      (Nat.mul_le_mul_left 2 (totalDegree_lin_le u))
    have h2 := (totalDegree_pow (quadPoly cw) (m - 1)).trans
      (Nat.mul_le_mul_left (m - 1) (totalDegree_quadPoly_le cw))
    omega

/-- `Ẽ[vᵀGv (vᵀ cw v)^(m-1)] ≥ 0`. -/
theorem E_G_mul_cw_pow_nonneg :
    0 ≤ E (quadPoly (cw - vecMulVec u u) * quadPoly cw ^ (m - 1)) := by
  refine E.nonneg_of_isSumSq (h.isSumSq_G.mul (isSumSq_pow h.isSumSq_cw _)) ?_
  refine (totalDegree_mul _ _).trans ?_
  have h1 := totalDegree_quadPoly_le (cw - vecMulVec u u)
  have h2 := (totalDegree_pow (quadPoly cw) (m - 1)).trans
    (Nat.mul_le_mul_left (m - 1) (totalDegree_quadPoly_le cw))
  have := h.one_le_m
  omega

/-! #### The equality constraint with sum-of-squares multipliers -/

/-- `‖vᵀDv‖₁ ≤ 2d`. -/
theorem coeffNorm1_QD_le : coeffNorm1 (quadPoly (diagonal κ)) ≤ 2 * d := by
  rw [quadPoly_diagonal]
  refine (coeffNorm1_sum_le _ _).trans ?_
  calc ∑ i, coeffNorm1 (C (κ i) * X i ^ 2) ≤ ∑ _i : Fin d, (2 : ℝ) := sum_le_sum fun i _ ↦ by
        rw [coeffNorm1_C_mul]
        have h1 : coeffNorm1 (X i ^ 2 : MvPolynomial (Fin d) ℝ) ≤ 1 :=
          (coeffNorm1_pow_le _ _).trans (by rw [coeffNorm1_X, one_pow])
        have h2 : |κ i| ≤ 2 := abs_le.2 ⟨by linarith [h.kappa_gt i], h.kappa_le i⟩
        nlinarith [abs_nonneg (κ i), coeffNorm1_nonneg (X i ^ 2 : MvPolynomial (Fin d) ℝ)]
    _ = 2 * d := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

/-- `‖vᵀDv - 1‖₂ ≤ 2d + 1`. -/
theorem coeffNorm_QD_sub_one_le : coeffNorm (quadPoly (diagonal κ) - 1) ≤ 2 * d + 1 :=
  (coeffNorm_le_coeffNorm1 _).trans ((coeffNorm1_sub_le _ _).trans (by
    rw [coeffNorm1_one]; linarith [h.coeffNorm1_QD_le]))

/-- **The equality constraint with multipliers `(vᵀDv)^i`**: for a sum of squares `g` with
`deg g + 2j ≤ 2m`, `|Ẽ[g (vᵀDv)^j] - Ẽ g| ≤ η₀ j ‖g‖₁ (2d + 1)^j` (telescoping). -/
theorem abs_E_mul_QD_pow_sub_le {g : MvPolynomial (Fin d) ℝ} (hg : IsSumSq g) {j : ℕ}
    (hj : g.totalDegree + 2 * j ≤ 2 * m) :
    |E (g * quadPoly (diagonal κ) ^ j) - E g| ≤ η₀ * j * coeffNorm1 g * (2 * d + 1) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hsq : IsSumSq (g * quadPoly (diagonal κ) ^ j) := hg.mul (isSumSq_pow h.isSumSq_QD j)
    have hdeg : (g * quadPoly (diagonal κ) ^ j).totalDegree + 2 ≤ 2 * m := by
      have h1 := totalDegree_mul g (quadPoly (diagonal κ) ^ j)
      have h2 := (totalDegree_pow (quadPoly (diagonal κ)) j).trans
        (Nat.mul_le_mul_left j (totalDegree_quadPoly_le (diagonal κ)))
      omega
    have h1 := h.eq_approx _ hsq hdeg
    have hB : (1 : ℝ) ≤ 2 * d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    have hc1 : coeffNorm (g * quadPoly (diagonal κ) ^ j) ≤ coeffNorm1 g * (2 * d + 1) ^ j :=
      (coeffNorm_le_coeffNorm1 _).trans ((coeffNorm1_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left ((coeffNorm1_pow_le _ _).trans (pow_le_pow_left₀
          (coeffNorm1_nonneg _) (by linarith [h.coeffNorm1_QD_le]) _)) (coeffNorm1_nonneg _)))
    have e1 : E (g * quadPoly (diagonal κ) ^ (j + 1)) - E g =
        E (g * quadPoly (diagonal κ) ^ j * (quadPoly (diagonal κ) - 1)) +
          (E (g * quadPoly (diagonal κ) ^ j) - E g) := by
      rw [← E.map_sub, ← E.map_sub, ← E.map_add]
      congr 1
      ring
    rw [e1]
    have hη := h.eta_nonneg
    have hg1 := coeffNorm1_nonneg g
    have hP : 0 ≤ η₀ * coeffNorm1 g * (2 * d + 1) ^ j := by positivity
    calc _ ≤ |E (g * quadPoly (diagonal κ) ^ j * (quadPoly (diagonal κ) - 1))| +
          |E (g * quadPoly (diagonal κ) ^ j) - E g| := abs_add_le _ _
      _ ≤ η₀ * (coeffNorm1 g * (2 * d + 1) ^ j) * (2 * d + 1) +
          η₀ * j * coeffNorm1 g * (2 * d + 1) ^ j :=
          add_le_add (h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hc1 hη)
            h.coeffNorm_QD_sub_one_le (coeffNorm_nonneg _) (by positivity))) (ih (by omega))
      _ = η₀ * coeffNorm1 g * (2 * d + 1) ^ j * ((2 * d + 1) + j) := by ring
      _ ≤ η₀ * coeffNorm1 g * (2 * d + 1) ^ j * ((2 * d + 1) * (j + 1)) :=
          mul_le_mul_of_nonneg_left (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) hP
      _ = η₀ * ((j + 1 : ℕ) : ℝ) * coeffNorm1 g * (2 * d + 1) ^ (j + 1) := by
          push_cast
          ring

/-- `|Ẽ (vᵀDv)^m - 1| ≤ errQ`. -/
theorem abs_E_QD_pow_sub_one_le : |E (quadPoly (diagonal κ) ^ m) - 1| ≤ errQ η₀ m d := by
  have h1 := h.abs_E_mul_QD_pow_sub_le IsSumSq.one (j := m) (by simp)
  rwa [one_mul, E.map_one, coeffNorm1_one, mul_one] at h1

/-- `|Ẽ[vᵀDv] - 1| ≤ η₀ (2d + 1)`. -/
theorem abs_E_QD_sub_one_le : |E (quadPoly (diagonal κ)) - 1| ≤ η₀ * (2 * d + 1) := by
  have h1 := h.abs_E_mul_QD_pow_sub_le IsSumSq.one (j := 1) (by simp [h.one_le_m])
  simpa only [one_mul, E.map_one, coeffNorm1_one, mul_one, pow_one, Nat.cast_one] using h1

/-- `η₀ (2d + 1) ≤ errQ`. -/
theorem eta_mul_le_errQ : η₀ * (2 * d + 1) ≤ errQ η₀ m d := by
  unfold errQ
  have hB : (1 : ℝ) ≤ 2 * d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast h.one_le_m
  have h1 : (2 * d + 1 : ℝ) ≤ (2 * d + 1) ^ m := le_self_pow₀ hB (by have := h.one_le_m; omega)
  have hη := h.eta_nonneg
  calc η₀ * (2 * d + 1) ≤ η₀ * (2 * d + 1) ^ m := mul_le_mul_of_nonneg_left h1 hη
    _ = 1 * (η₀ * (2 * d + 1) ^ m) := by ring
    _ ≤ m * (η₀ * (2 * d + 1) ^ m) := mul_le_mul_of_nonneg_right hm (by positivity)
    _ = η₀ * m * (2 * d + 1) ^ m := by ring

/-! #### Normalization -/

/-- **Normalization**: `N = Ẽ (vᵀ cw v)^m` has `|N - 1| ≤ errN = 2 (m δc + η₀ m (2d + 1)^m)`. -/
theorem abs_N_sub_one_le : |E (quadPoly cw ^ m) - 1| ≤ errN η₀ δc m d := by
  obtain ⟨hB, hP, hI⟩ := pow_bounds h.delta_nonneg (by linarith [h.delta_le_eighth]) (n := m)
    (by linarith [h.mdelta_le])
  have hQ := abs_le.1 h.abs_E_QD_pow_sub_one_le
  have hge := h.E_QD_pow_ge
  have hle := h.E_QD_pow_le
  have hN0 := h.E_cw_pow_nonneg
  have hq := h.errQ_nonneg
  have hx := h.mdelta_le
  have hx0 : 0 ≤ (m : ℝ) * δc := mul_nonneg (Nat.cast_nonneg _) h.delta_nonneg
  have hPm : 0 < (1 - δc) ^ m := by linarith
  rw [abs_le, errN]
  constructor
  · by_cases hN1 : 1 ≤ E (quadPoly cw ^ m)
    · linarith
    · push Not at hN1
      have h1 : (1 + δc) ^ m * E (quadPoly cw ^ m) ≤ (1 + 2 * m * δc) * E (quadPoly cw ^ m) :=
        mul_le_mul_of_nonneg_right hP hN0
      have h2 : (m : ℝ) * δc * E (quadPoly cw ^ m) ≤ m * δc * 1 :=
        mul_le_mul_of_nonneg_left hN1.le hx0
      linarith
  · have h1 : E (quadPoly cw ^ m) ≤ ((1 - δc) ^ m)⁻¹ * E (quadPoly (diagonal κ) ^ m) := by
      calc E (quadPoly cw ^ m) = ((1 - δc) ^ m)⁻¹ * ((1 - δc) ^ m * E (quadPoly cw ^ m)) := by
            rw [← mul_assoc, inv_mul_cancel₀ hPm.ne', one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hge (inv_nonneg.2 hPm.le)
    have h2 : ((1 - δc) ^ m)⁻¹ * E (quadPoly (diagonal κ) ^ m) ≤
        (1 + 2 * m * δc) * (1 + errQ η₀ m d) :=
      mul_le_mul hI (by linarith) ((mul_nonneg hPm.le hN0).trans hge) (by linarith)
    have h3 : (m : ℝ) * δc * errQ η₀ m d ≤ 1 / 8 * errQ η₀ m d := mul_le_mul_of_nonneg_right hx hq
    linarith

/-- `N ≤ 1 + errN`. -/
theorem N_le : E (quadPoly cw ^ m) ≤ 1 + errN η₀ δc m d := by
  linarith [(abs_le.1 h.abs_N_sub_one_le).2]

/-- `N ≥ 1 - errN`. -/
theorem N_ge : 1 - errN η₀ δc m d ≤ E (quadPoly cw ^ m) := by
  linarith [(abs_le.1 h.abs_N_sub_one_le).1]

/-! #### The defect `Ẽ[vᵀGv]` -/

/-- The entries of `G` are at most `3` in absolute value. -/
theorem abs_G_apply_le (i j : Fin d) : |(cw - vecMulVec u u) i j| ≤ 3 := by
  have hdiag : ∀ i, (cw - vecMulVec u u) i i ≤ 16 / 7 := by
    intro i
    have e1 : quad (cw - vecMulVec u u) (Pi.single i 1) = (cw - vecMulVec u u) i i :=
      single_dotProduct_mulVec_single _ i i
    have e2 : quad (diagonal κ) (Pi.single i 1) = κ i := by
      rw [quad, single_dotProduct_mulVec_single, diagonal_apply_eq]
    have hl := h.cmp_lower (Pi.single i 1)
    have hq := quad_sub_vecMulVec cw u (Pi.single i 1)
    have hc0 := quad_nonneg h.cw_posDef.posSemidef (Pi.single i 1)
    have hδ := h.delta_le_eighth
    have hk := h.kappa_le i
    rw [e2] at hl
    rw [e1] at hq
    have h1 : 0 ≤ (1 / 8 - δc) * quad cw (Pi.single i 1) := mul_nonneg (by linarith) hc0
    nlinarith [sq_nonneg (u ⬝ᵥ Pi.single i 1)]
  have hG := h.G_posSemidef
  have hcs := Rounding.sq_dotProduct_mulVec_le hG (Pi.single i 1) (Pi.single j 1)
  rw [single_dotProduct_mulVec_single, single_dotProduct_mulVec_single,
    single_dotProduct_mulVec_single] at hcs
  have hi0 := h.quad_G_nonneg (Pi.single i 1)
  have hj0 := h.quad_G_nonneg (Pi.single j 1)
  change 0 ≤ Pi.single i 1 ⬝ᵥ ((cw - vecMulVec u u) *ᵥ Pi.single i 1) at hi0
  change 0 ≤ Pi.single j 1 ⬝ᵥ ((cw - vecMulVec u u) *ᵥ Pi.single j 1) at hj0
  rw [single_dotProduct_mulVec_single] at hi0 hj0
  have h9 : (cw - vecMulVec u u) i j ^ 2 ≤ 9 := by
    have := mul_le_mul (hdiag i) (hdiag j) hj0 (by norm_num)
    nlinarith
  exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

/-- `‖vᵀGv‖₁ ≤ 3d²`. -/
theorem coeffNorm1_G_le : coeffNorm1 (quadPoly (cw - vecMulVec u u)) ≤ 3 * d ^ 2 := by
  refine (coeffNorm1_quadPoly_le _).trans ?_
  calc ∑ i, ∑ j, |(cw - vecMulVec u u) i j| ≤ ∑ _i : Fin d, ∑ _j : Fin d, (3 : ℝ) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ h.abs_G_apply_le i j
    _ = 3 * d ^ 2 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- `Ẽ[vᵀGv] ≤ Ẽ[vᵀGv (vᵀDv)^(m-1)] + 3 d² errQ` (the equality constraint). -/
theorem E_G_le_E_G_mul_QD_pow :
    E (quadPoly (cw - vecMulVec u u)) ≤
      E (quadPoly (cw - vecMulVec u u) * quadPoly (diagonal κ) ^ (m - 1)) +
        3 * d ^ 2 * errQ η₀ m d := by
  have hm := h.one_le_m
  have h1 := h.abs_E_mul_QD_pow_sub_le h.isSumSq_G (j := m - 1)
    (by have := totalDegree_quadPoly_le (cw - vecMulVec u u); omega)
  have h2 := (abs_le.1 h1).1
  have hB : (1 : ℝ) ≤ 2 * d + 1 := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hpow : (2 * d + 1 : ℝ) ^ (m - 1) ≤ (2 * d + 1) ^ m := pow_le_pow_right₀ hB (Nat.sub_le m 1)
  have hcast : ((m - 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (Nat.sub_le m 1)
  have hη := h.eta_nonneg
  have hb : η₀ * ((m - 1 : ℕ) : ℝ) * coeffNorm1 (quadPoly (cw - vecMulVec u u)) *
      (2 * d + 1) ^ (m - 1) ≤ 3 * d ^ 2 * errQ η₀ m d := by
    unfold errQ
    calc η₀ * ((m - 1 : ℕ) : ℝ) * coeffNorm1 (quadPoly (cw - vecMulVec u u)) *
          (2 * d + 1) ^ (m - 1) ≤ η₀ * m * (3 * d ^ 2) * (2 * d + 1) ^ m :=
          mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hcast hη) h.coeffNorm1_G_le
            (coeffNorm1_nonneg _) (mul_nonneg hη (Nat.cast_nonneg _))) hpow (by positivity)
            (mul_nonneg (mul_nonneg hη (Nat.cast_nonneg _)) (by positivity))
      _ = 3 * d ^ 2 * (η₀ * m * (2 * d + 1) ^ m) := by ring
  linarith

/-- **Defect, first step**: `Ẽ[vᵀGv] ≤ Ẽ[vᵀGv (⟨u, v⟩² + vᵀGv)^(m-1)] + errY`, from the
equality constraint and the comparison of `cw` with `D`. -/
theorem E_G_le :
    E (quadPoly (cw - vecMulVec u u)) ≤
      E (quadPoly (cw - vecMulVec u u) *
        (Separating.lin u ^ 2 + quadPoly (cw - vecMulVec u u)) ^ (m - 1)) +
        errY η₀ δc m d := by
  rw [← quadPoly_eq_sq_add cw u]
  have hcast : ((m - 1 : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (Nat.sub_le m 1)
  have hδ0 := h.delta_nonneg
  obtain ⟨-, hP, -⟩ := pow_bounds hδ0 (by linarith [h.delta_le_eighth]) (n := m - 1)
    ((mul_le_mul_of_nonneg_right hcast hδ0).trans (by linarith [h.mdelta_le]))
  have h1 := h.E_G_le_E_G_mul_QD_pow
  have h2 := h.E_G_mul_QD_pow_le
  have h3 := h.E_G_mul_cw_pow_le
  have h4 := h.E_G_mul_cw_pow_nonneg
  have hN := h.N_le
  have h5 := mul_le_mul_of_nonneg_right hP h4
  have h6 : ((m - 1 : ℕ) : ℝ) * δc *
      E (quadPoly (cw - vecMulVec u u) * quadPoly cw ^ (m - 1)) ≤
        m * δc * (1 + errN η₀ δc m d) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hcast hδ0) (h3.trans hN) h4
      (mul_nonneg (Nat.cast_nonneg _) hδ0)
  unfold errY
  linarith

/-- **Defect**: `Ẽ[vᵀGv] ≤ ∑_{l < m} C(m, l) λ_l + errY`, with
`λ_l = Ẽ[⟨u, v⟩^{2l} (vᵀGv)^{m-l}]`. -/
theorem E_G_le_sum :
    E (quadPoly (cw - vecMulVec u u)) ≤
      ∑ l ∈ range m, (m.choose l : ℝ) *
        E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) +
        errY η₀ δc m d := by
  have h1 := h.E_G_le
  have h2 := apply_mul_add_sq_pow_le E (totalDegree_lin_le u) h.isSumSq_G
    (totalDegree_quadPoly_le _) h.one_le_m le_rfl
  linarith

/-! #### The point on the line of the means -/

/-- **The feasible point `v* = c cw⁻¹ u`**, with `c² = 1 / (zᵀDz)`, `z = cw⁻¹ u`: it has
`‖v*‖² ≤ 2`, `v*ᵀDv* = 1`, and `Φ_{2m}(v*) = t M_{2m}` with `t = c^{2m}` within `2 m δc` of
`1` (since `v*ᵀGv* = 0` and `⟨u, v*⟩ = c`). -/
theorem exists_point : ∃ v : Fin d → ℝ, ∃ t : ℝ, ∑ i, v i ^ 2 ≤ 2 ∧
    eval v (quadPoly (diagonal κ)) = 1 ∧
    eval v (popPoly w a u SWq (2 * m)) = t * lineMom w a σ2 m ∧
    1 - 2 * m * δc ≤ t ∧ t ≤ 1 + 2 * m * δc := by
  obtain ⟨z, hz⟩ : ∃ z, z = cw⁻¹ *ᵥ u := ⟨_, rfl⟩
  have hz1 : quad cw z = 1 := by rw [hz, quad_inv_mulVec h.cw_posDef, h.u_cw_inv]
  have huz : u ⬝ᵥ z = 1 := by rw [hz, h.u_cw_inv]
  obtain ⟨q, hq⟩ : ∃ q, q = quad (diagonal κ) z := ⟨_, rfl⟩
  have hq1 : 1 - δc ≤ q := by have := h.cmp_lower z; rwa [hz1, mul_one, ← hq] at this
  have hq2 : q ≤ 1 + δc := by have := h.cmp_upper z; rwa [hz1, mul_one, ← hq] at this
  have hδ := h.delta_le_eighth
  have hδ0 := h.delta_nonneg
  have hqpos : 0 < q := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = (Real.sqrt q)⁻¹ := ⟨_, rfl⟩
  have hs2 : s ^ 2 = q⁻¹ := by rw [hs, inv_pow, Real.sq_sqrt hqpos.le]
  have hvD : quad (diagonal κ) (s • z) = 1 := by
    rw [quad_smul, hs2, ← hq, inv_mul_cancel₀ hqpos.ne']
  have huv : u ⬝ᵥ (s • z) = s := by rw [dotProduct_smul, huz, smul_eq_mul, mul_one]
  have hGv : quad (cw - vecMulVec u u) (s • z) = 0 := by
    rw [quad_sub_vecMulVec, huv, quad_smul, hz1]
    ring
  obtain ⟨-, hP, hI⟩ := pow_bounds hδ0 (by linarith) (n := m) (by linarith [h.mdelta_le])
  have hx0 : 0 ≤ 2 * (m : ℝ) * δc := by positivity
  refine ⟨s • z, q⁻¹ ^ m, ?_, ?_, ?_, ?_, ?_⟩
  · have hD := quad_diagonal κ (s • z)
    rw [hvD] at hD
    calc ∑ i, (s • z) i ^ 2 ≤ ∑ i, 2 * (κ i * (s • z) i ^ 2) :=
          sum_le_sum fun i _ ↦ by nlinarith [h.kappa_gt i, sq_nonneg ((s • z) i)]
      _ = 2 := by rw [← mul_sum, ← hD, mul_one]
  · rw [eval_quadPoly, hvD]
  · rw [eval_popPoly, lineMom, mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [h.quad_SWq, hGv, huv, zero_add, mul_comm (a c) s, mul_comm σ2 (s ^ 2), hmom_mul, pow_mul,
      hs2]
    ring
  · have h1 : ((1 + δc) ^ m)⁻¹ ≤ q⁻¹ ^ m := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.2 (by linarith)) (inv_anti₀ hqpos hq2) m
    have h2 : (1 + 2 * m * δc)⁻¹ ≤ ((1 + δc) ^ m)⁻¹ := inv_anti₀ (by positivity) hP
    linarith [one_sub_le_inv hx0]
  · have h1 : q⁻¹ ^ m ≤ ((1 - δc) ^ m)⁻¹ := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_nonneg.2 hqpos.le) (inv_anti₀ (by linarith) hq1) m
    linarith

/-- `|Φ(v) - Φ_{2m}(v)| ≤ e 258^m` for `‖v‖² ≤ 2`. -/
theorem abs_eval_sub_le {v : Fin d → ℝ} (hv : ∑ i, v i ^ 2 ≤ 2) :
    |eval v Φ - eval v (popPoly w a u SWq (2 * m))| ≤ e * 258 ^ m := by
  have hb : ∀ i, |v i| ≤ 2 := fun i ↦ by
    have : v i ^ 2 ≤ 2 :=
      (single_le_sum (f := fun i ↦ v i ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i)).trans hv
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have h1 := abs_eval_le (p := Φ - popPoly w a u SWq (2 * m)) (by norm_num : (1 : ℝ) ≤ 2) hb
  rw [map_sub] at h1
  have hdeg : (Φ - popPoly w a u SWq (2 * m)).totalDegree ≤ 2 * m :=
    (totalDegree_sub _ _).trans (max_le h.totalDegree_Phi_le (totalDegree_popPoly_le _ _ _ _ _))
  have he := h.e_nonneg
  calc _ ≤ coeffNorm1 (Φ - popPoly w a u SWq (2 * m)) *
        2 ^ (Φ - popPoly w a u SWq (2 * m)).totalDegree := h1
    _ ≤ e * 2 ^ (2 * m) :=
        mul_le_mul h.Phi_close (pow_le_pow_right₀ (by norm_num) hdeg) (by positivity) he
    _ ≤ e * 258 ^ m := mul_le_mul_of_nonneg_left (by
        rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) m) he

/-- `|Ẽ Φ - Ẽ Φ_{2m}| ≤ e 258^m`. -/
theorem abs_E_sub_le : |E Φ - E (popPoly w a u SWq (2 * m))| ≤ e * 258 ^ m := by
  rw [← E.map_sub]
  have hdeg : (Φ - popPoly w a u SWq (2 * m)).totalDegree ≤ 2 * m :=
    (totalDegree_sub _ _).trans (max_le h.totalDegree_Phi_le (totalDegree_popPoly_le _ _ _ _ _))
  exact (h.abs_E_le _ hdeg).trans (mul_le_mul_of_nonneg_right h.Phi_close (by positivity))

/-! #### The two programs -/

/-- `β_l ≥ 0`. -/
theorem nbeta_nonneg' (l : ℕ) : 0 ≤ nbeta w a σ2 m l :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (lineMom_nonneg h.w_nonneg h.sigma_nonneg l))
    (Nat.cast_nonneg _)

/-- `β_m = M_{2m} ≥ 1`. -/
theorem one_le_nbeta_self : 1 ≤ nbeta w a σ2 m m := by
  rw [nbeta_self]
  exact one_le_lineMom h.w_nonneg h.sum_w h.sigma_nonneg h.var_eq m

/-- **Case U** (the upper program). If `M_{2m} ≥ (4m)^m` and `Ẽ` is `γ`-optimal for maximizing
`Ẽ Φ` (`Φ(v) - γ ≤ Ẽ Φ` for every feasible `v`), then `Ẽ[vᵀGv] ≤ errD`. -/
theorem defect_le_of_max {γ : ℝ} (hγ : 0 ≤ γ) (hM : (4 * m : ℝ) ^ m ≤ lineMom w a σ2 m)
    (hopt : ∀ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 → eval v (quadPoly (diagonal κ)) = 1 →
      eval v Φ - γ ≤ E Φ) :
    E (quadPoly (cw - vecMulVec u u)) ≤ errD η₀ δc e γ m d := by
  obtain ⟨v, t, hv2, hvQ, hvpop, ht1, -⟩ := h.exists_point
  have hopt' := hopt v (by linarith) hvQ
  have hE1 := abs_le.1 (h.abs_eval_sub_le hv2)
  have hE2 := abs_le.1 h.abs_E_sub_le
  have hβ : ∀ l < m, nbeta w a σ2 m l ≤ nbeta w a σ2 m m / 2 := by
    intro l hl
    have h1 := nbeta_mul_two_pow_le h.w_nonneg h.sum_w h.sigma_nonneg h.one_le_m hM l hl.le
    have h2 : (2 : ℝ) ≤ 2 ^ (m - l) := le_self_pow₀ (by norm_num) (by omega)
    have := mul_le_mul_of_nonneg_left h2 (h.nbeta_nonneg' l)
    linarith
  have hmain : t * nbeta w a σ2 m m - (γ + 2 * e * 258 ^ m) ≤
      ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
        E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) *
          nbeta w a σ2 m l := by
    rw [← h.E_popPoly, nbeta_self, ← hvpop]
    linarith
  have hN : ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
      E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) ≤
        1 + errN η₀ δc m d := by
    rw [← E_cw_pow]
    exact h.N_le
  have he := h.e_nonneg
  have hmass := mass_le_of_max
    (lam := fun l ↦ E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)))
    (fun l hl ↦ h.lam_nonneg' hl) h.one_le_nbeta_self hβ (x := 2 * m * δc)
    (mul_nonneg (by positivity) h.delta_nonneg) (by positivity) h.errN_nonneg hN ht1 hmain
  have hdef := h.E_G_le_sum
  unfold errD
  linarith

/-- **Case L** (the lower program). If all `a_c² ≤ A²`, `σ² ≤ 1/16`, `m ≥ 5A² + 8` and `Ẽ` is
`γ`-optimal for minimizing `Ẽ Φ` (`Ẽ Φ ≤ Φ(v) + γ` for every feasible `v`), then
`Ẽ[vᵀGv] ≤ errD`. -/
theorem defect_le_of_min {γ A2 : ℝ} (hγ : 0 ≤ γ) (hA : ∀ c, a c ^ 2 ≤ A2) (hA0 : 0 ≤ A2)
    (hσ16 : σ2 ≤ 1 / 16) (hm : 5 * A2 + 8 ≤ m)
    (hopt : ∀ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 → eval v (quadPoly (diagonal κ)) = 1 →
      E Φ ≤ eval v Φ + γ) :
    E (quadPoly (cw - vecMulVec u u)) ≤ errD η₀ δc e γ m d := by
  obtain ⟨v, t, hv2, hvQ, hvpop, -, ht2⟩ := h.exists_point
  have hopt' := hopt v (by linarith) hvQ
  have hE1 := abs_le.1 (h.abs_eval_sub_le hv2)
  have hE2 := abs_le.1 h.abs_E_sub_le
  have hβ := two_mul_nbeta_le h.w_nonneg h.sigma_nonneg hA hA0 hσ16 hm
  have hmain : ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
      E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) *
        nbeta w a σ2 m l ≤ t * nbeta w a σ2 m m + (γ + 2 * e * 258 ^ m) := by
    rw [← h.E_popPoly, nbeta_self, ← hvpop]
    linarith
  have hN1 : 1 - errN η₀ δc m d ≤ ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
      E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) := by
    rw [← E_cw_pow]
    exact h.N_ge
  have hN2 : ∑ l ∈ range (m + 1), (m.choose l : ℝ) *
      E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)) ≤
        1 + errN η₀ δc m d := by
    rw [← E_cw_pow]
    exact h.N_le
  have he := h.e_nonneg
  have hmass := mass_le_of_min
    (lam := fun l ↦ E (Separating.lin u ^ (2 * l) * quadPoly (cw - vecMulVec u u) ^ (m - l)))
    (fun l hl ↦ h.lam_nonneg' hl) h.one_le_nbeta_self hβ (x := 2 * m * δc)
    (mul_nonneg (by positivity) h.delta_nonneg) (by positivity) h.errN_nonneg hN1 hN2 ht2 hmain
  have hdef := h.E_G_le_sum
  unfold errD
  linarith

/-! #### The test between the programs -/

/-- **(T1)** If the value `Ẽ Φ` of the upper program is at least `(5m)^m`, then the moment along
the line of the means is large: `M_{2m} ≥ (4m)^m`. -/
theorem lineMom_ge_of_test (hN : errN η₀ δc m d ≤ 1 / 8) (he : e * 258 ^ m ≤ 1 / 4)
    (hT : (5 * m : ℝ) ^ m ≤ E Φ) : (4 * m : ℝ) ^ m ≤ lineMom w a σ2 m := by
  by_contra hlt
  push Not at hlt
  have hm1 := h.one_le_m
  have hβ := nbeta_le_of_lineMom_le h.w_nonneg h.sum_w h.sigma_nonneg (s := m) (X := 4 * m)
    (by linarith [h.m_pos]) hlt.le
  have hpop : E (popPoly w a u SWq (2 * m)) ≤ (4 * m : ℝ) ^ m * E (quadPoly cw ^ m) := by
    rw [h.E_popPoly, E_cw_pow (u := u), mul_sum]
    refine sum_le_sum fun l hl ↦ ?_
    have hl' : l ≤ m := Nat.lt_succ_iff.1 (mem_range.1 hl)
    have := mul_le_mul_of_nonneg_left (hβ l hl')
      (mul_nonneg (Nat.cast_nonneg (m.choose l) : (0 : ℝ) ≤ _) (h.lam_nonneg' hl'))
    linarith
  have hE := abs_le.1 h.abs_E_sub_le
  have hNle := h.N_le
  have h45 : (5 / 4 : ℝ) * (4 * m) ^ m ≤ (5 * m) ^ m := by
    rw [show (5 * m : ℝ) = 5 / 4 * (4 * m) by ring, mul_pow (5 / 4 : ℝ) (4 * m) m]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) (by omega)) (by positivity)
  have h4 : (4 : ℝ) ≤ (4 * m) ^ m := by
    have h4m : (4 : ℝ) ≤ 4 * m := by linarith [(Nat.one_le_cast.2 hm1 : (1 : ℝ) ≤ m)]
    exact h4m.trans (le_self_pow₀ (by linarith) (by omega))
  have h98 : (4 * m : ℝ) ^ m * E (quadPoly cw ^ m) ≤ (4 * m) ^ m * (1 + 1 / 8) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **(T2)** If the value `Ẽ Φ` of the upper program is below `(5m)^m` and `Ẽ` is `γ`-optimal
for it with `γ ≤ 1`, then `M_{2m} ≤ 3 (5m)^m`. -/
theorem lineMom_le_of_test {γ : ℝ} (hγ : γ ≤ 1) (he : e * 258 ^ m ≤ 1 / 4)
    (hT : E Φ < (5 * m : ℝ) ^ m)
    (hopt : ∀ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 → eval v (quadPoly (diagonal κ)) = 1 →
      eval v Φ - γ ≤ E Φ) :
    lineMom w a σ2 m ≤ 3 * (5 * m : ℝ) ^ m := by
  obtain ⟨v, t, hv2, hvQ, hvpop, ht1, -⟩ := h.exists_point
  have hopt' := hopt v (by linarith) hvQ
  have hE1 := abs_le.1 (h.abs_eval_sub_le hv2)
  have hL0 := lineMom_nonneg h.w_nonneg h.sigma_nonneg (a := a) m
  have ht : 3 / 4 ≤ t := by linarith [h.mdelta_le]
  have h5 : (1 : ℝ) ≤ (5 * m) ^ m :=
    one_le_pow₀ (by linarith [(Nat.one_le_cast.2 h.one_le_m : (1 : ℝ) ≤ m)])
  have h34 := mul_le_mul_of_nonneg_right ht hL0
  rw [← hvpop] at h34
  linarith

/-! #### The pseudo-moment matrix -/

omit h in
/-- `Ẽ⟨u, v⟩² + Ẽ[vᵀGv] = Ẽ[vᵀ cw v]`. -/
theorem E_sq_add_E_G :
    E (Separating.lin u ^ 2) + E (quadPoly (cw - vecMulVec u u)) = E (quadPoly cw) := by
  rw [quadPoly_eq_sq_add cw u, E.map_add]

/-- `Ẽ[vᵀ cw v] ≥ 1 - errN`. -/
theorem one_sub_le_E_cw : 1 - errN η₀ δc m d ≤ E (quadPoly cw) := by
  have hm := h.one_le_m
  have h1 := abs_le.1 h.abs_E_QD_sub_one_le
  have h2 : E (quadPoly (diagonal κ)) ≤ (1 + δc) * E (quadPoly cw) := by
    have := apply_le_apply E h.isSumSq_sub_QD ((totalDegree_sub _ _).trans
      (max_le (totalDegree_C_mul_quadPoly_le _ _) (totalDegree_quadPoly_le _)) |>.trans
        (by omega))
    rwa [E.map_C_mul] at this
  have h3 := h.eta_mul_le_errQ
  have h0 : 0 ≤ E (quadPoly cw) :=
    E.nonneg_of_isSumSq h.isSumSq_cw ((totalDegree_quadPoly_le _).trans (by omega))
  have hδ0 := h.delta_nonneg
  have hq := h.errQ_nonneg
  have hmδ : δc ≤ m * δc := le_mul_of_one_le_left hδ0 (Nat.one_le_cast.2 hm)
  unfold errN
  by_cases hc : 1 ≤ E (quadPoly cw)
  · linarith
  · push Not at hc
    have := mul_le_mul_of_nonneg_left hc.le hδ0
    linarith

/-- `⟨u, Ẽ[vvᵀ] u⟩ = Ẽ⟨u, v⟩² ≥ 1/2` when the defect and `errN` are at most `1/4`. -/
theorem half_le_secondMom_u (hy : E (quadPoly (cw - vecMulVec u u)) ≤ 1 / 4)
    (hN : errN η₀ δc m d ≤ 1 / 4) : 1 / 2 ≤ u ⬝ᵥ (secondMom E *ᵥ u) := by
  rw [dotProduct_secondMom_mulVec, ← sq]
  have h1 := E_sq_add_E_G (E := E) (cw := cw) (u := u)
  have h2 := h.one_sub_le_E_cw
  linarith

/-- `tr Ẽ[vvᵀ] = Ẽ ‖v‖² ≥ Ẽ[vᵀDv] / 2 ≥ 1/4`. -/
theorem quarter_le_trace (hN : errN η₀ δc m d ≤ 1 / 2) : 1 / 4 ≤ ∑ i, secondMom E i i := by
  rw [sum_secondMom_diag]
  have hm := h.one_le_m
  have h1 : IsSumSq (quadPoly ((2 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) -
      quadPoly (diagonal κ)) :=
    isSumSq_quadPoly_sub (diagonal_transpose κ) (by rw [transpose_smul, transpose_one])
      fun v ↦ by
        rw [quad_smul_matrix, quad_diagonal, quad, one_mulVec, dotProduct, mul_sum]
        exact sum_le_sum fun i _ ↦ by nlinarith [h.kappa_le i, sq_nonneg (v i)]
  have h2 := apply_le_apply E h1 ((totalDegree_sub _ _).trans
    (max_le (totalDegree_quadPoly_le _) (totalDegree_quadPoly_le _)) |>.trans (by omega))
  rw [quadPoly_smul, E.map_C_mul] at h2
  have h3 := abs_le.1 h.abs_E_QD_sub_one_le
  have h4 := h.eta_mul_le_errQ
  have hmδ : 0 ≤ (m : ℝ) * δc := mul_nonneg (Nat.cast_nonneg _) h.delta_nonneg
  unfold errN at hN
  linarith

/-- A maximal diagonal entry of `Ẽ[vvᵀ]` is at least `1/(4d)`. -/
theorem inv_four_mul_le_diag (hN : errN η₀ δc m d ≤ 1 / 2) {j : Fin d}
    (hj : ∀ i, secondMom E i i ≤ secondMom E j j) : 1 / (4 * d) ≤ secondMom E j j := by
  have h1 := h.quarter_le_trace hN
  have h2 : ∑ i, secondMom E i i ≤ d * secondMom E j j := by
    calc ∑ i, secondMom E i i ≤ ∑ _i : Fin d, secondMom E j j := sum_le_sum fun i _ ↦ hj i
      _ = d * secondMom E j j := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hd : (0 : ℝ) < d := Nat.cast_pos.2 j.pos
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The direction.** If the defect is `Ẽ[vᵀGv] ≤ δ'` with `δ' ≤ 1/(10⁴ d)` and
`δ' ≤ 3σ²/8`, `errN ≤ 1/8`, and `j` maximizes the diagonal of `M = Ẽ[vvᵀ]`, then the column
`â = M e_j` has `âᵀGâ ≤ 3 σ² ⟨u, â⟩²` and `⟨u, â⟩ ≠ 0`. -/
theorem column_facts {δ' : ℝ} (hdef : E (quadPoly (cw - vecMulVec u u)) ≤ δ')
    (hδd : δ' ≤ 1 / (10 ^ 4 * d)) (hδσ : δ' ≤ 3 * σ2 / 8) (hN : errN η₀ δc m d ≤ 1 / 8)
    (j : Fin d) (hj : ∀ i, secondMom E i i ≤ secondMom E j j) :
    quad (cw - vecMulVec u u) (secondMom E *ᵥ Pi.single j 1) ≤
        3 * σ2 * (u ⬝ᵥ (secondMom E *ᵥ Pi.single j 1)) ^ 2 ∧
      u ⬝ᵥ (secondMom E *ᵥ Pi.single j 1) ≠ 0 := by
  have hd : (1 : ℝ) ≤ d := Nat.one_le_cast.2 j.pos
  have hδ4 : δ' ≤ 1 / 4 :=
    hδd.trans (one_div_le_one_div_of_le (by norm_num) (by nlinarith))
  have hcwj : (Pi.single j 1 : Fin d → ℝ) ⬝ᵥ (cw⁻¹ *ᵥ Pi.single j 1) ≤ 3 := by
    have h1 := Fr.inv_quad_le_of_diagonal h.cw_posDef (fun i ↦ (h.kappa_gt i).le)
      (by linarith [h.delta_le_eighth]) h.cmp_upper (Pi.single j 1)
    have h2 : (Pi.single j 1 : Fin d → ℝ) ⬝ᵥ Pi.single j 1 = 1 := by simp
    rwa [h2, mul_one] at h1
  exact column_perp_le (secondMom_posSemidef E (by have := h.one_le_m; omega)) h.cw_posDef
    h.u_cw_inv (by rw [trace_mul_secondMom]; exact hdef)
    (h.half_le_secondMom_u (hdef.trans hδ4) (by linarith)) j
    (h.inv_four_mul_le_diag (by linarith) hj) hcwj hδd hδσ

end PseudoHyp

end BS23.ColinearSoS
