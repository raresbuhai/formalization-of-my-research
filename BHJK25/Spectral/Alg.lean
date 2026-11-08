module

public import BHJK25.Model
public import Background.SumOfSquares.Algorithm.PDTestRat
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO

/-!
# The algorithm of Theorem 3.1

The algorithm reads a rational matrix `X`, forms `2I - (X + Xᵀ)/2`, and answers `true` when it is
not positive definite (`SoS.PDTestRat.test`, an exact test in polynomial time). If `X` is within
`1/n` of a symmetric matrix `M` in every entry, then `(X + Xᵀ)/2 - M` has operator norm at most
`1`; so the answer is `false` when `M` is negative semidefinite, and `true` when `M` has a vector
with `vᵀ M v > 3 ‖v‖²`.

* **Running time** (`BHJK25.Spectral.specAlg_runsInTime`): building the rows of
  `2I - (X + Xᵀ)/2` and the test have certificates (`Turing.MultiTapeTM.ComputableInPolyTime`), and
  the encoding of the input is that of the pair `(n, rows of X)`; a polynomial-time certificate
  has an explicit degree, which gives the bound `(|x| + 2)^c`.
* **Correctness** (`BHJK25.Spectral.specAlg_eq_false`, `BHJK25.Spectral.specAlg_eq_true`): a
  matrix `E` with entries at most `1/n` has `|vᵀ E v| ≤ ‖v‖²`
  (`BHJK25.Spectral.AlgAux.abs_quad_le`, from `|vᵢ vⱼ| ≤ (vᵢ² + vⱼ²)/2`), and
  `vᵀ (2I - (X + Xᵀ)/2) v = 2 ‖v‖² - vᵀ M v - vᵀ E v` with `E = (X + Xᵀ)/2 - M`.
-/

@[expose] public section

namespace BHJK25.Spectral

open Matrix

/-- The rows of `2I - (X + Xᵀ)/2`, for a square table `X` given by its rows (its dimension is its
number of rows). -/
def shiftedRows (rows : List (List ℚ)) : List (List ℚ) :=
  (List.range rows.length).map fun i ↦ (List.range rows.length).map fun j ↦
    (if i = j then 2 else 0) - (SoS.PDTestRat.entry rows i j + SoS.PDTestRat.entry rows j i) / 2

/-- **The algorithm of Theorem 3.1**: `true` when `2I - (X + Xᵀ)/2` is not positive definite. -/
def specAlg (x : RatMatrix) : Bool :=
  (SoS.PDTestRat.test (shiftedRows (rows x.2))).isSome

namespace AlgAux

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- Building the rows of `2I - (X + Xᵀ)/2` takes polynomial time. -/
theorem shiftedRows_polytime :
    ComputableInPolyTime shiftedRows (encList (encList encRat)) (encList (encList encRat)) := by
  unfold shiftedRows SoS.PDTestRat.entry
  exact mapWithInput (by fun_prop) (mapWithInput (by fun_prop) (by fun_prop))

/-- The algorithm on the pair `(n, rows)`. -/
def prog (p : ℕ × List (List ℚ)) : Bool := (SoS.PDTestRat.test (shiftedRows p.2)).isSome

/-- The algorithm on the pair `(n, rows)` runs in polynomial time. -/
theorem prog_polytime :
    ComputableInPolyTime prog (encPair encNat (encList (encList encRat))) encBool := by
  unfold prog
  have h := SoS.PDTestRat.test_polytime.comp (shiftedRows_polytime.comp
    (snd encNat (encList (encList encRat))))
  exact .of_tidy (ComputableTidilyInPolyTime.optionIsSome h.tidy)

end AlgAux

open Turing.MultiTapeTM in
/-- **The algorithm runs in polynomial time.** -/
theorem specAlg_runsInTime : ∃ c : ℕ,
    RunsInTime encRatMatrix Encoding.encBool specAlg fun x ↦ ((encRatMatrix x).length + 2) ^ c := by
  obtain ⟨d, e, hd⟩ := AlgAux.prog_polytime.tidy.exists_degree
  have h := hd.inO.of_encIn_eq (encIn' := encRatMatrix) (fun x : RatMatrix ↦ (x.1, rows x.2))
    fun _ ↦ rfl
  obtain ⟨c, hc, -⟩ := h.computableInO
  refine ⟨d, c, ?_⟩
  refine hc.mono (fun x ↦ ?_) (fun x ↦ ?_)
  all_goals
    refine Nat.mul_le_mul_left c ?_
    have hlen : (encPair encNat (encList (encList Encoding.encRat)) (x.1, rows x.2)).length =
        (encRatMatrix x).length := rfl
    have h2 : ((encRatMatrix x).length + 1) ^ d ≤ ((encRatMatrix x).length + 2) ^ d :=
      Nat.pow_le_pow_left (Nat.le_succ _) d
    beta_reduce
    rw [hlen]
    omega

namespace AlgAux

variable {n : ℕ}

/-- A quadratic form as a double sum. -/
theorem quad_eq_sum (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    v ⬝ᵥ (B *ᵥ v) = ∑ i, ∑ j, v i * B i j * v j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- `‖v‖² ≥ 0`. -/
theorem dotProduct_self_nonneg' (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (v i)

/-- A matrix whose entries are at most `1/n` in absolute value has operator norm at most `1`. -/
theorem abs_quad_le {E : Matrix (Fin n) (Fin n) ℝ} (hE : ∀ i j, |E i j| ≤ 1 / n)
    (v : Fin n → ℝ) : |v ⬝ᵥ (E *ᵥ v)| ≤ v ⬝ᵥ v := by
  rw [quad_eq_sum]
  have hpt : ∀ i j, |v i * E i j * v j| ≤ 1 / n * ((v i ^ 2 + v j ^ 2) / 2) := by
    intro i j
    have h1 : |v i * v j| ≤ (v i ^ 2 + v j ^ 2) / 2 :=
      abs_le.2 ⟨by nlinarith [sq_nonneg (v i + v j)], by nlinarith [sq_nonneg (v i - v j)]⟩
    rw [show v i * E i j * v j = E i j * (v i * v j) by ring, abs_mul]
    exact mul_le_mul (hE i j) h1 (abs_nonneg _) (by positivity)
  have hsum : ∑ i, ∑ j, 1 / (n : ℝ) * ((v i ^ 2 + v j ^ 2) / 2) = 1 / n * n * (v ⬝ᵥ v) := by
    have hS : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp [dotProduct, sq]
    rw [hS]
    simp only [← Finset.mul_sum, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  calc |∑ i, ∑ j, v i * E i j * v j| ≤ ∑ i, |∑ j, v i * E i j * v j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |v i * E i j * v j| :=
        Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, 1 / (n : ℝ) * ((v i ^ 2 + v j ^ 2) / 2) :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpt i j
    _ = 1 / n * n * (v ⬝ᵥ v) := hsum
    _ ≤ v ⬝ᵥ v := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [one_div_mul_cancel (by positivity), one_mul]

/-- The real matrix `2I - (X + Xᵀ)/2`. -/
noncomputable def shifted (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ (if i = j then 2 else 0) - ((X i j : ℝ) + X j i) / 2

/-- The error `(X + Xᵀ)/2 - M`. -/
noncomputable def err (X : Matrix (Fin n) (Fin n) ℚ) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j ↦ ((X i j : ℝ) + X j i) / 2 - M i j

/-- `2I - (X + Xᵀ)/2` is symmetric. -/
theorem shifted_symm (X : Matrix (Fin n) (Fin n) ℚ) : (shifted X)ᵀ = shifted X := by
  ext i j
  simp only [transpose_apply, shifted, of_apply, eq_comm (a := j), add_comm ((X j i : ℝ))]

/-- The table of `2I - (X + Xᵀ)/2` has `n` rows. -/
theorem length_shiftedRows (X : Matrix (Fin n) (Fin n) ℚ) : (shiftedRows (rows X)).length = n := by
  simp [shiftedRows, rows]

/-- The entries of the table are those of `2I - (X + Xᵀ)/2`. -/
theorem entry_shiftedRows (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    shifted X i j = SoS.PDTestRat.entry (shiftedRows (rows X)) i j := by
  simp [SoS.PDTestRat.entry, shiftedRows, List.getD_eq_getElem?_getD, shifted, rows,
    Fin.val_inj, apply_ite (Rat.cast : ℚ → ℝ)]

/-- The quadratic form of `2I - (X + Xᵀ)/2`. -/
theorem quad_shifted (X : Matrix (Fin n) (Fin n) ℚ) (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) :
    v ⬝ᵥ (shifted X *ᵥ v) = 2 * (v ⬝ᵥ v) - v ⬝ᵥ (M *ᵥ v) - v ⬝ᵥ (err X M *ᵥ v) := by
  have h : shifted X = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - M - err X M := by
    ext i j
    simp only [shifted, err, of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> ring
  rw [h, sub_mulVec, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]

/-- The error has entries at most `1/n`: `M` is symmetric. -/
theorem abs_err_le {X : Matrix (Fin n) (Fin n) ℚ} {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (hX : Approximates X M) (i j : Fin n) : |err X M i j| ≤ 1 / n := by
  have hM : M j i = M i j := by rw [← transpose_apply M i j, hsym]
  have h1 := abs_le.1 (hX i j)
  have h2 := abs_le.1 (hX j i)
  simp only [err, of_apply]
  rw [abs_le]
  constructor <;> linarith

/-- The answer of the test on `2I - (X + Xᵀ)/2`. -/
theorem test_spec (X : Matrix (Fin n) (Fin n) ℚ) :
    (SoS.PDTestRat.test (shiftedRows (rows X)) = none →
      ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ shifted X *ᵥ v) ∧
    ∀ w, SoS.PDTestRat.test (shiftedRows (rows X)) = some w → ∃ v : Fin n → ℝ, v ≠ 0 ∧
      v ⬝ᵥ shifted X *ᵥ v ≤ 0 := by
  obtain ⟨hnone, hsome⟩ := SoS.PDTestRat.test_spec (shiftedRows (rows X))
    (length_shiftedRows X) (shifted X) (entry_shiftedRows X) (shifted_symm X)
  refine ⟨hnone, fun w hw ↦ ?_⟩
  obtain ⟨v, -, hv, hle⟩ := hsome w hw
  refine ⟨fun i ↦ (v i : ℝ), fun h ↦ hv (funext fun i ↦ ?_), hle⟩
  have hi := congrFun h i
  simp only [Pi.zero_apply] at hi
  exact_mod_cast hi

end AlgAux

open AlgAux in
/-- **The algorithm answers `false`** on approximations of negative semidefinite matrices. -/
theorem specAlg_eq_false {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (hneg : ∀ v, v ⬝ᵥ (M *ᵥ v) ≤ 0) {X : Matrix (Fin n) (Fin n) ℚ} (hX : Approximates X M) :
    specAlg ⟨n, X⟩ = false := by
  change (SoS.PDTestRat.test (shiftedRows (rows X))).isSome = false
  cases hw : SoS.PDTestRat.test (shiftedRows (rows X)) with
  | none => rfl
  | some w =>
    exfalso
    obtain ⟨v, hv, hle⟩ := (test_spec X).2 w hw
    have hpos : 0 < v ⬝ᵥ v :=
      lt_of_le_of_ne (dotProduct_self_nonneg' v) (Ne.symm (dotProduct_self_eq_zero.not.2 hv))
    have herr := abs_le.1 (abs_quad_le (abs_err_le hsym hX) v)
    rw [quad_shifted X M v] at hle
    linarith [hneg v]

open AlgAux in
/-- **The algorithm answers `true`** on approximations of matrices with a large quadratic form. -/
theorem specAlg_eq_true {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hsym : Mᵀ = M)
    (hpos : ∃ v, 3 * (v ⬝ᵥ v) < v ⬝ᵥ (M *ᵥ v)) {X : Matrix (Fin n) (Fin n) ℚ}
    (hX : Approximates X M) : specAlg ⟨n, X⟩ = true := by
  change (SoS.PDTestRat.test (shiftedRows (rows X))).isSome = true
  obtain ⟨v, hv⟩ := hpos
  cases hw : SoS.PDTestRat.test (shiftedRows (rows X)) with
  | some w => rfl
  | none =>
    exfalso
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hq := (test_spec X).1 hw v hv0
    have herr := abs_le.1 (abs_quad_le (abs_err_le hsym hX) v)
    rw [quad_shifted X M v] at hq
    linarith

end BHJK25.Spectral
