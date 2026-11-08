module

public import BS23.Separating.Alg
public import BS23.ColinearSoS.Poly

/-!
# The sum-of-squares programs of the colinear algorithm

The two problems that the algorithm for [BS23, Theorem 1.2] (`BS23/ColinearSoS/Alg.lean`) hands to
the sum-of-squares solver, as raw polynomials (`SoS.Solver.RawPoly`) with rational coefficients in
`d` variables `v`, for whitened points `X₁, …, Xₙ ∈ ℚ^d`, weights `κ ∈ ℚ^d` and a unary budget
`Lb` that cuts the products. The raw pieces are those of `BS23/Separating/Program.lean`
(`BS23.Separating.powRaw`, `BS23.Separating.scaleRaw`, `BS23.Separating.ballRaw`).

* **The constraints** (`BS23.ColinearSoS.progC`): the ball `256 - ∑ᵢ vᵢ² ≥ 0` and the two halves
  `∑ᵢ κᵢ vᵢ² - 1 ≥ 0`, `1 - ∑ᵢ κᵢ vᵢ² ≥ 0` (`BS23.ColinearSoS.sphLoRaw`,
  `BS23.ColinearSoS.sphHiRaw`) of the equality `vᵀ D v = 1`, `D = diag κ`. They do not depend
  on the budget (`BS23.ColinearSoS.system_progC`). The objective is a single polynomial `q₀`,
  with no squared terms (`BS23.ColinearSoS.objective_progC`).
* **Moment polynomials.** `BS23.ColinearSoS.momRaw c Lb r X` is `c ∑ⱼ ⟨Xⱼ, v⟩^r`, exactly when
  `(d + 1)^r ≤ Lb` (`BS23.ColinearSoS.toPoly_momRaw`). Over the reals, `c = 1/n` gives the
  empirical moment polynomial `Φ̂_r = BS23.ColinearSoS.empPoly X r` and `c = -1/n` gives `-Φ̂_r`
  (`BS23.ColinearSoS.toReal_momRaw_inv`, `BS23.ColinearSoS.toReal_momRaw_neg_inv`).
* **The problems.** `BS23.ColinearSoS.probU Lb s X κ` has degree `2s` and objective `-Φ̂_{2s}`
  (it maximizes the `2s`-th directional moment), `BS23.ColinearSoS.probL Lb t X κ` has degree
  `2t` and objective `Φ̂_{2t}` (it minimizes the `2t`-th one).
* **Validity.** A real point `v` with `‖v‖² ≤ 256` and `vᵀ D v = 1` makes both problems valid
  for the solver (`BS23.ColinearSoS.valid_progC`, `BS23.ColinearSoS.valid_probU`,
  `BS23.ColinearSoS.valid_probL`).
* **The budget.** For every problem with at most three constraints, `N` variables and degree
  `ℓ`, the budget `Lb (|P| + 2)³` of `BS23.Separating.solve` suffices when
  `(N + 5)^(ℓ + 1) ≤ Lb` (`BS23.ColinearSoS.budgetOK_solverBudget_of`); so the solver output on
  a valid problem is correct (`BS23.ColinearSoS.correct_solve_progC`).
* **The accuracy** `acc = 2^-(|P|+2)` (`BS23.Separating.acc`) is at most `2^-|q₀|` for the
  number `|q₀|` of terms of the objective (`BS23.ColinearSoS.acc_le_two_pow_length`), so at most
  `2^-n` for both problems when `Lb ≥ 1` (`BS23.ColinearSoS.acc_probU_le`,
  `BS23.ColinearSoS.acc_probL_le`).
* **The specification** (`BS23.ColinearSoS.ProgSpec`, `BS23.ColinearSoS.exists_progSpec`). A
  correct output lists the pseudo-moments of a degree-`2m` pseudo-expectation `Ẽ` that satisfies
  the constraints with slack `2 acc` (`acc = 2^-(|P|+2)`, `BS23.Separating.acc`), has bounded
  values `|Ẽ f| ≤ ‖f‖₁ 258^m` (from the ball), satisfies the equality in the form
  `|Ẽ[h (vᵀDv - 1)]| ≤ 2 acc ‖h‖₂ ‖vᵀDv - 1‖₂` for every sum of squares `h` of degree at most
  `2m - 2` (from the two halves), and is near-optimal: `Ẽ q₀ ≤ q₀(v) + acc` for every real point
  `v` with `‖v‖² ≤ 256` and `vᵀ D v = 1` (the solver's optimality, compared with the evaluation
  at `v`, `SoS.Correct.ofPoint`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open MvPolynomial SoS SoS.Solver SoS.Poly Matrix
open Separating (expAt linQ powRaw scaleRaw ballRaw acc acc_pos solve solverBudget)

variable {n d : ℕ}

/-! ### Rational polynomials -/

/-- `∑ᵢ κᵢ vᵢ²`, with rational coefficients. -/
noncomputable def quadQ (κ : Fin d → ℚ) : MvPolynomial (Fin d) ℚ := ∑ i, C (κ i) * X i ^ 2

/-- `∑ⱼ ⟨Xⱼ, v⟩^r`, with rational coefficients. -/
noncomputable def sumPowQ (X : Fin n → Fin d → ℚ) (r : ℕ) : MvPolynomial (Fin d) ℚ :=
  ∑ j, linQ (X j) ^ r

/-! ### Raw polynomials and the problems -/

/-- The constraint `∑ᵢ κᵢ vᵢ² - 1 ≥ 0`. -/
def sphLoRaw (κ : Fin d → ℚ) : RawPoly :=
  ([], -1) :: (List.finRange d).map fun i : Fin d => (expAt d i 2, κ i)

/-- The constraint `1 - ∑ᵢ κᵢ vᵢ² ≥ 0`. -/
def sphHiRaw (κ : Fin d → ℚ) : RawPoly :=
  ([], 1) :: (List.finRange d).map fun i : Fin d => (expAt d i 2, -κ i)

/-- `c ∑ⱼ ⟨Xⱼ, v⟩^r` as a raw polynomial: the terms of all `⟨Xⱼ, v⟩^r`
(`BS23.Separating.powRaw`), scaled by `c`. -/
def momRaw (c : ℚ) (Lb r : ℕ) (X : Fin n → Fin d → ℚ) : RawPoly :=
  scaleRaw c ((List.finRange n).flatMap fun j => powRaw Lb r (X j))

/-- The problem of degree `ℓ` in `d` variables with the ball `256 - ∑ᵢ vᵢ² ≥ 0` and the equality
`∑ᵢ κᵢ vᵢ² = 1` as constraints, and the objective `Ẽ[obj]` (no squared terms). -/
def progC (ℓ : ℕ) (κ : Fin d → ℚ) (obj : RawPoly) : Problem :=
  (d, ℓ, [ballRaw d, sphLoRaw κ, sphHiRaw κ], (obj, []))

/-- **Program U**: degree `2s`, objective `-Φ̂_{2s} = -(1/n) ∑ⱼ ⟨Xⱼ, v⟩^(2s)`. -/
def probU (Lb s : ℕ) (X : Fin n → Fin d → ℚ) (κ : Fin d → ℚ) : Problem :=
  progC (2 * s) κ (momRaw (-(n : ℚ)⁻¹) Lb (2 * s) X)

/-- **Program L**: degree `2t`, objective `Φ̂_{2t} = (1/n) ∑ⱼ ⟨Xⱼ, v⟩^(2t)`. -/
def probL (Lb t : ℕ) (X : Fin n → Fin d → ℚ) (κ : Fin d → ℚ) : Problem :=
  progC (2 * t) κ (momRaw ((n : ℚ)⁻¹) Lb (2 * t) X)

/-! ### The polynomials of the raw polynomials -/

theorem toPoly_sphLoRaw (κ : Fin d → ℚ) : (sphLoRaw κ).toPoly d = quadQ κ - 1 := by
  rw [sphLoRaw, Separating.toPoly_cons, Separating.termPoly_nil, toPoly_eq_sum', List.map_map,
    quadQ, Fin.sum_univ_def, map_neg, map_one, neg_add_eq_sub]
  congr 2
  refine List.map_congr_left fun k _ => ?_
  simp [termPoly, Separating.toFinsupp_expAt, C_mul_X_pow_eq_monomial]

theorem toPoly_sphHiRaw (κ : Fin d → ℚ) : (sphHiRaw κ).toPoly d = 1 - quadQ κ := by
  rw [sphHiRaw, Separating.toPoly_cons, Separating.termPoly_nil, toPoly_eq_sum', List.map_map,
    quadQ, map_one, sub_eq_add_neg, ← Finset.sum_neg_distrib, Fin.sum_univ_def]
  congr 2
  refine List.map_congr_left fun k _ => ?_
  simp [termPoly, Separating.toFinsupp_expAt, C_mul_X_pow_eq_monomial]

/-- **Moment polynomials**: nothing is cut when `(d + 1)^r ≤ Lb`. -/
theorem toPoly_momRaw {Lb r : ℕ} (h : (d + 1) ^ r ≤ Lb) (c : ℚ) (X : Fin n → Fin d → ℚ) :
    (momRaw c Lb r X).toPoly d = C c * sumPowQ X r := by
  rw [momRaw, Separating.toPoly_scaleRaw, Separating.toPoly_flatMap, sumPowQ, Fin.sum_univ_def]
  congr 2
  exact List.map_congr_left fun j _ => Separating.toPoly_powRaw h (X j)

/-- **The constraints** `256 - ∑ᵢ vᵢ²`, `∑ᵢ κᵢ vᵢ² - 1` and `1 - ∑ᵢ κᵢ vᵢ²`. -/
theorem system_progC (ℓ : ℕ) (κ : Fin d → ℚ) (obj : RawPoly) :
    (progC ℓ κ obj).system = [C 256 - ∑ i : Fin d, X i ^ 2, quadQ κ - 1, 1 - quadQ κ] := by
  change [(ballRaw d).toPoly d, (sphLoRaw κ).toPoly d, (sphHiRaw κ).toPoly d] = _
  rw [Separating.toPoly_ballRaw, toPoly_sphLoRaw, toPoly_sphHiRaw]

theorem ball_mem_system_progC (ℓ : ℕ) (κ : Fin d → ℚ) (obj : RawPoly) :
    (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ) ∈ (progC ℓ κ obj).system := by
  rw [system_progC]
  exact List.mem_cons_self

theorem sphLo_mem_system_progC (ℓ : ℕ) (κ : Fin d → ℚ) (obj : RawPoly) :
    quadQ κ - 1 ∈ (progC ℓ κ obj).system := by
  rw [system_progC]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem sphHi_mem_system_progC (ℓ : ℕ) (κ : Fin d → ℚ) (obj : RawPoly) :
    1 - quadQ κ ∈ (progC ℓ κ obj).system := by
  rw [system_progC]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- **The objective** is `Ẽ[obj]`. -/
theorem objective_progC {ℓ' : ℕ} (ℓ : ℕ) (κ : Fin d → ℚ) (obj : RawPoly)
    (E : PseudoExpectation (Fin d) ℓ') :
    (progC ℓ κ obj).objective E = E (toReal (obj.toPoly d)) := by
  simp only [Problem.objective, progC, List.map_nil, List.sum_nil, add_zero]
  rfl

/-! ### Over the reals -/

namespace Prog

/-- The quadratic form of a diagonal matrix: `vᵀ diag(κ) v = ∑ᵢ κᵢ vᵢ²`. -/
theorem quadPoly_diagonal (κ : Fin d → ℝ) : quadPoly (diagonal κ) = ∑ i, C (κ i) * X i ^ 2 := by
  unfold quadPoly
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [diagonal_apply_ne κ (Ne.symm hb)]; simp)
    (fun h => absurd (Finset.mem_univ a) h), diagonal_apply_eq, mul_assoc, ← sq]

/-- `vᵀ diag(κ) v = ∑ᵢ κᵢ vᵢ²` at a point. -/
theorem eval_quadPoly_diagonal (κ v : Fin d → ℝ) :
    eval v (quadPoly (diagonal κ)) = ∑ i, κ i * v i ^ 2 := by
  simp [quadPoly_diagonal]

end Prog

theorem toReal_quadQ (κ : Fin d → ℚ) :
    toReal (quadQ κ) = quadPoly (diagonal fun i => (κ i : ℝ)) := by
  rw [Prog.quadPoly_diagonal]
  simp [toReal, quadQ]

theorem toReal_C_mul_sumPowQ (c : ℚ) (X : Fin n → Fin d → ℚ) (r : ℕ) :
    toReal (C c * sumPowQ X r) =
      C (c : ℝ) * ∑ j, Separating.lin (fun k => (X j k : ℝ)) ^ r := by
  rw [toReal, map_mul, map_C, sumPowQ, map_sum, eq_ratCast]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_pow, ← toReal, Separating.toReal_linQ]

/-- `c = 1/n` gives the empirical moment polynomial `Φ̂_r`. -/
theorem toReal_momRaw_inv {Lb r : ℕ} (h : (d + 1) ^ r ≤ Lb) (X : Fin n → Fin d → ℚ) :
    toReal ((momRaw ((n : ℚ)⁻¹) Lb r X).toPoly d) = empPoly (fun j k => (X j k : ℝ)) r := by
  rw [toPoly_momRaw h, toReal_C_mul_sumPowQ, empPoly, smul_eq_C_mul]
  push_cast
  rfl

/-- `c = -1/n` gives `-Φ̂_r`. -/
theorem toReal_momRaw_neg_inv {Lb r : ℕ} (h : (d + 1) ^ r ≤ Lb) (X : Fin n → Fin d → ℚ) :
    toReal ((momRaw (-(n : ℚ)⁻¹) Lb r X).toPoly d) = -empPoly (fun j k => (X j k : ℝ)) r := by
  rw [toPoly_momRaw h, toReal_C_mul_sumPowQ, empPoly, smul_eq_C_mul, ← neg_mul, ← map_neg]
  push_cast
  rfl

/-! ### Degrees -/

theorem isHomogeneous_quadQ (κ : Fin d → ℚ) : (quadQ κ).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X_pow i 2).C_mul _

theorem totalDegree_quadQ_sub_one_le (κ : Fin d → ℚ) : (quadQ κ - 1).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le (isHomogeneous_quadQ κ).totalDegree_le
    (by rw [totalDegree_one]; omega))

theorem totalDegree_one_sub_quadQ_le (κ : Fin d → ℚ) : (1 - quadQ κ).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_one]; omega)
    (isHomogeneous_quadQ κ).totalDegree_le)

theorem totalDegree_C_mul_sumPowQ_le (c : ℚ) (X : Fin n → Fin d → ℚ) (r : ℕ) :
    (C c * sumPowQ X r).totalDegree ≤ r :=
  ((IsHomogeneous.sum _ _ _ fun j _ => Separating.isHomogeneous_linQ_pow (X j) r).C_mul
    c).totalDegree_le

theorem totalDegree_momRaw_le {Lb r : ℕ} (h : (d + 1) ^ r ≤ Lb) (c : ℚ)
    (X : Fin n → Fin d → ℚ) : ((momRaw c Lb r X).toPoly d).totalDegree ≤ r := by
  rw [toPoly_momRaw h]
  exact totalDegree_C_mul_sumPowQ_le c X r

/-! ### Validity -/

/-- A real point with `‖v‖² ≤ 256` and `vᵀ diag(κ) v = 1` satisfies the constraints. -/
theorem feasible_progC {ℓ : ℕ} {κ : Fin d → ℚ} {obj : RawPoly} {v : Fin d → ℝ}
    (hball : ∑ i, v i ^ 2 ≤ 256) (hsph : eval v (quadPoly (diagonal fun i => (κ i : ℝ))) = 1) :
    ∀ f ∈ (progC ℓ κ obj).system, 0 ≤ eval v (toReal f) := by
  intro f hf
  rw [system_progC] at hf
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [Separating.eval_toReal_ball]
    linarith
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [toReal, map_sub, map_one, ← toReal, toReal_quadQ, eval_sub, hsph, map_one, sub_self]
  rcases List.mem_cons.1 hf with rfl | hf
  · rw [toReal, map_sub, map_one, ← toReal, toReal_quadQ, eval_sub, hsph, map_one, sub_self]
  · exact absurd hf List.not_mem_nil

/-- **The problem is valid** for the solver if some real point has `‖v‖² ≤ 256` and
`vᵀ diag(κ) v = 1`, the degree `2m` is at least `2` and the objective has degree at most `2m`. -/
theorem valid_progC {m : ℕ} (hm : 1 ≤ m) {κ : Fin d → ℚ} {obj : RawPoly}
    (hobj : (obj.toPoly d).totalDegree ≤ 2 * m) {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal fun i => (κ i : ℝ))) = 1) :
    (progC (2 * m) κ obj).Valid := by
  unfold Problem.Valid
  refine ⟨even_two_mul m, show 2 ≤ 2 * m by omega, ?_, ⟨256, ball_mem_system_progC _ κ obj⟩, v,
    feasible_progC hball hsph⟩
  intro q hq
  obtain rfl : q = obj := by simpa [progC] using hq
  exact hobj

/-- **Program U is valid** if some real point has `‖v‖² ≤ 256` and `vᵀ diag(κ) v = 1`. -/
theorem valid_probU {Lb s : ℕ} (hs : 1 ≤ s) (hLb : (d + 1) ^ (2 * s) ≤ Lb)
    (X : Fin n → Fin d → ℚ) {κ : Fin d → ℚ} {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal fun i => (κ i : ℝ))) = 1) : (probU Lb s X κ).Valid :=
  valid_progC hs (totalDegree_momRaw_le hLb _ X) hball hsph

/-- **Program L is valid** if some real point has `‖v‖² ≤ 256` and `vᵀ diag(κ) v = 1`. -/
theorem valid_probL {Lb t : ℕ} (ht : 1 ≤ t) (hLb : (d + 1) ^ (2 * t) ≤ Lb)
    (X : Fin n → Fin d → ℚ) {κ : Fin d → ℚ} {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal fun i => (κ i : ℝ))) = 1) : (probL Lb t X κ).Valid :=
  valid_progC ht (totalDegree_momRaw_le hLb _ X) hball hsph

/-! ### The solver call -/

/-- **The solver budget suffices** for every problem with at most three constraints, `P.1`
variables and degree `P.2.1`, when `(P.1 + 5)^(P.2.1 + 1) ≤ Lb`. -/
theorem budgetOK_solverBudget_of {P : Problem} {Lb : ℕ} (h3 : P.2.2.1.length ≤ 3)
    (hLb : (P.1 + 5) ^ (P.2.1 + 1) ≤ Lb) : SoS.Correct.BudgetOK P (solverBudget Lb P) := by
  have hpos : 0 < ((encProblem P).length + 2) ^ 3 := pow_pos (by omega) _
  have hLb1 : 0 < Lb := (pow_pos (by omega) _).trans_le hLb
  refine SoS.Correct.budgetOK_of_le ?_ ?_
  · calc (P.1 + P.2.2.1.length + 2) ^ (P.2.1 + 1) ≤ (P.1 + 5) ^ (P.2.1 + 1) :=
          Nat.pow_le_pow_left (by omega) _
      _ ≤ Lb := hLb
      _ ≤ solverBudget Lb P := Nat.le_mul_of_pos_right _ hpos
  · calc ((encProblem P).length + 2) ^ min P.2.2.1.length P.2.1
        ≤ ((encProblem P).length + 2) ^ 3 :=
          Nat.pow_le_pow_right (by omega) ((min_le_left _ _).trans h3)
      _ ≤ solverBudget Lb P := Nat.le_mul_of_pos_left _ hLb1

/-- **The solver output is correct** for a valid problem `progC ℓ κ obj` when
`(d + 5)^(ℓ + 1) ≤ Lb`. -/
theorem correct_solve_progC {ℓ Lb : ℕ} {κ : Fin d → ℚ} {obj : RawPoly}
    (hP : (progC ℓ κ obj).Valid) (hLb : (d + 5) ^ (ℓ + 1) ≤ Lb) :
    Correct (progC ℓ κ obj) (acc (progC ℓ κ obj)) (acc (progC ℓ κ obj))
      (solve Lb (progC ℓ κ obj)) :=
  SoS.Correct.core_correct_of_budget _ hP _ _ (acc_pos _) (acc_pos _)
    (budgetOK_solverBudget_of le_rfl hLb)

/-! ### The accuracy -/

namespace Prog

theorem foldl_sectStep_ne_nil {α : Type} {L : ℕ} (hL : 1 ≤ L) :
    ∀ (ls : List (List α)) (acc : List (List α)), (∀ l ∈ ls, l ≠ []) → acc ≠ [] →
      ls.foldl (sectStep L) acc ≠ []
  | [], _, _, h => h
  | l :: ls, acc, hne, h => by
    rw [List.foldl_cons]
    refine foldl_sectStep_ne_nil hL ls _ (fun l' hl' => hne l' (List.mem_cons_of_mem _ hl')) ?_
    obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil acc h
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l (hne l List.mem_cons_self)
    intro hc
    rcases List.take_eq_nil_iff.1 hc with hc | hc
    · omega
    · have hm : s ++ [a] ∈ acc.flatMap fun s => l.map fun a => s ++ [a] :=
        List.mem_flatMap.2 ⟨s, hs, List.mem_map.2 ⟨a, ha, rfl⟩⟩
      rw [hc] at hm
      exact List.not_mem_nil hm

/-- A power of a linear form keeps at least one term when `Lb ≥ 1`. -/
theorem powRaw_ne_nil {Lb : ℕ} (hLb : 1 ≤ Lb) (p : ℕ) (u : Fin d → ℚ) : powRaw Lb p u ≠ [] := by
  rw [powRaw, prodRaw, sectB, Ne, List.map_eq_nil_iff]
  refine foldl_sectStep_ne_nil hLb _ _ (fun f hf => ?_) (List.cons_ne_nil _ _)
  rw [List.eq_of_mem_replicate hf, Separating.linRaw]
  exact List.cons_ne_nil _ _

end Prog

/-- `c ∑ⱼ ⟨Xⱼ, v⟩^r` has at least `n` terms when `Lb ≥ 1`. -/
theorem le_length_momRaw {Lb : ℕ} (hLb : 1 ≤ Lb) (c : ℚ) (r : ℕ) (X : Fin n → Fin d → ℚ) :
    n ≤ (momRaw c Lb r X).length := by
  rw [momRaw, scaleRaw, List.length_map, List.length_flatMap]
  have h := List.length_le_sum_of_one_le ((List.finRange n).map fun j => (powRaw Lb r (X j)).length)
    (fun i hi => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hi
      exact List.length_pos_iff.2 (Prog.powRaw_ne_nil hLb r (X j)))
  rwa [List.length_map, List.length_finRange] at h

/-- **The accuracy is tiny**: `acc P = 2^-(|P|+2) ≤ 2^-|q₀|` for the number `|q₀|` of terms of the
objective. -/
theorem acc_le_two_pow_length (P : Problem) : (acc P : ℝ) ≤ 1 / 2 ^ P.2.2.2.1.length := by
  rw [Separating.cast_acc]
  have h : P.2.2.2.1.length ≤ (encProblem P).length + 2 :=
    ((SoS.Correct.length_le_encRaw _).trans
      (SoS.Correct.length_encRaw_obj_le List.mem_cons_self)).trans (Nat.le_add_right _ 2)
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) h)

/-- The accuracy of program U is at most `2^-n` when `Lb ≥ 1`. -/
theorem acc_probU_le {Lb : ℕ} (hLb : 1 ≤ Lb) (s : ℕ) (X : Fin n → Fin d → ℚ) (κ : Fin d → ℚ) :
    (acc (probU Lb s X κ) : ℝ) ≤ 1 / 2 ^ n :=
  (acc_le_two_pow_length _).trans (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (le_length_momRaw hLb _ _ X)))

/-- The accuracy of program L is at most `2^-n` when `Lb ≥ 1`. -/
theorem acc_probL_le {Lb : ℕ} (hLb : 1 ≤ Lb) (t : ℕ) (X : Fin n → Fin d → ℚ) (κ : Fin d → ℚ) :
    (acc (probL Lb t X κ) : ℝ) ≤ 1 / 2 ^ n :=
  (acc_le_two_pow_length _).trans (one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num) (le_length_momRaw hLb _ _ X)))

/-! ### The specification -/

/-- What the analysis uses about a correct solver output `out` of the problem `progC (2m) κ obj`,
for the pseudo-expectation `Ẽ` behind it, with `D = diag κ` (over the reals) and
`acc = BS23.Separating.acc (progC (2m) κ obj)`. -/
structure ProgSpec (m : ℕ) (κ : Fin d → ℚ) (obj : RawPoly) (out : SoS.Solver.Output)
    (E : PseudoExpectation (Fin d) (2 * m)) : Prop where
  /-- The output lists the pseudo-moments of `Ẽ`. -/
  moments : HasMoments E (out.toPoly d)
  /-- `Ẽ` satisfies the constraints with slack `2 acc`. -/
  approx : E.ApproxSatisfies (progC (2 * m) κ obj).system (2 * (acc (progC (2 * m) κ obj) : ℝ)) 0
  /-- `|Ẽ f| ≤ ‖f‖₁ 258^m` for `deg f ≤ 2m`. -/
  bound : ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ 2 * m → |E f| ≤ coeffNorm1 f * 258 ^ m
  /-- The equality `vᵀ D v = 1`: `|Ẽ[h (vᵀDv - 1)]| ≤ 2 acc ‖h‖₂ ‖vᵀDv - 1‖₂` for every sum of
  squares `h` of degree at most `2m - 2`. -/
  sph : ∀ h : MvPolynomial (Fin d) ℝ, IsSumSq h → h.totalDegree + 2 ≤ 2 * m →
    |E (h * (quadPoly (diagonal fun i => (κ i : ℝ)) - 1))| ≤
      2 * (acc (progC (2 * m) κ obj) : ℝ) * coeffNorm h *
        coeffNorm (quadPoly (diagonal fun i => (κ i : ℝ)) - 1)
  /-- **Near-optimality**: `Ẽ[obj] ≤ obj(v) + acc` for every real point `v` with `‖v‖² ≤ 256`
  and `vᵀ D v = 1`. -/
  opt : ∀ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 →
    eval v (quadPoly (diagonal fun i => (κ i : ℝ))) = 1 →
      E (toReal (obj.toPoly d)) ≤ eval v (toReal (obj.toPoly d)) + acc (progC (2 * m) κ obj)

namespace Prog

theorem coeffNorm_neg (p : MvPolynomial (Fin d) ℝ) : coeffNorm (-p) = coeffNorm p := by
  simp [coeffNorm, support_neg]

/-- A constraint `f ≥ 0` that `Ẽ` satisfies up to `η`, with a sum-of-squares multiplier `h`:
`Ẽ[h f] ≥ -η ‖h‖₂ ‖f‖₂`. -/
theorem neg_le_apply_mul_of_mem {K : Type*} [Field K] [Algebra K ℝ] {ℓ : ℕ}
    {E : PseudoExpectation (Fin d) ℓ} {A : System (Fin d) K} {η : ℝ} {r : ℕ}
    (hE : E.ApproxSatisfies A η r) {f : MvPolynomial (Fin d) K} (hf : f ∈ A)
    {h : MvPolynomial (Fin d) ℝ} (hh : IsSumSq h) (hdeg : h.totalDegree + max f.totalDegree r ≤ ℓ) :
    -(η * coeffNorm h * coeffNorm (toReal f)) ≤ E (h * toReal f) := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  have h1 := hE {i} h hh (by rwa [Finset.sum_singleton])
  rwa [Finset.prod_singleton, System.prod, Finset.prod_singleton] at h1

/-- The ball bound of `BS23.ColinearSoS.ProgSpec`. -/
theorem bound_of_approx {m : ℕ} {κ : Fin d → ℚ} {obj : RawPoly}
    {E : PseudoExpectation (Fin d) (2 * m)}
    (happrox : E.ApproxSatisfies (progC (2 * m) κ obj).system
      ((acc (progC (2 * m) κ obj) : ℝ) + acc (progC (2 * m) κ obj)) 0)
    {f : MvPolynomial (Fin d) ℝ} (hf : f.totalDegree ≤ 2 * m) :
    |E f| ≤ coeffNorm1 f * 258 ^ m := by
  have hη : (0 : ℝ) ≤ (acc (progC (2 * m) κ obj) : ℝ) + acc (progC (2 * m) κ obj) := by
    have : (0 : ℝ) < (acc (progC (2 * m) κ obj) : ℝ) := by exact_mod_cast acc_pos _
    linarith
  have hb : |E f| ≤ coeffNorm1 f * (1 + |algebraMap ℚ ℝ 256| +
      ((acc (progC (2 * m) κ obj) : ℝ) + acc (progC (2 * m) κ obj)) *
        coeffNorm (toReal (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ))) ^ (2 * m / 2) :=
    E.abs_apply_le (even_two_mul m) hη happrox (ball_mem_system_progC _ κ obj) hf
  have hslack : ((acc (progC (2 * m) κ obj) : ℝ) + acc (progC (2 * m) κ obj)) *
      coeffNorm (toReal (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ)) ≤ 1 / 2 :=
    Separating.acc_add_acc_mul_coeffNorm_le (ball_mem_system_progC (2 * m) κ obj)
  rw [Nat.mul_div_cancel_left m two_pos] at hb
  refine hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (add_nonneg (by positivity) (mul_nonneg hη (coeffNorm_nonneg _))) ?_ m)
    (coeffNorm1_nonneg _))
  have h256 : |(algebraMap ℚ ℝ) 256| = 256 := by norm_num
  rw [h256]
  linarith

/-- The equality constraint of `BS23.ColinearSoS.ProgSpec`, from its two halves. -/
theorem sph_of_approx {m : ℕ} {κ : Fin d → ℚ} {obj : RawPoly}
    {E : PseudoExpectation (Fin d) (2 * m)} {η : ℝ}
    (happrox : E.ApproxSatisfies (progC (2 * m) κ obj).system η 0)
    {h : MvPolynomial (Fin d) ℝ} (hh : IsSumSq h) (hdeg : h.totalDegree + 2 ≤ 2 * m) :
    |E (h * (quadPoly (diagonal fun i => (κ i : ℝ)) - 1))| ≤
      η * coeffNorm h * coeffNorm (quadPoly (diagonal fun i => (κ i : ℝ)) - 1) := by
  have hlo := neg_le_apply_mul_of_mem happrox (sphLo_mem_system_progC (2 * m) κ obj) hh
    (by have := totalDegree_quadQ_sub_one_le κ; omega)
  have hhi := neg_le_apply_mul_of_mem happrox (sphHi_mem_system_progC (2 * m) κ obj) hh
    (by have := totalDegree_one_sub_quadQ_le κ; omega)
  have e1 : toReal (quadQ κ - 1) = quadPoly (diagonal fun i => (κ i : ℝ)) - 1 := by
    rw [toReal, map_sub, map_one, ← toReal, toReal_quadQ]
  have e2 : toReal (1 - quadQ κ) = -(quadPoly (diagonal fun i => (κ i : ℝ)) - 1) := by
    rw [toReal, map_sub, map_one, ← toReal, toReal_quadQ, neg_sub]
  rw [e1] at hlo
  rw [e2, coeffNorm_neg, mul_neg, E.map_neg] at hhi
  rw [abs_le]
  constructor <;> linarith

/-- Near-optimality of `BS23.ColinearSoS.ProgSpec`: the solver's optimality against the
evaluation at a feasible point. -/
theorem opt_of_le {m : ℕ} {κ : Fin d → ℚ} {obj : RawPoly} {E : PseudoExpectation (Fin d) (2 * m)}
    (hopt : ∀ E' : PseudoExpectation (Fin d) (2 * m),
      E'.ApproxSatisfies (progC (2 * m) κ obj).system (acc (progC (2 * m) κ obj)) 0 →
        (progC (2 * m) κ obj).objective E ≤
          (progC (2 * m) κ obj).objective E' + acc (progC (2 * m) κ obj))
    {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal fun i => (κ i : ℝ))) = 1) :
    E (toReal (obj.toPoly d)) ≤ eval v (toReal (obj.toPoly d)) + acc (progC (2 * m) κ obj) := by
  have hacc : (0 : ℝ) ≤ (acc (progC (2 * m) κ obj) : ℝ) := by exact_mod_cast (acc_pos _).le
  have hpt := hopt (SoS.Correct.ofPoint (2 * m) v)
    (SoS.Correct.ofPoint_approxSatisfies (feasible_progC hball hsph) hacc)
  rw [objective_progC, objective_progC, SoS.Correct.ofPoint_apply] at hpt
  exact hpt

end Prog

/-- **The specification of a correct output**: the pseudo-expectation behind it has the
properties of `BS23.ColinearSoS.ProgSpec`. -/
theorem exists_progSpec {m : ℕ} {κ : Fin d → ℚ} {obj : RawPoly} {out : SoS.Solver.Output}
    (hC : Correct (progC (2 * m) κ obj) (acc (progC (2 * m) κ obj)) (acc (progC (2 * m) κ obj))
      out) :
    ∃ E : PseudoExpectation (Fin d) (2 * m), ProgSpec m κ obj out E := by
  obtain ⟨E, hmom, happrox, hopt⟩ := hC
  have happrox2 : E.ApproxSatisfies (progC (2 * m) κ obj).system
      (2 * (acc (progC (2 * m) κ obj) : ℝ)) 0 := by
    rw [two_mul ((acc (progC (2 * m) κ obj) : ℚ) : ℝ)]
    exact happrox
  exact ⟨E, hmom, happrox2, fun f hf => Prog.bound_of_approx happrox hf,
    fun h hh hdeg => Prog.sph_of_approx happrox2 hh hdeg,
    fun v hball hsph => Prog.opt_of_le hopt hball hsph⟩

end BS23.ColinearSoS
