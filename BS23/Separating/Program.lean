module

public import BS23.Separating.Whiten
public import Background.SumOfSquares.Algorithm.Correct
public import Background.SumOfSquares.PseudoBounds

/-!
# The sum-of-squares program of the separating algorithm

Step 3 of the algorithm for [BS23, Theorem 1.1]: the problem handed to the sum-of-squares solver,
as raw polynomials (`SoS.Solver.RawPoly`) with rational coefficients, in `d` variables `v`, for
whitened points `Z₁, …, Zₙ ∈ ℚ^d`, degrees `s ≤ t` and a unary budget `Lb` that cuts the
products (`SoS.Poly.prodRaw`).

* `BS23.Separating.linRaw u`: the linear form `⟨u, v⟩ = ∑ₖ uₖ vₖ` (`BS23.Separating.linQ u`). Its
  first term is a dummy zero constant, so that it is never empty, as `SoS.Poly.toPoly_prodRaw`
  needs (also for `d = 0`).
* `BS23.Separating.powRaw Lb p u`: `⟨u, v⟩^p`, a product of `p` copies of `linRaw u`; it is exact
  when `(d + 1)^p ≤ Lb` (`BS23.Separating.toPoly_powRaw`).
* `BS23.Separating.pairRaw Lb p Z`: the pair moment polynomial
  `F_p = n⁻² ∑_{i,j} ⟨Zᵢ - Zⱼ, v⟩^p` (`BS23.Separating.pairQ`, `BS23.Separating.toPoly_pairRaw`).
* The constraints: the ball `256 - ∑ₖ vₖ² ≥ 0` (`BS23.Separating.ballRaw`), the lower bound
  `F_{2s} - 1 ≥ 0` (`BS23.Separating.lowRaw`) and the upper bound `1024^t - F_{2t} ≥ 0`
  (`BS23.Separating.highRaw`). The problem `BS23.Separating.prob` has degree `2t`, these three
  constraints and the zero objective.
* **Validity.** A real point where the three constraints hold makes the problem valid for the
  solver (`BS23.Separating.valid_of_feasible`, `BS23.Separating.valid_of_eval`).
* **Accuracy.** The constraints have coefficient norm at most `2^|P|`
  (`BS23.Separating.coeffNorm_le_of_mem_system`), so with the accuracies
  `η = γ = 2^-(|P|+2)` (`BS23.Separating.acc`) the slack `(η + γ) ‖fᵢ‖₂` of each constraint is at
  most `1/2` (`BS23.Separating.acc_add_acc_mul_coeffNorm_le`). For a pseudo-expectation that
  satisfies the system that approximately, `Ẽ F_{2s} ≥ 1/2`, `Ẽ F_{2t} ≤ 1024^t + 1/2` and
  `|Ẽ f| ≤ ‖f‖₁ 258^t` (`BS23.Separating.ApproxBounds`, `BS23.Separating.approxBounds`).
* **The solver call** `BS23.Separating.solve Lb P = SoS.Core.core ((P, acc, acc), Lb (|P|+2)³)`;
  this budget suffices for the solver when `Lb ≥ (d + 5)^(2t+1)`
  (`BS23.Separating.budgetOK_solverBudget`).
-/

@[expose] public section

namespace BS23.Separating

open MvPolynomial SoS SoS.Solver SoS.Poly

variable {n d : ℕ}

/-! ### Raw polynomials -/

/-- The exponent vector of `X_k^e` in `d` variables: `e` at position `k`, `0` elsewhere. -/
def expAt (d k e : ℕ) : List ℕ := (List.range d).map fun i => if i = k then e else 0

theorem toFinsupp_expAt (k : Fin d) (e : ℕ) :
    Mono.toFinsupp d (expAt d k e) = Finsupp.single k e := by
  ext i
  rw [Mono.toFinsupp_apply, expAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.2, Option.map_some, Option.getD_some, Finsupp.single_apply]
  by_cases h : i = k
  · subst h
    simp
  · have h' : (i : ℕ) ≠ k := fun h' => h (Fin.ext h')
    simp [h', Ne.symm h]

theorem toFinsupp_nil : Mono.toFinsupp d [] = 0 := by
  ext i
  simp

/-- A term with no exponents is a constant. -/
theorem termPoly_nil (c : ℚ) : termPoly d ([], c) = C c := by
  rw [termPoly, toFinsupp_nil, ← C_apply]

theorem toPoly_nil : RawPoly.toPoly d [] = 0 := by
  simp [RawPoly.toPoly]

theorem toPoly_cons (t : List ℕ × ℚ) (p : RawPoly) :
    RawPoly.toPoly d (t :: p) = termPoly d t + p.toPoly d := by
  rw [toPoly_eq_sum', toPoly_eq_sum', List.map_cons, List.sum_cons]

theorem toPoly_flatMap {α : Type*} (l : List α) (g : α → RawPoly) :
    RawPoly.toPoly d (l.flatMap g) = (l.map fun a => (g a).toPoly d).sum := by
  induction l with
  | nil => simp [RawPoly.toPoly]
  | cons a l ih => rw [List.flatMap_cons, toPoly_append, ih, List.map_cons, List.sum_cons]

/-- All coefficients multiplied by `c`. -/
def scaleRaw (c : ℚ) (f : RawPoly) : RawPoly := f.map fun t => (t.1, c * t.2)

theorem toPoly_scaleRaw (c : ℚ) (f : RawPoly) : (scaleRaw c f).toPoly d = C c * f.toPoly d := by
  rw [toPoly_eq_sum', toPoly_eq_sum', scaleRaw, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp [termPoly, C_mul_monomial]

/-! ### Linear forms, their powers, and pair moments -/

/-- The linear form `⟨u, v⟩ = ∑ₖ uₖ vₖ`, with rational coefficients. -/
noncomputable def linQ (u : Fin d → ℚ) : MvPolynomial (Fin d) ℚ := ∑ k, C (u k) * X k

/-- The linear form `⟨u, v⟩` as a raw polynomial. The first term, a zero constant, keeps it
nonempty. -/
def linRaw (u : Fin d → ℚ) : RawPoly :=
  ([], 0) :: (List.finRange d).map fun k : Fin d => (expAt d k 1, u k)

theorem length_linRaw (u : Fin d → ℚ) : (linRaw u).length = d + 1 := by
  simp [linRaw]

theorem toPoly_linRaw (u : Fin d → ℚ) : (linRaw u).toPoly d = linQ u := by
  rw [linRaw, toPoly_cons, termPoly_nil, map_zero, zero_add, toPoly_eq_sum', List.map_map, linQ,
    Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp [termPoly, toFinsupp_expAt, C_mul_X_eq_monomial]

/-- `⟨u, v⟩^p` as a raw polynomial: the products of `p` terms of `linRaw u`, at most `Lb` of
them. -/
def powRaw (Lb p : ℕ) (u : Fin d → ℚ) : RawPoly := prodRaw d Lb (List.replicate p (linRaw u))

/-- **Powers of a linear form**: nothing is cut when `(d + 1)^p ≤ Lb`. -/
theorem toPoly_powRaw {Lb p : ℕ} (h : (d + 1) ^ p ≤ Lb) (u : Fin d → ℚ) :
    (powRaw Lb p u).toPoly d = linQ u ^ p := by
  have hne : ∀ f ∈ List.replicate p (linRaw u), f ≠ [] := fun f hf => by
    rw [List.eq_of_mem_replicate hf, linRaw]
    exact List.cons_ne_nil _ _
  have hL : ((List.replicate p (linRaw u)).map List.length).prod ≤ Lb := by
    rwa [List.map_replicate, List.prod_replicate, length_linRaw]
  rw [powRaw, toPoly_prodRaw hne hL, List.map_replicate, List.prod_replicate, toPoly_linRaw]

/-- The pair moment polynomial `F_p = n⁻² ∑_{i,j} ⟨Zᵢ - Zⱼ, v⟩^p`, with rational coefficients. -/
noncomputable def pairQ (p : ℕ) (Z : Fin n → Fin d → ℚ) : MvPolynomial (Fin d) ℚ :=
  C ((n : ℚ) ^ 2)⁻¹ * ∑ i, ∑ j, linQ (Z i - Z j) ^ p

/-- The pair moment polynomial `F_p` as a raw polynomial. -/
def pairRaw (Lb p : ℕ) (Z : Fin n → Fin d → ℚ) : RawPoly :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    scaleRaw ((n : ℚ) ^ 2)⁻¹ (powRaw Lb p (Z i - Z j))

/-- **Pair moments**: nothing is cut when `(d + 1)^p ≤ Lb`. -/
theorem toPoly_pairRaw {Lb p : ℕ} (h : (d + 1) ^ p ≤ Lb) (Z : Fin n → Fin d → ℚ) :
    (pairRaw Lb p Z).toPoly d = pairQ p Z := by
  rw [pairRaw, toPoly_flatMap, pairQ, Finset.mul_sum, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  rw [toPoly_flatMap, Finset.mul_sum, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [toPoly_scaleRaw, toPoly_powRaw h]

theorem isHomogeneous_linQ (u : Fin d → ℚ) : (linQ u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _

theorem isHomogeneous_linQ_pow (u : Fin d → ℚ) (p : ℕ) : (linQ u ^ p).IsHomogeneous p := by
  simpa using (isHomogeneous_linQ u).pow p

theorem isHomogeneous_pairQ (p : ℕ) (Z : Fin n → Fin d → ℚ) : (pairQ p Z).IsHomogeneous p :=
  (IsHomogeneous.sum _ _ _ fun _ _ => IsHomogeneous.sum _ _ _ fun _ _ =>
    isHomogeneous_linQ_pow _ p).C_mul _

/-! ### The constraints and the problem -/

/-- The ball constraint `256 - ∑ₖ vₖ² ≥ 0`. -/
def ballRaw (d : ℕ) : RawPoly :=
  ([], 256) :: (List.finRange d).map fun k : Fin d => (expAt d k 2, -1)

/-- The lower bound `F_{2s} - 1 ≥ 0`. -/
def lowRaw (Lb s : ℕ) (Z : Fin n → Fin d → ℚ) : RawPoly := pairRaw Lb (2 * s) Z ++ [([], -1)]

/-- The upper bound `1024^t - F_{2t} ≥ 0`. -/
def highRaw (Lb t : ℕ) (Z : Fin n → Fin d → ℚ) : RawPoly :=
  ([], 1024 ^ t) :: scaleRaw (-1) (pairRaw Lb (2 * t) Z)

/-- **The problem**: degree `2t`, in `d` variables, with the ball, the lower bound and the upper
bound as constraints, and the zero objective. -/
def prob (Lb s t : ℕ) (Z : Fin n → Fin d → ℚ) : Problem :=
  (d, 2 * t, [ballRaw d, lowRaw Lb s Z, highRaw Lb t Z], ([], []))

theorem toPoly_ballRaw : (ballRaw d).toPoly d = C 256 - ∑ i : Fin d, X i ^ 2 := by
  rw [ballRaw, toPoly_cons, termPoly_nil, toPoly_eq_sum', List.map_map, sub_eq_add_neg,
    ← Finset.sum_neg_distrib, Fin.sum_univ_def]
  congr 2
  refine List.map_congr_left fun k _ => ?_
  simp [termPoly, toFinsupp_expAt, X_pow_eq_monomial]

theorem toPoly_lowRaw {Lb s : ℕ} (h : (d + 1) ^ (2 * s) ≤ Lb) (Z : Fin n → Fin d → ℚ) :
    (lowRaw Lb s Z).toPoly d = pairQ (2 * s) Z - 1 := by
  rw [lowRaw, toPoly_append, toPoly_pairRaw h, toPoly_cons, termPoly_nil, toPoly_nil, add_zero,
    map_neg, map_one, sub_eq_add_neg]

theorem toPoly_highRaw {Lb t : ℕ} (h : (d + 1) ^ (2 * t) ≤ Lb) (Z : Fin n → Fin d → ℚ) :
    (highRaw Lb t Z).toPoly d = C (1024 ^ t) - pairQ (2 * t) Z := by
  rw [highRaw, toPoly_cons, termPoly_nil, toPoly_scaleRaw, toPoly_pairRaw h, map_neg, map_one,
    neg_one_mul, sub_eq_add_neg]

theorem system_prob (Lb s t : ℕ) (Z : Fin n → Fin d → ℚ) :
    (prob Lb s t Z).system =
      [(ballRaw d).toPoly d, (lowRaw Lb s Z).toPoly d, (highRaw Lb t Z).toPoly d] :=
  rfl

/-- **The constraints** `256 - ∑ₖ vₖ²`, `F_{2s} - 1` and `1024^t - F_{2t}`, when nothing is
cut. -/
theorem system_prob_eq {Lb s t : ℕ} (hs : (d + 1) ^ (2 * s) ≤ Lb) (ht : (d + 1) ^ (2 * t) ≤ Lb)
    (Z : Fin n → Fin d → ℚ) :
    (prob Lb s t Z).system =
      [C 256 - ∑ i : Fin d, X i ^ 2, pairQ (2 * s) Z - 1, C (1024 ^ t) - pairQ (2 * t) Z] := by
  rw [system_prob, toPoly_ballRaw, toPoly_lowRaw hs, toPoly_highRaw ht]

/-- **Membership in the system**, when nothing is cut. -/
theorem mem_system_prob {Lb s t : ℕ} (hs : (d + 1) ^ (2 * s) ≤ Lb) (ht : (d + 1) ^ (2 * t) ≤ Lb)
    {Z : Fin n → Fin d → ℚ} {f : MvPolynomial (Fin d) ℚ} :
    f ∈ (prob Lb s t Z).system ↔ f = C 256 - ∑ i : Fin d, X i ^ 2 ∨ f = pairQ (2 * s) Z - 1 ∨
      f = C (1024 ^ t) - pairQ (2 * t) Z := by
  have h : f ∈ (prob Lb s t Z).system ↔ f ∈ ([C 256 - ∑ i : Fin d, X i ^ 2, pairQ (2 * s) Z - 1,
      C (1024 ^ t) - pairQ (2 * t) Z] : List (MvPolynomial (Fin d) ℚ)) := by
    rw [system_prob_eq hs ht]
    exact Iff.rfl
  rw [h]
  simp

theorem ball_mem_system (Lb s t : ℕ) (Z : Fin n → Fin d → ℚ) :
    (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ) ∈ (prob Lb s t Z).system := by
  rw [system_prob, toPoly_ballRaw]
  exact List.mem_cons_self

theorem lowQ_mem_system {Lb s t : ℕ} (hs : (d + 1) ^ (2 * s) ≤ Lb) (Z : Fin n → Fin d → ℚ) :
    (pairQ (2 * s) Z - 1 : MvPolynomial (Fin d) ℚ) ∈ (prob Lb s t Z).system := by
  rw [system_prob, toPoly_lowRaw hs]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem highQ_mem_system {Lb s t : ℕ} (ht : (d + 1) ^ (2 * t) ≤ Lb) (Z : Fin n → Fin d → ℚ) :
    (C (1024 ^ t) - pairQ (2 * t) Z : MvPolynomial (Fin d) ℚ) ∈ (prob Lb s t Z).system := by
  rw [system_prob, toPoly_highRaw ht]
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-! ### Degrees -/

theorem totalDegree_ball_le :
    (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ).totalDegree ≤ 2 :=
  (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega)
    (IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow i 2).totalDegree_le)

theorem totalDegree_lowQ_le (s : ℕ) (Z : Fin n → Fin d → ℚ) :
    (pairQ (2 * s) Z - 1).totalDegree ≤ 2 * s :=
  (totalDegree_sub _ _).trans (max_le (isHomogeneous_pairQ _ _).totalDegree_le
    (by rw [totalDegree_one]; omega))

theorem totalDegree_highQ_le (t : ℕ) (Z : Fin n → Fin d → ℚ) :
    (C (1024 ^ t) - pairQ (2 * t) Z).totalDegree ≤ 2 * t :=
  (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_C]; omega)
    (isHomogeneous_pairQ _ _).totalDegree_le)

/-- **Every constraint has degree at most `2t`**, when nothing is cut and `1 ≤ t`, `s ≤ t`. -/
theorem totalDegree_le_of_mem_system {Lb s t : ℕ} (ht1 : 1 ≤ t) (hst : s ≤ t)
    (hs : (d + 1) ^ (2 * s) ≤ Lb) (ht : (d + 1) ^ (2 * t) ≤ Lb) {Z : Fin n → Fin d → ℚ}
    {f : MvPolynomial (Fin d) ℚ} (hf : f ∈ (prob Lb s t Z).system) : f.totalDegree ≤ 2 * t := by
  rcases (mem_system_prob hs ht).1 hf with rfl | rfl | rfl
  · exact totalDegree_ball_le.trans (by omega)
  · exact (totalDegree_lowQ_le s Z).trans (by omega)
  · exact totalDegree_highQ_le t Z

/-! ### Validity -/

/-- **The problem is valid** for the solver as soon as some real point satisfies the
constraints (and `t ≥ 1`): the degree `2t` is even and at least `2`, the objective is zero, and
the ball constraint is in the system. -/
theorem valid_of_feasible {Lb s t : ℕ} {Z : Fin n → Fin d → ℚ} (ht : 1 ≤ t) {v : Fin d → ℝ}
    (hv : ∀ f ∈ (prob Lb s t Z).system, 0 ≤ eval v (toReal f)) : (prob Lb s t Z).Valid := by
  unfold Problem.Valid
  refine ⟨even_two_mul t, show 2 ≤ 2 * t by omega, ?_, ⟨256, ball_mem_system Lb s t Z⟩, v, hv⟩
  intro q hq
  obtain rfl : q = [] := by simpa [prob] using hq
  simp [RawPoly.toPoly]

theorem eval_toReal_ball (v : Fin d → ℝ) :
    eval v (toReal (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ)) =
      256 - ∑ i, v i ^ 2 := by
  simp [toReal]

theorem eval_toReal_lowQ (s : ℕ) (Z : Fin n → Fin d → ℚ) (v : Fin d → ℝ) :
    eval v (toReal (pairQ (2 * s) Z - 1)) = eval v (toReal (pairQ (2 * s) Z)) - 1 := by
  simp [toReal]

theorem eval_toReal_highQ (t : ℕ) (Z : Fin n → Fin d → ℚ) (v : Fin d → ℝ) :
    eval v (toReal (C (1024 ^ t) - pairQ (2 * t) Z)) =
      1024 ^ t - eval v (toReal (pairQ (2 * t) Z)) := by
  simp [toReal]

/-- **Validity from a feasible point**: `‖v‖² ≤ 256`, `F_{2s}(v) ≥ 1` and `F_{2t}(v) ≤ 1024^t`. -/
theorem valid_of_eval {Lb s t : ℕ} {Z : Fin n → Fin d → ℚ} (ht1 : 1 ≤ t)
    (hs : (d + 1) ^ (2 * s) ≤ Lb) (ht : (d + 1) ^ (2 * t) ≤ Lb) {v : Fin d → ℝ}
    (hball : ∑ i, v i ^ 2 ≤ 256) (hlow : 1 ≤ eval v (toReal (pairQ (2 * s) Z)))
    (hhigh : eval v (toReal (pairQ (2 * t) Z)) ≤ 1024 ^ t) : (prob Lb s t Z).Valid := by
  refine valid_of_feasible ht1 (v := v) fun f hf => ?_
  rcases (mem_system_prob hs ht).1 hf with rfl | rfl | rfl
  · have h := eval_toReal_ball v
    exact (show (0 : ℝ) ≤ eval v (toReal (C 256 - ∑ i : Fin d, X i ^ 2 : MvPolynomial (Fin d) ℚ))
      by rw [h]; linarith)
  · have h := eval_toReal_lowQ s Z v
    exact (show (0 : ℝ) ≤ eval v (toReal (pairQ (2 * s) Z - 1)) by rw [h]; linarith)
  · have h := eval_toReal_highQ t Z v
    exact (show (0 : ℝ) ≤ eval v (toReal (C (1024 ^ t) - pairQ (2 * t) Z)) by rw [h]; linarith)

/-! ### Coefficient norms and accuracies -/

/-- **The constraints of a problem have coefficient norm at most `2^|P|`.** -/
theorem coeffNorm_le_of_mem_system {P : Problem} {f : MvPolynomial (Fin P.numVars) ℚ}
    (hf : f ∈ P.system) : coeffNorm (toReal f) ≤ 2 ^ (encProblem P).length := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  exact (SoS.Correct.coeffNorm_le_coeffNorm1 _).trans ((SoS.Correct.coeffNorm1_toReal_le _ _).trans
    ((SoS.Correct.rawNorm1_le g).trans
      (pow_le_pow_right₀ (by norm_num) (SoS.Correct.length_encRaw_le_of_mem hg))))

/-- The accuracies `η = γ = 2^-(|P|+2)` given to the solver. -/
def acc (P : Problem) : ℚ := 1 / 2 ^ ((encProblem P).length + 2)

theorem acc_pos (P : Problem) : 0 < acc P := by
  unfold acc
  positivity

theorem cast_acc (P : Problem) : ((acc P : ℚ) : ℝ) = 1 / 2 ^ ((encProblem P).length + 2) := by
  simp [acc]

/-- **The slack of each constraint is at most `1/2`**: `(η + γ) ‖f‖₂ ≤ 1/2`. -/
theorem acc_add_acc_mul_coeffNorm_le {P : Problem} {f : MvPolynomial (Fin P.numVars) ℚ}
    (hf : f ∈ P.system) : ((acc P : ℝ) + acc P) * coeffNorm (toReal f) ≤ 1 / 2 := by
  have h := coeffNorm_le_of_mem_system hf
  rw [cast_acc]
  calc (1 / 2 ^ ((encProblem P).length + 2) + 1 / 2 ^ ((encProblem P).length + 2) : ℝ) *
        coeffNorm (toReal f)
      ≤ (1 / 2 ^ ((encProblem P).length + 2) + 1 / 2 ^ ((encProblem P).length + 2)) *
          2 ^ (encProblem P).length :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / 2 := by
        rw [pow_add]
        field_simp
        norm_num

/-- The slack of each constraint of `prob Lb s t Z` is at most `1/2`. -/
theorem acc_add_acc_mul_coeffNorm_le_prob {Lb s t : ℕ} {Z : Fin n → Fin d → ℚ}
    {f : MvPolynomial (Fin d) ℚ} (hf : f ∈ (prob Lb s t Z).system) :
    ((acc (prob Lb s t Z) : ℝ) + acc (prob Lb s t Z)) * coeffNorm (toReal f) ≤ 1 / 2 :=
  acc_add_acc_mul_coeffNorm_le hf

/-- What a pseudo-expectation that satisfies the system with slack `2 acc` gives: the lower and
upper bounds on `Ẽ F_{2s}` and `Ẽ F_{2t}`, and bounded values from the ball. -/
structure ApproxBounds (s t : ℕ) (Z : Fin n → Fin d → ℚ)
    (E : PseudoExpectation (Fin d) (2 * t)) : Prop where
  /-- `Ẽ F_{2s} ≥ 1/2`. -/
  low : 1 / 2 ≤ E (toReal (pairQ (2 * s) Z))
  /-- `Ẽ F_{2t} ≤ 1024^t + 1/2`. -/
  high : E (toReal (pairQ (2 * t) Z)) ≤ 1024 ^ t + 1 / 2
  /-- `|Ẽ f| ≤ ‖f‖₁ 258^t` for `deg f ≤ 2t`. -/
  bound : ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ 2 * t → |E f| ≤ coeffNorm1 f * 258 ^ t

/-- **The bounds from approximate satisfaction** with slack `η + γ = 2 acc`: the constraints
give `Ẽ F_{2s} ≥ 1 - 1/2`, `Ẽ F_{2t} ≤ 1024^t + 1/2`, and the ball gives
`|Ẽ f| ≤ ‖f‖₁ (1 + 256 + 1/2)^t ≤ ‖f‖₁ 258^t`. -/
theorem approxBounds {Lb s t : ℕ} {Z : Fin n → Fin d → ℚ} (hst : s ≤ t)
    (hs : (d + 1) ^ (2 * s) ≤ Lb) (ht : (d + 1) ^ (2 * t) ≤ Lb)
    {E : PseudoExpectation (Fin d) (2 * t)}
    (hE : E.ApproxSatisfies (prob Lb s t Z).system
      ((acc (prob Lb s t Z) : ℝ) + acc (prob Lb s t Z)) 0) :
    ApproxBounds s t Z E := by
  set P := prob Lb s t Z
  have hη : (0 : ℝ) ≤ (acc P : ℝ) + acc P := by
    have := acc_pos P
    positivity
  refine ⟨?_, ?_, fun f hf => ?_⟩
  · have hm := lowQ_mem_system (t := t) hs Z
    have h := hE.neg_le_apply_of_mem hm
      (max_le ((totalDegree_lowQ_le s Z).trans (by omega)) (Nat.zero_le _))
    have hslack := acc_add_acc_mul_coeffNorm_le_prob hm
    have hE1 : E (toReal (pairQ (2 * s) Z - 1)) = E (toReal (pairQ (2 * s) Z)) - 1 := by
      rw [toReal, map_sub, map_one, E.map_sub, E.map_one, ← toReal]
    rw [hE1] at h
    linarith
  · have hm := highQ_mem_system (s := s) ht Z
    have h := hE.neg_le_apply_of_mem hm (max_le (totalDegree_highQ_le t Z) (Nat.zero_le _))
    have hslack := acc_add_acc_mul_coeffNorm_le_prob hm
    have hE1 : E (toReal (C (1024 ^ t) - pairQ (2 * t) Z)) =
        1024 ^ t - E (toReal (pairQ (2 * t) Z)) := by
      rw [toReal, map_sub, map_C, E.map_sub, E.map_C, ← toReal, eq_ratCast]
      push_cast
      rfl
    rw [hE1] at h
    linarith
  · have hb := E.abs_apply_le (even_two_mul t) hη hE (ball_mem_system Lb s t Z) hf
    have hslack := acc_add_acc_mul_coeffNorm_le_prob (ball_mem_system Lb s t Z)
    rw [Nat.mul_div_cancel_left t two_pos] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (add_nonneg (by positivity) (mul_nonneg hη (coeffNorm_nonneg _))) ?_ t)
      (coeffNorm1_nonneg _))
    have h256 : |(algebraMap ℚ ℝ) 256| = 256 := by norm_num
    rw [h256]
    linarith

/-! ### The solver call -/

/-- The budget of the solver: `Lb (|P| + 2)³`. -/
def solverBudget (Lb : ℕ) (P : Problem) : ℕ := Lb * ((encProblem P).length + 2) ^ 3

/-- **The solver call**: the sum-of-squares algorithm on `P` with the accuracies `acc P` and the
budget `solverBudget Lb P`. -/
def solve (Lb : ℕ) (P : Problem) : SoS.Solver.Output :=
  SoS.Core.core ((P, acc P, acc P), solverBudget Lb P)

/-- **The solver budget suffices** when `Lb ≥ (d + 5)^(2t + 1)`. -/
theorem budgetOK_solverBudget {Lb s t : ℕ} {Z : Fin n → Fin d → ℚ}
    (hLb : (d + 5) ^ (2 * t + 1) ≤ Lb) :
    SoS.Correct.BudgetOK (prob Lb s t Z) (solverBudget Lb (prob Lb s t Z)) := by
  have hpos : 0 < ((encProblem (prob Lb s t Z)).length + 2) ^ 3 := pow_pos (by omega) _
  have hLb1 : 0 < Lb := (pow_pos (by omega) _).trans_le hLb
  refine SoS.Correct.budgetOK_of_le ?_ ?_
  · change (d + 3 + 2) ^ (2 * t + 1) ≤ Lb * _
    exact hLb.trans (Nat.le_mul_of_pos_right _ hpos)
  · calc ((encProblem (prob Lb s t Z)).length + 2) ^ min 3 (2 * t)
        ≤ ((encProblem (prob Lb s t Z)).length + 2) ^ 3 :=
          Nat.pow_le_pow_right (by omega) (min_le_left _ _)
      _ ≤ solverBudget Lb (prob Lb s t Z) := Nat.le_mul_of_pos_left _ hLb1

end BS23.Separating
