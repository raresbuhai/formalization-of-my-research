module

public import BS23.SmallRadius.Whiten
public import BS23.SmallRadius.Program
public import BS23.SmallRadius.Coins
public import BS23.Common.Input
public import Background.SumOfSquares.Algorithm.Correct

/-!
# The small-radius algorithm

The algorithm of [BS23, Theorem 1.3] (with its moment constraint in two degrees), as a computable
function over the rationals (`BS23.SmallRadius.srCore`), on an input `x = (k, w, R, points)`,
coins `c` and a unary budget `Lb`. With `n` points `Y₀, …, Yₙ₋₁ ∈ ℚ^d` (`BS23.Colinear.pointsFun`):

1. **Guard** (`BS23.SmallRadius.guardB`): the numeric guard `BS23.SmallRadius.numGuardB`
   (`k ≥ 2`, `d ≥ 1`, `n ≥ 2^20`, `(d+1)^(4t) ≤ n`, `2^(4t) ≤ n`, `k ≤ n`) and positive leading
   principal minors of the second moment `Ĉ₀` (`BS23.SmallRadius.LeadMinorsPos`). If it fails,
   every point gets label `0` (in particular when `k ≤ 1`).
2. **Whitening and re-rounding**: `z = whitenData (gridPrec R n d) Y`, and the coefficients
   `b = bOf z t Lb` of `B̃(v) = (n t^t)⁻¹ ∑ⱼ ⟨zⱼ, v⟩^{2t}` (over all `n` points).
3. **`k` rounds of peeling** (`BS23.SmallRadius.peelState`). The remaining points `Rem` start as
   `[0, n)` in order. Round `r` (`BS23.SmallRadius.srRound`) on the points of `Rem`, re-indexed by
   `Fin |Rem|` (`BS23.SmallRadius.remPts`):
   * builds the program `problem (remPts z Rem) b s t m K Bd Lb` of
     [Program.lean](Program.lean) (`BS23.SmallRadius.roundProb`), with the parameters
     `BS23.SmallRadius.srPar` (`s = sDeg w`, `t = tDeg w R`, `m = mDeg w R`, `K = Kc w R`,
     `Bd = ballBd n`);
   * runs the solver `SoS.Core.core` with the accuracies `η = γ = 2^{-(n + |P| + 2)²}`
     (`BS23.SmallRadius.accOf`) and the budget `Lb` (`BS23.SmallRadius.roundOut`);
   * reads `Mwᵢ = Ẽ[wᵢ]` and `Mwwᵢᵢ' = Ẽ[wᵢ wᵢ']` off the output (`BS23.SmallRadius.mwRead`,
     `BS23.SmallRadius.mwwRead`, by the position `i` of the variable `wᵢ`);
   * picks the pivot `i₀ = pick ω b u` with `ωᵢ = max (Mwᵢ) 0`, `b = coinBits n` and `u` the
     number encoded by the `r`-th block of `b` coins (`BS23.SmallRadius.blockNat`);
   * extracts `C_r = {i ∈ Rem : Mw_{i₀} ≤ 2 Mww_{i₀ i}}`, labels its points `r`, and removes them
     from `Rem`.
   The points never extracted keep label `0`.

`BS23.SmallRadius.srAlg C₁` runs `srCore` with the unary budget
`budgetOf C₁ x = radiusTime C₁ x = (|x| + 2)^(C₁ (⌈R²⌉ + logInv w + 1))`.

## Main statements

* **Output shape**: `BS23.SmallRadius.length_srCore` (one label per point),
  `BS23.SmallRadius.outCluster_srCore_lt` (every label is `< k` when `k ≥ 1`),
  `BS23.SmallRadius.srCore_of_not_guard` and `BS23.SmallRadius.srCore_of_k_le_one` (all zeros).
* **Unfolding**: `BS23.SmallRadius.srLabels_of_guard` (on the guard, the labels are those of the
  peeling on the whitened data), the recursion `BS23.SmallRadius.peelRem_succ`,
  `BS23.SmallRadius.peelLab_succ`; `BS23.SmallRadius.mem_peelRem_iff` (a point remains iff no
  earlier round extracted it), `BS23.SmallRadius.peelLab_of_mem_peelC` (a point extracted in round
  `r < R` has label `r` after `R` rounds; for `1 ≤ r < R` this is an iff,
  `BS23.SmallRadius.peelLab_eq_iff`), `BS23.SmallRadius.peelLab_of_mem_peelRem` (the points never
  extracted have label `0`), `BS23.SmallRadius.peelLab_lt`, `BS23.SmallRadius.peelRem_sublist`
  (the remaining points are increasing, so distinct), `BS23.SmallRadius.srRound_sublist`.
* **Coins**: the state after `r` rounds only reads the first `r b` coins
  (`BS23.SmallRadius.peelState_take`), and round `r` only its prefix and the `r`-th block
  (`BS23.SmallRadius.peelC_eq_take`), as `BS23.SmallRadius.coinProb_seq_blockNat` needs; the
  output only reads the first `k b` coins (`BS23.SmallRadius.srCore_take`).
* **The solver, round by round** (`BS23.SmallRadius.exists_roundPE`): if the program of the round
  is valid and the budget suffices (`SoS.Correct.BudgetOK`, e.g. `budget (P, η, γ) ≤ Lb`,
  that is `(|P| + 2)^(64 t + 1) ≤ Lb`, by `BS23.SmallRadius.roundBudgetOK`), there is a
  pseudo-expectation `Ẽ` of degree `64 t` (`BS23.SmallRadius.RoundPE`) with the solver's moments,
  satisfying the program `(η + η)`-approximately, `η`-optimal for `∑ Ẽ[wᵢ]` among those satisfying
  it `η`-approximately, with `Mwᵢ = Ẽ[wᵢ]` and `Mwwᵢᵢ' = Ẽ[wᵢ wᵢ']`; then the round's output is
  `{i : Ẽ[w_{i₀}] ≤ 2 Ẽ[w_{i₀} wᵢ]}` for the pivot `i₀ = BS23.SmallRadius.pivotE`, picked with
  the real weights `max (Ẽ[wᵢ]) 0` (`BS23.SmallRadius.RoundPE.pivot_eq`,
  `BS23.SmallRadius.RoundPE.srRound_eq`, `BS23.SmallRadius.RoundPE.mem_srRound`).
* **The input from a sample** (`BS23.SmallRadius.srCore_roundedSample`): on the rounded sample,
  the output is `List.ofFn (srLabels k w R c Lb (roundedPts r ω))`.
-/

@[expose] public section

namespace BS23.SmallRadius

open MvPolynomial SoS SoS.Solver SoS.Poly RawAlg

variable {n d : ℕ}

/-! ### Reading the moments -/

/-- The exponent vector of `x_a x_b` in `N` variables (`x_a²` if `a = b`). -/
def pairExp (N a b : ℕ) : List ℕ :=
  (List.range N).map fun i => (if i = a then 1 else 0) + (if i = b then 1 else 0)

@[simp] theorem length_pairExp (N a b : ℕ) : (pairExp N a b).length = N := by simp [pairExp]

theorem toFinsupp_pairExp {N : ℕ} (a b : Fin N) :
    Mono.toFinsupp N (pairExp N a b) = Finsupp.single a 1 + Finsupp.single b 1 := by
  ext i
  rw [Mono.toFinsupp_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  simp only [pairExp, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.2,
    Option.map_some, Option.getD_some]
  have h1 : ((i : ℕ) = a) ↔ (a = i) := by rw [eq_comm, Fin.ext_iff]
  have h2 : ((i : ℕ) = b) ↔ (b = i) := by rw [eq_comm, Fin.ext_iff]
  simp only [h1, h2]

/-- `Ẽ[x_k]` is read from the moments. -/
theorem apply_X_eq_coeff {N ℓ : ℕ} {E : PseudoExpectation (Fin N) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly N)) (hℓ : 1 ≤ ℓ) (k : Fin N) :
    E (X k) = (SoS.Poly.coeff N out (unitExp N k 1) : ℝ) := by
  have h := hM (Finsupp.single k 1) (by rw [Finsupp.degree_single]; exact hℓ)
  have hc : (((out.toPoly N).coeff (Finsupp.single k 1) : ℚ) : ℝ) =
      (SoS.Poly.coeff N out (unitExp N k 1) : ℝ) := by
    rw [← toFinsupp_unitExp k 1, coeff_toPoly out (length_unitExp N k 1)]
  rw [← hc, ← h]
  rfl

/-- `Ẽ[x_a x_b]` is read from the moments. -/
theorem apply_X_mul_X_eq_coeff {N ℓ : ℕ} {E : PseudoExpectation (Fin N) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly N)) (hℓ : 2 ≤ ℓ) (a b : Fin N) :
    E (X a * X b) = (SoS.Poly.coeff N out (pairExp N a b) : ℝ) := by
  have h := hM (Finsupp.single a 1 + Finsupp.single b 1)
    (by rw [map_add, Finsupp.degree_single, Finsupp.degree_single]; exact hℓ)
  have hc : (((out.toPoly N).coeff (Finsupp.single a 1 + Finsupp.single b 1) : ℚ) : ℝ) =
      (SoS.Poly.coeff N out (pairExp N a b) : ℝ) := by
    rw [← toFinsupp_pairExp a b, coeff_toPoly out (length_pairExp N a b)]
  rw [← hc, ← h, X, X, monomial_mul_monomial, one_mul]

/-- `Ẽ[wᵢ]`, read from the moments `out` of a program in `N` variables whose `i`-th variable is
`wᵢ`. -/
def mwRead (N : ℕ) (out : RawPoly) (i : ℕ) : ℚ := SoS.Poly.coeff N out (unitExp N i 1)

/-- `Ẽ[wᵢ wᵢ']`, read from the moments `out`. -/
def mwwRead (N : ℕ) (out : RawPoly) (i i' : ℕ) : ℚ := SoS.Poly.coeff N out (pairExp N i i')

theorem mwRead_eq {L : Lay} {ℓ : ℕ} {E : PseudoExpectation (Fin L.N) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly L.N)) (hℓ : 1 ≤ ℓ) (i : Fin L.n) :
    (mwRead L.N out i : ℝ) = E (X (L.wv i)) := by
  rw [apply_X_eq_coeff hM hℓ, Lay.val_wv]
  rfl

theorem mwwRead_eq {L : Lay} {ℓ : ℕ} {E : PseudoExpectation (Fin L.N) ℓ} {out : RawPoly}
    (hM : HasMoments E (out.toPoly L.N)) (hℓ : 2 ≤ ℓ) (i i' : Fin L.n) :
    (mwwRead L.N out i i' : ℝ) = E (X (L.wv i) * X (L.wv i')) := by
  rw [apply_X_mul_X_eq_coeff hM hℓ, Lay.val_wv, Lay.val_wv]
  rfl

/-! ### One round -/

/-- The parameters shared by all rounds: the degrees `s, t`, the power `m`, the constant `K`, the
ball bound `Bd`, the budget `Lb`, the coin bits `nb` per round and the number `ne` of points in
the accuracy exponent. -/
structure RoundPar where
  /-- The identification degree `s`. -/
  s : ℕ
  /-- The scale degree `t`. -/
  t : ℕ
  /-- The power `m = t / s`. -/
  m : ℕ
  /-- The constant `K` of the moment constraint. -/
  K : ℚ
  /-- The ball bound. -/
  Bd : ℚ
  /-- The unary budget. -/
  Lb : ℕ
  /-- The number of coin bits per round. -/
  nb : ℕ
  /-- The number of points in the accuracy exponent. -/
  ne : ℕ

/-- The parameters of the algorithm, read off `w`, `R`, the number `n` of points and the budget
`Lb`. -/
def srPar (w R : ℚ) (n Lb : ℕ) : RoundPar :=
  ⟨sDeg w, tDeg w R, mDeg w R, Kc w R, ballBd n, Lb, coinBits n, n⟩

@[simp] theorem srPar_s (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).s = sDeg w := rfl
@[simp] theorem srPar_t (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).t = tDeg w R := rfl
@[simp] theorem srPar_m (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).m = mDeg w R := rfl
@[simp] theorem srPar_K (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).K = Kc w R := rfl
@[simp] theorem srPar_Bd (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).Bd = ballBd n := rfl
@[simp] theorem srPar_Lb (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).Lb = Lb := rfl
@[simp] theorem srPar_nb (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).nb = coinBits n := rfl
@[simp] theorem srPar_ne (w R : ℚ) (n Lb : ℕ) : (srPar w R n Lb).ne = n := rfl

section Round

variable (Q : RoundPar) (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) (Rem : List (Fin n))

/-- The points of `Rem`, re-indexed by `Fin |Rem|`. -/
def remPts : Fin Rem.length → Fin d → ℚ := fun i => z (Rem.get i)

/-- The layout of the program of a round on `Rem`. -/
abbrev remLay (d : ℕ) : Lay := lay Rem.length d Q.s Q.t Q.Lb

/-- **The program of a round** on the points of `Rem`. -/
def roundProb : Problem := problem (remPts z Rem) b Q.s Q.t Q.m Q.K Q.Bd Q.Lb

/-- The accuracy `2^{-(ne + |P| + 2)²}` of the solver on `P`. -/
def accOf (ne : ℕ) (P : Problem) : ℚ := 1 / 2 ^ accExp ne (encProblem P).length

/-- The accuracy of the round. -/
def roundAcc : ℚ := accOf Q.ne (roundProb Q z b Rem)

/-- **The solver output of a round**: `SoS.Core.core` with the accuracies `roundAcc` and the
budget `Lb`. -/
def roundOut : SoS.Solver.Output :=
  SoS.Core.core ((roundProb Q z b Rem, roundAcc Q z b Rem, roundAcc Q z b Rem), Q.Lb)

/-- **One round**: the cluster `C = {i ∈ Rem : Mw_{i₀} ≤ 2 Mww_{i₀ i}}` extracted from `Rem`, for
the pivot `i₀ = pick (max Mw 0) nb u` picked with the coin value `u` (`[]` if `Rem` is empty). -/
def srRound (u : ℕ) : List (Fin n) :=
  if h : Rem.length = 0 then [] else
    haveI : NeZero Rem.length := ⟨h⟩
    let N := (remLay Q Rem d).N
    let out := roundOut Q z b Rem
    let i₀ : Fin Rem.length := pick (fun i : Fin Rem.length => max (mwRead N out i) 0) Q.nb u
    ((List.finRange Rem.length).filter fun i : Fin Rem.length =>
      decide (mwRead N out i₀ ≤ 2 * mwwRead N out i₀ i)).map Rem.get

theorem roundProb_eq :
    roundProb Q z b Rem = problem (remPts z Rem) b Q.s Q.t Q.m Q.K Q.Bd Q.Lb := rfl

theorem accOf_pos (ne : ℕ) (P : Problem) : 0 < accOf ne P := by
  unfold accOf
  positivity

theorem roundAcc_pos : 0 < roundAcc Q z b Rem := accOf_pos _ _

theorem srRound_of_length_eq_zero (h : Rem.length = 0) (u : ℕ) : srRound Q z b Rem u = [] := by
  rw [srRound, dite_eq_left h]

/-- The round on a nonempty `Rem`, unfolded. -/
theorem srRound_eq [NeZero Rem.length] (u : ℕ) :
    srRound Q z b Rem u =
      ((List.finRange Rem.length).filter fun i : Fin Rem.length =>
        decide (mwRead (remLay Q Rem d).N (roundOut Q z b Rem)
            (pick (fun i : Fin Rem.length => max (mwRead (remLay Q Rem d).N (roundOut Q z b Rem) i)
              0) Q.nb u) ≤
          2 * mwwRead (remLay Q Rem d).N (roundOut Q z b Rem)
            (pick (fun i : Fin Rem.length => max (mwRead (remLay Q Rem d).N (roundOut Q z b Rem) i)
              0) Q.nb u) i)).map Rem.get := by
  rw [srRound, dite_eq_right (NeZero.ne _)]

/-- **The cluster of a round is a sublist of `Rem`**: its points are in `Rem`, in the same order. -/
theorem srRound_sublist (u : ℕ) : (srRound Q z b Rem u).Sublist Rem := by
  by_cases h : Rem.length = 0
  · rw [srRound_of_length_eq_zero Q z b Rem h]
    exact List.nil_sublist _
  · have : NeZero Rem.length := ⟨h⟩
    rw [srRound_eq]
    have h1 := (List.filter_sublist (l := List.finRange Rem.length)
      (p := fun i : Fin Rem.length => decide (mwRead (remLay Q Rem d).N (roundOut Q z b Rem)
            (pick (fun i : Fin Rem.length => max (mwRead (remLay Q Rem d).N (roundOut Q z b Rem) i)
              0) Q.nb u) ≤
          2 * mwwRead (remLay Q Rem d).N (roundOut Q z b Rem)
            (pick (fun i : Fin Rem.length => max (mwRead (remLay Q Rem d).N (roundOut Q z b Rem) i)
              0) Q.nb u) i))).map Rem.get
    rwa [← List.ofFn_eq_map, List.ofFn_get] at h1

theorem srRound_subset {u : ℕ} {i : Fin n} (hi : i ∈ srRound Q z b Rem u) : i ∈ Rem :=
  (srRound_sublist Q z b Rem u).subset hi

end Round

/-! ### The solver, round by round -/

/-- **A budget that suffices**: `SoS.Solver.budget` or more, for a valid problem. -/
theorem budgetOK_of_budget_le {P : Problem} (hP : P.Valid) (ηγ : ℚ × ℚ) {L : ℕ}
    (h : budget (P, ηγ) ≤ L) : SoS.Correct.BudgetOK P L := by
  have hB := SoS.Correct.budgetOK_budget hP ηγ
  exact ⟨⟨hB.1.1.trans h, hB.1.2.trans h, hB.1.3.trans h⟩, fun S hS => (hB.2 S hS).trans h⟩

section RoundPE

variable {Q : RoundPar} {z : Fin n → Fin d → ℚ} {b : List ℕ → ℚ} {Rem : List (Fin n)}

/-- **The budget of a round suffices** when `(|P| + 2)^(64 t + 1) ≤ Lb` for its program `P`. -/
theorem roundBudgetOK (hP : (roundProb Q z b Rem).Valid)
    (h : ((encProblem (roundProb Q z b Rem)).length + 2) ^ (64 * Q.t + 1) ≤ Q.Lb) :
    SoS.Correct.BudgetOK (roundProb Q z b Rem) Q.Lb :=
  budgetOK_of_budget_le hP (0, 0) h

/-- **The pseudo-expectation behind a round**: it has the solver's moments, satisfies the
program `(η + η)`-approximately (`η = roundAcc`), is `η`-optimal for `∑ Ẽ[wᵢ]` among the
pseudo-expectations satisfying the program `η`-approximately, and the readouts are `Ẽ[wᵢ]` and
`Ẽ[wᵢ wᵢ']`. -/
structure RoundPE (Q : RoundPar) (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) (Rem : List (Fin n))
    (E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)) : Prop where
  /-- The output lists the pseudo-moments of `Ẽ`. -/
  moments : HasMoments E ((roundOut Q z b Rem).toPoly (remLay Q Rem d).N)
  /-- `Ẽ` satisfies the program `(η + η)`-approximately. -/
  approx : E.ApproxSatisfies (roundProb Q z b Rem).system
    ((roundAcc Q z b Rem : ℝ) + roundAcc Q z b Rem) 0
  /-- `Ẽ` is `η`-optimal for `∑ Ẽ[wᵢ]`. -/
  opt : ∀ E' : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t),
    E'.ApproxSatisfies (roundProb Q z b Rem).system (roundAcc Q z b Rem : ℝ) 0 →
      ∑ i, E' (X ((remLay Q Rem d).wv i)) ≤ ∑ i, E (X ((remLay Q Rem d).wv i)) + roundAcc Q z b Rem
  /-- `Mwᵢ = Ẽ[wᵢ]`. -/
  mw_eq : ∀ i : Fin Rem.length,
    (mwRead (remLay Q Rem d).N (roundOut Q z b Rem) i : ℝ) = E (X ((remLay Q Rem d).wv i))
  /-- `Mwwᵢᵢ' = Ẽ[wᵢ wᵢ']`. -/
  mww_eq : ∀ i i' : Fin Rem.length,
    (mwwRead (remLay Q Rem d).N (roundOut Q z b Rem) i i' : ℝ) =
      E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i'))

/-- **The solver spec of a round**: for a valid program and a budget that suffices, there is a
pseudo-expectation with the properties of `BS23.SmallRadius.RoundPE`. -/
theorem exists_roundPE (hP : (roundProb Q z b Rem).Valid)
    (hbud : SoS.Correct.BudgetOK (roundProb Q z b Rem) Q.Lb) :
    ∃ E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t), RoundPE Q z b Rem E := by
  obtain ⟨E, hM, hA, hopt⟩ : ∃ E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t),
      HasMoments E ((roundOut Q z b Rem).toPoly (remLay Q Rem d).N) ∧
      E.ApproxSatisfies (roundProb Q z b Rem).system
        ((roundAcc Q z b Rem : ℝ) + roundAcc Q z b Rem) 0 ∧
      ∀ E' : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t),
        E'.ApproxSatisfies (roundProb Q z b Rem).system (roundAcc Q z b Rem : ℝ) 0 →
          (problem (remPts z Rem) b Q.s Q.t Q.m Q.K Q.Bd Q.Lb).objective E ≤
            (problem (remPts z Rem) b Q.s Q.t Q.m Q.K Q.Bd Q.Lb).objective E' +
              roundAcc Q z b Rem :=
    SoS.Correct.core_correct_of_budget _ hP _ _ (roundAcc_pos Q z b Rem) (roundAcc_pos Q z b Rem)
      hbud
  have h2 : 2 ≤ 64 * Q.t := hP.2.1
  refine ⟨E, hM, hA, fun E' hE' => ?_, fun i => mwRead_eq hM (one_le_two.trans h2) i,
    fun i i' => mwwRead_eq hM h2 i i'⟩
  have h := hopt E' hE'
  have h1 : (problem (remPts z Rem) b Q.s Q.t Q.m Q.K Q.Bd Q.Lb).objective E =
      -∑ i, E (X ((remLay Q Rem d).wv i)) := objective_eq E
  have h1' : (problem (remPts z Rem) b Q.s Q.t Q.m Q.K Q.Bd Q.Lb).objective E' =
      -∑ i, E' (X ((remLay Q Rem d).wv i)) := objective_eq E'
  rw [h1, h1'] at h
  linarith

/-- The pick of the round is the pick with the real weights `max (Ẽ[wᵢ]) 0`. -/
theorem pick_cast {N : ℕ} [NeZero N] (ω : Fin N → ℚ) (nb u : ℕ) :
    pick (fun i => (ω i : ℝ)) nb u = pick ω nb u := by
  unfold pick
  congr 2
  funext i
  have h1 : partialW (fun i => (ω i : ℝ)) (i + 1) = ((partialW ω (i + 1) : ℚ) : ℝ) := by
    simp [partialW]
  rw [h1]
  refine decide_eq_decide.2 ?_
  rw [← Rat.cast_sum, ← Rat.cast_natCast, ← Rat.cast_mul, ← Rat.cast_ofNat, ← Rat.cast_pow,
    ← Rat.cast_mul, Rat.cast_lt]

/-- The pivot of a round picked with the real weights `max (Ẽ[wᵢ]) 0`. -/
noncomputable def pivotE (Q : RoundPar) (Rem : List (Fin n)) {ℓ : ℕ} [NeZero Rem.length]
    (E : PseudoExpectation (Fin (remLay Q Rem d).N) ℓ) (u : ℕ) : Fin Rem.length :=
  pick (N := Rem.length) (fun i : Fin Rem.length => max (E (X ((remLay Q Rem d).wv i))) 0) Q.nb u

theorem pivotE_def {ℓ : ℕ} [NeZero Rem.length] (E : PseudoExpectation (Fin (remLay Q Rem d).N) ℓ)
    (u : ℕ) : pivotE Q Rem E u =
      pick (N := Rem.length) (fun i : Fin Rem.length => max (E (X ((remLay Q Rem d).wv i))) 0)
        Q.nb u := rfl

theorem RoundPE.pivot_eq {E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)}
    (hE : RoundPE Q z b Rem E) [NeZero Rem.length] (u : ℕ) :
    pick (fun i : Fin Rem.length => max (mwRead (remLay Q Rem d).N (roundOut Q z b Rem) i) 0)
        Q.nb u =
      pivotE Q Rem E u := by
  rw [pivotE_def, ← pick_cast]
  congr 1
  funext i
  rw [Rat.cast_max, Rat.cast_zero, hE.mw_eq]

/-- **The round from the pseudo-expectation**: with the pivot `i₀` picked with the real weights
`max (Ẽ[wᵢ]) 0`, the round outputs `{i ∈ Rem : Ẽ[w_{i₀}] ≤ 2 Ẽ[w_{i₀} wᵢ]}`. -/
theorem RoundPE.srRound_eq {E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)}
    (hE : RoundPE Q z b Rem E) [NeZero Rem.length] (u : ℕ) :
    srRound Q z b Rem u =
      ((List.finRange Rem.length).filter fun i : Fin Rem.length =>
        decide (E (X ((remLay Q Rem d).wv
            (pivotE Q Rem E u))) ≤
          2 * E (X ((remLay Q Rem d).wv
            (pivotE Q Rem E u)) *
              X ((remLay Q Rem d).wv i)))).map Rem.get := by
  rw [BS23.SmallRadius.srRound_eq, hE.pivot_eq u]
  congr 2
  funext i
  refine decide_eq_decide.2 ?_
  rw [← hE.mw_eq, ← hE.mww_eq]
  constructor <;> intro h <;> exact_mod_cast h

/-- **Membership in the round's output**, for `Rem` without repetitions. -/
theorem RoundPE.mem_srRound {E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)}
    (hE : RoundPE Q z b Rem E) [NeZero Rem.length] (hnd : Rem.Nodup) (u : ℕ)
    (i : Fin Rem.length) :
    Rem.get i ∈ srRound Q z b Rem u ↔
      E (X ((remLay Q Rem d).wv
          (pivotE Q Rem E u))) ≤
        2 * E (X ((remLay Q Rem d).wv
          (pivotE Q Rem E u)) *
            X ((remLay Q Rem d).wv i)) := by
  rw [hE.srRound_eq u, List.mem_map]
  constructor
  · rintro ⟨i', hi', he⟩
    have : i' = i := (hnd.get_inj_iff).1 he
    subst this
    simpa using hi'
  · intro h
    exact ⟨i, List.mem_filter.2 ⟨List.mem_finRange _, by simpa using h⟩, rfl⟩

end RoundPE

/-! ### Peeling -/

section Peel

variable (Q : RoundPar) (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) (us : ℕ → ℕ)

/-- **The state after `r` rounds**, with the coin values `us r'` of the rounds: the remaining
points (in increasing order) and the labels. -/
def peelState : ℕ → List (Fin n) × (Fin n → ℕ)
  | 0 => (List.finRange n, fun _ => 0)
  | r + 1 =>
    let st := peelState r
    let C := srRound Q z b st.1 (us r)
    (st.1.filter fun i => decide (i ∉ C), fun i => if i ∈ C then r else st.2 i)

/-- The remaining points after `r` rounds. -/
def peelRem (r : ℕ) : List (Fin n) := (peelState Q z b us r).1

/-- The labels after `r` rounds. -/
def peelLab (r : ℕ) : Fin n → ℕ := (peelState Q z b us r).2

/-- The cluster `C_r` extracted in round `r`. -/
def peelC (r : ℕ) : List (Fin n) := srRound Q z b (peelRem Q z b us r) (us r)

theorem peelRem_zero : peelRem Q z b us 0 = List.finRange n := rfl

theorem peelLab_zero : peelLab Q z b us 0 = fun _ => 0 := rfl

/-- **The remaining points after one more round.** -/
theorem peelRem_succ (r : ℕ) :
    peelRem Q z b us (r + 1) = (peelRem Q z b us r).filter fun i => decide (i ∉ peelC Q z b us r) :=
  rfl

/-- **The labels after one more round.** -/
theorem peelLab_succ (r : ℕ) (i : Fin n) :
    peelLab Q z b us (r + 1) i = if i ∈ peelC Q z b us r then r else peelLab Q z b us r i :=
  rfl

/-- The remaining points are a sublist of `[0, n)`: increasing, so without repetitions. -/
theorem peelRem_sublist : ∀ r, (peelRem Q z b us r).Sublist (List.finRange n)
  | 0 => List.Sublist.refl _
  | r + 1 => by
    rw [peelRem_succ]
    exact (List.filter_sublist).trans (peelRem_sublist r)

theorem peelRem_nodup (r : ℕ) : (peelRem Q z b us r).Nodup :=
  (peelRem_sublist Q z b us r).nodup (List.nodup_finRange n)

theorem peelRem_pairwise (r : ℕ) : (peelRem Q z b us r).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).sublist (peelRem_sublist Q z b us r)

theorem peelC_sublist (r : ℕ) : (peelC Q z b us r).Sublist (peelRem Q z b us r) :=
  srRound_sublist Q z b _ _

theorem peelC_nodup (r : ℕ) : (peelC Q z b us r).Nodup :=
  (peelC_sublist Q z b us r).nodup (peelRem_nodup Q z b us r)

variable {Q z b us}

theorem mem_peelRem_of_mem_peelC {r : ℕ} {i : Fin n} (hi : i ∈ peelC Q z b us r) :
    i ∈ peelRem Q z b us r :=
  (peelC_sublist Q z b us r).subset hi

/-- **A point remains after `r` rounds iff no earlier round extracted it.** -/
theorem mem_peelRem_iff {i : Fin n} :
    ∀ {r : ℕ}, i ∈ peelRem Q z b us r ↔ ∀ r' < r, i ∉ peelC Q z b us r'
  | 0 => by simp [peelRem_zero]
  | r + 1 => by
    rw [peelRem_succ, List.mem_filter, mem_peelRem_iff, decide_eq_true_iff]
    constructor
    · rintro ⟨h, hr⟩ r' hr'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hr' with hr' | rfl
      · exact h r' hr'
      · exact hr
    · intro h
      exact ⟨fun r' hr' => h r' (by omega), h r (by omega)⟩

/-- The clusters of different rounds are disjoint. -/
theorem not_mem_peelC_of_lt {r r' : ℕ} (hr : r' < r) {i : Fin n} (hi : i ∈ peelC Q z b us r) :
    i ∉ peelC Q z b us r' :=
  mem_peelRem_iff.1 (mem_peelRem_of_mem_peelC hi) r' hr

/-- Every point is extracted in some round `r < R` or remains after `R` rounds. -/
theorem mem_peelRem_or_exists (R : ℕ) (i : Fin n) :
    i ∈ peelRem Q z b us R ∨ ∃ r < R, i ∈ peelC Q z b us r := by
  by_cases h : ∃ r < R, i ∈ peelC Q z b us r
  · exact Or.inr h
  · push Not at h
    exact Or.inl (mem_peelRem_iff.2 h)

/-- **A point extracted in round `r < R` has label `r` after `R` rounds.** -/
theorem peelLab_of_mem_peelC {r : ℕ} {i : Fin n} (hi : i ∈ peelC Q z b us r) :
    ∀ {R : ℕ}, r < R → peelLab Q z b us R i = r
  | 0, h => absurd h (Nat.not_lt_zero _)
  | R + 1, h => by
    rw [peelLab_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [ite_eq_right fun hR => not_mem_peelC_of_lt h hR hi, peelLab_of_mem_peelC hi h]
    · rw [ite_eq_left hi]

/-- **A point that remains after `R` rounds has label `0`.** -/
theorem peelLab_of_mem_peelRem {i : Fin n} :
    ∀ {R : ℕ}, i ∈ peelRem Q z b us R → peelLab Q z b us R i = 0
  | 0, _ => rfl
  | R + 1, h => by
    rw [peelRem_succ, List.mem_filter, decide_eq_true_iff] at h
    rw [peelLab_succ, ite_eq_right h.2, peelLab_of_mem_peelRem h.1]

theorem peelLab_lt_max (i : Fin n) : ∀ R, peelLab Q z b us R i < max R 1
  | 0 => by simp [peelLab_zero]
  | R + 1 => by
    rw [peelLab_succ]
    split_ifs
    · omega
    · have := peelLab_lt_max i R
      omega

/-- **Every label after `R ≥ 1` rounds is below `R`.** -/
theorem peelLab_lt {R : ℕ} (hR : 1 ≤ R) (i : Fin n) : peelLab Q z b us R i < R := by
  have := peelLab_lt_max (Q := Q) (z := z) (b := b) (us := us) i R
  omega

/-- **Labels and clusters**: for `1 ≤ r < R`, a point has label `r` after `R` rounds iff round `r`
extracted it. (Label `0` also covers the points never extracted.) -/
theorem peelLab_eq_iff {r R : ℕ} (hr : 1 ≤ r) (hR : r < R) {i : Fin n} :
    peelLab Q z b us R i = r ↔ i ∈ peelC Q z b us r := by
  refine ⟨fun h => ?_, fun h => peelLab_of_mem_peelC h hR⟩
  rcases mem_peelRem_or_exists (Q := Q) (z := z) (b := b) (us := us) R i with h' | ⟨r', hr', h'⟩
  · rw [peelLab_of_mem_peelRem h'] at h
    omega
  · rw [peelLab_of_mem_peelC h' hr'] at h
    rwa [← h]

/-- **The state after `r` rounds only reads the coin values of the rounds before `r`.** -/
theorem peelState_congr {us' : ℕ → ℕ} :
    ∀ {r : ℕ}, (∀ r' < r, us r' = us' r') → peelState Q z b us r = peelState Q z b us' r
  | 0, _ => rfl
  | r + 1, h => by
    have ih : peelState Q z b us r = peelState Q z b us' r :=
      peelState_congr fun r' hr' => h r' (by omega)
    simp only [peelState, ih, h r (by omega)]

theorem peelRem_congr {us' : ℕ → ℕ} {r : ℕ} (h : ∀ r' < r, us r' = us' r') :
    peelRem Q z b us r = peelRem Q z b us' r := by
  rw [peelRem, peelRem, peelState_congr h]

theorem peelLab_congr {us' : ℕ → ℕ} {r : ℕ} (h : ∀ r' < r, us r' = us' r') :
    peelLab Q z b us r = peelLab Q z b us' r := by
  rw [peelLab, peelLab, peelState_congr h]

/-- **Coins**: with the coin values read from blocks of `nb` coins, the state after `r` rounds
only reads the first `r nb` coins. -/
theorem peelState_take (c : List Bool) (r : ℕ) :
    peelState Q z b (blockNat (c.take (r * Q.nb)) Q.nb) r = peelState Q z b (blockNat c Q.nb) r :=
  peelState_congr fun r' hr' =>
    blockNat_take (Nat.mul_le_mul_right _ (by omega : r' + 1 ≤ r))

/-- **Coins**: round `r` reads the first `r nb` coins (through the state) and the `r`-th block of
`nb` coins (its coin value), as `BS23.SmallRadius.coinProb_seq_blockNat` needs. -/
theorem peelC_eq_take (c : List Bool) (r : ℕ) :
    peelC Q z b (blockNat c Q.nb) r =
      srRound Q z b (peelRem Q z b (blockNat (c.take (r * Q.nb)) Q.nb) r) (blockNat c Q.nb r) := by
  rw [peelC, peelRem, peelRem, peelState_take]

/-- Round `r` only reads the first `(r + 1) nb` coins. -/
theorem peelC_take (c : List Bool) (r : ℕ) :
    peelC Q z b (blockNat (c.take ((r + 1) * Q.nb)) Q.nb) r = peelC Q z b (blockNat c Q.nb) r := by
  rw [peelC, peelC, blockNat_take le_rfl, peelRem_congr fun r' hr' =>
    blockNat_take (Nat.mul_le_mul_right _ (by omega : r' + 1 ≤ r + 1))]

/-- The labels after `R` rounds only read the first `R nb` coins. -/
theorem peelLab_take (c : List Bool) (R : ℕ) :
    peelLab Q z b (blockNat (c.take (R * Q.nb)) Q.nb) R = peelLab Q z b (blockNat c Q.nb) R := by
  rw [peelLab, peelLab, peelState_take]

end Peel

/-! ### The algorithm -/

/-- **The guard**: the numeric guard and positive leading principal minors of the second
moment. -/
def guardB (k : ℕ) (w R : ℚ) (Y : Fin n → Fin d → ℚ) : Bool :=
  numGuardB k w R n d && decide (LeadMinorsPos (secondMoment Y))

theorem guardB_iff {k : ℕ} {w R : ℚ} {Y : Fin n → Fin d → ℚ} :
    guardB k w R Y = true ↔ NumGuard k w R n d ∧ LeadMinorsPos (secondMoment Y) := by
  rw [guardB, Bool.and_eq_true, numGuardB_iff, decide_eq_true_iff]

/-- **The labels of the algorithm** on the points `Y` with the coins `c` and the budget `Lb`:
if the guard passes, the labels after `k` rounds of peeling on the whitened, re-rounded data
`z = whitenData (gridPrec R n d) Y`, with `B̃` from `z`, the parameters `srPar w R n Lb`, and the
coin value of round `r` read from the `r`-th block of `coinBits n` coins; otherwise all `0`. -/
def srLabels (k : ℕ) (w R : ℚ) (c : List Bool) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : Fin n → ℕ :=
  if guardB k w R Y then
    let z := whitenData (gridPrec R n d) Y
    peelLab (srPar w R n Lb) z (bOf z (tDeg w R) Lb) (blockNat c (coinBits n)) k
  else fun _ => 0

/-- **The algorithm** on the input `x`, the coins `c` and the unary budget `Lb`: the labels of
the points. -/
def srCore (x : RadiusInput) (c : List Bool) (Lb : ℕ) : Output :=
  List.ofFn (srLabels x.k x.wmin x.R c Lb (Colinear.pointsFun x.points))

/-- The unary budget `(|x| + 2)^(C₁ (⌈R²⌉ + logInv w + 1))` (the running time of the theorem with
constant `C₁`). -/
def budgetOf (C₁ : ℕ) (x : RadiusInput) : ℕ := radiusTime C₁ x

/-- **The algorithm of Theorem 1.3**, with the budget `budgetOf C₁`. -/
def srAlg (C₁ : ℕ) (xc : RadiusInput × List Bool) : Output := srCore xc.1 xc.2 (budgetOf C₁ xc.1)

theorem srAlg_eq (C₁ : ℕ) (x : RadiusInput) (c : List Bool) :
    srAlg C₁ (x, c) = srCore x c (budgetOf C₁ x) := rfl

section Labels

variable {k : ℕ} {w R : ℚ} {c : List Bool} {Lb : ℕ} {Y : Fin n → Fin d → ℚ}

/-- **On the guard**, the labels are those of the peeling. -/
theorem srLabels_of_guard (hg : NumGuard k w R n d) (hL : LeadMinorsPos (secondMoment Y)) :
    srLabels k w R c Lb Y =
      peelLab (srPar w R n Lb) (whitenData (gridPrec R n d) Y)
        (bOf (whitenData (gridPrec R n d) Y) (tDeg w R) Lb) (blockNat c (coinBits n)) k := by
  rw [srLabels, ite_eq_left (guardB_iff.2 ⟨hg, hL⟩)]

/-- **Off the guard**, all labels are `0`. -/
theorem srLabels_of_not_guard (h : ¬ (NumGuard k w R n d ∧ LeadMinorsPos (secondMoment Y))) :
    srLabels k w R c Lb Y = fun _ => 0 := by
  rw [srLabels, ite_eq_right (by rwa [guardB_iff])]

/-- For `k ≤ 1`, all labels are `0`. -/
theorem srLabels_of_k_le_one (hk : k ≤ 1) : srLabels k w R c Lb Y = fun _ => 0 :=
  srLabels_of_not_guard fun h => by have := h.1.two_le_k; omega

/-- **Every label is below `k`**, for `k ≥ 1`. -/
theorem srLabels_lt (hk : 1 ≤ k) (i : Fin n) : srLabels k w R c Lb Y i < k := by
  unfold srLabels
  split_ifs
  · exact peelLab_lt hk i
  · exact hk

/-- **The labels only read the first `k · coinBits n` coins.** -/
theorem srLabels_take {m : ℕ} (hm : k * coinBits n ≤ m) :
    srLabels k w R (c.take m) Lb Y = srLabels k w R c Lb Y := by
  unfold srLabels
  split_ifs
  · exact peelLab_congr fun r' hr' =>
      blockNat_take ((Nat.mul_le_mul_right _ (by omega : r' + 1 ≤ k)).trans hm)
  · rfl

end Labels

/-- One label per point. -/
@[simp] theorem length_srCore (x : RadiusInput) (c : List Bool) (Lb : ℕ) :
    (srCore x c Lb).length = x.points.length :=
  List.length_ofFn

theorem outCluster_srCore (x : RadiusInput) (c : List Bool) (Lb : ℕ) (j : Fin x.points.length) :
    outCluster (srCore x c Lb) j = srLabels x.k x.wmin x.R c Lb (Colinear.pointsFun x.points) j :=
  outCluster_ofFn _ j

/-- **Every label of the output is below `k`**, for `k ≥ 1` (also past the end of the list). -/
theorem outCluster_srCore_lt {x : RadiusInput} (hk : 1 ≤ x.k) (c : List Bool) (Lb j : ℕ) :
    outCluster (srCore x c Lb) j < x.k := by
  by_cases hj : j < x.points.length
  · have := outCluster_srCore x c Lb ⟨j, hj⟩
    simp only at this
    rw [this]
    exact srLabels_lt hk _
  · rw [outCluster, List.getD_eq_default _ _ (by rw [length_srCore]; omega)]
    exact hk

/-- **Off the guard**, the output is all zeros. -/
theorem srCore_of_not_guard {x : RadiusInput} (c : List Bool) (Lb : ℕ)
    (h : ¬ (NumGuard x.k x.wmin x.R x.points.length (dim x.points) ∧
      LeadMinorsPos (secondMoment (Colinear.pointsFun x.points)))) :
    srCore x c Lb = List.replicate x.points.length 0 := by
  rw [srCore, srLabels_of_not_guard h, List.ofFn_const]

/-- For `k ≤ 1`, the output is all zeros. -/
theorem srCore_of_k_le_one {x : RadiusInput} (hk : x.k ≤ 1) (c : List Bool) (Lb : ℕ) :
    srCore x c Lb = List.replicate x.points.length 0 :=
  srCore_of_not_guard c Lb fun h => by have := h.1.two_le_k; omega

/-- **The output only reads the first `k · coinBits n` coins.** -/
theorem srCore_take {x : RadiusInput} {m : ℕ} (hm : x.k * coinBits x.points.length ≤ m)
    (c : List Bool) (Lb : ℕ) : srCore x (c.take m) Lb = srCore x c Lb := by
  rw [srCore, srCore, srLabels_take hm]

/-! ### The input from a sample -/

/-- **The algorithm on a rounded sample** lists its labels of the rounded points. -/
theorem srCore_roundedSample {k' : ℕ} (k : ℕ) (w R : ℚ) (r : Rounding k' d)
    (ω : Fin n → Fin k' × EuclideanSpace ℝ (Fin d)) (c : List Bool) (Lb : ℕ) :
    srCore ⟨k, w, R, roundedSample r ω⟩ c Lb = List.ofFn (srLabels k w R c Lb (roundedPts r ω)) :=
  ofFn_pointsFun_roundedSample (fun _ _ Y => srLabels k w R c Lb Y) r ω

/-- The label of sample point `j` on a rounded sample. -/
theorem outCluster_srCore_roundedSample {k' : ℕ} (k : ℕ) (w R : ℚ) (r : Rounding k' d)
    (ω : Fin n → Fin k' × EuclideanSpace ℝ (Fin d)) (c : List Bool) (Lb : ℕ) (j : Fin n) :
    outCluster (srCore ⟨k, w, R, roundedSample r ω⟩ c Lb) j =
      srLabels k w R c Lb (roundedPts r ω) j := by
  rw [srCore_roundedSample, outCluster_ofFn]

/-- `BS23.ClustersWithin` of the output on a rounded sample only reads the labels of the rounded
points. -/
theorem clustersWithin_srCore_roundedSample {k' : ℕ} (k : ℕ) (w R : ℚ) (r : Rounding k' d)
    (ω : Fin n → Fin k' × EuclideanSpace ℝ (Fin d)) (c : List Bool) (Lb : ℕ) (ε : ℝ)
    (ℓ : Fin n → Fin k') :
    ClustersWithin ε ℓ (srCore ⟨k, w, R, roundedSample r ω⟩ c Lb) ↔
      ClustersWithin ε ℓ (List.ofFn (srLabels k w R c Lb (roundedPts r ω))) := by
  rw [srCore_roundedSample]

end BS23.SmallRadius
