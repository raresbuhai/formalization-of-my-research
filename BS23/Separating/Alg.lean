module

public import BS23.Separating.Program
public import BS23.Separating.Coins
public import BS23.Separating.MomentClose
public import BS23.Colinear.Alg

/-!
# The separating algorithm

The algorithm for [BS23, Theorem 1.1] (`BS23.Separating.run`), with parameters `r` (the ratio
`t / s` of the two moment degrees) and `Kc` (extra coin bits), on an input `x` with `n` points in
`ℚ^d` and weight bound `wmin`, coins `c` and a unary budget `Lb`. All arithmetic is rational.

1. `s = logInv wmin + 1` and `t = r s` (`BS23.Separating.sDeg`, `BS23.Separating.tDeg`).
2. The points are whitened (`BS23.Separating.whitened`, from `BS23/Separating/Whiten.lean`).
3. The sum-of-squares program of `BS23/Separating/Program.lean` on the whitened points
   (`BS23.Separating.progOf`) is solved with the accuracies `2^-(|P|+2)` and the budget
   `Lb (|P| + 2)³` (`BS23.Separating.outOf`).
4. The pivot `p` is read from the first `⌈log₂ n⌉ + Kc` coins (`BS23.Separating.pivot`,
   `BS23.Separating.coinBits`).
5. `q(u) = Ẽ ⟨u, v⟩^(2s)` is read off the solver's pseudo-moments (`BS23.Separating.qv`), and
   point `j` gets label `0` if `q(X_p - X_j) ≤ τ = 1 / (4 · 64^s)` (`BS23.Separating.tau`), `1`
   otherwise.

The machine-level function `BS23.Separating.sepAlg` keeps the first `coinBits` coins and uses the
budget `Lg x = (d + 5)^(2t + 1)` (`BS23.Separating.Lg`); `run` ignores the other coins
(`BS23.Separating.run_take`, `BS23.Separating.sepAlg_eq`).

**All failure probabilities** (`BS23.Separating.sepAlgU`): the parameters are read off the
failure probability `δ` of the input. For `δ > 0`, with `R = max ⌈1/δ⌉ 100`
(`BS23.Separating.rOf`), the algorithm is `sepAlg r Kc` with `r = 2^41 R`
(`BS23.Separating.ratioR`) and `Kc = ⌈log₂ (4R)⌉` (`BS23.Separating.kcR`); for `δ ≤ 0` it
outputs nothing.

**The specification** (`BS23.Separating.alg_spec`): if the solver output is correct
(`SoS.Solver.Correct`), there is a degree-`2t` pseudo-expectation `Ẽ` (`BS23.Separating.SolverPE`)
with the solver's pseudo-moments, satisfying the program with slack `2 · 2^-(|P|+2)`, with
`Ẽ F_{2s} ≥ 1/2`, `Ẽ F_{2t} ≤ 1024^t + 1/2` and `|Ẽ f| ≤ ‖f‖₁ 258^t`, such that
`q(u) = Ẽ ⟨u, v⟩^(2s)` for every `u`, and the output is
`List.ofFn fun j ↦ if Ẽ ⟨x_p - x_j, v⟩^(2s) ≤ τ then 0 else 1` for the real whitened points `x`
(`BS23.Separating.xR`). Here `F_p = n⁻² ∑_{i,j} ⟨x_i - x_j, v⟩^p` (`BS23.Separating.pairLin`).
The program is valid as soon as some point satisfies its constraints
(`BS23.Separating.progOf_valid`), and then the output is correct
(`BS23.Separating.correct_outOf`).
-/

@[expose] public section

namespace BS23.Separating

open MvPolynomial SoS SoS.Solver SoS.Poly

variable {n d : ℕ}

/-! ### Parameters -/

/-- `s = L + 1` for `L = logInv wmin`: the polynomial `q` has degree `2s`. -/
def sDeg (x : BipartitionInput) : ℕ := logInv x.wmin + 1

/-- `t = r s`: the pseudo-expectation has degree `2t`. -/
def tDeg (r : ℕ) (x : BipartitionInput) : ℕ := r * sDeg x

/-- The threshold `τ = 1 / (4 · 64^s)`. -/
def tau (s : ℕ) : ℚ := 1 / (4 * 64 ^ s)

theorem cast_tau (s : ℕ) : ((tau s : ℚ) : ℝ) = 1 / (4 * 64 ^ s) := by
  simp [tau]

/-- The number of coins read for the pivot, `⌈log₂ n⌉ + Kc`. -/
def coinBits (n Kc : ℕ) : ℕ := Nat.clog 2 n + Kc

/-- The global unary budget `(d + 5)^(2t + 1)`. -/
def Lg (r : ℕ) (x : BipartitionInput) : ℕ := (dim x.points + 5) ^ (2 * tDeg r x + 1)

theorem one_le_sDeg (x : BipartitionInput) : 1 ≤ sDeg x := by
  unfold sDeg
  omega

theorem sDeg_le_tDeg {r : ℕ} (hr : 1 ≤ r) (x : BipartitionInput) : sDeg x ≤ tDeg r x := by
  unfold tDeg
  exact Nat.le_mul_of_pos_left _ hr

theorem one_le_tDeg {r : ℕ} (hr : 1 ≤ r) (x : BipartitionInput) : 1 ≤ tDeg r x :=
  (one_le_sDeg x).trans (sDeg_le_tDeg hr x)

/-- `(d + 1)^(2t) ≤ Lg x`: the global budget cuts no product of the program. -/
theorem pow_le_Lg (r : ℕ) (x : BipartitionInput) :
    (dim x.points + 1) ^ (2 * tDeg r x) ≤ Lg r x :=
  (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))

/-! ### The algorithm -/

/-- The whitened points of the input. -/
def whitened (x : BipartitionInput) : Fin x.points.length → Fin (dim x.points) → ℚ :=
  whiten (Colinear.pointsFun x.points)

/-- The program solved on the input, with the budget `Lb`. -/
def progOf (r : ℕ) (x : BipartitionInput) (Lb : ℕ) : Problem :=
  prob Lb (sDeg x) (tDeg r x) (whitened x)

/-- The solver output: pseudo-moments `∑ α, Ẽ[vᵅ] vᵅ`. -/
def outOf (r : ℕ) (x : BipartitionInput) (Lb : ℕ) : SoS.Solver.Output :=
  solve Lb (progOf r x Lb)

/-- The value at `u` of the degree-`p` moment polynomial of the pseudo-moments `out`: the sum,
over the terms `(e, a)` of `⟨u, v⟩^p` (`BS23.Separating.powRaw`), of `a` times the coefficient of
`vᵉ` in `out`. -/
def qvOf (d Lb p : ℕ) (out : RawPoly) (u : Fin d → ℚ) : ℚ :=
  ((powRaw Lb p u).map fun t => t.2 * SoS.Poly.coeff d out (expo d t.1)).sum

/-- `q(u) = Ẽ ⟨u, v⟩^(2s)`, read off the solver output. -/
def qv (r : ℕ) (x : BipartitionInput) (Lb : ℕ) (u : Fin (dim x.points) → ℚ) : ℚ :=
  qvOf (dim x.points) Lb (2 * sDeg x) (outOf r x Lb) u

/-- The pivot index: the first `coinBits n Kc` coins, as a number, modulo `n`. -/
def pivot (n Kc : ℕ) (c : List Bool) : ℕ := coinIdx n (coinBits n Kc) c

/-- **The algorithm** with parameters `r`, `Kc`, on the input `x`, the coins `c` and the unary
budget `Lb`: label `0` for the points `j` with `q(X_p - X_j) ≤ τ`, `1` for the others. -/
def run (r Kc : ℕ) (x : BipartitionInput) (c : List Bool) (Lb : ℕ) : BS23.Output :=
  let X := whitened x
  let out := outOf r x Lb
  let p := pivot x.points.length Kc c
  List.ofFn fun j : Fin x.points.length =>
    if qvOf (dim x.points) Lb (2 * sDeg x) out (X ⟨p, coinIdx_lt j.pos _ _⟩ - X j) ≤ tau (sDeg x)
    then 0 else 1

/-- **The algorithm of Theorem 1.1**, as a function of the input and the coins: the first
`coinBits` coins and the budget `Lg`. -/
def sepAlg (r Kc : ℕ) (xc : BipartitionInput × List Bool) : BS23.Output :=
  run r Kc xc.1 (xc.2.take (coinBits xc.1.points.length Kc)) (Lg r xc.1)

@[simp] theorem length_run (r Kc : ℕ) (x : BipartitionInput) (c : List Bool) (Lb : ℕ) :
    (run r Kc x c Lb).length = x.points.length :=
  List.length_ofFn

theorem pivot_take {n Kc m : ℕ} (hm : coinBits n Kc ≤ m) (c : List Bool) :
    pivot n Kc (c.take m) = pivot n Kc c :=
  coinIdx_take hm c

/-- **`run` reads only the first `coinBits` coins.** -/
theorem run_take {r Kc : ℕ} {x : BipartitionInput} {m : ℕ}
    (hm : coinBits x.points.length Kc ≤ m) (c : List Bool) (Lb : ℕ) :
    run r Kc x (c.take m) Lb = run r Kc x c Lb := by
  unfold run
  dsimp only
  congr 1
  funext j
  have h : (⟨pivot x.points.length Kc (c.take m), coinIdx_lt j.pos _ _⟩ : Fin x.points.length) =
      ⟨pivot x.points.length Kc c, coinIdx_lt j.pos _ _⟩ :=
    Fin.ext (pivot_take hm c)
  rw [h]

theorem sepAlg_eq (r Kc : ℕ) (x : BipartitionInput) (c : List Bool) :
    sepAlg r Kc (x, c) = run r Kc x c (Lg r x) :=
  run_take le_rfl c _

/-! ### All failure probabilities -/

/-- The parameter `R = max ⌈1/δ⌉ 100` of the failure probability `δ > 0`, and `0` for `δ ≤ 0`. -/
def rOf (δ : ℚ) : ℕ := if 0 < δ then max ⌈1 / δ⌉₊ 100 else 0

/-- The ratio `r = 2^41 R` of the two moment degrees. -/
def ratioR (R : ℕ) : ℕ := 2 ^ 41 * R

/-- The number `Kc = ⌈log₂ (4R)⌉` of extra coin bits. -/
def kcR (R : ℕ) : ℕ := Nat.clog 2 (4 * R)

/-- **The algorithm of Theorem 1.1 for all failure probabilities**: `sepAlg r Kc` with
`r = ratioR R`, `Kc = kcR R` for `R = rOf δ`, if `δ > 0`; the empty output if `δ ≤ 0`. -/
def sepAlgU (xc : BipartitionInput × List Bool) : BS23.Output :=
  if rOf xc.1.δ = 0 then [] else sepAlg (ratioR (rOf xc.1.δ)) (kcR (rOf xc.1.δ)) xc

theorem rOf_of_pos {δ : ℚ} (hδ : 0 < δ) : rOf δ = max ⌈1 / δ⌉₊ 100 := ite_eq_left hδ

theorem rOf_ne_zero {δ : ℚ} (hδ : 0 < δ) : rOf δ ≠ 0 := by
  rw [rOf_of_pos hδ]
  omega

theorem sepAlgU_of_pos {x : BipartitionInput} (hδ : 0 < x.δ) (c : List Bool) :
    sepAlgU (x, c) = sepAlg (ratioR (rOf x.δ)) (kcR (rOf x.δ)) (x, c) :=
  ite_eq_right (rOf_ne_zero hδ)

/-! ### Over the reals -/

/-- The real whitened points: the casts of `BS23.Separating.whitened`. -/
noncomputable def xR (x : BipartitionInput) : Fin x.points.length → Fin (dim x.points) → ℝ :=
  fun j k => (whitened x j k : ℝ)

/-- The real whitened points are the whitened casts of the input points. -/
theorem xR_eq_whiten (x : BipartitionInput) :
    xR x = whiten fun j k => (Colinear.pointsFun x.points j k : ℝ) := by
  rw [whiten_cast]
  rfl

/-- The pair moment polynomial `F_p = n⁻² ∑_{i,j} ⟨x_i - x_j, v⟩^p` of real points (by
definition `BS23.Separating.PA.pairPoly lin x p` of `BS23/Separating/PseudoAnalysis.lean`). -/
noncomputable def pairLin (x : Fin n → Fin d → ℝ) (p : ℕ) : MvPolynomial (Fin d) ℝ :=
  ((n : ℝ) ^ 2)⁻¹ • ∑ i, ∑ j, lin (x i - x j) ^ p

theorem toReal_linQ (u : Fin d → ℚ) : toReal (linQ u) = lin fun k => (u k : ℝ) := by
  simp [toReal, linQ, lin]

theorem toReal_pairQ (p : ℕ) (Z : Fin n → Fin d → ℚ) :
    toReal (pairQ p Z) = pairLin (fun j k => (Z j k : ℝ)) p := by
  rw [pairQ, pairLin, toReal, map_mul, map_C, ← C_mul', eq_ratCast, map_sum]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_pow, ← toReal, toReal_linQ]
  congr 2
  funext k
  simp

/-- **Reading `q` off the pseudo-moments**: if `out` lists the moments of `Ẽ` up to degree
`ℓ ≥ p` and nothing is cut, then `qvOf d Lb p out u = Ẽ ⟨u, v⟩^p`. -/
theorem qvOf_eq {ℓ Lb p : ℕ} {out : RawPoly} {E : PseudoExpectation (Fin d) ℓ}
    (hE : HasMoments E (out.toPoly d)) (hp : p ≤ ℓ) (hLb : (d + 1) ^ p ≤ Lb) (u : Fin d → ℚ) :
    (qvOf d Lb p out u : ℝ) = E (lin (fun k => (u k : ℝ)) ^ p) := by
  set Y : (Fin d →₀ ℕ) → ℝ := fun α => ((out.toPoly d).coeff α : ℝ) with hY
  have h1 : (qvOf d Lb p out u : ℝ) = riesz Y (toReal ((powRaw Lb p u).toPoly d)) := by
    rw [riesz_toPoly, qvOf, Rat.cast_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Rat.cast_mul, hY]
    rw [← coeff_toPoly out (length_expo d t.1), toFinsupp_expo]
  have h2 : toReal ((powRaw Lb p u).toPoly d) = lin (fun k => (u k : ℝ)) ^ p := by
    rw [toPoly_powRaw hLb, toReal, map_pow, ← toReal, toReal_linQ]
  rw [h1, h2, riesz_apply, E.coe_apply, apply_eq_sum_coeff_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.degree ≤ ℓ :=
    (le_totalDegree hm).trans (((isHomogeneous_lin _).pow p).totalDegree_le.trans (by omega))
  rw [hE m hdeg]

/-! ### Validity -/

/-- **The program is valid** if some point `v` has `‖v‖² ≤ 256`, `F_{2s}(v) ≥ 1` and
`F_{2t}(v) ≤ 1024^t`. -/
theorem progOf_valid {r : ℕ} (hr : 1 ≤ r) {x : BipartitionInput} {Lb : ℕ}
    (hLb : (dim x.points + 1) ^ (2 * tDeg r x) ≤ Lb) {v : Fin (dim x.points) → ℝ}
    (hball : ∑ i, v i ^ 2 ≤ 256) (hlow : 1 ≤ eval v (pairLin (xR x) (2 * sDeg x)))
    (hhigh : eval v (pairLin (xR x) (2 * tDeg r x)) ≤ 1024 ^ tDeg r x) :
    (progOf r x Lb).Valid := by
  have hs : (dim x.points + 1) ^ (2 * sDeg x) ≤ Lb :=
    (Nat.pow_le_pow_right (by omega) (by have := sDeg_le_tDeg hr x; omega)).trans hLb
  refine valid_of_eval (one_le_tDeg hr x) hs hLb hball ?_ ?_
  · rw [toReal_pairQ]
    exact hlow
  · rw [toReal_pairQ]
    exact hhigh

/-- The solver budget suffices with the global budget `Lg`. -/
theorem budgetOK_progOf (r : ℕ) (x : BipartitionInput) :
    SoS.Correct.BudgetOK (progOf r x (Lg r x)) (solverBudget (Lg r x) (progOf r x (Lg r x))) :=
  budgetOK_solverBudget le_rfl

/-- **The solver output is correct** for a valid program with the global budget `Lg`. -/
theorem correct_outOf {r : ℕ} {x : BipartitionInput} (hP : (progOf r x (Lg r x)).Valid) :
    Correct (progOf r x (Lg r x)) (acc (progOf r x (Lg r x))) (acc (progOf r x (Lg r x)))
      (outOf r x (Lg r x)) :=
  SoS.Correct.core_correct_of_budget _ hP _ _ (acc_pos _) (acc_pos _) (budgetOK_progOf r x)

/-! ### The specification -/

/-- The facts about the pseudo-expectation `Ẽ` behind a correct solver output: it has the solver's
pseudo-moments, satisfies the program with slack `2 acc`, has `Ẽ F_{2s} ≥ 1/2`,
`Ẽ F_{2t} ≤ 1024^t + 1/2` and bounded values `|Ẽ f| ≤ ‖f‖₁ 258^t`, and `q = Ẽ ⟨·, v⟩^(2s)`. -/
structure SolverPE (r : ℕ) (x : BipartitionInput) (Lb : ℕ)
    (E : PseudoExpectation (Fin (dim x.points)) (2 * tDeg r x)) : Prop where
  /-- The output lists the pseudo-moments of `Ẽ`. -/
  moments : HasMoments E ((outOf r x Lb).toPoly (dim x.points))
  /-- `Ẽ` satisfies the program with slack `2 acc`. -/
  approx : E.ApproxSatisfies (progOf r x Lb).system (2 * (acc (progOf r x Lb) : ℝ)) 0
  /-- `Ẽ F_{2s} ≥ 1/2`. -/
  low : 1 / 2 ≤ E (pairLin (xR x) (2 * sDeg x))
  /-- `Ẽ F_{2t} ≤ 1024^t + 1/2`. -/
  high : E (pairLin (xR x) (2 * tDeg r x)) ≤ 1024 ^ tDeg r x + 1 / 2
  /-- `|Ẽ f| ≤ ‖f‖₁ 258^t` for `deg f ≤ 2t`. -/
  bound : ∀ f : MvPolynomial (Fin (dim x.points)) ℝ, f.totalDegree ≤ 2 * tDeg r x →
    |E f| ≤ coeffNorm1 f * 258 ^ tDeg r x
  /-- `q(u) = Ẽ ⟨u, v⟩^(2s)`. -/
  qv_eq : ∀ u : Fin (dim x.points) → ℚ,
    (qv r x Lb u : ℝ) = E (lin (fun k => (u k : ℝ)) ^ (2 * sDeg x))

/-- **The pseudo-expectation behind a correct output** has the properties of
`BS23.Separating.SolverPE` when the budget cuts nothing. -/
theorem solverPE_of {r : ℕ} (hr : 1 ≤ r) {x : BipartitionInput} {Lb : ℕ}
    (hLb : (dim x.points + 1) ^ (2 * tDeg r x) ≤ Lb)
    {E : PseudoExpectation (Fin (dim x.points)) (2 * tDeg r x)}
    (hmom : HasMoments E ((outOf r x Lb).toPoly (dim x.points)))
    (happrox : E.ApproxSatisfies (progOf r x Lb).system
      ((acc (progOf r x Lb) : ℝ) + acc (progOf r x Lb)) 0) :
    SolverPE r x Lb E := by
  have hst := sDeg_le_tDeg hr x
  have hs : (dim x.points + 1) ^ (2 * sDeg x) ≤ Lb :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hLb
  have hb := approxBounds hst hs hLb happrox
  refine ⟨hmom, by rw [two_mul ((acc (progOf r x Lb) : ℚ) : ℝ)]; exact happrox, ?_, ?_, hb.bound,
    fun u => qvOf_eq hmom (by omega) hs u⟩
  · have h := hb.low
    rw [toReal_pairQ] at h
    exact h
  · have h := hb.high
    rw [toReal_pairQ] at h
    exact h

/-- **The output from the pseudo-expectation**: for the pivot `p` read from the coins, label `0`
for the points `j` with `Ẽ ⟨x_p - x_j, v⟩^(2s) ≤ τ`, `1` for the others. -/
theorem run_eq_of_solverPE {r Kc : ℕ} {x : BipartitionInput} {c : List Bool} {Lb : ℕ}
    {E : PseudoExpectation (Fin (dim x.points)) (2 * tDeg r x)} (hE : SolverPE r x Lb E)
    (p : Fin x.points.length) (hp : (p : ℕ) = pivot x.points.length Kc c) :
    run r Kc x c Lb = List.ofFn fun j =>
      if E (lin (xR x p - xR x j) ^ (2 * sDeg x)) ≤ (tau (sDeg x) : ℝ) then 0 else 1 := by
  unfold run
  dsimp only
  congr 1
  funext j
  have hpj : (⟨pivot x.points.length Kc c, coinIdx_lt j.pos _ _⟩ : Fin x.points.length) = p :=
    Fin.ext hp.symm
  rw [hpj]
  have hq := hE.qv_eq (whitened x p - whitened x j)
  unfold qv at hq
  have hfun : (fun k => ((whitened x p - whitened x j) k : ℝ)) = xR x p - xR x j := by
    funext k
    simp [xR]
  rw [hfun] at hq
  refine if_congr ?_ rfl rfl
  rw [← hq]
  exact Rat.cast_le.symm

/-- **The specification of the algorithm.** If the solver output is correct and the budget cuts
nothing, there is a degree-`2t` pseudo-expectation `Ẽ` with the properties of
`BS23.Separating.SolverPE`, and for the pivot `p` read from the coins the output is
`List.ofFn fun j ↦ if Ẽ ⟨x_p - x_j, v⟩^(2s) ≤ τ then 0 else 1`. -/
theorem alg_spec {r Kc : ℕ} (hr : 1 ≤ r) {x : BipartitionInput} (c : List Bool) {Lb : ℕ}
    (hLb : (dim x.points + 1) ^ (2 * tDeg r x) ≤ Lb)
    (hC : Correct (progOf r x Lb) (acc (progOf r x Lb)) (acc (progOf r x Lb)) (outOf r x Lb)) :
    ∃ E : PseudoExpectation (Fin (dim x.points)) (2 * tDeg r x), SolverPE r x Lb E ∧
      ∀ p : Fin x.points.length, (p : ℕ) = pivot x.points.length Kc c →
        run r Kc x c Lb = List.ofFn fun j =>
          if E (lin (xR x p - xR x j) ^ (2 * sDeg x)) ≤ (tau (sDeg x) : ℝ) then 0 else 1 := by
  obtain ⟨E, hmom, happrox, -⟩ := hC
  have hE := solverPE_of hr hLb hmom happrox
  exact ⟨E, hE, fun p hp => run_eq_of_solverPE hE p hp⟩

end BS23.Separating
