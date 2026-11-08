module

public import BS23.ColinearSoS.Program
public import BS23.Common.Input

/-!
# The sum-of-squares algorithm for colinear means

The algorithm for [BS23, Theorem 1.2] that follows the paper's sum-of-squares route, as a function
of the number `k` of components, the weight bound `wmin`, a unary budget `Lb` and the points
`Y₁, …, Yₙ ∈ ℚ^d` (`BS23.ColinearSoS.colLabels`). All arithmetic is rational.

1. `s = logInv wmin + 1`, `t = 256 s` (`BS23.ColinearSoS.sCol`, `BS23.ColinearSoS.tCol`).
2. The points are whitened, `Xⱼ = W (Yⱼ - ȳ)` (`BS23.Separating.whiten`), and
   `κ = BS23.Separating.kappa Ĉ` for the empirical covariance `Ĉ`, so that `vᵀ diag(κ) v` is the
   empirical variance of `⟨X, v⟩` when `Ĉ ≻ 0`.
3. Program U (`BS23.ColinearSoS.progUY`, degree `2s`): maximize `Ẽ Φ̂_{2s}` subject to
   `‖v‖² ≤ 256` and `vᵀ diag(κ) v = 1`, where `Φ̂_r = (1/n) ∑ⱼ ⟨Xⱼ, v⟩^r`. It is solved
   (`BS23.ColinearSoS.outU`), and `OPT_U = (1/n) ∑ⱼ Ẽ ⟨Xⱼ, v⟩^(2s)` is read off the
   pseudo-moments (`BS23.ColinearSoS.optU`).
4. If `OPT_U ≥ (5s)^s` (`BS23.ColinearSoS.testU`) the output of U is used; otherwise program L
   (`BS23.ColinearSoS.progLY`, degree `2t`: minimize `Ẽ Φ̂_{2t}` under the same constraints) is
   solved and its output is used (`BS23.ColinearSoS.outC`).
5. From the chosen pseudo-moments, `M_ab = Ẽ[v_a v_b]` (`BS23.ColinearSoS.momOut`), the first
   index `j*` with the largest `M_jj` (`BS23.ColinearSoS.jstarOut`), the column `â = M e_{j*}`
   (`BS23.ColinearSoS.ahatOut`) and the direction `a = Wᵀ â` in the original coordinates
   (`BS23.ColinearSoS.dirOf`).
6. The labels are those of the clustering of the projections `⟨a, Yⱼ⟩` on the line, with the
   parameters `BS23.Colinear.params wmin` (`BS23.ColinearSoS.lineLabels`, as the last step of
   `BS23.Colinear.alg`); for `k ≤ 1` all labels are `0`.

On an input `x`, `BS23.ColinearSoS.colSoS x Lb` lists the labels of the input's points, and the
algorithm of the theorem is `BS23.ColinearSoS.colinearSoSAlg`, with the budget
`Lgc x = (d + 5)^(2t + 1)` (`BS23.ColinearSoS.Lgc`). It ignores its coins.

**Over the reals.** Every step commutes with casting to the reals except the solver calls, whose
outputs are read through the pseudo-expectations behind them.

* `BS23.ColinearSoS.SpecU`, `BS23.ColinearSoS.SpecL`: the facts about a pseudo-expectation behind
  a correct output of U or L: it has the solver's pseudo-moments, satisfies the constraints with
  slack `2 acc`, has `|Ẽ f| ≤ ‖f‖₁ 258^m`, satisfies `|Ẽ[h (vᵀDv - 1)]| ≤ 2 acc ‖h‖₂ ‖vᵀDv - 1‖₂`
  for sums of squares `h` of small degree, `Ẽ[v_a v_b]` is read off correctly, and it is
  near-optimal against every real `v` with `‖v‖² ≤ 256`, `vᵀDv = 1`: for U,
  `Φ̂_{2s}(v) - acc ≤ Ẽ Φ̂_{2s}` and `OPT_U = Ẽ Φ̂_{2s}`; for L, `Ẽ Φ̂_{2t} ≤ Φ̂_{2t}(v) + acc`.
  Such pseudo-expectations exist as soon as some real point satisfies the constraints and the
  budget is at least `(d + 5)^(2t + 1)` (`BS23.ColinearSoS.exists_specU`,
  `BS23.ColinearSoS.exists_specL`). The accuracy `acc` is at most `2^-n`
  (`BS23.ColinearSoS.acc_progUY_le`, `BS23.ColinearSoS.acc_progLY_le`).
* **The output in real terms** (`BS23.ColinearSoS.colLabels_eq_of_hasMoments`): if `Ẽ` has the
  pseudo-moments of the chosen output, the labels are those of the real line clustering along
  `a = Wᵀ â`, `âᵢ = Ẽ[vᵢ v_j]`, for an index `j` maximizing `Ẽ[v_j²]`. Which output is chosen:
  `BS23.ColinearSoS.outC_of_le`, `BS23.ColinearSoS.outC_of_lt`.
* **The specification** (`BS23.ColinearSoS.colLabels_spec`): for `k ≥ 2`, with the U
  pseudo-expectation `Ẽ_U`, if `(5s)^s ≤ Ẽ_U Φ̂_{2s}` the labels are given by `Ẽ_U`, otherwise by
  an L pseudo-expectation `Ẽ_L`. For `k ≤ 1` all labels are `0`
  (`BS23.ColinearSoS.colLabels_of_le_one`).
* **On a rounded sample** (`BS23.ColinearSoS.colSoS_roundedSample`): the output is the list of
  labels of the rounded points, indexed by the sample, and the budget is `(d + 5)^(2t + 1)`
  (`BS23.ColinearSoS.Lgc_roundedSample`).
-/

@[expose] public section

namespace BS23.ColinearSoS

open MvPolynomial SoS SoS.Solver SoS.Poly Matrix Colinear
open Separating (whiten W kappa acc acc_pos solve qvOf)

variable {n d : ℕ}

/-! ### Parameters -/

/-- `s = logInv wmin + 1`: program U has degree `2s`. -/
def sCol (wmin : ℚ) : ℕ := logInv wmin + 1

/-- `t = 256 s`: program L has degree `2t`. -/
def tCol (wmin : ℚ) : ℕ := 256 * sCol wmin

/-- The threshold `(5s)^s` of the test on `OPT_U`. -/
def testU (wmin : ℚ) : ℚ := ((5 * sCol wmin) ^ sCol wmin : ℕ)

theorem one_le_sCol (wmin : ℚ) : 1 ≤ sCol wmin := by
  unfold sCol
  omega

theorem sCol_le_tCol (wmin : ℚ) : sCol wmin ≤ tCol wmin := by
  unfold tCol
  omega

theorem one_le_tCol (wmin : ℚ) : 1 ≤ tCol wmin :=
  (one_le_sCol wmin).trans (sCol_le_tCol wmin)

theorem cast_testU (wmin : ℚ) : (testU wmin : ℝ) = (5 * (sCol wmin : ℝ)) ^ sCol wmin := by
  simp [testU]

/-! ### The algorithm -/

/-- **Program U** on the points `Y`: degree `2s`, objective `-Φ̂_{2s}` for the whitened points,
and the constraints `‖v‖² ≤ 256`, `vᵀ diag(κ) v = 1`. -/
def progUY (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : Problem :=
  probU Lb (sCol wmin) (whiten Y) (kappa (empCov Y))

/-- **Program L** on the points `Y`: degree `2t`, objective `Φ̂_{2t}`, the same constraints. -/
def progLY (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : Problem :=
  probL Lb (tCol wmin) (whiten Y) (kappa (empCov Y))

/-- The solver output of program U. -/
def outU (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : SoS.Solver.Output :=
  solve Lb (progUY wmin Lb Y)

/-- The solver output of program L. -/
def outL (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : SoS.Solver.Output :=
  solve Lb (progLY wmin Lb Y)

/-- `(1/n) ∑ⱼ Ẽ ⟨Xⱼ, v⟩^r`, read off the pseudo-moments `out` (`BS23.Separating.qvOf`). -/
def momVal (Lb r : ℕ) (X : Fin n → Fin d → ℚ) (out : SoS.Solver.Output) : ℚ :=
  (n : ℚ)⁻¹ * ∑ j, qvOf d Lb r out (X j)

/-- `OPT_U = (1/n) ∑ⱼ Ẽ_U ⟨Xⱼ, v⟩^(2s)`, read off the output of program U. -/
def optU (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : ℚ :=
  momVal Lb (2 * sCol wmin) (whiten Y) (outU wmin Lb Y)

/-- **The chosen output**: that of program U if `OPT_U ≥ (5s)^s`, else that of program L (which
is only solved in that case). -/
def outC (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : SoS.Solver.Output :=
  let oU := outU wmin Lb Y
  if testU wmin ≤ momVal Lb (2 * sCol wmin) (whiten Y) oU then oU else outL wmin Lb Y

/-- The exponent vector of the monomial `v_a v_b` in `d` variables. -/
def pairExp (d a b : ℕ) : List ℕ :=
  (List.range d).map fun i => (if i = a then 1 else 0) + (if i = b then 1 else 0)

/-- `M_ab = Ẽ[v_a v_b]`: the coefficient of `v_a v_b` in the pseudo-moments `out`. -/
def momOut (d : ℕ) (out : SoS.Solver.Output) (a b : ℕ) : ℚ :=
  SoS.Poly.coeff d out (pairExp d a b)

/-- The first index `j* < d` with the largest `M_jj` (`0` if `d = 0`). -/
def jstarOut (d : ℕ) (out : SoS.Solver.Output) : ℕ :=
  argmaxFrom (fun j => momOut d out j j) (List.range d) 0

/-- The column `â = M e_{j*}` of the pseudo-moment matrix. -/
def ahatOut (d : ℕ) (out : SoS.Solver.Output) : Fin d → ℚ :=
  fun i => momOut d out i (jstarOut d out)

section Field

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- The direction `a = Wᵀ â` in the original coordinates, for `W = BS23.Separating.W Ĉ`. -/
def dirOf (Y : Fin n → Fin d → K) (ah : Fin d → K) : Fin d → K := (W (empCov Y))ᵀ *ᵥ ah

/-- **The line clustering along `a`**: the labels of `BS23.OneDim.cluster` on the projections
`⟨a, Yⱼ⟩`, at the scales below `topScale A (aᵀĈa)`, as in the last step of
`BS23.Colinear.alg`. -/
def lineLabels (P : Params K) (k : ℕ) (Y : Fin n → Fin d → K) (a : Fin d → K) : Fin n → ℕ :=
  OneDim.cluster k P.θ P.ε (topScale P.A (quad (empCov Y) a)) (Nat.clog 2 n + 8)
    (fun j ↦ a ⬝ᵥ Y j)

end Field

/-- **The labels** given to the points `Y` with `k` components, weight bound `wmin` and budget
`Lb`: all `0` for `k ≤ 1`, otherwise the line clustering along the direction rounded from the
chosen pseudo-moments. -/
def colLabels (k : ℕ) (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) : Fin n → ℕ :=
  if k ≤ 1 then fun _ => 0 else
    lineLabels (params wmin) k Y (dirOf Y (ahatOut d (outC wmin Lb Y)))

/-- **The algorithm on an input** with the budget `Lb`: the labels of the input's points. -/
def colSoS (x : ColinearInput) (Lb : ℕ) : Output :=
  List.ofFn (colLabels x.k x.wmin Lb (pointsFun x.points))

/-- The global unary budget `(d + 5)^(2t + 1)`. -/
def Lgc (x : ColinearInput) : ℕ := (dim x.points + 5) ^ (2 * tCol x.wmin + 1)

/-- **The algorithm of Theorem 1.2**, sum-of-squares version: `colSoS` with the budget `Lgc`. It
ignores its coins. -/
def colinearSoSAlg (xc : ColinearInput × List Bool) : Output := colSoS xc.1 (Lgc xc.1)

theorem colinearSoSAlg_eq (x : ColinearInput) (c : List Bool) :
    colinearSoSAlg (x, c) = colSoS x (Lgc x) :=
  rfl

@[simp] theorem length_colSoS (x : ColinearInput) (Lb : ℕ) :
    (colSoS x Lb).length = x.points.length :=
  List.length_ofFn

/-- With at most one component, all labels are `0`. -/
theorem colLabels_of_le_one {k : ℕ} (hk : k ≤ 1) (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) :
    colLabels k wmin Lb Y = fun _ => 0 :=
  ite_eq_left hk

theorem colLabels_of_two_le {k : ℕ} (hk : 2 ≤ k) (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) :
    colLabels k wmin Lb Y = lineLabels (params wmin) k Y (dirOf Y (ahatOut d (outC wmin Lb Y))) :=
  ite_eq_right (by omega)

theorem outC_eq (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ) :
    outC wmin Lb Y = if testU wmin ≤ optU wmin Lb Y then outU wmin Lb Y else outL wmin Lb Y :=
  rfl

/-- If `OPT_U ≥ (5s)^s`, the output of U is chosen. -/
theorem outC_of_le {wmin : ℚ} {Lb : ℕ} {Y : Fin n → Fin d → ℚ}
    (h : (5 * (sCol wmin : ℝ)) ^ sCol wmin ≤ (optU wmin Lb Y : ℝ)) :
    outC wmin Lb Y = outU wmin Lb Y := by
  rw [outC_eq]
  refine ite_eq_left ?_
  rw [← cast_testU] at h
  exact_mod_cast h

/-- If `OPT_U < (5s)^s`, the output of L is chosen. -/
theorem outC_of_lt {wmin : ℚ} {Lb : ℕ} {Y : Fin n → Fin d → ℚ}
    (h : (optU wmin Lb Y : ℝ) < (5 * (sCol wmin : ℝ)) ^ sCol wmin) :
    outC wmin Lb Y = outL wmin Lb Y := by
  rw [outC_eq]
  refine ite_eq_right ?_
  rw [← cast_testU] at h
  exact not_le.2 (by exact_mod_cast h)

/-! ### Over the reals -/

/-- The points cast to the reals. On a rounded sample, these are the real rounded points
`BS23.Separating.yt r ω` (by definition). -/
noncomputable def ptsR (Y : Fin n → Fin d → ℚ) : Fin n → Fin d → ℝ := fun j a => (Y j a : ℝ)

theorem ptsR_def (Y : Fin n → Fin d → ℚ) : ptsR Y = fun j a => (Y j a : ℝ) :=
  rfl

theorem whiten_ptsR (Y : Fin n → Fin d → ℚ) :
    whiten (ptsR Y) = fun j i => ((whiten Y j i : ℚ) : ℝ) :=
  Separating.whiten_cast Y

theorem kappa_ptsR (Y : Fin n → Fin d → ℚ) :
    kappa (empCov (ptsR Y)) = fun i => ((kappa (empCov Y) i : ℚ) : ℝ) := by
  funext i
  rw [ptsR_def, empCov_cast, Separating.kappa_cast]

theorem dirOf_cast (Y : Fin n → Fin d → ℚ) (ah : Fin d → ℚ) :
    dirOf (ptsR Y) (fun i => (ah i : ℝ)) = fun i => ((dirOf Y ah i : ℚ) : ℝ) := by
  rw [dirOf, dirOf, ptsR_def, empCov_cast, Separating.W_cast, ← Matrix.transpose_map, mulVec_cast]

/-- **The line clustering commutes with casting.** -/
theorem lineLabels_cast (P : Params ℚ) (k : ℕ) (Y : Fin n → Fin d → ℚ) (a : Fin d → ℚ) :
    lineLabels P k Y a = lineLabels P.cast k (ptsR Y) (fun i => (a i : ℝ)) := by
  simp only [lineLabels, ptsR_def, Params.cast, empCov_cast, quad_cast, topScale_cast,
    dotProduct_cast, OneDim.cluster_cast]

theorem lineLabels_def {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FloorRing K] (P : Params K) (k : ℕ) (Y : Fin n → Fin d → K) (a : Fin d → K) :
    lineLabels P k Y a = OneDim.cluster k P.θ P.ε (topScale P.A (quad (empCov Y) a))
      (Nat.clog 2 n + 8) (fun j ↦ a ⬝ᵥ Y j) :=
  rfl

/-! ### Reading the pseudo-moments -/

namespace AlgC

theorem toFinsupp_pairExp (a b : Fin d) :
    Mono.toFinsupp d (pairExp d a b) = Finsupp.single a 1 + Finsupp.single b 1 := by
  ext i
  rw [Mono.toFinsupp_apply, pairExp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range i.2, Option.map_some, Option.getD_some, Finsupp.add_apply,
    Finsupp.single_apply, Finsupp.single_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

theorem length_pairExp (d a b : ℕ) : (pairExp d a b).length = d := by
  simp [pairExp]

end AlgC

/-- **Reading `Ẽ[v_a v_b]`**: if `out` lists the pseudo-moments of `Ẽ` (of degree `ℓ ≥ 2`), then
`M_ab = Ẽ[v_a v_b]`. -/
theorem momOut_eq {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {out : SoS.Solver.Output}
    {E : PseudoExpectation (Fin d) ℓ} (hE : HasMoments E (out.toPoly d)) (a b : Fin d) :
    (momOut d out a b : ℝ) = E (X a * X b) := by
  have hdeg : (Finsupp.single a 1 + Finsupp.single b 1 : Fin d →₀ ℕ).degree ≤ ℓ := by
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    exact hℓ
  rw [momOut, ← coeff_toPoly out (AlgC.length_pairExp d a b), AlgC.toFinsupp_pairExp,
    ← hE _ hdeg, X, X, monomial_mul_monomial, one_mul]

theorem jstarOut_lt (hd : 0 < d) (out : SoS.Solver.Output) : jstarOut d out < d := by
  have h := (argmaxFrom_spec (fun j => momOut d out j j) (List.range d) 0).1
  rcases List.mem_cons.1 h with h | h
  · rw [jstarOut, h]
    exact hd
  · exact List.mem_range.1 h

/-- `j*` maximizes `M_jj`. -/
theorem momOut_le_jstarOut (out : SoS.Solver.Output) {i : ℕ} (hi : i < d) :
    momOut d out i i ≤ momOut d out (jstarOut d out) (jstarOut d out) :=
  (argmaxFrom_spec (fun j => momOut d out j j) (List.range d) 0).2 i
    (List.mem_cons_of_mem _ (List.mem_range.2 hi))

/-- **Reading `(1/n) ∑ⱼ Ẽ ⟨Xⱼ, v⟩^r`**: if `out` lists the pseudo-moments of `Ẽ` up to degree
`ℓ ≥ r` and nothing is cut, it is `Ẽ Φ̂_r`. -/
theorem momVal_eq {ℓ Lb r : ℕ} {out : SoS.Solver.Output} {E : PseudoExpectation (Fin d) ℓ}
    (hE : HasMoments E (out.toPoly d)) (hr : r ≤ ℓ) (hLb : (d + 1) ^ r ≤ Lb)
    (X : Fin n → Fin d → ℚ) :
    (momVal Lb r X out : ℝ) = E (empPoly (fun j k => (X j k : ℝ)) r) := by
  rw [momVal, empPoly, E.map_smul, E.map_sum, Rat.cast_mul, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  congr 1
  exact Finset.sum_congr rfl fun j _ => Separating.qvOf_eq hE hr hLb (X j)

/-- **The output in real terms**: for `k ≥ 2` and `d ≥ 1`, if `Ẽ` (of degree `ℓ ≥ 2`) has the
pseudo-moments of the chosen output, there is an index `j` maximizing `Ẽ[v_j²]` such that the
labels are those of the real line clustering along `a = Wᵀ â`, `âᵢ = Ẽ[vᵢ v_j]`. -/
theorem colLabels_eq_of_hasMoments {k : ℕ} (hk : 2 ≤ k) (hd : 0 < d) {wmin : ℚ} {Lb : ℕ}
    {Y : Fin n → Fin d → ℚ} {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {E : PseudoExpectation (Fin d) ℓ}
    (hE : HasMoments E ((outC wmin Lb Y).toPoly d)) :
    ∃ j : Fin d, (∀ i, E (X i * X i) ≤ E (X j * X j)) ∧
      colLabels k wmin Lb Y =
        lineLabels (params wmin).cast k (ptsR Y) (dirOf (ptsR Y) fun i => E (X i * X j)) := by
  set out := outC wmin Lb Y with hout
  refine ⟨⟨jstarOut d out, jstarOut_lt hd out⟩, fun i => ?_, ?_⟩
  · rw [← momOut_eq hℓ hE, ← momOut_eq hℓ hE]
    exact_mod_cast momOut_le_jstarOut out i.2
  · have hah : (fun i : Fin d => E (X i * X ⟨jstarOut d out, jstarOut_lt hd out⟩)) =
        fun i => (ahatOut d out i : ℝ) := by
      funext i
      rw [← momOut_eq hℓ hE]
      rfl
    rw [colLabels_of_two_le hk, lineLabels_cast, hah, dirOf_cast]

/-! ### The specification of the solver calls -/

/-- What the analysis uses about a pseudo-expectation `Ẽ` of degree `2m` with the pseudo-moments
`out`, for the points `Y` (real points `y = ptsR Y`, `D = diag(kappa (empCov y))`) and slack
`η`: the moments, bounded values, the equality `vᵀDv = 1` against sums of squares, and
`M_ab = Ẽ[v_a v_b]`. -/
structure SolPE (m : ℕ) (Y : Fin n → Fin d → ℚ) (η : ℝ) (out : SoS.Solver.Output)
    (E : PseudoExpectation (Fin d) (2 * m)) : Prop where
  /-- The output lists the pseudo-moments of `Ẽ`. -/
  moments : HasMoments E (out.toPoly d)
  /-- `|Ẽ f| ≤ ‖f‖₁ 258^m` for `deg f ≤ 2m`. -/
  bound : ∀ f : MvPolynomial (Fin d) ℝ, f.totalDegree ≤ 2 * m → |E f| ≤ coeffNorm1 f * 258 ^ m
  /-- `|Ẽ[h (vᵀDv - 1)]| ≤ η ‖h‖₂ ‖vᵀDv - 1‖₂` for every sum of squares `h` with
  `deg h ≤ 2m - 2`. -/
  sph : ∀ h : MvPolynomial (Fin d) ℝ, IsSumSq h → h.totalDegree + 2 ≤ 2 * m →
    |E (h * (quadPoly (diagonal (kappa (empCov (ptsR Y)))) - 1))| ≤
      η * coeffNorm h * coeffNorm (quadPoly (diagonal (kappa (empCov (ptsR Y)))) - 1)
  /-- `M_ab = Ẽ[v_a v_b]`. -/
  mom_eq : ∀ a b : Fin d, (momOut d out a b : ℝ) = E (X a * X b)

/-- **A pseudo-expectation behind a correct output of program U** (`acc = acc (progUY …)`):
`BS23.ColinearSoS.SolPE` with slack `2 acc`, the constraints with slack `2 acc`,
near-optimality `Φ̂_{2s}(v) - acc ≤ Ẽ Φ̂_{2s}` for every real `v` with `‖v‖² ≤ 256` and
`vᵀDv = 1`, and `OPT_U = Ẽ Φ̂_{2s}`. -/
structure SpecU (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ)
    (E : PseudoExpectation (Fin d) (2 * sCol wmin)) : Prop extends
    SolPE (sCol wmin) Y (2 * acc (progUY wmin Lb Y)) (outU wmin Lb Y) E where
  /-- `Ẽ` satisfies the constraints with slack `2 acc`. -/
  approx : E.ApproxSatisfies (progUY wmin Lb Y).system (2 * (acc (progUY wmin Lb Y) : ℝ)) 0
  /-- Near-optimality against every feasible real point. -/
  opt : ∀ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 →
    eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1 →
      eval v (empPoly (whiten (ptsR Y)) (2 * sCol wmin)) - acc (progUY wmin Lb Y) ≤
        E (empPoly (whiten (ptsR Y)) (2 * sCol wmin))
  /-- `OPT_U = Ẽ Φ̂_{2s}`. -/
  optU_eq : (optU wmin Lb Y : ℝ) = E (empPoly (whiten (ptsR Y)) (2 * sCol wmin))

/-- **A pseudo-expectation behind a correct output of program L** (`acc = acc (progLY …)`):
`BS23.ColinearSoS.SolPE` with slack `2 acc`, the constraints with slack `2 acc`, and
near-optimality `Ẽ Φ̂_{2t} ≤ Φ̂_{2t}(v) + acc` for every real `v` with `‖v‖² ≤ 256` and
`vᵀDv = 1`. -/
structure SpecL (wmin : ℚ) (Lb : ℕ) (Y : Fin n → Fin d → ℚ)
    (E : PseudoExpectation (Fin d) (2 * tCol wmin)) : Prop extends
    SolPE (tCol wmin) Y (2 * acc (progLY wmin Lb Y)) (outL wmin Lb Y) E where
  /-- `Ẽ` satisfies the constraints with slack `2 acc`. -/
  approx : E.ApproxSatisfies (progLY wmin Lb Y).system (2 * (acc (progLY wmin Lb Y) : ℝ)) 0
  /-- Near-optimality against every feasible real point. -/
  opt : ∀ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 →
    eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1 →
      E (empPoly (whiten (ptsR Y)) (2 * tCol wmin)) ≤
        eval v (empPoly (whiten (ptsR Y)) (2 * tCol wmin)) + acc (progLY wmin Lb Y)

namespace AlgC

theorem pow_le_of_le {wmin : ℚ} {Lb : ℕ} (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb) :
    (d + 1) ^ (2 * tCol wmin) ≤ Lb :=
  (Nat.pow_le_pow_left (by omega) _).trans ((Nat.pow_le_pow_right (by omega) (by omega)).trans hLb)

theorem pow_s_le {wmin : ℚ} {Lb : ℕ} (hLb : (d + 1) ^ (2 * tCol wmin) ≤ Lb) :
    (d + 1) ^ (2 * sCol wmin) ≤ Lb :=
  (Nat.pow_le_pow_right (by omega) (by have := sCol_le_tCol wmin; omega)).trans hLb

theorem pow5_le_of_le {wmin : ℚ} {Lb : ℕ} (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb) {m : ℕ}
    (hm : m ≤ tCol wmin) : (d + 5) ^ (2 * m + 1) ≤ Lb :=
  (Nat.pow_le_pow_right (by omega) (by omega)).trans hLb

/-- The feasibility condition with the real `κ`. -/
theorem sph_cast {Y : Fin n → Fin d → ℚ} {v : Fin d → ℝ}
    (hsph : eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1) :
    eval v (quadPoly (diagonal fun i => ((kappa (empCov Y) i : ℚ) : ℝ))) = 1 := by
  rwa [← kappa_ptsR]

theorem diag_cast (Y : Fin n → Fin d → ℚ) :
    quadPoly (diagonal fun i => ((kappa (empCov Y) i : ℚ) : ℝ)) =
      quadPoly (diagonal (kappa (empCov (ptsR Y)))) := by
  rw [kappa_ptsR]

end AlgC

/-- **Program U is valid** if some real point has `‖v‖² ≤ 256` and `vᵀDv = 1`. -/
theorem valid_progUY {wmin : ℚ} {Lb : ℕ} (hLb : (d + 1) ^ (2 * tCol wmin) ≤ Lb)
    (Y : Fin n → Fin d → ℚ) {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1) :
    (progUY wmin Lb Y).Valid :=
  valid_probU (one_le_sCol wmin) (AlgC.pow_s_le hLb) _ hball (AlgC.sph_cast hsph)

/-- **Program L is valid** if some real point has `‖v‖² ≤ 256` and `vᵀDv = 1`. -/
theorem valid_progLY {wmin : ℚ} {Lb : ℕ} (hLb : (d + 1) ^ (2 * tCol wmin) ≤ Lb)
    (Y : Fin n → Fin d → ℚ) {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1) :
    (progLY wmin Lb Y).Valid :=
  valid_probL (one_le_tCol wmin) hLb _ hball (AlgC.sph_cast hsph)

/-- **The output of U is correct** for a valid program U with a budget `Lb ≥ (d + 5)^(2t+1)`. -/
theorem correct_outU {wmin : ℚ} {Lb : ℕ} {Y : Fin n → Fin d → ℚ}
    (hP : (progUY wmin Lb Y).Valid) (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb) :
    Correct (progUY wmin Lb Y) (acc (progUY wmin Lb Y)) (acc (progUY wmin Lb Y))
      (outU wmin Lb Y) :=
  correct_solve_progC hP (AlgC.pow5_le_of_le hLb (sCol_le_tCol wmin))

/-- **The output of L is correct** for a valid program L with a budget `Lb ≥ (d + 5)^(2t+1)`. -/
theorem correct_outL {wmin : ℚ} {Lb : ℕ} {Y : Fin n → Fin d → ℚ}
    (hP : (progLY wmin Lb Y).Valid) (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb) :
    Correct (progLY wmin Lb Y) (acc (progLY wmin Lb Y)) (acc (progLY wmin Lb Y))
      (outL wmin Lb Y) :=
  correct_solve_progC hP (AlgC.pow5_le_of_le hLb le_rfl)

/-- The accuracy of program U is at most `2^-n`. -/
theorem acc_progUY_le {wmin : ℚ} {Lb : ℕ} (hLb : 1 ≤ Lb) (Y : Fin n → Fin d → ℚ) :
    (acc (progUY wmin Lb Y) : ℝ) ≤ 1 / 2 ^ n :=
  acc_probU_le hLb _ _ _

/-- The accuracy of program L is at most `2^-n`. -/
theorem acc_progLY_le {wmin : ℚ} {Lb : ℕ} (hLb : 1 ≤ Lb) (Y : Fin n → Fin d → ℚ) :
    (acc (progLY wmin Lb Y) : ℝ) ≤ 1 / 2 ^ n :=
  acc_probL_le hLb _ _ _

/-- **The U pseudo-expectation**: if some real point has `‖v‖² ≤ 256` and `vᵀDv = 1`, and
`Lb ≥ (d + 5)^(2t+1)`, there is a pseudo-expectation with the properties of
`BS23.ColinearSoS.SpecU`. -/
theorem exists_specU {wmin : ℚ} {Lb : ℕ} (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb)
    (Y : Fin n → Fin d → ℚ) {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1) :
    ∃ E : PseudoExpectation (Fin d) (2 * sCol wmin), SpecU wmin Lb Y E := by
  have hs := AlgC.pow_s_le (AlgC.pow_le_of_le hLb)
  obtain ⟨E, hE⟩ := exists_progSpec
    (correct_outU (valid_progUY (AlgC.pow_le_of_le hLb) Y hball hsph) hLb)
  have hobj : toReal ((momRaw (-(n : ℚ)⁻¹) Lb (2 * sCol wmin) (whiten Y)).toPoly d) =
      -empPoly (whiten (ptsR Y)) (2 * sCol wmin) := by
    rw [toReal_momRaw_neg_inv hs, whiten_ptsR]
  refine ⟨E, ⟨⟨hE.moments, hE.bound, fun h hh hdeg => ?_, momOut_eq (by
    have := one_le_sCol wmin; omega) hE.moments⟩, hE.approx, fun w hw hwsph => ?_, ?_⟩⟩
  · have h1 := hE.sph h hh hdeg
    rwa [AlgC.diag_cast] at h1
  · have h1 := hE.opt w hw (AlgC.sph_cast hwsph)
    rw [hobj, eval_neg, E.map_neg] at h1
    change _ ≤ _ + ((acc (progUY wmin Lb Y) : ℚ) : ℝ) at h1
    linarith
  · rw [optU, momVal_eq hE.moments le_rfl hs, whiten_ptsR]

/-- **The L pseudo-expectation**: if some real point has `‖v‖² ≤ 256` and `vᵀDv = 1`, and
`Lb ≥ (d + 5)^(2t+1)`, there is a pseudo-expectation with the properties of
`BS23.ColinearSoS.SpecL`. -/
theorem exists_specL {wmin : ℚ} {Lb : ℕ} (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb)
    (Y : Fin n → Fin d → ℚ) {v : Fin d → ℝ} (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1) :
    ∃ E : PseudoExpectation (Fin d) (2 * tCol wmin), SpecL wmin Lb Y E := by
  have ht := AlgC.pow_le_of_le hLb
  obtain ⟨E, hE⟩ := exists_progSpec
    (correct_outL (valid_progLY (AlgC.pow_le_of_le hLb) Y hball hsph) hLb)
  have hobj : toReal ((momRaw ((n : ℚ)⁻¹) Lb (2 * tCol wmin) (whiten Y)).toPoly d) =
      empPoly (whiten (ptsR Y)) (2 * tCol wmin) := by
    rw [toReal_momRaw_inv ht, whiten_ptsR]
  refine ⟨E, ⟨⟨hE.moments, hE.bound, fun h hh hdeg => ?_, momOut_eq (by
    have := one_le_tCol wmin; omega) hE.moments⟩, hE.approx, fun w hw hwsph => ?_⟩⟩
  · have h1 := hE.sph h hh hdeg
    rwa [AlgC.diag_cast] at h1
  · have h1 := hE.opt w hw (AlgC.sph_cast hwsph)
    rwa [hobj] at h1

/-! ### The specification of the algorithm -/

/-- **The specification of the algorithm** for `k ≥ 2` and `d ≥ 1`. If some real point has
`‖v‖² ≤ 256` and `vᵀDv = 1` and `Lb ≥ (d + 5)^(2t+1)`, there is a U pseudo-expectation `Ẽ_U`
(`BS23.ColinearSoS.SpecU`) such that:
* if `(5s)^s ≤ Ẽ_U Φ̂_{2s}`, the labels are those of the line clustering along `Wᵀ â`,
  `âᵢ = Ẽ_U[vᵢ v_j]`, for an index `j` maximizing `Ẽ_U[v_j²]`;
* otherwise, there is an L pseudo-expectation `Ẽ_L` (`BS23.ColinearSoS.SpecL`) such that the same
  holds with `Ẽ_L`. -/
theorem colLabels_spec {k : ℕ} (hk : 2 ≤ k) (hd : 0 < d) {wmin : ℚ} {Lb : ℕ}
    {Y : Fin n → Fin d → ℚ} (hLb : (d + 5) ^ (2 * tCol wmin + 1) ≤ Lb) {v : Fin d → ℝ}
    (hball : ∑ i, v i ^ 2 ≤ 256)
    (hsph : eval v (quadPoly (diagonal (kappa (empCov (ptsR Y))))) = 1) :
    ∃ EU : PseudoExpectation (Fin d) (2 * sCol wmin), SpecU wmin Lb Y EU ∧
      ((5 * (sCol wmin : ℝ)) ^ sCol wmin ≤ EU (empPoly (whiten (ptsR Y)) (2 * sCol wmin)) →
        ∃ j : Fin d, (∀ i, EU (X i * X i) ≤ EU (X j * X j)) ∧
          colLabels k wmin Lb Y =
            lineLabels (params wmin).cast k (ptsR Y) (dirOf (ptsR Y) fun i => EU (X i * X j))) ∧
      (EU (empPoly (whiten (ptsR Y)) (2 * sCol wmin)) < (5 * (sCol wmin : ℝ)) ^ sCol wmin →
        ∃ EL : PseudoExpectation (Fin d) (2 * tCol wmin), SpecL wmin Lb Y EL ∧
          ∃ j : Fin d, (∀ i, EL (X i * X i) ≤ EL (X j * X j)) ∧
            colLabels k wmin Lb Y =
              lineLabels (params wmin).cast k (ptsR Y)
                (dirOf (ptsR Y) fun i => EL (X i * X j))) := by
  obtain ⟨EU, hU⟩ := exists_specU hLb Y hball hsph
  refine ⟨EU, hU, fun h => ?_, fun h => ?_⟩
  · rw [← hU.optU_eq] at h
    have hmom : HasMoments EU ((outC wmin Lb Y).toPoly d) := by
      rw [outC_of_le h]
      exact hU.moments
    exact colLabels_eq_of_hasMoments hk hd (by have := one_le_sCol wmin; omega) hmom
  · rw [← hU.optU_eq] at h
    obtain ⟨EL, hL⟩ := exists_specL hLb Y hball hsph
    have hmom : HasMoments EL ((outC wmin Lb Y).toPoly d) := by
      rw [outC_of_lt h]
      exact hL.moments
    exact ⟨EL, hL, colLabels_eq_of_hasMoments hk hd (by have := one_le_tCol wmin; omega) hmom⟩

/-! ### On a rounded sample -/

/-- **The algorithm on a rounded sample** lists the labels of the rounded points
`fun j a ↦ r (ω j) a`, indexed by the sample. -/
theorem colSoS_roundedSample {k : ℕ} (k' : ℕ) (wmin : ℚ) (Lb : ℕ) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    colSoS ⟨k', wmin, roundedSample r ω⟩ Lb =
      List.ofFn (colLabels k' wmin Lb fun j a ↦ r (ω j) a) := by
  rw [colSoS, ofFn_pointsFun_roundedSample (fun _ _ Y ↦ colLabels k' wmin Lb Y)]

/-- The budget on a nonempty rounded sample is `(d + 5)^(2t + 1)`. -/
theorem Lgc_roundedSample {k : ℕ} (k' : ℕ) (wmin : ℚ) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (hn : 0 < n) :
    Lgc ⟨k', wmin, roundedSample r ω⟩ = (d + 5) ^ (2 * tCol wmin + 1) := by
  rw [Lgc, dim_roundedSample r ω hn]

/-- **The algorithm of the theorem on a rounded sample.** -/
theorem colinearSoSAlg_roundedSample {k : ℕ} (k' : ℕ) (wmin : ℚ) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (hn : 0 < n) (c : List Bool) :
    colinearSoSAlg (⟨k', wmin, roundedSample r ω⟩, c) =
      List.ofFn (colLabels k' wmin ((d + 5) ^ (2 * tCol wmin + 1)) fun j a ↦ r (ω j) a) := by
  rw [colinearSoSAlg_eq, Lgc_roundedSample k' wmin r ω hn, colSoS_roundedSample]

end BS23.ColinearSoS
