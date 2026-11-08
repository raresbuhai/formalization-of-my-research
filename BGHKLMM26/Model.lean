module

public import Background.Encoding
public import Background.UniqueGames
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Max 2-LIN(2), Max-Cut, and randomized algorithms

The definitions that the main theorems of [BGHKLMM26] are stated in (`BGHKLMM26/Challenge.lean`).
Together with what they import (Mathlib, CSLib's multitape Turing machines, complexitylib's
complexity classes, and the encodings and Unique Games definitions in `Background/`), they are what
a reader has to check to know what the theorems say.

* **The Goemans–Williamson constant** (`BGHKLMM26.alphaGW`): the infimum over `-1 ≤ ρ < 1` of
  `(arccos ρ / π) / ((1 - ρ) / 2)`, and its minimizers (`BGHKLMM26.IsGWMinimizer`), which give
  `c* = (1 - ρ*) / 2` and `s* = arccos ρ* / π`.
* **Max 2-LIN(2)** (`BGHKLMM26.Instance`): `n` variables `xᵢ ∈ {±1}` and a list of constraints
  `xᵢ xⱼ = b` with rational weights `w ≥ 0`, on distinct pairs `i < j < n`
  (`BGHKLMM26.Valid`). The number `n` is encoded in unary, so that an algorithm can afford to
  output an assignment of all `n` variables. The value of an assignment is the total weight of
  the constraints it satisfies (`BGHKLMM26.satWeight`), and `BGHKLMM26.opt` is the largest
  value. In a Max-Cut instance (`BGHKLMM26.IsMaxCutInstance`) every constraint is `xᵢ xⱼ = -1`
  with weight `1`: a valid one is a simple graph, and the value of an assignment is the number of
  edges it cuts.
* **Randomized algorithms** (`BGHKLMM26.RunsInTime`): a deterministic multitape Turing machine that
  reads an instance `x` and a string `r` of coin flips and halts within `O(T |x| + |(x, r)|)`
  steps. Expectations are over coin strings of exactly `T |x|` flips (`BGHKLMM26.coinMean`).
* **Max-Cut** (`BGHKLMM26.Graph`): a simple graph on `0, …, n - 1`, encoded by `n` and its
  adjacency table. Its value `BGHKLMM26.maxCutValue` is the largest fraction of edges crossing a
  cut, and `BGHKLMM26.maxCutGap d c s` is the promise problem of telling graphs of maximum degree
  at most `d` with value at least `c` from those with value at most `s`.
* **The SDP relaxation** of Max-Cut, the Goemans–Williamson SDP with triangle inequalities:
  `BGHKLMM26.IsSDPSolution` says that vectors `v₀, …, vₙ₋₁ ∈ ℝⁿ` are feasible, and
  `BGHKLMM26.sdpValue` is their value, the average of `‖vᵢ - vⱼ‖² / 4` over the edges.
* **The Unique Games Conjecture** (`UniqueGames.UGC`) is the repository's shared one, in
  `Background/UniqueGames.lean`, in the form of [BGHKLMM26, Conjecture 4.10]: for every small
  enough `ε > 0` there is an alphabet size `R` such that telling simple bi-regular bipartite Unique
  Games instances of value at least `1 - ε` from those of value at most `ε` is NP-hard.

Reference: [BGHKLMM26] R.-D. Buhai, S. Ghoshal, N. Huang, P. K. Kothari, E. Lee,
K. Makarychev, Y. Makarychev, *Optimal Algorithms and Hardness for Max-Cut in Bounded Degree
Graphs*, SODA 2027, arXiv:2610.27216.
-/

@[expose] public section

namespace BGHKLMM26

open Encoding

/-! ### The Goemans–Williamson constant -/

/-- The ratio `(arccos ρ / π) / ((1 - ρ) / 2)`: the probability that hyperplane rounding cuts an
edge whose vectors have inner product `ρ`, over the edge's contribution to the SDP. -/
noncomputable def gwRatio (ρ : ℝ) : ℝ := (Real.arccos ρ / Real.pi) / ((1 - ρ) / 2)

/-- The **Goemans–Williamson constant** `α_GW ≈ 0.878`: the infimum of `gwRatio` over
`-1 ≤ ρ < 1`. -/
noncomputable def alphaGW : ℝ := sInf (gwRatio '' Set.Ico (-1) 1)

/-- `ρ` minimizes `gwRatio` over `-1 ≤ ρ < 1`. There is exactly one such `ρ*`, about `-0.689`
(`BGHKLMM26.exists_unique_isGWMinimizer` in `Challenge.lean`). -/
def IsGWMinimizer (ρ : ℝ) : Prop :=
  ρ ∈ Set.Ico (-1 : ℝ) 1 ∧ ∀ σ ∈ Set.Ico (-1 : ℝ) 1, gwRatio ρ ≤ gwRatio σ

/-! ### Max 2-LIN(2) -/

/-- A constraint `((i, j), b, w)`: the equation `xᵢ xⱼ = b` on `±1` variables, with `b = true`
for `+1` and `b = false` for `-1`, and weight `w`. -/
abbrev Constraint := (ℕ × ℕ) × Bool × ℚ

/-- A **Max 2-LIN(2) instance** `(n, cs)`: the number `n` of variables and a list `cs` of
constraints. Max-Cut is the case where every `b` is `-1`. -/
abbrev Instance := ℕ × List Constraint

/-- The number of variables is in unary: the output lists a value for each of them, so the input
must be at least as long. The variables in the constraints and the weights are in binary. -/
def encInstance : Instance ↪ List Bool :=
  encPair encUnary (encList (encPair (encPair encNat encNat) (encPair encBool encRat)))

/-- A **valid** instance: every constraint is on two variables `i < j < n` and has weight `w ≥ 0`,
and no two constraints are on the same pair, so that the constraints are the weighted edges of a
graph. -/
def Valid (I : Instance) : Prop :=
  (∀ c ∈ I.2, c.1.1 < c.1.2 ∧ c.1.2 < I.1 ∧ 0 ≤ c.2.2) ∧ (I.2.map Prod.fst).Nodup

/-- The number of constraints containing the variable `v`. -/
def degree (I : Instance) (v : ℕ) : ℕ :=
  (I.2.filter fun c ↦ c.1.1 = v ∨ c.1.2 = v).length

/-- Every variable appears in at most `d` constraints. -/
def MaxDegreeLE (I : Instance) (d : ℕ) : Prop := ∀ v, degree I v ≤ d

/-- The total weight of the constraints satisfied by the assignment `x`, with `x v = true` for
`+1` and `x v = false` for `-1`: `xᵢ xⱼ = b` holds when `xᵢ = xⱼ` is `b`. -/
def satWeight (I : Instance) (x : ℕ → Bool) : ℝ :=
  (I.2.map fun c ↦ if decide (x c.1.1 = x c.1.2) = c.2.1 then (c.2.2 : ℝ) else 0).sum

/-- The **optimum** of the instance: the largest total weight satisfied by an assignment of the
`n` variables. -/
noncomputable def opt (I : Instance) : ℝ :=
  ⨆ x : Fin I.1 → Bool, satWeight I fun v ↦ if h : v < I.1 then x ⟨v, h⟩ else false

/-- The total weight satisfied by an output `y`, read as the assignment `xᵥ = y[v]` (`false`, that
is `-1`, past the end of `y`). -/
def outputWeight (I : Instance) (y : List Bool) : ℝ := satWeight I fun v ↦ y.getD v false

/-- A **Max-Cut instance**: every constraint is `xᵢ xⱼ = -1` with weight `1`. A valid one is a
simple graph whose edges are the constraints, and the value of an assignment is the number of
edges it cuts. -/
def IsMaxCutInstance (I : Instance) : Prop := ∀ c ∈ I.2, c.2 = (false, 1)

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an instance `x` and a coin string `r`, halts with output `A (x, r)`
within `c (T |x| + |(x, r)| + 1)` steps and cells, for a constant `c`. Here `|x|` is the length of
the encoded instance. The machine reads its whole input, so the bound includes the length of the
input with the coins; `BGHKLMM26.coinMean` gives it exactly `T |x|` coins. -/
def RunsInTime (A : Instance × List Bool → List Bool) (T : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encInstance encBits) encBits
    (fun xr ↦ c * (T (encInstance xr.1).length + (encPair encInstance encBits xr).length + 1))
    (fun xr ↦ c * (T (encInstance xr.1).length + (encPair encInstance encBits xr).length + 1))

/-- The mean of `f` over the uniformly random strings of `m` coin flips. -/
noncomputable def coinMean (m : ℕ) (f : List Bool → ℝ) : ℝ :=
  (∑ r : Fin m → Bool, f (List.ofFn r)) / 2 ^ m

/-! ### Max-Cut -/

/-- A **graph** `⟨n, G⟩`: a simple graph on the vertices `0, …, n - 1`. -/
abbrev Graph := (n : ℕ) × SimpleGraph (Fin n)

open Classical in
/-- The adjacency table of a graph: the `n²` bits `[u ~ v]`, row by row. -/
noncomputable def adjTable (H : Graph) : List Bool :=
  List.ofFn fun k : Fin (H.1 * H.1) ↦
    decide (H.2.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

theorem adjTable_injective {n : ℕ} {G G' : SimpleGraph (Fin n)}
    (h : adjTable ⟨n, G⟩ = adjTable ⟨n, G'⟩) : G = G' := by
  classical
  have h' := List.ofFn_injective h
  ext u v
  simpa using congrFun h' (finProdFinEquiv (u, v))

/-- A graph is encoded by its number of vertices and its adjacency table. -/
noncomputable def encGraph : Graph ↪ List Bool :=
  ⟨fun H ↦ encPair encNat encBits (H.1, adjTable H), by
    rintro ⟨n, G⟩ ⟨n', G'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.1 ((encPair encNat encBits).injective h)
    rw [adjTable_injective h2]⟩

open Classical in
/-- The number of edges of `G` crossing the cut `x`. -/
noncomputable def cutSize {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : ℕ :=
  (G.edgeFinset.filter fun e ↦ ∀ u ∈ e, ∀ v ∈ e, u ≠ v → x u ≠ x v).card

open Classical in
/-- The **Max-Cut value** of a graph: the largest fraction of its edges crossing a cut, and `0` for
a graph with no edges. -/
noncomputable def maxCutValue (H : Graph) : ℝ :=
  (((Finset.univ : Finset (Fin H.1 → Bool)).sup (cutSize H.2) : ℕ) : ℝ) / H.2.edgeFinset.card

open Classical in
/-- Every vertex has at most `d` neighbours. -/
def MaxDegreeAtMost (H : Graph) (d : ℕ) : Prop := ∀ v, H.2.degree v ≤ d

open Cslib.Complexity in
/-- The **gap problem** of Max-Cut on graphs of maximum degree at most `d`: the yes-instances have
Max-Cut value at least `c`, the no-instances at most `s`, with `s < c` (complexitylib's
`Cslib.Complexity.PromiseProblem.gapMax`), both restricted to maximum degree at most `d`. -/
noncomputable def maxCutGap (d : ℕ) (c s : ℝ) : PromiseProblem Graph :=
  (PromiseProblem.gapMax maxCutValue (fun _ ↦ c) (fun _ ↦ s)).restrict
    {H | MaxDegreeAtMost H d}

/-! ### The SDP relaxation of Max-Cut -/

open scoped RealInnerProductSpace in
/-- A solution of the **Goemans–Williamson SDP with triangle inequalities** on `n` vertices
[BGHKLMM26, Section 3]: unit vectors `v₀, …, vₙ₋₁ ∈ ℝⁿ` with
`σᵢσⱼ ⟨vᵢ, vⱼ⟩ + σᵢσₖ ⟨vᵢ, vₖ⟩ + σⱼσₖ ⟨vⱼ, vₖ⟩ ≥ -1` for all distinct `i, j, k` and all signs
`σᵢ, σⱼ, σₖ ∈ {±1}`, which are the `ℓ₂²` triangle inequalities among the vectors `±vᵢ`. Every cut
gives a solution, with `vᵢ = ±e₀` according to the side of `i`. -/
def IsSDPSolution (n : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧
    ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
      ∀ a ∈ ({1, -1} : Set ℝ), ∀ b ∈ ({1, -1} : Set ℝ), ∀ c ∈ ({1, -1} : Set ℝ),
        -1 ≤ a * b * ⟪v i, v j⟫ + a * c * ⟪v i, v k⟫ + b * c * ⟪v j, v k⟫

open Classical in
/-- The **SDP value** of the vectors `v` for the graph `H`: the average over the edges `{i, j}` of
`‖vᵢ - vⱼ‖² / 4`, which is `(1 - ⟨vᵢ, vⱼ⟩) / 2` for unit vectors, and `0` for a graph with no
edges. It is normalized like `BGHKLMM26.maxCutValue`: the solution `vᵢ = ±e₀` of a cut has value
the fraction of edges the cut crosses. -/
noncomputable def sdpValue (H : Graph) (v : Fin H.1 → EuclideanSpace ℝ (Fin H.1)) : ℝ :=
  (∑ e ∈ H.2.edgeFinset,
    Sym2.lift ⟨fun i j ↦ ‖v i - v j‖ ^ 2 / 4, fun i j ↦ by dsimp only; rw [norm_sub_rev]⟩ e) /
    H.2.edgeFinset.card

end BGHKLMM26
