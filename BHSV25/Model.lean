module

public import Background.Encoding
public import Background.UniqueGames
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Complexity.Classes.NP
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Graphs, spectra, colorings and models

The definitions that the main theorems of [BHSV25] are stated in (`BHSV25/Challenge.lean`).
Together with what they import (Mathlib, CSLib's multitape Turing machines, complexitylib's
polynomial time, `P`, `NP` and NP-hardness of promise problems, and the Unique Games Conjecture of
`Background/UniqueGames.lean`), they are what a reader has to check to know what the theorems
say.

* **Graphs** (`BHSV25.Graph`): a simple graph on `0, …, n - 1`, encoded by `n` and its adjacency
  table (`BHSV25.encGraph`). Algorithms are deterministic multitape Turing machines running in
  polynomial time in the length of this encoding (complexitylib's
  `Turing.MultiTapeTM.ComputableInPolyTime`), so polynomial in `n`.
* **Spectra** (`BHSV25.Graph.normAdj`, `BHSV25.Graph.eig`): the eigenvalues, with multiplicity, of
  the normalized adjacency matrix `D^(-1/2) A D^(-1/2)`, which is `A / d` for a `d`-regular graph.
  A **`λ`-one-sided expander** (`BHSV25.Graph.IsOneSidedExpander`) has at most one eigenvalue
  larger than `λ`: its second largest eigenvalue is at most `λ`.
* **Independent sets and vertex covers** are output as membership bits, one per vertex
  (`BHSV25.Graph.vertexSet`).
* **Colorings** are output as one color per vertex (`BHSV25.Graph.color`); a color `≥ k` means
  "uncolored". A **`(k, δ)`-coloring** (`BHSV25.Graph.IsColoring`, [BHSV25, Definition 3.1]) is a
  list of `k` disjoint independent sets, the color classes, covering at least `(1 - δ) n`
  vertices.
* **Models** (`BHSV25.IsModel`): reversible row-stochastic `k × k` matrices with zero diagonal and
  second largest eigenvalue at most `0`. The model of a partition `χ` of a graph
  (`BHSV25.Graph.model`, [BHSV25, Definition 3.3]) is the matrix of transition probabilities
  between its parts, and an **`(M, δ)`-coloring** (`BHSV25.Graph.IsMColoring`, [BHSV25,
  Definition 3.5]) is a partition whose model is `δ`-close to `M` entrywise and whose
  monochromatic edges are covered by at most `δ n` vertices.
* **Partitions proper up to `δ n` vertices** (`BHSV25.Graph.IsAlmostProper`): the edges inside
  the parts are covered by at most `δ n` vertices, as in [BHSV25, Theorem 7.9].
* **Random planting** (`BHSV25.Graph.plant`, [BHSV25, Definition 7.11]): a `k`-coloring `χ` of the
  vertices of a host graph, uniform among the `k^n`, and the host without the edges inside its
  color classes. `BHSV25.Graph.plantProb` is the probability, over `χ`, that the planted graph has
  a given property.
* **Running times** (`BHSV25.RunsInTime A encIn encOut K C`): a deterministic multitape Turing
  machine computes `A` in at most `⌈K (m + 1)^C⌉` steps on inputs whose encoding has length `m`,
  in polynomially bounded space (CSLib's `Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`).
  `BHSV25.RunsInTimeWith A encIn encOut K C` lets the factor depend on the input: one machine
  computes `A` in at most `⌈K a (m + 1)^C⌉` steps on every input `a` of length `m`.
* **Hardness** is conditional on the Unique Games Conjecture on graphs (`UniqueGames.KhotUGC`, in
  `Background/UniqueGames.lean`, which asks for NP-hardness of Unique Games under deterministic
  polynomial-time reductions from every problem in `NP`). The conclusions are NP-hardness, under
  the same reductions, of gap problems of colorings (`BHSV25.coloringGap`): the graphs with a
  promised property that have a `(k, δ)`-coloring against the graphs that have none.

Reference: [BHSV25] R.-D. Buhai, Y. Hua, D. Steurer, A. Vári-Kakas, *Finding Colorings in
One-Sided Expanders*, arXiv:2508.02825 (v2).
-/

@[expose] public section

namespace BHSV25

open Encoding Cslib.Complexity

/-! ### Graphs -/

/-- A **graph** `⟨n, G⟩`: a simple graph on the vertices `0, …, n - 1`. -/
abbrev Graph := (n : ℕ) × SimpleGraph (Fin n)

open Classical in
/-- The adjacency table of a graph: the `n²` bits `[u ~ v]`, row by row. -/
noncomputable def adjTable (G : Graph) : List Bool :=
  List.ofFn fun k : Fin (G.1 * G.1) ↦
    decide (G.2.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

theorem adjTable_injective {n : ℕ} {H H' : SimpleGraph (Fin n)}
    (h : adjTable ⟨n, H⟩ = adjTable ⟨n, H'⟩) : H = H' := by
  classical
  have h' := List.ofFn_injective h
  ext u v
  simpa using congrFun h' (finProdFinEquiv (u, v))

/-- A graph is encoded by its number of vertices and its adjacency table. -/
noncomputable def encGraph : Graph ↪ List Bool :=
  ⟨fun G ↦ encPair encNat encBits (G.1, adjTable G), by
    rintro ⟨n, H⟩ ⟨n', H'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.1 ((encPair encNat encBits).injective h)
    rw [adjTable_injective h2]⟩

/-- Colorings are encoded as lists of numbers in binary. -/
def encColoring : List ℕ ↪ List Bool := encList encNat

namespace Graph

variable (G : Graph)

open Classical in
/-- `G` is **regular**: all its vertices have the same degree. -/
def IsRegular : Prop := ∃ d : ℕ, G.2.IsRegularOfDegree d

/-! ### Spectra -/

open Classical in
/-- The **normalized adjacency matrix** `D^(-1/2) A D^(-1/2)`: the entry of an edge `uv` is
`1 / √(deg u deg v)`, and the other entries are `0`. For a `d`-regular graph it is `A / d`. -/
noncomputable def normAdj : Matrix (Fin G.1) (Fin G.1) ℝ :=
  fun u v ↦ if G.2.Adj u v then 1 / Real.sqrt (G.2.degree u * G.2.degree v) else 0

theorem normAdj_isHermitian : G.normAdj.IsHermitian :=
  Matrix.IsHermitian.ext fun u v ↦ by
    simp only [normAdj, star_trivial]
    by_cases h : G.2.Adj u v
    · rw [ite_eq_left h.symm, ite_eq_left h, mul_comm]
    · rw [ite_eq_right fun h' ↦ h h'.symm, ite_eq_right h]

/-- The **spectrum** of `G`: the eigenvalues of its normalized adjacency matrix, with
multiplicity, indexed by the vertices (in no particular order). -/
noncomputable def eig : Fin G.1 → ℝ := G.normAdj_isHermitian.eigenvalues

/-- The number of eigenvalues larger than `τ`. -/
noncomputable def numEigGT (τ : ℝ) : ℕ := (Finset.univ.filter fun i ↦ τ < G.eig i).card

/-- `G` is a **`λ`-one-sided expander**: at most one eigenvalue of its normalized adjacency matrix
is larger than `λ`, that is, its second largest eigenvalue `λ₂` is at most `λ` [BHSV25,
Section 3]. (Graphs with a single vertex, which have no `λ₂`, count as expanders.) -/
def IsOneSidedExpander (lam : ℝ) : Prop := G.numEigGT lam ≤ 1

/-! ### Independent sets and vertex covers -/

/-- A set of vertices given by membership bits: `v` is in it when `s[v] = true`. Bits past the
end of `s` count as `false`, and bits past `n` are ignored. -/
def vertexSet (s : List Bool) : Finset (Fin G.1) :=
  Finset.univ.filter fun v ↦ s.getD v false = true

/-- `S` is a **vertex cover**: every edge has an endpoint in `S`. -/
def IsVertexCover (S : Finset (Fin G.1)) : Prop := ∀ u v, G.2.Adj u v → u ∈ S ∨ v ∈ S

/-- The **vertex cover number**: the least size of a vertex cover. (All vertices form one, so
the infimum is a minimum.) -/
noncomputable def vertexCoverNumber : ℕ :=
  sInf {m | ∃ S : Finset (Fin G.1), G.IsVertexCover S ∧ S.card = m}

/-- `G` has an independent set of at least `m` vertices. -/
def HasIndepSet (m : ℝ) : Prop :=
  ∃ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) ∧ m ≤ I.card

/-! ### Colorings -/

/-- The color of `v` in a list `c` of colors, one per vertex, as a partial `k`-coloring: `c[v]`,
which counts as a color when it is `< k` and as "uncolored" otherwise. Vertices past the end of
`c` are uncolored. -/
def color (k : ℕ) (c : List ℕ) (v : Fin G.1) : ℕ := c.getD v k

/-- `c` is a **partial `k`-coloring**: its color classes `0, …, k - 1` are independent sets, that
is, no edge joins two vertices of the same color `< k`. -/
def IsPartialColoring (k : ℕ) (c : List ℕ) : Prop :=
  ∀ u v, G.2.Adj u v → G.color k c u < k → G.color k c u ≠ G.color k c v

/-- The number of vertices with color `a`. -/
def classSize (k : ℕ) (c : List ℕ) (a : ℕ) : ℕ :=
  (Finset.univ.filter fun v ↦ G.color k c v = a).card

/-- The number of colored vertices. -/
def numColored (k : ℕ) (c : List ℕ) : ℕ :=
  (Finset.univ.filter fun v ↦ G.color k c v < k).card

/-- `c` is a **`(k, δ)`-coloring** [BHSV25, Definition 3.1]: `k` disjoint independent sets, its
color classes, that cover at least `(1 - δ) n` vertices. A proper `k`-coloring is a
`(k, 0)`-coloring. -/
def IsColoring (k : ℕ) (δ : ℝ) (c : List ℕ) : Prop :=
  G.IsPartialColoring k c ∧ (1 - δ) * G.1 ≤ G.numColored k c

/-- `G` **has a `(k, δ)`-coloring**: `k` disjoint independent sets covering at least `(1 - δ) n`
vertices. With `δ = 0`, `G` is `k`-colorable. -/
def HasColoring (k : ℕ) (δ : ℝ) : Prop := ∃ c, G.IsColoring k δ c

/-! ### Models -/

/-- The **model** of a partition `χ` of the vertices into `k` parts [BHSV25, Definition 3.3]:
`M(χ)_ab` is the average over the vertices `x` of part `a` of `∑_{y ∈ part b} Ã_xy`, where `Ã` is
the normalized adjacency matrix. For a regular graph this is the probability that a uniformly
random edge `xy` with `χ(x) = a` has `χ(y) = b`. (Rows of empty parts are `0`.) -/
noncomputable def model {k : ℕ} (χ : Fin G.1 → Fin k) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b ↦ (∑ x ∈ Finset.univ.filter (χ · = a), ∑ y ∈ Finset.univ.filter (χ · = b),
      G.normAdj x y) / (Finset.univ.filter (χ · = a)).card

/-- `χ` is an **`(M, δ)`-coloring** of `G` [BHSV25, Definition 3.5]: its model is within `δ` of
`M` in every entry, and the edges inside its parts are covered by at most `δ n` vertices. -/
def IsMColoring {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ) (χ : Fin G.1 → Fin k) : Prop :=
  (∀ a b, |M a b - G.model χ a b| ≤ δ) ∧
    ∃ S : Finset (Fin G.1), (S.card : ℝ) ≤ δ * G.1 ∧ ∀ u v, G.2.Adj u v → χ u = χ v → u ∈ S ∨ v ∈ S

/-- `G` is **`(M, δ)`-colorable**: it has an `(M, δ)`-coloring. -/
def MColorable {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (δ : ℝ) : Prop :=
  ∃ χ : Fin G.1 → Fin k, G.IsMColoring M δ χ

/-- `χ` is **proper up to `δ n` vertices**: the edges inside its parts are covered by at most
`δ n` vertices [BHSV25, Theorem 7.9]. -/
def IsAlmostProper {k : ℕ} (χ : Fin G.1 → Fin k) (δ : ℝ) : Prop :=
  ∃ S : Finset (Fin G.1), (S.card : ℝ) ≤ δ * G.1 ∧ ∀ u v, G.2.Adj u v → χ u = χ v → u ∈ S ∨ v ∈ S

/-! ### Random planting -/

/-- The graph obtained from `G` by **planting** the coloring `χ` [BHSV25, Definition 7.11]: `G`
without the edges whose endpoints have the same color. -/
def plant {k : ℕ} (χ : Fin G.1 → Fin k) : Graph :=
  ⟨G.1, { Adj := fun u v ↦ G.2.Adj u v ∧ χ u ≠ χ v
          symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
          loopless := ⟨fun u h ↦ G.2.loopless.irrefl u h.1⟩ }⟩

open Classical in
/-- The **probability** that the graph obtained by randomly planting a `k`-coloring in `G` has the
property `E` [BHSV25, Definition 7.11]: the colors of the vertices are independent and uniform in
`{0, …, k - 1}`, so this is the fraction of the `k^n` colorings `χ` for which `G.plant χ` has the
property. -/
noncomputable def plantProb (k : ℕ) (E : Graph → Prop) : ℝ :=
  ((Finset.univ.filter fun χ : Fin G.1 → Fin k ↦ E (G.plant χ)).card : ℝ) / (k : ℝ) ^ G.1

end Graph

/-- A **model** [BHSV25, Sections 1 and 3]: a `k × k` matrix with nonnegative entries, rows summing
to `1` and zeros on the diagonal; reversible, with a positive `π` such that
`π_a M_ab = π_b M_ba`; and with second largest eigenvalue at most `0`. Reversibility makes `M`
similar to a symmetric matrix, so its characteristic polynomial has only real roots, and its
largest one is `1`; the last condition says that at most one of them, counted with multiplicity, is
positive. -/
structure IsModel {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ M a b
  rowSum : ∀ a, ∑ b, M a b = 1
  diag : ∀ a, M a a = 0
  reversible : ∃ π : Fin k → ℝ, (∀ a, 0 < π a) ∧ ∀ a b, π a * M a b = π b * M b a
  secondEig : (M.charpoly.roots.filter (0 < ·)).card ≤ 1

/-- `π` is a **stationary distribution** of `M` in detailed balance: positive, summing to `1`,
with `π_a M_ab = π_b M_ba`. For a model, it is the unique stationary distribution. -/
def IsStationary {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ) : Prop :=
  (∀ a, 0 < π a) ∧ ∑ a, π a = 1 ∧ ∀ a b, π a * M a b = π b * M b a

open Classical in
/-- The **optimal uncovered fraction** `α` of [BHSV25, Theorem 1.9]:
`α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)`, where `M^(a)` is the row `a` of `M`. It is `0`
exactly when `M` has no repeated rows. -/
noncomputable def alpha {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ) : ℝ :=
  ∑ a, min (π a) (∑ b ∈ Finset.univ.filter (fun b ↦ b ≠ a ∧ M b = M a), π b)

/-! ### Running times -/

/-- `A` **runs in time `K · m^C`**: some deterministic multitape Turing machine with a binary
alphabet and finitely many states computes `A`, relative to the encodings `encIn` and `encOut`, in
at most `⌈K (m + 1)^C⌉` steps on every input whose encoding has length `m`, using a polynomially
bounded number of work-tape cells. A running time `n^{O(1)} · g(p)` for parameters `p` is: there is
`C` such that for all values of `p` some algorithm runs in time `g(p) · m^C`. -/
def RunsInTime {α β : Type*} (A : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (K : ℝ) (C : ℕ) : Prop :=
  ∃ s : ℕ → ℕ, Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength A encIn encOut
      (fun m ↦ ⌈K * ((m : ℝ) + 1) ^ C⌉₊) s

/-- `A` **runs in time `K a · m^C` on every input `a`**, for a factor `K a` that depends on the
input: one deterministic multitape Turing machine with a binary alphabet and finitely many states
computes `A`, relative to the encodings `encIn` and `encOut`, in at most `⌈K a (m + 1)^C⌉` steps
on every input `a` whose encoding has length `m`. A running time `n^{O(1)} · g(t)` for a number
`t` read off the input, such as a count of eigenvalues, is: one algorithm runs in time `K a · m^C`
with `K a ≤ g(t)` on the inputs with count at most `t`. -/
def RunsInTimeWith {α β : Type*} (A : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (K : α → ℝ) (C : ℕ) : Prop :=
  ∃ s : α → ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A encIn encOut
    (fun a ↦ ⌈K a * (((encIn a).length : ℝ) + 1) ^ C⌉₊) s

/-! ### Hardness -/

/-- The **gap problem of `(k, δ)`-colorings** of the graphs with property `P`: the yes-instances
are the graphs with property `P` that have a `(k, δ)`-coloring, and the no-instances the graphs
that have none. Its NP-hardness (`Cslib.Complexity.PromiseProblem.NPHard`) is the NP-hardness of
finding `(k, δ)`-colorings of the graphs with property `P`: an algorithm finding
`(k, δ')`-colorings of them, for some `δ' < δ`, tells the two apart by checking its output against
a rational threshold between `δ'` and `δ`. -/
def coloringGap (P : Graph → Prop) (k : ℕ) (δ : ℝ) : PromiseProblem Graph where
  yes := {G | P G ∧ G.HasColoring k δ}
  no := {G | ¬ G.HasColoring k δ}
  disjoint := Set.disjoint_left.2 fun _ hyes hno ↦ hno hyes.2

end BHSV25
