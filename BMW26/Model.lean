module

public import Background.Encoding
public import Background.SumOfSquares.Proof
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# The percolated hypercube, and randomized algorithms

The definitions that the results of [BMW26] are stated in (`BMW26/Challenge.lean`). Together
with what they import (Mathlib, CSLib's multitape Turing machines, and the sum-of-squares proofs of
`Background/SumOfSquares/Proof.lean`), they are what a reader has to check to know what the
results say.

* **The hypercube** `Q_d` (`BMW26.cube`): its vertices are the `2^d` vectors of `d` bits
  (`BMW26.Cube`), which stand for `{±1}^d`, and two vectors are adjacent when they differ in exactly
  one coordinate.
* **The percolated hypercube** `Q_d(p)` (`BMW26.percolationProb`): the random subgraph of `Q_d`
  that keeps each edge independently with probability `p`.
* **Renaming** (`BMW26.Renaming`, `BMW26.observed`): the vertices of the sample are renamed
  `0, …, 2^d - 1` by a bijection `z`, which gives each vertex `v` its hidden vector `z v`. The
  algorithm sees only the renamed graph, encoded by its number of vertices and its adjacency table
  (`BMW26.encGraph`).
* **Recovery** (`BMW26.Recovers`): the algorithm outputs one vector of `d` bits per vertex; it
  recovers the hidden vectors with at most `m` errors if, after one automorphism of `Q_d`
  (`BMW26.cubeAut`: a permutation of the coordinates and a sign flip of each), its vectors equal
  the hidden ones on all but at most `m` vertices.
* **Randomized algorithms** (`BMW26.RunsInTime`): a deterministic multitape Turing machine that
  reads an input `x` and a string `r` of coin flips and halts within `O(T |x| + |(x, r)|)` steps.
  Probabilities are over coin strings of exactly `T |x|` flips (`BMW26.coinProb`), as in [BKS23]
  and [BBKS24] in this repository.
* **Success** (`BMW26.successProb`): the probability, over `Q_d(p)` and the coins, that the
  algorithm recovers the hidden vectors with at most `m` errors, when the renaming is any function
  of the sample.
* **The sum-of-squares FKN theorem** (`BMW26.fknSystem`): variables `f(x)`, `x ∈ {±1}^d`, and
  `δ` (`BMW26.FKNVar`), the Fourier coefficients `⟨f, χᵢ⟩` as linear polynomials
  (`BMW26.fourierCoeff`), and the constraints of [BMW26, Theorem 4.1].
* **Laplacians** (`BMW26.lapForm`): the quadratic form `gᵀ L_H g = ∑_{xy ∈ E(H)} (g x - g y)²` of a
  graph on the hypercube; and the probability of an event under `Q_d(p)` (`BMW26.percProb`).

Reference: [BMW26] R.-D. Buhai, D. Mazzali, W. Wrzos-Kaminska, *Efficient recovery of latent
coordinate structure from sparse observations of the hypercube*, arXiv:2610.11741.
-/

@[expose] public section

namespace BMW26

open Encoding

/-! ### The hypercube and its percolation -/

/-- The sign of a bit, `(-1)^b`: `false ↦ 1`, `true ↦ -1`. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The vertices of the hypercube `Q_d`: the `2^d` vectors of `d` bits, standing for the vectors
of `{±1}^d`. -/
abbrev Cube (d : ℕ) := Fin d → Bool

/-- The **hypercube** `Q_d`: two vectors are adjacent when they differ in exactly one
coordinate. -/
def cube (d : ℕ) : SimpleGraph (Cube d) where
  Adj x y := hammingDist x y = 1
  symm := ⟨fun x y h ↦ by rwa [hammingDist_comm]⟩
  loopless := ⟨fun x h ↦ by simp at h⟩

open Classical in
/-- The probability of the graph `H` under the **percolated hypercube** `Q_d(p)`, which keeps each
edge of `Q_d` independently with probability `p`: `p^|E(H)| (1 - p)^(|E(Q_d)| - |E(H)|)` if `H` is
a subgraph of `Q_d`, and `0` otherwise. -/
noncomputable def percolationProb {d : ℕ} (p : ℝ) (H : SimpleGraph (Cube d)) : ℝ :=
  if H ≤ cube d then
    p ^ H.edgeFinset.card * (1 - p) ^ ((cube d).edgeFinset.card - H.edgeFinset.card)
  else 0

/-! ### Graphs given to the algorithm -/

/-- A **graph** `⟨n, G⟩`: a simple graph on the vertices `0, …, n - 1`. -/
abbrev Graph := (n : ℕ) × SimpleGraph (Fin n)

open Classical in
/-- The adjacency table of a graph: the `n²` bits `[u ~ v]`, row by row. -/
noncomputable def adjTable (G : Graph) : List Bool :=
  List.ofFn fun k : Fin (G.1 * G.1) ↦
    decide (G.2.Adj (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

theorem adjTable_injective {n : ℕ} {G G' : SimpleGraph (Fin n)}
    (h : adjTable ⟨n, G⟩ = adjTable ⟨n, G'⟩) : G = G' := by
  classical
  have h' := List.ofFn_injective h
  ext u v
  simpa using congrFun h' (finProdFinEquiv (u, v))

/-- A graph is encoded by its number of vertices and its adjacency table. -/
noncomputable def encGraph : Graph ↪ List Bool :=
  ⟨fun G ↦ encPair encNat encBits (G.1, adjTable G), by
    rintro ⟨n, G⟩ ⟨n', G'⟩ h
    obtain ⟨rfl, h2⟩ := Prod.ext_iff.1 ((encPair encNat encBits).injective h)
    rw [adjTable_injective h2]⟩

/-- A **renaming** of the vertices of `Q_d`: a bijection `z` from the names `0, …, 2^d - 1` to the
hypercube, which gives each vertex `v` its hidden vector `z v`. -/
abbrev Renaming (d : ℕ) := Fin (2 ^ d) ≃ Cube d

/-- The graph the algorithm observes: the graph `H` on the hypercube with its vertices renamed by
`z`. The vertices `u` and `v` are adjacent when `z u` and `z v` are adjacent in `H`. -/
def observed {d : ℕ} (H : SimpleGraph (Cube d)) (z : Renaming d) : Graph :=
  ⟨2 ^ d, H.comap z⟩

/-! ### Outputs and recovery -/

/-- An output: the recovered vectors of the vertices `0, 1, …`, each a list of bits. -/
abbrev Output := List (List Bool)

/-- Outputs are encoded as lists of bit strings. -/
def encOutput : Output ↪ List Bool := encList encBits

/-- The vector that the output `out` assigns to the vertex `v`, read as a vector of `d` bits: the
`v`-th list of `out`, where missing lists and missing bits read as `false`. -/
def outVec (d : ℕ) (out : Output) (v : ℕ) : Cube d := fun i ↦ (out.getD v []).getD i false

/-- The automorphism of `Q_d` that permutes the coordinates by `π` and then flips the coordinates
`i` with `s i = true`: `x ↦ (s i xor x (π i))ᵢ`. These are all the automorphisms of `Q_d`. -/
def cubeAut {d : ℕ} (π : Equiv.Perm (Fin d)) (s : Fin d → Bool) (x : Cube d) : Cube d :=
  fun i ↦ xor (s i) (x (π i))

open Classical in
/-- The output `out` **recovers** the hidden vectors of the renaming `z` with at most `m` errors:
for one automorphism of `Q_d`, applied to all recovered vectors, the recovered vector of `v`
equals its hidden vector `z v` for all but at most `m` vertices `v`. -/
def Recovers {d : ℕ} (z : Renaming d) (m : ℝ) (out : Output) : Prop :=
  ∃ (π : Equiv.Perm (Fin d)) (s : Fin d → Bool),
    ((Finset.univ.filter fun v : Fin (2 ^ d) ↦ cubeAut π s (outVec d out v) ≠ z v).card : ℝ) ≤ m

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: for a constant `c`, a binary multitape Turing machine with finitely
many states computes `A (x, r)` from the encoded graph `x` and the coin flips `r` within
`c (T |x| + |(x, r)| + 1)` steps and work-tape cells, where `|x|` is the length of the encoded
graph and `|(x, r)|` that of the encoded graph with the coins.

The term `|(x, r)|` lets the machine read its whole input, coins included. On the coin strings of
length `T |x|` over which the success probability is taken (`BMW26.successProb`), the bound is
`O(T |x| + |x|)`, which is `O(T |x|)` when `T N ≥ N`.

Since the machine is given exactly `T |x|` coins and may read them all, the length of its coin
string tells it `T |x|`. A statement should therefore take `T` explicit and computable, as
`BMW26.hypercube_recovery` does with `T N = (N + 2)^k`; for an arbitrary `T`, the coin string's
length could carry advice. -/
def RunsInTime (A : Graph × List Bool → Output) (T : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encGraph encBits) encOutput
    (fun xr ↦ c * (T (encGraph xr.1).length + (encPair encGraph encBits xr).length + 1))
    (fun xr ↦ c * (T (encGraph xr.1).length + (encPair encGraph encBits xr).length + 1))

open Classical in
/-- The probability that `P r` holds for a uniformly random string `r` of `m` coin flips. -/
noncomputable def coinProb (m : ℕ) (P : List Bool → Prop) : ℝ :=
  ((Finset.univ.filter fun r : Fin m → Bool ↦ P (List.ofFn r)).card : ℝ) / 2 ^ m

/-- The probability that the algorithm `A`, running in time `T`, recovers the hidden vectors with
at most `m` errors: over the sample `H ∼ Q_d(p)` and the coin flips, when `H` is renamed by
`ren H`. The renaming `ren` may be any function of the sample. The algorithm is given only the
renamed graph, not `p`, the renaming or the hidden vectors. -/
noncomputable def successProb (d : ℕ) (p : ℝ) (ren : SimpleGraph (Cube d) → Renaming d)
    (A : Graph × List Bool → Output) (T : ℕ → ℕ) (m : ℝ) : ℝ :=
  ∑ H : SimpleGraph (Cube d), percolationProb p H *
    coinProb (T (encGraph (observed H (ren H))).length) fun r ↦
      Recovers (ren H) m (A (observed H (ren H), r))

/-! ### The sum-of-squares FKN theorem -/

/-- The variables of [BMW26, Theorem 4.1]: the values `f(x)` of a function on the hypercube
(`some x`, for `x ∈ {±1}^d`), and `δ` (`none`). -/
abbrev FKNVar (d : ℕ) := Option (Cube d)

open MvPolynomial in
/-- The Fourier coefficient `⟨f, χᵢ⟩ = 2^{-d} ∑ₓ f(x) (-1)^{xᵢ}` on the dictator `χᵢ`, as a linear
polynomial in the variables `f(x)`. -/
noncomputable def fourierCoeff {d : ℕ} (i : Fin d) : MvPolynomial (FKNVar d) ℝ :=
  C (1 / 2 ^ d) * ∑ x : Cube d, C (sgn (x i)) * X (some x)

open MvPolynomial in
/-- The constraints of [BMW26, Theorem 4.1], with `δ` replaced by a polynomial `q`:
`∑ᵢ ⟨f, χᵢ⟩² ≥ 1 - q`, `q ≥ 0`, and `f(x)² = 1` for every `x` (as `f(x)² - 1 ≥ 0` and
`1 - f(x)² ≥ 0`). With `q = X none` this is the paper's system in the variables `f` and `δ`. -/
noncomputable def fknSystem {d : ℕ} (q : MvPolynomial (FKNVar d) ℝ) :
    SoS.System (FKNVar d) ℝ :=
  (∑ i, fourierCoeff i ^ 2 - (1 - q)) :: q ::
    (Finset.univ.toList.flatMap fun x : Cube d ↦ [X (some x) ^ 2 - 1, 1 - X (some x) ^ 2])

/-! ### Laplacians and spectral concentration -/

open Classical in
/-- The **Laplacian quadratic form** of a graph `H` on the hypercube:
`gᵀ L_H g = ∑_{xy ∈ E(H)} (g x - g y)²`, each edge counted once (the sum over ordered pairs of
adjacent vertices, halved). For `H = Q_d` it is the form of the hypercube's Laplacian `L`. -/
noncomputable def lapForm {d : ℕ} (H : SimpleGraph (Cube d)) (g : Cube d → ℝ) : ℝ :=
  (∑ x, ∑ y, if H.Adj x y then (g x - g y) ^ 2 else 0) / 2

open Classical in
/-- The probability that a sample of the percolated hypercube `Q_d(p)` has the property `P`. -/
noncomputable def percProb (d : ℕ) (p : ℝ) (P : SimpleGraph (Cube d) → Prop) : ℝ :=
  ∑ H : SimpleGraph (Cube d), if P H then percolationProb p H else 0

end BMW26
