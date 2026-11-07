module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# The semi-random planted clique model, and randomized algorithms

The definitions that the main theorem of [BKS23] is stated in (`BKS23/Challenge.lean`). Together
with what they import (Mathlib, and CSLib's multitape Turing machines), they are what a reader has
to check to know what the theorem says.

* **Encodings** of inputs and outputs as bit strings, built from those of
  `Background/Encoding.lean` (numbers, bit strings, pairs, lists). An input is a graph and the
  clique size `k`.
* **Randomized algorithms** (`BKS23.RunsInTime`): a deterministic multitape Turing machine that
  reads an input `x` and a string `r` of coin flips and halts within `O(T |x| + |(x, r)|)` steps.
  Its success probability is taken over coin strings of exactly `T |x|` flips
  (`BKS23.coinProb`), on which the bound is `O(T |x|)`.
* **The Feige–Kilian semi-random model** `FK(n, k, p)` [BKS23, Definition 1.1]: a `k`-set `S*` of
  vertices gets a clique, added to an Erdős–Rényi graph `G(n, p)`; then an adaptive adversary
  deletes any edges between `S*` and the rest and replaces the graph on the other vertices. The
  adversary (`BKS23.Adversary`) is any function of `S*` and the random graph that respects these
  rules. The paper chooses `S*` uniformly at random; here it is fixed, and the main theorem holds
  for every `S*`, which is stronger.
* **Success** (`BKS23.Succeeds`): the output is a list of vertex sets, each a `k`-clique of the
  input graph, one of them `S*`, and with at most a given number of entries. The success
  probability (`BKS23.successProb`) is over `FK(n, k, p)` with planted set `S*`, for a real `p`.

Reference: [BKS23] R.-D. Buhai, P. K. Kothari, D. Steurer, *Algorithms approaching the threshold
for semi-random planted clique*, STOC 2023, arXiv:2212.05619.
-/

@[expose] public section

namespace BKS23

open Encoding

/-! ### Inputs and outputs -/

/-- An input `(n, k, a)`: the number of vertices, the clique size, and the adjacency bits of a
graph (`BKS23.adjBits`). -/
abbrev Input := ℕ × ℕ × List Bool

def encInput : Input ↪ List Bool := encPair encNat (encPair encNat encBits)

/-- An output: a list of vertex sets, each given as a list of vertex numbers. -/
abbrev Output := List (List ℕ)

def encOutput : Output ↪ List Bool := encList (encList encNat)

open Classical in
/-- The adjacency bits of a graph on `Fin n`: one bit for each pair `i < j`, in lexicographic
order, saying whether `i` and `j` are adjacent. -/
noncomputable def adjBits {n : ℕ} (G : SimpleGraph (Fin n)) : List Bool :=
  (List.finRange n).flatMap fun i ↦
    ((List.finRange n).filter fun j ↦ i < j).map fun j ↦ decide (G.Adj i j)

/-- The input for a graph `G` on `Fin n` and clique size `k`. -/
noncomputable def input {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Input :=
  (n, k, adjBits G)

open Classical in
/-- The set of vertices of `Fin n` listed in `l` (numbers `≥ n` are ignored). -/
noncomputable def vertexSet (n : ℕ) (l : List ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ (v : ℕ) ∈ l

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: for a constant `c`, a binary multitape Turing machine with finitely
many states computes `A (x, r)` from the encoded input `x` and the coin flips `r` within
`c (T |x| + |(x, r)| + 1)` steps and work-tape cells, where `|x|` is the length of the encoded
input and `|(x, r)|` that of the encoded input with the coins.

The term `|(x, r)|` lets the machine read its whole input, coins included. On the coin strings of
length `T |x|` over which the success probability is taken (`BKS23.successProb`), the bound is
`O(T |x| + |x|)`, which is `O(T |x|)` when `T N ≥ N`. The constant `c` may depend on the
algorithm, as in "time `O(T)`".

Since the machine is given exactly `T |x|` coins and may read them all, the length of its coin
string tells it `T |x|`. A statement should therefore take `T` explicit and computable, as
`BKS23.semirandom_planted_clique` does with `T N = (N + 2)^d`; for an arbitrary `T`, the coin
string's length could carry advice. -/
def RunsInTime (A : Input × List Bool → Output) (T : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encInput encBits) encOutput
    (fun xr ↦ c * (T (encInput xr.1).length + (encPair encInput encBits xr).length + 1))
    (fun xr ↦ c * (T (encInput xr.1).length + (encPair encInput encBits xr).length + 1))

open Classical in
/-- The probability that `P r` holds for a uniformly random string `r` of `m` coin flips. -/
noncomputable def coinProb (m : ℕ) (P : List Bool → Prop) : ℝ :=
  ((Finset.univ.filter fun r : Fin m → Bool ↦ P (List.ofFn r)).card : ℝ) / 2 ^ m

/-! ### The Feige–Kilian semi-random planted clique model -/

open Classical in
/-- The probability of the graph `R` under the Erdős–Rényi distribution `G(n, p)`, which includes
each of the `n choose 2` possible edges independently with probability `p`. -/
noncomputable def erdosRenyiProb {n : ℕ} (p : ℝ) (R : SimpleGraph (Fin n)) : ℝ :=
  p ^ R.edgeFinset.card * (1 - p) ^ (n.choose 2 - R.edgeFinset.card)

/-- An adversary in the semi-random model `FK(n, k, p)` [BKS23, Definition 1.1]. From the planted
set `S` and the random graph `R`, it produces the graph `graph S R` given to the algorithm, which
must contain all edges inside `S`, and may contain an edge between `S` and the other vertices only
if `R` does. Inside the other vertices it is arbitrary. Since `graph` is any function of `S` and
`R`, the adversary is adaptive. -/
structure Adversary (n : ℕ) where
  /-- The graph given to the algorithm. -/
  graph : Finset (Fin n) → SimpleGraph (Fin n) → SimpleGraph (Fin n)
  /-- The planted set is a clique. -/
  clique : ∀ S R, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (graph S R).Adj u v
  /-- Edges between the planted set and the other vertices are a subset of the random ones. -/
  cut : ∀ S R u v, u ∈ S → v ∉ S → (graph S R).Adj u v → R.Adj u v

/-- The algorithm succeeds on the graph `G` with planted set `S` if its output is a list of at most
`bound` vertex sets, each a `k`-clique of `G`, one of them `S`. -/
def Succeeds {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (bound : ℝ)
    (out : Output) : Prop :=
  S ∈ out.map (vertexSet n) ∧ (∀ l ∈ out, G.IsNClique k (vertexSet n l)) ∧
    (out.length : ℝ) ≤ bound

open Classical in
/-- The probability that the algorithm `A`, running in time `T`, succeeds with list bound
`bound` on `FK(n, k, p)` with planted set `S` against the adversary `Adv`: over the random graph
`R ∼ G(n, p)` and the coin flips.

In [BKS23, Definition 1.1] the planted set is a uniformly random `k`-set; the average of this
probability over `S` is that probability, so a lower bound for every `S` implies the paper's. -/
noncomputable def successProb (n k : ℕ) (p : ℝ) (S : Finset (Fin n)) (Adv : Adversary n)
    (A : Input × List Bool → Output) (T : ℕ → ℕ) (bound : ℝ) : ℝ :=
  ∑ R : SimpleGraph (Fin n), erdosRenyiProb p R *
    coinProb (T (encInput (input (Adv.graph S R) k)).length) fun r ↦
      Succeeds k (Adv.graph S R) S bound (A (input (Adv.graph S R) k, r))

end BKS23
