module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Basic

/-!
# The semirandom planted clique model, and randomized algorithms

The definitions that the main theorem of [BBKS24] is stated in (`BBKS24/Challenge.lean`).
Together with what they import (Mathlib, and CSLib's multitape Turing machines), they are what a
reader has to check to know what the theorem says.

* **Encodings** of inputs and outputs as bit strings, built from those of
  `Background/Encoding.lean` (numbers, bit strings, pairs, lists). An input is a graph and the
  clique size `k` (`BBKS24.Input`), as in [BKS23]; the edge probability `p` is not part of it.
* **Randomized algorithms** (`BBKS24.RunsInTime`): a deterministic multitape Turing machine that
  reads an input `x` and a string `r` of coin flips and halts within `O(T |x| + |(x, r)|)` steps.
  Its success probability is taken over coin strings of exactly `T |x|` flips
  (`BBKS24.coinProb`), on which the bound is `O(T |x|)` when `T N ≥ N`.
* **The semirandom model** `SRPC(n, k, p)` [BBKS24, Definition 1.1], from [CSV17]: a `k`-clique
  is planted on an arbitrary set `S*` of vertices, each edge between `S*` and the other vertices is
  present independently with probability `p`, and an adaptive adversary chooses the graph on the
  other vertices. The adversary (`BBKS24.Adversary`) is any function of `S*` and the random graph
  that respects these rules. Unlike the model of [BKS23], it may not delete the random edges
  between `S*` and the other vertices. (The definition of [BKS23] also draws `S*` at random, but
  its formal statement, like this one, holds for every `S*`.)
* **Success** (`BBKS24.Succeeds`): the output is a list of vertex sets, each a `k`-clique of the
  input graph, one of them `S*`, and with at most a given number of entries. The success
  probability (`BBKS24.successProb`) is over the random edges and the coins, for a fixed `S*`
  and a real `p`.

Reference: [BBKS24] J. Błasiok, R.-D. Buhai, P. K. Kothari, D. Steurer, *Semirandom planted clique
and the restricted isometry property*, FOCS 2024, arXiv:2404.14159. [CSV17] M. Charikar,
J. Steinhardt, G. Valiant, *Learning from untrusted data*, STOC 2017.
-/

@[expose] public section

namespace BBKS24

open Encoding

/-! ### Inputs and outputs -/

/-- An input `(n, k, a)`: the number of vertices, the clique size, and the adjacency bits of a
graph (`BBKS24.adjBits`). -/
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
length `T |x|` over which the success probability is taken (`BBKS24.successProb`), the bound is
`O(T |x| + |x|)`, which is `O(T |x|)` when `T N ≥ N`. The constant `c` may depend on the
algorithm, as in "time `O(T)`".

Since the machine is given exactly `T |x|` coins and may read them all, the length of its coin
string tells it `T |x|`. A statement should therefore take `T` explicit and computable, as
`BBKS24.semirandom_planted_clique` does with `T N = (N + 2)^d`; for an arbitrary `T`, the coin
string's length could carry advice. -/
def RunsInTime (A : Input × List Bool → Output) (T : ℕ → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encInput encBits) encOutput
    (fun xr ↦ c * (T (encInput xr.1).length + (encPair encInput encBits xr).length + 1))
    (fun xr ↦ c * (T (encInput xr.1).length + (encPair encInput encBits xr).length + 1))

open Classical in
/-- The probability that `P r` holds for a uniformly random string `r` of `m` coin flips. -/
noncomputable def coinProb (m : ℕ) (P : List Bool → Prop) : ℝ :=
  ((Finset.univ.filter fun r : Fin m → Bool ↦ P (List.ofFn r)).card : ℝ) / 2 ^ m

/-! ### The semirandom planted clique model -/

open Classical in
/-- The probability of the graph `R` under the Erdős–Rényi distribution `G(n, p)`, which includes
each of the `n choose 2` possible edges independently with probability `p`. -/
noncomputable def erdosRenyiProb {n : ℕ} (p : ℝ) (R : SimpleGraph (Fin n)) : ℝ :=
  p ^ R.edgeFinset.card * (1 - p) ^ (n.choose 2 - R.edgeFinset.card)

/-- An adversary in the semirandom model `SRPC(n, k, p)` [BBKS24, Definition 1.1]. From the
planted set `S` and the random graph `R`, it produces the graph `graph S R` given to the
algorithm, which must contain all edges inside `S`, and must contain an edge between `S` and the
other vertices exactly when `R` does. Inside the other vertices it is arbitrary. Since `graph` is
any function of `S` and `R`, the adversary is adaptive. Only the edges of `R` between `S` and the
other vertices matter: they are the random edges of the model. -/
structure Adversary (n : ℕ) where
  /-- The graph given to the algorithm. -/
  graph : Finset (Fin n) → SimpleGraph (Fin n) → SimpleGraph (Fin n)
  /-- The planted set is a clique. -/
  clique : ∀ S R, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (graph S R).Adj u v
  /-- Edges between the planted set and the other vertices are exactly the random ones. -/
  cut : ∀ S R u v, u ∈ S → v ∉ S → ((graph S R).Adj u v ↔ R.Adj u v)

/-- The algorithm succeeds on the graph `G` with planted set `S` if its output is a list of at most
`bound` vertex sets, each a `k`-clique of `G`, one of them `S`. -/
def Succeeds {n : ℕ} (k : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (bound : ℝ)
    (out : Output) : Prop :=
  S ∈ out.map (vertexSet n) ∧ (∀ l ∈ out, G.IsNClique k (vertexSet n l)) ∧
    (out.length : ℝ) ≤ bound

open Classical in
/-- The probability that the algorithm `A`, running in time `T`, succeeds with list bound
`bound` on `SRPC(n, k, p)` with planted set `S` against the adversary `Adv`: over the random graph
`R ∼ G(n, p)` and the coin flips. The algorithm is given `n`, `k` and the graph, not `p`. -/
noncomputable def successProb (n k : ℕ) (p : ℝ) (S : Finset (Fin n)) (Adv : Adversary n)
    (A : Input × List Bool → Output) (T : ℕ → ℕ) (bound : ℝ) : ℝ :=
  ∑ R : SimpleGraph (Fin n), erdosRenyiProb p R *
    coinProb (T (encInput (input (Adv.graph S R) k)).length) fun r ↦
      Succeeds k (Adv.graph S R) S bound (A (input (Adv.graph S R) k, r))

end BBKS24
