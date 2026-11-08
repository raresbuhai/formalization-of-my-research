module

public import Background.Encoding
public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Unique Games and the Unique Games Conjecture

Bipartite Unique Games instances, their value, their gap problems, and the Unique Games
Conjecture [Khot 2002] in the form of [BGHKLMM26, Conjecture 4.10], for hardness results that
assume it.

* **Instances** (`UniqueGames.UGInstance`): `m` left vertices, `n` right vertices, `R` labels and
  a list of constraints, each a permutation of the labels between a left and a right vertex
  (`UniqueGames.UGValid`). Simple instances have no two constraints on the same pair
  (`UniqueGames.UGSimple`), and bi-regular ones are regular on both sides
  (`UniqueGames.BiRegular`).
* **The value** (`UniqueGames.ugValue`): the largest fraction of constraints satisfied by a
  labeling.
* **The Unique Games Conjecture** (`UniqueGames.UGC`): there is `ε₀ ∈ (0, 1/2]` such that for every
  `ε ∈ (0, ε₀]` there is a number `R` of labels for which telling simple bi-regular instances with
  `R` labels and value at least `1 - ε` from those of value at most `ε` is NP-hard (complexitylib's
  `Cslib.Complexity.PromiseProblem.NPHard`, under deterministic polynomial-time reductions from
  every problem in `NP`). It implies Khot's form, the hardness of telling value `1 - η` from `ζ`
  for all `η, ζ > 0` with enough labels (take `ε = min(η, ζ, ε₀)`), on simple bi-regular
  instances, which makes it formally stronger than Khot's form.

Reference: [BGHKLMM26] R.-D. Buhai, S. Ghoshal, N. Huang, P. K. Kothari, E. Lee,
K. Makarychev, Y. Makarychev, *Optimal Algorithms and Hardness for Max-Cut in Bounded Degree
Graphs*, SODA 2027, arXiv:2610.27216.
-/

@[expose] public section

namespace UniqueGames

open Encoding

/-- A Unique Games constraint `((u, v), π)` between the left vertex `u` and the right vertex `v`:
the labels must satisfy `σ(u) = π(σ(v))`, where the permutation `π` of the labels `0, …, R - 1` is
given by its table `[π(0), …, π(R - 1)]`. -/
abbrev UGConstraint := (ℕ × ℕ) × List ℕ

/-- A **Unique Games instance** `(m, n, R, cs)` on a bipartite graph: `m` left vertices, `n` right
vertices, `R` labels, and a list `cs` of constraints, each between a left and a right vertex. -/
abbrev UGInstance := ℕ × ℕ × ℕ × List UGConstraint

def encUG : UGInstance ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat
    (encList (encPair (encPair encNat encNat) (encList encNat)))))

/-- A **valid** instance: every constraint joins a left vertex `u < m` and a right vertex `v < n`,
and its table lists each label `0, …, R - 1` exactly once. -/
def UGValid (G : UGInstance) : Prop :=
  ∀ c ∈ G.2.2.2, c.1.1 < G.1 ∧ c.1.2 < G.2.1 ∧ c.2.length = G.2.2.1 ∧ c.2.Nodup ∧
    ∀ a ∈ c.2, a < G.2.2.1

/-- No two constraints join the same two vertices: the constraint graph is simple. -/
def UGSimple (G : UGInstance) : Prop := (G.2.2.2.map Prod.fst).Nodup

/-- **Bi-regular**: every left vertex lies on the same number of constraints, and so does every
right vertex. -/
def BiRegular (G : UGInstance) : Prop :=
  (∃ D : ℕ, ∀ u < G.1, (G.2.2.2.filter fun c ↦ c.1.1 = u).length = D) ∧
    ∃ D : ℕ, ∀ v < G.2.1, (G.2.2.2.filter fun c ↦ c.1.2 = v).length = D

/-- The number of constraints satisfied by the labeling `σ` of the left vertices and `τ` of the
right vertices. -/
def ugSatisfied (G : UGInstance) (σ τ : ℕ → ℕ) : ℕ :=
  (G.2.2.2.filter fun c ↦ σ c.1.1 = c.2.getD (τ c.1.2) 0).length

/-- The **value** of a Unique Games instance: the largest fraction of its constraints satisfied by
a labeling of its vertices with labels `0, …, R - 1`, and `0` for an instance with no
constraints. -/
noncomputable def ugValue (G : UGInstance) : ℝ :=
  ⨆ (σ : Fin G.1 → Fin G.2.2.1) (τ : Fin G.2.1 → Fin G.2.2.1),
    (ugSatisfied G (fun u ↦ if h : u < G.1 then σ ⟨u, h⟩ else 0)
      (fun v ↦ if h : v < G.2.1 then τ ⟨v, h⟩ else 0) : ℝ) / G.2.2.2.length

open Cslib.Complexity in
/-- The **gap problem** of Unique Games with `R` labels: the yes-instances have value at least
`1 - ε`, the no-instances at most `δ`, both restricted to valid, simple, bi-regular instances with
`R` labels. -/
noncomputable def ugGap (R : ℕ) (ε δ : ℝ) : PromiseProblem UGInstance :=
  (PromiseProblem.gapMax ugValue (fun _ ↦ 1 - ε) (fun _ ↦ δ)).restrict
    {G | UGValid G ∧ G.2.2.1 = R ∧ UGSimple G ∧ BiRegular G}

open Cslib.Complexity in
/-- The **Unique Games Conjecture** [Khot 2002], in the form of [BGHKLMM26, Conjecture 4.10]: there
is `ε₀ ∈ (0, 1/2]` such that for every `ε ∈ (0, ε₀]` there is a number `R` of labels for which it
is NP-hard to tell simple bi-regular Unique Games instances with `R` labels and value at least
`1 - ε` from those with value at most `ε`. NP-hardness is under deterministic polynomial-time
reductions from every problem in `NP`. -/
def UGC : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ R : ℕ, PromiseProblem.NPHard encUG (ugGap R ε ε)

end UniqueGames
