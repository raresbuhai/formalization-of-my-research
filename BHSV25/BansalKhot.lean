module

public import BHSV25.Model
public import BHSV25.BK.Main
public import BHSV25.UG.Bridge

/-!
# The hardness of almost-bipartite independent set

[BHSV25, Fact 8.1], the starting point of every hardness reduction in the paper: Bansal and Khot
proved, assuming the Unique Games Conjecture, that for all small `ε, γ > 0` it is NP-hard to tell
graphs with two disjoint independent sets of `(1/2 - ε) n` vertices each from graphs with no
independent set of `γ n` vertices; Bafna, Hsieh and Kothari note that the graphs can have maximum
degree `o(n)`.

This file states it as `BHSV25.BansalKhot`, for graphs of maximum degree at most `η n` for every
`η > 0`, and proves it from the Unique Games Conjecture on graphs (`UniqueGames.KhotUGC`;
`BHSV25.bansalKhot`): the double cover and a regularization (`BHSV25/UG/`) give hardness on
left-regular bipartite instances whose parallel constraints agree, from which the reduction of
`BHSV25/BK/` starts (`BHSV25/BK/README.md` describes it). The hardness theorems of
`Challenge.lean` assume the conjecture itself, and their proofs go through this statement.

References:
* N. Bansal, S. Khot, *Optimal long code test with one free bit*, FOCS 2009.
* M. Bafna, J.-T. Hsieh, P. K. Kothari, *Rounding large independent sets on expanders*, STOC 2025.
-/

@[expose] public section

namespace BHSV25

open Cslib.Complexity

open Classical in
/-- Every vertex has at most `η n` neighbours. -/
def Graph.MaxDegreeLE (G : Graph) (η : ℝ) : Prop := ∀ v, (G.2.degree v : ℝ) ≤ η * G.1

/-- The **gap problem of Bansal and Khot** with parameters `ε`, `γ` and `η`, on graphs of maximum
degree at most `η n`: the yes-instances have two disjoint independent sets of at least
`(1/2 - ε) n` vertices each, and the no-instances have no independent set of `γ n` vertices. (The
no-instances also ask `γ ≤ 1/2 - ε`, so that the two sides are disjoint.) -/
noncomputable def bkGap (ε γ η : ℝ) : PromiseProblem Graph where
  yes := {G | G.MaxDegreeLE η ∧ ∃ I J : Finset (Fin G.1), Disjoint I J ∧
    G.2.IsIndepSet (I : Set (Fin G.1)) ∧ G.2.IsIndepSet (J : Set (Fin G.1)) ∧
    (1 / 2 - ε) * G.1 ≤ I.card ∧ (1 / 2 - ε) * G.1 ≤ J.card}
  no := {G | G.MaxDegreeLE η ∧ γ ≤ 1 / 2 - ε ∧
    ∀ I : Finset (Fin G.1), G.2.IsIndepSet (I : Set (Fin G.1)) → (I.card : ℝ) < γ * G.1}
  disjoint := Set.disjoint_left.2 fun G hyes hno ↦ by
    obtain ⟨-, I, -, -, hI, -, hIc, -⟩ := hyes
    obtain ⟨-, hγ, hno⟩ := hno
    have hn : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    linarith [hno I hI, mul_le_mul_of_nonneg_right hγ hn]

/-- **[BHSV25, Fact 8.1]**: for all small enough `ε, γ > 0` and every `η > 0`, the gap problem
`bkGap ε γ η` is NP-hard, under deterministic polynomial-time reductions from every problem in
`NP`. -/
def BansalKhot : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε γ η : ℝ, 0 < ε → ε ≤ ε₀ → 0 < γ → γ ≤ ε₀ → 0 < η →
    PromiseProblem.NPHard encGraph (bkGap ε γ η)

/-- **Bansal and Khot's theorem**: the Unique Games Conjecture implies [BHSV25, Fact 8.1]. -/
theorem bansalKhot (hUGC : UniqueGames.KhotUGC) : BansalKhot :=
  BK.bansalKhot_of (UG.lrHard_of_khotUGC hUGC) BK.itAintOver

end BHSV25
