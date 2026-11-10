module

public import BHSV25.Model
public import BHSV25.Spectral.ThresholdRank
public import BHSV25.Alg.VertexCover
public import BHSV25.Alg.IndepSetFull
public import BHSV25.Alg.ExpanderFull
public import BHSV25.Alg.ColoringFull
public import BHSV25.Alg.VertexCoverFull
public import BHSV25.Alg.ColoringOrFull
public import BHSV25.Alg.Coloring
public import BHSV25.Hard.Corollaries
public import BHSV25.Hard.LowRank

/-!
# Main results: proofs

Restates the theorems of `Challenge.lean` with the same names and statements, and proves them from
the development in this folder. Don't import `Challenge` here: the names would clash.

All the statements are proved: the algorithms in their full versions, with their errors and
running times, the hardness results and Theorem 1.7.
-/

public section

namespace BHSV25

open Filter Topology Turing.MultiTapeTM UniqueGames

/-! ### Independent sets and vertex covers -/

/-- **Theorem 7.20** of [BHSV25]: for every `c > 0`, `λ ∈ (0, 1)`, `t` and `γ ∈ (0, 1/4)`, an
algorithm running in time `poly(n) · (γ / (1 - λ))^{-O(t)}` that, on regular graphs with at most
`t` eigenvalues at most `-λ` and an independent set of `(1/2 - γ) n` vertices, outputs an
independent set of at least `(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices. -/
theorem independentSet_bottomRank :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ t : ℕ,
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool,
          RunsInTime A encGraph Encoding.encBits
            (((D : ℝ) * (1 + (1 - lam) / γ)) ^ (D * (t + 1))) C ∧
          ∀ G : Graph, G.IsRegular → (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ (G.vertexSet (A G)).card) :=
  Alg.indepSet_bottomRank

/-- **Theorem 1.1** of [BHSV25], full version (Corollary 7.21): for every `c > 0`,
`λ ∈ (0, 1/2)`, `t` and `γ ∈ (0, 1/4)`, an algorithm running in time
`poly(n) · (γ / (1 - √(2λ)))^{-O(t/λ²)}` that, on regular graphs with at most `t` eigenvalues
larger than `λ` (`λ`-one-sided expanders for `t = 1`) and an independent set of `(1/2 - γ) n`
vertices, outputs an independent set of at least `(1/2 - γ - (4 + c) γ / (1 - √(2λ))) n`
vertices. -/
theorem independentSet_approximation :
    ∃ C : ℕ, ∀ c : ℝ, 0 < c → ∃ D : ℕ, ∀ lam : ℝ, 0 < lam → lam < 1 / 2 → ∀ t : ℕ,
      ∀ γ : ℝ, 0 < γ → γ < 1 / 4 →
        ∃ A : Graph → List Bool,
          RunsInTime A encGraph Encoding.encBits
            (((D : ℝ) * (1 + (1 - Real.sqrt (2 * lam)) / γ)) ^
              (D * (⌈(t : ℝ) / lam ^ 2⌉₊ + 1))) C ∧
          ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            (G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - γ - (4 + c) * γ / (1 - Real.sqrt (2 * lam))) * G.1 ≤
                (G.vertexSet (A G)).card) :=
  Alg.indepSet_topRank

/-- **Corollary 1.2** of [BHSV25]: for every `ε > 0`, a `(5/3 + ε)`-approximation algorithm for
vertex cover on regular `λ₀`-one-sided expanders, for some `λ₀ > 0`, running in time `K · m^C`
with `C` independent of `ε`. -/
theorem vertexCover_approximation :
    ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∃ K : ℝ,
      ∃ A : Graph → List Bool, RunsInTime A encGraph Encoding.encBits K C ∧
        ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam₀ →
          G.IsVertexCover (G.vertexSet (A G)) ∧
          ((G.vertexSet (A G)).card : ℝ) ≤ (5 / 3 + ε) * G.vertexCoverNumber :=
  Alg.vertexCover_approximation

/-! ### Algorithms for 3-colorable one-sided expanders -/

/-- **Theorem 1.3** of [BHSV25], full version (Theorem 7.9): for `δ ∈ [0, c₀)` and
`γ, λ ∈ (0, c₀)`, an algorithm running in time `n^{O(1)} · O_{δ,γ,λ}(1)` that, on regular
`λ`-one-sided expanders with a partition into `3` parts of at most `(1/2 - γ) n` vertices each
whose inside edges are covered by `δ n` vertices, outputs `3` independent sets covering all but
`O(λ / γ⁸ + δ / (λ γ⁸)) n` vertices. -/
theorem threeColoring_balanced :
    ∃ C : ℕ, ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ γ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < γ → γ < c₀ →
      0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
            (∃ χ : Fin G.1 → Fin 3, G.IsAlmostProper χ δ ∧
              ∀ a, ((Finset.univ.filter (χ · = a)).card : ℝ) ≤ (1 / 2 - γ) * G.1) →
            G.IsColoring 3 (B * (lam + δ / lam) / γ ^ 8) (A G) :=
  Alg.threeColoring_balanced

/-- **Corollary 1.4** of [BHSV25]: for every `λ > 0`, an algorithm running in time `K · m^C`, with
`C` independent of `λ`, that, on regular `λ`-one-sided expanders with `3` independent sets
covering all but `λ n` vertices, outputs `3` independent sets of which one has at least
`(1/2 - f λ) n` vertices or which cover all but `f λ · n` vertices, where `f λ → 0` as
`λ → 0`. -/
theorem threeColoring_independentSet_or_coloring :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧ ∃ C : ℕ,
      ∀ lam : ℝ, 0 < lam → ∃ K : ℝ,
        ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 lam →
            G.IsPartialColoring 3 (A G) ∧
            ((∃ a < 3, (1 / 2 - f lam) * G.1 ≤ G.classSize 3 (A G) a) ∨
              (1 - f lam) * G.1 ≤ G.numColored 3 (A G)) :=
  Alg.threeColoring_independentSet_or_coloring

/-! ### Hardness for almost 3-colorable graphs -/

/-- **Theorem 1.5** of [BHSV25] (Corollary 8.4): assuming the Unique Games
Conjecture, for all `ε, γ, λ > 0`, no polynomial-time algorithm finds `3` independent sets
covering `(1/2 + γ) n` vertices in every regular `λ`-one-sided expander with `3` independent sets
covering `(1 - ε) n` vertices, unless `NP ⊆ P`. -/
theorem threeColoring_unbalanced_hardness (hUGC : UGC) :
    ∀ ε γ lam : ℝ, 0 < ε → 0 < γ → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.HasColoring 3 ε →
          G.IsColoring 3 (1 / 2 - γ) (A G)) →
        NPSubsetP :=
  Hard.threeColoring_unbalanced_hardness hUGC

/-- **Theorem 1.6** of [BHSV25] (Theorem 8.6): assuming the Unique Games
Conjecture, for every `ε > 0` there is `R` such that for every `γ > 0` no polynomial-time
algorithm finds `3` independent sets covering `(7/9 + γ) n` vertices in every regular graph with
`3` disjoint independent sets of `(1/3 - ε) n` vertices each, at most two eigenvalues larger than
`ε` and at most `R` eigenvalues larger than `ε` in absolute value, unless `NP ⊆ P`. -/
theorem threeColoring_lowRank_hardness (hUGC : UGC) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ γ : ℝ, 0 < γ →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular →
          (∃ c, G.IsPartialColoring 3 c ∧ ∀ a < 3, (1 / 3 - ε) * G.1 ≤ G.classSize 3 c a) →
          G.numEigGT ε ≤ 2 →
          (Finset.univ.filter fun i ↦ ε < |G.eig i|).card ≤ R →
          G.IsColoring 3 (2 / 9 - γ) (A G)) →
        NPSubsetP :=
  Hard.threeColoring_lowRank_hardness hUGC

/-! ### Threshold ranks -/

/-- **Theorem 4.1** of [BHSV25], in the parameters of Theorem 1.7: for a symmetric matrix with
nonnegative entries and eigenvalues in `[-1, 1]`, and all `τ > 0` and `τ' < τ²`,
`((τ² - τ') / (1 - τ'))² · #{eigenvalues ≤ -τ} ≤ #{eigenvalues ≥ τ'}`. -/
theorem thresholdRank {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (hnonneg : ∀ i j, 0 ≤ A i j) (hnorm : ∀ i, |hA.eigenvalues i| ≤ 1)
    (τ τ' : ℝ) (hτ : 0 < τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 *
        ((Finset.univ.filter fun i ↦ hA.eigenvalues i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ hA.eigenvalues i).card :=
  Spectral.thresholdRank A hA hnonneg hnorm τ τ' hτ hτ'

/-- **Theorem 1.7** of [BHSV25]: for every graph and all `τ > 0` and `τ' < τ²`, the spectrum `σ(G)`
of its normalized adjacency matrix satisfies
`((τ² - τ') / (1 - τ'))² · |σ(G) ∩ (-∞, -τ]| ≤ |σ(G) ∩ [τ', ∞)|`. -/
theorem thresholdRank_graph (G : Graph) (τ τ' : ℝ) (hτ : 0 < τ) (hτ' : τ' < τ ^ 2) :
    ((τ ^ 2 - τ') / (1 - τ')) ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤
      (Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card :=
  Spectral.thresholdRank_graph G τ τ' hτ hτ'

/-! ### The meta-theorems -/

/-- **Theorem 1.8 (1)** of [BHSV25], full version (Corollary 7.2): for every model `M` without
repeated rows, `δ ∈ [0, c₀)` and `λ ∈ (0, c₀)`, an algorithm running in time
`n^{O(1)} · O_{δ,λ,M}(1)` that, on regular `λ`-one-sided expanders with an `(M, δ)`-coloring,
outputs a `(k, O_M(√δ + λ + δ/λ))`-coloring. -/
theorem expanderColoring_distinctRows :
    ∃ C : ℕ, ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ), IsModel M → Function.Injective M →
      ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
            G.IsColoring k (B * (Real.sqrt δ + lam + δ / lam)) (A G) :=
  Alg.expanderColoring_distinctRows

/-- **Theorem 1.8 (2)** of [BHSV25] (Corollary 8.3): assuming the Unique Games
Conjecture, for every model `M` with repeated rows there is `δ > 0` such that, for all
`ε, λ > 0`, no polynomial-time algorithm finds a `(k, δ)`-coloring of every regular `λ`-one-sided
expander with an `(M, ε)`-coloring, unless `NP ⊆ P`. -/
theorem expanderColoring_repeatedRows_hardness (hUGC : UGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (hrows : ¬ Function.Injective M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε lam : ℝ, 0 < ε → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M ε →
          G.IsColoring k δ (A G)) →
        NPSubsetP :=
  Hard.expanderColoring_repeatedRows_hardness hUGC M hM hrows

/-- **Theorem 1.9 (1)** of [BHSV25], full version (Theorem 7.1): for every model `M` with
stationary distribution `π`, `δ ∈ [0, c₀)` and `λ ∈ (0, c₀)`, an algorithm running in time
`n^{O(1)} · O_{δ,λ,M}(1)` that, on regular `λ`-one-sided expanders with an `(M, δ)`-coloring,
outputs a `(k', α + O_M(√δ + λ + δ/λ))`-coloring, where `k'` is the number of distinct rows of
`M` and `α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)`. -/
theorem expanderColoring_algorithm :
    ∃ C : ℕ, ∀ (k : ℕ) (M : Matrix (Fin k) (Fin k) ℝ) (π : Fin k → ℝ), IsModel M →
      IsStationary M π →
      ∃ B c₀ : ℝ, 0 < c₀ ∧ ∀ δ lam : ℝ, 0 ≤ δ → δ < c₀ → 0 < lam → lam < c₀ →
        ∃ K : ℝ, ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M δ →
            G.IsColoring (Nat.card (Set.range M))
              (alpha M π + B * (Real.sqrt δ + lam + δ / lam)) (A G) :=
  Alg.expanderColoring_algorithm

/-- **Theorem 1.9 (2)** of [BHSV25] (Theorem 8.2): assuming the Unique Games
Conjecture, for every model `M` with stationary distribution `π` and all `γ, ε, λ > 0`, no
polynomial-time algorithm finds a `(k, α - γ)`-coloring of every regular `λ`-one-sided expander
with an `(M, ε)`-coloring, unless `NP ⊆ P`. -/
theorem expanderColoring_hardness (hUGC : UGC) {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ)
    (hM : IsModel M) (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∀ γ ε lam : ℝ, 0 < γ → 0 < ε → 0 < lam →
      ∀ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring →
        (∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam → G.MColorable M ε →
          G.IsColoring k (alpha M π - γ) (A G)) →
        NPSubsetP :=
  Hard.expanderColoring_hardness hUGC M hM π hπ

end BHSV25
