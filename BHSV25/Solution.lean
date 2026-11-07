module

public import BHSV25.Model
public import BHSV25.Spectral.ThresholdRank
public import BHSV25.Alg.VertexCover
public import BHSV25.Alg.Coloring
public import BHSV25.Alg.Expander
public import BHSV25.Hard.Corollaries
public import BHSV25.Hard.LowRank

/-!
# Main results: proofs

Restates the theorems of `Challenge.lean` with the same names and statements, and proves them from
the development in this folder. Don't import `Challenge` here: the names would clash.
-/

public section

namespace BHSV25

open Filter Topology Turing.MultiTapeTM UniqueGames

/-! ### Independent sets and vertex covers -/

/-- **Theorem 1.1** of [BHSV25] (Corollary 7.21): for every `λ ∈ (0, 1)` and every `t`, a
polynomial-time algorithm that, on regular graphs with at most `t` eigenvalues larger than `λ`
(`λ`-one-sided expanders for `t = 1`) and an independent set of `(1/2 - γ) n` vertices for some
`γ ∈ [0, 1/10]`, outputs an independent set of at least `(1/2 - (5 + f λ) γ) n` vertices, where
`f λ → 0` as `λ → 0`. -/
theorem independentSet_approximation :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ t : ℕ,
        ∃ A : Graph → List Bool, ComputableInPolyTime A encGraph Encoding.encBits ∧
          ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
            G.2.IsIndepSet (G.vertexSet (A G) : Set (Fin G.1)) ∧
            ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 / 10 → G.HasIndepSet ((1 / 2 - γ) * G.1) →
              (1 / 2 - (5 + f lam) * γ) * G.1 ≤ (G.vertexSet (A G)).card :=
  Alg.independentSet_approximation

/-- **Corollary 1.2** of [BHSV25]: for every `ε > 0`, a polynomial-time `(5/3 + ε)`-approximation
algorithm for vertex cover on regular `λ₀`-one-sided expanders, for some `λ₀ > 0`. -/
theorem vertexCover_approximation :
    ∀ ε : ℝ, 0 < ε → ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∃ A : Graph → List Bool, ComputableInPolyTime A encGraph Encoding.encBits ∧
        ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam₀ →
          G.IsVertexCover (G.vertexSet (A G)) ∧
          ((G.vertexSet (A G)).card : ℝ) ≤ (5 / 3 + ε) * G.vertexCoverNumber :=
  Alg.vertexCover_approximation

/-! ### Algorithms for 3-colorable one-sided expanders -/

/-- **Theorem 1.3** of [BHSV25] (Theorem 7.9): for every `λ > 0`, a polynomial-time algorithm that,
on regular `λ`-one-sided expanders with `3` independent sets of at most `(1/2 - f λ) n` vertices
each that cover all but `λ n` vertices, outputs `3` independent sets covering all but `f λ · n`
vertices, where `f λ → 0` as `λ → 0`. -/
theorem threeColoring_balanced :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
          ∀ G : Graph, G.IsRegular → G.IsOneSidedExpander lam →
            (∃ c, G.IsColoring 3 lam c ∧
              ∀ a < 3, (G.classSize 3 c a : ℝ) ≤ (1 / 2 - f lam) * G.1) →
            G.IsColoring 3 (f lam) (A G) :=
  Alg.threeColoring_balanced

/-- **Corollary 1.4** of [BHSV25]: for every `λ > 0`, a polynomial-time algorithm that, on regular
`λ`-one-sided expanders with `3` independent sets covering all but `λ n` vertices, outputs `3`
independent sets of which one has at least `(1/2 - f λ) n` vertices or which cover all but
`f λ · n` vertices, where `f λ → 0` as `λ → 0`. -/
theorem threeColoring_independentSet_or_coloring :
    ∃ f : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧
      ∀ lam : ℝ, 0 < lam →
        ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
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

/-- **Theorem 1.8 (1)** of [BHSV25] (Corollary 7.2): for every model `M` without repeated rows, a
polynomial-time algorithm solves `M`-expander-coloring. -/
theorem expanderColoring_distinctRows {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M)
    (hrows : Function.Injective M) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M 0 A :=
  Alg.expanderColoring_distinctRows M hM hrows

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

/-- **Theorem 1.9 (1)** of [BHSV25] (Theorem 7.1): for every model `M` with stationary
distribution `π`, a polynomial-time algorithm solves `(M, α)`-expander-coloring, where
`α = ∑_a min(π_a, ∑_{b ≠ a, M^(b) = M^(a)} π_b)`. -/
theorem expanderColoring_algorithm {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M)
    (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∃ A : Graph → List ℕ, ComputableInPolyTime A encGraph encColoring ∧
      SolvesExpanderColoring M (alpha M π) A :=
  Alg.expanderColoring_algorithm M hM π hπ

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
