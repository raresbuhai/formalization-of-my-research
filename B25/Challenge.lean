module

public import B25.Model

/-!
# Main results: statements

Four results of [B25], with proofs `sorry`: the main result, Theorem 1.5, that the restricted
eigenvalue constants of a partially-rotated design with respect to subsets of `S` do not depend on
the columns outside `S`; its consequence for the Lasso, Corollary 1.6; and two families of
partially-rotated designs, Lemmas 1.3 and 1.4. Numbers are those of the arXiv version (v1). None of
the results is about algorithms: Corollary 1.6 bounds the error of the Lasso estimate, the
minimizer of a convex program, however it is computed.

What a reader has to trust is this file and what it imports: the definitions in `B25/Model.lean`
(norms and correlations, the restricted eigenvalue constant, partially-rotated and rotated
designs, the uniform distribution on the sphere, the Lasso) and Mathlib.

## Conventions of all four results

* **Random designs** are maps `X : Ω → Matrix (Fin n) (Fin d) ℝ` on a probability space
  `(Ω, P)`, and random matrices `R` likewise; `Ω` is arbitrary. "With probability at least
  `1 - p`" is `P(bad event) ≤ p`. `P` of a set that need not be measurable is its outer measure,
  the least measure of a measurable event containing it. So some measurable event of probability
  at most `p` contains the bad event, and the conclusion holds on a measurable event of
  probability at least `1 - p`.
* **Constants.** "For some constant `c > 0`, there exists some constant `C > 0`" is
  `∀ c > 0, ∃ C > 0`: the constants of the conclusion depend only on `c` (in Corollary 1.6 also
  on the exponent `τ` of the failure probability), not on `n`, `d`, `S` or the design.
  `e^(-Ω(n))` is `e^(-c' n)` for such a constant `c' > 0`. Logarithms are natural.
* **Columns of norm `√n`** (`B25.HasNormalizedColumns`) are asked to hold almost surely.
* **`γ_{S'}(X_S)`** is `B25.reConst (B25.cols X S) (S'.subtype (· ∈ S))`: the constant of the
  `n × |S|` matrix `X_S` with respect to `S'`, a set of its columns. For `S' = ∅` the paper's
  constant is not defined; here it is `0`, and the statements are trivial for `S' = ∅`.
* **No divisions by `γ`.** The bounds of Theorem 1.5 and Corollary 1.6 that divide by
  `γ = γ_{S'}(X_S)` are multiplied by it: `n ≥ C |S'| log d / γ` is `C |S'| log d ≤ n γ`, and
  `(1/n) ‖X β̂ - X β‖₂² ≤ C σ² k log d / (γ n)` is `γ ‖X β̂ - X β‖₂² ≤ C σ² k log d`. For `γ > 0`
  these are the same; for `γ = 0` the paper's bounds say nothing, and in Lean, where `x / 0 = 0`,
  the divided forms would be false.

## Lemma 1.3

[B25, Lemma 1.3]: let `R ∈ ℝ^{n×n}` be a random matrix such that, for a fixed unit vector `v`,
`Rv` is distributed uniformly over the unit sphere (e.g., a random orthogonal matrix). Then, for
any matrix `X ∈ ℝ^{n×d}` and any set `S ⊆ [d]`, the matrix `X' = [X_S, R X_{Sᶜ}]` is
`(0.01, c)`-partially rotated for some constant `c > 0`.

Formally (`B25.partiallyRotated_of_uniform`): there are `c > 0` and `n₀` such that for every
`n ≥ n₀`, every `X ∈ ℝ^{n×d}` and `S`, and every random `R` such that `Rv` has the law
`B25.uniformSphere n` for each fixed unit vector `v`, the design `[X_S, R X_{Sᶜ}]`
(`B25.rotateCols`) is `(1/100, c)`-partially rotated with respect to `S`.

* **`n ≥ n₀`.** Partial rotation asks for the bound `e^(-cn)` with no constant factor, and for
  small `n` the lemma fails for some `X`. For `n = 1`, `d = 2`, `X = [1, 1]`, `S` the first column
  and `R` uniform on `{-1, 1}` (which maps each unit vector of `ℝ¹` to a uniform point of the
  sphere `{-1, 1}`), the two columns always have correlation `±1`, and the lemma would say
  `1 ≤ e^(-c)`. So the lemma is stated for `n` large enough.
* **The hypothesis** is the law of `Rv` for each fixed unit vector `v ∈ ℝⁿ`; nothing else is
  assumed about the law of `R`. A Haar-random orthogonal matrix satisfies it. As an equality of
  laws, it also makes `ω ↦ R ω v` almost-everywhere measurable: for a map that is not, Mathlib's
  `Measure.map` is a Dirac measure, and `B25.uniformSphere n` is not one for `n ≥ 1`.

## Lemma 1.4

[B25, Lemma 1.4]: let `R ∈ ℝ^{n×n}` be a random matrix with independent entries that have mean
zero, variance `σ²`, and are `(σ')²`-sub-Gaussian. Then, for any matrix `X ∈ ℝ^{n×d}` and any set
`S ⊆ [d]`, the matrix `X' = [X_S, R X_{Sᶜ}]` is `(0.01, c σ⁴/(σ')⁴)`-partially rotated for some
constant `c > 0`.

Formally (`B25.partiallyRotated_of_subgaussian`): there are `c > 0` and `K` such that for all
`n ≥ K (σ'/σ)⁴`, every `X` and `S`, and every random `R` with independent entries (`iIndepFun`),
each of mean `0`, variance `σ² > 0` and sub-Gaussian with variance proxy `(σ')²`, the design
`[X_S, R X_{Sᶜ}]` is `(1/100, c σ⁴/(σ')⁴)`-partially rotated with respect to `S`.

* **Sub-Gaussian** [B25, Definition A.1] is Mathlib's `HasSubgaussianMGF`:
  `E e^(tX) ≤ e^((σ')² t²/2)` for all `t`. For a variable of mean `0` this is the paper's
  definition, which centers `X`.
* **`n ≥ K (σ'/σ)⁴`.** As in Lemma 1.3, small `n` must be excluded: the example there has a
  Rademacher `R`, whose entry has mean `0`, variance `1` and variance proxy `1`. The exponent
  `c σ⁴/(σ')⁴` makes `e^(-δn)` close to `1` until `n` is of order `(σ'/σ)⁴`, which is where the
  lemma starts.

## Theorem 1.5

[B25, Theorem 1.5]: suppose a matrix `X ∈ ℝ^{n×d}` with columns of norm `√n` is
`(0.01, c)`-partially rotated with respect to a set `S ⊆ [d]` for some constant `c > 0`. Then there
exists some constant `C > 0` such that, with probability at least `1 - e^(-Ω(n))`, for all
`S' ⊆ S` such that `n ≥ C |S'| log d / γ_{S'}(X_S)` it holds that `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)`.

Formally (`B25.re_of_partiallyRotated`): for every `c > 0` there are `C > 0` and `c' > 0` such that
for every random design `X` whose columns have norm `√n` almost surely and that is
`(1/100, c)`-partially rotated with respect to `S`, the probability that some `S' ⊆ S` has
`C |S'| log d ≤ n γ_{S'}(X_S)` and `γ_{S'}(X) < 0.9 γ_{S'}(X_S)` is at most `e^(-c' n)`.

* The event quantifies over all `S' ⊆ S` at once, and `γ_{S'}(X_S)`, a function of the random
  design, is evaluated on the same outcome.
* **No measurability** is assumed of the design. For a measurable design this is the paper's
  statement. For any design it bounds the outer measure of the bad event, which is a stronger
  statement; it holds because the bad event lies in the union of the bad events of the
  hypothesis for finitely many pairs `(α, β)` and of the null event where the columns do not have
  norm `√n`, and outer measures are subadditive.

## Corollary 1.6

[B25, Corollary 1.6]: in the sparse linear regression model `y = Xβ + w`, `w ~ N(0, σ² Iₙ)`,
suppose that the design `X ∈ ℝ^{n×d}` with columns of norm `√n` is `(0.01, c)`-partially rotated
with respect to a set `S ⊆ [d]` for some constant `c > 0`. Then, if `supp(β) ⊆ S`, the Lasso
estimate `β̂` satisfies with high probability
`(1/n) ‖X β̂ - X β‖₂² ≤ O(σ² k log d / (γ_{supp(β)}(X_S) n))`.

Formally (`B25.lasso_of_partiallyRotated`): for every `c > 0` and `τ ≥ 1` there are `C > 0` and
`c' > 0` such that, for every measurable random design `X` as in Theorem 1.5 and all `σ` and `β`
with `supp β ⊆ S`, every instance has a Lasso estimate, and with probability at least
`1 - e^(-c' n) - 2 d^(-τ)` over the design and the noise, every Lasso estimate `β̂` of radius
`‖β‖₁` satisfies `γ_{supp β}(X_S) ‖X β̂ - X β‖₂² ≤ C σ² |supp β| log d`.

* **The noise** is independent of the design: the outcome `ω` and the noise `w` have the law
  `P ⊗ N(0, σ² Iₙ)` (`B25.noiseLaw`), so the pair `(X, w)` has the law `(P.map X) ⊗ N(0, σ² Iₙ)`,
  and `y = X β + w`. The paper gives the law of `w` alone; without independence the design could
  depend on the noise. Unlike in Theorem 1.5, the design is assumed measurable: the proof bounds
  the probability of the bad event by conditioning on the design.
* **`k = |supp β|`.** A `k`-sparse `β` has `|supp β| ≤ k`, so the bound with `|supp β|` implies the
  bound with `k`.
* **The Lasso** is the constrained one, with radius `‖β‖₁` [B25, Equation (1.2)]. It may have
  several minimizers; the bound is asked of every one, and the statement says that there is one.
* **"With high probability"** is made explicit: `1 - e^(-c' n) - 2 d^(-τ)` for any `τ ≥ 1`, with
  `C` depending on `c` and `τ`. In the proof, `e^(-c' n)` comes from Theorem 1.5 and from the norm
  of the noise, and `2 d^(-τ)` from the largest correlation of the noise with a column.

Reference: [B25] R.-D. Buhai, *Lasso and partially-rotated designs*, arXiv:2505.11093.
-/

@[expose] public section

namespace B25

open MeasureTheory ProbabilityTheory Matrix

/-- **Lemma 1.3** of [B25]: rotating the columns outside `S` by a random matrix that maps every
fixed unit vector to a uniform point of the sphere gives a partially-rotated design. -/
theorem partiallyRotated_of_uniform :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (d : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : Ω → Matrix (Fin n) (Fin n) ℝ),
        (∀ v : Fin n → ℝ, v ⬝ᵥ v = 1 → P.map (fun ω ↦ R ω *ᵥ v) = uniformSphere n) →
        PartiallyRotated P (fun ω ↦ rotateCols X S (R ω)) S (1 / 100) c :=
  sorry

/-- **Lemma 1.4** of [B25]: rotating the columns outside `S` by a random matrix with independent
sub-Gaussian entries gives a partially-rotated design. -/
theorem partiallyRotated_of_subgaussian :
    ∃ c K : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : Ω → Matrix (Fin n) (Fin n) ℝ) (σ σ' : ℝ), 0 < σ → K * (σ' / σ) ^ 4 ≤ n →
        iIndepFun (fun (ij : Fin n × Fin n) (ω : Ω) ↦ R ω ij.1 ij.2) P →
        (∀ i j, ∫ ω, R ω i j ∂P = 0) →
        (∀ i j, Var[fun ω ↦ R ω i j; P] = σ ^ 2) →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ R ω i j) (σ' ^ 2).toNNReal P) →
        PartiallyRotated P (fun ω ↦ rotateCols X S (R ω)) S (1 / 100) (c * σ ^ 4 / σ' ^ 4) :=
  sorry

/-- **Theorem 1.5** of [B25]: with probability `1 - e^(-Ω(n))`, a partially-rotated design with
columns of norm `√n` has `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)` for every `S' ⊆ S` with
`n ≥ C |S'| log d / γ_{S'}(X_S)`. -/
theorem re_of_partiallyRotated :
    ∀ c : ℝ, 0 < c → ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (n d : ℕ) (S : Finset (Fin d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → Matrix (Fin n) (Fin d) ℝ),
        (∀ᵐ ω ∂P, HasNormalizedColumns (X ω)) → PartiallyRotated P X S (1 / 100) c →
        P {ω | ∃ S' ⊆ S,
            C * S'.card * Real.log d ≤ n * reConst (cols (X ω) S) (S'.subtype (· ∈ S)) ∧
              reConst (X ω) S' < 9 / 10 * reConst (cols (X ω) S) (S'.subtype (· ∈ S))} ≤
          ENNReal.ofReal (Real.exp (-(c' * n))) :=
  sorry

/-- **Corollary 1.6** of [B25]: for a partially-rotated design with columns of norm `√n` and a
secret supported in `S`, with high probability every Lasso estimate has prediction error
`(1/n) ‖X β̂ - X β‖₂² ≤ C σ² |supp β| log d / (γ_{supp β}(X_S) n)`. -/
theorem lasso_of_partiallyRotated :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 1 ≤ τ → ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (n d : ℕ) (S : Finset (Fin d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → Matrix (Fin n) (Fin d) ℝ), Measurable X →
        (∀ᵐ ω ∂P, HasNormalizedColumns (X ω)) → PartiallyRotated P X S (1 / 100) c →
        ∀ (σ : ℝ) (β : Fin d → ℝ), supp β ⊆ S →
          (∀ ω w, ∃ b, IsLasso (X ω) (X ω *ᵥ β + w) (l1 β) b) ∧
          (P.prod (noiseLaw n σ))
              {p | ∃ b, IsLasso (X p.1) (X p.1 *ᵥ β + p.2) (l1 β) b ∧
                C * σ ^ 2 * (supp β).card * Real.log d <
                  reConst (cols (X p.1) S) ((supp β).subtype (· ∈ S)) *
                    ((X p.1 *ᵥ (b - β)) ⬝ᵥ (X p.1 *ᵥ (b - β)))} ≤
            ENNReal.ofReal (Real.exp (-(c' * n)) + 2 * (d : ℝ) ^ (-τ)) :=
  sorry

end B25
