# B25: Lasso and partially-rotated designs

The results are the main result of [B25], Theorem 1.5, its consequence for the Lasso,
Corollary 1.6, and two families of designs it applies to, Lemmas 1.3 and 1.4. A design is
partially rotated with respect to a set `S` of columns when, with high probability, every fixed
combination of the columns in `S` is nearly orthogonal to every fixed combination of the others.
Theorem 1.5 says that the restricted eigenvalue constants of such a design with respect to subsets
of `S` are then, with high probability, at least `0.9` times those of the columns in `S` alone,
however the other columns are correlated. The results are stated in
[Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them. None
of them is about algorithms: Corollary 1.6 bounds the error of the Lasso estimate itself. Lemmas
1.3 and 1.4 are stated for `n` large enough, since a bound `e^(-cn)` without a constant factor
cannot hold for small `n`.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v1).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Lemma 1.3 | `partiallyRotated_of_uniform` | There are `c > 0` and `n₀` such that for `n ≥ n₀`, every `X ∈ ℝ^{n×d}` and `S ⊆ [d]`, and every random `R ∈ ℝ^{n×n}` that maps each fixed unit vector to a uniformly random point of the unit sphere, the design `[X_S, R X_{Sᶜ}]` is `(0.01, c)`-partially rotated with respect to `S`. |
| Lemma 1.4 | `partiallyRotated_of_subgaussian` | There are `c > 0` and `K` such that for `n ≥ K (σ'/σ)⁴`, every `X` and `S`, and every random `R` with independent entries of mean `0` and variance `σ²` that are sub-Gaussian with variance proxy `σ'²`, the design `[X_S, R X_{Sᶜ}]` is `(0.01, c σ⁴/σ'⁴)`-partially rotated with respect to `S`. |
| Theorem 1.5 | `re_of_partiallyRotated` | For every `c > 0` there are `C, c' > 0` such that for every random design `X` with columns of norm `√n` that is `(0.01, c)`-partially rotated with respect to `S`, with probability `1 - e^(-c'n)`, every `S' ⊆ S` with `n γ_{S'}(X_S) ≥ C \|S'\| log d` has `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)`. |
| Corollary 1.6 | `lasso_of_partiallyRotated` | For every `c > 0` and `τ ≥ 1` there are `C, c' > 0` such that for such a design, noise `N(0, σ² Iₙ)` independent of it, and `β` with `supp β ⊆ S`, a Lasso estimate exists, and with probability `1 - e^(-c'n) - 2 d^(-τ)` every Lasso estimate `β̂` of radius `‖β‖₁` has `γ_{supp β}(X_S) ‖Xβ̂ - Xβ‖₂² ≤ C σ² \|supp β\| log d`. |

* **Partially-rotated designs** [B25, Definition 1.2] (`PartiallyRotated`): a random design is a
  map from a probability space to `n × d` matrices. For every fixed `α` supported on `S` and `β`
  supported on `Sᶜ`, the correlation `⟨Xα/‖Xα‖₂, Xβ/‖Xβ‖₂⟩` exceeds `ε` in absolute value with
  probability at most `e^(-δn)`; it is `0` when either vector is.
* **The restricted eigenvalue constant** [B25, Definition 1.1] (`reConst`) is the minimum of
  `(1/n) ‖Xβ‖₂² / ‖β_{S'}‖₂²` over the cone `‖β_{S'ᶜ}‖₁ ≤ ‖β_{S'}‖₁`; `γ_{S'}(X_S)` is that of the
  `n × |S|` matrix of the columns in `S`.
* **Probabilities.** The probability of an event that need not be measurable is its outer measure.
  Theorem 1.5 assumes nothing about measurability of the design; its proof only uses union bounds.
  Corollary 1.6 assumes the design measurable, and its noise is independent of it.
* **No divisions by `γ`.** The bounds that divide by `γ_{S'}(X_S)` are multiplied by it, so that
  `γ = 0`, where the paper's bounds say nothing, does not make them false.
* **Lemmas 1.3 and 1.4** hold for `n` large enough. For `n = 1`, `X = [1, 1]`, `S` the first column
  and `R` uniform on `{-1, 1}`, the two columns always have correlation `±1`. The uniform
  distribution on the sphere is Mathlib's surface measure (`Measure.toSphere`), normalized, and the
  hypothesis of Lemma 1.3 is about every fixed unit vector of `ℝⁿ`. "Sub-Gaussian" is Mathlib's
  `HasSubgaussianMGF`.
* **Corollary 1.6** makes "with high probability" explicit as `1 - e^(-c'n) - 2 d^(-τ)`, with `C`
  depending on `τ`. The Lasso is the constrained one of radius `‖β‖₁`, as in the paper, and the
  bound holds for every minimizer.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### Theorem 1.5

The proof has the paper's three steps: Maurey's sparsification [B25, Lemma 2.1], restricted
normalized orthogonality (RNO) implies restricted eigenvalues [B25, Proposition 1.10], and RNO
holds with high probability.

* **Sparsification** ([RE/Maurey.lean](RE/Maurey.lean)). For `β ≠ 0` and `s ≥ 1` there are `s`
  signed coordinates `±e_{jₜ}` of the support of `β` with
  `‖Xβ - (‖β‖₁/s) X ∑ₜ ±e_{jₜ}‖₂² ≤ D² ‖β‖₁² / s`, where `D` bounds the column norms. This is
  Maurey's empirical method (draw `j` with probability `|βⱼ|/‖β‖₁`), with the draws fixed one at a
  time.
* **RNO implies RE** ([RE/RNO.lean](RE/RNO.lean)). RNO is used only for the directions that the
  sparsification produces: sums of `s` signed coordinates of `S` against sums of `s` signed
  coordinates of `Sᶜ`. With `ε = 0.01`, the paper's argument gives `γ_{S'}(X) ≥ 0.9 γ_{S'}(X_S)`
  whenever `s γ_{S'}(X_S) ≥ 22500 |S'|`.
* **RNO with high probability** ([RE/Main.lean](RE/Main.lean)). Correlations do not change when
  the vectors are scaled by positive numbers, so RNO is needed only for `(2d)^(2s)` fixed pairs of
  directions. Partial rotation bounds each pair by `e^(-cn)`, and a union bound finishes, with no
  net over a sphere. Since `γ_{S'}(X_S)` is random, one level `s = ⌊cn / (4 log (2d))⌋` is used
  for every `S'`. Then `C = 8 · 22501 / c` makes `C |S'| log d ≤ n γ` imply
  `s γ ≥ 22500 |S'|`, and the failure probability is at most `e^(-cn/2)`.

### Corollary 1.6

The proof is the paper's [B25, Appendix B]. For a Lasso estimate `β̂`, `Δ = β̂ - β` lies in the cone
of `supp β`, and comparing with `β` gives `‖XΔ‖₂² ≤ 2 ⟨w, XΔ⟩`
([Lasso/Basic.lean](Lasso/Basic.lean)). When `n γ ≥ C₂ |supp β| log d`, Theorem 1.5 gives
`γ_{supp β}(X) ≥ 0.9 γ`, and Hölder with the largest correlation of the noise with a column gives
the fast rate. Otherwise `‖XΔ‖₂² ≤ 4 ‖w‖₂²` already suffices. The noise has Gaussian correlations
with the columns and a chi-square norm ([Lasso/Noise.lean](Lasso/Noise.lean)). The two
exponentially small failure probabilities fit into one `e^(-c'n)` because a large `C₂` makes the
first impossible for small `n` ([Lasso/Main.lean](Lasso/Main.lean)).

### Lemmas 1.3 and 1.4

Both proofs reduce, as in the paper, to the correlation `⟨u, Rw⟩ / ‖Rw‖₂` for fixed unit vectors
`u` and `w`.

* **Lemma 1.3** ([Rot/Sphere.lean](Rot/Sphere.lean)). `Rw` is a uniform point of the sphere, and
  the cap `{y : |⟨u, y⟩| > ε}` is bounded through the definition of the surface measure: its cone
  in the unit ball lies in three balls of radius at most `1 - ε²/8`, so the cap has measure at most
  `2^(-n) + 2 (1 - ε²/8)ⁿ`. The paper bounds it through Gaussian tails instead. The constants are
  `c = 1/160000` and `n₀ = 320000`.
* **Lemma 1.4** ([Rot/SubGauss.lean](Rot/SubGauss.lean)). `⟨u, Rw⟩` is sub-Gaussian with proxy
  `σ'²`. The coordinates of `Rw` are independent with second moment `σ²` and fourth moment at most
  `36 σ'⁴`, and `‖Rw‖₂² ≥ σ² n / 4` with probability `1 - e^(-nσ⁴/(144 σ'⁴))` by a Chernoff bound
  on `e^(-λ ‖Rw‖₂²)`, in place of the paper's Hanson–Wright inequality. The constants are
  `c = 1/960000` and `K = 1920000`.

## Map of the files

| Files | Content |
| --- | --- |
| [Model.lean](Model.lean), [Challenge.lean](Challenge.lean) | the definitions and the statements |
| [Basic.lean](Basic.lean) | norms and correlations, signed tuples of coordinates, the restricted eigenvalue constant as an infimum, rotated designs |
| [RE/Maurey.lean](RE/Maurey.lean) | Maurey's sparsification |
| [RE/RNO.lean](RE/RNO.lean) | RNO on signed tuples implies restricted eigenvalues |
| [RE/Main.lean](RE/Main.lean) | Theorem 1.5 |
| [Lasso/Basic.lean](Lasso/Basic.lean), [Lasso/Noise.lean](Lasso/Noise.lean) | the Lasso's existence, basic inequality and fast rate; the tails of the noise |
| [Lasso/Main.lean](Lasso/Main.lean) | Corollary 1.6 |
| [Rot/Sphere.lean](Rot/Sphere.lean) | Lemma 1.3 |
| [Rot/SubGauss.lean](Rot/SubGauss.lean) | Lemma 1.4 |
| [Solution.lean](Solution.lean) | the four results |

*Formalized by [Claude Code](https://claude.com/claude-code).*
