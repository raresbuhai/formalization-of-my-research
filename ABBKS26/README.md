# ABBKS26: Dimension reduction via sum-of-squares and improved clustering algorithms for non-spherical mixtures

The results are finite-precision variants of [ABBKS26, Theorems 1.1 and 1.2], in their full
versions (Theorems 5.2 and 6.2), stated in [Challenge.lean](Challenge.lean) with the definitions
of [Model.lean](Model.lean) and proved in [Solution.lean](Solution.lean), with only the standard
axioms; `lake comparator` checks them. A mixture of `k` Gaussians whose components are pairwise
`Δ`-separated, either all centered (Theorem 1.1) or all with one common covariance (Theorem 1.2),
is observed through an `ε`-corruption. The theorems cluster the sample with error
`O(k/wmin · max(ε, Δ^(-1/(Ck))))` in each component, in time `g(1/wmin, Δ) · poly(|x|)` for
centered mixtures and `g(1/wmin, Δ) · poly(|x|) · d^O(log² (1/wmin))` for a common covariance.
The algorithms read rational approximations of the sample points, and the guarantees hold for
every such approximation. They are given a failure probability `δ > 0` and succeed with probability
`1 - δ` from `poly(1/δ)` times the paper's number of samples.

The formal proof follows the paper's argument in outline, though some of its steps take a different
route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v2).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 1.1 (Thm. 5.2) | `centered_clustering` | There are `C ≥ 1`, a computable `g` and `f ≥ 1`, and an algorithm running in time `g(⌈1/wmin⌉, ⌈Δ⌉) · (\|x\| + 2)^C` such that, for a mixture of centered Gaussians whose components are pairwise `Δ`-separated (spectrally or in relative Frobenius norm) with `Δ ≥ f(1/wmin)`, an `ε`-corruption with `ε ≤ 1/f(1/wmin)`, and `n ≥ ((d + 1)(Δ + 1)/(wmin δ))^C` rounded samples, it returns with probability `1 - δ` a clustering that recovers each component up to a `C k/wmin · max(ε, Δ^(-1/(Ck)))` fraction of its points. |
| Theorem 1.2 (Thm. 6.2) | `identical_covariance_clustering` | The same for a mixture of Gaussians with one common covariance whose means are pairwise `Δ`-separated along some direction, from `n ≥ ((d + 1)/wmin)^(C (log (1/wmin) + 1)) ((Δ + 1)/δ)^C` rounded samples, in time `g(⌈1/wmin⌉, ⌈Δ⌉) · (\|x\| + 2)^C · (d + 2)^(C (L² + 1))` with `L ≈ log₂ (1/wmin)`. |

* **The model** ([Model.lean](Model.lean)): `k` Gaussians `N(μᵢ, Σᵢ)` in `ℝ^d` with positive
  definite covariances and nonnegative weights `wᵢ ≥ wmin` summing to `1`. Separation is the
  paper's Definition 5.1 (some direction `v` with `vᵀΣᵢv > Δ² vᵀΣⱼv`, or
  `‖Σᵢ^(-1/2) Σⱼ Σᵢ^(-1/2) - I‖_F² > Δ² ‖Σᵢ^(-1/2) Σⱼ Σᵢ^(-1/2)‖²`) for Theorem 1.1, and
  Definition 6.1 (some `v` with `⟨μᵢ - μⱼ, v⟩² > 2Δ² vᵀΣv`) for Theorem 1.2.
* **Corruptions** (`ABBKS26.IsCorruption`): each sample point is an independent triple
  `(i, y, z)` of a label, a point `y` of component `i`, and the observed point `z`, with `z ≠ y`
  with probability at most `ε`. The law of `z` is then any distribution within total variation
  distance `ε` of the mixture. The guarantee holds for every such corruption, and the components
  `Sᵢ` to recover are the sets of points with label `i`, corrupted ones included.
* **Rounded samples** (`ABBKS26.IsRounding`): the algorithm reads, for each observed point `z` with
  label `i`, a rational vector `r (i, z)` with `‖Σᵢ^(-1/2) (r (i, z) - z)‖ ≤ 1/n`, in the geometry
  of the point's own component. The guarantee holds for every such rounding. It is applied to each
  point separately, may use the label and depend on the mixture, `n` and the corruption, and need
  not be measurable. The paper's analysis is for the exact points.
* **The input** is `k`, `wmin`, `Δ`, `δ` (rationals) and the rounded sample; not `ε`, the
  weights, the means, the covariances, the labels, the corruption or the rounding. One natural
  number `C` stands for all the `O(·)`s, the functions `f` and `g` for the paper's.
* **Algorithms** are multitape Turing machines with coins, running within the explicit time
  bounds `ABBKS26.centeredTime` and `ABBKS26.identicalCovTime` in the length `|x|` of the encoded
  input. The factor `(|x| + 2)^C` pays for reading the sample. The probability
  (`ABBKS26.successProb`) is over the sample and the coins; it is a lower integral, since the
  rounding need not be measurable.
* **Recovery** (`ABBKS26.RecoversClusters`): the output labels every point, and for some
  permutation `π` of the labels each output cluster `Ŝᵢ` keeps all but an `η` fraction of `S_{π i}`.
* **The failure probability** `δ` is part of the input; one algorithm and one `C` serve all `δ`,
  and the sample size grows like `(1/δ)^C`. The paper's statements are "with high probability";
  the dependence on `δ` comes from the proof. The paper's explicit bounds on `f` and `g` in its
  footnotes are not formalized.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

Both theorems are proved by one development, parametrized by the kind of mixture
(`ABBKS26.Common.Mode`): the same tree, selection and assembly, with the paper's two subspace
theorems and their splits plugged in.

### Common structure

* **One good event.** All probability enters through one measurable event on the labelled
  sample ([Tree/Good.lean](Tree/Good.lean), from [Prob/](Prob/)): the label counts are close to
  their expectations ([Prob/Counts.lean](Prob/Counts.lean)), few points are corrupted, every
  window `{a ≤ q(x) ≤ b}` for every quadratic polynomial `q` holds nearly the expected number of
  each component's points, uniformly ([Prob/Uniform.lean](Prob/Uniform.lean), by a net of
  quadratic polynomials and Hoeffding's inequality,
  [Prob/UniformHoeffding.lean](Prob/UniformHoeffding.lean)), and the empirical moments of the
  standardized points of each component are close to Gaussian ones
  ([Prob/Moments.lean](Prob/Moments.lean)). A lower bound on every good sample gives a lower bound
  on `successProb` ([Prob/Glue.lean](Prob/Glue.lean)).
* **Everything else is deterministic** on the good event, for every rounding and every
  corruption ([Assembly/Det.lean](Assembly/Det.lean)), including the directions, frames and
  thresholds the algorithm computes from the data: the uniform window counts cover them all, so
  no stage needs fresh samples, and the paper's split of the sample into two parts is not used.
  The algorithm ignores its coins.
* **Robustness to the rounding.** Each point moves by at most `1/n` in the geometry of its
  component; every window and moment estimate carries this perturbation
  ([Tree/RefineAuxResilience.lean](Tree/RefineAuxResilience.lean),
  [Select/LearnAuxResilience.lean](Select/LearnAuxResilience.lean)).
* **A fixed schedule.** The paper guesses the corruption level `ε` from a grid and keeps a
  candidate for every guess. Here the parameters at depth `h` of the tree depend only on
  `wmin`, `k` and `h` ([Assembly/Schedule.lean](Assembly/Schedule.lean)); only the final tests use
  `Δ`. The hypotheses `Δ ≥ f(1/wmin)` and `ε ≤ 1/f(1/wmin)` pay for it.

### Sum-of-squares dimension reduction (Section 4)

* **Theorem 4.1, Algorithm 1** ([Rounding/DetRound.lean](Rounding/DetRound.lean),
  `ABBKS26.Rounding.detRound_spec`): if the solutions of a system concentrate near a subspace of
  rank `r`, a subspace of bounded dimension approximately contains all of them. Each round solves a
  sum-of-squares program with the verified solver of
  [Background/SumOfSquares](../Background/SumOfSquares) and reads the pseudo-moment matrix
  `Ẽ[uuᵀ]`. It stops when the objective certifies that the current span covers every solution.
  Otherwise, instead of the paper's random eigenvector, a deterministic greedy step appends dyadic
  vectors along which the pseudo-variance outside the current span is large, until it is small in
  every direction. A packing bound in the range of the hidden subspace bounds the number of
  rounds. The test whether a pseudo-expectation exists is replaced by this optimization form,
  since the solver is approximate.
* **Lemma 4.3 and Theorem 4.2** ([Rounding/Nested.lean](Rounding/Nested.lean),
  [Rounding/Raw.lean](Rounding/Raw.lean), [Rounding/RC2.lean](Rounding/RC2.lean),
  `ABBKS26.Rounding.roundComplement_spec`): the orthogonal complement. The system "`‖u‖² = 1` and
  there is a sum-of-squares proof that `⟨u, v⟩²` is small for every solution `v`" becomes an
  ordinary system by encoding the inner proof with Gram variables
  ([Common/Gram.lean](Common/Gram.lean)) and coefficient-matching equalities, with rational
  coefficients and an explicit size bound. The inner proofs use one sum-of-squares multiplier per
  constraint. Theorem 4.2 is Algorithm 1 applied to this system.
* **Derivations** are normed and linear in the constraints (`SoS.DerivesNq`, in
  [Background/SumOfSquares/NormedLinear.lean](../Background/SumOfSquares/NormedLinear.lean)), with
  the inequalities of the paper's Section 3.1 in [SoS/Kit.lean](SoS/Kit.lean). A family of
  constraints indexed by a vector, such as the paper's Hessian constraint, enters a derivation
  through finitely many instances ([Rounding/Family.lean](Rounding/Family.lean)).

### Centered mixtures (Section 5)

* **The system** ([Centered/Poly.lean](Centered/Poly.lean)): the fourth-moment excess of a centered
  mixture is a weighted sum of squares of the covariance deviations `Σᵢ - Σ̄` (Lemma 5.8), and its
  Hessian gives the constraint of Definition 5.9. One instance of the Hessian family,
  `u = (Σᵢ - Σ̄) v`, suffices, and in isotropic position its cross terms cancel, so the
  identifiability proof (Lemmas 5.11 and 5.12, [Centered/Ident.lean](Centered/Ident.lean)) stays at
  degree 8.
* **Approximate moments** ([Centered/Transfer.lean](Centered/Transfer.lean),
  [Centered/Empirical*.lean](Centered/)): the system built from the robustly estimated, rounded
  fourth moments is compared with the exact system referenced to the mixture covariance `Σ̄`,
  rather than to the whitened mixture, which avoids matrix square roots (Lemmas 5.16–5.18).
* **Feasibility and rank** ([Centered/Feasible.lean](Centered/Feasible.lean)): Lemmas 5.13
  and 5.20.
* **Theorem 5.6** ([Centered/ThmZ.lean](Centered/ThmZ.lean), `ABBKS26.Centered.thmZ`): the
  orthogonal-complement rounding of the empirical system approximately contains the thin
  directions of every centered mixture compatible with the moment estimates, with explicit
  parameters ([Centered/Params.lean](Centered/Params.lean)).
* **Refinement** (Algorithms 2 and 3): Frobenius splits and spectral splits by windows on
  `⟨v, x⟩²` along a net of the subspace of Theorem 5.6 times a grid of thresholds
  ([Tree/Complete.lean](Tree/Complete.lean), [Tree/CompleteAuxPopulation.lean](Tree/CompleteAuxPopulation.lean):
  Lemmas 5.24 and 5.25). A pair of components that is close in Frobenius norm is spectrally
  separated by a congruence argument ([Linalg/Separation.lean](Linalg/Separation.lean)), in place of
  Fact 5.21.

### Identical covariances (Section 6)

* **The system** ([IdCov/MomPoly.lean](IdCov/MomPoly.lean)): generalized Hermite polynomials
  (Lemma 6.6) and the moment constraints of Definition 6.7, comparing the projected moments of degree
  `O(log (1/wmin))` with those of a Gaussian with the same second moment along `v`.
* **Identifiability** ([IdCov/Ident.lean](IdCov/Ident.lean), Lemmas 6.8 and 6.9), from the moment
  mismatch of a discrete distribution with minimum weight `wmin`
  ([IdCov/Mismatch.lean](IdCov/Mismatch.lean), as in [BS23]).
* **Approximate moments and rounding conditions** ([IdCov/Approx.lean](IdCov/Approx.lean),
  [IdCov/RoundCond.lean](IdCov/RoundCond.lean)): Lemmas 6.13–6.15.
* **Theorem 6.5** ([IdCov/Subspace.lean](IdCov/Subspace.lean), `ABBKS26.IdCov.thmSUB`).
* **Refinement** (Algorithms 4 and 5): mean splits by windows on `⟨v, x⟩` along a net of the
  subspace of Theorem 6.5 (Lemma 6.16).

### Robust subroutines

The paper cites robust algorithms as black boxes; they are proved here in the form the argument
needs ([Robust/](Robust/)):

* **Robust isotropic position** (Fact 3.21) and **robust learning of one Gaussian** (Fact 3.18):
  a filter on quadratic features ([Robust/Filter.lean](Robust/Filter.lean)). Each failing
  iteration removes mostly corrupted weight or exhibits a quadratic statistic of large spread; a
  passing iteration gives accurate second moments.
* **Certified moments** (Fact 5.14 and Theorem 6.11): one semidefinite program over weights on the
  points, solved by the same verified solver ([Robust/MomentSDP.lean](Robust/MomentSDP.lean)).
* **Frobenius clustering** (Fact 3.22) is deterministic: the quadratic statistics recorded by the
  filter give candidate splits, which are checked by their window counts and deduplicated, leaving
  at most `2^(k-1)` splits (`ABBKS26.Tree.frobSplits` in
  [Tree/RefineAuxCore.lean](Tree/RefineAuxCore.lean)).
  This is the only place where splits are checked while the tree is built.

### The tree, selection and reclustering

* **The tree** ([Tree/Tree.lean](Tree/Tree.lean), [Tree/RefineAuxCore.lean](Tree/RefineAuxCore.lean),
  `ABBKS26.Tree.refine_spec`): as in Algorithms 2–5, every node of partial clusterings is refined by
  all its candidate splits, without pruning. Its size is bounded at every level (Lemmas 5.26
  and 6.17), and on the good event a path of good partial clusterings reaches a leaf (Lemmas 5.27
  and 6.18). Any split by a window leaks few points of the components it cuts
  ([Tree/Sound.lean](Tree/Sound.lean)).
* **Selection** (Appendix A, [Select/Learn.lean](Select/Learn.lean)): as in Algorithm 6, every
  leaf's parts are learned robustly. The paper's tournament between the learned mixtures is
  replaced by a simpler rule: the first leaf all of whose path splits pass their window and size
  checks is selected. On the good event such a leaf exists and each of its parts is one component
  up to few points.
* **Reclustering** ([Select/Pairwise.lean](Select/Pairwise.lean),
  [Select/Recluster.lean](Select/Recluster.lean)): with the learned parameters, every point gets the
  unique label that wins all pairwise tests (spectral or quadratic for centered mixtures, linear
  for a common covariance), in place of the reclustering of [IK22]. The tests' error on the clean
  points depends only on `Δ`, and the corrupted points are counted directly, so the error is
  linear in `ε`.

### The algorithm and its running time

[Assembly/Alg.lean](Assembly/Alg.lean) defines the algorithm as a function on the input (tree,
learning, selection, reclustering) and a list program on rationals that computes it when given a
large enough budget. The `Exec*` files of [Assembly/](Assembly/) implement each stage as such a
program, with sizes capped so that it runs in polynomial time on all inputs, and prove that it
agrees with the stage on well-formed inputs. The machine writes the budget
`g(⌈1/wmin⌉, ⌈Δ⌉) · (|x| + 2)^C` (times `(d + 2)^(C (L² + 1))` for a common covariance) in unary
and runs the program ([Assembly/RunTime.lean](Assembly/RunTime.lean)), with `g` computable.
[Assembly/Main.lean](Assembly/Main.lean) puts the parts together. The constants are explicit but
astronomically large.

## Map of the files

| Files | Content |
| --- | --- |
| [Challenge.lean](Challenge.lean), [Model.lean](Model.lean) | the statements and their definitions |
| [Solution.lean](Solution.lean) | the statements, proved from [Assembly/Main.lean](Assembly/Main.lean) |
| [Common/](Common/) | vectors, matrices, polynomials, the frame of a mixture, Gram factors |
| [SoS/](SoS/) | normed sum-of-squares inequalities |
| [Rounding/](Rounding/) | Section 4: Algorithm 1, the orthogonal-complement system, Theorems 4.1 and 4.2 |
| [Centered/](Centered/) | Section 5.1: the centered system and Theorem 5.6 |
| [IdCov/](IdCov/) | Section 6.1: the moment system for a common covariance and Theorem 6.5 |
| [Robust/](Robust/) | the quadratic filter and certified moments |
| [Prob/](Prob/), [Split/](Split/) | the good event and its probability; window counts of Gaussians |
| [Linalg/](Linalg/) | separation of covariances under congruence |
| [Tree/](Tree/) | the good event on nodes, splits, refinement and the tree |
| [Select/](Select/) | learning, selection, pairwise tests and reclustering |
| [Assembly/](Assembly/) | the schedule, the list programs, the running time and the main theorems |

*Formalized by [Claude Code](https://claude.com/claude-code) and [Codex](https://openai.com/codex/).*
