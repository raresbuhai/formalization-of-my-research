# BB20: Learning restricted Boltzmann machines with sparse latent variables

The main results are [BB20, Theorems 4, 6, 11 and 12], stated in [Challenge.lean](Challenge.lean)
with the definitions of [Model.lean](Model.lean) and proved in [Solution.lean](Solution.lean), with
only the standard axioms; `lake comparator` checks them. Theorem 4 is the key structural result:
when few latent variables touch the neighbourhood of `u`, a small set of neighbours carries a
fixed fraction of the information that a large one does. Theorem 6 learns the neighbourhoods of the
Markov random field of the observed variables in time `poly · (n + 2)^{2^s}`. Theorem 11 learns, with no
dependence on the minimum potential, the neighbours joined by large potentials, and Theorem 12
bounds the prediction error of the regression step built on them. The sample sizes of Theorems 6
and 11 are larger than the paper's, and their running times are polynomial in the input length
(the samples and the bits of the parameter bounds) rather than linear in the number of samples
(see [The statements](#the-statements)).

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v2).

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 4 (Lemma 10) | `nu_subset_bound` | If `I` is a set of MRF neighbours of `u`, and `u`, `I`, `S` are disjoint, then some `I' ⊆ I` with `\|I'\| ≤ 2^s` has `ν_{u,I'\|S} ≥ (4\|I\|)^{-2^s} (1/\|I\|)^{2^s(2^s+1)} ν_{u,I\|S}`. |
| Theorem 6 | `structure_learning` | A Turing machine running in time `poly(\|x\|) · (n + 2)^{2^s}` recovers every MRF neighbourhood with probability at least `1 - ω` from `sampleSize α γ d D s n ω` samples. |
| Theorem 11 | `structure_learning_strong` | With no bound on the minimum potential, a Turing machine running in time `poly(\|x\|) · (n + 2)^{2^s}` finds, for every variable, a set of its MRF neighbours containing all neighbours joined to it by a coefficient of absolute value at least `ζ`, with probability at least `1 - ω` from `sampleSize (ζη) γ d D s n ω` samples. |
| Theorem 12 | `prediction_error` | Given sets of at most `D` variables containing the `ζ`-strong neighbours, with `ζ ≤ √ε / (D^d √(1 + e^{2γ}))`, every near-minimizer of the empirical logistic loss over the `ℓ₁` ball of radius `2γ` predicts every variable with mean squared error at most `ε`, with probability at least `1 - δ`, from `C γ² ln(8 n 2^D / δ) / ε²` samples. |

* **The model** ([Model.lean](Model.lean)): an RBM with `n` observed and `m` latent `±1`
  variables; the observed variables follow its marginal law, a Markov random field whose Fourier
  coefficients are the clique potentials, and the MRF neighbourhood of `u` is the set of
  variables sharing a nonzero coefficient with it. The parameters (minimum potential `α`, width
  `γ`, latent degree `d`, MRF degree `D`, and `s`) enter as bounds.
* **Sample sizes**: explicit, of the form of the paper's, with `δ = σ(-2γ)`, `α²` in place of
  `4α²` and `max(1, C(D, d-1))` in place of `C(D, d-1)` in `τ`, `L = 2^s · 8/τ'²` in place of
  `8/τ'²`, and, for Theorem 11, the paper's `η` multiplied by `δ^{D/2}/√2`. The paper's sample
  sizes do not follow from its analysis, and for Theorem 11 they fail.
* **Algorithms** are deterministic multitape Turing machines (`BB20.RunsInTime`), given `n`, the
  samples as bits, and the parameter bounds. Their time `(|x| + 2)^c (n + 2)^{2^s}` on every input
  is polynomial in the number of samples, in `n` and in the bit lengths of the parameter bounds,
  times `(n + 2)^{2^s}`; the paper counts word-RAM operations.
* **Theorem 12** is stated for fixed estimates of the neighbourhoods (any sets of at most `D`
  variables containing the `ζ`-strong neighbours) and for every near-minimizer of the empirical
  risk, within `ε/4`, with an absolute constant `C`; it states no running time for finding
  such an estimate.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### Basic facts

[Basic.lean](Basic.lean) and [Basic/Cube.lean](Basic/Cube.lean) prove what the other parts share:
the observed law is `P(x) ∝ exp(f(x))` with `f = ∑_S f̂(S) χ_S` (Walsh inversion); the local field
`E_u(x) = ∑_{S ∋ u} f̂(S) χ_{S∖u}(x)` gives `P(X_u = 1 | X_{∖u}) = σ(2E_u)`, with `|E_u| ≤ γ`;
conditional probabilities are at least `σ(-2γ)` per variable; the Markov property; and every
nonzero coefficient on two or more variables lies inside the support of one latent variable.

### Theorem 4

[Structural/Latent.lean](Structural/Latent.lean) writes the marginals of the observed variables as
mixtures over the latent configurations. [Structural/Pattern.lean](Structural/Pattern.lean) writes
the term of each configuration in `ν_{u,I|S}` as a sum, over the at most `2^s` configurations of
the latent variables connected to `I`, of products over `I` of numbers in `[0, 1]`.
[Structural/NonCancel.lean](Structural/NonCancel.lean) proves the non-cancellation lemmas: Lemma
16 by induction, and Lemma 8 by splitting the columns repeatedly into `m + 1` parts of nearly equal
size and a strong induction on their number. [Structural/Pigeonhole.lean](Structural/Pigeonhole.lean)
chooses one subset of `I` of size at most `2^s` for all configurations, by pigeonhole.

### The lower bound on the proxy

[LowerBound.lean](LowerBound.lean) proves the ingredient of Theorem 5 that the paper takes from
Hamilton, Koehler and Moitra: if a coefficient of absolute value at least `κ` joins `u` to a
variable outside `S`, some set of at most `d - 1` neighbours outside `S` has `ν_{u,I|S} ≥ 2τ(κ)`.
The proof is a direct argument for `±1` variables. The quantity `E[E_u (X_u - E[X_u | X_S])]` is
at most `2^d γ max_I ν_{u,I|S}`, term by term in the expansion of `E_u`; and it is at least the
conditional variance of `E_u` over `cosh² γ`, which flipping one variable of the large coefficient
bounds from below ([LowerBound/CondExp.lean](LowerBound/CondExp.lean),
[LowerBound/Field.lean](LowerBound/Field.lean)). The same bound serves Theorem 6 (`κ = α`) and
Theorem 11 (`κ = ζη` and `κ = ζ`).

### The algorithms and their correctness

[Learning/Algorithm.lean](Learning/Algorithm.lean) defines the algorithms as Lean functions: at
each variable `u`, greedy steps that add the first candidate set (in the order of `List.sublists`)
whose empirical proxy is above a threshold, then the pruning step of Theorem 6 or of Theorem 11.
They are parametrized by the computation of their thresholds, and proved correct for every
threshold in `[0.9 τ', τ']`:

* the empirical marginals on at most `L + 2^s + 1` variables are close to the true ones with
  probability at least `1 - ω`, by Hoeffding's inequality and a union bound, and then
  `|ν̂ - ν| ≤ 4 · 2^{|S|} σ`, with no lower bound on probabilities
  ([Learning/Concentration.lean](Learning/Concentration.lean),
  [Learning/Link.lean](Learning/Link.lean));
* the number of greedy additions is bounded with the potential `E[E[X_u | X_S]²] ≤ 1`, which grows
  by at least `4ν²` at each addition ([Learning/Progress.lean](Learning/Progress.lean),
  [Learning/Greedy.lean](Learning/Greedy.lean));
* the pruning step of Theorem 11 removes the non-neighbours through
  `ν_{u,Z|S'} ≤ 2^{|Y|-|Z|} ν_{u,Y|S'}` under conditional independence, and a bound on how much
  removing a non-neighbour from the conditioning set can raise `ν`
  ([Learning/Prune.lean](Learning/Prune.lean));
* [Learning/Bounds.lean](Learning/Bounds.lean) has the constants, and
  [Learning/Correct.lean](Learning/Correct.lean) the two theorems.

### Thresholds and running time

The thresholds ([Machine/ThrDef.lean](Machine/ThrDef.lean), [Machine/ThrSpec.lean](Machine/ThrSpec.lean),
[Machine/ThrPolyTime.lean](Machine/ThrPolyTime.lean)) are rational lower approximations of `τ'`,
within a factor `0.9`, from upper approximations of `e^{2γ}` by Taylor series; every exponent is
capped by a bound on the input length, which the sample size never reaches, so they are computed
in polynomial time.

The running time must be linear in the number of candidate sets, which can be `n^{2^s}`, so a
composition of polynomial-time certificates does not suffice. [Machine/Loop.lean](Machine/Loop.lean)
proves that `a · b^k` rounds of a polynomial-time step run in time `(a b^k + 1) · poly(|x|)`, with
complexitylib's streaming iteration and a unary round count built by repeated unary
multiplication. Each algorithm is one state machine ([Machine/Flat.lean](Machine/Flat.lean)) of
`2n · n · (n + 1)^k` rounds, `k = min(2^s, n)`: the empirical proxy is computed from the sample
patterns rather than all `2ⁿ` configurations ([Machine/EffNu.lean](Machine/EffNu.lean)), and the
first candidate above the threshold is found by a counter in base `n + 1` that keeps the candidate
with the smallest code `∑_{i ∈ I} 2^i`, the order of `List.sublists`
([Machine/Search.lean](Machine/Search.lean)). [Machine/Time.lean](Machine/Time.lean) assembles the
certificates.

### Theorem 12

[Prediction/Logistic.lean](Prediction/Logistic.lean) has Pinsker's inequality and
`KL(σ(a) ‖ σ(t)) ≤ (t - a)²/8` for the Bernoulli divergences that make up the excess risk.
[Prediction/Risk.lean](Prediction/Risk.lean) bounds the prediction error by half the excess risk and
compares with the weights `w̄_T = 2 f̂(T ∪ {u})`, whose excess risk is at most `ε/2`. The uniform
deviation over the `ℓ₁` ball goes through a ghost sample, symmetrization, the Ledoux–Talagrand
contraction in exponential form and Massart's lemma ([Prediction/Contraction.lean](Prediction/Contraction.lean),
[Prediction/Deviation.lean](Prediction/Deviation.lean)); [Prediction/Sample.lean](Prediction/Sample.lean)
applies it to the samples. The constant is `C = 2048`.

## Map of the files

| Files | Content |
| --- | --- |
| [Basic.lean](Basic.lean), [Basic/Cube.lean](Basic/Cube.lean) | The observed law, characters and Walsh inversion, the local field, conditional probabilities, the Markov property. |
| [Structural.lean](Structural.lean), [Structural/](Structural/) | Theorem 4: `Latent` (Lemmas 13, 14), `Pattern` (Lemmas 15, 7, 9), `NonCancel` (Lemmas 16, 8), `Pigeonhole` (Lemma 10). |
| [LowerBound.lean](LowerBound.lean), [LowerBound/](LowerBound/) | The lower bound on `ν`: `CondExp` (conditional expectations given `X_S`), `Field` (flips of the local field). |
| [Learning/Algorithm.lean](Learning/Algorithm.lean) | The algorithms of Theorems 6 and 11 as Lean functions, and the specifications of their thresholds. |
| [Learning/](Learning/) | Their correctness: `Link`, `Concentration`, `Progress`, `Greedy`, `Prune`, `Bounds`, `Correct`. |
| [Machine/Threshold.lean](Machine/Threshold.lean), `Machine/Thr*.lean` | The thresholds and their polynomial-time certificates. |
| [Machine/Loop.lean](Machine/Loop.lean), `Machine/Loop*.lean` | Loops of `a · b^k` rounds in time linear in the number of rounds. |
| [Machine/Time.lean](Machine/Time.lean), `EffNu`, `Search`, `Flat`, `NuPolyTime`, `StepPolyTime`, `RunBounds` | The algorithms as one state machine, its certificates, and the running time. |
| [Prediction.lean](Prediction.lean), [Prediction/](Prediction/) | Theorem 12: `Logistic`, `Risk`, `Contraction`, `Deviation`, `Sample`. |
| [Solution.lean](Solution.lean) | The four theorems from the parts, checked by `lake comparator` ([comparator.json](comparator.json)). |

*Formalized by [Claude Code](https://claude.com/claude-code).*
