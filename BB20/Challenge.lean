module

public import BB20.Model

/-!
# Results: statements

The key structural result of [BB20] (Theorem 4, in the form of Lemma 10), the guarantee of its
structure-learning algorithm (Theorem 6), and the two results on learning without the minimum
potential (Theorems 11 and 12), with proofs `sorry`. Numbers are those of the arXiv version (v2).

Two differences from the paper's statements stand out:

* **Running times** of the algorithms (Theorems 6 and 11) are polynomial in the length of the
  input (the `M n` bits of the samples and the bits of the parameter bounds; so polynomial in `M`
  and in the paper's `L ≤ log₂ M + 1`), times `(n + 2)^{2^s}`, where the paper's are
  `O(M L n^{2^s + 1})`; see "Running times" below.
* **Sample sizes** of Theorems 6 and 11 are larger than the paper's. The paper's do not follow
  from its analysis, and for Theorem 11 they fail. The dominant terms have the same form, and
  the differences amount to replacing `γ` by `γ + 1` and the paper's `L` by `2^s L` (with a
  smaller `η` in Theorem 11); see the comparisons under Theorems 6 and 11.

What a reader has to trust is this file and what it imports: the definitions in `BB20/Model.lean`
(restricted Boltzmann machines, the induced Markov random field and its parameters, the proxy
`ν`, samples, algorithms and the explicit bounds, prediction), the encodings in
`Background/Encoding.lean`, CSLib's multitape Turing machines, and Mathlib.

## Conventions

* **The model.** An RBM (`BB20.RBM`) has `n` observed and `m` latent `±1` variables, real
  interactions `J` and real external fields `h`, `g`. The observed variables follow the marginal
  law (`BB20.RBM.obsProb`), a Markov random field `P(X = x) ∝ exp(f(x))` whose Fourier
  coefficients `f̂(S)` (`BB20.RBM.fourier`) are the clique potentials. The MRF neighbourhood
  `N(u)` (`BB20.RBM.nbhd`) consists of the variables `i ≠ u` with `f̂(S) ≠ 0` for some
  `S ∋ u, i`.
* **Parameters** enter as bounds, which every RBM satisfies for large enough (or, for `α`, small
  enough) values: `α ≤ |f̂(S)|` for every nonzero `f̂(S)` with `|S| ≥ 2` (`BB20.RBM.MinCoeffGE`),
  width at most `γ` (`BB20.RBM.WidthLE`), latent degree at most `d`
  (`BB20.RBM.LatentDegreeLE`), MRF degree at most `D` (`BB20.RBM.DegreeLE`), and at most `s`
  latent variables connected to each MRF neighbourhood (`BB20.RBM.SparsityLE`). The paper's
  minimum potential `α` is the smallest nonzero `|f̂(S)|`; coefficients on one variable (external
  fields) do not affect neighbourhoods and are not constrained here.
* **Samples** are independent samples of the observed variables (`BB20.RBM.sampleProb`).
* **Algorithms** are deterministic multitape Turing machines (`BB20.RunsInTime`). They read `n`,
  the samples as lists of bits (`true` for `+1`), rational bounds `α` (or `ζ`) and `γ`, and the
  numbers `d`, `D`, `s` (`BB20.Input`). One algorithm serves all RBMs and all parameter values.
  The output lists, for each variable `u`, its estimated neighbourhood (`BB20.outNbhd`).
* **Running times.** The paper's `O(M L n^{2^s + 1})` counts operations in the word RAM, where
  reading a sample's value at a variable and adding or comparing counts up to `M` each take one
  step. A multitape Turing machine pays a polynomial overhead for both: it has to move along the
  input to reach a sample's bits, and the counts take `O(log M)` bits. So the formal statements
  ask for `(|x| + 2)^c · (n + 2)^{2^s}` steps on every input (`BB20.learnTime`), for an absolute
  constant `c`, where `|x|` is the length of the encoded input: the `M n` bits of the samples,
  and the bits of `n` and of the parameter bounds `α` (or `ζ`), `γ`, `d`, `D`, `s`. So the
  bound is polynomial in `M`, in `n` and in the bit lengths of the parameter bounds, times
  `(n + 2)^{2^s}`. Apart from this explicit dependence on `s`, there is no factor depending on
  the values of the parameters. (The bounds `α` (or `ζ`), `γ`, `d` and `D` affect an algorithm
  only through its thresholds, which it needs to constant relative precision, and only when
  `M ≥ 1/τ'²`; for `ω ≤ 1` a smaller sample is below the theorems' sample size, and then the
  output does not matter. `s` also sets the largest size `2^s` of a candidate set.) Compared
  with the paper's bound, this is polynomial instead of linear in `M` and `L`, and it keeps the
  exponent `2^s` of `n`, the point of the paper, with `n + 2` in place of `n`:
  `(n + 2)^{2^s} ≤ e² n^{2^s}` when `2^s ≤ n` (when `2^s > n`, every nonempty set of the
  variables other than `u` and those already chosen is a candidate, and the bound is generous).
  It does not keep
  the paper's precise `n^{2^s + 1}`. The difference between the machine models motivates this
  relaxation; it does not make the two bounds equivalent. At the theorems' sample sizes (with
  `n ≥ 1` and `ω ≤ 1`; for `ω > 1` there is nothing to prove), `L ≤ log₂ M + 1`: the sample size
  is then at least `5 L 16^L`, since `δ ≤ 1/2`, the logarithmic factor is at least `2^s ln 2`,
  and `τ'² = 2^{s+3} / L`. (`L` can be close to `0`, when the bounds given are far from the
  RBM's parameters.)
* Logarithms are natural.

## Theorem 4

[BB20, Theorem 4]: fix an observed variable `u` and sets `I` and `S`, such that all three are
disjoint. Suppose that `I` is a subset of the MRF neighbourhood of `u` and that `|I| ≤ d - 1`.
Then there is a subset `I' ⊆ I` with `|I'| ≤ 2^s` such that
`ν_{u,I'|S} ≥ (4d)^{-2^s} (1/d)^{2^s (2^s + 1)} ν_{u,I|S}`.

Formally (`BB20.nu_subset_bound`):

* **The form of [BB20, Lemma 10]**: the factor is `(4|I|)^{-2^s} (1/|I|)^{2^s (2^s + 1)}`, with
  `|I|` in place of `d`, and `I` may have any size. Since the factor decreases in `|I|`, this
  implies Theorem 4. For `I = ∅` the factor reads `1/0 = 0` in Lean, and the statement is
  `ν_{u,I'|S} ≥ 0`.
* **`ν`** is `BB20.RBM.nu`, and `s` is any bound on the paper's `s`.

## Theorem 6

[BB20, Theorem 6]: fix `ω > 0`. Suppose we are given `M` samples from an RBM, where
`M ≥ 60 · 2^{2L} / (τ'² (e^{-2γ})^{2L})`
`· (log(1/ω) + log(L + 2^s + 1) + (L + 2^s + 1) log(2n) + log 2)` with `L = 8 / τ'²`,
`τ' = (4d)^{-2^s} (1/d)^{2^s (2^s + 1)} τ` and
`τ = ½ · 4α² (e^{-2γ})^{d+D-1} / (d^{4d} 2^{d+1} C(D, d-1) γ e^{2γ})`, with `C(D, d-1)` a
binomial coefficient. Then with probability at least `1 - ω` the algorithm, run from each
observed variable `u`, recovers the MRF neighbourhood of `u`. Each run takes time
`O(M L n^{2^s + 1})`.

Formally (`BB20.structure_learning`):

* **The sample size** (`BB20.sampleSize`) is
  `60 · 2^{2L} / (τ'² δ^{2L}) · (log(1/ω) + log(L + 2^s + 1) + (L + 2^s + 1) log(2n) + log 2)`,
  where
  * `δ = σ(-2γ) = 1 / (1 + e^{2γ})` (`BB20.condLB`), the smallest conditional probability of a
    value of a variable given the values of other variables;
  * `τ = ½ · α² δ^{d+D-1} / (d^{4d} 2^{d+1} max(1, C(D, d-1)) γ e^{2γ})` (`BB20.tau`);
  * `τ' = τ / ((4d)^{2^s} d^{2^s (2^s + 1)})` (`BB20.tauPrime`);
  * `L = 2^s · 8 / τ'²` (`BB20.stepBound`), a bound on the size of the sets of variables the
    algorithm conditions on: it adds sets of at most `2^s` variables at a time.

  It is evaluated at the bounds `α, γ, d, D, s` given to the algorithm, with `α, γ > 0` and
  `d ≥ 1`.
* **Comparison with the paper's sample size.** This sample size is larger than the paper's, which
  does not follow from the paper's analysis. The bound has the form of the paper's, and differs
  from it in four places:
  * `δ = σ(-2γ)` in place of `e^{-2γ}`, in `τ` and in `δ^{2L}`: conditional probabilities can be
    as small as `σ(-2γ) < e^{-2γ}`, which is what the analysis needs `δ` to bound. Since
    `σ(-2γ) ≥ e^{-2γ}/2`, each factor `δ` is at most `2` times smaller;
  * `α²` in place of `4α²` in `τ`: the paper takes `2τ`, the lower bound on `ν_{u,I|S}` for
    some set `I` of at most `d - 1` neighbours, from [HKM17, Theorem 4.6] (Hamilton, Koehler,
    Moitra, NeurIPS 2017, arXiv:1705.11107), whose proof drops a normalizing factor; `α²` is
    what a direct proof for `±1` variables gives;
  * `max(1, C(D, d-1))` in place of `C(D, d-1)`, which differ only when `D < d - 1`, where the
    paper's `τ` is undefined;
  * `L = 2^s · 8 / τ'²` in place of `8 / τ'²`: each step of the algorithm adds a set of up to
    `2^s` variables, so `8 / τ'²` bounds the number of steps, not the size of the set the
    algorithm conditions on, which is what the sample size needs.

  So, when `D ≥ d - 1`, `τ` (and `τ'`) is the paper's divided by `4 (1 + e^{-2γ})^{d+D-1}`,
  which lies between `4` and `2^{d+D+1}` and is close to `4` when `e^{2γ}` is large compared
  with `d + D`; and `L` is the paper's multiplied by `2^s` and by the square of that factor.
* **What stays the same.** The bound is the paper's expression
  `60 · 2^{2L} / (τ'² δ^{2L}) · (log(1/ω) + log(L + 2^s + 1) + (L + 2^s + 1) log(2n) + log 2)`,
  with a different `δ`, `τ` and `L` (`L = 2^s · 8 / τ'²` here, `8 / τ'²` in the paper). So it
  depends on `n` and `ω` in the same way, through `log(1/ω)` and `log(2n)` with coefficients that
  depend only on `α, γ, d, D, s`. Within those coefficients, the differences amount to replacing
  `γ` by `γ + 1` and the paper's `L` by `2^s` times it: when `D ≥ d - 1`, the sample size here is
  at most the paper's expression with `γ + 1` in place of `γ` and `2^s · 8 / τ'²` in place of
  `L`, with `τ'` the paper's at `γ + 1`. This is because `τ` here is at least the paper's `τ`
  with `γ + 1` in place of `γ`, and `δ ≥ e^{-2(γ+1)}`. As `L` is in an exponent, the
  coefficients can still be larger than the paper's by more than a constant factor.
* **Success**: with probability at least `1 - ω` over the samples, the output lists exactly
  `N(u)` for every variable `u` (`BB20.RBM.Recovers`).
* **Running time** `(|x| + 2)^c · (n + 2)^{2^s}` (`BB20.learnTime`) on every input, for an
  absolute constant `c` (see "Running times" above).

## Theorem 11

[BB20, Theorem 11]: fix `ω > 0`. Given `M` samples from an RBM, where `M` is as in Theorem 6 if
`α` were equal to `ζ η` with `η = 1 / (√3 · 2^{D/2 + 2^s} · D^{2^{s-1} (2^s + 2)})`, with
probability at least `1 - ω` the algorithm, run from each observed variable `u`, recovers a subset
of the MRF neighbours of `u` that contains every neighbour connected to `u` through a Fourier
coefficient of absolute value at least `ζ`. Each run takes time `O(M L n^{2^s + 1})`.

Formally (`BB20.structure_learning_strong`):

* **No bound on the minimum potential.** The algorithm is given a rational `ζ > 0` in place of
  `α`, and the RBM is not assumed to satisfy any lower bound on its nonzero coefficients.
* **The sample size** is that of the formal Theorem 6 (`BB20.sampleSize`) with `α = ζ η`, where
  `η = √(δ^D / (6 · 2^{D + 2^{s+1}} · D^{2^s (2^s + 2)}))` (`BB20.eta`) with `δ = σ(-2γ)`. It
  does not depend on the coefficients of the RBM. `D ≥ 1` is assumed, so that `η > 0`.
* **Comparison with the paper's sample size.** Besides the differences listed for Theorem 6,
  `η` is the paper's `η` multiplied by `δ^{D/2} / √2 ≥ e^{-(γ+1) D} / √2`, a factor of the
  same kind as those already in `τ`; the dominant terms keep the form described for
  Theorem 6. With the paper's `η`, the paper's
  algorithm fails, however many samples it gets. Take observed variables `u`, `a`, `i`, a latent
  variable joining `u` and `a` with a tiny weight, another joining `a` and `i` with weight about
  `14` (so `f̂({a, i}) ≈ 13.4`), and `ζ ≈ 1`. If the algorithm adds `i` first, it never adds `a`,
  since given `i` the variable `a` says almost nothing more about `u`; its pruning step then keeps
  `i`, a non-neighbour of `u`, since without `i` the variable `a` says much about `u`. The
  pruning step conditions on `S ∖ {i}` while the first stage only controls conditioning on `S`,
  and the smaller `η` makes up for the difference.
* **Success**: with probability at least `1 - ω`, for every variable `u`, the output contains
  every `ζ`-strong neighbour of `u` (`BB20.RBM.strongNbhd`) and only neighbours of `u`
  (`BB20.RBM.RecoversStrong`).
* **Running time** as in Theorem 6: `(|x| + 2)^c · (n + 2)^{2^s}` for an absolute constant `c`
  (see "Running times" above).

## Theorem 12

[BB20, Theorem 12]: fix `δ > 0` and `ε > 0`. Suppose that we are given neighbourhoods `n(u)`
satisfying the guarantees of Theorem 11 for each observed variable `u`, and `M` samples, with
`M = Ω(γ² ln(8 n 2^D / δ) / ε²)` and `ζ ≤ √ε / (D^d √(1 + e^{2γ}))`. Let `z_u` be the features
`χ_T(X)`, `T ⊆ n(u)`, and `ŵ_u` the weights that minimize the empirical logistic loss
`(1/M) ∑ₖ ln(1 + e^{-y⁽ᵏ⁾ (w · z⁽ᵏ⁾)})` subject to `‖w‖₁ ≤ 2γ`, where `y = X_u`. Then with
probability at least `1 - δ`, for all variables `u`,
`E[(P(X_u = 1 | X_{∖u}) - σ(ŵ_u · z_u))²] ≤ ε`.

Formally (`BB20.prediction_error`):

* **The neighbourhoods** `nb` are fixed before the samples are drawn. For each `u`,
  `u ∉ nb u`, `|nb u| ≤ D`, and `nb u` contains every `ζ`-strong neighbour of `u`. The output of
  Theorem 11 satisfies this, since `|N(u)| ≤ D`, and so does any set of at most `D` variables
  containing the `ζ`-strong neighbours.
* **`Ω(·)`** is an absolute constant `C`: `M ≥ C γ² ln(8 n 2^D / δ) / ε²`.
* **The estimate** is any near-minimizer of the empirical risk (`BB20.IsNearMinimizer`): any `w`
  with `‖w‖₁ ≤ 2γ` whose empirical risk (`BB20.empRisk`) is within `ε/4` of that of every `w'`
  in the ball. Exact minimizers are among them. The weights are functions on sets; only those of
  the subsets of `nb u` count (`BB20.score`, `BB20.l1Norm`). The theorem is about the estimates,
  not their computation: it states no running time for finding a near-minimizer.
* **The error** is `BB20.RBM.predError`, over a fresh sample of the observed variables, with
  `P(X_u = 1 | X_{∖u})` given by `BB20.RBM.condProb`.
* `γ` bounds the width, as in the other theorems, and is used both in the constraint and in the
  sample size; `d` and `D` bound the latent and MRF degrees.
-/

public section

namespace BB20

/-- **Theorem 4** of [BB20], in the form of Lemma 10: if `I` is a set of MRF neighbours of `u`,
and `u`, `I`, `S` are disjoint, then some `I' ⊆ I` with `|I'| ≤ 2^s` satisfies
`ν_{u,I'|S} ≥ (4|I|)^{-2^s} (1/|I|)^{2^s (2^s + 1)} ν_{u,I|S}`. -/
theorem nu_subset_bound {n m : ℕ} (R : RBM n m) (s : ℕ) (hs : R.SparsityLE s) (u : Fin n)
    (I S : Finset (Fin n)) (hI : I ⊆ R.nbhd u) (hu : u ∉ S) (hIS : Disjoint I S) :
    ∃ I' ⊆ I, I'.card ≤ 2 ^ s ∧
      R.nu u I S / ((4 * I.card : ℝ) ^ 2 ^ s * (I.card : ℝ) ^ (2 ^ s * (2 ^ s + 1))) ≤
        R.nu u I' S :=
  sorry

/-- **Theorem 6** of [BB20]: an algorithm running in time `poly(|x|) · (n + 2)^{2^s}` recovers all
MRF neighbourhoods of an RBM with probability at least `1 - ω` from `BB20.sampleSize α γ d D s n ω`
samples. -/
theorem structure_learning :
    ∃ (A : Input → Output) (c : ℕ), RunsInTime encInput encOutput A (learnTime c) ∧
      ∀ (n m : ℕ) (R : RBM n m) (α γ : ℚ) (d D s : ℕ), 0 < α → 0 < γ → 1 ≤ d →
        R.MinCoeffGE α → R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → R.SparsityLE s →
        ∀ (ω : ℝ) (M : ℕ), 0 < ω → sampleSize α γ d D s n ω ≤ M →
          1 - ω ≤ R.sampleProb M fun X ↦ R.Recovers (A ⟨n, sampleList X, α, γ, d, D, s⟩) :=
  sorry

/-- **Theorem 11** of [BB20]: without any bound on the minimum potential, an algorithm running in
time `poly(|x|) · (n + 2)^{2^s}` finds, with probability at least `1 - ω` from
`BB20.sampleSize (ζ η) γ d D s n ω` samples, for every variable a set of its MRF neighbours that
contains all its `ζ`-strong neighbours. -/
theorem structure_learning_strong :
    ∃ (A : Input → Output) (c : ℕ), RunsInTime encInput encOutput A (learnTime c) ∧
      ∀ (n m : ℕ) (R : RBM n m) (ζ γ : ℚ) (d D s : ℕ), 0 < ζ → 0 < γ → 1 ≤ d → 1 ≤ D →
        R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → R.SparsityLE s →
        ∀ (ω : ℝ) (M : ℕ), 0 < ω → sampleSize (ζ * eta γ D s) γ d D s n ω ≤ M →
          1 - ω ≤ R.sampleProb M fun X ↦
            R.RecoversStrong ζ (A ⟨n, sampleList X, ζ, γ, d, D, s⟩) :=
  sorry

/-- **Theorem 12** of [BB20]: given, for every variable `u`, a set of at most `D` variables
containing its `ζ`-strong neighbours, with `ζ ≤ √ε / (D^d √(1 + e^{2γ}))`, and
`M ≥ C γ² ln(8 n 2^D / δ) / ε²` samples, with probability at least `1 - δ` every near-minimizer of
the empirical logistic loss over the `ℓ₁` ball of radius `2γ` predicts every variable with error at
most `ε`. -/
theorem prediction_error :
    ∃ C : ℝ, ∀ (n m : ℕ) (R : RBM n m) (γ : ℝ) (d D : ℕ) (ζ ε δ : ℝ),
      R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → 0 < ζ → 0 < ε → 0 < δ →
      ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))) →
      ∀ nb : Fin n → Finset (Fin n),
        (∀ u, u ∉ nb u ∧ (nb u).card ≤ D ∧ R.strongNbhd ζ u ⊆ nb u) →
      ∀ M : ℕ, C * γ ^ 2 * Real.log (8 * n * 2 ^ D / δ) / ε ^ 2 ≤ M →
        1 - δ ≤ R.sampleProb M fun X ↦ ∀ (u : Fin n) (w : Finset (Fin n) → ℝ),
          IsNearMinimizer γ (ε / 4) u (nb u) X w → R.predError u (nb u) w ≤ ε :=
  sorry

end BB20
