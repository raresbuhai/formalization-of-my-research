# BMW26: Efficient recovery of latent coordinate structure from sparse observations of the hypercube

The results are [BMW26, Theorem 1.2] (the main result), Theorem 4.1 (the sum-of-squares FKN
theorem) and Lemma 5.1 (spectral concentration of the percolated hypercube), stated in
[Challenge.lean](Challenge.lean) with the definitions of [Model.lean](Model.lean) and proved in
[Solution.lean](Solution.lean), with only the standard axioms; `lake comparator` checks them.

The formal proof follows the paper's argument in outline, though some of its steps take a
different route (see [below](#how-the-proof-is-implemented)).

Numbers refer to the arXiv version (v1). The paper has no venue yet, so the key uses the arXiv
year.

## The statements

| Result | Lean name | Content |
| --- | --- | --- |
| Theorem 1.2 | `hypercube_recovery` | For every `c` there are `C` and a polynomial-time algorithm that, given a sample of `Q_d(p)` with `p ≥ C log d / d` whose vertices have been renamed, recovers the hidden vectors of all but `2^d / d^c` vertices, up to an automorphism of `Q_d`, with probability `1 - o_d(1)`. |
| Theorem 4.1 | `sos_fkn` | The constraints `∑ᵢ ⟨f, χᵢ⟩² ≥ 1 - δ`, `f(x)² = 1`, `δ ≥ 0` prove `∑ᵢ ⟨f, χᵢ⟩⁴ ≥ 1 - Kδ` in degree `4`, by a proof in which `δ` appears only as the monomial `δ` and whose coefficients are at most `2^(K (d + 1))` in absolute value; also with `δ` replaced by any polynomial of degree at most `2`, by a proof whose coefficients are at most `2^(b + K (d + 1))` when those of that polynomial are at most `2^b`. |
| Lemma 5.1 | `spectral_concentration` | For every `ε > 0` and `C₁, C₂`, if `p ≥ C log d / d`, then with probability at least `1 - 1/d^C₁` some set `R` of at most `2^d / d^C₂` vertices has `|gᵀ(L' - pL)g| ≤ ε p gᵀLg + d² ∑_{x ∈ R} (g x - ḡ)²` for every `g`. |

* **The model** ([Model.lean](Model.lean)): `Q_d(p)` keeps each edge of the hypercube
  independently with probability `p`; the vertices of the sample are renamed by a bijection that
  may be any function of the sample, and the algorithm sees only the renamed graph (its adjacency
  table), not `p`.
* **Recovery** (`BMW26.Recovers`) is up to one automorphism of `Q_d` (a permutation of the
  coordinates and a sign flip of each), and `1/d^O(1)` is `d^(-c)` for every `c`, with `C` and the
  algorithm depending on `c`.
* **Algorithms** are multitape Turing machines with coins, running in time `O((N + 2)^k)` on inputs
  of length `N` (`BMW26.RunsInTime`, as in BKS23 and BBKS24); the probability is over the sample and
  the coins.
* **Theorem 4.1** is stated with the sum-of-squares proofs of
  `Background/SumOfSquares/Proof.lean`, in the variables `f(x)` and `δ`, in two parts. The first
  is the paper's statement with its "`δ` only appears in degree-1 monomials", literally: in every
  term `p_S ∏_{i ∈ S} fᵢ` of the proof, every monomial containing `δ` is `δ`. The second is what
  the clause is used for: `δ` can be replaced by any polynomial of degree at most `2` (Lemma 6.3
  substitutes `δ = (⟨f, Lf⟩ - 2)/2`). The statement also bounds the coefficients of the proof, which the
  paper does not: every coefficient of the constraints, the goal and the multipliers is at most
  `2^(b + K (d + 1))` in absolute value (`b = 0` for `δ`), that is `2^b · poly(n)` with `n = 2^d`.
  This is `SoS.DerivesWithin`, which the background calls bit complexity, but only magnitudes are
  bounded: the coefficients are real, with no bound on the length of an encoding. Such a bound is
  what lets the theorem apply to pseudo-expectations that satisfy the constraints only
  approximately, as those of a solver do.
* **Lemma 5.1** is stated with quadratic forms (`BMW26.lapForm`), for every `ε > 0` and all real
  `C₁, C₂`.

The module doc of [Challenge.lean](Challenge.lean) explains each choice.

## How the proof is implemented

### The algorithm

The algorithm ([Alg/Algorithm.lean](Alg/Algorithm.lean)) solves the degree-`4` sum-of-squares
program of Section 6 (Boolean, balance and cut constraints, with the edge density estimated from
the number of edges and the slack `δ = d^-(c+7)`) with the solver of
[../Background/SumOfSquares](../Background/SumOfSquares/README.md), and rounds its second moments
`M_{uv} = Ẽ[f_u f_v]` without the Ma–Shi–Steurer rounding:

* the program minimizes `∑_{u,v} Ẽ[f_u f_v]²`; the uniform mixture of the coordinate cuts has value
  `n²/d`, so with level-one mass at least `1 - ε'`, `‖M - (1/d) ∑ᵢ χ̂ᵢ χ̂ᵢᵀ‖_F² ≤ 2n²ε'/d + γ`
  ([Round/Moments.lean](Round/Moments.lean));
* for each observed edge `(u, u')` in direction `i`, the sign vector of `M_u - M_{u'}` is close to
  `±χ̂ᵢ`; a greedy clustering of these vectors keeps one per direction
  ([Round/Function.lean](Round/Function.lean), [Round/Correct.lean](Round/Correct.lean)).

The algorithm does not use its coins. Its running time is proved with complexitylib's polynomial
time calculus ([Alg/PolyTime.lean](Alg/PolyTime.lean)).

### The sum-of-squares certificate

[SoS/Main.lean](SoS/Main.lean) proves Lemmas 6.3–6.9 in the form the rounding needs: on a good
sample, the program proves that the level-one Fourier mass is at least `1 - O(δ + τ₀ + ξ)`. The
spectral comparisons enter as quadratic forms with a *diagonal* error `∑ₓ D(x) g(x)²`, which is a
constant on `±1`-valued `g`; a nonnegative quadratic form is a sum of squares (positive
semidefinite matrices factor as `BᵀB`). Polynomial identities are checked at every real point
(`MvPolynomial.funext`). [SoS/FKN.lean](SoS/FKN.lean) proves Theorem 4.1 as one sum-of-squares
identity, with the constant `6`; it uses that `ℓ² - 1` has no Fourier mass on level `1`, in place
of a separate bound on `f̂(∅)`. Its multipliers have coefficients summing to at most `2^(40(d + 4))`
in absolute value; [Paper/FKN.lean](Paper/FKN.lean) carries this bound to the statement, with
`K = 200`, and tracks where `δ` appears: only in `10 (∑ᵢ ⟨f, χᵢ⟩² - (1 - δ))` and `190 δ`.

### Spectral concentration

[Spec/](Spec/) proves Lemma 5.1, in two forms: with a diagonal error of small trace
([Spec/Main.lean](Spec/Main.lean), used by the main theorem), and in the paper's form
([Spec/Paper.lean](Spec/Paper.lean)). The ingredients:

* few vertices of atypical degree (Lemma 5.2, Bernstein's inequality and Markov);
* Lemmas 5.6 and 5.8 on the low-degree functions, by second moments and Markov in place of the
  matrix Bernstein inequality: their space has dimension `k` with `k² ≪ 2^d`;
* Lemma 5.9, by second moments in place of Bernstein's inequality with bounded dependence;
* Lemma 5.3, with the edge isoperimetry of the hypercube, the count of connected sets through
  closed walks, and a union bound; Lemma 5.4 from it with the converse expander mixing lemma of
  Bilu and Linial ([Spec/BiluLinial.lean](Spec/BiluLinial.lean));
* the low- and high-degree parts are put together by Cauchy–Schwarz (in place of a Schur
  complement), on `g` minus its mean for the paper's form.

Bernstein's inequality is TauCeti's (`Imported/TauCeti/Probability/Moments/Bernstein.lean`);
independent coins on a probability space are in [Prob/Coins.lean](Prob/Coins.lean), and
[Prob/Percolation.lean](Prob/Percolation.lean) reads `Q_d(p)`, its half-cubes and its edge counts
on them.

### Assembly

[Assembly.lean](Assembly.lean) puts the parts together: a sample is good (spectral closeness of
`Q_d(p)` and of its `2d` half-cubes, edge counts per direction) with probability at least
`1 - 4/d`, and on a good sample the algorithm succeeds for every renaming and every coin string.
The pseudo-expectation of the solver is moved to the hypercube's variables by the renaming, where
the certificate applies. [Paper/FKN.lean](Paper/FKN.lean) and [Paper/Spectral.lean](Paper/Spectral.lean)
derive the statements of Theorem 4.1 and Lemma 5.1.

## Map of the files

| Files | Content |
| --- | --- |
| [Cube/Basic.lean](Cube/Basic.lean) | Flips, characters, Fourier expansion and Parseval, energies and Laplacians of weighted subgraphs of the hypercube. |
| [Prob/Coins.lean](Prob/Coins.lean), [Prob/Percolation.lean](Prob/Percolation.lean) | Independent coins: second moments, Bernstein, Markov; `Q_d(p)` as coins, half-cubes, edge counts. |
| [Spec/](Spec/) | Lemma 5.1: `Defs`, `BadSet` (5.2), `Discrepancy` (5.3), `BiluLinial` (5.4, 5.5), `LowDegree` (5.6, 5.8), `BadFourier` (5.9), `Deterministic` and `Main` (diagonal form), `Paper` (the paper's form). |
| [SoS/Basic.lean](SoS/Basic.lean), [SoS/FKN.lean](SoS/FKN.lean), [SoS/Main.lean](SoS/Main.lean) | Polynomials of the analysis, Theorem 4.1, Lemmas 6.3–6.9. |
| [Round/](Round/) | The rounding as a function on lists, the second moments, and its correctness. |
| [Alg/](Alg/) | The program as an input of the solver, the algorithm and its correctness relative to the solver, its running time. |
| [Assembly.lean](Assembly.lean), [Paper/](Paper/) | Theorem 1.2, Theorem 4.1 and Lemma 5.1 from the parts. |

*Formalized by [Claude Code](https://claude.com/claude-code).*
