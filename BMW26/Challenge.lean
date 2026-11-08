module

public import BMW26.Model

/-!
# Results: statements

The main result of [BMW26] (Theorem 1.2), its sum-of-squares FKN theorem (Theorem 4.1) and its
spectral concentration lemma (Lemma 5.1), with proofs `sorry`. `lake comparator` checks that
`Solution.lean` proves exactly these statements using only the axioms listed in `comparator.json`.

What a reader has to trust is this file and what it imports: the definitions in
`BMW26/Model.lean` (the percolated hypercube, renamings, recovery, randomized algorithms, the FKN
system, Laplacian forms), the encodings in `Background/Encoding.lean`, the sum-of-squares proofs of
`Background/SumOfSquares/Proof.lean`, CSLib's multitape Turing machines, and Mathlib.

## Theorem 1.2

Numbers are those of the arXiv version (v1).

[BMW26, Theorem 1.2]: for a sufficiently large absolute constant `C` and `p ≥ C log d / d`, there
is a `poly(n)`-time algorithm that takes as input an arbitrarily renamed sample `G = (V, E)` from
`Q_d(p)` and outputs an embedding `ẑ : V → {±1}^d`. With probability `1 - o_d(1)`, the recovered
vectors `ẑ(v)` agree exactly with the hidden vectors `z(v)` on all but a `1/d^O(1)` fraction of
the vertices, up to a common permutation of the coordinates and a common choice of sign for each
coordinate. Here `n = 2^d` is the number of vertices.

Formally (`BMW26.hypercube_recovery`):

* **The model.** The sample `H` is drawn from `Q_d(p)` (`BMW26.percolationProb`), and its vertices
  are renamed `0, …, 2^d - 1` by a bijection `ren H` (`BMW26.Renaming`). The renaming may be any
  function of the sample, so the guarantee holds also when it is chosen after seeing the sample.
* **The input** is the renamed graph alone (`BMW26.observed`), encoded by its number of vertices
  and its adjacency table. The algorithm is not given `p`, as in the paper, whose algorithm
  estimates `p` from the number of edges.
  * `p` is any real number with `C log d / d ≤ p ≤ 1` and may depend on `d`: one algorithm, one
    `δ` and one threshold for "large enough `d`" serve every `p`. The constant `C` is positive, so
    for `d ≥ 2` every such `p` lies in `(0, 1]`. Logarithms are natural; the base only changes
    `C`.
* **The output** is one list of bits for each vertex, read as a vector of `d` bits
  (`BMW26.outVec`).
* **Agreement up to the symmetries of `Q_d`** (`BMW26.Recovers`): there are a permutation `π` of
  the coordinates and signs `s` such that `BMW26.cubeAut π s` maps the recovered vector of `v` to
  its hidden vector for all but at most `2^d / d^c` vertices `v`.
* **`1/d^O(1)`** is `d^(-c)` for every exponent `c`, with the algorithm and `C` depending on `c`.
  `C` has to grow with `c`: for `p = C log d / d`, about a `(1 - p)^d ≈ d^(-C)` fraction of the
  vertices are isolated, and nothing in the graph tells their hidden vectors apart.
* **Probability `1 - o_d(1)`**: `δ` is a function of `d` tending to `0`. The probability is over
  the sample and the algorithm's coins (`BMW26.successProb`), and the bound holds for all large
  enough `d`, every `p` in the range and every renaming.
* **Running time `poly(n)`**: `A` runs in time `O((N + 2)^k)` on inputs of encoded length `N`
  (`BMW26.RunsInTime` with `T N = (N + 2)^k`), for a natural number `k`. The input has length
  `4^d + O(d)`, so this is `n^O(k)`.
  * The time bound is an explicit polynomial, not any function bounded by one: the algorithm is
    given exactly `T N` coins and may read them all, so the length of its coin string would pass
    it `T N`, which for an arbitrary `T` could be advice no machine computes.

## Theorem 4.1

[BMW26, Theorem 4.1] (sum-of-squares FKN): for the system `𝒫` of the constraints
`∑ᵢ ⟨f, χᵢ⟩² ≥ 1 - δ`, `f(x)² = 1` for every `x ∈ {±1}^d`, and `δ ≥ 0`, in the variables `f(x)` and
`δ`, there is a degree-`4` sum-of-squares proof that `𝒫` implies `∑ᵢ ⟨f, χᵢ⟩⁴ ≥ 1 - O(δ)`.
Furthermore, `δ` only appears in the proof as part of degree-`1` monomials.

Formally (`BMW26.sos_fkn`), in two parts with one constant `K`:

* **The system** is `BMW26.fknSystem q`, in the variables `f(x)` and `δ` (`BMW26.FKNVar`), with `δ`
  replaced by a polynomial `q`. With `q = δ` (the variable `X none`) it is the paper's system.
* **Sum-of-squares proofs** are those of `Background/SumOfSquares/Proof.lean` (`SoS.Proof`):
  `g = ∑_S p_S ∏_{i ∈ S} fᵢ` for sums of squares `p_S`, with `deg p_S + ∑_{i ∈ S} deg fᵢ ≤ 4`. The
  products `p_S ∏_{i ∈ S} fᵢ` are the *terms* of the proof.
* **First part: the theorem with its "furthermore", literally.** For the paper's system there is a
  proof `P` of `∑ᵢ ⟨f, χᵢ⟩⁴ ≥ 1 - K δ` in which every monomial containing `δ`, in every term, is
  `δ` itself. This reads "degree-`1` monomials" as monomials of total degree `1`; it implies the
  weaker reading, degree `1` in `δ`. The condition is on each term, so `δ` cannot hide in terms
  that cancel, and it keeps `δ` out of the squares that make up the multipliers, since a square
  containing `δ` would contain `δ²`.
* **Second part: the "furthermore" as the paper uses it.** `δ` can be replaced by any polynomial
  `q` of degree at most `2`, such as `(⟨f, L f⟩ - 2)/2` in [BMW26, Lemma 6.3], and there is still
  a proof of degree `4`. Substituting `q` for `δ` in a proof as in the first part gives one; the
  statement asserts only that one exists for each `q`.
* **`O(δ)`** is `K δ`, and `K q` in the second part, for one constant `K`, the same for every `d`
  and `q`.
* **The coefficient bound.** Every coefficient of the constraints, of
  `∑ᵢ ⟨f, χᵢ⟩⁴ - (1 - K q)` and of the multipliers `p_S` is at most `2^B` in absolute value, with
  `B = b + K (d + 1)`, when every coefficient of `q` is at most `2^b` (`SoS.CoeffsLE`; `b = 0` for
  `q = δ`, as in the first part). This is `SoS.Proof.BitComplexityLE` and `SoS.DerivesWithin`,
  which the background calls bit complexity, but it bounds magnitudes only: the coefficients are
  real numbers, with no bound on the length of an encoding of them or of the polynomials being
  squared, and nothing says how to find the proof. With
  `n = 2^d` the number of points of the cube, the coefficients are at most `2^b · poly(n)`. The
  paper states no such bound. It is the size that approximate soundness pays for
  (`SoS.PseudoExpectation.ApproxSatisfies.apply_derivesWithin`): it lets the theorem apply to
  pseudo-expectations that satisfy the constraints only approximately, as those of a solver do.

## Lemma 5.1

[BMW26, Lemma 5.1] (spectral concentration of the percolated hypercube): fix `ε ∈ (0, 1/10)`,
`C₁ ≥ 1` and `C₂ ≥ 20`. For `d` large enough and `C log d / d ≤ p ≤ 1` with `C = C(ε, C₁, C₂)`,
with probability at least `1 - 1/d^C₁` there is a set `R ⊆ {±1}^d` with `|R| ≤ 2^d / d^C₂` and
`-ε p L - d² P_{>0} Π_R P_{>0} ⪯ L' - p L ⪯ ε p L + d² P_{>0} Π_R P_{>0}`, where `L` and `L'` are
the Laplacians of `Q_d` and of the sample `Q_d'`, `P_{>0}` the projection orthogonal to the
constant functions and `Π_R` the diagonal projection on `R`.

Formally (`BMW26.spectral_concentration`):

* **The matrix inequalities** are stated through quadratic forms, for every `g : {±1}^d → ℝ`:
  `gᵀ L_H g = ∑_{xy ∈ E(H)} (g x - g y)²` (`BMW26.lapForm`), and
  `gᵀ P_{>0} Π_R P_{>0} g = ∑_{x ∈ R} (g x - ḡ)²` with `ḡ` the mean of `g`. The two-sided
  inequality is one inequality with an absolute value.
* **The parameters** are any `ε > 0` and any real `C₁`, `C₂` (the paper's lower bounds on them are
  not needed), and `C` and the threshold for "large enough `d`" depend on them.
* **The probability** is over `Q_d(p)` (`BMW26.percProb`).
-/

public section

namespace BMW26

open Filter Topology

/-- **Theorem 1.2** of [BMW26]: for every `c`, there are a constant `C` and a randomized
polynomial-time algorithm that, given a sample of the percolated hypercube `Q_d(p)` with
`p ≥ C log d / d` whose vertices have been arbitrarily renamed, recovers the hidden vectors of all
but `2^d / d^c` vertices, up to a symmetry of `Q_d`, with probability `1 - o_d(1)`. -/
theorem hypercube_recovery :
    ∀ c : ℕ, ∃ (A : Graph × List Bool → Output) (k : ℕ), RunsInTime A (fun N ↦ (N + 2) ^ k) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ d : ℕ in atTop, ∀ p : ℝ, C * Real.log d / d ≤ p → p ≤ 1 →
          ∀ ren : SimpleGraph (Cube d) → Renaming d,
            1 - δ d ≤ successProb d p ren A (fun N ↦ (N + 2) ^ k) (2 ^ d / (d : ℝ) ^ c) :=
  sorry

open MvPolynomial in
/-- **Theorem 4.1** of [BMW26], the sum-of-squares FKN theorem: the constraints
`∑ᵢ ⟨f, χᵢ⟩² ≥ 1 - δ`, `δ ≥ 0` and `f(x)² = 1` prove `∑ᵢ ⟨f, χᵢ⟩⁴ ≥ 1 - K δ` in degree `4`, by a
proof whose coefficients are at most `2^(K (d + 1))` in absolute value and in which `δ` appears in
each term only as the monomial `δ`; and when `δ` is replaced by any polynomial `q` of degree at most
`2`, there is still such a proof of degree `4`, whose coefficients are at most `2^(b + K (d + 1))`
when those of `q` are at most `2^b`. -/
theorem sos_fkn :
    ∃ K : ℝ,
      (∀ d : ℕ, ∃ P : SoS.Proof (fknSystem (X none : MvPolynomial (FKNVar d) ℝ))
          (∑ i, fourierCoeff i ^ 4 - (1 - C K * X none)) 4,
        P.BitComplexityLE (K * (d + 1)) ∧
          ∀ S, ∀ m ∈ (P.mult S * SoS.System.prod (fknSystem (X none : MvPolynomial (FKNVar d) ℝ))
            S).support, m none ≠ 0 → m = Finsupp.single none 1) ∧
      ∀ (d b : ℕ) (q : MvPolynomial (FKNVar d) ℝ), q.totalDegree ≤ 2 →
        SoS.CoeffsLE q (2 ^ b) →
          SoS.DerivesWithin (fknSystem q) 4 (b + K * (d + 1))
            (∑ i, fourierCoeff i ^ 4 - (1 - C K * q)) :=
  sorry

/-- **Lemma 5.1** of [BMW26], spectral concentration of the percolated hypercube: with probability
at least `1 - 1/d^C₁`, there is a set `R` of at most `2^d / d^C₂` vertices such that
`|gᵀ (L' - p L) g| ≤ ε p gᵀ L g + d² ∑_{x ∈ R} (g x - ḡ)²` for every `g`. -/
theorem spectral_concentration :
    ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ p : ℝ,
      C * Real.log d / d ≤ p → p ≤ 1 →
        1 - 1 / (d : ℝ) ^ C₁ ≤ percProb d p fun H ↦ ∃ R : Finset (Cube d),
          (R.card : ℝ) ≤ 2 ^ d / (d : ℝ) ^ C₂ ∧ ∀ g : Cube d → ℝ,
            |lapForm H g - p * lapForm (cube d) g| ≤
              ε * p * lapForm (cube d) g + (d : ℝ) ^ 2 * ∑ x ∈ R, (g x - (∑ y, g y) / 2 ^ d) ^ 2 :=
  sorry

end BMW26
