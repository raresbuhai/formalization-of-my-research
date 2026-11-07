# Sum of squares: design notes

The main result is the sum-of-squares algorithm, stated in [Solver.lean](Solver.lean) and proved
as `SoS.Solver.exists_solver` ([Algorithm/Correct.lean](Algorithm/Correct.lean)): one multitape
Turing machine that, for every
feasible, explicitly bounded system of polynomial constraints, even degree `ℓ ≥ 2` and accuracies
`η, γ > 0`, outputs the pseudo-moments of a degree-`ℓ` pseudo-distribution that satisfies the
constraints `(η + γ)`-approximately and whose objective is within `γ` of every pseudo-distribution
satisfying them `η`-approximately, in time `n^O(ℓ)`, polynomial in the bits of the problem and
polylogarithmic in `1/η` and `1/γ`.

This library formalizes the sum-of-squares (SoS) method as it is used in algorithm design: SoS
proofs, pseudo-distributions, their soundness, and the SoS algorithm with its bit complexity on
Turing machines. It is shared by several papers in this repository and imports Mathlib, CSLib
(for Turing machines) and other `Background` modules (for encodings and the ellipsoid method).

**What is proved.** Definitions, the calculus of SoS proofs, pseudo-distributions, soundness
(exact and approximate, with bit complexity), Cauchy–Schwarz, reweighting, and the algorithm (see
[Proving the solver](#proving-the-solver)).

| File | Contents |
| --- | --- |
| [Basic.lean](Basic.lean) | Sums of squares, coefficient sizes, coefficient norms |
| [SumSq.lean](SumSq.lean) | A real sum of squares of degree `≤ ℓ` is a sum of squares of polynomials of degree `≤ ℓ/2` |
| [Proof.lean](Proof.lean) | Systems, SoS proofs, `A ⊢[k] g`, `A ⊢[k, B] g` |
| [Calculus.lean](Calculus.lean) | Building proofs: assumptions, sums of squares, sums, products, multiplying by sums of squares, equality constraints, substitution, composition |
| [PseudoExpectation.lean](PseudoExpectation.lean) | Pseudo-expectations and pseudo-distributions, and their equivalence; exact and approximate satisfaction |
| [Facts.lean](Facts.lean) | Cauchy–Schwarz, reweighting, soundness |
| [Solver.lean](Solver.lean) | The specification of the algorithm: an approximately optimal, approximately feasible degree-`ℓ` pseudo-distribution, computed by a Turing machine in time `n^O(ℓ)`; proved in [Algorithm/Correct.lean](Algorithm/Correct.lean) |
| [Approximate.lean](Approximate.lean) | Approximate soundness: from `η`-approximate satisfaction and a proof of bit complexity `B`, `Ẽ[h g] ≥ -η ‖h‖₂ 2^O(…)`; coefficient norms; counting monomials |
| [Normed.lean](Normed.lean) | Real proofs with `‖·‖₁` bounds on their multipliers (`A ⊢ g` as `DerivesN`, `A ⊢ q = 0` as `DerivesEq`); equalities multiplied by any polynomial; norms bound bit complexity; norm bounds as powers `W^e`; approximate soundness `Ẽ g ≥ -η M ∏ᵢ (1 + ‖fᵢ‖₂)` (`DerivesN.approx_ge`) |
| [Mixture.lean](Mixture.lean) | Mixtures `(1 - t) Ẽ + t Ẽ'` of pseudo-expectations, and their approximate satisfaction |
| [Boolean.lean](Boolean.lean) | Boolean variables: `x_S² = x_S`, `x_S ≥ 0`, `x_S x_T ≥ 0`, products of literals `xᵢ`, `1 - xᵢ` are nonnegative, and `(∑_{i ∈ U} xᵢ)^t = ∑_m m! S(t, m) e_m`, with explicit norms |
| [Moments.lean](Moments.lean) | Moments and Riesz functionals; pseudo-expectations from their moments; approximate satisfaction as a semidefinite condition (distance to a positive semidefinite moment sequence, by cone duality); constant constraints; moments bounded by an explicit ball constraint |
| [GridMoments.lean](GridMoments.lean) | The uniform distribution on the grid `{0, …, d}ⁿ`: rational moments, and a moment matrix with smallest eigenvalue at least an explicit `λ > 0` (by interpolation with the inverse Vandermonde matrix) |
| [Lifted.lean](Lifted.lean) | The algorithm stated mathematically: the set it searches (moments and auxiliary sequences, relaxed by `τ` and boxed), the lift of every competitor into it, a ball around every lift, the Lipschitz objective, and the output after mixing with the grid moments |
| [PDTest.lean](PDTest.lean) | An exact positive definiteness test by determinants and adjugates, which otherwise returns a witness `v ≠ 0` with `vᵀAv ≤ 0`; it commutes with `ℚ → ℝ` |
| [Separation.lean](Separation.lean) | Moment matrices (`MinEigGE` is `M + τI ⪰ 0`), the gradients of moment functionals, and a valid cut for every failed test: box, positive semidefiniteness of the moments and of each auxiliary sequence, distance; the objective cut |
| [Algorithm/](Algorithm/) | The algorithm on lists of rationals, its polynomial-time certificates, and its correctness; `SoS.Solver.exists_solver` (see [Proving the solver](#proving-the-solver)) |

## How bit complexity is handled

In algorithmic uses of SoS, the algorithm only ever computes pseudo-distributions, by solving the
moment SDP approximately. SoS proofs appear only in the analysis, through soundness. Their "bit
complexity" matters for one reason: the solver's pseudo-distribution satisfies the constraints
only up to an error `η`, and soundness survives that error only if the proof's coefficients are
not too large [O'Donnell 2017; Raghavendra–Weitz 2017]. So this library follows [RW17]:

- **SoS proofs have real coefficients**, and "bit complexity at most `B`" means every coefficient
  (of the constraints, of `g` and of the multipliers) is at most `2^B` in absolute value. The
  usual rational bit count bounds the logarithm of every coefficient, so bounds in that measure
  imply these.
- **Rational numbers and bit lengths appear only where a Turing machine sees numbers:** the input
  system, the output pseudo-moments, and the running time of the solver.
- **No exact rational certificates.** They belong to verified computation (checking a certificate
  exactly), which none of the algorithmic statements need. Even certification results can be
  stated on the pseudo-distribution side: the algorithm outputs the SDP's bound.

## Representation choices

1. **Polynomials** are Mathlib's `MvPolynomial σ K`, with variables `σ` (usually `Fin n`) and
   coefficients in a field `K` inside `ℝ`: `ℝ` in the analysis, `ℚ` for the input of an
   algorithm. Degree is `totalDegree`.
2. **"Sum of squares" means a sum of squares of real polynomials** (`SoS.IsSOS`).
3. **SoS proofs are data** (`SoS.Proof A g k`): one multiplier `p S` for each set `S` of
   constraints, with `g = ∑ S, p S * ∏ i ∈ S, fᵢ` and `deg (p S) + ∑ i ∈ S, deg fᵢ ≤ k` for
   every nonzero `p S`. (For nonzero multipliers this is the usual `deg (p S ∏ fᵢ) ≤ k`; zero
   multipliers are unconstrained.) `A ⊢[k] g` says a
   proof exists, and `A ⊢[k, B] g` that one exists with bit complexity at most `B`.
4. **Systems are lists of inequalities `f ≥ 0`.** An equality `h = 0` is the pair `h ≥ 0`,
   `-h ≥ 0`. [Normed.lean](Normed.lean) derives `q h = 0` from the pair for every polynomial `q`
   (`SoS.DerivesEq.mul`), at degree `2 deg q`.
5. **Pseudo-expectations are linear functionals** on real polynomials (`SoS.PseudoExpectation σ ℓ`)
   with `Ẽ 1 = 1` and `Ẽ (f * f) ≥ 0` when `deg f ≤ ℓ/2`. Pseudo-distributions in the usual sense
   (finitely supported `D : ℝⁿ → ℝ`) are also defined, and two statements show the notions agree on
   polynomials of degree at most `ℓ`, so nothing is lost.
6. **"poly(…)" and "O(…)" bounds** are explicit, with constants uniform over all parameters. For
   example, a bound `poly(B, d)` becomes `∃ K k, … ≤ K (B + d + 1)^k`.
7. **Facts about indeterminates** stay that way: an inequality in variables `f₁, …, fᵣ` is
   proved in those variables, and `SoS.Derives.subst` applies it to concrete polynomials.
8. **Constant constraints** (`c ≥ 0` for a constant `c`) are allowed. Exact soundness handles
   them by factoring them out; approximate soundness needs degree `0` or no constant constraints,
   since an approximate inequality can't be divided by a constant.

## Proving the solver

`SoS.Solver.exists_solver` is proved in the parts below. The method is the standard one (Shor, Nesterov,
Parrilo, Lasserre; the ellipsoid method of Grötschel–Lovász–Schrijver), but its bit complexity is
subtle [O'Donnell 2017; RW17; Gribling–Polak–Slot 2023], and no source writes out a complete proof
of this version, so the parts assemble one.

| Files | Content |
| --- | --- |
| [Moments.lean](Moments.lean) | The moment formulation. Approximate satisfaction of each set `S` of nonconstant constraints is a semidefinite condition on the moments `y`, with an auxiliary moment sequence `w_S`, so the algorithm optimizes over a convex set described by semidefinite and Euclidean-norm constraints. The explicit ball constraint bounds that set. |
| [GridMoments.lean](GridMoments.lean) | A distribution with a well-conditioned moment matrix: uniform on the grid `{0, …, ℓ / 2}ⁿ`, with smallest eigenvalue at least `λ`, `log (1/λ) = O(n ℓ² log ℓ + ℓ log n)`. Mixing it in makes the output exactly positive semidefinite (`SoS.MinEigGE.isPSD_add_smul`), and it converts the algorithm's slack into the distances of the moment formulation. Its moments are products of power sums, so the algorithm computes them without listing the grid. |
| [../Ellipsoid.lean](../Ellipsoid.lean) | The ellipsoid method with rounding: the step with slack `σ = 1/(4n)` that absorbs entrywise rounding errors `δ`, containment of the half-ellipsoid, `det` shrinking by `1 - 3σ/4` per step (via monotonicity of `det` in the Loewner order), eigenvalue bounds `λ/4^k ≤ P_k ≤ 2^k Λ`, and the iteration. Ellipsoids are defined by `(uᵀ(x - c))² ≤ uᵀPu`, so no inverses appear. |
| [Lifted.lean](Lifted.lean) | The algorithm, mathematically, with `Ellipsoid.exists_feasible_le`. The set `InSet A ℓ η τ R`: moment matrices `⪰ -τ`, localized moments within `η ∏ ‖fᵢ‖₂` of auxiliary sequences, coordinates at most `R`. Every competitor lifts into it with `τ = 0` (`exists_lift`); everything within `ρ` of a lift is in the relaxed set with `η + γ/2` and `τ = ρ (n + 1)^ℓ` (`mem_of_near`); the objective is Lipschitz (`abs_obj_sub_le`); the ellipsoid method with objective cuts finds a feasible center at least as good as any point with a ball around it; mixing that center with the grid moments gives an exact pseudo-expectation satisfying the constraints up to `η + γ` (`output`) with almost the same objective (`abs_obj_mix_sub_le`). |
| [PDTest.lean](PDTest.lean), [Separation.lean](Separation.lean) | The separation oracle. Positive definiteness of `M + τI` is tested by peeling off the last row: with `d = det B`, `u = adj(B) b`, `s = c d - bᵀu`, either `s ≤ 0` and `(-u, d)` is a witness, or `d² vᵀAv = (dw + yu)ᵀB(dw + yu) + d s y²` shows `A` positive definite. Only determinants and adjugates are computed, so numbers stay as large as minors. Each failed test gives a cut (`validAnswer_of_box`, `validAnswer_of_psd`, `validAnswer_of_psd_aux`, `validAnswer_of_dist`), passing all tests certifies membership (`validAnswer_none`), and the objective is cut by its gradient (`objective_cut`). Points are declared feasible for `τ` and cuts keep the set for `τ/2`; `Ellipsoid.exists_feasible_le` allows this. |
| [Algorithm/](Algorithm/) | Turing machines, through complexitylib's polynomial-time calculus (plain Lean functions on `ℕ`, `ℤ`, `ℚ` and lists, certified by `fun_prop`/`polytime`, folds and iterations with size bounds). See [below](#turing-machines-in-detail). |
| [Algorithm/Correct.lean](Algorithm/Correct.lean) | Assembly. For a valid problem the budget cuts nothing (`ctx_eq`), and every quantity of the argument lies between `2^-Z` and `2^(Z²)` for the size `Z = \|x\| + L + 4`. The parameters are powers of `2`: `R = 2^(3Z²+1)`, `τ = 2^(-16Z⁴)`, `t = 2^(-8Z²)`, the starting ball `s = 2^(8Z²)`, the ball radius `ρ = 2^(-32Z⁴)` around each lifted competitor, `K = 6N²(64Z⁴ + 8Z² + 1)` steps, precision `2^-(2K + 3N + 16)` and clamp `2^(2K + 1 + 8Z²)`. `Ellipsoid.exists_feasible_le` runs on the algorithm's own trajectory (`exists_good`); its steps may assume the eigenvalue and drift bounds at their start, which show that the clamps never act. The problem's feasible point gives a competitor, so a center is declared feasible; the best one (`best_good`), mixed with the grid moments, is the output (`core_correct`). With no coordinates (`n = 0`), every point is the lift of every competitor. |

### Turing machines in detail

The algorithm is a function `core (x, L)` of the input and a *budget* `L` in unary: every loop
runs at most `L` times, every list is cut at length `L`, and every number is clamped to `poly(L)`
bits. Then `core` is polynomial-time on all inputs, and with the budget `(|P| + 2)^(ℓ + 1)` none
of the cuts happens, so it computes the true answer.

| Files | Content |
| --- | --- |
| [Algorithm/Padding.lean](Algorithm/Padding.lean) | The budget: if `core` is polynomial-time, then `x ↦ core (x, (\|P\| + 2)^(ℓ + 1))` runs within `timeBound C` (`SoS.Solver.exists_computableInTimeAndSpace_of_budget`). The budget is written in unary in time polynomial in itself. |
| [../PolyTime/Rat.lean](../PolyTime/Rat.lean) | Rational arithmetic: `+ - * ⁻¹ /`, `≤ <`, casts, floor, and sums of lists (over the common denominator `∏ dᵢ`, so that only integer arithmetic is iterated), as `fun_prop` rules over `Encoding.encRat`. |
| [Algorithm/PDTestRows.lean](Algorithm/PDTestRows.lean), [Algorithm/PDTestRat.lean](Algorithm/PDTestRat.lean) | The positive definiteness test on lists. `PDTest.test_eq_find` unrolls the recursive test: it stops at the first leading block with `s ≤ 0`. [Algorithm/PDTestRows.lean](Algorithm/PDTestRows.lean) computes that on integer matrices with complexitylib's polynomial-time determinant `Cslib.Circuits.Rational.detRows` and Cramer's rule, proves it equal to `PDTest.test`, correct, and polynomial-time; [Algorithm/PDTestRat.lean](Algorithm/PDTestRat.lean) runs it on rational matrices scaled by the product of their denominators. |
| [Algorithm/Monomials.lean](Algorithm/Monomials.lean), [Algorithm/RawPoly.lean](Algorithm/RawPoly.lean), [Algorithm/Coords.lean](Algorithm/Coords.lean) | Polynomials and coordinates. [Algorithm/Monomials.lean](Algorithm/Monomials.lean): the exponent vectors of length `n` and degree at most `D`, each once (`Mono.all`), at most `(n + 1)^D` of them, budgeted (`Mono.allB`). [Algorithm/RawPoly.lean](Algorithm/RawPoly.lean): coefficients, degrees (capped at `ℓ + 1`, since exponents are binary), Riesz functionals and squared norms of raw polynomials term by term, shifts, and products of constraints as budgeted lists of one term from each factor (`sectB`), so that rational sizes only add. [Algorithm/Coords.lean](Algorithm/Coords.lean): sets of constraints as indicator vectors, the coordinate list and its equivalence with `Lifted.Coord`, the moments of a point, and cuts as sparse vectors made dense. |
| [Algorithm/Oracle.lean](Algorithm/Oracle.lean) | The oracle on lists. Every test gives a list of cuts, empty if it passes; the oracle declares the center feasible exactly when there is none. Every cut is valid (`validAnswer_of_mem_cuts`), no cut means the center is in the set (`inSet_of_cuts_eq_nil`), and the objective cut keeps the better points (`oracle_spec`). |
| [Algorithm/Loop.lean](Algorithm/Loop.lean) | The ellipsoid loop. The step avoids `√(aᵀPa)` by `(Pa)ᵢ/√(aᵀPa) = sign((Pa)ᵢ) √((Pa)ᵢ²/aᵀPa)`, with an integer square root; every number is rounded down to a multiple of `2^-p` and clamped. The step is within `2/2^p` of the exact one when the clamps do not act (`stepL_spec`), and keeps the shape symmetric. The loop remembers the best center declared feasible (`best_spec`); [../Ellipsoid.lean](../Ellipsoid.lean) bounds the step (`abs_stepCenter_sub_le`, `abs_stepShape_le`). |
| [Algorithm/Core.lean](Algorithm/Core.lean), [Algorithm/PolyTime.lean](Algorithm/PolyTime.lean) | `core` and its certificate (`core_polytime`). The loop's states stay small: every number is a multiple of `2^-p` at most `2^b` (`length_encState_le`). |

*Formalized by [Claude Code](https://claude.com/claude-code).*
