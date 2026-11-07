# Theorem 1.2: opening `k + O(log n / ε²)` centers

[BCFGJPSSV26a, Theorem 1.2] (Theorem 5.16 in full), `BCFGJPSSV26.Greedy.greedy_main :
BCFGJPSSV26.Combine.Thm12` ([Main.lean](Main.lean)): with `C = 10¹⁰`, for every `ε > 0` a
deterministic polynomial-time algorithm outputs at most `k + C log n / ε²` distinct facilities of
cost at most `(1.9499 + ε) opt k`. The algorithm for `ε` is `BCFGJPSSV26.Greedy.algFor ε`
([Constants.lean](Constants.lean)), its guarantee `BCFGJPSSV26.Greedy.algFor_spec` and its running
time `BCFGJPSSV26.Greedy.algFor_polytime` ([PolyTime/Main.lean](PolyTime/Main.lean)).

The algorithm is the log-adaptive greedy of [BCFGJPSSV26a, Section 5 and Appendices D and E] with
the bid `β(α, d) = [α - 1.224 d]⁺`, whose solutions for two opening costs are merged as in
[CGLSS25, Section 3.5]. Its analysis rests on the bound `2 - 0.224² = 1.949824` on the
factor-revealing program [BCFGJPSSV26a, Theorem 4.4], from the library
[`KMedian195`](../../Imported/KMedian195). Along the way it proves the robust LMP guarantee
`BCFGJPSSV26.Greedy.robust_lmp` ([LMP.lean](LMP.lean)), which Theorem 1.4 ([../FL](../FL)) uses.

## The route

1. **Exact tests** (`BCFGJPSSV26.Greedy.test1`, `BCFGJPSSV26.Greedy.test2`): the test of type 2
   uses the one-parameter family of bids `τ = F_i(T)` for `T ∈ [θ, (1 + ε²) θ]`, that is
   `min (T, (1 - δ) d(j, S), (1 + ε) θ - d(j, i))` on the active clients near `i` and `θ` on the
   other active clients, and computes in closed form the least `T` that pays for the facility
   (`BCFGJPSSV26.Greedy.tstar`, `BCFGJPSSV26.Greedy.test2_iff`). So all tests are exact rational
   computations, and no linear program is solved. Accepted facilities are `(2, 0)`-openable
   [BCFGJPSSV26a, Definition D.2], and when none is accepted, no facility is openable with bids of
   this form, which is the maximality the analysis uses: a key lemma
   (`BCFGJPSSV26.Greedy.key_lemma`) gives the pay-to-open lemma for these bids [BCFGJPSSV26a,
   Lemma D.11] and the step "increasing `θ`" of [BCFGJPSSV26a, Lemma E.6].
2. **Valid solutions** ([BCFGJPSSV26a, Definitions D.3 and D.6], `BCFGJPSSV26.Greedy.Sol`): exactly
   `2R` sequences; regular facilities and free copies at an offset, compared through their pairs
   `(facility, offset)`; profiles capped at `K = 2 θ_R`, so that a free copy at offset `K` is
   invisible. No overbidding holds throughout ([BCFGJPSSV26a, Lemma E.6],
   `BCFGJPSSV26.Greedy.noOver_partial`), every client is inactive at the end, by the maximality of
   the last sequence of type 1, and the structure lemma [BCFGJPSSV26a, Lemma E.7] holds.
3. **The robust LMP guarantee** ([BCFGJPSSV26a, Theorem D.7], `BCFGJPSSV26.Greedy.robust_lmp`), in
   linear form: `(1 - δ) connCost H + |H_reg| f ≤ (ρ + 6δ) cost(O) + |O| f + |H_reg| n η` for every
   nonempty set `O` of facilities. The execution is a list of atomic steps (openings and raises of
   the time), and the values `α*_j`, the chains `R_{j,·}` and `Z_{j,·}`, freezing and far supersets
   ([BCFGJPSSV26a, Observations E.2 to E.4, Lemmas E.8 and E.11]) are indexed by steps. The clients
   served by one facility of `O` give a feasible point of the factor-revealing program
   ([BCFGJPSSV26a, Lemmas E.13 to E.16], `BCFGJPSSV26.Greedy.Run.embed_feasible`), and the cost
   bounds ([BCFGJPSSV26a, Lemmas E.9, E.12 and E.17]) sum up.
4. **The core** (`BCFGJPSSV26.Greedy.core`, distances in `[1, M]`): CompleteSequence adds the first
   facility that passes the test, so the completion depends only on the profile of the prefix;
   bisection on a grid of opening costs `f̂ ∈ [δ, 4 n M]`; then the merge, one phase per sequence:
   make the parameters agree (using [BCFGJPSSV26a, Claim D.12]), walk one sequence towards the
   other, remove extra facilities, and search the offset of a new free copy on a grid. A promise
   kept from phase to phase (`BCFGJPSSV26.Greedy.Ctx.Promise`) gives a valid solution with exactly
   `k` regular facilities and at most three free copies per sequence
   (`BCFGJPSSV26.Greedy.Ctx.merge_spec`). With the robust LMP guarantee, the core outputs at most
   `k + 6R` facilities of cost at most `(ρ + 10δ) cost(O)` for every nonempty set `O` of at most
   `k` facilities (`BCFGJPSSV26.Greedy.core_spec`).
5. **The reduction** (`BCFGJPSSV26.Greedy.algMain`): the trivial solution, the nearest facility of
   every client, costs at most `opt k` and has at most `k` facilities when `opt k = 0`; it is the
   output when it has at most `k + ⌊log₂ n⌋ ⌈1/δ²⌉` facilities. Otherwise the distances are scaled,
   in place of the reduction of [CGLSS25, Lemma 1.4]: for each guess `Λ` of `max_j d(j, OPT)` among
   the positive client–facility distances, `d̃ = min (d / t + 1, M)` off the diagonal with
   `t = ε' Λ / n` and `M = 8 n² / ε' + 1`; the core runs on every guess, and the cheapest output by
   exact cost is kept.
6. **Constants** (`Constants.lean`): `δ ∈ (ε/200, ε/100)` for `ε ≤ 1` and `δ = 1/100` for
   `1 < ε < 4`; for `ε ≥ 4` the local search of Part II (`BCFGJPSSV26.Stable.localSearch`, swaps of
   size `24 · 201`), which costs at most `4 opt k` with `k` facilities. The two bounds on the
   number of facilities, `⌊log₂ n⌋ ⌈1/δ²⌉` and `6R`, are at most `10¹⁰ log n / ε²`
   (`BCFGJPSSV26.Greedy.bcomp_le`, `BCFGJPSSV26.Greedy.sixR_le`).
7. **Polynomial time** (`PolyTime/`): every loop has an explicit count polynomial in the input and
   every number is a rational of polynomially many bits, so complexitylib's certificates compose
   (`BCFGJPSSV26.Greedy.core_polytime`).

## Files

| Files | Content |
| --- | --- |
| [Bid.lean](Bid.lean), [Space.lean](Space.lean) | The bid `[x - γ y]⁺` with `γ = 153/125`, `ρ = 1.949824`, the chain lemmas; spaces, parameters and their inequalities, atoms, capped profiles. |
| [Openable.lean](Openable.lean) | Openability, no overbidding, candidates; the exact tests; the key lemma, pay-to-open and raising the time. |
| [Valid.lean](Valid.lean), [Structure.lean](Structure.lean) | Valid sequences and solutions, the invariants and the validity calculus of the merge; the structure lemma. |
| [Trace.lean](Trace.lean) | The execution as atomic steps: `α*`, the chains, the observations, freezing, far supersets. |
| [FRP.lean](FRP.lean), [Embed.lean](Embed.lean), [LMP.lean](LMP.lean) | The factor-revealing bound of `KMedian195` in the form used here; the embedding into the program; the cost bounds and the robust LMP guarantee. |
| [Alg/Defs.lean](Alg/Defs.lean), [Alg/Bridge.lean](Alg/Bridge.lean), [Alg/Complete.lean](Alg/Complete.lean) | The core on lists and natural numbers; from the algorithm to the analysis; CompleteSequence and CompleteSolution. |
| [Alg/MergeAux.lean](Alg/MergeAux.lean), [Alg/MergeWalk.lean](Alg/MergeWalk.lean), [Alg/Merge.lean](Alg/Merge.lean), [Alg/Core.lean](Alg/Core.lean) | Correctness of the merge; the core theorem. |
| [Reduction/Trivial.lean](Reduction/Trivial.lean), [Reduction/Scale.lean](Reduction/Scale.lean) | The trivial solution; the scaled distances and the guesses. |
| [Algorithm.lean](Algorithm.lean), [Constants.lean](Constants.lean), [Main.lean](Main.lean) | The main and the large-`ε` algorithms, the constants, Theorem 1.2. |
| [PolyTime/Core.lean](PolyTime/Core.lean), [`PolyTime/Aux{Basic,Ctx,Complete,Search,Walk,Round,Merge,Core}.lean`](PolyTime) | The core in polynomial time. |
| [PolyTime/AuxMain.lean](PolyTime/AuxMain.lean), [PolyTime/Main.lean](PolyTime/Main.lean) | The trivial solution, the guesses, the local search and the whole algorithm in polynomial time. |
