# Theorem 1.4: an LMP algorithm for facility location

[BCFGJPSSV26a, Theorem 1.4] (Theorem 4.3 in full), `BCFGJPSSV26.FL.fl_main : BCFGJPSSV26.FL.Thm14`
([Main.lean](Main.lean)): a deterministic polynomial-time algorithm that, given a valid instance
with at least one client and an opening cost `f ≥ 0`, outputs a nonempty list `S` of distinct
facilities with `cost S ≤ 1.9499 (OPT_f - f |S|)`. The algorithm is `BCFGJPSSV26.FL.alg`
([Algorithm.lean](Algorithm.lean)), its guarantee `BCFGJPSSV26.FL.alg_spec` and its running time
`BCFGJPSSV26.FL.alg_polytime` ([PolyTime.lean](PolyTime.lean)).

It reuses the log-adaptive greedy of [BCFGJPSSV26a, Section 5] as formalized for Theorem 1.2
([../Greedy](../Greedy)): CompleteSolution from the empty solution with the exact tests, at one
opening cost, and the robust LMP guarantee `BCFGJPSSV26.Greedy.robust_lmp`. Facility location needs
neither the bisection on the opening cost nor the merge.

## The route

1. **Shift and scale** (`BCFGJPSSV26.FL.tFL`, `BCFGJPSSV26.FL.stabFL`): with `d_min` the least
   positive client–facility distance and `t = min (d_min / (10⁵ n), f)`, the distances become
   `d / t + 1` off the diagonal, a pseudometric with client–facility distances at least `1`, as the
   analysis of the greedy asks. Every client pays `1` more, which costs `n t ≤ d_min / 10⁵` after
   scaling back.
2. **The greedy run** (`BCFGJPSSV26.FL.runFL`): CompleteSolution at the scaled opening cost
   `f̂ = 1.9499 (1 - δ) f / t`, with `δ = 10⁻⁶` and the paper's `ε = δ / 10`, and with the bound
   `M = d_max / t + 1 + f̂` that fixes the number of phases. It gives a `0`-valid solution
   (`BCFGJPSSV26.Greedy.Ctx.complete_sol`).
3. **The LMP bound for the run** (`BCFGJPSSV26.FL.runFL_spec`): the robust LMP guarantee applies
   with no slack, `η = 0` (validity does not depend on the slack parameter,
   `BCFGJPSSV26.FL.sol_eta`). Scaled back, and since `cost O ≥ d_min` when `O` has a positive
   cost, it gives `cost S + 1.9499 f |S| ≤ 1.9499 (cost O + f |O|)` for `n, m ≥ 2` and `f > 0`
   (`BCFGJPSSV26.FL.fl_arith`).
4. **The output** (`BCFGJPSSV26.FL.alg`): the candidate, among the greedy run (if it is a list of
   distinct facilities) and the trivial solution (the nearest facility of every client,
   `BCFGJPSSV26.Greedy.trivialSol`), with the least `cost S + 1.9499 f |S|`. The guarantee is a
   bound on this objective (`BCFGJPSSV26.FL.lmp_of_score`). The trivial solution meets it when it
   has at most as many facilities as an optimal set `O`, which covers `n = 1`, `m = 1` and
   `cost O = 0`, and when `f = 0` (`BCFGJPSSV26.FL.score_trivialSol_le`); otherwise the run meets
   it.
5. **Polynomial time**: as for the core of Theorem 1.2, with the certificates of CompleteSolution
   restated for the computed parameters of the run.

## Files

| Files | Content |
| --- | --- |
| [Algorithm.lean](Algorithm.lean) | The constants, the scale, the parameters, the greedy run and the output. |
| [Run.lean](Run.lean) | The scaled space, the hypotheses of the greedy analysis, and the LMP bound for the run. |
| [Select.lean](Select.lean) | The objective, the trivial solution, and the choice of the output. |
| [PolyTimeCtx.lean](PolyTimeCtx.lean), [PolyTime.lean](PolyTime.lean) | CompleteSolution for computed parameters, and the algorithm, in polynomial time. |
| [Main.lean](Main.lean) | The guarantee and Theorem 1.4. |
