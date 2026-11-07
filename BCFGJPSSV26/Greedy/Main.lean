module

public import BCFGJPSSV26.Greedy.PolyTime.Main
public import BCFGJPSSV26.Combine

/-!
# Theorem 1.2

[BCFGJPSSV26a, Theorem 1.2] (Theorem 5.16 in full): `BCFGJPSSV26.Greedy.greedy_main` proves the
statement `BCFGJPSSV26.Combine.Thm12` of `BCFGJPSSV26.kMedian_pseudoApproximation` with
`C = 10¹⁰`. For each `ε > 0`, the algorithm is `BCFGJPSSV26.Greedy.algFor ε` on the tuple of the
instance: the main algorithm (`Greedy/Algorithm.lean`) for `ε < 4`, with the constants of
`Greedy/Constants.lean`, and the local search of Part II for `ε ≥ 4`. It runs in polynomial time
(`BCFGJPSSV26.Greedy.algFor_polytime`) and satisfies the guarantee
(`BCFGJPSSV26.Greedy.algFor_spec`).

`Greedy/README.md` describes the route and the files.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- **Theorem 1.2** of [BCFGJPSSV26a]: the statement of
`BCFGJPSSV26.kMedian_pseudoApproximation`. -/
theorem greedy_main : Combine.Thm12 :=
  ⟨Cthm, fun _ hε ↦ ⟨fun I ↦ algFor _ (toRaw I), algFor_polytime _, fun _ hI ↦ algFor_spec hε hI⟩⟩

end BCFGJPSSV26.Greedy
