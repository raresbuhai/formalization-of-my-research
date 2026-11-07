module

public import BCFGJPSSV26.Greedy.Alg.Defs
public import BCFGJPSSV26.Basic.Raw
public import Background.PolyTime.Rat
public import BCFGJPSSV26.Greedy.PolyTime.AuxCore

/-!
# The core runs in polynomial time

`BCFGJPSSV26.Greedy.core_polytime`: for fixed constants, the core of `Greedy/Alg/Defs.lean` is
computable in polynomial time, on core inputs encoded as instances are (`BCFGJPSSV26.encRaw`) except
that the numbers `n` of clients and `m` of facilities are written in unary
(`BCFGJPSSV26.Greedy.encCoreIn`): the core loops over all clients and all facilities, and runs
CompleteSequence `L = m + 4` times, so `n` and `m` must be polynomial in the length of the input.
For an instance they are (its table has `n + m` rows), and `BCFGJPSSV26.Greedy.toRawU_polytime`
converts. This does not need any correctness property of the algorithm: every loop has a count
polynomial in the input (`L` steps of CompleteSequence, `2R` sequences and phases, `Pf` and `Pu`
steps of the searches, `L` rounds of the walk, each with at most `|cur|` deletions), and every
number is a rational of polynomially many bits (`θ r = (1 + ε²)^r` for `r ≤ R`, the grids, the
profiles, and the sums of `n` such terms in the tests, computed with a common denominator as in
`Background/PolyTime/Rat.lean`). Here `R = O(log(n M) / ε²)` and `Pf, Pu = O(R + log n)` for fixed
`ε`, so all counts are polynomial in the length of the input.

The proof is in the files `Greedy/PolyTime/Aux*.lean`, namespace `BCFGJPSSV26.Greedy.PT`:

* `AuxBasic`: the encodings (atoms and sequences in binary), generic certificates (powers,
  ceilings, `⌈log₂⌉` in unary, folds of `min` and `max`) and bounds on encoded lengths;
* `AuxCtx`: the parameters (`BCFGJPSSV26.Greedy.ipar`), profiles and tests;
* `AuxComplete`: CompleteSequence (at most one atom per step) and CompleteSolution (at most one
  sequence of at most `L` atoms per step);
* `AuxSearch`: pairs and results as tagged tuples, the binary searches (their states stay below
  the initial upper end) and the bisection;
* `AuxWalk`, `AuxRound`: the kinds of the points of the walk as tagged tuples, and the walk (every
  recorded sequence has at most `|H'p| + 2L + 1` atoms, there are at most `1 + L (|H'p| + 2L + 2)`
  points, and every atom comes from the inputs, the completions or the free copies);
* `AuxMerge`: BinSearch, step C, the dispatch of step B, the phases;
* `AuxCore`: the invariant of the merge loop (`BCFGJPSSV26.Greedy.PT.ResOK`: at most `2R`
  sequences of at most `9L + 5` atoms, the sequences from the current phase on with at most `L`
  atoms, facilities at most `m` and offset indices at most `2^Pu + 1`), which bounds its states,
  and the certificate of the core.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM

/-- **Core inputs** encoded as instances are, except that `n` and `m` are in unary. -/
abbrev encCoreIn : CoreIn ↪ List Bool := PT.encCI

/-- **The core runs in polynomial time**, for fixed constants. -/
theorem core_polytime (c : Consts) : ComputableInPolyTime (core c) encCoreIn (encList encNat) :=
  PT.coreS c (X := fun x ↦ x) ComputableInPolyTime.id'

end BCFGJPSSV26.Greedy
