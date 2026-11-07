module

public import BGHKLMM26.Hardness.Defs
public import BGHKLMM26.Hardness.MachineList

/-!
# The reduction runs in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the number of coins
(`BGHKLMM26.Hard.coinCount_polytime`, in unary) and for the reduction
(`BGHKLMM26.Hard.reduce_polytime`), for fixed parameters.

The pieces are in `BGHKLMM26/Hardness/MachineList.lean`: the decoder of an edge and the adjacency
table of the output are rewritten as functions on lists (the points of the cube as lists of bits,
`π x` by looking up `x[π(j)]`), and each is certified with complexitylib's list and number rules.
The greedy simplification is a fold whose state, the kept edges, is a sublist of the sampled edges,
so its encoding is never longer than theirs. Every length is polynomial since `R`, `b`, `D` and `Δ`
are constants: `nVert ≤ |cs| 2^R`, `samples = nVert D` and `blockLen = 2t + R + R b` with
`t = 2|cs| + R + Δ`. On instances that are not `ok` the output is a fixed single vertex.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open UniqueGames

open Turing.MultiTapeTM

/-- **The number of coins is computable in polynomial time**, in unary. -/
theorem coinCount_polytime (P : Prm) : ComputableInPolyTime P.coinCount encUG encUnary :=
  Mach.coinCount_polytime' P

/-- **The reduction runs in polynomial time**, from an instance and its coins to the encoded
graph. -/
theorem reduce_polytime (P : Prm) :
    ComputableInPolyTime (reduce P) (encPair encUG encBits) encGraph :=
  Mach.reduce_polytime' P

end BGHKLMM26.Hard
