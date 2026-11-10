module

public import BHSV25.Spectral.Basic
public import BHSV25.Net.Correct
public import BHSV25.Net.PolyTime

/-!
# Rational vectors

A vector of the nets is a list of rationals, read as a real vector of length `n`
(`BHSV25.Net.vecOf`, missing entries are `0`). The input of the algorithms is the number of vertices
and the adjacency table, the pair that `BHSV25.encGraph` encodes; the encodings are those of
`Background/Encoding.lean`, which agree with complexitylib's up to definitional unfolding.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Turing.MultiTapeTM Matrix

/-- A list of rationals read as a real vector of length `n` (missing entries are `0`). -/
def vecOf (n : ℕ) (c : List ℚ) : Fin n → ℝ := fun i ↦ ((c.getD i 0 : ℚ) : ℝ)

end Net

end BHSV25
