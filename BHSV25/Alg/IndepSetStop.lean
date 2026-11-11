module

public import BHSV25.Alg.IndepSetGS
public import BHSV25.Net.StopCorrect

/-!
# Theorem 7.20: the algorithm that finds the number of rounds

The algorithm of [BHSV25, Theorem 7.20] for all `t` at once (`BHSV25.Alg.indepAlgU`): the
algorithm `BHSV25.Alg.indepAlgGS` of the greedy net with filter `((I - Ã) / 2)^E`, `E = a n⁵`,
whose number `T` of rounds is the stopping round of the greedy selection (`BHSV25.Net.stopZ`) for
the threshold `ψ^E`, with the grid of radius `(⌊√T⌋ + 1) K` cut at a budget `B` read with the
graph. It reads the parameters `(a, K, β, r, s)`, which do not depend on `t`.

The paper computes the eigenvectors with eigenvalue at most `-λ`; the algorithm finds their
number up to the threshold `ψ = 1 - (1 - 1/β) g / 2`, for the gap `g = max(r / s, 1 / (4 n⁴))`
and a fraction `r / s` within `c'' (1 - λ)` below `1 - λ` (`BHSV25.Alg.thrF`); see
`BHSV25/Alg/IndepSetStopCorrect.lean` for the analysis.

* `BHSV25.Alg.indepAlgU_polytime`: one machine reading the parameters and two unary paddings with
  the graph runs in polynomial time; the padding `2^padU` (`BHSV25.Alg.padU`) pays for the grid.
-/

@[expose] public section

namespace BHSV25.Alg

open Turing.MultiTapeTM ComputableInPolyTime Matrix
open Encoding (encRat)

/-! ### The algorithm -/

/-- The gap `g = max(r / s, 1 / (4 n⁴))`, as a fraction `(numerator, denominator)`. -/
def gapF (r s n : ℕ) : ℕ × ℕ := if s ≤ 4 * n ^ 4 * r then (r, s) else (1, 4 * n ^ 4)

/-- The threshold `ψ = 1 - (1 - 1/β) g / 2`, as a fraction `(numerator, denominator)`. -/
def thrF (β r s n : ℕ) : ℕ × ℕ :=
  (2 * β * (gapF r s n).2 - (β - 1) * (gapF r s n).1, 2 * β * (gapF r s n).2)

/-- The parameters `(a, K, β, r, s)` of the algorithm: the power `a n⁵` of the filter, the
precision `4 / K`, and the threshold. -/
abbrev UPar := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The parameters, in unary. -/
abbrev encUPar : UPar ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary encUnary)))

/-- **The number of rounds**: the stopping round of the greedy selection on the filter
`Q = (d I - A)^E`, `E = a n⁵`, for the test `X = den^(2E)`, `Y = (2 d num)^(2E)` of the threshold
`ψ = num / den`: the residuals of `Q` against `(2 d ψ)^E`, those of `((I - Ã) / 2)^E` against
`ψ^E`. -/
def roundsU (p : UPar) (x : ℕ × List Bool) : ℕ :=
  Net.stopZ (numV x) (Net.gramRows (numV x) (Net.filtQ true (p.1 * numV x ^ 5) x))
    (((thrF p.2.2.1 p.2.2.2.1 p.2.2.2.2 (numV x)).2 ^ (2 * (p.1 * numV x ^ 5)) : ℕ) : ℤ)
    (((2 * Net.deg (numV x) x.2 * (thrF p.2.2.1 p.2.2.2.1 p.2.2.2.2 (numV x)).1) ^
      (2 * (p.1 * numV x ^ 5)) : ℕ) : ℤ)

/-- The exponent of the padding: `⌈log₂ (3 + 12 K)⌉` per round, so that the padding `2^(...)` is
at least the budget `(3 + 12 K)^T` of the grid. -/
def padU (p : UPar) (x : ℕ × List Bool) : ℕ := Nat.clog 2 (3 + 12 * p.2.1) * roundsU p x

/-- **The algorithm** of [BHSV25, Theorem 7.20] for all `t`: `BHSV25.Alg.indepAlgGS` with the
stopping round `T`, the grid of radius `(⌊√T⌋ + 1) K` and the budget `B` read with the graph. -/
def indepAlgU (p : UPar) (z : (ℕ × ℕ) × (ℕ × List Bool)) : List Bool :=
  indepAlgGS (p.1, roundsU p z.2, (Nat.sqrt (roundsU p z.2) + 1) * p.2.1, z.1.1) z.2

/-! ### Polynomial time -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- The gap `gapF`, as a pair in unary, in polynomial time. -/
theorem stopU_gapF' {r s n : α → ℕ} (hr : ComputableInPolyTime r input encUnary)
    (hs : ComputableInPolyTime s input encUnary) (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ gapF (r a) (s a) (n a)) input (encPair encUnary encUnary) := by
  have hn4 : ComputableInPolyTime (fun a ↦ 4 * n a ^ 4) input encUnary := by
    have h := unary_mul' (const 4) (unary_mul' (unary_mul' (unary_mul' hn hn) hn) hn)
    convert h using 1
    funext a
    ring
  have hle := unary_le' hs (unary_mul' hn4 hr)
  have key := Net.ite_prop (p := fun a ↦ s a ≤ 4 * n a ^ 4 * r a) hle (hr.prod hs)
    ((const 1).prod hn4)
  unfold gapF
  exact key

/-- The numerator of the threshold `thrF`, in unary, in polynomial time. -/
theorem stopU_thrF₁' {β r s n : α → ℕ} (hβ : ComputableInPolyTime β input encUnary)
    (hr : ComputableInPolyTime r input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ (thrF (β a) (r a) (s a) (n a)).1) input encUnary := by
  have hg := stopU_gapF' hr hs hn
  have hg1 := (fst encUnary encUnary).comp hg
  have hg2 := (snd encUnary encUnary).comp hg
  have key := unary_sub' (unary_mul' (unary_mul' (const 2) hβ) hg2)
    (unary_mul' (unary_sub' hβ (const 1)) hg1)
  exact key

/-- The denominator of the threshold `thrF`, in unary, in polynomial time. -/
theorem stopU_thrF₂' {β r s n : α → ℕ} (hβ : ComputableInPolyTime β input encUnary)
    (hr : ComputableInPolyTime r input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ (thrF (β a) (r a) (s a) (n a)).2) input encUnary := by
  have hg := stopU_gapF' hr hs hn
  have hg2 := (snd encUnary encUnary).comp hg
  have key := unary_mul' (unary_mul' (const 2) hβ) hg2
  exact key

/-- A power `b^e` of unary numbers, as a binary integer, in polynomial time. -/
theorem stopU_powInt' {b e : α → ℕ} (hb : ComputableInPolyTime b input encUnary)
    (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ ((b a ^ e a : ℕ) : ℤ)) input encIntBin :=
  intBin_natCast.comp (binary_pow' (Net.toBinary' hb) he)

end PolyTime

theorem roundsU_polytime : ComputableInPolyTime
    (fun z : UPar × (ℕ × List Bool) ↦ roundsU z.1 z.2)
    (encPair encUPar (encPair encNat encBits)) encUnary := by
  unfold roundsU
  set I := encPair encUPar (encPair encNat encBits)
  have hp : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1) I encUPar := fst _ _
  have hx : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.2) I
      (encPair encNat encBits) := snd _ _
  have ha : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1.1) I encUnary :=
    (fst _ _).comp hp
  have hβ : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1.2.2.1) I encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp hp))
  have hr : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1.2.2.2.1) I encUnary :=
    (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
  have hs : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1.2.2.2.2) I encUnary :=
    (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hp)))
  have hn : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ numV z.2) I encUnary :=
    numV_polytime.comp hx
  have hadj : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.2.2) I encBits :=
    (snd _ _).comp hx
  have hn5 : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ numV z.2 ^ 5) I
      encUnary := by
    have h := unary_mul' (unary_mul' (unary_mul' (unary_mul' hn hn) hn) hn) hn
    convert h using 1
    funext z
    ring
  have hE : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1.1 * numV z.2 ^ 5) I
      encUnary := unary_mul' ha hn5
  have hQ := (Net.filtQ_polytime true).comp (hE.prod hx)
  have hG := Net.gramRows_polytime.comp (hn.prod hQ)
  have h2E := unary_mul' (const 2) hE
  have hX := stopU_powInt' (stopU_thrF₂' hβ hr hs hn) h2E
  have hY := stopU_powInt' (unary_mul' (unary_mul' (const 2) (Net.deg' hn hadj))
    (stopU_thrF₁' hβ hr hs hn)) h2E
  have key := Net.stopZ_polytime.comp ((hn.prod hG).prod (hX.prod hY))
  exact key

theorem padU_polytime : ComputableInPolyTime
    (fun z : UPar × (ℕ × List Bool) ↦ padU z.1 z.2)
    (encPair encUPar (encPair encNat encBits)) encUnary := by
  unfold padU
  have hK : ComputableInPolyTime (fun z : UPar × (ℕ × List Bool) ↦ z.1.2.1)
      (encPair encUPar (encPair encNat encBits)) encUnary :=
    (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hc := (unary_clog_const 2).comp (unary_add' (const 3) (unary_mul' (const 12) hK))
  have key := unary_mul' hc roundsU_polytime
  exact key

/-- **The algorithm runs in polynomial time**, reading its parameters and the paddings in unary
with the graph. -/
theorem indepAlgU_polytime : ComputableInPolyTime
    (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ indepAlgU z.1 z.2)
    (encPair encUPar (encPair (encPair encUnary encUnary) (encPair encNat encBits))) encBits := by
  unfold indepAlgU
  set I := encPair encUPar (encPair (encPair encUnary encUnary) (encPair encNat encBits))
  have hp : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1) I
      encUPar := fst _ _
  have hy : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.1) I
      (encPair encUnary encUnary) := (fst _ _).comp (snd _ _)
  have hx : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.2) I
      (encPair encNat encBits) := (snd _ _).comp (snd _ _)
  have ha : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1.1) I
      encUnary := (fst _ _).comp hp
  have hK : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1.2.1) I
      encUnary := (fst _ _).comp ((snd _ _).comp hp)
  have hB : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.1.1) I
      encUnary := (fst _ _).comp hy
  have hT : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦
      roundsU z.1 z.2.2) I encUnary := roundsU_polytime.comp (hp.prod hx)
  have hsq : ComputableInPolyTime (fun z : UPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦
      Nat.sqrt (roundsU z.1 z.2.2)) I encUnary :=
    binary_to_unary_bounded (binary_sqrt' (Net.toBinary' hT)) hT fun _ ↦ Nat.sqrt_le_self _
  have hN := unary_mul' (unary_add' hsq (const 1)) hK
  have hpar := ha.prod (hT.prod (hN.prod hB))
  have key := indepAlgGS_polytime.comp (hpar.prod hx)
  exact key

end BHSV25.Alg
