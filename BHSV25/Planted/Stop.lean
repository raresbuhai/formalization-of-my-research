module

public import BHSV25.Planted.Partial
public import BHSV25.Net.Stop

/-!
# Theorem 7.12: the algorithm that finds the number of rounds

The algorithm of [BHSV25, Theorem 7.12] for all `t` at once (`BHSV25.Planted.planAlgU`): the
algorithm `BHSV25.Alg.expAlg` of Theorem 7.1 with `k` colors, whose greedy net with filter
`A^E`, `E = 2 a n`, has as number `T` of rounds the stopping round of the greedy selection
(`BHSV25.Net.stopZ`), with the grid of radius `(⌊√T⌋ + 1) K` of the net cut at a budget `B₁`
and the tuples of the clustering cut at a budget `B₂`, both read with the graph. It reads the
parameters `(k, K, a)`, which do not depend on `t`.

The analysis works with `A_G / d` for the degree `d` of the host, which the algorithm does not
know. The threshold of the stopping round is `(S / (20 k² n))^E` for the number `S` of ones of
the adjacency table, that is, `ψ = 1 / (20 k²)` at the scale of the average degree `S / n`
(`BHSV25.Planted.roundsP`). The average degree is at most `d`, and on the good colorings at least
`d / 2`, which is all the analysis needs (`BHSV25/Planted/StopCorrect.lean`).

* `BHSV25.Planted.planAlgU_polytime`: one machine reading the parameters and two unary paddings
  with the graph runs in polynomial time; the paddings `2^padP₁` and `2^padP₂`
  (`BHSV25.Planted.padP₁`, `BHSV25.Planted.padP₂`) pay for the net and the tuples.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### The algorithm -/

/-- The parameters `(k, K, a)` of the algorithm: the number of colors, the precision `4 / K` and
the power `2 a n` of the filter. -/
abbrev PPar := ℕ × ℕ × ℕ

/-- The parameters, in unary. -/
abbrev encPPar : PPar ↪ List Bool := encPair encUnary (encPair encUnary encUnary)

/-- **The number of rounds**: the stopping round of the greedy selection on the filter `Q = A^E`,
`E = 2 a n`, for the test `X = (20 k² n)^(2E)`, `Y = S^(2E)`, for the number `S` of ones of the
table: the residuals of `Q` against `(S / (20 k² n))^E`. -/
def roundsP (p : PPar) (x : ℕ × List Bool) : ℕ :=
  Net.stopZ (Alg.numV x) (Net.gramRows (Alg.numV x) (Net.filtQ false (2 * (p.2.2 * Alg.numV x)) x))
    (((20 * p.1 ^ 2 * Alg.numV x) ^ (2 * (2 * (p.2.2 * Alg.numV x))) : ℕ) : ℤ)
    (((x.2.count true) ^ (2 * (2 * (p.2.2 * Alg.numV x))) : ℕ) : ℤ)

/-- The exponent of the padding of the net: `⌈log₂ (3 + 12 K)⌉` per round, so that `2^padP₁` is
at least the budget `(3 + 12 K)^T` of the grid. -/
def padP₁ (p : PPar) (x : ℕ × List Bool) : ℕ := Nat.clog 2 (3 + 12 * p.2.1) * roundsP p x

/-- The exponent of the padding of the tuples: `2^padP₂ ≥ (2^padP₁ + 1)^k + (2 K' + 1)^(k²)` for
the range `K' = 64 k³ + 1` of the grid of centers. -/
def padP₂ (p : PPar) (x : ℕ × List Bool) : ℕ :=
  p.1 * (padP₁ p x + 1) + p.1 * p.1 * Nat.clog 2 (2 * gridK p.1 + 1) + 1

/-- **The algorithm** of [BHSV25, Theorem 7.12] for all `t`: `BHSV25.Alg.expAlg` with `k`
colors, the stopping round `T`, the grid of radius `(⌊√T⌋ + 1) K`, and the budgets `B₁` of the
net and `B₂` of the tuples read with the graph. -/
def planAlgU (p : PPar) (z : (ℕ × ℕ) × (ℕ × List Bool)) : List ℕ :=
  Alg.expAlg ((p.1, p.1, gridS p.1, gridK p.1, z.1.2),
    (p.2.2, roundsP p z.2, (Nat.sqrt (roundsP p z.2) + 1) * p.2.1, z.1.1)) z.2

/-! ### Polynomial time -/

section PolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- A power `b^e` of unary numbers, as a binary integer, in polynomial time. -/
theorem stopP_powInt' {b e : α → ℕ} (hb : ComputableInPolyTime b input encUnary)
    (he : ComputableInPolyTime e input encUnary) :
    ComputableInPolyTime (fun a ↦ ((b a ^ e a : ℕ) : ℤ)) input encIntBin :=
  intBin_natCast.comp (binary_pow' (Net.toBinary' hb) he)

/-- The number of ones of a bit string, in unary, in polynomial time. -/
theorem stopP_count' {f : α → List Bool} (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a ↦ (f a).count true) input encUnary := by
  have hl : ComputableInPolyTime f input (encList encBool) :=
    (bits_encList_polyTime encBool).1.comp hf
  exact .of_tidy (ComputableTidilyInPolyTime.countWithInput hl.tidy
    (ComputableTidilyInPolyTime.const true))

/-- The range `64 k³ + 1` of the grid of centers, in unary, in polynomial time. -/
theorem stopP_gridK' {k : α → ℕ} (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ gridK (k a)) input encUnary := by
  unfold gridK
  have h := unary_add' (unary_mul' (const 64) (unary_mul' (unary_mul' hk hk) hk)) (const 1)
  convert h using 1
  funext a
  ring

/-- The scale `32 k²` of the grid of centers, in unary, in polynomial time. -/
theorem stopP_gridS' {k : α → ℕ} (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun a ↦ gridS (k a)) input encUnary := by
  unfold gridS
  have h := unary_mul' (const 32) (unary_mul' hk hk)
  convert h using 1
  funext a
  ring

end PolyTime

theorem roundsP_polytime : ComputableInPolyTime
    (fun z : PPar × (ℕ × List Bool) ↦ roundsP z.1 z.2)
    (encPair encPPar (encPair encNat encBits)) encUnary := by
  unfold roundsP
  set I := encPair encPPar (encPair encNat encBits)
  have hp : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.1) I encPPar := fst _ _
  have hx : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.2) I
      (encPair encNat encBits) := snd _ _
  have hk : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.1.1) I encUnary :=
    (fst _ _).comp hp
  have ha : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.1.2.2) I encUnary :=
    (snd _ _).comp ((snd _ _).comp hp)
  have hn : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ Alg.numV z.2) I encUnary :=
    Alg.numV_polytime.comp hx
  have hadj : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.2.2) I encBits :=
    (snd _ _).comp hx
  have hE := unary_mul' (const 2) (unary_mul' ha hn)
  have hQ := (Net.filtQ_polytime false).comp (hE.prod hx)
  have hG := Net.gramRows_polytime.comp (hn.prod hQ)
  have h2E := unary_mul' (const 2) hE
  have hk2 : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.1.1 ^ 2) I encUnary := by
    have h := unary_mul' hk hk
    convert h using 1
    funext z
    ring
  have hX := stopP_powInt' (unary_mul' (unary_mul' (const 20) hk2) hn) h2E
  have hY := stopP_powInt' (stopP_count' hadj) h2E
  have key := Net.stopZ_polytime.comp ((hn.prod hG).prod (hX.prod hY))
  exact key

theorem padP₁_polytime : ComputableInPolyTime
    (fun z : PPar × (ℕ × List Bool) ↦ padP₁ z.1 z.2)
    (encPair encPPar (encPair encNat encBits)) encUnary := by
  unfold padP₁
  have hK : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.1.2.1)
      (encPair encPPar (encPair encNat encBits)) encUnary :=
    (fst _ _).comp ((snd _ _).comp (fst _ _))
  have hc := (unary_clog_const 2).comp (unary_add' (const 3) (unary_mul' (const 12) hK))
  have key := unary_mul' hc roundsP_polytime
  exact key

theorem padP₂_polytime : ComputableInPolyTime
    (fun z : PPar × (ℕ × List Bool) ↦ padP₂ z.1 z.2)
    (encPair encPPar (encPair encNat encBits)) encUnary := by
  unfold padP₂
  have hk : ComputableInPolyTime (fun z : PPar × (ℕ × List Bool) ↦ z.1.1)
      (encPair encPPar (encPair encNat encBits)) encUnary := (fst _ _).comp (fst _ _)
  have hc := (unary_clog_const 2).comp (unary_add' (unary_mul' (const 2) (stopP_gridK' hk))
    (const 1))
  have key := unary_add' (unary_add' (unary_mul' hk (unary_add' padP₁_polytime (const 1)))
    (unary_mul' (unary_mul' hk hk) hc)) (const 1)
  exact key

/-- **The algorithm runs in polynomial time**, reading its parameters and the paddings in unary
with the graph. -/
theorem planAlgU_polytime : ComputableInPolyTime
    (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ planAlgU z.1 z.2)
    (encPair encPPar (encPair (encPair encUnary encUnary) (encPair encNat encBits)))
    encColoring := by
  unfold planAlgU
  set I := encPair encPPar (encPair (encPair encUnary encUnary) (encPair encNat encBits))
  have hp : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1) I
      encPPar := fst _ _
  have hy : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.1) I
      (encPair encUnary encUnary) := (fst _ _).comp (snd _ _)
  have hx : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.2) I
      (encPair encNat encBits) := (snd _ _).comp (snd _ _)
  have hk : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1.1) I
      encUnary := (fst _ _).comp hp
  have hK : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1.2.1) I
      encUnary := (fst _ _).comp ((snd _ _).comp hp)
  have ha : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.1.2.2) I
      encUnary := (snd _ _).comp ((snd _ _).comp hp)
  have hB₁ : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.1.1) I
      encUnary := (fst _ _).comp hy
  have hB₂ : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦ z.2.1.2) I
      encUnary := (snd _ _).comp hy
  have hT : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦
      roundsP z.1 z.2.2) I encUnary := roundsP_polytime.comp (hp.prod hx)
  have hsq : ComputableInPolyTime (fun z : PPar × ((ℕ × ℕ) × (ℕ × List Bool)) ↦
      Nat.sqrt (roundsP z.1 z.2.2)) I encUnary :=
    binary_to_unary_bounded (binary_sqrt' (Net.toBinary' hT)) hT fun _ ↦ Nat.sqrt_le_self _
  have hN := unary_mul' (unary_add' hsq (const 1)) hK
  have hgrid := hk.prod (hk.prod ((stopP_gridS' hk).prod ((stopP_gridK' hk).prod hB₂)))
  have hnet := ha.prod (hT.prod (hN.prod hB₁))
  have key := Alg.expAlg_polytime.comp ((hgrid.prod hnet).prod hx)
  exact key

end Planted

end BHSV25
