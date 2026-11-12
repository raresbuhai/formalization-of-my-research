module

public import BDT24.Alg.PolyTime.Basic

/-!
# The paired test and one round in polynomial time

Certificates for the paired test (`BDT24.Alg.PT.pairTest'`), for a polynomial-time regression
algorithm: the number `slrTime e` of its coins is computed in unary from the length of the encoded
regression input, which is polynomial in the input. Then the coin counts of a round (in unary:
`BDT24.Alg.linB` is polynomial in the input, since `k` enters it only through the length of its
binary encoding), its two tests and the round itself (`BDT24.Alg.PT.blockTest'`), and the final
state (`BDT24.Alg.PT.doneSt'`).
-/

@[expose] public section

namespace BDT24.Alg.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

variable {α : Type} {input : α ↪ List Bool}

/-- **The paired test**, for a polynomial-time regression algorithm. -/
theorem pairTest' {A : SLRInput × List Bool → Estimate}
    (hA : ComputableInPolyTime A (encPair encSLRInput encBits) (encList encRat)) (e : ℕ)
    {k p q : α → ℕ} {u u' : α → Pts} {r : α → List Bool}
    (hk : ComputableInPolyTime k input encNat) (hp : ComputableInPolyTime p input encUnary)
    (hq : ComputableInPolyTime q input encUnary) (hu : ComputableInPolyTime u input encPts)
    (hu' : ComputableInPolyTime u' input encPts) (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a ↦ pairTest A e (k a) (p a) (q a) (u a) (u' a) (r a)) input
      encBool := by
  unfold pairTest
  have hX := slrInputOf' hk hp hq hu hu'
  have hT : ComputableInPolyTime
      (fun a ↦ slrTime e (slrInputOf (k a) (p a) (q a) (u a) (u' a))) input encUnary := by
    unfold slrTime
    exact (unary_pow e).comp (unary_add' ((encoding_length encSLRInput).comp hX) (const 2))
  have hE := hA.comp (g := fun a ↦ (slrInputOf (k a) (p a) (q a) (u a) (u' a),
      (r a).take (slrTime e (slrInputOf (k a) (p a) (q a) (u a) (u' a)))))
    (hX.prod (bitsTakeWithInput hr hT))
  have hP := predict' hq hu hu' hE
  exact rat_le' (resid' hq hP hu) (resid' hq hP hu')

/-- The bound on the length of the regression inputs, in unary. -/
@[fun_prop]
theorem linB' {n m k p : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hk : ComputableInPolyTime k input encNat)
    (hp : ComputableInPolyTime p input encUnary) :
    ComputableInPolyTime (fun a ↦ linB (n a) (m a) (k a) (p a)) input encUnary := by
  unfold linB
  have hl : ComputableInPolyTime (fun a ↦ (Encoding.encNat (k a)).length) input encUnary :=
    (encoding_length encNat).comp hk
  fun_prop

/-- The coins of one run of the regression algorithm, in unary. -/
@[fun_prop]
theorem lenA' (e : ℕ) {x : α → SPCAInput} (hx : ComputableInPolyTime x input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ lenA e (x a)) input encUnary := by
  unfold lenA
  exact (unary_pow e).comp (unary_add' (linB' (nOf' (spcaPts' hx)) (mOf' (spcaPts' hx))
    (spcaK' hx) (spcaP' hx)) (const 2))

/-- The coins of one own sample, in unary. -/
@[fun_prop]
theorem lenC' {x : α → SPCAInput} (hx : ComputableInPolyTime x input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ lenC (x a)) input encUnary := by
  unfold lenC
  have hn := nOf' (spcaPts' hx)
  have hm := mOf' (spcaPts' hx)
  exact unary_mul' (unary_mul' hn hm) (cbits' hn hm (spcaQ' hx))

/-- The coins of one round, in unary. -/
@[fun_prop]
theorem lenBlk' (e : ℕ) {x : α → SPCAInput} (hx : ComputableInPolyTime x input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ lenBlk e (x a)) input encUnary := by
  unfold lenBlk
  exact unary_add' (lenC' hx) (unary_mul' (const 2) (lenA' e hx))

/-- The own sample of a block. -/
@[fun_prop]
theorem ownOf' {x : α → SPCAInput} {c : α → List Bool}
    (hx : ComputableInPolyTime x input encSPCAInput) (hc : ComputableInPolyTime c input encBits) :
    ComputableInPolyTime (fun a ↦ ownOf (x a) (c a)) input encPts := by
  unfold ownOf
  exact ownSample' (nOf' (spcaPts' hx)) (mOf' (spcaPts' hx)) (spcaQ' hx) hc

/-- The first test of a round. -/
theorem fwd' {A : SLRInput × List Bool → Estimate}
    (hA : ComputableInPolyTime A (encPair encSLRInput encBits) (encList encRat)) (e : ℕ)
    {x : α → SPCAInput} {blk : α → List Bool} (hx : ComputableInPolyTime x input encSPCAInput)
    (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ fwd A e (x a) (blk a)) input encBool := by
  unfold fwd
  exact pairTest' hA e (spcaK' hx) (spcaP' hx) (spcaQ' hx) (spcaPts' hx)
    (ownOf' hx (bitsTakeWithInput hb (lenC' hx)))
    (bitsTakeWithInput (bitsDropWithInput hb (lenC' hx)) (lenA' e hx))

/-- The second test of a round. -/
theorem bwd' {A : SLRInput × List Bool → Estimate}
    (hA : ComputableInPolyTime A (encPair encSLRInput encBits) (encList encRat)) (e : ℕ)
    {x : α → SPCAInput} {blk : α → List Bool} (hx : ComputableInPolyTime x input encSPCAInput)
    (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ bwd A e (x a) (blk a)) input encBool := by
  unfold bwd
  exact pairTest' hA e (spcaK' hx) (spcaP' hx) (spcaQ' hx)
    (ownOf' hx (bitsTakeWithInput hb (lenC' hx))) (spcaPts' hx)
    (bitsTakeWithInput (bitsDropWithInput hb (unary_add' (lenC' hx) (lenA' e hx))) (lenA' e hx))

/-- **One round.** -/
theorem blockTest' {A : SLRInput × List Bool → Estimate}
    (hA : ComputableInPolyTime A (encPair encSLRInput encBits) (encList encRat)) (e : ℕ)
    {x : α → SPCAInput} {blk : α → List Bool} (hx : ComputableInPolyTime x input encSPCAInput)
    (hb : ComputableInPolyTime blk input encBits) :
    ComputableInPolyTime (fun a ↦ blockTest A e (x a) (blk a)) input encBool := by
  unfold blockTest
  exact bool_and' (fwd' hA e hx hb) (bool_not.comp (bwd' hA e hx hb))

/-- The final state with a computed answer. -/
@[fun_prop]
theorem doneSt' {c : α → Bool} (hc : ComputableInPolyTime c input encBool) :
    ComputableInPolyTime (fun a ↦ doneSt (c a)) input encSt := by
  unfold doneSt
  exact stMk' (const _) (const 0) (const 0) (const []) hc

end BDT24.Alg.PT
