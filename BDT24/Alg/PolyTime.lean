module

public import BDT24.Alg.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import BDT24.Alg.PolyTime.Test

/-!
# The pieces of the algorithm in polynomial time

* The regression algorithm, given as a machine within `c ((|x| + 2)^e + |(x, r)| + 1)` steps,
  is polynomial-time (`BDT24.Alg.polytime_of_runsInTime`).
* The initial state (`BDT24.Alg.initSt_polytime`) and one step of the fold over the coins
  (`BDT24.Alg.stepSt_polytime`) are polynomial-time, for a polynomial-time regression algorithm.
  A step runs a round when the block is full: it draws the own sample from the coins
  (`BDT24.Num.cellInv` by bisection on the series of `Φ`), builds the two regression inputs, runs
  the regression algorithm and compares the predictions.

The certificates of the pieces are in `BDT24/Alg/PolyTime/`: the numerics
(`BDT24/Alg/PolyTime/Numerics.lean`), the encodings, the parameters, the own sample and the
regression inputs (`BDT24/Alg/PolyTime/Basic.lean`), and the paired test and one round
(`BDT24/Alg/PolyTime/Test.lean`).
-/

@[expose] public section

namespace BDT24.Alg

open Turing.MultiTapeTM

/-- A regression algorithm within `c ((|x| + 2)^e + |(x, r)| + 1)` steps is polynomial-time. -/
theorem polytime_of_runsInTime {A : SLRInput × List Bool → Estimate} {e : ℕ}
    (h : RunsInTime encSLRInput encEstimate A (slrTime e)) :
    ComputableInPolyTime A (Encoding.encPair encSLRInput Encoding.encBits) encEstimate := by
  obtain ⟨c, hc⟩ := h
  have hp : Cslib.PolynomiallyBounded fun N ↦ c * ((N + 2) ^ e + N + 1) := by
    refine Cslib.polynomiallyBounded_iff_le.2 ⟨3 * c * 2 ^ e, e + 1, fun N ↦ ?_⟩
    have h1 : (N + 2) ^ e ≤ 2 ^ e * (N + 1) ^ (e + 1) := by
      calc (N + 2) ^ e ≤ (2 * (N + 1)) ^ e := Nat.pow_le_pow_left (by omega) _
        _ = 2 ^ e * (N + 1) ^ e := by rw [mul_pow]
        _ ≤ 2 ^ e * (N + 1) ^ (e + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : N + 1 ≤ 2 ^ e * (N + 1) ^ (e + 1) := by
      calc N + 1 = 1 * (N + 1) ^ 1 := by ring
        _ ≤ 2 ^ e * (N + 1) ^ (e + 1) :=
          Nat.mul_le_mul (Nat.one_le_two_pow) (Nat.pow_le_pow_right (by omega) (by omega))
    calc c * ((N + 2) ^ e + N + 1) ≤ c * (3 * (2 ^ e * (N + 1) ^ (e + 1))) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 3 * c * 2 ^ e * (N + 1) ^ (e + 1) := by ring
  refine ⟨_, _, hp, hp, hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩ <;>
  · have h1 :
        (encSLRInput xr.1).length ≤ (encPair encSLRInput encBits xr).length :=
      length_le_encPair_left encSLRInput encBits xr
    have h2 : (Encoding.encPair encSLRInput Encoding.encBits xr).length =
        (encPair encSLRInput encBits xr).length := rfl
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.pow_le_pow_left (by omega) _) _) _)

open ComputableInPolyTime PT in
/-- The initial state in polynomial time. -/
theorem initSt_polytime : ComputableInPolyTime initSt encSPCAInput encSt := by
  unfold initSt
  have hr := rounds' (spcaDelta' id') (nOf' (spcaPts' id'))
  exact SoS.PolyTime.ite_prop (binary_lt' (const 0) hr)
    (stMk' id' (const 0) hr (const []) (const true)) (const _)

open ComputableInPolyTime PT in
/-- One step of the fold in polynomial time. -/
theorem stepSt_polytime {A : SLRInput × List Bool → Estimate}
    (hA : ComputableInPolyTime A (Encoding.encPair encSLRInput Encoding.encBits) encEstimate)
    (e : ℕ) :
    ComputableInPolyTime (fun s : St × Bool ↦ stepSt A e s.1 s.2)
      (Encoding.encPair encSt Encoding.encBool) encSt := by
  have hA' : ComputableInPolyTime A (encPair encSLRInput encBits) (encList Encoding.encRat) := hA
  change ComputableInPolyTime _ (encPair encSt encBool) encSt
  unfold stepSt
  have hs : ComputableInPolyTime (fun s : St × Bool ↦ s.1) (encPair encSt encBool) encSt :=
    fst _ _
  have hb : ComputableInPolyTime (fun s : St × Bool ↦ s.2) (encPair encSt encBool) encBool :=
    snd _ _
  have hx := stX' hs
  have hj := stJ' hs
  have hM := stM' hs
  have hbuf := stBuf' hs
  have hacc := stAcc' hs
  have hblk : ComputableInPolyTime (fun s : St × Bool ↦ s.1.buf ++ [s.2])
      (encPair encSt encBool) encBits := bitsAppend hbuf (bitsCons hb (const []))
  have hj1 : ComputableInPolyTime (fun s : St × Bool ↦ s.1.j + 1) (encPair encSt encBool)
      encNat := binAdd' hj (const 1)
  have hpass := bool_and' hacc (blockTest' hA' e hx hblk)
  exact SoS.PolyTime.ite_prop (binary_lt' hj hM)
    (SoS.PolyTime.ite_prop (unary_lt' (unary_add' (length_bits.comp hbuf) (const 1))
      (lenBlk' e hx)) (stMk' hx hj hM hblk hacc)
      (SoS.PolyTime.ite_prop (binary_lt' hj1 hM) (stMk' hx hj1 hM (const []) hpass)
        (doneSt' hpass))) hs

end BDT24.Alg
