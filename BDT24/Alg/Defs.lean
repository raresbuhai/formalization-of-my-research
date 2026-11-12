module

public import BDT24.Model
public import BDT24.Alg.Numerics

/-!
# The reduction's algorithm

The PCA algorithm `BDT24.Alg.algB A e` built from a regression algorithm `A` that runs in time
`slrTime e`, following [BDT24, Lemma 4.1 and the proof of Theorem 3.1].

* **The paired test** (`BDT24.Alg.pairTest`): from two samples `u, u'` (`q`-bit integers, one
  list per point), the regression instance with design the coordinates `2, …, d+1` of both points,
  coarsened to `p` bits (`BDT24.Alg.coarsen`), and response `⌊2^p √(2/3) (u₁ + u'₁)⌋`
  (`BDT24.Alg.resp`, computed exactly with integer square roots, `BDT24.Alg.floorS`). Run `A`,
  predict with the `q`-bit design (`BDT24.Alg.predict`), and say "the first sample is planted"
  when the predictions are closer to `√(2/3)` times the first coordinates of `u` than to those of
  `u'` (`BDT24.Alg.resid`, with `√(2/3)` approximated from below to `q` bits).
* **Own null points** (`BDT24.Alg.ownSample`): `n` points of `m` coordinates, each the cell of
  `cbits` coins turned into a Gaussian by bisection on `Φ` (`BDT24.Num.cellInv`), to `q` bits.
* **One round** (`BDT24.Alg.blockTest`): a block of `lenBlk` coins gives one own sample `u'`
  and coins for two runs of `A`; the round passes when the test says that the input `u` is planted
  in the pair `(u, u')` and that `u'` is not planted in the pair `(u', u)`.
* **The algorithm** (`BDT24.Alg.algB`): `rounds δ n = min ⌊√⌊1/(2δ)⌋⌋ 2^(n / K₀)` rounds on
  consecutive blocks; output `true` (planted) when all pass. It is written as a fold over the
  coin bits (`BDT24.Alg.stepSt`) that collects a block, runs the round, and shrinks to a one-bit
  state when done, so that its running time is linear in the number of rounds and in the coins.
-/

@[expose] public section

namespace BDT24.Alg

open Encoding

/-- Samples as the algorithms read them: one list of integers per point. -/
abbrev Pts := List (List ℤ)

/-- The number of points. -/
def nOf (u : Pts) : ℕ := u.length

/-- The number of coordinates: the length of the first point. -/
def mOf (u : Pts) : ℕ := (u.headD []).length

/-! ### Rounds -/

/-- The rounds are capped at `2^(n / K₀)`. -/
def K0 : ℕ := 2 ^ 24

/-- The number of rounds `min ⌊√⌊1/(2δ)⌋⌋ 2^(n / K₀)` (`0` for `δ ≤ 0` or `δ > 1/2`). -/
def rounds (δ : ℚ) (n : ℕ) : ℕ := min (Nat.sqrt ⌊1 / (2 * δ)⌋₊) (2 ^ (n / K0))

/-! ### Own null points -/

/-- The range `R`: own points are accurate for coordinates of absolute value at most `R`. -/
def rad (n m : ℕ) : ℕ := n + m + 1

/-- The number of coins per cell. -/
def cbits (n m q : ℕ) : ℕ := (rad n m + 1) ^ 2 + q + n + m + 20

/-- The number of terms of the series of `Φ`. -/
def phiN (n m q : ℕ) : ℕ := 3 * (rad n m + 1) ^ 2 + cbits n m q

/-- The number of bisection steps. -/
def bisK (n m q : ℕ) : ℕ := q + n + m + 2 * rad n m + 20

/-- The Gaussian recovered from cell `j`. -/
def gHat (n m q j : ℕ) : ℚ :=
  Num.cellInv (cbits n m q) (phiN n m q) (bisK n m q) (cbits n m q) ((rad n m : ℚ) + 1) j

/-- The Gaussian of cell `j`, to `q` bits. -/
def ownVal (n m q j : ℕ) : ℤ := ⌊(2 : ℚ) ^ q * gHat n m q j⌋

/-- The binary number of a list of bits, least significant first. -/
def bitsNat : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bitsNat l

/-- `n` own null points of `m` coordinates, from coins: coordinate `j` of point `i` is the cell of
the block of `cbits` coins number `i m + j`. -/
def ownSample (n m q : ℕ) (c : List Bool) : Pts :=
  (List.range n).map fun i ↦ (List.range m).map fun j ↦
    ownVal n m q (bitsNat ((c.drop ((i * m + j) * cbits n m q)).take (cbits n m q)))

/-! ### The paired test -/

/-- `⌊√(2/3) t⌋`, with integer square roots: `⌊√(2t²/3)⌋` for `t ≥ 0` and `-⌈√(2t²/3)⌉`
otherwise. -/
def floorS (t : ℚ) : ℤ :=
  if 0 ≤ t then (Nat.sqrt ⌊2 * t ^ 2 / 3⌋₊ : ℤ)
  else -((Nat.sqrt (⌈2 * t ^ 2 / 3⌉₊ - 1) : ℤ) + 1)

/-- The response `⌊2^p √(2/3) (a + b)/2^q⌋` of two `q`-bit coordinates, to `p` bits. -/
def resp (p q : ℕ) (a b : ℤ) : ℤ := floorS ((2 : ℚ) ^ p * (a + b) / 2 ^ q)

/-- A `q`-bit coordinate to `p` bits: `⌊a / 2^(q - p)⌋`. -/
def coarsen (p q : ℕ) (a : ℤ) : ℤ := ⌊(a : ℚ) / 2 ^ (q - p)⌋

/-- The design row of a pair of points: coordinates `2, …, m` of both, to `p` bits. -/
def slrRow (p q : ℕ) (r r' : List ℤ) : List ℤ :=
  r.tail.map (coarsen p q) ++ r'.tail.map (coarsen p q)

/-- The regression input of a pair of samples. -/
def slrInputOf (k p q : ℕ) (u u' : Pts) : SLRInput :=
  ⟨k, p, List.zipWith (slrRow p q) u u',
    List.zipWith (fun r r' ↦ resp p q (r.headD 0) (r'.headD 0)) u u'⟩

/-- The prediction `∑ⱼ (row j / 2^q) x̂ⱼ` of a row of `q`-bit integers. -/
def dotQ (q : ℕ) (row : List ℤ) (xh : List ℚ) : ℚ :=
  ((List.range row.length).map fun j ↦ (row.getD j 0 : ℚ) / 2 ^ q * xh.getD j 0).sum

/-- The predictions of the estimate on the `q`-bit design of a pair of samples. -/
def predict (q : ℕ) (u u' : Pts) (xh : Estimate) : List ℚ :=
  List.zipWith (fun r r' ↦ dotQ q (r.tail ++ r'.tail) xh) u u'

/-- `√(2/3)` from below, to `q` bits. -/
def sQ (q : ℕ) : ℚ := SoS.Loop.sqrtP q (2 / 3)

/-- The squared distance of the predictions to `√(2/3)` times the first coordinates of `u`. -/
def resid (q : ℕ) (pr : List ℚ) (u : Pts) : ℚ :=
  (List.zipWith (fun y r ↦ (y - sQ q * ((r.headD 0 : ℚ) / 2 ^ q)) ^ 2) pr u).sum

/-- **The paired test**: is the first sample the planted one? `A` gets the first
`slrTime e` of the coins `r`. -/
def pairTest (A : SLRInput × List Bool → Estimate) (e k p q : ℕ) (u u' : Pts) (r : List Bool) :
    Bool :=
  decide (resid q (predict q u u' (A (slrInputOf k p q u u',
      r.take (slrTime e (slrInputOf k p q u u'))))) u ≤
    resid q (predict q u u' (A (slrInputOf k p q u u',
      r.take (slrTime e (slrInputOf k p q u u'))))) u')

/-! ### One round -/

/-- A bound on the length of the regression inputs on samples with small coordinates. -/
def linB (n m k p : ℕ) : ℕ :=
  128 * (n + 1) * (m + 1) * (p + n + m + 10) + 4 * (encNat k).length + 64

/-- The coins of one run of `A`. -/
def lenA (e : ℕ) (x : SPCAInput) : ℕ := (linB (nOf x.points) (mOf x.points) x.k x.p + 2) ^ e

/-- The coins of one own sample. -/
def lenC (x : SPCAInput) : ℕ :=
  nOf x.points * mOf x.points * cbits (nOf x.points) (mOf x.points) x.q

/-- The coins of one round. -/
def lenBlk (e : ℕ) (x : SPCAInput) : ℕ := lenC x + 2 * lenA e x

/-- The own sample of a block. -/
def ownOf (x : SPCAInput) (c : List Bool) : Pts :=
  ownSample (nOf x.points) (mOf x.points) x.q c

/-- The first test of a round: the input against the own sample. -/
def fwd (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput) (blk : List Bool) : Bool :=
  pairTest A e x.k x.p x.q x.points (ownOf x (blk.take (lenC x)))
    ((blk.drop (lenC x)).take (lenA e x))

/-- The second test of a round: the own sample against the input. -/
def bwd (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput) (blk : List Bool) : Bool :=
  pairTest A e x.k x.p x.q (ownOf x (blk.take (lenC x))) x.points
    ((blk.drop (lenC x + lenA e x)).take (lenA e x))

/-- **One round** passes when the input is planted against the own sample and not the other way
round. -/
def blockTest (A : SLRInput × List Bool → Estimate) (e : ℕ) (x : SPCAInput) (blk : List Bool) :
    Bool :=
  fwd A e x blk && !bwd A e x blk

/-! ### The algorithm -/

/-- The state of the fold over the coins: the input, the round `j` of `M`, the coins of the
current block, and whether all rounds so far passed. It is running while `j < M`. -/
structure St where
  /-- The input. -/
  x : SPCAInput
  /-- The current round. -/
  j : ℕ
  /-- The number of rounds. -/
  M : ℕ
  /-- The coins of the current block so far. -/
  buf : List Bool
  /-- Whether all rounds so far passed. -/
  acc : Bool

/-- States are encoded as their five fields. -/
def encSt : St ↪ List Bool :=
  ⟨fun s ↦ encPair encSPCAInput (encPair encNat (encPair encNat (encPair encBits encBool)))
      (s.x, s.j, s.M, s.buf, s.acc), by
    rintro ⟨x, j, M, b, a⟩ ⟨x', j', M', b', a'⟩ h
    have h' := (encPair encSPCAInput
      (encPair encNat (encPair encNat (encPair encBits encBool)))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- The final state, with the answer `a` and nothing else. -/
def doneSt (a : Bool) : St := ⟨⟨0, 0, 0, 0, []⟩, 0, 0, [], a⟩

/-- The initial state: round `0` of `rounds δ n`, or done with answer `true` if there are no
rounds. -/
def initSt (x : SPCAInput) : St :=
  if 0 < rounds x.δ (nOf x.points) then ⟨x, 0, rounds x.δ (nOf x.points), [], true⟩
  else doneSt true

/-- One coin: add it to the block; when the block is full, run the round, and move to the next
round or finish. -/
def stepSt (A : SLRInput × List Bool → Estimate) (e : ℕ) (s : St) (b : Bool) : St :=
  if s.j < s.M then
    if s.buf.length + 1 < lenBlk e s.x then ⟨s.x, s.j, s.M, s.buf ++ [b], s.acc⟩
    else if s.j + 1 < s.M then ⟨s.x, s.j + 1, s.M, [], s.acc && blockTest A e s.x (s.buf ++ [b])⟩
    else doneSt (s.acc && blockTest A e s.x (s.buf ++ [b]))
  else s

/-- **The PCA algorithm**: fold the coins into the state; the answer is `true` (planted) when all
rounds passed. -/
def algB (A : SLRInput × List Bool → Estimate) (e : ℕ) (xr : SPCAInput × List Bool) : Bool :=
  (xr.2.foldl (stepSt A e) (initSt xr.1)).acc

end BDT24.Alg
