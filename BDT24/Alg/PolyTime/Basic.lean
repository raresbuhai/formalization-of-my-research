module

public import BDT24.Alg.Defs
public import BDT24.Alg.PolyTime.Numerics
public import Background.PolyTime.Lists
public import Mathlib.Data.List.GetD
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# The pieces of the paired test in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`), in the compositional style of
complexitylib, for the functions of `BDT24/Alg/Defs.lean` below the paired test:

* the encodings of the inputs and of the states as tuples of complexitylib's encodings (the custom
  embeddings `BDT24.encSLRInput`, `BDT24.encSPCAInput` and `BDT24.Alg.encSt` agree with them
  definitionally), with the fields read off and the structures built;
* the parameters: the number of rounds (in binary, from `δ` in binary), the numbers of points and
  coordinates, and the parameters of the own sample (in unary);
* the own sample (`BDT24.Alg.ownSample`), cell by cell with `BDT24.Alg.PT.cellInv'`;
* the regression input of a pair of samples (`BDT24.Alg.slrInputOf`), with the integer square
  roots of `BDT24.Alg.floorS`, the predictions and the residuals.
-/

@[expose] public section

namespace BDT24.Alg.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open SoS.PolyTime SoS.Loop

variable {α : Type} {input : α ↪ List Bool}

/-! ### Small certificates -/

/-- The sum of two binary naturals. -/
theorem binAdd' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add.comp (g := fun a ↦ (f a, g a))
    (hf.prod hg).tidy)

/-- The smaller of two binary naturals. -/
theorem binMin' {f g : α → ℕ} (hf : ComputableInPolyTime f input encNat)
    (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun a ↦ min (f a) (g a)) input encNat := by
  have h := ite_prop (p := fun a ↦ f a ≤ g a) (binary_le' hf hg) hf hg
  exact h.of_enc_eq fun a ↦ by rw [min_def]

/-- The natural floor of a rational, in binary. -/
theorem rat_natFloor' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ ⌊f a⌋₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (⌊f a⌋).toNat) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_toNat.comp (rat_floor' hf).tidy)
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_toNat]

/-- The natural ceiling of a rational, in binary. -/
theorem rat_natCeil' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ ⌈f a⌉₊) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ (-⌊-f a⌋).toNat) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.intBin_toNat.comp
      (ComputableTidilyInPolyTime.intBin_neg.comp (rat_floor' (rat_neg' hf)).tidy))
  refine h.of_enc_eq fun a ↦ ?_
  rw [Int.floor_neg, neg_neg, Int.ceil_toNat]

/-- A binary natural as a binary integer. -/
theorem int_ofNat' {f : α → ℕ} (hf : ComputableInPolyTime f input encNat) :
    ComputableInPolyTime (fun a ↦ ((f a : ℕ) : ℤ)) input encIntBin :=
  intBin_natCast.comp hf

/-- The negation of a binary integer. -/
theorem int_neg' {f : α → ℤ} (hf : ComputableInPolyTime f input encIntBin) :
    ComputableInPolyTime (fun a ↦ -f a) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_neg.comp hf.tidy)

/-- The sum of two binary integers. -/
theorem int_add' {f g : α → ℤ} (hf : ComputableInPolyTime f input encIntBin)
    (hg : ComputableInPolyTime g input encIntBin) :
    ComputableInPolyTime (fun a ↦ f a + g a) input encIntBin :=
  .of_tidy (ComputableTidilyInPolyTime.intBin_add' hf.tidy hg.tidy)

/-- `List.zipWith`, for a function with the input. -/
theorem zipWith' {β γ δ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {encD : δ ↪ List Bool} {f : α → β → γ → δ} {u : α → List β} {v : α → List γ}
    (hu : ComputableInPolyTime u input (encList encB))
    (hv : ComputableInPolyTime v input (encList encC))
    (hf : ComputableInPolyTime (fun p : α × (β × γ) ↦ f p.1 p.2.1 p.2.2)
      (encPair input (encPair encB encC)) encD) :
    ComputableInPolyTime (fun a ↦ List.zipWith (f a) (u a) (v a)) input (encList encD) := by
  have hz : ComputableInPolyTime (fun a ↦ (u a).zip (v a)) input
      (encList (encPair encB encC)) :=
    .of_tidy ((ComputableTidilyInPolyTime.zip encB encC).comp (g := fun a ↦ (u a, v a))
      (hu.prod hv).tidy)
  have h := mapWithInput (f := fun a (x : β × γ) ↦ f a x.1 x.2) hz hf
  refine h.of_enc_eq fun a ↦ ?_
  rw [List.map_zip_eq_zipWith]
  rfl

/-! ### Encodings -/

/-- Samples: one list of binary integers per point. -/
abbrev encPts : Pts ↪ List Bool := encList (encList encIntBin)

/-- Regression inputs as tuples: `k` in binary, `p` in unary, the design and the responses. -/
abbrev encSLRT : ℕ × ℕ × Pts × List ℤ ↪ List Bool :=
  encPair encNat (encPair encUnary (encPair encPts (encList encIntBin)))

/-- PCA inputs as tuples: `δ`, `p` in unary, `k` in binary, `q` in unary, and the points. -/
abbrev encSPCAT : ℚ × ℕ × ℕ × ℕ × Pts ↪ List Bool :=
  encPair encRat (encPair encUnary (encPair encNat (encPair encUnary encPts)))

/-- States as tuples: the input, `j` and `M` in binary, the block, and the answer so far. -/
abbrev encStT : SPCAInput × ℕ × ℕ × List Bool × Bool ↪ List Bool :=
  encPair encSPCAInput (encPair encNat (encPair encNat (encPair encBits encBool)))

/-- Estimates are encoded as complexitylib's lists of rationals. -/
theorem encEstimate_eq : encEstimate = encList encRat := rfl

/-- Building a regression input from its fields. -/
theorem slrMk_polytime : ComputableInPolyTime
    (fun t : ℕ × ℕ × Pts × List ℤ ↦ (⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩ : SLRInput)) encSLRT
    encSLRInput :=
  of_eq fun _ ↦ rfl

/-- A regression input from computed fields. -/
@[fun_prop]
theorem slrMk' {k p : α → ℕ} {d : α → Pts} {y : α → List ℤ}
    (hk : ComputableInPolyTime k input encNat) (hp : ComputableInPolyTime p input encUnary)
    (hd : ComputableInPolyTime d input encPts)
    (hy : ComputableInPolyTime y input (encList encIntBin)) :
    ComputableInPolyTime (fun a ↦ (⟨k a, p a, d a, y a⟩ : SLRInput)) input encSLRInput :=
  slrMk_polytime.comp (g := fun a ↦ (k a, p a, d a, y a)) (hk.prod (hp.prod (hd.prod hy)))

/-- The fields of a PCA input. -/
theorem spcaUn_polytime : ComputableInPolyTime
    (fun x : SPCAInput ↦ (x.δ, x.p, x.k, x.q, x.points)) encSPCAInput encSPCAT :=
  of_eq fun _ ↦ rfl

/-- The failure probability of a PCA input. -/
@[fun_prop]
theorem spcaDelta' {f : α → SPCAInput} (hf : ComputableInPolyTime f input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ (f a).δ) input encRat :=
  (fst _ _).comp (spcaUn_polytime.comp hf)

/-- The regression precision of a PCA input, in unary. -/
@[fun_prop]
theorem spcaP' {f : α → SPCAInput} (hf : ComputableInPolyTime f input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ (f a).p) input encUnary :=
  (fst _ _).comp ((snd _ _).comp (spcaUn_polytime.comp hf))

/-- The sparsity of a PCA input, in binary. -/
@[fun_prop]
theorem spcaK' {f : α → SPCAInput} (hf : ComputableInPolyTime f input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ (f a).k) input encNat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (spcaUn_polytime.comp hf)))

/-- The precision of a PCA input, in unary. -/
@[fun_prop]
theorem spcaQ' {f : α → SPCAInput} (hf : ComputableInPolyTime f input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ (f a).q) input encUnary :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (spcaUn_polytime.comp hf))))

/-- The points of a PCA input. -/
@[fun_prop]
theorem spcaPts' {f : α → SPCAInput} (hf : ComputableInPolyTime f input encSPCAInput) :
    ComputableInPolyTime (fun a ↦ (f a).points) input encPts :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (spcaUn_polytime.comp hf))))

/-- Building a state from its fields. -/
theorem stMk_polytime : ComputableInPolyTime
    (fun t : SPCAInput × ℕ × ℕ × List Bool × Bool ↦
      (⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩ : St)) encStT encSt :=
  of_eq fun ⟨_, _, _, _, _⟩ ↦ rfl

/-- A state from computed fields. -/
@[fun_prop]
theorem stMk' {x : α → SPCAInput} {j M : α → ℕ} {b : α → List Bool} {c : α → Bool}
    (hx : ComputableInPolyTime x input encSPCAInput) (hj : ComputableInPolyTime j input encNat)
    (hM : ComputableInPolyTime M input encNat) (hb : ComputableInPolyTime b input encBits)
    (hc : ComputableInPolyTime c input encBool) :
    ComputableInPolyTime (fun a ↦ (⟨x a, j a, M a, b a, c a⟩ : St)) input encSt :=
  stMk_polytime.comp (g := fun a ↦ (x a, j a, M a, b a, c a))
    (hx.prod (hj.prod (hM.prod (hb.prod hc))))

/-- The fields of a state. -/
theorem stUn_polytime : ComputableInPolyTime (fun s : St ↦ (s.x, s.j, s.M, s.buf, s.acc)) encSt
    encStT :=
  of_eq fun _ ↦ rfl

/-- The input of a state. -/
@[fun_prop]
theorem stX' {f : α → St} (hf : ComputableInPolyTime f input encSt) :
    ComputableInPolyTime (fun a ↦ (f a).x) input encSPCAInput :=
  (fst _ _).comp (stUn_polytime.comp hf)

/-- The round of a state. -/
@[fun_prop]
theorem stJ' {f : α → St} (hf : ComputableInPolyTime f input encSt) :
    ComputableInPolyTime (fun a ↦ (f a).j) input encNat :=
  (fst _ _).comp ((snd _ _).comp (stUn_polytime.comp hf))

/-- The number of rounds of a state. -/
@[fun_prop]
theorem stM' {f : α → St} (hf : ComputableInPolyTime f input encSt) :
    ComputableInPolyTime (fun a ↦ (f a).M) input encNat :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp (stUn_polytime.comp hf)))

/-- The block of a state. -/
@[fun_prop]
theorem stBuf' {f : α → St} (hf : ComputableInPolyTime f input encSt) :
    ComputableInPolyTime (fun a ↦ (f a).buf) input encBits :=
  (fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (stUn_polytime.comp hf))))

/-- The answer so far of a state. -/
@[fun_prop]
theorem stAcc' {f : α → St} (hf : ComputableInPolyTime f input encSt) :
    ComputableInPolyTime (fun a ↦ (f a).acc) input encBool :=
  (snd _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (stUn_polytime.comp hf))))

/-! ### Parameters -/

/-- The number of points, in unary. -/
@[fun_prop]
theorem nOf' {f : α → Pts} (hf : ComputableInPolyTime f input encPts) :
    ComputableInPolyTime (fun a ↦ nOf (f a)) input encUnary :=
  (length_list _).comp hf

/-- The number of coordinates, in unary. -/
@[fun_prop]
theorem mOf' {f : α → Pts} (hf : ComputableInPolyTime f input encPts) :
    ComputableInPolyTime (fun a ↦ mOf (f a)) input encUnary :=
  (length_list _).comp ((headD (encA := encList encIntBin) (encL := encPts) []).comp hf)

/-- The number of rounds, in binary. -/
@[fun_prop]
theorem rounds' {d : α → ℚ} {n : α → ℕ} (hd : ComputableInPolyTime d input encRat)
    (hn : ComputableInPolyTime n input encUnary) :
    ComputableInPolyTime (fun a ↦ rounds (d a) (n a)) input encNat := by
  unfold rounds
  have h1 : ComputableInPolyTime (fun a ↦ Nat.sqrt ⌊1 / (2 * d a)⌋₊) input encNat :=
    binary_sqrt' (rat_natFloor' (rat_div' (const 1) (rat_mul' (const 2) hd)))
  have h2 : ComputableInPolyTime (fun a ↦ 2 ^ (n a / K0)) input encNat :=
    binary_two_pow.comp ((unary_div_const K0).comp hn)
  exact binMin' h1 h2

/-- The range of the own points. -/
@[fun_prop]
theorem rad' {n m : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) :
    ComputableInPolyTime (fun a ↦ rad (n a) (m a)) input encUnary := by
  unfold rad; fun_prop

/-- The coins per cell. -/
@[fun_prop]
theorem cbits' {n m q : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a ↦ cbits (n a) (m a) (q a)) input encUnary := by
  unfold cbits
  have := rad' hn hm
  fun_prop

/-- The number of terms of the series of `Φ`. -/
@[fun_prop]
theorem phiN' {n m q : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a ↦ phiN (n a) (m a) (q a)) input encUnary := by
  unfold phiN
  have := rad' hn hm
  have := cbits' hn hm hq
  fun_prop

/-- The number of bisection steps. -/
@[fun_prop]
theorem bisK' {n m q : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a ↦ bisK (n a) (m a) (q a)) input encUnary := by
  unfold bisK
  have := rad' hn hm
  fun_prop

/-! ### The own sample -/

/-- The Gaussian of a cell. -/
@[fun_prop]
theorem gHat' {n m q j : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hq : ComputableInPolyTime q input encUnary)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ gHat (n a) (m a) (q a) (j a)) input encRat := by
  unfold gHat
  exact cellInv' (cbits' hn hm hq) (phiN' hn hm hq) (bisK' hn hm hq) (cbits' hn hm hq)
    (rad' hn hm) hj

/-- The Gaussian of a cell, to `q` bits. -/
@[fun_prop]
theorem ownVal' {n m q j : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (hq : ComputableInPolyTime q input encUnary)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ ownVal (n a) (m a) (q a) (j a)) input encIntBin := by
  unfold ownVal
  exact rat_floor' (rat_mul' (rat_two_pow' hq) (gHat' hn hm hq hj))

/-- `BDT24.Alg.bitsNat` is complexitylib's reading of a little-endian word. -/
theorem bitsNat_eq_ofBits (l : List Bool) : bitsNat l = ofBits l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [bitsNat, ih]
    cases b
    · simp [ofBits, Nat.bit]
    · simp [ofBits, Nat.bit]
      omega

/-- The binary number of a computed word. -/
@[fun_prop]
theorem bitsNat' {f : α → List Bool} (hf : ComputableInPolyTime f input encBits) :
    ComputableInPolyTime (fun a ↦ bitsNat (f a)) input encNat := by
  have h : ComputableInPolyTime (fun a ↦ ofBits (f a)) input encNat :=
    .of_tidy (ComputableTidilyInPolyTime.bitsToNat.comp hf.tidy)
  exact h.of_enc_eq fun a ↦ by rw [bitsNat_eq_ofBits]

/-- **The own sample**, cell by cell. -/
@[fun_prop]
theorem ownSample' {n m q : α → ℕ} {c : α → List Bool}
    (hn : ComputableInPolyTime n input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hq : ComputableInPolyTime q input encUnary) (hc : ComputableInPolyTime c input encBits) :
    ComputableInPolyTime (fun a ↦ ownSample (n a) (m a) (q a) (c a)) input encPts := by
  unfold ownSample
  have hn2 := hn.comp (fst input encUnary)
  have hm2 := hm.comp (fst input encUnary)
  have hq2 := hq.comp (fst input encUnary)
  have hn3 := hn2.comp (fst (encPair input encUnary) encUnary)
  have hm3 := hm2.comp (fst (encPair input encUnary) encUnary)
  have hq3 := hq2.comp (fst (encPair input encUnary) encUnary)
  have hc3 := (hc.comp (fst input encUnary)).comp (fst (encPair input encUnary) encUnary)
  have hi3 := (snd input encUnary).comp (fst (encPair input encUnary) encUnary)
  have hj3 := snd (encPair input encUnary) encUnary
  have hB := cbits' hn3 hm3 hq3
  have hoff : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦
      (p.1.2 * m p.1.1 + p.2) * cbits (n p.1.1) (m p.1.1) (q p.1.1))
      (encPair (encPair input encUnary) encUnary) encUnary :=
    unary_mul' (unary_add' (unary_mul' hi3 hm3) hj3) hB
  have hcell := ownVal' hn3 hm3 hq3 (bitsNat' (bitsTakeWithInput (bitsDropWithInput hc3 hoff) hB))
  exact mapWithInput (range.comp hn) (mapWithInput (range.comp hm2) hcell)

/-! ### The regression input of a pair of samples -/

/-- `⌊√(2/3) t⌋`, with integer square roots. -/
@[fun_prop]
theorem floorS' {f : α → ℚ} (hf : ComputableInPolyTime f input encRat) :
    ComputableInPolyTime (fun a ↦ floorS (f a)) input encIntBin := by
  unfold floorS
  have ht : ComputableInPolyTime (fun a ↦ 2 * f a ^ 2 / 3) input encRat := by fun_prop
  have h1 : ComputableInPolyTime (fun a ↦ ((Nat.sqrt ⌊2 * f a ^ 2 / 3⌋₊ : ℕ) : ℤ)) input
      encIntBin := int_ofNat' (binary_sqrt' (rat_natFloor' ht))
  have h2 : ComputableInPolyTime (fun a ↦ -(((Nat.sqrt (⌈2 * f a ^ 2 / 3⌉₊ - 1) : ℕ) : ℤ) + 1))
      input encIntBin :=
    int_neg' (int_add' (int_ofNat' (binary_sqrt' (binary_sub' (rat_natCeil' ht) (const 1))))
      (const 1))
  exact ite_prop (rat_le' (const 0) hf) h1 h2

/-- The response of two coordinates. -/
@[fun_prop]
theorem resp' {p q : α → ℕ} {u v : α → ℤ} (hp : ComputableInPolyTime p input encUnary)
    (hq : ComputableInPolyTime q input encUnary) (hu : ComputableInPolyTime u input encIntBin)
    (hv : ComputableInPolyTime v input encIntBin) :
    ComputableInPolyTime (fun a ↦ resp (p a) (q a) (u a) (v a)) input encIntBin := by
  unfold resp
  exact floorS' (rat_div' (rat_mul' (rat_two_pow' hp) (rat_add' (rat_intCast' hu)
    (rat_intCast' hv))) (rat_two_pow' hq))

/-- A coordinate to `p` bits. -/
@[fun_prop]
theorem coarsen' {p q : α → ℕ} {u : α → ℤ} (hp : ComputableInPolyTime p input encUnary)
    (hq : ComputableInPolyTime q input encUnary) (hu : ComputableInPolyTime u input encIntBin) :
    ComputableInPolyTime (fun a ↦ coarsen (p a) (q a) (u a)) input encIntBin := by
  unfold coarsen
  exact rat_floor' (rat_div' (rat_intCast' hu) (rat_two_pow' (unary_sub' hq hp)))

/-- The tail of a computed row. -/
theorem rowTail' {r : α → List ℤ} (hr : ComputableInPolyTime r input (encList encIntBin)) :
    ComputableInPolyTime (fun a ↦ (r a).tail) input (encList encIntBin) :=
  (tail (encA := encIntBin) (encL := encList encIntBin)).comp hr

/-- The first coordinate of a computed row. -/
theorem rowHead' {r : α → List ℤ} (hr : ComputableInPolyTime r input (encList encIntBin)) :
    ComputableInPolyTime (fun a ↦ (r a).headD 0) input encIntBin :=
  (headD (encA := encIntBin) (encL := encList encIntBin) 0).comp hr

/-- The design row of a pair of points. -/
@[fun_prop]
theorem slrRow' {p q : α → ℕ} {r r' : α → List ℤ} (hp : ComputableInPolyTime p input encUnary)
    (hq : ComputableInPolyTime q input encUnary)
    (hr : ComputableInPolyTime r input (encList encIntBin))
    (hr' : ComputableInPolyTime r' input (encList encIntBin)) :
    ComputableInPolyTime (fun a ↦ slrRow (p a) (q a) (r a) (r' a)) input (encList encIntBin) := by
  unfold slrRow
  have hc := coarsen' (hp.comp (fst input encIntBin)) (hq.comp (fst input encIntBin))
    (snd input encIntBin)
  exact listAppend' (mapWithInput (f := fun a z ↦ coarsen (p a) (q a) z) (rowTail' hr) hc)
    (mapWithInput (f := fun a z ↦ coarsen (p a) (q a) z) (rowTail' hr') hc)

/-- **The regression input of a pair of samples.** -/
@[fun_prop]
theorem slrInputOf' {k p q : α → ℕ} {u u' : α → Pts} (hk : ComputableInPolyTime k input encNat)
    (hp : ComputableInPolyTime p input encUnary) (hq : ComputableInPolyTime q input encUnary)
    (hu : ComputableInPolyTime u input encPts) (hu' : ComputableInPolyTime u' input encPts) :
    ComputableInPolyTime (fun a ↦ slrInputOf (k a) (p a) (q a) (u a) (u' a)) input
      encSLRInput := by
  unfold slrInputOf
  set E := encPair input (encPair (encList encIntBin) (encList encIntBin))
  have hp2 : ComputableInPolyTime (fun x : α × (List ℤ × List ℤ) ↦ p x.1) E encUnary :=
    hp.comp (fst _ _)
  have hq2 : ComputableInPolyTime (fun x : α × (List ℤ × List ℤ) ↦ q x.1) E encUnary :=
    hq.comp (fst _ _)
  have hr : ComputableInPolyTime (fun x : α × (List ℤ × List ℤ) ↦ x.2.1) E
      (encList encIntBin) := (fst _ _).comp (snd _ _)
  have hr' : ComputableInPolyTime (fun x : α × (List ℤ × List ℤ) ↦ x.2.2) E
      (encList encIntBin) := (snd _ _).comp (snd _ _)
  exact slrMk' hk hp (zipWith' (f := fun a r r' ↦ slrRow (p a) (q a) r r') hu hu'
    (slrRow' hp2 hq2 hr hr'))
    (zipWith' (f := fun a (r r' : List ℤ) ↦ resp (p a) (q a) (r.headD 0) (r'.headD 0)) hu hu'
      (resp' hp2 hq2 (rowHead' hr) (rowHead' hr')))

/-! ### Predictions and residuals -/

/-- The prediction of a row. -/
@[fun_prop]
theorem dotQ' {q : α → ℕ} {r : α → List ℤ} {xh : α → List ℚ}
    (hq : ComputableInPolyTime q input encUnary)
    (hr : ComputableInPolyTime r input (encList encIntBin))
    (hxh : ComputableInPolyTime xh input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ dotQ (q a) (r a) (xh a)) input encRat := by
  unfold dotQ
  have hr2 := hr.comp (fst input encUnary)
  have hxh2 := hxh.comp (fst input encUnary)
  have hq2 := hq.comp (fst input encUnary)
  have hj := snd input encUnary
  exact rat_sum' (mapWithInput (range.comp ((length_list _).comp hr))
    (rat_mul' (rat_div' (rat_intCast' (listGetDWithInput hr2 hj 0)) (rat_two_pow' hq2))
      (listGetDWithInput hxh2 hj 0)))

/-- The predictions of an estimate on a pair of samples. -/
@[fun_prop]
theorem predict' {q : α → ℕ} {u u' : α → Pts} {xh : α → List ℚ}
    (hq : ComputableInPolyTime q input encUnary) (hu : ComputableInPolyTime u input encPts)
    (hu' : ComputableInPolyTime u' input encPts)
    (hxh : ComputableInPolyTime xh input (encList encRat)) :
    ComputableInPolyTime (fun a ↦ predict (q a) (u a) (u' a) (xh a)) input (encList encRat) := by
  unfold predict
  set E := encPair input (encPair (encList encIntBin) (encList encIntBin))
  have hr : ComputableInPolyTime (fun x : α × (List ℤ × List ℤ) ↦ x.2.1) E
      (encList encIntBin) := (fst _ _).comp (snd _ _)
  have hr' : ComputableInPolyTime (fun x : α × (List ℤ × List ℤ) ↦ x.2.2) E
      (encList encIntBin) := (snd _ _).comp (snd _ _)
  exact zipWith' (f := fun a (r r' : List ℤ) ↦ dotQ (q a) (r.tail ++ r'.tail) (xh a)) hu hu'
    (dotQ' (hq.comp (fst _ _)) (listAppend' (rowTail' hr) (rowTail' hr')) (hxh.comp (fst _ _)))

/-- `√(2/3)` from below. -/
@[fun_prop]
theorem sQ' {q : α → ℕ} (hq : ComputableInPolyTime q input encUnary) :
    ComputableInPolyTime (fun a ↦ sQ (q a)) input encRat := by
  unfold sQ
  exact sqrtP' hq (const _)

/-- The squared distance of predictions to the first coordinates of a sample. -/
@[fun_prop]
theorem resid' {q : α → ℕ} {pr : α → List ℚ} {u : α → Pts}
    (hq : ComputableInPolyTime q input encUnary)
    (hpr : ComputableInPolyTime pr input (encList encRat))
    (hu : ComputableInPolyTime u input encPts) :
    ComputableInPolyTime (fun a ↦ resid (q a) (pr a) (u a)) input encRat := by
  unfold resid
  set E := encPair input (encPair encRat (encList encIntBin))
  have hq2 : ComputableInPolyTime (fun x : α × (ℚ × List ℤ) ↦ q x.1) E encUnary :=
    hq.comp (fst _ _)
  have hy : ComputableInPolyTime (fun x : α × (ℚ × List ℤ) ↦ x.2.1) E encRat :=
    (fst _ _).comp (snd _ _)
  have hr : ComputableInPolyTime (fun x : α × (ℚ × List ℤ) ↦ x.2.2) E (encList encIntBin) :=
    (snd _ _).comp (snd _ _)
  exact rat_sum' (zipWith' (f := fun a (y : ℚ) (r : List ℤ) ↦
      (y - sQ (q a) * ((r.headD 0 : ℚ) / 2 ^ (q a))) ^ 2) hpr hu
    (rat_sq' (rat_sub' hy (rat_mul' (sQ' hq2) (rat_div' (rat_intCast' (rowHead' hr))
      (rat_two_pow' hq2))))))

end BDT24.Alg.PT
