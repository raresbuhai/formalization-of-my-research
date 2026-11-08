module

public import BHJK25.RS.Alg.Basic
public import Background.PolyTime.Lists
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# A guess is checked in polynomial time

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the test of a guess
(`BHJK25.RS.AlgAux.guessOK`), ending with `BHJK25.RS.AlgAux.guessOK_polytime`. The data of a run
(`BHJK25.RS.AlgAux.Dat`) is encoded as the tuple of its fields (`BHJK25.RS.AlgAux.encDat`), with
the numbers `n`, `ℓ`, `r`, `L`, `m`, `W` in unary, the table as a bit string, and the coefficient
lists in binary; the index of a guess is in binary. Since `n` is in unary, the indices into the
table are polynomial in the length of the data; they are computed in binary, and the table is read
at a binary index.
-/

@[expose] public section

namespace BHJK25.RS.AlgAux

open Turing.MultiTapeTM ComputableInPolyTime

/-! ### Encodings -/

/-- The data of a run, as a tuple. -/
abbrev DatTuple : Type := ℕ × List Bool × ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List (List ℕ)

/-- The fields of the data. -/
def Dat.toTuple (d : Dat) : DatTuple := (d.n, d.w, d.l, d.r, d.L, d.m, d.W, d.fl, d.elts)

theorem Dat.toTuple_injective : Function.Injective Dat.toTuple := by
  rintro ⟨⟩ ⟨⟩ h
  simp only [Dat.toTuple, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- The encoding of the tuple of the fields of the data. -/
abbrev encTuple : DatTuple ↪ List Bool :=
  encPair encUnary (encPair encBits (encPair encUnary (encPair encUnary (encPair encUnary
    (encPair encUnary (encPair encUnary (encPair (encList encNat) (encList (encList encNat)))))))))

/-- The encoding of the data of a run: its fields. -/
def encDat : Dat ↪ List Bool :=
  ⟨fun d ↦ encTuple d.toTuple, encTuple.injective.comp Dat.toTuple_injective⟩

/-- The points, as pairs of bit lists. -/
abbrev encPts : List (List ℕ × List ℕ) ↪ List Bool :=
  encList (encPair (encList encNat) (encList encNat))

variable {α : Type} {input : α ↪ List Bool}

theorem toTuple_polytime : ComputableInPolyTime Dat.toTuple encDat encTuple := of_eq fun _ ↦ rfl

/-! ### Small certificates -/

/-- A case distinction on a decidable proposition. -/
theorem ite_prop {β : Type} {encB : β ↪ List Bool} {p : α → Prop} [DecidablePred p]
    {f g : α → β} (hp : ComputableInPolyTime (fun a ↦ decide (p a)) input encBool)
    (hf : ComputableInPolyTime f input encB) (hg : ComputableInPolyTime g input encB) :
    ComputableInPolyTime (fun a ↦ if p a then f a else g a) input encB := by
  have := ite' hp hf hg
  simpa only [decide_eq_true_eq] using this

/-- A unary natural, in binary. -/
theorem toBin {f : α → ℕ} (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime f input encNat :=
  unary_to_binary.comp' hf

/-- The sum of a list of binary naturals. -/
theorem sum' {f : α → List ℕ} (hf : ComputableInPolyTime f input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ (f a).sum) input encNat :=
  (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_sum).comp' hf

/-! ### The fields of the data -/

section Fields

variable {d : α → Dat} (hd : ComputableInPolyTime d input encDat)
include hd

theorem tup_polytime : ComputableInPolyTime (fun a ↦ (d a).toTuple) input encTuple :=
  toTuple_polytime.comp' hd

theorem dat_n : ComputableInPolyTime (fun a ↦ (d a).n) input encUnary :=
  (fst _ _).comp' (tup_polytime hd)

theorem dat_w : ComputableInPolyTime (fun a ↦ (d a).w) input encBits :=
  (fst _ _).comp' ((snd _ _).comp' (tup_polytime hd))

theorem dat_l : ComputableInPolyTime (fun a ↦ (d a).l) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' (tup_polytime hd)))

theorem dat_r : ComputableInPolyTime (fun a ↦ (d a).r) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' (tup_polytime hd))))

theorem dat_L : ComputableInPolyTime (fun a ↦ (d a).L) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    (tup_polytime hd)))))

theorem dat_m : ComputableInPolyTime (fun a ↦ (d a).m) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    ((snd _ _).comp' (tup_polytime hd))))))

theorem dat_W : ComputableInPolyTime (fun a ↦ (d a).W) input encUnary :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    ((snd _ _).comp' ((snd _ _).comp' (tup_polytime hd)))))))

theorem dat_fl : ComputableInPolyTime (fun a ↦ (d a).fl) input (encList encNat) :=
  (fst _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' (tup_polytime hd))))))))

theorem dat_elts : ComputableInPolyTime (fun a ↦ (d a).elts) input (encList (encList encNat)) :=
  (snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp'
    ((snd _ _).comp' ((snd _ _).comp' ((snd _ _).comp' (tup_polytime hd))))))))

end Fields

/-! ### Reading the table -/

theorem dig_polytime {n idx j : α → ℕ} (hn : ComputableInPolyTime n input encNat)
    (hidx : ComputableInPolyTime idx input encNat) (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun a ↦ dig (n a) (idx a) (j a)) input encNat :=
  binary_mod.comp' ((binary_div.comp' (hidx.prod (binary_pow' hn hj))).prod hn)

theorem pos_polytime (k : ℕ) {l s b t : α → ℕ} (hl : ComputableInPolyTime l input encUnary)
    (hs : ComputableInPolyTime s input encUnary) (hb : ComputableInPolyTime b input encUnary)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a ↦ pos k (l a) (s a) (b a) (t a)) input encUnary :=
  unary_add' (unary_mul' (unary_add' (unary_mul' hs (const (k - 1))) hb) hl) ht

/-- Digit `b` of `i` in base `ℓ`, in unary: it is at most `i`. -/
theorem baseDigit_polytime {i l b : α → ℕ} (hi : ComputableInPolyTime i input encUnary)
    (hl : ComputableInPolyTime l input encUnary) (hb : ComputableInPolyTime b input encUnary) :
    ComputableInPolyTime (fun a ↦ i a / l a ^ b a % l a) input encUnary :=
  binary_to_unary_bounded
    (binary_mod.comp' ((binary_div.comp' ((toBin hi).prod (binary_pow' (toBin hl) hb))).prod
      (toBin hl))) hi
    fun _ ↦ (Nat.mod_le _ _).trans (Nat.div_le_self _ _)

theorem tabIdx_polytime (k : ℕ) {d : α → Dat} {idx s v i : α → ℕ}
    (hd : ComputableInPolyTime d input encDat) (hidx : ComputableInPolyTime idx input encNat)
    (hs : ComputableInPolyTime s input encUnary) (hv : ComputableInPolyTime v input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a ↦ tabIdx k (d a) (idx a) (s a) (v a) (i a)) input encNat := by
  have h1 := fst input encUnary
  have hb := snd input encUnary
  have hd1 := hd.comp' h1
  have hterm : ComputableInPolyTime (fun p : α × ℕ ↦ dig (d p.1).n (idx p.1)
      (pos k (d p.1).l (s p.1) p.2 (i p.1 / (d p.1).l ^ p.2 % (d p.1).l)) * (d p.1).n ^ p.2)
      (encPair input encUnary) encNat :=
    binary_mul' (dig_polytime (toBin (dat_n hd1)) (hidx.comp' h1)
      (pos_polytime k (dat_l hd1) (hs.comp' h1) hb
        (baseDigit_polytime (hi.comp' h1) (dat_l hd1) hb)))
      (binary_pow' (toBin (dat_n hd1)) hb)
  exact binary_add.comp' ((sum' (mapWithInput (range.comp' (const (k - 1))) hterm)).prod
    (binary_mul' (toBin hv) (binary_pow' (toBin (dat_n hd)) (const (k - 1)))))

theorem bitList_polytime (k : ℕ) {d : α → Dat} {idx s v : α → ℕ}
    (hd : ComputableInPolyTime d input encDat) (hidx : ComputableInPolyTime idx input encNat)
    (hs : ComputableInPolyTime s input encUnary) (hv : ComputableInPolyTime v input encUnary) :
    ComputableInPolyTime (fun a ↦ bitList k (d a) (idx a) (s a) (v a)) input (encList encNat) := by
  have h1 := fst input encUnary
  have hd1 := hd.comp' h1
  exact mapWithInput (range.comp' (dat_r hd)) ((of_finite Bool.toNat).comp'
    (listGetD_binary (encA := encBool) (encL := encBits) false (dat_w hd1)
      (tabIdx_polytime k hd1 (hidx.comp' h1) (hs.comp' h1) (hv.comp' h1) (snd _ _))))

theorem digits_polytime {d : α → Dat} {idx : α → ℕ} (hd : ComputableInPolyTime d input encDat)
    (hidx : ComputableInPolyTime idx input encNat) :
    ComputableInPolyTime (fun a ↦ digits (d a) (idx a)) input (encList encNat) := by
  have h1 := fst input encUnary
  exact mapWithInput (range.comp' (dat_L hd))
    (dig_polytime (toBin (dat_n (hd.comp' h1))) (hidx.comp' h1) (snd _ _))

theorem points_polytime (k : ℕ) {d : α → Dat} {idx : α → ℕ}
    (hd : ComputableInPolyTime d input encDat) (hidx : ComputableInPolyTime idx input encNat) :
    ComputableInPolyTime (fun a ↦ points k (d a) (idx a)) input encPts := by
  have h1 := fst input encUnary
  have hd1 := hd.comp' h1
  have hidx1 := hidx.comp' h1
  exact mapWithInput (filterWithInput (range.comp' (dat_n hd))
      (bool_not.comp' (decide_mem (digits_polytime hd1 hidx1) (toBin (snd _ _)))))
    ((bitList_polytime k hd1 hidx1 (const 0) (snd _ _)).prod
      (bitList_polytime k hd1 hidx1 (const 1) (snd _ _)))

/-! ### Deciding a guess -/

theorem nodupB_polytime {l : α → List ℕ} (hl : ComputableInPolyTime l input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ nodupB (l a)) input encBool :=
  beq ((length_list encNat).comp' (listDedup hl)) ((length_list encNat).comp' hl)

theorem constCheck_polytime {t : α → ℕ} {pts : α → List (List ℕ × List ℕ)}
    (ht : ComputableInPolyTime t input encUnary) (hpts : ComputableInPolyTime pts input encPts) :
    ComputableInPolyTime (fun a ↦ constCheck (t a) (pts a)) input encBool := by
  have hq := snd input (encPair (encList encNat) (encList encNat))
  have hf := fst input (encPair (encList encNat) (encList encNat))
  have htest : ComputableInPolyTime
      (fun p : (α × (List ℕ × List ℕ)) × (List ℕ × List ℕ) ↦ p.2.2 == p.1.2.2)
      (encPair (encPair input (encPair (encList encNat) (encList encNat)))
        (encPair (encList encNat) (encList encNat))) encBool :=
    beq ((snd _ _).comp' (snd _ _)) ((snd _ _).comp' (hq.comp' (fst _ _)))
  have hsel := mapWithInput (f := fun _ ↦ (Prod.fst : List ℕ × List ℕ → List ℕ))
    (filterWithInput (test := fun x (xy : List ℕ × List ℕ) ↦ xy.2 == x.2.2) (hpts.comp' hf) htest)
    ((fst _ _).comp' (snd _ _))
  exact anyWithInput hpts (unary_le' (ht.comp' hf)
    ((length_list (encList encNat)).comp' (listDedup hsel)))

theorem decidePts_polytime {d : α → Dat} {pts : α → List (List ℕ × List ℕ)}
    (hd : ComputableInPolyTime d input encDat) (hpts : ComputableInPolyTime pts input encPts) :
    ComputableInPolyTime (fun a ↦ decidePts (d a) (pts a)) input encBool :=
  ite_prop (unary_le' (const 2) (dat_m hd))
    (decodeL_polytime.comp' ((dat_fl hd).prod ((dat_elts hd).prod ((dat_m hd).prod
      ((dat_W hd).prod hpts)))))
    (constCheck_polytime (unary_add' (dat_W hd) (const 1)) hpts)

/-- **A guess is checked in polynomial time.** -/
theorem guessOK_polytime (k : ℕ) {d : α → Dat} {idx : α → ℕ}
    (hd : ComputableInPolyTime d input encDat) (hidx : ComputableInPolyTime idx input encNat) :
    ComputableInPolyTime (fun a ↦ guessOK k (d a) (idx a)) input encBool :=
  bool_and' (nodupB_polytime (digits_polytime hd hidx))
    (decidePts_polytime hd (points_polytime k hd hidx))

end BHJK25.RS.AlgAux
