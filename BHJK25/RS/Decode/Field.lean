module

public import BHJK25.RS.Defs
public import BHJK25.RS.Decode.Sem
public import Mathlib.Data.List.GetD

/-!
# The per-guess decoder: the field `F_q`

Coefficient lists are read in `F_q = BHJK25.RS.Fld T n` by `Cslib.GaloisRingArith.val`
(`BHJK25.RS.DecodeAux.fldSem`). A list `c` has the value of its bits `cᵢ mod 2`, `i < r`
(`BHJK25.RS.DecodeAux.val_eq_ofBits`), so the zero test of `BHJK25.RS.DecodeAux.isZ` is exact
(`BHJK25.RS.DecodeAux.isZ_iff_val_eq_zero`). The bit lists `bitsOf r a`, `a < 2^r`, list every
element of `F_q` exactly once (`BHJK25.RS.DecodeAux.nodup_map_val_elts`,
`BHJK25.RS.DecodeAux.exists_mem_elts`).
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

open Cslib

/-- The value of a list depends only on its first `r` coordinates modulo `2`. -/
theorem val_congr {fl c d : List ℕ} (h : ∀ i < fl.length, c.getD i 0 % 2 = d.getD i 0 % 2) :
    GaloisRingArith.val 1 fl c = GaloisRingArith.val 1 fl d := by
  unfold GaloisRingArith.val
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hc := GaloisRingArith.natCast_mod_two_pow (p := 1) (fl := fl) (c.getD i 0)
  have hd := GaloisRingArith.natCast_mod_two_pow (p := 1) (fl := fl) (d.getD i 0)
  have h2 : c.getD i 0 % 2 ^ 1 = d.getD i 0 % 2 ^ 1 := by
    rw [pow_one]
    exact h i (Finset.mem_range.mp hi)
  rw [← hc, ← hd, h2]

variable {T n : ℕ}

/-- The bits of a list: its coordinates modulo `2`. -/
def bitsMod (T n : ℕ) (c : List ℕ) : Fin (rbits T n) → Bool := fun i ↦ decide (c.getD i 0 % 2 = 1)

/-- A list has the value of its bits. -/
theorem val_eq_ofBits (c : List ℕ) :
    GaloisRingArith.val 1 (irrPoly (rbits T n)) c = ofBits (bitsMod T n c) := by
  refine val_congr fun i hi ↦ ?_
  rw [FieldAux.length_irrPoly] at hi
  rw [List.getD_eq_getElem (List.ofFn _) _ (by simpa using hi), List.getElem_ofFn, bitsMod]
  rcases Nat.mod_two_eq_zero_or_one (c.getD i 0) with h | h <;> rw [h] <;> rfl

theorem val_nil (fl : List ℕ) : GaloisRingArith.val 1 fl [] = 0 :=
  FieldAux.val_eq_zero_of_forall (by simp)

/-- **The zero test is exact.** -/
theorem isZ_iff_val_eq_zero (c : List ℕ) :
    isZ (irrPoly (rbits T n)) c = true ↔ GaloisRingArith.val 1 (irrPoly (rbits T n)) c = 0 := by
  rw [isZ, List.all_eq_true, FieldAux.length_irrPoly]
  simp only [List.mem_range, beq_iff_eq]
  constructor
  · intro h
    rw [val_congr (d := []) fun i hi ↦ ?_, val_nil]
    rw [FieldAux.length_irrPoly] at hi
    rw [h i hi]
    rfl
  · intro h i hi
    have h0 : ofBits (T := T) (n := n) (fun _ ↦ false) = 0 := by
      rw [ofBits, val_congr (d := []) fun j _ ↦ ?_, val_nil]
      rcases lt_or_ge j (rbits T n) with hj | hj
      · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
        rfl
      · rw [List.getD_eq_default _ _ (by simpa using hj)]
        rfl
    rw [val_eq_ofBits, ← h0] at h
    have := congrFun ((ofBits_bijective T n).1 h) ⟨i, hi⟩
    simp only [bitsMod, decide_eq_false_iff_not] at this
    exact (Nat.mod_two_eq_zero_or_one _).resolve_right this

/-- The reading of coefficient lists in `F_q`. -/
noncomputable def fldSem (T n : ℕ) : Sem (irrPoly (rbits T n)) (Fld T n) where
  ev := GaloisRingArith.val 1 (irrPoly (rbits T n))
  ev_add := GaloisRingArith.val_add
  ev_sub := GaloisRingArith.val_sub
  ev_mul := GaloisRingArith.val_mul
  ev_pow := GaloisRingArith.val_pow
  ev_zero := GaloisRingArith.val_zero
  ev_one := GaloisRingArith.val_one
  ev_nil := val_nil _
  isZ_iff := isZ_iff_val_eq_zero

theorem fldSem_ev (c : List ℕ) :
    (fldSem T n).ev c = GaloisRingArith.val 1 (irrPoly (rbits T n)) c := rfl

/-! ### The list of all elements -/

/-- The value of `bitsOf r a`. -/
theorem val_bitsOf (a : ℕ) :
    GaloisRingArith.val 1 (irrPoly (rbits T n)) (bitsOf (rbits T n) a) =
      ofBits fun i ↦ a.testBit i := by
  rw [FieldAux.bitsOf_eq_ofFn]
  rfl

private theorem val_bitsOf_injOn {a b : ℕ} (ha : a < 2 ^ rbits T n) (hb : b < 2 ^ rbits T n)
    (h : GaloisRingArith.val 1 (irrPoly (rbits T n)) (bitsOf (rbits T n) a) =
      GaloisRingArith.val 1 (irrPoly (rbits T n)) (bitsOf (rbits T n) b)) : a = b := by
  rw [val_bitsOf, val_bitsOf] at h
  exact congrArg Fin.val ((FieldAux.bijective_testBit _).1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
    ((ofBits_bijective T n).1 h))

/-- The elements `bitsOf r a`, `a < 2^r`, are distinct. -/
theorem nodup_map_val_elts (T n : ℕ) :
    (((List.range (2 ^ rbits T n)).map (bitsOf (rbits T n))).map
      (GaloisRingArith.val 1 (irrPoly (rbits T n)))).Nodup := by
  rw [List.map_map]
  refine List.Nodup.map_on (fun a ha b hb h ↦ ?_) List.nodup_range
  exact val_bitsOf_injOn (List.mem_range.mp ha) (List.mem_range.mp hb) h

/-- Every element of `F_q` is the value of some `bitsOf r a`, `a < 2^r`. -/
theorem exists_mem_elts (x : Fld T n) :
    ∃ c ∈ (List.range (2 ^ rbits T n)).map (bitsOf (rbits T n)),
      GaloisRingArith.val 1 (irrPoly (rbits T n)) c = x := by
  obtain ⟨a, ha, hx⟩ := FieldAux.exists_val_bitsOf (FieldAux.length_irrPoly _) x
  exact ⟨_, List.mem_map_of_mem (List.mem_range.2 ha), hx⟩

end BHJK25.RS.DecodeAux
