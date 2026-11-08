module

public import BHJK25.RS.Defs

/-!
# Bits of field elements

The field `F_q = F₂[U]/(f)` (`BHJK25.RS.Fld`) has characteristic `2`, and the bits of an element
(`BHJK25.RS.bitEquiv`) are its coordinates in the basis `1, U, …, U^(r-1)`. So bits add as
exclusive or (`BHJK25.RS.ConsAux.ofBits_xor`), and adding the element `U^i`, whose only nonzero
bit is bit `i` (`BHJK25.RS.ConsAux.unitBit`), flips bit `i` and keeps the others
(`BHJK25.RS.ConsAux.bits_add_unitBit`).
-/

@[expose] public section

namespace BHJK25.RS.ConsAux

open Cslib

variable {T n : ℕ}

theorem ofBits_eq_sum (c : Fin (rbits T n) → Bool) :
    ofBits c = ∑ i, ((c i).toNat : Fld T n) * AdjoinRoot.root _ ^ (i : ℕ) :=
  FieldAux.val_ofFn (FieldAux.length_irrPoly _) c

/-- The field has characteristic `2`. -/
theorem add_self (a : Fld T n) : a + a = 0 := by
  have h2 : (2 : Fld T n) = 0 := by
    have := GaloisRingArith.natCast_two_pow (p := 1) (fl := irrPoly (rbits T n))
    simpa using this
  rw [← two_mul, h2, zero_mul]

theorem natCast_xor (a b : Bool) :
    (((xor a b).toNat : ℕ) : Fld T n) = (a.toNat : Fld T n) + (b.toNat : Fld T n) := by
  cases a <;> cases b <;> simp [add_self]

/-- Bits add as exclusive or. -/
theorem ofBits_xor (c d : Fin (rbits T n) → Bool) :
    ofBits (fun i ↦ xor (c i) (d i)) = ofBits c + ofBits d := by
  rw [ofBits_eq_sum, ofBits_eq_sum, ofBits_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [natCast_xor, add_mul]

/-- The field element `U^i`, whose only nonzero bit is bit `i`. -/
noncomputable def unitBit (i : Fin (rbits T n)) : Fld T n := ofBits fun j ↦ decide (j = i)

/-- Adding `U^i` flips bit `i` and keeps the other bits. -/
theorem bits_add_unitBit (a : Fld T n) (i j : Fin (rbits T n)) :
    (bitEquiv T n).symm (a + unitBit i) j = xor ((bitEquiv T n).symm a j) (decide (j = i)) := by
  have h : a + unitBit i =
      bitEquiv T n fun j ↦ xor ((bitEquiv T n).symm a j) (decide (j = i)) := by
    rw [show (bitEquiv T n) _ = ofBits _ from rfl, ofBits_xor]
    congr 1
    exact ((bitEquiv T n).apply_symm_apply a).symm
  rw [h, Equiv.symm_apply_apply]

theorem bits_add_unitBit_self (a : Fld T n) (i : Fin (rbits T n)) :
    (bitEquiv T n).symm (a + unitBit i) i = !(bitEquiv T n).symm a i := by
  rw [bits_add_unitBit, decide_eq_true rfl, Bool.xor_true]

theorem bits_add_unitBit_of_ne (a : Fld T n) {i j : Fin (rbits T n)} (hji : j ≠ i) :
    (bitEquiv T n).symm (a + unitBit i) j = (bitEquiv T n).symm a j := by
  rw [bits_add_unitBit, decide_eq_false hji, Bool.xor_false]

end BHJK25.RS.ConsAux
