module

public import BHJK25.RS.Decode.Algo
public import Complexity.Tactic.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# The per-guess decoder in polynomial time: field elements

Certificates (`Turing.MultiTapeTM.ComputableInPolyTime`) for the field operations of
`BHJK25.RS.DecodeAux`, with field elements, vectors and matrices encoded as lists of binary
numbers (`BHJK25.RS.DecodeAux.PT.encE`, `encV`, `encM`), and the size of their outputs: every
arithmetic output is reduced, with `r = fl.length` coordinates in `{0, 1}`, so it has an encoding
of length at most `3 r` (`BHJK25.RS.DecodeAux.PT.length_encE_fadd` and its siblings).
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux.PT

open Turing.MultiTapeTM Cslib

/-- The encoding of field elements. -/
abbrev encE : List ℕ ↪ List Bool := encList encNat

/-- The encoding of vectors of field elements. -/
abbrev encV : List (List ℕ) ↪ List Bool := encList encE

/-- The encoding of matrices (and bivariate polynomials) of field elements. -/
abbrev encM : List (List (List ℕ)) ↪ List Bool := encList encV

/-! ### Sizes -/

theorem length_encE_fadd (fl a b : List ℕ) : (encE (fadd fl a b)).length ≤ fl.length * 3 :=
  GaloisRingArith.length_encList_le (p := 1) (GaloisRingArith.length_add 1 fl a b)
    fun _ h ↦ GaloisRingArith.lt_of_mem_add h

theorem length_encE_fsub (fl a b : List ℕ) : (encE (fsub fl a b)).length ≤ fl.length * 3 :=
  length_encE_fadd fl a _

theorem length_encE_fmul (fl a b : List ℕ) : (encE (fmul fl a b)).length ≤ fl.length * 3 :=
  GaloisRingArith.length_encList_le (p := 1) (GaloisRingArith.length_mul 1 fl a b)
    fun _ h ↦ GaloisRingArith.lt_of_mem_mul h

theorem length_encE_fzero (fl : List ℕ) : (encE (fzero fl)).length ≤ fl.length * 3 :=
  GaloisRingArith.length_encList_le (p := 1) (GaloisRingArith.length_zero fl) fun x h ↦ by
    simp only [fzero, GaloisRingArith.zero, List.mem_map] at h
    obtain ⟨_, _, rfl⟩ := h
    norm_num

theorem length_encE_fsum (fl : List ℕ) (l : List (List ℕ)) :
    (encE (fsum fl l)).length ≤ fl.length * 3 := by
  rw [fsum]
  induction l using List.reverseRecOn with
  | nil => exact length_encE_fzero fl
  | append_singleton l a _ =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact length_encE_fadd _ _ _

variable {α : Type} {input : α ↪ List Bool}

/-- The size `3 r` of a reduced field element is polynomial in the input. -/
theorem polyBounded_three_mul_length {fl : α → List ℕ}
    (hfl : ComputableInPolyTime fl input encE) :
    PolyBounded (fun x ↦ (input x).length) (fun x ↦ (fl x).length * 3) := by
  refine (hfl.polyBounded_length.mul (PolyBounded.const 3)).mono fun x ↦ ?_
  have : (fl x).length ≤ (encE (fl x)).length := by
    rw [length_encList]
    calc (fl x).length = ((fl x).map fun _ ↦ 1).sum := by simp
      _ ≤ ((fl x).map fun a ↦ 2 * (encNat a).length + 1).sum :=
        List.sum_le_sum fun a _ ↦ by omega
  exact Nat.mul_le_mul_right 3 this

/-! ### Certificates -/

/-- The sum of field elements is polynomial-time. -/
@[fun_prop]
theorem fadd' {fl a b : α → List ℕ} (hfl : ComputableInPolyTime fl input encE)
    (ha : ComputableInPolyTime a input encE) (hb : ComputableInPolyTime b input encE) :
    ComputableInPolyTime (fun x ↦ fadd (fl x) (a x) (b x)) input encE :=
  GaloisRingArith.computableInPolyTime_add (ComputableInPolyTime.const 1) hfl ha hb

/-- The difference of field elements is polynomial-time. -/
@[fun_prop]
theorem fsub' {fl a b : α → List ℕ} (hfl : ComputableInPolyTime fl input encE)
    (ha : ComputableInPolyTime a input encE) (hb : ComputableInPolyTime b input encE) :
    ComputableInPolyTime (fun x ↦ fsub (fl x) (a x) (b x)) input encE :=
  GaloisRingArith.computableInPolyTime_sub (ComputableInPolyTime.const 1) hfl ha hb

/-- The product of field elements is polynomial-time. -/
@[fun_prop]
theorem fmul' {fl a b : α → List ℕ} (hfl : ComputableInPolyTime fl input encE)
    (ha : ComputableInPolyTime a input encE) (hb : ComputableInPolyTime b input encE) :
    ComputableInPolyTime (fun x ↦ fmul (fl x) (a x) (b x)) input encE :=
  GaloisRingArith.computableInPolyTime_mul (ComputableInPolyTime.const 1) hfl ha hb

/-- Powers of field elements, with a unary exponent, are polynomial-time. -/
@[fun_prop]
theorem fpow' {fl a : α → List ℕ} {k : α → ℕ} (hfl : ComputableInPolyTime fl input encE)
    (ha : ComputableInPolyTime a input encE) (hk : ComputableInPolyTime k input encUnary) :
    ComputableInPolyTime (fun x ↦ fpow (fl x) (a x) (k x)) input encE :=
  GaloisRingArith.computableInPolyTime_pow (ComputableInPolyTime.const 1) hfl ha hk

/-- Zero is polynomial-time. -/
@[fun_prop]
theorem fzero' {fl : α → List ℕ} (hfl : ComputableInPolyTime fl input encE) :
    ComputableInPolyTime (fun x ↦ fzero (fl x)) input encE :=
  GaloisRingArith.computableInPolyTime_tabulate (g := fun _ _ ↦ 0)
    ((ComputableInPolyTime.length_list encNat).comp hfl) (ComputableInPolyTime.const 0)

/-- One is polynomial-time. -/
@[fun_prop]
theorem fone' {fl : α → List ℕ} (hfl : ComputableInPolyTime fl input encE) :
    ComputableInPolyTime (fun x ↦ fone (fl x)) input encE :=
  GaloisRingArith.computableInPolyTime_one hfl

/-- The zero test is polynomial-time. -/
@[fun_prop]
theorem isZ' {fl c : α → List ℕ} (hfl : ComputableInPolyTime fl input encE)
    (hc : ComputableInPolyTime c input encE) :
    ComputableInPolyTime (fun x ↦ isZ (fl x) (c x)) input encBool := by
  unfold isZ
  refine ComputableInPolyTime.allWithInput
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list encNat).comp hfl)) ?_
  have hmod := GaloisRingArith.computableInPolyTime_mod_two_pow
    (GaloisRingArith.computableInPolyTime_getD (hc.comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd input encUnary)) (ComputableInPolyTime.const 1)
  simp only [pow_one] at hmod
  exact ComputableInPolyTime.beq hmod (ComputableInPolyTime.const 0)

/-- The sum of a list of field elements is polynomial-time. -/
@[fun_prop]
theorem fsum' {fl : α → List ℕ} {l : α → List (List ℕ)}
    (hfl : ComputableInPolyTime fl input encE) (hl : ComputableInPolyTime l input encV) :
    ComputableInPolyTime (fun x ↦ fsum (fl x) (l x)) input encE := by
  unfold fsum
  have hstep : ComputableInPolyTime
      (fun q : (α × List ℕ) × List ℕ ↦ fadd (fl q.1.1) q.1.2 q.2)
      (encPair (encPair input encE) encE) encE :=
    fadd' (hfl.comp ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)))
      ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
      (ComputableInPolyTime.snd _ _)
  exact ComputableInPolyTime.foldlWithInput_of_bounded_growth (encA := encE) (encL := encV)
    (step := fun x acc e ↦ fadd (fl x) acc e) (fzero' hfl)
    ⟨hl, hstep, inferInstance, inferInstance⟩
    ⟨polyBounded_three_mul_length hfl, fun x s e _ ↦ by
      have := length_encE_fadd (fl x) s e
      omega⟩

end BHJK25.RS.DecodeAux.PT
