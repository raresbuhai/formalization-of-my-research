module

public import BHJK25.Model
public import Complexity.Computability.PolyTime.GaloisRingArithmetic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement

/-!
# The Reed–Solomon construction of Theorem 2.1: definitions

The construction behind [BHJK25, Theorem 2.1], with the parameters used here, and the property
that the algorithm decides.

* **Parameters** (for a natural number `T ≥ 1`, used with `T = ⌈1/(6ε)⌉`, so `1/T ≤ 6ε`), with
  `c = ⌈log₂ n⌉`: field elements have `r = c + ⌈c/(2T)⌉ + 4` bits (`BHJK25.RS.rbits`), so the
  field has `q = 2^r ≥ 16 n^{1 + 1/(2T)}` elements; polynomials have `m = 2^⌈(1 - 1/T) c⌉ ≥
  n^{1 - 1/T}` coefficients (`BHJK25.RS.mdeg`); Sudan's weighted degree is `W = ⌊√(2nm)⌋ + 1`
  (`BHJK25.RS.wdeg`) and the agreement threshold is `W + 1` (`BHJK25.RS.thr`). A field element
  is written on a grid of `ℓ^(k-1) ≥ r` cells (`BHJK25.RS.ell`).
* **The field** `F_q = F₂[U]/(f)` (`BHJK25.RS.Fld`) for the first monic `f` of degree `r` (in
  the order of the binary numbers of its lower coefficients) such that `F₂[U]/(f)` has no zero
  divisors (`BHJK25.RS.irrPoly`), with complexitylib's arithmetic on coefficient lists
  (`Cslib.GaloisRingArith`); an element is read from its `r` bits (`BHJK25.RS.ofBits`).
* **Guesses** (`BHJK25.RS.Guess`): `2 (k - 1) ℓ` vertices, in two sides (`α` and `β`) of `k - 1`
  blocks of `ℓ`. For a column vertex `v` outside the guess, bit `i` of side `s` is the entry at the
  cell formed by `v` and, in each block `b` of side `s`, the vertex at position `digit_b(i)`, the
  `b`-th digit of `i` in base `ℓ` (`BHJK25.RS.cell`).
* **Acceptance** (`BHJK25.RS.Accept`): for some valid guess, some polynomial of degree `< m`
  agrees with the read pairs `(α_v, β_v)` at `W + 1` distinct values `α_v`.
* **The planted distribution** (`BHJK25.RS.planted`): coefficients `x ∈ F^m`, values `α ∈ F^n`
  and `β' ∈ F^n`, and padding bits, all uniform; `β_v = Σ xᵢ α_vⁱ` when `α_v` is unique among the
  columns and `β'_v` otherwise; the bits of `α_v` and `β_v` are written on the cells of column
  `v` of a fixed layout, every other entry is a padding bit; then the vertices are relabelled by
  a uniformly random permutation.
-/

@[expose] public section

namespace BHJK25.RS

open Cslib MeasureTheory

/-! ### Parameters -/

/-- The number `r = c + ⌈c/(2T)⌉ + 4` of bits of a field element, with `c = ⌈log₂ n⌉`. -/
def rbits (T n : ℕ) : ℕ := Nat.clog 2 n + (Nat.clog 2 n + 2 * T - 1) / (2 * T) + 4

/-- The side `ℓ` of the grid that carries a field element: the least `ℓ ≤ r` with
`ℓ^(k-1) ≥ r` (and `r` if there is none, which happens only for `k ≤ 1`). -/
def ell (k T n : ℕ) : ℕ :=
  ((List.range (rbits T n + 1)).find? fun l ↦ decide (rbits T n ≤ l ^ (k - 1))).getD (rbits T n)

/-- The number `m = 2^⌈(1 - 1/T) ⌈log₂ n⌉⌉ ≥ n^(1 - 1/T)` of coefficients of the polynomials. -/
def mdeg (T n : ℕ) : ℕ := 2 ^ (((T - 1) * Nat.clog 2 n + T - 1) / T)

/-- Sudan's weighted degree `W = ⌊√(2 n m)⌋ + 1`. -/
def wdeg (T n : ℕ) : ℕ := Nat.sqrt (2 * n * mdeg T n) + 1

/-- The agreement threshold `W + 1`. -/
def thr (T n : ℕ) : ℕ := wdeg T n + 1

/-! ### The field -/

/-- The binary digits of `a`, least significant first, as a coefficient list of length `r`. -/
def bitsOf (r a : ℕ) : List ℕ := (List.range r).map fun i ↦ if a.testBit i then 1 else 0

/-- `F₂[U]/(f)`, for the monic `f` with lower coefficients `fl`, has no zero divisors among the
elements with reduced coordinates (`a, b < 2^r`). -/
def noZeroDiv (fl : List ℕ) : Bool :=
  (List.range (2 ^ fl.length)).all fun a ↦ (List.range (2 ^ fl.length)).all fun b ↦
    a == 0 || b == 0 ||
      (GaloisRingArith.mul 1 fl (bitsOf fl.length a) (bitsOf fl.length b)).any (· != 0)

/-- The lower coefficients of the first monic `f` of degree `r` over `F₂` (in the order of the
binary numbers of its lower coefficients) for which `F₂[U]/(f)` has no zero divisors. -/
def irrPoly (r : ℕ) : List ℕ :=
  (((List.range (2 ^ r)).map (bitsOf r)).find? noZeroDiv).getD (List.replicate r 0)

/-- The field `F_q = F₂[U]/(f)` with `q = 2^r` elements. -/
abbrev Fld (T n : ℕ) : Type := GaloisRingArith.Ring 1 (irrPoly (rbits T n))

instance : Fact (Nat.Prime (2 ^ 1)) := ⟨Nat.prime_two⟩

/-! The field facts behind `irreducible_irrPoly` and `ofBits_bijective`. Over `F₂`, the
coordinate lists with entries in `{0, 1}` are the coordinates in the power basis
`1, U, …, U^(r-1)` of `F₂[U]/(f)` (`FieldAux.bijective_val_ofFn`). So the test `noZeroDiv` says
exactly that `F₂[U]/(f)` has no zero divisors, which holds if and only if `f` is irreducible; and
some monic irreducible `f` of degree `r` exists (the minimal polynomial of a primitive element of
`GF(2^r)`), so the search in `irrPoly` succeeds. -/

namespace FieldAux

open Polynomial

theorem natDegree_monicOf (fl : List ℕ) :
    (GaloisRingArith.monicOf fl).natDegree = fl.length := by
  unfold GaloisRingArith.monicOf
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  refine (degree_sum_le _ _).trans_lt ?_
  rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
  intro i hi
  exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hi))

theorem natDegree_poly (fl : List ℕ) :
    ((GaloisRingArith.monicOf fl).map (Int.castRingHom (ZMod (2 ^ 1)))).natDegree =
      fl.length := by
  rw [(GaloisRingArith.monic_monicOf fl).natDegree_map, natDegree_monicOf]

theorem bijective_toNat_cast :
    Function.Bijective fun b : Bool ↦ ((b.toNat : ℕ) : ZMod (2 ^ 1)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro a b h
  cases a <;> cases b <;> simp_all

theorem zmod_cases (z : ZMod (2 ^ 1)) : z = 0 ∨ z = 1 := by
  obtain ⟨b, rfl⟩ := bijective_toNat_cast.2 z
  cases b <;> simp

theorem bijective_sum_pow {R : Type*} [CommRing R] [Algebra (ZMod (2 ^ 1)) R]
    (pb : PowerBasis (ZMod (2 ^ 1)) R) :
    Function.Bijective fun c : Fin pb.dim → Bool ↦
      ∑ i, ((c i).toNat : R) * pb.gen ^ (i : ℕ) := by
  have : (fun c : Fin pb.dim → Bool ↦ ∑ i, ((c i).toNat : R) * pb.gen ^ (i : ℕ)) =
      pb.basis.equivFun.symm ∘ fun c i ↦ (((c i).toNat : ℕ) : ZMod (2 ^ 1)) := by
    funext c
    simp only [Function.comp_apply, Module.Basis.equivFun_symm_apply, PowerBasis.coe_basis]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [this]
  refine pb.basis.equivFun.symm.bijective.comp ⟨fun c d h ↦ funext fun i ↦
    bijective_toNat_cast.1 (congrFun h i), fun z ↦ ⟨fun i ↦ (bijective_toNat_cast.2 (z i)).choose,
      funext fun i ↦ (bijective_toNat_cast.2 (z i)).choose_spec⟩⟩

theorem val_ofFn {fl : List ℕ} {r : ℕ} (hlen : fl.length = r) (c : Fin r → Bool) :
    GaloisRingArith.val 1 fl (List.ofFn fun i ↦ (c i).toNat) =
      ∑ i : Fin r, ((c i).toNat : GaloisRingArith.Ring 1 fl) * AdjoinRoot.root _ ^ (i : ℕ) := by
  unfold GaloisRingArith.val
  rw [hlen, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem bijective_val_ofFn {fl : List ℕ} {r : ℕ} (hlen : fl.length = r) :
    Function.Bijective fun c : Fin r → Bool ↦
      GaloisRingArith.val 1 fl (List.ofFn fun i ↦ (c i).toNat) := by
  have hm := (GaloisRingArith.monic_monicOf fl).map (Int.castRingHom (ZMod (2 ^ 1)))
  have hdim : (AdjoinRoot.powerBasis' hm).dim = r := by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_poly, hlen]
  subst hdim
  simp_rw [val_ofFn hlen]
  exact bijective_sum_pow (AdjoinRoot.powerBasis' hm)

theorem length_bitsOf (r a : ℕ) : (bitsOf r a).length = r := by simp [bitsOf]

theorem bitsOf_eq_ofFn (r a : ℕ) :
    bitsOf r a = List.ofFn fun i : Fin r ↦ (a.testBit i).toNat := by
  apply List.ext_getElem (by simp [bitsOf])
  intro i h1 h2
  simp only [bitsOf, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  cases a.testBit i <;> rfl

theorem bijective_testBit (r : ℕ) :
    Function.Bijective fun a : Fin (2 ^ r) ↦ fun i : Fin r ↦ (a : ℕ).testBit i := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h ↦ Fin.ext (Nat.eq_of_testBit_eq fun i ↦ ?_), by simp⟩
  by_cases hi : i < r
  · exact congrFun h ⟨i, hi⟩
  · have hle : 2 ^ r ≤ 2 ^ i := Nat.pow_le_pow_right two_pos (not_lt.1 hi)
    rw [Nat.testBit_lt_two_pow (a.2.trans_le hle), Nat.testBit_lt_two_pow (b.2.trans_le hle)]

theorem val_bitsOf_eq_zero {fl : List ℕ} {r a : ℕ} (hlen : fl.length = r) (ha : a < 2 ^ r) :
    GaloisRingArith.val 1 fl (bitsOf r a) = 0 ↔ a = 0 := by
  have h0 : GaloisRingArith.val 1 fl (bitsOf r 0) = 0 := by
    rw [bitsOf_eq_ofFn, val_ofFn hlen]
    simp
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ h0⟩
  rw [← h0, bitsOf_eq_ofFn, bitsOf_eq_ofFn] at h
  have h1 := (bijective_val_ofFn hlen).1 h
  have h2 := (bijective_testBit r).1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨0, Nat.two_pow_pos r⟩) h1
  exact congrArg Fin.val h2

theorem exists_val_bitsOf {fl : List ℕ} {r : ℕ} (hlen : fl.length = r)
    (x : GaloisRingArith.Ring 1 fl) : ∃ a < 2 ^ r, GaloisRingArith.val 1 fl (bitsOf r a) = x := by
  obtain ⟨c, rfl⟩ := (bijective_val_ofFn hlen).2 x
  obtain ⟨a, ha⟩ := (bijective_testBit r).2 c
  refine ⟨a, a.2, ?_⟩
  rw [bitsOf_eq_ofFn, ← ha]

theorem val_eq_zero_of_forall {fl L : List ℕ} (h : ∀ y ∈ L, y = 0) :
    GaloisRingArith.val 1 fl L = 0 := by
  unfold GaloisRingArith.val
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [List.getD_eq_getElem?_getD]
  cases hi : L[i]? with
  | none => simp
  | some y => simp [h y (List.mem_of_getElem? hi)]

theorem forall_eq_zero_of_val {fl L : List ℕ} {r : ℕ} (hlen : fl.length = r)
    (hL : L.length = r) (hlt : ∀ y ∈ L, y < 2) (h : GaloisRingArith.val 1 fl L = 0) :
    ∀ y ∈ L, y = 0 := by
  have hL' : L = List.ofFn fun i : Fin r ↦ (decide (L.getD i 0 = 1)).toNat := by
    apply List.ext_getElem (by simp [hL])
    intro i h1 h2
    have := hlt _ (List.getElem_mem h1)
    rw [List.getElem_ofFn, List.getD_eq_getElem _ _ h1]
    by_cases h3 : L[i] = 1
    · rw [h3]
      rfl
    · rw [decide_eq_false h3, Bool.toNat_false]
      omega
  have h0 : GaloisRingArith.val 1 fl (List.ofFn fun _ : Fin r ↦ false.toNat) = 0 :=
    val_eq_zero_of_forall (by simp)
  rw [hL'] at h
  have h1 := (bijective_val_ofFn hlen).1 (h.trans h0.symm)
  intro y hy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have h2 := congrFun h1 ⟨i, hL ▸ hi⟩
  have h3 := hlt _ (List.getElem_mem hi)
  simp only [decide_eq_false_iff_not, List.getD_eq_getElem _ _ hi] at h2
  omega

theorem noZeroDiv_of_irreducible {fl : List ℕ}
    (hirr : Irreducible ((GaloisRingArith.monicOf fl).map (Int.castRingHom (ZMod (2 ^ 1))))) :
    noZeroDiv fl = true := by
  have := Fact.mk hirr
  unfold noZeroDiv
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    bne_iff_ne, ne_eq]
  intro a ha b hb
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨ha0, hb0⟩, hall⟩ := hcon
  have h1 := (val_bitsOf_eq_zero rfl ha).not.2 ha0
  have h2 := (val_bitsOf_eq_zero rfl hb).not.2 hb0
  have h3 := val_eq_zero_of_forall (fl := fl) hall
  rw [GaloisRingArith.val_mul] at h3
  exact mul_ne_zero h1 h2 h3

theorem irreducible_of_noZeroDiv {fl : List ℕ} (hpos : 0 < fl.length) (h : noZeroDiv fl = true) :
    Irreducible ((GaloisRingArith.monicOf fl).map (Int.castRingHom (ZMod (2 ^ 1)))) := by
  set f := (GaloisRingArith.monicOf fl).map (Int.castRingHom (ZMod (2 ^ 1))) with hf
  have hm : f.Monic := (GaloisRingArith.monic_monicOf fl).map _
  have hdeg : f.natDegree = fl.length := natDegree_poly fl
  refine Prime.irreducible ⟨hm.ne_zero, not_isUnit_of_natDegree_pos _ (hdeg ▸ hpos),
    fun a b hab ↦ ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.mk_eq_zero]
  have hab' : AdjoinRoot.mk f a * AdjoinRoot.mk f b = 0 := by
    rw [← map_mul, AdjoinRoot.mk_eq_zero]
    exact hab
  obtain ⟨x, hx, hxa⟩ := exists_val_bitsOf rfl (AdjoinRoot.mk f a)
  obtain ⟨y, hy, hyb⟩ := exists_val_bitsOf rfl (AdjoinRoot.mk f b)
  unfold noZeroDiv at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    bne_iff_ne, ne_eq] at h
  rcases h x hx y hy with (hx0 | hy0) | ⟨z, hz, hz0⟩
  · left
    rw [← hxa]
    exact (val_bitsOf_eq_zero rfl hx).2 hx0
  · right
    rw [← hyb]
    exact (val_bitsOf_eq_zero rfl hy).2 hy0
  · exfalso
    have hval : GaloisRingArith.val 1 fl
        (GaloisRingArith.mul 1 fl (bitsOf fl.length x) (bitsOf fl.length y)) = 0 := by
      rw [GaloisRingArith.val_mul, hxa, hyb, hab']
    exact hz0 (forall_eq_zero_of_val rfl (GaloisRingArith.length_mul _ _ _ _)
      (fun w hw ↦ (GaloisRingArith.lt_of_mem_mul hw).trans_eq (pow_one 2)) hval z hz)

theorem exists_monic_irreducible (r : ℕ) (hr : 0 < r) :
    ∃ g : (ZMod (2 ^ 1))[X], g.Monic ∧ Irreducible g ∧ g.natDegree = r := by
  obtain ⟨α, hα⟩ :=
    Field.exists_primitive_element_of_finite_bot (ZMod (2 ^ 1)) (GaloisField (2 ^ 1) r)
  have hint : IsIntegral (ZMod (2 ^ 1)) α := .of_finite _ _
  refine ⟨minpoly _ α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  exact GaloisField.finrank (2 ^ 1) hr.ne'

theorem exists_bitsOf_irreducible (r : ℕ) (hr : 0 < r) : ∃ a < 2 ^ r,
    Irreducible ((GaloisRingArith.monicOf (bitsOf r a)).map (Int.castRingHom (ZMod (2 ^ 1)))) := by
  obtain ⟨g, hm, hirr, hdeg⟩ := exists_monic_irreducible r hr
  obtain ⟨a, ha⟩ := (bijective_testBit r).2 fun i ↦ decide (g.coeff i = 1)
  refine ⟨a, a.2, ?_⟩
  convert hirr using 1
  rw [hm.as_sum, hdeg]
  simp only [GaloisRingArith.monicOf, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, length_bitsOf]
  congr 1
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.mem_range.1 hi
  have h1 := congrFun ha ⟨i, hi'⟩
  simp only at h1
  rw [List.getD_eq_getElem _ _ (by simp [length_bitsOf, hi'])]
  simp only [bitsOf, List.getElem_map, List.getElem_range, h1]
  rcases zmod_cases (g.coeff i) with h | h <;> simp [h]

theorem length_irrPoly (r : ℕ) : (irrPoly r).length = r := by
  unfold irrPoly
  cases h : ((List.range (2 ^ r)).map (bitsOf r)).find? noZeroDiv with
  | none => simp
  | some fl =>
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some h)
    exact length_bitsOf r a

end FieldAux

theorem irreducible_irrPoly (T n : ℕ) :
    Irreducible ((GaloisRingArith.monicOf (irrPoly (rbits T n))).map
      (Int.castRingHom (ZMod (2 ^ 1)))) := by
  have hr : 0 < rbits T n := Nat.lt_of_lt_of_le (by norm_num) (Nat.le_add_left 4 _)
  unfold irrPoly
  cases h : ((List.range (2 ^ rbits T n)).map (bitsOf (rbits T n))).find? noZeroDiv with
  | none =>
    exfalso
    obtain ⟨a, ha, hirr⟩ := FieldAux.exists_bitsOf_irreducible _ hr
    exact List.find?_eq_none.1 h (bitsOf _ a) (List.mem_map.2 ⟨a, List.mem_range.2 ha, rfl⟩)
      (by simp [FieldAux.noZeroDiv_of_irreducible hirr])
  | some fl =>
    simp only [Option.getD_some]
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_of_find?_eq_some h)
    exact FieldAux.irreducible_of_noZeroDiv (by rw [FieldAux.length_bitsOf]; exact hr)
      (List.find?_some h)

instance (T n : ℕ) : Fact (Irreducible ((GaloisRingArith.monicOf (irrPoly (rbits T n))).map
    (Int.castRingHom (ZMod (2 ^ 1))))) := ⟨irreducible_irrPoly T n⟩

noncomputable instance (T n : ℕ) : Field (Fld T n) := inferInstance

/-- The field element with bits `c`: `Σ cᵢ Uⁱ`. -/
noncomputable def ofBits {T n : ℕ} (c : Fin (rbits T n) → Bool) : Fld T n :=
  GaloisRingArith.val 1 (irrPoly (rbits T n)) (List.ofFn fun i ↦ (c i).toNat)

theorem ofBits_bijective (T n : ℕ) : Function.Bijective (ofBits (T := T) (n := n)) :=
  FieldAux.bijective_val_ofFn (FieldAux.length_irrPoly _)

/-- Field elements and their bits. -/
noncomputable def bitEquiv (T n : ℕ) : (Fin (rbits T n) → Bool) ≃ Fld T n :=
  Equiv.ofBijective _ (ofBits_bijective T n)

noncomputable instance (T n : ℕ) : Fintype (Fld T n) := Fintype.ofEquiv _ (bitEquiv T n)

noncomputable instance (T n : ℕ) : DecidableEq (Fld T n) := Classical.decEq _

/-! ### Guesses, cells, and acceptance -/

/-- The entry of `M` at the set `S` of vertices; `false` unless `S` has `k` elements. -/
def readAt {k n : ℕ} (M : Tensor k n) (S : Finset (Fin n)) : Bool :=
  if h : S.card = k then M ⟨S, h⟩ else false

theorem ell_pos (k T n : ℕ) : 0 < ell k T n := by
  have hr : 4 ≤ rbits T n := Nat.le_add_left _ _
  unfold ell
  cases h : (List.range (rbits T n + 1)).find? (fun l ↦ decide (rbits T n ≤ l ^ (k - 1))) with
  | none =>
    simp only [Option.getD_none]
    omega
  | some l =>
    simp only [Option.getD_some]
    have hl := List.find?_some h
    simp only [decide_eq_true_eq] at hl
    rcases Nat.eq_zero_or_pos l with rfl | hpos
    · have : (0 : ℕ) ^ (k - 1) ≤ 1 := by
        rcases Nat.eq_zero_or_pos (k - 1) with h0 | h0
        · rw [h0, pow_zero]
        · rw [zero_pow h0.ne']
          exact Nat.zero_le 1
      omega
    · exact hpos

/-- A **guess**: a vertex for each side `s` (`0` for `α`, `1` for `β`), block `b < k - 1` and
position `t < ℓ`. -/
abbrev Guess (k T n : ℕ) : Type := Fin 2 → Fin (k - 1) → Fin (ell k T n) → Fin n

/-- A guess is valid when its `2 (k - 1) ℓ` vertices are distinct. -/
def Guess.Valid {k T n : ℕ} (g : Guess k T n) : Prop :=
  Function.Injective fun x : Fin 2 × Fin (k - 1) × Fin (ell k T n) ↦ g x.1 x.2.1 x.2.2

/-- `v` is a column of the guess: none of its vertices. -/
def IsCol {k T n : ℕ} (g : Guess k T n) (v : Fin n) : Prop := ∀ s b t, g s b t ≠ v

/-- Digit `b` of `i` in base `ℓ`. -/
def digit (k T n i : ℕ) (b : Fin (k - 1)) : Fin (ell k T n) :=
  ⟨i / ell k T n ^ (b : ℕ) % ell k T n, Nat.mod_lt _ (ell_pos k T n)⟩

/-- The cell carrying bit `i` of side `s` of the column `v`: `v` and, in each block `b` of side
`s`, the vertex at position `digit_b(i)`. -/
def cell {k T n : ℕ} (g : Guess k T n) (s : Fin 2) (v : Fin n) (i : ℕ) : Finset (Fin n) :=
  insert v (Finset.univ.image fun b : Fin (k - 1) ↦ g s b (digit k T n i b))

/-- The field element of side `s` read at the column `v`, from the bits on its cells. -/
noncomputable def readElt {k T n : ℕ} (g : Guess k T n) (s : Fin 2) (M : Tensor k n)
    (v : Fin n) : Fld T n :=
  ofBits fun i ↦ readAt M (cell g s v i)

/-- The values `x = α_v` at which the polynomial `p` agrees with a column, `β_v = p(α_v)`. -/
noncomputable def agreeSet {k T n : ℕ} (g : Guess k T n) (M : Tensor k n)
    (p : Polynomial (Fld T n)) : Finset (Fld T n) :=
  open Classical in
  Finset.univ.filter fun x ↦ ∃ v, IsCol g v ∧ readElt g 0 M v = x ∧ readElt g 1 M v = p.eval x

/-- The guess `g` is valid and some polynomial of degree `< m` agrees with its columns at
`W + 1` distinct values. -/
def AcceptGuess {k T n : ℕ} (g : Guess k T n) (M : Tensor k n) : Prop :=
  g.Valid ∧ ∃ p : Polynomial (Fld T n), p.natDegree < mdeg T n ∧ thr T n ≤ (agreeSet g M p).card

/-- **Acceptance**: some guess is accepted. -/
def Accept (k T n : ℕ) (M : Tensor k n) : Prop := ∃ g : Guess k T n, AcceptGuess g M

/-! ### The planted distribution -/

theorem layout_lt {k T n : ℕ} (h : 2 * (k - 1) * ell k T n < n) (s : Fin 2) (b : Fin (k - 1))
    (t : Fin (ell k T n)) : ((s : ℕ) * (k - 1) + b) * ell k T n + t < n := by
  have hs : (s : ℕ) ≤ 1 := Nat.lt_succ_iff.1 s.2
  have hb := b.2
  have ht := t.2
  have h1 : (s : ℕ) * (k - 1) + b + 1 ≤ 2 * (k - 1) := by nlinarith
  have h2 : ((s : ℕ) * (k - 1) + b) * ell k T n + t < ((s : ℕ) * (k - 1) + b + 1) * ell k T n := by
    nlinarith
  calc _ < _ := h2
    _ ≤ 2 * (k - 1) * ell k T n := Nat.mul_le_mul_right _ h1
    _ < n := h

/-- The hidden layout: side `s`, block `b`, position `t` at the vertex `(s (k - 1) + b) ℓ + t`;
the columns are the vertices from `2 (k - 1) ℓ` on. -/
def layout {k T n : ℕ} (h : 2 * (k - 1) * ell k T n < n) : Guess k T n :=
  fun s b t ↦ ⟨((s : ℕ) * (k - 1) + b) * ell k T n + t, layout_lt h s b t⟩

/-- The randomness of the construction: the coefficients `x`, the values `α`, the independent
values `β'` and the padding bits. -/
abbrev Sample (k T n : ℕ) : Type :=
  (Fin (mdeg T n) → Fld T n) × (Fin n → Fld T n) × (Fin n → Fld T n) × Tensor k n

/-- `α_v` is unique among the columns of `g`. -/
def UniqueCol {k T n : ℕ} (g : Guess k T n) (α : Fin n → Fld T n) (v : Fin n) : Prop :=
  ∀ w, IsCol g w → w ≠ v → α w ≠ α v

open Classical in
/-- `β_v = Σ xᵢ α_vⁱ` when `α_v` is unique among the columns, `β'_v` otherwise. -/
noncomputable def betaVal {k T n : ℕ} (g : Guess k T n) (ω : Sample k T n) (v : Fin n) :
    Fld T n :=
  if UniqueCol g ω.2.1 v then ∑ i, ω.1 i * ω.2.1 v ^ (i : ℕ) else ω.2.2.1 v

open Classical in
/-- The planted tensor before relabelling: on the cells of each column `v` of the layout, the
bits of `α_v` (side `0`) and of `β_v` (side `1`); padding bits elsewhere. -/
noncomputable def encode {k T n : ℕ} (h : 2 * (k - 1) * ell k T n < n) (ω : Sample k T n) :
    Tensor k n := fun S ↦
  if hα : ∃ v, ∃ i : Fin (rbits T n), IsCol (layout h) v ∧ S.1 = cell (layout h) 0 v i then
    (bitEquiv T n).symm (ω.2.1 hα.choose) hα.choose_spec.choose
  else if hβ : ∃ v, ∃ i : Fin (rbits T n), IsCol (layout h) v ∧ S.1 = cell (layout h) 1 v i then
    (bitEquiv T n).symm (betaVal (layout h) ω hβ.choose) hβ.choose_spec.choose
  else ω.2.2.2 S

/-- **The planted distribution** `P_n`: the planted tensor of a uniformly random sample,
relabelled by a uniformly random permutation; the uniform distribution when `n` is too small for
the layout. -/
noncomputable def planted (k T n : ℕ) : Measure (Tensor k n) :=
  if h : 2 * (k - 1) * ell k T n < n then
    ((Fintype.card (Sample k T n) * n.factorial : ENNReal)⁻¹) •
      ∑ ω : Sample k T n, ∑ σ : Equiv.Perm (Fin n), Measure.dirac (relabel σ (encode h ω))
  else uniformTensor k n

end BHJK25.RS
