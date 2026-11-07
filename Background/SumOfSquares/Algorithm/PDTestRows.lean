module

public import Background.SumOfSquares.PDTest
public import Complexity.Computability.Circuit.Rational.Runtime.Determinant
public import Complexity.Computability.PolyTime.Int.Table
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Complexity.Tactic.PolyTime

/-!
# The positive definiteness test on lists of integers

`SoS.PDTest.test` as a program on integer matrices given as lists of rows, which runs in
polynomial time on multitape Turing machines (`SoS.PDTestRows.test_polytime`) and computes the
same answer (`SoS.PDTestRows.test_eq`).

By `SoS.PDTest.test_eq_find`, the test stops at the first leading block whose Schur complement
`c det B - bᵀ adj(B) b` is not positive, and returns that block's witness `(-adj(B) b, det B)`
padded with zeros. Every quantity is a determinant of a submatrix: `det B`, and by Cramer's rule
the entries of `adj(B) b`. They are computed with complexitylib's polynomial-time integer
determinant `Cslib.Circuits.Rational.detRows`.
-/

@[expose] public section

namespace SoS.PDTestRows

open Cslib (rowEntry tabulateTable rowEntry_tabulateTable_of_lt)
open Cslib.Circuits.Rational (detRows ofRows detRows_eq_det_of_rowEntry)
open Matrix

/-- The leading `k × k` block of a table. -/
def block (rows : List (List ℤ)) (k : ℕ) : List (List ℤ) :=
  tabulateTable k k fun i j => rowEntry rows i j

/-- The leading `k × k` block with column `c` replaced by the column `k` above the diagonal. -/
def cramerBlock (rows : List (List ℤ)) (k c : ℕ) : List (List ℤ) :=
  tabulateTable k k fun i j => if j = c then rowEntry rows i k else rowEntry rows i j

/-- `adj(B) b`, by Cramer's rule. -/
def cof (rows : List (List ℤ)) (k : ℕ) : List ℤ :=
  (List.range k).map fun c => detRows (cramerBlock rows k c)

/-- `s = c det B - bᵀ adj(B) b` for the leading `(k + 1) × (k + 1)` block. -/
def schur (rows : List (List ℤ)) (k : ℕ) : ℤ :=
  rowEntry rows k k * detRows (block rows k) -
    ((List.range k).map fun c => rowEntry rows c k * detRows (cramerBlock rows k c)).sum

/-- The witness `(-adj(B) b, det B)` of the leading `(k + 1) × (k + 1)` block, padded with zeros
to the number of rows. -/
def witness (rows : List (List ℤ)) (k : ℕ) : List ℤ :=
  (cof rows k).map (fun z => -z) ++
    detRows (block rows k) :: List.replicate (rows.drop (k + 1)).length 0

/-- **The test**: `none` if the matrix is positive definite, otherwise a witness. -/
def test (rows : List (List ℤ)) : Option (List ℤ) :=
  ((List.range rows.length).find? fun k => decide (schur rows k ≤ 0)).elim none
    fun k => some (witness rows k)

/-! ### It computes `SoS.PDTest.test` -/

section Correct

variable (rows : List (List ℤ)) (k : Fin rows.length)

theorem lead_leadBlock_apply (i j : Fin k) :
    PDTest.lead (PDTest.leadBlock (ofRows rows) k) i j = rowEntry rows i j := rfl

theorem det_lead_leadBlock :
    (PDTest.lead (PDTest.leadBlock (ofRows rows) k)).det = detRows (block rows k) := by
  refine (detRows_eq_det_of_rowEntry _ (by simp [block]) fun i j => ?_).symm
  rw [block, rowEntry_tabulateTable_of_lt _ i.2 j.2]
  rfl

theorem cof_leadBlock (c : Fin k) :
    PDTest.cof (PDTest.leadBlock (ofRows rows) k) c = detRows (cramerBlock rows k c) := by
  rw [PDTest.cof, ← cramer_eq_adjugate_mulVec, cramer_apply]
  refine (detRows_eq_det_of_rowEntry _ (by simp [cramerBlock]) fun i j => ?_).symm
  rw [cramerBlock, rowEntry_tabulateTable_of_lt _ i.2 j.2, updateCol_apply]
  simp only [Fin.val_inj]
  split_ifs <;> rfl

theorem schur_eq : schur rows k = PDTest.schur (PDTest.leadBlock (ofRows rows) k) := by
  rw [schur, PDTest.schur, det_lead_leadBlock, dotProduct]
  congr 1
  simp only [cof_leadBlock]
  exact (Fin.sum_univ_eq_sum_range
    (fun c => rowEntry rows c k * detRows (cramerBlock rows k c)) k).symm

theorem witness_eq : witness rows k = List.ofFn (PDTest.padWitness (ofRows rows) k) := by
  have hk := k.isLt
  apply List.ext_getElem
  · simp only [witness, cof, List.length_append, List.length_map, List.length_range,
      List.length_cons, List.length_replicate, List.length_drop, List.length_ofFn]
    omega
  · intro j h1 h2
    simp only [List.getElem_ofFn, PDTest.padWitness, PDTest.witness]
    rcases lt_trichotomy j k with hj | rfl | hj
    · rw [dite_eq_left_of_eq_true (eq_true (by omega))]
      have hcast : (⟨j, by omega⟩ : Fin (k + 1)) = Fin.castSucc ⟨j, hj⟩ := rfl
      rw [hcast, Fin.snoc_castSucc, Pi.neg_apply, cof_leadBlock]
      simp [witness, cof, List.getElem_append_left, hj]
    · rw [dite_eq_left_of_eq_true (eq_true le_rfl)]
      have hcast : (⟨(k : ℕ), by omega⟩ : Fin (k + 1)) = Fin.last k := rfl
      rw [hcast, Fin.snoc_last, det_lead_leadBlock]
      simp [witness, cof, List.getElem_append_right]
    · rw [dite_eq_right_of_eq_false (eq_false (by omega))]
      simp only [witness, cof]
      rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      rw [List.getElem_cons, dite_eq_right_of_eq_false (eq_false (by omega))]
      simp

end Correct

/-- **The list program computes the test.** -/
theorem test_eq (rows : List (List ℤ)) :
    test rows = (PDTest.test (ofRows rows)).map List.ofFn := by
  rw [PDTest.test_eq_find, Option.map_map, test, ← List.map_coe_finRange_eq_range,
    List.find?_map]
  have hp : (fun k : ℕ => decide (schur rows k ≤ 0)) ∘ Fin.val =
      PDTest.stopsAt (ofRows rows) := by
    funext k
    simp [PDTest.stopsAt, schur_eq]
  rw [hp]
  cases (List.finRange rows.length).find? (PDTest.stopsAt (ofRows rows)) with
  | none => rfl
  | some k => simp [witness_eq]

/-- **The test on lists is correct.** For a symmetric integer matrix given by its rows, `none`
means that it is positive definite over the reals, and `some w` gives a nonzero integer vector
`v`, with `w` its list of entries, such that `vᵀ A v ≤ 0`. -/
theorem test_spec (rows : List (List ℤ)) (hA : (ofRows rows)ᵀ = ofRows rows) :
    (test rows = none → ∀ v : Fin rows.length → ℝ, v ≠ 0 →
      0 < v ⬝ᵥ ((ofRows rows).map (Int.cast : ℤ → ℝ)) *ᵥ v) ∧
    ∀ w, test rows = some w → ∃ v : Fin rows.length → ℤ, w = List.ofFn v ∧ v ≠ 0 ∧
      v ⬝ᵥ ofRows rows *ᵥ v ≤ 0 := by
  set A := ofRows rows
  have hmap := PDTest.test_map (Int.castRingHom ℝ) (fun x => by simp) A
  have hAr : (A.map (Int.castRingHom ℝ))ᵀ = A.map (Int.castRingHom ℝ) := by
    rw [← transpose_map, hA]
  obtain ⟨hnone, hsome⟩ := PDTest.test_spec _ hAr
  rw [test_eq]
  constructor
  · intro h v hv
    have h' : PDTest.test A = none := by simpa using h
    rw [h', Option.map_none] at hmap
    exact hnone hmap v hv
  · intro w h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [hv, Option.map_some] at hmap
    obtain ⟨hne, hle⟩ := hsome _ hmap
    refine ⟨v, rfl, fun h0 => hne (by simp [h0]), ?_⟩
    have : ((v ⬝ᵥ A *ᵥ v : ℤ) : ℝ) =
        (Int.castRingHom ℝ ∘ v) ⬝ᵥ A.map (Int.castRingHom ℝ) *ᵥ (Int.castRingHom ℝ ∘ v) := by
      simp [dotProduct, mulVec]
    exact_mod_cast this ▸ hle

/-- `SoS.PDTestRows.test_spec` for any integer matrix that the rows describe. -/
theorem test_spec' {n : ℕ} (rows : List (List ℤ)) (hn : rows.length = n)
    (N : Matrix (Fin n) (Fin n) ℤ) (hN : ∀ i j : Fin n, N i j = rowEntry rows i j)
    (hsym : Nᵀ = N) :
    (test rows = none → ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ (N.map (Int.cast : ℤ → ℝ)) *ᵥ v) ∧
    ∀ w, test rows = some w → ∃ v : Fin n → ℤ, w = List.ofFn v ∧ v ≠ 0 ∧ v ⬝ᵥ N *ᵥ v ≤ 0 := by
  subst hn
  have : N = ofRows rows := by
    ext i j
    rw [hN]
    rfl
  subst this
  exact test_spec rows hsym

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM
open Cslib.Circuits.Rational (detRows_polytime)

/-- Integer matrices, as lists of rows. -/
abbrev encRows : List (List ℤ) ↪ List Bool := encList (encList encIntBin)

@[fun_prop]
theorem detRows' {α : Type} {input : α ↪ List Bool} {f : α → List (List ℤ)}
    (hf : ComputableInPolyTime f input encRows) :
    ComputableInPolyTime (fun a => detRows (f a)) input encIntBin :=
  detRows_polytime.comp (g := f) hf

theorem block_polytime : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => block p.1 p.2)
    (encPair encRows encUnary) encRows := by
  unfold block
  fun_prop

theorem cramerBlock_polytime : ComputableInPolyTime
    (fun p : (List (List ℤ) × ℕ) × ℕ => cramerBlock p.1.1 p.1.2 p.2)
    (encPair (encPair encRows encUnary) encUnary) encRows := by
  unfold cramerBlock
  fun_prop

theorem cof_polytime : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => cof p.1 p.2)
    (encPair encRows encUnary) (encList encIntBin) := by
  unfold cof
  exact ComputableInPolyTime.mapWithInput (by fun_prop) (detRows' cramerBlock_polytime)

theorem schur_polytime : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => schur p.1 p.2)
    (encPair encRows encUnary) encIntBin := by
  unfold schur
  have hdet : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => detRows (block p.1 p.2))
      (encPair encRows encUnary) encIntBin := detRows' block_polytime
  have hl : ComputableInPolyTime (fun p : List (List ℤ) × ℕ =>
      (List.range p.2).map fun c => rowEntry p.1 c p.2 * detRows (cramerBlock p.1 p.2 c))
      (encPair encRows encUnary) (encList encIntBin) :=
    ComputableInPolyTime.mapWithInput (by fun_prop) (by
      have := detRows' cramerBlock_polytime
      fun_prop)
  fun_prop

theorem witness_polytime : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => witness p.1 p.2)
    (encPair encRows encUnary) (encList encIntBin) := by
  unfold witness
  have hc := cof_polytime
  have hdet : ComputableInPolyTime (fun p : List (List ℤ) × ℕ => detRows (block p.1 p.2))
      (encPair encRows encUnary) encIntBin := detRows' block_polytime
  fun_prop

/-- **The test runs in polynomial time.** -/
theorem test_polytime : ComputableInPolyTime test encRows (encOption (encList encIntBin)) := by
  unfold test
  have hfind : ComputableInPolyTime (fun rows : List (List ℤ) =>
      (List.range rows.length).find? fun k => decide (schur rows k ≤ 0))
      encRows (encOption encUnary) :=
    ComputableInPolyTime.findWithInput (by fun_prop)
      (.of_tidy (ComputableTidilyInPolyTime.intBin_le' schur_polytime.tidy
        (ComputableTidilyInPolyTime.const 0)))
  exact ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.optionElimWithInput hfind.tidy
    (ComputableTidilyInPolyTime.const none)
    (ComputableTidilyInPolyTime.optionSome _ |>.comp witness_polytime.tidy))

end PolyTime

end SoS.PDTestRows
