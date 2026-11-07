module

public import Background.SumOfSquares.Algorithm.PDTestRows
public import Background.PolyTime.Rat
public import Mathlib.Data.List.GetD

/-!
# The positive definiteness test on rational matrices

A rational matrix, given as a list of rows, is multiplied by the product `D` of the denominators of
its entries, which makes it an integer matrix, and tested with `SoS.PDTestRows.test`
(`SoS.PDTestRat.test`). Multiplying by `D > 0` changes neither positive definiteness nor the sign
of a quadratic form, so the answer is correct for the rational matrix (`SoS.PDTestRat.test_spec`).
The test runs in polynomial time (`SoS.PDTestRat.test_polytime`).
-/

@[expose] public section

namespace SoS.PDTestRat

open Cslib (rowEntry)
open Cslib.Circuits.Rational (ofRows)
open Matrix

/-- Entry `(i, j)` of a rational table; missing entries read as `0`. -/
def entry (rows : List (List ℚ)) (i j : ℕ) : ℚ :=
  (rows.getD i []).getD j 0

/-- The square matrix of a rational table, of dimension its number of rows. -/
def toMatrix (rows : List (List ℚ)) : Matrix (Fin rows.length) (Fin rows.length) ℚ :=
  Matrix.of fun i j => entry rows i j

/-- The product of the denominators of the entries. -/
def commonDen (rows : List (List ℚ)) : ℤ :=
  (rows.flatten.map fun q => (q.den : ℤ)).prod

/-- The table multiplied by `commonDen`, which makes it an integer table. -/
def scale (rows : List (List ℚ)) : List (List ℤ) :=
  rows.map fun r => r.map fun q => (q * (commonDen rows : ℚ)).num

/-- **The test**: `none` if the matrix is positive definite, otherwise a witness. -/
def test (rows : List (List ℚ)) : Option (List ℤ) :=
  PDTestRows.test (scale rows)

/-! ### Correctness -/

theorem commonDen_pos (rows : List (List ℚ)) : 0 < commonDen rows := by
  unfold commonDen
  refine List.prod_pos fun z hz => ?_
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hz
  exact_mod_cast q.den_pos

/-- Multiplying an entry by `commonDen` gives an integer. -/
theorem num_mul_commonDen {rows : List (List ℚ)} {q : ℚ} (hq : q ∈ rows.flatten) :
    (((q * (commonDen rows : ℚ)).num : ℤ) : ℚ) = q * commonDen rows := by
  have hdvd : (q.den : ℤ) ∣ commonDen rows :=
    List.dvd_prod (List.mem_map_of_mem (f := fun q : ℚ => (q.den : ℤ)) hq)
  obtain ⟨e, he⟩ := hdvd
  have h : q * (commonDen rows : ℚ) = ((q.num * e : ℤ) : ℚ) := by
    rw [he]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  rw [h, Rat.num_intCast]

theorem getD_map_of_eq {α β : Type} (f : α → β) (l : List α) (j : ℕ) {d : β} {d' : α}
    (h : f d' = d) : (l.map f).getD j d = f (l.getD j d') := by
  rw [← h, List.getD_map]

/-- Every entry is an entry of the table or the default `0`. -/
theorem entry_mem_or_zero (rows : List (List ℚ)) (i j : ℕ) :
    entry rows i j ∈ rows.flatten ∨ entry rows i j = 0 := by
  unfold entry
  by_cases hi : i < rows.length
  · rw [List.getD_eq_getElem rows [] hi]
    by_cases hj : j < rows[i].length
    · rw [List.getD_eq_getElem _ 0 hj]
      exact Or.inl (List.mem_flatten.2 ⟨rows[i], List.getElem_mem hi, List.getElem_mem hj⟩)
    · exact Or.inr (List.getD_eq_default _ 0 (by omega))
  · rw [List.getD_eq_default rows [] (by omega)]
    simp

theorem rowEntry_scale (rows : List (List ℚ)) (i j : ℕ) :
    ((rowEntry (scale rows) i j : ℤ) : ℚ) = commonDen rows * entry rows i j := by
  have h : rowEntry (scale rows) i j = (entry rows i j * (commonDen rows : ℚ)).num := by
    unfold rowEntry scale entry
    rw [getD_map_of_eq _ _ _ (d := []) (d' := []) rfl,
      getD_map_of_eq _ _ _ (d := 0) (d' := 0) (by simp)]
  rw [h]
  rcases entry_mem_or_zero rows i j with hq | hq
  · rw [num_mul_commonDen hq, mul_comm]
  · simp [hq]

/-- **The test is correct.** For a symmetric real matrix `M` whose entries are those of the rational
table, `none` means that `M` is positive definite, and `some w` gives a nonzero integer vector `v`,
with `w` its list of entries, such that `vᵀ M v ≤ 0`. -/
theorem test_spec {n : ℕ} (rows : List (List ℚ)) (hn : rows.length = n)
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ i j : Fin n, M i j = entry rows i j)
    (hsym : Mᵀ = M) :
    (test rows = none → ∀ v : Fin n → ℝ, v ≠ 0 → 0 < v ⬝ᵥ M *ᵥ v) ∧
    ∀ w, test rows = some w → ∃ v : Fin n → ℤ, w = List.ofFn v ∧ v ≠ 0 ∧
      (fun i => (v i : ℝ)) ⬝ᵥ M *ᵥ (fun i => (v i : ℝ)) ≤ 0 := by
  set D : ℝ := ((commonDen rows : ℤ) : ℝ)
  have hD : 0 < D := Int.cast_pos.2 (commonDen_pos rows)
  -- The integer matrix of the scaled table is `D M`.
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => rowEntry (scale rows) i j
  have hNM : N.map (Int.cast : ℤ → ℝ) = D • M := by
    ext i j
    have h := congrArg (Rat.cast : ℚ → ℝ) (rowEntry_scale rows i j)
    push_cast at h
    simp [N, D, h, hM]
  have hNsym : Nᵀ = N := by
    ext i j
    have h1 := congrFun (congrFun hNM i) j
    have h2 := congrFun (congrFun hNM j) i
    have hMij : M j i = M i j := by rw [← transpose_apply M j i, hsym]
    simp only [map_apply, Matrix.smul_apply, smul_eq_mul] at h1 h2
    rw [transpose_apply]
    exact_mod_cast h2.trans (hMij ▸ h1.symm)
  have hquad : ∀ v : Fin n → ℝ, v ⬝ᵥ (N.map (Int.cast : ℤ → ℝ)) *ᵥ v = D * (v ⬝ᵥ M *ᵥ v) := by
    intro v
    rw [hNM, smul_mulVec, dotProduct_smul, smul_eq_mul]
  obtain ⟨hnone, hsome⟩ := PDTestRows.test_spec' (scale rows) (by simp [scale, hn]) N
    (fun _ _ => rfl) hNsym
  refine ⟨fun h v hv => ?_, fun w h => ?_⟩
  · have := hnone h v hv
    rw [hquad] at this
    exact pos_of_mul_pos_right this hD.le
  · obtain ⟨v, hw, hv, hle⟩ := hsome w h
    refine ⟨v, hw, hv, ?_⟩
    have hcast : ((v ⬝ᵥ N *ᵥ v : ℤ) : ℝ) =
        (fun i => (v i : ℝ)) ⬝ᵥ (N.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => (v i : ℝ)) := by
      simp [dotProduct, mulVec]
    have : D * ((fun i => (v i : ℝ)) ⬝ᵥ M *ᵥ (fun i => (v i : ℝ))) ≤ 0 := by
      rw [← hquad, ← hcast]
      exact_mod_cast hle
    exact nonpos_of_mul_nonpos_right this hD

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-- Rational matrices, as lists of rows. -/
abbrev encRatRows : List (List ℚ) ↪ List Bool := encList (encList encRat)

theorem commonDen_polytime : ComputableInPolyTime commonDen encRatRows encIntBin := by
  unfold commonDen
  have h : ComputableInPolyTime (fun rows : List (List ℚ) => rows.flatten.map fun q => (q.den : ℤ))
      encRatRows (encList encIntBin) := by fun_prop
  exact .of_tidy (ComputableTidilyInPolyTime.intBin_prod.comp h.tidy)

theorem scale_polytime : ComputableInPolyTime scale encRatRows PDTestRows.encRows := by
  unfold scale
  have hD := commonDen_polytime
  refine mapWithInput (by fun_prop) ?_
  refine mapWithInput (by fun_prop) ?_
  fun_prop

/-- **The test runs in polynomial time.** -/
theorem test_polytime : ComputableInPolyTime test encRatRows (encOption (encList encIntBin)) :=
  PDTestRows.test_polytime.comp scale_polytime

end PolyTime

end SoS.PDTestRat
