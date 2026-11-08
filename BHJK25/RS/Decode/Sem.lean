module

public import BHJK25.RS.Decode.Algo
public import BHJK25.RS.Basic.Lists
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Field.Defs

/-!
# The per-guess decoder: reading lists in a field

A reading `S : BHJK25.RS.DecodeAux.Sem fl F` of coefficient lists as elements of a field `F`
commutes with the arithmetic of `BHJK25.RS.DecodeAux` and detects zero. A list of field elements
`q` is read as the polynomial `Σ_{i < L} q_i X^i` (`BHJK25.RS.DecodeAux.Sem.toP`), and a list of
such lists `Q` as the bivariate polynomial `Σ_{j < BY} Q_j(X) Y^j`
(`BHJK25.RS.DecodeAux.Sem.toBP`), in `F[X][Y] = Polynomial (Polynomial F)`; entries outside the
window `j < BY`, `i < L` are ignored.
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

open Polynomial

/-- A reading of coefficient lists as elements of a field `F` that commutes with the arithmetic
and detects zero. -/
structure Sem (fl : List ℕ) (F : Type*) [Field F] where
  /-- The value of a coefficient list. -/
  ev : List ℕ → F
  ev_add : ∀ a b, ev (fadd fl a b) = ev a + ev b
  ev_sub : ∀ a b, ev (fsub fl a b) = ev a - ev b
  ev_mul : ∀ a b, ev (fmul fl a b) = ev a * ev b
  ev_pow : ∀ a k, ev (fpow fl a k) = ev a ^ k
  ev_zero : ev (fzero fl) = 0
  ev_one : ev (fone fl) = 1
  ev_nil : ev [] = 0
  isZ_iff : ∀ c, isZ fl c = true ↔ ev c = 0

namespace Sem

attribute [simp] ev_add ev_sub ev_mul ev_pow ev_zero ev_one ev_nil

variable {fl : List ℕ} {F : Type*} [Field F] (S : Sem fl F)

theorem isZ_eq_false_iff (c : List ℕ) : isZ fl c = false ↔ S.ev c ≠ 0 := by
  rw [Ne, ← S.isZ_iff, Bool.not_eq_true]

private theorem ev_foldl_fadd (l : List (List ℕ)) (a : List ℕ) :
    S.ev (l.foldl (fadd fl) a) = S.ev a + (l.map S.ev).sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih, S.ev_add, List.map_cons, List.sum_cons, add_assoc]

/-- The value of a sum. -/
theorem ev_fsum (l : List (List ℕ)) : S.ev (fsum fl l) = (l.map S.ev).sum := by
  rw [fsum, ev_foldl_fadd, S.ev_zero, zero_add]

/-- The value of a sum over `List.range`. -/
theorem ev_fsum_range (K : ℕ) (g : ℕ → List ℕ) :
    S.ev (fsum fl ((List.range K).map g)) = ∑ k ∈ Finset.range K, S.ev (g k) := by
  rw [ev_fsum, List.map_map, sum_map_range]
  rfl

/-- The value of a dot product. -/
theorem ev_dot (K : ℕ) (a v : List (List ℕ)) :
    S.ev (dot fl K a v) = ∑ k ∈ Finset.range K, S.ev (a.getD k []) * S.ev (v.getD k []) := by
  rw [dot, ev_fsum_range]
  simp

/-! ### Polynomials -/

/-- The polynomial `Σ_{i < L} q_i X^i`. -/
noncomputable def toP (L : ℕ) (q : List (List ℕ)) : F[X] :=
  ∑ i ∈ Finset.range L, monomial i (S.ev (q.getD i []))

/-- The bivariate polynomial `Σ_{j < BY} Q_j(X) Y^j`. -/
noncomputable def toBP (BY L : ℕ) (Q : List (List (List ℕ))) : F[X][X] :=
  ∑ j ∈ Finset.range BY, monomial j (S.toP L (Q.getD j []))

theorem coeff_toP (L : ℕ) (q : List (List ℕ)) (i : ℕ) :
    (S.toP L q).coeff i = if i < L then S.ev (q.getD i []) else 0 := by
  rw [toP, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range L) i]
  simp

theorem coeff_toBP (BY L : ℕ) (Q : List (List (List ℕ))) (j : ℕ) :
    (S.toBP BY L Q).coeff j = if j < BY then S.toP L (Q.getD j []) else 0 := by
  rw [toBP, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range BY) j]
  simp

/-- The coefficient of `X^i Y^j`. -/
theorem coeff_coeff_toBP (BY L : ℕ) (Q : List (List (List ℕ))) (j i : ℕ) :
    ((S.toBP BY L Q).coeff j).coeff i =
      if j < BY ∧ i < L then S.ev ((Q.getD j []).getD i []) else 0 := by
  rw [coeff_toBP]
  by_cases hj : j < BY
  · rw [ite_eq_left hj, coeff_toP]
    by_cases hi : i < L
    · rw [ite_eq_left hi, ite_eq_left ⟨hj, hi⟩]
    · rw [ite_eq_right hi, ite_eq_right fun h ↦ hi h.2]
  · rw [ite_eq_right hj, ite_eq_right fun h ↦ hj h.1, coeff_zero]

/-- The coefficients of `toBP` vanish outside the window. -/
theorem lt_of_coeff_coeff_toBP_ne_zero {BY L : ℕ} {Q : List (List (List ℕ))} {j i : ℕ}
    (h : ((S.toBP BY L Q).coeff j).coeff i ≠ 0) : j < BY ∧ i < L := by
  rw [coeff_coeff_toBP] at h
  by_contra h'
  exact h (ite_eq_right h')

/-- A bivariate polynomial supported in the window is read from the list of its coefficients. -/
theorem toBP_eq_of_coeff {BY L : ℕ} {Q : List (List (List ℕ))} {P : F[X][X]}
    (h1 : ∀ j < BY, ∀ i < L, S.ev ((Q.getD j []).getD i []) = (P.coeff j).coeff i)
    (h2 : ∀ j i, (P.coeff j).coeff i ≠ 0 → j < BY ∧ i < L) : S.toBP BY L Q = P := by
  ext j i
  rw [coeff_coeff_toBP]
  split_ifs with h
  · exact h1 j h.1 i h.2
  · by_contra hne
    exact h (h2 j i (Ne.symm hne))

/-- The `Y`-degree of `toBP` is below `BY`. -/
theorem natDegree_toBP_lt {BY L : ℕ} (hBY : 0 < BY) (Q : List (List (List ℕ))) :
    (S.toBP BY L Q).natDegree < BY := by
  refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ ?_) (Nat.sub_lt hBY one_pos)
  rw [coeff_toBP, ite_eq_right (by omega)]

end Sem

end BHJK25.RS.DecodeAux
