module

public import BHJK25.RS.Decode.Sem
public import Mathlib.Algebra.Polynomial.Taylor

/-!
# The per-guess decoder: Roth–Ruckenstein on lists

The list operations of Roth–Ruckenstein compute, read in the field, in the window `j < BY`,
`i < L` of `BHJK25.RS.DecodeAux.Sem.toBP`:

* `Q(0, c)` (`BHJK25.RS.DecodeAux.Sem.ev_eval0`);
* the Taylor shift `Q(X, Y + c)`, exactly (`BHJK25.RS.DecodeAux.Sem.toBP_taylorL`): Horner's rule
  stays in the window, since after `t` steps the partial result has `Y`-degree below `t`;
* `H(X, X Y)`, when it stays in the window (`BHJK25.RS.DecodeAux.Sem.toBP_shiftL`);
* the division by the largest power `X^v` dividing `Q ≠ 0`, after which `Q(0, Y) ≠ 0`
  (`BHJK25.RS.DecodeAux.Sem.toBP_stripL`).
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

namespace Sem

open Polynomial

variable {fl : List ℕ} {F : Type*} [Field F] (S : Sem fl F)

/-! ### Reading the list builders -/

private theorem getD_getD_map_range {BY L j i : ℕ} (g : ℕ → ℕ → List ℕ) (hj : j < BY)
    (hi : i < L) :
    (((List.range BY).map fun j ↦ (List.range L).map fun i ↦ g j i).getD j []).getD i [] =
      g j i := by
  rw [getD_map_range_of_lt _ _ hj, getD_map_range_of_lt _ _ hi]

/-- `eval0` computes `Q(0, c)`. -/
theorem ev_eval0 {BY L : ℕ} (hL : 0 < L) (Q : List (List (List ℕ))) (c : List ℕ) :
    S.ev (eval0 fl BY Q c) = ((S.toBP BY L Q).map constantCoeff).eval (S.ev c) := by
  rw [eval0, S.ev_fsum_range, toBP, Polynomial.map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [map_monomial, eval_monomial, constantCoeff_apply, coeff_toP, ite_eq_left hL, S.ev_mul,
    S.ev_pow]

/-! ### The Taylor shift -/

/-- The coefficients of one Horner step `C q + (Y + C r) P`. -/
private theorem coeff_coeff_horner (q : F[X]) (r : F) (P : F[X][X]) (j i : ℕ) :
    ((C q + (X + C (C r)) * P).coeff j).coeff i =
      (if j = 0 then q.coeff i else (P.coeff (j - 1)).coeff i) + r * (P.coeff j).coeff i := by
  cases j with
  | zero => simp [coeff_C]
  | succ j => simp [add_mul, coeff_X_mul]

private theorem toBP_taylorStep {BY L : ℕ} (hBY : 0 < BY) (c : List ℕ)
    (acc : List (List (List ℕ))) (q : List (List ℕ)) (h : (S.toBP BY L acc).coeff (BY - 1) = 0) :
    S.toBP BY L (taylorStep fl BY L c acc q) =
      C (S.toP L q) + (X + C (C (S.ev c))) * S.toBP BY L acc := by
  refine S.toBP_eq_of_coeff (fun j hj i hi ↦ ?_) (fun j i hne ↦ ?_)
  · rw [taylorStep, getD_getD_map_range _ hj hi, S.ev_add, S.ev_mul, coeff_coeff_horner,
      S.coeff_coeff_toBP BY L acc j i, ite_eq_left (show j < BY ∧ i < L from ⟨hj, hi⟩), add_comm]
    split_ifs with hj0
    · rw [coeff_toP, ite_eq_left hi]
    · rw [coeff_coeff_toBP, ite_eq_left (show j - 1 < BY ∧ i < L from ⟨by omega, hi⟩)]
  · by_contra hcon
    apply hne
    rw [coeff_coeff_horner]
    by_cases hi : i < L
    · have hj : BY ≤ j := by
        by_contra hj
        exact hcon ⟨by omega, hi⟩
      have hj1 : (S.toBP BY L acc).coeff (j - 1) = 0 := by
        rcases (show j - 1 = BY - 1 ∨ BY ≤ j - 1 by omega) with h' | h'
        · rw [h', h]
        · rw [coeff_toBP, ite_eq_right (by omega)]
      rw [ite_eq_right (by omega), hj1, coeff_toBP, ite_eq_right (by omega)]
      simp
    · simp [coeff_coeff_toBP, coeff_toP, hi]

private theorem toBP_foldr_taylorStep {BY L : ℕ} (hBY : 0 < BY) (Q : List (List (List ℕ)))
    (c : List ℕ) (n : ℕ) (hn : n ≤ BY) (s : ℕ) :
    S.toBP BY L ((List.range' s n).foldr
        (fun b acc ↦ taylorStep fl BY L c acc (Q.getD b [])) []) =
      ∑ k ∈ Finset.range n, C (S.toP L (Q.getD (s + k) [])) * (X + C (C (S.ev c))) ^ k ∧
    ∀ j, n ≤ j → (S.toBP BY L ((List.range' s n).foldr
        (fun b acc ↦ taylorStep fl BY L c acc (Q.getD b [])) [])).coeff j = 0 := by
  induction n generalizing s with
  | zero =>
    have h0 : S.toBP BY L [] = 0 := by
      ext j i
      simp [coeff_coeff_toBP]
    simp [h0]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega) (s + 1)
    rw [List.range'_succ, List.foldr_cons,
      S.toBP_taylorStep hBY c _ (Q.getD s []) (ih2 (BY - 1) (by omega))]
    refine ⟨?_, fun j hj ↦ ?_⟩
    · rw [ih1, Finset.sum_range_succ', Finset.mul_sum, add_comm, pow_zero, mul_one, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [show s + (k + 1) = s + 1 + k by omega, pow_succ]
      ring
    · ext i
      rw [coeff_coeff_horner, ite_eq_right (by omega), ih2 _ (by omega), ih2 _ (by omega)]
      simp

/-- `taylorL` computes the Taylor shift `Q(X, Y + c)`. -/
theorem toBP_taylorL {BY L : ℕ} (hBY : 0 < BY) (Q : List (List (List ℕ))) (c : List ℕ) :
    S.toBP BY L (taylorL fl BY L Q c) = taylor (C (S.ev c)) (S.toBP BY L Q) := by
  rw [taylorL, List.foldl_reverse, List.range_eq_range',
    (S.toBP_foldr_taylorStep hBY Q c BY le_rfl 0).1, toBP, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [taylor_monomial, zero_add]

/-! ### The shift and the strip -/

/-- `shiftL` computes `H(X, X Y)` when it stays in the window. -/
theorem toBP_shiftL {BY L : ℕ} (H : List (List (List ℕ)))
    (h : ∀ j i, ((S.toBP BY L H).coeff j).coeff i ≠ 0 → i + j < L) :
    S.toBP BY L (shiftL fl BY L H) = (S.toBP BY L H).comp (C X * X) := by
  refine S.toBP_eq_of_coeff (fun j hj i hi ↦ ?_) (fun j i hne ↦ ?_)
  · rw [shiftL, getD_getD_map_range _ hj hi, comp_C_mul_X_coeff, coeff_mul_X_pow',
      coeff_coeff_toBP]
    by_cases hji : j ≤ i
    · rw [ite_eq_left hji, ite_eq_left hji, ite_eq_left ⟨hj, by omega⟩]
    · rw [ite_eq_right hji, ite_eq_right hji, S.ev_zero]
  · rw [comp_C_mul_X_coeff, coeff_mul_X_pow'] at hne
    by_cases hji : j ≤ i
    · rw [ite_eq_left hji] at hne
      have h1 := h j (i - j) hne
      exact ⟨(S.lt_of_coeff_coeff_toBP_ne_zero hne).1, by omega⟩
    · rw [ite_eq_right hji] at hne
      exact absurd rfl hne

/-- `stripL` divides `Q ≠ 0` by the largest power `X^v` dividing it. -/
theorem toBP_stripL {BY L : ℕ} (Q : List (List (List ℕ))) (hQ : S.toBP BY L Q ≠ 0) :
    ∃ v, S.toBP BY L Q = C (X ^ v) * S.toBP BY L (stripL fl BY L Q) ∧
      (S.toBP BY L (stripL fl BY L Q)).map constantCoeff ≠ 0 := by
  obtain ⟨j₀, i₀, h₀⟩ : ∃ j i, ((S.toBP BY L Q).coeff j).coeff i ≠ 0 := by
    by_contra hcon
    refine hQ (Polynomial.ext fun j ↦ Polynomial.ext fun i ↦ ?_)
    rw [coeff_zero, coeff_zero]
    by_contra hne
    exact hcon ⟨j, i, hne⟩
  have hlt₀ := S.lt_of_coeff_coeff_toBP_ne_zero h₀
  rw [coeff_coeff_toBP, ite_eq_left hlt₀] at h₀
  obtain ⟨v, hv⟩ : ∃ v, (List.range L).find? (fun i ↦
      (List.range BY).any fun j ↦ !isZ fl ((Q.getD j []).getD i [])) = some v := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    refine ⟨i₀, List.mem_range.2 hlt₀.2, ?_⟩
    rw [List.any_eq_true]
    exact ⟨j₀, List.mem_range.2 hlt₀.1, by simpa [S.isZ_eq_false_iff] using h₀⟩
  have hs : stripL fl BY L Q = (List.range BY).map fun j ↦ (List.range L).map fun i ↦
      if i + v < L then fadd fl ((Q.getD j []).getD (i + v) []) (fzero fl) else fzero fl := by
    simp only [stripL, hv, Option.getD_some]
  rw [List.find?_range_eq_some] at hv
  obtain ⟨hv1, hv2, hv3⟩ := hv
  rw [List.mem_range] at hv2
  refine ⟨v, ?_, ?_⟩
  · ext j i
    rw [coeff_C_mul, coeff_X_pow_mul', coeff_coeff_toBP, coeff_coeff_toBP]
    by_cases hvi : v ≤ i
    · rw [ite_eq_left hvi]
      by_cases hj : j < BY ∧ i < L
      · rw [ite_eq_left hj, ite_eq_left ⟨hj.1, by omega⟩, hs,
          getD_getD_map_range _ hj.1 (by omega), ite_eq_left (by omega), Nat.sub_add_cancel hvi,
          S.ev_add, S.ev_zero, add_zero]
      · rw [ite_eq_right hj]
        by_cases hj' : j < BY ∧ i - v < L
        · have hiL : ¬ i < L := fun h ↦ hj ⟨hj'.1, h⟩
          rw [ite_eq_left hj', hs, getD_getD_map_range _ hj'.1 hj'.2, ite_eq_right (by omega),
            S.ev_zero]
        · rw [ite_eq_right hj']
    · rw [ite_eq_right hvi]
      have hz := hv3 i (by omega)
      simp only [Bool.not_eq_true', List.any_eq_false, Bool.not_eq_false,
        List.mem_range] at hz
      split_ifs with hj
      · exact (S.isZ_iff _).1 (hz j hj.1)
      · rfl
  · obtain ⟨j₁, hj₁, hne⟩ := List.any_eq_true.1 hv1
    rw [List.mem_range] at hj₁
    intro h0
    have h1 := congrArg (fun P ↦ P.coeff j₁) h0
    simp only [coeff_map, coeff_zero, constantCoeff_apply] at h1
    rw [coeff_coeff_toBP, ite_eq_left ⟨hj₁, by omega⟩, hs, getD_getD_map_range _ hj₁ (by omega),
      ite_eq_left (by omega), zero_add, S.ev_add, S.ev_zero, add_zero] at h1
    simp only [Bool.not_eq_true', S.isZ_eq_false_iff] at hne
    exact hne h1

end Sem

end BHJK25.RS.DecodeAux
