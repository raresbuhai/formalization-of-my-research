module

public import BHJK25.RS.Decode.Sem
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image

/-!
# The per-guess decoder: agreement

Read in the field, `BHJK25.RS.DecodeAux.evalPoly` evaluates the polynomial with the given
coefficients (`BHJK25.RS.DecodeAux.Sem.ev_evalPoly`), and `BHJK25.RS.DecodeAux.agree` counts the
distinct `x` among the points `(x, y)` with `p(x) = y`, when the points are written by an injective
encoding (`BHJK25.RS.DecodeAux.Sem.agree_eq`).
-/

@[expose] public section

namespace BHJK25.RS.DecodeAux

namespace Sem

open Polynomial

variable {fl : List ℕ} {F : Type*} [Field F] (S : Sem fl F)

/-- `evalPoly` evaluates the polynomial with the given coefficients. -/
theorem ev_evalPoly (p : List (List ℕ)) (x : List ℕ) :
    S.ev (evalPoly fl p x) = (S.toP p.length p).eval (S.ev x) := by
  rw [evalPoly, ev_fsum_range, toP, eval_finsetSum]
  simp only [S.ev_mul, S.ev_pow, eval_monomial]

/-- The polynomial with `L ≥ 1` coefficients has degree below `L`. -/
theorem natDegree_toP_lt {L : ℕ} (hL : 0 < L) (q : List (List ℕ)) :
    (S.toP L q).natDegree < L := by
  refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) (Nat.sub_lt hL one_pos)
  rw [coeff_toP, ite_eq_right (by omega)]

/-- **Agreement.** With the points written by an injective encoding `enc` read back by `S`,
`agree` counts the distinct `x` among the points `(x, y)` with `p(x) = y`. -/
theorem agree_eq [DecidableEq F] (enc : F → List ℕ) (henc : ∀ x, S.ev (enc x) = x)
    (pts : List (F × F)) (p : List (List ℕ)) :
    agree fl (pts.map fun xy ↦ (enc xy.1, enc xy.2)) p =
      ((pts.filter fun xy ↦ (S.toP p.length p).eval xy.1 = xy.2).map Prod.fst).toFinset.card := by
  have hinj : Function.Injective enc := fun x y h ↦ by rw [← henc x, h, henc]
  rw [agree, List.filter_map, List.map_map]
  have hfilt : (pts.filter ((fun xy : List ℕ × List ℕ ↦
      isZ fl (fsub fl (evalPoly fl p xy.1) xy.2)) ∘ fun xy ↦ (enc xy.1, enc xy.2))) =
      pts.filter fun xy ↦ (S.toP p.length p).eval xy.1 = xy.2 := by
    refine List.filter_congr fun xy _ ↦ ?_
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, S.isZ_iff, S.ev_sub, S.ev_evalPoly, henc, henc, sub_eq_zero,
      decide_eq_true_iff]
  rw [hfilt]
  set l := (pts.filter fun xy ↦ (S.toP p.length p).eval xy.1 = xy.2).map Prod.fst
  have hl : (pts.filter fun xy ↦ (S.toP p.length p).eval xy.1 = xy.2).map
      (Prod.fst ∘ fun xy ↦ (enc xy.1, enc xy.2)) = l.map enc := by
    rw [List.map_map]
    rfl
  rw [hl, ← List.toFinset_card_of_nodup (List.nodup_eraseDupsBy_eq _)]
  have hset : ((l.map enc).eraseDupsBy fun x y ↦ decide (x = y)).toFinset =
      l.toFinset.image enc := by
    ext c
    rw [List.mem_toFinset, List.mem_eraseDupsBy_eq, Finset.mem_image, List.mem_map]
    simp only [List.mem_toFinset]
  rw [hset, Finset.card_image_of_injective _ hinj]

end Sem

end BHJK25.RS.DecodeAux
