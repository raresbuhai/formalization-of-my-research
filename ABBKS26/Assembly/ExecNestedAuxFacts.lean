module

public import ABBKS26.Assembly.ExecNestedAuxBuild

/-! # Elementary semantic and machine lemmas for the nested list primitives -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common MvPolynomial
open Encoding (encRat)
open SoS.Solver (RawPoly encRawPoly)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

/-- Constants retain their usual interpretation even in zero variables. -/
theorem constant_toPoly (v : ℕ) (c : ℚ) :
    (constant c).toPoly v = C c := by
  simp [constant, SoS.Solver.RawPoly.toPoly]

/-- Scaling preserves the interpretation without collecting duplicate terms. -/
theorem scale_toPoly (v : ℕ) (c : ℚ) (p : RawPoly) :
    (scale c p).toPoly v = C c * p.toPoly v := by
  simp only [scale, SoS.Solver.RawPoly.toPoly, List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp [mul_assoc]

/-- A dense unit row decodes to a single finitely supported exponent. -/
theorem unitExp_toFinsupp (v i e : ℕ) (hi : i < v) :
    SoS.Mono.toFinsupp v (unitExp v i e) = Finsupp.single ⟨i, hi⟩ e := by
  ext j
  simp [unitExp, List.getD_eq_getElem?_getD, Finsupp.single_apply, Fin.ext_iff, eq_comm]

/-- An in-range singleton term is precisely the corresponding variable power. -/
theorem unit_toPoly (v i e : ℕ) (c : ℚ) (hi : i < v) :
    SoS.Solver.RawPoly.toPoly v [(unitExp v i e, c)] = C c * X ⟨i, hi⟩ ^ e := by
  rw [SoS.Poly.toPoly_eq_sum']
  simp [SoS.Poly.termPoly, unitExp_toFinsupp v i e hi, X_pow_eq_monomial,
    C_mul_monomial]


/-- Interpret solver-variable rows in the natural-index polynomial ring. -/
noncomputable def decode (v : ℕ) (p : RawPoly) : Rounding.NPoly :=
  rename Fin.val (SoS.toReal (p.toPoly v))

theorem decode_append (v : ℕ) (p q : RawPoly) :
    decode v (p ++ q) = decode v p + decode v q := by
  simp [decode, SoS.Poly.toPoly_append, SoS.toReal]

theorem decode_constant (v : ℕ) (c : ℚ) : decode v (constant c) = C (c : ℝ) := by
  simp [decode, constant_toPoly, SoS.toReal]

theorem decode_scale (v : ℕ) (c : ℚ) (p : RawPoly) :
    decode v (scale c p) = C (c : ℝ) * decode v p := by
  simp [decode, scale_toPoly, SoS.toReal]

/-- The sphere uses only the first d solver variables. -/
theorem decode_norm (v d : ℕ) (hd : d ≤ v) :
    decode v (normRaw v d) = ∑ i : Fin d, (X i.val : Rounding.NPoly) ^ 2 := by
  unfold decode normRaw
  rw [SoS.Solver.RawPoly.toPoly, List.map_map, SoS.Coords.sum_range_map]
  simp only [SoS.toReal, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := unit_toPoly v i.val 2 1 (i.isLt.trans_le hd)
  have hr := congrArg (fun f ↦ rename Fin.val (SoS.toReal f)) h
  simpa [SoS.Solver.RawPoly.toPoly, SoS.toReal] using hr

/-- The ball includes every solver variable, in the same order as `nestedSystem`. -/
theorem decode_ball (v : ℕ) (b : ℚ) :
    decode v (constant b ++ scale (-1) (normRaw v v)) =
      C (b : ℝ) - ∑ i ∈ Finset.range v, (X i : Rounding.NPoly) ^ 2 := by
  rw [decode_append, decode_constant, decode_scale, decode_norm v v le_rfl]
  simp only [Rat.cast_neg, Rat.cast_one, C_neg, C_1, neg_one_mul, sub_eq_add_neg]
  congr 2
  exact Fin.sum_univ_eq_sum_range (fun i ↦ (X i : Rounding.NPoly) ^ 2) v

/-- Normalizing an already normalized exponent row has no effect. -/
theorem expo_idem (v : ℕ) (e : List ℕ) :
    SoS.Poly.expo v (SoS.Poly.expo v e) = SoS.Poly.expo v e := by
  change (List.range v).map (fun i ↦ (SoS.Poly.expo v e).getD i 0) = _
  apply List.map_congr_left
  intro i hi
  exact SoS.Poly.getD_expo e (List.mem_range.1 hi)

/-- Deleting all copies of a cancelled monomial preserves every coefficient. -/
theorem coeff_clean (v : ℕ) (p : RawPoly) (μ : List ℕ) :
    SoS.Poly.coeff v (clean v p) μ = SoS.Poly.coeff v p μ := by
  rw [SoS.Poly.coeff]
  simp only [clean, List.filter_map, List.filter_filter, List.map_map,
    Function.comp_def, expo_idem]
  have htest (t : List ℕ × ℚ) :
      (decide (SoS.Poly.expo v t.1 = μ) &&
        decide (SoS.Poly.coeff v p (SoS.Poly.expo v t.1) ≠ 0)) =
      decide (SoS.Poly.expo v t.1 = μ ∧ SoS.Poly.coeff v p μ ≠ 0) := by
    by_cases ht : SoS.Poly.expo v t.1 = μ <;> simp [ht]
  simp only [htest]
  by_cases hμ : SoS.Poly.coeff v p μ = 0
  · simp [hμ]
  · simp only [hμ, ne_eq, not_false_eq_true, and_true]
    rfl

/-- Normalization before the capped substitution preserves the input polynomial. -/
theorem clean_toPoly (v : ℕ) (p : RawPoly) :
    (clean v p).toPoly v = p.toPoly v := by
  ext α
  rw [← SoS.Poly.toFinsupp_ofFn α]
  rw [SoS.Poly.coeff_toPoly _ (by simp), SoS.Poly.coeff_toPoly _ (by simp), coeff_clean]

@[fun_prop]
theorem unitExp_polytime {α : Type} {input : α ↪ List Bool}
    {v i e : α → ℕ} (hv : ComputableInPolyTime v input encUnary)
    (hi : ComputableInPolyTime i input encUnary)
    (he : ComputableInPolyTime e input encNat) :
    ComputableInPolyTime (fun a ↦ unitExp (v a) (i a) (e a))
      input (encList encNat) := by
  unfold unitExp
  apply mapWithInput (range.comp hv)
  exact ite_decide (.of_tidy (ComputableTidilyInPolyTime.decide_eq'
    (snd _ _).tidy (hi.comp (fst _ _)).tidy))
    (he.comp (fst _ _)) (const 0)

@[fun_prop]
theorem scale_polytime {α : Type} {input : α ↪ List Bool}
    {c : α → ℚ} {p : α → RawPoly} (hc : ComputableInPolyTime c input encRat)
    (hp : ComputableInPolyTime p input encRawPoly) :
    ComputableInPolyTime (fun a ↦ scale (c a) (p a)) input encRawPoly := by
  unfold scale
  apply mapWithInput hp
  exact ((fst _ _).comp (snd _ _)).prod
    (rat_mul' (hc.comp (fst _ _)) ((snd _ _).comp (snd _ _)))

/-- Removing cancelled monomials costs only polynomially many exact coefficient scans. -/
theorem clean_polytime : ComputableInPolyTime
    (fun q : ℕ × RawPoly ↦ clean q.1 q.2) (encPair encUnary encRawPoly) encRawPoly := by
  unfold clean
  apply mapWithInput (filterWithInput (by fun_prop) (by fun_prop))
  exact (SoS.Poly.expo' (by fun_prop) (by fun_prop)).prod (by fun_prop)

/-- Coefficient splitting scans the sparse input once for each requested exponent. -/
theorem split_polytime : ComputableInPolyTime
    (fun q : ℕ × List ℕ × RawPoly ↦ Rounding.splitCoeffsRaw q.1 q.2.1 q.2.2)
    (encPair encUnary (encPair (encList encNat) encRawPoly)) encRawPoly := by
  unfold Rounding.splitCoeffsRaw
  apply mapWithInput (filterWithInput (by fun_prop) (by fun_prop))
  fun_prop

end ABBKS26.Assembly.Exec.NestedProgram
