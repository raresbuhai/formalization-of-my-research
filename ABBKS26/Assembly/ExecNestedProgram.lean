module

public import ABBKS26.Assembly.ExecNestedProgramAuxPoly
public import ABBKS26.Assembly.ExecNestedProgramAuxSemantic
public import ABBKS26.Assembly.ExecNestedProgramAuxSize

/-!
# Correctness proofs for the concrete nested encoder

The obligations below concern this particular capped list program, not an arbitrary choice
of the existential witness in `Rounding.exists_nestedRaw`. The layout and constraint lemmas
separate indexing from polynomial identities; the plain size lemma keeps degree linear in
the dimension exponent. Neither the sample size nor global sample fuel occurs in that bound.

Moment rounding is an upstream operation: the fixed-grid lemmas give an error bound and a
bit bound only after a magnitude bound has been supplied. `solver_valid` explicitly requires
feasibility; validity of the outer family alone does not imply feasibility of the nested SDP.
Agreement here is with `Rounding.nestedSystem`. Selecting the centered/SUB inputs and running
the deterministic subspace procedure are obligations of the callers, including `ExecRound`.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.NestedProgram

open Common MvPolynomial
open Encoding (encRat)
open SoS.Solver (RawPoly Problem encRawPoly encProblem)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators


/-- A magnitude guard and a fixed dyadic grid remove the original denominator from the
output bit bound. Rounding just the fractional part would not give this conclusion. -/
theorem rounded_coefficient (p b : ℕ) (q : ℚ) (hq : |q| ≤ 2 ^ b) :
    |(roundRat p q : ℝ) - q| ≤ 1 / (2 : ℝ) ^ p ∧
      (encRat (roundRat p q)).length ≤ 3 * (b + 1 + p) + 6 := by
  have hpow : (0 : ℚ) < 2 ^ p := by positivity
  have hlo := Int.floor_le ((2 : ℚ) ^ p * q)
  have hhi := Int.lt_floor_add_one ((2 : ℚ) ^ p * q)
  have herr : |roundRat p q - q| ≤ 1 / (2 : ℚ) ^ p := by
    have he : (⌊(2 : ℚ) ^ p * q⌋ : ℚ) / 2 ^ p - q =
        ((⌊(2 : ℚ) ^ p * q⌋ : ℚ) - 2 ^ p * q) / 2 ^ p := by field_simp
    rw [roundRat, he, abs_div, abs_of_pos hpow]
    exact (div_le_div_iff_of_pos_right hpow).2
      (abs_le.2 ⟨by linarith, by linarith⟩)
  refine ⟨?_, SoS.PolyTime.length_encRat_le_of_small ?_⟩
  · have hh : ((|roundRat p q - q| : ℚ) : ℝ) ≤ ((1 / (2 : ℚ) ^ p : ℚ) : ℝ) :=
      Rat.cast_le.2 herr
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat] using hh
  refine ⟨?_, ⌊(2 : ℚ) ^ p * q⌋, by unfold roundRat; field_simp⟩
  have hinv : 1 / (2 : ℚ) ^ p ≤ 1 := by
    exact (div_le_one hpow).2 (one_le_pow₀ (by norm_num))
  calc
    |roundRat p q| ≤ |roundRat p q - q| + |q| := by
      simpa using abs_add_le (roundRat p q - q) q
    _ ≤ 1 + 2 ^ b := add_le_add (herr.trans hinv) hq
    _ ≤ 2 ^ (b + 1) := by
      rw [pow_succ]
      have : (1 : ℚ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
      linarith

/-- Capped Gram bases and filtered slots have exactly the analytic block layout once the
specified local fuel suffices. The equality includes the even solver degree. -/
theorem layout_agrees (I : Rounding.RawInput)
    (_hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    numVars I = Rounding.nestedVars I.family.real I.degree ∧
      degree I = Rounding.solverDegree I.family.real I.degree := by
  exact ⟨vars_agree I hfuel, degree_agrees I⟩

/-- One coefficient of the sparse Gram/family expansion agrees with the analytic template.
Only auxiliary monomials are enumerated; solver polynomials use sparse term lists. -/
theorem coefficient_agrees (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) (μ : List ℕ)
    (hμ : μ ∈ SoS.Mono.all I.family.dimension I.degree) :
    decode (numVars I) (Rounding.splitCoeffsRaw I.family.dimension μ (residual I)) =
      Rounding.coefficient I.family.real I.degree I.epsilon
        (SoS.Mono.toFinsupp I.family.dimension μ) := by
  exact concrete_coefficient_agrees I hI hfuel μ hμ

/-- Sparse Gram expansion and capped family substitution reify every coefficient equation.
No dense enumeration of monomials in the solver variables is used. This covers the centered
family slots and specializes to SUB when both family and slot lists are empty. -/
theorem constraints_agree (I : Rounding.RawInput)
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel) :
    (constraints I).map (fun p ↦
      rename Fin.val (SoS.toReal (p.toPoly (numVars I)))) =
        Rounding.nestedSystem I.family.real I.degree I.epsilon I.ball := by
  have hd : I.family.dimension ≤ numVars I := by
    rw [vars_agree I hfuel]
    exact Rounding.RawAux.dimension_le_vars I.family.real I.degree
  have hs : decode (numVars I)
      (normRaw (numVars I) I.family.dimension ++ constant (-1)) =
        (∑ i : Fin I.family.dimension, (X i.val : Rounding.NPoly) ^ 2) - 1 := by
    rw [decode_append, decode_norm _ _ hd, decode_constant]
    simp [sub_eq_add_neg]
  have hc : ((SoS.Mono.allB I.fuel I.family.dimension I.degree).flatMap fun μ ↦
      let c := Rounding.splitCoeffsRaw I.family.dimension μ (residual I)
      [c, scale (-1) c]).map (decode (numVars I)) =
      (Rounding.monos I.family.dimension I.degree).flatMap (fun μ ↦
        [Rounding.coefficient I.family.real I.degree I.epsilon μ,
          -Rounding.coefficient I.family.real I.degree I.epsilon μ]) := by
    rw [bases_uncapped I hfuel _ le_rfl]
    simp only [List.map_flatMap, Rounding.monos, List.flatMap_map]
    apply List.flatMap_congr
    intro μ hμ
    simp only [List.map_cons, List.map_nil, decode_scale, Rat.cast_neg, Rat.cast_one,
      C_neg, C_1, neg_one_mul]
    rw [coefficient_agrees I hI hfuel μ hμ]
    rfl
  change (constraints I).map (decode (numVars I)) = _
  simp only [constraints, List.map_append, List.map_cons, List.map_nil]
  rw [hc, decode_scale, hs, decode_ball, vars_agree I hfuel]
  simp [Rounding.nestedSystem]

/-- The SUB problem has a sparse size bound with a linear degree exponent on dimension.
Coefficient bits, support, and plain constraint count have absolute exponents. -/
theorem plain_size (I : Rounding.RawInput) (support bits : ℕ)
    (hF : I.family.families = []) (hS : I.family.slots = [])
    (hI : I.family.real.Valid I.degree)
    (hfuel : (Rounding.nestedVars I.family.real I.degree + 2) ^
      (2 * I.degree + 2) ≤ I.fuel)
    (hp : ∀ p ∈ I.family.plain, p.length ≤ support ∧
      ∀ t ∈ p, t.1.length ≤ I.family.dimension ∧ t.1.sum ≤ I.degree ∧
        (encRat t.2).length ≤ bits)
    (hε : (encRat I.epsilon).length ≤ bits) (hB : (encRat I.ball).length ≤ bits) :
    (encProblem (numVars I, degree I, constraints I, [], [])).length ≤
      sparseBound I.family.dimension I.degree I.family.plain.length support bits := by
  exact concrete_plain_size I support bits hF hS hI hfuel
    (fun p hp' ↦ ⟨(hp p hp').1, fun t ht ↦
      ⟨((hp p hp').2 t ht).2.1, ((hp p hp').2 t ht).2.2⟩⟩) hε hB

/-- The actual constructor is polynomial in its full encoded input and unary local fuel.
This certificate covers junk inputs as well as valid systems. -/
theorem build_polytime : ComputableInPolyTime build
    (encPair encNestedArgs encUnary) encProblem := by
  exact concrete_build_polytime

/-- Representation follows from the separate layout and coefficient identities. -/
theorem build_represents (q : NestedArgs × ℕ)
    (hI : (nestedInput q).family.real.Valid (nestedInput q).degree)
    (hfuel : (Rounding.nestedVars (nestedInput q).family.real (nestedInput q).degree + 2) ^
      (2 * (nestedInput q).degree + 2) ≤ q.2) :
    Rounding.RawRep (nestedInput q) (code.build q) := by
  obtain ⟨hn, hd⟩ := layout_agrees (nestedInput q) hI hfuel
  refine ⟨hn, hd, ?_⟩
  dsimp only [code, build, Problem.system, Problem.numVars]
  rw [List.map_map]
  exact constraints_agree (nestedInput q) hI hfuel

/-- Translate the raw plain-system certificate to the unchanged public interface. -/
theorem build_sparse_plain (q : NestedArgs × ℕ) (support bits : ℕ)
    (hF : q.1.2.2.2.1 = []) (hS : q.1.2.2.2.2.1 = [])
    (hI : (nestedInput q).family.real.Valid (nestedInput q).degree)
    (hfuel : (Rounding.nestedVars (nestedInput q).family.real (nestedInput q).degree + 2) ^
      (2 * (nestedInput q).degree + 2) ≤ q.2)
    (hp : ∀ p ∈ q.1.2.2.1, p.length ≤ support ∧
      ∀ t ∈ p, t.1.length ≤ q.1.1 ∧ t.1.sum ≤ q.1.2.1 ∧
        (encRat t.2).length ≤ bits)
    (hε : (encRat q.1.2.2.2.2.2.1).length ≤ bits)
    (hB : (encRat q.1.2.2.2.2.2.2).length ≤ bits) :
    (encProblem (code.build q)).length ≤
      sparseBound q.1.1 q.1.2.1 q.1.2.2.1.length support bits := by
  exact plain_size (nestedInput q) support bits hF hS hI hfuel hp hε hB


end ABBKS26.Assembly.Exec.NestedProgram
