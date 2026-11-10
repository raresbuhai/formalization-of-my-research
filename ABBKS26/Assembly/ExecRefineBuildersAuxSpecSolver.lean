module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecFamily

/-! Local layout fuel and objective normalization for the centered nested solver. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecSolver

open Common Rounding MvPolynomial
open Encoding (encRat)
open SoS.Solver (RawPoly Problem encRawPoly encProblem)
open Turing.MultiTapeTM ComputableInPolyTime

def layoutFuel (d : ℕ) : ℕ := (d + 4 * (d + 1) ^ 8 + d ^ 2 + 2) ^ 18

def query (d : ℕ) (p : RawPoly) (εq εh ε Bd : ℚ) : NestedArgs × ℕ :=
  ((d, 8, SpecFamily.plain d p εq, [SpecFamily.hConstraint d p εh], [0], ε, Bd),
    layoutFuel d)

/-- `RawRep` specifies the constraints but leaves the objective unconstrained. -/
def zeroObjective (P : Problem) : Problem := (P.numVars, P.degree, P.2.2.1, [], [])

theorem zeroObjective_polytime : ComputableInPolyTime zeroObjective encProblem encProblem := by
  unfold zeroObjective SoS.Solver.Problem.numVars SoS.Solver.Problem.degree
  fun_prop

theorem layoutFuel_polytime : ComputableInPolyTime layoutFuel encUnary encUnary := by
  exact (unary_pow 18).comp (unary_add' (unary_add' (unary_add' id'
    (unary_mul' (const 4) ((unary_pow 8).comp (unary_add' id' (const 1)))))
    ((unary_pow 2).comp id')) (const 2))

theorem query_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {p : α → RawPoly} {εq εh ε Bd : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hp : ComputableInPolyTime p enc encRawPoly)
    (hq : ComputableInPolyTime εq enc encRat)
    (hh : ComputableInPolyTime εh enc encRat)
    (he : ComputableInPolyTime ε enc encRat)
    (hB : ComputableInPolyTime Bd enc encRat) :
    ComputableInPolyTime (fun a ↦ query (d a) (p a) (εq a) (εh a) (ε a) (Bd a))
      enc (encPair encNestedArgs encUnary) := by
  exact (hd.prod ((const 8).prod ((SpecFamily.plain_polytime_of hd hp hq).prod
    ((cons' (SpecFamily.hConstraint_polytime_of hd hp hh) (const [])).prod
      ((const [0]).prod (he.prod hB)))))).prod (layoutFuel_polytime.comp hd)

theorem build_polytime_of {α : Type} {enc : α ↪ List Bool}
    (N : NestedCode) (hN : NestedSpec N)
    {q : α → NestedArgs × ℕ}
    (hq : ComputableInPolyTime q enc (encPair encNestedArgs encUnary)) :
    ComputableInPolyTime (fun a ↦ zeroObjective (N.build (q a))) enc encProblem :=
  zeroObjective_polytime.comp (hN.polytime.comp hq)

noncomputable section

theorem zeroObjective_rep (I : RawInput) (P : Problem) (hP : RawRep I P) :
    RawRep I (zeroObjective P) := hP

theorem layout_bound (d : ℕ) (p : RawPoly) (εq εh ε Bd : ℚ) :
    (nestedVars (nestedInput (query d p εq εh ε Bd)).family.real 8 + 2) ^ 18 ≤
      layoutFuel d := by
  let A := (SpecFamily.family d p εq εh).real
  have hc : A.plain.length = 2 ∧ A.slots.length = 1 := by
    simp [A, SpecFamily.family, SpecFamily.plain, RawFamily.real]
  have hb := (nested_size A 8 ε Bd).1
  change nestedVars A 8 ≤ d + (A.plain.length + 1 + A.slots.length) * (d + 1) ^ 8 +
    A.slots.length * d ^ 2 at hb
  rw [hc.1, hc.2] at hb
  change (nestedVars A 8 + 2) ^ 18 ≤ _
  exact Nat.pow_le_pow_left (by omega) 18

/-- Arbitrary specified nested builders represent this concrete centered family. -/
theorem build_rep (N : NestedCode) (hN : NestedSpec N)
    (d : ℕ) (p : RawPoly) (εq εh ε Bd : ℚ)
    (hp : ∀ z ∈ p, (SoS.Poly.expo d z.1).sum ≤ 4)
    (hh : (p.toPoly d).IsHomogeneous 4) :
    RawRep (nestedInput (query d p εq εh ε Bd))
      (zeroObjective (N.build (query d p εq εh ε Bd))) := by
  apply zeroObjective_rep
  apply hN.represents
  · exact SpecFamily.family_valid d p εq εh hp hh
  · exact layout_bound d p εq εh ε Bd


theorem solverDegree_le {d : ℕ} (A : FamilySystem d) (hA : A.Valid 8) :
    solverDegree A 8 ≤ 26 := by
  have hb : (A.families.map MvPolynomial.totalDegree).foldl max 0 ≤ 8 := by
    apply SoS.Poly.foldl_max_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    intro n hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    exact hA.2.2 f hf
  unfold solverDegree outerDegree
  omega

/-- The complete local rounder key, including every reified coefficient bit. -/
def roundSize (a : RoundArgs) : ℕ :=
  (encProblem a.1).length + a.2.1 + a.2.2.2.1 +
    (encRat a.2.2.1).length + (encRat a.2.2.2.2).length + 2

/-- Cap the packing factor before converting it to unary. The degree bound is fixed. -/
def roundBudget (c ℓ : ℕ) (q : RoundArgs × ℕ) : ℕ :=
  roundSize q.1 ^ (100 * (c + 1) * (ℓ + 1)) *
    (min q.2 (rankCap q.1.2.2.1 q.1.2.2.2.1) + 2) ^ 100

theorem roundSize_polytime : ComputableInPolyTime roundSize encRoundArgs encUnary := by
  have hp : ComputableInPolyTime (fun a : RoundArgs ↦ a.1) encRoundArgs encProblem := by
    fun_prop
  have hγ : ComputableInPolyTime (fun a : RoundArgs ↦ a.2.2.1) encRoundArgs encRat := by
    fun_prop
  have hM : ComputableInPolyTime (fun a : RoundArgs ↦ a.2.2.2.2) encRoundArgs encRat := by
    fun_prop
  have hplen : ComputableInPolyTime (fun a : RoundArgs ↦ (encProblem a.1).length)
      encRoundArgs encUnary := .of_tidy
    ((ComputableTidilyInPolyTime.encoding_length encProblem).comp hp.tidy)
  have hγlen : ComputableInPolyTime (fun a : RoundArgs ↦ (encRat a.2.2.1).length)
      encRoundArgs encUnary := .of_tidy
    ((ComputableTidilyInPolyTime.encoding_length encRat).comp hγ.tidy)
  have hMlen : ComputableInPolyTime (fun a : RoundArgs ↦ (encRat a.2.2.2.2).length)
      encRoundArgs encUnary := .of_tidy
    ((ComputableTidilyInPolyTime.encoding_length encRat).comp hM.tidy)
  exact unary_add' (unary_add' (unary_add' (unary_add'
    (unary_add' hplen (by fun_prop)) (by fun_prop)) hγlen) hMlen) (const 2)

theorem roundBudget_polytime (c ℓ : ℕ) : ComputableInPolyTime (roundBudget c ℓ)
    (encPair encRoundArgs encUnary) encUnary := by
  have hrr : ComputableInPolyTime
      (fun q : RoundArgs × ℕ ↦ (q.1.2.2.1, q.1.2.2.2.1))
      (encPair encRoundArgs encUnary) (encPair encRat encUnary) := by
    fun_prop
  have hcap := binary_min_unary' (snd encRoundArgs encUnary)
    (RoundProgram.rankCap_polytime.comp hrr)
  exact unary_mul'
    ((unary_pow (100 * (c + 1) * (ℓ + 1))).comp
      (roundSize_polytime.comp (fst _ _)))
    ((unary_pow 100).comp (unary_add' hcap (const 2)))

/-- The capped evaluator pays exactly the specified rounder's sufficient budget whenever
the caller's allowance includes its rank cap. It is independent of solver implementation. -/
theorem roundFuel_le (ℓ : ℕ) (q : RoundArgs × ℕ)
    (hdeg : q.1.1.degree ≤ ℓ) (hcap : rankCap q.1.2.2.1 q.1.2.2.2.1 ≤ q.2) :
    roundFuel (RoundProgram.input q.1) ≤ roundBudget solverConstant ℓ q := by
  change roundSize q.1 ^ (100 * (solverConstant + 1) * (q.1.1.degree + 1)) *
    (rankCap q.1.2.2.1 q.1.2.2.2.1 + 2) ^ 100 ≤ _
  rw [roundBudget, min_eq_right hcap]
  apply Nat.mul_le_mul_right
  apply Nat.pow_le_pow_right
  · dsimp only [roundSize]
    omega
  · exact Nat.mul_le_mul_left _ (by omega)

def round (c ℓ : ℕ) (R : RoundCode) (q : RoundArgs × ℕ) : Points :=
  roundL R (q.1, roundBudget c ℓ q)

theorem round_polytime (c ℓ : ℕ) (R : RoundCode) (hR : RoundSpecL R) :
    ComputableInPolyTime (round c ℓ R) (encPair encRoundArgs encUnary) encPoints :=
  hR.polytime.comp ((fst _ _).prod (roundBudget_polytime c ℓ))


end

end ABBKS26.Assembly.Exec.RefineSynth.SpecSolver
