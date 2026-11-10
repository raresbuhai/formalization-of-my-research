module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecSolver

/-! Local fuel and sparse size certificates for the plain SUB nested problem. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdSolver

open Common Rounding
open SoS.Solver (RawPoly encRawPoly encProblem)
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- This bound depends only on the local dimension, degree, and constraint count. -/
def layoutFuel (d K : ℕ) (A : List RawPoly) : ℕ :=
  (d + (A.length + 1) * (d + 1) ^ K + 2) ^ (2 * K + 2)

/-- The original sample allowance is a unary cap, separate from every rational coefficient. -/
def query (d K : ℕ) (A : List RawPoly) (ε Bd : ℚ) (fuel : ℕ) : NestedArgs × ℕ :=
  ((d, K, A, [], [], ε, Bd), min fuel (layoutFuel d K A))

private theorem add_polytime_of {α : Type} {enc : α ↪ List Bool} {m n : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun a ↦ m a + n a) enc encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hm.tidy hn.tidy)

theorem layoutFuel_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d K : α → ℕ} {A : α → List RawPoly}
    (hd : ComputableInPolyTime d enc encUnary)
    (hK : ComputableInPolyTime K enc encUnary)
    (hA : ComputableInPolyTime A enc (encList encRawPoly)) :
    ComputableInPolyTime (fun a ↦ layoutFuel (d a) (K a) (A a)) enc encNat := by
  have hdb := unary_to_binary.comp hd
  have hm := unary_to_binary.comp (unary_add' ((length_list encRawPoly).comp hA) (const 1))
  have hp := binary_pow' (add_polytime_of hdb (const 1)) hK
  exact binary_pow' (add_polytime_of
    (add_polytime_of hdb (binary_mul' hm hp)) (const 2))
    (unary_add' (unary_mul' (const 2) hK) (const 2))

theorem query_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d K fuel : α → ℕ} {A : α → List RawPoly} {ε Bd : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hK : ComputableInPolyTime K enc encUnary)
    (hA : ComputableInPolyTime A enc (encList encRawPoly))
    (hε : ComputableInPolyTime ε enc encRat)
    (hBd : ComputableInPolyTime Bd enc encRat)
    (hf : ComputableInPolyTime fuel enc encUnary) :
    ComputableInPolyTime (fun a ↦ query (d a) (K a) (A a) (ε a) (Bd a) (fuel a))
      enc (encPair encNestedArgs encUnary) :=
  (hd.prod (hK.prod (hA.prod ((const []).prod ((const []).prod (hε.prod hBd)))))).prod
    (binary_min_unary' hf (layoutFuel_polytime_of hd hK hA))


noncomputable section

/-- The decoded input has no family slots and exactly the supplied plain system. -/
theorem family_real (d K : ℕ) (A : List RawPoly) (ε Bd : ℚ) (fuel : ℕ) :
    (nestedInput (query d K A ε Bd fuel)).family.real =
      plainSystem (A.map fun p ↦ SoS.toReal (p.toPoly d)) := by
  simp [query, nestedInput, RawFamily.real, plainSystem]

theorem layout_bound (d K : ℕ) (A : List RawPoly) (ε Bd : ℚ) (fuel : ℕ) :
    (nestedVars (nestedInput (query d K A ε Bd fuel)).family.real K + 2) ^ (2 * K + 2) ≤
      layoutFuel d K A := by
  let F := (nestedInput (query d K A ε Bd fuel)).family.real
  have hb := (nested_size F K ε Bd).1
  have hplain : F.plain.length = A.length := by
    simp [F, query, nestedInput, RawFamily.real]
  have hslots : F.slots.length = 0 := by
    simp [F, query, nestedInput, RawFamily.real]
  rw [hplain, hslots] at hb
  simp only [Nat.add_zero, Nat.zero_mul] at hb
  change nestedVars F K ≤ d + (A.length + 1) * (d + 1) ^ K at hb
  exact Nat.pow_le_pow_left (Nat.add_le_add_right hb 2) _

/-- Representation holds once the locally computed cap fits the external unary allowance. -/
theorem represents (N : NestedCode) (hN : NestedSpec N)
    (d K : ℕ) (A : List RawPoly) (ε Bd : ℚ) (fuel : ℕ)
    (hA : (plainSystem (A.map fun p ↦ SoS.toReal (p.toPoly d))).Valid K)
    (hf : layoutFuel d K A ≤ fuel) :
    RawRep (nestedInput (query d K A ε Bd fuel))
      (SpecSolver.zeroObjective (N.build (query d K A ε Bd fuel))) := by
  apply SpecSolver.zeroObjective_rep
  apply hN.represents
  · change (nestedInput (query d K A ε Bd fuel)).family.real.Valid K
    rwa [family_real]
  · change _ ≤ min fuel (layoutFuel d K A)
    rw [min_eq_right hf]
    exact layout_bound d K A ε Bd fuel

/-- The high-degree problem's encoded size is independent of the external sample allowance. -/
theorem sparse_bound (N : NestedCode) (hN : NestedSpec N)
    (d K : ℕ) (A : List RawPoly) (ε Bd : ℚ) (fuel support bits : ℕ)
    (hA : (plainSystem (A.map fun p ↦ SoS.toReal (p.toPoly d))).Valid K)
    (hf : layoutFuel d K A ≤ fuel)
    (hs : ∀ p ∈ A, p.length ≤ support ∧ ∀ t ∈ p,
      t.1.length ≤ d ∧ t.1.sum ≤ K ∧ (encRat t.2).length ≤ bits)
    (hε : (encRat ε).length ≤ bits) (hBd : (encRat Bd).length ≤ bits) :
    (encProblem (N.build (query d K A ε Bd fuel))).length ≤
      sparseBound d K A.length support bits := by
  apply hN.sparse_plain (query d K A ε Bd fuel) support bits rfl rfl
  · change (nestedInput (query d K A ε Bd fuel)).family.real.Valid K
    rwa [family_real]
  · change _ ≤ min fuel (layoutFuel d K A)
    rw [min_eq_right hf]
    exact layout_bound d K A ε Bd fuel
  · exact hs
  · exact hε
  · exact hBd

end

end ABBKS26.Assembly.Exec.RefineSynth.IdSolver
