module

public import ABBKS26.Rounding.RawAuxLayout

/-!
# Rational nested encoding

The orthogonal-complement system of [ABBKS26, Lemma 4.3] as an input of the verified
sum-of-squares solver: the nested sum-of-squares proofs become Gram variables, with rational
coefficients and an explicit bound on their size.
-/

@[expose] public section

namespace ABBKS26.Rounding

noncomputable section


open Matrix

open Common MvPolynomial SoS.Solver Encoding
open Turing.MultiTapeTM (PolyBounded ComputableInPolyTime)
open scoped BigOperators

/-- Extract coefficients in the first d variables and retain the remaining exponent rows. -/
def splitCoeffsRaw (d : ℕ) (μ : List ℕ) (p : RawPoly) : RawPoly :=
  (p.filter (fun t ↦ SoS.Poly.expo d t.1 = μ)).map (fun t ↦ (t.1.drop d, t.2))

structure RawFamily where
  dimension : ℕ
  plain : List RawPoly
  families : List RawPoly
  slots : List ℕ

def sumIndex (d : ℕ) (i : Fin (d + d)) : Fin d ⊕ Fin d :=
  if h : i.val < d then Sum.inl ⟨i.val, h⟩ else Sum.inr ⟨i.val - d, by omega⟩

def RawFamily.real (A : RawFamily) : FamilySystem A.dimension :=
  let Fs := A.families.map fun F ↦
    rename (sumIndex A.dimension) (SoS.toReal (F.toPoly (A.dimension + A.dimension)))
  ⟨A.plain.map (fun p ↦ SoS.toReal (p.toPoly A.dimension)), Fs,
    A.slots.filterMap (fun a ↦ if h : a < Fs.length then some ⟨a, h⟩ else none)⟩

structure RawInput where
  family : RawFamily
  degree : ℕ
  epsilon : ℚ
  ball : ℚ
  fuel : ℕ

def RawRep (I : RawInput) (P : Problem) : Prop :=
  P.numVars = nestedVars I.family.real I.degree ∧
  P.degree = solverDegree I.family.real I.degree ∧
  (P.system.map (fun f ↦ rename Fin.val (SoS.toReal f))) =
    nestedSystem I.family.real I.degree I.epsilon I.ball


end

end ABBKS26.Rounding
