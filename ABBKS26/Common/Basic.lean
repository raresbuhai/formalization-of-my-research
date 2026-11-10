module

public import ABBKS26.Model
public import Background.SumOfSquares.NormedLinear
public import Background.SumOfSquares.Algorithm.RawPoly
public import Background.SumOfSquares.Algorithm.Monomials
public import Background.PolyTime.Rat
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Shared definitions

Vectors, matrices and polynomials over `ℝ` and `ℚ`, quadratic forms and projections, the
frame model of a mixture after a linear change of coordinates, the two kinds of mixtures
(`Mode`), and dyadic rounding of rationals.
-/

@[expose] public section

namespace ABBKS26.Common

noncomputable section


open MvPolynomial Matrix
open scoped BigOperators

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev RPoly (d : ℕ) := MvPolynomial (Fin d) ℝ
abbrev QPoly (d : ℕ) := MvPolynomial (Fin d) ℚ
abbrev BiPoly (d : ℕ) := MvPolynomial (Fin d ⊕ Fin d) ℝ

def nsq {d : ℕ} : RPoly d := ∑ i, X i ^ 2

def lin {d : ℕ} (a : Vec d) : RPoly d := ∑ i, C (a i) * X i

def quad {d : ℕ} (A : Mat d) : RPoly d :=
  ∑ i, ∑ j, C (A i j) * X i * X j

def sqnorm {d : ℕ} (v : Vec d) : ℝ := v ⬝ᵥ v

def qform {d : ℕ} (A : Mat d) (v : Vec d) : ℝ := v ⬝ᵥ (A *ᵥ v)

def frobSq {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, A i j ^ 2

def LE {d : ℕ} (A B : Mat d) : Prop := ∀ v, qform A v ≤ qform B v

def Projection {d : ℕ} (P : Mat d) : Prop := Pᵀ = P ∧ P * P = P

def InRange {d : ℕ} (P : Mat d) (v : Vec d) : Prop := P *ᵥ v = v

noncomputable def subst {d : ℕ} (P : Mat d) (f : RPoly d) : RPoly d :=
  aeval (fun i ↦ lin (P i)) f

noncomputable def liftV {d : ℕ} (f : RPoly d) : BiPoly d := rename Sum.inr f
noncomputable def liftU {d : ℕ} (f : RPoly d) : BiPoly d := rename Sum.inl f

noncomputable def inst {d : ℕ} (F : BiPoly d) (P : Mat d) : RPoly d :=
  aeval (Sum.elim (fun i ↦ lin (P i)) X) F

noncomputable def substV {d : ℕ} (P : Mat d) (F : BiPoly d) : BiPoly d :=
  aeval (Sum.elim (fun i ↦ X (Sum.inl i)) (fun i ↦ liftV (lin (P i)))) F

def ball {d : ℕ} : List (RPoly d) := [1 - nsq]

structure FrameModel (k d : ℕ) where
  weight : Fin k → ℝ
  mean : Fin k → Vec d
  cov : Fin k → Mat d

def FrameModel.Valid {k d : ℕ} (F : FrameModel k d) (w : ℝ) : Prop :=
  0 < w ∧ (∀ i, w ≤ F.weight i) ∧ ∑ i, F.weight i = 1 ∧
    (∀ i, (F.cov i).PosDef)

def FrameModel.second {k d : ℕ} (F : FrameModel k d) : Mat d :=
  ∑ i, F.weight i • (F.cov i + vecMulVec (F.mean i) (F.mean i))

def FrameModel.Isotropic {k d : ℕ} (F : FrameModel k d) (γ : ℝ) : Prop :=
  0 ≤ γ ∧ LE ((1 - γ) • (1 : Mat d)) F.second ∧
    LE F.second ((1 + γ) • (1 : Mat d))

inductive Mode where
  | centered
  | identical
  deriving DecidableEq

def Mode.Condition {k d : ℕ} (m : Mode) (M : Mixture k d) : Prop :=
  match m with
  | .centered => M.IsCentered
  | .identical => M.HasIdenticalCovariances

def Mode.Separated {k d : ℕ} (m : Mode) (M : Mixture k d) (Δ : ℝ) : Prop :=
  match m with
  | .centered => ∀ a b, a ≠ b → CenteredSeparated Δ (M.S a) (M.S b)
  | .identical => ∀ a b, a ≠ b → MeanSeparated Δ (M.μ a) (M.μ b) (M.S a)


noncomputable def projector {d : ℕ} (Y : List (Fin d → ℚ)) : Mat d :=
  let B : Matrix (Fin d) (Fin Y.length) ℝ := fun i j ↦ (Y[j] i : ℝ)
  B * (Bᵀ * B)⁻¹ * Bᵀ

def Covers {d : ℕ} (P : Mat d) (T : Set (Vec d)) (γ : ℝ) : Prop :=
  ∀ v ∈ T, ∃ u, sqnorm u = 1 ∧ InRange P u ∧ sqnorm (v - u) ≤ γ ^ 2

def dyadicDown (q : ℚ) : ℚ :=
  if 0 < q then (2 : ℚ) ^ (Nat.clog 2 ⌈1 / q⌉₊ + 1) |>.inv else 0

def dyadicUp (q : ℚ) : ℚ := (2 : ℚ) ^ Nat.clog 2 (max 1 ⌈q⌉₊)

def sqrtUp (q : ℚ) : ℚ := (Nat.sqrt ⌈max 0 q⌉₊ + 1 : ℕ)

def roundRat (p : ℕ) (q : ℚ) : ℚ := (⌊(2 : ℚ) ^ p * q⌋ : ℤ) / (2 : ℚ) ^ p

noncomputable def roundPoly {d : ℕ} (p : ℕ) (f : QPoly d) : QPoly d :=
  f.support.sum fun a ↦ monomial a (roundRat p (f.coeff a))

end

end ABBKS26.Common
