module

public import ABBKS26.Robust.RBAuxFrameLoop

/-!
# Robust black boxes

The contracts of the robust subroutines the paper cites: robust isotropic position
([ABBKS26, Fact 3.21]), certified moments ([ABBKS26, Fact 5.14 and Theorem 6.11]) and robust
learning of one Gaussian ([ABBKS26, Fact 3.18]), in the minimal form the proof needs.
-/

@[expose] public section

namespace ABBKS26.Robust

noncomputable section


open Matrix

open Common Matrix MvPolynomial
open scoped MatrixOrder
open scoped BigOperators
variable {n k d : ℕ}

structure FrameResult (d : ℕ) where
  passed : Bool
  transform : Matrix (Fin d) (Fin d) ℚ
  center : Fin d → ℚ
  covariance : Matrix (Fin d) (Fin d) ℚ
  certificates : List (Unif.Quad d)
  eligible : List Bool

structure Estimate (d : ℕ) where
  mean : Fin d → ℚ
  cov : Matrix (Fin d) (Fin d) ℚ

def Accurate (M : Mixture k d) (j : Fin k) (E : Estimate d) : Prop :=
  let S := E.cov.map (algebraMap ℚ ℝ)
  S.PosDef ∧ LE ((0.9 : ℝ) • M.S j) S ∧ LE S ((1.1 : ℝ) • M.S j) ∧
    frobSq ((CFC.sqrt (M.S j))⁻¹ * S * (CFC.sqrt (M.S j))⁻¹ - 1) ≤ 1 / 100 ∧
    sqNormIn (M.S j) (fun i ↦ (E.mean i : ℝ) - M.μ j i) ≤ 1 / 10000000

def CloseFrame (D : Reference n k d) (F : FrameResult d) (π R ζ : ℝ) : Prop :=
  F.passed = true ∧
    frobSq (F.transform.map (algebraMap ℚ ℝ) * D.cov *
      (F.transform.map (algebraMap ℚ ℝ))ᵀ - 1) ≤
        (65 * Real.sqrt (sigmaSq π R) * Real.sqrt D.contamination + ζ) ^ 2

def statCenter (F : FrameModel k d) (j : Fin k) (q : Unif.Quad d) : ℝ :=
  (q.A * F.cov j).trace + qform q.A (F.mean j) + q.b ⬝ᵥ F.mean j + q.c

def statVariance (F : FrameModel k d) (j : Fin k) (q : Unif.Quad d) : ℝ :=
  2 * (q.A * F.cov j * q.A * F.cov j).trace +
    qform (F.cov j) (2 • (q.A *ᵥ F.mean j) + q.b)

def Far (D : Reference n k d) (F : FrameResult d) (R sb : ℝ) : Prop :=
  ∃ a : Fin F.certificates.length, F.eligible[a.val]? = some true ∧
    ∃ i j : Fin k, R ≤ |statCenter D.model i F.certificates[a] -
      statCenter D.model j F.certificates[a]| ∧
      ∀ l, statVariance D.model l F.certificates[a] ≤ sb ^ 2

abbrev FrameProc := (d : ℕ) → Points → Mode → ℚ → ℚ → ℚ → ℕ → FrameResult d

def Represents (D : Reference n k d) (pts : Points) : Prop :=
  pts.length = D.block.card ∧ ∃ indices : Fin pts.length → Fin n,
    Function.Injective indices ∧ Set.range indices = {l | l ∈ D.block} ∧
      ∀ l, pts[l].length = d ∧ ∀ j : Fin d,
        (pts[l].getD j.val 0 : ℝ) = D.observed (indices l) j

def FrameContract (run : FrameProc) : Prop :=
  (∀ d pts mode π R ζ fuel, (run d pts mode π R ζ fuel).certificates.length ≤
    pts.length * d ^ 2) ∧
  ∀ {n k d} (D : Reference n k d) pts mode (π R ζ : ℚ) fuel,
    Represents D pts → D.Valid π → D.Resilient 4 (min (1 / 10 ^ 8) (ζ ^ 2 / 10 ^ 8)) →
    0 < π → π ≤ 1 / 2 → 0 ≤ R → 0 < ζ →
    (mode = .centered → ∀ j, D.model.mean j = 0) →
    D.contamination ≤ min (maxContamination π R) (π / 400) →
    2 / maxContamination π R ≤ pts.length →
    (pts.length + d + 2) ^ 100 ≤ fuel →
    let F := run d pts mode π R ζ fuel
    (Far D F R (20 / π) ∨ CloseFrame D F π R ζ) ∧
      (mode = .centered → F.center = 0) ∧
      (∀ j : Fin F.certificates.length,
        F.eligible[j.val]? = some true →
        ∀ l, statVariance D.model l F.certificates[j] ≤ (20 / π) ^ 2)


end

end ABBKS26.Robust
