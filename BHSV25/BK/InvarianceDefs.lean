module

public import OAI.Computability.MaxCut.Estimates.Degree
public import Background.Gaussian
public import Background.GaussianCalculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# The invariance principle: definitions

Definitions for the invariance principle used in the proof of It Ain't Over Till It's Over
(`BHSV25/BK/README.md`, Section 7), copied from `BGHKLMM26/RobustMIS/Defs.lean` (papers do not
import each other), with the namespace changed to `BHSV25.BK.Aint` and only the parts used here
kept.

* The standard normal density `npdf` and Gaussian space `Gs n` with its standard Gaussian `gm n`
  (used to mollify test functions).
* **Multilinear polynomials** on `ℝ^R`: `mlEval c x = ∑_S c_S ∏_{i∈S} xᵢ` (subsets `S` are points
  `s : Cube (Fin R)`, as in OpenAI's Walsh analysis), the noise operator `smoothC r c`
  (`c_S ↦ r^|S| c_S`), influences `inflC`, the truncation `truncC d c` to degree `≤ d`, and the
  sign vector `bitVec x` of a cube point.
* **Test functions** of two variables: `LipPair Ψ K` (`K`-Lipschitz for the `ℓ¹` distance on
  `ℝ²`) and `LineC3 Φ B` (`C³` along lines, third derivative `≤ B ‖direction‖₁³`).
-/

@[expose] public section

namespace BHSV25.BK.Aint

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

/-- The standard normal density `φ(y) = e^{-y²/2}/√(2π)`. -/
noncomputable abbrev npdf (y : ℝ) : ℝ := gaussianPDFReal 0 1 y

/-- Gaussian space `ℝⁿ`. -/
abbrev Gs (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard Gaussian measure `γₙ`. -/
noncomputable abbrev gm (n : ℕ) : Measure (Gs n) := stdGaussian (Gs n)

variable {R : ℕ}

/-- The size `|S|` of a subset `S`, given as a point of the cube (OpenAI's `degree`). -/
abbrev sdeg (s : Cube (Fin R)) : ℕ := OAI.OptimalMaxCut.Analytic.degree s

/-- The sign vector `(σ(xᵢ))ᵢ ∈ {±1}^R` of a cube point (`σ = bitSign`, `σ(false) = 1`). -/
def bitVec (x : Cube (Fin R)) : Fin R → ℝ := fun i ↦ bitSign (x i)

/-- The multilinear polynomial with coefficients `c`, `x ↦ ∑_S c_S ∏_{i ∈ S} xᵢ` (a subset `S` is a
point `s : Cube (Fin R)`, `i ∈ S ↔ s i`). -/
noncomputable def mlEval (c : Cube (Fin R) → ℝ) (x : Fin R → ℝ) : ℝ :=
  ∑ s, c s * ∏ i, if s i then x i else 1

/-- The noise operator on coefficients: `c_S ↦ r^|S| c_S`. -/
noncomputable def smoothC (r : ℝ) (c : Cube (Fin R) → ℝ) : Cube (Fin R) → ℝ :=
  fun s ↦ r ^ sdeg s * c s

/-- The influence `∑_{S ∋ i} c_S²` of a coefficient vector. -/
noncomputable def inflC (c : Cube (Fin R) → ℝ) (i : Fin R) : ℝ :=
  ∑ s ∈ univ.filter (fun s : Cube (Fin R) ↦ s i = true), c s ^ 2

/-- The truncation `c^{≤d}` to degree `≤ d`. -/
noncomputable def truncC (d : ℕ) (c : Cube (Fin R) → ℝ) : Cube (Fin R) → ℝ :=
  fun s ↦ if sdeg s ≤ d then c s else 0

/-- `Ψ : ℝ × ℝ → ℝ` (curried) is `K`-Lipschitz for the `ℓ¹` distance. -/
def LipPair (Ψ : ℝ → ℝ → ℝ) (K : ℝ) : Prop :=
  ∀ a b a' b' : ℝ, |Ψ a b - Ψ a' b'| ≤ K * (|a - a'| + |b - b'|)

/-- `Φ` is `C³` along every line `x ↦ (a + x a', b + x b')`, with third derivative at most
`B (|a'| + |b'|)³`. -/
def LineC3 (Φ : ℝ → ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ a b a' b' : ℝ, ContDiff ℝ 3 (fun x : ℝ ↦ Φ (a + x * a') (b + x * b')) ∧
    ∀ x : ℝ, |iteratedDeriv 3 (fun x : ℝ ↦ Φ (a + x * a') (b + x * b')) x| ≤
      B * (|a'| + |b'|) ^ 3

end BHSV25.BK.Aint
