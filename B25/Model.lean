module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.Variance

/-!
# Restricted eigenvalues, partially-rotated designs, and the Lasso

The definitions that the main results of [B25] are stated in (`B25/Challenge.lean`). Together with
Mathlib, they are what a reader has to check to know what the theorems say.

* **Vectors** are functions `Fin n → ℝ`, with the Euclidean norm `‖x‖₂ = √(x ⬝ᵥ x)`
  (`B25.l2`) and the `ℓ₁`-norm `‖x‖₁ = ∑ᵢ |xᵢ|` (`B25.l1`), written out because Mathlib's `‖x‖`
  on `Fin n → ℝ` is the sup norm. A design is a real `n × d` matrix `X`; `X *ᵥ β` is `Xβ`.
* **Correlations** (`B25.corr`): `⟨u/‖u‖₂, v/‖v‖₂⟩`, which is `0` when `u = 0` or `v = 0`, the
  convention of [B25, Definition 1.9].
* **The restricted eigenvalue constant** [B25, Definition 1.1] (`B25.reConst`):
  `γ_S(X) = min_{β ∈ C(S)} (1/n) ‖Xβ‖₂² / ‖β_S‖₂²` over the cone
  `C(S) = {β : ‖β_{Sᶜ}‖₁ ≤ ‖β_S‖₁}` (`B25.cone`), with `β_S ≠ 0`. `X_S` is the `n × |S|` matrix of
  the columns in `S` (`B25.cols`).
* **Partially-rotated designs** [B25, Definition 1.2] (`B25.PartiallyRotated`): a random design is
  a map `X : Ω → Matrix (Fin n) (Fin d) ℝ` on a probability space. It is `(ε, δ)`-partially
  rotated with respect to `S` when every fixed combination of the columns in `S` and every fixed
  combination of the columns outside `S` have correlation at most `ε` in absolute value, except
  with probability at most `e^(-δn)`.
* **Rotated designs** [B25, Lemmas 1.3 and 1.4] (`B25.rotateCols`): `[X_S, R X_{Sᶜ}]`, the design
  that keeps the columns of `X` in `S` and multiplies the others by `R`; and the uniform
  distribution on the unit sphere of `ℝⁿ` (`B25.uniformSphere`), Mathlib's surface measure
  `Measure.toSphere`, normalized.
* **The Lasso** [B25, Equation (1.2)] (`B25.IsLasso`): in its constrained form, `β̂` minimizes
  `‖y - Xβ̂‖₂²` subject to `‖β̂‖₁ ≤ r`. The noise of sparse linear regression is `N(0, σ² Iₙ)`
  (`B25.noiseLaw`); `supp β` is the support of `β` (`B25.supp`).

Reference: [B25] R.-D. Buhai, *Lasso and partially-rotated designs*, arXiv:2505.11093.
-/

@[expose] public section

namespace B25

open MeasureTheory ProbabilityTheory Matrix

/-! ### Norms and correlations -/

/-- The Euclidean norm `‖x‖₂ = √(∑ᵢ xᵢ²)`. -/
noncomputable def l2 {n : ℕ} (x : Fin n → ℝ) : ℝ := √(x ⬝ᵥ x)

/-- The `ℓ₁`-norm `‖x‖₁ = ∑ᵢ |xᵢ|`. -/
def l1 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, |x i|

/-- The correlation `⟨u/‖u‖₂, v/‖v‖₂⟩` of two vectors, regarded as `0` when `u = 0` or `v = 0`
[B25, Definition 1.9]. -/
noncomputable def corr {n : ℕ} (u v : Fin n → ℝ) : ℝ := (u ⬝ᵥ v) / (l2 u * l2 v)

/-- The support `supp β = {j : βⱼ ≠ 0}` of a vector. -/
noncomputable def supp {d : ℕ} (β : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun j ↦ β j ≠ 0

/-! ### The restricted eigenvalue constant -/

/-- The cone `C(S) = {β : ‖β_{Sᶜ}‖₁ ≤ ‖β_S‖₁}` [B25, Definition 1.1]. -/
def cone {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) : Set (ι → ℝ) :=
  {β | ∑ j ∈ Sᶜ, |β j| ≤ ∑ j ∈ S, |β j|}

/-- The **restricted eigenvalue constant** `γ_S(X) = min_{β ∈ C(S)} (1/n) ‖Xβ‖₂² / ‖β_S‖₂²` of an
`n × ι` matrix with respect to `S` [B25, Definition 1.1], over the `β ∈ C(S)` with `β_S ≠ 0` (the
others are `β = 0`). The ratio is invariant under scaling `β`, so the infimum is a minimum over a
compact set. For `S = ∅` there is no such `β`, and the infimum is `0`. -/
noncomputable def reConst {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix (Fin n) ι ℝ) (S : Finset ι) : ℝ :=
  ⨅ β : {β : ι → ℝ // β ∈ cone S ∧ ∃ j ∈ S, β j ≠ 0},
    ((X *ᵥ β.1) ⬝ᵥ (X *ᵥ β.1) / n) / ∑ j ∈ S, β.1 j ^ 2

/-- `X_S`: the `n × |S|` matrix of the columns of `X` indexed by `S`. A set `S' ⊆ S` is a set of
its columns as `S'.subtype (· ∈ S)`. -/
def cols {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) : Matrix (Fin n) S ℝ :=
  X.submatrix id Subtype.val

/-- The columns of `X` have norm `√n`, the normalization of [B25]. -/
def HasNormalizedColumns {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) : Prop :=
  ∀ j, ∑ i, X i j ^ 2 = n

/-! ### Partially-rotated designs -/

/-- A random design `X` is **`(ε, δ)`-partially rotated** with respect to `S` [B25, Definition 1.2]
if for all `α ∈ ℝ^|S|` and `β ∈ ℝ^|Sᶜ|`,
`P(|⟨X_S α / ‖X_S α‖₂, X_{Sᶜ} β / ‖X_{Sᶜ} β‖₂⟩| > ε) ≤ e^(-δn)`. Here `α` and `β` are vectors of
`ℝ^d` supported on `S` and on `Sᶜ`, so that `X_S α = Xα` and `X_{Sᶜ} β = Xβ`. -/
def PartiallyRotated {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) (ε δ : ℝ) : Prop :=
  ∀ α β : Fin d → ℝ, (∀ j ∉ S, α j = 0) → (∀ j ∈ S, β j = 0) →
    P {ω | ε < |corr (X ω *ᵥ α) (X ω *ᵥ β)|} ≤ ENNReal.ofReal (Real.exp (-(δ * n)))

/-- The design `[X_S, R X_{Sᶜ}]` [B25, Lemmas 1.3 and 1.4]: column `j` is column `j` of `X` if
`j ∈ S`, and column `j` of `R X` otherwise. -/
def rotateCols {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (R : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of fun i j ↦ if j ∈ S then X i j else (R * X) i j

/-- The **uniform distribution on the unit sphere** of `ℝⁿ`: Mathlib's surface measure
`Measure.toSphere` of the Lebesgue measure of `EuclideanSpace ℝ (Fin n)`, normalized to a
probability measure and seen as a measure on `Fin n → ℝ`. -/
noncomputable def uniformSphere (n : ℕ) : Measure (Fin n → ℝ) :=
  (((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere).map
      fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ↦ x.1.ofLp

/-! ### Sparse linear regression and the Lasso -/

/-- The noise `w ~ N(0, σ² Iₙ)` of sparse linear regression `y = Xβ + w` [B25, Equation (1.1)]. -/
noncomputable def noiseLaw (n : ℕ) (σ : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ ↦ gaussianReal 0 (σ ^ 2).toNNReal

/-- `b` is a **Lasso estimate** with radius `r` [B25, Equation (1.2)]: it minimizes
`‖y - Xb‖₂²` over the `b` with `‖b‖₁ ≤ r`. The paper takes `r = ‖β‖₁`. -/
def IsLasso {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (r : ℝ) (b : Fin d → ℝ) :
    Prop :=
  l1 b ≤ r ∧
    ∀ b' : Fin d → ℝ, l1 b' ≤ r → (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b) ≤ (y - X *ᵥ b') ⬝ᵥ (y - X *ᵥ b')

end B25
