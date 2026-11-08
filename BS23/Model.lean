module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Nat.Log

/-!
# Gaussian mixtures, rounded samples, and randomized algorithms

The definitions that the main theorems of [BS23] are stated in (`BS23/Challenge.lean`). Together
with what they import (Mathlib, and CSLib's multitape Turing machines), they are what a reader has
to check to know what the theorems say.

* **Mixtures** (`BS23.Mixture`): `k` Gaussian components `N(μᵢ, Σ)` in `ℝ^d` with weights `wᵢ`
  and one covariance `Σ` shared by all components (the field `S`). A mixture is valid when the
  weights are nonnegative and sum to `1` and `Σ` is positive definite (`BS23.Mixture.Valid`).
* **Linear algebra**: the squared length `vᵀ Σ⁻¹ v = ‖Σ^{-1/2} v‖²` (`BS23.sqNormIn`), the
  covariance of the mixture (`BS23.Mixture.cov`), and the paper's `σ²` for colinear means
  (`BS23.Mixture.sigmaSq`).
* **Samples** (`BS23.Mixture.sampleLaw`): `n` independent labelled points. Each draws its label `i`
  with probability `wᵢ` and then its point from `N(μᵢ, Σ)` (Mathlib's `multivariateGaussian`). The
  labels give the paper's true clustering `S₁, …, S_k` (`BS23.cluster`).
* **Rounding** (`BS23.IsRounding`, `BS23.roundedSample`): the algorithm does not see the real points
  but rational approximations. A map `r` from labelled points to rational vectors is applied to
  each sample point separately. It may be any function (it need not be measurable) and may use the
  label; it only has to stay within `δ` of the point in the geometry of the components:
  `‖Σ^{-1/2} (r (i, y) - y)‖ ≤ δ`.
* **Outputs**: a list of `n` numbers, one per sample point: its cluster (`BS23.outCluster`). It
  is read as a bipartition (`BS23.IsSeparatingBipartition`) or as a clustering into `k` sets
  (`BS23.ClustersWithin`); both require the list to have exactly `n` entries.
* **Randomized algorithms** (`BS23.RunsInTime`): a deterministic multitape Turing machine that
  reads an input `x` and a string `r` of coin flips and halts within `O(T x + |(x, r)|)` steps.
  Probabilities are over coin strings of exactly `T x` flips (`BS23.coinProb`), as elsewhere in
  this repository.
* **Success** (`BS23.successProb`): the probability, over the sample and the coins, that the output
  on the rounded sample is good for the labels. Since the rounding need not be measurable, it is a
  lower integral (see `BS23.successProb`).

Reference: [BS23] R.-D. Buhai, D. Steurer, *Beyond parallel pancakes: quasi-polynomial time
guarantees for non-spherical Gaussian mixtures*, COLT 2023, arXiv:2112.05445.
-/

@[expose] public section

namespace BS23

open Encoding MeasureTheory ProbabilityTheory Matrix

/-! ### Mixtures -/

/-- A **mixture of `k` Gaussians in `ℝ^d` with a common covariance**: the weight `w i` and the
mean `μ i` of each component, and the covariance `S` (the paper's `Σ`) shared by all
components. -/
structure Mixture (k d : ℕ) where
  /-- The weight of each component. -/
  w : Fin k → ℝ
  /-- The mean of each component. -/
  μ : Fin k → Fin d → ℝ
  /-- The covariance matrix of every component. -/
  S : Matrix (Fin d) (Fin d) ℝ

variable {k d : ℕ}

/-- A **valid** mixture: the weights are nonnegative and sum to `1`, and the covariance is
positive definite. (The theorems also ask every weight to be at least a given positive number, so
the weights are positive.) -/
structure Mixture.Valid (M : Mixture k d) : Prop where
  nonneg_w : ∀ i, 0 ≤ M.w i
  sum_w : ∑ i, M.w i = 1
  posDef : M.S.PosDef

/-- The squared length `vᵀ S⁻¹ v = ‖S^{-1/2} v‖²` of a vector `v` in the geometry of a positive
definite matrix `S`. -/
noncomputable def sqNormIn (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  v ⬝ᵥ (S⁻¹ *ᵥ v)

/-- The mean `μ̄ = ∑ᵢ wᵢ μᵢ` of the mixture. -/
noncomputable def Mixture.mean (M : Mixture k d) : Fin d → ℝ :=
  ∑ i, M.w i • M.μ i

/-- The covariance `Σ + ∑ᵢ wᵢ (μᵢ - μ̄)(μᵢ - μ̄)ᵀ` of the mixture (the paper's `cov(y⁰)`), where
`μ̄` is its mean. -/
noncomputable def Mixture.cov (M : Mixture k d) : Matrix (Fin d) (Fin d) ℝ :=
  M.S + ∑ i, M.w i • vecMulVec (M.μ i - M.mean) (M.μ i - M.mean)

/-- The paper's `σ² = (uᵀ cov⁻¹ u) / (uᵀ Σ⁻¹ u)` for colinear means [BS23, Section 6], where `u`
spans the direction of the line through the means. It does not depend on the length of `u`. -/
noncomputable def Mixture.sigmaSq (M : Mixture k d) (u : Fin d → ℝ) : ℝ :=
  sqNormIn M.cov u / sqNormIn M.S u

/-! ### Samples -/

/-- The law of one **labelled sample point**: the label `i` with probability `wᵢ`, then the point
drawn from `N(μᵢ, Σ)`. -/
noncomputable def Mixture.law (M : Mixture k d) : Measure (Fin k × EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ENNReal.ofReal (M.w i) •
    (multivariateGaussian (WithLp.toLp 2 (M.μ i)) M.S).map (fun y ↦ (i, y))

/-- The law of a **sample**: `n` independent labelled points. -/
noncomputable def Mixture.sampleLaw (M : Mixture k d) (n : ℕ) :
    Measure (Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :=
  Measure.pi fun _ ↦ M.law

/-- The samples with label `i`: the paper's `Sᵢ`. -/
def cluster {n : ℕ} (ℓ : Fin n → Fin k) (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (ℓ · = i)

/-! ### Rounding -/

/-- A **rounding**: a map from labelled points to rational vectors. It is applied to each sample
point separately (`BS23.roundedSample`). -/
abbrev Rounding (k d : ℕ) := Fin k × EuclideanSpace ℝ (Fin d) → Fin d → ℚ

/-- `r` **rounds within `δ`** in the geometry of the components: `‖S^{-1/2} (r (i, y) - y)‖ ≤ δ`
for every label `i` and point `y`. -/
def IsRounding (S : Matrix (Fin d) (Fin d) ℝ) (δ : ℝ) (r : Rounding k d) : Prop :=
  ∀ i y, sqNormIn S (fun j ↦ (r (i, y) j : ℝ) - y j) ≤ δ ^ 2

/-- A sample as the algorithm reads it: one list of `d` rational coordinates per point. -/
abbrev Points := List (List ℚ)

/-- Points are encoded as lists of lists of rationals. -/
def encPoints : Points ↪ List Bool := encList (encList encRat)

/-- The **rounded sample**: the points of `ω`, rounded by `r` one by one, in the order of the
sample. -/
def roundedSample {n : ℕ} (r : Rounding k d) (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) :
    Points :=
  List.ofFn fun j ↦ List.ofFn (r (ω j))

/-- The dimension of the points: the length of the first one. -/
def dim (pts : Points) : ℕ := (pts.headD []).length

/-! ### Inputs and outputs -/

/-- The input of the algorithm of [BS23, Theorem 1.1]: the failure probability `δ`, a lower bound
`wmin` on the weights, and the rounded sample. -/
structure BipartitionInput where
  /-- The failure probability. -/
  δ : ℚ
  /-- A lower bound on the weights. -/
  wmin : ℚ
  /-- The rounded sample. -/
  points : Points

/-- Encoded as the failure probability, the bound, and the points. -/
def encBipartitionInput : BipartitionInput ↪ List Bool :=
  ⟨fun x ↦ encPair encRat (encPair encRat encPoints) (x.δ, x.wmin, x.points), by
    rintro ⟨δ, w, p⟩ ⟨δ', w', p'⟩ h
    have h' := (encPair encRat (encPair encRat encPoints)).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- The input of the algorithm of [BS23, Theorem 1.2]: the number `k` of components, a lower bound
`wmin` on the weights, and the rounded sample. -/
structure ColinearInput where
  /-- The number of components. -/
  k : ℕ
  /-- A lower bound on the weights. -/
  wmin : ℚ
  /-- The rounded sample. -/
  points : Points

/-- Encoded as `k` in binary, the bound, and the points. -/
def encColinearInput : ColinearInput ↪ List Bool :=
  ⟨fun x ↦ encPair encNat (encPair encRat encPoints) (x.k, x.wmin, x.points), by
    rintro ⟨k, w, p⟩ ⟨k', w', p'⟩ h
    have h' := (encPair encNat (encPair encRat encPoints)).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- The input of the algorithm of [BS23, Theorem 1.3]: the number `k` of components, a lower bound
`wmin` on the weights, a bound `R` on the radius of the means, and the rounded sample. -/
structure RadiusInput where
  /-- The number of components. -/
  k : ℕ
  /-- A lower bound on the weights. -/
  wmin : ℚ
  /-- A bound on `‖Σ^{-1/2} μᵢ‖`. -/
  R : ℚ
  /-- The rounded sample. -/
  points : Points

/-- Encoded as `k` in binary, the two bounds, and the points. -/
def encRadiusInput : RadiusInput ↪ List Bool :=
  ⟨fun x ↦ encPair encNat (encPair encRat (encPair encRat encPoints)) (x.k, x.wmin, x.R, x.points),
    by
    rintro ⟨k, w, R, p⟩ ⟨k', w', R', p'⟩ h
    have h' := (encPair encNat (encPair encRat (encPair encRat encPoints))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- An output: a list of numbers, one per sample point, its cluster. (`BS23.ClustersWithin` and
`BS23.IsSeparatingBipartition` require exactly one entry per sample point.) -/
abbrev Output := List ℕ

/-- Outputs are encoded as lists of numbers in binary. -/
def encOutput : Output ↪ List Bool := encList encNat

/-- The cluster that the output puts sample point `j` in: the `j`-th number of the list, `0` if
the list is shorter. -/
def outCluster (out : Output) (j : ℕ) : ℕ := out.getD j 0

/-- `C` contains at least a `0.99` fraction of the sample points of some component:
`maxᵢ |C ∩ Sᵢ| / |Sᵢ| ≥ 0.99`, over the components `i` that have sample points. -/
def ContainsMostOfSome {n : ℕ} (ℓ : Fin n → Fin k) (C : Finset (Fin n)) : Prop :=
  ∃ i, (cluster ℓ i).Nonempty ∧ (0.99 : ℝ) * (cluster ℓ i).card ≤ (C ∩ cluster ℓ i).card

/-- The output is a **separating bipartition** for the labels `ℓ` [BS23, Theorem 1.1]: it is a
list of `n` numbers, one per sample point; the points it puts in cluster `0` form one side `C₁`,
all others the other side `C₂`, and each side contains at least a `0.99` fraction of the points of
some component. (The two components differ, since the sides are disjoint.) -/
def IsSeparatingBipartition {n : ℕ} (ℓ : Fin n → Fin k) (out : Output) : Prop :=
  out.length = n ∧
  ContainsMostOfSome ℓ (Finset.univ.filter fun j ↦ outCluster out j = 0) ∧
    ContainsMostOfSome ℓ (Finset.univ.filter fun j ↦ outCluster out j ≠ 0)

/-- The output **clusters the sample with error at most `ε`** for the labels `ℓ` [BS23, Theorems
1.2 and 1.3]: it is a list of `n` numbers, one per sample point; it puts every sample point in a
cluster `i < k`, so the sets `Cᵢ` of points it puts in cluster `i` partition the sample into `k`
sets, and for some permutation `π` of the components, `1 - (1/n) ∑ᵢ |Cᵢ ∩ S_{π(i)}| ≤ ε`. -/
def ClustersWithin {n : ℕ} (ε : ℝ) (ℓ : Fin n → Fin k) (out : Output) : Prop :=
  out.length = n ∧ (∀ j : Fin n, outCluster out j < k) ∧ ∃ π : Equiv.Perm (Fin k),
    1 - (∑ i : Fin k,
      (((Finset.univ.filter fun j : Fin n ↦ outCluster out j = i) ∩ cluster ℓ (π i)).card : ℝ)) / n
      ≤ ε

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an input `x` and a coin string `r`, halts with output `A (x, r)`
within `c (T x + |(x, r)| + 1)` steps and cells, for a constant `c`. The machine reads its whole
input, so the bound includes the length of the input with the coins; `BS23.successProb` gives it
exactly `T x` coins.

Since the machine may read all its coins, the length of its coin string tells it `T x`; the
theorems take `T` explicit and computable from `x`, so this is no advice. -/
def RunsInTime {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (A : α × List Bool → β) (T : α → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encIn encBits) encOut
    (fun xr ↦ c * (T xr.1 + (encPair encIn encBits xr).length + 1))
    (fun xr ↦ c * (T xr.1 + (encPair encIn encBits xr).length + 1))

open Classical in
/-- The probability that a uniformly random string of `m` coin flips satisfies `P`. -/
noncomputable def coinProb (m : ℕ) (P : List Bool → Prop) : ℝ :=
  (Fintype.card {r : Fin m → Bool // P (List.ofFn r)} : ℝ) / 2 ^ m

/-- `⌈log₂ ⌈1/q⌉⌉`, which is `log₂ (1/q)` up to rounding, for a weight bound `0 < q ≤ 1`. -/
def logInv (q : ℚ) : ℕ := Nat.clog 2 ⌈q⁻¹⌉₊

/-- The running time `(|x| + 2)^C (d + 2)^(C ⌈1/δ⌉^C (L + 1))` of the algorithm of [BS23, Theorem
1.1] on an input `x` with failure probability `δ`, points in `ℝ^d` and weight bound `wmin`, where
`|x|` is the length of the encoded input and `L = logInv wmin ≈ log₂ (1/wmin)`:
`poly(|x|) · d^O(δ^(-O(1)) log (1/wmin))`. (For `δ ≤ 0`, `⌈1/δ⌉ = 0` and the second factor is
`1`.) -/
def bipartitionTime (C : ℕ) (x : BipartitionInput) : ℕ :=
  ((encBipartitionInput x).length + 2) ^ C *
    (dim x.points + 2) ^ (C * ⌈1 / x.δ⌉₊ ^ C * (logInv x.wmin + 1))

/-- The running time `(|x| + 2)^(C (L + 1))` of the algorithm of [BS23, Theorem 1.2], with
`L = logInv wmin ≈ log₂ (1/wmin)`: `|x|^O(log (1/wmin))`. -/
def colinearTime (C : ℕ) (x : ColinearInput) : ℕ :=
  ((encColinearInput x).length + 2) ^ (C * (logInv x.wmin + 1))

/-- The running time `(|x| + 2)^(C (⌈R²⌉ + L + 1))` of the algorithm of [BS23, Theorem 1.3], with
`L = logInv wmin ≈ log₂ (1/wmin)`: `|x|^O(R² + log (1/wmin))`. -/
def radiusTime (C : ℕ) (x : RadiusInput) : ℕ :=
  ((encRadiusInput x).length + 2) ^ (C * (⌈x.R ^ 2⌉₊ + logInv x.wmin + 1))

/-! ### Success -/

/-- The **success probability** of the algorithm `A`, running in time `T`, when the sample is
rounded by `r`: over a sample of `n` labelled points from `M` and the coin flips, the probability
that `A`'s output on the input `input (roundedSample r ω)` satisfies `Good` for the labels of the
sample. The algorithm sees neither the labels, nor the real points, nor `M`.

It is `∫ ω, P_coins[Good] dω`. Since `r` need not be measurable, the integrand need not be either,
so this is Mathlib's `lintegral`, which for any function is the lower integral: the supremum of the
integrals of the measurable simple functions below it. So a lower bound on `successProb` is a
lower bound on the integral of a measurable function below the success probability; a
non-measurable `r` can only make it smaller. (For a valid mixture the sample law is a probability
measure, so the value is at most `1` and `toReal` loses nothing.) -/
noncomputable def successProb {α β : Type} (M : Mixture k d) (n : ℕ) (r : Rounding k d)
    (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (coinProb (T (input (roundedSample r ω)))
      fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c))) ∂(M.sampleLaw n)).toReal

end BS23
