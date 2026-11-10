module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Computability.Partrec
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Nat.Log

/-!
# Gaussian mixtures, corrupted and rounded samples, and randomized algorithms

The definitions that the main theorems of [ABBKS26] are stated in (`ABBKS26/Challenge.lean`).
Together with what they import (Mathlib, and CSLib's multitape Turing machines), they are what a
reader has to check to know what the theorems say.

* **Mixtures** (`ABBKS26.Mixture`): `k` Gaussian components `N(μᵢ, Σᵢ)` in `ℝ^d` with weights
  `wᵢ`. A mixture is valid when the weights are nonnegative and sum to `1` and every `Σᵢ` is
  positive definite
  (`ABBKS26.Mixture.Valid`). The two theorems are about the two special cases of the paper:
  centered components, `μᵢ = 0` (`ABBKS26.Mixture.IsCentered`), and components with one
  covariance, `Σᵢ = Σⱼ` (`ABBKS26.Mixture.HasIdenticalCovariances`).
* **Separation**: the paper's `Δ`-separation of two centered components [ABBKS26, Definition 5.1]
  (`ABBKS26.CenteredSeparated`) and of two components with the same covariance [ABBKS26,
  Definition 6.1] (`ABBKS26.MeanSeparated`).
* **Samples with corruptions** (`ABBKS26.IsCorruption`): the paper's samples come from a
  distribution `M'` within total variation distance `ε` of the mixture `M`. Here a sample point is
  a triple `(i, y, z)`: a label `i` and a point `y` drawn from `M`, and the point `z` that is
  observed, which differs from `y` with probability at most `ε`. The labels give the paper's true
  clustering `S₁, …, S_k` (`ABBKS26.cluster`).
* **Rounding** (`ABBKS26.IsRounding`, `ABBKS26.roundedSample`): the algorithm reads rational
  approximations of the observed points, within `δ` in the geometry of the point's component:
  `‖Σᵢ^{-1/2} (r (i, z) - z)‖ ≤ δ`. The map `r` is applied to each sample point separately, may use
  the label, and need not be measurable.
* **Outputs**: a list of numbers, one per sample point, its cluster (`ABBKS26.outCluster`), read
  as a partition into `k` sets (`ABBKS26.RecoversClusters`).
* **Randomized algorithms** (`ABBKS26.RunsInTime`): a deterministic multitape Turing machine that
  reads an input `x` and a string `r` of coin flips and halts within `O(T x + |(x, r)|)` steps.
  Probabilities are over coin strings of exactly `T x` flips (`ABBKS26.coinProb`), as elsewhere in
  this repository.
* **Success** (`ABBKS26.successProb`): the probability, over the sample and the coins, that the
  output on the rounded sample is good for the labels of the sample. Since the rounding need not be
  measurable, it is a lower integral (see `ABBKS26.successProb`).

Reference: [ABBKS26] P. Anderson, M. Bafna, R.-D. Buhai, P. K. Kothari, D. Steurer, *Dimension
reduction via sum-of-squares and improved clustering algorithms for non-spherical mixtures*,
COLT 2026, arXiv:2411.12438.
-/

@[expose] public section

namespace ABBKS26

open Encoding MeasureTheory ProbabilityTheory Matrix

/-! ### Mixtures -/

/-- A **mixture of `k` Gaussians in `ℝ^d`**: the weight `w i`, the mean `μ i` and the covariance
`S i` (the paper's `Σᵢ`) of each component. -/
structure Mixture (k d : ℕ) where
  /-- The weight of each component. -/
  w : Fin k → ℝ
  /-- The mean of each component. -/
  μ : Fin k → Fin d → ℝ
  /-- The covariance matrix of each component. -/
  S : Fin k → Matrix (Fin d) (Fin d) ℝ

variable {k d : ℕ}

/-- A **valid** mixture: the weights are nonnegative and sum to `1`, and every covariance is
positive definite. (The theorems also ask every weight to be at least a given positive number, so
the weights are positive.) -/
structure Mixture.Valid (M : Mixture k d) : Prop where
  nonneg_w : ∀ i, 0 ≤ M.w i
  sum_w : ∑ i, M.w i = 1
  posDef : ∀ i, (M.S i).PosDef

/-- A **centered** mixture: every component has mean `0`. -/
def Mixture.IsCentered (M : Mixture k d) : Prop :=
  ∀ i, M.μ i = 0

/-- A mixture with **identical covariances**: all components have the same covariance. -/
def Mixture.HasIdenticalCovariances (M : Mixture k d) : Prop :=
  ∀ i j, M.S i = M.S j

/-- The squared length `vᵀ S⁻¹ v = ‖S^{-1/2} v‖²` of a vector `v` in the geometry of a positive
definite matrix `S`. -/
noncomputable def sqNormIn (S : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) : ℝ :=
  v ⬝ᵥ (S⁻¹ *ᵥ v)

/-! ### Separation -/

/-- **Spectral separation** [ABBKS26, Definition 5.1]: in some direction `v`, the variance under
`S₁` is more than `Δ²` times the variance under `S₂`: `vᵀ S₁ v > Δ² vᵀ S₂ v`. -/
def SpectrallySeparated (Δ : ℝ) (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ v : Fin d → ℝ, Δ ^ 2 * (v ⬝ᵥ (S₂ *ᵥ v)) < v ⬝ᵥ (S₁ *ᵥ v)

/-- **Relative Frobenius separation** [ABBKS26, Definition 5.1]:
`‖S₁^{-1/2} S₂ S₁^{-1/2} - I‖_F² > Δ² ‖S₁^{-1/2} S₂ S₁^{-1/2}‖²`, where the norm on the right is the
spectral norm. It is written without square roots of matrices, for positive definite `S₁` and
`S₂`:

* the left side is `tr ((S₁⁻¹ S₂ - I)²)`: with `B = S₁^{-1/2} S₂ S₁^{-1/2}`, the matrix `B - I` is
  symmetric, so `‖B - I‖_F² = tr ((B - I)²)`, and `B - I = S₁^{1/2} (S₁⁻¹ S₂ - I) S₁^{-1/2}`, so
  `(B - I)²` and `(S₁⁻¹ S₂ - I)²` are similar and have the same trace;
* the spectral norm of the positive definite `B` is its largest eigenvalue, the least `t` with
  `vᵀ S₂ v ≤ t vᵀ S₁ v` for all `v`; so the inequality holds exactly when it holds for some such
  `t` in place of the norm. -/
def FrobeniusSeparated (Δ : ℝ) (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ t : ℝ, (∀ v : Fin d → ℝ, v ⬝ᵥ (S₂ *ᵥ v) ≤ t * (v ⬝ᵥ (S₁ *ᵥ v))) ∧
    Δ ^ 2 * t ^ 2 < ((S₁⁻¹ * S₂ - 1) * (S₁⁻¹ * S₂ - 1)).trace

/-- Two centered Gaussians with covariances `S₁` and `S₂` are **`Δ`-separated** [ABBKS26,
Definition 5.1]: they are spectrally separated or relatively Frobenius separated, in one order or
the other. -/
def CenteredSeparated (Δ : ℝ) (S₁ S₂ : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  SpectrallySeparated Δ S₁ S₂ ∨ SpectrallySeparated Δ S₂ S₁ ∨
    FrobeniusSeparated Δ S₁ S₂ ∨ FrobeniusSeparated Δ S₂ S₁

/-- Two Gaussians with means `μ₁`, `μ₂` and the same covariance `S` are **`Δ`-separated**
[ABBKS26, Definition 6.1]: in some direction `v`, `⟨μ₁ - μ₂, v⟩² > 2 Δ² vᵀ S v`. (For positive
definite `S` this says `(μ₁ - μ₂)ᵀ S⁻¹ (μ₁ - μ₂) > 2 Δ²`.) -/
def MeanSeparated (Δ : ℝ) (μ₁ μ₂ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∃ v : Fin d → ℝ, 2 * Δ ^ 2 * (v ⬝ᵥ (S *ᵥ v)) < ((μ₁ - μ₂) ⬝ᵥ v) ^ 2

/-! ### Samples with corruptions -/

/-- The law of one **labelled point** of the mixture: the label `i` with probability `wᵢ`, then
the point drawn from `N(μᵢ, Σᵢ)`. -/
noncomputable def Mixture.law (M : Mixture k d) : Measure (Fin k × EuclideanSpace ℝ (Fin d)) :=
  ∑ i, ENNReal.ofReal (M.w i) •
    (multivariateGaussian (WithLp.toLp 2 (M.μ i)) (M.S i)).map (fun y ↦ (i, y))

/-- An **`ε`-corruption** of the mixture `M`: the law `P` of a triple `(i, y, z)` of a label, a
point and the point that is observed, such that

* the labelled point `(i, y)` has the law of `M` (`ABBKS26.Mixture.law`), and
* the observed point differs from it with probability at most `ε`.

The law of the observed point is then a distribution `M'` within total variation distance `ε` of
the mixture, as in [ABBKS26, Theorems 5.2 and 6.2]; conversely, every such `M'` is the law of the
observed point of some `ε`-corruption (a coupling of `M` and `M'` that attains their total
variation distance). The labels are the components that the points come from before corruption.

(The map `(i, y, z) ↦ (i, y)` is measurable, so its pushforward is the usual one, and the first
condition makes `P` a probability measure when `M` is valid: the weights are then nonnegative, so
`M.law` has mass `∑ᵢ wᵢ = 1`.) -/
structure IsCorruption (M : Mixture k d) (ε : ℝ)
    (P : Measure (Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) : Prop where
  map_clean : P.map (fun p ↦ (p.1, p.2.1)) = M.law
  corrupted_le : P {p | p.2.1 ≠ p.2.2} ≤ ENNReal.ofReal ε

/-- The samples with label `i`: the paper's `Sᵢ`. -/
def cluster {n : ℕ} (ℓ : Fin n → Fin k) (i : Fin k) : Finset (Fin n) :=
  Finset.univ.filter (ℓ · = i)

/-! ### Rounding -/

/-- A **rounding**: a map from labelled points to rational vectors. It is applied to each observed
sample point separately (`ABBKS26.roundedSample`). -/
abbrev Rounding (k d : ℕ) := Fin k × EuclideanSpace ℝ (Fin d) → Fin d → ℚ

/-- `r` **rounds within `δ`** in the geometry of each component: a point `z` with label `i` is
moved by at most `δ` in the geometry of `Σᵢ`, `‖Σᵢ^{-1/2} (r (i, z) - z)‖ ≤ δ`. -/
def IsRounding (M : Mixture k d) (δ : ℝ) (r : Rounding k d) : Prop :=
  ∀ i y, sqNormIn (M.S i) (fun j ↦ (r (i, y) j : ℝ) - y j) ≤ δ ^ 2

/-- A sample as the algorithm reads it: one list of `d` rational coordinates per point. -/
abbrev Points := List (List ℚ)

/-- Points are encoded as lists of lists of rationals. -/
def encPoints : Points ↪ List Bool := encList (encList encRat)

/-- The **rounded sample**: the observed points of `ω`, rounded by `r` one by one (each with its
label), in the order of the sample. -/
def roundedSample {n : ℕ} (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) : Points :=
  List.ofFn fun j ↦ List.ofFn (r ((ω j).1, (ω j).2.2))

/-- The dimension of the points: the length of the first one. -/
def dim (pts : Points) : ℕ := (pts.headD []).length

/-! ### Inputs and outputs -/

/-- The input of the algorithms of [ABBKS26, Theorems 5.2 and 6.2]: the number `k` of components,
a lower bound `wmin` on the weights, the separation parameter `Δ`, the allowed failure probability
`δ`, and the rounded sample. -/
structure Input where
  /-- The number of components. -/
  k : ℕ
  /-- A lower bound on the weights. -/
  wmin : ℚ
  /-- The separation parameter. -/
  Δ : ℚ
  /-- The allowed failure probability. -/
  δ : ℚ
  /-- The rounded sample. -/
  points : Points

/-- Encoded as `k` in binary, the three numbers, and the points. -/
def encInput : Input ↪ List Bool :=
  ⟨fun x ↦ encPair encNat (encPair encRat (encPair encRat (encPair encRat encPoints)))
      (x.k, x.wmin, x.Δ, x.δ, x.points),
    by
    rintro ⟨k, w, D, e, p⟩ ⟨k', w', D', e', p'⟩ h
    have h' := (encPair encNat
      (encPair encRat (encPair encRat (encPair encRat encPoints)))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- An output: one number per sample point, its cluster. -/
abbrev Output := List ℕ

/-- Outputs are encoded as lists of numbers in binary. -/
def encOutput : Output ↪ List Bool := encList encNat

/-- The cluster that the output puts sample point `j` in: the `j`-th number of the list.
(`ABBKS26.RecoversClusters` asks for one number per sample point; past the end of the list the
value is `0`, which is never used then.) -/
def outCluster (out : Output) (j : ℕ) : ℕ := out.getD j 0

/-- The output **recovers every component up to a fraction `η`** for the labels `ℓ` of `n` sample
points [ABBKS26, Theorems 5.2 and 6.2]: it is a list of `n` numbers, one per sample point, each a
cluster `i < k`, so the sets `Ŝᵢ` of points it puts in cluster `i` partition the sample into `k`
sets; and for some permutation `π` of the components, each `Ŝᵢ` contains all but an `η` fraction
of the points of its component: `|Ŝᵢ ∩ S_{π(i)}| ≥ (1 - η) |S_{π(i)}|`, the paper's
`minᵢ |Ŝᵢ ∩ S_{π(i)}| / |S_{π(i)}| ≥ 1 - η` (also when `S_{π(i)}` is empty). -/
def RecoversClusters {n : ℕ} (η : ℝ) (ℓ : Fin n → Fin k) (out : Output) : Prop :=
  out.length = n ∧ (∀ j : Fin n, outCluster out j < k) ∧ ∃ π : Equiv.Perm (Fin k), ∀ i : Fin k,
    (1 - η) * (cluster ℓ (π i)).card ≤
      (((Finset.univ.filter fun j : Fin n ↦ outCluster out j = i) ∩ cluster ℓ (π i)).card : ℝ)

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an input `x` and a coin string `r`, halts with output `A (x, r)`
within `c (T x + |(x, r)| + 1)` steps and cells, for a constant `c`. The machine reads its whole
input, so the bound includes the length of the input with the coins; `ABBKS26.successProb` gives
it exactly `T x` coins.

Since the machine may read all its coins, the length of its coin string tells it `T x`; the
theorems take `T` computable from `x`, so this is no advice. -/
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

/-- The running time `g(⌈1/wmin⌉, ⌈Δ⌉) (|x| + 2)^C` of the algorithm of [ABBKS26, Theorem 5.2] on
an input `x` with weight bound `wmin` and separation parameter `Δ`, where `|x|` is the length of
the encoded input: a function of `wmin` and `Δ` times a polynomial of fixed degree in `|x|`. (It
has no separate term for the failure probability `δ`: the theorems take at least `1/δ` sample
points, so `|x| ≥ 1/δ`.) -/
def centeredTime (g : ℕ → ℕ → ℕ) (C : ℕ) (x : Input) : ℕ :=
  g ⌈1 / x.wmin⌉₊ ⌈x.Δ⌉₊ * ((encInput x).length + 2) ^ C

/-- The running time `g(⌈1/wmin⌉, ⌈Δ⌉) (|x| + 2)^C (d + 2)^(C (L² + 1))` of the algorithm of
[ABBKS26, Theorem 6.2] on an input `x` with points in `ℝ^d`, weight bound `wmin` and separation
parameter `Δ`, where `|x|` is the length of the encoded input and
`L = logInv wmin ≈ log₂ (1/wmin)`: `g(1/wmin, Δ) · poly(|x|) · d^O(log² (1/wmin))`. -/
def identicalCovTime (g : ℕ → ℕ → ℕ) (C : ℕ) (x : Input) : ℕ :=
  g ⌈1 / x.wmin⌉₊ ⌈x.Δ⌉₊ * ((encInput x).length + 2) ^ C *
    (dim x.points + 2) ^ (C * (logInv x.wmin ^ 2 + 1))

/-! ### Success -/

/-- The **success probability** of the algorithm `A`, running in time `T`, when the sample is
rounded by `r`: over a sample of `n` independent triples `(i, y, z)` from the law `P` (an
`ε`-corruption of the mixture) and the coin flips, the probability that `A`'s output on the input
`input (roundedSample r ω)` satisfies `Good` for the labels of the sample. The algorithm sees
neither the labels, nor the real points, nor the mixture.

It is `∫ ω, P_coins[Good] dω`. Since `r` need not be measurable, the integrand need not be either,
so this is Mathlib's `lintegral`, which for any function is the lower integral: the supremum of the
integrals of the measurable simple functions below it. So a lower bound on `successProb` is a
lower bound on the integral of a measurable function below the success probability; a
non-measurable `r` can only make it smaller. (For an `ε`-corruption of a valid mixture, `P` is a
probability measure, so the value is at most `1` and `toReal` loses nothing.) -/
noncomputable def successProb {α β : Type}
    (P : Measure (Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) (n : ℕ)
    (r : Rounding k d) (input : Points → α) (A : α × List Bool → β) (T : α → ℕ)
    (Good : (Fin n → Fin k) → β → Prop) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (coinProb (T (input (roundedSample r ω)))
      fun c ↦ Good (fun j ↦ (ω j).1) (A (input (roundedSample r ω), c)))
    ∂(Measure.pi fun _ : Fin n ↦ P)).toReal

end ABBKS26
