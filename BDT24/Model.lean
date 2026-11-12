module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Sparse linear regression, negative sparse PCA, quantized samples, and randomized algorithms

The definitions that the main theorem of [BDT24] is stated in (`BDT24/Challenge.lean`). Together
with what they import (Mathlib, and CSLib's multitape Turing machines), they are what a reader has
to check to know what the theorem says.

* **Quantization**: both algorithms read each real number `t` of their sample to a given number
  `p` of bits after the binary point, as the integer `⌊2^p t⌋` (`BDT24.quantize`), and are given
  `p`.
* **Sparse linear regression** (`BDT24.slrLaw`, [BDT24, Model 1.1]): a sample point is a pair
  `(a, y)` with `a ~ N(0, Σ)` in `ℝ^D` and `y = ⟨a, x*⟩ + w` for an independent noise
  `w ~ N(0, 1)`. The instances are those with `I/(k+2) ⪯ Σ ⪯ I` and a `k`-sparse `x*` with
  `‖x*‖² ≤ k` (`BDT24.IsBoundedInstance`).
* **Prediction error** (`BDT24.PredictsWell`): `(1/n) ‖X (x̂ - x*)‖² ≤ 0.01` for the real design
  `X`, as in the paper.
* **Negative sparse PCA** ([BDT24, Model 1.3]): the null law is `N(0, I_{d+1})`; the planted law
  draws a spike `x` with `x₁ = -1/√(k+1)` and the other coordinates a uniformly random vector with
  exactly `k` entries `±1/√(k+1)` (`BDT24.spikeSigns`, `BDT24.spikeVector`), and then the points
  from `N(0, I_{d+1} - θ x xᵀ)` (`BDT24.spikedCov`).
* **Randomized algorithms** (`BDT24.RunsInTime`): a deterministic multitape Turing machine that
  reads an input `x` and a string `r` of coin flips and halts within `O(T x + |(x, r)|)` steps.
  Probabilities are over coin strings of exactly `T x` flips (`BDT24.coinProb`), as elsewhere in
  this repository.
* **Success** (`BDT24.slrSuccessProb`, `BDT24.spcaOutputProb`): the probability, over `n`
  independent sample points and the coins, that the output on the quantized sample is good.
* **Low-degree polynomials** ([BDT24, Appendix B]): the degree-`D` advantage of one law over
  another (`BDT24.AdvantageAtMost`), for the planted and null laws of `n` points of negative
  sparse PCA (`BDT24.plantedSample`, `BDT24.nullSample`) and polynomials in their coordinates
  (`BDT24.sampleCoords`).
* **Statistical dimension** ([BDT24, Appendix C]): the relative densities of the planted laws of
  one point (`BDT24.relDensity`), their correlations (`BDT24.pairCorr`), and the statistical
  dimension with average correlation (`BDT24.SDAAtLeast`).

Reference: [BDT24] R.-D. Buhai, J. Ding, S. Tiegel, *Computational-statistical gaps for improper
learning in sparse linear regression*, COLT 2024, arXiv:2402.14103.
-/

@[expose] public section

namespace BDT24

open Encoding MeasureTheory ProbabilityTheory Matrix

variable {D m : ℕ}

/-! ### Quantization -/

/-- A real number `t` to `p` bits after the binary point: the integer `⌊2^p t⌋`, which stands for
the dyadic rational `2^(-p) ⌊2^p t⌋`. -/
noncomputable def quantize (p : ℕ) (t : ℝ) : ℤ := ⌊(2 : ℝ) ^ p * t⌋

/-! ### Sparse linear regression -/

/-- `x` is **`k`-sparse**: it has at most `k` nonzero entries. -/
def IsSparse (k : ℕ) (x : Fin D → ℝ) : Prop :=
  (Finset.univ.filter fun i ↦ x i ≠ 0).card ≤ k

/-- The instances of sparse linear regression that the theorem asks about: the design covariance
satisfies `I/(k+2) ⪯ Σ ⪯ I` (in particular it is positive definite), and the secret `x*` is
`k`-sparse with `‖x*‖² ≤ k`. -/
def IsBoundedInstance (k : ℕ) (S : Matrix (Fin D) (Fin D) ℝ) (xs : Fin D → ℝ) : Prop :=
  (S - ((k : ℝ) + 2)⁻¹ • (1 : Matrix (Fin D) (Fin D) ℝ)).PosSemidef ∧ (1 - S).PosSemidef ∧
    IsSparse k xs ∧ ∑ i, xs i ^ 2 ≤ k

/-- The response `⟨a, x*⟩ + w` of a design point `a` with noise `w`. -/
noncomputable def response (xs : Fin D → ℝ) (p : EuclideanSpace ℝ (Fin D) × ℝ) :
    EuclideanSpace ℝ (Fin D) × ℝ :=
  (p.1, ∑ i, p.1 i * xs i + p.2)

/-- The response map is measurable (it is continuous), so `BDT24.slrLaw` is a genuine
pushforward. -/
theorem measurable_response (xs : Fin D → ℝ) : Measurable (response xs) := by
  unfold response
  fun_prop

/-- The law of one sample point of **sparse linear regression with Gaussian design** [BDT24,
Model 1.1] with noise variance `1`: the pair `(a, ⟨a, x*⟩ + w)` for independent `a ~ N(0, S)` and
`w ~ N(0, 1)`. -/
noncomputable def slrLaw (S : Matrix (Fin D) (Fin D) ℝ) (xs : Fin D → ℝ) :
    Measure (EuclideanSpace ℝ (Fin D) × ℝ) :=
  ((multivariateGaussian 0 S).prod (gaussianReal 0 1)).map (response xs)

/-- The input of a regression algorithm: the sparsity `k`, the precision `p`, and the sample to
`p` bits: the design (one list per sample point) and the responses, each number `t` as `⌊2^p t⌋`. -/
structure SLRInput where
  /-- The sparsity. -/
  k : ℕ
  /-- The number of bits after the binary point. -/
  p : ℕ
  /-- The rows of the design matrix, each entry `t` as `⌊2^p t⌋`. -/
  design : List (List ℤ)
  /-- The responses, each `t` as `⌊2^p t⌋`. -/
  response : List ℤ

/-- Encoded as `k` in binary, `p` in unary, the rows, and the responses. The precision is in unary
so that the input is at least as long as one number written to `p` bits. -/
def encSLRInput : SLRInput ↪ List Bool :=
  ⟨fun x ↦ encPair encNat (encPair encUnary (encPair (encList (encList encInt)) (encList encInt)))
      (x.k, x.p, x.design, x.response), by
    rintro ⟨k, p, A, y⟩ ⟨k', p', A', y'⟩ h
    have h' := (encPair encNat
      (encPair encUnary (encPair (encList (encList encInt)) (encList encInt)))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- The input that a sample of `n` points gives a regression algorithm: the sparsity `k`, the
precision `p`, and the points to `p` bits, in the order of the sample. -/
noncomputable def slrInput {n : ℕ} (k p : ℕ) (ω : Fin n → EuclideanSpace ℝ (Fin D) × ℝ) :
    SLRInput :=
  ⟨k, p, List.ofFn fun j ↦ List.ofFn fun i ↦ quantize p ((ω j).1 i),
    List.ofFn fun j ↦ quantize p (ω j).2⟩

/-- An estimate: a list of rational coordinates. -/
abbrev Estimate := List ℚ

/-- Estimates are encoded as lists of rationals. -/
def encEstimate : Estimate ↪ List Bool := encList encRat

/-- The estimate `x̂` **achieves prediction error `0.01`** on the sample `ω` for the secret `x*`
[BDT24, Model 1.1]: `(1/n) ‖X x̂ - X x*‖² ≤ 0.01`, where `X` is the real design of the sample.
It is written `‖X x̂ - X x*‖² ≤ n/100`, which for `n = 0` always holds. Coordinate `i` of `x̂` is
the `i`-th entry of the list, `0` past its end; further entries are ignored. -/
def PredictsWell {n : ℕ} (ω : Fin n → EuclideanSpace ℝ (Fin D) × ℝ) (xs : Fin D → ℝ)
    (est : Estimate) : Prop :=
  ∑ j : Fin n, (∑ i : Fin D, (ω j).1 i * ((est.getD i 0 : ℝ) - xs i)) ^ 2 ≤ n / 100

/-! ### Negative sparse PCA -/

/-- The sign patterns of the spike: vectors in `{-1, 0, 1}^d` with exactly `k` nonzero entries. -/
def spikeSigns (d k : ℕ) : Finset (Fin d → SignType) :=
  Finset.univ.filter fun v ↦ (Finset.univ.filter fun i ↦ v i ≠ 0).card = k

/-- The **spike** of [BDT24, Model 1.3] with sign pattern `v`: the unit vector `x ∈ ℝ^{d+1}` with
first coordinate `x₁ = -1/√(k+1)` and `x_{i+1} = vᵢ/√(k+1)`. -/
noncomputable def spikeVector {d : ℕ} (k : ℕ) (v : Fin d → SignType) : Fin (d + 1) → ℝ :=
  Fin.cons (-1 / √((k : ℝ) + 1)) fun i ↦ (v i : ℝ) / √((k : ℝ) + 1)

/-- The planted covariance `I - θ x xᵀ` of [BDT24, Model 1.3]. -/
noncomputable def spikedCov (θ : ℝ) (x : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - θ • vecMulVec x x

/-- The spike strength `θ = (k+1)/(k+2)` of [BDT24, Theorem 3.1]. -/
noncomputable def theta (k : ℕ) : ℝ := ((k : ℝ) + 1) / ((k : ℝ) + 2)

/-- The input of a PCA algorithm: the failure probability `δ` and the precision `p` of the
regression algorithm, the sparsity `k`, the precision `q`, and the points to `q` bits, each
coordinate `z` as `⌊2^q z⌋`. -/
structure SPCAInput where
  /-- The failure probability of the regression algorithm. -/
  δ : ℚ
  /-- The precision of the regression algorithm's input. -/
  p : ℕ
  /-- The sparsity. -/
  k : ℕ
  /-- The number of bits after the binary point. -/
  q : ℕ
  /-- The points, each coordinate `z` as `⌊2^q z⌋`. -/
  points : List (List ℤ)

/-- Encoded as `δ`, `p` in unary, `k` in binary, `q` in unary, and the points. -/
def encSPCAInput : SPCAInput ↪ List Bool :=
  ⟨fun x ↦ encPair encRat (encPair encUnary (encPair encNat (encPair encUnary
      (encList (encList encInt))))) (x.δ, x.p, x.k, x.q, x.points), by
    rintro ⟨δ, p, k, q, z⟩ ⟨δ', p', k', q', z'⟩ h
    have h' := (encPair encRat (encPair encUnary (encPair encNat (encPair encUnary
      (encList (encList encInt)))))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- The input that a sample of `n` points gives a PCA algorithm: `δ`, `p`, the sparsity `k`, the
precision `q`, and the points to `q` bits, in the order of the sample. -/
noncomputable def spcaInput {n : ℕ} (δ : ℚ) (p k q : ℕ)
    (ω : Fin n → EuclideanSpace ℝ (Fin m)) : SPCAInput :=
  ⟨δ, p, k, q, List.ofFn fun j ↦ List.ofFn fun i ↦ quantize q (ω j i)⟩

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an input `x` and a coin string `r`, halts with output `A (x, r)`
within `c (T x + |(x, r)| + 1)` steps and cells, for a constant `c`. The machine reads its whole
input, so the bound includes the length of the input with the coins; the success probabilities
give it exactly `T x` coins.

Since the machine may read all its coins, the length of its coin string tells it `T x`; the
theorem takes `T` explicit and computable from `x`, so this is no advice. -/
def RunsInTime {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (A : α × List Bool → β) (T : α → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encIn encBits) encOut
    (fun xr ↦ c * (T xr.1 + (encPair encIn encBits xr).length + 1))
    (fun xr ↦ c * (T xr.1 + (encPair encIn encBits xr).length + 1))

open Classical in
/-- The probability that a uniformly random string of `m` coin flips satisfies `P`. -/
noncomputable def coinProb (m : ℕ) (P : List Bool → Prop) : ℝ :=
  (Fintype.card {r : Fin m → Bool // P (List.ofFn r)} : ℝ) / 2 ^ m

/-- The running time `(|x| + 2)^e` of a regression algorithm, where `|x|` is the length of the
encoded input. -/
def slrTime (e : ℕ) (x : SLRInput) : ℕ := ((encSLRInput x).length + 2) ^ e

/-- The running time `(⌊√⌈1/δ⌉⌋ + 1) (|x| + 2)^e` of a PCA algorithm, `O(1 + δ^(-1/2)) · poly(|x|)`,
where `|x|` is the length of the encoded input. It is polynomial in `|x|` only when `1/δ` is
polynomially bounded: a `δ` written in binary can be exponentially small in its length. -/
def spcaTime (e : ℕ) (x : SPCAInput) : ℕ :=
  (Nat.sqrt ⌈1 / x.δ⌉₊ + 1) * ((encSPCAInput x).length + 2) ^ e

/-! ### Success -/

/-- The **success probability** of the regression algorithm `A`, running in time `T`, on `n`
independent sample points from `slrLaw S xs` read to `p` bits: over the sample and the coins, the
probability that `A`'s estimate achieves prediction error `0.01` for the secret `x*` on the real
design. The algorithm sees the sparsity, the precision and the quantized sample, but neither the
real sample nor `Σ` nor `x*`.

It is `∫ ω, P_coins[good] dω`, written as a lower integral as in the other papers of this
repository. The integrand is measurable (the quantization is, and the prediction error is
continuous in the sample for each estimate), so this is the ordinary integral. -/
noncomputable def slrSuccessProb (A : SLRInput × List Bool → Estimate) (T : SLRInput → ℕ)
    (n k p : ℕ) (S : Matrix (Fin D) (Fin D) ℝ) (xs : Fin D → ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal (coinProb (T (slrInput k p ω))
      fun c ↦ PredictsWell ω xs (A (slrInput k p ω, c)))
    ∂(Measure.pi fun _ : Fin n ↦ slrLaw S xs)).toReal

/-- The regression algorithm `A`, running in time `T`, **solves sparse linear regression** with
`n` samples in dimension `D` with sparsity `k`, read to `p` bits, with failure probability `δ`
[BDT24, Model 1.1, noise variance `1`]: on every instance with `I/(k+2) ⪯ Σ ⪯ I` and a `k`-sparse
`x*` with `‖x*‖² ≤ k`, its estimate achieves prediction error `0.01` with probability at least
`1 - δ`. -/
def SolvesSLR (A : SLRInput × List Bool → Estimate) (T : SLRInput → ℕ) (n D k p : ℕ) (δ : ℝ) :
    Prop :=
  ∀ (S : Matrix (Fin D) (Fin D) ℝ) (xs : Fin D → ℝ), IsBoundedInstance k S xs →
    1 - δ ≤ slrSuccessProb A T n k p S xs

/-- The probability that the PCA algorithm `B`, running in time `T`, outputs `b` on `n`
independent points from `N(0, S)` read to `q` bits, given `δ`, `p` and `k`, over the sample and
the coins. The quantization is measurable, so the integrand is, and this lower integral is the
ordinary integral. -/
noncomputable def spcaOutputProb (B : SPCAInput × List Bool → Bool) (T : SPCAInput → ℕ)
    (δ : ℚ) (p k q n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (b : Bool) : ℝ :=
  (∫⁻ ω, ENNReal.ofReal
      (coinProb (T (spcaInput δ p k q ω)) fun c ↦ B (spcaInput δ p k q ω, c) = b)
    ∂(Measure.pi fun _ : Fin n ↦ multivariateGaussian 0 S)).toReal

/-- The PCA algorithm `B`, running in time `T` and given `δ` and `p`, **solves `NegSPCA_θ`** for
`θ = (k+1)/(k+2)` with `n` samples in dimension `d + 1`, read to `q` bits, with probability
`1 - ε` [BDT24, Model 1.3]:

* on samples from the null law `N(0, I_{d+1})` it outputs `false` with probability at least
  `1 - ε`, and
* on samples from the planted law it outputs `true` with probability at least `1 - ε`: the
  spike's sign pattern `v` is uniform on `BDT24.spikeSigns d k`, and given `v` the points are
  independent from `N(0, I - θ x xᵀ)` for the spike `x` of `v`. -/
def SolvesNegSPCA (B : SPCAInput × List Bool → Bool) (T : SPCAInput → ℕ) (δ : ℚ)
    (p q n d k : ℕ) (ε : ℝ) : Prop :=
  1 - ε ≤ spcaOutputProb B T δ p k q n (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) false ∧
  1 - ε ≤ (∑ v ∈ spikeSigns d k,
      spcaOutputProb B T δ p k q n (spikedCov (theta k) (spikeVector k v)) true) /
    (spikeSigns d k).card

/-! ### Low-degree polynomials -/

/-- `P` has **degree-`D` advantage at most `ε`** over `Q` (as in [BDT24, Appendix B], following
the low-degree literature), for points with coordinates `x ω : ι → ℝ`: every polynomial `f` of
total degree at most `D` in the coordinates is integrable under `P` and square-integrable under
`Q`, and `E_P f - E_Q f ≤ ε √(Var_Q f)`.

The advantage is the largest ratio `(E_P f - E_Q f) / √(Var_Q f)`; this says that it is at most
`ε`, without dividing. For `E_Q f = 0` the ratio is the paper's `E_P f / √(E_Q f²)`. A polynomial
with `Var_Q f = 0` must have `E_P f ≤ E_Q f`. The integrability makes the expectations the
paper's: Lean's integral of a function that is not integrable is `0`. (The same definition as
`BHJK25.AdvantageAtMost`; papers do not import each other.) -/
def AdvantageAtMost {Ω ι : Type} [MeasurableSpace Ω] (x : Ω → ι → ℝ) (D : ℝ)
    (P Q : Measure Ω) (ε : ℝ) : Prop :=
  ∀ f : MvPolynomial ι ℝ, (f.totalDegree : ℝ) ≤ D →
    Integrable (fun ω ↦ MvPolynomial.eval (x ω) f) P ∧
      MemLp (fun ω ↦ MvPolynomial.eval (x ω) f) 2 Q ∧
      (∫ ω, MvPolynomial.eval (x ω) f ∂P) - ∫ ω, MvPolynomial.eval (x ω) f ∂Q ≤
        ε * √(variance (fun ω ↦ MvPolynomial.eval (x ω) f) Q)

/-- The coordinates of a sample of `n` points of `ℝ^m`: entry `(i, j)` is coordinate `j` of
point `i`. Polynomials in them are the paper's polynomials `f(z₁, …, z_n)`. -/
def sampleCoords {n m : ℕ} (ω : Fin n → EuclideanSpace ℝ (Fin m)) (ij : Fin n × Fin m) : ℝ :=
  ω ij.1 ij.2

/-- The law of `n` independent null points `N(0, I_{d+1})` of negative sparse PCA
[BDT24, Model 1.3]. -/
noncomputable def nullSample (n d : ℕ) : Measure (Fin n → EuclideanSpace ℝ (Fin (d + 1))) :=
  Measure.pi fun _ ↦ multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)

/-- The law of `n` planted points of `NegSPCA_θ` [BDT24, Model 1.3]: the spike's sign pattern `v`
is uniform on `BDT24.spikeSigns d k`, and given `v` the points are independent from
`N(0, I - θ x xᵀ)` for the spike `x` of `v` (`BDT24.spikeVector`). One spike is shared by all `n`
points. -/
noncomputable def plantedSample (n d k : ℕ) (θ : ℝ) :
    Measure (Fin n → EuclideanSpace ℝ (Fin (d + 1))) :=
  ((spikeSigns d k).card : ENNReal)⁻¹ • ∑ v ∈ spikeSigns d k,
    Measure.pi fun _ ↦ multivariateGaussian 0 (spikedCov θ (spikeVector k v))

/-! ### Statistical dimension -/

/-- The **relative density** `D̄_v = dP_v / dQ` [BDT24, Definition C.2] of the law
`P_v = N(0, I - θ x xᵀ)` of one planted point, for the spike `x` of the sign pattern `v`, with
respect to the null law `Q = N(0, I_{d+1})`: Mathlib's Radon–Nikodym derivative, as a real
function. -/
noncomputable def relDensity {d : ℕ} (k : ℕ) (θ : ℝ) (v : Fin d → SignType)
    (z : EuclideanSpace ℝ (Fin (d + 1))) : ℝ :=
  ((multivariateGaussian 0 (spikedCov θ (spikeVector k v))).rnDeriv
    (multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)) z).toReal

/-- The **correlation** `⟨D̄_u, D̄_v⟩ = E_Q [D̄_u D̄_v]` of the planted laws of two sign patterns
[BDT24, Definition C.2]. -/
noncomputable def pairCorr {d : ℕ} (k : ℕ) (θ : ℝ) (u v : Fin d → SignType) : ℝ :=
  ∫ z, relDensity k θ u z * relDensity k θ v z
    ∂(multivariateGaussian 0 (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ))

/-- The **statistical dimension** of `NegSPCA_θ` at VSTAT parameter `n` is at least `q`
[BDT24, Definition C.2]: for every set `A` of pairs of sign patterns of probability at least
`1/q²` under two independent uniform sign patterns, the average over `A` of
`|⟨D̄_u, D̄_v⟩ - 1|` is at most `1/n`.

The paper's `SDA(S, μ, n)` is the largest `q` with `E_{u,v ~ μ} [|⟨D̄_u, D̄_v⟩ - 1| | A] ≤ 1/n`
for every event `A` with `P(A) ≥ 1/q²`. Here the prior `μ` is uniform on the finite set
`BDT24.spikeSigns d k`, so an event is a set of pairs, its probability is its size over the
number of pairs, and the conditional expectation is the average over it. For `q ≥ 1` the
condition only gets harder as `q` grows (more events qualify), so the statistical dimension is at
least `q` exactly when the condition holds at `q`; this predicate is that condition. (A largest
`q` need not exist when the condition holds for every `q`; the predicate needs none.)

For valid sign patterns and `0 < θ < 1`, the planted law is absolutely continuous with respect
to the null law and its relative density `(1 - θ)^(-1/2) exp(-θ ⟨x, z⟩² / (2(1 - θ)))` is at
most `(1 - θ)^(-1/2)`, so the products of relative densities are integrable and `pairCorr` is the
ordinary finite correlation, `(1 - θ² ⟨x_u, x_v⟩²)^(-1/2)`. -/
def SDAAtLeast (d k : ℕ) (θ : ℝ) (n q : ℕ) : Prop :=
  ∀ A : Finset ((Fin d → SignType) × (Fin d → SignType)), A ⊆ spikeSigns d k ×ˢ spikeSigns d k →
    1 / (q : ℝ) ^ 2 ≤ (A.card : ℝ) / ((spikeSigns d k).card : ℝ) ^ 2 →
    (∑ uv ∈ A, |pairCorr k θ uv.1 uv.2 - 1|) / A.card ≤ 1 / n

end BDT24
