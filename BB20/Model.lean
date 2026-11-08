module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Restricted Boltzmann machines, their samples, and learning algorithms

The definitions that the results of [BB20] are stated in (`BB20/Challenge.lean`). Together with
what they import (Mathlib, and CSLib's multitape Turing machines), they are what a reader has to
check to know what the results say.

* **Configurations** (`BB20.Config`): assignments of `±1` to `n` variables, with `true` standing
  for `+1` and `false` for `-1` (`BB20.spin`), and the characters `χ_S(x) = ∏_{i ∈ S} xᵢ`
  (`BB20.chi`).
* **Restricted Boltzmann machines** (`BB20.RBM`): `n` observed variables `X` and `m` latent
  variables `Y`, with `P(X = x, Y = y) ∝ exp(xᵀ J y + hᵀ x + gᵀ y)`. The observed variables have
  the marginal law `P(X = x) ∝ ∑_y exp(xᵀ J y + hᵀ x + gᵀ y)` (`BB20.RBM.obsProb`).
* **The induced Markov random field**: `P(X = x) ∝ exp(f(x))` with
  `f(x) = log ∑_y exp(xᵀ J y + hᵀ x + gᵀ y)` (`BB20.RBM.potential`), which is the paper's
  `∑_j ρ(J_j · x + g_j) + hᵀ x` with `ρ(t) = log(eᵗ + e⁻ᵗ)`, and its Fourier coefficients
  `f̂(S)` (`BB20.RBM.fourier`). The **MRF neighbourhood** `N(u)` of a variable `u`
  (`BB20.RBM.nbhd`) is the set of variables `i ≠ u` that share a nonzero coefficient with `u`:
  `f̂(S) ≠ 0` for some `S ∋ u, i`.
* **Parameters**, as bounds (`BB20.RBM.MinCoeffGE`, `BB20.RBM.WidthLE`,
  `BB20.RBM.LatentDegreeLE`, `BB20.RBM.DegreeLE`, `BB20.RBM.SparsityLE`): the smallest nonzero
  coefficient `α`, the width `γ = max_u ∑_{S ∋ u} |f̂(S)|`, the largest degree `d` of a latent
  variable, the largest MRF degree `D`, and the paper's `s`, the largest number of latent
  variables connected to the MRF neighbourhood of a variable.
* **The mutual-information proxy** `ν_{u,I|S}` (`BB20.RBM.nu`), through the marginals of the
  observed law (`BB20.RBM.marg`).
* **Samples** (`BB20.RBM.sampleProb`): `M` independent samples of the observed variables.
* **Algorithms** (`BB20.RunsInTime`): deterministic multitape Turing machines. They read the
  number of variables, the samples as lists of bits, and bounds on the parameters (`BB20.Input`),
  and output one list of variables per variable (`BB20.Output`, `BB20.outNbhd`).
* **The bounds** of the structure-learning theorems: `δ = σ(-2γ)` (`BB20.condLB`), the thresholds
  `τ` and `τ'` (`BB20.tau`, `BB20.tauPrime`), the bound `L` on the size of the sets the algorithm
  conditions on (`BB20.stepBound`), the sample size (`BB20.sampleSize`), and `η`
  (`BB20.eta`).
* **Prediction** ([BB20, Section 5.2]): features `χ_T(x)` for `T ⊆ V` (`BB20.score`), the
  logistic loss and the empirical risk (`BB20.logLoss`, `BB20.empRisk`), near-minimizers of the
  empirical risk over an `ℓ₁` ball (`BB20.IsNearMinimizer`), and the prediction error
  `E[(P(X_u = 1 | X_{∖u}) - σ(w · z))²]` (`BB20.RBM.predError`).

References: [BB20] G. Bresler, R.-D. Buhai, *Learning restricted Boltzmann machines with sparse
latent variables*, NeurIPS 2020, arXiv:2006.04166. [HKM17] L. Hamilton, F. Koehler, A. Moitra,
*Information theoretic properties of Markov random fields, and their algorithmic applications*,
NeurIPS 2017, arXiv:1705.11107.
-/

@[expose] public section

namespace BB20

open Encoding Finset

/-! ### Configurations and characters -/

/-- An assignment of signs to the variables `0, …, n - 1`: `true` stands for `+1` and `false` for
`-1`. -/
abbrev Config (n : ℕ) := Fin n → Bool

/-- The sign a bit stands for: `true ↦ 1`, `false ↦ -1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- The character `χ_S(x) = ∏_{i ∈ S} xᵢ`. -/
def chi {n : ℕ} (S : Finset (Fin n)) (x : Config n) : ℝ := ∏ i ∈ S, spin (x i)

/-! ### Restricted Boltzmann machines -/

/-- A **restricted Boltzmann machine** with `n` observed and `m` latent variables: the interaction
matrix `J`, the external field `h` on the observed variables, and the external field `g` on the
latent variables. -/
structure RBM (n m : ℕ) where
  /-- The interactions `J i j` between observed variable `i` and latent variable `j`. -/
  J : Fin n → Fin m → ℝ
  /-- The external field on the observed variables. -/
  h : Fin n → ℝ
  /-- The external field on the latent variables. -/
  g : Fin m → ℝ

variable {n m : ℕ}

namespace RBM

/-- The unnormalized probability `exp(xᵀ J y + hᵀ x + gᵀ y)` of the observed configuration `x`
together with the latent configuration `y`. -/
noncomputable def weight (R : RBM n m) (x : Config n) (y : Config m) : ℝ :=
  Real.exp (∑ i, ∑ j, R.J i j * spin (x i) * spin (y j) + ∑ i, R.h i * spin (x i) +
    ∑ j, R.g j * spin (y j))

/-- The unnormalized marginal probability `∑_y exp(xᵀ J y + hᵀ x + gᵀ y)` of the observed
configuration `x`. -/
noncomputable def obsWeight (R : RBM n m) (x : Config n) : ℝ := ∑ y, R.weight x y

/-- The **law of the observed variables**: `P(X = x)`, the marginal of the RBM. -/
noncomputable def obsProb (R : RBM n m) (x : Config n) : ℝ :=
  R.obsWeight x / ∑ x', R.obsWeight x'

/-- The potential `f(x) = log ∑_y exp(xᵀ J y + hᵀ x + gᵀ y)` of the Markov random field of the
observed variables, `P(X = x) ∝ exp(f(x))`. It equals `∑_j ρ(J_j · x + g_j) + hᵀ x` with
`ρ(t) = log(eᵗ + e⁻ᵗ)` and `J_j` the `j`-th column of `J`. -/
noncomputable def potential (R : RBM n m) (x : Config n) : ℝ := Real.log (R.obsWeight x)

/-- The **Fourier coefficient** `f̂(S) = 2⁻ⁿ ∑ₓ f(x) χ_S(x)` of the potential, the potential of the
clique `S` in the Markov random field: `f = ∑_S f̂(S) χ_S`. -/
noncomputable def fourier (R : RBM n m) (S : Finset (Fin n)) : ℝ :=
  (∑ x, R.potential x * chi S x) / 2 ^ n

open Classical in
/-- The **MRF neighbourhood** `N(u)`: the variables `i ≠ u` such that `f̂(S) ≠ 0` for some set `S`
containing both `u` and `i`. -/
noncomputable def nbhd (R : RBM n m) (u : Fin n) : Finset (Fin n) :=
  univ.filter fun i ↦ i ≠ u ∧ ∃ S : Finset (Fin n), u ∈ S ∧ i ∈ S ∧ R.fourier S ≠ 0

open Classical in
/-- The **`ζ`-strong neighbours** of `u` [BB20, Theorem 11]: the variables `i ≠ u` connected to
`u` through a Fourier coefficient of absolute value at least `ζ`: `|f̂(S)| ≥ ζ` for some set `S`
containing both `u` and `i`. For `ζ > 0` they are neighbours. -/
noncomputable def strongNbhd (R : RBM n m) (ζ : ℝ) (u : Fin n) : Finset (Fin n) :=
  univ.filter fun i ↦ i ≠ u ∧ ∃ S : Finset (Fin n), u ∈ S ∧ i ∈ S ∧ ζ ≤ |R.fourier S|

/-- Every nonzero Fourier coefficient `f̂(S)` on at least two variables has absolute value at
least `α`: `α` is a lower bound on the paper's minimum potential. (Coefficients on one variable,
the external fields of the Markov random field, play no role in its neighbourhoods and are not
constrained.) -/
def MinCoeffGE (R : RBM n m) (α : ℝ) : Prop :=
  ∀ S : Finset (Fin n), 2 ≤ S.card → R.fourier S ≠ 0 → α ≤ |R.fourier S|

/-- The **width** of the Markov random field is at most `γ`: `∑_{S ∋ u} |f̂(S)| ≤ γ` for every
variable `u`. -/
def WidthLE (R : RBM n m) (γ : ℝ) : Prop :=
  ∀ u : Fin n, ∑ S ∈ univ.filter (u ∈ ·), |R.fourier S| ≤ γ

open Classical in
/-- Every latent variable is connected to at most `d` observed variables: the paper's `d` is at
most `d`. -/
def LatentDegreeLE (R : RBM n m) (d : ℕ) : Prop :=
  ∀ j : Fin m, (univ.filter fun i ↦ R.J i j ≠ 0).card ≤ d

/-- Every MRF neighbourhood has at most `D` variables: the paper's `D` is at most `D`. -/
def DegreeLE (R : RBM n m) (D : ℕ) : Prop :=
  ∀ u : Fin n, (R.nbhd u).card ≤ D

open Classical in
/-- For every variable `u`, at most `s` latent variables are connected to the MRF neighbourhood
of `u`: the paper's `s` is at most `s`. -/
def SparsityLE (R : RBM n m) (s : ℕ) : Prop :=
  ∀ u : Fin n, (univ.filter fun j : Fin m ↦ ∃ i ∈ R.nbhd u, R.J i j ≠ 0).card ≤ s

/-! ### The mutual-information proxy -/

open Classical in
/-- The probability `P(X_A = z_A)` that the observed variables agree with `z` on the set `A`. -/
noncomputable def marg (R : RBM n m) (A : Finset (Fin n)) (z : Config n) : ℝ :=
  ∑ x, if ∀ i ∈ A, x i = z i then R.obsProb x else 0

/-- The **mutual-information proxy**
`ν_{u,I|S} = E_{R,G} E_{X_S} |P(X_u = R, X_I = G | X_S) - P(X_u = R | X_S) P(X_I = G | X_S)|`,
with `R` and `G` uniform on `{±1}` and `{±1}^I`, for disjoint `{u}`, `I` and `S`.

It is written as an average over a uniform configuration `z`, which supplies `R = z_u`, `G = z_I`
and the value `z_S` of `X_S`: the term of `z` is
`P(X_S = z_S) · |P(z_u, z_I | z_S) - P(z_u | z_S) P(z_I | z_S)|
  = |P(z_u, z_I, z_S) - P(z_u, z_S) P(z_I, z_S) / P(z_S)|`, and the sum over the `2ⁿ`
configurations divided by `2^(n - |S|)` is the average over `R` and `G` of the sum over `z_S`. -/
noncomputable def nu (R : RBM n m) (u : Fin n) (I S : Finset (Fin n)) : ℝ :=
  (∑ z : Config n, |R.marg (insert u (I ∪ S)) z -
    R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z|) / 2 ^ (n - S.card)

/-! ### Samples -/

open Classical in
/-- The probability that `M` independent samples `X₁, …, X_M` of the observed variables satisfy
`P`. -/
noncomputable def sampleProb (R : RBM n m) (M : ℕ) (P : (Fin M → Config n) → Prop) : ℝ :=
  ∑ X : Fin M → Config n, if P X then ∏ k, R.obsProb (X k) else 0

/-! ### Conditional probabilities -/

/-- The conditional probability `P(X_u = 1 | X_{∖u} = x_{∖u})` of `X_u = +1` given the values of
`x` on the other variables. -/
noncomputable def condProb (R : RBM n m) (u : Fin n) (x : Config n) : ℝ :=
  R.obsProb (Function.update x u true) /
    (R.obsProb (Function.update x u true) + R.obsProb (Function.update x u false))

end RBM

/-! ### Learning algorithms -/

/-- The input of the structure-learning algorithms of [BB20, Theorems 6 and 11]. -/
structure Input where
  /-- The number of observed variables. -/
  n : ℕ
  /-- The samples: one list of `n` bits per sample, `true` standing for `+1`. -/
  samples : List (List Bool)
  /-- A coefficient bound: a lower bound `α` on the nonzero Fourier coefficients (Theorem 6), or
  the threshold `ζ` (Theorem 11). -/
  coeff : ℚ
  /-- An upper bound `γ` on the width. -/
  gamma : ℚ
  /-- An upper bound `d` on the degree of a latent variable. -/
  d : ℕ
  /-- An upper bound `D` on the MRF degree. -/
  D : ℕ
  /-- An upper bound `s` on the number of latent variables connected to an MRF neighbourhood. -/
  s : ℕ

/-- Encoded as `n` in binary, the samples, the two rational bounds, and `d`, `D`, `s` in
binary. -/
def encInput : Input ↪ List Bool :=
  ⟨fun x ↦ encPair encNat (encPair (encList encBits) (encPair encRat (encPair encRat
      (encPair encNat (encPair encNat encNat))))) (x.n, x.samples, x.coeff, x.gamma, x.d, x.D, x.s),
    by
    rintro ⟨n, X, a, g, d, D, s⟩ ⟨n', X', a', g', d', D', s'⟩ h
    have h' := (encPair encNat (encPair (encList encBits) (encPair encRat (encPair encRat
      (encPair encNat (encPair encNat encNat)))))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h'
    rfl⟩

/-- The samples `X₁, …, X_M` as the algorithm reads them: one list of `n` bits per sample, in the
order of the samples. -/
def sampleList {M : ℕ} (X : Fin M → Config n) : List (List Bool) :=
  List.ofFn fun k ↦ List.ofFn (X k)

/-- An output: one list of variables for each variable `0, 1, …`, its estimated neighbourhood. -/
abbrev Output := List (List ℕ)

/-- Outputs are encoded as lists of lists of numbers in binary. -/
def encOutput : Output ↪ List Bool := encList (encList encNat)

/-- The estimated neighbourhood of the variable `u` in the output `out`: the set of numbers in the
`u`-th list, empty if the output has no `u`-th list. -/
def outNbhd (out : Output) (u : ℕ) : Finset ℕ := (out.getD u []).toFinset

/-- The output **recovers** the MRF neighbourhoods [BB20, Theorem 6]: for every variable `u`, its
estimated neighbourhood is exactly `N(u)`. -/
def RBM.Recovers (R : RBM n m) (out : Output) : Prop :=
  ∀ u : Fin n, outNbhd out u = (R.nbhd u).map Fin.valEmbedding

/-- The output **recovers the `ζ`-strong neighbours** [BB20, Theorem 11]: for every variable `u`,
its estimated neighbourhood contains every `ζ`-strong neighbour of `u` and only neighbours of
`u`. -/
def RBM.RecoversStrong (R : RBM n m) (ζ : ℝ) (out : Output) : Prop :=
  ∀ u : Fin n, (R.strongNbhd ζ u).map Fin.valEmbedding ⊆ outNbhd out u ∧
    outNbhd out u ⊆ (R.nbhd u).map Fin.valEmbedding

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an input `x`, halts with output `A x` within `c (T x + |x| + 1)`
steps and cells, for a constant `c`, where `|x|` is the length of the encoded input. -/
def RunsInTime {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (A : α → β)
    (T : α → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A encIn encOut
    (fun x ↦ c * (T x + (encIn x).length + 1)) (fun x ↦ c * (T x + (encIn x).length + 1))

/-- The running time `(|x| + 2)^c · (n + 2)^(2^s)` of a structure-learning algorithm on the input
`x`, where `|x|` is the length of the encoded input, `n` the number of variables and `s` the bound
given with `x`. -/
def learnTime (c : ℕ) (x : Input) : ℕ :=
  ((encInput x).length + 2) ^ c * (x.n + 2) ^ 2 ^ x.s

/-! ### The bounds of the structure-learning theorems -/

/-- `δ = σ(-2γ) = 1 / (1 + e^{2γ})`: in a Markov random field of width at most `γ`, the
conditional probability of any value of a variable, given the values of any other variables, is
at least `δ`. -/
noncomputable def condLB (γ : ℝ) : ℝ := 1 / (1 + Real.exp (2 * γ))

/-- The threshold `τ = ½ · α² δ^{d+D-1} / (d^{4d} 2^{d+1} max(1, C(D, d-1)) γ e^{2γ})` with
`δ = σ(-2γ)` (`BB20.condLB`): when `S` does not contain all of `N(u)`, `2τ` lower-bounds
`ν_{u,I|S}` for some set `I` of at most `d - 1` neighbours of `u` outside `S` (as in [BB20, proof
of Theorem 5]). It has the form of the paper's `τ`; `BB20/Challenge.lean` lists the
differences. -/
noncomputable def tau (α γ : ℝ) (d D : ℕ) : ℝ :=
  1 / 2 * (α ^ 2 * condLB γ ^ (d + D - 1) /
    ((d : ℝ) ^ (4 * d) * 2 ^ (d + 1) * max 1 ((D.choose (d - 1) : ℕ) : ℝ) * γ *
      Real.exp (2 * γ)))

/-- The threshold `τ' = τ / ((4d)^{2^s} d^{2^s (2^s + 1)})` [BB20, Section 3]: when `S` does not
contain all of `N(u)`, `2τ'` lower-bounds `ν_{u,I|S}` for some set `I` of at most `2^s`
neighbours of `u` outside `S` [BB20, Theorem 5]. -/
noncomputable def tauPrime (α γ : ℝ) (d D s : ℕ) : ℝ :=
  tau α γ d D / ((4 * d : ℝ) ^ 2 ^ s * (d : ℝ) ^ (2 ^ s * (2 ^ s + 1)))

/-- `L = 2^s · 8 / τ'²`: a bound on the size of the sets of variables that the structure-learning
algorithm conditions on. It adds sets of at most `2^s` variables, each raising the mutual
information with `X_u` by `Ω(τ'²)`. -/
noncomputable def stepBound (α γ : ℝ) (d D s : ℕ) : ℝ :=
  2 ^ s * 8 / tauPrime α γ d D s ^ 2

/-- The sample size of the formal Theorem 6 (`BB20.structure_learning`) for failure probability
`ω`:
`60 · 2^{2L} / (τ'² δ^{2L}) · (log(1/ω) + log(L + 2^s + 1) + (L + 2^s + 1) log(2n) + log 2)`,
with `δ = σ(-2γ)` (`BB20.condLB`), `τ'` (`BB20.tauPrime`) and `L` (`BB20.stepBound`). The
exponents `2L` are real. It has the form of the sample size in [BB20, Theorem 6];
`BB20/Challenge.lean` lists the differences. -/
noncomputable def sampleSize (α γ : ℝ) (d D s n : ℕ) (ω : ℝ) : ℝ :=
  60 * 2 ^ (2 * stepBound α γ d D s) /
      (tauPrime α γ d D s ^ 2 * condLB γ ^ (2 * stepBound α γ d D s)) *
    (Real.log (1 / ω) + Real.log (stepBound α γ d D s + 2 ^ s + 1) +
      (stepBound α γ d D s + 2 ^ s + 1) * Real.log (2 * n) + Real.log 2)

/-- `η = √(δ^D / (6 · 2^{D + 2^{s+1}} · D^{2^s (2^s + 2)}))` with `δ = σ(-2γ)`
(`BB20.condLB`): the formal Theorem 11 (`BB20.structure_learning_strong`) uses the sample size of
the formal Theorem 6 with `α = ζ η`, as [BB20, Theorem 11] does with its `η`. This `η` is the
paper's `η = 1 / (√3 · 2^{D/2 + 2^s} · D^{2^{s-1} (2^s + 2)})` multiplied by `δ^{D/2} / √2`. -/
noncomputable def eta (γ : ℝ) (D s : ℕ) : ℝ :=
  Real.sqrt (condLB γ ^ D / (6 * 2 ^ (D + 2 ^ (s + 1)) * (D : ℝ) ^ (2 ^ s * (2 ^ s + 2))))

/-! ### Prediction -/

/-- The sigmoid `σ(t) = 1 / (1 + e^{-t})`. -/
noncomputable def sigmoid (t : ℝ) : ℝ := 1 / (1 + Real.exp (-t))

/-- The linear predictor `w · z = ∑_{T ⊆ V} w_T χ_T(x)` on the features `z_T = χ_T(x)`,
`T ⊆ V`. Weights are indexed by sets; only those of subsets of `V` count. -/
def score (V : Finset (Fin n)) (w : Finset (Fin n) → ℝ) (x : Config n) : ℝ :=
  ∑ T ∈ V.powerset, w T * chi T x

/-- The `ℓ₁` norm `∑_{T ⊆ V} |w_T|` of the weights of the subsets of `V`. -/
def l1Norm (V : Finset (Fin n)) (w : Finset (Fin n) → ℝ) : ℝ :=
  ∑ T ∈ V.powerset, |w T|

/-- The logistic loss `l(t) = log(1 + e^{-t})`. -/
noncomputable def logLoss (t : ℝ) : ℝ := Real.log (1 + Real.exp (-t))

/-- The empirical risk `(1/M) ∑_k l(y_k (w · z_k))` of the weights `w` for predicting `X_u` from
the features of `V` on the samples `X₁, …, X_M`, with `y_k` the sign of `X_u` in sample `k`. -/
noncomputable def empRisk {M : ℕ} (u : Fin n) (V : Finset (Fin n)) (X : Fin M → Config n)
    (w : Finset (Fin n) → ℝ) : ℝ :=
  (∑ k, logLoss (spin (X k u) * score V w (X k))) / M

/-- `w` is a **near-minimizer** of the empirical risk over the `ℓ₁` ball of radius `2γ`, within
`η`: `‖w‖₁ ≤ 2γ`, and its empirical risk exceeds that of any other `w'` with `‖w'‖₁ ≤ 2γ` by at
most `η`. -/
def IsNearMinimizer (γ η : ℝ) {M : ℕ} (u : Fin n) (V : Finset (Fin n)) (X : Fin M → Config n)
    (w : Finset (Fin n) → ℝ) : Prop :=
  l1Norm V w ≤ 2 * γ ∧
    ∀ w' : Finset (Fin n) → ℝ, l1Norm V w' ≤ 2 * γ → empRisk u V X w ≤ empRisk u V X w' + η

/-- The **prediction error** `E[(P(X_u = 1 | X_{∖u}) - σ(w · z))²]` of the weights `w` on the
features of `V`, over a sample `X` of the observed variables. -/
noncomputable def RBM.predError (R : RBM n m) (u : Fin n) (V : Finset (Fin n))
    (w : Finset (Fin n) → ℝ) : ℝ :=
  ∑ x, R.obsProb x * (R.condProb u x - sigmoid (score V w x)) ^ 2

end BB20
