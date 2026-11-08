module

public import Background.Encoding
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.Moments.Variance

/-!
# The low-degree advantage, the two counterexamples, and algorithms

The definitions that the main results of [BHJK25] are stated in (`BHJK25/Challenge.lean`).
Together with what they import (Mathlib, and CSLib's multitape Turing machines), they are what a
reader has to check to know what the theorems say.

* **The low-degree advantage** (`BHJK25.AdvantageAtMost`, [BHJK25, Definition 1.1]): `P` has
  degree-`D` advantage at most `δ` over `Q` when every polynomial `f` of degree at most `D` in the
  coordinates has `E_P f - E_Q f ≤ δ √(Var_Q f)`.
* **Boolean tensors** ([BHJK25, Section 2]): a symmetric `k`-tensor with entries in `{0, 1}` is a
  function from the `k`-element subsets of `{0, …, n - 1}` to bits (`BHJK25.Tensor`), that is, a
  point of `{0,1}^(n choose k)`. Permutations of `{0, …, n - 1}` relabel it (`BHJK25.relabel`,
  `BHJK25.SnInvariant`). The null distribution `Q_n` is uniform (`BHJK25.uniformTensor`,
  `BHJK25.uniformProb`), and the noise operator `T_ε` replaces each entry by a uniformly random
  bit with probability `ε` (`BHJK25.noisyProb`).
* **Spiked spectra** ([BHJK25, Section 3]): the eigenvalue distribution `μ_γ`
  (`BHJK25.eigLaw`), the null and planted distributions of `U diag(λ) Uᵀ` (`BHJK25.nullLaw`,
  `BHJK25.plantedLaw`) and their instances in Theorem 3.1 (`BHJK25.nullAt`, `BHJK25.plantedAt`),
  the noisy matrix `(1 - ε) M₁ + ε M₀` (`BHJK25.noisyLaw`), and rotation invariance
  (`BHJK25.RotationInvariant`). The maps that define these laws are measurable
  (`BHJK25.measurable_spectral`, `BHJK25.measurable_noisy`, `BHJK25.measurable_conj`), so the
  laws are the intended images of measures.
* **Rational approximations** (`BHJK25.Approximates`): the algorithm of Theorem 3.1 reads a
  rational matrix within `1/n` of the real one in every entry.
* **Algorithms** (`BHJK25.RunsInTime`): deterministic multitape Turing machines, reading inputs
  encoded as bit strings (`BHJK25.encTensor`, `BHJK25.encRatMatrix`).
* **Events** (`BHJK25.ProbAtLeast`): a property holds with probability at least `p` when it holds
  on a measurable event of probability at least `p`.

Reference: [BHJK25] R.-D. Buhai, J.-T. Hsieh, A. Jain, P. K. Kothari, *The quasi-polynomial
low-degree conjecture is false*, FOCS 2025, arXiv:2505.17360.
-/

@[expose] public section

namespace BHJK25

open Encoding MeasureTheory ProbabilityTheory Matrix

/-! ### The low-degree advantage -/

/-- `P` has **degree-`D` advantage at most `δ`** over `Q` [BHJK25, Definition 1.1], for points
with coordinates `x ω : ι → ℝ`: every polynomial `f` of total degree at most `D` in the
coordinates is integrable under `P` and square-integrable under `Q`, and
`E_P f - E_Q f ≤ δ √(Var_Q f)`.

The paper's advantage is the largest ratio `(E_P f - E_Q f) / √(Var_Q f)`; this says that it is at
most `δ`, without dividing. A polynomial with `Var_Q f = 0` must have `E_P f ≤ E_Q f`, as it must
for its ratio not to be infinite. The integrability makes the expectations those of the paper:
Lean's integral of a function that is not integrable is `0`. Since `-f` is a polynomial too,
advantage at most `0` says that `E_P f = E_Q f` for every polynomial `f` of degree at most `D`. -/
def AdvantageAtMost {Ω ι : Type} [MeasurableSpace Ω] (x : Ω → ι → ℝ) (D : ℝ)
    (P Q : Measure Ω) (δ : ℝ) : Prop :=
  ∀ f : MvPolynomial ι ℝ, (f.totalDegree : ℝ) ≤ D →
    Integrable (fun ω ↦ MvPolynomial.eval (x ω) f) P ∧
      MemLp (fun ω ↦ MvPolynomial.eval (x ω) f) 2 Q ∧
      (∫ ω, MvPolynomial.eval (x ω) f ∂P) - ∫ ω, MvPolynomial.eval (x ω) f ∂Q ≤
        δ * √(variance (fun ω ↦ MvPolynomial.eval (x ω) f) Q)

/-! ### Boolean tensors -/

/-- The `k`-element subsets of `{0, …, n - 1}`: the positions `{i₁, …, i_k}` of the entries of a
symmetric `k`-tensor whose indices are distinct. -/
abbrev KSet (k n : ℕ) := {S : Finset (Fin n) // S.card = k}

/-- A **symmetric `k`-tensor** with entries in `{0, 1}` (`true` standing for `1`): one entry
`M_{i₁ … i_k}` for each set `{i₁, …, i_k}` of `k` distinct indices. This is a point of
`{0,1}^(n choose k)`, the domain of [BHJK25, Conjecture 1.2]; for `k = 2` it is a graph on `n`
vertices. -/
abbrev Tensor (k n : ℕ) := KSet k n → Bool

variable {k n : ℕ}

/-- The entries of a tensor as the real numbers `0` and `1`: the coordinates at which the
polynomials of the low-degree advantage are evaluated. -/
def entryBits (M : Tensor k n) : KSet k n → ℝ := fun S ↦ if M S then 1 else 0

/-- The **relabelling** of a tensor by a permutation `σ` of `{0, …, n - 1}`: its entry at `σ(S)`
is the entry of `M` at `S`. -/
def relabel (σ : Equiv.Perm (Fin n)) (M : Tensor k n) : Tensor k n :=
  fun S ↦ M ⟨S.1.map σ.symm.toEmbedding, by rw [Finset.card_map]; exact S.2⟩

/-- A distribution on tensors is **`S_n`-invariant** [BHJK25, Conjecture 1.2] when relabelling
does not change it: every tensor has the same probability as each of its relabellings. -/
def SnInvariant (P : Measure (Tensor k n)) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (M : Tensor k n), P {relabel σ M} = P {M}

/-- The **null distribution** `Q_n`: the uniform distribution on tensors, whose entries are
independent uniformly random bits. -/
noncomputable def uniformTensor (k n : ℕ) : Measure (Tensor k n) :=
  Measure.uniformOfFinset Finset.univ

open Classical in
/-- The probability that a tensor drawn from `Q_n` satisfies `E`. -/
noncomputable def uniformProb (k n : ℕ) (E : Tensor k n → Prop) : ℝ :=
  (Fintype.card {M : Tensor k n // E M} : ℝ) / 2 ^ Fintype.card (KSet k n)

/-- The probability that the noise operator `T_ε` turns the tensor `M` into `M'`. Each entry is
independently replaced, with probability `ε`, by a uniformly random bit [BHJK25, Section 2], so it
is kept with probability `1 - ε / 2` and flipped with probability `ε / 2`. -/
noncomputable def noiseMass (ε : ℝ) (M M' : Tensor k n) : ℝ :=
  ∏ S, if M' S = M S then 1 - ε / 2 else ε / 2

open Classical in
/-- The probability that a tensor drawn from `T_ε P` satisfies `E`: a tensor `M` is drawn from
`P`, and the noise turns it into `M'`. -/
noncomputable def noisyProb (ε : ℝ) (P : Measure (Tensor k n)) (E : Tensor k n → Prop) : ℝ :=
  ∑ M, ∑ M', if E M' then (P {M}).toReal * noiseMass ε M M' else 0

/-! ### Tensors as inputs -/

/-- An input of the algorithm of Theorem 2.1: a number `n` and a tensor. -/
abbrev TensorInput (k : ℕ) := (n : ℕ) × Tensor k n

open Classical in
/-- The **table** of a tensor: its `n^k` entries `M_{i₁ … i_k}`, one for each index tuple
`(i₁, …, i_k)` (in the order of `finFunctionFinEquiv`, which reads a tuple as a number in base
`n`), with `0` (`false`) where two indices coincide. This is the tensor as an element of
`({0,1}^n)^⊗k`, as in [BHJK25, Theorem 2.1]; for `k = 2` it is the adjacency matrix. -/
noncomputable def table (M : Tensor k n) : List Bool :=
  List.ofFn fun t : Fin (n ^ k) ↦
    if h : Function.Injective (finFunctionFinEquiv.symm t) then
      M ⟨Finset.univ.image (finFunctionFinEquiv.symm t), by
        rw [Finset.card_image_of_injective _ h, Finset.card_univ, Fintype.card_fin]⟩
    else false

theorem table_injective {M M' : Tensor k n} (h : table M = table M') : M = M' := by
  classical
  have h' := List.ofFn_injective h
  funext S
  have hS := congrFun h' (finFunctionFinEquiv (S.1.orderEmbOfFin S.2))
  have hinj : Function.Injective (finFunctionFinEquiv.symm
      (finFunctionFinEquiv (S.1.orderEmbOfFin S.2))) := by
    rw [Equiv.symm_apply_apply]
    exact (S.1.orderEmbOfFin S.2).injective
  simp only [hinj, ↓reduceDIte] at hS
  have hset : (⟨Finset.univ.image (finFunctionFinEquiv.symm
      (finFunctionFinEquiv (S.1.orderEmbOfFin S.2))), by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]⟩ :
      KSet k n) = S := by
    apply Subtype.ext
    simp only [Equiv.symm_apply_apply]
    exact Finset.image_orderEmbOfFin_univ S.1 S.2
  rwa [hset] at hS

/-- A tensor input is encoded as `n` in binary followed by the table of the tensor. -/
noncomputable def encTensor (k : ℕ) : TensorInput k ↪ List Bool :=
  ⟨fun x ↦ encPair encNat encBits (x.1, table x.2), by
    rintro ⟨n, M⟩ ⟨n', M'⟩ h
    have h' := (encPair encNat encBits).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, h2⟩ := h'
    rw [table_injective h2]⟩

/-- The running time `n^O(log^(1/(k-1)) n)` of [BHJK25, Theorem 2.1] on a tensor input with
dimension `n`: `(n + 2)^(C ((log (n + 2))^(1/(k-1)) + 1))`, rounded up. -/
noncomputable def tensorTime (k C : ℕ) (x : TensorInput k) : ℕ :=
  ⌈((x.1 : ℝ) + 2) ^ ((C : ℝ) * (Real.log ((x.1 : ℝ) + 2) ^ (1 / ((k : ℝ) - 1)) + 1))⌉₊

/-! ### Spiked spectra -/

/-- The **eigenvalue distribution** `μ_γ` [BHJK25, Definition 3.2]: uniform on `[-1, 0]` with
probability `γ`, and `0` otherwise. (The interval `[-1, 0]` has length `1`, so Lebesgue measure on
it is the uniform distribution.) It is a probability distribution when `0 ≤ γ ≤ 1`. -/
noncomputable def eigLaw (γ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - γ) • Measure.dirac 0 + ENNReal.ofReal γ • volume.restrict (Set.Icc (-1) 0)

/-- The law of the matrix `U diag(λ) Uᵀ`, where `λ ∈ ℝ^m` has law `ν` and `U` is an independent
`n × m` matrix with independent standard Gaussian entries. -/
noncomputable def spectralLaw {m : ℕ} (ν : Measure (Fin m → ℝ)) (n : ℕ) :
    Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (ν.prod (Measure.pi fun _ : Fin n ↦ Measure.pi fun _ : Fin m ↦ gaussianReal 0 1)).map
    fun p ↦ Matrix.of p.2 * Matrix.diagonal p.1 * (Matrix.of p.2)ᵀ

/-- The **null distribution** `Q_n^(γ, m)` [BHJK25, Definition 3.3]: `U diag(λ) Uᵀ` with
`λ₁, …, λ_m` independent with law `μ_γ`. -/
noncomputable def nullLaw (γ : ℝ) (m n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  spectralLaw (Measure.pi fun _ : Fin m ↦ eigLaw γ) n

/-- The **planted distribution** `P_n^(γ, m, λ*)` [BHJK25, Definition 3.4]: as the null
distribution, except that the last eigenvalue is `λ_m = λ*` (`spike`). -/
noncomputable def plantedLaw (γ : ℝ) (m : ℕ) (spike : ℝ) (n : ℕ) :
    Measure (Matrix (Fin n) (Fin n) ℝ) :=
  spectralLaw
    (Measure.pi fun i : Fin m ↦ if (i : ℕ) + 1 = m then Measure.dirac spike else eigLaw γ) n

/-- The paper's `γ = C log² n / n`, the probability that an eigenvalue is not `0`, in the proof of
[BHJK25, Theorem 3.1] (Section 3.3), capped at `1`. The cap changes nothing for large `n`, and
makes `μ_γ` a probability distribution for every `n` when `C ≥ 0`. -/
noncomputable def sparsity (C : ℝ) (n : ℕ) : ℝ := min 1 (C * Real.log n ^ 2 / n)

/-- The null distribution `Q_n` of [BHJK25, Theorem 3.1], with the parameters of its proof:
`m = n` eigenvalues, and `γ = min(1, C log² n / n)` (`BHJK25.sparsity`). -/
noncomputable def nullAt (C : ℝ) (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  nullLaw (sparsity C n) n n

/-- The planted distribution `P_n` of [BHJK25, Theorem 3.1], with the parameters of its proof:
`m = n` eigenvalues, `γ = min(1, C log² n / n)` (`BHJK25.sparsity`), and `λ* = γ log n`. -/
noncomputable def plantedAt (C : ℝ) (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  plantedLaw (sparsity C n) n (sparsity C n * Real.log n) n

/-- The law of the **noisy matrix** `(1 - ε) M₁ + ε M₀`, where `M₁ ∼ P` and `M₀ ∼ Q` are
independent [BHJK25, Theorem 3.1]. -/
noncomputable def noisyLaw (ε : ℝ) (P Q : Measure (Matrix (Fin n) (Fin n) ℝ)) :
    Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (P.prod Q).map fun p ↦ (1 - ε) • p.1 + ε • p.2

/-- A distribution on `n × n` matrices is **rotation invariant** when, for every orthogonal matrix
`O`, `O M Oᵀ` has the same distribution as `M`. -/
def RotationInvariant (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  ∀ O ∈ Matrix.orthogonalGroup (Fin n) ℝ, μ.map (fun M ↦ O * M * Oᵀ) = μ

/-! The maps that define these laws are measurable (they are continuous). This matters:
`Measure.map f μ` is the law of `f` under `μ` only for an (almost everywhere) measurable `f`, and
otherwise Mathlib defines it as an arbitrary Dirac mass. So `BHJK25.spectralLaw`,
`BHJK25.noisyLaw` and `BHJK25.RotationInvariant` mean what they say. -/

theorem measurable_spectral {m n : ℕ} :
    Measurable fun p : (Fin m → ℝ) × (Fin n → Fin m → ℝ) ↦
      Matrix.of p.2 * Matrix.diagonal p.1 * (Matrix.of p.2)ᵀ := by
  apply Continuous.measurable
  fun_prop

theorem measurable_noisy (ε : ℝ) :
    Measurable fun p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ ↦
      (1 - ε) • p.1 + ε • p.2 := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fun_prop

theorem measurable_conj (O : Matrix (Fin n) (Fin n) ℝ) :
    Measurable fun M : Matrix (Fin n) (Fin n) ℝ ↦ O * M * Oᵀ := by
  apply Continuous.measurable
  fun_prop

/-- The entries of a matrix: the `n²` coordinates at which the polynomials of the low-degree
advantage are evaluated. -/
def entries (M : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℝ := fun p ↦ M p.1 p.2

/-! ### Rational matrices as inputs -/

/-- The rational matrix `X` **approximates** the real matrix `M`: every entry of `X` is within
`1/n` of the entry of `M`. Then `X - M` has Frobenius norm, hence operator norm, at most `1`. -/
def Approximates (X : Matrix (Fin n) (Fin n) ℚ) (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, |(X i j : ℝ) - M i j| ≤ 1 / n

/-- An input of the algorithm of Theorem 3.1: a number `n` and an `n × n` rational matrix. -/
abbrev RatMatrix := (n : ℕ) × Matrix (Fin n) (Fin n) ℚ

/-- The rows of a rational matrix. -/
def rows (X : Matrix (Fin n) (Fin n) ℚ) : List (List ℚ) :=
  List.ofFn fun i ↦ List.ofFn (X i)

/-- A rational matrix is encoded as `n` in binary followed by its rows, as lists of rationals. -/
def encRatMatrix : RatMatrix ↪ List Bool :=
  ⟨fun x ↦ encPair encNat (encList (encList encRat)) (x.1, rows x.2), by
    rintro ⟨n, X⟩ ⟨n', X'⟩ h
    have h' := (encPair encNat (encList (encList encRat))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, h2⟩ := h'
    have h3 := List.ofFn_injective h2
    have : X = X' := by
      ext i j
      exact congrFun (List.ofFn_injective (congrFun h3 i)) j
    rw [this]⟩

/-! ### Algorithms and events -/

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an input `x`, halts with output `A x` within `c (T x + |x| + 1)`
steps and cells, for a constant `c`, where `|x|` is the length of the encoded input. The machine is
deterministic: it has no coins, so the time bound `T` cannot pass it advice. -/
def RunsInTime {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (A : α → β)
    (T : α → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A encIn encOut
    (fun x ↦ c * (T x + (encIn x).length + 1)) (fun x ↦ c * (T x + (encIn x).length + 1))

/-- `Good` holds **with probability at least `p`** under `μ`: there is a measurable event of
probability at least `p` on which `Good` holds. `Good` itself need not be measurable (for
instance, "the algorithm is correct on every rational approximation of the matrix"); this is a
lower bound on its inner probability. -/
def ProbAtLeast {α : Type} [MeasurableSpace α] (μ : Measure α) (p : ℝ) (Good : α → Prop) : Prop :=
  ∃ E : Set α, MeasurableSet E ∧ p ≤ (μ E).toReal ∧ ∀ x ∈ E, Good x

end BHJK25
