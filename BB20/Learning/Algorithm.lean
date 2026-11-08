module

public import BB20.Model
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Finset.Sort

/-!
# The structure-learning algorithms

The algorithms of [BB20, Theorems 6 and 11], as Lean functions on `BB20.Input`, parametrized by
the computation of their thresholds (`thr`). Their correctness is proved for every threshold
function meeting `BB20.ThrSpec6` / `BB20.ThrSpec11` (`BB20/Learning/Correct.lean`), and their
running time for every polynomial-time threshold function (`BB20/Machine/`). The definitions here
are the specification the Turing machines compute; they are not efficient themselves (the
empirical proxy sums over all `2ⁿ` configurations).

* `BB20.empMarg`, `BB20.empNu`: the empirical marginals and the empirical proxy `ν̂_{u,I|S}` of a
  sample `X : Fin M → Config n`, the same formulas as `BB20.RBM.marg` and `BB20.RBM.nu` with the
  empirical law in place of the observed law.
* `BB20.empMargL`, `BB20.empNuL`: the same, computed as rationals from the samples as the algorithm
  reads them (lists of bits) and variables as natural numbers.
* `BB20.candList`: the candidate sets at `u` given `S`, in the order of `List.sublists`.
* `BB20.grow`, `BB20.greedy`: Step 2 of the algorithm, adding the first candidate `I` with
  `ν̂_{u,I|S} > t` while there is one.
* `BB20.alg6`, `BB20.alg11`: the algorithms, with the pruning steps of Theorems 6 and 11.
-/

@[expose] public section

namespace BB20

open Finset

variable {n : ℕ}

/-! ### Empirical marginals and the empirical proxy -/

open Classical in
/-- The empirical probability that the samples agree with `z` on `A`. -/
noncomputable def empMarg {M : ℕ} (X : Fin M → Config n) (A : Finset (Fin n)) (z : Config n) :
    ℝ :=
  ((univ.filter fun k : Fin M ↦ ∀ i ∈ A, X k i = z i).card : ℝ) / M

/-- The empirical proxy `ν̂_{u,I|S}`: `BB20.RBM.nu` with the empirical marginals. -/
noncomputable def empNu {M : ℕ} (X : Fin M → Config n) (u : Fin n) (I S : Finset (Fin n)) : ℝ :=
  (∑ z : Config n, |empMarg X (insert u (I ∪ S)) z -
    empMarg X (insert u S) z * empMarg X (I ∪ S) z / empMarg X S z|) / 2 ^ (n - S.card)

/-- Bit `i` of sample `k`, `false` if missing. -/
def bitAt (samples : List (List Bool)) (k i : ℕ) : Bool := (samples.getD k []).getD i false

/-- The empirical probability, from the samples as lists of bits, that variables in `A` (numbers
below `n`) agree with `z`. -/
def empMargL (samples : List (List Bool)) (n : ℕ) (A : Finset ℕ) (z : Fin n → Bool) : ℚ :=
  ((List.range samples.length).countP fun k ↦
      decide (∀ i ∈ A, ∀ h : i < n, bitAt samples k i = z ⟨i, h⟩) : ℚ) / samples.length

/-- The empirical proxy `ν̂_{u,I|S}` computed from the samples as lists of bits. -/
def empNuL (samples : List (List Bool)) (n u : ℕ) (I S : Finset ℕ) : ℚ :=
  (∑ z : Fin n → Bool, |empMargL samples n (insert u (I ∪ S)) z -
    empMargL samples n (insert u S) z * empMargL samples n (I ∪ S) z /
      empMargL samples n S z|) / 2 ^ (n - S.card)

/-! ### The greedy step -/

/-- The candidate sets at `u` given `S`: the nonempty sets of at most `k` numbers below `n`, other
than `u` and the elements of `S`, as increasing lists in the order of `List.sublists`. -/
def candList (n u k : ℕ) (S : Finset ℕ) : List (List ℕ) :=
  (((List.range n).filter fun i ↦ i ≠ u ∧ i ∉ S).sublists).filter
    fun l ↦ l ≠ [] ∧ l.length ≤ k

/-- One greedy step at `u` with threshold `t`: add the first candidate `I` with `ν̂_{u,I|S} > t`,
if there is one. `nh I S` is the proxy `ν̂_{u,I|S}`. -/
def grow (nh : Finset ℕ → Finset ℕ → ℚ) (n u k : ℕ) (t : ℚ) (S : Finset ℕ) : Finset ℕ :=
  match (candList n u k S).find? (fun l ↦ decide (t < nh l.toFinset S)) with
  | some l => S ∪ l.toFinset
  | none => S

/-- Step 2: `n` greedy steps from `∅` (each step that adds something adds a new number below `n`,
so after `n` steps no candidate is left above the threshold). -/
def greedy (nh : Finset ℕ → Finset ℕ → ℚ) (n u k : ℕ) (t : ℚ) : Finset ℕ :=
  (grow nh n u k t)^[n] ∅

/-! ### The algorithms -/

/-- The input is well formed: there is at least one sample, and every sample has `n` bits. -/
def WellFormed (x : Input) : Prop :=
  x.samples ≠ [] ∧ ∀ l ∈ x.samples, l.length = x.n

instance (x : Input) : Decidable (WellFormed x) := by
  unfold WellFormed
  infer_instance

/-- The algorithm of [BB20, Theorem 6], with threshold `t = thr x` (none: give up). At each `u`:
greedy steps with threshold `t`, then keep the `i ∈ S` with `ν̂_{u,{i}|S ∖ {i}} > t`. -/
def alg6 (thr : Input → Option ℚ) (x : Input) : Output :=
  if WellFormed x then
    match thr x with
    | none => []
    | some t => (List.range x.n).map fun u ↦
        let nh := fun I S ↦ empNuL x.samples x.n u I S
        let S := greedy nh x.n u (2 ^ x.s) t
        (S.filter fun i ↦ t < nh {i} (S.erase i)).sort (· ≤ ·)
  else []

/-- The algorithm of [BB20, Theorem 11], with thresholds `(t₂, t₃) = thr x` (none: give up). At
each `u`: greedy steps with threshold `t₂`, then keep the `i ∈ S` such that some candidate `I` at
`u` given `S ∖ {i}` has `ν̂_{u,I|S ∖ {i}} > t₃`. -/
def alg11 (thr : Input → Option (ℚ × ℚ)) (x : Input) : Output :=
  if WellFormed x then
    match thr x with
    | none => []
    | some (t₂, t₃) => (List.range x.n).map fun u ↦
        let nh := fun I S ↦ empNuL x.samples x.n u I S
        let S := greedy nh x.n u (2 ^ x.s) t₂
        (S.filter fun i ↦ ((candList x.n u (2 ^ x.s) (S.erase i)).any fun l ↦
          decide (t₃ < nh l.toFinset (S.erase i)))).sort (· ≤ ·)
  else []

/-! ### What the thresholds must satisfy -/

/-- The threshold of Theorem 6 is within `[0.9 τ', τ']` whenever the sample size of Theorem 6 is
met (for `n ≥ 1` and `ω ≤ 1`). It may depend on the samples only through their number. -/
def ThrSpec6 (thr : Input → Option ℚ) : Prop :=
  ∀ (n : ℕ) (samples : List (List Bool)) (α γ : ℚ) (d D s : ℕ) (ω : ℝ),
    1 ≤ n → 0 < α → 0 < γ → 1 ≤ d → 0 < ω → ω ≤ 1 →
    sampleSize α γ d D s n ω ≤ samples.length →
    ∃ t : ℚ, thr ⟨n, samples, α, γ, d, D, s⟩ = some t ∧
      9 / 10 * tauPrime α γ d D s ≤ t ∧ (t : ℝ) ≤ tauPrime α γ d D s

/-- The thresholds of Theorem 11 are within `[0.9 τ'(ζ η), τ'(ζ η)]` and `[0.9 τ'(ζ), τ'(ζ)]`
whenever the sample size of Theorem 11 is met (for `n ≥ 1`, `D ≥ 1` and `ω ≤ 1`). -/
def ThrSpec11 (thr : Input → Option (ℚ × ℚ)) : Prop :=
  ∀ (n : ℕ) (samples : List (List Bool)) (ζ γ : ℚ) (d D s : ℕ) (ω : ℝ),
    1 ≤ n → 0 < ζ → 0 < γ → 1 ≤ d → 1 ≤ D → 0 < ω → ω ≤ 1 →
    sampleSize (ζ * eta γ D s) γ d D s n ω ≤ samples.length →
    ∃ t₂ t₃ : ℚ, thr ⟨n, samples, ζ, γ, d, D, s⟩ = some (t₂, t₃) ∧
      9 / 10 * tauPrime (ζ * eta γ D s) γ d D s ≤ t₂ ∧
      (t₂ : ℝ) ≤ tauPrime (ζ * eta γ D s) γ d D s ∧
      9 / 10 * tauPrime ζ γ d D s ≤ t₃ ∧ (t₃ : ℝ) ≤ tauPrime ζ γ d D s

end BB20
