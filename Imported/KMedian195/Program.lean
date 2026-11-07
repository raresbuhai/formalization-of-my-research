/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`, file `bound-195/Challenge.lean` (the statements
that the source checks with the comparator), without its two theorems, which are proved in
`Imported/KMedian195/Main.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`) and a module
docstring. The source defines these declarations twice, in `Challenge.lean` and in the development
(`Idx`, `suffixRange` in `Imported/KMedian195/Basic.lean`, the rest in
`Imported/KMedian195/FactorRevealingPrimal.lean`); here they are defined once, in this file, which
`Imported/KMedian195/Basic.lean` imports. The docstrings of `OriginalPrimalSolution` and
`OriginalPrimalUpperBound` are the development's.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Basic.Real.Basic

/-!
# The factor-revealing program

The factor-revealing program of Definition 4.1 in *A Better-than-2 Approximation for
k-Median*, Part I (arXiv:2610.18144), for the bid `β_γ(α, d) = [α - γ d]^+`.

Indices are shifted by one: the paper's clients `1, …, n` are `Idx n = Fin n`, and its times
`1, …, n + 1` are `TimeIdx n = Fin (n + 1)`. For a client `i : Idx n`, the paper's times `i` and
`i + 1` are `TimeIdx.ofIdx i` and `TimeIdx.succ i`, and the paper's time `n + 1` is
`TimeIdx.last n`. The paper's variable `r_{j,k}` exists only for `k ≥ j`; here `x.r j ℓ` is
defined for every `ℓ`, and the entries with `ℓ < TimeIdx.ofIdx j` occur only in the nonnegativity
constraint.
-/

@[expose] public section

namespace KMedian195

noncomputable section

/-- Finite client/time indices for the size-`n` factor-revealing programs. -/
abbrev Idx (n : ℕ) := Fin n

/-- Suffix `{i | j ≤ i}` used for lower-triangular ranges. -/
def suffixRange (j : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun i => j ≤ i

abbrev TimeIdx (n : ℕ) := Fin (n + 1)

namespace TimeIdx

def last (n : ℕ) : TimeIdx n := Fin.last n

def ofIdx (i : Idx n) : TimeIdx n := Fin.castSucc i

def succ (i : Idx n) : TimeIdx n := Fin.succ i

end TimeIdx

/-- The original factor-revealing variables from Definition 4.1,
specialized to the one-piece bid `β_γ(α,d) = [α - γ d]^+`. -/
structure OriginalPrimalSolution (n : ℕ) where
  d : Idx n → ℝ
  f : ℝ
  r : Idx n → TimeIdx n → ℝ

namespace OriginalPrimalSolution

variable {n : ℕ}

def bidValue (gamma alpha dist : ℝ) : ℝ :=
  max (alpha - gamma * dist) 0

def objective (gamma : ℝ) (x : OriginalPrimalSolution n) : ℝ :=
  (Finset.sum Finset.univ fun j =>
    Finset.sum (suffixRange j) (fun i =>
      bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
      x.r j (TimeIdx.last n)) - x.f

def Feasible (gamma : ℝ) (x : OriginalPrimalSolution n) : Prop :=
  (Finset.sum Finset.univ x.d = 1) ∧
    (∀ ⦃j i : Idx n⦄, j ≤ i → x.r j (TimeIdx.succ i) ≤ x.r j (TimeIdx.ofIdx i)) ∧
    (∀ ⦃j k : Idx n⦄, j < k →
      x.r k (TimeIdx.ofIdx k) ≤ x.r j (TimeIdx.ofIdx k) + x.d k + x.d j) ∧
    (∀ ⦃j k : Idx n⦄ ⦃ell : TimeIdx n⦄,
      j ≠ k →
      TimeIdx.ofIdx j < ell →
      TimeIdx.ofIdx k < ell →
      x.r j ell ≤ x.r k ell + x.d k + x.d j) ∧
    (∀ k : Idx n,
      Finset.sum Finset.univ (fun j =>
          if _h : j < k then
            bidValue gamma (x.r j (TimeIdx.ofIdx k)) (x.d j)
          else
            bidValue gamma (x.r k (TimeIdx.ofIdx k)) (x.d j)) ≤ x.f) ∧
    (0 ≤ x.f) ∧
    (∀ j, 0 ≤ x.d j) ∧
    (∀ j ell, 0 ≤ x.r j ell)

end OriginalPrimalSolution

/-- A direct upper-bound formulation for the specialized original FRP:
every feasible objective value is at most `bound`. -/
def OriginalPrimalUpperBound (gamma bound : ℝ) : Prop :=
  ∀ n, n ≠ 0 → ∀ x : OriginalPrimalSolution n,
    x.Feasible gamma → x.objective gamma ≤ bound

end

end KMedian195
