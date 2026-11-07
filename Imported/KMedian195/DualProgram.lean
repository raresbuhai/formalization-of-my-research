/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`,
file `bound-195/KMedian195/DualProgram.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`).
-/
module

public import KMedian195.Basic

@[expose] public section

namespace KMedian195

/-- A lower-triangular `0/1` bidding pattern `b_{i,j}`. -/
structure BiddingMatrix (n : ℕ) where
  toFun : Idx n → Idx n → Bool
  upper_zero : ∀ {i j : Idx n}, i < j → toFun i j = false

instance : CoeFun (BiddingMatrix n) (fun _ => Idx n → Idx n → Bool) := ⟨BiddingMatrix.toFun⟩

namespace BiddingMatrix

/-- Real-valued version of the binary coefficient `b_{i,j}`. -/
def coeff (b : BiddingMatrix n) (i j : Idx n) : ℝ :=
  if b i j then 1 else 0

@[simp] theorem coeff_eq_one {b : BiddingMatrix n} {i j : Idx n} (h : b i j = true) :
    b.coeff i j = 1 := by
  simp [coeff, h]

@[simp] theorem coeff_eq_zero {b : BiddingMatrix n} {i j : Idx n} (h : b i j = false) :
    b.coeff i j = 0 := by
  simp [coeff, h]

@[simp] theorem coeff_eq_zero_of_lt {b : BiddingMatrix n} {i j : Idx n} (hij : i < j) :
    b.coeff i j = 0 := by
  simp [coeff, b.upper_zero hij]

theorem coeff_nonneg (b : BiddingMatrix n) (i j : Idx n) : 0 ≤ b.coeff i j := by
  by_cases h : b i j
  · simp [coeff, h]
  · simp [coeff, h]

end BiddingMatrix

/-- A single inner dual LP from Definition `frdual`, determined by `n`, `M`, and `b`. -/
structure DualProgram (n : ℕ) where
  Mcoeff : ℝ
  bidding : BiddingMatrix n

namespace DualProgram

def Mcoeffmone (P : DualProgram n) : ℝ :=
  P.Mcoeff - 1

def bid (P : DualProgram n) (i j : Idx n) : ℝ :=
  P.bidding.coeff i j

@[simp] theorem bid_eq_zero_of_lt (P : DualProgram n) {i j : Idx n} (hij : i < j) :
    P.bid i j = 0 := by
  simpa [bid] using P.bidding.coeff_eq_zero_of_lt hij

end DualProgram

/-- The dual variables `(rho, \hat g, g, s, t)` from Definition `frdual`. -/
structure DualSolution (n : ℕ) where
  rho : ℝ
  hatG : Idx n → ℝ
  g : Idx n → Idx n → ℝ
  /--
  The corrected dual only uses the strict-lower entries `s_{i,j}` with `j < i`.
  We still store `s` as a total function for convenience, but all LP expressions below
  ignore the diagonal.
  -/
  s : Idx n → Idx n → ℝ
  t : Idx n → Idx n → ℝ

namespace DualSolution

def totalHatG (x : DualSolution n) : ℝ :=
  Finset.sum Finset.univ x.hatG

/-- The strict-lower part of `s`, with the diagonal discarded. -/
def strictS (x : DualSolution n) (i j : Idx n) : ℝ :=
  if j < i then x.s i j else 0

/-- Left-hand side of the paper's `(r_{j,i})` constraint. -/
def clientCredit (x : DualSolution n) (i j : Idx n) : ℝ :=
  Finset.sum (strictSuffixRange j) (fun q => x.g j q) +
    Finset.sum (intervalRange j i) (fun p => x.g p j + x.t p j - x.strictS p j)

/-- Left-hand side of the paper's `(m_i)` constraint. -/
def poolCredit (x : DualSolution n) (i : Idx n) : ℝ :=
  Finset.sum (prefixRange i) fun p =>
    Finset.sum (prefixRange p) fun j => x.strictS p j - x.t p j

/-- Right-hand side of the paper's `(d_j)` bound for column `j`. -/
def columnValue (x : DualSolution n) (P : DualProgram n) (j : Idx n) : ℝ :=
  P.Mcoeff * Finset.sum Finset.univ (fun i => x.g i j) +
    Finset.sum (strictSuffixRange j) (fun i => x.s i j) +
    Finset.sum (suffixRange j) (fun i => x.t i j)

def BoundedHatG (x : DualSolution n) : Prop :=
  x.totalHatG ≤ 1

def DominatesColumns (x : DualSolution n) : Prop :=
  ∀ i j, x.g i j ≤ x.hatG i

def SatisfiesClientConstraints (x : DualSolution n) (P : DualProgram n) : Prop :=
  ∀ ⦃j i : Idx n⦄, j ≤ i →
    x.clientCredit i j ≥
      P.bid i j - P.Mcoeffmone * Finset.sum (halfOpenIntervalRange j i) (fun p => P.bid p j)

def SatisfiesPoolConstraints (x : DualSolution n) : Prop :=
  ∀ i, 0 ≤ x.poolCredit i

def SatisfiesValueConstraints (x : DualSolution n) (P : DualProgram n) : Prop :=
  ∀ j, x.rho ≥ x.columnValue P j

def Nonnegative (x : DualSolution n) : Prop :=
  (∀ i, 0 ≤ x.hatG i) ∧
    (∀ i j, 0 ≤ x.g i j) ∧
    (∀ i j, 0 ≤ x.s i j) ∧
    (∀ i j, 0 ≤ x.t i j)

/-- Feasibility for one inner program of the family in Definition `frdual`. -/
def Feasible (x : DualSolution n) (P : DualProgram n) : Prop :=
  x.BoundedHatG ∧
    x.DominatesColumns ∧
    x.SatisfiesClientConstraints P ∧
    x.SatisfiesPoolConstraints ∧
    x.SatisfiesValueConstraints P ∧
    x.Nonnegative

/-- Existence of a feasible certificate of value at most `bound`. -/
def HasValueAtMost (P : DualProgram n) (bound : ℝ) : Prop :=
  ∃ x : DualSolution n, x.Feasible P ∧ x.rho ≤ bound

end DualSolution

/-- A formal target for the paper's global upper-bound statement over all `n ≥ 1`. -/
def FamilyUpperBound (Mcoeff bound : ℝ) : Prop :=
  ∀ n, n ≠ 0 → ∀ bidding : BiddingMatrix n,
    DualSolution.HasValueAtMost ({ Mcoeff := Mcoeff, bidding := bidding } : DualProgram n) bound

end KMedian195
