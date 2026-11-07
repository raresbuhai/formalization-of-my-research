module

public import BCFGJPSSV26.Basic.Raw
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Parameters

The algorithm of [BCFGJPSSV26b, Theorem 1.1] for a rational accuracy `ε` runs with the accuracy
`1/N`, for a power of two `N ≥ 256` computed from `ε` (`BCFGJPSSV26.Stable.accN`), with
`ε/512 ≤ 1/N < ε` for `ε ∈ (0, 1/200)`. All its parameters are explicit functions of `N`, of the
number `L ≥ 1/β` and of the instance (`BCFGJPSSV26.Stable.Par`), since the algorithm reads `N` as
part of its input. In the analysis, `N` comes with `201 ≤ N`
(`BCFGJPSSV26.Stable.Prm`) and `ε := 1/N` is a real number (`BCFGJPSSV26.Stable.Prm.eps`).

| name | value | role |
| --- | --- | --- |
| `Par.p N` | `24 N` | swap size of the local search |
| `Par.s N L` | `632 N L` | bound on the special clusters (`≥ 632/(εβ)`) |
| `Par.Gr N` | `10 N² + 1` | number of radius grid points |
| `Par.bits N ℓ` | `ℓ + 7 N` | bits per chunk of coins, `ℓ = |enc I|` |
| `Par.csChunks N L` | `6 s` | chunks of the client sampling (`2 s` iterations of `3`) |
| `Par.M₂ N L` | `20 s + 20` | steps (chunks) of the cluster sampling |
| `Par.Ctr N L k` | `6 s + M₂ + k` | chunks per trial |
| `Par.R N L` | `N^(200 s + 1)` | number of trials |
| `Par.e₁ N` | `10⁶ N²` | budget exponent: the budget is `stableTime e₁ (I, L)` |
| `eta` | `89/100` | substitution factor `η` |
| `aW` | `3/25` | win-win weight `a` |
| `Prm.q₁` | `1/(440 N⁸)` | per-iteration success of the client sampling |
| `Prm.q₂` | `1/(12 N³)` | per-step success of the cluster sampling |
| `Prm.q L` | `N^(-200 s)` | per-trial success |
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

/-! ### Parameters of the algorithm -/

namespace Par

/-- The swap size `p = 24 N` of the local search. -/
def p (N : ℕ) : ℕ := 24 * N

/-- The bound `s = 632 N L` on the number of special clusters. -/
def s (N L : ℕ) : ℕ := 632 * N * L

/-- The number `10 N² + 1` of radius grid points. -/
def Gr (N : ℕ) : ℕ := 10 * N ^ 2 + 1

/-- The number of bits per chunk of coins, `|enc I| + 7 N`. -/
def bits (N len : ℕ) : ℕ := len + 7 * N

/-- The chunks read by the client sampling: `2 s` iterations of three chunks. -/
def csChunks (N L : ℕ) : ℕ := 6 * s N L

/-- The steps of the cluster sampling, one chunk each. -/
def M₂ (N L : ℕ) : ℕ := 20 * s N L + 20

/-- The chunks of one trial: client sampling, cluster sampling, then one coloring bit for each of
at most `k` centers. -/
abbrev Ctr (N L k : ℕ) : ℕ := 6 * s N L + M₂ N L + k

/-- The number of trials, `N^(200 s + 1)`. -/
def R (N L : ℕ) : ℕ := N ^ (200 * s N L + 1)

/-- The budget exponent `e₁ = 10⁶ N²`. -/
def e₁ (N : ℕ) : ℕ := 10 ^ 6 * N ^ 2

/-- The budget `stableTime e₁ (I, L) = 2^(e₁ L) (|I| + 2)^(e₁)`: every loop and enumeration of the
algorithm is cut at it. -/
def budget (N : ℕ) (I : Instance) (L : ℕ) : ℕ := stableTime (e₁ N) (I, L)

/-- The number of coins the algorithm reads: `R` trials of `Ctr` chunks of `bits` bits. -/
def coinLen (N : ℕ) (I : Instance) (L : ℕ) : ℕ :=
  R N L * Ctr N L I.k * bits N (encInstance I).length

end Par

/-- The substitution factor `η = 89/100`. -/
noncomputable def eta : ℝ := 89 / 100

/-- The weight `a = 3/25` of the local search in the win-win argument. -/
noncomputable def aW : ℝ := 3 / 25

/-! ### The accuracy -/

/-- The accuracy parameter: `N ≥ 201`, and `ε = 1/N`. -/
structure Prm where
  /-- The inverse accuracy. -/
  N : ℕ
  hN : 201 ≤ N

namespace Prm

variable (P : Prm)

/-- The accuracy `ε = 1/N`. -/
noncomputable def eps : ℝ := 1 / P.N

/-- The per-iteration success probability of the client sampling. -/
noncomputable def q₁ : ℝ := 1 / (440 * (P.N : ℝ) ^ 8)

/-- The per-step success probability of the cluster sampling. -/
noncomputable def q₂ : ℝ := 1 / (12 * (P.N : ℝ) ^ 3)

/-- The per-trial success probability `N^(-200 s)`. -/
noncomputable def q (L : ℕ) : ℝ := 1 / (P.N : ℝ) ^ (200 * Par.s P.N L)

theorem N_pos : 0 < P.N := by have := P.hN; omega

theorem N_pos' : (0 : ℝ) < P.N := by exact_mod_cast P.N_pos

theorem N_ge : (201 : ℝ) ≤ P.N := by exact_mod_cast P.hN

theorem eps_pos : 0 < P.eps := by
  have := P.N_pos'
  unfold eps
  positivity

theorem eps_le : P.eps ≤ 1 / 201 := by
  unfold eps
  exact one_div_le_one_div_of_le (by norm_num) P.N_ge

theorem eps_lt : P.eps < 1 / 200 := P.eps_le.trans_lt (by norm_num)

theorem N_mul_eps : (P.N : ℝ) * P.eps = 1 := by
  unfold eps
  field_simp [P.N_pos'.ne']

/-- `s ≥ 632/(εβ)` when `L ≥ 1/β`. -/
theorem s_ge {β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 1 / β ≤ L) :
    632 / (P.eps * β) ≤ Par.s P.N L := by
  have hN := P.N_pos'
  unfold Par.s eps
  push_cast
  rw [div_le_iff₀ (by positivity)]
  have h : 1 ≤ (L : ℝ) * β := by rwa [div_le_iff₀ hβ] at hL
  have : (632 : ℝ) * P.N * L * (1 / P.N * β) = 632 * (L * β) := by field_simp
  rw [this]
  linarith

/-- `L ≥ 1`, since `L ≥ 1/β > 0`. -/
theorem one_le_L {β : ℝ} (hβ : 0 < β) {L : ℕ} (hL : 1 / β ≤ L) : 1 ≤ L := by
  have h : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  exact_mod_cast h

end Prm

end BCFGJPSSV26.Stable
