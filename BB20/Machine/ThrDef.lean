module

public import BB20.Model
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Rat.Floor

/-!
# The threshold functions

Threshold functions for the algorithms of Theorems 6 and 11 (`BB20.Machine.thr6`,
`BB20.Machine.thr11`). They compute rational approximations from below of `τ'` (`BB20.tauPrime`)
within a factor `0.9` (`BB20/Machine/ThrSpec.lean`), in polynomial time
(`BB20/Machine/ThrPolyTime.lean`).

Write `E = e^{2γ}` and `K = d + D - 1`. Then
`τ' = R / (E (1 + E)^K)` with the rational `R = α² / (2 γ P)` and the integer
`P = d^{4d} 2^{d+1} max(1, C(D, d-1)) (4d)^{2^s} d^{2^s (2^s+1)}` (`BB20.Machine.Thr.facP`).
The thresholds replace `E` by an upper bound `Ê ≥ E` within a factor `(1 + 2/m!)^N`
(`BB20.Machine.Thr.expHi`): `e^{2γ} = (e^{2γ/N})^N` with `N = ⌊2γ⌋ + 1`, and `e^{2γ/N}` is
bounded by its Taylor polynomial of degree `m - 1` plus Lagrange's bound on the remainder
(`BB20.Machine.Thr.expUp`, `Real.exp_bound'`).

The parameters `d`, `D`, `2^s` and `⌊2γ⌋` are given in binary, so the integers above may be
exponentially long. Each of them is capped by `Λ = 2 ⌈log₂(|num α| + 1)⌉ + ⌈log₂(den γ + 1)⌉ + M`
(`BB20.Machine.Thr.cap`), `M` the number of samples: every factor of `E (1 + E)^K P` is at most
`α² M / (2γ) < 2^Λ` when the sample size is met, and then the caps change nothing. With the caps,
all the exponents and series lengths are polynomial in the input length.
-/

@[expose] public section

namespace BB20.Machine

open Finset

namespace Thr

/-- The cap `Λ = 2 |num α| + |den γ| + M` on the parameters, with `|·|` the length in binary and
`M` the number of samples. -/
def cap (x : Input) : ℕ := 2 * x.coeff.num.natAbs.size + x.gamma.den.size + x.samples.length

/-- `d`, capped by `Λ`. -/
def dc (x : Input) : ℕ := min (cap x) x.d

/-- `D`, capped by `Λ`. -/
def Dc (x : Input) : ℕ := min (cap x) x.D

/-- `2^s`, capped by `Λ`. -/
def pc (x : Input) : ℕ := min (cap x) (2 ^ min (cap x) x.s)

/-- `N = ⌊2γ⌋ + 1`, with `⌊2γ⌋` capped by `Λ`. -/
def Nc (x : Input) : ℕ := min (cap x) ⌊2 * x.gamma⌋₊ + 1

/-- `K = d + D - 1`, from the capped `d` and `D`. -/
def Kc (x : Input) : ℕ := dc x + Dc x - 1

/-- `P = d^{4d} 2^{d+1} max(1, C(D, d-1)) (4d)^p d^{p (p+1)}`, with `p = 2^s` in `τ'`. -/
def facP (d D p : ℕ) : ℕ :=
  d ^ (4 * d) * 2 ^ (d + 1) * max 1 (D.choose (d - 1)) * (4 * d) ^ p * d ^ (p * (p + 1))

/-- `Q = 6 · 2^{D + 2p} D^{p (p+2)}`, with `p = 2^s`: `η² = δ^D / Q`. -/
def facQ (D p : ℕ) : ℕ := 6 * 2 ^ (D + 2 * p) * D ^ (p * (p + 2))

/-- The upper bound `∑_{i < m} yⁱ / i! + y^m (m + 1) / (m! m)` on `e^y` for `0 ≤ y ≤ 1`
(`Real.exp_bound'`). -/
def expUp (y : ℚ) (m : ℕ) : ℚ :=
  ∑ i ∈ range m, y ^ i / (i.factorial : ℚ) + y ^ m * (m + 1) / (m.factorial * m)

/-- The upper bound `Ê = (expUp (2γ / N) m)^N` on `e^{2γ}` (for `2γ ≤ N`). -/
def expHi (γ : ℚ) (N m : ℕ) : ℚ := expUp (2 * γ / N) m ^ N

/-- `R / (E (1 + E)^K)`. -/
def val (R E : ℚ) (K : ℕ) : ℚ := R / (E * (1 + E) ^ K)

/-- `R = α² / (2 γ P)`, with the capped parameters. -/
def base (x : Input) : ℚ := x.coeff ^ 2 / (2 * x.gamma * facP (dc x) (Dc x) (pc x))

/-- `Ê` for Theorem 6. -/
def expHi6 (x : Input) : ℚ := expHi x.gamma (Nc x) (20 * Nc x * (Kc x + 1))

/-- `Ê` for Theorem 11. -/
def expHi11 (x : Input) : ℚ := expHi x.gamma (Nc x) (20 * Nc x * (Kc x + Dc x + 1))

end Thr

open Thr

/-- **The threshold of Theorem 6**: `R / (Ê (1 + Ê)^K)`, an approximation from below of
`τ' = R / (E (1 + E)^K)`. -/
def thr6 (x : Input) : Option ℚ := some (val (base x) (expHi6 x) (Kc x))

/-- **The thresholds of Theorem 11**: approximations from below of `τ'(ζ η) = η² τ'(ζ)` and of
`τ'(ζ)`. -/
def thr11 (x : Input) : Option (ℚ × ℚ) :=
  some (val (base x / facQ (Dc x) (pc x)) (expHi11 x) (Kc x + Dc x),
    val (base x) (expHi11 x) (Kc x))

end BB20.Machine
