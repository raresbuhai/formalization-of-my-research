module

public import BGHKLMM26.Robust
public import BGHKLMM26.Numerics
public import Background.SumOfSquares.Algorithm.PDTestRat

/-!
# The algorithm

[BGHKLMM26, Algorithm 1] as a function of the instance `I` and the coins `r`
(`BGHKLMM26.Alg.alg`), with a precision constant `Q₀`:

1. **Parameters**: `D = max 2 (max degree)`, `L = ⌈log₂ D⌉`, `k = ⌊√(16L + 4)⌋ + 1`, the smoothing
   `η = (k² - 1)/(k² + 1)` (so `√(1 - η) ≥ 1/k`), the shift `λ = 1/(100k)`, and the threshold
   `ε = 1/(10⁶ k² D)`. With `Z = n + m + 3`, the solver's accuracies are `2^-(Z + Q₀)`, the
   Gaussians are read on `[-R, R]` for `R = Z² 2^Q₀`, and the fixed-point precision is
   `p = 4 (Z + Q₀)²`.
2. **The SDP** with the sum-of-squares solver (`BGHKLMM26.SDP.problem`), its moments `M` rescaled to
   a positive definite matrix `A` with unit diagonal (`BGHKLMM26.Factor.rescaled`).
3. **The window** `T = {c | 1/2 < b A_ij < 4/5}` and the **branch**: hyperplane rounding if
   `SDP_N ≥ ε SDP`, else the shifted rounding — both exact rational tests.
4. **The coefficients** `cₖ, Dₖ` of the vectors with Gram matrix `A`, from the positive definiteness
   test on the integer matrix `A` scaled by its common denominator.
5. **Gaussians**: block `k` of `T` coins is the cell of `gₖ` (`BGHKLMM26.Alg.algC` is the algorithm
   as a function of the cells); `ĝₖ` recovers `gₖ` by bisection on `Φ`.
6. **Projections** `ξₖ = ∑_{l<k} cₖₗ ξₗ + √Dₖ gₖ`, rounded to multiples of `2^-p`.
7. **The output**: `[ξᵢ ≥ 0]`, or `[ξᵢ + λ fᵢ ≥ 0]` with `fᵢ = ∑ₑ pₑ (2 Φ(η hₑ / √(1 - η²)) - 1)`
   and `hₑ = (b ξⱼ - ρ ξᵢ) / √(1 - ρ²)`.
-/

@[expose] public section

namespace BGHKLMM26.Alg

open SoS SoS.Solver SoS.Loop

/-! ### Parameters -/

/-- The largest degree of a variable. -/
def maxDeg (I : Instance) : ℕ := ((List.range I.1).map (degree I)).foldr max 0

/-- `D = max 2 (max degree)`. -/
def dPar (I : Instance) : ℕ := max 2 (maxDeg I)

/-- `L = ⌈log₂ D⌉ ≥ 1`. -/
def lPar (I : Instance) : ℕ := Nat.clog 2 (dPar I)

/-- `k = ⌊√(16 L + 4)⌋ + 1`, so `k² > 16 L + 4`. -/
def kPar (I : Instance) : ℕ := Nat.sqrt (16 * lPar I + 4) + 1

/-- The smoothing `η = (k² - 1)/(k² + 1)`. -/
def etaQ (I : Instance) : ℚ := ((kPar I : ℚ) ^ 2 - 1) / ((kPar I : ℚ) ^ 2 + 1)

/-- `η / √(1 - η²) = (k² - 1)/(2k)`. -/
def ratioQ (I : Instance) : ℚ := ((kPar I : ℚ) ^ 2 - 1) / (2 * kPar I)

/-- The shift `λ = 1/(100 k)`. -/
def tQ (I : Instance) : ℚ := 1 / (100 * kPar I)

/-- The threshold `ε = 1/(10⁶ k² D)` of the branch. -/
def epsQ (I : Instance) : ℚ := 1 / (10 ^ 6 * (kPar I : ℚ) ^ 2 * dPar I)

/-- The size `Z = n + m + 3` for `n` variables and `m` constraints, at most `|I| + 2`. -/
def zPar (I : Instance) : ℕ := I.1 + I.2.length + 3

/-- The precision exponent `Q = Z + Q₀`. -/
def qPar (Q₀ : ℕ) (I : Instance) : ℕ := zPar I + Q₀

/-! ### The SDP -/

/-- The total weight, as a rational. -/
def wTot (I : Instance) : ℚ := (I.2.map fun c ↦ c.2.2).sum

/-- The solver's accuracies `η, γ` and the regularization `τ`. -/
def etaS (Q₀ : ℕ) (I : Instance) : ℚ := 1 / 2 ^ qPar Q₀ I

def gammaS (Q₀ : ℕ) (I : Instance) : ℚ :=
  (if wTot I = 0 then 1 else min (wTot I) 1) / 2 ^ qPar Q₀ I

def tauS (Q₀ : ℕ) (I : Instance) : ℚ := 1 / 2 ^ qPar Q₀ I

/-- The solver's input. -/
def solverInput (Q₀ : ℕ) (I : Instance) : SoS.Solver.Input :=
  (SDP.problem I, etaS Q₀ I, gammaS Q₀ I)

/-- The solver's output. -/
def solverOut (Q₀ : ℕ) (I : Instance) : RawPoly :=
  SoS.Core.core (solverInput Q₀ I, budget (solverInput Q₀ I))

/-- The rescaled moments `A`. -/
def aQ (Q₀ : ℕ) (I : Instance) (i j : ℕ) : ℚ :=
  Factor.rescaled I.1 (SDP.momentsOf I.1 (solverOut Q₀ I)) (tauS Q₀ I) i j

/-- `ρ = b Aᵢⱼ` of a constraint. -/
def rhoQ (Q₀ : ℕ) (I : Instance) (c : Constraint) : ℚ :=
  SDP.objective.bsignQ c.2.1 * aQ Q₀ I c.1.1 c.1.2

/-- Whether a constraint is in the window `1/2 < ρ < 4/5`. -/
def inWin (Q₀ : ℕ) (I : Instance) (c : Constraint) : Bool :=
  decide (1 / 2 < rhoQ Q₀ I c ∧ rhoQ Q₀ I c < 4 / 5)

/-- The window `T`. -/
def winList (Q₀ : ℕ) (I : Instance) : List Constraint := I.2.filter (inWin Q₀ I)

/-- The SDP value `∑ w (1 + ρ)/2` and its part outside the window. -/
def sdpQ (Q₀ : ℕ) (I : Instance) : ℚ := (I.2.map fun c ↦ c.2.2 * ((1 + rhoQ Q₀ I c) / 2)).sum

def sdpOutQ (Q₀ : ℕ) (I : Instance) : ℚ :=
  (I.2.map fun c ↦ if inWin Q₀ I c then 0 else c.2.2 * ((1 + rhoQ Q₀ I c) / 2)).sum

/-- **The branch** [BGHKLMM26, Algorithm 1, line 9]: hyperplane rounding if `SDP_N ≥ ε SDP`. -/
def branch0 (Q₀ : ℕ) (I : Instance) : Bool := decide (epsQ I * sdpQ Q₀ I ≤ sdpOutQ Q₀ I)

/-! ### The coefficients of the vectors -/

/-- The rows of `A`. -/
def rowsQ (Q₀ : ℕ) (I : Instance) : List (List ℚ) :=
  (List.range I.1).map fun i ↦ (List.range I.1).map fun j ↦ aQ Q₀ I i j

/-- `A` scaled to integers. -/
def zRows (Q₀ : ℕ) (I : Instance) : List (List ℤ) := PDTestRat.scale (rowsQ Q₀ I)

/-- `det B` of the leading block of size `k`. -/
def detB (Q₀ : ℕ) (I : Instance) (k : ℕ) : ℤ :=
  Cslib.Circuits.Rational.detRows (PDTestRows.block (zRows Q₀ I) k)

/-- `cₖ = adj(B) b / det B`. -/
def coefL (Q₀ : ℕ) (I : Instance) (k : ℕ) : List ℚ :=
  (PDTestRows.cof (zRows Q₀ I) k).map fun u : ℤ ↦ (u : ℚ) / detB Q₀ I k

/-- `Dₖ = s / det B` (with the scale of `A` divided out). -/
def diagL (Q₀ : ℕ) (I : Instance) (k : ℕ) : ℚ :=
  (PDTestRows.schur (zRows Q₀ I) k : ℚ) /
    (detB Q₀ I k * PDTestRat.commonDen (rowsQ Q₀ I))

/-! ### Gaussians from coins -/

/-- The range `R = Z² 2^Q₀` of the Gaussians. -/
def rPar (Q₀ : ℕ) (I : Instance) : ℕ := zPar I ^ 2 * 2 ^ Q₀

/-- The fixed-point precision `p = 4 (Z + Q₀)²`. -/
def pPar (Q₀ : ℕ) (I : Instance) : ℕ := 4 * (zPar I + Q₀) ^ 2

/-- The precision `T = (R + 1)² + p + 8` of the cells and of `π`. -/
def tPar (Q₀ : ℕ) (I : Instance) : ℕ := (rPar Q₀ I + 1) ^ 2 + pPar Q₀ I + 8

/-- The number of terms of `Φ`'s series. -/
def nSer (Q₀ : ℕ) (I : Instance) : ℕ := 30000 * (rPar Q₀ I + 1) ^ 4 + tPar Q₀ I

/-- The number of bisection steps. -/
def kBis (Q₀ : ℕ) (I : Instance) : ℕ := pPar Q₀ I + rPar Q₀ I + 2

/-- The cell read from block `k` of `B` coins: the bit `i` has weight `2^i`. -/
def cellOfCoins (B : ℕ) (r : List Bool) (k : ℕ) : ℕ :=
  ((List.range B).map fun i ↦ if r.getD (k * B + i) false then 2 ^ i else 0).sum

/-- `ĝₖ`: the Gaussian recovered from its cell. -/
def gHat (Q₀ : ℕ) (I : Instance) (cells : ℕ → ℕ) (k : ℕ) : ℚ :=
  Num.cellInv (tPar Q₀ I) (nSer Q₀ I) (kBis Q₀ I) (tPar Q₀ I) (rPar Q₀ I + 1) (cells k)

/-! ### Projections -/

/-- The clamp `2^p` of the projections. -/
def clampPar (Q₀ : ℕ) (I : Instance) : ℚ := 2 ^ pPar Q₀ I

/-- The new projection `ξₖ = ∑_{l<k} cₖₗ ξₗ + √Dₖ ĝₖ`, rounded and clamped, from the previous
ones. -/
def xiNext (Q₀ : ℕ) (I : Instance) (cells : ℕ → ℕ) (acc : List ℚ) (k : ℕ) : ℚ :=
  clamp (clampPar Q₀ I) (roundP (pPar Q₀ I)
    (((coefL Q₀ I k).zipWith (· * ·) acc).sum +
      sqrtP (pPar Q₀ I) (diagL Q₀ I k) * gHat Q₀ I cells k))

/-- One step of the projections. -/
def xiStep (Q₀ : ℕ) (I : Instance) (cells : ℕ → ℕ) (acc : List ℚ) (k : ℕ) : List ℚ :=
  acc ++ [xiNext Q₀ I cells acc k]

/-- The projections `ξ̂₀, …, ξ̂ₙ₋₁`. -/
def xiHat (Q₀ : ℕ) (I : Instance) (cells : ℕ → ℕ) : List ℚ :=
  (List.range I.1).foldl (xiStep Q₀ I cells) []

/-! ### The output -/

/-- `ĥₑ = (b ξⱼ - ρ ξᵢ) / √(1 - ρ²)` for the out-edge `e = (j, b, w)` of `i`. -/
def hHat (Q₀ : ℕ) (I : Instance) (xi : List ℚ) (i : ℕ) (e : ℕ × Bool × ℚ) : ℚ :=
  let ρ := SDP.objective.bsignQ e.2.1 * aQ Q₀ I i e.1
  (SDP.objective.bsignQ e.2.1 * xi.getD e.1 0 - ρ * xi.getD i 0) /
    sqrtP (pPar Q₀ I) (1 - ρ ^ 2)

/-- The weighted degree in the window. -/
def wDegQ (Q₀ : ℕ) (I : Instance) (i : ℕ) : ℚ :=
  ((outEdges (winList Q₀ I) i).map fun e ↦ e.2.2).sum

/-- `f̂ᵢ = ∑ₑ (wₑ/Wᵢ) (2 Φ(η ĥₑ / √(1 - η²)) - 1)`. -/
def fHat (Q₀ : ℕ) (I : Instance) (xi : List ℚ) (i : ℕ) : ℚ :=
  ((outEdges (winList Q₀ I) i).map fun e ↦ e.2.2 / wDegQ Q₀ I i *
    (2 * Num.phiQ (tPar Q₀ I) (nSer Q₀ I) (ratioQ I * hHat Q₀ I xi i e) - 1)).sum

/-- The output from the cells of the Gaussians. -/
def algC (Q₀ : ℕ) (I : Instance) (cells : ℕ → ℕ) : List Bool :=
  let xi := xiHat Q₀ I cells
  if branch0 Q₀ I then (List.range I.1).map fun i ↦ decide (0 ≤ xi.getD i 0)
  else (List.range I.1).map fun i ↦ decide (0 ≤ xi.getD i 0 + tQ I * fHat Q₀ I xi i)

/-- **The algorithm** with precision constant `Q₀`: block `k` of `T` coins is the cell of the
Gaussian `gₖ`. -/
def alg (Q₀ : ℕ) (x : Instance × List Bool) : List Bool :=
  algC Q₀ x.1 (cellOfCoins (tPar Q₀ x.1) x.2)

end BGHKLMM26.Alg
