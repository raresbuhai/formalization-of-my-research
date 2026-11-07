module

public import BGHKLMM26.Algorithm

/-!
# The algorithm with the solver's budget as an input

The functions of `BGHKLMM26/Algorithm.lean` that depend on the solver's output, with that output
`out` as an argument, and `BGHKLMM26.Alg.run`: the algorithm on an instance, coins and a budget
`L` in unary, which runs the solver with budget `L`. With the solver's own budget it is the
algorithm (`BGHKLMM26.Alg.alg_eq_run`), by definition. This is the form whose running time is
certified, as for [BKS23] in this repository.
-/

@[expose] public section

namespace BGHKLMM26.Alg.O

open SoS SoS.Solver SoS.Loop

variable (Q₀ : ℕ) (I : Instance) (out : RawPoly)

/-- The rescaled moments `A` of the solver's output `out`. -/
def aQ (i j : ℕ) : ℚ := Factor.rescaled I.1 (SDP.momentsOf I.1 out) (tauS Q₀ I) i j

def rhoQ (c : Constraint) : ℚ := SDP.objective.bsignQ c.2.1 * aQ Q₀ I out c.1.1 c.1.2

def inWin (c : Constraint) : Bool :=
  decide (1 / 2 < rhoQ Q₀ I out c ∧ rhoQ Q₀ I out c < 4 / 5)

def winList : List Constraint := I.2.filter (inWin Q₀ I out)

def sdpQ : ℚ := (I.2.map fun c ↦ c.2.2 * ((1 + rhoQ Q₀ I out c) / 2)).sum

def sdpOutQ : ℚ :=
  (I.2.map fun c ↦ if inWin Q₀ I out c then 0 else c.2.2 * ((1 + rhoQ Q₀ I out c) / 2)).sum

def branch0 : Bool := decide (epsQ I * sdpQ Q₀ I out ≤ sdpOutQ Q₀ I out)

def rowsQ : List (List ℚ) :=
  (List.range I.1).map fun i ↦ (List.range I.1).map fun j ↦ aQ Q₀ I out i j

def zRows : List (List ℤ) := PDTestRat.scale (rowsQ Q₀ I out)

def detB (k : ℕ) : ℤ := Cslib.Circuits.Rational.detRows (PDTestRows.block (zRows Q₀ I out) k)

def coefL (k : ℕ) : List ℚ :=
  (PDTestRows.cof (zRows Q₀ I out) k).map fun u : ℤ ↦ (u : ℚ) / detB Q₀ I out k

def diagL (k : ℕ) : ℚ :=
  (PDTestRows.schur (zRows Q₀ I out) k : ℚ) /
    (detB Q₀ I out k * PDTestRat.commonDen (rowsQ Q₀ I out))

def xiNext (cells : ℕ → ℕ) (acc : List ℚ) (k : ℕ) : ℚ :=
  clamp (clampPar Q₀ I) (roundP (pPar Q₀ I)
    (((coefL Q₀ I out k).zipWith (· * ·) acc).sum +
      sqrtP (pPar Q₀ I) (diagL Q₀ I out k) * gHat Q₀ I cells k))

def xiStep (cells : ℕ → ℕ) (acc : List ℚ) (k : ℕ) : List ℚ :=
  acc ++ [xiNext Q₀ I out cells acc k]

def xiHat (cells : ℕ → ℕ) : List ℚ := (List.range I.1).foldl (xiStep Q₀ I out cells) []

def hHat (xi : List ℚ) (i : ℕ) (e : ℕ × Bool × ℚ) : ℚ :=
  let ρ := SDP.objective.bsignQ e.2.1 * aQ Q₀ I out i e.1
  (SDP.objective.bsignQ e.2.1 * xi.getD e.1 0 - ρ * xi.getD i 0) /
    sqrtP (pPar Q₀ I) (1 - ρ ^ 2)

def wDegQ (i : ℕ) : ℚ := ((outEdges (winList Q₀ I out) i).map fun e ↦ e.2.2).sum

def fHat (xi : List ℚ) (i : ℕ) : ℚ :=
  ((outEdges (winList Q₀ I out) i).map fun e ↦ e.2.2 / wDegQ Q₀ I out i *
    (2 * Num.phiQ (tPar Q₀ I) (nSer Q₀ I) (ratioQ I * hHat Q₀ I out xi i e) - 1)).sum

def algC (cells : ℕ → ℕ) : List Bool :=
  let xi := xiHat Q₀ I out cells
  if branch0 Q₀ I out then (List.range I.1).map fun i ↦ decide (0 ≤ xi.getD i 0)
  else (List.range I.1).map fun i ↦ decide (0 ≤ xi.getD i 0 + tQ I * fHat Q₀ I out xi i)

end BGHKLMM26.Alg.O

namespace BGHKLMM26.Alg

/-- **The algorithm with budget `L`**: the solver runs with budget `L`. -/
def run (Q₀ : ℕ) (x : (Instance × List Bool) × ℕ) : List Bool :=
  O.algC Q₀ x.1.1 (SoS.Core.core (solverInput Q₀ x.1.1, x.2))
    (cellOfCoins (tPar Q₀ x.1.1) x.1.2)

/-- **The algorithm is `run` with the solver's budget.** -/
theorem alg_eq_run (Q₀ : ℕ) (x : Instance × List Bool) :
    alg Q₀ x = run Q₀ (x, SoS.Solver.budget (solverInput Q₀ x.1)) := rfl

end BGHKLMM26.Alg
