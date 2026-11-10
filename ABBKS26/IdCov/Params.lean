module

public import ABBKS26.IdCov.MomPoly

/-!
# Parameters for identical covariances

The rational parameters of the identical-covariance subspace theorem ([ABBKS26, Theorem 6.5]):
moment degree, accuracies and the rank cap that bounds the dimension of the subspace found.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section

open Matrix

open Common MvPolynomial

def tDegree (w : ℚ) : ℕ := logInv w + 3
-- The denominator 25 reconciles RC2 with the advertised radius β.
def epsilonR (β : ℚ) : ℚ := (β / 25) ^ 8

def tauStar (β : ℚ) : ℚ := epsilonR β / 3
def gammaStar (β : ℚ) : ℚ := epsilonR β / 6
def cStar (β : ℚ) : ℚ := epsilonR β ^ 2 / 3

def epsilonId (w β : ℚ) : ℚ := (cStar β / (64 * tDegree w)) ^ (4 * tDegree w)
def epsilonSys (w β : ℚ) : ℚ := epsilonId w β / 4

def etaStar (w β : ℚ) : ℚ :=
  epsilonSys w β / (8 * tDegree w : ℚ) ^ (4 * tDegree w + 2)

/-- IdCov's packing name denotes the full deterministic output-rank cap. -/
def N_pack (β : ℚ) (k : ℕ) : ℕ := Rounding.rankCap β k

end

end ABBKS26.IdCov
