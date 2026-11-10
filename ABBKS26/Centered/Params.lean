module

public import ABBKS26.Centered.Poly

/-!
# Parameters for centered mixtures

The rational parameters of the centered subspace theorem ([ABBKS26, Theorem 5.6]): accuracies,
rounding radius and the rank caps that bound the dimension of the subspace found.
-/

@[expose] public section

namespace ABBKS26.Centered

noncomputable section

open Matrix

open Common MvPolynomial

def nu (w μ : ℚ) : ℚ := w * μ ^ 4
def delta (w μ : ℚ) : ℚ := nu w μ ^ 8
def gammaStar (w μ : ℚ) : ℚ := delta w μ ^ 2 / 20
def etaStar (w μ : ℚ) : ℚ := delta w μ ^ 4 / 9
def roundTolerance (μ : ℚ) : ℚ := 7 * μ ^ 8
def radius (μ : ℚ) : ℚ := 32 * μ

def rankBound (w rF μ : ℚ) : ℕ := ⌊rF / (w * delta w μ ^ 2)⌋₊

def dimensionCap (w rF μ : ℚ) : ℕ := Rounding.rankCap (radius μ) (rankBound w rF μ)

end

end ABBKS26.Centered
