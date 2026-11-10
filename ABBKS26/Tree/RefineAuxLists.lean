module

public import ABBKS26.Tree.Complete

/-! Input-determined rational direction and threshold lists with unconditional caps. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix MeasureTheory _root_.ABBKS26.Tree
open scoped BigOperators

variable {d : ℕ}


def spectralThresholdCount (p : StepParams) : ℕ :=
  Nat.clog 2 ⌈256 * (4 / p.w) ^ 2 / p.subspaceAccuracy ^ 2⌉₊ + 5

/-- All magnitudes on the prescribed geometric grid, squared for spectral statistics. -/
def spectralThresholds (p : StepParams) : List ℚ :=
  (List.range (spectralThresholdCount p)).map fun i ↦
    (2 * sqrtUp (4 / p.w) / 2 ^ i) ^ 2

theorem spectralThresholds_length (p : StepParams) :
    (spectralThresholds p).length = spectralThresholdCount p := by
  simp only [spectralThresholds, List.length_map, List.length_range]

def meanThresholdRadius (k : ℕ) (p : StepParams) : ℕ :=
  ⌈64 * k * sqrtUp (1 / p.w)⌉₊

/-- The additive mean grid includes both endpoints and one extra point on each side. -/
def meanThresholds (k : ℕ) (p : StepParams) : List ℚ :=
  let J := meanThresholdRadius k p
  (List.range (2 * J + 3)).map fun (i : ℕ) ↦
    ((i : ℚ) - ((J : ℚ) + 1)) / (16 * (k : ℚ))


end

end ABBKS26.RefineAux
