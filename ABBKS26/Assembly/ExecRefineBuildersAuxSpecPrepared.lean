module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecProgram
public import ABBKS26.Assembly.ExecRefineAuxWrapper

/-! Prepared fuel bounds for the executable spectral grid and rounder. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecPrepared

open Common Centered Rounding _root_.ABBKS26.Tree Sources Builders

theorem fields {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    let a := (args k ps x h P, fuel)
    SpecInput.weight a = (ps h).w / 2 ∧
      SpecInput.accuracy a = (ps h).subspaceAccuracy ∧
      SpecFuel.deviation a = 10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10 := by
  have hw : field (args k ps x h P, fuel) 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  have hμ : field (args k ps x h P, fuel) 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  have hσ : field (args k ps x h P, fuel) 9 = (ps h).sigmaSq := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  simp only [SpecInput.weight, SpecInput.accuracy, SpecFuel.deviation, hw, hμ, hσ,
    and_self]

theorem block_cap (mode : Mode) (k : ℕ) (ps : ℕ → StepParams)
    (h : ℕ) (hh : h < k - 1) :
    stepBranchCap mode k (ps h) ≤ branchCap mode k ps := by
  have hc : stepBranchCap mode k (ps h) ≤
      ((List.range (k - 1)).map fun j ↦ stepBranchCap mode k (ps j)).foldl max 0 :=
    SoS.Poly.le_foldl_max (x := stepBranchCap mode k (ps h))
      (List.mem_map.mpr ⟨h, List.mem_range.mpr hh, rfl⟩) 0
  exact hc.trans ((Nat.le_mul_of_pos_left _ (by omega)).trans (le_max_right 1 _))

theorem dimension_le_net (D : ℕ) (μ : ℚ) (hμ : 0 < μ ∧ μ ≤ 1 / 100) :
    D ≤ netBound D μ := by
  by_cases hD : D = 0
  · subst D
    exact Nat.zero_le _
  have hD0 : (0 : ℚ) < D := by exact_mod_cast Nat.pos_of_ne_zero hD
  have hμ0 := hμ.1
  have hc : 0 < ⌈64 * (D : ℚ) / μ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  exact (Nat.lt_two_pow_self (n := D)).le.trans (Nat.pow_le_pow_left (by omega) _)

theorem net_le_block (k : ℕ) (p : StepParams) :
    netBound (dimensionCap (p.w / 2)
      (10000 * p.sigmaSq / (p.w / 2) + 10) p.subspaceAccuracy) p.subspaceAccuracy ≤
        stepBranchCap .centered k p := by
  unfold stepBranchCap
  have hc : 0 < Nat.clog 2 ⌈256 * (4 / p.w) ^ 2 / p.subspaceAccuracy ^ 2⌉₊ + 5 :=
    by omega
  exact (Nat.le_mul_of_pos_right _ hc).trans (Nat.le_add_left _ _)

/-- The public branch reserve pays for both the full packing cap and its entire grid. -/
theorem caps {n k d : ℕ} (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n))
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hμ : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 100) :
    let a := (args k ps x h P, fuel)
    rankBound (SpecInput.weight a) (SpecFuel.deviation a) (SpecInput.accuracy a) ≤ fuel ∧
      dimensionCap (SpecInput.weight a) (SpecFuel.deviation a)
        (SpecInput.accuracy a) ≤ fuel ∧
      netBound (dimensionCap (SpecInput.weight a) (SpecFuel.deviation a)
        (SpecInput.accuracy a)) (SpecInput.accuracy a) ≤ fuel := by
  obtain ⟨hw', hμ', hr'⟩ := fields k ps x fuel h P (by omega)
  dsimp only
  rw [hw', hμ', hr']
  have hnet := (net_le_block k (ps h)).trans
    ((block_cap .centered k ps h hh).trans ((count_fuel .centered k n d ps).2.trans hf))
  have hdim := (dimension_le_net _ _ hμ).trans hnet
  have hμ0 := hμ.1
  exact ⟨(SpecFuel.rank_le_cap (Centered.radius (ps h).subspaceAccuracy) _
    (by unfold Centered.radius; positivity)).trans hdim,
    hdim, hnet⟩

theorem grid_fuel (D r : ℕ) (μ : ℚ) (hr : r ≤ D) (hD : 0 < D)
    (hμ : 0 < μ ∧ μ ≤ 1 / 100) :
    (2 * ⌈8 * (D : ℚ) / μ⌉₊ + 1) ^ r ≤ netBound D μ := by
  have hc := (CompleteAux.grid_size D μ hD hμ).2.1
  exact (Nat.pow_le_pow_left hc _).trans (Nat.pow_le_pow_right (by omega) hr)

end ABBKS26.Assembly.Exec.RefineSynth.SpecPrepared
