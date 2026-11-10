module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdGuard
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecCoverage

/-! Capped rank, packing, and net programs for the identical-covariance branch. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdFuel

open Common Rounding _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def accuracy (a : Args) : ℚ := field a 10

def rank (a : Args) : ℕ := min a.2 a.1.2.1

def dimension (a : Args) : ℕ := min a.2 (rankCap (accuracy a) (rank a))

def mesh (a : Args) : ℕ := ⌈8 * (dimension a : ℚ) / accuracy a⌉₊

theorem rank_polytime : ComputableInPolyTime rank encArgs encUnary :=
  binary_min_unary' (by fun_prop) (by fun_prop)

theorem dimension_polytime : ComputableInPolyTime dimension encArgs encUnary :=
  binary_min_unary' (snd _ _)
    (SpecFuel.packing_polytime_of (field_polytime 10) rank_polytime)

theorem mesh_polytime : ComputableInPolyTime mesh encArgs encNat :=
  FrameAux.Linear.rat_natCeil' (rat_div' (rat_mul' (const 8)
    (rat_natCast' (unary_to_binary.comp dimension_polytime))) (field_polytime 10))

theorem dimension_le (a : Args) (hβ : 0 < accuracy a) :
    dimension a ≤ IdCov.N_pack (accuracy a) a.1.2.1 := by
  by_cases hk : a.1.2.1 ≤ a.2
  · unfold dimension rank
    rw [min_eq_right hk]
    exact min_le_right _ _
  · exact (min_le_left _ _).trans
      ((Nat.le_of_lt (Nat.lt_of_not_ge hk)).trans
        (SpecFuel.rank_le_cap (accuracy a) a.1.2.1 hβ))

def grid (B : Args → Points) (a : Args) : Points :=
  if 0 < accuracy a ∧ accuracy a ≤ 1 / 100 then
    SpecNetGrid.run a.1.1 (mesh a) a.2 ((B a).take (dimension a))
  else []

theorem grid_polytime (B : Args → Points)
    (hB : ComputableInPolyTime B encArgs encPoints) :
    ComputableInPolyTime (grid B) encArgs encPoints := by
  have hc : ComputableInPolyTime (fun a : Args ↦ decide
      (0 < accuracy a ∧ accuracy a ≤ 1 / 100)) encArgs encBool := by
    refine (bool_and.comp ((rat_lt' (const 0) (field_polytime 10)).prod
      (rat_le' (field_polytime 10) (const (1 / 100))))).of_enc_eq fun a ↦ ?_
    congr 1
  unfold grid
  apply FrameAux.Linear.ite_prop hc
  · exact SpecNetGrid.run_polytime_of (by fun_prop) mesh_polytime (snd _ _)
      (.of_tidy (ComputableTidilyInPolyTime.listTakeWithInput
        hB.tidy dimension_polytime.tidy))
  · exact const []

theorem grid_length (B : Args → Points) (a : Args) :
    (grid B a).length ≤ netBound (IdCov.N_pack (accuracy a) a.1.2.1) (accuracy a) := by
  unfold grid
  split_ifs with hβ
  · let D := IdCov.N_pack (accuracy a) a.1.2.1
    have hD : dimension a ≤ D := dimension_le a hβ.1
    have hD0 : 0 < D := by
      dsimp only [D, IdCov.N_pack, rankCap]
      unfold greedyCap
      positivity
    have hm : mesh a ≤ ⌈8 * (D : ℚ) / accuracy a⌉₊ := by
      apply Nat.ceil_mono
      apply div_le_div_of_nonneg_right _ hβ.1.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) (by norm_num)
    have hb := (CompleteAux.grid_size D (accuracy a) hD0 hβ).2.1
    apply (SpecNetGrid.length_run _ _ _ _).trans
    apply (Nat.pow_le_pow_left (show 2 * mesh a + 1 ≤
      1 + ⌈64 * (D : ℚ) / accuracy a⌉₊ by omega) _).trans
    exact Nat.pow_le_pow_right (by omega) ((List.length_take_le _ _).trans hD)
  · exact Nat.zero_le _

theorem fields {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    accuracy (args k ps x h P, fuel) = (ps h).subspaceAccuracy := by
  unfold accuracy
  rw [field_args _ _ _ _ _ _ hh]
  rfl

theorem caps {n k d : ℕ} (ps : ℕ → StepParams) (_x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (_P : Finset (Fin n))
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hβ : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 100) :
    k ≤ fuel ∧ IdCov.N_pack (ps h).subspaceAccuracy k ≤ fuel ∧
      netBound (IdCov.N_pack (ps h).subspaceAccuracy k) (ps h).subspaceAccuracy ≤ fuel ∧
      2 * ABBKS26.RefineAux.meanThresholdRadius k (ps h) + 3 ≤ fuel := by
  let D := IdCov.N_pack (ps h).subspaceAccuracy k
  let T := 2 * ABBKS26.RefineAux.meanThresholdRadius k (ps h) + 3
  have hD0 : 0 < D := by
    dsimp only [D, IdCov.N_pack, rankCap]
    unfold greedyCap
    positivity
  have hDn : D ≤ netBound D (ps h).subspaceAccuracy :=
    SpecPrepared.dimension_le_net _ _ hβ
  have hnet0 : 1 ≤ netBound D (ps h).subspaceAccuracy :=
    (by omega : 1 ≤ D).trans hDn
  have hblock : stepBranchCap .identical k (ps h) ≤ fuel :=
    (SpecPrepared.block_cap .identical k ps h hh).trans
      ((count_fuel .identical k n d ps).2.trans hf)
  have hnet : netBound D (ps h).subspaceAccuracy ≤ fuel :=
    (Nat.le_mul_of_pos_right _ (by dsimp only [T]; omega : 0 < T)).trans hblock
  have ht : T ≤ fuel := (Nat.le_mul_of_pos_left _ hnet0).trans hblock
  exact ⟨(count_fuel .identical k n d ps).1.trans hf, hDn.trans hnet, hnet, ht⟩

end ABBKS26.Assembly.Exec.RefineSynth.IdFuel
