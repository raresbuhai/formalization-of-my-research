module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecNetGrid
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecGuard

/-! Unary caps for the spectral rank and grid on arbitrary list inputs. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecFuel

open Common Centered Rounding _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def radius (a : Args) : ℚ := Centered.radius (SpecInput.accuracy a)

def deviation (a : Args) : ℚ :=
  10000 * field a 9 / SpecInput.weight a + 10

def rank (a : Args) : ℕ :=
  min a.2 (rankBound (SpecInput.weight a) (deviation a) (SpecInput.accuracy a))

def dimension (a : Args) : ℕ := min a.2 (rankCap (radius a) (rank a))

def mesh (a : Args) : ℕ := ⌈8 * (dimension a : ℚ) / SpecInput.accuracy a⌉₊

theorem radius_polytime : ComputableInPolyTime radius encArgs encRat :=
  rat_mul' (const 32) (field_polytime 10)

theorem deviation_polytime : ComputableInPolyTime deviation encArgs encRat :=
  rat_add' (rat_div' (rat_mul' (const 10000) (field_polytime 9))
    (rat_div' (field_polytime 0) (const 2))) (const 10)

theorem rank_polytime : ComputableInPolyTime rank encArgs encUnary := by
  have hr : ComputableInPolyTime
      (fun a : Args ↦ rankBound (SpecInput.weight a) (deviation a)
        (SpecInput.accuracy a)) encArgs encNat :=
    FrameAux.Linear.rat_natFloor' (rat_div' deviation_polytime
      (rat_mul' (rat_div' (field_polytime 0) (const 2))
        (FrameAux.Linear.rat_pow' SpecInput.delta_polytime (const 2))))
  exact binary_min_unary' (snd _ _) hr

theorem packing_polytime_of {α : Type} {enc : α ↪ List Bool}
    {γ : α → ℚ} {r : α → ℕ}
    (hγ : ComputableInPolyTime γ enc encRat)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (fun a ↦ rankCap (γ a) (r a)) enc encNat := by
  have ht : ComputableInPolyTime
      ((fun q : ℚ × ℕ ↦ rankCap q.1 q.2) ∘ (fun a ↦ (γ a, r a))) enc encNat :=
    RoundProgram.rankCap_polytime.comp (hγ.prod hr)
  exact ht

theorem packing_polytime : ComputableInPolyTime
    (fun a : Args ↦ rankCap (radius a) (rank a)) encArgs encNat :=
  packing_polytime_of radius_polytime rank_polytime

theorem dimension_polytime : ComputableInPolyTime dimension encArgs encUnary := by
  unfold dimension
  exact binary_min_unary' (snd _ _) packing_polytime

theorem mesh_polytime : ComputableInPolyTime mesh encArgs encNat :=
  FrameAux.Linear.rat_natCeil' (rat_div' (rat_mul' (const 8)
    (rat_natCast' (unary_to_binary.comp dimension_polytime))) (field_polytime 10))

/-- The cap is applied before either rank is used in a unary loop. -/
theorem rank_agrees (a : Args)
    (hf : rankBound (SpecInput.weight a) (deviation a) (SpecInput.accuracy a) ≤ a.2) :
    rank a = rankBound (SpecInput.weight a) (deviation a) (SpecInput.accuracy a) :=
  min_eq_right hf

theorem dimension_agrees (a : Args)
    (hr : rankBound (SpecInput.weight a) (deviation a) (SpecInput.accuracy a) ≤ a.2)
    (hd : dimensionCap (SpecInput.weight a) (deviation a) (SpecInput.accuracy a) ≤ a.2) :
    dimension a = dimensionCap (SpecInput.weight a) (deviation a)
      (SpecInput.accuracy a) := by
  unfold dimension
  rw [rank_agrees a hr]
  exact min_eq_right hd

theorem rank_le_cap (γ : ℚ) (r : ℕ) (hγ : 0 < γ) : r ≤ rankCap γ r := by
  have hs : (0 : ℚ) < sqrtUp (r : ℚ) := by unfold sqrtUp; positivity
  have hc : 0 < ⌈40 * sqrtUp (r : ℚ) / γ⌉₊ := Nat.ceil_pos.mpr (by positivity)
  have hp : r ≤ packCount γ r :=
    (Nat.lt_two_pow_self (n := r)).le.trans (Nat.pow_le_pow_left (by omega) r)
  exact hp.trans ((Nat.le_succ _).trans
    (Nat.le_mul_of_pos_right _ (by unfold greedyCap; omega)))

/-- Even when the true rank exceeds fuel, the capped dimension fits the public cap. -/
theorem dimension_le (a : Args) (hμ : 0 < SpecInput.accuracy a) :
    dimension a ≤ dimensionCap (SpecInput.weight a) (deviation a)
      (SpecInput.accuracy a) := by
  by_cases hr : rankBound (SpecInput.weight a) (deviation a) (SpecInput.accuracy a) ≤ a.2
  · unfold dimension
    rw [rank_agrees a hr]
    exact min_le_right _ _
  · apply (min_le_left _ _).trans
    apply (Nat.le_of_lt (Nat.lt_of_not_ge hr)).trans
    exact rank_le_cap _ _ (by unfold Centered.radius; positivity)

/-- Truncate malformed basis lists before enumeration. Empty or invalid parameter calls
produce no directions, so the product cap also holds outside the prepared regime. -/
def grid (B : Args → Points) (a : Args) : Points :=
  if 0 < SpecInput.accuracy a ∧ SpecInput.accuracy a ≤ 1 / 100 then
    SpecNetGrid.run a.1.1 (mesh a) a.2 ((B a).take (dimension a))
  else []

theorem grid_polytime (B : Args → Points)
    (hB : ComputableInPolyTime B encArgs encPoints) :
    ComputableInPolyTime (grid B) encArgs encPoints := by
  have htest : ComputableInPolyTime (fun a : Args ↦ decide
      (0 < SpecInput.accuracy a ∧ SpecInput.accuracy a ≤ 1 / 100))
      encArgs encBool := by
    refine (bool_and.comp ((rat_lt' (const 0) (field_polytime 10)).prod
      (rat_le' (field_polytime 10) (const (1 / 100))))).of_enc_eq fun a ↦ ?_
    congr 1
  unfold grid
  apply FrameAux.Linear.ite_prop htest
  · exact SpecNetGrid.run_polytime_of (by fun_prop) mesh_polytime (snd _ _)
      (.of_tidy (ComputableTidilyInPolyTime.listTakeWithInput
        hB.tidy dimension_polytime.tidy))
  · exact const []

theorem grid_length (B : Args → Points) (a : Args) :
    (grid B a).length ≤ netBound
      (dimensionCap (SpecInput.weight a) (deviation a) (SpecInput.accuracy a))
      (SpecInput.accuracy a) := by
  unfold grid
  split_ifs with hμ
  · let D := dimensionCap (SpecInput.weight a) (deviation a) (SpecInput.accuracy a)
    have hD : dimension a ≤ D := dimension_le a hμ.1
    have hD0 : 0 < D := by
      dsimp only [D, dimensionCap]
      unfold rankCap greedyCap
      positivity
    have hm : mesh a ≤ ⌈8 * (D : ℚ) / SpecInput.accuracy a⌉₊ := by
      apply Nat.ceil_mono
      apply div_le_div_of_nonneg_right _ hμ.1.le
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) (by norm_num)
    have hb := (CompleteAux.grid_size D (SpecInput.accuracy a) hD0 hμ).2.1
    apply (SpecNetGrid.length_run _ _ _ _).trans
    apply (Nat.pow_le_pow_left (show 2 * mesh a + 1 ≤
      1 + ⌈64 * (D : ℚ) / SpecInput.accuracy a⌉₊ by omega) _).trans
    exact Nat.pow_le_pow_right (by omega) ((List.length_take_le _ _).trans hD)
  · exact Nat.zero_le _

end ABBKS26.Assembly.Exec.RefineSynth.SpecFuel
