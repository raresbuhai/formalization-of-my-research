module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecWindows
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdStorage

/-! Fixed additive mean windows, capped before unary enumeration. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdWindows

open Common _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

/-- The public radius is kept in binary until it is capped by the input fuel. -/
def radius (a : Args) : ℕ := ⌈64 * a.1.2.1 * sqrtUp (1 / field a 0)⌉₊

def count (a : Args) : ℕ := min a.2 (2 * radius a + 3)

def threshold (a : Args) (i : ℕ) : ℚ :=
  ((i : ℚ) - ((radius a : ℚ) + 1)) / (16 * a.1.2.1)

def window (a : Args) (i : ℕ) : Window :=
  let t := threshold a i
  (t, t - 1 / (16 * a.1.2.1), t + 1 / (16 * a.1.2.1))

def run (a : Args) : List Window := (List.range (count a)).map (window a)

theorem radius_polytime : ComputableInPolyTime radius encArgs encNat := by
  exact FrameAux.Linear.rat_natCeil' (rat_mul'
    (rat_mul' (const 64) (rat_natCast' (by fun_prop)))
    (SpecWindows.sqrtUp_polytime_of (rat_div' (const 1) (field_polytime 0))))

theorem count_polytime : ComputableInPolyTime count encArgs encUnary := by
  have hb : ComputableInPolyTime (fun a : Args ↦ 2 * radius a + 3) encArgs encNat :=
    .of_tidy (ComputableTidilyInPolyTime.binary_add'
      (ComputableTidilyInPolyTime.binary_mul' (const 2).tidy radius_polytime.tidy)
      (const 3).tidy)
  exact binary_min_unary' (snd _ _) hb

theorem window_polytime : ComputableInPolyTime (fun q : Args × ℕ ↦ window q.1 q.2)
    (encPair encArgs encUnary) (encPair encRat (encPair encRat encRat)) := by
  have hr : ComputableInPolyTime (fun q : Args × ℕ ↦ (radius q.1 : ℚ))
      (encPair encArgs encUnary) encRat :=
    rat_natCast' (radius_polytime.comp (fst _ _))
  have hk : ComputableInPolyTime (fun q : Args × ℕ ↦ (q.1.1.2.1 : ℚ))
      (encPair encArgs encUnary) encRat := rat_natCast' (by fun_prop)
  have hw := rat_mul' (const 16) hk
  have ht := rat_div' (rat_sub' (rat_natCast' (unary_to_binary.comp (snd _ _)))
    (rat_add' hr (const 1))) hw
  exact ht.prod ((rat_sub' ht (rat_div' (const 1) hw)).prod
    (rat_add' ht (rat_div' (const 1) hw)))

theorem run_polytime : ComputableInPolyTime run encArgs
    (encList (encPair encRat (encPair encRat encRat))) :=
  mapWithInput (range.comp count_polytime) window_polytime

theorem length_run (a : Args) : (run a).length ≤ 2 * radius a + 3 := by
  simpa only [run, count, List.length_map, List.length_range] using min_le_right a.2 _

theorem radius_agrees {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    radius (args k ps x h P, fuel) = ABBKS26.RefineAux.meanThresholdRadius k (ps h) := by
  simp only [radius, field_args _ _ _ _ _ _ hh]
  rfl

theorem agrees {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k)
    (hf : 2 * ABBKS26.RefineAux.meanThresholdRadius k (ps h) + 3 ≤ fuel) :
    run (args k ps x h P, fuel) =
      (ABBKS26.RefineAux.meanThresholds k (ps h)).map fun t ↦
        (t, t - 1 / (16 * k : ℚ), t + 1 / (16 * k : ℚ)) := by
  have hr := radius_agrees k ps x fuel h P hh
  unfold run count
  rw [hr, min_eq_right hf]
  simp only [ABBKS26.RefineAux.meanThresholds, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  dsimp only [window, threshold]
  rw [hr]
  rfl

theorem component_bound (a : Args) :
    FrobSize.RatBound (FrobScan.key a) (a.1.2.1 : ℚ) := by
  have hb : (encNat a.1.2.1).length ≤ FrobScan.key a := by
    simp only [FrobScan.key, encBlockArgs, length_encPair, encUnary_apply,
      List.length_replicate]
    omega
  have hn : a.1.2.1 ≤ 2 ^ FrobScan.key a := by
    apply (Nat.size_le.mp ?_).le
    simpa only [encNat_apply, Nat.size_eq_bits_len] using hb
  constructor
  · rw [abs_of_nonneg (by positivity)]
    exact_mod_cast hn
  · simpa only [Rat.den_natCast] using Nat.one_le_two_pow

theorem radius_bound (a : Args) : radius a ≤ 2 ^ (3 * FrobScan.key a + 7) := by
  have h64 : FrobSize.RatBound 6 64 := by constructor <;> norm_num
  have hs := SpecWindows.sqrtUp_bound (SpecWindows.inverse_bound (FrobScan.field_bound a 0))
  have hb := (h64.mul (component_bound a)).mul hs
  unfold radius
  apply Nat.ceil_le.mpr
  have he : 6 + FrobScan.key a + (2 * FrobScan.key a + 1) =
      3 * FrobScan.key a + 7 := by omega
  rw [he] at hb
  rw [Nat.cast_pow, Nat.cast_ofNat]
  apply (le_abs_self (64 * (a.1.2.1 : ℚ) * sqrtUp (1 / field a 0))).trans
  simpa only [one_div] using hb.magnitude

theorem endpoints (a : Args) (t lo hi : ℚ) (ht : (t, lo, hi) ∈ run a) :
    FrobSize.RatBound (FrobScan.key a ^ 4) t ∧
      FrobSize.RatBound (FrobScan.key a ^ 4) lo ∧
      FrobSize.RatBound (FrobScan.key a ^ 4) hi := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
  let z := FrobScan.key a
  have hz : 64 ≤ z := (FrobScan.key_bounds a).1
  have hr : radius a ≤ 2 ^ (3 * z + 7) := radius_bound a
  have hi' : i < 2 * radius a + 3 :=
    (List.mem_range.mp hi).trans_le (min_le_right _ _)
  have hiB : i ≤ 2 ^ (3 * z + 10) := by
    have hp : 1 ≤ 2 ^ (3 * z + 7) := Nat.one_le_two_pow
    rw [show 3 * z + 10 = (3 * z + 7) + 3 by omega, pow_add]
    norm_num only [Nat.reducePow]
    omega
  have hn {m b : ℕ} (hm : m ≤ 2 ^ b) : FrobSize.RatBound b (m : ℚ) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hm
    · simpa only [Rat.den_natCast] using Nat.one_le_two_pow
  have h16 : FrobSize.RatBound 4 16 := by constructor <;> norm_num
  have hw := SpecWindows.inverse_bound (h16.mul (component_bound a))
  have hb := ((hn hiB).sub ((hn hr).add FrobSize.RatBound.one)).mul hw
  have hb' : FrobSize.RatBound (8 * z + 27) (threshold a i) := by
    convert hb using 1
    · dsimp only [z]
      omega
    · simp only [threshold, div_eq_mul_inv]
  have hw' : FrobSize.RatBound (2 * z + 8) (1 / (16 * a.1.2.1 : ℚ)) := by
    simpa only [show 2 * (4 + FrobScan.key a) = 2 * z + 8 by dsimp only [z]; omega,
      one_div] using hw
  have hroom : 10 * z + 36 ≤ z ^ 4 := by
    have hz2 := Nat.pow_le_pow_left hz 2
    have hz3 : 4096 * z ≤ z ^ 3 := by nlinarith only [hz2]
    have hz4 : z ^ 3 ≤ z ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  change FrobSize.RatBound (z ^ 4) _ ∧ FrobSize.RatBound (z ^ 4) _ ∧
    FrobSize.RatBound (z ^ 4) _
  exact ⟨hb'.mono (by omega), (hb'.sub hw').mono (by omega),
    (hb'.add hw').mono (by omega)⟩

end ABBKS26.Assembly.Exec.RefineSynth.IdWindows
