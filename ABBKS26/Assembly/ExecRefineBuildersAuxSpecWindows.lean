module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecSquare

/-! The fixed spectral windows, including their fuel-independent endpoint ledger. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecWindows

open Common _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

def count (a : Args) : ℕ :=
  Nat.clog 2 ⌈256 * (4 / field a 0) ^ 2 / field a 10 ^ 2⌉₊ + 5

def threshold (a : Args) (i : ℕ) : ℚ :=
  (2 * sqrtUp (4 / field a 0) / 2 ^ i) ^ 2

def window (a : Args) (i : ℕ) : ℚ × ℚ × ℚ :=
  let t := threshold a i
  (t, t / field a 5 ^ 2, t * field a 5 ^ 2)

def run (a : Args) : List (ℚ × ℚ × ℚ) :=
  (List.range (count a)).map (window a)

theorem sqrtUp_polytime_of {α : Type} {enc : α ↪ List Bool} {q : α → ℚ}
    (hq : ComputableInPolyTime q enc encRat) :
    ComputableInPolyTime (fun a ↦ sqrtUp (q a)) enc encRat := by
  unfold sqrtUp
  have hc := binary_sqrt' (FrameAux.Linear.rat_natCeil' (rat_max' (const 0) hq))
  exact rat_natCast' (.of_tidy (ComputableTidilyInPolyTime.binary_add' hc.tidy
    (const 1).tidy))

theorem count_polytime : ComputableInPolyTime count encArgs encUnary := by
  unfold count
  exact unary_add' (binary_clog_two.comp (FrameAux.Linear.rat_natCeil'
    (rat_div' (rat_mul' (const 256) (FrameAux.Linear.rat_pow'
      (rat_div' (const 4) (field_polytime 0)) (const 2)))
      (FrameAux.Linear.rat_pow' (field_polytime 10) (const 2))))) (const 5)

theorem window_polytime : ComputableInPolyTime (fun q : Args × ℕ ↦ window q.1 q.2)
    (encPair encArgs encUnary) (encPair encRat (encPair encRat encRat)) := by
  have ht : ComputableInPolyTime (fun q : Args × ℕ ↦ threshold q.1 q.2)
      (encPair encArgs encUnary) encRat := by
    unfold threshold
    exact FrameAux.Linear.rat_pow' (rat_div' (rat_mul' (const 2)
      (sqrtUp_polytime_of (rat_div' (const 4) ((field_polytime 0).comp (fst _ _)))))
      (rat_two_pow' (snd _ _))) (const 2)
  have hK : ComputableInPolyTime (fun q : Args × ℕ ↦ field q.1 5 ^ 2)
      (encPair encArgs encUnary) encRat :=
    FrameAux.Linear.rat_pow' ((field_polytime 5).comp (fst _ _)) (const 2)
  exact ht.prod ((rat_div' ht hK).prod (rat_mul' ht hK))

theorem run_polytime : ComputableInPolyTime run encArgs
    (encList (encPair encRat (encPair encRat encRat))) :=
  mapWithInput (range.comp count_polytime) window_polytime

theorem agrees {n d : ℕ} (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (P : Finset (Fin n)) (hh : h < k) :
    run (args k ps x h P, fuel) =
      (ABBKS26.RefineAux.spectralThresholds (ps h)).map fun t ↦
        (t, t / (ps h).K ^ 2, t * (ps h).K ^ 2) := by
  have hw : field (args k ps x h P, fuel) 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  have hβ : field (args k ps x h P, fuel) 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  have hK : field (args k ps x h P, fuel) 5 = (ps h).K := by
    rw [field_args _ _ _ _ _ _ hh]
    rfl
  simp only [run, count, hw, hβ,
    ABBKS26.RefineAux.spectralThresholds, ABBKS26.RefineAux.spectralThresholdCount,
    List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  simp only [window, threshold, hw, hK]

theorem inverse_bound {b : ℕ} {q : ℚ} (hq : FrobSize.RatBound b q) :
    FrobSize.RatBound (2 * b) q⁻¹ := by
  by_cases hzero : q = 0
  · simpa only [hzero, inv_zero] using FrobSize.RatBound.zero (2 * b)
  have hn : 1 ≤ q.num.natAbs := by
    have hne : q.num ≠ 0 := fun hn ↦ hzero (Rat.num_eq_zero.mp hn)
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have he : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
      abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
  have hinv : |q⁻¹| ≤ q.den := by
    rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hzero)]
    have hn' : (1 : ℚ) ≤ q.num.natAbs := by exact_mod_cast hn
    simpa only [he, mul_comm] using hn'
  have hnum : q.num.natAbs ≤ 2 ^ (2 * b) := by
    have hd : (q.den : ℚ) ≤ 2 ^ b := by exact_mod_cast hq.denominator
    have hb : (q.num.natAbs : ℚ) ≤ 2 ^ (2 * b) := by
      rw [he, two_mul, pow_add]
      exact mul_le_mul hq.magnitude hd (by positivity) (by positivity)
    exact_mod_cast hb
  refine ⟨?_, ?_⟩
  · exact hinv.trans ((by exact_mod_cast hq.denominator : (q.den : ℚ) ≤ 2 ^ b).trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  · simpa only [Rat.den_inv_of_ne_zero hzero] using hnum

theorem sqrtUp_bound {b : ℕ} {q : ℚ} (hq : FrobSize.RatBound b q) :
    FrobSize.RatBound (b + 1) (sqrtUp q) := by
  have hq' : max 0 q ≤ (2 : ℚ) ^ b :=
    max_le (by positivity) ((le_abs_self q).trans hq.magnitude)
  have hc : ⌈max 0 q⌉₊ ≤ 2 ^ b := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hq'
  have hs : Nat.sqrt ⌈max 0 q⌉₊ + 1 ≤ 2 ^ (b + 1) := by
    have hh := (Nat.sqrt_le_self _).trans hc
    have hp : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    rw [pow_succ]
    omega
  constructor
  · rw [abs_of_nonneg (by unfold sqrtUp; positivity)]
    unfold sqrtUp
    exact_mod_cast hs
  · unfold sqrtUp
    simpa using Nat.one_le_two_pow

theorem count_bound (a : Args) : count a ≤ 8 * FrobScan.key a + 17 := by
  let z := FrobScan.key a
  have h256 : FrobSize.RatBound 8 256 := by constructor <;> norm_num
  have h4 : FrobSize.RatBound 2 4 := by constructor <;> norm_num
  have hw := h4.mul (inverse_bound (FrobScan.field_bound a 0))
  have hβ := inverse_bound ((FrobScan.field_bound a 10).mul (FrobScan.field_bound a 10))
  have hb := h256.mul ((hw.mul hw).mul hβ)
  have hq : 256 * (4 / field a 0) ^ 2 / field a 10 ^ 2 ≤
      (2 : ℚ) ^ (8 * z + 12) := by
    have he : FrobSize.RatBound (8 * z + 12)
        (256 * (4 / field a 0) ^ 2 / field a 10 ^ 2) := by
      convert hb using 1
      · dsimp only [z]
        omega
      · simp only [div_eq_mul_inv, pow_two]
        ring
    exact (le_abs_self _).trans he.magnitude
  have hc : ⌈256 * (4 / field a 0) ^ 2 / field a 10 ^ 2⌉₊ ≤ 2 ^ (8 * z + 12) := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hq
  exact Nat.add_le_add_right (Nat.clog_le_of_le_pow hc) 5

theorem endpoints (a : Args) (t lo hi : ℚ) (ht : (t, lo, hi) ∈ run a) :
    FrobSize.RatBound (FrobScan.key a ^ 4) t ∧
      FrobSize.RatBound (FrobScan.key a ^ 4) lo ∧
      FrobSize.RatBound (FrobScan.key a ^ 4) hi := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj he |>.imp_right Prod.mk.inj
  let z := FrobScan.key a
  have hz : 64 ≤ z := (FrobScan.key_bounds a).1
  have hi' : i ≤ 8 * z + 17 := (List.mem_range.mp hi).le.trans (count_bound a)
  have h4 : FrobSize.RatBound 2 4 := by constructor <;> norm_num
  have h2 : FrobSize.RatBound 1 2 := by constructor <;> norm_num
  have hs := sqrtUp_bound (h4.mul (inverse_bound (FrobScan.field_bound a 0)))
  have hd : FrobSize.RatBound i ((2 : ℚ) ^ i) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
    · simpa using Nat.one_le_two_pow
  have hbase := (h2.mul hs).mul (inverse_bound hd)
  have hthreshold : FrobSize.RatBound (4 * z + 4 * i + 8) (threshold a i) := by
    convert hbase.mul hbase using 1
    · dsimp only [z]
      omega
    · simp only [threshold, div_eq_mul_inv, pow_two]
  have hK := (FrobScan.field_bound a 5).mul (FrobScan.field_bound a 5)
  have hlo := hthreshold.mul (inverse_bound hK)
  have hhi := hthreshold.mul hK
  have hroom : 8 * z + 4 * i + 8 ≤ z ^ 4 := by
    have hz2 := Nat.pow_le_pow_left hz 2
    have hz3 : 4096 * z ≤ z ^ 3 := by nlinarith only [hz2]
    have hz4 : z ^ 3 ≤ z ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith only [hi', hz3, hz4, hz]
  change FrobSize.RatBound (z ^ 4) (threshold a i) ∧
    FrobSize.RatBound (z ^ 4) (threshold a i / field a 5 ^ 2) ∧
    FrobSize.RatBound (z ^ 4) (threshold a i * field a 5 ^ 2)
  dsimp only [z] at hroom hthreshold ⊢
  exact ⟨hthreshold.mono (by omega), by
    simpa only [div_eq_mul_inv, pow_two] using hlo.mono (by omega), by
    simpa only [pow_two] using hhi.mono (by omega)⟩

end ABBKS26.Assembly.Exec.RefineSynth.SpecWindows
