module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobBounds
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobPrecision

/-! Fuel-independent exponents and scan bounds including the encoded schedule. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobScan

open Common _root_.ABBKS26.Tree Sources Builders
open Turing.MultiTapeTM ComputableInPolyTime

/-- Only the original block arguments enter this size, including arbitrary rational schedules. -/
def key (a : Args) : ℕ := (encBlockArgs a.1).length + 64

def coefficientExponent (a : Args) : ℕ := key a ^ 3

def limit (a : Args) : ℕ := key a ^ 20

theorem key_polytime : ComputableInPolyTime key encArgs encUnary := by
  have hb : ComputableInPolyTime (fun a : Args ↦ a.1) encArgs encBlockArgs := fst _ _
  exact unary_add' (.of_tidy
    ((ComputableTidilyInPolyTime.encoding_length encBlockArgs).comp hb.tidy)) (const 64)

theorem coefficientExponent_polytime :
    ComputableInPolyTime coefficientExponent encArgs encUnary := by
  exact (unary_mul' (unary_mul' key_polytime key_polytime) key_polytime).of_enc_eq
    (fun _ ↦ by congr 1; simp only [coefficientExponent, pow_succ, pow_zero, one_mul])

theorem limit_polytime : ComputableInPolyTime limit encArgs encNat := by
  exact binary_pow' (unary_to_binary.comp key_polytime) (const 20)


theorem key_bounds (a : Args) :
    64 ≤ key a ∧ a.1.1 ≤ key a ∧
      (encPoints a.1.2.2.1).length ≤ key a ∧
      (encPoints a.1.2.2.2.1).length ≤ key a ∧
      (encNat a.1.2.2.2.2.1).length ≤ key a ∧
      (encIndices a.1.2.2.2.2.2).length ≤ key a := by
  simp only [key, encBlockArgs, length_encPair, encUnary_apply, List.length_replicate]
  omega

theorem field_bound (a : Args) (j : ℕ) :
    FrobSize.RatBound (key a) (field a j) :=
  (FrobSize.point_bound a.1.2.2.1 a.1.2.2.2.2.1 j).mono (key_bounds a).2.2.1

private theorem inv_bound {q : ℚ} {b : ℕ} (h : FrobSize.RatBound b q) :
    FrobSize.RatBound (2 * b) q⁻¹ := by
  by_cases hq : q = 0
  · simpa only [hq, inv_zero] using FrobSize.RatBound.zero (2 * b)
  have hn : 1 ≤ q.num.natAbs := by
    have hne : q.num ≠ 0 := fun hn ↦ hq (Rat.num_eq_zero.mp hn)
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
  have he : (q.num.natAbs : ℚ) = |q| * q.den := by
    rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
      abs_of_pos (by exact_mod_cast q.den_pos : (0 : ℚ) < q.den)]
  have hnum : q.num.natAbs ≤ 2 ^ (2 * b) := by
    have hd : (q.den : ℚ) ≤ 2 ^ b := by exact_mod_cast h.denominator
    have hb : (q.num.natAbs : ℚ) ≤ 2 ^ (2 * b) := by
      rw [he, two_mul, pow_add]
      exact mul_le_mul h.magnitude hd (by positivity) (by positivity)
    exact_mod_cast hb
  constructor
  · have hinv : |q⁻¹| ≤ q.den := by
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hq)]
      have hn' : (1 : ℚ) ≤ q.num.natAbs := by exact_mod_cast hn
      simpa only [he, mul_comm] using hn'
    exact hinv.trans ((by exact_mod_cast h.denominator : (q.den : ℚ) ≤ 2 ^ b).trans
      (pow_le_pow_right₀ (by norm_num) (by omega)))
  · simpa only [Rat.den_inv_of_ne_zero hq] using hnum

theorem scale_bound (a : Args) :
    40 / (field a 0 : ℝ) ≤ (2 : ℝ) ^ (key a + 6) := by
  have hsmall : |(field a 0)⁻¹| ≤ (2 : ℚ) ^ key a := by
    by_cases hzero : field a 0 = 0
    · simp only [hzero, inv_zero, abs_zero]
      positivity
    have hn : 1 ≤ (field a 0).num.natAbs := by
      have hne : (field a 0).num ≠ 0 := fun hn ↦ hzero (Rat.num_eq_zero.mp hn)
      exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hne)
    have he : ((field a 0).num.natAbs : ℚ) =
        |field a 0| * (field a 0).den := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Rat.mul_den_eq_num, abs_mul,
        abs_of_pos (by exact_mod_cast (field a 0).den_pos :
          (0 : ℚ) < (field a 0).den)]
    have hinv : |(field a 0)⁻¹| ≤ (field a 0).den := by
      rw [abs_inv, inv_le_iff_one_le_mul₀ (abs_pos.mpr hzero)]
      have hn' : (1 : ℚ) ≤ (field a 0).num.natAbs := by exact_mod_cast hn
      simpa only [he, mul_comm] using hn'
    exact hinv.trans (by exact_mod_cast (field_bound a 0).denominator)
  have hreal : |(field a 0 : ℝ)⁻¹| ≤ (2 : ℝ) ^ key a := by
    exact_mod_cast hsmall
  rw [div_eq_mul_inv, pow_add]
  norm_num only [pow_succ, pow_zero, mul_one]
  have hpos : 0 ≤ (2 : ℝ) ^ key a := by positivity
  nlinarith only [(le_abs_self (field a 0 : ℝ)⁻¹).trans hreal, hpos]

theorem precision_bound (a : Args) :
    coefficientExponent a + FrobPrecision.precision (FrobBounds.exponent a) + 1 ≤
      key a ^ 4 := by
  let z := key a
  have hz : 64 ≤ z := (key_bounds a).1
  have hd : a.1.1 ≤ z := (key_bounds a).2.1
  have hx : (encPoints a.1.2.2.2.1).length ≤ z := (key_bounds a).2.2.2.1
  have hdim : FrobSize.RatBound z (a.1.1 : ℚ) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hd.trans (Nat.lt_two_pow_self (n := z)).le
    · simpa only [Rat.den_natCast] using Nat.one_le_two_pow
  have h16 : FrobSize.RatBound 4 16 := by constructor <;> norm_num
  have hpow : FrobSize.RatBound (encPoints a.1.2.2.2.1).length
      ((2 : ℚ) ^ (encPoints a.1.2.2.2.1).length) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
    · simpa using Nat.one_le_two_pow
  have hcov := ((h16.mul hdim).mul (hpow.mul hpow)).mul (inv_bound (field_bound a 0))
  have hcov' : FrobSize.RatBound (5 * z + 4) (FrobBounds.covBound a) := by
    simp only [FrobBounds.covBound, pow_two, div_eq_mul_inv]
    apply hcov.mono
    change 4 + z + ((encPoints a.1.2.2.2.1).length +
      (encPoints a.1.2.2.2.1).length) + 2 * z ≤ 5 * z + 4
    omega
  have hR := (field_bound a 8).bits
  have he : FrobBounds.exponent a ≤ 40 * z := by
    have hc := hcov'.bits
    unfold FrobBounds.exponent
    dsimp only [z] at hc hd hR ⊢
    omega
  have hp : FrobPrecision.precision (FrobBounds.exponent a) ≤ 160 * z + 10 := by
    unfold FrobPrecision.precision
    omega
  have hz2 : 64 ^ 2 ≤ z ^ 2 := Nat.pow_le_pow_left hz 2
  have hz3 : 160 * z + 11 ≤ z ^ 3 := by
    have hh := Nat.mul_le_mul_right z hz2
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
    norm_num at hh
    nlinarith only [hh, hz]
  have hroom : 2 * z ^ 3 ≤ z ^ 4 := by
    calc
      _ ≤ z * z ^ 3 := Nat.mul_le_mul_right _ (by omega : 2 ≤ z)
      _ = _ := by ring
  change z ^ 3 + FrobPrecision.precision (FrobBounds.exponent a) + 1 ≤ z ^ 4
  omega

/-- Every record in the rounded scan fits the same binary limit. No population,
eligibility, or bound on the unrounded coefficients is needed for this size estimate. -/
theorem rounded_scan (a : Args) (p b : ℕ) (s : ℚ) (q : StatisticL)
    (hpb : b + p + 1 ≤ key a ^ 4) :
    ∀ e ∈ Thresholds.rawL a.1.1 a.1.2.2.2.1 a.1.2.2.2.2.1 a.1.2.2.2.2.2
      (FrobRound.roundedL a.1.1 p b s q) (field a 6), (encEdge e).length ≤ limit a := by
  let z := key a
  have hz : 2 ≤ z := by have hh := (key_bounds a).1; omega
  have hd : a.1.1 ≤ z := (key_bounds a).2.1
  have hx : (encPoints a.1.2.2.2.1).length ≤ z ^ 4 :=
    (key_bounds a).2.2.2.1 |>.trans (by
      simpa only [pow_one] using
        Nat.pow_le_pow_right (by omega : 1 ≤ z) (by norm_num : 1 ≤ 4))
  have hA (i : ℕ) (hi : i < a.1.1) (j : ℕ) (hj : j < a.1.1) :
      FrobSize.RatBound (b + p + 1)
        (((FrobRound.roundedL a.1.1 p b s q).1.getD i []).getD j 0) := by
    simp only [FrobRound.roundedL, FrameAux.Features.table]
    rw [FrameAux.Linear.getD_map_range _ _ hi, FrameAux.Linear.getD_map_range _ _ hj]
    exact FrobSize.of_small (FrobRound.entry_small p b s _)
  have hb (i : ℕ) (hi : i < a.1.1) :
      FrobSize.RatBound (b + p + 1) ((FrobRound.roundedL a.1.1 p b s q).2.1.getD i 0) := by
    simpa only [FrobRound.roundedL, List.getD_replicate (0 : ℚ) hi] using
      FrobSize.RatBound.zero (b + p + 1)
  have hv (i : ℕ) : FrobSize.RatBound (20 * z ^ 6)
      (evalL a.1.1 (FrobRound.roundedL a.1.1 p b s q) (a.1.2.2.2.1.getD i [])) := by
    exact (FrobSize.eval_bound _ _ _ _ _ hA hb (FrobSize.RatBound.zero _)
      (fun j _ ↦ FrobSize.point_bound _ i j)).mono
        (FrobSize.evalBound_le _ _ _ z hz hd hpb hx)
  have hW := (field_bound a 6).mono
    (show z ≤ z ^ 4 by simpa only [pow_one] using
      Nat.pow_le_pow_right (by omega : 1 ≤ z) (by norm_num : 1 ≤ 4))
  intro e he
  have hraw := FrobSize.raw_bits _ _ _ _ _ _ (20 * z ^ 6) (z ^ 4) (200 * z ^ 6)
    (FrobRound.roundedL_bits_envelope _ _ _ z s q hz hd hpb) (fun i _ ↦ hv i) hW e he
  have hh := (key_bounds a).2.2.2.2.1
  have hN := (key_bounds a).2.2.2.2.2
  have h46 : z ^ 4 ≤ z ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h16 : z ≤ z ^ 6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega) (by norm_num : 1 ≤ 6)
  have h6 : 1 ≤ z ^ 6 := one_le_pow₀ (by omega)
  have hsmall : (encEdge e).length ≤ 2048 * z ^ 6 := by
    have hone : (encNat 1).length = 1 := rfl
    rw [hone] at hraw
    change _ ≤ z at hh hN
    omega
  have h11 : 2048 ≤ z ^ 11 := by
    have hp := Nat.pow_le_pow_left hz 11
    norm_num at hp
    exact hp
  calc
    _ ≤ 2048 * z ^ 6 := hsmall
    _ ≤ z ^ 11 * z ^ 6 := Nat.mul_le_mul_right _ h11
    _ = z ^ 17 := by rw [← pow_add]
    _ ≤ limit a := Nat.pow_le_pow_right (by omega) (by norm_num)

end ABBKS26.Assembly.Exec.RefineSynth.FrobScan
