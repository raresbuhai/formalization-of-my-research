module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobRound
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobSize

/-! Explicit dyadic precision for simultaneous Gaussian variance and center-gap stability. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobPrecision

open Common _root_.ABBKS26.Tree
open Turing.MultiTapeTM ComputableInPolyTime

def precision (z : ℕ) : ℕ := 4 * z + 10

def contraction (z : ℕ) : ℚ := 1 - 1 / (2 : ℚ) ^ (z + 4)

theorem contraction_nonneg (z : ℕ) : 0 ≤ (contraction z : ℝ) := by
  have hp : (1 : ℚ) ≤ 2 ^ (z + 4) := one_le_pow₀ (by norm_num)
  have hh : 0 ≤ contraction z := by
    apply sub_nonneg.mpr
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hp
  exact_mod_cast hh

theorem contraction_lt_one (z : ℕ) : (contraction z : ℝ) < 1 := by
  have hh : contraction z < 1 := sub_lt_self _ (by positivity)
  exact_mod_cast hh

theorem contraction_gap (z : ℕ) :
    1 - (contraction z : ℝ) = 1 / (16 * (2 : ℝ) ^ z) := by
  unfold contraction
  push_cast
  rw [pow_add]
  norm_num
  ring

theorem precision_pow (z : ℕ) :
    (2 : ℝ) ^ precision z = 1024 * ((2 : ℝ) ^ z) ^ 4 := by
  rw [precision, pow_add, mul_comm 4 z, pow_mul]
  norm_num
  ring

private theorem power_room (T : ℝ) (hT : 1 ≤ T) : 32 * T ^ 3 ≤ 1024 * T ^ 4 := by
  have hp : T ^ 3 ≤ T ^ 4 := pow_le_pow_right₀ hT (by norm_num)
  have hpos : 0 ≤ T ^ 4 := pow_nonneg (zero_le_one.trans hT) _
  linarith only [hp, hpos]

/-- The precision pays for contraction even when the original variance cap is saturated. -/
theorem variance_precision (z d : ℕ) (c B : ℝ) (hc : 0 ≤ c)
    (hcz : c ≤ (2 : ℝ) ^ z) (hd : (d : ℝ) ≤ (2 : ℝ) ^ z) (hB : 1 ≤ B) :
    2 * c ^ 2 * ((d : ℝ) * (1 / (2 : ℝ) ^ precision z)) ^ 2 ≤
      (1 - (contraction z : ℝ)) ^ 2 * B ^ 2 := by
  let T := (2 : ℝ) ^ z
  have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hT0 : 0 < T := by positivity
  have hden : 0 < 1024 * T ^ 4 := by positivity
  have hsmall : 2 * c * ((d : ℝ) / (1024 * T ^ 4)) ≤ 1 / (16 * T) := by
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < 16 * T),
      div_mul_eq_mul_div, div_le_iff₀ hden]
    calc
      _ ≤ (2 * T * T) * (16 * T) := by gcongr
      _ = 32 * T ^ 3 := by ring
      _ ≤ _ := by simpa only [one_mul] using power_room T hT
  have hsq := pow_le_pow_left₀ (by positivity :
    0 ≤ 2 * c * ((d : ℝ) / (1024 * T ^ 4))) hsmall 2
  have hBsq : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hpaid := mul_le_mul_of_nonneg_left hBsq (sq_nonneg (1 / (16 * T)))
  rw [precision_pow, contraction_gap]
  change 2 * c ^ 2 * ((d : ℝ) * (1 / (1024 * T ^ 4))) ^ 2 ≤
    (1 / (16 * T)) ^ 2 * B ^ 2
  have hn := sq_nonneg (c * ((d : ℝ) / (1024 * T ^ 4)))
  simp only [mul_one] at hpaid
  simp only [div_eq_mul_inv, one_mul] at hsq hn hpaid ⊢
  nlinarith only [hsq, hpaid, hn]

/-- The same precision loses less than the half-unit margin available in a prepared node. -/
theorem center_loss (z d : ℕ) (c R : ℝ) (hc : 0 ≤ c)
    (hcz : c ≤ (2 : ℝ) ^ z) (hd : (d : ℝ) ≤ (2 : ℝ) ^ z)
    (hR : R ≤ (2 : ℝ) ^ z) :
    (1 - (contraction z : ℝ)) * R +
      2 * (d : ℝ) ^ 2 * (1 / (2 : ℝ) ^ precision z) * c ≤ 1 / 2 := by
  let T := (2 : ℝ) ^ z
  have hT : 1 ≤ T := one_le_pow₀ (by norm_num)
  have hT0 : 0 < T := by positivity
  have hfirst : (1 / (16 * T)) * R ≤ 1 / 16 := by
    calc
      _ ≤ (1 / (16 * T)) * T := by gcongr
      _ = _ := by field_simp
  have hsecond : 2 * (d : ℝ) ^ 2 * (1 / (1024 * T ^ 4)) * c ≤ 1 / 16 := by
    calc
      _ ≤ 2 * T ^ 2 * (1 / (1024 * T ^ 4)) * T := by gcongr
      _ = (2 * T ^ 3) / (1024 * T ^ 4) := by ring
      _ ≤ 1 / 16 := by
        rw [div_le_iff₀ (by positivity : 0 < 1024 * T ^ 4)]
        have hp := power_room T hT
        linarith only [hp]
  rw [precision_pow, contraction_gap]
  change (1 / (16 * T)) * R + _ ≤ _
  linarith only [hfirst, hsecond]

theorem precision_polytime {α : Type} {input : α ↪ List Bool} {z : α → ℕ}
    (hz : ComputableInPolyTime z input encUnary) :
    ComputableInPolyTime (fun x ↦ precision (z x)) input encUnary := by
  exact unary_add' (unary_mul' (const 4) hz) (const 10)

theorem contraction_polytime {α : Type} {input : α ↪ List Bool} {z : α → ℕ}
    (hz : ComputableInPolyTime z input encUnary) :
    ComputableInPolyTime (fun x ↦ contraction (z x)) input Encoding.encRat := by
  exact rat_sub' (const 1) (rat_div' (const 1)
    (rat_two_pow' (unary_add' hz (const 4))))

end ABBKS26.Assembly.Exec.RefineSynth.FrobPrecision
