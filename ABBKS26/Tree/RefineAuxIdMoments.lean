module

public import ABBKS26.Tree.RefineAuxAffine

/-! A weight floor close to the original weight for high-degree moment certification. -/

@[expose] public section

namespace ABBKS26.RefineAux

noncomputable section

open Common Matrix

/-- Losing only an inverse-degree fraction of the weight costs a constant in the moments. -/
def momentWeight (w : ℚ) (t : ℕ) : ℚ := w * (1 - 1 / (100 * t : ℚ))

theorem momentWeight_pos (w : ℚ) (t : ℕ) (hw : 0 < w) (ht : 1 ≤ t) :
    0 < momentWeight w t := by
  have htR : (1 : ℚ) ≤ t := by exact_mod_cast ht
  apply mul_pos hw
  apply sub_pos.mpr
  rw [div_lt_one (by positivity : (0 : ℚ) < 100 * t)]
  linarith only [htR]

theorem momentWeight_le (w : ℚ) (t : ℕ) (hw : 0 ≤ w) : momentWeight w t ≤ w := by
  apply mul_le_of_le_one_right hw
  have h : (0 : ℚ) ≤ 1 / (100 * t : ℚ) := by positivity
  linarith only [h]

private theorem moment_scale_power (t : ℕ) (ht : 1 ≤ t) :
    (1 / 2 : ℝ) ≤ (1 - 1 / (100 * t : ℝ)) ^ (4 * t) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hx : (1 / (100 * t : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity : (0 : ℝ) < 100 * t)]
    linarith only [htR]
  have hh := one_add_mul_le_pow (a := -(1 / (100 * t : ℝ))) (by linarith only [hx])
    (4 * t)
  have he : (1 : ℝ) + (4 * t : ℕ) * -(1 / (100 * t : ℝ)) = 24 / 25 := by
    push_cast
    field_simp
    ring
  rw [he] at hh
  exact (by norm_num : (1 / 2 : ℝ) ≤ 24 / 25).trans hh

/-- The near-original weight avoids an exponential loss from replacing `w` by `w / 2`. -/
theorem momentBudget_momentWeight (w : ℚ) (t r : ℕ)
    (hw : 0 < w) (hw1 : w ≤ 1 / 2) (ht : 1 ≤ t) (hr : r ≤ 4 * t) :
    Robust.momentBudget (momentWeight w t) r ≤
      2 * (2 * (80 * (t : ℝ) / w) ^ (4 * t)) := by
  let q : ℝ := 1 - 1 / (100 * t : ℝ)
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hw1R : (w : ℝ) ≤ 1 / 2 := by
    have hc := Rat.cast_le (K := ℝ) |>.mpr hw1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hweight : (0 : ℝ) < momentWeight w t := by
    exact_mod_cast momentWeight_pos w t hw ht
  have hweight1 : (momentWeight w t : ℝ) ≤ 1 / 2 := by
    have hh := (momentWeight_le w t hw.le).trans hw1
    have hc := Rat.cast_le (K := ℝ) |>.mpr hh
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hc
    exact hc
  have hcast : (momentWeight w t : ℝ) = (w : ℝ) * q := by
    simp only [momentWeight, Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_natCast, q]
  have hq : 0 < q := by
    rw [hcast] at hweight
    rcases mul_pos_iff.mp hweight with hh | hh
    · exact hh.2
    · exact False.elim (not_lt_of_ge hwR.le hh.1)
  have hbase : (1 : ℝ) ≤ 80 * t / (momentWeight w t : ℝ) := by
    rw [le_div_iff₀ hweight]
    linarith only [htR, hweight1]
  have hrR : (r : ℝ) ≤ 4 * t := by exact_mod_cast hr
  have hnum : 20 * (r : ℝ) / (momentWeight w t : ℝ) ≤
      80 * t / (momentWeight w t : ℝ) := by
    apply div_le_div_of_nonneg_right _ hweight.le
    linarith only [hrR]
  have hp : (20 * (r : ℝ) / (momentWeight w t : ℝ)) ^ r ≤
      (80 * t / (momentWeight w t : ℝ)) ^ (4 * t) :=
    (pow_le_pow_left₀ (by positivity) hnum r).trans (pow_le_pow_right₀ hbase hr)
  have he : (80 * (t : ℝ) / (momentWeight w t : ℝ)) ^ (4 * t) * q ^ (4 * t) =
      (80 * (t : ℝ) / w) ^ (4 * t) := by
    rw [← mul_pow, hcast]
    congr 1
    field_simp
  have hpow := moment_scale_power t ht
  change (1 / 2 : ℝ) ≤ q ^ (4 * t) at hpow
  have hm := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (80 * (t : ℝ) / (momentWeight w t : ℝ)) ^ (4 * t))
  rw [he] at hm
  unfold Robust.momentBudget
  nlinarith only [hp, hm]

/-- The schedule's denominator pays every degree up to `4t` with this weight floor. -/
theorem identical_moment_budget (p : Tree.StepParams) (η : ℝ) (t r : ℕ)
    (hw : 0 < p.w) (hw1 : p.w ≤ 1 / 2) (ht : 1 ≤ t) (hr : r ≤ 4 * t)
    (hη : 0 ≤ η ∧ η ≤ 1 / 100) (hηc : 8 * η ≤ p.contamination)
    (hc : p.contamination ≤ p.momentError /
      (10000 * (2 * (80 * (t : ℚ) / p.w) ^ (4 * t)))) :
    250 * (p.contamination : ℝ) * Robust.momentBudget (momentWeight p.w t) r +
      3 * (η / 10 ^ 8) ^ 2 * Robust.momentBudget (momentWeight p.w t) r ≤
        p.momentError := by
  let B : ℝ := 2 * (80 * (t : ℝ) / p.w) ^ (4 * t)
  have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw
  have htR : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hbound := momentBudget_momentWeight p.w t r hw hw1 ht hr
  change Robust.momentBudget (momentWeight p.w t) r ≤ 2 * B at hbound
  have hc' : (p.contamination : ℝ) ≤ (p.momentError : ℝ) / (10000 * B) := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr hc
    push_cast at hh
    exact hh
  have hbudget := (le_div_iff₀ (by positivity : 0 < 10000 * B)).mp hc'
  have hc0 : (0 : ℝ) ≤ p.contamination :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hη.1).trans hηc
  have hηsq : η ^ 2 ≤ η := by nlinarith only [hη.1, hη.2]
  have hθ : 3 * (η / 10 ^ 8) ^ 2 ≤ (p.contamination : ℝ) := by
    nlinarith only [hηsq, hη.1, hηc]
  have hmain := mul_le_mul_of_nonneg_left hbound
    (by positivity : 0 ≤ 250 * (p.contamination : ℝ))
  have hw' : (0 : ℝ) < momentWeight p.w t := by
    exact_mod_cast momentWeight_pos p.w t hw ht
  have htail := mul_le_mul hθ hbound
    (by unfold Robust.momentBudget; positivity) hc0
  have hcB := mul_nonneg hc0 hB.le
  nlinarith only [hbudget, hmain, htail, hcB]

/-- The scheduled moment error is smaller than the inverse-degree weight allowance. -/
theorem etaStar_weight_allowance (w β : ℚ) (hβ : 0 < β ∧ β ≤ 1 / 100) :
    IdCov.etaStar w β / 4 ≤ 1 / (1000 * IdCov.tDegree w : ℚ) := by
  let t := IdCov.tDegree w
  have ht : (3 : ℚ) ≤ t := by
    exact_mod_cast (show 3 ≤ t by unfold t IdCov.tDegree; omega)
  have heps : 0 ≤ IdCov.epsilonR β ∧ IdCov.epsilonR β ≤ 1 := by
    refine ⟨by unfold IdCov.epsilonR; positivity, ?_⟩
    exact pow_le_one₀ (div_nonneg hβ.1.le (by norm_num)) (by linarith only [hβ.2])
  have hc : 0 ≤ IdCov.cStar β ∧ IdCov.cStar β ≤ 1 := by
    have hpow := pow_le_one₀ heps.1 heps.2 (n := 2)
    refine ⟨by unfold IdCov.cStar; positivity, ?_⟩
    change IdCov.epsilonR β ^ 2 / 3 ≤ 1
    linarith only [hpow]
  have hbase : 0 ≤ IdCov.cStar β / (64 * t) ∧
      IdCov.cStar β / (64 * t) ≤ 1 := by
    refine ⟨div_nonneg hc.1 (by positivity), ?_⟩
    rw [div_le_one (by positivity : (0 : ℚ) < 64 * t)]
    linarith only [hc.2, ht]
  have hid : IdCov.epsilonId w β ≤ 1 := pow_le_one₀ hbase.1 hbase.2
  have hpow : (8 * (t : ℚ)) ^ 2 ≤ (8 * (t : ℚ)) ^ (4 * t + 2) :=
    pow_le_pow_right₀ (by linarith only [ht]) (by omega)
  have hden : 1000 * (t : ℚ) ≤ 16 * (8 * (t : ℚ)) ^ (4 * t + 2) := by
    nlinarith only [hpow, ht, mul_nonneg (by linarith only [ht] : 0 ≤ (t : ℚ))
      (by linarith only [ht] : 0 ≤ (t : ℚ) - 1)]
  have he : IdCov.etaStar w β / 4 =
      IdCov.epsilonId w β / (16 * (8 * (t : ℚ)) ^ (4 * t + 2)) := by
    unfold IdCov.etaStar IdCov.epsilonSys
    ring
  rw [he]
  calc
    _ ≤ 1 / (16 * (8 * (t : ℚ)) ^ (4 * t + 2)) := by
      exact div_le_div_of_nonneg_right hid (by positivity)
    _ ≤ 1 / (1000 * (t : ℚ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

end

end ABBKS26.RefineAux
