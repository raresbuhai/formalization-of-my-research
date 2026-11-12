module

public import BDT24.LowDeg.Hermite
public import BDT24.LowDeg.Norm
public import BDT24.LowDeg.Overlap
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Theorem B.4

`BDT24.LowDeg.lowDegree_negSPCA_main`: the statement of `BDT24.lowDegree_negSPCA` in
`BDT24/Challenge.lean`. With `D = ⌊k^δ⌋`, the advantage is at most the square root of
`∑_{L=1}^{⌊D/2⌋} (n + L)^L / L! · E ⟨x_u, x_v⟩^(2L)` (`BDT24.LowDeg.advantage_le_of_hermite`,
`BDT24.LowDeg.lowDegNorm_le`), and with `BDT24.LowDeg.overlapMoment_le` and `L^L / L! ≤ e^L` each
term is at most `r^L` with `r = e C (n + D)(1/d + D/k²)`, so the sum is at most `2r` once `r ≤ 1/2`.
Under `n ≤ η min(d, k^(2-δ))`, `(n + D)(1/d + D/k²) ≤ n/d + n D/k² + D/d + D²/k²
≤ 2η + k^(δ-1) + k^(2δ-2)`, which is small for small `η` and large `k`.
-/

@[expose] public section

namespace BDT24.LowDeg

open MeasureTheory ProbabilityTheory

namespace MN

/-- A bound on the advantage at degree `⌊D⌋` is one at degree `D`, and the advantage bound may be
raised. -/
theorem advantageAtMost_floor_mono_qz {Ω ι : Type} [MeasurableSpace Ω] {x : Ω → ι → ℝ} {D : ℝ}
    {P Q : Measure Ω} {ε ε' : ℝ} (h : AdvantageAtMost x (⌊D⌋₊ : ℝ) P Q ε) (hε : ε ≤ ε') :
    AdvantageAtMost x D P Q ε' := by
  intro f hf
  obtain ⟨h1, h2, h3⟩ := h f (by exact_mod_cast Nat.le_floor hf)
  exact ⟨h1, h2, h3.trans (mul_le_mul_of_nonneg_right hε (Real.sqrt_nonneg _))⟩

/-- `∑_{L=1}^{M} r^L ≤ 2r` for `0 ≤ r ≤ 1/2`. -/
theorem sum_pow_Icc_le_two_mul_qz {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (M : ℕ) :
    ∑ L ∈ Finset.Icc 1 M, r ^ L ≤ 2 * r := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  refine (geom_sum_Ico_le_of_lt_one hr0 (by linarith)).trans ?_
  rw [pow_one, div_le_iff₀ (by linarith)]
  nlinarith

/-- One term of the sum: `(n + L)^L / L! · E ⟨x_u, x_v⟩^(2L) ≤ (e C (n + D)(1/d + D/k²))^L` for
`1 ≤ L ≤ D`, from a bound `(C L)^L (1/d + L/k²)^L` on the moments. -/
theorem term_le_qz {C : ℝ} (hC : 0 < C)
    (hov : ∀ d k L : ℕ, 1 ≤ k → k ≤ d → 1 ≤ L →
      overlapMoment d k L ≤ (C * L) ^ L * (1 / d + L / k ^ 2) ^ L)
    {n d k D L : ℕ} (hk : 1 ≤ k) (hkd : k ≤ d) (hL1 : 1 ≤ L) (hLD : L ≤ D) :
    ((n : ℝ) + L) ^ L / L.factorial * overlapMoment d k L ≤
      (Real.exp 1 * C * ((n : ℝ) + D) * (1 / d + D / k ^ 2)) ^ L := by
  have hLD' : (L : ℝ) ≤ D := by exact_mod_cast hLD
  calc ((n : ℝ) + L) ^ L / L.factorial * overlapMoment d k L
      ≤ ((n : ℝ) + L) ^ L / L.factorial * ((C * L) ^ L * (1 / d + L / k ^ 2) ^ L) :=
        mul_le_mul_of_nonneg_left (hov d k L hk hkd hL1) (by positivity)
    _ = (C * ((n : ℝ) + L) * (1 / d + L / k ^ 2)) ^ L * ((L : ℝ) ^ L / L.factorial) := by
        rw [mul_pow, mul_pow, mul_pow]; ring
    _ ≤ (C * ((n : ℝ) + L) * (1 / d + L / k ^ 2)) ^ L * Real.exp L :=
        mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) L)
          (by positivity)
    _ = (Real.exp 1 * C * ((n : ℝ) + L) * (1 / d + L / k ^ 2)) ^ L := by
        rw [← Real.exp_one_pow, ← mul_pow]; congr 1; ring
    _ ≤ (Real.exp 1 * C * ((n : ℝ) + D) * (1 / d + D / k ^ 2)) ^ L :=
        pow_le_pow_left₀ (by positivity) (by gcongr) L

/-- The parameters: `(n + D)(1/d + D/k²) ≤ 4τ` for `D = ⌊k^δ⌋`, `n ≤ τ min(d, k^(2-δ))` and
`k ≥ 1/τ²`, when `0 < δ ≤ 1/10` and `0 < τ ≤ 1`. -/
theorem params_le_qz {δ τ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 10) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    {n d k : ℕ} (hk1 : 1 ≤ k) (hkτ : 1 / τ ^ 2 ≤ k) (hkd : k ≤ d)
    (hn : (n : ℝ) ≤ τ * min (d : ℝ) ((k : ℝ) ^ (2 - δ))) :
    ((n : ℝ) + ⌊(k : ℝ) ^ δ⌋₊) * (1 / d + ⌊(k : ℝ) ^ δ⌋₊ / k ^ 2) ≤ 4 * τ := by
  set D : ℕ := ⌊(k : ℝ) ^ δ⌋₊
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hkd' : (k : ℝ) ≤ d := by exact_mod_cast hkd
  have hd0 : (0 : ℝ) < d := by linarith
  have hDk : (D : ℝ) ≤ (k : ℝ) ^ δ := Nat.floor_le (by positivity)
  have hD0 : (0 : ℝ) ≤ D := by positivity
  -- `D² ≤ k`
  have hD2 : (D : ℝ) ^ 2 ≤ k := by
    calc (D : ℝ) ^ 2 ≤ ((k : ℝ) ^ δ) ^ 2 := pow_le_pow_left₀ hD0 hDk 2
      _ = (k : ℝ) ^ (2 * δ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hk0.le]; norm_num [mul_comm]
      _ ≤ (k : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hk1' (by linarith)
      _ = k := Real.rpow_one _
  -- `1/k ≤ τ²`
  have hkinv : 1 / (k : ℝ) ≤ τ ^ 2 := by
    rw [div_le_iff₀ hk0]
    rw [div_le_iff₀ (by positivity)] at hkτ
    linarith
  -- `D²/k² ≤ τ²`
  have hDk2 : (D : ℝ) ^ 2 / (k : ℝ) ^ 2 ≤ τ ^ 2 := by
    calc (D : ℝ) ^ 2 / (k : ℝ) ^ 2 ≤ (k : ℝ) / (k : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hD2 (by positivity)
      _ = 1 / (k : ℝ) := by field_simp
      _ ≤ τ ^ 2 := hkinv
  -- `D/k ≤ τ`
  have hDkτ : (D : ℝ) / k ≤ τ := by
    rw [← pow_le_pow_iff_left₀ (by positivity) hτ0.le two_ne_zero, div_pow]
    exact hDk2
  -- the four terms
  have h1 : (n : ℝ) / d ≤ τ := by
    rw [div_le_iff₀ hd0]
    exact hn.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hτ0.le)
  have h2 : (n : ℝ) * D / (k : ℝ) ^ 2 ≤ τ := by
    rw [div_le_iff₀ (by positivity)]
    have hn' : (n : ℝ) ≤ τ * (k : ℝ) ^ (2 - δ) :=
      hn.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hτ0.le)
    calc (n : ℝ) * D ≤ τ * (k : ℝ) ^ (2 - δ) * (k : ℝ) ^ δ :=
          mul_le_mul hn' hDk hD0 (by positivity)
      _ = τ * (k : ℝ) ^ ((2 - δ) + δ) := by rw [Real.rpow_add hk0]; ring
      _ = τ * (k : ℝ) ^ 2 := by norm_num
  have h3 : (D : ℝ) / d ≤ τ :=
    (div_le_div_of_nonneg_left hD0 hk0 hkd').trans hDkτ
  have h4 : (D : ℝ) ^ 2 / (k : ℝ) ^ 2 ≤ τ := by nlinarith
  calc ((n : ℝ) + D) * (1 / d + D / k ^ 2)
      = (n : ℝ) / d + (n : ℝ) * D / (k : ℝ) ^ 2 + (D : ℝ) / d + (D : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
        ring
    _ ≤ 4 * τ := by linarith

end MN

open MN in
/-- **[BDT24, Theorem B.4]**, the statement of `BDT24/Challenge.lean`. -/
theorem lowDegree_negSPCA_main :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 10 → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∃ k₀ : ℕ,
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ n d k : ℕ, k₀ ≤ k → k ≤ d →
        (n : ℝ) ≤ η * min (d : ℝ) ((k : ℝ) ^ (2 - δ)) →
        AdvantageAtMost sampleCoords ((k : ℝ) ^ δ) (plantedSample n d k θ) (nullSample n d) ε := by
  intro δ hδ0 hδ1 ε hε
  obtain ⟨C, hC, hov⟩ := overlapMoment_le
  set m : ℝ := min (1 / 2) (ε ^ 2 / 2)
  have hm0 : 0 < m := lt_min (by norm_num) (by positivity)
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set τ : ℝ := min 1 (m / (4 * Real.exp 1 * C))
  have hτ0 : 0 < τ := lt_min one_pos (by positivity)
  have hτ1 : τ ≤ 1 := min_le_left _ _
  have hτm : τ ≤ m / (4 * Real.exp 1 * C) := min_le_right _ _
  refine ⟨τ, hτ0, ⌈1 / τ ^ 2⌉₊ + 1, fun θ hθ0 hθ1 n d k hk hkd hn ↦ ?_⟩
  have hk1 : 1 ≤ k := le_of_add_le_right hk
  have hkτ : 1 / τ ^ 2 ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans hk)
  set D : ℕ := ⌊(k : ℝ) ^ δ⌋₊
  set r : ℝ := Real.exp 1 * C * ((n : ℝ) + D) * (1 / d + D / k ^ 2) with hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hr0 : 0 ≤ r := by positivity
  have hrm : r ≤ m := by
    have hp := params_le_qz hδ0 hδ1 hτ0 hτ1 hk1 hkτ hkd hn
    calc r = Real.exp 1 * C * (((n : ℝ) + D) * (1 / d + D / k ^ 2)) := by rw [hr]; ring
      _ ≤ Real.exp 1 * C * (4 * τ) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ Real.exp 1 * C * (4 * (m / (4 * Real.exp 1 * C))) := by gcongr
      _ = m := by field_simp
  have hsum : ∑ L ∈ Finset.Icc 1 (D / 2), ((n : ℝ) + L) ^ L / L.factorial * overlapMoment d k L
      ≤ ε ^ 2 := by
    calc ∑ L ∈ Finset.Icc 1 (D / 2), ((n : ℝ) + L) ^ L / L.factorial * overlapMoment d k L
        ≤ ∑ L ∈ Finset.Icc 1 (D / 2), r ^ L := by
          refine Finset.sum_le_sum fun L hL ↦ ?_
          obtain ⟨hL1, hL2⟩ := Finset.mem_Icc.mp hL
          exact term_le_qz hC hov hk1 hkd hL1 (hL2.trans (Nat.div_le_self _ _))
      _ ≤ 2 * r := sum_pow_Icc_le_two_mul_qz hr0 (hrm.trans (min_le_left _ _)) _
      _ ≤ 2 * m := by linarith
      _ ≤ ε ^ 2 := by linarith [min_le_right (1 / 2 : ℝ) (ε ^ 2 / 2)]
  have := isProbabilityMeasure_plantedSample (n := n) hkd θ
  have hadv := advantage_le_of_hermite sampleCoords measurable_sampleCoords
    (plantedSample n d k θ) (nullSample n d) (map_sampleCoords_nullSample n d)
    (integrable_plantedSample θ) D ((lowDegNorm_le hθ0.le hθ1.le D).trans hsum)
  refine advantageAtMost_floor_mono_qz hadv ?_
  rw [Real.sqrt_sq hε.le]

end BDT24.LowDeg
