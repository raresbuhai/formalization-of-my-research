module

public import ABBKS26.Tree.RefineAuxCore

/-! Numerical consequences of the centered depth schedule. -/

@[expose] public section

namespace ABBKS26.Tree.RefineBlocksAux

noncomputable section

open Common Matrix

variable {n k d : ℕ}

private theorem etaStar_le_square (w β : ℚ)
    (hw : 0 ≤ w ∧ w ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1) :
    Centered.etaStar w β ≤ β ^ 2 := by
  have hν0 : 0 ≤ Centered.nu w β := mul_nonneg hw.1 (pow_nonneg hβ.1 4)
  have hνβ : Centered.nu w β ≤ β := by
    have hh := pow_le_pow_of_le_one hβ.1 hβ.2 (show 1 ≤ 4 by omega)
    simp only [pow_one] at hh
    exact (mul_le_of_le_one_left (pow_nonneg hβ.1 4) hw.2).trans hh
  have hδ0 : 0 ≤ Centered.delta w β := pow_nonneg hν0 8
  have hδβ : Centered.delta w β ≤ β := by
    exact (pow_le_pow_left₀ hν0 hνβ 8).trans
      (by simpa only [pow_one] using pow_le_pow_of_le_one hβ.1 hβ.2 (show 1 ≤ 8 by omega))
  unfold Centered.etaStar
  exact (div_le_self (pow_nonneg hδ0 4) (by norm_num)).trans
    ((pow_le_pow_left₀ hδ0 hδβ 4).trans
      (pow_le_pow_of_le_one hβ.1 hβ.2 (by norm_num)))

/-- The grid and population rounding errors fit the scheduled spectral tail allowance. -/
theorem centered_budget
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (m : ℕ) (hm : 2 ≤ m) (hmk : m ≤ k) :
    let p := params h
    (0 < p.w ∧ p.w ≤ 1 / 2) ∧ 0 < p.subspaceAccuracy ∧ 1 ≤ p.K ∧
      (0 < p.tail ∧ p.tail ≤ 1) ∧
      ((p.subspaceAccuracy : ℝ) * (1024 * (p.K : ℝ) ^ 2 / p.tail) ^ (2 * (m - 1)) ≤
        1 / (128 * (4 / p.w : ℝ))) ∧
      (1 / (8 / (p.tail : ℝ)) + 2 * Real.sqrt η ≤ p.tail) := by
  let p := params h
  have hleak := hp.leakageBudget_nonneg .centered M ε w η Δ D ω r params h (by omega)
  have hweight := hp.weight_at .centered M ε w η Δ D ω r params h (by omega)
  obtain ⟨_, _, _, hwR, _, hε, hη, _, _, _, _, _, _, _, hready, hparams⟩ := hp
  obtain ⟨hw, hw2, hβ, hβ100, hφ, ht, _, _, _, _, _, htail, _, _, _, _, hm'⟩ :=
    hready h hh
  obtain ⟨_, hK, _, _, _, _, _, hbudget, _, hE, hc, _⟩ := hm'
  have hφ1 : (p.straddle : ℝ) ≤ 1 :=
    ((hparams h (by omega)).2.2.2.2.2.2 hh).2.2.1.trans
      (Real.exp_le_one_iff.mpr (by norm_num))
  have hK1 : 1 ≤ p.K := by
    apply le_trans _ hK
    rw [le_div_iff₀ hφ]
    have hhQ : p.straddle ≤ 1 := by exact_mod_cast hφ1
    linarith only [hhQ]
  have ht1 : p.tail ≤ 1 :=
    ((htail.trans (min_le_right _ _)).trans (min_le_right _ _)).trans
      (by linarith only [hw2] : p.w / 4096 ≤ 1)
  have hB : (1 : ℚ) ≤ 1024 * p.K ^ 2 / p.tail := by
    rw [le_div_iff₀ ht]
    nlinarith only [one_le_pow₀ hK1 (n := 2), ht1]
  have hC : (1 : ℚ) ≤ 4 / p.w := by
    rw [le_div_iff₀ hw]
    linarith only [hw2]
  have hbudgetQ : p.subspaceAccuracy * (1024 * p.K ^ 2 / p.tail) ^ (2 * (k - 1)) ≤
      1 / (128 * (4 / p.w)) := by
    have hpos : (0 : ℚ) < 1024 * p.K ^ 2 / p.tail := by positivity
    have he : p.tail / (1024 * p.K ^ 2) = (1024 * p.K ^ 2 / p.tail)⁻¹ := by
      field_simp
    rw [he, inv_pow, ← div_eq_mul_inv] at hbudget
    exact (le_div_iff₀ (pow_pos hpos _)).mp (by simpa only [one_div] using hbudget)
  have hbudgetM : p.subspaceAccuracy * (1024 * p.K ^ 2 / p.tail) ^ (2 * (m - 1)) ≤
      1 / (128 * (4 / p.w)) := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by omega)) hβ.le).trans hbudgetQ
  have hβB : p.subspaceAccuracy * (1024 * p.K ^ 2 / p.tail) ≤ 1 := by
    have hh := (mul_le_mul_of_nonneg_left
      (le_self_pow₀ hB (by omega : 2 * (k - 1) ≠ 0)) hβ.le).trans hbudgetQ
    exact hh.trans ((div_le_one (by positivity)).mpr (by linarith only [hC]))
  have hβtail : p.subspaceAccuracy ≤ p.tail / 1024 := by
    have hh := (div_le_iff₀ ht).mp (show p.subspaceAccuracy *
      (1024 * p.K ^ 2) / p.tail ≤ 1 by simpa only [mul_div_assoc] using hβB)
    have hpow := one_le_pow₀ hK1 (n := 2)
    rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 1024)]
    nlinarith only [hh, mul_le_mul_of_nonneg_left hpow hβ.le]
  have hE0 : 0 ≤ p.momentError := by rw [hE]; unfold Centered.etaStar; positivity
  have hden : (1 : ℚ) ≤ 10000 * (2 * (80 / p.w) ^ 4) := by
    have hb : (1 : ℚ) ≤ 80 / p.w := by
      rw [le_div_iff₀ hw]
      linarith only [hw2]
    nlinarith only [one_le_pow₀ hb (n := 4)]
  have hcE : p.contamination ≤ p.momentError := hc.trans (div_le_self hE0 hden)
  have hEβ : p.momentError ≤ p.subspaceAccuracy ^ 2 := by
    rw [hE]
    exact etaStar_le_square _ _ ⟨by positivity, by linarith only [hw2]⟩
      ⟨hβ.le, hβ100.trans (by norm_num)⟩
  have hηc : η ≤ (p.contamination : ℝ) := by
    obtain ⟨_, hleakp, hcont, _⟩ := hparams h (by omega)
    have hl0 : (0 : ℝ) ≤ p.leakage := hleak.trans hleakp
    have hn : (0 : ℝ) ≤ 1 / n := by positivity
    have hh := (div_le_iff₀ hwR).mp hcont
    have hc0 : (0 : ℝ) ≤ p.contamination := by
      have hh0 : 0 ≤ 8 * ((p.leakage : ℝ) + ε + η + 1 / n) / w := by positivity
      exact hh0.trans hcont
    have hw1 : w ≤ 1 := by
      have hhQ := Rat.cast_le (K := ℝ) |>.mpr hw2
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hhQ
      linarith only [hweight, hhQ]
    have hm := mul_le_mul_of_nonneg_left hw1 hc0
    nlinarith only [hh, hm, hl0, hε, hn, hη.le]
  have hηβ : η ≤ (p.subspaceAccuracy : ℝ) ^ 2 :=
    hηc.trans (by exact_mod_cast hcE.trans hEβ)
  have hroot : Real.sqrt η ≤ (p.subspaceAccuracy : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by exact_mod_cast hβ.le, hηβ⟩
  refine ⟨⟨hw, hw2⟩, hβ, hK1, ⟨ht, ht1⟩, ?_, ?_⟩
  · exact_mod_cast hbudgetM
  · have htR : (0 : ℝ) < p.tail := by exact_mod_cast ht
    have hβtailR : (p.subspaceAccuracy : ℝ) ≤ (p.tail : ℝ) / 1024 := by
      exact_mod_cast hβtail
    rw [one_div_div]
    nlinarith only [hroot, hβtailR, htR]

end

end ABBKS26.Tree.RefineBlocksAux
