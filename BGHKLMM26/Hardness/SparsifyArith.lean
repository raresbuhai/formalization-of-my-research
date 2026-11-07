module

public import BGHKLMM26.Hardness.Sparsify
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Sparsification: the arithmetic of the soundness proof

The inequalities behind [BGHKLMM26, Lemma 6.6], with the robust inverse in Eldan's form: at each
dyadic level `η ∈ [λ, η₀]`, `λ = K log² D / D` with `K = 2 (96 C₁² + 16)`, the Hamming radius
`δ = min(C₁ √(η log(1/η)), 1)` (`BGHKLMM26.Hard.radius`) satisfies
`δ log(e/δ) ≤ ½ · D t² / (12 δ + 4 t)` for `t = η/2` (`BGHKLMM26.Hard.radius_entropy_le`), since
`D η ≥ K log² D` and `log(1/η) ≤ log D`; and the Bernstein exponent is at least `D λ² / 56`
(`BGHKLMM26.Hard.bernstein_exponent_ge`). The conditions on `D` hold for `D ≥ D₀`
(`BGHKLMM26.Hard.exists_D₀`).

With Eldan's error the entropy bound needs `D η ≳ log² D`, so the smallest level is
`K log² D / D` and the theorem has the paper's `log² d`.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Real

/-- The constant `κ = min(C₁ √log(1/η₀), 1)`: the radius `min(C₁ √(η log(1/η)), 1)` is at least
`κ √η` for `η ≤ η₀`. -/
noncomputable def kap (C₁ η₀ : ℝ) : ℝ := min (C₁ * √(log (1 / η₀))) 1

/-- How large `log D` must be. -/
noncomputable def ellReq (C₁ η₀ : ℝ) : ℝ := max (1 + log (1 / kap C₁ η₀)) (2 * (96 * C₁ ^ 2 + 16))

/-- The Hamming radius at level `η`, capped at `1`. -/
noncomputable def radius (C₁ η : ℝ) : ℝ := min (C₁ * √(η * log (1 / η))) 1

theorem kap_pos {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀ : 0 < η₀) (hη₀1 : η₀ < 1) :
    0 < kap C₁ η₀ := by
  unfold kap
  have : 0 < log (1 / η₀) := log_pos (by rw [lt_div_iff₀ hη₀]; linarith)
  positivity

theorem kap_le_one (C₁ η₀ : ℝ) : kap C₁ η₀ ≤ 1 := min_le_right _ _

theorem radius_le_one (C₁ η : ℝ) : radius C₁ η ≤ 1 := min_le_right _ _

theorem one_le_lamK (C₁ : ℝ) : 1 ≤ lamK C₁ := by
  unfold lamK
  nlinarith [sq_nonneg C₁]

theorem lam_eq_mul (C₁ : ℝ) (D : ℕ) (hD : (0 : ℝ) < D) :
    (D : ℝ) * lam C₁ D = lamK C₁ * log D ^ 2 := by
  unfold lam
  field_simp

theorem one_div_le_lam {C₁ : ℝ} {D : ℕ} (hD : (0 : ℝ) < D) (hl : 1 ≤ log D) :
    1 / (D : ℝ) ≤ lam C₁ D := by
  unfold lam
  apply div_le_div_of_nonneg_right _ hD.le
  have := one_le_lamK C₁
  have : 1 ≤ log D ^ 2 := one_le_pow₀ hl
  nlinarith

theorem lam_pos_of_log {C₁ : ℝ} {D : ℕ} (hD : (0 : ℝ) < D) (hl : 1 ≤ log D) : 0 < lam C₁ D :=
  lt_of_lt_of_le (by positivity) (one_div_le_lam hD hl)

/-- The radius is at least `κ √η`. -/
theorem kap_mul_sqrt_le_radius {C₁ η₀ η : ℝ} (hC₁ : 0 < C₁) (hη : 0 < η) (hηη₀ : η ≤ η₀)
    (hη₀1 : η₀ < 1) : kap C₁ η₀ * √η ≤ radius C₁ η := by
  have hη₀ : 0 < η₀ := lt_of_lt_of_le hη hηη₀
  have hη1 : η < 1 := lt_of_le_of_lt hηη₀ hη₀1
  have hlog : log (1 / η₀) ≤ log (1 / η) := by
    apply log_le_log (by positivity)
    exact one_div_le_one_div_of_le hη hηη₀
  have hlog0 : 0 < log (1 / η₀) := log_pos (by rw [lt_div_iff₀ hη₀]; linarith)
  have hsq1 : √η ≤ 1 := by rw [sqrt_le_one]; exact hη1.le
  unfold radius kap
  apply le_min
  · calc min (C₁ * √(log (1 / η₀))) 1 * √η ≤ C₁ * √(log (1 / η₀)) * √η :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (sqrt_nonneg _)
      _ = C₁ * (√η * √(log (1 / η₀))) := by ring
      _ ≤ C₁ * √(η * log (1 / η)) := by
          apply mul_le_mul_of_nonneg_left _ hC₁.le
          rw [← sqrt_mul hη.le]
          exact sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog hη.le)
  · calc min (C₁ * √(log (1 / η₀))) 1 * √η ≤ 1 * 1 :=
          mul_le_mul (min_le_right _ _) hsq1 (sqrt_nonneg _) (by norm_num)
      _ = 1 := by norm_num

theorem radius_pos {C₁ η₀ η : ℝ} (hC₁ : 0 < C₁) (hη : 0 < η) (hηη₀ : η ≤ η₀) (hη₀1 : η₀ < 1) :
    0 < radius C₁ η :=
  lt_of_lt_of_le (mul_pos (kap_pos hC₁ (lt_of_lt_of_le hη hηη₀) hη₀1) (sqrt_pos.2 hη))
    (kap_mul_sqrt_le_radius hC₁ hη hηη₀ hη₀1)

/-- The square of the radius is at most `C₁² η log(1/η)`. -/
theorem radius_sq_le {C₁ η : ℝ} (hC₁ : 0 < C₁) (hη : 0 < η) (hη1 : η ≤ 1) :
    radius C₁ η ^ 2 ≤ C₁ ^ 2 * (η * log (1 / η)) := by
  have h0 : 0 ≤ η * log (1 / η) :=
    mul_nonneg hη.le (log_nonneg (by rw [le_div_iff₀ hη]; linarith))
  have h1 : 0 ≤ radius C₁ η := le_min (by positivity) (by norm_num)
  have h2 : radius C₁ η ≤ C₁ * √(η * log (1 / η)) := min_le_left _ _
  calc radius C₁ η ^ 2 ≤ (C₁ * √(η * log (1 / η))) ^ 2 := pow_le_pow_left₀ h1 h2 2
    _ = C₁ ^ 2 * (η * log (1 / η)) := by rw [mul_pow, sq_sqrt h0]

/-- `log(e/δ) ≤ 1 + log(1/κ) + log D` for the radius `δ` at a level `η ≥ 1/D`. -/
theorem log_e_div_radius_le {C₁ η₀ η : ℝ} {D : ℝ} (hC₁ : 0 < C₁) (hη : 0 < η) (hηη₀ : η ≤ η₀)
    (hη₀1 : η₀ < 1) (hD : 0 < D) (hηD : 1 / D ≤ η) :
    log (exp 1 / radius C₁ η) ≤ 1 + log (1 / kap C₁ η₀) + log D := by
  have hη₀ : 0 < η₀ := lt_of_lt_of_le hη hηη₀
  have hk := kap_pos hC₁ hη₀ hη₀1
  have hr := radius_pos hC₁ hη hηη₀ hη₀1
  have hkr := kap_mul_sqrt_le_radius hC₁ hη hηη₀ hη₀1
  have hsq : 0 < √η := sqrt_pos.2 hη
  rw [log_div (exp_pos 1).ne' hr.ne', log_exp]
  have h1 : log (kap C₁ η₀ * √η) ≤ log (radius C₁ η) := log_le_log (by positivity) hkr
  rw [log_mul hk.ne' hsq.ne', log_sqrt hη.le] at h1
  have h2 : log (1 / η) ≤ log D := by
    apply log_le_log (by positivity)
    rw [div_le_iff₀ hη]
    rw [div_le_iff₀ hD] at hηD
    linarith
  rw [one_div, log_inv] at h2
  rw [one_div, log_inv]
  have := log_nonpos hη.le (by linarith : η ≤ 1)
  linarith

/-- `log(e/δ) ≥ 1` for a radius `δ ≤ 1`. -/
theorem one_le_log_e_div_radius {C₁ η₀ η : ℝ} (hC₁ : 0 < C₁) (hη : 0 < η) (hηη₀ : η ≤ η₀)
    (hη₀1 : η₀ < 1) : 1 ≤ log (exp 1 / radius C₁ η) := by
  have hr := radius_pos hC₁ hη hηη₀ hη₀1
  rw [log_div (exp_pos 1).ne' hr.ne', log_exp]
  have := log_nonpos hr.le (radius_le_one C₁ η)
  linarith

/-- **The exponent at one level** [BGHKLMM26, proof of Lemma 6.6]: for `log D` large and
`λ ≤ η ≤ η₀`, the Hamming ball of radius `δ = min(C₁ √(η log(1/η)), 1)` is small next to
Bernstein's bound at deviation `η/2`: `δ log(e/δ) ≤ ½ D t² / (12 δ + 4 t)`, `t = η/2`. -/
theorem radius_entropy_le {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀1 : η₀ < 1) {D : ℕ} (hD : (0 : ℝ) < D)
    (hl1 : 1 ≤ log D) (hl : ellReq C₁ η₀ ≤ log D) {η : ℝ} (hlη : lam C₁ D ≤ η)
    (hηη₀ : η ≤ η₀) :
    radius C₁ η * log (exp 1 / radius C₁ η) ≤
      (1 / 2) * (D * (η / 2) ^ 2 / (12 * radius C₁ η + 4 * (η / 2))) := by
  have hlam := lam_pos_of_log (C₁ := C₁) hD hl1
  have hη : 0 < η := lt_of_lt_of_le hlam hlη
  have hη1 : η ≤ 1 := hηη₀.trans hη₀1.le
  have hηD : 1 / (D : ℝ) ≤ η := (one_div_le_lam hD hl1).trans hlη
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = radius C₁ η := ⟨_, rfl⟩
  rw [← hδ]
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = log (exp 1 / δ) := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = log (D : ℝ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = log (1 / kap C₁ η₀) := ⟨_, rfl⟩
  rw [← hΛ]
  have hδ0 : 0 < δ := hδ ▸ radius_pos hC₁ hη hηη₀ hη₀1
  have hδ1 : δ ≤ 1 := hδ ▸ radius_le_one C₁ η
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, hδ]; exact one_le_log_e_div_radius hC₁ hη hηη₀ hη₀1
  have hΛu : Λ ≤ 1 + B + ℓ := by
    rw [hΛ, hB, hℓ, hδ]; exact log_e_div_radius_le hC₁ hη hηη₀ hη₀1 hD hηD
  have hδsq : δ ^ 2 ≤ C₁ ^ 2 * (η * ℓ) := by
    rw [hδ]
    refine (radius_sq_le hC₁ hη hη1).trans ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hη.le
    rw [hℓ]
    apply log_le_log (by positivity)
    rw [div_le_iff₀ hη]
    rw [div_le_iff₀ hD] at hηD
    linarith
  have hreq : 1 + B ≤ ℓ ∧ 2 * (96 * C₁ ^ 2 + 16) ≤ ℓ := by
    rw [hB, hℓ]
    exact ⟨(le_max_left _ _).trans hl, (le_max_right _ _).trans hl⟩
  have hℓ1 : 1 ≤ ℓ := hℓ ▸ hl1
  have hDl : (D : ℝ) * lam C₁ D = lamK C₁ * ℓ ^ 2 := hℓ ▸ lam_eq_mul C₁ D hD
  -- `8 δ Λ (12 δ + 2 η) ≤ D η²`
  have hA : 96 * δ ^ 2 * Λ ≤ 96 * (C₁ ^ 2 * (η * ℓ)) * (1 + B + ℓ) :=
    mul_le_mul (by linarith) hΛu (by linarith) (by positivity)
  have hB' : 16 * δ * η * Λ ≤ 16 * η * (1 + B + ℓ) := by
    have : δ * Λ ≤ 1 * (1 + B + ℓ) := mul_le_mul hδ1 hΛu (by linarith) (by norm_num)
    nlinarith
  have hC : 96 * (C₁ ^ 2 * (η * ℓ)) * (1 + B + ℓ) + 16 * η * (1 + B + ℓ) ≤
      η * (lamK C₁ * ℓ ^ 2) := by
    have h1 : 1 + B + ℓ ≤ 2 * ℓ := by linarith [hreq.1]
    have h2 : 96 * C₁ ^ 2 * ℓ + 16 ≤ (96 * C₁ ^ 2 + 16) * ℓ := by nlinarith
    have h3 : (96 * C₁ ^ 2 * ℓ + 16) * (1 + B + ℓ) ≤ ((96 * C₁ ^ 2 + 16) * ℓ) * (2 * ℓ) :=
      mul_le_mul h2 h1 (by linarith) (by positivity)
    have h4 : ((96 * C₁ ^ 2 + 16) * ℓ) * (2 * ℓ) = lamK C₁ * ℓ ^ 2 := by unfold lamK; ring
    have : 96 * (C₁ ^ 2 * (η * ℓ)) * (1 + B + ℓ) + 16 * η * (1 + B + ℓ) =
        η * ((96 * C₁ ^ 2 * ℓ + 16) * (1 + B + ℓ)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (h4 ▸ h3) hη.le
  have hE : η * (lamK C₁ * ℓ ^ 2) ≤ D * η ^ 2 := by
    rw [← hDl]
    have := mul_le_mul_of_nonneg_left hlη (show (0 : ℝ) ≤ D * η by positivity)
    nlinarith
  have hmain : 8 * δ * Λ * (12 * δ + 2 * η) ≤ D * η ^ 2 := by nlinarith
  have hden : 0 < 12 * δ + 4 * (η / 2) := by positivity
  rw [mul_div_assoc', le_div_iff₀ hden]
  nlinarith

/-- The Bernstein exponent at every level is at least `D λ² / 56`. -/
theorem bernstein_exponent_ge {C₁ η₀ : ℝ} (hC₁ : 0 < C₁) (hη₀1 : η₀ < 1) {D : ℕ}
    (hD : (0 : ℝ) < D) (hl1 : 1 ≤ log D) {η : ℝ} (hlη : lam C₁ D ≤ η) (hηη₀ : η ≤ η₀) :
    D * lam C₁ D ^ 2 / 56 ≤ D * (η / 2) ^ 2 / (12 * radius C₁ η + 4 * (η / 2)) := by
  have hlam := lam_pos_of_log (C₁ := C₁) hD hl1
  have hη : 0 < η := lt_of_lt_of_le hlam hlη
  have hδ0 := radius_pos hC₁ hη hηη₀ hη₀1
  have hδ1 := radius_le_one C₁ η
  have hη1 : η ≤ 1 := hηη₀.trans hη₀1.le
  have hden : 0 < 12 * radius C₁ η + 4 * (η / 2) := by positivity
  have hden' : 12 * radius C₁ η + 4 * (η / 2) ≤ 14 := by linarith
  rw [div_le_div_iff₀ (by norm_num) hden]
  have h1 : lam C₁ D ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hlam.le hlη 2
  have h2 : D * lam C₁ D ^ 2 * (12 * radius C₁ η + 4 * (η / 2)) ≤ D * lam C₁ D ^ 2 * 14 :=
    mul_le_mul_of_nonneg_left hden' (by positivity)
  have h3 : D * lam C₁ D ^ 2 * 14 ≤ D * η ^ 2 * 14 := by
    have := mul_le_mul_of_nonneg_left h1 hD.le
    nlinarith
  nlinarith

/-- **The choice of `D₀`**: all the conditions on `D` hold for `D` large. -/
theorem exists_D₀ (C₁ : ℝ) {η₀ : ℝ} (hη₀ : 0 < η₀) : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    360 ≤ D ∧ 1 ≤ log D ∧ ellReq C₁ η₀ ≤ log D ∧ lam C₁ D ≤ η₀ ∧ 4 ≤ D * η₀ ^ 2 := by
  have hK : 0 < lamK C₁ := lt_of_lt_of_le one_pos (one_le_lamK C₁)
  have ht := (tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).eventually
    (Iio_mem_nhds (div_pos hη₀ hK))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ht
  refine ⟨max (max 360 ⌈N⌉₊) (max ⌈exp (max (ellReq C₁ η₀) 1)⌉₊ ⌈4 / η₀ ^ 2⌉₊),
    fun D hD ↦ ?_⟩
  simp only [max_le_iff] at hD
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hD
  have hD3 : (exp (max (ellReq C₁ η₀) 1) : ℝ) ≤ D := (Nat.le_ceil _).trans (by exact_mod_cast h3)
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (exp_pos _) hD3
  have hlog : max (ellReq C₁ η₀) 1 ≤ log D := by
    rw [← log_exp (max (ellReq C₁ η₀) 1)]
    exact log_le_log (exp_pos _) hD3
  refine ⟨h1, (le_max_right _ _).trans hlog, (le_max_left _ _).trans hlog, ?_, ?_⟩
  · have := hN D ((Nat.le_ceil _).trans (by exact_mod_cast h2))
    simp only [one_mul, add_zero] at this
    unfold lam
    rw [mul_div_assoc]
    have := (lt_div_iff₀' hK).1 this
    exact this.le
  · have h4' : 4 / η₀ ^ 2 ≤ (D : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast h4)
    rw [div_le_iff₀ (by positivity)] at h4'
    exact h4'

end BGHKLMM26.Hard
