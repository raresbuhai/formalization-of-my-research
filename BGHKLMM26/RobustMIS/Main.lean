module

public import BGHKLMM26.RobustMIS.Transfer

/-!
# Robust Majority is Stablest

[BGHKLMM26, Theorem 7.1] with the error `C √η`, `BGHKLMM26.Hard.RobustMIS`, from the Gaussian
lemma with the error `C √Δ` taken as a hypothesis: `robustMIS_of_sharp (hG : GaussSharp)`, from
Corollary `positive-transfer` (`BGHKLMM26.RobustMIS.positive_transfer`) and Majority is Stablest
(`OAI.OptimalMaxCut.MISProof.untruncated_majority_is_stablest`), following the paper's proof of
Theorem 7.1. (`BGHKLMM26.RobustMIS.robustMIS`, in `Final.lean`, discharges `hG` with
`gaussian_sharp`.)

For `ρ ∈ (-1, 0)`, `t = -ρ` and `h = 2g - 1` with mean `m`: the cut condition is
`Stab_ρ(h) ≤ (2/π) arcsin ρ + 2η`; with the even and odd parts `Ev`, `Od` of the spectrum,
`Stab_ρ(h) = Ev - Od`, `Stab_t(h) = Ev + Od`, `Ev ≥ m²`, and Majority is Stablest for the odd
part `Od = Stab_t(h_odd) ≤ (2/π) arcsin t + ξ₁`. Hence `m² ≤ 2η + ξ₁` (so `E g ∈ [1/4, 3/4]`) and
`Stab_t(h) ≥ (2/π) arcsin t - 2η`, so that, by the quadratic bound on `Γ_t` at `1/2` and
Sheppard's formula, `D = Γ_t(E g) - Stab_t(g) ≤ C_Γ (2η + ξ₁) + η/2`. Corollary `positive-transfer`
and `√D ≤ √(2 C_Γ + 1) √η + √(C_Γ ξ₁)` conclude.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open Real Set Finset Filter Topology
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic OAI.OptimalMaxCut.MISProof
  BGHKLMM26.Hard

variable {R : ℕ}

/-! ### Fourier facts on the cube -/

theorem influence_oddPart_le (i : Fin R) (h : Cube (Fin R) → ℝ) :
    influence i (oddPart h) ≤ influence i h := by
  unfold influence
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [coefficient_oddPart, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (oddFactor_sq _)

theorem coefficient_two_mul_sub_one (g : Cube (Fin R) → ℝ) (s : Cube (Fin R)) :
    coefficient (fun x ↦ 2 * g x - 1) s =
      2 * coefficient g s - if s = (fun _ ↦ false) then 1 else 0 := by
  rw [← coefficient_one s]
  unfold coefficient
  rw [Finset.mul_expect, ← Finset.expect_sub_distrib]
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  ring

theorem coefficient_zero_eq_expect (g : Cube (Fin R) → ℝ) :
    coefficient g (fun _ ↦ false) = 𝔼 x, g x := by
  simp [coefficient]

theorem influence_two_mul_sub_one (i : Fin R) (g : Cube (Fin R) → ℝ) :
    influence i (fun x ↦ 2 * g x - 1) = 4 * influence i g := by
  unfold influence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  have hsi : s i = true := (Finset.mem_filter.1 hs).2
  have hs0 : s ≠ fun _ ↦ false := fun h ↦ by simp [h] at hsi
  simp only [coefficient_two_mul_sub_one, hs0, ↓reduceIte]
  ring

theorem stability_two_mul_sub_one (t : ℝ) (g : Cube (Fin R) → ℝ) :
    stability t (fun x ↦ 2 * g x - 1) = 4 * stability t g - 4 * (𝔼 x, g x) + 1 := by
  unfold stability
  simp_rw [coefficient_two_mul_sub_one]
  have e : ∀ s : Cube (Fin R), t ^ sdeg s *
      (2 * coefficient g s - if s = (fun _ ↦ false) then 1 else 0) ^ 2 =
      4 * (t ^ sdeg s * coefficient g s ^ 2) -
        (if s = (fun _ ↦ false) then 4 * coefficient g s - 1 else 0) := by
    intro s
    split_ifs with hs
    · subst hs; simp only [sdeg, degree_zero, pow_zero]; ring
    · ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ]
  simp only [Finset.mem_univ, ↓reduceIte, coefficient_zero_eq_expect]
  ring

/-- The even/odd decomposition at correlation `-t`:
`Stab_t(h) = Stab_{-t}(h) + 2 Stab_t(h_odd)`. -/
theorem stability_eq_neg_add_oddPart (t : ℝ) (h : Cube (Fin R) → ℝ) :
    stability t h = stability (-t) h + 2 * stability t (oddPart h) := by
  unfold stability
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [coefficient_oddPart, mul_pow, neg_pow]
  rcases Nat.even_or_odd (sdeg s) with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num; ring

/-- The even part of the spectrum at `t ≥ 0` dominates the mean: `(E h)² ≤ Stab_{-t}(h) +
Stab_t(h_odd)`. -/
theorem sq_expect_le_even {t : ℝ} (ht : 0 ≤ t) (h : Cube (Fin R) → ℝ) :
    (𝔼 x, h x) ^ 2 ≤ stability (-t) h + stability t (oddPart h) := by
  have e : stability (-t) h + stability t (oddPart h) =
      ∑ s, (if Even (sdeg s) then t ^ sdeg s * coefficient h s ^ 2 else 0) := by
    unfold stability
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [coefficient_oddPart, mul_pow, neg_pow]
    rcases Nat.even_or_odd (sdeg s) with he | ho
    · simp only [he.neg_one_pow, he, ↓reduceIte]; norm_num
    · simp only [ho.neg_one_pow, Nat.not_even_iff_odd.2 ho, ↓reduceIte]; norm_num
  rw [e, ← coefficient_zero_eq_expect]
  have hnn : ∀ s ∈ (Finset.univ : Finset (Cube (Fin R))),
      0 ≤ (if Even (sdeg s) then t ^ sdeg s * coefficient h s ^ 2 else 0) :=
    fun s _ ↦ by split_ifs <;> positivity
  have := Finset.single_le_sum hnn (Finset.mem_univ (fun _ : Fin R ↦ false))
  simpa using this

/-! ### Theorem 7.1 -/

/-- **Robust Majority is Stablest** [BGHKLMM26, Theorem 7.1], from the Gaussian lemma with the
error `C √Δ` (`hG : GaussSharp`). -/
theorem robustMIS_of_sharp (hG : GaussSharp) : BGHKLMM26.Hard.RobustMIS := by
  intro ρ hρ1 hρ0
  obtain ⟨t, rfl⟩ : ∃ t, ρ = -t := ⟨-ρ, by ring⟩
  have ht0 : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  obtain ⟨CT, hCT, hT⟩ := positive_transfer hG ht0 ht1
  obtain ⟨CΓ, hCΓ, hΓ⟩ := Gam_quadratic ht0.le ht1
  have hCm : (0 : ℝ) < 2 * CΓ + 1 := by linarith
  refine ⟨CT * √(2 * CΓ + 1), 1 / 100, by positivity, by norm_num, by norm_num, ?_⟩
  intro ξ hξ
  -- `ξ₁`: the error allowed in Majority is Stablest.
  obtain ⟨δ, hδ, hδω⟩ : ∃ δ > 0, ∀ x, |x| < δ → CT * √x < ξ / 2 := by
    have hc := Real.continuous_sqrt.continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hδ'⟩ := hc (ξ / (2 * CT)) (by positivity)
    refine ⟨δ, hδ, fun x hx ↦ ?_⟩
    have h1 := hδ' (x := x) (by simpa [Real.dist_eq] using hx)
    rw [Real.dist_eq, Real.sqrt_zero, sub_zero, abs_of_nonneg (Real.sqrt_nonneg x)] at h1
    calc CT * √x < CT * (ξ / (2 * CT)) := mul_lt_mul_of_pos_left h1 hCT
      _ = ξ / 2 := by field_simp
  set ξ₁ := min (1 / 8 : ℝ) (δ / (2 * (CΓ + 1))) with hξ₁
  have hξ₁0 : 0 < ξ₁ := lt_min (by norm_num) (by positivity)
  have hξ₁8 : ξ₁ ≤ 1 / 8 := min_le_left _ _
  have hξ₁δ : CΓ * ξ₁ < δ := by
    have h1 : ξ₁ ≤ δ / (2 * (CΓ + 1)) := min_le_right _ _
    have h2 : CΓ * ξ₁ ≤ CΓ * (δ / (2 * (CΓ + 1))) := mul_le_mul_of_nonneg_left h1 hCΓ
    have h3 : CΓ * (δ / (2 * (CΓ + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨τM, hτM, hMIS⟩ := untruncated_majority_is_stablest t ht0 ht1 ξ₁ hξ₁0
  obtain ⟨τT, hτT, hTr⟩ := hT (ξ / 2) (by linarith)
  refine ⟨min τT (τM / 8), lt_min hτT (by positivity), ?_⟩
  intro R g h01 hinf η hη0 hη1 hcut
  set h : Cube (Fin R) → ℝ := fun x ↦ 2 * g x - 1 with hh
  have hhmem : ∀ x, -1 ≤ h x ∧ h x ≤ 1 := fun x ↦ by
    have := h01 x; constructor <;> simp only [h] <;> linarith [this.1, this.2]
  -- The cut condition: `Stab_{-t}(h) ≤ -(2/π) arcsin t + 2η`.
  have hasin : Real.arcsin (-t) = -Real.arcsin t := Real.arcsin_neg t
  have hstabρ : stability (-t) h ≤ -(2 / π * Real.arcsin t) + 2 * η := by
    have hc := hcut
    rw [cutValue, corrAverage_cut, Real.arccos_eq_pi_div_two_sub_arcsin, hasin] at hc
    have e : (π / 2 - -Real.arcsin t) / π = 1 / 2 + Real.arcsin t / π := by
      field_simp
      ring
    rw [e] at hc
    have e2 : 2 / π * Real.arcsin t = 2 * (Real.arcsin t / π) := by ring
    rw [e2]
    linarith
  -- Majority is Stablest for the odd part.
  have hodd : stability t (oddPart h) ≤ 2 / π * Real.arcsin t + ξ₁ := by
    refine hMIS R (oddPart h) (oddPart_mem hhmem) (expect_oddPart h) fun i ↦ ?_
    calc influence i (oddPart h) ≤ influence i h := influence_oddPart_le i h
      _ = 4 * influence i g := influence_two_mul_sub_one i g
      _ ≤ 4 * (τM / 8) := by linarith [hinf i, min_le_right τT (τM / 8)]
      _ < τM := by linarith
  -- The mean.
  have hmean : (𝔼 x, h x) = 2 * (𝔼 x, g x) - 1 := by
    simp only [h]
    rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hm2 := sq_expect_le_even ht0.le h
  have hm2' : (𝔼 x, h x) ^ 2 ≤ 2 * η + ξ₁ := by linarith
  have hm_abs : |𝔼 x, h x| ≤ 1 / 2 := by
    rw [← Real.sqrt_sq_eq_abs]
    rw [show (1 / 2 : ℝ) = √(1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hgm1 : 1 / 4 ≤ 𝔼 x, g x := by
    have := neg_abs_le (𝔼 x, h x); linarith
  have hgm2 : (𝔼 x, g x) ≤ 3 / 4 := by
    have := le_abs_self (𝔼 x, h x); linarith
  -- The stability at `t`.
  have hstabt : 2 / π * Real.arcsin t - 2 * η ≤ stability t h := by
    have := stability_eq_neg_add_oddPart t h
    nlinarith [sq_nonneg (𝔼 x, h x)]
  -- The deficit.
  set m := 𝔼 x, h x with hm
  have hD : Gam t (𝔼 x, g x) - stability t g ≤ CΓ * (2 * η + ξ₁) + η / 2 := by
    have hg : (𝔼 x, g x) = (1 + m) / 2 := by rw [hmean]; ring
    have hq := hΓ m ⟨by linarith [neg_abs_le m], by linarith [le_abs_self m]⟩
    rw [Gam_half ⟨by linarith, ht1.le⟩] at hq
    have hs := stability_two_mul_sub_one t g
    rw [← hh] at hs
    rw [hg]
    have hCm2 : CΓ * m ^ 2 ≤ CΓ * (2 * η + ξ₁) := mul_le_mul_of_nonneg_left hm2' hCΓ
    have e : 2 / π * Real.arcsin t = 4 * (Real.arcsin t / (2 * π)) := by ring
    rw [e] at hstabt
    rw [hg] at hs
    linarith
  -- Corollary `positive-transfer`.
  have hdist := hTr R g h01 hgm1 hgm2 fun i ↦ (hinf i).trans (min_le_left _ _)
  -- The rate.
  have hη0' : 0 ≤ (2 * CΓ + 1) * η := by positivity
  have hξ₁' : 0 ≤ CΓ * ξ₁ := by positivity
  have hω : √(Gam t (𝔼 x, g x) - stability t g) ≤ √(2 * CΓ + 1) * √η + √(CΓ * ξ₁) := by
    calc √(Gam t (𝔼 x, g x) - stability t g)
        ≤ √((2 * CΓ + 1) * η + CΓ * ξ₁) := Real.sqrt_le_sqrt (by linarith)
      _ ≤ √((2 * CΓ + 1) * η) + √(CΓ * ξ₁) := Transfer.sqrt_add_le_add hη0' hξ₁'
      _ = √(2 * CΓ + 1) * √η + √(CΓ * ξ₁) := by rw [Real.sqrt_mul hCm.le]
  have hsmall : CT * √(CΓ * ξ₁) < ξ / 2 :=
    hδω _ (by rw [abs_of_nonneg hξ₁']; exact hξ₁δ)
  calc ltfDist g ≤ CT * √(Gam t (𝔼 x, g x) - stability t g) + ξ / 2 := hdist
    _ ≤ CT * (√(2 * CΓ + 1) * √η + √(CΓ * ξ₁)) + ξ / 2 := by gcongr
    _ = CT * √(2 * CΓ + 1) * √η + (CT * √(CΓ * ξ₁) + ξ / 2) := by ring
    _ ≤ CT * √(2 * CΓ + 1) * √η + ξ := by linarith

end BGHKLMM26.RobustMIS
