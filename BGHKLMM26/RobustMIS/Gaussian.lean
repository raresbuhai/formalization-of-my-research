module

public import BGHKLMM26.RobustMIS.Bootstrap
public import BGHKLMM26.RobustMIS.QBath
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Eldan's robust Borell estimate: the Gaussian lemma

Theorem A(c), (d) and Corollary B of `eldan-proof.tex`: Lemma `gaussian-main` of [BGHKLMM26]
(`robust-MIS-main.tex`) with `√Δ` replaced by `ω(Δ) = √(Δ log(e/Δ))` (`sqrtLog`). It is the first
step of the Gaussian lemma with the error `C √Δ` (`BGHKLMM26.RobustMIS.gaussian_sharp`,
`Sharp.lean`), which uses it to put `F` close to the halfspace. Mossel–Neeman's functional Borell
and robust Borell theorems, Heilman's theorems, Lemma `gaussian-facts` (a), (b), (e), (f) and the
epigraph construction are not needed.

* `theoremA_c`: `‖f - 𝟙_H‖₁ ≤ 2 (λ c₁)^{-1/2} ω(Δ)` for the halfspace `H` of measure `m` with normal
  `F̂/|F̂|`. Proof (§9.2): if `Δ > c₁`, the right side is `≥ 4`; if `Δ = 0` then `ε = 0`
  (`theoremA_b`) and `δ₁ = 0` (`qbath`); otherwise `x = λ δ₁²/4 ≤ ε₀` (`qbath`),
  `x/log(1/x) ≤ ε₀/log(1/ε₀) ≤ Δ/c₁` (`strictMonoOn_div_log`, `theoremA_b`), and invert
  (`le_of_div_log_le`).
* `theoremA_d`: `Δ ≤ (c₁λ²/4)² ⟹ |F̂| ≥ λ/√π` (inversion with `x = ε₀`, `sqrt_mul_log_le`,
  `qf_ge_lam`).
* `gaussian_main` (Corollary B), with `λ_I = a(1 - b)` as the lower bound of `λ` on `[a, b]`.

Status: all three are proved, from `theoremA_b`, `qbath`, `gDef_nonneg`, `epsF_nonneg`,
`epsF_le`, `qf_ge_lam`, `kap_pos`, `kap_le_one` and the `Rates` lemmas.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

namespace GaussianLem

theorem integral_abs_sub_halfInd_le (f : Gs n → ℝ)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (ν : Gs n) (θ : ℝ) :
    ∫ x, |f x - halfInd ν θ x| ∂gm n ≤ 1 := by
  have hb : ∀ x, |f x - halfInd ν θ x| ≤ 1 := by
    intro x
    have := h01 x
    unfold halfInd
    by_cases hx : x ∈ {x : Gs n | θ ≤ ⟪ν, x⟫}
    · rw [indicator_of_mem hx]; simp only [Pi.one_apply]
      rw [abs_le]; constructor <;> linarith
    · rw [indicator_of_notMem hx]; simp only [sub_zero]
      rw [abs_le]; constructor <;> linarith
  calc ∫ x, |f x - halfInd ν θ x| ∂gm n ≤ ∫ _x, (1 : ℝ) ∂gm n :=
        integral_mono_of_nonneg (ae_of_all _ fun _ ↦ abs_nonneg _) (integrable_const _)
          (ae_of_all _ hb)
    _ = 1 := by simp

/-- The inversion step of §9.2: if `0 < Δ ≤ c₁ ≤ 1`, `x, ε ∈ (0, 1)`, `x ≤ ε` and
`c₁ ε / log(1/ε) ≤ Δ`, then `x ≤ (Δ/c₁) log(e/Δ)`. -/
theorem inversion {x ε Δ c₁ : ℝ} (hx : 0 < x) (hxε : x ≤ ε) (hε1 : ε < 1) (hc₁ : 0 < c₁)
    (hc₁1 : c₁ ≤ 1) (hΔc : Δ ≤ c₁) (hb : c₁ * ε / Real.log (1 / ε) ≤ Δ) :
    x ≤ Δ / c₁ * Real.log (exp 1 / Δ) := by
  have hε0 : 0 < ε := hx.trans_le hxε
  have hL : 0 < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
  have hΔ0 : 0 < Δ := lt_of_lt_of_le (by positivity) hb
  have hD0 : 0 < Δ / c₁ := div_pos hΔ0 hc₁
  have hD1 : Δ / c₁ ≤ 1 := (div_le_one hc₁).2 hΔc
  have hmono : x / Real.log (1 / x) ≤ ε / Real.log (1 / ε) :=
    strictMonoOn_div_log.monotoneOn ⟨hx, hxε.trans_lt hε1⟩ ⟨hε0, hε1⟩ hxε
  have hεD : ε / Real.log (1 / ε) ≤ Δ / c₁ := by
    rw [le_div_iff₀ hc₁]
    calc ε / Real.log (1 / ε) * c₁ = c₁ * ε / Real.log (1 / ε) := by ring
      _ ≤ Δ := hb
  have h := le_of_div_log_le ⟨hx, hxε.trans_lt hε1⟩ ⟨hD0, hD1⟩ (hmono.trans hεD)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ hD0.le)
  apply Real.log_le_log (div_pos (exp_pos 1) hD0)
  rw [div_le_div_iff₀ hD0 hΔ0]
  calc exp 1 * Δ = exp 1 * (Δ / c₁ * c₁) := by rw [div_mul_cancel₀ _ hc₁.ne']
    _ ≤ exp 1 * (Δ / c₁) := by
        apply mul_le_mul_of_nonneg_left _ (exp_pos 1).le
        calc Δ / c₁ * c₁ ≤ Δ / c₁ * 1 := mul_le_mul_of_nonneg_left hc₁1 hD0.le
          _ = Δ / c₁ := mul_one _

end GaussianLem

/-- **Theorem A(c)**: robustness in `L¹`. -/
theorem theoremA_c {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hm : gMean f ∈ Ioo (0 : ℝ) 1) (ν : Gs n) (hν : ‖ν‖ = 1)
    (hF : hermite1 f = ‖hermite1 f‖ • ν) :
    ∫ x, |f x - halfInd ν (-Psi (gMean f)) x| ∂gm n ≤
      2 / √(lam (gMean f) * eldanC1 t (gMean f)) * sqrtLog (gDef t f) := by
  have hla := DriftEstimate.lam_pos hm
  have hla4 := DriftEstimate.lam_le_quarter (gMean f)
  have hc := Bootstrap.eldanC1_pos ht hm
  have hc2 := Bootstrap.eldanC1_le_half (m := gMean f) ht
  obtain ⟨hΔ0, hΔ1⟩ := gDef_nonneg ht f hf h01 hm
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ∫ x, |f x - halfInd ν (-Psi (gMean f)) x| ∂gm n := ⟨_, rfl⟩
  rw [← hδ]
  have hδ0 : 0 ≤ δ := hδ ▸ integral_nonneg (fun _ ↦ abs_nonneg _)
  have hδ1 : δ ≤ 1 := hδ ▸ GaussianLem.integral_abs_sub_halfInd_le f h01 ν _
  have hqb := (qbath f hf h01 hm ν hν hF).2
  rw [← hδ] at hqb
  have hslc : √(lam (gMean f) * eldanC1 t (gMean f)) =
      √(lam (gMean f)) * √(eldanC1 t (gMean f)) := Real.sqrt_mul hla.le _
  have hsl : √(lam (gMean f)) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hsl0 : 0 < √(lam (gMean f)) := Real.sqrt_pos.2 hla
  have hsc0 : 0 < √(eldanC1 t (gMean f)) := Real.sqrt_pos.2 hc
  rcases le_or_gt (gDef t f) (eldanC1 t (gMean f)) with hΔc | hΔc
  · rcases hδ0.eq_or_lt with h0 | hpos
    · rw [← h0]
      exact mul_nonneg (by positivity) (sqrtLog_nonneg _)
    · -- `x = λ δ²/4 ∈ (0, ε₀]`
      obtain ⟨hε0', hε1'⟩ := epsF_le f h01
      have hx0 : 0 < lam (gMean f) / 4 * δ ^ 2 := by positivity
      have hε0 : 0 < epsF f := hx0.trans_le hqb
      have hε1 : epsF f < 1 := hε1'.trans_lt (by
        rw [div_lt_one (by positivity)]; nlinarith [Real.two_le_pi])
      have hb := theoremA_b ht f hf h01 hm hε0
      have hinv := GaussianLem.inversion hx0 hqb hε1 hc (by linarith) hΔc hb
      have hΔpos : 0 < gDef t f := by
        have hL : 0 < Real.log (1 / epsF f) :=
          Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
        exact lt_of_lt_of_le (by positivity) hb
      have hlog : 0 ≤ Real.log (exp 1 / gDef t f) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hΔpos, one_mul]
        linarith [Real.add_one_le_exp 1]
      rw [sqrtLog_eq ⟨hΔ0, hΔ1⟩]
      have hsq : (2 / √(lam (gMean f) * eldanC1 t (gMean f)) *
          √(gDef t f * Real.log (exp 1 / gDef t f))) ^ 2 =
          4 / (lam (gMean f) * eldanC1 t (gMean f)) *
            (gDef t f * Real.log (exp 1 / gDef t f)) := by
        rw [mul_pow, div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
        norm_num
      rw [← sq_le_sq₀ hδ0 (by positivity), hsq]
      have e : 4 / (lam (gMean f) * eldanC1 t (gMean f)) *
          (gDef t f * Real.log (exp 1 / gDef t f)) =
          4 / lam (gMean f) * (gDef t f / eldanC1 t (gMean f) *
            Real.log (exp 1 / gDef t f)) := by
        field_simp
      rw [e]
      have : δ ^ 2 = 4 / lam (gMean f) * (lam (gMean f) / 4 * δ ^ 2) := by
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)
  · have h1 : √(eldanC1 t (gMean f)) ≤ sqrtLog (gDef t f) := by
      calc √(eldanC1 t (gMean f)) = √(min (eldanC1 t (gMean f)) 1) := by
            rw [min_eq_left (by linarith)]
        _ ≤ sqrtLog (eldanC1 t (gMean f)) := sqrt_min_le_sqrtLog hc.le
        _ ≤ sqrtLog (gDef t f) := monotone_sqrtLog hΔc.le
    calc δ ≤ 1 := hδ1
      _ ≤ 2 / √(lam (gMean f)) := by
          rw [le_div_iff₀ hsl0]; linarith
      _ = 2 / √(lam (gMean f) * eldanC1 t (gMean f)) * √(eldanC1 t (gMean f)) := by
          rw [hslc]; field_simp
      _ ≤ 2 / √(lam (gMean f) * eldanC1 t (gMean f)) * sqrtLog (gDef t f) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)


theorem GaussianLem.pi_le_two_sqrt_exp : π ≤ 2 * √(exp 1) := by
  have h1 : π / 2 ≤ √(exp 1) := by
    rw [Real.le_sqrt (by linarith [Real.pi_pos]) (exp_pos 1).le]
    nlinarith [Real.pi_lt_d2, Real.exp_one_gt_d9, Real.pi_pos]
  linarith

/-- **Theorem A(d)**: non-degeneracy of the direction. -/
theorem theoremA_d {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hm : gMean f ∈ Ioo (0 : ℝ) 1)
    (hΔ : gDef t f ≤ (eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4) ^ 2) :
    lam (gMean f) / √π ≤ ‖hermite1 f‖ := by
  have hla := DriftEstimate.lam_pos hm
  have hla4 := DriftEstimate.lam_le_quarter (gMean f)
  have hc := Bootstrap.eldanC1_pos ht hm
  have hc2 := Bootstrap.eldanC1_le_half (m := gMean f) ht
  have hq := qf_ge_lam (Ioo_subset_Icc_self hm)
  have hpi := Real.pi_pos
  have hspi : 0 < √π := Real.sqrt_pos.2 hpi
  -- it suffices that `‖F̂‖² ≥ λ²/π`
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), div_pow, Real.sq_sqrt hpi.le]
  have hq2 : 2 / π * lam (gMean f) ^ 2 ≤ qf (gMean f) ^ 2 := by
    have h2 : (√(2 / π) * lam (gMean f)) ^ 2 = 2 / π * lam (gMean f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [← h2]
    exact pow_le_pow_left₀ (by positivity) hq 2
  have hε : ‖hermite1 f‖ ^ 2 = qf (gMean f) ^ 2 - epsF f := by unfold epsF; ring
  -- `ε₀ ≤ λ²/π`
  suffices hε0 : epsF f ≤ lam (gMean f) ^ 2 / π by
    rw [hε]
    have : lam (gMean f) ^ 2 / π = 2 / π * lam (gMean f) ^ 2 - lam (gMean f) ^ 2 / π := by ring
    linarith
  rcases (epsF_nonneg f hf h01).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  obtain ⟨-, hε1'⟩ := epsF_le f h01
  have hε1 : epsF f < 1 := hε1'.trans_lt (by
    rw [div_lt_one (by positivity)]; nlinarith [Real.two_le_pi])
  have hb := theoremA_b ht f hf h01 hm hpos
  obtain ⟨hΔ0, hΔ1⟩ := gDef_nonneg ht f hf h01 hm
  have hA0 : 0 ≤ eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 := by positivity
  have hA1 : eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 ≤ 1 := by
    have : lam (gMean f) ^ 2 ≤ 1 := by nlinarith
    have : eldanC1 t (gMean f) * lam (gMean f) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hΔc : gDef t f ≤ eldanC1 t (gMean f) := by
    refine hΔ.trans ?_
    calc (eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4) ^ 2
        ≤ eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 := by nlinarith
      _ ≤ eldanC1 t (gMean f) := by
          have : lam (gMean f) ^ 2 ≤ 1 := by nlinarith
          nlinarith
  have hinv := GaussianLem.inversion hpos le_rfl hε1 hc (by linarith) hΔc hb
  have hL : 0 < Real.log (1 / epsF f) := Real.log_pos (by rw [lt_div_iff₀ hpos]; linarith)
  have hΔpos : 0 < gDef t f := lt_of_lt_of_le (by positivity) hb
  -- `Δ log(e/Δ) = √Δ (√Δ log(e/Δ)) ≤ (c₁λ²/4)(2/√e)`
  have hsΔ : √(gDef t f) ≤ eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 := by
    rw [Real.sqrt_le_left hA0]; exact hΔ
  have hml := sqrt_mul_log_le ⟨hΔpos, hΔ1⟩
  have hse : 0 < √(exp 1) := Real.sqrt_pos.2 (exp_pos 1)
  have hlog : 0 ≤ √(gDef t f) * Real.log (exp 1 / gDef t f) := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Real.log_nonneg
    rw [le_div_iff₀ hΔpos, one_mul]
    linarith [Real.add_one_le_exp 1]
  have key : gDef t f * Real.log (exp 1 / gDef t f) ≤
      eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 * (2 / √(exp 1)) := by
    calc gDef t f * Real.log (exp 1 / gDef t f)
        = √(gDef t f) * (√(gDef t f) * Real.log (exp 1 / gDef t f)) := by
          rw [← mul_assoc, Real.mul_self_sqrt hΔ0]
      _ ≤ eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 * (2 / √(exp 1)) :=
          mul_le_mul hsΔ hml hlog hA0
  calc epsF f ≤ gDef t f / eldanC1 t (gMean f) * Real.log (exp 1 / gDef t f) := hinv
    _ = (gDef t f * Real.log (exp 1 / gDef t f)) / eldanC1 t (gMean f) := by ring
    _ ≤ (eldanC1 t (gMean f) * lam (gMean f) ^ 2 / 4 * (2 / √(exp 1))) /
          eldanC1 t (gMean f) := div_le_div_of_nonneg_right key hc.le
    _ = lam (gMean f) ^ 2 / (2 * √(exp 1)) := by field_simp; ring
    _ ≤ lam (gMean f) ^ 2 / π :=
        div_le_div_of_nonneg_left (by positivity) hpi GaussianLem.pi_le_two_sqrt_exp


theorem GaussianLem.halfInd_normalize (w : Gs n) (hw : 0 < ‖w‖) (θ : ℝ) :
    halfInd w (θ * ‖w‖) = halfInd (‖w‖⁻¹ • w) θ := by
  unfold halfInd
  congr 1
  ext x
  simp only [mem_ofPred_eq, real_inner_smul_left]
  rw [le_inv_mul_iff₀ hw, mul_comm]

/-- **Corollary B** (Lemma `gaussian-main` of [BGHKLMM26] with Eldan's estimate): for a closed
interval `[a, b] ⊂ (0, 1)` there are `C, c₀, δ₀ > 0` such that a measurable `F : ℝⁿ → [0, 1]` with
mean `m ∈ [a, b]` has `Δ = Γ_t(m) - Stab_t(F) ≥ 0`, and if `Δ ≤ δ₀` then `|F̂⁽¹⁾| ≥ c₀` and the
LTF `𝟙{⟨F̂⁽¹⁾, x⟩ ≥ -Φ⁻¹(m) |F̂⁽¹⁾|}`, whose coefficient vector is `F̂⁽¹⁾`, is within
`C √(Δ log(e/Δ))` of `F` in `L¹(γ)`.

Proof: with `λ_I = a(1 - b) ≤ λ(m)`, `c₁(t, I) = ½ κ_t min(t, λ_I³/1280) ≤ c₁(t, m)`:
`C = 2 (λ_I c₁(t, I))^{-1/2}`, `c₀ = λ_I/√π`, `δ₀ = (c₁(t, I) λ_I²/4)²`; Theorem A(a), (d), (c)
with `ν = F̂/|F̂|`. -/
theorem gaussian_main {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hb : b < 1) :
    ∃ C c₀ δ₀ : ℝ, 0 < C ∧ 0 < c₀ ∧ 0 < δ₀ ∧
      ∀ (n : ℕ) (F : Gs n → ℝ), Measurable F → (∀ x, 0 ≤ F x ∧ F x ≤ 1) →
        a ≤ gMean F → gMean F ≤ b →
        0 ≤ gDef t F ∧
          (gDef t F ≤ δ₀ → c₀ ≤ ‖hermite1 F‖ ∧
            ∫ x, |F x - halfInd (hermite1 F) (-Psi (gMean F) * ‖hermite1 F‖) x| ∂gm n ≤
              C * sqrtLog (gDef t F)) := by
  have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, ht1⟩
  obtain ⟨lI, hlI⟩ : ∃ l : ℝ, l = a * (1 - b) := ⟨_, rfl⟩
  have hl0 : 0 < lI := by rw [hlI]; exact mul_pos ha (by linarith)
  obtain ⟨cI, hcI⟩ : ∃ c : ℝ, c = 1 / 2 * kap t * min t (lI ^ 3 / 1280) := ⟨_, rfl⟩
  have hk := kap_pos (r := t) ⟨by linarith, ht1⟩
  have hc0 : 0 < cI := by
    rw [hcI]
    exact mul_pos (mul_pos (by norm_num) hk) (lt_min ht0 (by positivity))
  refine ⟨2 / √(lI * cI), lI / √π, (cI * lI ^ 2 / 4) ^ 2, by positivity, by positivity,
    by positivity, ?_⟩
  intro n F hF h01 haF hFb
  have hm : gMean F ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le haF, hFb.trans_lt hb⟩
  have hlm : lI ≤ lam (gMean F) := by
    rw [hlI]; unfold lam
    exact mul_le_mul haF (by linarith) (by linarith) (by linarith [hm.1])
  have hcm : cI ≤ eldanC1 t (gMean F) := by
    rw [hcI]; unfold eldanC1
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply min_le_min_left
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ hl0.le hlm 3
  refine ⟨(gDef_nonneg ht F hF h01 hm).1, fun hΔ ↦ ?_⟩
  have hΔ' : gDef t F ≤ (eldanC1 t (gMean F) * lam (gMean F) ^ 2 / 4) ^ 2 := by
    refine hΔ.trans (pow_le_pow_left₀ (by positivity) ?_ 2)
    have : lI ^ 2 ≤ lam (gMean F) ^ 2 := pow_le_pow_left₀ hl0.le hlm 2
    have := mul_le_mul hcm this (by positivity) (hc0.le.trans hcm)
    linarith
  have hd := theoremA_d ht F hF h01 hm hΔ'
  have hc0' : lI / √π ≤ ‖hermite1 F‖ :=
    le_trans (div_le_div_of_nonneg_right hlm (Real.sqrt_nonneg _)) hd
  refine ⟨hc0', ?_⟩
  have hFpos : 0 < ‖hermite1 F‖ := lt_of_lt_of_le (by positivity) hc0'
  have hν : ‖‖hermite1 F‖⁻¹ • hermite1 F‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hFpos.ne']
  have hFν : hermite1 F = ‖hermite1 F‖ • (‖hermite1 F‖⁻¹ • hermite1 F) := by
    rw [smul_smul, mul_inv_cancel₀ hFpos.ne', one_smul]
  have hc := theoremA_c ht F hF h01 hm _ hν hFν
  rw [GaussianLem.halfInd_normalize _ hFpos]
  refine hc.trans (mul_le_mul_of_nonneg_right ?_ (sqrtLog_nonneg _))
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact Real.sqrt_le_sqrt (mul_le_mul hlm hcm hc0.le (by linarith [DriftEstimate.lam_pos hm]))

end BGHKLMM26.RobustMIS
