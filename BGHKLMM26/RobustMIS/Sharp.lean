module

public import BGHKLMM26.RobustMIS.SharpLocal

/-!
# The sharp Gaussian lemma

[BGHKLMM26, Lemma 7.4]: the Gaussian lemma with the error `C √Δ`
(`BGHKLMM26.RobustMIS.gaussian_sharp : BGHKLMM26.RobustMIS.GaussSharp`).

Eldan's estimate (`gaussian_main`) puts `F` within `C ω(Δ) → 0` of the halfspace `H` with normal
`ν = F̂⁽¹⁾/|F̂⁽¹⁾|` and the mean of `F`, and `F̂⁽¹⁾` is along `ν`. For `Δ` small this is within the
neighborhood of the local estimate (`sharp_local`), so `Δ ≥ (1 - t) I_t(F, H)`, and the transport
bound (`sharp_transport`) gives `I_t(F, H) ≥ c ‖F - 𝟙_H‖₁²`, i.e. `‖F - 𝟙_H‖₁ ≤ C √Δ`.

* `SharpT.exists_sqrtLog_le`: `C ω(δ) ≤ ε` for `δ ≤ δ₀`, from `ω(0) = 0` and the continuity
  and monotonicity of `ω`.
* `SharpT.abs_Psi_le`: `|Φ⁻¹(m)| ≤ max |Φ⁻¹(a)| |Φ⁻¹(b)|` for `m ∈ [a, b] ⊂ (0, 1)`.
* `SharpT.le_of_sq`: `k L² ≤ Δ ⟹ L ≤ k^{-1/2} √Δ` for `k > 0`, `L ≥ 0`, applied with
  `k = (1 - t) c`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set Topology
open scoped RealInnerProductSpace
open Gaussian

namespace SharpT

/-- `C ω(δ) ≤ ε` for all `δ ≤ δ₀`. -/
theorem exists_sqrtLog_le {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ x, x ≤ δ₀ → C * sqrtLog x ≤ ε := by
  have hev : ∀ᶠ x in 𝓝 (0 : ℝ), C * sqrtLog x < ε := by
    have hc : Continuous fun x ↦ C * sqrtLog x := continuous_const.mul continuous_sqrtLog
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    simpa [sqrtLog_zero] using hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨r / 2, by positivity, fun x hx ↦ ?_⟩
  have h2 : C * sqrtLog (r / 2) < ε := by
    refine hball ?_
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  exact (mul_le_mul_of_nonneg_left (monotone_sqrtLog hx) hC).trans h2.le

/-- `|Φ⁻¹(m)| ≤ max |Φ⁻¹(a)| |Φ⁻¹(b)|` for `m ∈ [a, b] ⊂ (0, 1)`. -/
theorem abs_Psi_le {a b m : ℝ} (ha : 0 < a) (hb : b < 1) (ham : a ≤ m) (hmb : m ≤ b) :
    |Psi m| ≤ max |Psi a| |Psi b| := by
  have hma : a ∈ Ioo (0 : ℝ) 1 := ⟨ha, by linarith⟩
  have hmb' : b ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, hb⟩
  have hmm : m ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  exact abs_le_max_abs_abs (strictMonoOn_Psi.monotoneOn hma hmm ham)
    (strictMonoOn_Psi.monotoneOn hmm hmb' hmb)

/-- `k L² ≤ Δ ⟹ L ≤ k^{-1/2} √Δ`. -/
theorem le_of_sq {k L Δ : ℝ} (hk : 0 < k) (hL : 0 ≤ L) (h : k * L ^ 2 ≤ Δ) :
    L ≤ (√k)⁻¹ * √Δ := by
  have hsq : L ^ 2 ≤ Δ / k := by
    rw [le_div_iff₀ hk]; linarith
  have := Real.abs_le_sqrt hsq
  rw [abs_of_nonneg hL, Real.sqrt_div' _ hk.le, div_eq_inv_mul] at this
  exact this

end SharpT

/-- **The Gaussian lemma with the error `C √Δ`** [BGHKLMM26, Lemma 7.4].

Proof: `c₀` is that of `gaussian_main`; with `A = max |Φ⁻¹(a)| |Φ⁻¹(b)|`, `ε₀` from `sharp_local`
and `c` from `sharp_transport`, `δ₀ ≤ δ₀(gaussian_main)` is such that `C_E ω(δ₀) ≤ ε₀`, and
`C = ((1 - t) c)^{-1/2}`. -/
theorem gaussian_sharp : GaussSharp := by
  intro t ht0 ht1 a b ha hab hb
  obtain ⟨CE, c₀, δ₁, hCE, hc₀, hδ₁, hmain⟩ := gaussian_main ht0 ht1 ha hab hb
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = max |Psi a| |Psi b| := ⟨_, rfl⟩
  obtain ⟨ε₀, hε₀, hloc⟩ := sharp_local ht0 ht1 A
  obtain ⟨c, hc, htr⟩ := sharp_transport ht0 ht1 A
  obtain ⟨δ₂, hδ₂, hω⟩ := SharpT.exists_sqrtLog_le hCE.le hε₀
  have hk : 0 < (1 - t) * c := mul_pos (by linarith) hc
  refine ⟨(√((1 - t) * c))⁻¹, c₀, min δ₁ δ₂, by positivity, hc₀, lt_min hδ₁ hδ₂, ?_⟩
  intro n F hF h01 haF hFb
  obtain ⟨hnn, hmain'⟩ := hmain n F hF h01 haF hFb
  refine ⟨hnn, fun hΔ ↦ ?_⟩
  obtain ⟨hc0F, hL1⟩ := hmain' (hΔ.trans (min_le_left _ _))
  refine ⟨hc0F, ?_⟩
  have hw : 0 < ‖hermite1 F‖ := hc₀.trans_le hc0F
  have hm : gMean F ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le haF, hFb.trans_lt hb⟩
  rw [GaussianLem.halfInd_normalize _ hw] at hL1 ⊢
  have hν : ‖‖hermite1 F‖⁻¹ • hermite1 F‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw.ne']
  have hα : |-Psi (gMean F)| ≤ A := by
    rw [abs_neg, hA]; exact SharpT.abs_Psi_le ha hb haF hFb
  have hmean : gMean F = 1 - Phi (-Psi (gMean F)) := by
    rw [Phi_neg, Phi_Psi hm]; ring
  have horth : ∀ v : Gs n, ⟪v, ‖hermite1 F‖⁻¹ • hermite1 F⟫ = 0 → ⟪v, hermite1 F⟫ = 0 := by
    intro v hv
    rw [real_inner_smul_right] at hv
    exact (mul_eq_zero.1 hv).resolve_left (inv_ne_zero hw.ne')
  have hsmall : ∫ x, |F x - halfInd (‖hermite1 F‖⁻¹ • hermite1 F) (-Psi (gMean F)) x| ∂gm n ≤
      ε₀ := hL1.trans (hω _ (hΔ.trans (min_le_right _ _)))
  have hlocal := hloc n _ _ hν hα F hF h01 hmean horth hsmall
  have htrans := htr n _ _ hν hα F hF h01 hmean
  refine SharpT.le_of_sq hk (integral_nonneg fun _ ↦ abs_nonneg _) ?_
  have := mul_le_mul_of_nonneg_left htrans (by linarith : (0 : ℝ) ≤ 1 - t)
  linarith

end BGHKLMM26.RobustMIS
