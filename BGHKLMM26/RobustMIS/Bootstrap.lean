module

public import BGHKLMM26.RobustMIS.DriftEstimate
public import BGHKLMM26.RobustMIS.Deficit

/-!
# The bootstrap: robustness in the centroid metric

§9.1, Steps 2 and 3 of `eldan-proof.tex` (new; replaces Eldan's stopping-time Lemmas 17 and 19),
Theorem A(b): `Δ(f) ≥ c₁ ε(f) / log(1/ε(f))` with `c₁ = ½ κ_t min(t, λ³/1280)`.

* `ode_bootstrap` (Step 2): an abstract continuity argument (pure real analysis; the mean value
  inequality on `[0, s*]` with `s* = sup{s ≤ α : y ≤ 2ε₀ on [0, s]}`).
* `theoremA_b` (Step 3): with `α = min(t, 1/2, 1/(8K√L₀), πλ²/(16 L₀))`, `L₀ = log(1/ε₀)`,
  `K = 160 λ⁻³`, `c = πλ²/8`: `y ≥ ε₀/2` on `[0, α]` (`ode_bootstrap`, `drift_identity`,
  `drift_estimate`, `yFlow_nonneg`), so `Δ ≥ κ_t α ε₀ / 2 ≥ c₁ ε₀ / L₀` (`borell_remainder`).

Status: both are proved. `ode_bootstrap` uses Lagrange's mean value theorem on `[0, s]` and the
first time `s₁ = inf{s : y(s) ≥ 2ε₀}` (a closed set, so `y(s₁) ≥ 2ε₀`, contradicting
`|y(s₁) - ε₀| ≤ ε₀/2`); `theoremA_b` uses the statements of `Drift`, `DriftEstimate`, `Deficit`,
`Static` (`epsF_le`), `Gamma` (`kap_pos`) and `Rates`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set

variable {n : ℕ}

namespace Bootstrap

theorem eldanC1_pos {t m : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hm : m ∈ Ioo (0 : ℝ) 1) :
    0 < eldanC1 t m := by
  unfold eldanC1
  have h1 := kap_pos (r := t) ⟨by linarith [ht.1], ht.2⟩
  have h2 := DriftEstimate.lam_pos hm
  have h3 : 0 < min t (lam m ^ 3 / 1280) := lt_min ht.1 (by positivity)
  exact mul_pos (mul_pos (by norm_num) h1) h3

theorem eldanC1_le_half {t m : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : eldanC1 t m ≤ 1 / 2 := by
  unfold eldanC1
  have h1 := kap_le_one ht.1.le
  have h0 := (kap_pos (r := t) ⟨by linarith [ht.1], ht.2⟩).le
  have h2 : min t (lam m ^ 3 / 1280) ≤ 1 := (min_le_left _ _).trans ht.2.le
  have h3 : kap t * min t (lam m ^ 3 / 1280) ≤ 1 := by
    rcases le_total 0 (min t (lam m ^ 3 / 1280)) with h | h
    · calc kap t * min t (lam m ^ 3 / 1280) ≤ 1 * 1 := mul_le_mul h1 h2 h zero_le_one
        _ = 1 := one_mul 1
    · nlinarith
  linarith

/-- The pointwise drift bound in the region `0 ≤ y ≤ 2ε₀`, `0 < r ≤ α`. -/
theorem drift_le {ε₀ K c α r v : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / (2 * π))
    (hK : 0 ≤ K) (hc : 0 ≤ c) (hr : 0 < r) (hrα : r ≤ α)
    (hαc : exp (-c / α) ≤ ε₀ ^ 2) (hv0 : 0 ≤ v) (hv : v ≤ 2 * ε₀) :
    K * psiL v + 2 * exp (-c / r) ≤
      2 * K * ε₀ * √(Real.log (1 / ε₀)) + 2 * ε₀ ^ 2 := by
  have h2ε : 2 * ε₀ ≤ exp (-(1 / 2)) := by
    refine le_trans ?_ DriftEstimate.inv_pi_le_exp
    calc 2 * ε₀ ≤ 2 * (1 / (2 * π)) := by linarith
      _ = 1 / π := by field_simp
  have hψ1 : psiL v ≤ psiL (2 * ε₀) :=
    monotoneOn_psiL ⟨hv0, hv.trans h2ε⟩ ⟨by linarith, h2ε⟩ hv
  have hψ2 : psiL (2 * ε₀) ≤ 2 * ε₀ * √(Real.log (1 / ε₀)) := by
    unfold psiL
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.sqrt_le_sqrt
    apply Real.log_le_log (by positivity)
    apply one_div_le_one_div_of_le hε₀
    linarith
  have he : exp (-c / r) ≤ ε₀ ^ 2 := by
    refine le_trans (exp_le_exp.mpr ?_) hαc
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hc hr hrα
  have := mul_le_mul_of_nonneg_left (hψ1.trans hψ2) hK
  nlinarith

/-- Step 3: `min(t, λ³/1280)/L₀ ≤ α`. -/
theorem min_div_le_alpha {t l L : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hl : 0 < l)
    (hl1 : l ≤ 1) (hL : 1 ≤ L) :
    min t (l ^ 3 / 1280) / L ≤
      min (min t (1 / 2)) (min (1 / (8 * (160 / l ^ 3) * √L)) (π * l ^ 2 / (16 * L))) := by
  have hL0 : 0 < L := by linarith
  have hM0 : 0 ≤ min t (l ^ 3 / 1280) := le_min ht.1.le (by positivity)
  have hML : min t (l ^ 3 / 1280) / L ≤ min t (l ^ 3 / 1280) := div_le_self hM0 hL
  have hl3 : l ^ 3 ≤ 1 := pow_le_one₀ hl.le hl1
  have hsL : √L ≤ L := by rw [Real.sqrt_le_left hL0.le]; nlinarith
  have hsL0 : 0 < √L := Real.sqrt_pos.2 hL0
  have hM1 : min t (l ^ 3 / 1280) / L ≤ l ^ 3 / 1280 / L :=
    div_le_div_of_nonneg_right (min_le_right _ _) hL0.le
  refine le_min (le_min (hML.trans (min_le_left _ _)) ?_) (le_min ?_ ?_)
  · refine hML.trans ((min_le_right _ _).trans ?_)
    linarith
  · have e : 1 / (8 * (160 / l ^ 3) * √L) = l ^ 3 / 1280 / √L := by
      field_simp; ring
    rw [e]
    exact hM1.trans (div_le_div_of_nonneg_left (by positivity) hsL0 hsL)
  · have h1 : l ^ 3 / 1280 ≤ π * l ^ 2 / 16 := by
      have : l ^ 3 ≤ l ^ 2 := pow_le_pow_of_le_one hl.le hl1 (by norm_num)
      nlinarith [Real.pi_gt_three]
    have e : π * l ^ 2 / (16 * L) = π * l ^ 2 / 16 / L := by field_simp
    rw [e]
    exact hM1.trans (div_le_div_of_nonneg_right h1 hL0.le)

end Bootstrap

/-- **The bootstrap** (§9.1, Step 2), abstractly: a continuous `y ≥ 0` on `[0, α]` with
`y(0) = ε₀ ∈ (0, 1/(2π)]` and `|y'(s)| ≤ K ψ(y(s)) + 2e^{-c/s}` stays `≥ ε₀/2` if
`α · 2Kε₀√(log(1/ε₀)) ≤ ε₀/4` and `e^{-c/α} ≤ ε₀²`. -/
theorem ode_bootstrap {y : ℝ → ℝ} {ε₀ K c α : ℝ} (hε₀ : 0 < ε₀) (hε₀1 : ε₀ ≤ 1 / (2 * π))
    (hK : 0 ≤ K) (hc : 0 ≤ c) (_hα0 : 0 < α) (hα1 : α ≤ 1 / 2)
    (hαK : α * (2 * K * ε₀ * √(Real.log (1 / ε₀))) ≤ ε₀ / 4) (hαc : exp (-c / α) ≤ ε₀ ^ 2)
    (hcont : ContinuousOn y (Icc 0 α)) (hy0 : y 0 = ε₀) (hnn : ∀ s ∈ Icc 0 α, 0 ≤ y s)
    (hder : ∀ s ∈ Ioo 0 α, ∃ y', HasDerivAt y y' s ∧ |y'| ≤ K * psiL (y s) + 2 * exp (-c / s)) :
    ∀ s ∈ Icc 0 α, ε₀ / 2 ≤ y s := by
  have hε₀4 : ε₀ ≤ 1 / 4 := by
    refine hε₀1.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [Real.two_le_pi]
  -- the mean value inequality on `[0, s]` while `y ≤ 2ε₀`
  have key : ∀ s ∈ Ioc 0 α, (∀ r ∈ Ioo 0 s, y r ≤ 2 * ε₀) → |y s - ε₀| ≤ ε₀ / 2 := by
    intro s hs hy
    have hdiff : DifferentiableOn ℝ y (Ioo 0 s) := by
      intro r hr
      obtain ⟨y', hy', -⟩ := hder r ⟨hr.1, hr.2.trans_le hs.2⟩
      exact hy'.differentiableAt.differentiableWithinAt
    obtain ⟨r, hr, hdr⟩ := exists_deriv_eq_slope y hs.1
      (hcont.mono (Icc_subset_Icc le_rfl hs.2)) hdiff
    obtain ⟨y', hy', hbd⟩ := hder r ⟨hr.1, hr.2.trans_le hs.2⟩
    rw [hy'.deriv, hy0, sub_zero] at hdr
    have hB := Bootstrap.drift_le hε₀ hε₀1 hK hc hr.1 (hr.2.le.trans hs.2) hαc
      (hnn r ⟨hr.1.le, hr.2.le.trans hs.2⟩) (hy r hr)
    have hys : y s - ε₀ = y' * s := by
      rw [hdr]; field_simp [hs.1.ne']
    rw [hys, abs_mul, abs_of_pos hs.1]
    have h1 : |y'| * s ≤ (2 * K * ε₀ * √(Real.log (1 / ε₀)) + 2 * ε₀ ^ 2) * α :=
      mul_le_mul (hbd.trans hB) hs.2 hs.1.le (by positivity)
    nlinarith
  -- `y < 2ε₀` on `[0, α]`
  have hlt : ∀ s ∈ Icc 0 α, y s < 2 * ε₀ := by
    by_contra hne
    push Not at hne
    obtain ⟨A, hA⟩ : ∃ A : Set ℝ, A = Icc 0 α ∩ y ⁻¹' Ici (2 * ε₀) := ⟨_, rfl⟩
    have hAc : IsClosed A := hA ▸ hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hAne : A.Nonempty := by
      obtain ⟨s, hs, hys⟩ := hne
      exact ⟨s, hA ▸ ⟨hs, hys⟩⟩
    have hAb : BddBelow A := ⟨0, fun x hx ↦ (hA ▸ hx).1.1⟩
    have hmem := hAc.csInf_mem hAne hAb
    obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ = sInf A := ⟨_, rfl⟩
    rw [← hs₁] at hmem
    have hbelow : ∀ r, r < s₁ → r ∉ A := fun r hr ↦ notMem_of_lt_csInf (hs₁ ▸ hr) hAb
    rw [hA] at hmem hbelow
    obtain ⟨⟨h0, hα⟩, h2⟩ := hmem
    have h2' : 2 * ε₀ ≤ y s₁ := h2
    have hpos : 0 < s₁ := by
      rcases h0.eq_or_lt with h | h
      · rw [← h, hy0] at h2'; linarith
      · exact h
    have hk := key s₁ ⟨hpos, hα⟩ (fun r hr ↦ by
      have hr' := hbelow r hr.2
      have : r ∈ Icc 0 α := ⟨hr.1.le, hr.2.le.trans hα⟩
      by_contra h
      exact hr' ⟨this, show 2 * ε₀ ≤ y r by linarith⟩)
    rw [abs_le] at hk
    linarith
  intro s hs
  rcases hs.1.eq_or_lt with h | h
  · rw [← h, hy0]; linarith
  · have hk := key s ⟨h, hs.2⟩ fun r hr ↦ (hlt r ⟨hr.1.le, hr.2.le.trans hs.2⟩).le
    rw [abs_le] at hk
    linarith

/-- **Theorem A(b)**: `Δ(f) ≥ c₁ ε(f) / log(1/ε(f))` when `ε(f) > 0`. -/
theorem theoremA_b {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (f : Gs n → ℝ) (hf : Measurable f)
    (h01 : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hm : gMean f ∈ Ioo (0 : ℝ) 1) (hε : 0 < epsF f) :
    eldanC1 t (gMean f) * epsF f / Real.log (1 / epsF f) ≤ gDef t f := by
  obtain ⟨l, hl⟩ : ∃ l, l = lam (gMean f) := ⟨_, rfl⟩
  have hl0 : 0 < l := hl ▸ DriftEstimate.lam_pos hm
  have hl4 : l ≤ 1 / 4 := hl ▸ DriftEstimate.lam_le_quarter _
  have hε1 : epsF f ≤ 1 / (2 * π) := (epsF_le f h01).2
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log (1 / epsF f) := ⟨_, rfl⟩
  have hpi := Real.pi_pos
  have h2pi : 2 * π ≤ 1 / epsF f := by
    rw [le_div_iff₀ hε]; rw [le_div_iff₀ (by positivity)] at hε1; linarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]
    refine le_trans ?_ h2pi
    have := Real.exp_one_lt_d9
    nlinarith [Real.pi_gt_three]
  have hL0 : 0 < L := by linarith
  have hsL0 : 0 < √L := Real.sqrt_pos.2 hL0
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 160 / l ^ 3 := ⟨_, rfl⟩
  have hK0 : 0 < K := hK ▸ by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = π * l ^ 2 / 8 := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ by positivity
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α =
      min (min t (1 / 2)) (min (1 / (8 * K * √L)) (π * l ^ 2 / (16 * L))) := ⟨_, rfl⟩
  have hα0 : 0 < α := by
    rw [hα]
    exact lt_min (lt_min ht.1 (by norm_num)) (lt_min (by positivity) (by positivity))
  have hα1 : α ≤ 1 / 2 := hα ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hαt : α ≤ t := hα ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hαK' : α ≤ 1 / (8 * K * √L) := hα ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hαL : α ≤ π * l ^ 2 / (16 * L) := hα ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hαK : α * (2 * K * epsF f * √(Real.log (1 / epsF f))) ≤ epsF f / 4 := by
    rw [← hL]
    calc α * (2 * K * epsF f * √L) ≤ 1 / (8 * K * √L) * (2 * K * epsF f * √L) :=
          mul_le_mul_of_nonneg_right hαK' (by positivity)
      _ = epsF f / 4 := by field_simp; ring
  have hαc : exp (-c / α) ≤ epsF f ^ 2 := by
    have h2L : 2 * L ≤ c / α := by
      rw [le_div_iff₀ hα0, hc]
      calc 2 * L * α ≤ 2 * L * (π * l ^ 2 / (16 * L)) :=
            mul_le_mul_of_nonneg_left hαL (by positivity)
        _ = π * l ^ 2 / 8 := by field_simp; ring
    have he : exp (-(2 * L)) = epsF f ^ 2 := by
      rw [show -(2 * L) = -L + -L by ring, Real.exp_add, Real.exp_neg, hL,
        Real.exp_log (by positivity)]
      field_simp
    rw [← he, neg_div]
    exact exp_le_exp.mpr (neg_le_neg h2L)
  have hdi := drift_identity f hf h01 hm
  have hcont : ContinuousOn (yFlow f) (Icc 0 t) :=
    hdi.1.mono fun s hs ↦ ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hboot := ode_bootstrap hε hε1 hK0.le hc0.le hα0 hα1 hαK hαc
    (hcont.mono (Icc_subset_Icc le_rfl hαt)) (yFlow_zero f)
    (fun s _ ↦ yFlow_nonneg f hf h01 s) (fun s hs ↦ by
      refine ⟨_, hdi.2 s ⟨hs.1, by linarith [hs.2]⟩, ?_⟩
      have hde := drift_estimate f hf h01 hm hs.1 (by linarith [hs.2])
      rw [← hl] at hde
      have e : -(π * l ^ 2) / (8 * s) = -c / s := by rw [hc]; ring
      rw [e, ← hK] at hde
      exact hde)
  -- `∫₀ᵗ y ≥ α ε₀ / 2`
  have hint : α * (epsF f / 2) ≤ ∫ s in (0 : ℝ)..t, yFlow f s := by
    have hi1 : IntervalIntegrable (yFlow f) volume 0 α :=
      (hcont.mono (by rw [uIcc_of_le hα0.le]; exact Icc_subset_Icc le_rfl hαt)).intervalIntegrable
    have hi2 : IntervalIntegrable (yFlow f) volume α t :=
      (hcont.mono (by rw [uIcc_of_le hαt]; exact Icc_subset_Icc hα0.le le_rfl)).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have h1 : ∫ s in (0 : ℝ)..α, epsF f / 2 ≤ ∫ s in (0 : ℝ)..α, yFlow f s :=
      intervalIntegral.integral_mono_on hα0.le intervalIntegrable_const hi1 hboot
    have h2 : 0 ≤ ∫ s in α..t, yFlow f s :=
      intervalIntegral.integral_nonneg hαt fun s _ ↦ yFlow_nonneg f hf h01 s
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    linarith
  have hbr := borell_remainder ht f hf h01 hm
  have hk := kap_pos (r := t) ⟨by linarith [ht.1], ht.2⟩
  have hmin := Bootstrap.min_div_le_alpha ht hl0 (by linarith) hL1
  rw [← hK, ← hα] at hmin
  rw [← hL]
  calc eldanC1 t (gMean f) * epsF f / L
      = kap t * (epsF f / 2) * (min t (l ^ 3 / 1280) / L) := by
        rw [eldanC1, ← hl]; field_simp
    _ ≤ kap t * (epsF f / 2) * α := mul_le_mul_of_nonneg_left hmin (by positivity)
    _ = kap t * (α * (epsF f / 2)) := by ring
    _ ≤ kap t * ∫ s in (0 : ℝ)..t, yFlow f s := mul_le_mul_of_nonneg_left hint hk.le
    _ ≤ gDef t f := hbr

end BGHKLMM26.RobustMIS
