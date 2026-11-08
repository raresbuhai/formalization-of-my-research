module

public import BS23.Colinear.Correct
public import BS23.Colinear.PolyTime
public import BS23.Common.Glue
public import BS23.Common.Input
public import BS23.Common.UniformProof

/-!
# Theorem 1.2 of [BS23]

`BS23.Colinear.colinear_clustering_main` is the statement of `BS23.colinear_clustering`
(`BS23/Challenge.lean`), proved from its parts:

* the algorithm is `BS23.Colinear.colinearAlg`, which ignores its coins, and it runs in time
  `colinearTime C` (`BS23.Colinear.colinearAlg_runsInTime`; the time bound is monotone in `C`,
  `BS23.Colinear.runsInTime_colinearTime_mono`);
* on every sample in the good event `BS23.GoodNoise` of degree `Dcol wmin` and accuracy `η`, for
  every rounding, it clusters the sample with error `(wmin / k)^c`
  (`BS23.Colinear.alg_correct`, with the noise in uniform form,
  `BS23.uniformNoise_of_goodNoise_stdNoise`, and the input read as in
  `BS23.Colinear.clustersWithin_algInput_roundedSample`);
* the good event fails with probability at most `k / (n η²) (1 / wmin + (d+1)^D (2D)^D)`
  (`BS23.le_successProb_of_goodNoise`).

The accuracy is `η = colTarget wmin d σ² / (4 (d+1)^D)`. All the constants are bounded by powers
of `B = (d + 1) / wmin ≥ 2` (`BS23.Colinear.colTarget_bound`), and the exponents by multiples of
`L + 1 ≤ 3 (log (1/wmin) + 1)`, `L = logInv wmin` (`BS23.Colinear.logInv_add_one_le`), so a sample
of size `σ⁻⁴ B^(2c + 8200 (L + 1))` suffices (`BS23.Colinear.main_numerics`), which the hypothesis
of the theorem gives for `C ≥ 2 c + 24600` (`BS23.Colinear.sample_bound`,
`BS23.Colinear.exponent_le`). The constant of the theorem is `C = T₀ + Csep c + 2 c + 24600`,
`T₀` the time constant; `C ≥ Csep c` gives the separation `alg_correct` needs. The case `k = 1`
needs no separate treatment (`alg_correct` covers it), and `n > 0` follows from the sample size.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix

/-! ### The running time -/

/-- `colinearTime C` is monotone in `C`. -/
theorem colinearTime_mono {C C' : ℕ} (h : C ≤ C') (x : ColinearInput) :
    colinearTime C x ≤ colinearTime C' x := by
  unfold colinearTime
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ h)

/-- `BS23.RunsInTime` is monotone in the time bound. -/
theorem runsInTime_mono {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {A : α × List Bool → β} {T T' : α → ℕ} (h : RunsInTime encIn encOut A T)
    (hT : ∀ x, T x ≤ T' x) : RunsInTime encIn encOut A T' := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, hc.mono (fun xr ↦ Nat.mul_le_mul_left c (by have := hT xr.1; omega))
    (fun xr ↦ Nat.mul_le_mul_left c (by have := hT xr.1; omega))⟩

/-- The colinear algorithm runs in time `colinearTime C` for every large enough `C`. -/
theorem runsInTime_colinearTime_mono {C C' : ℕ} (h : C ≤ C')
    (hC : RunsInTime encColinearInput encOutput (fun xr : ColinearInput × List Bool ↦
      colinearAlg xr.1) (colinearTime C)) :
    RunsInTime encColinearInput encOutput (fun xr : ColinearInput × List Bool ↦
      colinearAlg xr.1) (colinearTime C') :=
  runsInTime_mono hC (colinearTime_mono h)

/-! ### `logInv` -/

/-- `2^L ≤ 4 / wmin` for `L = logInv wmin` and `0 < wmin ≤ 1`. -/
theorem two_pow_logInv_le {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) :
    (2 : ℝ) ^ logInv wmin ≤ 4 / wmin := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hw1' : (wmin : ℝ) ≤ 1 := by exact_mod_cast hw1
  have hinv : (1 : ℝ) ≤ (wmin : ℝ)⁻¹ := (one_le_inv₀ hw').mpr hw1'
  rcases Nat.lt_or_ge 1 ⌈wmin⁻¹⌉₊ with hN1 | hN1
  · have hpos : 0 < logInv wmin := Nat.clog_pos (by norm_num) hN1
    have hlt : 2 ^ (logInv wmin - 1) < ⌈wmin⁻¹⌉₊ := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
      rwa [Nat.pred_eq_sub_one] at this
    have hceil : (⌈wmin⁻¹⌉₊ : ℚ) < wmin⁻¹ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : 2 ^ logInv wmin < 2 * ⌈wmin⁻¹⌉₊ := by
      have : logInv wmin = (logInv wmin - 1) + 1 := by omega
      rw [this, pow_succ]
      omega
    have h3 : ((2 ^ logInv wmin : ℕ) : ℝ) < 2 * (⌈wmin⁻¹⌉₊ : ℝ) := by exact_mod_cast h1
    have h4 : (⌈wmin⁻¹⌉₊ : ℝ) < (wmin : ℝ)⁻¹ + 1 := by exact_mod_cast hceil
    push_cast at h3
    rw [div_eq_mul_inv]
    linarith
  · have h0 : logInv wmin = 0 := Nat.clog_of_right_le_one hN1 2
    rw [h0, pow_zero, div_eq_mul_inv]
    linarith

/-- `L + 1 ≤ 3 (log (1/wmin) + 1)` for `L = logInv wmin` and `0 < wmin ≤ 1`. -/
theorem logInv_add_one_le {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) :
    (logInv wmin : ℝ) + 1 ≤ 3 * (Real.log (1 / (wmin : ℝ)) + 1) := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hw1' : (wmin : ℝ) ≤ 1 := by exact_mod_cast hw1
  have h := two_pow_logInv_le hw hw1
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_pow, div_eq_mul_inv, Real.log_mul (by norm_num) (by positivity)] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hl2 := Real.log_two_gt_d9
  rw [one_div]
  have hx : 0 ≤ Real.log (wmin : ℝ)⁻¹ := Real.log_nonneg ((one_le_inv₀ hw').mpr hw1')
  have key : ((logInv wmin : ℝ) - 2 - 2 * Real.log (wmin : ℝ)⁻¹) * Real.log 2 ≤ 0 := by
    nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 2 * Real.log 2 - 1)]
  have : (logInv wmin : ℝ) - 2 - 2 * Real.log (wmin : ℝ)⁻¹ ≤ 0 := by
    by_contra hc
    have := mul_pos (lt_of_not_ge hc) (by linarith : (0 : ℝ) < Real.log 2)
    linarith
  linarith

/-! ### Bounds by powers of `B = (d + 1) / wmin` -/

section Numerics

variable {B : ℝ}

/-- `2^L ≤ B^3`. -/
theorem two_pow_logInv_le_B {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) : (2 : ℝ) ^ logInv wmin ≤ B ^ 3 := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have h4 : (4 : ℝ) ≤ B ^ 2 := by nlinarith
  calc (2 : ℝ) ^ logInv wmin ≤ 4 / wmin := two_pow_logInv_le hw hw1
    _ = 4 * (1 / wmin) := by ring
    _ ≤ B ^ 2 * B := mul_le_mul h4 hBw (one_div_pos.mpr hw').le (by positivity)
    _ = B ^ 3 := by ring

/-- `M + 1 ≤ B^9` for the largest Hermite degree `M = 40 (L + 1)`. -/
theorem M_add_one_le_B {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) : ((params wmin).M : ℝ) + 1 ≤ B ^ 9 := by
  have h := two_pow_logInv_le_B hw hw1 hB2 hBw
  have hL : (params wmin).M + 1 ≤ 64 * 2 ^ logInv wmin := by
    rw [params_M]
    have := Nat.lt_two_pow_self (n := logInv wmin)
    omega
  have hL' : ((params wmin).M : ℝ) + 1 ≤ 64 * 2 ^ logInv wmin := by exact_mod_cast hL
  have h64 : (64 : ℝ) ≤ B ^ 6 :=
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ B ^ 6 := pow_le_pow_left₀ (by norm_num) hB2 6
  calc ((params wmin).M : ℝ) + 1 ≤ 64 * 2 ^ logInv wmin := hL'
    _ ≤ B ^ 6 * B ^ 3 := mul_le_mul h64 h (by positivity) (by positivity)
    _ = B ^ 9 := by ring

/-- `2 D ≤ B^12` for the degree `D = Dcol wmin` of the good event. -/
theorem two_Dcol_le_B {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) : 2 * (Dcol wmin : ℝ) ≤ B ^ 12 := by
  have h := two_pow_logInv_le_B hw hw1 hB2 hBw
  have hL : 2 * Dcol wmin ≤ 512 * 2 ^ logInv wmin := by
    unfold Dcol
    rw [params_M]
    have := Nat.lt_two_pow_self (n := logInv wmin)
    omega
  have hL' : 2 * (Dcol wmin : ℝ) ≤ 512 * 2 ^ logInv wmin := by exact_mod_cast hL
  have h512 : (512 : ℝ) ≤ B ^ 9 :=
    calc (512 : ℝ) = 2 ^ 9 := by norm_num
      _ ≤ B ^ 9 := pow_le_pow_left₀ (by norm_num) hB2 9
  calc 2 * (Dcol wmin : ℝ) ≤ 512 * 2 ^ logInv wmin := hL'
    _ ≤ B ^ 9 * B ^ 3 := mul_le_mul h512 h (by positivity) (by positivity)
    _ = B ^ 12 := by ring

/-- `1 ≤ η₀ B^(80 (L + 1) + 2)`. -/
theorem one_le_colEta0_mul {wmin : ℚ} (hw : 0 < wmin) (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) : 1 ≤ colEta0 wmin * B ^ (80 * (logInv wmin + 1) + 2) := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hB0 : 0 < B := by linarith
  set a := 10 * (logInv wmin + 1) with ha
  have h1 : 1 / B ^ 2 ≤ (wmin : ℝ) / 2 := by
    have : 1 ≤ (wmin : ℝ) * B := by
      rw [div_le_iff₀ hw'] at hBw
      linarith
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : (4 : ℝ) * 16 ^ a ≤ B ^ 2 * (B ^ 4) ^ a := by
    have h4 : (4 : ℝ) ≤ B ^ 2 := by nlinarith
    have h16 : (16 : ℝ) ≤ B ^ 4 := by nlinarith
    exact mul_le_mul h4 (pow_le_pow_left₀ (by norm_num) h16 a) (by positivity) (by positivity)
  have h3 : (1 / B ^ 2) ^ (2 * a) / (B ^ 2 * (B ^ 4) ^ a) ≤ colEta0 wmin := by
    unfold colEta0
    rw [← ha]
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) h1 _) (by positivity) h2
  have e : (1 / B ^ 2) ^ (2 * a) / (B ^ 2 * (B ^ 4) ^ a) * B ^ (80 * (logInv wmin + 1) + 2) =
      1 := by
    have : 80 * (logInv wmin + 1) + 2 = 2 * (2 * a) + 4 * a + 2 := by omega
    rw [this, div_pow, one_pow, ← pow_mul, ← pow_mul]
    field_simp
    ring
  calc (1 : ℝ) = (1 / B ^ 2) ^ (2 * a) / (B ^ 2 * (B ^ 4) ^ a) *
        B ^ (80 * (logInv wmin + 1) + 2) := e.symm
    _ ≤ colEta0 wmin * B ^ (80 * (logInv wmin + 1) + 2) :=
        mul_le_mul_of_nonneg_right h3 (by positivity)

/-- The bound on the denominator of `colTarget`, for an abstract degree `m` with `m + 1 ≤ B^9`. -/
theorem den_le {m d : ℕ} {w : ℝ} (hw0 : 0 < w) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B)
    (hBd : (d : ℝ) + 1 ≤ B) (hm9 : (m : ℝ) + 1 ≤ B ^ 9) :
    2 ^ (m + 8) * ((m : ℝ) + 1) ^ (m + 1) * ((d : ℝ) + 1) ^ m * momConst m w *
      fmLip m (2 * ((m : ℝ) + 1) / w) ≤ B ^ (80 * m + 86) := by
  have hB0 : 0 < B := by linarith
  have hiw : 0 ≤ 1 / w := (one_div_pos.mpr hw0).le
  have h4 : (4 : ℝ) ≤ B ^ 2 := by nlinarith
  have h12 : (12 : ℝ) ≤ B ^ 4 := by nlinarith
  have hQ1 : (2 : ℝ) ^ (m + 8) ≤ B ^ (m + 8) := pow_le_pow_left₀ (by norm_num) hB2 _
  have hQ2 : ((m : ℝ) + 1) ^ (m + 1) ≤ B ^ (9 * (m + 1)) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by positivity) hm9 _
  have hQ3 : ((d : ℝ) + 1) ^ m ≤ B ^ m := pow_le_pow_left₀ (by positivity) hBd _
  have hK : momConst m w ≤ B ^ (23 * (m + 1)) := by
    unfold momConst
    have h11 : 4 * ((m : ℝ) + 1) ≤ B ^ 11 :=
      calc 4 * ((m : ℝ) + 1) ≤ B ^ 2 * B ^ 9 :=
            mul_le_mul h4 hm9 (by positivity) (by positivity)
        _ = B ^ 11 := by ring
    have e2 : B ^ (23 * (m + 1)) = (B ^ 11) ^ (2 * (m + 1)) * B ^ (m + 1) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    rw [div_eq_mul_one_div, ← _root_.one_div_pow, e2]
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) h11 _) (pow_le_pow_left₀ hiw hBw _)
      (pow_nonneg hiw _) (by positivity)
  have hLip : fmLip m (2 * ((m : ℝ) + 1) / w) ≤ B ^ (46 * (m + 1)) := by
    unfold fmLip
    have h23 : 6 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) / w) ≤ B ^ 23 := by
      have e : 6 * ((m : ℝ) + 1) * (2 * ((m : ℝ) + 1) / w) =
          12 * ((m : ℝ) + 1) * ((m : ℝ) + 1) * (1 / w) := by ring
      rw [e]
      calc 12 * ((m : ℝ) + 1) * ((m : ℝ) + 1) * (1 / w) ≤ B ^ 4 * B ^ 9 * B ^ 9 * B := by
            refine mul_le_mul ?_ hBw hiw (by positivity)
            refine mul_le_mul ?_ hm9 (by positivity) (by positivity)
            exact mul_le_mul h12 hm9 (by positivity) (by positivity)
        _ = B ^ 23 := by ring
    rw [show 46 * (m + 1) = 23 * (2 * (m + 1)) by ring, pow_mul B 23]
    exact pow_le_pow_left₀ (by positivity) h23 _
  have hK0 : 0 ≤ momConst m w := by unfold momConst; positivity
  have hL0 : 0 ≤ fmLip m (2 * ((m : ℝ) + 1) / w) := by unfold fmLip; positivity
  calc 2 ^ (m + 8) * ((m : ℝ) + 1) ^ (m + 1) * ((d : ℝ) + 1) ^ m * momConst m w *
        fmLip m (2 * ((m : ℝ) + 1) / w) ≤
        B ^ (m + 8) * B ^ (9 * (m + 1)) * B ^ m * B ^ (23 * (m + 1)) * B ^ (46 * (m + 1)) := by
        gcongr
    _ = B ^ (80 * m + 86) := by ring

/-- The denominator of `colTarget` is at most `B^(80 M + 86)`. -/
theorem colDen_le {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) {d : ℕ} (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) (hBd : (d : ℝ) + 1 ≤ B) :
    2 ^ ((params wmin).M + 8) * (((params wmin).M : ℝ) + 1) ^ ((params wmin).M + 1) *
      ((d : ℝ) + 1) ^ (params wmin).M * momConst (params wmin).M (wmin : ℝ) *
      fmLip (params wmin).M (2 * (((params wmin).M : ℝ) + 1) / (wmin : ℝ)) ≤
      B ^ (80 * (params wmin).M + 86) :=
  den_le (by exact_mod_cast hw) hB2 hBw hBd (M_add_one_le_B hw hw1 hB2 hBw)

/-- An abstract form of `BS23.Colinear.colTarget_bound`. -/
theorem le_target_mul {σ2 η₀ Den x y : ℝ} (hσ : 0 ≤ σ2) (hη : 1 ≤ η₀ * x) (hDen : Den ≤ y)
    (hD0 : 0 < Den) : σ2 ≤ η₀ * σ2 / Den * (x * y) := by
  have h1 : 1 ≤ y / Den := by rw [le_div_iff₀ hD0]; linarith
  have e : η₀ * σ2 / Den * (x * y) = σ2 * (η₀ * x) * (y / Den) := by
    field_simp
  rw [e]
  calc σ2 = σ2 * 1 * 1 := by ring
    _ ≤ σ2 * (η₀ * x) * (y / Den) := by gcongr

/-- **The accuracy target is not too small**: `σ² ≤ colTarget wmin d σ² · B^(3400 (L + 1))`. -/
theorem colTarget_bound {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) {d : ℕ} (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) (hBd : (d : ℝ) + 1 ≤ B) {σ2 : ℝ} (hσ : 0 < σ2) :
    σ2 ≤ colTarget wmin d σ2 * B ^ (3400 * (logInv wmin + 1)) := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hB1 : 1 ≤ B := by linarith
  have hexp : 80 * (logInv wmin + 1) + 2 + (80 * (params wmin).M + 86) ≤
      3400 * (logInv wmin + 1) := by
    rw [params_M]
    omega
  have hT0 := (colTarget_pos hw d hσ).le
  unfold colTarget at hT0 ⊢
  refine (le_target_mul hσ.le (one_le_colEta0_mul hw hB2 hBw)
    (colDen_le hw hw1 (d := d) hB2 hBw hBd) ?_).trans ?_
  · unfold momConst fmLip
    positivity
  · rw [← pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hexp) hT0

end Numerics

/-! ### The sample size -/

/-- **What the sample size gives**: for `C ≥ 2` and `N ≤ C Λ`, the hypothesis
`(hi / (lo σ²))^C B^(C Λ) ≤ n` gives `B^N / σ⁴ ≤ n`. -/
theorem sample_bound {B σ2 hi lo Λ n : ℝ} {C N : ℕ} (hB : 1 ≤ B) (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hC : 2 ≤ C) (hN : (N : ℝ) ≤ C * Λ)
    (hn : (hi / (lo * σ2)) ^ C * B ^ ((C : ℝ) * Λ) ≤ n) : B ^ N / σ2 ^ 2 ≤ n := by
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlohi
  have h1 : 1 / σ2 ≤ hi / (lo * σ2) := by
    rw [div_le_div_iff₀ hσ0 (by positivity)]
    nlinarith
  have h1' : 1 ≤ 1 / σ2 := by rw [le_div_iff₀ hσ0]; linarith
  have h2 : (1 / σ2) ^ 2 ≤ (hi / (lo * σ2)) ^ C :=
    calc (1 / σ2) ^ 2 ≤ (1 / σ2) ^ C := pow_le_pow_right₀ h1' hC
      _ ≤ (hi / (lo * σ2)) ^ C := pow_le_pow_left₀ (by positivity) h1 _
  have h3 : B ^ N ≤ B ^ ((C : ℝ) * Λ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hB hN
  calc B ^ N / σ2 ^ 2 = (1 / σ2) ^ 2 * B ^ N := by ring
    _ ≤ (hi / (lo * σ2)) ^ C * B ^ ((C : ℝ) * Λ) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ ≤ n := hn

/-- The exponent `N = 2c + 8200 (L + 1)` is at most `C (x + 1)` when `L + 1 ≤ 3 (x + 1)`,
`x ≥ 0` and `C ≥ 2c + 24600`. -/
theorem exponent_le {c L C : ℕ} {x : ℝ} (hx : 0 ≤ x) (hL : (L : ℝ) + 1 ≤ 3 * (x + 1))
    (hC : 2 * c + 24600 ≤ C) : ((2 * c + 8200 * (L + 1) : ℕ) : ℝ) ≤ C * (x + 1) := by
  have hC' : (2 * (c : ℝ) + 24600) ≤ (C : ℝ) := by exact_mod_cast hC
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have e1 := mul_nonneg hc0 hx
  have e2 := mul_le_mul_of_nonneg_right hC' (by linarith : (0 : ℝ) ≤ x + 1)
  push_cast
  linarith

/-- **The numerics of Theorem 1.2**, abstractly: `L` stands for `logInv wmin`, `D` for
`Dcol wmin`, `T` for the accuracy target, `B` for `(d + 1) / wmin`. -/
theorem numerics_core (c : ℕ) {k d L D : ℕ} {w B σ2 T η n : ℝ} (hw0 : 0 < w)
    (hk' : (0 : ℝ) < k) (hkw : (k : ℝ) * w ≤ 1) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B)
    (hBd : (d : ℝ) + 1 ≤ B) (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1) (hTpos : 0 < T)
    (hTB : σ2 ≤ T * B ^ (3400 * (L + 1))) (h2D : 2 * (D : ℝ) ≤ B ^ 12) (hDpos : 1 ≤ D)
    (hD : D ≤ 82 * L + 88) (hη : η = T / (4 * ((d : ℝ) + 1) ^ D))
    (hn : B ^ (2 * c + 8200 * (L + 1)) / σ2 ^ 2 ≤ n) :
    8 ≤ n ∧ 1 / σ2 ≤ n ∧ 0 < η ∧ η + η * ((d : ℝ) + 1) ^ D + 1 / n ≤ T ∧
      k / (n * η ^ 2) * (1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D) ≤ (w / k) ^ c := by
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hdD : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ D :=
    one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg d))
  have h4 : (4 : ℝ) ≤ B ^ 2 :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ B ^ 2 := pow_le_pow_left₀ (by norm_num) hB2 2
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηT : η * ((d : ℝ) + 1) ^ D = T / 4 := by
    rw [hη]
    field_simp
  have hηB : σ2 ≤ η * B ^ (D + 2 + 3400 * (L + 1)) := by
    have h1 : T ≤ η * B ^ (D + 2) := by
      have hdB : ((d : ℝ) + 1) ^ D ≤ B ^ D := pow_le_pow_left₀ (by positivity) hBd _
      calc T = η * (((d : ℝ) + 1) ^ D * 4) := by rw [← mul_assoc, hηT]; ring
        _ ≤ η * (B ^ D * B ^ 2) := by gcongr
        _ = η * B ^ (D + 2) := by rw [pow_add]
    calc σ2 ≤ T * B ^ (3400 * (L + 1)) := hTB
      _ ≤ η * B ^ (D + 2) * B ^ (3400 * (L + 1)) := by gcongr
      _ = η * B ^ (D + 2 + 3400 * (L + 1)) := by rw [pow_add B (D + 2), mul_assoc]
  have hBN : B ^ (2 * c + 8200 * (L + 1)) ≤ n * σ2 ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hn
  have hσ2 : σ2 ^ 2 ≤ σ2 := by
    rw [sq]
    exact mul_le_of_le_one_left hσ0.le hσ1
  have hσ2' : 0 < σ2 ^ 2 := by positivity
  have hn0 : 0 ≤ n := le_trans (by positivity) hn
  have hBNn : B ^ (2 * c + 8200 * (L + 1)) ≤ n :=
    hBN.trans (mul_le_of_le_one_right hn0 (pow_le_one₀ hσ0.le hσ1))
  have h8 : 8 ≤ n := by
    have h3 : B ^ 3 ≤ B ^ (2 * c + 8200 * (L + 1)) := pow_le_pow_right₀ hB1 (by omega)
    have : (8 : ℝ) ≤ B ^ 3 :=
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ B ^ 3 := pow_le_pow_left₀ (by norm_num) hB2 3
    linarith
  have hnpos : 0 < n := by linarith
  refine ⟨h8, ?_, hηpos, ?_, ?_⟩
  · -- `1/σ² ≤ n`
    have h1 : 1 / σ2 ≤ 1 / σ2 ^ 2 := one_div_le_one_div_of_le hσ2' hσ2
    have h2 : 1 / σ2 ^ 2 ≤ B ^ (2 * c + 8200 * (L + 1)) / σ2 ^ 2 :=
      div_le_div_of_nonneg_right (one_le_pow₀ hB1) hσ2'.le
    linarith
  · -- the accuracy
    have hηle : η ≤ T / 4 := by
      rw [← hηT]
      exact le_mul_of_one_le_right hηpos.le hdD
    have h2 : 2 ≤ n * T := by
      have hE : 2 * B ^ (3400 * (L + 1)) ≤ B ^ (2 * c + 8200 * (L + 1)) := by
        calc 2 * B ^ (3400 * (L + 1)) ≤ B * B ^ (3400 * (L + 1)) := by gcongr
          _ = B ^ (3400 * (L + 1) + 1) := by ring
          _ ≤ B ^ (2 * c + 8200 * (L + 1)) := pow_le_pow_right₀ hB1 (by omega)
      have h3 : B ^ (2 * c + 8200 * (L + 1)) ≤ n * T * B ^ (3400 * (L + 1)) :=
        calc B ^ (2 * c + 8200 * (L + 1)) ≤ n * σ2 ^ 2 := hBN
          _ ≤ n * σ2 := by gcongr
          _ ≤ n * (T * B ^ (3400 * (L + 1))) := by gcongr
          _ = n * T * B ^ (3400 * (L + 1)) := by ring
      have := hE.trans h3
      exact le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < B ^ (3400 * (L + 1)))
    have h3 : 1 / n ≤ T / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]
      linarith
    rw [hηT]
    linarith
  · -- the failure probability
    have hX : 1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D ≤ B ^ (13 * D + 1) := by
      have h1 : ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D ≤ B ^ (13 * D) :=
        calc ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D ≤ B ^ D * (B ^ 12) ^ D :=
              mul_le_mul (pow_le_pow_left₀ (by positivity) hBd _)
                (pow_le_pow_left₀ (by positivity) h2D _) (by positivity) (by positivity)
          _ = B ^ (13 * D) := by rw [← pow_mul, ← pow_add]; ring_nf
      have h2 : 1 / w ≤ B ^ (13 * D) := hBw.trans (le_self_pow₀ hB1 (by omega))
      calc _ ≤ B ^ (13 * D) + B ^ (13 * D) := add_le_add h2 h1
        _ = 2 * B ^ (13 * D) := by ring
        _ ≤ B * B ^ (13 * D) := by gcongr
        _ = B ^ (13 * D + 1) := by ring
    have hkB : (k : ℝ) ≤ B := by
      have : (k : ℝ) ≤ 1 / w := by rw [le_div_iff₀ hw0]; exact hkw
      linarith
    have hP : 1 ≤ (w / k) ^ c * B ^ (2 * c) := by
      have h1 : 1 ≤ w / k * B ^ 2 := by
        have hwB : 1 ≤ w * B := by
          rw [div_le_iff₀ hw0] at hBw
          linarith
        rw [div_mul_eq_mul_div, le_div_iff₀ hk']
        have := mul_le_mul_of_nonneg_right hwB hB0.le
        calc 1 * (k : ℝ) ≤ B := by linarith
          _ ≤ w * B * B := by linarith
          _ = w * B ^ 2 := by ring
      calc (1 : ℝ) ≤ (w / k * B ^ 2) ^ c := one_le_pow₀ h1
        _ = (w / k) ^ c * B ^ (2 * c) := by rw [mul_pow, ← pow_mul]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have key1 : (k : ℝ) * (1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D) *
        B ^ (2 * c + 2 * (D + 2 + 3400 * (L + 1))) ≤ B ^ (2 * c + 8200 * (L + 1)) :=
      calc (k : ℝ) * (1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D) *
            B ^ (2 * c + 2 * (D + 2 + 3400 * (L + 1))) ≤
            B * B ^ (13 * D + 1) * B ^ (2 * c + 2 * (D + 2 + 3400 * (L + 1))) := by gcongr
        _ = B ^ (13 * D + 1 + 1 + (2 * c + 2 * (D + 2 + 3400 * (L + 1)))) := by ring
        _ ≤ B ^ (2 * c + 8200 * (L + 1)) := pow_le_pow_right₀ hB1 (by omega)
    have key2 : B ^ (2 * c + 8200 * (L + 1)) ≤
        (w / k) ^ c * (n * η ^ 2) * B ^ (2 * c + 2 * (D + 2 + 3400 * (L + 1))) :=
      calc B ^ (2 * c + 8200 * (L + 1)) ≤ n * σ2 ^ 2 := hBN
        _ ≤ n * (η * B ^ (D + 2 + 3400 * (L + 1))) ^ 2 := by gcongr
        _ ≤ ((w / k) ^ c * B ^ (2 * c)) * (n * (η * B ^ (D + 2 + 3400 * (L + 1))) ^ 2) :=
            le_mul_of_one_le_left (by positivity) hP
        _ = (w / k) ^ c * (n * η ^ 2) * B ^ (2 * c + 2 * (D + 2 + 3400 * (L + 1))) := by ring
    exact le_of_mul_le_mul_right (key1.trans key2) (by positivity)

/-- **The numerics of Theorem 1.2.** With `B = (d + 1) / wmin`, `L = logInv wmin`,
`D = Dcol wmin` and the accuracy `η = colTarget wmin d σ² / (4 (d + 1)^D)`, a sample of size
`n ≥ B^(2c + 8200 (L + 1)) / σ⁴` has `n ≥ 8`, `n ≥ 1/σ²`, `η + η (d + 1)^D + 1/n ≤ colTarget`
(the accuracy `alg_correct` needs), and failure probability
`k / (n η²) (1/wmin + (d + 1)^D (2D)^D) ≤ (wmin / k)^c` for the good event. -/
theorem main_numerics (c : ℕ) {k d : ℕ} {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1)
    (hk : 0 < k) (hkw : (k : ℝ) * wmin ≤ 1) (hd : 1 ≤ d) {σ2 : ℝ} (hσ0 : 0 < σ2)
    (hσ1 : σ2 ≤ 1) {η : ℝ} (hη : η = colTarget wmin d σ2 / (4 * ((d : ℝ) + 1) ^ Dcol wmin))
    {n : ℝ} (hn : (((d : ℝ) + 1) / wmin) ^ (2 * c + 8200 * (logInv wmin + 1)) / σ2 ^ 2 ≤ n) :
    8 ≤ n ∧ 1 / σ2 ≤ n ∧ 0 < η ∧
      η + η * ((d : ℝ) + 1) ^ Dcol wmin + 1 / n ≤ colTarget wmin d σ2 ∧
      k / (n * η ^ 2) * (1 / (wmin : ℝ) +
        ((d : ℝ) + 1) ^ Dcol wmin * (2 * (Dcol wmin : ℝ)) ^ Dcol wmin) ≤
        ((wmin : ℝ) / k) ^ c := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hw1' : (wmin : ℝ) ≤ 1 := by exact_mod_cast hw1
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hBd : (d : ℝ) + 1 ≤ ((d : ℝ) + 1) / wmin := by
    rw [le_div_iff₀ hw0]
    nlinarith
  have hB2 : 2 ≤ ((d : ℝ) + 1) / wmin := by linarith
  have hBw : 1 / (wmin : ℝ) ≤ ((d : ℝ) + 1) / wmin :=
    div_le_div_of_nonneg_right (by linarith) hw0.le
  have hD : Dcol wmin ≤ 82 * logInv wmin + 88 := by
    unfold Dcol
    rw [params_M]
    omega
  have hDpos : 1 ≤ Dcol wmin := by
    unfold Dcol
    omega
  exact numerics_core c hw0 (by exact_mod_cast hk) hkw hB2 hBw hBd hσ0 hσ1
    (colTarget_pos hw d hσ0) (colTarget_bound hw hw1 hB2 hBw hBd hσ0)
    (two_Dcol_le_B hw hw1 hB2 hBw) hDpos hD hη hn

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2** of [BS23] (full version: Theorem 6.1): the statement of
`BS23.colinear_clustering`. The algorithm is `BS23.Colinear.colinearAlg` (it ignores its coins),
and the constant is `C = T₀ + Csep c + 2 c + 24600` with `T₀` its time constant. -/
theorem colinear_clustering_main :
    ∀ c : ℕ, ∃ (A : ColinearInput × List Bool → Output) (C : ℕ),
      RunsInTime encColinearInput encOutput A (colinearTime C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin : ℚ), M.Valid → 0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) →
        (∀ a b, a ≠ b → C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) →
        ∀ base u : Fin d → ℝ, u ≠ 0 → (∀ i, ∃ t : ℝ, M.μ i = base + t • u) →
        ∀ lo hi : ℝ, 0 < lo → (∀ v, lo * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M.cov *ᵥ v)) →
          (∀ v, v ⬝ᵥ (M.cov *ᵥ v) ≤ hi * (v ⬝ᵥ v)) →
        ∀ n : ℕ, (hi / (lo * M.sigmaSq u)) ^ C *
            ((d + 1) / (wmin : ℝ)) ^ (C * (Real.log (1 / wmin) + 1)) ≤ n →
        ∀ r : Rounding k d, IsRounding M.S (1 / n) r →
          1 - ((wmin : ℝ) / k) ^ c ≤ successProb M n r (fun pts ↦ ⟨k, wmin, pts⟩) A
            (colinearTime C) (ClustersWithin (((wmin : ℝ) / k) ^ c)) := by
  intro c
  obtain ⟨T₀, hT₀⟩ := colinearAlg_runsInTime
  refine ⟨fun xr ↦ colinearAlg xr.1, T₀ + Csep c + 2 * c + 24600,
    runsInTime_colinearTime_mono (by omega) hT₀, ?_⟩
  intro k d M wmin hM hwmin hw hsep base u hu hcol lo hi hlo hlo' hhi n hn r hr
  set C := T₀ + Csep c + 2 * c + 24600 with hC
  -- the weights
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hwpos : ∀ i, 0 ≤ M.w i := fun i ↦ hw0.le.trans (hw i)
  have hw1 : (wmin : ℝ) ≤ 1 := wmin_le_one hM hw0 hw
  have hw1q : wmin ≤ 1 := by exact_mod_cast hw1
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · have := hM.sum_w
      simp at this
    · exact h
  have hkw : (k : ℝ) * wmin ≤ 1 :=
    calc (k : ℝ) * wmin = ∑ _i : Fin k, (wmin : ℝ) := by simp
      _ ≤ ∑ i, M.w i := Finset.sum_le_sum fun i _ ↦ hw i
      _ = 1 := hM.sum_w
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exact absurd (Subsingleton.elim u 0) hu
    · exact h
  -- `σ²`
  have hcol' := hcol
  choose t hμ using hcol'
  have hσ := colinear_sigmaSq hM.posDef (cov_posDef M hM hwpos) hu (tau2_nonneg (t := t) hwpos)
    (cov_eq hM hμ)
  have hσ0 : 0 < M.sigmaSq u := hσ.2.1
  have hσ1 : M.sigmaSq u ≤ 1 := hσ.2.2
  -- `lo ≤ hi`
  have huu : 0 < u ⬝ᵥ u := by
    have h0 : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (u i)
    exact lt_of_le_of_ne h0 fun h ↦ hu (dotProduct_self_eq_zero.mp h.symm)
  have hlohi : lo ≤ hi := le_of_mul_le_mul_right ((hlo' u).trans (hhi u)) huu
  -- the sample size
  have hlog0 : 0 ≤ Real.log (1 / (wmin : ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
  have hB1 : (1 : ℝ) ≤ ((d : ℝ) + 1) / wmin := by
    rw [le_div_iff₀ hw0]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN := exponent_le hlog0 (logInv_add_one_le hwmin hw1q) (show 2 * c + 24600 ≤ C by omega)
  have hnB := sample_bound hB1 hσ0 hσ1 hlo hlohi (by omega) hN hn
  obtain ⟨hn8, hσn, hηpos, hacc, hprob⟩ :=
    main_numerics c hwmin hw1q hk hkw hd hσ0 hσ1 rfl hnB
  have hnpos : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < n)
  have hn8' : 8 ≤ n := by exact_mod_cast hn8
  have hsep' : ∀ a b, a ≠ b →
      (Csep c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b) := fun a b hab ↦
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show Csep c ≤ C by omega)) hlog0).trans
      (hsep a b hab)
  -- the good event
  refine le_trans ?_ (le_successProb_of_goodNoise hM hw0 hw hηpos hnpos (Dcol wmin) r
    (fun pts ↦ ⟨k, wmin, pts⟩) (fun xr ↦ colinearAlg xr.1) (colinearTime C)
    (ClustersWithin (((wmin : ℝ) / k) ^ c)) zero_le_one ?_)
  · rw [one_mul]
    linarith
  · intro ω hG
    have hU := uniformNoise_of_goodNoise_stdNoise M hM.posDef hG
    have hround : ∀ j, sqNormIn M.S ((fun j a ↦ (r (ω j) a : ℝ)) j -
        (M.μ (labels ω j) + (fun j i ↦ (ω j).2 i - M.μ (ω j).1 i) j)) ≤ 1 / (n : ℝ) ^ 2 := by
      intro j
      have h := hr (ω j).1 (ω j).2
      rw [Prod.mk.eta, _root_.one_div_pow] at h
      convert h using 2
      funext a
      simp [labels]
    have hcorr : ClustersWithin (((wmin : ℝ) / k) ^ c) (fun j ↦ (ω j).1)
        (colinearAlg ⟨k, wmin, roundedSample r ω⟩) := by
      change ClustersWithin _ (labels ω) (algInput (params wmin) ⟨k, wmin, roundedSample r ω⟩)
      rw [clustersWithin_algInput_roundedSample]
      exact alg_correct c M hM hwmin hw hsep' hu hcol hn8' hσn (labels ω) _ _ hround hG.1 hU hacc
    exact le_of_eq (coinProb_of_forall fun _ ↦ hcorr).symm

end BS23.Colinear
