module

public import BS23.SmallRadius.Budget
public import BS23.SmallRadius.GoodProb
public import BS23.Colinear.Main

/-!
# Theorem 1.3 of [BS23]

`BS23.SmallRadius.small_radius_clustering_main` is the statement of `BS23.small_radius_clustering`
(`BS23/Challenge.lean`), proved from its parts.

* **The algorithm** is `BS23.SmallRadius.srAlg budgetC` (`BS23/SmallRadius/Alg.lean`), with the
  unary budget `radiusTime budgetC x`, `budgetC = 2^14`. It does not depend on `c`. It runs in time
  `radiusTime T₀` for some `T₀` (`BS23.SmallRadius.srAlg_runsInTime`), hence in time
  `radiusTime C` for every `C ≥ T₀` (`BS23.SmallRadius.radiusTime_mono`).
* **`k = 1`**: the output is all zeros, which clusters the sample with error `0`
  (`BS23.SmallRadius.clustersWithin_replicate_zero`).
* **`k ≥ 2`**, so `wmin ≤ 1/2` and (by the separation) `d ≥ 1`. The sample size gives the guard
  (`BS23.SmallRadius.guard_of_sampleSize`), hence the parameter facts. On every sample in the
  graded good event `BS23.SmallRadius.GoodGraded` and for every rounding, the frame of the sample
  is good (`BS23.SmallRadius.frame_of_model`), the budget cuts nothing and suffices
  (`BS23.SmallRadius.budget_facts`, `BS23.SmallRadius.pow_le_budgetOf`), and peeling succeeds
  within `δ' = (wmin/k)^(c+2)` with probability at least `1 - δ'/2` over the coins
  (`BS23.SmallRadius.peel_good_of_sep`; `BS23.SmallRadius.le_coinProb_of_goodGraded`). The good
  event fails with probability at most `((d+1)/wmin)^(26t+4)/n ≤ δ'/2`
  (`BS23.SmallRadius.prob_not_goodGraded_le`, `BS23.SmallRadius.prob_arith`). So the success
  probability is at least `(1 - δ'/2)² ≥ 1 - δ' ≥ 1 - (wmin/k)^c`.
* **The numerics.** With the separation constant `Csep = 2^(4c+48)`, `ρ = 2^18 s/(Csep ln(1/w))`
  is at most `2^(-(4c+25))`, and with `2^s ≥ 256/w`, `ρ^s ≤ w^(4c+13)/2560`
  (`BS23.SmallRadius.rho_pow_le`); then `peel_good_of_sep`'s conditions hold for
  `n ≥ 4096 w^(-(4c+13))` (`BS23.SmallRadius.cross_arith`) and `n ≥ 2^(4c+13)`
  (`BS23.SmallRadius.err_arith`, via `n^(4c+13) ≤ 2^n`). All sample-size conditions are powers
  `B^N`, `B = (d+1)/wmin`, with `N ≤ (4c + 1465) Λ`, `Λ = R² + ln(1/wmin) + 1`, as
  `t ≤ 56 Λ` (`BS23.SmallRadius.tDeg_le_real`).

The constant of the theorem is `C = T₀ + 2^(4c+64) + 4c + 1465`.
-/

@[expose] public section

namespace BS23.SmallRadius

open MeasureTheory

/-! ### The running time -/

/-- `radiusTime C` is monotone in `C`. -/
theorem radiusTime_mono {C C' : ℕ} (h : C ≤ C') (x : RadiusInput) :
    radiusTime C x ≤ radiusTime C' x := by
  unfold radiusTime
  exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ h)

/-! ### Clustering facts -/

/-- `BS23.ClustersWithin` is monotone in the error. -/
theorem clustersWithin_mono {n k : ℕ} {ε ε' : ℝ} (h : ε ≤ ε') {ℓ : Fin n → Fin k} {out : Output}
    (hc : ClustersWithin ε ℓ out) : ClustersWithin ε' ℓ out :=
  ⟨hc.1, hc.2.1, hc.2.2.imp fun _ hπ => hπ.trans h⟩

/-- **One component**: all zeros clusters a nonempty sample with any error `ε ≥ 0`. -/
theorem clustersWithin_replicate_zero {n : ℕ} (hn : 0 < n) (ℓ : Fin n → Fin 1) {ε : ℝ}
    (hε : 0 ≤ ε) : ClustersWithin ε ℓ (List.replicate n 0) := by
  have hout : ∀ j : Fin n, outCluster (List.replicate n 0) j = 0 := fun j => by
    simp [outCluster, List.getD_eq_getElem?_getD, j.2]
  refine ⟨List.length_replicate, fun j => by rw [hout]; omega, 1, ?_⟩
  have hfull : ((Finset.univ.filter fun j : Fin n => outCluster (List.replicate n 0) j =
      ((0 : Fin 1) : ℕ)) ∩ cluster ℓ ((1 : Equiv.Perm (Fin 1)) 0)) = Finset.univ := by
    ext j
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, hout, cluster,
      Fin.val_zero, iff_true]
    exact Subsingleton.elim _ _
  rw [Fin.sum_univ_one, hfull, Finset.card_univ, Fintype.card_fin]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_self hn']
  linarith

/-! ### Numerics -/

/-- From the sample size `B^(C Λ) ≤ n` (a real power) to `B^N ≤ n` for `N ≤ C Λ`. -/
theorem pow_le_of_rpow_le' {B Λ n : ℝ} {C N : ℕ} (hB : 1 ≤ B) (hN : (N : ℝ) ≤ C * Λ)
    (hn : B ^ ((C : ℝ) * Λ) ≤ n) : B ^ N ≤ n := by
  rw [← Real.rpow_natCast]
  exact (Real.rpow_le_rpow_of_exponent_le hB hN).trans hn

/-- `n^b ≤ 2^n` for `n ≥ 2^20` and `2^b ≤ n`. -/
theorem pow_le_two_pow_of {n b : ℕ} (hn : 2 ^ 20 ≤ n) (hb : 2 ^ b ≤ n) : n ^ b ≤ 2 ^ n := by
  have hn0 : n ≠ 0 := by positivity
  set L := Nat.log 2 n with hLdef
  have hL : 2 ^ L ≤ n := Nat.pow_log_le_self 2 hn0
  have hL' : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hbL : b < L + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hb.trans_lt hL')
  have h20 : 20 < L + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hn.trans_lt hL')
  have h1 : n ^ b ≤ 2 ^ ((L + 1) * b) := by
    rw [pow_mul 2]; exact Nat.pow_le_pow_left hL'.le _
  have h2 : (L + 1) * b ≤ 14 * L ^ 2 := by
    calc (L + 1) * b ≤ (L + 1) * L := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 14 * L ^ 2 := by nlinarith
  calc n ^ b ≤ 2 ^ ((L + 1) * b) := h1
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num)
        (h2.trans ((fourteen_sq_le_two_pow (by omega)).trans hL))

section Real

variable {w k : ℝ}

/-- `w² ≤ w / k` for `k ≤ 1/w`. -/
theorem sq_le_div (hw : 0 < w) (hk : 0 < k) (hkw : k * w ≤ 1) : w ^ 2 ≤ w / k := by
  rw [le_div_iff₀ hk]
  nlinarith

/-- `w^(4c+9) ≤ δ'² w` for `δ' = (w/k)^(c+2)`. -/
theorem pow_le_delta_sq (c : ℕ) (hw : 0 < w) (hk : 0 < k) (hkw : k * w ≤ 1) :
    w ^ (4 * c + 9) ≤ ((w / k) ^ (c + 2)) ^ 2 * w := by
  have h := sq_le_div hw hk hkw
  have h1 : (w ^ 2) ^ (2 * c + 4) ≤ (w / k) ^ (2 * c + 4) := pow_le_pow_left₀ (by positivity) h _
  calc w ^ (4 * c + 9) = (w ^ 2) ^ (2 * c + 4) * w := by ring
    _ ≤ (w / k) ^ (2 * c + 4) * w := mul_le_mul_of_nonneg_right h1 hw.le
    _ = ((w / k) ^ (c + 2)) ^ 2 * w := by ring

/-- **The cross ratio**: `ρ^s ≤ w^(4c+13)/2560` for `ρ = 2^18 s / (2^(4c+48) ln (1/w))`, when
`256 ≤ w 2^s`, `s ≤ 20 + 3 ln (1/w)` and `w ≤ 1/2`. -/
theorem rho_pow_le (c : ℕ) {s : ℕ} (hw : 0 < w) (hw2 : w ≤ 1 / 2) (hs : 256 ≤ w * 2 ^ s)
    (hsle : (s : ℝ) ≤ 20 + 3 * Real.log (1 / w)) :
    (2 ^ 18 * (s : ℝ) / ((2 ^ (4 * c + 48) : ℕ) * Real.log (1 / w))) ^ s ≤
      w ^ (4 * c + 13) / 2560 := by
  set Lg := Real.log (1 / w) with hLg
  have hl2 := Real.log_two_gt_d9
  have hLg2 : Real.log 2 ≤ Lg := Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hw]; linarith)
  have hLg0 : 0 < Lg := by linarith
  have hsL : (s : ℝ) ≤ 32 * Lg := by linarith
  set a := 4 * c + 13 with ha
  have hρ0 : 0 ≤ 2 ^ 18 * (s : ℝ) / ((2 ^ (4 * c + 48) : ℕ) * Lg) := by positivity
  have hρ : 2 ^ 18 * (s : ℝ) / ((2 ^ (4 * c + 48) : ℕ) * Lg) ≤ 1 / 2 ^ (a + 12) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    have e : (2 : ℝ) ^ (4 * c + 48) = 2 ^ (a + 12) * 2 ^ 23 := by
      rw [← pow_add]
    rw [e]
    have : (2 : ℝ) ^ 18 * s * 2 ^ (a + 12) ≤ 2 ^ 18 * (32 * Lg) * 2 ^ (a + 12) := by gcongr
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (a + 12)]
  have h2s : 1 / (2 : ℝ) ^ s ≤ w / 256 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  calc (2 ^ 18 * (s : ℝ) / ((2 ^ (4 * c + 48) : ℕ) * Lg)) ^ s ≤ (1 / 2 ^ (a + 12)) ^ s :=
        pow_le_pow_left₀ hρ0 hρ _
    _ = (1 / (2 : ℝ) ^ s) ^ (a + 12) := by
        rw [div_pow, div_pow, one_pow, one_pow, ← pow_mul, ← pow_mul, mul_comm]
    _ ≤ (w / 256) ^ (a + 12) := pow_le_pow_left₀ (by positivity) h2s _
    _ = w ^ a * (w ^ 12 / 256 ^ (a + 12)) := by rw [div_pow, pow_add w]; ring
    _ ≤ w ^ a * (1 / 2560) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hw12 : w ^ 12 ≤ 1 := pow_le_one₀ hw.le (by linarith)
        have h256 : (2560 : ℝ) ≤ 256 ^ (a + 12) :=
          calc (2560 : ℝ) ≤ 256 ^ 2 := by norm_num
            _ ≤ 256 ^ (a + 12) := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
    _ = w ^ a / 2560 := by ring

/-- **The cross condition of peeling**: `640 k² (k² (2 n² ρ^s + 1)) ≤ δ'² w n²` for
`δ' = (w/k)^(c+2)`, when `ρ^s ≤ w^(4c+13)/2560`, `k ≤ 1/w` and `n ≥ 4096 w^(-(4c+13))`. -/
theorem cross_arith (c : ℕ) {n ρs : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hk : 0 < k)
    (hkw : k * w ≤ 1) (hρ : ρs ≤ w ^ (4 * c + 13) / 2560)
    (hn : 4096 * (1 / w) ^ (4 * c + 13) ≤ n) :
    640 * k ^ 2 * (k ^ 2 * (2 * n ^ 2 * ρs + 1)) ≤ ((w / k) ^ (c + 2)) ^ 2 * w * n ^ 2 := by
  set a := 4 * c + 13 with ha
  have hwa : 0 < w ^ a := pow_pos hw _
  have hk4 : k ^ 4 * w ^ 4 ≤ 1 := by
    have h := pow_le_one₀ (by positivity) hkw (n := 4)
    rwa [mul_pow] at h
  have hnw : 4096 ≤ n * w ^ a := by
    have e : (1 / w) ^ a * w ^ a = 1 := by rw [← mul_pow, one_div, inv_mul_cancel₀ hw.ne', one_pow]
    have := mul_le_mul_of_nonneg_right hn hwa.le
    rw [mul_assoc, e, mul_one] at this
    linarith
  have hn0 : 0 < n := by
    have : 0 < (1 / w) ^ a := by positivity
    linarith
  have hδ := pow_le_delta_sq c hw hk hkw
  -- `k⁴ (n² w^a / 2 + 640) ≤ w^(4c+9) n²`
  have key : k ^ 4 * (n ^ 2 * w ^ a / 2 + 640) ≤ w ^ (4 * c + 9) * n ^ 2 := by
    have e1 : w ^ a = w ^ (4 * c + 9) * w ^ 4 := by rw [ha, ← pow_add]
    have hn1 : 1 ≤ n := by
      have : 1 ≤ (1 / w) ^ a := one_le_pow₀ (by rw [le_div_iff₀ hw]; linarith)
      linarith
    have h640 : 1280 ≤ n ^ 2 * w ^ a := by
      calc (1280 : ℝ) ≤ 1 * 4096 := by norm_num
        _ ≤ n * (n * w ^ a) := mul_le_mul hn1 hnw (by norm_num) (by linarith)
        _ = n ^ 2 * w ^ a := by ring
    have hX : 0 ≤ n ^ 2 * w ^ a / 2 + 640 := by positivity
    calc k ^ 4 * (n ^ 2 * w ^ a / 2 + 640) ≤ k ^ 4 * (n ^ 2 * w ^ a) := by
          gcongr; linarith
      _ = (k ^ 4 * w ^ 4) * (w ^ (4 * c + 9) * n ^ 2) := by rw [e1]; ring
      _ ≤ 1 * (w ^ (4 * c + 9) * n ^ 2) := by gcongr
      _ = w ^ (4 * c + 9) * n ^ 2 := one_mul _
  calc 640 * k ^ 2 * (k ^ 2 * (2 * n ^ 2 * ρs + 1))
      = k ^ 4 * (1280 * n ^ 2 * ρs + 640) := by ring
    _ ≤ k ^ 4 * (1280 * n ^ 2 * (w ^ a / 2560) + 640) := by gcongr
    _ = k ^ 4 * (n ^ 2 * w ^ a / 2 + 640) := by ring
    _ ≤ w ^ (4 * c + 9) * n ^ 2 := key
    _ ≤ ((w / k) ^ (c + 2)) ^ 2 * w * n ^ 2 := by gcongr

/-- **The soundness condition of peeling**: `2^11 k² n ≤ δ'² w 2^n` for `δ' = (w/k)^(c+2)`, when
`k ≤ 1/w ≤ n` and `n^(4c+13) ≤ 2^n`, `2^11 ≤ n`. -/
theorem err_arith (c : ℕ) {n : ℕ} (hw : 0 < w) (hk : 0 < k) (hkw : k * w ≤ 1)
    (hwn : 1 / w ≤ n) (h11 : (2 : ℝ) ^ 11 ≤ n) (hpow : (n : ℝ) ^ (4 * c + 13) ≤ 2 ^ n) :
    2 ^ 11 * k ^ 2 * n ≤ ((w / k) ^ (c + 2)) ^ 2 * w * 2 ^ n := by
  have hδ := pow_le_delta_sq c hw hk hkw
  have hn0 : (0 : ℝ) < n := by linarith
  have hwn1 : 1 ≤ w * n := by rw [div_le_iff₀ hw] at hwn; linarith
  have hk2 : k ^ 2 * w ^ 2 ≤ 1 := by
    have h := pow_le_one₀ (by positivity) hkw (n := 2)
    rwa [mul_pow] at h
  have h1 : (1 : ℝ) ≤ (w * n) ^ (4 * c + 11) := one_le_pow₀ hwn1
  calc 2 ^ 11 * k ^ 2 * (n : ℝ) ≤ 2 ^ 11 * k ^ 2 * n * (w * n) ^ (4 * c + 11) :=
        le_mul_of_one_le_right (by positivity) h1
    _ = (k ^ 2 * w ^ 2) * (w ^ (4 * c + 9) * (2 ^ 11 * (n : ℝ) ^ (4 * c + 12))) := by ring
    _ ≤ 1 * (w ^ (4 * c + 9) * ((n : ℝ) * (n : ℝ) ^ (4 * c + 12))) := by gcongr
    _ = w ^ (4 * c + 9) * (n : ℝ) ^ (4 * c + 13) := by ring
    _ ≤ ((w / k) ^ (c + 2)) ^ 2 * w * 2 ^ n := by gcongr

/-- **The failure probability**: `B^(26t+4)/n ≤ δ'/2` for `δ' = (w/k)^(c+2)` when
`n ≥ B^(26t + 2c + 9)`, `B ≥ 2`, `B ≥ 1/w` and `k ≤ 1/w`. -/
theorem prob_arith (c t : ℕ) {B n : ℝ} (hw : 0 < w) (hk : 0 < k) (hkw : k * w ≤ 1) (hB2 : 2 ≤ B)
    (hBw : 1 / w ≤ B) (hn : B ^ (26 * t + 2 * c + 9) ≤ n) :
    B ^ (26 * t + 4) / n ≤ (w / k) ^ (c + 2) / 2 := by
  have hB0 : 0 < B := by linarith
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hwB : 1 ≤ w * B := by rw [div_le_iff₀ hw] at hBw; linarith
  have hu : w ^ 2 ≤ w / k := sq_le_div hw hk hkw
  have hδ : 1 ≤ (w / k) ^ (c + 2) * B ^ (2 * c + 4) := by
    calc (1 : ℝ) ≤ (w * B) ^ (2 * c + 4) := one_le_pow₀ hwB
      _ = (w ^ 2) ^ (c + 2) * B ^ (2 * c + 4) := by ring
      _ ≤ (w / k) ^ (c + 2) * B ^ (2 * c + 4) := by gcongr
  rw [div_le_iff₀ hn0]
  calc B ^ (26 * t + 4) ≤ B ^ (26 * t + 4) * ((w / k) ^ (c + 2) * B ^ (2 * c + 4)) :=
        le_mul_of_one_le_right (by positivity) hδ
    _ = (w / k) ^ (c + 2) / 2 * (2 * B ^ (26 * t + 2 * c + 8)) := by ring
    _ ≤ (w / k) ^ (c + 2) / 2 * (B * B ^ (26 * t + 2 * c + 8)) := by gcongr
    _ = (w / k) ^ (c + 2) / 2 * B ^ (26 * t + 2 * c + 9) := by ring
    _ ≤ (w / k) ^ (c + 2) / 2 * n := by gcongr

end Real

/-! ### One good sample -/

/-- **On a sample in the graded good event**, for every rounding within `1/n`: on the guard, the
algorithm clusters the sample within `ε` with probability at least `1 - δ'/2` over `T` coins, for
`δ' ≤ ε` satisfying the conditions of `BS23.SmallRadius.peel_good_of_sep`. -/
theorem le_coinProb_of_goodGraded {k d n : ℕ} (M : Mixture k d) (hM : M.Valid) {wmin : ℚ}
    (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i) {R : ℚ}
    (hrad : ∀ i, sqNormIn M.S (M.μ i) ≤ (R : ℝ) ^ 2) {Csep : ℝ} (hCsep : 0 < Csep)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / (wmin : ℝ)) ≤ sqNormIn M.S (M.μ a - M.μ b))
    (hG : NumGuard k wmin R n d) (hw2 : (wmin : ℝ) ≤ 1 / 2) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)}
    (hω : GoodGraded M wmin (tDeg wmin R) ω) {δ' : ℝ} (hδ : 0 < δ') (hδw : δ' ≤ (wmin : ℝ) / 4)
    (hε : 640 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 *
        (2 ^ 18 * (sDeg wmin : ℝ) / (Csep * Real.log (1 / (wmin : ℝ)))) ^ sDeg wmin + 1)) ≤
      δ' ^ 2 * wmin * (n : ℝ) ^ 2)
    (herr : 2 ^ 11 * (k : ℝ) ^ 2 * n ≤ δ' ^ 2 * wmin * 2 ^ n)
    {T : ℕ} (hT : k * coinBits n ≤ T) {ε : ℝ} (hδε : δ' ≤ ε) :
    1 - δ' / 2 ≤ coinProb T (fun c => ClustersWithin ε (fun j => (ω j).1)
      (srAlg budgetC (⟨k, wmin, R, roundedSample r ω⟩, c))) := by
  have hP := srParams_of_numGuard hG hwmin hw2
  obtain ⟨hL, hF⟩ := frame_of_model M hM hw hrad hsep hP hr hω
  have hLb : n ^ (6 * (64 * tDeg wmin R + 1)) ≤
      budgetOf budgetC ⟨k, wmin, R, roundedSample r ω⟩ := by
    have h := pow_le_budgetOf ⟨k, wmin, R, roundedSample r ω⟩
    simpa [roundedSample] using h
  obtain ⟨hfit, hbud⟩ := budget_facts hG (roundedPts r ω) hLb
  have hpeel := peel_good_of_sep hF hfit hbud hCsep hδ hδw hε herr hT
  refine hpeel.trans (coinProb_mono fun c hc => ?_)
  rw [srAlg_eq, clustersWithin_srCore_roundedSample, srLabels_of_guard hG hL]
  exact clustersWithin_mono hδε hc

/-! ### The coins -/

/-- The `k (n + 8)` coins of the algorithm are among the `radiusTime C x` coins for `C ≥ 3`, when
`k ≤ n`. -/
theorem coinBits_le_radiusTime {k n C : ℕ} (hkn : k ≤ n) (hC : 3 ≤ C) (x : RadiusInput)
    (hx : x.points.length = n) : k * coinBits n ≤ radiusTime C x := by
  have hn := RT.length_points_le x
  rw [hx] at hn
  unfold radiusTime coinBits
  have h3 : n * (n + 8) ≤ (n + 2) ^ 3 := by
    have e : (n + 2) ^ 3 = n * (n + 8) + (n ^ 3 + 5 * n ^ 2 + 4 * n + 8) := by ring
    rw [e]
    exact Nat.le_add_right _ _
  calc k * (n + 8) ≤ n * (n + 8) := Nat.mul_le_mul_right _ hkn
    _ ≤ (n + 2) ^ 3 := h3
    _ ≤ ((encRadiusInput x).length + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    _ ≤ ((encRadiusInput x).length + 2) ^ (C * (⌈x.R ^ 2⌉₊ + logInv x.wmin + 1)) :=
        Nat.pow_le_pow_right (by omega) (le_trans hC (Nat.le_mul_of_pos_right _ (by omega)))

/-! ### Small real facts -/

theorem nat_le_mul_of {N K : ℕ} {Λ : ℝ} (h : N ≤ K) (hΛ : 1 ≤ Λ) : (N : ℝ) ≤ (K : ℝ) * Λ :=
  (Nat.cast_le.2 h).trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hΛ)

theorem exponent_le_t {t c : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (ht : (t : ℝ) ≤ 56 * Λ) :
    ((26 * t + 2 * c + 9 : ℕ) : ℝ) ≤ ((4 * c + 1465 : ℕ) : ℝ) * Λ := by
  push_cast
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  nlinarith

theorem one_sub_le_sq {δ ε : ℝ} (hδ : δ ≤ ε) :
    1 - ε ≤ (1 - δ / 2) * (1 - δ / 2) := by
  nlinarith [sq_nonneg δ]

/-- `δ' = (w/k)^(c+2) ≤ w / 4` for `k ≥ 2`, and `δ' ≤ (w/k)^c`. -/
theorem delta_facts (c : ℕ) {w k : ℝ} (hw0 : 0 < w) (hw2 : w ≤ 1 / 2) (hk2 : 2 ≤ k) :
    0 < (w / k) ^ (c + 2) ∧ (w / k) ^ (c + 2) ≤ w / 4 ∧ (w / k) ^ (c + 2) ≤ (w / k) ^ c := by
  have hk0 : 0 < k := by linarith
  have hu0 : 0 < w / k := by positivity
  have hu2 : w / k ≤ w / 2 := div_le_div_of_nonneg_left hw0.le (by norm_num) hk2
  have hu1 : w / k ≤ 1 := by linarith
  refine ⟨by positivity, ?_, pow_le_pow_of_le_one hu0.le hu1 (by omega)⟩
  calc (w / k) ^ (c + 2) ≤ (w / k) ^ 2 := pow_le_pow_of_le_one hu0.le hu1 (by omega)
    _ = (w / k) * (w / k) := sq _
    _ ≤ (w / 2) * (1 / 4) := mul_le_mul hu2 (by linarith) hu0.le (by linarith)
    _ ≤ w / 4 := by linarith

/-- `4096 w^(-(4c+13)) ≤ B^(4c+19)` for `B ≥ 4`, `B ≥ 1/w`. -/
theorem le_pow_B (c : ℕ) {w B : ℝ} (hw0 : 0 < w) (hB4 : 4 ≤ B) (hBw : 1 / w ≤ B) :
    4096 * (1 / w) ^ (4 * c + 13) ≤ B ^ (4 * c + 19) := by
  have h2 : (4096 : ℝ) ≤ B ^ 6 :=
    calc (4096 : ℝ) = 4 ^ 6 := by norm_num
      _ ≤ B ^ 6 := pow_le_pow_left₀ (by norm_num) hB4 6
  calc 4096 * (1 / w) ^ (4 * c + 13) ≤ B ^ 6 * B ^ (4 * c + 13) :=
        mul_le_mul h2 (pow_le_pow_left₀ (by positivity) hBw _) (by positivity) (by positivity)
    _ = B ^ (4 * c + 19) := by rw [← pow_add]; ring_nf

/-! ### Theorem 1.3 for `k ≥ 2` -/

/-- **Theorem 1.3 for at least two components**, with the constant `C ≥ 2^(4c+64) + 4c + 1465`
in the separation and the sample size. -/
theorem success_of_two_le (c : ℕ) {k d : ℕ} (M : Mixture k d) (hM : M.Valid) {wmin : ℚ}
    (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i) (hk : 2 ≤ k) {C : ℕ}
    (hC : 2 ^ (4 * c + 64) + 4 * c + 1465 ≤ C)
    (hsep : ∀ a b, a ≠ b → C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) {R : ℚ}
    (hrad : ∀ i, sqNormIn M.S (M.μ i) ≤ (R : ℝ) ^ 2) {n : ℕ}
    (hn : ((d + 1) / (wmin : ℝ)) ^ (C * ((R : ℝ) ^ 2 + Real.log (1 / wmin) + 1)) ≤ n)
    {r : Rounding k d} (hr : IsRounding M.S (1 / n) r) :
    1 - ((wmin : ℝ) / k) ^ c ≤ successProb M n r (fun pts ↦ ⟨k, wmin, R, pts⟩) (srAlg budgetC)
      (radiusTime C) (ClustersWithin (((wmin : ℝ) / k) ^ c)) := by
  -- the constants
  obtain ⟨X, hX48, hX64, hXC⟩ : ∃ X, 2 ^ (4 * c + 48) ≤ X ∧ 2 ^ 64 ≤ X ∧
      X + 4 * c + 1465 ≤ C :=
    ⟨_, Nat.pow_le_pow_right (by norm_num) (by omega),
      Nat.pow_le_pow_right (by norm_num) (by omega), hC⟩
  have hC3 : 3 ≤ C := by omega
  have hCsepN : 2 ^ (4 * c + 48) ≤ C := by omega
  have hC64 : (2 : ℝ) ^ 64 ≤ C := by
    have : 2 ^ 64 ≤ C := by omega
    exact_mod_cast this
  have hClin : 4 * c + 1465 ≤ C := by omega
  have hClin' : ((4 * c + 1465 : ℕ) : ℝ) ≤ C := by exact_mod_cast hClin
  -- the weights
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hwpos : ∀ i, 0 ≤ M.w i := fun i => hw0.le.trans (hw i)
  have hkw : (k : ℝ) * wmin ≤ 1 :=
    calc (k : ℝ) * wmin = ∑ _i : Fin k, (wmin : ℝ) := by simp
      _ ≤ ∑ i, M.w i := Finset.sum_le_sum fun i _ => hw i
      _ = 1 := hM.sum_w
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hw2 : (wmin : ℝ) ≤ 1 / 2 := by
    have : 2 * (wmin : ℝ) ≤ k * wmin := mul_le_mul_of_nonneg_right hk2 hw0.le
    linarith
  have hw1 : (wmin : ℝ) ≤ 1 := by linarith
  have hiw : 2 ≤ 1 / (wmin : ℝ) := by rw [le_div_iff₀ hw0]; linarith
  have hlog : 0 < Real.log (1 / (wmin : ℝ)) := Real.log_pos (by linarith)
  -- the dimension
  have hd : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · exfalso
      have h := hsep ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
      have h0 : sqNormIn M.S (M.μ ⟨0, by omega⟩ - M.μ ⟨1, by omega⟩) = 0 := by
        simp [sqNormIn, dotProduct]
      have hC0 : (0 : ℝ) < C := by
        have : 0 < C := by omega
        exact_mod_cast this
      have := mul_pos hC0 hlog
      linarith
    · exact h
  -- the guard and the parameters
  have hG : NumGuard k wmin R n d := guard_of_sampleSize hk hd hwmin hw2 hkw hC64 hn
  have hP := srParams_of_numGuard hG hwmin hw2
  have hn0 : 0 < n := hP.n_pos
  have ht56 := hP.t_le
  have ht1 : 1 ≤ tDeg wmin R := by have := eight_le_tDeg wmin R; omega
  -- the sample size
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((d : ℝ) + 1) / wmin := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (R : ℝ) ^ 2 + Real.log (1 / wmin) + 1 := ⟨_, rfl⟩
  rw [← hB, ← hΛ] at hn
  rw [← hΛ] at ht56
  have hd1 : (2 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hBw : 1 / (wmin : ℝ) ≤ B := by
    rw [hB, div_le_div_iff_of_pos_right hw0]; linarith
  have hB4 : 4 ≤ B := by
    have e : B = ((d : ℝ) + 1) * (1 / wmin) := by rw [hB]; ring
    rw [e]
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ ((d : ℝ) + 1) * (1 / wmin) := mul_le_mul hd1 hiw (by norm_num) (by linarith)
  have hB2 : 2 ≤ B := by linarith
  have hΛ1 : 1 ≤ Λ := by
    have := sq_nonneg (R : ℝ)
    rw [hΛ]; linarith
  have key : ∀ N : ℕ, (N : ℝ) ≤ (4 * c + 1465 : ℕ) * Λ → B ^ N ≤ n := fun N hN =>
    pow_le_of_rpow_le' (by linarith) (hN.trans (mul_le_mul_of_nonneg_right hClin' (by linarith)))
      hn
  -- the separation
  have hCsep0 : (0 : ℝ) < ((2 ^ (4 * c + 48) : ℕ) : ℝ) := by positivity
  have hCsepC : ((2 ^ (4 * c + 48) : ℕ) : ℝ) ≤ C := Nat.cast_le.2 hCsepN
  have hsep' : ∀ a b, a ≠ b → ((2 ^ (4 * c + 48) : ℕ) : ℝ) * Real.log (1 / (wmin : ℝ)) ≤
      sqNormIn M.S (M.μ a - M.μ b) :=
    fun a b hab => le_trans (mul_le_mul_of_nonneg_right hCsepC hlog.le) (hsep a b hab)
  -- the accuracy `δ'`
  obtain ⟨hδ0, hδw, hδc⟩ := delta_facts c hw0 hw2 hk2
  -- the conditions of peeling
  have hρ := rho_pow_le c hw0 hw2 hP.s_ge hP.s_le
  have hn4096 : 4096 * (1 / (wmin : ℝ)) ^ (4 * c + 13) ≤ n :=
    (le_pow_B c hw0 hB4 hBw).trans (key _ (nat_le_mul_of (by omega) hΛ1))
  have hε := cross_arith c hw0 hw1 hk0 hkw hρ hn4096
  have hpow : (n : ℝ) ^ (4 * c + 13) ≤ 2 ^ n := by
    have h1 : B ^ (4 * c + 13) ≤ n := key _ (nat_le_mul_of (by omega) hΛ1)
    have h2 : (2 : ℝ) ^ (4 * c + 13) ≤ n := (pow_le_pow_left₀ (by norm_num) hB2 _).trans h1
    have h3 : 2 ^ (4 * c + 13) ≤ n := by exact_mod_cast h2
    have h4 := pow_le_two_pow_of hP.n_ge h3
    exact_mod_cast h4
  have h11 : (2 : ℝ) ^ 11 ≤ n := by
    have : 2 ^ 11 ≤ n := le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hP.n_ge
    exact_mod_cast this
  have herr := err_arith c hw0 hk0 hkw hP.inv_w_le_n h11 hpow
  -- the failure probability
  have hfail : (M.sampleLaw n {ω | ¬ GoodGraded M wmin (tDeg wmin R) ω}).toReal ≤
      ((wmin : ℝ) / k) ^ (c + 2) / 2 := by
    refine (prob_not_goodGraded_le hM hw0 hw2 hw hn0 ht1).trans ?_
    rw [← hB]
    exact prob_arith c (tDeg wmin R) hw0 hk0 hkw hB2 hBw (key _ (exponent_le_t hΛ1 ht56))
  -- the glue
  have hglue := mul_one_sub_le_successProb hM hwpos r
    (fun pts ↦ (⟨k, wmin, R, pts⟩ : RadiusInput))
    (srAlg budgetC) (radiusTime C) (ClustersWithin (((wmin : ℝ) / k) ^ c))
    (measurableSet_goodGraded M n wmin (tDeg wmin R)) (p := 1 - ((wmin : ℝ) / k) ^ (c + 2) / 2)
    (δ := ((wmin : ℝ) / k) ^ (c + 2) / 2) (by linarith)
    (fun ω hω => le_coinProb_of_goodGraded M hM hwmin hw hrad hCsep0 hsep' hG hw2 hr hω hδ0 hδw
      hε herr (coinBits_le_radiusTime hG.k_le hC3 _ (by simp [roundedSample])) hδc)
    (by rw [Set.compl_ofPred]; exact hfail)
  exact le_trans (one_sub_le_sq hδc) hglue

/-! ### Theorem 1.3 for one component -/

/-- **Theorem 1.3 for one component**: the output is all zeros, which clusters every sample with
error `0`, so the success probability is `1` (for a sample size `n ≥ 1`). -/
theorem success_of_one {d : ℕ} (M : Mixture 1 d) (hM : M.Valid) {wmin : ℚ}
    (hw : ∀ i, (wmin : ℝ) ≤ M.w i) (hwmin : 0 < wmin) {R : ℚ} {n : ℕ} (hn : 0 < n)
    (r : Rounding 1 d) (T : RadiusInput → ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    1 - ε ≤ successProb M n r (fun pts ↦ ⟨1, wmin, R, pts⟩) (srAlg budgetC) T
      (ClustersWithin ε) := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hwpos : ∀ i, 0 ≤ M.w i := fun i => hw0.le.trans (hw i)
  have h := le_successProb (n := n) hM hwpos r (fun pts ↦ (⟨1, wmin, R, pts⟩ : RadiusInput))
    (srAlg budgetC) T (ClustersWithin ε) MeasurableSet.univ (p := 1) fun ω _ => by
      refine le_of_eq (coinProb_of_forall fun cs => ?_).symm
      rw [srAlg_eq, srCore_of_k_le_one (le_refl 1)]
      have hlen : (⟨1, wmin, R, roundedSample r ω⟩ : RadiusInput).points.length = n := by
        simp [roundedSample]
      rw [hlen]
      exact clustersWithin_replicate_zero hn _ hε
  have := M.isProbabilityMeasure_sampleLaw hM hwpos n
  rw [measure_univ, ENNReal.toReal_one, one_mul] at h
  linarith

/-! ### Theorem 1.3 -/

/-- **Theorem 1.3** of [BS23] (full version: Theorem 7.1): the statement of
`BS23.small_radius_clustering`. The algorithm is `BS23.SmallRadius.srAlg budgetC`, and the
constant is `C = T₀ + 2^(4c+64) + 4c + 1465` with `T₀` its time constant. -/
theorem small_radius_clustering_main :
    ∀ c : ℕ, ∃ (A : RadiusInput × List Bool → Output) (C : ℕ),
      RunsInTime encRadiusInput encOutput A (radiusTime C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin : ℚ), M.Valid → 0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) →
        (∀ a b, a ≠ b → C * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) →
        ∀ R : ℚ, (∀ i, sqNormIn M.S (M.μ i) ≤ (R : ℝ) ^ 2) →
        ∀ n : ℕ, ((d + 1) / (wmin : ℝ)) ^ (C * ((R : ℝ) ^ 2 + Real.log (1 / wmin) + 1)) ≤ n →
        ∀ r : Rounding k d, IsRounding M.S (1 / n) r →
          1 - ((wmin : ℝ) / k) ^ c ≤ successProb M n r (fun pts ↦ ⟨k, wmin, R, pts⟩) A
            (radiusTime C) (ClustersWithin (((wmin : ℝ) / k) ^ c)) := by
  intro c
  obtain ⟨T₀, hT₀⟩ := srAlg_runsInTime budgetC
  refine ⟨srAlg budgetC, T₀ + 2 ^ (4 * c + 64) + 4 * c + 1465,
    Colinear.runsInTime_mono hT₀ (radiusTime_mono (by generalize 2 ^ (4 * c + 64) = X; omega)), ?_⟩
  intro k d M wmin hM hwmin hw hsep R hrad n hn r hr
  rcases Nat.lt_or_ge k 2 with hk | hk
  · -- one component
    have hk1 : k = 1 := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · have := hM.sum_w
        simp at this
      · omega
    subst hk1
    have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
    have hw1 : (wmin : ℝ) ≤ 1 := (hw 0).trans (le_of_eq (by simpa using hM.sum_w))
    have hn1 : (1 : ℝ) ≤ n := by
      refine le_trans (Real.one_le_rpow ?_ ?_) hn
      · rw [le_div_iff₀ hw0]
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith
      · have h1 : 0 ≤ Real.log (1 / (wmin : ℝ)) :=
          Real.log_nonneg (by rw [le_div_iff₀ hw0]; linarith)
        have h2 := sq_nonneg (R : ℝ)
        positivity
    have hn0 : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < n)
    exact success_of_one M hM hw hwmin hn0 r _ (by positivity)
  · exact success_of_two_le c M hM hwmin hw hk (by generalize 2 ^ (4 * c + 64) = X; omega) hsep
      hrad hn hr

end BS23.SmallRadius
