module

public import BS23.ColinearSoS.Correct
public import BS23.ColinearSoS.RunTime
public import BS23.Colinear.Main
public import BS23.Common.Glue

/-!
# Theorem 1.2 of [BS23] along the sum-of-squares route

`BS23.ColinearSoS.colinear_clustering_main` is the statement of `BS23.colinear_clustering`
(`BS23/Challenge.lean`), proved with the sum-of-squares algorithm
`BS23.ColinearSoS.colinearSoSAlg`:

* the algorithm ignores its coins and runs in time `colinearTime C`
  (`BS23.ColinearSoS.colinearSoSAlg_runsInTime`; the time bound is monotone in `C`,
  `BS23.Colinear.colinearTime_mono`);
* on every sample in the good event `BS23.GoodNoise` of degree `D = DcolS wmin` and accuracy `η`,
  for every rounding, it clusters the sample with error `(wmin / k)^c`
  (`BS23.ColinearSoS.colLabels_correct`, with the algorithm on a rounded sample read as in
  `BS23.ColinearSoS.colinearSoSAlg_roundedSample`);
* the good event fails with probability at most `k / (n η²) (1 / wmin + (d+1)^D (2D)^D)`
  (`BS23.le_successProb_of_goodNoise`).

The accuracy is `η = colSoSTarget wmin d σ² / (4 (d+1)^D)`. With `B = (d + 1) / wmin ≥ 2`,
`L = logInv wmin` and `t = tCol wmin = 256 (L + 1)`, the base of the target is
`Q = mpBase d t wmin ≤ B^39` (`BS23.ColinearSoS.MainS.mpBase_le_B`), so
`σ² ≤ colSoSTarget wmin d σ² · B^(50040 (L + 1))` (`BS23.ColinearSoS.MainS.target_bound`), and
`2D ≤ B^14`, `D ≤ 520 (L + 1)` (`BS23.ColinearSoS.MainS.two_DcolS_le_B`). So a sample of size
`σ⁻⁴ B^(2c + 109000 (L + 1))` suffices (`BS23.ColinearSoS.MainS.main_numerics`), which the
hypothesis of the theorem gives for `C ≥ 2c + 327000`, as `L + 1 ≤ 3 (log (1/wmin) + 1)`
(`BS23.Colinear.logInv_add_one_le`, `BS23.Colinear.sample_bound`,
`BS23.ColinearSoS.MainS.exponent_le`). The constant of the theorem is
`C = T₀ + CsepS c + 2c + 327000`, `T₀` the time constant; `C ≥ CsepS c` gives the separation
`colLabels_correct` needs. The case `k = 1` needs no separate treatment (`colLabels_correct`
covers it), `u ≠ 0` forces `d ≥ 1`, and `n > 0` follows from the sample size.
-/

@[expose] public section

namespace BS23.ColinearSoS

open Matrix Colinear

namespace MainS

/-! ### Bounds by powers of `B = (d + 1) / wmin` -/

section Numerics

variable {B : ℝ}

/-- **The base of the target is a power of `B`**: `Q = mpBase d t wmin ≤ B^39` for
`t = tCol wmin`. -/
theorem mpBase_le_B {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) {d : ℕ} (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) (hBd : (d : ℝ) + 1 ≤ B) :
    mpBase d (tCol wmin) wmin ≤ B ^ 39 := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hB0 : 0 ≤ B := by linarith
  have h2L := two_pow_logInv_le_B hw hw1 hB2 hBw
  have h10 : (10 : ℝ) ^ 6 ≤ B ^ 20 :=
    calc (10 : ℝ) ^ 6 ≤ 2 ^ 20 := by norm_num
      _ ≤ B ^ 20 := pow_le_pow_left₀ (by norm_num) hB2 20
  have hd6 : ((d : ℝ) + 1) ^ 6 ≤ B ^ 6 := pow_le_pow_left₀ (by positivity) hBd 6
  have ht : ((tCol wmin : ℕ) : ℝ) + 1 ≤ B ^ 12 := by
    have hn : tCol wmin + 1 ≤ 512 * 2 ^ logInv wmin := by
      unfold tCol sCol
      have := Nat.lt_two_pow_self (n := logInv wmin)
      omega
    have hn' : ((tCol wmin : ℕ) : ℝ) + 1 ≤ 512 * 2 ^ logInv wmin := by exact_mod_cast hn
    have h512 : (512 : ℝ) ≤ B ^ 9 :=
      calc (512 : ℝ) = 2 ^ 9 := by norm_num
        _ ≤ B ^ 9 := pow_le_pow_left₀ (by norm_num) hB2 9
    calc ((tCol wmin : ℕ) : ℝ) + 1 ≤ 512 * 2 ^ logInv wmin := hn'
      _ ≤ B ^ 9 * B ^ 3 := mul_le_mul h512 h2L (by positivity) (by positivity)
      _ = B ^ 12 := by ring
  have e : mpBase d (tCol wmin) wmin =
      10 ^ 6 * ((d : ℝ) + 1) ^ 6 * (((tCol wmin : ℕ) : ℝ) + 1) * (1 / (wmin : ℝ)) := by
    unfold mpBase
    ring
  rw [e]
  calc 10 ^ 6 * ((d : ℝ) + 1) ^ 6 * (((tCol wmin : ℕ) : ℝ) + 1) * (1 / (wmin : ℝ)) ≤
      B ^ 20 * B ^ 6 * B ^ 12 * B := by
        have : 0 ≤ 1 / (wmin : ℝ) := (one_div_pos.mpr hw0).le
        gcongr
    _ = B ^ 39 := by ring

/-- **The accuracy target is not too small**:
`σ² ≤ colSoSTarget wmin d σ² · B^(50040 (L + 1))`, `L = logInv wmin`. -/
theorem target_bound {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) {d : ℕ} (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) (hBd : (d : ℝ) + 1 ≤ B) {σ2 : ℝ} (hσ : 0 < σ2) :
    σ2 ≤ colSoSTarget wmin d σ2 * B ^ (50040 * (logInv wmin + 1)) := by
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hw
  have hB1 : 1 ≤ B := by linarith
  have hQ0 : 0 < mpBase d (tCol wmin) wmin := mpBase_pos hw0
  have hQ := mpBase_le_B hw hw1 hB2 hBw hBd
  have hexp : 39 * (5 * tCol wmin + 3) ≤ 50040 * (logInv wmin + 1) := by
    unfold tCol sCol
    omega
  set m := 5 * tCol wmin + 3
  set Q := mpBase d (tCol wmin) wmin
  unfold colSoSTarget
  calc σ2 = σ2 / Q ^ m * Q ^ m := by field_simp
    _ ≤ σ2 / Q ^ m * (B ^ 39) ^ m := by gcongr
    _ = σ2 / Q ^ m * B ^ (39 * m) := by rw [pow_mul]
    _ ≤ σ2 / Q ^ m * B ^ (50040 * (logInv wmin + 1)) := by gcongr

/-- `2 D ≤ B^14` and `D ≤ 520 (L + 1)` for the degree `D = DcolS wmin` of the good event. -/
theorem two_DcolS_le_B {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1) (hB2 : 2 ≤ B)
    (hBw : 1 / (wmin : ℝ) ≤ B) :
    2 * (DcolS wmin : ℝ) ≤ B ^ 14 ∧ DcolS wmin ≤ 520 * (logInv wmin + 1) := by
  refine ⟨?_, by unfold DcolS tCol sCol; omega⟩
  have h := two_pow_logInv_le_B hw hw1 hB2 hBw
  have hL : 2 * DcolS wmin ≤ 2048 * 2 ^ logInv wmin := by
    unfold DcolS tCol sCol
    have := Nat.lt_two_pow_self (n := logInv wmin)
    omega
  have hL' : 2 * (DcolS wmin : ℝ) ≤ 2048 * 2 ^ logInv wmin := by exact_mod_cast hL
  have h2048 : (2048 : ℝ) ≤ B ^ 11 :=
    calc (2048 : ℝ) = 2 ^ 11 := by norm_num
      _ ≤ B ^ 11 := pow_le_pow_left₀ (by norm_num) hB2 11
  calc 2 * (DcolS wmin : ℝ) ≤ 2048 * 2 ^ logInv wmin := hL'
    _ ≤ B ^ 11 * B ^ 3 := mul_le_mul h2048 h (by positivity) (by positivity)
    _ = B ^ 14 := by ring

end Numerics

/-! ### The sample size -/

/-- The exponent `N = 2c + 109000 (L + 1)` is at most `C (x + 1)` when `L + 1 ≤ 3 (x + 1)`,
`x ≥ 0` and `C ≥ 2c + 327000`. -/
theorem exponent_le {c L C : ℕ} {x : ℝ} (hx : 0 ≤ x) (hL : (L : ℝ) + 1 ≤ 3 * (x + 1))
    (hC : 2 * c + 327000 ≤ C) : ((2 * c + 109000 * (L + 1) : ℕ) : ℝ) ≤ C * (x + 1) := by
  have hC' : (2 * (c : ℝ) + 327000) ≤ (C : ℝ) := by exact_mod_cast hC
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have e1 := mul_nonneg hc0 hx
  have e2 := mul_le_mul_of_nonneg_right hC' (by linarith : (0 : ℝ) ≤ x + 1)
  push_cast
  linarith

/-- **The numerics of Theorem 1.2**, abstractly: `D` stands for the degree of the good event,
`T` for the accuracy target with `σ² ≤ T B^E`, `B` for `(d + 1) / wmin`; a sample of size
`n ≥ B^N / σ⁴` with `N ≥ 2c + 17 D + 6 + 2E` suffices. -/
theorem numerics_core (c : ℕ) {k d D E N : ℕ} {w B σ2 T η n : ℝ} (hw0 : 0 < w)
    (hk' : (0 : ℝ) < k) (hkw : (k : ℝ) * w ≤ 1) (hB2 : 2 ≤ B) (hBw : 1 / w ≤ B)
    (hBd : (d : ℝ) + 1 ≤ B) (hσ0 : 0 < σ2) (hσ1 : σ2 ≤ 1) (hTpos : 0 < T)
    (hTB : σ2 ≤ T * B ^ E) (h2D : 2 * (D : ℝ) ≤ B ^ 14) (hDpos : 1 ≤ D)
    (hN : 2 * c + 17 * D + 6 + 2 * E ≤ N) (hη : η = T / (4 * ((d : ℝ) + 1) ^ D))
    (hn : B ^ N / σ2 ^ 2 ≤ n) :
    0 < n ∧ 0 < η ∧ η + η * ((d : ℝ) + 1) ^ D + 1 / n ≤ T ∧
      k / (n * η ^ 2) * (1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D) ≤ (w / k) ^ c := by
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hdD : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ D :=
    one_le_pow₀ (le_add_of_nonneg_left (Nat.cast_nonneg d))
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηT : η * ((d : ℝ) + 1) ^ D = T / 4 := by
    rw [hη]
    field_simp
  have hηB : σ2 ≤ η * B ^ (D + 2 + E) := by
    have h4 : (4 : ℝ) ≤ B ^ 2 :=
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ B ^ 2 := pow_le_pow_left₀ (by norm_num) hB2 2
    have h1 : T ≤ η * B ^ (D + 2) := by
      have hdB : ((d : ℝ) + 1) ^ D ≤ B ^ D := pow_le_pow_left₀ (by positivity) hBd _
      calc T = η * (((d : ℝ) + 1) ^ D * 4) := by rw [← mul_assoc, hηT]; ring
        _ ≤ η * (B ^ D * B ^ 2) := by gcongr
        _ = η * B ^ (D + 2) := by rw [pow_add]
    calc σ2 ≤ T * B ^ E := hTB
      _ ≤ η * B ^ (D + 2) * B ^ E := by gcongr
      _ = η * B ^ (D + 2 + E) := by rw [pow_add B (D + 2), mul_assoc]
  have hσ2' : 0 < σ2 ^ 2 := by positivity
  have hBN : B ^ N ≤ n * σ2 ^ 2 := by
    rwa [div_le_iff₀ hσ2'] at hn
  have hσ2 : σ2 ^ 2 ≤ σ2 := by
    rw [sq]
    exact mul_le_of_le_one_left hσ0.le hσ1
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hn
  refine ⟨hnpos, hηpos, ?_, ?_⟩
  · -- the accuracy
    have hηle : η ≤ T / 4 := by
      rw [← hηT]
      exact le_mul_of_one_le_right hηpos.le hdD
    have h2 : 2 ≤ n * T := by
      have hE : 2 * B ^ E ≤ B ^ N := by
        calc 2 * B ^ E ≤ B * B ^ E := by gcongr
          _ = B ^ (E + 1) := by ring
          _ ≤ B ^ N := pow_le_pow_right₀ hB1 (by omega)
      have h3 : B ^ N ≤ n * T * B ^ E :=
        calc B ^ N ≤ n * σ2 ^ 2 := hBN
          _ ≤ n * σ2 := by gcongr
          _ ≤ n * (T * B ^ E) := by gcongr
          _ = n * T * B ^ E := by ring
      have := hE.trans h3
      exact le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < B ^ E)
    have h3 : 1 / n ≤ T / 2 := by
      rw [div_le_div_iff₀ hnpos (by norm_num)]
      linarith
    rw [hηT]
    linarith
  · -- the failure probability
    have hX : 1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D ≤ B ^ (15 * D + 1) := by
      have h1 : ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D ≤ B ^ (15 * D) :=
        calc ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D ≤ B ^ D * (B ^ 14) ^ D :=
              mul_le_mul (pow_le_pow_left₀ (by positivity) hBd _)
                (pow_le_pow_left₀ (by positivity) h2D _) (by positivity) (by positivity)
          _ = B ^ (15 * D) := by rw [← pow_mul, ← pow_add]; ring_nf
      have h2 : 1 / w ≤ B ^ (15 * D) := hBw.trans (le_self_pow₀ hB1 (by omega))
      calc _ ≤ B ^ (15 * D) + B ^ (15 * D) := add_le_add h2 h1
        _ = 2 * B ^ (15 * D) := by ring
        _ ≤ B * B ^ (15 * D) := by gcongr
        _ = B ^ (15 * D + 1) := by ring
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
        B ^ (2 * c + 2 * (D + 2 + E)) ≤ B ^ N :=
      calc (k : ℝ) * (1 / w + ((d : ℝ) + 1) ^ D * (2 * (D : ℝ)) ^ D) *
            B ^ (2 * c + 2 * (D + 2 + E)) ≤
            B * B ^ (15 * D + 1) * B ^ (2 * c + 2 * (D + 2 + E)) := by gcongr
        _ = B ^ (15 * D + 1 + 1 + (2 * c + 2 * (D + 2 + E))) := by ring
        _ ≤ B ^ N := pow_le_pow_right₀ hB1 (by omega)
    have key2 : B ^ N ≤ (w / k) ^ c * (n * η ^ 2) * B ^ (2 * c + 2 * (D + 2 + E)) :=
      calc B ^ N ≤ n * σ2 ^ 2 := hBN
        _ ≤ n * (η * B ^ (D + 2 + E)) ^ 2 := by gcongr
        _ ≤ ((w / k) ^ c * B ^ (2 * c)) * (n * (η * B ^ (D + 2 + E)) ^ 2) :=
            le_mul_of_one_le_left (by positivity) hP
        _ = (w / k) ^ c * (n * η ^ 2) * B ^ (2 * c + 2 * (D + 2 + E)) := by ring
    exact le_of_mul_le_mul_right (key1.trans key2) (by positivity)

/-- **The numerics of Theorem 1.2.** With `B = (d + 1) / wmin`, `L = logInv wmin`,
`D = DcolS wmin` and the accuracy `η = colSoSTarget wmin d σ² / (4 (d + 1)^D)`, a sample of size
`n ≥ B^(2c + 109000 (L + 1)) / σ⁴` has `n > 0`, `η > 0`,
`η + η (d + 1)^D + 1/n ≤ colSoSTarget wmin d σ²` (the accuracy `colLabels_correct` needs), and
failure probability `k / (n η²) (1/wmin + (d + 1)^D (2D)^D) ≤ (wmin / k)^c` for the good
event. -/
theorem main_numerics (c : ℕ) {k d : ℕ} {wmin : ℚ} (hw : 0 < wmin) (hw1 : wmin ≤ 1)
    (hk : 0 < k) (hkw : (k : ℝ) * wmin ≤ 1) (hd : 1 ≤ d) {σ2 : ℝ} (hσ0 : 0 < σ2)
    (hσ1 : σ2 ≤ 1) {η : ℝ}
    (hη : η = colSoSTarget wmin d σ2 / (4 * ((d : ℝ) + 1) ^ DcolS wmin)) {n : ℝ}
    (hn : (((d : ℝ) + 1) / wmin) ^ (2 * c + 109000 * (logInv wmin + 1)) / σ2 ^ 2 ≤ n) :
    0 < n ∧ 0 < η ∧
      η + η * ((d : ℝ) + 1) ^ DcolS wmin + 1 / n ≤ colSoSTarget wmin d σ2 ∧
      k / (n * η ^ 2) * (1 / (wmin : ℝ) +
        ((d : ℝ) + 1) ^ DcolS wmin * (2 * (DcolS wmin : ℝ)) ^ DcolS wmin) ≤
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
  obtain ⟨h2D, hD⟩ := two_DcolS_le_B hw hw1 hB2 hBw
  have hDpos : 1 ≤ DcolS wmin := by
    unfold DcolS
    omega
  have hN : 2 * c + 17 * DcolS wmin + 6 + 2 * (50040 * (logInv wmin + 1)) ≤
      2 * c + 109000 * (logInv wmin + 1) := by
    omega
  exact numerics_core c hw0 (by exact_mod_cast hk) hkw hB2 hBw hBd hσ0 hσ1
    (colSoSTarget_pos hw d hσ0) (target_bound hw hw1 hB2 hBw hBd hσ0) h2D hDpos hN hη hn

end MainS

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2** of [BS23] (full version: Theorem 6.1): the statement of
`BS23.colinear_clustering`, proved along the paper's sum-of-squares route. The algorithm is
`BS23.ColinearSoS.colinearSoSAlg` (it ignores its coins), and the constant is
`C = T₀ + CsepS c + 2 c + 327000` with `T₀` its time constant. -/
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
  obtain ⟨T₀, hT₀⟩ := colinearSoSAlg_runsInTime
  refine ⟨colinearSoSAlg, T₀ + CsepS c + 2 * c + 327000,
    runsInTime_mono hT₀ (colinearTime_mono (by omega)), ?_⟩
  intro k d M wmin hM hwmin hw hsep base u hu hcol lo hi hlo hlo' hhi n hn r hr
  set C := T₀ + CsepS c + 2 * c + 327000 with hC
  -- the weights
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hwpos : ∀ i, 0 ≤ M.w i := fun i ↦ hw0.le.trans (hw i)
  have hw1 : (wmin : ℝ) ≤ 1 := Colinear.wmin_le_one hM hw0 hw
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
  have hN := MainS.exponent_le hlog0 (logInv_add_one_le hwmin hw1q)
    (show 2 * c + 327000 ≤ C by omega)
  have hnB := sample_bound hB1 hσ0 hσ1 hlo hlohi (by omega) hN hn
  obtain ⟨hnpos, hηpos, hacc, hprob⟩ :=
    MainS.main_numerics c hwmin hw1q hk hkw hd hσ0 hσ1 rfl hnB
  have hnpos' : 0 < n := by exact_mod_cast hnpos
  have hsep' : ∀ a b, a ≠ b →
      (CsepS c : ℝ) * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b) := fun a b hab ↦
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show CsepS c ≤ C by omega)) hlog0).trans
      (hsep a b hab)
  -- the good event
  refine le_trans ?_ (le_successProb_of_goodNoise hM hw0 hw hηpos hnpos' (DcolS wmin) r
    (fun pts ↦ ⟨k, wmin, pts⟩) colinearSoSAlg (colinearTime C)
    (ClustersWithin (((wmin : ℝ) / k) ^ c)) zero_le_one ?_)
  · rw [one_mul]
    linarith
  · intro ω hG
    have hcorr := colLabels_correct c M hM hwmin hw hsep' hu hcol hnpos' r hr ω hG hacc
    refine le_of_eq (coinProb_of_forall fun co ↦ ?_).symm
    rw [colinearSoSAlg_roundedSample k wmin r ω hnpos' co]
    exact hcorr

end BS23.ColinearSoS
