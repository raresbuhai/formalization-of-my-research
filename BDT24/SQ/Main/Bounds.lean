module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real inequalities for Theorem C.6

Facts about real numbers used in `BDT24/SQ/Main.lean`:

* `BDT24.SQ.MS.corrGap_quintic`: for `0 ≤ θ ≤ (k+1)/(k+2)` and `0 ≤ t ≤ 1`, the gap
  `g = (1 - θ² t)^(-1/2) - 1` satisfies `0 ≤ g ≤ 2t + (k + 2) (4t)^5`.
* `BDT24.SQ.MS.rootSixteen_le`: `(q² B^p)^(1/p) ≤ 16 B` when `q ≤ 2^(p+1)`.
* `BDT24.SQ.MS.sixteenB_le_inv`: the bound `16 B ≤ 1/n` on the parameters of Theorem C.6.
-/

@[expose] public section

namespace BDT24.SQ.MS

/-- **The gap of the correlation**: for `0 ≤ θ ≤ (k+1)/(k+2)` and `0 ≤ t ≤ 1`,
`0 ≤ (1 - θ² t)^(-1/2) - 1 ≤ 2t + (k + 2) (4t)^5`. Below `t = 1/4` the gap is at most `2t`, and
it is always at most `k + 1`, since `1 - θ² t ≥ 1 - θ ≥ 1/(k+2)`. -/
theorem corrGap_quintic (k : ℕ) {θ t : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ ((k : ℝ) + 1) / ((k : ℝ) + 2))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 1 / √(1 - θ ^ 2 * t) - 1 ∧
      1 / √(1 - θ ^ 2 * t) - 1 ≤ 2 * t + ((k : ℝ) + 2) * (4 * t) ^ 5 := by
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hθ' : 1 / ((k : ℝ) + 2) ≤ 1 - θ := by
    have : ((k : ℝ) + 1) / ((k : ℝ) + 2) = 1 - 1 / ((k : ℝ) + 2) := by
      field_simp
      ring
    linarith
  have hkinv : 0 < 1 / ((k : ℝ) + 2) := by positivity
  have hθ1' : θ ≤ 1 := by linarith
  have hθsq : θ ^ 2 ≤ θ := by nlinarith
  have hs0 : 0 ≤ θ ^ 2 * t := by positivity
  have hst : θ ^ 2 * t ≤ t := by nlinarith
  have hsθ : θ ^ 2 * t ≤ θ := by nlinarith
  have hpos : 0 < 1 - θ ^ 2 * t := by linarith
  have hsq : 0 < √(1 - θ ^ 2 * t) := Real.sqrt_pos.mpr hpos
  have hsq1 : √(1 - θ ^ 2 * t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  refine ⟨by linarith [one_le_one_div hsq hsq1], ?_⟩
  rcases le_or_gt t (1 / 4) with ht | ht
  · -- small overlaps: `(1 - s)^(-1/2) ≤ 1 + 2s`
    have hs4 : θ ^ 2 * t ≤ 1 / 4 := by linarith
    have hle : 1 / (1 + 2 * (θ ^ 2 * t)) ≤ √(1 - θ ^ 2 * t) := by
      refine (Real.le_sqrt (by positivity) hpos.le).mpr ?_
      rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
      have key : 0 ≤ (θ ^ 2 * t) * (3 - 4 * (θ ^ 2 * t) ^ 2) := mul_nonneg hs0 (by nlinarith)
      nlinarith [key]
    have h := (one_div_le hsq (by positivity)).mpr hle
    have h5 : 0 ≤ ((k : ℝ) + 2) * (4 * t) ^ 5 := by positivity
    linarith
  · -- large overlaps: `(1 - s)^(-1/2) ≤ k + 2 ≤ (k + 2) (4t)^5`
    have hle : 1 / ((k : ℝ) + 2) ≤ √(1 - θ ^ 2 * t) := by
      refine (Real.le_sqrt hkinv.le hpos.le).mpr ?_
      have : (1 / ((k : ℝ) + 2)) ^ 2 ≤ 1 / ((k : ℝ) + 2) := by
        rw [sq]
        exact mul_le_of_le_one_left hkinv.le
          ((div_le_one hk2).mpr (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]))
      linarith
    have h := (one_div_le hsq hk2).mpr hle
    have h4 : 1 ≤ (4 * t) ^ 5 := one_le_pow₀ (by linarith)
    have h5 : (k : ℝ) + 2 ≤ ((k : ℝ) + 2) * (4 * t) ^ 5 := le_mul_of_one_le_right hk2.le h4
    linarith

/-- **The `p`-th root in Hölder's bound**: `(q² B^p)^(1/p) ≤ 16 B` when `0 ≤ q ≤ 2^(p+1)`,
`0 ≤ B` and `p ≥ 1`, since then `q² ≤ 2^(2p+2) ≤ 16^p`. -/
theorem rootSixteen_le {p : ℕ} (hp : 1 ≤ p) {q B : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 2 ^ (p + 1))
    (hB : 0 ≤ B) : (q ^ 2 * B ^ p) ^ (1 / (p : ℝ)) ≤ 16 * B := by
  have hq2 : q ^ 2 ≤ 16 ^ p := by
    calc q ^ 2 ≤ (2 ^ (p + 1)) ^ 2 := pow_le_pow_left₀ hq0 hq 2
      _ = 2 ^ (2 * p + 2) := by ring
      _ ≤ 2 ^ (4 * p) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 16 ^ p := by rw [pow_mul]; norm_num
  have hle : q ^ 2 * B ^ p ≤ (16 * B) ^ p := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hq2 (by positivity)
  calc (q ^ 2 * B ^ p) ^ (1 / (p : ℝ)) ≤ ((16 * B) ^ p) ^ (1 / (p : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hle (by positivity)
    _ = 16 * B := by rw [one_div, Real.pow_rpow_inv_natCast (by positivity) (by omega)]

/-- **The bound on the parameters of Theorem C.6**: with `X = C p (1/d + p/k²)` and
`Y = C (5p) (1/d + 5p/k²)`, the bound `B = 4X + 2 (k + 2) 4^5 Y^5` of the moments satisfies
`16 B ≤ 1/n`. Here `w = k^δ ≤ p ≤ 2w`, `n w ≤ η d` and `n w² ≤ η k²`, so `n p/d ≤ 2η`,
`n p²/k² ≤ 4η` and `n ≤ k²`; with `Y ≤ 110 C w/k` and `w^5 ≤ k`, the second term of `16 n B` is
at most `98304 (110 C)^5 / k`. -/
theorem sixteenB_le_inv {C η k d n w p : ℝ} (hC : 0 < C) (hη1 : η ≤ 1)
    (hηC : 768 * C * η ≤ 1) (hk : 1 ≤ k) (hkd : k ≤ d) (hn : 0 < n) (hw1 : 1 ≤ w) (hwk : w ≤ k)
    (hw5 : w ^ 5 ≤ k) (hp0 : 0 ≤ p) (hp2 : p ≤ 2 * w) (hnd : n * w ≤ η * d)
    (hnk : n * w ^ 2 ≤ η * k ^ 2) (hkK : 2 * (98304 * (110 * C) ^ 5) ≤ k) :
    16 * (4 * (C * p * (1 / d + p / k ^ 2)) +
      2 * (k + 2) * 4 ^ 5 * (C * (5 * p) * (1 / d + 5 * p / k ^ 2)) ^ 5) ≤ 1 / n := by
  have hk0 : 0 < k := by linarith
  have hd : 0 < d := by linarith
  have hk2 : 0 < k ^ 2 := by positivity
  -- the first term
  have h1 : n * p / d ≤ 2 * η := by
    rw [div_le_iff₀ hd]
    nlinarith
  have h2 : n * p ^ 2 / k ^ 2 ≤ 4 * η := by
    rw [div_le_iff₀ hk2]
    have : p ^ 2 ≤ 4 * w ^ 2 := by nlinarith
    nlinarith
  have hX : n * (C * p * (1 / d + p / k ^ 2)) ≤ 6 * C * η := by
    have : n * (C * p * (1 / d + p / k ^ 2)) = C * (n * p / d + n * p ^ 2 / k ^ 2) := by ring
    rw [this]
    nlinarith
  -- the second term
  have hY0 : 0 ≤ C * (5 * p) * (1 / d + 5 * p / k ^ 2) := by positivity
  have hY : C * (5 * p) * (1 / d + 5 * p / k ^ 2) ≤ 110 * C * w / k := by
    have hd1 : 1 / d ≤ 1 / k := one_div_le_one_div_of_le hk0 hkd
    have hpk : 5 * p / k ^ 2 ≤ 10 / k := by
      rw [div_le_div_iff₀ hk2 hk0]
      nlinarith
    have hsum : 1 / d + 5 * p / k ^ 2 ≤ 11 / k := by
      have : 1 / k + 10 / k = 11 / k := by ring
      linarith
    calc C * (5 * p) * (1 / d + 5 * p / k ^ 2) ≤ (10 * C * w) * (11 / k) :=
          mul_le_mul (by nlinarith) hsum (by positivity) (by positivity)
      _ = 110 * C * w / k := by ring
  have hY5 : (C * (5 * p) * (1 / d + 5 * p / k ^ 2)) ^ 5 ≤ (110 * C) ^ 5 / k ^ 4 := by
    calc (C * (5 * p) * (1 / d + 5 * p / k ^ 2)) ^ 5 ≤ (110 * C * w / k) ^ 5 :=
          pow_le_pow_left₀ hY0 hY 5
      _ = (110 * C) ^ 5 * w ^ 5 / k ^ 5 := by ring
      _ ≤ (110 * C) ^ 5 * k / k ^ 5 := by gcongr
      _ = (110 * C) ^ 5 / k ^ 4 := by field_simp
  have hn2 : n ≤ k ^ 2 := by
    have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw1
    have : n ≤ n * w ^ 2 := le_mul_of_one_le_right hn.le hw2
    have : η * k ^ 2 ≤ k ^ 2 := mul_le_of_le_one_left hk2.le hη1
    linarith
  set Y := C * (5 * p) * (1 / d + 5 * p / k ^ 2)
  have hnY : n * ((k + 2) * Y ^ 5) ≤ 3 * (110 * C) ^ 5 / k := by
    calc n * ((k + 2) * Y ^ 5) ≤ k ^ 2 * (3 * k * ((110 * C) ^ 5 / k ^ 4)) :=
          mul_le_mul hn2 (mul_le_mul (by linarith) hY5 (by positivity) (by positivity))
            (by positivity) (by positivity)
      _ = 3 * (110 * C) ^ 5 / k := by field_simp
  have hK : 98304 * (110 * C) ^ 5 / k ≤ 1 / 2 := by
    rw [div_le_iff₀ hk0]
    linarith
  rw [le_div_iff₀ hn]
  have : 16 * (4 * (C * p * (1 / d + p / k ^ 2)) + 2 * (k + 2) * 4 ^ 5 * Y ^ 5) * n =
      64 * (n * (C * p * (1 / d + p / k ^ 2))) + 32768 * (n * ((k + 2) * Y ^ 5)) := by ring
  rw [this]
  have : 32768 * (3 * (110 * C) ^ 5 / k) = 98304 * (110 * C) ^ 5 / k := by ring
  nlinarith

end BDT24.SQ.MS
