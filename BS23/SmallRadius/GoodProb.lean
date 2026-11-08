module

public import BS23.SmallRadius.Params
public import BS23.Common.GoodProb

/-!
# The graded good event of the small-radius analysis

The analysis of the algorithm of [BS23, Theorem 1.3] uses the good event `BS23.GoodNoise` of
every degree `r ≤ 2t` at once, with the tolerance `τ_r = w 256^{-t} (d+1)^{-2t} √(r^r)`
(`BS23.SmallRadius.τ`) growing with the degree: this is `BS23.SmallRadius.GoodGraded`.

* `BS23.SmallRadius.measurableSet_goodGraded`: the event is measurable (a finite intersection of
  good events).
* `BS23.SmallRadius.prob_not_goodGraded_le`: for a valid mixture with weights at least
  `0 < w ≤ 1/2` and `t ≥ 1`, it fails with probability at most `((d+1)/w)^(26t+4) / n`.

**Proof of the bound.** By `BS23.sampleLaw_not_goodNoise_le`, the good event of degree `r` fails
with probability at most `k / (n τ_r²) · (1/w + (d+1)^r (2r)^r)`. With `k ≤ 1/w`,
`τ_r² = w² 2^{-16t} (d+1)^{-4t} r^r`, `r^r ≥ 1`, `(2r)^r = 2^r r^r` and `r ≤ 2t`, this is at most
`w^{-4} (d+1)^{6t} 2^{18t} / n ≤ ((d+1)/w)^(24t+4) / n` (`BS23.SmallRadius.not_goodNoise_term_le`).
A union bound over the `2t + 1 ≤ 2^{2t}` degrees gives the claim.
-/

@[expose] public section

namespace BS23.SmallRadius

open MeasureTheory

variable {k d : ℕ}

/-- **The graded good event**: the good events `GoodNoise M.w τ_r r` of all degrees `r ≤ 2t`, for
the labels and the standardized noises of the sample. -/
def GoodGraded (M : Mixture k d) (w : ℝ) (t : ℕ) {n : ℕ}
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ r ≤ 2 * t, GoodNoise M.w (τ w d t r) r (labels ω) (stdNoise M ω)

theorem setOf_goodGraded (M : Mixture k d) (n : ℕ) (w : ℝ) (t : ℕ) :
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d) | GoodGraded M w t ω} =
      ⋂ r ∈ Finset.range (2 * t + 1),
        {ω | GoodNoise M.w (τ w d t r) r (labels ω) (stdNoise M ω)} := by
  ext ω
  simp only [GoodGraded, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range,
    Nat.lt_add_one_iff]

theorem setOf_not_goodGraded (M : Mixture k d) (n : ℕ) (w : ℝ) (t : ℕ) :
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d) | ¬ GoodGraded M w t ω} =
      ⋃ r ∈ Finset.range (2 * t + 1),
        {ω | ¬ GoodNoise M.w (τ w d t r) r (labels ω) (stdNoise M ω)} := by
  ext ω
  simp only [GoodGraded, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range,
    Nat.lt_add_one_iff, not_forall, exists_prop]

/-- **The graded good event is measurable.** -/
theorem measurableSet_goodGraded (M : Mixture k d) (n : ℕ) (w : ℝ) (t : ℕ) :
    MeasurableSet {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d) | GoodGraded M w t ω} := by
  rw [setOf_goodGraded]
  exact Finset.measurableSet_biInter _ fun r _ ↦ measurableSet_goodNoise_sample M n _ r

/-- The failure bound of the good event of one degree `r ≤ 2t`:
`k / (n τ_r²) · (1/w + (d+1)^r (2r)^r) ≤ ((d+1)/w)^(24t+4) / n`. -/
theorem not_goodNoise_term_le {w : ℝ} (hw : 0 < w) (hw2 : w ≤ 1 / 2) (hkw : (k : ℝ) * w ≤ 1)
    {t r : ℕ} (ht : 1 ≤ t) (hr : r ≤ 2 * t) {n : ℝ} (hn : 0 < n) :
    k / (n * τ w d t r ^ 2) * (1 / w + ((d : ℝ) + 1) ^ r * (2 * r) ^ r) ≤
      (((d : ℝ) + 1) / w) ^ (24 * t + 4) / n := by
  set A : ℝ := (d : ℝ) + 1 with hA
  set iw : ℝ := 1 / w with hiw
  set P : ℝ := (r : ℝ) ^ r with hP
  have hA1 : 1 ≤ A := by rw [hA]; linarith [d.cast_nonneg (α := ℝ)]
  have hiw2 : 2 ≤ iw := by rw [hiw, le_div_iff₀ hw]; linarith
  have hP1 : 1 ≤ P := one_le_pow_self r
  have hk : (k : ℝ) ≤ iw := by rw [hiw, le_div_iff₀ hw]; exact hkw
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hτ := τ_pos hw d t r
  have hτ2 : 0 < τ w d t r ^ 2 := by positivity
  -- the bracket
  set Y : ℝ := A ^ (2 * t) * 2 ^ (2 * t) with hY
  have hY4 : 4 ≤ Y := by
    have h1 : 1 ≤ A ^ (2 * t) := one_le_pow₀ hA1
    have h2 : (4 : ℝ) ≤ 2 ^ (2 * t) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * t) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [hY]
    nlinarith
  have hQ : 1 / w + A ^ r * (2 * r) ^ r ≤ P * (iw + Y) := by
    have h1 : A ^ r ≤ A ^ (2 * t) := pow_le_pow_right₀ hA1 hr
    have h2 : (2 : ℝ) ^ r ≤ 2 ^ (2 * t) := pow_le_pow_right₀ (by norm_num) hr
    have h3 : A ^ r * (2 * r) ^ r = A ^ r * 2 ^ r * P := by rw [hP, mul_pow]; ring
    have h4 : A ^ r * 2 ^ r ≤ Y := mul_le_mul h1 h2 (by positivity) (by positivity)
    have hP0 : 0 ≤ P := by linarith
    rw [h3, ← hiw]
    nlinarith
  have hkQ : (k : ℝ) * (1 / w + A ^ r * (2 * r) ^ r) ≤ P * iw ^ 2 * Y := by
    have h1 : iw * (iw + Y) ≤ iw ^ 2 * Y := by
      have h0 : 1 ≤ (iw - 1) * (Y - 1) := by nlinarith
      have e : iw ^ 2 * Y - iw * (iw + Y) = iw * ((iw - 1) * (Y - 1) - 1) := by ring
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ iw) (by linarith : 0 ≤ (iw - 1) * (Y - 1) - 1)]
    have hQ0 : 0 ≤ 1 / w + A ^ r * (2 * r) ^ r := by positivity
    calc (k : ℝ) * (1 / w + A ^ r * (2 * r) ^ r) ≤ iw * (P * (iw + Y)) :=
          mul_le_mul hk hQ hQ0 (by linarith)
      _ = P * (iw * (iw + Y)) := by ring
      _ ≤ P * (iw ^ 2 * Y) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = P * iw ^ 2 * Y := by ring
  -- the tolerance
  have hτsq : τ w d t r ^ 2 = w ^ 2 * P / (2 ^ (16 * t) * A ^ (4 * t)) := by
    rw [τ_sq, hP, hA]
    have : ((1 : ℝ) / 256) ^ (2 * t) = 1 / 2 ^ (16 * t) := by
      rw [div_pow, one_pow, show (256 : ℝ) = 2 ^ 8 by norm_num, ← pow_mul]
      ring_nf
    rw [this]
    field_simp
  have hmain : (k : ℝ) * (1 / w + A ^ r * (2 * r) ^ r) / τ w d t r ^ 2 ≤
      iw ^ 4 * A ^ (6 * t) * 2 ^ (18 * t) := by
    rw [div_le_iff₀ hτ2, hτsq]
    have e : iw ^ 4 * A ^ (6 * t) * 2 ^ (18 * t) * (w ^ 2 * P / (2 ^ (16 * t) * A ^ (4 * t))) =
        P * iw ^ 2 * Y := by
      rw [hY, hiw]
      have hA0 : A ≠ 0 := by positivity
      field_simp
      ring
    rw [e]
    exact hkQ
  have hfin : iw ^ 4 * A ^ (6 * t) * 2 ^ (18 * t) ≤ (A / w) ^ (24 * t + 4) := by
    have e : A / w = A * iw := by rw [hiw]; ring
    rw [e, mul_pow]
    have h1 : A ^ (6 * t) ≤ A ^ (24 * t + 4) := pow_le_pow_right₀ hA1 (by omega)
    have h2 : (2 : ℝ) ^ (18 * t) ≤ iw ^ (18 * t) := pow_le_pow_left₀ (by norm_num) hiw2 _
    have h3 : iw ^ 4 * iw ^ (18 * t) ≤ iw ^ (24 * t + 4) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    calc iw ^ 4 * A ^ (6 * t) * 2 ^ (18 * t) ≤ iw ^ 4 * A ^ (24 * t + 4) * iw ^ (18 * t) := by
          gcongr
      _ = A ^ (24 * t + 4) * (iw ^ 4 * iw ^ (18 * t)) := by ring
      _ ≤ A ^ (24 * t + 4) * iw ^ (24 * t + 4) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  have e : k / (n * τ w d t r ^ 2) * (1 / w + A ^ r * (2 * r) ^ r) =
      ((k : ℝ) * (1 / w + A ^ r * (2 * r) ^ r) / τ w d t r ^ 2) / n := by
    field_simp
  rw [e]
  exact div_le_div_of_nonneg_right (hmain.trans hfin) hn.le

/-- **The graded good event has high probability.** For a valid mixture with weights at least
`0 < w ≤ 1/2`, `n > 0` points and `t ≥ 1`, the graded good event fails with probability at most
`((d+1)/w)^(26t+4) / n`. -/
theorem prob_not_goodGraded_le {M : Mixture k d} (hM : M.Valid) {w : ℝ} (hw : 0 < w)
    (hw2 : w ≤ 1 / 2) (hwc : ∀ c, w ≤ M.w c) {n : ℕ} (hn : 0 < n) {t : ℕ} (ht : 1 ≤ t) :
    (M.sampleLaw n {ω | ¬ GoodGraded M w t ω}).toReal ≤ (((d : ℝ) + 1) / w) ^ (26 * t + 4) / n := by
  have hkw : (k : ℝ) * w ≤ 1 := by
    calc (k : ℝ) * w = ∑ _c : Fin k, w := by simp
      _ ≤ ∑ c, M.w c := Finset.sum_le_sum fun c _ ↦ hwc c
      _ = 1 := hM.sum_w
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := ((d : ℝ) + 1) / w with hx
  have hx2 : 2 ≤ x := by
    rw [hx, le_div_iff₀ hw]
    nlinarith [d.cast_nonneg (α := ℝ)]
  rw [← measureReal_def, setOf_not_goodGraded]
  calc (M.sampleLaw n).real (⋃ r ∈ Finset.range (2 * t + 1),
        {ω | ¬ GoodNoise M.w (τ w d t r) r (labels ω) (stdNoise M ω)})
      ≤ ∑ r ∈ Finset.range (2 * t + 1), (M.sampleLaw n).real
          {ω | ¬ GoodNoise M.w (τ w d t r) r (labels ω) (stdNoise M ω)} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ Finset.range (2 * t + 1), x ^ (24 * t + 4) / n := by
        refine Finset.sum_le_sum fun r hr ↦ ?_
        rw [Finset.mem_range, Nat.lt_add_one_iff] at hr
        rw [measureReal_def]
        exact (sampleLaw_not_goodNoise_le hM hw hwc (τ_pos hw d t r) hn r).trans
          (not_goodNoise_term_le hw hw2 hkw ht hr hn')
    _ = (2 * t + 1 : ℕ) * (x ^ (24 * t + 4) / n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ x ^ (2 * t) * (x ^ (24 * t + 4) / n) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have h1 : 2 * t + 1 ≤ 2 ^ (2 * t) := Nat.lt_two_pow_self
        have h2 : ((2 * t + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * t) := by exact_mod_cast h1
        exact h2.trans (pow_le_pow_left₀ (by norm_num) hx2 _)
    _ = x ^ (26 * t + 4) / n := by
        rw [← mul_div_assoc, ← pow_add]
        ring_nf

end BS23.SmallRadius
