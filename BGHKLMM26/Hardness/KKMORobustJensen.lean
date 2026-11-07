module

public import BGHKLMM26.Hardness.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Jensen's inequality for `√(z log(1/z))`, and the averaging of Lemma bound-2

The real analysis of the robust inverse of soundness (`BGHKLMM26.Hard.kkmo_robust`):

* `φ(z) = √(z log(1/z))` (with `z log(1/z) = negMulLog z`) satisfies Jensen's inequality for
  averages of points of `[0,1]` (`avg_sqrt_negMulLog_le`: `negMulLog` and `√` are concave, `√`
  nondecreasing), is subadditive on `[0,1]` (`sqrt_negMulLog_add_le`), dominates the identity on
  `[0, 1/2]` (`le_sqrt_negMulLog`) and is small near `0` (`exists_sqrt_negMulLog_small`), and
  `negMulLog` is nondecreasing on `[0, 1/3]` (`negMulLog_le_negMulLog`);
* `avg_bound`: the averaging argument of [BGHKLMM26, Lemma bound-2] with Claims c-1 to c-3, for
  abstract numbers attached to the left vertices.
-/

@[expose] public section

namespace BGHKLMM26.Hard.KKMORobust

open Finset Real
open scoped BigOperators

/-! ### The function `z log(1/z)` -/

theorem negMulLog_eq_mul_log_one_div (z : ℝ) : negMulLog z = z * log (1 / z) := by
  rw [negMulLog, one_div, log_inv]; ring

theorem one_lt_log_three : 1 < log 3 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  exact exp_one_lt_d9.trans (by norm_num)

/-- `z log(1/z)` is nondecreasing on `[0, 1/3]`. -/
theorem negMulLog_le_negMulLog {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 3) :
    negMulLog a ≤ negMulLog b := by
  rcases ha.eq_or_lt with rfl | ha'
  · rw [negMulLog_zero]; exact negMulLog_nonneg (by linarith) (by linarith)
  have hb0 : 0 < b := ha'.trans_le hab
  -- `a (log b - log a) ≤ b - a` and `log b ≤ -1`
  have h1 : log b - log a ≤ b / a - 1 := by
    rw [← log_div hb0.ne' ha'.ne']
    exact log_le_sub_one_of_pos (div_pos hb0 ha')
  have h2 : a * (log b - log a) ≤ b - a := by
    have := mul_le_mul_of_nonneg_left h1 ha'.le
    have e : a * (b / a - 1) = b - a := by field_simp
    linarith
  have h3 : log b ≤ -1 := by
    have : log b ≤ log (1 / 3) := log_le_log hb0 hb
    rw [one_div, log_inv] at this
    linarith [one_lt_log_three]
  have h4 : (b - a) * log b ≤ (b - a) * (-1) := mul_le_mul_of_nonneg_left h3 (by linarith)
  unfold negMulLog
  nlinarith

/-- `z log(1/z)` is subadditive. -/
theorem negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    negMulLog (a + b) ≤ negMulLog a + negMulLog b := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → -a * log (a + b) ≤ -a * log a := by
    intro a b ha hb
    rcases ha.eq_or_lt with rfl | ha'
    · simp
    · have : log a ≤ log (a + b) := log_le_log ha' (by linarith)
      nlinarith
  have e : negMulLog (a + b) = -a * log (a + b) + -b * log (b + a) := by
    unfold negMulLog; rw [add_comm b a]; ring
  rw [e]
  unfold negMulLog
  linarith [key a b ha hb, key b a hb ha]

theorem sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [sqrt_le_left (by positivity)]
  have := sq_sqrt ha
  have := sq_sqrt hb
  nlinarith [sqrt_nonneg a, sqrt_nonneg b]

/-- `φ(z) = √(z log(1/z))` is subadditive on `[0,1]`. -/
theorem sqrt_negMulLog_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    √(negMulLog (a + b)) ≤ √(negMulLog a) + √(negMulLog b) := by
  calc √(negMulLog (a + b)) ≤ √(negMulLog a + negMulLog b) :=
        sqrt_le_sqrt (negMulLog_add_le ha hb)
    _ ≤ _ := sqrt_add_le_add_sqrt' (negMulLog_nonneg ha (by linarith))
        (negMulLog_nonneg hb (by linarith))

/-- `η ≤ √(η log(1/η))` for `η ≤ 1/2`. -/
theorem le_sqrt_negMulLog {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1 / 2) : η ≤ √(negMulLog η) := by
  rcases h0.eq_or_lt with rfl | h0'
  · simp
  apply le_sqrt_of_sq_le
  have h := one_sub_inv_le_log_of_pos (inv_pos.mpr h0')
  rw [inv_inv, log_inv] at h
  unfold negMulLog
  nlinarith

/-- `φ` is small near `0`. -/
theorem exists_sqrt_negMulLog_small {C ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 ≤ δ → δ < δ₀ → C * √(negMulLog δ) < ε := by
  have hc : Continuous fun δ : ℝ ↦ C * √(negMulLog δ) := by fun_prop
  obtain ⟨δ₀, hδ₀, h⟩ := Metric.continuous_iff.mp hc 0 ε hε
  refine ⟨δ₀, hδ₀, fun δ hδ hδ₀' ↦ ?_⟩
  have := h δ (by rw [Real.dist_eq, sub_zero, abs_of_nonneg hδ]; exact hδ₀')
  simp only [negMulLog_zero, sqrt_zero, mul_zero, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-- **Jensen** for `φ = √(z log(1/z))` on `[0,1]`, averaged over `m` points. -/
theorem avg_sqrt_negMulLog_le {m : ℕ} (hm : 0 < m) (Z : ℕ → ℝ)
    (hZ : ∀ u ∈ range m, 0 ≤ Z u ∧ Z u ≤ 1) :
    (∑ u ∈ range m, √(negMulLog (Z u))) / m ≤ √(negMulLog ((∑ u ∈ range m, Z u) / m)) := by
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hw0 : ∀ u ∈ range m, (0 : ℝ) ≤ 1 / m := fun _ _ ↦ by positivity
  have hw1 : ∑ u ∈ range m, (1 / m : ℝ) = 1 := by
    rw [sum_const, card_range, nsmul_eq_mul]; field_simp
  have e : ∀ F : ℕ → ℝ, (∑ u ∈ range m, F u) / m = ∑ u ∈ range m, (1 / m : ℝ) • F u := by
    intro F; rw [sum_div]; refine sum_congr rfl fun u _ ↦ ?_; rw [smul_eq_mul]; ring
  have j1 := strictConcaveOn_sqrt.concaveOn.le_map_sum hw0 hw1
    (p := fun u ↦ negMulLog (Z u)) fun u hu ↦
      Set.mem_Ici.mpr (negMulLog_nonneg (hZ u hu).1 (hZ u hu).2)
  have j2 := concaveOn_negMulLog.le_map_sum hw0 hw1 (p := Z) fun u hu ↦
    Set.mem_Ici.mpr (hZ u hu).1
  rw [e, e]
  calc ∑ u ∈ range m, (1 / m : ℝ) • √(negMulLog (Z u))
      ≤ √(∑ u ∈ range m, (1 / m : ℝ) • negMulLog (Z u)) := j1
    _ ≤ _ := sqrt_le_sqrt j2

/-! ### Lemma bound-2, abstractly -/

/-- **The averaging of [BGHKLMM26, Lemma bound-2]** (Claims c-1 to c-3 and Jensen), for numbers
`c u` (the cut values of `g_u`), `c' u` (those of the smoothed `T g_u`) and `d u` (the distances of
`T g_u` to the LTFs) at the left vertices `u < m`, of which at most `ν m` are bad: the good ones cut
at most `s + ξ₂`, and those of them that cut at least `s - η₁` are within `C_M φ(s - c' u) + ξ'` of
an LTF. -/
theorem avg_bound {m : ℕ} (hm : 0 < m) (bad : ℕ → Prop) [DecidablePred bad]
    (c c' d : ℕ → ℝ) {s η η₁ κ ν ξ₂ ξ' CM : ℝ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (hη₁ : 0 < η₁) (hη₁1 : η₁ ≤ 1) (hκ : 0 ≤ κ) (hν : 0 ≤ ν)
    (hξ₂ : 0 ≤ ξ₂) (hξ' : 0 ≤ ξ') (hCM : 0 ≤ CM)
    (hsmall : η + (κ + ν + ξ₂) ≤ 1 / 3)
    (hbad : (((range m).filter bad).card : ℝ) ≤ ν * m)
    (hcut : s - η ≤ (∑ u ∈ range m, c u) / m)
    (hc' : ∀ u ∈ range m, c u - κ ≤ c' u)
    (hc'1 : ∀ u ∈ range m, c' u ≤ 1)
    (hd1 : ∀ u ∈ range m, d u ≤ 1)
    (hgood : ∀ u ∈ range m, ¬ bad u → c' u ≤ s + ξ₂)
    (hmis : ∀ u ∈ range m, ¬ bad u → s - η₁ ≤ c' u →
      d u ≤ CM * √(negMulLog (max 0 (s - c' u))) + ξ') :
    (∑ u ∈ range m, d u) / m ≤
      ν + (η + (κ + ν + ξ₂)) / η₁ + CM * (√(negMulLog η) + √(negMulLog (κ + ν + ξ₂))) + ξ' := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = κ + ν + ξ₂ := ⟨_, rfl⟩
  rw [← hδ] at hsmall ⊢
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  -- indicators
  set G2 : ℕ → Prop := fun u ↦ ¬ bad u ∧ c' u < s - η₁ with hG2
  set ib : ℕ → ℝ := fun u ↦ if bad u then 1 else 0 with hib
  set ig : ℕ → ℝ := fun u ↦ if G2 u then 1 else 0 with hig
  set Z : ℕ → ℝ := fun u ↦ if ¬ bad u ∧ s - η₁ ≤ c' u then max 0 (s - c' u) else 0 with hZ
  obtain ⟨nB, hnB⟩ : ∃ x : ℝ, x = (((range m).filter bad).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨nG, hnG⟩ : ∃ x : ℝ, x = (((range m).filter G2).card : ℝ) := ⟨_, rfl⟩
  have hsib : ∑ u ∈ range m, ib u = nB := by
    rw [hnB, hib]; simp only [Finset.sum_boole]
  have hsig : ∑ u ∈ range m, ig u = nG := by
    rw [hnG, hig]; simp only [Finset.sum_boole]
  rw [← hnB] at hbad
  have hib0 : ∀ u, 0 ≤ ib u := fun u ↦ by simp only [hib]; split_ifs <;> norm_num
  have hig0 : ∀ u, 0 ≤ ig u := fun u ↦ by simp only [hig]; split_ifs <;> norm_num
  -- the cut values of the smoothed tables
  have hsc : (s - η) * m ≤ ∑ u ∈ range m, c u := (le_div_iff₀ hm').mp hcut
  have hsc' : ∑ u ∈ range m, (c u - κ) ≤ ∑ u ∈ range m, c' u := sum_le_sum hc'
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] at hsc'
  -- Claim c-2: few good vertices cut little
  have hpt1 : ∀ u ∈ range m, c' u ≤ s + ξ₂ - η₁ * ig u + ib u := by
    intro u hu
    by_cases hb : bad u
    · have : ib u = 1 := by simp [hib, hb]
      have h2 : ig u = 0 := by simp [hig, hG2, hb]
      rw [this, h2]; linarith [hc'1 u hu]
    · have h1 : ib u = 0 := by simp [hib, hb]
      by_cases hl : c' u < s - η₁
      · have h2 : ig u = 1 := by simp [hig, hG2, hb, hl]
        rw [h1, h2]; linarith
      · have h2 : ig u = 0 := by simp [hig, hG2, hl]
        rw [h1, h2]; linarith [hgood u hu hb]
  have hs1 : ∑ u ∈ range m, c' u ≤ (s + ξ₂) * m - η₁ * nG + nB := by
    have := sum_le_sum hpt1
    rw [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
      hsig, hsib] at this
    linarith
  have hnG' : η₁ * nG ≤ (η + δ) * m := by
    rw [hδ]; nlinarith
  -- Claim c-3: the deficits of the remaining good vertices
  have hZ01 : ∀ u ∈ range m, 0 ≤ Z u ∧ Z u ≤ 1 := by
    intro u hu
    simp only [hZ]
    split_ifs with h
    · exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith [h.2])⟩
    · exact ⟨le_refl _, by norm_num⟩
  have hpt2 : ∀ u ∈ range m, Z u ≤ s - c' u + ξ₂ + ib u := by
    intro u hu
    by_cases hb : bad u
    · have : ib u = 1 := by simp [hib, hb]
      have h2 : Z u = 0 := by simp [hZ, hb]
      rw [this, h2]; linarith [hc'1 u hu]
    · have h1 : ib u = 0 := by simp [hib, hb]
      rw [h1]
      by_cases hl : s - η₁ ≤ c' u
      · have h2 : Z u = max 0 (s - c' u) := ite_eq_left ⟨hb, hl⟩
        rw [h2]
        exact max_le (by linarith [hgood u hu hb]) (by linarith)
      · have h2 : Z u = 0 := ite_eq_right fun h ↦ hl h.2
        rw [h2]; linarith
  have hsZ : ∑ u ∈ range m, Z u ≤ (η + δ) * m := by
    have := sum_le_sum hpt2
    rw [sum_add_distrib, sum_add_distrib, sum_sub_distrib, sum_const, sum_const, card_range,
      nsmul_eq_mul, nsmul_eq_mul, hsib] at this
    rw [hδ]; nlinarith
  -- the distances
  have hpt3 : ∀ u ∈ range m, d u ≤ ib u + ig u + CM * √(negMulLog (Z u)) + ξ' := by
    intro u hu
    have hφ : 0 ≤ CM * √(negMulLog (Z u)) := mul_nonneg hCM (sqrt_nonneg _)
    by_cases hb : bad u
    · have : ib u = 1 := by simp [hib, hb]
      rw [this]; linarith [hd1 u hu, hig0 u]
    · by_cases hl : s - η₁ ≤ c' u
      · have h2 : Z u = max 0 (s - c' u) := ite_eq_left ⟨hb, hl⟩
        rw [h2]; linarith [hmis u hu hb hl, hib0 u, hig0 u]
      · have h2 : ig u = 1 := by simp [hig, hG2, hb, not_le.mp hl]
        rw [h2]; linarith [hd1 u hu, hib0 u]
  have hsd : ∑ u ∈ range m, d u ≤ nB + nG + CM * ∑ u ∈ range m, √(negMulLog (Z u)) + ξ' * m := by
    have := sum_le_sum hpt3
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
      ← mul_sum, hsib, hsig] at this
    linarith
  -- Jensen
  have hJ := avg_sqrt_negMulLog_le hm Z hZ01
  have havg0 : 0 ≤ (∑ u ∈ range m, Z u) / m :=
    div_nonneg (sum_nonneg fun u hu ↦ (hZ01 u hu).1) hm'.le
  have havg : (∑ u ∈ range m, Z u) / m ≤ η + δ := (div_le_iff₀ hm').mpr hsZ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hmono := negMulLog_le_negMulLog havg0 havg hsmall
  have hsub := sqrt_negMulLog_add_le hη hδ0 (by linarith)
  have hJ' : (∑ u ∈ range m, √(negMulLog (Z u))) / m ≤ √(negMulLog η) + √(negMulLog δ) :=
    hJ.trans ((sqrt_le_sqrt hmono).trans hsub)
  have hJ'' : ∑ u ∈ range m, √(negMulLog (Z u)) ≤ (√(negMulLog η) + √(negMulLog δ)) * m :=
    (div_le_iff₀ hm').mp hJ'
  have hnG'' : nG ≤ (η + δ) / η₁ * m := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hη₁]; linarith
  rw [div_le_iff₀ hm']
  have hC := mul_le_mul_of_nonneg_left hJ'' hCM
  nlinarith

end BGHKLMM26.Hard.KKMORobust
