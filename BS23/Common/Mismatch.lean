module

public import BS23.Common.HermiteFacts
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The one-dimensional moment mismatch

A discrete distribution on the line whose atoms all have weight at least `w_min` cannot have
Hermite moments close to those of a Gaussian up to a degree of order `log (1 / w_min)`:
`BS23.exists_hermite_mismatch` gives, for `V` taking the value `V c` with probability `w c` and
`s² = E V²` (or any `q ∈ (0, 1]` in place of `s²`, `BS23.exists_hermite_mismatch_of_le_one`), a
degree `1 ≤ m ≤ 4t` with `|E He_m(V; s²)| ≥ s^{4t} / (4 · 16^t)`, as soon as `t ≥ 10` and
`t ≥ 10 ln (1 / w_min)`. No assumption on the mean of `V` is needed.

Proof. Write `h_j = E He_j(V; q)`. By the inversion formula `x^r = ∑_i c_{r,i} q^i He_{r-2i}(x; q)`,
`E V^{2T} = (2T-1)‼ q^T + ∑_{i < T} c_{2T,i} q^i h_{2T-2i}`, so if `|h_j| < η` for all
`1 ≤ j ≤ 4t` then `|E V^{2T} - (2T-1)‼ q^T| ≤ η 4^T (2T-1)‼` for `T ≤ 2t`
(`BS23.abs_moment_sub_le`). With `η = q^{2t} / (4 · 16^t)` the moments of order `2t` and `4t` are
within a factor `1 ± 1/2` of the Gaussian ones. With `B = max_c V_c^{2t}`, this gives
`w_min B ≤ E V^{2t} ≤ (3/2) (2t-1)‼ q^t` and `(1/2) (4t-1)‼ q^{2t} ≤ E V^{4t} ≤ B²`, so
`w_min² (4t-1)‼ ≤ (9/2) ((2t-1)‼)²`. But `(4t-1)‼ ≥ 2^t ((2t-1)‼)²`
(`BS23.two_pow_mul_doubleFactorial_sq_le`), and `w_min² 2^t > 9/2` for `t ≥ 10 ln (1 / w_min)`,
`t ≥ 10`.
-/

@[expose] public section

namespace BS23

open Finset
open scoped Nat

/-! ### Odd double factorials -/

theorem doubleFactorial_two_mul_succ_sub_one (n : ℕ) :
    (2 * (n + 1) - 1)‼ = (2 * n + 1) * (2 * n - 1)‼ := by
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  exact Nat.doubleFactorial_add_one (2 * n)

theorem doubleFactorial_two_mul_sub_one_mono {i j : ℕ} (h : i ≤ j) :
    (2 * i - 1)‼ ≤ (2 * j - 1)‼ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [doubleFactorial_two_mul_succ_sub_one]
    exact ih.trans (Nat.le_mul_of_pos_left _ (by omega))

/-- `2^j (2j-1)‼ (2t-1)‼ ≤ (2(t+j)-1)‼` for `j ≤ t`: each of the factors `2t+1, …, 2t+2j-1` is
at least twice the corresponding factor `1, …, 2j-1`. -/
theorem two_pow_mul_doubleFactorial_le {t j : ℕ} (h : j ≤ t) :
    2 ^ j * (2 * j - 1)‼ * (2 * t - 1)‼ ≤ (2 * (t + j) - 1)‼ := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc 2 ^ (j + 1) * (2 * (j + 1) - 1)‼ * (2 * t - 1)‼
        = 2 * (2 * j + 1) * (2 ^ j * (2 * j - 1)‼ * (2 * t - 1)‼) := by
          rw [doubleFactorial_two_mul_succ_sub_one, pow_succ]; ring
      _ ≤ 2 * (2 * j + 1) * (2 * (t + j) - 1)‼ := Nat.mul_le_mul_left _ (ih (by omega))
      _ ≤ (2 * (t + j) + 1) * (2 * (t + j) - 1)‼ := Nat.mul_le_mul_right _ (by omega)
      _ = (2 * (t + (j + 1)) - 1)‼ := by
          rw [show t + (j + 1) = t + j + 1 by ring, doubleFactorial_two_mul_succ_sub_one]

/-- `2^t ((2t-1)‼)² ≤ (4t-1)‼`. -/
theorem two_pow_mul_doubleFactorial_sq_le (t : ℕ) :
    2 ^ t * ((2 * t - 1)‼) ^ 2 ≤ (2 * (2 * t) - 1)‼ := by
  have := two_pow_mul_doubleFactorial_le (le_refl t)
  rw [show t + t = 2 * t by ring] at this
  calc 2 ^ t * ((2 * t - 1)‼) ^ 2 = 2 ^ t * (2 * t - 1)‼ * (2 * t - 1)‼ := by ring
    _ ≤ _ := this

/-- `∑_{i < T} c_{2T,i} ≤ 4^T (2T-1)‼`. -/
theorem sum_hermCoeff_le (T : ℕ) :
    ∑ i ∈ range T, hermCoeff (2 * T) i ≤ 4 ^ T * (2 * T - 1)‼ := by
  have hchoose : ∑ i ∈ range T, (2 * T).choose (2 * i) ≤ 4 ^ T := by
    calc ∑ i ∈ range T, (2 * T).choose (2 * i)
        = ∑ p ∈ (range T).image (fun i ↦ 2 * i), (2 * T).choose p := by
          rw [sum_image]
          intro i _ j _ h
          simpa using h
      _ ≤ ∑ p ∈ range (2 * T + 1), (2 * T).choose p := by
          apply sum_le_sum_of_subset
          intro p hp
          simp only [mem_image, mem_range] at hp ⊢
          omega
      _ = 4 ^ T := by rw [Nat.sum_range_choose, pow_mul]; norm_num
  calc ∑ i ∈ range T, hermCoeff (2 * T) i
      ≤ ∑ i ∈ range T, (2 * T).choose (2 * i) * (2 * T - 1)‼ := by
        apply sum_le_sum
        intro i hi
        simp only [mem_range] at hi
        exact Nat.mul_le_mul_left _ (doubleFactorial_two_mul_sub_one_mono hi.le)
    _ = (∑ i ∈ range T, (2 * T).choose (2 * i)) * (2 * T - 1)‼ := by rw [sum_mul]
    _ ≤ 4 ^ T * (2 * T - 1)‼ := Nat.mul_le_mul_right _ hchoose

/-! ### Moments from Hermite moments -/

variable {k : ℕ}

/-- `E V^{2T} = ∑_{i < T} c_{2T,i} q^i E He_{2T-2i}(V; q) + (2T-1)‼ q^T`. -/
theorem moment_eq_sum_hermite (w V : Fin k → ℝ) (hsum : ∑ c, w c = 1) (q : ℝ) (T : ℕ) :
    ∑ c, w c * V c ^ (2 * T) =
      ∑ i ∈ range T, (hermCoeff (2 * T) i : ℝ) * q ^ i *
          ∑ c, w c * hermite (2 * T - 2 * i) (V c) q +
        ((2 * T - 1)‼ : ℝ) * q ^ T := by
  simp_rw [pow_eq_sum_hermite (2 * T) _ q, mul_sum]
  rw [sum_comm, show 2 * T / 2 = T by omega, sum_range_succ]
  congr 1
  · refine sum_congr rfl fun i _ ↦ sum_congr rfl fun c _ ↦ ?_
    ring
  · simp only [hermCoeff_two_mul_self, Nat.sub_self, hermite_zero, mul_one]
    rw [← sum_mul, hsum, one_mul]

/-- If the Hermite moments of degrees `2, 4, …, 2T` are at most `η`, the `2T`-th moment is within
`η 4^T (2T-1)‼` of the Gaussian one `(2T-1)‼ q^T`. -/
theorem abs_moment_sub_le (w V : Fin k → ℝ) (hsum : ∑ c, w c = 1) {q η : ℝ} (hq : 0 ≤ q)
    (hq1 : q ≤ 1) (hη : 0 ≤ η) (T : ℕ)
    (hh : ∀ i < T, |∑ c, w c * hermite (2 * T - 2 * i) (V c) q| ≤ η) :
    |∑ c, w c * V c ^ (2 * T) - ((2 * T - 1)‼ : ℝ) * q ^ T| ≤ η * (4 ^ T * (2 * T - 1)‼) := by
  rw [moment_eq_sum_hermite w V hsum q T, add_sub_cancel_right]
  calc |∑ i ∈ range T, (hermCoeff (2 * T) i : ℝ) * q ^ i *
          ∑ c, w c * hermite (2 * T - 2 * i) (V c) q|
      ≤ ∑ i ∈ range T, |(hermCoeff (2 * T) i : ℝ) * q ^ i *
          ∑ c, w c * hermite (2 * T - 2 * i) (V c) q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range T, η * (hermCoeff (2 * T) i : ℝ) := by
        apply sum_le_sum
        intro i hi
        simp only [mem_range] at hi
        rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow, abs_of_nonneg hq]
        have h1 : q ^ i ≤ 1 := pow_le_one₀ hq hq1
        have h2 := hh i hi
        have h3 : (0 : ℝ) ≤ hermCoeff (2 * T) i := Nat.cast_nonneg _
        have h4 : 0 ≤ q ^ i := pow_nonneg hq i
        calc (hermCoeff (2 * T) i : ℝ) * q ^ i * |∑ c, w c * hermite (2 * T - 2 * i) (V c) q|
            ≤ (hermCoeff (2 * T) i : ℝ) * 1 * η := by gcongr
          _ = η * (hermCoeff (2 * T) i : ℝ) := by ring
    _ = η * ((∑ i ∈ range T, hermCoeff (2 * T) i : ℕ) : ℝ) := by rw [← mul_sum, Nat.cast_sum]
    _ ≤ η * (4 ^ T * (2 * T - 1)‼ : ℕ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (sum_hermCoeff_le T)) hη
    _ = η * (4 ^ T * (2 * T - 1)‼) := by push_cast; ring

/-! ### The mismatch lemma -/

/-- `9/2 < w_min² 2^t` once `t ≥ 10` and `t ≥ 10 ln (1 / w_min)`. -/
theorem nine_div_two_lt {wmin : ℝ} (hwmin : 0 < wmin) {t : ℕ} (ht : 10 ≤ t)
    (htw : 10 * Real.log (1 / wmin) ≤ t) : 9 / 2 < wmin ^ 2 * 2 ^ t := by
  have hlog : -((t : ℝ) / 10) ≤ Real.log wmin := by
    rw [one_div, Real.log_inv] at htw
    linarith
  have hw : Real.exp (-((t : ℝ) / 10)) ≤ wmin := by
    calc Real.exp (-((t : ℝ) / 10)) ≤ Real.exp (Real.log wmin) := Real.exp_le_exp.mpr hlog
      _ = wmin := Real.exp_log hwmin
  have h2 : (2 : ℝ) ^ t = Real.exp (t * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  have he : Real.exp (-((t : ℝ) / 10)) ^ 2 * 2 ^ t =
      Real.exp ((t : ℝ) * (Real.log 2 - 1 / 5)) := by
    rw [h2, sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have ht' : (10 : ℝ) ≤ t := by exact_mod_cast ht
  have hl := Real.log_two_gt_d9
  have hpos : (0 : ℝ) < Real.log 2 - 1 / 5 := by linarith
  have hbig : (4 : ℝ) < (t : ℝ) * (Real.log 2 - 1 / 5) := by nlinarith
  calc (9 / 2 : ℝ) < (t : ℝ) * (Real.log 2 - 1 / 5) + 1 := by linarith
    _ ≤ Real.exp ((t : ℝ) * (Real.log 2 - 1 / 5)) := Real.add_one_le_exp _
    _ = Real.exp (-((t : ℝ) / 10)) ^ 2 * 2 ^ t := he.symm
    _ ≤ wmin ^ 2 * 2 ^ t := by gcongr

/-- **Moment mismatch**, for any variance parameter `q ∈ (0, 1]`: a distribution with atoms
`V c` of weights `w c ≥ w_min` has a Hermite moment `E He_m(V; q)` of degree `1 ≤ m ≤ 4t` of size
at least `q^{2t} / (4 · 16^t)`, once `t ≥ 10` and `t ≥ 10 ln (1 / w_min)`. -/
theorem exists_hermite_mismatch_of_le_one (w V : Fin k → ℝ) {wmin q : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ w c) (hsum : ∑ c, w c = 1) (hq : 0 < q) (hq1 : q ≤ 1) {t : ℕ}
    (ht : 10 ≤ t) (htw : 10 * Real.log (1 / wmin) ≤ t) :
    ∃ m, 1 ≤ m ∧ m ≤ 4 * t ∧ q ^ (2 * t) / (4 * 16 ^ t) ≤ |∑ c, w c * hermite m (V c) q| := by
  by_contra hcon
  push Not at hcon
  set η := q ^ (2 * t) / (4 * 16 ^ t) with hη
  have hw0 : ∀ c, 0 ≤ w c := fun c ↦ hwmin.le.trans (hw c)
  -- the two moment bounds
  have hdev : ∀ T, T ≤ 2 * t →
      |∑ c, w c * V c ^ (2 * T) - ((2 * T - 1)‼ : ℝ) * q ^ T| ≤ η * (4 ^ T * (2 * T - 1)‼) := by
    intro T hT
    refine abs_moment_sub_le w V hsum hq.le hq1 (by positivity) T
      fun i hi ↦ (hcon _ (by omega) (by omega)).le
  set D1 : ℝ := ((2 * t - 1)‼ : ℝ) with hD1
  set D2 : ℝ := ((2 * (2 * t) - 1)‼ : ℝ) with hD2
  have hD1pos : 0 < D1 := by rw [hD1]; exact_mod_cast Nat.doubleFactorial_pos _
  have hqt : 0 < q ^ t := pow_pos hq t
  have hq2t : q ^ (2 * t) = (q ^ t) ^ 2 := by rw [mul_comm, pow_mul]
  have h16 : (16 : ℝ) ^ t = 4 ^ t * 4 ^ t := by rw [← mul_pow]; norm_num
  have h4pos : (0 : ℝ) < 4 ^ t := by positivity
  have hle1 : q ^ t ≤ 1 := pow_le_one₀ hq.le hq1
  -- `E V^{2t} ≤ (3/2) (2t-1)‼ q^t`
  have hup : ∑ c, w c * V c ^ (2 * t) ≤ 3 / 2 * D1 * q ^ t := by
    have h := (abs_le.mp (hdev t (by omega))).2
    have hηt : η * 4 ^ t ≤ q ^ t / 2 := by
      have e : η * 4 ^ t = (q ^ t) ^ 2 / (4 * 4 ^ t) := by
        rw [hη, h16, hq2t]
        field_simp
      have h1 : (1 : ℝ) ≤ 4 ^ t := one_le_pow₀ (by norm_num)
      calc η * 4 ^ t = (q ^ t) ^ 2 / (4 * 4 ^ t) := e
        _ ≤ q ^ t / (4 * 4 ^ t) := by gcongr; nlinarith
        _ ≤ q ^ t / 2 := by gcongr; linarith
    have : η * (4 ^ t * D1) ≤ q ^ t / 2 * D1 := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hηt hD1pos.le
    linarith
  -- `E V^{4t} ≥ (1/2) (4t-1)‼ q^{2t}`
  have hlow : 1 / 2 * D2 * q ^ (2 * t) ≤ ∑ c, w c * V c ^ (2 * (2 * t)) := by
    have h := (abs_le.mp (hdev (2 * t) le_rfl)).1
    have hηt : η * 4 ^ (2 * t) = q ^ (2 * t) / 4 := by
      rw [hη, show (4 : ℝ) ^ (2 * t) = 16 ^ t by rw [pow_mul]; norm_num]
      field_simp
    have hD2pos : 0 ≤ D2 := by rw [hD2]; positivity
    have hq2pos : 0 ≤ q ^ (2 * t) := by positivity
    have : η * (4 ^ (2 * t) * D2) = q ^ (2 * t) / 4 * D2 := by rw [← mul_assoc, hηt]
    rw [this] at h
    nlinarith
  -- the largest `V_c^{2t}`
  have hk : (univ : Finset (Fin k)).Nonempty := by
    rw [univ_nonempty_iff]
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hsum
  obtain ⟨c0, -, hc0⟩ := exists_max_image univ (fun c ↦ V c ^ (2 * t)) hk
  set B := V c0 ^ (2 * t) with hB
  have hev : ∀ c, 0 ≤ V c ^ (2 * t) := fun c ↦ by rw [pow_mul]; positivity
  have hB0 : 0 ≤ B := hev c0
  have hwB : wmin * B ≤ 3 / 2 * D1 * q ^ t := by
    calc wmin * B ≤ w c0 * V c0 ^ (2 * t) := mul_le_mul_of_nonneg_right (hw c0) hB0
      _ ≤ ∑ c, w c * V c ^ (2 * t) :=
          single_le_sum (f := fun c ↦ w c * V c ^ (2 * t))
            (fun c _ ↦ mul_nonneg (hw0 c) (hev c)) (mem_univ c0)
      _ ≤ _ := hup
  have hB2 : ∑ c, w c * V c ^ (2 * (2 * t)) ≤ B ^ 2 := by
    calc ∑ c, w c * V c ^ (2 * (2 * t)) = ∑ c, w c * (V c ^ (2 * t)) ^ 2 := by
          refine sum_congr rfl fun c _ ↦ ?_
          rw [← pow_mul, mul_comm (2 * t) 2]
      _ ≤ ∑ c, w c * B ^ 2 := by
          apply sum_le_sum
          intro c _
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hev c) (hc0 c (mem_univ c)) 2)
            (hw0 c)
      _ = B ^ 2 := by rw [← sum_mul, hsum, one_mul]
  -- combine: `w_min² (4t-1)‼ ≤ (9/2) ((2t-1)‼)²`
  have hsq : (wmin * B) ^ 2 ≤ (3 / 2 * D1 * q ^ t) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hwmin.le hB0) hwB 2
  have hmain : wmin ^ 2 * D2 ≤ 9 / 2 * D1 ^ 2 := by
    have h1 : wmin ^ 2 * (1 / 2 * D2 * q ^ (2 * t)) ≤ wmin ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_left (hlow.trans hB2) (by positivity)
    have h2 : wmin ^ 2 * D2 * (q ^ t) ^ 2 ≤ 9 / 2 * D1 ^ 2 * (q ^ t) ^ 2 := by
      rw [hq2t] at h1
      nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hfact : 2 ^ t * D1 ^ 2 ≤ D2 := by
    rw [hD1, hD2]
    exact_mod_cast two_pow_mul_doubleFactorial_sq_le t
  have hfin : wmin ^ 2 * 2 ^ t * D1 ^ 2 ≤ 9 / 2 * D1 ^ 2 := by
    calc wmin ^ 2 * 2 ^ t * D1 ^ 2 = wmin ^ 2 * (2 ^ t * D1 ^ 2) := by ring
      _ ≤ wmin ^ 2 * D2 := mul_le_mul_of_nonneg_left hfact (by positivity)
      _ ≤ _ := hmain
  have := le_of_mul_le_mul_right hfin (by positivity)
  linarith [nine_div_two_lt hwmin ht htw]

/-- **Moment mismatch** (`s² = E V²`): a distribution with atoms `V c` of weights `w c ≥ w_min`
and second moment `s² ∈ (0, 1]` has a Hermite moment `E He_m(V; s²)` of degree `1 ≤ m ≤ 4t` of
size at least `s^{4t} / (4 · 16^t)`, once `t ≥ 10` and `t ≥ 10 ln (1 / w_min)`. -/
theorem exists_hermite_mismatch (w V : Fin k → ℝ) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ w c) (hsum : ∑ c, w c = 1) (hs2 : 0 < ∑ c, w c * V c ^ 2)
    (hs2' : ∑ c, w c * V c ^ 2 ≤ 1) {t : ℕ} (ht : 10 ≤ t)
    (htw : 10 * Real.log (1 / wmin) ≤ t) :
    ∃ m, 1 ≤ m ∧ m ≤ 4 * t ∧ (∑ c, w c * V c ^ 2) ^ (2 * t) / (4 * 16 ^ t) ≤
      |∑ c, w c * hermite m (V c) (∑ c, w c * V c ^ 2)| :=
  exists_hermite_mismatch_of_le_one w V hwmin hw hsum hs2 hs2' ht htw

end BS23
