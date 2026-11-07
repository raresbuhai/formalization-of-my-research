module

public import BBKS24.Events
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Recovery for large `n`

[BBKS24, the proofs of Lemma 3.7 and Theorem 4.1]: for all large `n`, every `1/2 ≤ q < 1`, every
`k` with `C₁ √n log² n (q/(1-q))⁴ ≤ k ≤ n` and every planted set `S` of size `k`, with probability
at least `1 - 1/400` over `R ∼ G(n, q)`, every graph planted on `S` with the edges of `R` between
`S` and the rest has a triple `α ⊆ S` whose refined set is `S` (`BBKS24.eventually_recovers`).

The parameters of recovery, with `B = p₋ = √(q/(1-q))`, `p₊ = 1/B` and `m = n - k`:
`t₁ = k p₊⁴/2`, `t₂ = k p₊/6`, `τ = k p₊⁴/3` and `s = ⌊18 m² B¹⁰/k²⌋ + 1`. The three events fail
with probability at most `1/1200` each:

* all good: `2 C(k,3) k e^(-k²/(8 n B¹⁶)) ≤ 2 n⁴ e^(-C₁² log⁴ n / 8)`;
* degrees: `2 m e^(-k/(72 B⁴)) ≤ 2 n e^(-C₁ log² n B⁴/72)`;
* few bad: if `m B⁴ < τ` it holds always (`BBKS24.fewBad_of_small`); otherwise
  `m ≥ k/(3B⁸)`, and the sparse norm bound applies once `log² n = O(√n)`.

The size of `S_α ∖ S` for the best triple is at most `m s / C(k, 3) ≤ k/(100 B²) + 1`, against
`(1 - q) k ≥ k/(2B²)` for the refinement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval Finset Real RandomGraph SimpleGraph Filter

namespace BBKS24

variable {n : ℕ}

/-- **Recovery** for `R`: every graph planted on `S` with the edges of `R` between `S` and the
rest has a triple `α ⊆ S` whose refined set is `S`. -/
def Recovers (q : ℝ) (k : ℕ) (S : Finset (Fin n)) (R : SimpleGraph (Fin n)) : Prop :=
  ∀ G : SimpleGraph (Fin n), Planted G R S →
    ∃ α ∈ S.powersetCard 3, refine G k (selected q G k α) = S

/-! ### Facts about the characters -/

section Chars

variable {q : ℝ}

theorem pminus_sq (hq1 : q < 1) (hq0 : 0 ≤ q) : pminus q ^ 2 = q / (1 - q) :=
  Real.sq_sqrt (div_nonneg hq0 (by linarith))

theorem pplus_eq_inv (hq0 : 0 < q) (hq1 : q < 1) : pplus q = (pminus q)⁻¹ :=
  eq_inv_of_mul_eq_one_left (pplus_mul_pminus hq0 hq1)

theorem one_sub_eq (hq0 : 0 < q) (hq1 : q < 1) : 1 - q = 1 / (1 + pminus q ^ 2) := by
  rw [pminus_sq hq1 hq0.le]
  have : 0 < 1 - q := by linarith
  field_simp
  ring

theorem sqrt_mul_pplus (hq0 : 0 < q) (hq1 : q < 1) : √(q * (1 - q)) * pplus q = 1 - q := by
  have h1 : 0 < 1 - q := by linarith
  rw [pplus, ← Real.sqrt_mul (by positivity), show q * (1 - q) * ((1 - q) / q) = (1 - q) ^ 2 by
    field_simp, Real.sqrt_sq h1.le]

end Chars

theorem choose_three_ge {k : ℕ} (hk : 6 ≤ k) : (k : ℝ) ^ 3 / 12 ≤ k.choose 3 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose k 3
  have hd : k.descFactorial 3 = k * (k - 1) * (k - 2) := by
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
    ring
  rw [hd] at h
  have h6 : Nat.factorial 3 = 6 := rfl
  rw [h6] at h
  have h' : (k : ℝ) * (k - 1) * (k - 2) = 6 * k.choose 3 := by
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega)] at this
    linarith
  have hk' : (6 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem choose_three_le (k : ℕ) : (k.choose 3 : ℝ) ≤ k ^ 3 / 6 := by
  have := Nat.choose_le_pow_div (α := ℝ) 3 k
  simpa [Nat.factorial] using this

theorem exp_eight_ge : (2400 : ℝ) ≤ exp 8 := by
  have h := exp_one_gt_d9
  have : exp 8 = exp 1 ^ 8 := by rw [← exp_nat_mul]; norm_num
  rw [this]
  calc (2400 : ℝ) ≤ 2.7182818283 ^ 8 := by norm_num
    _ ≤ exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h.le 8

/-! ### The parameters -/

/-- The number `s` of bad triples allowed: `⌊18 m² B¹⁰/k²⌋ + 1`. -/
noncomputable def nBad (m B : ℝ) (k : ℕ) : ℕ := ⌊18 * m ^ 2 * B ^ 10 / k ^ 2⌋₊ + 1

theorem lt_nBad (m B : ℝ) (k : ℕ) : 18 * m ^ 2 * B ^ 10 / k ^ 2 < nBad m B k :=
  by unfold nBad; push_cast; exact Nat.lt_floor_add_one _

theorem nBad_le {m B : ℝ} (k : ℕ) :
    (nBad m B k : ℝ) ≤ 18 * m ^ 2 * B ^ 10 / k ^ 2 + 1 := by
  unfold nBad
  push_cast
  have : 0 ≤ 18 * m ^ 2 * B ^ 10 / k ^ 2 := by
    have : 0 ≤ B ^ 10 := by positivity
    positivity
  linarith [Nat.floor_le this]

/-- The parameters work, deterministically: the three failure probabilities are at most `1/1200`
(for the third, in the case of many outside vertices, given the requirement of the sparse norm
bound), and the inequalities of recovery hold. Here `Λ = log n ≥ 1`, `B = p₋`,
`C₁² n Λ⁴ B¹⁶ ≤ k²` and `k ≤ n`. -/
theorem params {q : ℝ} (hq : 1 / 2 ≤ q) (hq1 : q < 1) {k : ℕ} {m C₁ : ℝ}
    (hn3 : 3 ≤ n) (hC₁ : 648 ≤ C₁)
    (hsize : C₁ ^ 2 * n * log n ^ 4 * pminus q ^ 16 ≤ (k : ℝ) ^ 2) (hkn : k ≤ n)
    (hm0 : 0 ≤ m) (hmn : m ≤ n) :
    (k.choose 3 : ℝ) * k * (2 * exp (-(k * pplus q ^ 4 / 2) ^ 2 / (2 * (n * (pminus q ^ 4) ^ 2))))
      ≤ 1 / 1200 ∧
    m * (2 * exp (-(k * pplus q / 6) ^ 2 / (2 * (k * pminus q ^ 2)))) ≤ 1 / 1200 ∧
    q * k + √(q * (1 - q)) * (k * pplus q / 6) + m * nBad m (pminus q) k / k.choose 3 < k - 1 ∧
    6 ≤ k := by
  have hq0 : 0 < q := by linarith
  set B := pminus q with hBdef
  set Λ := log (n : ℝ) with hΛ
  have hB1 : 1 ≤ B := one_le_pminus hq hq1
  have hBpos : 0 < B := by linarith
  have hpp : pplus q = B⁻¹ := pplus_eq_inv hq0 hq1
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, le_log_iff_exp_le (by linarith)]
    linarith [exp_one_lt_d9]
  have hnΛ : (n : ℝ) = exp Λ := (exp_log (by linarith)).symm
  -- `k ≥ C₁ Λ² B⁸`.
  have hB8 : 1 ≤ B ^ 8 := one_le_pow₀ hB1
  have hk : C₁ * Λ ^ 2 * B ^ 8 ≤ k := by
    have h2 : (C₁ * Λ ^ 2 * B ^ 8) ^ 2 ≤ (k : ℝ) ^ 2 := by
      calc (C₁ * Λ ^ 2 * B ^ 8) ^ 2 = C₁ ^ 2 * 1 * Λ ^ 4 * B ^ 16 := by ring
        _ ≤ C₁ ^ 2 * n * Λ ^ 4 * B ^ 16 := by gcongr; linarith
        _ ≤ _ := hsize
    exact (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg _) (by norm_num)).1 h2
  have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
  have hΛsq : 1 ≤ Λ ^ 2 := one_le_pow₀ hΛ1
  have hB4 : B ^ 4 ≤ B ^ 8 := pow_le_pow_right₀ hB1 (by norm_num)
  have hB41 : 1 ≤ B ^ 4 := one_le_pow₀ hB1
  have hk648 : 648 * Λ * B ^ 4 ≤ k :=
    le_trans (by gcongr) hk
  have hk648' : (648 : ℝ) ≤ k :=
    le_trans (by nlinarith [mul_le_mul hΛ1 hB41 (by norm_num) (by linarith)]) hk648
  have hkpos : (0 : ℝ) < k := by linarith
  have hk6 : 6 ≤ k := by
    exact_mod_cast (show (6 : ℝ) ≤ k by linarith)
  have hk6' : (6 : ℝ) ≤ k := by exact_mod_cast hk6
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  refine ⟨?_, ?_, ?_, hk6⟩
  · -- All good.
    have hexp : -(k * pplus q ^ 4 / 2) ^ 2 / (2 * (n * (B ^ 4) ^ 2)) ≤ -(C₁ ^ 2 * Λ ^ 4 / 8) := by
      rw [hpp, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      have : (k * B⁻¹ ^ 4 / 2) ^ 2 = k ^ 2 / (4 * B ^ 8) := by field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      nlinarith
    have hc : (k.choose 3 : ℝ) * k ≤ exp (4 * Λ) := by
      calc (k.choose 3 : ℝ) * k ≤ k ^ 3 / 6 * k :=
            mul_le_mul_of_nonneg_right (choose_three_le k) hkpos.le
        _ ≤ (n : ℝ) ^ 4 := by
            have : (k : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ hkpos.le hknR 4
            nlinarith [pow_pos hkpos 4]
        _ = exp (4 * Λ) := by rw [hnΛ, ← exp_nat_mul]; norm_num
    have h8 := exp_eight_ge
    have hΛ4 : Λ ≤ Λ ^ 4 := by nlinarith [pow_le_pow_right₀ hΛ1 (show 2 ≤ 4 by norm_num)]
    calc (k.choose 3 : ℝ) * k * (2 * exp (-(k * pplus q ^ 4 / 2) ^ 2 / (2 * (n * (B ^ 4) ^ 2))))
        ≤ exp (4 * Λ) * (2 * exp (-(C₁ ^ 2 * Λ ^ 4 / 8))) := by gcongr
      _ = 2 * exp (4 * Λ - C₁ ^ 2 * Λ ^ 4 / 8) := by rw [sub_eq_add_neg, exp_add]; ring
      _ ≤ 2 * exp (-8) := by
          gcongr
          have hC2 : (648 : ℝ) ^ 2 ≤ C₁ ^ 2 := pow_le_pow_left₀ (by norm_num) hC₁ 2
          have hCΛ : 648 ^ 2 * Λ ≤ C₁ ^ 2 * Λ ^ 4 :=
            mul_le_mul hC2 hΛ4 (by positivity) (by positivity)
          linarith
      _ ≤ 1 / 1200 := by
          rw [exp_neg]
          have : (0 : ℝ) < exp 8 := exp_pos 8
          rw [show (2 : ℝ) * (exp 8)⁻¹ = 2 / exp 8 by ring, div_le_div_iff₀ this (by norm_num)]
          linarith
  · -- Degrees.
    have hexp : -(k * pplus q / 6) ^ 2 / (2 * (k * B ^ 2)) ≤ -(Λ + 8) := by
      rw [hpp, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      have : (k * B⁻¹ / 6) ^ 2 = k ^ 2 / (36 * B ^ 2) := by field_simp; ring
      rw [this, le_div_iff₀ (by positivity)]
      have hk72 : 72 * B ^ 4 * (Λ + 8) ≤ k := by nlinarith [one_le_pow₀ (n := 4) hB1]
      nlinarith
    have h8 := exp_eight_ge
    calc m * (2 * exp (-(k * pplus q / 6) ^ 2 / (2 * (k * B ^ 2))))
        ≤ exp Λ * (2 * exp (-(Λ + 8))) := by
          gcongr
          rw [← hnΛ]
          exact hmn
      _ = 2 * exp (-8) := by rw [mul_left_comm, ← exp_add]; ring_nf
      _ ≤ 1 / 1200 := by
          rw [exp_neg]
          have : (0 : ℝ) < exp 8 := exp_pos 8
          rw [show (2 : ℝ) * (exp 8)⁻¹ = 2 / exp 8 by ring, div_le_div_iff₀ this (by norm_num)]
          linarith
  · -- The refinement.
    have h1q : 1 - q = 1 / (1 + B ^ 2) := one_sub_eq hq0 hq1
    have hsq : √(q * (1 - q)) * (k * pplus q / 6) = (1 - q) * k / 6 := by
      rw [show √(q * (1 - q)) * (k * pplus q / 6) = √(q * (1 - q)) * pplus q * k / 6 by ring,
        sqrt_mul_pplus hq0 hq1]
    rw [hsq]
    have hchoose := choose_three_ge hk6
    have hcpos : (0 : ℝ) < k.choose 3 := by nlinarith
    have hs := nBad_le (m := m) (B := B) k
    -- `m s / C(k, 3) ≤ k / (100 B²) + 1`.
    have hΛ41 : 1 ≤ Λ ^ 4 := one_le_pow₀ hΛ1
    have hk2 : C₁ ^ 2 * n * B ^ 16 ≤ (k : ℝ) ^ 2 :=
      calc C₁ ^ 2 * n * B ^ 16 = C₁ ^ 2 * n * 1 * B ^ 16 := by ring
        _ ≤ C₁ ^ 2 * n * Λ ^ 4 * B ^ 16 := by gcongr
        _ ≤ _ := hsize
    have hk6pow : 21600 * (n : ℝ) ^ 3 * B ^ 12 ≤ (k : ℝ) ^ 6 := by
      have h3 : (C₁ ^ 2 * n * B ^ 16) ^ 3 ≤ ((k : ℝ) ^ 2) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hk2 3
      have hB : B ^ 12 ≤ B ^ 48 := pow_le_pow_right₀ hB1 (by norm_num)
      have hC6 : (21600 : ℝ) ≤ C₁ ^ 6 :=
        le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hC₁ 6)
      calc 21600 * (n : ℝ) ^ 3 * B ^ 12 ≤ C₁ ^ 6 * n ^ 3 * B ^ 48 := by gcongr
        _ = (C₁ ^ 2 * n * B ^ 16) ^ 3 := by ring
        _ ≤ ((k : ℝ) ^ 2) ^ 3 := h3
        _ = (k : ℝ) ^ 6 := by ring
    have hms : m * nBad m B k / k.choose 3 ≤ k / (100 * B ^ 2) + 1 := by
      rw [div_le_iff₀ hcpos]
      have hm3 : m ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ hm0 hmn 3
      calc m * nBad m B k ≤ m * (18 * m ^ 2 * B ^ 10 / k ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left hs hm0
        _ = 18 * m ^ 3 * B ^ 10 / k ^ 2 + m := by ring
        _ ≤ 18 * (n : ℝ) ^ 3 * B ^ 10 / k ^ 2 + n := by gcongr
        _ ≤ (k / (100 * B ^ 2) + 1) * (k ^ 3 / 12) := by
            have hkk : 12 * (n : ℝ) ≤ k ^ 3 := by
              have hC1 : (1 : ℝ) ≤ C₁ ^ 2 := one_le_pow₀ (by linarith)
              have hB16 : (1 : ℝ) ≤ B ^ 16 := one_le_pow₀ hB1
              have hk2' : (n : ℝ) ≤ k ^ 2 :=
                calc (n : ℝ) = 1 * n * 1 := by ring
                  _ ≤ C₁ ^ 2 * n * B ^ 16 := by gcongr
                  _ ≤ _ := hk2
              calc 12 * (n : ℝ) ≤ 648 * n := by linarith
                _ ≤ k * k ^ 2 := mul_le_mul hk648' hk2' (by positivity) (by positivity)
                _ = k ^ 3 := by ring
            have h1 : 18 * (n : ℝ) ^ 3 * B ^ 10 / k ^ 2 ≤ k / (100 * B ^ 2) * (k ^ 3 / 12) := by
              rw [div_le_iff₀ (by positivity)]
              have : k / (100 * B ^ 2) * (k ^ 3 / 12) * k ^ 2 = k ^ 6 / (1200 * B ^ 2) := by
                field_simp
                ring
              rw [this, le_div_iff₀ (by positivity)]
              have : 18 * (n : ℝ) ^ 3 * B ^ 10 * (1200 * B ^ 2) = 21600 * n ^ 3 * B ^ 12 := by ring
              linarith
            have : (k / (100 * B ^ 2) + 1) * (k ^ 3 / 12) =
                k / (100 * B ^ 2) * (k ^ 3 / 12) + k ^ 3 / 12 := by ring
            linarith
        _ ≤ (k / (100 * B ^ 2) + 1) * k.choose 3 := by gcongr
    have hB2k : 5 * B ^ 2 < k := by
      have hB24 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB1 (by norm_num)
      have : 648 * 1 * B ^ 2 ≤ 648 * Λ * B ^ 4 := by gcongr
      have : 0 < B ^ 2 := by positivity
      linarith
    have hq1B : 1 / (2 * B ^ 2) ≤ 1 - q := by
      rw [h1q]
      have hB2' : 1 ≤ B ^ 2 := one_le_pow₀ hB1
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have hgoal : k / (100 * B ^ 2) + 2 < 5 * (1 - q) * k / 6 := by
      have : 5 * (1 / (2 * B ^ 2)) * k / 6 ≤ 5 * (1 - q) * k / 6 := by gcongr
      have h2 : k / (100 * B ^ 2) + 2 < 5 * (1 / (2 * B ^ 2)) * k / 6 := by
        have : 5 * (1 / (2 * B ^ 2)) * k / 6 = 5 * k / (12 * B ^ 2) := by field_simp; ring
        rw [this]
        have hB2 : 0 < B ^ 2 := by positivity
        rw [div_add' _ _ _ (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
        have h5 := mul_lt_mul_of_pos_left hB2k hB2
        have hkB : 0 ≤ (k : ℝ) * B ^ 2 := by positivity
        nlinarith only [h5, hkB]
      linarith only [this, h2]
    linarith only [hms, hgoal]

/-! ### For large `n` -/

theorem card_out_eq (S : Finset (Fin n)) :
    (Fintype.card {v // v ∉ S} : ℝ) = n - S.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin,
    Nat.cast_sub (by simpa using card_le_univ S)]

/-- `(log n)² ≤ c √n` for all large `n`, for any `c > 0`. -/
theorem eventually_log_sq_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, Real.log n ^ 2 ≤ c * √(n : ℝ) := by
  have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 4 by norm_num)).bound
    (Real.sqrt_pos.2 hc)
  have h' := tendsto_natCast_atTop_atTop.eventually (h.and (eventually_ge_atTop (1 : ℝ)))
  filter_upwards [h'] with n ⟨hn, hn1⟩
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hr : 0 ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by positivity
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hr] at hn
  calc Real.log n ^ 2 ≤ (√c * (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hlog hn 2
    _ = c * √(n : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hc.le, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
          Real.sqrt_eq_rpow]
        norm_num

/-- `log (C(k, 3) + 2) ≤ 3 log n` for `2 ≤ k ≤ n`. -/
theorem log_choose_add_two_le {k : ℕ} (hkn : k ≤ n) (hk : 2 ≤ k) :
    Real.log ((k.choose 3 : ℝ) + 2) ≤ 3 * Real.log n := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  rw [show (3 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 3) by rw [Real.log_pow]; norm_num]
  refine Real.log_le_log (by positivity) ?_
  have h1 := choose_three_le k
  have h2 : (k : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hknR 3
  have h3 : (8 : ℝ) ≤ k ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hk' 3
    norm_num at this
    linarith
  linarith

/-- The arithmetic of the sparse norm requirement with many outside vertices: with `k ≤ 3 m B⁸`,
`C₁ √n Λ² B⁸ ≤ k ≤ n` and `(3888 C)⁴ Λ² ≤ √n`, `C B⁶ s L⁴ D ≤ m`. -/
theorem many_outside_arith {C C₁ B Λ m k n s L D : ℝ} (hC : 0 < C) (hC₁ : 648 ≤ C₁)
    (hC₁C : 23328 * C ≤ C₁ ^ 2) (hΛ1 : 1 ≤ Λ) (hB1 : 1 ≤ B) (hn : 3 ≤ n)
    (hsize : C₁ * √n * Λ ^ 2 * B ^ 8 ≤ k) (hkn : k ≤ n) (hkm : k ≤ 3 * m * B ^ 8)
    (hlarge : (3888 * C) ^ 4 * Λ ^ 2 ≤ √n) (hmn : m ≤ n)
    (hs : s ≤ 18 * m ^ 2 * B ^ 10 / k ^ 2 + 1) (hL : L ≤ 3 * Λ) (hL0 : 0 ≤ L)
    (hD : D ≤ 8) (hD0 : 0 ≤ D) : C * B ^ 6 * s * L ^ 4 * D ≤ m := by
  have hBpos : 0 < B := by linarith
  have hsn : 0 < √n := Real.sqrt_pos.2 (by linarith)
  have hsq : √n * √n = n := Real.mul_self_sqrt (by linarith)
  have hk1 : 1 ≤ √n := Real.one_le_sqrt.2 (by linarith)
  have hkpos : 0 < k := by
    have : 0 < C₁ * √n * Λ ^ 2 * B ^ 8 := by positivity
    linarith
  have hm0 : 0 < m := by
    have : 0 < 3 * m * B ^ 8 := by linarith
    have hB8 : 0 < B ^ 8 := by positivity
    nlinarith
  -- `B⁸ C₁ Λ² ≤ √n`.
  have hBΛ : B ^ 8 * (C₁ * Λ ^ 2) ≤ √n := by
    have : B ^ 8 * (C₁ * Λ ^ 2) * √n ≤ √n * √n := by
      rw [hsq]
      nlinarith
    exact le_of_mul_le_mul_right this hsn
  -- `3888 C B⁶ Λ² ≤ C₁ √n`, by fourth powers.
  have h4 : (3888 * C * B ^ 6 * Λ ^ 2) ^ 4 ≤ (C₁ * √n) ^ 4 := by
    have hy : (B ^ 8 * (C₁ * Λ ^ 2)) ^ 3 ≤ √n ^ 3 := pow_le_pow_left₀ (by positivity) hBΛ 3
    have hC₁0 : 0 < C₁ := by linarith
    have hC17 : 1 ≤ C₁ ^ 7 := one_le_pow₀ (by linarith)
    calc (3888 * C * B ^ 6 * Λ ^ 2) ^ 4
        = (3888 * C) ^ 4 * Λ ^ 2 * ((B ^ 8 * (C₁ * Λ ^ 2)) ^ 3) / C₁ ^ 3 := by
          field_simp
      _ ≤ √n * √n ^ 3 / C₁ ^ 3 := by gcongr
      _ ≤ C₁ ^ 7 * √n * √n ^ 3 / C₁ ^ 3 := by
          gcongr
          nlinarith
      _ = (C₁ * √n) ^ 4 := by
          field_simp
  have h1 : 3888 * C * B ^ 6 * Λ ^ 2 ≤ C₁ * √n :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h4
  -- `C₁ √n Λ² ≤ 3 m`.
  have h2 : C₁ * √n * Λ ^ 2 ≤ 3 * m := by
    have : C₁ * √n * Λ ^ 2 * B ^ 8 ≤ 3 * m * B ^ 8 := hsize.trans hkm
    exact le_of_mul_le_mul_right this (by positivity)
  have hmB : 1296 * C * B ^ 6 * Λ ^ 4 ≤ m := by
    have h3 : 3888 * C * B ^ 6 * Λ ^ 2 * Λ ^ 2 ≤ C₁ * √n * Λ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  -- The first term: `11664 C B¹⁶ m² Λ⁴ / k² ≤ m / 2`.
  have hk2 : C₁ ^ 2 * n * Λ ^ 4 * B ^ 16 ≤ k ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hsize 2
    calc C₁ ^ 2 * n * Λ ^ 4 * B ^ 16 = (C₁ * √n * Λ ^ 2 * B ^ 8) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
          ring
      _ ≤ _ := this
  have hterm1 : 11664 * C * B ^ 16 * m ^ 2 * Λ ^ 4 / k ^ 2 ≤ m / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hmn' : m * (23328 * C * B ^ 16 * Λ ^ 4) ≤ n * (C₁ ^ 2 * Λ ^ 4 * B ^ 16) := by
      have : 23328 * C * B ^ 16 * Λ ^ 4 ≤ C₁ ^ 2 * Λ ^ 4 * B ^ 16 := by
        have := mul_le_mul_of_nonneg_right hC₁C (show 0 ≤ B ^ 16 * Λ ^ 4 by positivity)
        linarith
      exact mul_le_mul hmn this (by positivity) (by positivity)
    have : m * (C₁ ^ 2 * n * Λ ^ 4 * B ^ 16) ≤ m * k ^ 2 := mul_le_mul_of_nonneg_left hk2 hm0.le
    nlinarith
  have hL4 : L ^ 4 ≤ (3 * Λ) ^ 4 := pow_le_pow_left₀ hL0 hL 4
  calc C * B ^ 6 * s * L ^ 4 * D
      ≤ C * B ^ 6 * (18 * m ^ 2 * B ^ 10 / k ^ 2 + 1) * (3 * Λ) ^ 4 * 8 := by gcongr
    _ = 11664 * C * B ^ 16 * m ^ 2 * Λ ^ 4 / k ^ 2 + 648 * C * B ^ 6 * Λ ^ 4 := by ring
    _ ≤ m := by linarith

/-- `2 m B² m < s τ²` for `s > 18 m² B¹⁰ / k²` and `τ = k B⁻⁴ / 3`. -/
theorem bad_count_arith {m B k s : ℝ} (hk : 0 < k) (hB : 0 < B)
    (hs : 18 * m ^ 2 * B ^ 10 / k ^ 2 < s) : 2 * m * B ^ 2 * m < s * (k * B⁻¹ ^ 4 / 3) ^ 2 := by
  have h : (k * B⁻¹ ^ 4 / 3) ^ 2 = k ^ 2 / (9 * B ^ 8) := by field_simp; ring
  rw [h]
  have : 2 * m * B ^ 2 * m = 18 * m ^ 2 * B ^ 10 / k ^ 2 * (k ^ 2 / (9 * B ^ 8)) := by
    field_simp
    ring
  rw [this]
  exact mul_lt_mul_of_pos_right hs (by positivity)

/-- **Recovery for large `n`** [BBKS24, Lemma 3.7, Theorem 4.1]: for all large `n`, every
`1/2 ≤ q < 1`, every `k` with `C₁ √n log² n (q/(1-q))⁴ ≤ k ≤ n` and every `k`-set `S`, with
probability at least `1 - 1/400` over `R ∼ G(n, q)`, every graph planted on `S` with the cut of
`R` has a triple `α ⊆ S` whose refined set is `S`. -/
theorem eventually_recovers : ∃ C₁ : ℝ, 648 ≤ C₁ ∧ ∀ᶠ n : ℕ in atTop, ∀ q : I,
    1 / 2 ≤ (q : ℝ) → (q : ℝ) < 1 → ∀ k : ℕ,
    C₁ * √(n : ℝ) * Real.log n ^ 2 * ((q : ℝ) / (1 - q)) ^ 4 ≤ k → k ≤ n →
    ∀ S : Finset (Fin n), S.card = k →
      1 - 1 / 400 ≤ (G(Fin n, q)).real {R | Recovers q k S R} := by
  obtain ⟨C, hC, hfew⟩ := prob_not_fewBad
  obtain ⟨C₁, hC₁def⟩ : ∃ C₁ : ℝ, C₁ = 648 + 153 * √C := ⟨_, rfl⟩
  have hC₁ : 648 ≤ C₁ := by have := Real.sqrt_nonneg C; linarith
  have hC₁C : 23328 * C ≤ C₁ ^ 2 := by
    have h1 : 153 * √C ≤ C₁ := by have := Real.sqrt_nonneg C; linarith
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    rw [mul_pow, Real.sq_sqrt hC.le] at h2
    linarith
  refine ⟨C₁, hC₁, ?_⟩
  have hc : 0 < 1 / (3888 * C) ^ 4 := by positivity
  filter_upwards [eventually_log_sq_le hc, eventually_ge_atTop 3] with n hlarge hn3 q hq hq1 k
    hsize hkn S hS
  have hq0 : 0 < (q : ℝ) := by linarith
  obtain ⟨B, hB⟩ : ∃ B, B = pminus q := ⟨_, rfl⟩
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, Λ = Real.log (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = (Fintype.card {v // v ∉ S} : ℝ) := ⟨_, rfl⟩
  have hB1 : 1 ≤ B := hB ▸ one_le_pminus hq hq1
  have hBpos : 0 < B := by linarith
  have hpp : pplus q = B⁻¹ := hB ▸ pplus_eq_inv hq0 hq1
  have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hB8 : ((q : ℝ) / (1 - q)) ^ 4 = B ^ 8 := by
    rw [hB, ← pminus_sq hq1 hq0.le, ← pow_mul]
  rw [hB8, ← hΛ] at hsize
  have hsize2 : C₁ ^ 2 * n * Λ ^ 4 * B ^ 16 ≤ (k : ℝ) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hsize 2
    calc C₁ ^ 2 * n * Λ ^ 4 * B ^ 16 = (C₁ * √(n : ℝ) * Λ ^ 2 * B ^ 8) ^ 2 := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
          ring
      _ ≤ _ := this
  have hm : m = n - k := by rw [hmdef, card_out_eq, hS]
  have hknR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hm0 : 0 ≤ m := by rw [hm]; linarith
  have hmn : m ≤ n := by rw [hm]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hsize2' : C₁ ^ 2 * n * Real.log n ^ 4 * pminus q ^ 16 ≤ (k : ℝ) ^ 2 := by
    rw [← hB, ← hΛ]; exact hsize2
  obtain ⟨hF1, hF2, hI3, hk6⟩ := params hq hq1 hn3 hC₁ hsize2' hkn hm0 hmn
  rw [← hB] at hF1 hF2 hI3
  have hk6' : (6 : ℝ) ≤ k := by exact_mod_cast hk6
  have hkpos : (0 : ℝ) < k := by linarith
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = k * pplus q ^ 4 / 3 := ⟨_, rfl⟩
  have hτ : 0 < τ := by
    have := pplus_pos hq0 hq1
    rw [hτdef]
    positivity
  obtain ⟨s, hsdef⟩ : ∃ s, s = nBad m B k := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hsdef, nBad]; omega
  -- The third event.
  have h3 : (cutLaw (Fin n) S q).real {x | ¬ ∀ u : {v // v ∉ S} → ℝ, (∀ i, |u i| ≤ pminus q) →
      ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s} ≤
      1 / 1200 := by
    by_cases hsmall : m * B ^ 4 < τ
    · have hempty : {x : {v // v ∉ S} → {w // w ∈ S} → Prop | ¬ ∀ u : {v // v ∉ S} → ℝ,
          (∀ i, |u i| ≤ pminus q) →
          ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s} =
          ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        refine fun u hu ↦ fewBad_of_small S hq hq1 hs1 ?_ x u hu
        rw [← hmdef, ← hB]
        exact hsmall
      rw [hempty, measureReal_empty]
      norm_num
    · have hkm : (k : ℝ) ≤ 3 * m * B ^ 8 := by
        have h := not_lt.1 hsmall
        rw [hτdef, hpp, inv_pow] at h
        have h' : (k : ℝ) = k * (B ^ 4)⁻¹ / 3 * (3 * B ^ 4) := by field_simp
        have : (k : ℝ) * (B ^ 4)⁻¹ / 3 * (3 * B ^ 4) ≤ m * B ^ 4 * (3 * B ^ 4) :=
          mul_le_mul_of_nonneg_right h (by positivity)
        calc (k : ℝ) = k * (B ^ 4)⁻¹ / 3 * (3 * B ^ 4) := h'
          _ ≤ m * B ^ 4 * (3 * B ^ 4) := this
          _ = 3 * m * B ^ 8 := by ring
      have hchoose := choose_three_ge hk6
      have hB8k : B ^ 8 ≤ k := by
        have h1 : 1 * 1 * 1 * B ^ 8 ≤ C₁ * √(n : ℝ) * Λ ^ 2 * B ^ 8 := by
          gcongr
          · linarith
          · exact Real.one_le_sqrt.2 (by linarith)
          · exact one_le_pow₀ hΛ1
        linarith
      have hB6 : B ^ 6 ≤ B ^ 8 := pow_le_pow_right₀ hB1 (by norm_num)
      have hK : pminus q ^ 6 ≤ (S.card.choose 3 : ℝ) + 2 := by
        rw [← hB, hS]
        nlinarith
      have hL := log_choose_add_two_le hkn (by omega)
      have hL0 : 0 ≤ Real.log ((k.choose 3 : ℝ) + 2) := Real.log_nonneg (by
        have : (0 : ℝ) ≤ k.choose 3 := Nat.cast_nonneg _
        linarith)
      have hD : Real.log (2 / (1 / 1200)) ≤ 8 := by
        rw [show (2 : ℝ) / (1 / 1200) = 2400 by norm_num, Real.log_le_iff_le_exp (by norm_num)]
        exact exp_eight_ge
      have hD0 : 0 ≤ Real.log (2 / (1 / 1200)) := Real.log_nonneg (by norm_num)
      have hlarge' : (3888 * C) ^ 4 * Λ ^ 2 ≤ √(n : ℝ) := by
        rw [hΛ]
        calc (3888 * C) ^ 4 * Real.log n ^ 2 ≤ (3888 * C) ^ 4 * (1 / (3888 * C) ^ 4 * √(n : ℝ)) :=
              by gcongr
          _ = √(n : ℝ) := by field_simp
      refine hfew S hq hq1 (by norm_num) (by norm_num) hK ?_ hτ ?_
      · rw [← hB, ← hmdef, hS]
        exact many_outside_arith hC hC₁ hC₁C hΛ1 hB1 hn3' hsize hknR hkm hlarge' hmn
          (hsdef ▸ nBad_le k) (hΛ ▸ hL) hL0 hD hD0
      · rw [← hB, ← hmdef, hτdef, hpp]
        exact bad_count_arith hkpos hBpos (hsdef ▸ lt_nBad m B k)
  -- The good cut.
  have hpp0 := pplus_pos hq0 hq1
  have hgood := prob_goodCut S hq hq1 (t₁ := k * pplus q ^ 4 / 2) (t₂ := k * pplus q / 6)
    (by positivity) (by positivity) (M := n) (by rw [← hmdef]; exact hmn) h3
  rw [card_powersetCard, hS, ← hmdef, ← hB] at hgood
  have hsub : {R : SimpleGraph (Fin n) | GoodCut q S (k * pplus q ^ 4 / 2) (k * pplus q / 6) τ s
      (cut S R)} ⊆ {R | Recovers q k S R} := by
    intro R hR G hP
    refine hR.exists_refine_eq hP hq hq1 hS (by omega) le_rfl ?_ ?_
    · rw [hτdef]
      ring_nf
      exact le_rfl
    · rw [← hm, hsdef]
      exact hI3
  calc 1 - 1 / 400 ≤ 1 - ((k.choose 3 : ℝ) * k * (2 * Real.exp (-(k * pplus q ^ 4 / 2) ^ 2 /
        (2 * (n * (B ^ 4) ^ 2)))) + m * (2 * Real.exp (-(k * pplus q / 6) ^ 2 /
        (2 * (k * B ^ 2)))) + 1 / 1200) := by linarith
    _ ≤ _ := hgood
    _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)

end BBKS24
