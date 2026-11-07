module

public import BCFGJPSSV26.Greedy.Algorithm
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The constants of Theorem 1.2

For each `ε > 0`:

| regime | `δ` | paper's `ε` | `ε'` |
|---|---|---|---|
| `ε ≤ 1` | a rational in `(ε/200, ε/100)` | `δ/10` | `25 δ` |
| `1 < ε < 4` | `1/100` | `1/1000` | `1/4` |
| `ε ≥ 4` | local search | | |

and one constant `C = 10¹⁰` (`BCFGJPSSV26.Greedy.Cthm`) for all `ε`. The ratio is
`(ρ + 10δ)(1 + ε') ≤ 1.9499 + ε` (`BCFGJPSSV26.Greedy.ratio_le`). The trivial solution may have
`⌊log₂ n⌋ ⌈1/δ²⌉ ≤ C log n / ε²` extra facilities (`BCFGJPSSV26.Greedy.bcomp_le`); when it has
more, `n > ⌊log₂ n⌋ ⌈1/δ²⌉ ≥ 1/δ²`, so `log M = O(log n)` and `6 R ≤ C log n / ε²`
(`BCFGJPSSV26.Greedy.sixR_le`). This keeps the bound uniform in `ε`, although after the scaling
`log M` is only `O(log n + log(1/ε))` in general.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- The constant `C` of Theorem 1.2. -/
def Cthm : ℝ := 10 ^ 10

/-- `δ` for `ε ≤ 1`: a rational in `(ε/200, ε/100)`. -/
noncomputable def δsmall (ε : ℝ) : ℚ :=
  if h : 0 < ε then (exists_rat_btwn (by linarith : ε / 200 < ε / 100)).choose else 1 / 100

theorem δsmall_spec {ε : ℝ} (hε : 0 < ε) : ε / 200 < δsmall ε ∧ (δsmall ε : ℝ) < ε / 100 := by
  unfold δsmall
  rw [dite_eq_left hε]
  exact (exists_rat_btwn (by linarith : ε / 200 < ε / 100)).choose_spec

/-- The constants for `ε < 4`. -/
noncomputable def constsOf (ε : ℝ) : Consts :=
  if ε ≤ 1 then ⟨δsmall ε, δsmall ε / 10, 25 * δsmall ε⟩ else ⟨1 / 100, 1 / 1000, 1 / 4⟩

theorem constsOf_good {ε : ℝ} (hε : 0 < ε) : (constsOf ε).Good := by
  unfold constsOf
  split_ifs with h1
  · obtain ⟨h₁, h₂⟩ := δsmall_spec hε
    have hpos : (0 : ℝ) < δsmall ε := by linarith
    have hle : (δsmall ε : ℝ) ≤ 1 / 100 := by linarith
    have hpos' : (0 : ℚ) < δsmall ε := by exact_mod_cast hpos
    have hle' : δsmall ε ≤ 1 / 100 := by
      have : ((δsmall ε : ℚ) : ℝ) ≤ ((1 / 100 : ℚ) : ℝ) := by
        rw [show ((1 / 100 : ℚ) : ℝ) = 1 / 100 by norm_num]
        exact hle
      exact (Rat.cast_le (K := ℝ)).1 this
    exact ⟨hpos', hle', rfl, by positivity, by linarith⟩
  · exact ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The ratio**: `(ρ + 10δ)(1 + ε') ≤ 1.9499 + ε`. -/
theorem ratio_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) :
    ((((ρ + 10 * (constsOf ε).δ) * (1 + (constsOf ε).εp) : ℚ)) : ℝ) ≤ 1.9499 + ε := by
  have hρ : ((ρ : ℚ) : ℝ) = 30466 / 15625 := by
    rw [ρ_eq]
    norm_num
  unfold constsOf
  split_ifs with h1
  · obtain ⟨h₁, h₂⟩ := δsmall_spec hε
    push_cast
    rw [hρ]
    have hδ : (0 : ℝ) < δsmall ε := by linarith
    nlinarith [mul_lt_mul_of_pos_left h₂ hδ]
  · push_cast
    rw [hρ]
    push Not at h1
    norm_num
    linarith

/-- `⌊log₂ n⌋ ≤ 2 log n`, from `log 2 ≥ 1/2`. -/
theorem natLog_two_le_two_log (n : ℕ) : (Nat.log 2 n : ℝ) ≤ 2 * Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h2 : (2 : ℝ) ^ Nat.log 2 n ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have h := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h
  have hl2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [one_div, Real.log_inv] at this
    linarith
  have := (Nat.cast_nonneg (Nat.log 2 n) : (0 : ℝ) ≤ _)
  nlinarith

/-- `1/δ² ≤ 160000/ε²` for the constants of `ε < 4`. -/
theorem inv_δ_sq_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) :
    1 / ((constsOf ε).δ : ℝ) ^ 2 ≤ 160000 / ε ^ 2 := by
  unfold constsOf
  split_ifs with h1
  · obtain ⟨h₁, -⟩ := δsmall_spec hε
    have hδ : (0 : ℝ) < δsmall ε := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · push Not at h1
    push_cast
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The parameters of `ε < 4`: `ε_g = δ/10` and `ε' = 25 δ`. -/
theorem constsOf_rel {ε : ℝ} (hε : 0 < ε) :
    0 < (constsOf ε).δ ∧ (constsOf ε).δ ≤ 1 / 100 ∧ (constsOf ε).εg = (constsOf ε).δ / 10 ∧
      (constsOf ε).εp = 25 * (constsOf ε).δ := by
  have hc := constsOf_good hε
  refine ⟨hc.δ_pos, hc.δ_le, hc.εg_eq, ?_⟩
  unfold constsOf
  split_ifs <;> norm_num

/-- **The extra facilities of the trivial solution**: `⌊log₂ n⌋ ⌈1/δ²⌉ ≤ C log n / ε²`. -/
theorem bcomp_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) (n : ℕ) :
    (bcomp (constsOf ε) n : ℝ) ≤ Cthm * Real.log n / ε ^ 2 := by
  have hq := inv_δ_sq_le hε h4
  obtain ⟨hδ0, hδ1, -, -⟩ := constsOf_rel hε
  have hL := natLog_two_le_two_log n
  have hlog := Real.log_natCast_nonneg n
  have hδ0' : (0 : ℝ) < (constsOf ε).δ := by exact_mod_cast hδ0
  have hδ1' : ((constsOf ε).δ : ℝ) ≤ 1 / 100 := by
    have h := (Rat.cast_le (K := ℝ)).2 hδ1
    rwa [show ((1 / 100 : ℚ) : ℝ) = 1 / 100 by norm_num] at h
  -- `⌈1/δ²⌉ ≤ 1/δ² + 1 ≤ 2/δ²`
  have hA : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ) ≤ 2 * (1 / ((constsOf ε).δ : ℝ) ^ 2) := by
    have h1 : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℚ) < 1 / (constsOf ε).δ ^ 2 + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ) < 1 / ((constsOf ε).δ : ℝ) ^ 2 + 1 := by
      exact_mod_cast h1
    have h3 : (1 : ℝ) ≤ 1 / ((constsOf ε).δ : ℝ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hu : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  have he : Cthm * Real.log n / ε ^ 2 = 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by
    unfold Cthm
    ring
  have he' : (160000 : ℝ) / ε ^ 2 = 160000 * (1 / ε ^ 2) := by ring
  rw [he]
  rw [he'] at hq
  unfold bcomp
  push_cast
  have hA' : (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ) ≤ 320000 * (1 / ε ^ 2) := by linarith
  calc (Nat.log 2 n : ℝ) * (⌈1 / (constsOf ε).δ ^ 2⌉₊ : ℝ)
      ≤ (2 * Real.log n) * (320000 * (1 / ε ^ 2)) :=
        mul_le_mul hL hA' (Nat.cast_nonneg _) (by positivity)
    _ ≤ 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by nlinarith


/-- The number of phases for `ε_g = δ/10` and `ε' = 25 δ`, when `n > ⌊log₂ n⌋ ⌈1/δ²⌉` and
`n ≥ 2`: then `1/δ < n`, `M ≤ n³ + 1`, `⌈log₂ ⌈5 n M⌉⌉ ≤ 12 ⌊log₂ n⌋`, and
`6 R ≤ 7278 ⌊log₂ n⌋ / δ²`. -/
theorem sixR_le_aux {c : Consts} (hδ0 : 0 < c.δ) (hδ1 : c.δ ≤ 1 / 100) (hg : c.εg = c.δ / 10)
    (hp : c.εp = 25 * c.δ) {n : ℕ} (hbn : bcomp c n < n) (hn : 2 ≤ n) :
    ((6 * Rof c n : ℕ) : ℚ) ≤ 7278 * Nat.log 2 n * (1 / c.δ ^ 2) := by
  have hL1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hq1 : 1 ≤ 1 / c.δ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- `⌈1/δ²⌉ < n`, so `1/δ ≤ 1/δ² < n`
  have hA : ⌈1 / c.δ ^ 2⌉₊ < n := by
    unfold bcomp at hbn
    have : ⌈1 / c.δ ^ 2⌉₊ ≤ Nat.log 2 n * ⌈1 / c.δ ^ 2⌉₊ := Nat.le_mul_of_pos_left _ hL1
    omega
  have hqn : 1 / c.δ ^ 2 < n := by
    have h1 : 1 / c.δ ^ 2 ≤ ⌈1 / c.δ ^ 2⌉₊ := Nat.le_ceil _
    have h2 : (⌈1 / c.δ ^ 2⌉₊ : ℚ) < n := by exact_mod_cast hA
    linarith
  have hinv : 1 / c.δ ≤ 1 / c.δ ^ 2 := by
    rw [div_le_div_iff₀ hδ0 (by positivity)]
    nlinarith
  -- `5 n M ≤ 16 n⁴ ≤ 2^(4 ⌊log₂ n⌋ + 8)`
  have hn0 : (1 : ℚ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hM : 5 * (n : ℚ) * Mof c n ≤ 2 ^ (4 * Nat.log 2 n + 8) := by
    have hn2 : (n : ℚ) ≤ 2 ^ (Nat.log 2 n + 1) := by
      exact_mod_cast (Nat.lt_pow_succ_log_self (by norm_num) n).le
    have hMe : Mof c n = 8 / 25 * (n : ℚ) ^ 2 * (1 / c.δ) + 1 := by
      unfold Mof
      rw [hp]
      field_simp
    rw [hMe]
    have h1 : 1 / c.δ ≤ n := hinv.trans hqn.le
    have h2 : 8 / 25 * (n : ℚ) ^ 2 * (1 / c.δ) ≤ 8 / 25 * (n : ℚ) ^ 2 * n :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (n : ℚ) ^ 4 ≤ (2 ^ (Nat.log 2 n + 1)) ^ 4 := pow_le_pow_left₀ (by positivity) hn2 4
    have h4 : (n : ℚ) ≤ (n : ℚ) ^ 4 := by
      have : (n : ℚ) ^ 1 ≤ (n : ℚ) ^ 4 := pow_le_pow_right₀ hn0 (by norm_num)
      simpa using this
    calc 5 * (n : ℚ) * (8 / 25 * (n : ℚ) ^ 2 * (1 / c.δ) + 1)
        ≤ 5 * (n : ℚ) * (8 / 25 * (n : ℚ) ^ 2 * n + 1) := by gcongr
      _ ≤ 16 * (2 ^ (Nat.log 2 n + 1)) ^ 4 := by nlinarith
      _ = 2 ^ (4 * Nat.log 2 n + 8) := by ring
  have ha : Nat.clog 2 ⌈5 * (n : ℚ) * Mof c n⌉₊ ≤ 12 * Nat.log 2 n := by
    refine (Nat.clog_le_of_le_pow ?_).trans (by omega : 4 * Nat.log 2 n + 8 ≤ 12 * Nat.log 2 n)
    exact Nat.ceil_le.2 (by exact_mod_cast hM)
  -- `⌈1/ε_g²⌉ ≤ 100/δ² + 1`
  have hB : (⌈1 / c.εg ^ 2⌉₊ : ℚ) ≤ 100 * (1 / c.δ ^ 2) + 1 := by
    have h1 : (⌈1 / c.εg ^ 2⌉₊ : ℚ) < 1 / c.εg ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 / c.εg ^ 2 = 100 * (1 / c.δ ^ 2) := by
      rw [hg]
      field_simp
      norm_num
    linarith
  have ha' : (Nat.clog 2 ⌈5 * (n : ℚ) * Mof c n⌉₊ : ℚ) ≤ 12 * Nat.log 2 n := by
    exact_mod_cast ha
  have hL1' : (1 : ℚ) ≤ Nat.log 2 n := by exact_mod_cast hL1
  have hBa := mul_le_mul hB ha' (Nat.cast_nonneg _) (by positivity)
  unfold Rof
  push_cast
  nlinarith

/-- **The free atoms of the core**: when `n > ⌊log₂ n⌋ ⌈1/δ²⌉` and `n ≥ 2`,
`6 R ≤ C log n / ε²`. -/
theorem sixR_le {ε : ℝ} (hε : 0 < ε) (h4 : ε < 4) {n : ℕ} (hbn : bcomp (constsOf ε) n < n)
    (hn : 2 ≤ n) : ((6 * Rof (constsOf ε) n : ℕ) : ℝ) ≤ Cthm * Real.log n / ε ^ 2 := by
  obtain ⟨hδ0, hδ1, hg, hp⟩ := constsOf_rel hε
  have h := sixR_le_aux hδ0 hδ1 hg hp hbn hn
  have h' : ((6 * Rof (constsOf ε) n : ℕ) : ℝ) ≤
      7278 * Nat.log 2 n * (1 / ((constsOf ε).δ : ℝ) ^ 2) := by
    exact_mod_cast h
  have hq := inv_δ_sq_le hε h4
  have hL := natLog_two_le_two_log n
  have hlog := Real.log_natCast_nonneg n
  have hu : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  have he : Cthm * Real.log n / ε ^ 2 = 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by
    unfold Cthm
    ring
  have he' : (160000 : ℝ) / ε ^ 2 = 160000 * (1 / ε ^ 2) := by ring
  rw [he]
  rw [he'] at hq
  have hδ0' : (0 : ℝ) < (constsOf ε).δ := by exact_mod_cast hδ0
  calc ((6 * Rof (constsOf ε) n : ℕ) : ℝ)
      ≤ 7278 * Nat.log 2 n * (1 / ((constsOf ε).δ : ℝ) ^ 2) := h'
    _ ≤ 7278 * (2 * Real.log n) * (160000 * (1 / ε ^ 2)) := by
        have := Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)
        gcongr
    _ ≤ 10 ^ 10 * Real.log n * (1 / ε ^ 2) := by nlinarith

/-! ### The algorithm for `ε` -/

/-- **The algorithm of Theorem 1.2 for `ε`**, on the tuple of an instance. -/
noncomputable def algFor (ε : ℝ) : Raw → List ℕ :=
  if 4 ≤ ε then algLS else algMain (constsOf ε)

theorem log_div_nonneg (ε : ℝ) (n : ℕ) : 0 ≤ Cthm * Real.log n / ε ^ 2 := by
  have := Real.log_natCast_nonneg n
  unfold Cthm
  positivity

/-- **The guarantee of the algorithm for `ε`.** -/
theorem algFor_spec {ε : ℝ} (hε : 0 < ε) {I : Instance} (hI : I.Valid) :
    I.IsCenterList (algFor ε (toRaw I)) ∧
      ((algFor ε (toRaw I)).length : ℝ) ≤ I.k + Cthm * Real.log I.n / ε ^ 2 ∧
      I.cost (I.centers (algFor ε (toRaw I))) ≤ (1.9499 + ε) * I.opt I.k := by
  have hopt0 := Instance.opt_nonneg' hI I.k
  have hlog := log_div_nonneg ε I.n
  unfold algFor
  split_ifs with h4
  · obtain ⟨hc, hlen, hcost⟩ := algLS_spec hI
    refine ⟨hc, ?_, hcost.trans ?_⟩
    · have : ((algLS (toRaw I)).length : ℝ) ≤ I.k := by exact_mod_cast hlen
      linarith
    · nlinarith
  · push Not at h4
    obtain ⟨hc, hlen, hcost⟩ := algMain_spec (constsOf_good hε) hI
    refine ⟨hc, ?_, hcost.trans (mul_le_mul_of_nonneg_right (ratio_le hε h4) hopt0)⟩
    rcases hlen with hlen | ⟨hbn, hn2, hlen⟩
    · have h := bcomp_le hε h4 I.n
      have : ((algMain (constsOf ε) (toRaw I)).length : ℝ) ≤ I.k + bcomp (constsOf ε) I.n := by
        exact_mod_cast hlen
      linarith
    · have h := sixR_le hε h4 hbn hn2
      have : ((algMain (constsOf ε) (toRaw I)).length : ℝ) ≤
          I.k + ((6 * Rof (constsOf ε) I.n : ℕ) : ℝ) := by
        exact_mod_cast hlen
      linarith

end BCFGJPSSV26.Greedy
