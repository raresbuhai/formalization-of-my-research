module

public import BCFGJPSSV26.Stable.Params

/-!
# The parameter `κ`

[BCFGJPSSV26b, Lemma 3.9 and Appendix C]: for each optimal
cluster, with `x = per/avg_OPT`, `t = max(η, min(1, x))` and `1 + κ = (89 - 12 t)/(65 t)`. Here `κ`
is a definition (`BCFGJPSSV26.Stable.kappa`), not an existential, so that the algorithm's analysis
and the win-win argument use the same value.

* `BCFGJPSSV26.Stable.kappa_mem`: `κ ∈ [12/65, 23/65] ⊆ [1/η - 1, 1/2]`;
* `BCFGJPSSV26.Stable.technical` (the radius–diameter condition of [BCFGJPSSV26b, Lemma 3.9]): if
  `x ≥ η/(1 + ε)` then `(2 + κ) x ≥ 2 + 6 ε`, for `ε < 1/200`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

/-- The ratio `x = per/avg`, and `1` if `avg = 0`. -/
noncomputable def xRatio (per avg : ℝ) : ℝ := if avg = 0 then 1 else per / avg

/-- `t = max(η, min(1, x))`. -/
noncomputable def tClamp (x : ℝ) : ℝ := max eta (min 1 x)

/-- **`κ`**: `1 + κ = (89 - 12 t)/(65 t)`, `t = max(η, min(1, x))`. -/
noncomputable def kappa (x : ℝ) : ℝ := (89 - 12 * tClamp x) / (65 * tClamp x) - 1

theorem tClamp_mem (x : ℝ) : eta ≤ tClamp x ∧ tClamp x ≤ 1 := by
  unfold tClamp eta
  refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- **`κ ∈ [12/65, 23/65]`.** -/
theorem kappa_mem (x : ℝ) : 12 / 65 ≤ kappa x ∧ kappa x ≤ 23 / 65 := by
  obtain ⟨h1, h2⟩ := tClamp_mem x
  unfold eta at h1
  have hpos : 0 < tClamp x := by linarith
  unfold kappa
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    nlinarith

theorem kappa_pos (x : ℝ) : 0 < kappa x := lt_of_lt_of_le (by norm_num) (kappa_mem x).1

theorem kappa_le_half (x : ℝ) : kappa x ≤ 1 / 2 := (kappa_mem x).2.trans (by norm_num)

/-- `κ ≥ 1/η - 1`. -/
theorem inv_eta_sub_one_le_kappa (x : ℝ) : 1 / eta - 1 ≤ kappa x := by
  refine le_trans ?_ (kappa_mem x).1
  unfold eta
  norm_num

/-- `6 ε ≤ κ` for `ε < 1/200`. -/
theorem six_eps_le_kappa {ε : ℝ} (hε : ε < 1 / 200) (x : ℝ) : 6 * ε ≤ kappa x := by
  have := (kappa_mem x).1
  linarith

/-- **The technical condition** (the radius–diameter condition of [BCFGJPSSV26b, Lemma 3.9]): if
`x ≥ η/(1 + ε)` then
`(2 + κ) x ≥ 2 + 6 ε`. -/
theorem technical {ε : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 200) {x : ℝ} (hx : eta / (1 + ε) ≤ x) :
    2 + 6 * ε ≤ (2 + kappa x) * x := by
  obtain ⟨h1, -⟩ := tClamp_mem x
  unfold eta at h1
  have ht : 0 < tClamp x := by linarith
  have h2k : 2 + kappa x = (89 + 53 * tClamp x) / (65 * tClamp x) := by
    unfold kappa
    field_simp
    ring
  have hx' : 89 / 100 ≤ x * (1 + ε) := by
    unfold eta at hx
    rwa [div_le_iff₀ (by linarith)] at hx
  rw [h2k, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  unfold tClamp eta
  rcases le_total x 1 with h | h
  · rw [min_eq_right h]
    rcases le_total (89 / 100) x with h' | h'
    · rw [max_eq_right h']
      have : 0 ≤ x * (53 * x - 41 - 390 * ε) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    · rw [max_eq_left h']
      have : ε * x ≤ ε := mul_le_of_le_one_right hε h
      nlinarith
  · rw [min_eq_left h, max_eq_right (by norm_num)]
    nlinarith

end BCFGJPSSV26.Stable
