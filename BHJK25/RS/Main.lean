module

public import BHJK25.RS.Construction
public import BHJK25.RS.Null
public import BHJK25.RS.Planted
public import BHJK25.RS.Alg

/-!
# Theorem 2.1

Assembly of [BHJK25, Theorem 2.1] (`BHJK25.reed_solomon_counterexample` in `Challenge.lean`),
with `K = 6`, `ε₀ = 1/30`, `T = ⌈1/(6ε)⌉` (so `1/T ≤ 6ε` and `ε T ≤ 1/5`), the planted
distribution `BHJK25.RS.planted` and the algorithm `BHJK25.RS.rsAlg`.
-/

@[expose] public section

namespace BHJK25

open MeasureTheory Filter RS

/-- `T = ⌈1/(6ε)⌉` satisfies `1 ≤ T`, `1/T ≤ 6ε` and `ε T ≤ 1/5` for `0 < ε ≤ 1/30`. -/
theorem RS.param_T {ε : ℝ} (hε : 0 < ε) (hε0 : ε ≤ 1 / 30) :
    1 ≤ ⌈1 / (6 * ε)⌉₊ ∧ 1 / (⌈1 / (6 * ε)⌉₊ : ℝ) ≤ 6 * ε ∧ ε * ⌈1 / (6 * ε)⌉₊ ≤ 1 / 5 := by
  have h6 : 0 < 6 * ε := by positivity
  have hpos : 0 < 1 / (6 * ε) := by positivity
  have hle : 1 / (6 * ε) ≤ (⌈1 / (6 * ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hlt : (⌈1 / (6 * ε)⌉₊ : ℝ) < 1 / (6 * ε) + 1 := Nat.ceil_lt_add_one hpos.le
  have hTpos : (0 : ℝ) < ⌈1 / (6 * ε)⌉₊ := hpos.trans_le hle
  refine ⟨Nat.one_le_iff_ne_zero.2 fun h ↦ ?_, ?_, ?_⟩
  · rw [h, Nat.cast_zero] at hTpos
    exact lt_irrefl _ hTpos
  · rw [div_le_iff₀ hTpos]
    calc (1 : ℝ) = 6 * ε * (1 / (6 * ε)) := by field_simp
      _ ≤ 6 * ε * ⌈1 / (6 * ε)⌉₊ := by gcongr
  · calc ε * ⌈1 / (6 * ε)⌉₊ ≤ ε * (1 / (6 * ε) + 1) := by gcongr
      _ = 1 / 6 + ε := by field_simp
      _ ≤ 1 / 5 := by linarith

theorem reed_solomon_main :
    ∃ K ε₀ : ℝ, 0 < ε₀ ∧ ∀ k : ℕ, 2 ≤ k → ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ (P : (n : ℕ) → Measure (Tensor k n)) (A : TensorInput k → Bool),
        (∀ n, IsProbabilityMeasure (P n) ∧ SnInvariant (P n) ∧
          AdvantageAtMost entryBits ((n : ℝ) ^ (1 - 6 * ε)) (P n) (uniformTensor k n) 0) ∧
        RunsInTime (encTensor k) Encoding.encBool A (tensorTime k C) ∧
        ∀ᶠ n : ℕ in atTop,
          1 - Real.exp (-(n : ℝ) ^ (1 - K * ε)) ≤ uniformProb k n (fun M ↦ A ⟨n, M⟩ = false) ∧
          1 - Real.exp (-(n : ℝ) ^ (1 - K * ε)) ≤ noisyProb ε (P n) (fun M ↦ A ⟨n, M⟩ = true) := by
  refine ⟨6, 1 / 30, by norm_num, fun k hk ↦ ?_⟩
  obtain ⟨C, hC⟩ := rsAlg_time hk
  refine ⟨C, fun ε hε hε0 ↦ ?_⟩
  obtain ⟨hT, hTε, hεT⟩ := RS.param_T hε hε0
  set T := ⌈1 / (6 * ε)⌉₊ with hTdef
  have hexp : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ^ (1 - 6 * ε) ≤ (n : ℝ) ^ (1 - 1 / (T : ℝ)) :=
    fun n hn ↦ Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  refine ⟨planted k T, rsAlg k T, fun n ↦ ⟨isProbabilityMeasure_planted k T n,
    snInvariant_planted k T n, planted_uniform hk hT n ?_⟩, hC T hT, ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h1 : (1 : ℝ) - 6 * ε ≠ 0 := by linarith
      rw [Nat.cast_zero, Real.zero_rpow h1]
      exact Real.rpow_nonneg le_rfl _
    · exact hexp n hn
  · filter_upwards [null_bound hk hT, planted_bound hk hT hε hεT, rsAlg_correct hk hT,
      eventually_ge_atTop 1] with n hnull hpl hcorr hn
    have hle : 1 - Real.exp (-(n : ℝ) ^ (1 - 6 * ε)) ≤
        1 - Real.exp (-(n : ℝ) ^ (1 - 1 / (T : ℝ))) := by
      have := hexp n hn
      have := Real.exp_le_exp.2 (neg_le_neg this)
      linarith
    refine ⟨hle.trans (hnull.trans_eq ?_), hle.trans (hpl.trans_eq ?_)⟩
    · have hfun : (fun M ↦ ¬ Accept k T n M) = fun M ↦ rsAlg k T ⟨n, M⟩ = false := by
        funext M
        simp [hcorr]
      rw [hfun]
    · unfold noisyProb
      refine Finset.sum_congr rfl fun M _ ↦ Finset.sum_congr rfl fun M' _ ↦ ?_
      have h' : (rsAlg k T ⟨n, M'⟩ = true) ↔ Accept k T n M' := by simp [hcorr]
      by_cases h : Accept k T n M' <;> simp [h, h']

end BHJK25
