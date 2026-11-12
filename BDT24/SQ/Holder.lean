module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev

/-!
# The statistical dimension from moments of the correlations

`BDT24.SQ.avg_abs_le_of_moment`: the argument of [BBH+20, Theorem 3.1] for the bound on the
statistical dimension. If `E |g|^p ≤ M` under the uniform law on a finite set `S`, then on every
`A ⊆ S` of probability at least `1/q²`, by Hölder (or the power-mean inequality)
`(E[|g| | A])^p ≤ E[|g|^p | A] ≤ q² E |g|^p ≤ q² M`. [BBH+20] bound the moments of
`⟨D̄_u, D̄_v⟩ - 1` through the low-degree norm; here they are bounded through the closed form of
the correlations (`BDT24.SQ.pairCorr_eq`).
-/

@[expose] public section

namespace BDT24.SQ

/-- **Hölder for the statistical dimension**: if the `p`-th moment of `|g|` under the uniform law
on `S` is at most `M`, then on every `A ⊆ S` of probability at least `1/q²` the average of `|g|`
is at most `(q² M)^(1/p)`. -/
theorem avg_abs_le_of_moment {α : Type*} {S A : Finset α} (hA : A ⊆ S) (g : α → ℝ) {p : ℕ}
    (hp : 1 ≤ p) {q M : ℝ} (hq : 0 < q) (hAS : 1 / q ^ 2 ≤ (A.card : ℝ) / S.card)
    (hM : (∑ a ∈ S, |g a| ^ p) / S.card ≤ M) :
    (∑ a ∈ A, |g a|) / A.card ≤ (q ^ 2 * M) ^ (1 / (p : ℝ)) := by
  have hq2 : 0 < 1 / q ^ 2 := by positivity
  have hApos : (0 : ℝ) < A.card := by
    rcases Nat.eq_zero_or_pos A.card with h | h
    · rw [h, Nat.cast_zero, zero_div] at hAS
      linarith
    · exact_mod_cast h
  have hSpos : (0 : ℝ) < S.card := by
    rcases Nat.eq_zero_or_pos S.card with h | h
    · rw [h, Nat.cast_zero, div_zero] at hAS
      linarith
    · exact_mod_cast h
  have hx : 0 ≤ (∑ a ∈ A, |g a|) / A.card := by positivity
  -- the power-mean inequality on `A`
  have h1 : ((∑ a ∈ A, |g a|) / A.card) ^ p ≤ (∑ a ∈ A, |g a| ^ p) / A.card := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
    have h := pow_sum_div_card_le_sum_pow (s := A) (f := fun a ↦ |g a|)
      (fun _ _ ↦ abs_nonneg _) m
    rw [div_pow, pow_succ (A.card : ℝ) m, ← div_div]
    exact div_le_div_of_nonneg_right h hApos.le
  have h2 : (∑ a ∈ A, |g a| ^ p) ≤ ∑ a ∈ S, |g a| ^ p :=
    Finset.sum_le_sum_of_subset_of_nonneg hA fun _ _ _ ↦ by positivity
  have hSA : (S.card : ℝ) / A.card ≤ q ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hSpos, one_mul] at hAS
    rw [div_le_iff₀ hApos]
    linarith
  have havg : 0 ≤ (∑ a ∈ S, |g a| ^ p) / S.card := by positivity
  have h3 : (∑ a ∈ A, |g a| ^ p) / A.card ≤ q ^ 2 * M := by
    calc (∑ a ∈ A, |g a| ^ p) / A.card ≤ (∑ a ∈ S, |g a| ^ p) / A.card :=
          div_le_div_of_nonneg_right h2 hApos.le
      _ = (S.card / A.card) * ((∑ a ∈ S, |g a| ^ p) / S.card) := by
          field_simp
      _ ≤ q ^ 2 * M := mul_le_mul hSA hM havg (by positivity)
  have hp0 : p ≠ 0 := by omega
  calc (∑ a ∈ A, |g a|) / A.card
      = (((∑ a ∈ A, |g a|) / A.card) ^ p) ^ (1 / (p : ℝ)) := by
        rw [one_div, Real.pow_rpow_inv_natCast hx hp0]
    _ ≤ (q ^ 2 * M) ^ (1 / (p : ℝ)) :=
        Real.rpow_le_rpow (by positivity) (h1.trans h3) (by positivity)

end BDT24.SQ
