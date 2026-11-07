module

public import BKS23.Model
import BKS23.Assembly
import BKS23.Assembly1
import BKS23.Algorithm1PolyTime

/-!
# Main results: proofs

Restates each theorem of `Challenge.lean` with the same name and statement, and proves it from the
development in this folder. Don't import `Challenge` here: the names would clash.

* Theorem 5.6 (1) is assembled in `BKS23/Assembly1.lean`: the algorithm `BKS23.Algorithm.alg1`,
  its running time (`BKS23.Algorithm.exists_alg1_inO`), and its success probability for large `n`
  (`BKS23.Assembly1.le_successProb1`, `BKS23.Size1.eventually_large`), with `C = 32`.
* Theorem 5.6 (2) is assembled in `BKS23/Assembly.lean`: the algorithm `BKS23.Algorithm.alg t`
  with `t = BKS23.Assembly.tOf ε`, its running time (`BKS23.Algorithm.exists_alg_inO`), and its
  success probability for large `n` (`BKS23.Assembly.le_successProb_of_large`,
  `BKS23.Assembly.eventually_large`).
-/

public section

namespace BKS23

open Filter Topology

/-- **Theorem 5.6 (1)** of [BKS23]: semi-random planted clique can be solved in polynomial time,
in the list-decoding sense, for cliques of size `k ≥ O(n^(2/3) p^(1/3) / (1 - p)^(2/3))` and
`k ≥ O(√n log n)`, by an algorithm that is not given the edge probability `p`. -/
theorem semirandom_planted_clique_two_thirds :
    ∃ (A : Input × List Bool → Output) (d : ℕ),
      1 ≤ d ∧ RunsInTime A (fun N ↦ (N + 2) ^ d) ∧
      ∃ C : ℝ, ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
          C * max ((n : ℝ) ^ (2 / 3 : ℝ) * p ^ (1 / 3 : ℝ) / (1 - p) ^ (2 / 3 : ℝ))
            (√(n : ℝ) * Real.log n) ≤ k → k ≤ n →
          ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
            0.99 ≤ successProb n k p S Adv A (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) := by
  obtain ⟨d, c, hc⟩ := Algorithm.exists_alg1_inO
  refine ⟨Algorithm.alg1, d + 1, by omega, ⟨c, hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩, 32,
    Size1.δ1, Size1.tendsto_δ1, ?_⟩
  all_goals
    try
      refine Nat.mul_le_mul_left c ?_
      have : ((encInput xr.1).length + 2) ^ d ≤ ((encInput xr.1).length + 2) ^ (d + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.le_succ_of_le (Nat.add_le_add this (le_of_eq rfl))
  filter_upwards [Size1.eventually_large] with n hL p hp hp1 k hsize hkn S hS Adv
  exact Assembly1.le_successProb1 hL hp hp1 hsize hkn hS Adv _

/-- **Theorem 5.6 (2)** of [BKS23]: semi-random planted clique can be solved, in the list-decoding
sense, for cliques of size approaching `√n`. -/
theorem semirandom_planted_clique :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
      ∃ (A : Input × List Bool → Output) (d : ℕ),
        1 ≤ d ∧ (d : ℝ) ≤ C / ε ∧ RunsInTime A (fun N ↦ (N + 2) ^ d) ∧
        ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
          ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
            (n : ℝ) ^ (1 / 2 + ε) / (1 - p) ^ (1 / ε) ≤ k → k ≤ n →
            ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
              0.99 ≤ successProb n k p S Adv A (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) := by
  obtain ⟨E, hE⟩ := Algorithm.exists_alg_inO
  refine ⟨E + 1, fun ε hε hε1 ↦ ?_⟩
  obtain ⟨-, h2, h3⟩ := Assembly.tOf_spec hε hε1
  set t := Assembly.tOf ε
  obtain ⟨c, hc⟩ := hE t
  -- The exponent `d = E (t + 1) + 1`, and `t + 1 ≤ 1/ε`.
  have ht : ((t : ℝ) + 1) * ε ≤ 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) t]
  refine ⟨Algorithm.alg t, E * (t + 1) + 1, by omega, ?_, ⟨c, hc.mono (fun xr ↦ ?_) (fun xr ↦ ?_)⟩,
    Assembly.δOf ε t, Assembly.tendsto_δOf (Assembly.one_div_lt hε hε1) h3, ?_⟩
  · have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg E
    rw [le_div_iff₀ hε]
    push_cast
    nlinarith
  all_goals
    try
      refine Nat.mul_le_mul_left c ?_
      have : ((encInput xr.1).length + 2) ^ (E * (t + 1)) ≤
          ((encInput xr.1).length + 2) ^ (E * (t + 1) + 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.le_succ_of_le (Nat.add_le_add this (le_of_eq rfl))
  filter_upwards [Assembly.eventually_large hε hε1] with n hL p hp hp1 k hsize hkn S hS Adv
  exact Assembly.le_successProb_of_large hε hε1 hL hp hp1 hsize hkn hS Adv _

end BKS23
