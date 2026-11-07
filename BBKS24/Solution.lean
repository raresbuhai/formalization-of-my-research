module

public import BBKS24.Model
import BBKS24.Assembly
import BBKS24.RunTime

/-!
# Main result: proof

Restates the theorem of `Challenge.lean` with the same name and statement, and proves it from the
development in this folder. Don't import `Challenge` here: the names would clash.

The algorithm is `BBKS24.Alg.alg`. Its running time is `BBKS24.Alg.exists_runsInTime`, and its
success probability for all large `n` is `BBKS24.Asm.eventually_le_successProb`.
-/

public section

namespace BBKS24

open Filter Topology

/-- **Theorem 4.1** of [BBKS24], which contains **Theorem 1.2** (Theorem 3.1) as the case
`p = 1/2`: semirandom planted clique can be solved, in the list-decoding sense, in polynomial time
for cliques of size `k ≥ O(√n log² n · max(1, (p/(1 - p))⁴))`, by an algorithm that is not given
the edge probability `p`. -/
theorem semirandom_planted_clique :
    ∃ (A : Input × List Bool → Output) (d : ℕ),
      1 ≤ d ∧ RunsInTime A (fun N ↦ (N + 2) ^ d) ∧
      ∃ C : ℝ, ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop, ∀ p : ℝ, 0 ≤ p → p < 1 → ∀ k : ℕ,
          C * √(n : ℝ) * Real.log n ^ 2 * max 1 ((p / (1 - p)) ^ 4) ≤ k → k ≤ n →
          ∀ S : Finset (Fin n), S.card = k → ∀ Adv : Adversary n,
            0.99 ≤ successProb n k p S Adv A (fun N ↦ (N + 2) ^ d) ((1 + δ n) * n / k) := by
  obtain ⟨d, hd, hrun⟩ := Alg.exists_runsInTime
  obtain ⟨C, δ, hδ, hev⟩ := Asm.eventually_le_successProb
  exact ⟨Alg.alg, d, by omega, hrun, C, δ, hδ, hev d hd⟩

end BBKS24
