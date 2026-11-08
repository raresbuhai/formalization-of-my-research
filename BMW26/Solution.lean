module

public import BMW26.Model
import BMW26.Assembly
import BMW26.Paper.FKN
import BMW26.Paper.Spectral

/-!
# Results: proofs

Restates each theorem of `Challenge.lean` with the same name and statement, and proves it from the
development in this folder. Don't import `Challenge` here: the names would clash.

* Theorem 1.2: `BMW26.hypercube_recovery_of_parts` in `BMW26/Assembly.lean`.
* Theorem 4.1: `BMW26.sos_fkn_of_parts` in `BMW26/Paper/FKN.lean`.
* Lemma 5.1: `BMW26.spectral_concentration_of_parts` in `BMW26/Paper/Spectral.lean`.
-/

public section

namespace BMW26

open Filter Topology

/-- **Theorem 1.2** of [BMW26]: for every `c`, there are a constant `C` and a randomized
polynomial-time algorithm that, given a sample of the percolated hypercube `Q_d(p)` with
`p ≥ C log d / d` whose vertices have been arbitrarily renamed, recovers the hidden vectors of all
but `2^d / d^c` vertices, up to a symmetry of `Q_d`, with probability `1 - o_d(1)`. -/
theorem hypercube_recovery :
    ∀ c : ℕ, ∃ (A : Graph × List Bool → Output) (k : ℕ), RunsInTime A (fun N ↦ (N + 2) ^ k) ∧
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
        ∀ᶠ d : ℕ in atTop, ∀ p : ℝ, C * Real.log d / d ≤ p → p ≤ 1 →
          ∀ ren : SimpleGraph (Cube d) → Renaming d,
            1 - δ d ≤ successProb d p ren A (fun N ↦ (N + 2) ^ k) (2 ^ d / (d : ℝ) ^ c) :=
  hypercube_recovery_of_parts

open MvPolynomial in
/-- **Theorem 4.1** of [BMW26], the sum-of-squares FKN theorem: the constraints
`∑ᵢ ⟨f, χᵢ⟩² ≥ 1 - δ`, `δ ≥ 0` and `f(x)² = 1` prove `∑ᵢ ⟨f, χᵢ⟩⁴ ≥ 1 - K δ` in degree `4`, by a
proof whose coefficients are at most `2^(K (d + 1))` in absolute value and in which `δ` appears in
each term only as the monomial `δ`; and when `δ` is replaced by any polynomial `q` of degree at most
`2`, there is still such a proof of degree `4`, whose coefficients are at most `2^(b + K (d + 1))`
when those of `q` are at most `2^b`. -/
theorem sos_fkn :
    ∃ K : ℝ,
      (∀ d : ℕ, ∃ P : SoS.Proof (fknSystem (X none : MvPolynomial (FKNVar d) ℝ))
          (∑ i, fourierCoeff i ^ 4 - (1 - C K * X none)) 4,
        P.BitComplexityLE (K * (d + 1)) ∧
          ∀ S, ∀ m ∈ (P.mult S * SoS.System.prod (fknSystem (X none : MvPolynomial (FKNVar d) ℝ))
            S).support, m none ≠ 0 → m = Finsupp.single none 1) ∧
      ∀ (d b : ℕ) (q : MvPolynomial (FKNVar d) ℝ), q.totalDegree ≤ 2 →
        SoS.CoeffsLE q (2 ^ b) →
          SoS.DerivesWithin (fknSystem q) 4 (b + K * (d + 1))
            (∑ i, fourierCoeff i ^ 4 - (1 - C K * q)) :=
  sos_fkn_of_parts

/-- **Lemma 5.1** of [BMW26], spectral concentration of the percolated hypercube: with probability
at least `1 - 1/d^C₁`, there is a set `R` of at most `2^d / d^C₂` vertices such that
`|gᵀ (L' - p L) g| ≤ ε p gᵀ L g + d² ∑_{x ∈ R} (g x - ḡ)²` for every `g`. -/
theorem spectral_concentration :
    ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : ℝ, ∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ p : ℝ,
      C * Real.log d / d ≤ p → p ≤ 1 →
        1 - 1 / (d : ℝ) ^ C₁ ≤ percProb d p fun H ↦ ∃ R : Finset (Cube d),
          (R.card : ℝ) ≤ 2 ^ d / (d : ℝ) ^ C₂ ∧ ∀ g : Cube d → ℝ,
            |lapForm H g - p * lapForm (cube d) g| ≤
              ε * p * lapForm (cube d) g + (d : ℝ) ^ 2 * ∑ x ∈ R, (g x - (∑ y, g y) / 2 ^ d) ^ 2 :=
  spectral_concentration_of_parts

end BMW26
