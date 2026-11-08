module

public import BHJK25.Spectral.LDA
public import BHJK25.Spectral.Prob
public import BHJK25.Spectral.Tail
public import BHJK25.Spectral.Alg

/-!
# Theorem 3.1

Assembly of [BHJK25, Theorem 3.1] (`BHJK25.top_eigenvalue_counterexample` in `Challenge.lean`):
the algorithm (`BHJK25.Spectral.specAlg`), the distributions (`BHJK25.Spectral.Prob`), the
low-degree bound (`BHJK25.Spectral.lda`), and the eigenvalue of the noisy planted matrix
(`BHJK25.Spectral.noisy_spike`).
-/

@[expose] public section

namespace BHJK25

open Matrix Filter

theorem ProbAtLeast.mono {α : Type} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {p : ℝ}
    {Good Good' : α → Prop} (h : ProbAtLeast μ p Good) (hG : ∀ x, Good x → Good' x) :
    ProbAtLeast μ p Good' := by
  obtain ⟨E, hE, hp, hgood⟩ := h
  exact ⟨E, hE, hp, fun x hx ↦ hG x (hgood x hx)⟩

open Spectral in
theorem top_eigenvalue_main :
    ∃ (A : RatMatrix → Bool) (c : ℕ),
      RunsInTime encRatMatrix Encoding.encBool A (fun x ↦ ((encRatMatrix x).length + 2) ^ c) ∧
      ∀ C : ℝ, 0 < C →
        (∀ n, MeasureTheory.IsProbabilityMeasure (nullAt C n) ∧
          MeasureTheory.IsProbabilityMeasure (plantedAt C n) ∧
          RotationInvariant (nullAt C n) ∧ RotationInvariant (plantedAt C n)) ∧
        (∀ b : ℕ, ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
          AdvantageAtMost entries ((n : ℝ) ^ (1 / 3 : ℝ) / Real.log n ^ a) (plantedAt C n)
            (nullAt C n) (1 / Real.log n ^ b)) ∧
        (∀ n, ProbAtLeast (nullAt C n) 1 fun M ↦ ∀ X, Approximates X M → A ⟨n, X⟩ = false) ∧
        ∀ ε : ℝ, 0 ≤ ε → ε < 1 → ∀ e : ℕ, ∀ᶠ n : ℕ in atTop,
          ProbAtLeast (noisyLaw ε (plantedAt C n) (nullAt C n)) (1 - 1 / (n : ℝ) ^ e) fun M ↦
            ∀ X, Approximates X M → A ⟨n, X⟩ = true := by
  obtain ⟨c, hc⟩ := specAlg_runsInTime
  refine ⟨specAlg, c, hc, fun C hC ↦ ⟨fun n ↦ ⟨isProbabilityMeasure_nullAt hC.le n,
    isProbabilityMeasure_plantedAt hC.le n, rotationInvariant_nullAt C n,
    rotationInvariant_plantedAt C n⟩, fun b ↦ lda hC b, fun n ↦ ?_, fun ε hε0 hε1 e ↦ ?_⟩⟩
  · exact (null_nsd hC.le n).mono fun M hM X hX ↦ specAlg_eq_false hM.1 hM.2 hX
  · filter_upwards [noisy_spike hC hε0 hε1 e] with n hn
    exact hn.mono fun M hM X hX ↦ specAlg_eq_true hM.1 hM.2 hX

end BHJK25
