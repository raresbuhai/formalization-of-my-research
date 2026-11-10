module

public import ABBKS26.Assembly.RunTime

/-!
# Proofs of Theorems 5.2 and 6.2

`clustering_main` combines the deterministic recovery theorem, the probability of the good
event and the running time for both kinds of mixtures; `centered_clustering_main` and
`identical_covariance_clustering_main` have exactly the types of the two theorems of
`ABBKS26/Challenge.lean`.
-/

@[expose] public section

namespace ABBKS26.Main

noncomputable section


open Matrix

open Common _root_.ABBKS26.Tree MeasureTheory

/-- Probability and time assembly, shared by the two frozen statements. -/
theorem clustering_main (mode : Mode) :
    ∃ (A : Input × List Bool → Output) (C : ℕ) (g : ℕ → ℕ → ℕ) (f : ℝ → ℝ),
      1 ≤ C ∧ (∀ x, 1 ≤ f x) ∧ Computable₂ g ∧
      RunsInTime encInput encOutput A (Assembly.time mode g C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin Δ δ : ℚ), M.Valid → mode.Condition M →
        0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) → f (1 / wmin) ≤ Δ →
        mode.Separated M Δ → 0 < δ →
        ∀ (ε : ℝ) (P : Measure (Triple k d)),
          0 ≤ ε → ε ≤ 1 / f (1 / wmin) → IsCorruption M ε P →
        ∀ n : ℕ, Schedule.sampleBound mode C k d wmin Δ δ ≤ n →
        ∀ r : Rounding k d, IsRounding M (1 / n) r →
          1 - δ ≤ successProb P n r (fun pts ↦ ⟨k, wmin, Δ, δ, pts⟩) A
            (Assembly.time mode g C)
            (RecoversClusters (C * k / wmin *
              max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))) := by
  obtain ⟨Cs, hCs, hsamples⟩ := Schedule.exists_sampleExponent mode
  obtain ⟨budget, Ct, g, hg, htime, hbudget⟩ := Assembly.exists_runtime mode
  let C := max 32 (max Cs Ct)
  have hC32 : 32 ≤ C := le_max_left _ _
  have hCsC : Cs ≤ C := (le_max_left Cs Ct).trans (le_max_right _ _)
  have hCtC : Ct ≤ C := (le_max_right Cs Ct).trans (le_max_right _ _)
  refine ⟨Assembly.algorithm mode budget, C, g, Schedule.f mode, by omega,
    Schedule.f_ge_one mode, hg, Assembly.runtime_mono mode _ g Ct C hCtC htime, ?_⟩
  intro k d M w Δ δ hM hm hw hwj hΔ hs hδ ε P he he' hP n hn r hr
  have : IsProbabilityMeasure P := hP.isProbabilityMeasure hM
  by_cases hδ1 : (δ : ℝ) < 1
  · have hready := hsamples C k d n M w Δ δ hCsC hM hw hwj hΔ hδ hδ1 hn
    let η := Schedule.analysisEta mode w Δ k
    let D := Schedule.momentDegree mode w
    have hsetup := Assembly.probability_setup mode M w Δ δ ε P hM hw hwj hΔ hδ hδ1
      he he' hP n hready
    apply one_sub_le_successProb r (fun pts ↦ ⟨k, w, Δ, δ, pts⟩)
      (Assembly.algorithm mode budget) (Assembly.time mode g C)
      (RecoversClusters (C * k / w * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k))))))
      (G := {ω | Good M ε w η D ω}) (measurable_good M ε w η D) hsetup
    intro ω hω coins
    exact Assembly.deterministic mode budget hbudget C hC32 M w Δ δ hM hm hw hwj hΔ
      hs hδ ε he he' hready r hr ω hω coins
  · have hδge : (1 : ℝ) ≤ δ := le_of_not_gt hδ1
    exact (sub_nonpos.mpr hδge).trans ENNReal.toReal_nonneg

theorem centered_clustering_main :
    ∃ (A : Input × List Bool → Output) (C : ℕ) (g : ℕ → ℕ → ℕ) (f : ℝ → ℝ),
      1 ≤ C ∧ (∀ x, 1 ≤ f x) ∧ Computable₂ g ∧
      RunsInTime encInput encOutput A (centeredTime g C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin Δ δ : ℚ), M.Valid → M.IsCentered →
        0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) → f (1 / wmin) ≤ Δ →
        (∀ a b, a ≠ b → CenteredSeparated Δ (M.S a) (M.S b)) → 0 < δ →
        ∀ (ε : ℝ) (P : Measure (Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))),
          0 ≤ ε → ε ≤ 1 / f (1 / wmin) → IsCorruption M ε P →
        ∀ n : ℕ, ((d + 1) * (Δ + 1) / ((wmin : ℝ) * δ)) ^ C ≤ n →
        ∀ r : Rounding k d, IsRounding M (1 / n) r →
          1 - δ ≤ successProb P n r (fun pts ↦ ⟨k, wmin, Δ, δ, pts⟩) A (centeredTime g C)
            (RecoversClusters (C * k / wmin * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))) := by
  simpa only [Common.Mode.Condition, Common.Mode.Separated, Assembly.time,
    Schedule.sampleBound] using clustering_main Common.Mode.centered

theorem identical_covariance_clustering_main :
    ∃ (A : Input × List Bool → Output) (C : ℕ) (g : ℕ → ℕ → ℕ) (f : ℝ → ℝ),
      1 ≤ C ∧ (∀ x, 1 ≤ f x) ∧ Computable₂ g ∧
      RunsInTime encInput encOutput A (identicalCovTime g C) ∧
      ∀ (k d : ℕ) (M : Mixture k d) (wmin Δ δ : ℚ), M.Valid → M.HasIdenticalCovariances →
        0 < wmin → (∀ i, (wmin : ℝ) ≤ M.w i) → f (1 / wmin) ≤ Δ →
        (∀ a b, a ≠ b → MeanSeparated Δ (M.μ a) (M.μ b) (M.S a)) → 0 < δ →
        ∀ (ε : ℝ) (P : Measure (Fin k × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))),
          0 ≤ ε → ε ≤ 1 / f (1 / wmin) → IsCorruption M ε P →
        ∀ n : ℕ,
          ((d + 1) / (wmin : ℝ)) ^ (C * (Real.log (1 / wmin) + 1)) * ((Δ + 1) / (δ : ℝ)) ^ C ≤ n →
        ∀ r : Rounding k d, IsRounding M (1 / n) r →
          1 - δ ≤ successProb P n r (fun pts ↦ ⟨k, wmin, Δ, δ, pts⟩) A (identicalCovTime g C)
            (RecoversClusters (C * k / wmin * max ε ((Δ : ℝ) ^ (-(1 / ((C : ℝ) * k)))))) := by
  simpa only [Common.Mode.Condition, Common.Mode.Separated, Assembly.time,
    Schedule.sampleBound] using clustering_main Common.Mode.identical

end

end ABBKS26.Main
