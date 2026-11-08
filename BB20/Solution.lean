module

public import BB20.Model
public import BB20.Structural
public import BB20.Prediction
public import BB20.Learning.Correct
public import BB20.Machine.Threshold
public import BB20.Machine.Time

/-!
# Results: proofs

The statements of `BB20/Challenge.lean`, proved. `lake comparator` checks that they are the same
statements and that the proofs use only the axioms listed in `comparator.json`.

* Theorem 4: `BB20.Structural.nuSubsetBound` (`BB20/Structural/`).
* Theorems 6 and 11: the algorithms `BB20.alg6` and `BB20.alg11` (`BB20/Learning/Algorithm.lean`)
  with threshold functions from `BB20.Machine.exists_thr6` and `BB20.Machine.exists_thr11`; their
  correctness is `BB20.Learning.alg6_correct` and `BB20.Learning.alg11_correct`, and their running
  time `BB20.Machine.alg6_runsInTime` and `BB20.Machine.alg11_runsInTime`.
* Theorem 12: `BB20.Prediction.predictionError` (`BB20/Prediction/`).
-/

public section

namespace BB20

theorem nu_subset_bound {n m : ℕ} (R : RBM n m) (s : ℕ) (hs : R.SparsityLE s) (u : Fin n)
    (I S : Finset (Fin n)) (hI : I ⊆ R.nbhd u) (hu : u ∉ S) (hIS : Disjoint I S) :
    ∃ I' ⊆ I, I'.card ≤ 2 ^ s ∧
      R.nu u I S / ((4 * I.card : ℝ) ^ 2 ^ s * (I.card : ℝ) ^ (2 ^ s * (2 ^ s + 1))) ≤
        R.nu u I' S :=
  Structural.nuSubsetBound R s hs u I S hI hu hIS

theorem structure_learning :
    ∃ (A : Input → Output) (c : ℕ), RunsInTime encInput encOutput A (learnTime c) ∧
      ∀ (n m : ℕ) (R : RBM n m) (α γ : ℚ) (d D s : ℕ), 0 < α → 0 < γ → 1 ≤ d →
        R.MinCoeffGE α → R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → R.SparsityLE s →
        ∀ (ω : ℝ) (M : ℕ), 0 < ω → sampleSize α γ d D s n ω ≤ M →
          1 - ω ≤ R.sampleProb M fun X ↦ R.Recovers (A ⟨n, sampleList X, α, γ, d, D, s⟩) := by
  obtain ⟨thr, hspec, hpoly⟩ := Machine.exists_thr6
  obtain ⟨c, hc⟩ := Machine.alg6_runsInTime thr hpoly
  exact ⟨alg6 thr, c, hc, fun n m R α γ d D s hα hγ hd hmin hW hL hDeg hs ω M hω hM ↦
    Learning.alg6_correct thr hspec n m R α γ d D s hα hγ hd hmin hW hL hDeg hs ω M hω hM⟩

theorem structure_learning_strong :
    ∃ (A : Input → Output) (c : ℕ), RunsInTime encInput encOutput A (learnTime c) ∧
      ∀ (n m : ℕ) (R : RBM n m) (ζ γ : ℚ) (d D s : ℕ), 0 < ζ → 0 < γ → 1 ≤ d → 1 ≤ D →
        R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → R.SparsityLE s →
        ∀ (ω : ℝ) (M : ℕ), 0 < ω → sampleSize (ζ * eta γ D s) γ d D s n ω ≤ M →
          1 - ω ≤ R.sampleProb M fun X ↦
            R.RecoversStrong ζ (A ⟨n, sampleList X, ζ, γ, d, D, s⟩) := by
  obtain ⟨thr, hspec, hpoly⟩ := Machine.exists_thr11
  obtain ⟨c, hc⟩ := Machine.alg11_runsInTime thr hpoly
  exact ⟨alg11 thr, c, hc, fun n m R ζ γ d D s hζ hγ hd hD hW hL hDeg hs ω M hω hM ↦
    Learning.alg11_correct thr hspec n m R ζ γ d D s hζ hγ hd hD hW hL hDeg hs ω M hω hM⟩

theorem prediction_error :
    ∃ C : ℝ, ∀ (n m : ℕ) (R : RBM n m) (γ : ℝ) (d D : ℕ) (ζ ε δ : ℝ),
      R.WidthLE γ → R.LatentDegreeLE d → R.DegreeLE D → 0 < ζ → 0 < ε → 0 < δ →
      ζ ≤ Real.sqrt ε / ((D : ℝ) ^ d * Real.sqrt (1 + Real.exp (2 * γ))) →
      ∀ nb : Fin n → Finset (Fin n),
        (∀ u, u ∉ nb u ∧ (nb u).card ≤ D ∧ R.strongNbhd ζ u ⊆ nb u) →
      ∀ M : ℕ, C * γ ^ 2 * Real.log (8 * n * 2 ^ D / δ) / ε ^ 2 ≤ M →
        1 - δ ≤ R.sampleProb M fun X ↦ ∀ (u : Fin n) (w : Finset (Fin n) → ℝ),
          IsNearMinimizer γ (ε / 4) u (nb u) X w → R.predError u (nb u) w ≤ ε :=
  Prediction.predictionError

end BB20
