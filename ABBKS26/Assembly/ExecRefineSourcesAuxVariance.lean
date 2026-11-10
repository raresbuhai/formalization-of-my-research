module

public import ABBKS26.Assembly.ExecRefineKernelsAuxSources

/-! The variance identity needed when transferring eligible frame certificates. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.Variance

open Common _root_.ABBKS26.Tree Matrix

/-- For a symmetric rational certificate, the algebraic centered variance is the actual
Gaussian variance. The constant term does not affect this identity. -/
theorem centered_variance_eq {d : ℕ} (q : Statistic d) (hA : q.Aᵀ = q.A)
    (S : Mat d) (hS : S.PosSemidef) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) =
        2 * (q.A.map (algebraMap ℚ ℝ) * S * q.A.map (algebraMap ℚ ℝ) * S).trace +
          qform S (fun i ↦ (q.b i : ℝ)) := by
  have hsym : (q.A.map (algebraMap ℚ ℝ)).IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map, hA]
  have heval : (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp) =
      Population.quadStat (q.A.map (algebraMap ℚ ℝ)) (fun i ↦ (q.b i : ℝ)) q.c := by
    funext y
    simp only [Statistic.eval, Population.quadStat, qform]
  rw [heval, Population.variance_quadStat_multivariateGaussian hS hsym]
  simp only [Matrix.mul_assoc, qform]

/-- This is the transfer from a decoded frame certificate when symmetry is available. -/
theorem centered_variance_eq_statVariance {k d : ℕ} (F : FrameModel k d)
    (j : Fin k) (hj : F.mean j = 0) (hS : (F.cov j).PosSemidef)
    (q : Statistic d) (hA : q.Aᵀ = q.A) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 (F.cov j)) =
        Robust.statVariance F j (FrameProgram.quadOf d (statisticList q)) := by
  rw [centered_variance_eq q hA _ hS]
  simp [Robust.statVariance, FrameProgram.quadOf, statisticList, hj,
    matrix_roundtrip, vector_roundtrip]


end ABBKS26.Assembly.Exec.RefineSynth.Variance
