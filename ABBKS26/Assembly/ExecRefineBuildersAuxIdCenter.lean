module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdCoverage

/-! Executable common-covariance centers from the rational quadratic filter. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdCenter

open Common Matrix FrameAux FrameAux.Linear FrameAux.Features
open _root_.ABBKS26.Tree Sources Builders FrameProgram
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

variable {n k d : ℕ}

/-- This call uses the concrete filter, whose clean-state invariant controls its center. -/
def run (a : Builders.Args) : FrameProgram.DataL :=
  FrameProgram.run .identical (FrobFar.callArgs a)

theorem run_polytime : ComputableInPolyTime run Builders.encArgs
    FrameProgram.encDataL :=
  (FrameProgram.rounded_frame_polytime .identical).comp FrobFar.callArgs_polytime

noncomputable section

private theorem powerTrace_real (pts : Points) (idx : Fin pts.length → Fin n)
    (w : Vector) (p : ℕ) :
    (powerTrace (d * d) p (iterationCov d pts w) : ℝ) =
      ((liftState idx d pts w).featureCov ^ p).trace := by
  have hp := power_reindex_real d p (iterationCov d pts w)
  have hcov : reindexRingEquiv ℝ finProdFinEquiv.symm
      ((matrixOf (d * d) (iterationCov d pts w)).map (algebraMap ℚ ℝ)) =
        (liftState idx d pts w).featureCov := by
    ext a b
    simp only [coe_reindexRingEquiv, reindex_apply, Equiv.symm_symm, submatrix_apply,
      Matrix.map_apply, eq_ratCast, liftState]
  rw [hcov] at hp
  have ht : ((liftState idx d pts w).featureCov ^ p).trace =
      ((matrixOf (d * d) (power (d * d) p (iterationCov d pts w))).map
        (algebraMap ℚ ℝ)).trace := by
    rw [← hp]
    simp only [Matrix.trace, coe_reindexRingEquiv, reindex_apply, Equiv.symm_symm]
    exact (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).sum_comp
      (fun i ↦ ((matrixOf (d * d) (power (d * d) p (iterationCov d pts w))).map
        (algebraMap ℚ ℝ)) i i)
  rw [ht]
  have hcast := AddMonoidHom.map_trace (algebraMap ℚ ℝ)
    (matrixOf (d * d) (power (d * d) p (iterationCov d pts w)))
  rw [matrixOf_power_real] at hcast
  rw [powerTrace_eq]
  simpa only [matrixOf_power, Matrix.map_pow, eq_ratCast] using hcast

private theorem passed_agrees (pts : Points) (idx : Fin pts.length → Fin n)
    (π R : ℚ) (w : Vector) :
    Passed d pts π R w ↔ Robust.Pass (liftState idx d pts w) π R := by
  unfold Passed Robust.Pass Robust.sigmaSq
  rw [← powerTrace_real pts idx w]
  norm_cast


/-- Common covariance rules out the first type-B state of the executable filter. -/
theorem clean_pass (D : Robust.Reference n k d) (pts : Points)
    (π R ζ : ℚ) (fuel : ℕ) (hrep : Robust.Represents D pts) (hD : D.Valid π)
    (hres : D.Resilient 4 (min (1 / 10 ^ 8) ((ζ : ℝ) ^ 2 / 10 ^ 8)))
    (hπ : 0 < π) (hπ1 : π ≤ 1 / 2) (hR : 0 ≤ R) (hζ : 0 < ζ)
    (he : D.contamination ≤ min (Robust.maxContamination π R) ((π : ℝ) / 400))
    (hn : 2 / Robust.maxContamination π R ≤ (pts.length : ℝ))
    (hf : (pts.length + d + 2) ^ 100 ≤ fuel)
    (hid : ∀ i j, D.model.cov i = D.model.cov j) :
    ∃ idx : Fin pts.length → Fin n,
      let result := loop d pts π R fuel pts.length (List.replicate pts.length 1)
      Clean D idx π result.2.2 ∧ result.1 = true ∧
        Robust.Pass (liftState idx d pts result.2.2) π R := by
  obtain ⟨idx, _, _, hc⟩ := rounded_loop_invariant D pts π R ζ fuel
    hrep hD hres hπ hπ1 hR hζ he hn hf
  rcases hc with ⟨w, hw, hc, _, hb⟩ | hc
  · have hfail := (rounded_loop_bound d pts π R fuel pts.length
      (List.replicate pts.length 1)).2 w hw |>.2
    let st := liftState idx d pts w
    have hl := Robust.covariance_lower D st π R hc.invariant hc.normalized he
    have hM : LE (st.frame * D.cov * st.frameᵀ) (6 • (1 : Mat d)) := by
      intro v
      obtain ⟨q, hq, hframe⟩ := hc.normalized.1
      have hC : qform (st.frame * Robust.weightedCov D st * st.frameᵀ) v ≤
          4 * sqnorm v := by
        rw [hframe]
        simp only [qform, mulVec_diagonal, sqnorm, dotProduct, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        nlinarith only [mul_le_mul_of_nonneg_right (hq i).2.le (sq_nonneg (v i))]
      have hv := hl v
      simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul,
        nsmul_eq_mul, Matrix.mul_one, Nat.cast_ofNat, Matrix.ofNat_mulVec] at hv ⊢
      change qform (st.frame * D.cov * st.frameᵀ) v ≤ 6 * sqnorm v
      change (0.68 : ℝ) * qform (st.frame * D.cov * st.frameᵀ) v ≤
        qform (st.frame * Robust.weightedCov D st * st.frameᵀ) v at hv
      linarith only [hv, hC, Rounding.DetRoundAux.sqnorm_nonneg v]
    obtain ⟨j, _, hbet⟩ := Robust.typeB_candidate D st π R hc.invariant hc.normalized he
      (fun hp ↦ hfail ((passed_agrees pts idx π R w).mpr hp)) hb
    have hlt := ABBKS26.RefineAux.identical_between_lt_sigma D π R
      hc.invariant.1 hc.invariant.2.1 hid st.frame
      (Robust.RBAux.FrameLoop.normalizedColumn st.featureCov st.power j)
      (Robust.RBAux.FrameLoop.normalizedColumn_norm _ _ _) hM
    exact (not_le_of_gt hlt hbet).elim
  · exact ⟨idx, hc⟩

/-- A covariance upper bound transports a Mahalanobis mean estimate to any chosen frame. -/
theorem mean_transport (S T : Mat d) (hS : S.PosDef) (y : Vec d) (c e : ℝ)
    (hc : LE (T * S * Tᵀ) (c • (1 : Mat d)))
    (he : sqNormIn S y ≤ e) (hc0 : 0 ≤ c) (he0 : 0 ≤ e) :
    sqnorm (T *ᵥ y) ≤ c * e := by
  let z := T *ᵥ y
  have hinv : S * S⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
  have hh := hS.star_dotProduct_mulVec_mul_le (Tᵀ *ᵥ z) (S⁻¹ *ᵥ y)
  simp only [star_trivial, mulVec_mulVec, hinv, one_mulVec] at hh
  have hdot : (Tᵀ *ᵥ z) ⬝ᵥ y = sqnorm z := by
    change _ = z ⬝ᵥ (T *ᵥ y)
    rw [dotProduct_mulVec, ← mulVec_transpose]
  have hb := hc z
  rw [Robust.RBAux.qform_conjugate] at hb
  simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hb
  change qform S (Tᵀ *ᵥ z) ≤ c * sqnorm z at hb
  have hm : 0 ≤ sqNormIn S y := by
    simpa only [sqNormIn, star_trivial] using hS.inv.posSemidef.dotProduct_mulVec_nonneg y
  have hq : 0 ≤ qform S (Tᵀ *ᵥ z) := by
    simpa only [qform, star_trivial] using hS.posSemidef.dotProduct_mulVec_nonneg (Tᵀ *ᵥ z)
  have hshift : sqnorm z ^ 2 ≤ sqNormIn S y * qform S (Tᵀ *ᵥ z) := by
    simpa only [hdot, sqnorm, qform, sqNormIn, dotProduct_comm, pow_two, mul_comm,
      mulVec_mulVec] using hh
  have hn := Rounding.DetRoundAux.sqnorm_nonneg z
  have hbound := mul_le_mul he hb hq he0
  change sqnorm z ≤ c * e
  nlinarith only [hshift, hbound, hn, mul_nonneg hc0 he0]

/-- The same rational center is accurate in every sufficiently whitened compatible frame. -/
theorem center_bound (D : Robust.Reference n k d) (pts : Points)
    (π R ζ : ℚ) (fuel : ℕ) (hrep : Robust.Represents D pts) (hD : D.Valid π)
    (hres : D.Resilient 4 (min (1 / 10 ^ 8) ((ζ : ℝ) ^ 2 / 10 ^ 8)))
    (hπ : 0 < π) (hπ1 : π ≤ 1 / 2) (hR : 0 ≤ R) (hζ : 0 < ζ)
    (he : D.contamination ≤ min (Robust.maxContamination π R) ((π : ℝ) / 400))
    (hn : 2 / Robust.maxContamination π R ≤ (pts.length : ℝ))
    (hf : (pts.length + d + 2) ^ 100 ≤ fuel)
    (hid : ∀ i j, D.model.cov i = D.model.cov j)
    (T : Mat d) (hT : LE (T * D.cov * Tᵀ) ((1.01 : ℝ) • (1 : Mat d))) :
    let Y := decode d (FrameProgram.run .identical ((d, pts, π, R, ζ), fuel))
    Robust.CloseFrame D Y π R ζ ∧
      sqnorm (T *ᵥ ((fun i ↦ (Y.center i : ℝ)) - D.mean)) ≤
        400 * D.contamination := by
  obtain ⟨idx, hc, hp, hpass⟩ := clean_pass D pts π R ζ fuel
    hrep hD hres hπ hπ1 hR hζ he hn hf hid
  rw [rounded_frame_agrees]
  dsimp only
  refine ⟨⟨hp, ?_⟩, ?_⟩
  · exact normalizedL_pass D _ π R _ ζ hc.positive hζ hc.covariance_agrees
      (by rw [liftState, iterationFrame, matrixOf_whitenL]) hc.invariant hc.normalized he hpass
  · have hm := (Robust.pass_accuracy D _ π R hc.invariant hc.normalized he hpass).2.2.2
    have hnonneg : 0 ≤ D.contamination := by
      unfold Robust.Reference.contamination
      positivity
    have hb := mean_transport D.cov T hD.2.2.2.2.2.1 _ 1.01
      (370 * D.contamination) hT hm (by norm_num) (by positivity)
    exact hb.trans (by nlinarith only [hnonneg])

end

end ABBKS26.Assembly.Exec.RefineSynth.IdCenter
