module

public import ABBKS26.Assembly.ExecRefineSourcesAuxVariance
public import ABBKS26.Assembly.ExecRefineKernelsAuxFramePool

/-! Gaussian variance transfer for symmetric certificates in the paired frame pool. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobVariance

open Common _root_.ABBKS26.Tree Matrix
open Turing.MultiTapeTM ComputableInPolyTime


/-- A true paired flag identifies the same certificate and flag in the decoded frame,
even when the two raw lists have different lengths. -/
theorem paired_certificate {d : ℕ} (data : FrameData) (q : Statistic d)
    (hq : (q, true) ∈ FramePool.typed d data) :
    ∃ i : Fin (frameOf d data).certificates.length,
      (frameOf d data).eligible[i.val]? = some true ∧
      (frameOf d data).certificates[i] =
        FrameProgram.quadOf d (statisticList q) := by
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hp
  have hfirst : i < data.2.2.2.2.1.length := by
    exact (lt_min_iff.mp (List.length_zip ▸ hi)).1
  have hsecond : i < data.2.2.2.2.2.length := by
    exact (lt_min_iff.mp (List.length_zip ▸ hi)).2
  have hqeq : statisticOf d p.1 = q := congrArg Prod.fst heq
  have hflag : p.2 = true := congrArg Prod.snd heq
  have hc : data.2.2.2.2.1[i] = p.1 := by
    simpa only [List.getElem_zip] using congrArg Prod.fst hget
  have hf : data.2.2.2.2.2[i] = true := by
    simpa only [List.getElem_zip, hflag] using congrArg Prod.snd hget
  refine ⟨⟨i, by simpa only [frameOf, List.length_map] using hfirst⟩, ?_, ?_⟩
  · change data.2.2.2.2.2[i]? = some true
    rw [List.getElem?_eq_getElem hsecond, hf]
  · simp only [frameOf, Fin.getElem_fin, List.getElem_map, hc]
    rw [← hqeq]
    simp [FrameProgram.quadOf, statisticList, statisticOf]

/-- This is the genuine Gaussian bound for a symmetric eligible P1 certificate.
The input bound can be supplied directly by `FrameSpec.contract`. -/
theorem paired_variance {k d : ℕ} (F : FrameModel k d) (data : FrameData) (B : ℝ)
    (hcenter : ∀ j, F.mean j = 0) (hS : ∀ j, (F.cov j).PosSemidef)
    (hvalid : ∀ i : Fin (frameOf d data).certificates.length,
      (frameOf d data).eligible[i.val]? = some true →
      ∀ j, Robust.statVariance F j (frameOf d data).certificates[i] ≤ B ^ 2)
    (q : Statistic d) (hq : (q, true) ∈ FramePool.typed d data) (hsym : q.Aᵀ = q.A) :
    ∀ j, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 (F.cov j)) ≤ B ^ 2 := by
  obtain ⟨i, hi, heq⟩ := paired_certificate data q hq
  intro j
  rw [Variance.centered_variance_eq_statVariance F j (hcenter j) (hS j) q hsym,
    ← heq]
  exact hvalid i hi j

/-- The frame specification supplies rational symmetry at the original paired index. -/
theorem paired_symmetric (F : FrameCode) (hF : FrameSpec F) (mode : Mode)
    (a : FrameArgs × ℕ) (q : Statistic a.1.1)
    (hq : (q, true) ∈ FramePool.typed a.1.1 (F.run mode a)) : q.Aᵀ = q.A := by
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hq
  obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hp
  have hfirst : i < (F.run mode a).2.2.2.2.1.length :=
    (lt_min_iff.mp (List.length_zip ▸ hi)).1
  have hsecond : i < (F.run mode a).2.2.2.2.2.length :=
    (lt_min_iff.mp (List.length_zip ▸ hi)).2
  have hc : (F.run mode a).2.2.2.2.1[i]? = some p.1 := by
    rw [List.getElem?_eq_getElem hfirst]
    simpa only [List.getElem_zip] using congrArg (fun p ↦ some p.1) hget
  have hf : (F.run mode a).2.2.2.2.2[i]? = some true := by
    rw [List.getElem?_eq_getElem hsecond]
    simpa only [List.getElem_zip] using
      (congrArg (fun p ↦ some p.2) hget).trans (congrArg some (congrArg Prod.snd heq))
  have hs := hF.symmetric mode a i p.1 hc hf
  have he : statisticOf a.1.1 p.1 = q := congrArg Prod.fst heq
  rwa [he] at hs

/-- A specified frame's algebraic bound transfers to Gaussian variance with no additional
symmetry assumption on the caller. Missing or surplus flags are handled by the paired pool. -/
theorem specified_variance {k : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (mode : Mode) (a : FrameArgs × ℕ) (M : FrameModel k a.1.1) (B : ℝ)
    (hcenter : ∀ j, M.mean j = 0) (hS : ∀ j, (M.cov j).PosSemidef)
    (hvalid : ∀ i : Fin (frameOf a.1.1 (F.run mode a)).certificates.length,
      (frameOf a.1.1 (F.run mode a)).eligible[i.val]? = some true →
      ∀ j, Robust.statVariance M j
        (frameOf a.1.1 (F.run mode a)).certificates[i] ≤ B ^ 2)
    (q : Statistic a.1.1) (hq : (q, true) ∈ FramePool.typed a.1.1 (F.run mode a)) :
    ∀ j, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin a.1.1) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 (M.cov j)) ≤ B ^ 2 := by
  exact paired_variance M _ B hcenter hS hvalid q hq
    (paired_symmetric F hF mode a q hq)

/-- Every eligible decoded index occurs in the paired pool with its original flag. -/
theorem certificate_paired {d : ℕ} (data : FrameData)
    (i : Fin (frameOf d data).certificates.length)
    (hi : (frameOf d data).eligible[i.val]? = some true) :
    ∃ q : Statistic d, (q, true) ∈ FramePool.typed d data ∧
      (frameOf d data).certificates[i] =
        FrameProgram.quadOf d (statisticList q) := by
  have hfirst : i.val < data.2.2.2.2.1.length := by
    simpa only [frameOf, List.length_map] using i.isLt
  obtain ⟨hsecond, hf⟩ := List.getElem?_eq_some_iff.mp hi
  let p := data.2.2.2.2.1[i.val]
  have hmem : (p, true) ∈ data.2.2.2.2.1.zip data.2.2.2.2.2 := by
    apply List.mem_iff_getElem.mpr
    refine ⟨i.val, by simp only [List.length_zip]; exact lt_min hfirst hsecond, ?_⟩
    simp only [List.getElem_zip]
    exact Prod.ext rfl hf
  refine ⟨statisticOf d p, List.mem_map.mpr ⟨(p, true), hmem, rfl⟩, ?_⟩
  change (frameOf d data).certificates[i.val] = _
  simp [frameOf, FrameProgram.quadOf, statisticList, statisticOf, p]

/-- The FAR certificate of any specified frame has the advertised Gaussian variance.
This uses the variance bound recorded by FAR itself and preserves its exact center gap. -/
theorem far_certificate {n k : ℕ} (F : FrameCode) (hF : FrameSpec F) (mode : Mode)
    (a : FrameArgs × ℕ) (D : Robust.Reference n k a.1.1) (R B : ℝ)
    (hcenter : ∀ j, D.model.mean j = 0) (hS : ∀ j, (D.model.cov j).PosSemidef)
    (hfar : Robust.Far D (frameOf a.1.1 (F.run mode a)) R B) :
    ∃ q : Statistic a.1.1, (q, true) ∈ FramePool.typed a.1.1 (F.run mode a) ∧
      (∀ j, ProbabilityTheory.variance
        (fun y : EuclideanSpace ℝ (Fin a.1.1) ↦ q.eval y.ofLp)
        (ProbabilityTheory.multivariateGaussian 0 (D.model.cov j)) ≤ B ^ 2) ∧
      ∃ i j, R ≤ |Robust.statCenter D.model i
        (FrameProgram.quadOf a.1.1 (statisticList q)) -
          Robust.statCenter D.model j (FrameProgram.quadOf a.1.1 (statisticList q))| := by
  obtain ⟨i, hi, j, l, hgap, hvar⟩ := hfar
  obtain ⟨q, hq, heq⟩ := certificate_paired _ i hi
  refine ⟨q, hq, ?_, j, l, ?_⟩
  · intro j
    rw [Variance.centered_variance_eq_statVariance D.model j (hcenter j) (hS j) q
      (paired_symmetric F hF mode a q hq), ← heq]
    exact hvar j
  · rwa [heq] at hgap


end ABBKS26.Assembly.Exec.RefineSynth.FrobVariance
