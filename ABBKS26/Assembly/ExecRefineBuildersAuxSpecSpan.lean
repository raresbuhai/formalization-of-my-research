module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecBasis

/-! The rational basis normalization preserves the rounder's subspace. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecSpan

open Common Matrix
open scoped BigOperators

noncomputable section

def rowSpan {r d : ℕ} (C : Matrix (Fin r) (Fin d) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  Submodule.span ℝ (Set.range fun i ↦ WithLp.toLp 2 (C i))

theorem mul_row {r s d : ℕ} (H : Matrix (Fin r) (Fin s) ℝ)
    (C : Matrix (Fin s) (Fin d) ℝ) (i : Fin r) :
    WithLp.toLp 2 ((H * C) i) = ∑ j, H i j • WithLp.toLp 2 (C j) := by
  ext c
  simp [Matrix.mul_apply]

theorem mul_span_le {r s d : ℕ} (H : Matrix (Fin r) (Fin s) ℝ)
    (C : Matrix (Fin s) (Fin d) ℝ) : rowSpan (H * C) ≤ rowSpan C := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change WithLp.toLp 2 ((H * C) i) ∈ rowSpan C
  rw [mul_row]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem mul_span_eq {r d : ℕ} (H : Mat r) (C : Matrix (Fin r) (Fin d) ℝ)
    (hH : H.det ≠ 0) : rowSpan (H * C) = rowSpan C := by
  apply le_antisymm (mul_span_le H C)
  have he : H⁻¹ * (H * C) = C := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hH),
      Matrix.one_mul]
  have hh := mul_span_le H⁻¹ (H * C)
  rwa [he] at hh

/-- Positive diagonal Gram entries imply that normalization is invertible, including
the empty basis. Consequently it cannot discard any of the rounder's range. -/
theorem normalized_span (d : ℕ) (B : Points) (ζ : ℚ)
    (hB : ((SpecBasis.rows d B * (SpecBasis.rows d B)ᵀ).map
      (algebraMap ℚ ℝ)).PosDef) :
    let C := (SpecBasis.rows d B).map (algebraMap ℚ ℝ)
    let H := (matrixOf B.length
      (FrameAux.Linear.normalizedL B.length (RoundProgram.gram d B) ζ)).map
        (algebraMap ℚ ℝ)
    rowSpan (H * C) = rowSpan C := by
  dsimp only
  apply mul_span_eq
  obtain ⟨q, hq, he⟩ := SpecBasis.normalized_diagonal d B ζ hB
  have hp : (diagonal q).PosDef := posDef_diagonal_iff.mpr hq
  let C := (SpecBasis.rows d B).map (algebraMap ℚ ℝ)
  let H := (matrixOf B.length
    (FrameAux.Linear.normalizedL B.length (RoundProgram.gram d B) ζ)).map
      (algebraMap ℚ ℝ)
  have heq : H * (C * Cᵀ) * Hᵀ = diagonal q := by
    calc
      _ = (H * C) * (H * C)ᵀ := by
        rw [transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = _ := by simpa only [H, C, Matrix.map_mul] using he
  have hd := hp.det_pos.ne'
  rw [← heq, det_mul, det_mul, det_transpose] at hd
  change H.det ≠ 0
  intro hz
  apply hd
  rw [hz]
  ring

theorem transpose_mulVec_mem {r d : ℕ} (C : Matrix (Fin r) (Fin d) ℝ)
    (w : Fin r → ℝ) : WithLp.toLp 2 (Cᵀ *ᵥ w) ∈ rowSpan C := by
  have he : WithLp.toLp 2 (Cᵀ *ᵥ w) = ∑ j, w j • WithLp.toLp 2 (C j) := by
    ext c
    simp [Matrix.mulVec, dotProduct, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem projector_mem {d : ℕ} (Y : List (Fin d → ℚ)) (v : Vec d)
    (hv : InRange (projector Y) v) :
    WithLp.toLp 2 v ∈ rowSpan (fun (i : Fin Y.length) c ↦ (Y[i] c : ℝ)) := by
  let C : Matrix (Fin Y.length) (Fin d) ℝ := fun i c ↦ (Y[i] c : ℝ)
  have he : Cᵀ *ᵥ ((C * Cᵀ)⁻¹ *ᵥ (C *ᵥ v)) = v := by
    rw [mulVec_mulVec, mulVec_mulVec]
    exact hv
  rw [← he]
  exact transpose_mulVec_mem C _

theorem normalized_row (d : ℕ) (B : Points) (ζ : ℚ)
    (i : Fin (SpecBasis.run d B ζ).length) :
    let H := matrixOf B.length
      (FrameAux.Linear.normalizedL B.length (RoundProgram.gram d B) ζ)
    SpecNetGrid.row d (SpecBasis.run d B ζ) i =
      WithLp.toLp 2 (((H * SpecBasis.rows d B).map (algebraMap ℚ ℝ))
        (Fin.cast (SpecBasis.length_run d B ζ) i)) := by
  ext c
  have hr := SpecBasis.combine_agrees d B
    (FrameAux.Linear.normalizedL B.length (RoundProgram.gram d B) ζ)
      (Fin.cast (SpecBasis.length_run d B ζ) i) c
  have he := congrArg (algebraMap ℚ ℝ) hr
  change (((SpecBasis.run d B ζ).getD i.val []).getD c.val 0 : ℝ) = _ at he
  change (((SpecBasis.run d B ζ)[i]).getD c.val 0 : ℝ) = _
  simpa only [List.getD_eq_getElem _ _ i.isLt, Fin.getElem_fin, Matrix.map_apply] using he

/-- The executable normalized grid covers the entire range of the original basis. -/
theorem normalized_covers {d D fuel : ℕ} (α ζ : ℚ) (B : Points)
    (hB : ((SpecBasis.rows d B * (SpecBasis.rows d B)ᵀ).map
      (algebraMap ℚ ℝ)).PosDef)
    (hD : B.length ≤ D) (hD0 : 0 < D) (hα : 0 < α ∧ α ≤ 1 / 100)
    (hζ : 0 < ζ) (hζα : (ζ : ℝ) ≤ (α : ℝ) / (8 * D))
    (hf : (2 * ⌈8 * (D : ℚ) / α⌉₊ + 1) ^ B.length ≤ fuel)
    (v : Vec d) (hvS : WithLp.toLp 2 v ∈
      rowSpan ((SpecBasis.rows d B).map (algebraMap ℚ ℝ))) (hv : sqnorm v = 1) :
    ∃ q ∈ SpecNetGrid.run d ⌈8 * (D : ℚ) / α⌉₊ fuel (SpecBasis.run d B ζ),
      ‖WithLp.toLp 2 (fun c : Fin d ↦ (vectorOf d q c : ℝ)) - WithLp.toLp 2 v‖ ≤
        (α : ℝ) / 4 := by
  let C := (SpecBasis.rows d B).map (algebraMap ℚ ℝ)
  let H := (matrixOf B.length
    (FrameAux.Linear.normalizedL B.length (RoundProgram.gram d B) ζ)).map
      (algebraMap ℚ ℝ)
  obtain ⟨b, hb⟩ := SpecBasis.approximates d B ζ hB hζ
  have hspan : rowSpan (H * C) = rowSpan C := normalized_span d B ζ hB
  have hspan' : Submodule.span ℝ (Set.range fun i ↦
      WithLp.toLp 2 (((matrixOf B.length
        (FrameAux.Linear.normalizedL B.length (RoundProgram.gram d B) ζ) *
          SpecBasis.rows d B).map (algebraMap ℚ ℝ)) i)) = rowSpan C := by
    simpa only [rowSpan, H, C, Matrix.map_mul] using hspan
  let b' := (b.map (LinearIsometryEquiv.ofEq _ _ hspan')).reindex
    (finCongr (SpecBasis.length_run d B ζ).symm)
  have happ (i : Fin (SpecBasis.run d B ζ).length) :
      ‖SpecNetGrid.row d (SpecBasis.run d B ζ) i -
        (b' i : EuclideanSpace ℝ (Fin d))‖ ≤ (α : ℝ) / (8 * D) := by
    rw [normalized_row]
    simp only [b', OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
      LinearIsometryEquiv.coe_ofEq_apply]
    exact (hb _).trans hζα
  have hvnorm : ‖WithLp.toLp 2 v‖ = 1 := by
    have he := _root_.ABBKS26.Tree.CompleteAux.norm_sq v
    rw [hv] at he
    nlinarith only [he, norm_nonneg (WithLp.toLp 2 v)]
  exact SpecNetGrid.covers α (SpecBasis.run d B ζ) (rowSpan C) b'
    (by rwa [SpecBasis.length_run]) hD0 hα happ
    (by rwa [SpecBasis.length_run]) ⟨WithLp.toLp 2 v, hvS⟩ hvnorm

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecSpan
