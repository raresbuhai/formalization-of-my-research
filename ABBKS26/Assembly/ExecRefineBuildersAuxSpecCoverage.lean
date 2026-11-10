module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecSpan
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecPrepared

/-! Coverage of the actual normalized and fuel-capped executable direction grid. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecCoverage

open Common Centered Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {d : ℕ}

theorem stored_rows (Y : RoundOutput d) :
    ((SpecBasis.rows d (Y.basis.map List.ofFn)).map (algebraMap ℚ ℝ)) =
      Matrix.submatrix (fun (i : Fin Y.basis.length) (c : Fin d) ↦ (Y.basis[i] c : ℝ))
        (finCongr ((show (Y.basis.map List.ofFn).length = Y.basis.length by simp))) id := by
  ext i c
  have hi : i.val < Y.basis.length := by simpa only [List.length_map] using i.isLt
  simp [SpecBasis.rows, FrameAux.Linear.ent, List.getD_eq_getElem?_getD, hi, c.isLt,
    Matrix.submatrix, Fin.getElem_fin]
  rfl

theorem stored_gram (Y : RoundOutput d) (hY : Y.proj.rank = Y.basis.length) :
    ((SpecBasis.rows d (Y.basis.map List.ofFn) *
      (SpecBasis.rows d (Y.basis.map List.ofFn))ᵀ).map (algebraMap ℚ ℝ)).PosDef := by
  let C : Matrix (Fin Y.basis.length) (Fin d) ℝ := fun i c ↦ (Y.basis[i] c : ℝ)
  have hC : (C * Cᵀ).PosDef := SpecBasis.gram_posDef_of_rank C hY
  let e := finCongr ((show (Y.basis.map List.ofFn).length = Y.basis.length by simp))
  have hp := hC.submatrix e.injective
  rw [Matrix.map_mul, transpose_map, stored_rows]
  have he : (C.submatrix e id)ᵀ = Cᵀ.submatrix id e := rfl
  change (C.submatrix e id * (C.submatrix e id)ᵀ).PosDef
  rw [he]
  have heq : C.submatrix e id * Cᵀ.submatrix id e = (C * Cᵀ).submatrix e e := by
    simpa only [Equiv.coe_refl] using Matrix.submatrix_mul_equiv C Cᵀ e (Equiv.refl _) e
  rw [heq]
  exact hp

theorem stored_mem (Y : RoundOutput d) (v : Vec d) (hv : InRange Y.proj v) :
    WithLp.toLp 2 v ∈ SpecSpan.rowSpan
      ((SpecBasis.rows d (Y.basis.map List.ofFn)).map (algebraMap ℚ ℝ)) := by
  rw [stored_rows]
  have he : SpecSpan.rowSpan
      (Matrix.submatrix (fun (i : Fin Y.basis.length) (c : Fin d) ↦ (Y.basis[i] c : ℝ))
        (finCongr ((show (Y.basis.map List.ofFn).length = Y.basis.length by simp))) id) =
      SpecSpan.rowSpan (fun (i : Fin Y.basis.length) c ↦ (Y.basis[i] c : ℝ)) := by
    unfold SpecSpan.rowSpan
    congr 1
    ext v
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      let e := finCongr (show (Y.basis.map List.ofFn).length = Y.basis.length by simp)
      obtain ⟨j, rfl⟩ := e.surjective i
      exact ⟨j, rfl⟩
  rw [he]
  exact SpecSpan.projector_mem Y.basis v hv

/-- All enumeration caps are inactive at sufficient prepared fuel. -/
theorem grid_covers (F : FrameCode) (MC : MomentCode) (NC : NestedCode)
    (RC : RoundCode) (a : Args)
    (hμ : 0 < SpecInput.accuracy a ∧ SpecInput.accuracy a ≤ 1 / 100)
    (hr : rankBound (SpecInput.weight a) (SpecFuel.deviation a)
      (SpecInput.accuracy a) ≤ a.2)
    (hd : dimensionCap (SpecInput.weight a) (SpecFuel.deviation a)
      (SpecInput.accuracy a) ≤ a.2)
    (hn : netBound (dimensionCap (SpecInput.weight a) (SpecFuel.deviation a)
      (SpecInput.accuracy a)) (SpecInput.accuracy a) ≤ a.2)
    (Y : RoundOutput a.1.1)
    (hbasis : SpecProgram.basis F MC NC RC a = Y.basis.map List.ofFn)
    (hlen : Y.basis.length ≤ rankCap (SpecFuel.radius a) (SpecFuel.rank a))
    (hyRank : Y.proj.rank = Y.basis.length)
    {S : Set (Vec a.1.1)} (hcover : Covers Y.proj S (SpecFuel.radius a))
    (v : Vec a.1.1) (hv : v ∈ S) :
    ∃ q ∈ SpecFuel.grid (SpecProgram.normalized F MC NC RC) a,
      sqnorm (fun c ↦ (vectorOf a.1.1 q c : ℝ)) ≤ 4 ∧
      |‖WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ))‖ - 1| ≤
        (SpecInput.accuracy a : ℝ) / 4 ∧
      ‖WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ)) - WithLp.toLp 2 v‖ ≤
        (33 : ℝ) * SpecInput.accuracy a := by
  let D := dimensionCap (SpecInput.weight a) (SpecFuel.deviation a) (SpecInput.accuracy a)
  have hdim : SpecFuel.dimension a = D := SpecFuel.dimension_agrees a hr hd
  have hrank := SpecFuel.rank_agrees a hr
  have hlen' : Y.basis.length ≤ D := by
    change Y.basis.length ≤ rankCap (SpecFuel.radius a) (SpecFuel.rank a) at hlen
    rwa [hrank] at hlen
  have hD0 : 0 < D := by
    dsimp only [D, dimensionCap]
    unfold rankCap greedyCap
    positivity
  obtain ⟨u, hu, huY, hnear⟩ := hcover v hv
  have hζ : 0 < SpecProgram.accuracy a := by
    unfold SpecProgram.accuracy
    have hμ0 := hμ.1
    positivity
  have hζα : (SpecProgram.accuracy a : ℝ) ≤ (SpecInput.accuracy a : ℝ) / (8 * D) := by
    simp only [SpecProgram.accuracy, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_add, Rat.cast_natCast, Rat.cast_one, hdim]
    apply div_le_div_of_nonneg_left (by exact_mod_cast hμ.1.le) (by positivity)
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD0
    linarith only [hDR]
  obtain ⟨q, hq, hqu⟩ := SpecSpan.normalized_covers (SpecInput.accuracy a)
    (SpecProgram.accuracy a) (Y.basis.map List.ofFn) (stored_gram Y hyRank)
    (by simpa only [List.length_map] using hlen') hD0 hμ hζ hζα
    (by
      simp only [List.length_map]
      exact (SpecPrepared.grid_fuel D Y.basis.length (SpecInput.accuracy a)
        hlen' hD0 hμ).trans hn) u (stored_mem Y u huY) hu
  have hq' : q ∈ SpecFuel.grid (SpecProgram.normalized F MC NC RC) a := by
    unfold SpecFuel.grid
    rw [ite_eq_left hμ, SpecProgram.normalized, hbasis, hdim]
    rw [List.take_of_length_le (by rwa [SpecBasis.length_run, List.length_map])]
    simpa only [SpecFuel.mesh, hdim] using hq
  have hμR : (0 : ℝ) < SpecInput.accuracy a := by exact_mod_cast hμ.1
  have hμ1 : (SpecInput.accuracy a : ℝ) ≤ 1 / 100 := by
    have he := Rat.cast_mono (K := ℝ) hμ.2
    norm_num at he
    exact he
  have hunorm : ‖WithLp.toLp 2 u‖ = 1 := by
    have he := CompleteAux.norm_sq u
    rw [hu] at he
    nlinarith only [he, norm_nonneg (WithLp.toLp 2 u)]
  have hqnorm : ‖WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ))‖ ≤
      1 + (SpecInput.accuracy a : ℝ) / 4 := by
    have he := norm_add_le
      (WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ)) - WithLp.toLp 2 u)
      (WithLp.toLp 2 u)
    rw [sub_add_cancel, hunorm] at he
    linarith only [he, hqu]
  have huv : ‖WithLp.toLp 2 u - WithLp.toLp 2 v‖ ≤
      (32 : ℝ) * SpecInput.accuracy a := by
    have he := CompleteAux.norm_sq (v - u)
    change sqnorm (v - u) ≤ (SpecFuel.radius a : ℝ) ^ 2 at hnear
    simp only [SpecFuel.radius, Centered.radius, Rat.cast_mul, Rat.cast_ofNat] at hnear
    have hn : ‖WithLp.toLp 2 (v - u)‖ ≤ (32 : ℝ) * SpecInput.accuracy a := by
      nlinarith only [he, hnear, norm_nonneg (WithLp.toLp 2 (v - u)), hμR]
    simpa only [WithLp.toLp_sub, norm_sub_rev] using hn
  refine ⟨q, hq', ?_, ?_, ?_⟩
  · rw [← CompleteAux.norm_sq]
    nlinarith only [hqnorm, hμ1, hμR,
      norm_nonneg (WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ)))]
  · rw [← hunorm]
    exact (abs_norm_sub_norm_le _ _).trans hqu
  · have he := norm_add_le
      (WithLp.toLp 2 (fun c ↦ (vectorOf a.1.1 q c : ℝ)) - WithLp.toLp 2 u)
      (WithLp.toLp 2 u - WithLp.toLp 2 v)
    rw [sub_add_sub_cancel] at he
    linarith only [he, hqu, huv, hμR]

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecCoverage
