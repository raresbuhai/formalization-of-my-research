module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecNetGrid

/-! Rational normalization of the executable rounder's stored basis. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecBasis

open Common Matrix FrameAux FrameAux.Linear
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

/-- Multiply a square coefficient table by a rectangular list of ambient vectors. -/
def combine (d : ℕ) (B H : Points) : Points :=
  (List.range B.length).map fun i ↦ (List.range d).map fun c ↦
    ((List.range B.length).map fun j ↦ ent H i j * ent B j c).sum

theorem combine_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {B H : α → Points}
    (hd : ComputableInPolyTime d enc encUnary)
    (hB : ComputableInPolyTime B enc encPoints)
    (hH : ComputableInPolyTime H enc encPoints) :
    ComputableInPolyTime (fun a ↦ combine (d a) (B a) (H a)) enc encPoints := by
  unfold combine
  apply mapWithInput (range.comp ((length_list encVector).comp hB))
  apply mapWithInput (range.comp (hd.comp (fst _ _)))
  apply rat_sum'
  apply mapWithInput (range.comp
    ((length_list encVector).comp ((hB.comp (fst _ _)).comp (fst _ _))))
  fun_prop

def run (d : ℕ) (B : Points) (ζ : ℚ) : Points :=
  combine d B (normalizedL B.length (RoundProgram.gram d B) ζ)

theorem normalization_polytime_of {α : Type} {enc : α ↪ List Bool}
    {r : α → ℕ} {G : α → MatrixL} {ζ : α → ℚ}
    (hr : ComputableInPolyTime r enc encUnary)
    (hG : ComputableInPolyTime G enc encMatrix)
    (hζ : ComputableInPolyTime ζ enc encRat) :
    ComputableInPolyTime (fun a ↦ normalizedL (r a) (G a) (ζ a)) enc encMatrix := by
  have ht : ComputableInPolyTime
      ((fun q : (ℕ × MatrixL) × ℚ ↦ normalizedL q.1.1 q.1.2 q.2) ∘
        (fun a ↦ ((r a, G a), ζ a))) enc encMatrix :=
    normalizedL_polytime.comp ((hr.prod hG).prod hζ)
  exact ht

theorem run_polytime_of {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {B : α → Points} {ζ : α → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hB : ComputableInPolyTime B enc encPoints)
    (hζ : ComputableInPolyTime ζ enc encRat) :
    ComputableInPolyTime (fun a ↦ run (d a) (B a) (ζ a)) enc encPoints := by
  exact combine_polytime_of hd hB (normalization_polytime_of
    ((length_list encVector).comp hB) (RoundProgram.gram_polytime hd hB) hζ)

theorem length_run (d : ℕ) (B : Points) (ζ : ℚ) : (run d B ζ).length = B.length := by
  simp only [run, combine, List.length_map, List.length_range]

def rows (d : ℕ) (B : Points) : Matrix (Fin B.length) (Fin d) ℚ :=
  fun i c ↦ ent B i c

theorem gram_agrees (d : ℕ) (B : Points) :
    matrixOf B.length (RoundProgram.gram d B) = rows d B * (rows d B)ᵀ := by
  ext i j
  change ent (RoundProgram.gram d B) i j = _
  simp only [RoundProgram.gram, RoundProgram.table, ent]
  rw [getD_map_range _ _ i.isLt, getD_map_range _ _ j.isLt]
  unfold dotL
  symm
  apply sum_fin_eq_list
  intro c
  rfl

theorem combine_agrees (d : ℕ) (B H : Points) :
    RepT (combine d B H) (matrixOf B.length H * rows d B) := by
  intro i c
  unfold combine ent
  rw [getD_map_range _ _ i.isLt, getD_map_range _ _ c.isLt]
  symm
  apply sum_fin_eq_list
  intro j
  rfl

noncomputable section

/-- A projector with the advertised rank forces its stored Gram matrix to be
nonsingular, including the empty-basis case. -/
theorem gram_posDef_of_rank {r d : ℕ} (C : Matrix (Fin r) (Fin d) ℝ)
    (hr : (Cᵀ * (C * Cᵀ)⁻¹ * C).rank = r) : (C * Cᵀ).PosDef := by
  have hp : (C * Cᵀ).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      posSemidef_self_mul_conjTranspose C
  apply hp.posDef_iff_det_ne_zero.mpr
  intro hz
  have hi : (C * Cᵀ)⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit _ (by
    rw [hz]
    exact not_isUnit_zero)
  rw [hi, Matrix.mul_zero, Matrix.zero_mul, Matrix.rank_zero] at hr
  have : IsEmpty (Fin r) := Fin.isEmpty_iff.mpr hr.symm
  rw [Matrix.det_isEmpty] at hz
  norm_num at hz

/-- The actual rectangular rows have the Gram matrix of the normalized square frame.
This is the identity needed to turn them into approximations to an orthonormal basis. -/
theorem normalized_gram (d : ℕ) (B : Points) (ζ : ℚ) :
    let C := rows d B
    let H := matrixOf B.length (normalizedL B.length (RoundProgram.gram d B) ζ)
    (H * C) * (H * C)ᵀ =
      H * matrixOf B.length (RoundProgram.gram d B) * Hᵀ := by
  dsimp only
  rw [transpose_mul, gram_agrees]
  simp only [Matrix.mul_assoc]

theorem gram_error (d : ℕ) (B : Points) (ζ : ℚ)
    (hB : ((rows d B * (rows d B)ᵀ).map (algebraMap ℚ ℝ)).PosDef)
    (hζ : 0 < ζ) :
    let C := (rows d B).map (algebraMap ℚ ℝ)
    let H := (matrixOf B.length
      (normalizedL B.length (RoundProgram.gram d B) ζ)).map (algebraMap ℚ ℝ)
    frobSq ((H * C) * (H * C)ᵀ - 1) ≤ (ζ : ℝ) ^ 2 := by
  have hpos : ((matrixOf B.length (RoundProgram.gram d B)).map
      (algebraMap ℚ ℝ)).PosDef := by rwa [gram_agrees]
  have he := normalizedL_error B.length (RoundProgram.gram d B)
    ((matrixOf B.length (RoundProgram.gram d B)).map (algebraMap ℚ ℝ)) 0 ζ hpos
      le_rfl hζ (by simp [frobSq, Matrix.zero_apply])
  dsimp only
  simp only [zero_add] at he
  have hgram := congrArg (fun A ↦ A.map (algebraMap ℚ ℝ)) (normalized_gram d B ζ)
  simp only [Matrix.map_mul, transpose_map] at hgram
  rw [hgram]
  exact he

theorem normalized_diagonal (d : ℕ) (B : Points) (ζ : ℚ)
    (hB : ((rows d B * (rows d B)ᵀ).map (algebraMap ℚ ℝ)).PosDef) :
    let H := matrixOf B.length (normalizedL B.length (RoundProgram.gram d B) ζ)
    let A := (H * rows d B).map (algebraMap ℚ ℝ)
    ∃ q : Fin B.length → ℝ, (∀ i, 0 < q i) ∧ A * Aᵀ = diagonal q := by
  let G := matrixOf B.length (RoundProgram.gram d B)
  let T := (whitenMat G).map (algebraMap ℚ ℝ)
  let q := whitenDiag G
  let s : Fin B.length → ℝ := fun i ↦
    invSqrt (normalizePrecision B.length ζ) (q i)
  have hpos : (G.map (algebraMap ℚ ℝ)).PosDef := by
    dsimp only [G]
    rwa [gram_agrees]
  have hq := whitenDiag_spec G hpos
  have hs (i : Fin B.length) : 0 < s i := by
    change (0 : ℝ) < (invSqrt (normalizePrecision B.length ζ) (q i) : ℝ)
    exact_mod_cast (invSqrt_spec (normalizePrecision B.length ζ) (hq i)).1
  have hdiag : T * G.map (algebraMap ℚ ℝ) * Tᵀ =
      diagonal (fun i ↦ (q i : ℝ)) := whitenMat_spec_real G hpos
  refine ⟨fun i ↦ s i ^ 2 * (q i : ℝ), ?_, ?_⟩
  · intro i
    have hi : (0 : ℝ) < q i := by exact_mod_cast (lt_of_lt_of_le (by norm_num) (hq i).1)
    exact mul_pos (sq_pos_of_pos (hs i)) hi
  · have hgram := congrArg (fun A ↦ A.map (algebraMap ℚ ℝ)) (normalized_gram d B ζ)
    simp only [Matrix.map_mul, transpose_map] at hgram
    simp only [Matrix.map_mul]
    rw [hgram, matrixOf_normalizedL_real]
    change (diagonal s * T) * G.map (algebraMap ℚ ℝ) * (diagonal s * T)ᵀ = _
    calc
      _ = diagonal s * (T * G.map (algebraMap ℚ ℝ) * Tᵀ) * diagonal s := by
        rw [transpose_mul, diagonal_transpose]
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext i
        ring

variable {d : ℕ}

/-- Normalize an orthogonal family analytically to identify the basis approximated by
the rational program. The basis is used only in the proof of grid coverage. -/
theorem unit_basis {r : ℕ} (v : Fin r → EuclideanSpace ℝ (Fin d))
    (hne : ∀ i, v i ≠ 0)
    (horth : Pairwise fun i j ↦ inner ℝ (v i) (v j) = 0) :
    ∃ b : OrthonormalBasis (Fin r) ℝ (Submodule.span ℝ (Set.range v)),
      ∀ i, (b i : EuclideanSpace ℝ (Fin d)) = ‖v i‖⁻¹ • v i := by
  classical
  let w := fun i ↦ ‖v i‖⁻¹ • v i
  have hn (i : Fin r) : ‖v i‖ ≠ 0 := norm_ne_zero_iff.mpr (hne i)
  have hw : Orthonormal ℝ w := by
    constructor
    · intro i
      simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (hn i)]
    · intro i j hij
      simp only [w, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
        horth hij, mul_zero]
  have hspan : Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : ‖v i‖ • w i ∈ Submodule.span ℝ (Set.range w) :=
        Submodule.smul_mem (Submodule.span ℝ (Set.range w)) ‖v i‖
          (Submodule.subset_span (Set.mem_range_self i))
      have hei : ‖v i‖ • w i = v i := by
        dsimp only [w]
        rw [smul_smul, mul_inv_cancel₀ (hn i), one_smul]
      exact hei ▸ hi
  let b₀ := Module.Basis.span hw.linearIndependent
  have hb₀ : (fun i ↦ b₀ i) =
      (fun i ↦ ⟨w i, Submodule.subset_span (Set.mem_range_self i)⟩) :=
    funext (fun i ↦ Module.Basis.span_apply hw.linearIndependent i)
  let b : OrthonormalBasis (Fin r) ℝ (Submodule.span ℝ (Set.range w)) :=
    OrthonormalBasis.mk (orthonormal_span hw) (by rw [← hb₀]; exact b₀.span_eq.ge)
  refine ⟨b.map (LinearIsometryEquiv.ofEq _ _ hspan), ?_⟩
  intro i
  simp [b, OrthonormalBasis.coe_mk, w]

theorem norm_error (t ζ : ℝ) (ht : 0 ≤ t) (hζ : 0 ≤ ζ)
    (he : (t ^ 2 - 1) ^ 2 ≤ ζ ^ 2) : |t - 1| ≤ ζ := by
  have hb : |t ^ 2 - 1| ≤ ζ :=
    (sq_le_sq₀ (abs_nonneg _) hζ).mp (by simpa only [sq_abs] using he)
  calc
    _ ≤ |t - 1| * (t + 1) := le_mul_of_one_le_right (abs_nonneg _) (by linarith)
    _ = |t ^ 2 - 1| := by
      rw [← abs_of_nonneg (by linarith : 0 ≤ t + 1), ← abs_mul]
      congr 1
      ring
    _ ≤ ζ := hb

theorem unit_approx {r : ℕ} (A : Matrix (Fin r) (Fin d) ℝ) (ζ : ℝ)
    (hζ : 0 ≤ ζ) (he : frobSq (A * Aᵀ - 1) ≤ ζ ^ 2) (i : Fin r)
    (hne : WithLp.toLp 2 (A i) ≠ 0) :
    ‖WithLp.toLp 2 (A i) - ‖WithLp.toLp 2 (A i)‖⁻¹ • WithLp.toLp 2 (A i)‖ ≤ ζ := by
  let v := WithLp.toLp 2 (A i)
  let E : Mat r := A * Aᵀ - 1
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  have hdiag : E i i = ‖v‖ ^ 2 - 1 := by
    dsimp only [E]
    rw [Matrix.sub_apply, Matrix.one_apply_eq]
    change (A i ⬝ᵥ A i) - 1 = _
    change sqnorm (A i) - 1 = _
    rw [← _root_.ABBKS26.Tree.CompleteAux.norm_sq]
  have hi : (E i i) ^ 2 ≤ frobSq E := by
    apply (Finset.single_le_sum (fun j _ ↦ sq_nonneg (E i j))
      (Finset.mem_univ i)).trans
    exact Finset.single_le_sum
      (fun j _ ↦ Finset.sum_nonneg fun c _ ↦ sq_nonneg (E j c))
      (Finset.mem_univ i)
  rw [hdiag] at hi
  have hb := norm_error ‖v‖ ζ (norm_nonneg _) hζ (hi.trans he)
  change ‖v - ‖v‖⁻¹ • v‖ ≤ ζ
  calc
    _ = ‖(1 - ‖v‖⁻¹) • v‖ := congrArg norm (by module)
    _ = |1 - ‖v‖⁻¹| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = |‖v‖ - 1| := by
      calc
        _ = |(1 - ‖v‖⁻¹) * ‖v‖| := by rw [abs_mul, abs_of_nonneg (norm_nonneg v)]
        _ = _ := by congr 1; field_simp
    _ ≤ ζ := hb

/-- The rational normalization approximates an orthonormal basis of its row span,
with exactly the tolerance requested by the caller. -/
theorem approximates (d : ℕ) (B : Points) (ζ : ℚ)
    (hB : ((rows d B * (rows d B)ᵀ).map (algebraMap ℚ ℝ)).PosDef) (hζ : 0 < ζ) :
    let H := matrixOf B.length (normalizedL B.length (RoundProgram.gram d B) ζ)
    let A := (H * rows d B).map (algebraMap ℚ ℝ)
    ∃ b : OrthonormalBasis (Fin B.length) ℝ
        (Submodule.span ℝ (Set.range (fun i ↦ WithLp.toLp 2 (A i)))),
      ∀ i, ‖WithLp.toLp 2 (A i) - (b i : EuclideanSpace ℝ (Fin d))‖ ≤ (ζ : ℝ) := by
  let H := matrixOf B.length (normalizedL B.length (RoundProgram.gram d B) ζ)
  let A := (H * rows d B).map (algebraMap ℚ ℝ)
  let v := fun i ↦ WithLp.toLp 2 (A i)
  obtain ⟨q, hq, hdiag⟩ := normalized_diagonal d B ζ hB
  have hn (i : Fin B.length) : sqnorm (A i) = q i := by
    change (A * Aᵀ) i i = q i
    rw [hdiag, diagonal_apply_eq]
  have hne (i : Fin B.length) : v i ≠ 0 := by
    intro hz
    have hz' : A i = 0 := congrArg WithLp.ofLp hz
    have hh := hn i
    rw [hz', sqnorm, dotProduct_zero] at hh
    exact (ne_of_gt (hq i)) hh.symm
  have horth : Pairwise fun i j ↦ inner ℝ (v i) (v j) = 0 := by
    intro i j hij
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [star_trivial]
    change A j ⬝ᵥ A i = 0
    rw [dotProduct_comm]
    change (A * Aᵀ) i j = 0
    rw [hdiag, diagonal_apply_ne _ hij]
  obtain ⟨b, hb⟩ := unit_basis v hne horth
  refine ⟨b, fun i ↦ ?_⟩
  rw [hb i]
  have herr : frobSq (A * Aᵀ - 1) ≤ (ζ : ℝ) ^ 2 := by
    dsimp only [A, H]
    rw [Matrix.map_mul]
    exact gram_error d B ζ hB hζ
  exact unit_approx A ζ (by exact_mod_cast hζ.le) herr i (hne i)

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecBasis
