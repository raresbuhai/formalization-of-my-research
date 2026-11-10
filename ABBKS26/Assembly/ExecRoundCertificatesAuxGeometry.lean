module

public import ABBKS26.Assembly.ExecRoundAuxPoly

/-! Exact interpretation of the rational projector and the append tests. -/

@[expose] public section


namespace ABBKS26.Assembly.Exec.RoundCertificates.Geometry

open Common Rounding RoundProgram FrameAux.Linear Matrix
open Cslib (rowEntry)
open Cslib.Circuits.Rational (detRows detRows_eq_det_of_rowEntry)
open scoped BigOperators

private theorem table_rep (d : ℕ) (f : ℕ → ℕ → ℚ) :
    RepT (table d f) (fun i j : Fin d ↦ f i j) :=
  repT_map_range _ _ (fun _ _ ↦ rfl)

theorem determinant_eq {m : ℕ} {A : MatrixL} {M : Matrix (Fin m) (Fin m) ℚ}
    (hlen : A.length = m) (hA : RepT A M) : determinant A = M.det := by
  let D := SoS.PDTestRat.commonDen A
  let N : Matrix (Fin m) (Fin m) ℤ := fun i j ↦ rowEntry (SoS.PDTestRat.scale A) i j
  have hdet : detRows (SoS.PDTestRat.scale A) = N.det :=
    detRows_eq_det_of_rowEntry N (by simpa [SoS.PDTestRat.scale] using hlen)
      (fun _ _ ↦ rfl)
  have hN : N.map (Int.cast : ℤ → ℚ) = (D : ℚ) • M := by
    ext i j
    change (rowEntry (SoS.PDTestRat.scale A) i j : ℚ) = (D : ℚ) * M i j
    rw [SoS.PDTestRat.rowEntry_scale]
    congr 1
    exact hA i j
  have hD : (D : ℚ) ≠ 0 := by
    exact_mod_cast (SoS.PDTestRat.commonDen_pos A).ne'
  rw [determinant, hdet, Int.cast_det, hN, det_smul, Fintype.card_fin, hlen]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hD)

theorem inverse_rep {m : ℕ} {A : MatrixL} {M : Matrix (Fin m) (Fin m) ℚ}
    (hlen : A.length = m) (hA : RepT A M) : RepT (inverse A) (M⁻¹ : Matrix (Fin m) (Fin m) ℚ) := by
  have hden := determinant_eq hlen hA
  have hnum (i j : Fin m) : determinant (replaceRow A j i) = M.adjugate i j := by
    rw [adjugate_apply]
    apply determinant_eq (by simp [replaceRow, table, hlen])
    intro r c
    have hr : r.val < A.length := by omega
    have hc : c.val < A.length := by omega
    simp only [replaceRow, table, ent]
    rw [getD_map_range _ _ hr, getD_map_range _ _ hc]
    change (if r.val = j.val then (if c.val = i.val then 1 else 0)
      else ent A r c) = M.updateRow j (Pi.single i 1) r c
    rw [hA r c]
    simp [updateRow_apply, Pi.single_apply, Fin.ext_iff, eq_comm]
  intro i j
  have hi : i.val < A.length := by omega
  have hj : j.val < A.length := by omega
  simp only [inverse, table, ent]
  rw [getD_map_range _ _ hi, getD_map_range _ _ hj, hnum, hden]
  change M.adjugate i j / M.det = ((Ring.inverse M.det) • M.adjugate) i j
  rw [Ring.inverse_eq_inv]
  exact div_eq_inv_mul _ _

private def columns (d : ℕ) (B : Points) : Matrix (Fin d) (Fin B.length) ℚ :=
  fun i j ↦ (B[j]).getD i 0

private theorem gram_rep (d : ℕ) (B : Points) :
    RepT (gram d B) (((columns d B)ᵀ * columns d B) : Matrix (Fin B.length) (Fin B.length) ℚ) := by
  intro i j
  have h := table_rep B.length (fun i j ↦ dotL d (B.getD i []) (B.getD j [])) i j
  change ent (table B.length _) i j = _
  rw [h]
  unfold dotL
  symm
  apply sum_fin_eq_list
  intro k
  simp [columns, Matrix.transpose_apply]

private theorem projection_eq_rat (d : ℕ) (B : Points) :
    matrixOf d (projection d B) =
      columns d B * ((columns d B)ᵀ * columns d B)⁻¹ * (columns d B)ᵀ := by
  have hG := inverse_rep (by simp [RoundProgram.gram, table]) (gram_rep d B)
  ext a b
  change ent (projection d B) a b = _
  rw [show ent (projection d B) a b =
      ((List.range B.length).map fun i ↦ ((List.range B.length).map fun j ↦
        ent B i a * ent (inverse (gram d B)) i j * ent B j b).sum).sum from
    table_rep d _ a b]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  symm
  apply sum_fin_eq_list
  intro i
  symm
  apply sum_fin_eq_list
  intro j
  rw [hG i j]
  simp [columns, ent]

private theorem cast_inv {m : ℕ} (M : Matrix (Fin m) (Fin m) ℚ) :
    M⁻¹.map (algebraMap ℚ ℝ) = (M.map (algebraMap ℚ ℝ))⁻¹ := by
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
  have ha := (algebraMap ℚ ℝ).map_adjugate M
  ext i j
  change ((M.det⁻¹ * M.adjugate i j : ℚ) : ℝ) = _
  push_cast
  change (M.map (algebraMap ℚ ℝ)).det⁻¹ * (M.adjugate i j : ℝ) =
    (M.map (algebraMap ℚ ℝ)).det⁻¹ * (M.map (algebraMap ℚ ℝ)).adjugate i j
  congr 1
  exact congrArg (fun A ↦ A i j) ha

theorem projection_eq (a : RoundArgs) (B : Points) :
    (matrixOf a.2.1 (projection a.2.1 B)).map (algebraMap ℚ ℝ) = (output a B).proj := by
  rw [projection_eq_rat, Matrix.map_mul, Matrix.map_mul, cast_inv,
    Matrix.map_mul, Matrix.transpose_map]
  let C := (columns a.2.1 B).map (algebraMap ℚ ℝ)
  have hlen : (output a B).basis.length = B.length := by simp [output]
  let e := finCongr hlen
  have hm : (fun (i : Fin a.2.1) (j : Fin (output a B).basis.length) ↦
      ((output a B).basis[j] i : ℝ)) = C.submatrix id e := by
    ext i j
    change ((List.map (vectorOf a.2.1) B)[j.val] i : ℝ) = _
    rw [List.getElem_map]
    rfl
  change C * (Cᵀ * C)⁻¹ * Cᵀ = _
  change _ = DetRoundAux.frameProj _
  rw [hm]
  unfold DetRoundAux.frameProj
  rw [transpose_submatrix]
  have hg : Cᵀ.submatrix e id * C.submatrix id e = (Cᵀ * C).submatrix e e :=
    submatrix_mul_equiv Cᵀ C e (Equiv.refl _) e
  rw [hg, inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
    submatrix_id_id]

theorem complement_eq (a : RoundArgs) (B : Points) :
    (matrixOf a.2.1 (complement a.2.1 B)).map (algebraMap ℚ ℝ) =
      1 - (output a B).proj := by
  rw [← projection_eq]
  ext i j
  have h := table_rep a.2.1 (fun i j ↦ ent (identity a.2.1) i j -
    ent (projection a.2.1 B) i j) i j
  have hI := table_rep a.2.1 (fun i j ↦ if i = j then 1 else 0) i j
  change ((ent (complement a.2.1 B) i j : ℚ) : ℝ) = _
  rw [show ent (complement a.2.1 B) i j = _ from h]
  dsimp only
  rw [show ent (identity a.2.1) i j = _ from hI]
  simp only [Matrix.one_apply, Fin.ext_iff, matrixOf, ent, Matrix.sub_apply,
    Matrix.map_apply]
  by_cases hij : i.val = j.val <;> simp [hij]

theorem residual_eq (a : RoundArgs) (B : Points) (v : Vector) :
    (dotL a.2.1 (mulVecL a.2.1 (complement a.2.1 B) v)
      (mulVecL a.2.1 (complement a.2.1 B) v) : ℝ) =
      sqnorm ((1 - (output a B).proj) *ᵥ (fun i ↦ (vectorOf a.2.1 v i : ℝ))) := by
  have hm : RepV (mulVecL a.2.1 (complement a.2.1 B) v)
      (matrixOf a.2.1 (complement a.2.1 B) *ᵥ vectorOf a.2.1 v) :=
    mulVecL_rep (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  rw [dotL_eq hm hm, ← dotProduct_cast]
  rw [← complement_eq a B, sqnorm]
  have hcast := mulVec_cast (matrixOf a.2.1 (complement a.2.1 B)) (vectorOf a.2.1 v)
  change _ = (fun i ↦ _) ⬝ᵥ (fun i ↦ _)
  exact congrArg (fun z ↦ z ⬝ᵥ z) hcast.symm

private def family {d : ℕ} (Y : List (Fin d → ℚ)) : Fin Y.length → Vec d :=
  fun j i ↦ (Y[j] i : ℝ)

private def basisMatrix {d : ℕ} (Y : List (Fin d → ℚ)) :
    Matrix (Fin d) (Fin Y.length) ℝ := fun i j ↦ family Y j i

private theorem gram_det_ne_zero {d : ℕ} {Y : List (Fin d → ℚ)}
    (hY : LinearIndependent ℝ (family Y)) :
    ((basisMatrix Y)ᵀ * basisMatrix Y).det ≠ 0 := by
  have hi : Function.Injective (basisMatrix Y).mulVec :=
    Matrix.mulVec_injective_iff.2 hY
  have hp := Matrix.PosDef.conjTranspose_mul_self (basisMatrix Y) hi
  simpa only [conjTranspose_eq_transpose_of_trivial] using hp.det_pos.ne'

private theorem family_fixed {d : ℕ} {Y : List (Fin d → ℚ)}
    (hY : LinearIndependent ℝ (family Y)) (j : Fin Y.length) :
    projector Y *ᵥ family Y j = family Y j := by
  have hf := (DetRoundAux.frameProj_spec (basisMatrix Y) (gram_det_ne_zero hY)).2.2
  funext i
  exact congrArg (fun M ↦ M i j) hf

private theorem span_fixed {d : ℕ} {Y : List (Fin d → ℚ)}
    (hY : LinearIndependent ℝ (family Y)) {x : Vec d}
    (hx : x ∈ Submodule.span ℝ (Set.range (family Y))) : projector Y *ᵥ x = x := by
  have hs : Submodule.span ℝ (Set.range (family Y)) ≤
      LinearMap.ker ((1 - projector Y).mulVecLin) := by
    apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    change (1 - projector Y) *ᵥ family Y j = 0
    rw [sub_mulVec, one_mulVec, family_fixed hY, sub_self]
  have h := hs hx
  change (1 - projector Y) *ᵥ x = 0 at h
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at h
  exact h.symm

private theorem family_snoc {d : ℕ} (Y : List (Fin d → ℚ)) (v : Fin d → ℚ)
    (hY : LinearIndependent ℝ (family Y))
    (hv : (fun i ↦ (v i : ℝ)) ∉ Submodule.span ℝ (Set.range (family Y))) :
    LinearIndependent ℝ (family (Y ++ [v])) := by
  let e : Fin (Y ++ [v]).length ≃ Fin (Y.length + 1) := finCongr (by simp)
  have he : family (Y ++ [v]) =
      (Fin.snoc (family Y) (fun i ↦ (v i : ℝ))) ∘ e := by
    funext j
    by_cases hj : j.val < Y.length
    · have hc : e j = (⟨j.val, hj⟩ : Fin Y.length).castSucc := Fin.ext rfl
      simp only [Function.comp_apply, hc, Fin.snoc_castSucc]
      funext i
      change (((Y ++ [v])[j.val] i : ℚ) : ℝ) = (Y[j.val] i : ℝ)
      rw [List.getElem_append_left]
    · have hj' : j.val = Y.length := by
        have h := j.isLt
        simp only [List.length_append, List.length_singleton] at h
        omega
      have hc : e j = Fin.last Y.length := Fin.ext hj'
      simp only [Function.comp_apply, hc, Fin.snoc_last]
      funext i
      change (((Y ++ [v])[j.val] i : ℚ) : ℝ) = (v i : ℝ)
      simp [hj']
  rw [he]
  exact (hY.finSnoc hv).comp e e.injective

private theorem good_independent (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    LinearIndependent ℝ (family (output a B).basis) := by
  induction hB with
  | nil =>
      change LinearIndependent ℝ (fun j : Fin 0 ↦ family (output a []).basis j)
      exact linearIndependent_empty_type
  | @snoc B v hB hv _ ih =>
    have hz : (9 / 64 : ℝ) ≤ sqnorm ((1 - (output a B).proj) *ᵥ
        (fun i ↦ (vectorOf a.2.1 v i : ℝ))) := by
      rw [← residual_eq]
      have h : (9 / 64 : ℚ) ≤ _ := hv.2.2.1
      have h' := Rat.cast_le (K := ℝ) |>.2 h
      norm_num at h' ⊢
      exact h'
    have hnot : (fun i ↦ (vectorOf a.2.1 v i : ℝ)) ∉
        Submodule.span ℝ (Set.range (family (output a B).basis)) := by
      intro hmem
      have hf := span_fixed ih hmem
      change (output a B).proj *ᵥ _ = _ at hf
      rw [sub_mulVec, one_mulVec, hf, sub_self] at hz
      norm_num [sqnorm, dotProduct] at hz
    change LinearIndependent ℝ (family ((B ++ [v]).map (vectorOf a.2.1)))
    rw [List.map_append, List.map_singleton]
    exact family_snoc (output a B).basis (vectorOf a.2.1 v) ih hnot

private theorem good_history (a : RoundArgs) (B : Points) (hB : GoodBasis a B)
    (j : Fin B.length) : acceptable a (B.take j.val) B[j] ∧ OnGrid a B[j] := by
  induction hB with
  | nil => exact Fin.elim0 j
  | @snoc B v hB hv hg ih =>
    by_cases hj : j.val < B.length
    · have h := ih ⟨j.val, hj⟩
      simpa only [Fin.getElem_fin, List.getElem_append_left hj,
        List.take_append_of_le_length hj.le] using h
    · have hj' : j.val = B.length := by
        have h := j.isLt
        simp only [List.length_append, List.length_singleton] at h
        omega
      simpa [Fin.getElem_fin, hj'] using And.intro hv hg

theorem basis_geometry (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    Projection (output a B).proj ∧ (output a B).proj.rank = B.length ∧
      (output a B).WellConditioned (greedyPrecision a) := by
  have hi := good_independent a B hB
  have hspec := DetRoundAux.frameProj_spec (basisMatrix (output a B).basis)
    (gram_det_ne_zero hi)
  refine ⟨hspec.1, ?_, ?_⟩
  · change (DetRoundAux.frameProj (basisMatrix (output a B).basis)).rank = _
    rw [hspec.2.1]
    simp only [output, List.length_map]
  · intro j
    have hj : j.val < B.length := by simpa [output] using j.isLt
    obtain ⟨hv, hg⟩ := good_history a B hB ⟨j.val, hj⟩
    simp only [Fin.getElem_fin] at hv hg
    have hres := residual_eq a (B.take j.val) B[j.val]
    have hprefix : (output a (B.take j.val)).proj =
        projector ((output a B).basis.take j.val) := by
      simp only [output, RoundOutput.proj, List.map_take]
    rw [hprefix] at hres
    have hvec : (output a B).basis[j] = vectorOf a.2.1 B[j.val] := by
      change (B.map (vectorOf a.2.1))[j.val] = _
      rw [List.getElem_map]
    change 9 / 64 ≤ sqnorm _ ∧ sqnorm _ ≤ 81 / 64 ∧ _
    rw [hvec]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hres]
      have h : (9 / 64 : ℚ) ≤ _ := hv.2.2.1
      have h' := Rat.cast_le (K := ℝ) |>.2 h
      norm_num at h' ⊢
      exact h'
    · rw [← hres]
      have h : _ ≤ (81 / 64 : ℚ) := hv.2.2.2
      have h' := Rat.cast_le (K := ℝ) |>.2 h
      norm_num at h' ⊢
      exact h'
    · intro i
      have hm : (B[j.val]).getD i.val 0 ∈ B[j.val] := by
        rw [List.getD_eq_getElem _ _ (by rw [hv.1]; exact i.isLt)]
        exact List.getElem_mem _
      exact ⟨(hv.2.1 _ hm).1, (hv.2.1 _ hm).2, hg _ hm⟩

end ABBKS26.Assembly.Exec.RoundCertificates.Geometry

namespace ABBKS26.Assembly.Exec.RoundCertificates.Bounds

open Common Rounding RoundProgram FrameAux.Linear Matrix
open Encoding (encRat)
open Turing.MultiTapeTM
open scoped BigOperators

private theorem abs_encoding (q : ℚ) : (encRat |q|).length = (encRat q).length := by
  by_cases h : 0 ≤ q
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), Rounding.RawAux.length_rat_neg]

private theorem inverse_sq_bound (q : ℚ) :
    1 / q ^ 2 ≤ (2 : ℚ) ^ (2 * (encRat q).length) := by
  by_cases hq : q = 0
  · simp [hq]
  · have h := SoS.Correct.two_pow_inv_le (abs_pos.2 hq)
    rw [abs_encoding] at h
    have h' : 1 / (2 : ℚ) ^ (encRat q).length ≤ |q| := by
      apply (Rat.cast_le (K := ℝ)).1
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ 1 / 2 ^
      (encRat q).length) h' 2
    rw [div_pow, one_pow, sq_abs, ← pow_mul] at hs
    rw [Nat.mul_comm (encRat q).length 2] at hs
    apply (div_le_iff₀ (sq_pos_of_ne_zero hq)).2
    have hp : (0 : ℚ) < 2 ^ (2 * (encRat q).length) := by positivity
    have hh := (div_le_iff₀ hp).1 hs
    simpa only [mul_comm] using hh

theorem objectivePrecision_bound (a : RoundArgs) :
    objectivePrecision a ≤ 2 * (encRat a.2.2.1).length + a.2.1 + 11 := by
  let N := 2 * (encRat a.2.2.1).length + a.2.1 + 11
  have hd : (a.2.1 + 1 : ℚ) ≤ (2 : ℚ) ^ (a.2.1 + 1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := a.2.1 + 1)).le
  have hq := inverse_sq_bound a.2.2.1
  have h : 1024 * (a.2.1 + 1 : ℚ) / a.2.2.1 ^ 2 ≤ (2 : ℚ) ^ N := by
    calc
      _ = 1024 * (a.2.1 + 1 : ℚ) * (1 / a.2.2.1 ^ 2) := by ring
      _ ≤ 1024 * 2 ^ (a.2.1 + 1) * 2 ^ (2 * (encRat a.2.2.1).length) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hq
          (by positivity) (by positivity)
      _ = (2 : ℚ) ^ N := by
        dsimp [N]
        rw [show 2 * (encRat a.2.2.1).length + a.2.1 + 11 =
          10 + (a.2.1 + 1) + 2 * (encRat a.2.2.1).length by omega,
          pow_add, pow_add]
        norm_num [pow_add]
  apply Nat.clog_le_of_le_pow
  exact Nat.ceil_le.2 (by exact_mod_cast h)

theorem threshold_pos (a : RoundArgs) : 0 < greedyThreshold a.2.2.1 a.2.2.2.1 := by
  unfold greedyThreshold
  positivity

theorem greedyCap_pos (a : RoundArgs) : 1 ≤ greedyCap a.2.2.1 a.2.2.2.1 := by
  unfold greedyCap
  omega

theorem greedyCap_le_rankCap (a : RoundArgs) :
    greedyCap a.2.2.1 a.2.2.2.1 ≤ rankCap a.2.2.1 a.2.2.2.1 := by
  unfold rankCap
  exact Nat.le_mul_of_pos_left _ (by omega)

theorem packCount_le_rankCap (a : RoundArgs) :
    packCount a.2.2.1 a.2.2.2.1 + 1 ≤ rankCap a.2.2.1 a.2.2.2.1 := by
  unfold rankCap
  exact Nat.le_mul_of_pos_right _ (greedyCap_pos a)

theorem greedyPrecision_bound (a : RoundArgs) :
    greedyPrecision a ≤ 120 * (a.2.1 + 1) * rankCap a.2.2.1 a.2.2.2.1 + 2 := by
  have ht := threshold_pos a
  have hcap : 1 / greedyThreshold a.2.2.1 a.2.2.2.1 ≤
      (greedyCap a.2.2.1 a.2.2.2.1 : ℚ) := by
    have h := Nat.le_ceil (32 / greedyThreshold a.2.2.1 a.2.2.2.1 : ℚ)
    unfold greedyCap
    push_cast
    have hle : 1 / greedyThreshold a.2.2.1 a.2.2.2.1 ≤
        32 / greedyThreshold a.2.2.1 a.2.2.2.1 :=
      div_le_div_of_nonneg_right (by norm_num) ht.le
    linarith
  have hr : 1 / greedyThreshold a.2.2.1 a.2.2.2.1 ≤
      (rankCap a.2.2.1 a.2.2.2.1 : ℚ) :=
    hcap.trans (by exact_mod_cast greedyCap_le_rankCap a)
  have hc : ⌈120 * (a.2.1 + 1 : ℚ) / greedyThreshold a.2.2.1 a.2.2.2.1⌉₊ ≤
      120 * (a.2.1 + 1) * rankCap a.2.2.1 a.2.2.2.1 := by
    apply Nat.ceil_le.2
    push_cast
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℚ) ≤ 120 * (a.2.1 + 1))
  exact Nat.add_le_add_right
    ((Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le).trans hc) 2

theorem list_encoding_bound {α : Type} (enc : α ↪ List Bool) (l : List α) (b : ℕ)
    (h : ∀ x ∈ l, (enc x).length ≤ b) : (encList enc l).length ≤ l.length * (2 * b + 1) :=
  Rounding.RawAux.length_list_le enc l h

private theorem good_coordinates (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    ∀ w ∈ B, (∀ q ∈ w, -1 ≤ q ∧ q ≤ 1) ∧ OnGrid a w := by
  induction hB with
  | nil => simp
  | @snoc B w _ hw hg ih =>
    intro z hz
    rcases List.mem_append.1 hz with hz | hz
    · exact ih z hz
    · have he : z = w := by simpa using hz
      subst z
      exact ⟨hw.2.1, hg⟩

theorem basis_encoding_bound (a : RoundArgs) (B : Points) (hB : GoodBasis a B)
    (hlen : B.length ≤ rankCap a.2.2.1 a.2.2.2.1) :
    (encPoints B).length ≤ rankCap a.2.2.1 a.2.2.2.1 *
      (2 * (a.2.1 * (6 * greedyPrecision a + 13)) + 1) := by
  apply (list_encoding_bound encVector B _ ?_).trans
    (Nat.mul_le_mul_right _ hlen)
  intro v hv
  have hs : SoS.PolyTime.Small (greedyPrecision a) 0 =
      (fun q : ℚ ↦ |q| ≤ 1 ∧ ∃ z : ℤ, q * 2 ^ greedyPrecision a = z) := by
    funext q
    simp only [SoS.PolyTime.Small, pow_zero]
  have hc : ∀ q ∈ v, (encRat q).length ≤ 3 * greedyPrecision a + 6 := by
    intro q hq
    obtain ⟨hb, hg⟩ := good_coordinates a B hB v hv
    have hsmall : SoS.PolyTime.Small (greedyPrecision a) 0 q := by
      rw [hs]
      refine ⟨abs_le.2 (hb q hq), ?_⟩
      obtain ⟨z, hz⟩ := hg q hq
      refine ⟨z, ?_⟩
      rw [hz, div_mul_cancel₀ _ (by positivity)]
    simpa only [Nat.zero_add] using SoS.PolyTime.length_encRat_le_of_small hsmall
  have hlenv := hB.rows v hv
  have h := list_encoding_bound encRat v _ hc
  rw [hlenv] at h
  convert h using 1
  ring

private theorem projection_entry {d : ℕ} (P : Mat d) (hP : Projection P) (i j : Fin d) :
    |P i j| ≤ 1 := by
  have hentry (v : Vec d) : v i ^ 2 ≤ sqnorm v := by
    unfold sqnorm dotProduct
    simpa only [pow_two] using Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) ↦ mul_self_nonneg (v k)) (Finset.mem_univ i)
  have h := (hentry (P *ᵥ Pi.single j 1)).trans
    (DetRoundAux.projection_contract P hP (Pi.single j 1))
  have he : sqnorm (Pi.single j 1 : Vec d) = 1 := by
    rw [sqnorm, dotProduct_single, Pi.single_eq_same, mul_one]
  have hx : (P *ᵥ Pi.single j 1) i = P i j := by simp [Matrix.mulVec_single]
  rw [he, hx] at h
  exact (sq_le_one_iff_abs_le_one _).1 h

private theorem round_small (p : ℕ) (q : ℚ) (hq : |q| ≤ 1) :
    SoS.PolyTime.Small p 0 (roundRat p q) := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  have hupper := Int.floor_le ((2 : ℚ) ^ p * q)
  have hlower : -(2 : ℤ) ^ p ≤ ⌊(2 : ℚ) ^ p * q⌋ := by
    apply Int.le_floor.2
    push_cast
    nlinarith [(abs_le.1 hq).1]
  have hlow : -(2 : ℚ) ^ p ≤ (⌊(2 : ℚ) ^ p * q⌋ : ℤ) := by exact_mod_cast hlower
  refine ⟨?_, ⌊(2 : ℚ) ^ p * q⌋, ?_⟩
  · rw [pow_zero, abs_le]
    unfold roundRat
    constructor
    · exact (le_div_iff₀ hp).2 (by simpa only [neg_one_mul] using hlow)
    · exact (div_le_iff₀ hp).2 (hupper.trans (by nlinarith [(abs_le.1 hq).2]))
  · unfold roundRat
    exact div_mul_cancel₀ _ hp.ne'

private theorem rounded_entry (a : RoundArgs) (B : Points) (i j : Fin a.2.1) :
    ent (roundedProjection a B) i j =
      roundRat (objectivePrecision a) (ent (projection a.2.1 B) i j) := by
  unfold ent roundedProjection
  rw [SoS.PDTestRat.getD_map_of_eq
    (fun row : List ℚ ↦ row.map (roundRat (objectivePrecision a)))
    (projection a.2.1 B) i.val (d := []) (d' := []) rfl]
  exact SoS.PDTestRat.getD_map_of_eq _ _ _ (d' := 0) (by simp [roundRat])

theorem rounded_entry_bits (a : RoundArgs) (B : Points) (hB : GoodBasis a B)
    (i j : Fin a.2.1) :
    (encRat (ent (roundedProjection a B) i j)).length ≤
      3 * objectivePrecision a + 6 := by
  have hP := (Geometry.basis_geometry a B hB).1
  have he := congrArg (fun M ↦ M i j) (Geometry.projection_eq a B)
  have hentry := projection_entry _ hP i j
  rw [← he] at hentry
  have hrat : |ent (projection a.2.1 B) i j| ≤ 1 := by
    change |((ent (projection a.2.1 B) i j : ℚ) : ℝ)| ≤ 1 at hentry
    apply (Rat.cast_le (K := ℝ)).1
    simpa only [Rat.cast_abs, Rat.cast_one] using hentry
  rw [rounded_entry]
  simpa only [Nat.zero_add] using
    SoS.PolyTime.length_encRat_le_of_small (round_small _ _ hrat)

private theorem exponent_bits (n i j : ℕ) :
    (encList encNat (pairExponent n i j)).length ≤ 5 * n := by
  have hl : (pairExponent n i j).length = n := by simp [pairExponent]
  have h := list_encoding_bound encNat (pairExponent n i j) 2 (by
    intro e he
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 he
    split_ifs <;> decide)
  simpa only [hl, Nat.reduceMul, Nat.reduceAdd, Nat.mul_comm] using h

theorem objective_bits (a : RoundArgs) (B : Points) (hB : GoodBasis a B) :
    (SoS.Solver.encProblem (objective a (roundedProjection a B))).length ≤
      (SoS.Solver.encProblem a.1).length +
        2 * (a.2.1 ^ 2 * (20 * a.1.numVars + 6 * objectivePrecision a + 15)) := by
  let raw := (List.range a.2.1).flatMap fun i ↦ (List.range a.2.1).map fun j ↦
    (pairExponent a.1.numVars i j, ent (roundedProjection a B) i j)
  have hl : raw.length = a.2.1 ^ 2 := by simp [raw, List.length_flatMap, pow_two]
  have ht : ∀ t ∈ raw, (encPair (encList encNat) encRat t).length ≤
      10 * a.1.numVars + 3 * objectivePrecision a + 7 := by
    intro t ht
    obtain ⟨i, hi, ht⟩ := List.mem_flatMap.1 ht
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
    have hi' : i < a.2.1 := List.mem_range.1 hi
    have hj' : j < a.2.1 := List.mem_range.1 hj
    have he := exponent_bits a.1.numVars i j
    have hc := rounded_entry_bits a B hB ⟨i, hi'⟩ ⟨j, hj'⟩
    rw [length_encPair]
    dsimp only [Prod.fst, Prod.snd, Fin.val_mk] at hc ⊢
    omega
  have hr := list_encoding_bound (encPair (encList encNat) encRat) raw _ ht
  have hraw : (SoS.Solver.encRawPoly raw).length ≤
      a.2.1 ^ 2 * (20 * a.1.numVars + 6 * objectivePrecision a + 15) := by
    rw [hl] at hr
    change (encList (encPair (encList encNat) encRat) raw).length ≤ _
    convert hr using 1
    ring
  have hlen : (SoS.Solver.encProblem (objective a (roundedProjection a B))).length ≤
      (SoS.Solver.encProblem a.1).length + 2 * (SoS.Solver.encRawPoly raw).length := by
    rw [SoS.Correct.length_encProblem, SoS.Correct.length_encProblem]
    change 2 * (encNat a.1.1).length + 1 +
      (2 * (encNat a.1.2.1).length + 1 +
        (2 * (encList SoS.Solver.encRawPoly a.1.2.2.1).length + 1 +
          (2 * (SoS.Solver.encRawPoly raw).length + 1 + 0))) ≤ _
    change _ ≤ 2 * (encNat a.1.1).length + 1 +
      (2 * (encNat a.1.2.1).length + 1 +
        (2 * (encList SoS.Solver.encRawPoly a.1.2.2.1).length + 1 +
          (2 * (SoS.Solver.encRawPoly a.1.2.2.2.1).length + 1 +
            (encList SoS.Solver.encRawPoly a.1.2.2.2.2).length))) + _
    omega
  exact hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hraw) _)

def size (a : RoundArgs) : ℕ :=
  (SoS.Solver.encProblem a.1).length + a.2.1 + a.2.2.2.1 +
    (encRat a.2.2.1).length + (encRat a.2.2.2.2).length + 2

def capacity (a : RoundArgs) : ℕ := rankCap a.2.2.1 a.2.2.2.1 + 2

private theorem size_ge_two (a : RoundArgs) : 2 ≤ size a := by unfold size; omega

private theorem capacity_ge_two (a : RoundArgs) : 2 ≤ capacity a := by
  unfold capacity
  omega

private theorem size_fields (a : RoundArgs) :
    (SoS.Solver.encProblem a.1).length ≤ size a ∧ a.2.1 + 1 ≤ size a ∧
      (encRat a.2.2.1).length ≤ size a := by unfold size; omega

theorem objective_size_bound (a : RoundArgs) (B : Points) (hB : GoodBasis a B)
    (hn : a.1.numVars ≤ (SoS.Solver.encProblem a.1).length) :
    (SoS.Solver.encProblem (objective a (roundedProjection a B))).length + 2 ≤
      size a ^ 12 := by
  let S := size a
  have hs : 2 ≤ S := size_ge_two a
  obtain ⟨hL, hd, hγ⟩ := size_fields a
  have hd' : a.2.1 ≤ S := by omega
  have hn' : a.1.numVars ≤ S := hn.trans hL
  have hp := objectivePrecision_bound a
  have ht : 20 * a.1.numVars + 6 * objectivePrecision a + 15 ≤ 79 * S := by
    dsimp only [S] at *
    omega
  have hb := objective_bits a B hB
  have hsq : a.2.1 ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hd' _
  have hprod := Nat.mul_le_mul hsq ht
  have hsmall : (SoS.Solver.encProblem (objective a (roundedProjection a B))).length + 2 ≤
      160 * S ^ 3 := by
    have hS : S ≤ S ^ 3 := Nat.le_self_pow (by omega) S
    nlinarith
  have hlarge : 160 ≤ S ^ 9 := by
    have h := Nat.pow_le_pow_left hs 9
    norm_num at h
    omega
  exact hsmall.trans (by
    have h := Nat.mul_le_mul_right (S ^ 3) hlarge
    simpa only [← pow_add] using h)

theorem basis_size_bound (a : RoundArgs) (B : Points) (hB : GoodBasis a B)
    (hlen : B.length ≤ rankCap a.2.2.1 a.2.2.2.1) :
    (encPoints B).length ≤ (size a * capacity a) ^ 8 := by
  let S := size a
  let K := capacity a
  let A := S * K
  have hs : 2 ≤ S := size_ge_two a
  have hk : 2 ≤ K := capacity_ge_two a
  have ha : 4 ≤ A := Nat.mul_le_mul hs hk
  have hK : K ≤ A := Nat.le_mul_of_pos_left _ (by omega)
  have hcap : rankCap a.2.2.1 a.2.2.2.1 ≤ K := by dsimp [K, capacity]; omega
  have hd : a.2.1 ≤ S := by have h := (size_fields a).2.1; omega
  have hp : greedyPrecision a ≤ 120 * S * K + 2 :=
    (greedyPrecision_bound a).trans (by gcongr; exact (size_fields a).2.1)
  have hb := basis_encoding_bound a B hB hlen
  have hsmall : (encPoints B).length ≤ 2048 * A ^ 2 := by
    have ht : rankCap a.2.2.1 a.2.2.2.1 *
        (2 * (a.2.1 * (6 * greedyPrecision a + 13)) + 1) ≤
        K * (2 * (S * (6 * (120 * S * K + 2) + 13)) + 1) := by gcongr
    have hsq : A ≤ A ^ 2 := Nat.le_self_pow (by omega) A
    dsimp only [A, S, K] at *
    nlinarith
  have hlarge : 2048 ≤ A ^ 6 := by
    have h := Nat.pow_le_pow_left ha 6
    norm_num at h
    omega
  exact hsmall.trans (by
    have h := Nat.mul_le_mul_right (A ^ 2) hlarge
    simpa only [← pow_add] using h)

theorem sufficient_basis_fuel (I : RoundInput) :
    (size (roundArgs I) * capacity (roundArgs I)) ^ 8 ≤ roundFuel I := by
  let a := roundArgs I
  have hs : 1 ≤ size a := (by omega : 1 ≤ 2).trans (size_ge_two a)
  have hk : 1 ≤ capacity a := (by omega : 1 ≤ 2).trans (capacity_ge_two a)
  have he : 8 ≤ 100 * (solverConstant + 1) * (I.problem.degree + 1) := by
    have h := Nat.mul_le_mul (by omega : 1 ≤ solverConstant + 1)
      (by omega : 1 ≤ I.problem.degree + 1)
    nlinarith
  change (size a * capacity a) ^ 8 ≤
    size a ^ (100 * (solverConstant + 1) * (I.problem.degree + 1)) * capacity a ^ 100
  rw [mul_pow]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right hs he) (Nat.pow_le_pow_right hk (by omega))

theorem sufficient_solver_fuel (I : RoundInput) (B : Points)
    (hB : GoodBasis (roundArgs I) B)
    (hn : I.problem.numVars ≤ (SoS.Solver.encProblem I.problem).length) (acc : ℚ × ℚ) :
    SoS.Solver.budget (objective (roundArgs I) (roundedProjection (roundArgs I) B), acc) ≤
      roundFuel I := by
  let a := roundArgs I
  have hsize := objective_size_bound a B hB hn
  have hs : 1 ≤ size a := (by omega : 1 ≤ 2).trans (size_ge_two a)
  have hk : 1 ≤ capacity a := (by omega : 1 ≤ 2).trans (capacity_ge_two a)
  have he : 12 * (I.problem.degree + 1) ≤
      100 * (solverConstant + 1) * (I.problem.degree + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  change ((SoS.Solver.encProblem (objective a (roundedProjection a B))).length + 2) ^
    (I.problem.degree + 1) ≤
      size a ^ (100 * (solverConstant + 1) * (I.problem.degree + 1)) * capacity a ^ 100
  calc
    _ ≤ (size a ^ 12) ^ (I.problem.degree + 1) := Nat.pow_le_pow_left hsize _
    _ ≤ size a ^ (100 * (solverConstant + 1) * (I.problem.degree + 1)) := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right hs he
    _ ≤ _ := Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

theorem sufficient_counts (I : RoundInput) :
    greedyCap I.radius I.rankBound ≤ roundFuel I ∧
      packCount I.radius I.rankBound + 1 ≤ roundFuel I := by
  let a := roundArgs I
  have hle : rankCap I.radius I.rankBound ≤
      (size a * capacity a) ^ 8 := by
    have hc : rankCap I.radius I.rankBound ≤ capacity a := by
      simp only [a, capacity, roundArgs]
      omega
    have hk : capacity a ≤ size a * capacity a := Nat.le_mul_of_pos_left _
      (by have h := size_ge_two a; omega)
    exact (hc.trans hk).trans (Nat.le_self_pow (by omega) _)
  have hf := hle.trans (sufficient_basis_fuel I)
  exact ⟨(greedyCap_le_rankCap a).trans hf, (packCount_le_rankCap a).trans hf⟩

end ABBKS26.Assembly.Exec.RoundCertificates.Bounds
