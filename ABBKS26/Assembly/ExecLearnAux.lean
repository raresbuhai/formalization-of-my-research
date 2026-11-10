module

public import ABBKS26.Assembly.ExecFrame

/-!
# Rational singleton learning

Sharpen the rounded singleton resilience bound, transfer a clean rational filtering pass to
population coordinates, and certify the guarded list program and its canonical output.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.LearnAux

noncomputable section

open Common Matrix MvPolynomial SoS Finset _root_.ABBKS26.Tree
open Select.LearnAux Select.LearnAux.Resilience
open scoped BigOperators MatrixOrder

variable {n k d : ℕ}

private theorem affine_moments
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (j : Fin k)
    (H : Mat d) (b : Vec d) (q : ℕ) (hq : q ≤ 4) :
    coeffNorm1 (empMom (cluster (labels ω) j)
        (fun l ↦ b + H *ᵥ standardizedRounded M ω r l) q -
      IdCov.hmom q (lin b) (quad (H * Hᵀ))) ≤
      ((1 / 10 ^ 8) / (d + 1 : ℝ) ^ 8) *
        (1 + coeffNorm1 (lin b) + coeffNorm1 (quad (H * Hᵀ))) ^ q := by
  let t : ℝ := d + 1
  let A := coeffNorm1 (lin b)
  let Q := coeffNorm1 (quad (H * Hᵀ))
  let δ : ℝ := 1 / (10 ^ 8 * t ^ 12)
  let β := t * (1 + Q)
  have ht : 1 ≤ t := by dsimp only [t]; linarith only [Nat.cast_nonneg (α := ℝ) d]
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hA : 0 ≤ A := coeffNorm1_nonneg _
  have hQ : 0 ≤ Q := coeffNorm1_nonneg _
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hb := affine_error (cluster (labels ω) j) (standardizedRounded M ω r)
    H b q δ β hβ (factor_column_bound H)
    (fun a ha ↦ rounded_moments mode M ε w η Δ D ω r params hp j a (ha.trans hq))
  have hbase : A + β ≤ t * (1 + A + Q) := by
    have hh := mul_nonneg (sub_nonneg.mpr ht) hA
    dsimp only [β]
    nlinarith only [hh]
  have hscale : δ * t ^ q ≤ (1 / 10 ^ 8) / t ^ 8 := by
    calc
      _ ≤ δ * t ^ 4 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hq) hδ
      _ = (1 / (10 : ℝ) ^ 8) / t ^ 8 := by
        dsimp only [δ]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  apply hb.trans
  calc
    _ ≤ δ * (t * (1 + A + Q)) ^ q :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase q) hδ
    _ = (δ * t ^ q) * (1 + A + Q) ^ q := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (by positivity)

/-- The missing tree-to-filter bridge, with the actual rounded clean reference. -/
theorem singleton_resilient
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (j : Fin k) (N : Finset (Fin n)) :
    (singletonReference M j ω r N).Resilient 4 (1 / 10 ^ 8) := by
  intro T a c q hq
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  let R := singletonReference M j ω r N
  let B := CFC.sqrt (M.S j)
  let H := T * B
  let b := T *ᵥ (M.μ j - a)
  let g := standardizedRounded M ω r
  have hBsym : Bᵀ = B := (Robust.RBAux.sqrt_properties _ (hp.1.posDef j)).1
  have hBunit : IsUnit B.det :=
    isUnit_iff_ne_zero.mpr (Robust.RBAux.sqrt_properties _ (hp.1.posDef j)).2.1
  have hH : H * Hᵀ = T * M.S j * Tᵀ := by
    calc
      _ = T * (B * B) * Tᵀ := by simp only [H, transpose_mul, hBsym, mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self _ (hp.1.posDef j).posSemidef.nonneg]
  have hpoint (l : Fin n) (hl : l ∈ cluster (labels ω) j) :
      b + H *ᵥ g l = T *ᵥ (R.clean l - a) := by
    have hj : (ω l).1 = j := (mem_filter.mp hl).2
    have hg : g l = B⁻¹ *ᵥ (R.clean l - M.μ j) := by
      ext i
      simp only [g, standardizedRounded, stdPt_apply, R, singletonReference, hj]
      rfl
    have hrec : B *ᵥ g l = R.clean l - M.μ j := by
      rw [hg, mulVec_mulVec, mul_nonsing_inv _ hBunit, one_mulVec]
    change T *ᵥ (M.μ j - a) + (T * B) *ᵥ g l = _
    rw [← mulVec_mulVec, hrec, ← mulVec_add]
    congr 1
    abel
  have he : empMom (cluster (labels ω) j) (fun l ↦ b + H *ᵥ g l) q =
      C ((cluster (labels ω) j).card : ℝ)⁻¹ *
        ∑ l ∈ cluster (labels ω) j, lin (T *ᵥ (R.clean l - a)) ^ q := by
    rw [empMom, smul_eq_C_mul]
    congr 1
    exact sum_congr rfl fun l hl ↦ by rw [hpoint l hl]
  have hh := affine_moments mode M ε w η Δ D ω r params hp j H b q hq
  change coeffNorm1 (empMom (cluster (labels ω) j) (fun l ↦ b + H *ᵥ g l) q -
    IdCov.hmom q (lin b) (quad (H * Hᵀ))) ≤ _ at hh
  rw [he, hH] at hh
  simpa only [R, b, singletonReference, filter_true] using hh


end

end ABBKS26.Assembly.Exec.LearnAux

namespace ABBKS26.Assembly.Exec.LearnAux

noncomputable section

open Common Matrix _root_.ABBKS26.Tree Select.LearnAux
open FrameAux FrameAux.Linear FrameAux.Features FrameProgram
open scoped BigOperators MatrixOrder

variable {n k d : ℕ}

/-- Removing an LA4 frame with diagonal at least one cannot increase relative error. -/
private theorem unframe_error (C D T : Mat d) (hC : C.PosDef) (hD : Dᵀ = D)
    (hT : T.det ≠ 0) (q : Vec d) (hq : ∀ i, 1 ≤ q i)
    (hdiag : T * C * Tᵀ = diagonal q) :
    frobSq ((CFC.sqrt C)⁻¹ * D * (CFC.sqrt C)⁻¹) ≤
      frobSq (T * D * Tᵀ) := by
  let A := (CFC.sqrt C)⁻¹
  let U := A * T⁻¹
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  have hTtu : IsUnit Tᵀ.det := by rwa [det_transpose]
  have hAt : Aᵀ = A := by
    rw [transpose_nonsing_inv, (Robust.RBAux.sqrt_properties C hC).1]
  have hAA : A * A = C⁻¹ := by
    dsimp only [A]
    rw [← Matrix.mul_inv_rev, (Robust.RBAux.sqrt_properties C hC).2.2]
  have hU : Uᵀ * U = diagonal (fun i ↦ (q i)⁻¹) := by
    calc
      _ = (Tᵀ)⁻¹ * C⁻¹ * T⁻¹ := by
        simp only [U, transpose_mul, hAt, transpose_nonsing_inv, mul_assoc, ← hAA]
      _ = (T * C * Tᵀ)⁻¹ := by simp only [Matrix.mul_inv_rev, mul_assoc]
      _ = _ := by
        rw [hdiag]
        apply inv_eq_left_inv
        rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (ne_of_gt (zero_lt_one.trans_le (hq i)))
  have hbound (v : Vec d) : qform (Uᵀ * U) v ≤ (1 : ℝ) * sqnorm v := by
    rw [hU]
    simp only [qform, mulVec_diagonal, dotProduct, sqnorm, one_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi : (q i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hq i)
    nlinarith only [mul_le_mul_of_nonneg_right hi (sq_nonneg (v i))]
  have hsym : (T * D * Tᵀ)ᵀ = T * D * Tᵀ := by
    simp only [transpose_mul, transpose_transpose, hD, mul_assoc]
  have heq : U * (T * D * Tᵀ) * Uᵀ = A * D * A := by
    simp only [U, transpose_mul, hAt, transpose_nonsing_inv]
    calc
      _ = A * (T⁻¹ * T) * D * (Tᵀ * (Tᵀ)⁻¹) * A := by
        simp only [mul_assoc]
      _ = _ := by rw [nonsing_inv_mul _ hTu, mul_nonsing_inv _ hTtu]; simp
  simpa only [heq, one_pow, one_mul] using
    frobSq_congruence_le U (T * D * Tᵀ) hsym 1 (by norm_num) hbound


/-- The stored rational parameters already satisfy the population accuracy contract. -/
theorem pass_estimate_accurate (M : Mixture k d) (j : Fin k) (hM : M.Valid)
    (R : Robust.Reference n 1 d) (pts : Points) (idx : Fin pts.length → Fin n)
    (w : Vector) (hc : Clean R idx (1 / 2) w)
    (hp : Robust.Pass (liftState idx d pts w) (1 / 2) 0)
    (he : R.contamination ≤ 2 / 10 ^ 10) (hR : R.cov.PosDef)
    (hRerr : frobSq ((CFC.sqrt (M.S j))⁻¹ * R.cov *
      (CFC.sqrt (M.S j))⁻¹ - 1) ≤ 1 / 10 ^ 6)
    (hmean : sqNormIn (M.S j) (R.mean - M.μ j) ≤ 1 / 10 ^ 10) :
    Robust.Accurate M j
      ⟨vectorOf d (mean d pts w), matrixOf d (covariance d pts w)⟩ := by
  let C := (matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)
  let st := liftState idx d pts w
  have he' : R.contamination ≤ min (Robust.maxContamination (1 / 2) 0)
      ((1 / 2) / 400) :=
    he.trans (by norm_num [Robust.maxContamination, Robust.sigmaSq])
  have hi : Robust.IterationInvariant R st (1 / 2) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc.invariant
  obtain ⟨_, _, herr, hm⟩ :=
    Robust.pass_accuracy R st (1 / 2) 0 hi hc.normalized he' hp
  have hCt : Cᵀ = C := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hc.positive.isHermitian.eq
  have hRt : R.covᵀ = R.cov := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  obtain ⟨q, hq, hdiag⟩ := hc.normalized.1
  rw [← hc.covariance_agrees] at herr hdiag
  have hdet : st.frame.det ≠ 0 := hc.invariant.2.2.2.2.1
  have herror := (unframe_error C (C - R.cov) st.frame hc.positive
    (by rw [transpose_sub, hCt, hRt]) hdet q (fun i ↦ (hq i).1) hdiag).trans herr
  have hCerr : frobSq ((CFC.sqrt C)⁻¹ * (C - R.cov) * (CFC.sqrt C)⁻¹) ≤
      1 / 500 := by
    norm_num [Robust.sigmaSq] at herror
    linarith only [herror, he]
  have hcov := covariance_transfer (M.S j) R.cov C (hM.posDef j) hR hc.positive
    hRerr hCerr
  obtain ⟨hpos, hlo, hup⟩ := Robust.RBAux.relative_bounds (M.S j) C (hM.posDef j)
    hCt (hcov.trans (by norm_num))
  refine ⟨hpos, hlo, hup, hcov.trans (by norm_num), ?_⟩
  have hupper := (Robust.RBAux.relative_bounds (M.S j) R.cov (hM.posDef j) hRt
    (hRerr.trans (by norm_num))).2.2
  have hm' := (sqNormIn_comparison (M.S j) R.cov (hM.posDef j) hR 1.1 hupper
    (st.center - R.mean)).trans
    (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1.1))
  have hh := sqNormIn_add_le (M.S j) (hM.posDef j)
    (st.center - R.mean) (R.mean - M.μ j)
  have hsum : st.center - R.mean + (R.mean - M.μ j) = st.center - M.μ j := by abel
  rw [hsum] at hh
  change sqNormIn (M.S j) (st.center - M.μ j) ≤ _
  linarith only [hh, hm', hmean, he]

end

end ABBKS26.Assembly.Exec.LearnAux

namespace ABBKS26.Assembly.Exec.LearnAux

open Common Matrix _root_.ABBKS26.Tree
open Encoding (encRat)
open FrameAux FrameAux.Linear FrameAux.Features FrameProgram
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators MatrixOrder

abbrev Args := ℕ × Points × List ℕ
abbrev encArgs := encPair encUnary (encPair encPoints encIndices)

def block (pts : Points) (N : List ℕ) : Points := N.map fun i ↦ pts.getD i []

def run (q : Args × ℕ) : Option EstimateL :=
  let F := FrameProgram.run .identical
    ((q.1.1, block q.1.2.1 q.1.2.2, 1 / 2, 0, 1), q.2)
  if F.1 then some (F.2.2.1, F.2.2.2.1) else none

theorem run_polytime : ComputableInPolyTime run
    (encPair encArgs encUnary) (encOption encEstimate) := by
  have hb := fst encArgs encUnary
  have hd := (fst _ _).comp hb
  have ht := (snd _ _).comp hb
  have hx := (fst _ _).comp ht
  have hN := (snd _ _).comp ht
  have hp : ComputableInPolyTime
      (fun q : Args × ℕ ↦ block q.1.2.1 q.1.2.2)
      (encPair encArgs encUnary) encPoints := by
    unfold block
    apply mapWithInput hN
    exact .of_tidy (ComputableTidilyInPolyTime.listGetD_binary
      (encA := encVector) (encL := encList encVector) []
      (hx.comp (fst _ _)).tidy (snd _ _).tidy)
  have hF := (rounded_frame_polytime .identical).comp
    ((hd.prod (hp.prod ((const (1 / 2)).prod ((const 0).prod (const 1))))).prod
      (snd _ _))
  unfold run
  exact ite ((fst _ _).comp hF)
    ((optionSome encEstimate).comp
      (((fst _ _).comp ((snd _ _).comp ((snd _ _).comp hF))).prod
        ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp hF))))))
    (const none)

variable {n k d : ℕ}

private theorem list_canonical (v : Vector) (h : v.length = d) :
    List.ofFn (vectorOf d v) = v := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    simp only [List.getElem_ofFn, vectorOf]
    exact List.getD_eq_getElem _ _ hi'

private theorem mean_canonical (pts : Points) (w : Vector) :
    List.ofFn (vectorOf d (mean d pts w)) = mean d pts w :=
  list_canonical _ (by simp [mean])

private theorem covariance_canonical (pts : Points) (w : Vector) :
    List.ofFn (fun i ↦ List.ofFn (matrixOf d (covariance d pts w) i)) =
      covariance d pts w := by
  apply List.ext_getElem
  · simp [covariance, second, table]
  · intro i hi hi'
    simp only [List.getElem_ofFn]
    change List.ofFn (vectorOf d ((covariance d pts w).getD i [])) = _
    rw [List.getD_eq_getElem _ _ hi']
    apply list_canonical
    simp [covariance, second, table] at hi' ⊢

theorem run_canonical (q : Args × ℕ) :
    (run q).map (fun E ↦ estimateList (estimateOf q.1.1 E)) = run q := by
  simp only [run, FrameProgram.run]
  split
  · simp only [Option.map_some, estimateList, estimateOf, reduceCtorEq, ↓reduceIte,
      mean_canonical, covariance_canonical]
  · rfl

theorem block_points {n d : ℕ} (x : Fin n → Fin d → ℚ) (N : Finset (Fin n)) :
    block (pointsOf x) (indexList N) = ABBKS26.RefineAux.blockInput x N := by
  simp only [block, indexList, List.map_map, pointsOf, Function.comp_def]
  have hget (i : Fin n) : (List.ofFn (fun l ↦ List.ofFn (x l))).getD i.val [] =
      List.ofFn (x i) := by simp [List.getD_eq_getElem?_getD]
  simp_rw [hget]
  rw [ABBKS26.RefineAux.blockInput, ← N.listMap_orderEmbOfFin_finRange rfl]
  simp only [List.map_map, List.ofFn_eq_map]
  rfl

private theorem powerTrace_real (pts : Points) (idx : Fin pts.length → Fin n) (w : Vector) (p : ℕ) :
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


/-- A singleton clean prefix has no type-B exit, so the guarded loop passes. -/
private theorem singleton_pass (R : Robust.Reference n 1 d) (pts : Points)
    (hrep : Robust.Represents R pts) (hR : R.Valid (1 / 2))
    (hres : R.Resilient 4 (1 / 10 ^ 8)) (he : R.contamination ≤ 2 / 10 ^ 10)
    (hn : 10 ^ 10 ≤ pts.length) (fuel : ℕ)
    (hf : (pts.length + d + 2) ^ 100 ≤ fuel) :
    ∃ idx : Fin pts.length → Fin n,
      let result := loop d pts (1 / 2) 0 fuel pts.length (List.replicate pts.length 1)
      Clean R idx (1 / 2) result.2.2 ∧ result.1 = true ∧
        Robust.Pass (liftState idx d pts result.2.2) (1 / 2) 0 := by
  have hres' : R.Resilient 4
      (min (1 / 10 ^ 8) (((1 : ℚ) : ℝ) ^ 2 / 10 ^ 8)) := by
    simpa only [Rat.cast_one, one_pow, min_self] using hres
  have he' : R.contamination ≤ min (Robust.maxContamination
      (((1 / 2 : ℚ) : ℝ)) ((0 : ℚ) : ℝ)) (((1 / 2 : ℚ) : ℝ) / 400) :=
    he.trans (by norm_num [Robust.maxContamination, Robust.sigmaSq])
  have hn' : 2 / Robust.maxContamination (((1 / 2 : ℚ) : ℝ)) ((0 : ℚ) : ℝ) ≤
      (pts.length : ℝ) := by
    norm_num [Robust.maxContamination, Robust.sigmaSq]
    omega
  have hR' : R.Valid (((1 / 2 : ℚ) : ℝ)) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hR
  obtain ⟨idx, _, _, hloop⟩ := rounded_loop_invariant R pts (1 / 2) 0 1 fuel
    hrep hR' hres' (by norm_num) (by norm_num) (by norm_num) (by norm_num) he' hn' hf
  refine ⟨idx, ?_⟩
  rcases hloop with ⟨w, hw, hc, _, hnotA⟩ | hpass
  · have hb := (rounded_loop_bound d pts (1 / 2) 0 fuel pts.length
      (List.replicate pts.length 1)).2 w hw
    have hi : Robust.IterationInvariant R (liftState idx d pts w) (1 / 2) := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc.invariant
    apply (hnotA (Select.LearnAux.singleton_typeA R _ hi hc.normalized he ?_)).elim
    intro hpass
    apply hb.2
    apply (passed_agrees pts idx (1 / 2) 0 w).mpr
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero] using hpass
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero] using hpass

private theorem block_represents (R : Robust.Reference n 1 d)
    (x : Fin n → Fin d → ℚ) (N : Finset (Fin n)) (hblock : R.block = N)
    (hobs : ∀ l i, (x l i : ℝ) = R.observed l i) :
    Robust.Represents R (ABBKS26.RefineAux.blockInput x N) := by
  classical
  let pts := ABBKS26.RefineAux.blockInput x N
  have hlen : pts.length = N.card := by simp [pts, ABBKS26.RefineAux.blockInput]
  let idx : Fin pts.length → Fin n :=
    fun l ↦ N.orderEmbOfFin rfl (Fin.cast hlen l)
  have hcast : Function.Injective (Fin.cast hlen) := by
    intro a b h
    exact Fin.ext (congrArg (fun t : Fin N.card ↦ t.val) h)
  refine ⟨hlen.trans (congrArg Finset.card hblock.symm), idx,
    (N.orderEmbOfFin rfl).injective.comp hcast, ?_, ?_⟩
  · rw [hblock]
    ext l
    constructor
    · rintro ⟨a, rfl⟩
      exact N.orderEmbOfFin_mem rfl _
    · intro hl
      let j := (N.orderIsoOfFin rfl).symm ⟨l, hl⟩
      refine ⟨Fin.cast hlen.symm j, ?_⟩
      change N.orderEmbOfFin rfl (Fin.cast hlen (Fin.cast hlen.symm j)) = l
      rw [show Fin.cast hlen (Fin.cast hlen.symm j) = j from Fin.ext rfl]
      change ((N.orderIsoOfFin rfl) ((N.orderIsoOfFin rfl).symm ⟨l, hl⟩)).val = l
      simp only [OrderIso.apply_symm_apply]
  · intro l
    have helem : (ABBKS26.RefineAux.blockInput x N)[l] = List.ofFn (x (idx l)) := by
      change (List.ofFn (fun a : Fin N.card ↦ List.ofFn (x (N.orderEmbOfFin rfl a)))).get l
        = List.ofFn (x (idx l))
      rw [List.get_ofFn]
    change (ABBKS26.RefineAux.blockInput x N)[l].length = d ∧ _
    rw [helem]
    refine ⟨List.length_ofFn, fun j ↦ ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact hobs _ _

/-- Prepared singleton blocks give an accurate result of the same list program. -/
theorem run_accurate (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (fuel : ℕ) (hp : Prepared mode M ε w η Δ D ω r params)
    (hf : localBudget mode k n d params ≤ fuel) (N : Finset (Fin n)) (j : Fin k)
    (hl : leakage ω N {j} ≤ (params (k - 1)).leakage) (hN : w * n / 4 ≤ N.card) :
    ∃ E, (run ((d, pointsOf (fun l i ↦ r ((ω l).1, (ω l).2.2) i), indexList N),
      fuel)).map (estimateOf d) = some E ∧ Robust.Accurate M j E := by
  let x : Fin n → Fin d → ℚ := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let R := Select.LearnAux.singletonReference M j ω r N
  let pts := ABBKS26.RefineAux.blockInput x N
  have hlen : pts.length = N.card := by simp [pts, ABBKS26.RefineAux.blockInput]
  have hrep : Robust.Represents R pts := block_represents R x N rfl (fun _ _ ↦ rfl)
  obtain ⟨hR, hRerr, hm⟩ :=
    Select.LearnAux.singleton_reference_accuracy mode M ε w η Δ D ω r params hp j N
  have hne : (cluster (labels ω) j).Nonempty :=
    Finset.card_pos.mp (SoundAux.good_cluster_pos M ε w η D ω hp.2.2.2.2.2.2.2.2.2.1 j)
  have hv := Select.LearnAux.singletonReference_valid M j ω r N hp.1 hne hR
  have he := Select.LearnAux.singleton_contamination mode M ε w η Δ D ω r params
    hp N j hl hN
  have hr := singleton_resilient mode M ε w η Δ D ω r params hp j N
  have hM := hp.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hlarge, _, _, _⟩ := hp
  have hn : 10 ^ 10 ≤ pts.length := by
    rw [hlen]
    exact_mod_cast hlarge.trans hN
  have hfu : (pts.length + d + 2) ^ 100 ≤ fuel := by
    apply le_trans _ hf
    have hc : N.card ≤ n := (Finset.card_le_univ N).trans_eq (Fintype.card_fin n)
    rw [hlen]
    calc
      _ ≤ (n + d + 2) ^ 100 := Nat.pow_le_pow_left (by omega) _
      _ ≤ (n + d + 2) ^ (1000000000 * (Rounding.solverConstant + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ localBudget mode k n d params := by
        unfold localBudget
        have hb : 0 < (if mode = .centered then 1 else
            (d + 2) ^ (1000000000 * (Rounding.solverConstant + 1) *
              (logInv (params 0).w + 3) ^ 2) *
            (idReserves k params + 2) ^ (1000000000 * (Rounding.solverConstant + 1) *
              (logInv (params 0).w + 3) ^ 2)) := by
          split_ifs
          · exact Nat.zero_lt_one
          · exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
        exact (Nat.le_mul_of_pos_left _ (by positivity)).trans
          (Nat.le_mul_of_pos_right _ hb)
  obtain ⟨idx, hc, hpass, hpassed⟩ := singleton_pass R pts hrep hv hr he hn fuel hfu
  let weights := (loop d pts (1 / 2) 0 fuel pts.length (List.replicate pts.length 1)).2.2
  let E : Robust.Estimate d :=
    ⟨vectorOf d (mean d pts weights), matrixOf d (covariance d pts weights)⟩
  refine ⟨E, ?_, pass_estimate_accurate M j hM R pts idx weights hc hpassed he
    hR hRerr hm⟩
  change (run ((d, pointsOf x, indexList N), fuel)).map (estimateOf d) = some E
  simp only [run, block_points, FrameProgram.run, reduceCtorEq, ↓reduceIte]
  rw [hpass]
  rfl

end ABBKS26.Assembly.Exec.LearnAux
