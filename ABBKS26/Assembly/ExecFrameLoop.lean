module

public import ABBKS26.Assembly.ExecFrameAuxFeatures
public import ABBKS26.Assembly.ExecFrameAuxWeights

/-!
# Loop obligations for the rational frame filter

The program below stores grid weights and recomputes every frame from the original points.
Its history contains every failing iteration, including iterations after the first type B.
Eligibility is attached separately, so validity must not assume a type-A history.

The analytic results are `eligible_certificate_valid`, `first_typeB_certificate`, and
`rounded_loop_invariant`. The machine result is `rounded_frame_polytime`.
All refer to the explicit list program below.
-/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameProgram

open Common Matrix FrameAux FrameAux.Linear FrameAux.Features
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

abbrev Args := ℕ × Points × ℚ × ℚ × ℚ
abbrev DataL := Bool × MatrixL × Vector × MatrixL × List StatisticL × List Bool
abbrev encArgs := encPair encUnary
  (encPair encPoints (encPair encRat (encPair encRat encRat)))
abbrev encDataL := encPair encBool (encPair encMatrix (encPair encVector
  (encPair encMatrix (encPair (encList encStatistic) (encList encBool)))))

variable {n k d : ℕ}

/-- The rational upper approximation to a nonzero column's norm is `2 / scaleL s`.
Thus the stored column has norm between one half and one, with no square root. -/
def columnMatrix (d : ℕ) (H : MatrixL) (j : ℕ) : MatrixL :=
  let s := ((List.range (d * d)).map fun i ↦ ent H i j ^ 2).sum
  table d d fun a b ↦ scaleL s / 2 * ent H (a * d + b) j

private theorem column_scale_bounds {s : ℚ} (hs : 0 < s) :
    1 / 4 ≤ (scaleL s / 2) ^ 2 * s ∧ (scaleL s / 2) ^ 2 * s ≤ 1 := by
  obtain ⟨hl, hu⟩ := scaleL_spec hs
  constructor <;> nlinarith only [hl, hu]

def multiply (d : ℕ) (A B : MatrixL) : MatrixL :=
  table d d fun i j ↦ ((List.range d).map fun r ↦ ent A i r * ent B r j).sum

/-- Expand `(T(x-a))ᵀ A (T(x-a))` into rational coefficients. -/
def pullback (d : ℕ) (T : MatrixL) (a : Vector) (A : MatrixL) : StatisticL :=
  let B := multiply d (table d d fun i j ↦ ent T j i) (multiply d A T)
  (B, (mulVecL d B a).map (fun q ↦ -2 * q), quadL d B a)

def iterationFrame (d : ℕ) (pts : Points) (w : Vector) : MatrixL :=
  whitenL d (covariance d pts w)

def iterationFeatures (d : ℕ) (pts : Points) (w : Vector) : Points :=
  featurePoints d (iterationFrame d pts w) pts w

def iterationCov (d : ℕ) (pts : Points) (w : Vector) : MatrixL :=
  covariance (d * d) (iterationFeatures d pts w) w

/-- All `d²` columns are retained, including harmless zero statistics. -/
def columns (d : ℕ) (pts : Points) (w : Vector) : List StatisticL :=
  let H := power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)
  (List.range (d * d)).map fun j ↦
    pullback d (iterationFrame d pts w) (mean d pts w) (columnMatrix d H j)

def Eligible (pts : Points) (π : ℚ) (w : Vector) : Prop :=
  pts.length - total pts.length w ≤ π * pts.length / 130

instance (pts : Points) (π : ℚ) (w : Vector) : Decidable (Eligible pts π w) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Fixed row-major order within each recorded iteration; flags are never window tests. -/
def certificatePool (d : ℕ) (pts : Points) (π : ℚ) (history : List Vector) :
    List (StatisticL × Bool) :=
  history.flatMap fun w ↦ (columns d pts w).map fun q ↦ (q, decide (Eligible pts π w))

/-- The pool has exactly `d²` entries per recorded iteration, with paired eligibility flags. -/
theorem certificate_pool_bounds (d : ℕ) (pts : Points) (π : ℚ)
    (history : List Vector) :
    (certificatePool d pts π history).length = history.length * d ^ 2 := by
  simp [certificatePool, columns, List.length_flatMap, pow_two]

private theorem multiply_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {A B : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrix)
    (hB : ComputableInPolyTime B input encMatrix) :
    ComputableInPolyTime (fun x ↦ multiply (d x) (A x) (B x)) input encMatrix := by
  apply table_polytime hd hd
  have hb := (fst input encUnary).comp (fst _ encUnary)
  apply sum_polytime (hd.comp hb)
  have hc := hb.comp (fst _ encUnary)
  exact rat_mul'
    (ent' (hA.comp hc) ((snd _ _).comp ((fst _ _).comp (fst _ _))) (snd _ _))
    (ent' (hB.comp hc) (snd _ _) ((snd _ _).comp (fst _ _)))

private theorem pullback_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {T A : α → MatrixL} {a : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hT : ComputableInPolyTime T input encMatrix)
    (ha : ComputableInPolyTime a input encVector)
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ pullback (d x) (T x) (a x) (A x))
      input encStatistic := by
  have ht : ComputableInPolyTime
      (fun x ↦ table (d x) (d x) fun i j ↦ ent (T x) j i) input encMatrix := by
    apply table_polytime hd hd
    exact ent' (hT.comp ((fst input encUnary).comp (fst _ encUnary)))
      (snd _ _) ((snd _ _).comp (fst _ _))
  have hB := multiply_polytime hd ht (multiply_polytime hd hA hT)
  exact hB.prod ((mapWithInput (mulVecL' hd hB ha)
    (rat_mul' (const (-2)) (snd _ _))).prod (quadL' hd hB ha))

private theorem columnMatrix_polytime {α : Type} {input : α ↪ List Bool}
    {d j : α → ℕ} {H : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hH : ComputableInPolyTime H input encMatrix)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x ↦ columnMatrix (d x) (H x) (j x))
      input encMatrix := by
  have he : ComputableInPolyTime (fun p : α × ℕ ↦ ent (H p.1) p.2 (j p.1))
      (encPair input encUnary) encRat :=
    ent' (hH.comp (fst input encUnary)) (snd _ _) (hj.comp (fst _ _))
  have hs : ComputableInPolyTime (fun x ↦
      ((List.range (d x * d x)).map fun i ↦ ent (H x) i (j x) ^ 2).sum)
      input encRat := sum_polytime (unary_mul' hd hd) (rat_sq' he)
  apply table_polytime hd hd
  have hb := (fst input encUnary).comp (fst _ encUnary)
  exact rat_mul' (rat_div' (scaleL_polytime.comp (hs.comp hb)) (const 2))
    (ent' (hH.comp hb)
      (unary_add' (unary_mul' ((snd _ _).comp (fst _ _)) (hd.comp hb)) (snd _ _))
      (hj.comp hb))

private theorem iterationFrame_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ iterationFrame (d x) (pts x) (w x))
      input encMatrix := by
  unfold iterationFrame
  have hC : ComputableInPolyTime (fun x ↦ covariance (d x) (pts x) (w x))
      input encMatrix := covariance_polytime hd hx hw
  exact whitenL_polytime.comp (g := fun x ↦ (d x, covariance (d x) (pts x) (w x)))
    (hd.prod hC)

private theorem iterationFeatures_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ iterationFeatures (d x) (pts x) (w x))
      input encPoints :=
  featurePoints_polytime hd (iterationFrame_polytime hd hx hw) hx hw

private theorem iterationCov_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ iterationCov (d x) (pts x) (w x))
      input encMatrix :=
  covariance_polytime (unary_mul' hd hd) (iterationFeatures_polytime hd hx hw) hw

private theorem columns_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ columns (d x) (pts x) (w x))
      input (encList encStatistic) := by
  have hp : ComputableInPolyTime (fun x ↦ Robust.RBAux.FrameLoop.power (d x) / 2)
      input encUnary := unary_div.comp
    ((unary_mul' (const 2) (unary_add' (unary_mul' hd hd) (const 1))).prod (const 2))
  have hH := power_polytime (unary_mul' hd hd) hp (iterationCov_polytime hd hx hw)
  unfold columns
  apply mapWithInput (range.comp (unary_mul' hd hd))
  apply pullback_polytime (hd.comp (fst _ _))
    ((iterationFrame_polytime hd hx hw).comp (fst _ _))
    ((mean_polytime hd hx hw).comp (fst _ _))
  exact columnMatrix_polytime (hd.comp (fst _ _)) (hH.comp (fst _ _)) (snd _ _)

private theorem eligible_polytime {α : Type} {input : α ↪ List Bool}
    {pts : α → Points} {π : α → ℚ} {w : α → Vector}
    (hx : ComputableInPolyTime pts input encPoints)
    (hπ : ComputableInPolyTime π input encRat)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ decide (Eligible (pts x) (π x) (w x)))
      input encBool := by
  have hn := (length_list encVector).comp hx
  have hr := rat_natCast' (unary_to_binary.comp hn)
  exact rat_le' (rat_sub' hr (total_polytime hn hw))
    (rat_div' (rat_mul' hπ hr) (const 130))

/-- Pool generation is polynomial on arbitrary rational histories, including junk blocks. -/
theorem certificate_pool_polytime : ComputableInPolyTime
    (fun q : (ℕ × Points × ℚ) × List Vector ↦
      certificatePool q.1.1 q.1.2.1 q.1.2.2 q.2)
    (encPair (encPair encUnary (encPair encPoints encRat)) (encList encVector))
    (encList (encPair encStatistic encBool)) := by
  unfold certificatePool
  apply flatMapWithInput (snd _ _)
  let E := encPair encUnary (encPair encPoints encRat)
  have hb := (fst E (encList encVector)).comp (fst _ encVector)
  have hd := (fst encUnary (encPair encPoints encRat)).comp hb
  have hx := ((fst encPoints encRat).comp (snd _ _)).comp hb
  have hπ := ((snd encPoints encRat).comp (snd _ _)).comp hb
  apply mapWithInput (columns_polytime hd hx (snd _ _))
  apply (snd _ _).prod
  exact (eligible_polytime hx hπ (snd _ _)).comp (fst _ _)

/-- Guards inspected before every pass test and reset. -/
def Ready (d : ℕ) (pts : Points) (w : Vector) : Prop :=
  w.length = pts.length ∧ (∀ q ∈ w, 0 ≤ q ∧ q ≤ 1) ∧
    (pts.length : ℚ) / 2 ≤ total pts.length w ∧
    SoS.PDTestRat.test (covariance d pts w) = none

instance (d : ℕ) (pts : Points) (w : Vector) : Decidable (Ready d pts w) := by
  unfold Ready
  infer_instance

def Passed (d : ℕ) (pts : Points) (π R : ℚ) (w : Vector) : Prop :=
  powerTrace (d * d) (Robust.RBAux.FrameLoop.power d) (iterationCov d pts w) ≤
    (16 * (600 / π ^ 2 + 2 * R ^ 2)) ^ Robust.RBAux.FrameLoop.power d

instance (d : ℕ) (pts : Points) (π R : ℚ) (w : Vector) :
    Decidable (Passed d pts π R w) := inferInstanceAs (Decidable (_ ≤ _))

/-- Inactive scores are zeroed before taking the maximum; the reset fixes zero weights. -/
def activeScores (d : ℕ) (pts : Points) (w : Vector) : Vector :=
  let s := scores (d * d) (Robust.RBAux.FrameLoop.power d) (iterationFeatures d pts w) w
  (List.range pts.length).map fun i ↦ if 0 < w.getD i 0 then max 0 (s.getD i 0) else 0

def maximum (s : Vector) : ℚ := s.foldl max 0

/-- Only grid weights are fed to the next iteration; the cap bounds their encoding on junk.
The first component records PASS, the second the failing history and terminal weights. -/
def loop (d : ℕ) (pts : Points) (π R : ℚ) (fuel : ℕ) :
    ℕ → Vector → Bool × List Vector × Vector
  | 0, w => (false, [], w)
  | steps + 1, w =>
    if Ready d pts w then
      if Passed d pts π R w then (true, [], w) else
        let s := activeScores d pts w
        let M := maximum s
        if 0 < M then
          let v := cap encVector fuel [] (reset (resetPrecision pts.length) M w s)
          let result := loop d pts π R fuel steps v
          (result.1, w :: result.2.1, result.2.2)
        else (false, [], w)
    else (false, [], w)

/-- Each recorded failure consumes one iteration, and every recorded weight list passed
the guards. Consequently the complete pool, including ineligible entries, has size `≤ nd²`.
-/
theorem rounded_loop_bound (d : ℕ) (pts : Points) (π R : ℚ) (fuel steps : ℕ)
    (w : Vector) :
    (loop d pts π R fuel steps w).2.1.length ≤ steps ∧
      ∀ v ∈ (loop d pts π R fuel steps w).2.1,
        Ready d pts v ∧ ¬ Passed d pts π R v := by
  induction steps generalizing w with
  | zero => simp [loop]
  | succ steps ih =>
    simp only [loop]
    split_ifs with hr hp hm
    · simp
    · obtain ⟨hb, hv⟩ := ih
        (cap encVector fuel [] (reset (resetPrecision pts.length)
          (maximum (activeScores d pts w)) w (activeScores d pts w)))
      refine ⟨by simpa using Nat.succ_le_succ hb, ?_⟩
      intro v hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact ⟨hr, hp⟩
      · exact hv v hmem
    · simp
    · simp

noncomputable def quadOf (d : ℕ) (q : StatisticL) : Unif.Quad d :=
  ⟨(matrixOf d q.1).map (algebraMap ℚ ℝ),
    fun i ↦ (vectorOf d q.2.1 i : ℝ), (q.2.2 : ℝ)⟩

/-- The typed state uses exactly the rational LA4 frame and feature covariance of the loop. -/
noncomputable def liftState {m : ℕ} (idx : Fin m → Fin n) (d : ℕ)
    (pts : Points) (w : Vector) : Robust.FilterState n d where
  weights := Robust.RBAux.FrameLoop.liftWeights idx (fun i ↦ (w.getD i 0 : ℝ))
  center := fun j ↦ (vectorOf d (mean d pts w) j : ℝ)
  frame := (matrixOf d (iterationFrame d pts w)).map (algebraMap ℚ ℝ)
  featureCov := fun a b ↦ (matrixOf (d * d) (iterationCov d pts w)
    (finProdFinEquiv a) (finProdFinEquiv b) : ℝ)
  power := Robust.RBAux.FrameLoop.power d

/-- Analytic invariants at a type-A prefix, plus the rational/typed covariance agreement. -/
structure Clean {pts : Points} (D : Robust.Reference n k d)
    (idx : Fin pts.length → Fin n) (π : ℚ) (w : Vector) : Prop where
  positive : ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)).PosDef
  invariant : Robust.IterationInvariant D (liftState idx d pts w) π
  normalized : Robust.FrameNormalized D (liftState idx d pts w)
  covariance_agrees : (matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ) =
    Robust.weightedCov D (liftState idx d pts w)

private theorem weights_bounds {pts : Points} {w : Vector}
    (hw : Ready d pts w) (i : Fin pts.length) :
    0 ≤ (w.getD i 0 : ℝ) ∧ (w.getD i 0 : ℝ) ≤ 1 := by
  have hi : i.val < w.length := by rw [hw.1]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact_mod_cast hw.2.1 _ (List.getElem_mem hi)

private theorem ready_positive {pts : Points} {w : Vector} (hw : Ready d pts w) :
    ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)).PosDef := by
  have hc := covariance_real (d := d) (m := pts.length) rfl
    (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  have hpsd : ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)).PosSemidef := by
    rw [hc]
    exact Robust.RBAux.FrameLoop.covariance_psd _
      (fun i ↦ (weights_bounds hw i).1) _
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨hpsd.isHermitian, ?_⟩
  intro v hv
  simpa only [star_trivial] using (SoS.PDTestRat.test_spec (n := d) (covariance d pts w)
    (by simp [covariance, second, table])
    ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)) (fun _ _ ↦ rfl)
    (by simpa only [isHermitian_iff_isSymm, Matrix.IsSymm] using hpsd.isHermitian)).1 hw.2.2.2 v hv

private theorem decoded_mass (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block}) (w : Vector) :
    (liftState idx d pts w).mass D.block = (total pts.length w : ℝ) := by
  rw [Robust.FilterState.mass, Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange]
  simp only [liftState, Robust.RBAux.FrameLoop.liftWeights_apply idx hinj]
  exact_mod_cast (total_eq (w' := fun i : Fin pts.length ↦ w.getD i 0)
    (fun _ ↦ rfl)).symm

private theorem decoded_center (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j) (w : Vector) :
    (liftState idx d pts w).center = ((liftState idx d pts w).mass D.block)⁻¹ •
      ∑ l ∈ D.block, (liftState idx d pts w).weights l • D.observed l := by
  have hm := mean_real (d := d) (m := pts.length) rfl
    (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  rw [Robust.FilterState.mass, Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange,
    Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange]
  simp only [liftState, Robust.RBAux.FrameLoop.liftWeights_apply idx hinj]
  rw [hm]
  simp only [Robust.RBAux.FrameLoop.center, Robust.RBAux.FrameLoop.mass]
  congr 2
  funext i
  congr 1
  funext j
  exact hx i j

private theorem decoded_covariance (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j) (w : Vector) :
    (matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ) =
      Robust.weightedCov D (liftState idx d pts w) := by
  have hm := mean_real (d := d) (m := pts.length) rfl
    (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  rw [covariance_real (d := d) (m := pts.length) rfl
    (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)]
  rw [Robust.weightedCov, Robust.FilterState.mass,
    Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange,
    Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange]
  simp only [liftState, Robust.RBAux.FrameLoop.liftWeights_apply idx hinj, hm]
  have hx' : (fun (i : Fin pts.length) (j : Fin d) ↦ (ent pts i j : ℝ)) =
      fun i ↦ D.observed (idx i) := by
    funext i j
    exact hx i j
  simp only [Robust.RBAux.FrameLoop.covariance, Robust.RBAux.FrameLoop.mass, hx']
  congr 2
  funext i
  rw [show (fun j : Fin d ↦ (ent pts i j : ℝ)) = D.observed (idx i) from funext (hx i)]

private theorem decoded_normalized (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (w : Vector) (hw : Ready d pts w) :
    Robust.FrameNormalized D (liftState idx d pts w) := by
  have hC := ready_positive hw
  obtain ⟨_, hq, _⟩ := rational_frame d (covariance d pts w) hC
  refine ⟨⟨fun i ↦ (vectorOf d (diagonalL d (covariance d pts w)) i : ℝ), ?_, ?_⟩, ?_⟩
  · intro i
    dsimp only
    constructor
    · exact_mod_cast (hq i).1
    · exact_mod_cast (hq i).2
  · rw [← decoded_covariance D pts idx hinj hrange hx w]
    simpa only [liftState, iterationFrame, matrixOf_whitenL, vectorOf_diagonalL] using
      whitenMat_spec_real (matrixOf d (covariance d pts w)) hC
  · have hm := mean_real (d := d) (m := pts.length) rfl
      (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
      (fun _ _ ↦ rfl) (fun _ ↦ rfl)
    have hfeat := featureCovariance_real (d := d) (m := pts.length) rfl
      (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
      (T := iterationFrame d pts w) (T' := matrixOf d (iterationFrame d pts w))
      (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    rw [← hm] at hfeat
    dsimp only
    rw [Robust.FilterState.mass,
      Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange,
      Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange,
      Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange]
    simp only [liftState, Robust.RBAux.FrameLoop.liftWeights_apply idx hinj]
    have hx' (i : Fin pts.length) :
        (fun j : Fin d ↦ (ent pts i j : ℝ)) = D.observed (idx i) := funext (hx i)
    simp only [iterationCov, iterationFeatures, featureCovariance, hx'] at hfeat ⊢
    ext a b
    have hh := congrFun (congrFun hfeat a) b
    simpa only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply,
      Pi.smul_apply, Finset.sum_apply, smul_eq_mul, iterationFeatures] using hh

private theorem matrixOf_multiply (d : ℕ) (A B : MatrixL) :
    matrixOf d (multiply d A B) = matrixOf d A * matrixOf d B := by
  ext i j
  exact (table_rep _ i j).trans
    (sum_fin_eq_list (fun r : Fin d ↦ ent A i r * ent B r j)
      (fun r ↦ ent A i r * ent B r j) (fun _ ↦ rfl)).symm

private theorem quad_ext {q r : Unif.Quad d} (hA : q.A = r.A)
    (hb : q.b = r.b) (hc : q.c = r.c) : q = r := by
  cases q
  cases r
  cases hA
  cases hb
  cases hc
  rfl

private theorem pullback_agrees (d : ℕ) (T : MatrixL) (a : Vector) (A : MatrixL) :
    quadOf d (pullback d T a A) = Robust.RBAux.FrameLoop.frameQuad
      ((matrixOf d T).map (algebraMap ℚ ℝ)) (fun i ↦ (vectorOf d a i : ℝ))
      ((matrixOf d A).map (algebraMap ℚ ℝ)) := by
  let B := multiply d (table d d fun i j ↦ ent T j i) (multiply d A T)
  have hB : matrixOf d B = (matrixOf d T)ᵀ * matrixOf d A * matrixOf d T := by
    have ht : matrixOf d (table d d fun i j ↦ ent T j i) = (matrixOf d T)ᵀ := by
      ext i j
      exact table_rep _ i j
    simp only [B, matrixOf_multiply, ht, Matrix.mul_assoc]
  have hBr : (matrixOf d B).map (algebraMap ℚ ℝ) =
      ((matrixOf d T).map (algebraMap ℚ ℝ))ᵀ *
        (matrixOf d A).map (algebraMap ℚ ℝ) *
        (matrixOf d T).map (algebraMap ℚ ℝ) := by
    rw [hB, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
  apply quad_ext
  · exact hBr
  · funext i
    change (((mulVecL d B a).map (fun q : ℚ ↦ (-2 : ℚ) * q)).getD i 0 : ℝ) = _
    have he := mulVecL_rep (C := B) (M := matrixOf d B) (v := a)
      (v' := vectorOf d a) (fun _ _ ↦ rfl) (fun _ ↦ rfl) i
    rw [show (0 : ℚ) = -2 * 0 by ring, List.getD_map, he]
    push_cast
    have hh : ((matrixOf d B).map (algebraMap ℚ ℝ) *ᵥ
        (fun j ↦ (vectorOf d a j : ℝ))) i = ((matrixOf d B *ᵥ vectorOf d a) i : ℝ) := by
      simp [mulVec, dotProduct]
    rw [← hh]
    rw [hBr]
    simp only [Robust.RBAux.FrameLoop.frameQuad, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · change (quadL d B a : ℝ) = _
    rw [quadL_eq (C := B) (M := matrixOf d B) (v' := vectorOf d a)
      (fun _ _ ↦ rfl) (fun _ ↦ rfl), ← quad_cast]
    change qform ((matrixOf d B).map (algebraMap ℚ ℝ)) _ = _
    rw [hBr]
    simpa only [Matrix.mul_assoc, Matrix.transpose_transpose,
      Robust.RBAux.FrameLoop.frameQuad] using
      (Robust.RBAux.qform_conjugate ((matrixOf d T).map (algebraMap ℚ ℝ))ᵀ
        ((matrixOf d A).map (algebraMap ℚ ℝ)) (fun i ↦ (vectorOf d a i : ℝ)))

private theorem columnMatrix_entry (d : ℕ) (H : MatrixL) (j : ℕ)
    (a b : Fin d) :
    (matrixOf d (columnMatrix d H j)).map (algebraMap ℚ ℝ) a b =
      ((scaleL (((List.range (d * d)).map fun i ↦ ent H i j ^ 2).sum) / 2 : ℚ) : ℝ) *
        (ent H (a * d + b) j : ℝ) := by
  have h := table_rep (fun a b ↦
    scaleL (((List.range (d * d)).map fun i ↦ ent H i j ^ 2).sum) / 2 *
      ent H (a * d + b) j) a b
  change ((ent (columnMatrix d H j) a b : ℚ) : ℝ) = _
  exact_mod_cast h

private theorem columnMatrix_norm (d : ℕ) (H : MatrixL) (j : ℕ) :
    frobSq ((matrixOf d (columnMatrix d H j)).map (algebraMap ℚ ℝ)) ≤ 1 := by
  let s := ((List.range (d * d)).map fun i ↦ ent H i j ^ 2).sum
  have hs : 0 ≤ s := by
    apply List.sum_nonneg
    intro q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    exact sq_nonneg _
  have hsum : (s : ℝ) = ∑ i : Fin (d * d), (ent H i j : ℝ) ^ 2 := by
    have hh := congrArg (Rat.cast : ℚ → ℝ)
      (sum_fin_eq_list (fun i : Fin (d * d) ↦ ent H i j ^ (2 : ℕ))
        (fun i ↦ ent H i j ^ (2 : ℕ)) (fun _ ↦ rfl)).symm
    push_cast at hh
    simpa only [s, Rat.cast_list_sum] using hh
  have hnorm : frobSq ((matrixOf d (columnMatrix d H j)).map (algebraMap ℚ ℝ)) =
      ((scaleL s / 2 : ℚ) : ℝ) ^ 2 * (s : ℝ) := by
    simp only [frobSq, columnMatrix_entry, mul_pow]
    simp_rw [← Finset.mul_sum]
    rw [hsum]
    congr 1
    rw [← Fintype.sum_prod_type (f := fun ab : Fin d × Fin d ↦
      (ent H (ab.1.val * d + ab.2.val) j : ℝ) ^ 2)]
    have he := (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).sum_comp
      (fun i ↦ (ent H i j : ℝ) ^ 2)
    refine Eq.trans ?_ he
    apply Finset.sum_congr rfl
    intro ab _
    congr 3
    change ab.1.val * d + ab.2.val = ab.2.val + d * ab.1.val
    simp only [Nat.mul_comm, Nat.add_comm]
  rw [hnorm]
  by_cases hz : s = 0
  · simp [hz]
  · have hp : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    exact_mod_cast (column_scale_bounds hp).2

private theorem iterationPower_entry (pts : Points) (idx : Fin pts.length → Fin n)
    (w : Vector) (p : ℕ) (a b : Fin d) (j : Fin (d * d)) :
    (ent (power (d * d) p (iterationCov d pts w)) (a * d + b) j : ℝ) =
      ((liftState idx d pts w).featureCov ^ p) (a, b) (finProdFinEquiv.symm j) := by
  have hp := power_reindex_real d p (iterationCov d pts w)
  have h := congrFun (congrFun hp (a, b)) (finProdFinEquiv.symm j)
  simp only [coe_reindexRingEquiv, reindex_apply, Equiv.symm_symm,
    submatrix_apply, Equiv.apply_symm_apply] at h
  change (ent (power (d * d) p (iterationCov d pts w))
    (b.val + d * a.val) j : ℝ) = _ at h
  have hcov : ((matrixOf (d * d) (iterationCov d pts w)).map
      (algebraMap ℚ ℝ)).submatrix finProdFinEquiv finProdFinEquiv =
        (liftState idx d pts w).featureCov := by
    ext a b
    simp only [submatrix_apply, Matrix.map_apply, eq_ratCast, liftState]
  rw [hcov] at h
  simpa only [Nat.mul_comm, Nat.add_comm] using h

private theorem rationalColumn_scale (pts : Points) (idx : Fin pts.length → Fin n)
    (w : Vector) (j : Fin d × Fin d)
    (hN : (∑ a, ((liftState idx d pts w).featureCov ^
      ((liftState idx d pts w).power / 2)) a j ^ 2) ≠ 0) :
    let st := liftState idx d pts w
    let H := power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)
    ∃ t : ℝ, 1 / 2 ≤ t ∧ t ≤ 1 ∧
      (matrixOf d (columnMatrix d H (finProdFinEquiv j))).map (algebraMap ℚ ℝ) =
        t • Robust.RBAux.FrameLoop.normalizedColumn st.featureCov st.power j := by
  let st := liftState idx d pts w
  let H := power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)
  let s := ((List.range (d * d)).map fun i ↦ ent H i (finProdFinEquiv j) ^ 2).sum
  let N := ∑ a, (st.featureCov ^ (st.power / 2)) a j ^ 2
  have hsum : (s : ℝ) = N := by
    have hs := congrArg (Rat.cast : ℚ → ℝ) (sum_fin_eq_list
      (fun i : Fin (d * d) ↦ ent H i (finProdFinEquiv j) ^ (2 : ℕ))
      (fun i ↦ ent H i (finProdFinEquiv j) ^ (2 : ℕ)) (fun _ ↦ rfl)).symm
    push_cast at hs
    rw [show (s : ℝ) = ∑ i : Fin (d * d), (ent H i (finProdFinEquiv j) : ℝ) ^ 2 by
      simpa only [s, Rat.cast_list_sum] using hs]
    rw [← (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).sum_comp]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    have he := iterationPower_entry pts idx w (Robust.RBAux.FrameLoop.power d / 2)
      a.1 a.2 (finProdFinEquiv j)
    simp only [Equiv.symm_apply_apply] at he
    have hv : (finProdFinEquiv a).val = a.1.val * d + a.2.val := by
      change a.2.val + d * a.1.val = a.1.val * d + a.2.val
      simp only [Nat.mul_comm, Nat.add_comm]
    rw [hv]
    simpa only [H, st, liftState] using he
  have hN0 : 0 < N := lt_of_le_of_ne (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    (Ne.symm hN)
  have hs0 : 0 < s := by
    have hh : (0 : ℝ) < (s : ℝ) := hsum.symm ▸ hN0
    exact_mod_cast hh
  let c : ℝ := ((scaleL s / 2 : ℚ) : ℝ)
  let t := c * Real.sqrt N
  have hc : 0 < c := by dsimp only [c]; exact_mod_cast (div_pos (scaleL_pos s) (by norm_num))
  have ht0 : 0 ≤ t := mul_nonneg hc.le (Real.sqrt_nonneg N)
  have ht : t ^ 2 = c ^ 2 * (s : ℝ) := by
    change (c * Real.sqrt N) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt hN0.le, hsum]
  have hb := column_scale_bounds hs0
  have hl : (1 : ℝ) ≤ 4 * t ^ 2 := by
    rw [ht]
    dsimp only [c]
    exact_mod_cast (show (1 : ℚ) ≤ 4 * ((scaleL s / 2) ^ 2 * s) by
      linarith only [hb.1])
  have hu : t ^ 2 ≤ 1 := by
    rw [ht]
    dsimp only [c]
    exact_mod_cast hb.2
  refine ⟨t, by nlinarith only [hl, ht0], by nlinarith only [hu, ht0], ?_⟩
  ext a b
  rw [columnMatrix_entry]
  have he := iterationPower_entry pts idx w (Robust.RBAux.FrameLoop.power d / 2)
    a b (finProdFinEquiv j)
  simp only [Equiv.symm_apply_apply] at he
  rw [he]
  change c * (st.featureCov ^ (st.power / 2)) (a, b) j =
    t * ((st.featureCov ^ (st.power / 2)) (a, b) j / Real.sqrt N)
  dsimp only [t]
  field_simp [Real.sqrt_ne_zero'.mpr hN0]

private theorem columnMatrix_symmetric (D : Robust.Reference n k d)
    (pts : Points) (idx : Fin pts.length → Fin n) (w : Vector)
    (hn : Robust.FrameNormalized D (liftState idx d pts w)) (j : Fin (d * d)) :
    let H := power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)
    let A := (matrixOf d (columnMatrix d H j)).map (algebraMap ℚ ℝ)
    Aᵀ = A := by
  let st := liftState idx d pts w
  have hh := Robust.RBAux.FrameLoop.power_column_symmetric D st
    (Robust.RBAux.FrameLoop.power_spec d).2.1 hn (finProdFinEquiv.symm j)
  have hp := power_reindex_real d (Robust.RBAux.FrameLoop.power d / 2)
    (iterationCov d pts w)
  have he (a b : Fin d) :
      (ent (power (d * d) (Robust.RBAux.FrameLoop.power d / 2)
        (iterationCov d pts w)) (a * d + b) j : ℝ) =
      (st.featureCov ^ (st.power / 2)) (a, b) (finProdFinEquiv.symm j) := by
    have h := congrFun (congrFun hp (a, b)) (finProdFinEquiv.symm j)
    simp only [coe_reindexRingEquiv, reindex_apply, Equiv.symm_symm,
      submatrix_apply, Equiv.apply_symm_apply] at h
    change (ent (power (d * d) (Robust.RBAux.FrameLoop.power d / 2)
      (iterationCov d pts w)) (b.val + d * a.val) j : ℝ) = _ at h
    have hcov : ((matrixOf (d * d) (iterationCov d pts w)).map
        (algebraMap ℚ ℝ)).submatrix finProdFinEquiv finProdFinEquiv = st.featureCov := by
      ext a b
      simp only [submatrix_apply, Matrix.map_apply, eq_ratCast, st, liftState]
    rw [hcov] at h
    simpa only [Nat.mul_comm, Nat.add_comm, st, liftState] using h
  ext a b
  dsimp only [Matrix.transpose_apply]
  simp only [columnMatrix_entry, he]
  congr 1
  exact congrFun (congrFun hh a) b

/-- Every eligible rational column has the population variance bound, even after type B.
No type-A accounting or clean-prefix invariant is assumed here. -/
theorem eligible_certificate_valid (D : Robust.Reference n k d) (pts : Points)
    (π R : ℚ) (w : Vector) (hrep : Robust.Represents D pts) (hD : D.Valid π)
    (hres : D.Resilient 4 (1 / 10000)) (hπ : (π : ℝ) ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R)
    (hw : Ready d pts w) (hel : Eligible pts π w) (q : StatisticL)
    (hq : q ∈ columns d pts w) :
    ∀ l, Robust.statVariance D.model l (quadOf d q) ≤ (20 / (π : ℝ)) ^ 2 := by
  obtain ⟨idx, hinj, hrange, hx⟩ := hrep.2
  have hobs (i : Fin pts.length) (j : Fin d) :
      (ent pts i j : ℝ) = D.observed (idx i) j := by
    simpa only [ent, List.getD_eq_getElem _ _ i.isLt, Fin.getElem_fin] using (hx i).2 j
  let st := liftState idx d pts w
  have hnorm := decoded_normalized D pts idx hinj hrange hobs w hw
  have hw' := Robust.RBAux.FrameLoop.liftWeights_bounds idx hinj
    (fun i ↦ (w.getD i 0 : ℝ)) (weights_bounds hw)
  have hel' : D.block.card - st.mass D.block ≤ (π : ℝ) * D.block.card / 130 := by
    rw [decoded_mass D pts idx hinj hrange w, ← hrep.1]
    exact_mod_cast hel
  obtain ⟨hM, ha⟩ := Robust.RBAux.eligible_frame_bounds D st π R hD hres hπ he
    hw' hel' hnorm (decoded_center D pts idx hinj hrange hobs w)
  simp only [columns, List.mem_map, List.mem_range] at hq
  obtain ⟨j, hj, rfl⟩ := hq
  let H := power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)
  let A := (matrixOf d (columnMatrix d H j)).map (algebraMap ℚ ℝ)
  have hA : Aᵀ = A := columnMatrix_symmetric D pts idx w hnorm ⟨j, hj⟩
  have hnA := columnMatrix_norm d H j
  have hT : st.frame.det ≠ 0 := by
    have hd := (rational_frame d (covariance d pts w) (ready_positive hw)).1
    change ((matrixOf d (whitenL d (covariance d pts w))).map (algebraMap ℚ ℝ)).det ≠ 0
    have hdet := (algebraMap ℚ ℝ).map_det (matrixOf d (whitenL d (covariance d pts w)))
    simp only [RingHom.mapMatrix_apply] at hdet
    rw [← hdet]
    exact (map_ne_zero (algebraMap ℚ ℝ)).mpr hd
  intro l
  rw [pullback_agrees]
  change Robust.RBAux.FrameLoop.quadVariance D.model l
    (Robust.RBAux.FrameLoop.frameQuad st.frame st.center A) ≤ _
  rw [Robust.RBAux.FrameLoop.frameQuad_variance _ _ _ _ _ hA]
  exact Robust.quadratic_resilience D π (1 / 10000) hD (by norm_num) hres
    st.frame A st.center hT hA hnA hM ha l

open Robust Robust.RBAux Robust.RBAux.FrameLoop in
private theorem spread_double_of_between (D : Reference n k d) (π R : ℝ) (hD : D.Valid π)
    (hres : D.Resilient 4 (1 / 10000)) (hπ1 : π ≤ 1)
    (T A : Mat d) (a : Vec d) (hA : Aᵀ = A) (hn : frobSq A ≤ 1)
    (hM : LE (T * D.cov * Tᵀ) (6 • (1 : Mat d)))
    (ha : sqnorm (T *ᵥ (a - D.mean)) ≤ 1)
    (hbet : sigmaSq π R ≤ betweenVariance D T D.mean A) :
    ∃ i j, 2 * R ≤ |quadCenter D.model i (frameQuad T a A) -
      quadCenter D.model j (frameQuad T a A)| := by
  classical
  by_contra! hnone
  let w := D.model.weight
  let c := fun j ↦ quadCenter D.model j (frameQuad T a A)
  let c₀ := fun j ↦ (A * (T * D.model.cov j * Tᵀ)).trace +
    qform A (T *ᵥ (D.model.mean j - D.mean))
  let δ := T *ᵥ (a - D.mean)
  let ν := fun j ↦ T *ᵥ (D.model.mean j - D.mean)
  let t := fun j ↦ (A *ᵥ δ) ⬝ᵥ ν j
  let μ := ∑ j, w j * c j
  have hw : ∀ j, 0 ≤ w j := fun j ↦ hD.1.1.le.trans (hD.1.2.1 j)
  have hw1 : ∑ j, w j = 1 := hD.1.2.2.1
  obtain ⟨l, _⟩ := hD.2.2.2.2.1
  let j₀ := D.label l
  have hvarc : (∑ j, w j * (c j - μ) ^ 2) ≤ R ^ 2 := by
    obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ c
      (Finset.univ_nonempty_iff.mpr ⟨j₀⟩)
    obtain ⟨b, _, hb⟩ := Finset.exists_min_image Finset.univ c
      (Finset.univ_nonempty_iff.mpr ⟨j₀⟩)
    have hgap := (le_abs_self (c a - c b)).trans (hnone a b).le
    apply (FilterAux.weighted_variance_min w c hw1 ((c a + c b) / 2)).trans
    calc
      _ ≤ ∑ j, w j * R ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hw j)
        have hu := ha j (Finset.mem_univ j)
        have hl := hb j (Finset.mem_univ j)
        have hup : 0 ≤ R - (c j - (c a + c b) / 2) := by linarith
        have hlo : 0 ≤ R + (c j - (c a + c b) / 2) := by linarith
        nlinarith only [mul_nonneg hup hlo]
      _ = R ^ 2 := by rw [← Finset.sum_mul, hw1, one_mul]
  have hAδ : sqnorm (A *ᵥ δ) ≤ 1 := by
    have hh := FilterAux.sqnorm_mulVec_le A δ
    have h₁ := mul_le_mul_of_nonneg_right hn (Rounding.DetRoundAux.sqnorm_nonneg δ)
    change sqnorm δ ≤ 1 at ha
    nlinarith only [hh, h₁, ha]
  have htj (j : Fin k) : π * t j ^ 2 ≤ (601 / 100 : ℝ) := by
    have hh := population_second_frame D π hD hres T hM j (A *ᵥ δ)
    have h₁ := mul_le_mul_of_nonneg_right (hD.1.2.1 j) (sq_nonneg (t j))
    change w j * t j ^ 2 ≤ _ at hh
    nlinarith only [hh, h₁, hAδ]
  have htsum : π * (∑ j, w j * t j ^ 2) ≤ (601 / 100 : ℝ) := by
    calc
      _ = ∑ j, w j * (π * t j ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j, w j * (601 / 100 : ℝ) :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (htj j) (hw j)
      _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]
  have hc₀ (j : Fin k) : c₀ j = c j + 2 * t j - qform A δ := by
    have hshift : T *ᵥ (D.model.mean j - a) = ν j - δ := by
      dsimp only [ν, δ]
      rw [← mulVec_sub]
      congr 1
      abel
    have hh := frameQuad_center D.model j T A a hA
    rw [hshift, FilterAux.qform_sub_symmetric A hA] at hh
    dsimp only [c₀, c, t, ν]
    linarith only [hh]
  have hvar₀ : betweenVariance D T D.mean A ≤
      2 * R ^ 2 + 8 * (∑ j, w j * t j ^ 2) := by
    apply (FilterAux.weighted_variance_min w c₀ hw1 (μ - qform A δ)).trans
    calc
      _ ≤ ∑ j, w j * (2 * (c j - μ) ^ 2 + 8 * t j ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (hw j)
        rw [hc₀]
        nlinarith only [sq_nonneg (c j - μ - 2 * t j)]
      _ = 2 * (∑ j, w j * (c j - μ) ^ 2) +
          8 * (∑ j, w j * t j ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := by linarith only [hvarc]
  have hπ : 0 < π := hD.1.1
  have hσ : sigmaSq π R * π ^ 2 = 600 + 2 * R ^ 2 * π ^ 2 := by
    dsimp only [sigmaSq]
    rw [add_mul, div_mul_cancel₀ _ (sq_pos_of_pos hπ).ne']
  have h₁ := mul_le_mul_of_nonneg_right (hbet.trans hvar₀) (sq_nonneg π)
  have h₂ := mul_le_mul_of_nonneg_left htsum hπ.le
  have h₃ := mul_le_mul_of_nonneg_left hπ1 (by norm_num : (0 : ℝ) ≤ 601 / 100)
  nlinarith only [h₁, h₂, h₃, hσ]

private theorem invariant_eligible (D : Robust.Reference n k d)
    (st : Robust.FilterState n d) (π R : ℝ)
    (hi : Robust.IterationInvariant D st π) (hπ : π ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R) :
    D.block.card - st.mass D.block ≤ π * D.block.card / 130 := by
  rcases hi with ⟨hD, _, hw, _, _, _, _, _, _, _, hrem, _, _⟩
  have heπ := Robust.RBAux.contamination_small_pi D π R hD.1.1 hπ he
  have he1 : D.contamination ≤ 1 / 10000 := by linarith
  have hε : 0 ≤ D.contamination := by unfold Robust.Reference.contamination; positivity
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  obtain ⟨hgB, hgR, _⟩ := Robust.RBAux.FrameLoop.reference_count_bounds D π hD he1
  have hgN : (D.good.card : ℝ) ≤ D.reference.card := by
    exact_mod_cast Finset.card_le_card hD.2.1
  have hgm : (D.good.card : ℝ) ≤ D.block.card := by
    exact_mod_cast Finset.card_le_card hD.2.2.1
  have hNm : (D.reference.card : ℝ) ≤ 2 * D.block.card := by
    nlinarith only [hgR, hgm, mul_le_mul_of_nonneg_right he1 hN.le]
  have hrem' : D.reference.card - st.mass D.good ≤
      4 * D.contamination * D.reference.card := by
    rwa [← div_eq_inv_mul, div_le_iff₀ hN] at hrem
  have hgood : st.mass D.good ≤ st.mass D.block :=
    Finset.sum_le_sum_of_subset_of_nonneg hD.2.2.1 (fun l _ _ ↦ (hw l).1)
  have hεNm := mul_le_mul_of_nonneg_left hNm hε
  have hsmall := mul_le_mul_of_nonneg_right heπ
    (show (0 : ℝ) ≤ D.block.card by positivity)
  nlinarith only [hgB, hgN, hrem', hgood, hεNm, hsmall,
    mul_nonneg hD.1.1.le (show (0 : ℝ) ≤ D.block.card by positivity)]

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

private theorem statCenter_smul (F : FrameModel k d) (j : Fin k)
    (T A : Mat d) (a : Vec d) (t : ℝ) (hA : Aᵀ = A) :
    Robust.statCenter F j (Robust.RBAux.FrameLoop.frameQuad T a (t • A)) =
      t * Robust.statCenter F j (Robust.RBAux.FrameLoop.frameQuad T a A) := by
  have hAt : (t • A)ᵀ = t • A := by rw [transpose_smul, hA]
  change Robust.RBAux.FrameLoop.quadCenter F j
    (Robust.RBAux.FrameLoop.frameQuad T a (t • A)) =
      t * Robust.RBAux.FrameLoop.quadCenter F j (Robust.RBAux.FrameLoop.frameQuad T a A)
  rw [Robust.RBAux.FrameLoop.frameQuad_center _ _ _ _ _ hAt,
    Robust.RBAux.FrameLoop.frameQuad_center _ _ _ _ _ hA]
  simp only [Matrix.smul_mul, Matrix.trace_smul, qform, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]
  ring

/-- A failing first type-B state supplies a column with the requested population spread.
The factor-two rational normalization loss must be included in the F6 spread estimate. -/
theorem first_typeB_certificate (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (π R : ℚ) (w : Vector)
    (hrep : Robust.Represents D pts) (hπ : π ≤ 1 / 2) (hR : 0 ≤ R)
    (he : D.contamination ≤ min (Robust.maxContamination π R) ((π : ℝ) / 400))
    (hc : Clean D idx π w) (hf : ¬ Passed d pts π R w)
    (hb : ¬ Robust.TypeA D (liftState idx d pts w)) :
    ∃ q ∈ columns d pts w, ∃ i j,
      (R : ℝ) ≤ |Robust.statCenter D.model i (quadOf d q) -
        Robust.statCenter D.model j (quadOf d q)| := by
  have _ := hrep
  let st := liftState idx d pts w
  have hi := hc.invariant
  have hD := hi.1
  have hres := hi.2.1
  have hπ1 : (π : ℝ) ≤ 1 := by
    exact_mod_cast hπ.trans (by norm_num : (1 / 2 : ℚ) ≤ 1)
  have hel := invariant_eligible D st π R hi hπ1 (he.trans (min_le_left _ _))
  obtain ⟨hM, ha⟩ := Robust.RBAux.eligible_frame_bounds D st π R hD hres hπ1
    (he.trans (min_le_left _ _)) hi.2.2.1 hel hc.normalized hi.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨j, hN, hbet⟩ := Robust.typeB_candidate D st π R hi hc.normalized he
    (fun hp ↦ hf ((passed_agrees pts idx π R w).mpr hp)) hb
  let A := Robust.RBAux.FrameLoop.normalizedColumn st.featureCov st.power j
  have hA := Robust.RBAux.FrameLoop.normalizedColumn_symm D st
    (Robust.RBAux.FrameLoop.power_spec d).2.1 hc.normalized j
  obtain ⟨i, l, hspread⟩ := spread_double_of_between D π R hD hres hπ1
    st.frame A st.center hA (Robust.RBAux.FrameLoop.normalizedColumn_norm _ _ _)
    hM ha hbet
  obtain ⟨t, ht, _, heq⟩ := rationalColumn_scale pts idx w j hN
  let H := power (d * d) (Robust.RBAux.FrameLoop.power d / 2) (iterationCov d pts w)
  let q := pullback d (iterationFrame d pts w) (mean d pts w)
    (columnMatrix d H (finProdFinEquiv j))
  refine ⟨q, ?_, i, l, ?_⟩
  · apply List.mem_map.mpr
    exact ⟨(finProdFinEquiv j).val, List.mem_range.mpr (finProdFinEquiv j).isLt, rfl⟩
  · dsimp only [q]
    rw [pullback_agrees, heq]
    change (R : ℝ) ≤ |Robust.statCenter D.model i
      (Robust.RBAux.FrameLoop.frameQuad st.frame st.center (t • A)) -
        Robust.statCenter D.model l
          (Robust.RBAux.FrameLoop.frameQuad st.frame st.center (t • A))|
    rw [statCenter_smul _ _ _ _ _ _ hA, statCenter_smul _ _ _ _ _ _ hA,
      ← mul_sub, abs_mul, abs_of_nonneg (by linarith only [ht] : 0 ≤ t)]
    have hR0 : (0 : ℝ) ≤ R := by exact_mod_cast hR
    change 2 * (R : ℝ) ≤ |Robust.statCenter D.model i
      (Robust.RBAux.FrameLoop.frameQuad st.frame st.center A) -
        Robust.statCenter D.model l (Robust.RBAux.FrameLoop.frameQuad st.frame st.center A)|
      at hspread
    nlinarith only [ht, hspread, hR0, mul_nonneg (by linarith only [ht] : 0 ≤ t - 1 / 2)
      (abs_nonneg (Robust.statCenter D.model i
        (Robust.RBAux.FrameLoop.frameQuad st.frame st.center A) -
          Robust.statCenter D.model l
            (Robust.RBAux.FrameLoop.frameQuad st.frame st.center A)))]

private theorem ready_of_positive (pts : Points) (π : ℚ) (w : Vector)
    (hlen : w.length = pts.length) (hwb : ∀ q ∈ w, 0 ≤ q ∧ q ≤ 1)
    (hel : Eligible pts π w) (hπ : π ≤ 1)
    (hC : ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)).PosDef) :
    Ready d pts w := by
  refine ⟨hlen, hwb, ?_, ?_⟩
  · have hn : (0 : ℚ) ≤ pts.length := by positivity
    have hh := mul_le_mul_of_nonneg_right hπ hn
    dsimp only [Eligible] at hel
    linarith only [hel, hh, hn]
  · have hspec := SoS.PDTestRat.test_spec (n := d) (covariance d pts w)
      (by simp only [covariance, second, table_length])
      ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)) (fun _ _ ↦ rfl)
      (by simpa only [isHermitian_iff_isSymm, Matrix.IsSymm] using hC.isHermitian)
    cases ht : SoS.PDTestRat.test (covariance d pts w) with
    | none => rfl
    | some z =>
      obtain ⟨v, _, hv, hneg⟩ := hspec.2 z ht
      have hv' : (fun i ↦ (v i : ℝ)) ≠ 0 := by
        intro hz
        apply hv
        funext i
        have hi : (v i : ℝ) = 0 := congrFun hz i
        exact_mod_cast hi
      have hp := hC.dotProduct_mulVec_pos hv'
      simp only [star_trivial] at hp
      exact False.elim (not_lt_of_ge hneg hp)

private theorem clean_of_slack (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (π R : ℚ) (hD : D.Valid π) (hres : D.Resilient 4 (1 / 10000)) (hπ1 : π ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R)
    (w : Vector) (hlen : w.length = pts.length) (hwb : ∀ q ∈ w, 0 ≤ q ∧ q ≤ 1)
    (e : ℝ) (he0 : e ≤ D.contamination * D.reference.card)
    (hbal : D.good.card - (liftState idx d pts w).mass D.good ≤
      (D.block \ D.good).card - (liftState idx d pts w).mass (D.block \ D.good) + e) :
    Ready d pts w ∧ Clean D idx π w ∧ Eligible pts π w := by
  let st := liftState idx d pts w
  have hπr : (π : ℝ) ≤ 1 := by exact_mod_cast hπ1
  have heπ := Robust.RBAux.contamination_small_pi D π R hD.1.1 hπr he
  have he1 : D.contamination ≤ 1 / 10000 := by linarith only [heπ, hπr]
  have hε : 0 ≤ D.contamination := by unfold Robust.Reference.contamination; positivity
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hw : ∀ i : Fin pts.length, 0 ≤ (w.getD i 0 : ℝ) ∧ (w.getD i 0 : ℝ) ≤ 1 := by
    intro i
    have hi : i.val < w.length := by rw [hlen]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact_mod_cast hwb _ (List.getElem_mem hi)
  have hweights := Robust.RBAux.FrameLoop.liftWeights_bounds idx hinj _ hw
  obtain ⟨hgB, hgR, hmN⟩ := Robust.RBAux.FrameLoop.reference_count_bounds D π hD he1
  have hgm : (D.good.card : ℝ) ≤ D.block.card := by
    exact_mod_cast Finset.card_le_card hD.2.2.1
  have hNm : (D.reference.card : ℝ) ≤ 2 * D.block.card := by
    nlinarith only [hgR, hgm, mul_le_mul_of_nonneg_right he1 hN.le]
  have hcard : ((D.block \ D.good).card : ℝ) + D.good.card = D.block.card := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hD.2.2.1
  have hbadcard : ((D.block \ D.good).card : ℝ) ≤ D.contamination * D.block.card := by
    linarith only [hgB, hcard]
  have hbad0 : 0 ≤ st.mass (D.block \ D.good) :=
    Finset.sum_nonneg fun l _ ↦ (hweights l).1
  have hsplit : st.mass (D.block \ D.good) + st.mass D.good = st.mass D.block :=
    Finset.sum_sdiff hD.2.2.1
  have hrem4 : D.reference.card - st.mass D.good ≤
      4 * D.contamination * D.reference.card := by
    have hh := mul_le_mul_of_nonneg_left hmN hε
    nlinarith only [hbal, he0, hgR, hbadcard, hbad0, hh,
      mul_nonneg hε hN.le]
  have hel : D.block.card - st.mass D.block ≤ (π : ℝ) * D.block.card / 130 := by
    have hh := mul_le_mul_of_nonneg_left hNm hε
    have hhπ := mul_le_mul_of_nonneg_right heπ
      (show (0 : ℝ) ≤ D.block.card by positivity)
    nlinarith only [hbal, he0, hcard, hsplit, hbadcard, hbad0, hh, hhπ,
      mul_nonneg hD.1.1.le (show (0 : ℝ) ≤ D.block.card by positivity)]
  obtain ⟨hrem, hupper, hlower, hbad⟩ := Robust.RBAux.eligible_mass_bounds D st π hD
    hπr heπ hweights hel
  have hW : 0 < st.mass D.block := by linarith only [hlower, hN]
  have hcov := Robust.RBAux.retained_covariance_lower D st π hD hres hweights
    hrem hupper hW
  have hC : ((matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ)).PosDef := by
    rw [decoded_covariance D pts idx hinj hrange hx w]
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · rw [← decoded_covariance D pts idx hinj hrange hx w,
        covariance_real (d := d) (m := pts.length) rfl
          (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
          (fun _ _ ↦ rfl) (fun _ ↦ rfl)]
      exact (Robust.RBAux.FrameLoop.covariance_psd _ (fun i ↦ (hw i).1) _).1
    · intro v hv
      have hh := hcov v
      have hp := hD.2.2.2.2.2.1.dotProduct_mulVec_pos hv
      simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul, star_trivial] at hh hp ⊢
      linarith only [hh, hp]
  have hcard' : D.block.card = pts.length := by
    have hh := Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange (fun _ ↦ (1 : ℕ))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one] using hh
  have hel' : Eligible pts π w := by
    rw [decoded_mass D pts idx hinj hrange w, hcard'] at hel
    exact_mod_cast hel
  have hready := ready_of_positive pts π w hlen hwb hel' hπ1 hC
  have hnorm := decoded_normalized D pts idx hinj hrange hx w hready
  have hdet : st.frame.det ≠ 0 := by
    have hd := (rational_frame d (covariance d pts w) hC).1
    have hh := (algebraMap ℚ ℝ).map_det (matrixOf d (whitenL d (covariance d pts w)))
    simp only [RingHom.mapMatrix_apply] at hh
    change ((matrixOf d (whitenL d (covariance d pts w))).map (algebraMap ℚ ℝ)).det ≠ 0
    rw [← hh]
    exact (map_ne_zero (algebraMap ℚ ℝ)).mpr hd
  refine ⟨hready, ⟨hC, ?_, hnorm, decoded_covariance D pts idx hinj hrange hx w⟩, hel'⟩
  refine ⟨hD, hres, hweights, ?_, hdet, ?_,
    (Robust.RBAux.FrameLoop.power_spec d).1, (Robust.RBAux.FrameLoop.power_spec d).2.1,
    (Robust.RBAux.FrameLoop.power_spec d).2.2, hbad, ?_, ?_,
    decoded_center D pts idx hinj hrange hx w⟩
  · intro l hl
    apply Robust.RBAux.FrameLoop.liftWeights_zero
    simpa only [hrange, Set.mem_ofPred_eq] using hl
  · rw [hnorm.2]
    apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr hW.le)
    apply Matrix.posSemidef_sum
    intro l _
    apply Matrix.PosSemidef.smul _ (hweights l).1
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
      (Robust.feature (st.frame *ᵥ (D.observed l - st.center)) -
        (st.mass D.block)⁻¹ • ∑ i ∈ D.block,
          st.weights i • Robust.feature (st.frame *ᵥ (D.observed i - st.center)))
  · rw [← div_eq_inv_mul, div_le_iff₀ hN]
    exact hrem4
  · have hgood : st.mass D.good ≤ st.mass D.block :=
      Finset.sum_le_sum_of_subset_of_nonneg hD.2.2.1 (fun l _ _ ↦ (hweights l).1)
    have hh := mul_le_mul_of_nonneg_right he1 hN.le
    nlinarith only [hrem4, hgood, hh]

private theorem feature_entry (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n)
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (w : Vector) (i : Fin pts.length) (a : Fin d × Fin d) :
    (ent (iterationFeatures d pts w) i (finProdFinEquiv a) : ℝ) =
      Robust.feature ((liftState idx d pts w).frame *ᵥ
        (D.observed (idx i) - (liftState idx d pts w).center)) a := by
  have hm := mean_real (d := d) (m := pts.length) rfl
    (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  have hh := featurePoints_real (d := d) (m := pts.length) rfl
    (x := fun i j ↦ ent pts i j) (w' := fun i ↦ w.getD i 0)
    (T := iterationFrame d pts w) (T' := matrixOf d (iterationFrame d pts w))
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) i (finProdFinEquiv a)
  rw [← hm, Equiv.symm_apply_apply] at hh
  have hi : (fun j : Fin d ↦ (ent pts i j : ℝ)) = D.observed (idx i) := funext (hx i)
  rw [hi] at hh
  exact hh

private theorem feature_mean_entry (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (w : Vector) (a : Fin d × Fin d) :
    (vectorOf (d * d) (mean (d * d) (iterationFeatures d pts w) w)
      (finProdFinEquiv a) : ℝ) =
      (((liftState idx d pts w).mass D.block)⁻¹ • ∑ l ∈ D.block,
        (liftState idx d pts w).weights l • Robust.feature
          ((liftState idx d pts w).frame *ᵥ
            (D.observed l - (liftState idx d pts w).center))) a := by
  have hm := mean_real (d := d * d) (m := pts.length)
    (featurePoints_length d (iterationFrame d pts w) pts w)
    (x := fun i j ↦ ent (iterationFeatures d pts w) i j)
    (w' := fun i ↦ w.getD i 0) (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  have hh := congrFun hm (finProdFinEquiv a)
  simp only [Robust.RBAux.FrameLoop.center, Robust.RBAux.FrameLoop.mass,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at hh
  simp_rw [feature_entry D pts idx hx w] at hh
  rw [Robust.FilterState.mass,
    Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange,
    Robust.RBAux.FrameLoop.sum_index D.block idx hinj hrange]
  simpa only [liftState, Robust.RBAux.FrameLoop.liftWeights_apply idx hinj,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, iterationFeatures] using hh

private theorem form_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (A : Matrix κ κ ℝ) (v : κ → ℝ) :
    (v ∘ e) ⬝ᵥ (A.submatrix e e *ᵥ (v ∘ e)) = v ⬝ᵥ (A *ᵥ v) := by
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  exact comp_equiv_dotProduct_comp_equiv v (A *ᵥ v) e

private theorem scores_agree (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (w : Vector) (i : Fin pts.length) :
    ((scores (d * d) (Robust.RBAux.FrameLoop.power d) (iterationFeatures d pts w) w).getD
      i 0 : ℝ) = (liftState idx d pts w).score D (idx i) := by
  let P := iterationFeatures d pts w
  let p := Robust.RBAux.FrameLoop.power d
  let y : Fin (d * d) → ℝ := fun a ↦ (ent P i a : ℝ) -
    (vectorOf (d * d) (mean (d * d) P w) a : ℝ)
  have hm := mean_real (d := d * d) (m := pts.length)
    (featurePoints_length d (iterationFrame d pts w) pts w)
    (x := fun i j ↦ ent P i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  have hc := covariance_real (d := d * d) (m := pts.length)
    (featurePoints_length d (iterationFrame d pts w) pts w)
    (x := fun i j ↦ ent P i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl)
  have hs := scores_real (d := d * d) (m := pts.length)
    (featurePoints_length d (iterationFrame d pts w) pts w)
    (x := fun i j ↦ ent P i j) (w' := fun i ↦ w.getD i 0)
    (fun _ _ ↦ rfl) (fun _ ↦ rfl) p i
  rw [← hm, ← hc] at hs
  have hp := power_reindex_real d p (iterationCov d pts w)
  have hcov : reindexRingEquiv ℝ finProdFinEquiv.symm
      ((matrixOf (d * d) (iterationCov d pts w)).map (algebraMap ℚ ℝ)) =
        (liftState idx d pts w).featureCov := by
    ext a b
    simp only [coe_reindexRingEquiv, reindex_apply, Equiv.symm_symm, submatrix_apply,
      Matrix.map_apply, eq_ratCast, liftState]
  rw [hcov] at hp
  have hy : y ∘ finProdFinEquiv = Robust.feature
      ((liftState idx d pts w).frame *ᵥ (D.observed (idx i) - (liftState idx d pts w).center)) -
        (((liftState idx d pts w).mass D.block)⁻¹ • ∑ l ∈ D.block,
          (liftState idx d pts w).weights l • Robust.feature
            ((liftState idx d pts w).frame *ᵥ
              (D.observed l - (liftState idx d pts w).center))) := by
    funext a
    exact congrArg₂ (· - ·) (feature_entry D pts idx hx w i a)
      (feature_mean_entry D pts idx hinj hrange hx w a)
  have hform := form_reindex (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d))
    ((matrixOf (d * d) (power (d * d) p (iterationCov d pts w))).map (algebraMap ℚ ℝ)) y
  have hp' := hp
  simp only [coe_reindexRingEquiv, reindex_apply, Equiv.symm_symm] at hp'
  rw [hp', hy, matrixOf_power_real] at hform
  exact hs.trans hform.symm

private theorem foldl_max_mem (s : Vector) (a : ℚ) : s.foldl max a ∈ a :: s := by
  induction s generalizing a with
  | nil => simp
  | cons b s ih =>
    simp only [List.foldl_cons]
    have h := ih (max a b)
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      rcases le_total a b with hab | hba
      · simp [max_eq_right hab]
      · simp [max_eq_left hba]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)


private theorem typed_score_total (D : Robust.Reference n k d)
    (st : Robust.FilterState n d) (π : ℝ) (hi : Robust.IterationInvariant D st π)
    (hf : Robust.FrameNormalized D st) (hW : 0 < st.mass D.block) :
    (∑ i ∈ D.block, st.weights i * st.score D i) =
      st.mass D.block * (st.featureCov ^ (st.power + 1)).trace := by
  let A := st.featureCov
  let H := A ^ (st.power / 2)
  let a := fun j i ↦ H i j
  let φ := fun i ↦ Robust.feature (st.frame *ᵥ (D.observed i - st.center)) -
    (st.mass D.block)⁻¹ • ∑ l ∈ D.block,
      st.weights l • Robust.feature (st.frame *ᵥ (D.observed l - st.center))
  have hH : Hᵀ = H := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (hi.2.2.2.2.2.1.pow (st.power / 2)).1.eq
  have hHH : H * H = A ^ st.power := by
    dsimp only [H]
    rw [← pow_add]
    congr 1
    obtain ⟨q, hq⟩ := hi.2.2.2.2.2.2.1
    omega
  have hscore (i : Fin n) : st.score D i = ∑ j, (a j ⬝ᵥ φ i) ^ 2 := by
    change φ i ⬝ᵥ (A ^ st.power *ᵥ φ i) = _
    rw [← hHH]
    exact Robust.FilterAux.column_square_sum H hH _
  have hvariance (j : Fin d × Fin d) :
      (∑ i ∈ D.block, st.weights i * (a j ⬝ᵥ φ i) ^ 2) =
        st.mass D.block * (a j ⬝ᵥ (A *ᵥ a j)) := by
    have hh := Robust.FilterAux.covariance_sum_form D.block st.weights φ
      (st.mass D.block) (a j)
    change _ = st.mass D.block * (a j ⬝ᵥ (st.featureCov *ᵥ a j))
    rw [hf.2]
    rw [hh, ← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]
  have hform : (∑ j, a j ⬝ᵥ (A *ᵥ a j)) = (A ^ (st.power + 1)).trace := by
    rw [Robust.FilterAux.column_form_sum, hH, trace_mul_cycle, hHH, ← pow_succ]
  simp_rw [hscore, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [hvariance]
  rw [← Finset.mul_sum, hform]

private theorem foldl_max_bounds (s : Vector) (a : ℚ) :
    a ≤ s.foldl max a ∧ ∀ q ∈ s, q ≤ s.foldl max a := by
  induction s generalizing a with
  | nil => simp
  | cons b s ih =>
    obtain ⟨ha, hs⟩ := ih (max a b)
    refine ⟨(le_max_left a b).trans ha, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (le_max_right a q).trans ha
    · exact hs q hq

private theorem activeScores_length (d : ℕ) (pts : Points) (w : Vector) :
    (activeScores d pts w).length = pts.length := by
  simp only [activeScores, List.length_map, List.length_range]

private theorem activeScores_entry (d : ℕ) (pts : Points) (w : Vector)
    (i : Fin pts.length) :
    (activeScores d pts w).getD i 0 = if 0 < w.getD i 0 then
      max 0 ((scores (d * d) (Robust.RBAux.FrameLoop.power d)
        (iterationFeatures d pts w) w).getD i 0) else 0 :=
  getD_map_range _ _ i.isLt

private theorem activeScores_nonneg (d : ℕ) (pts : Points) (w : Vector) :
    ∀ q ∈ activeScores d pts w, 0 ≤ q := by
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

private theorem activeScores_le (d : ℕ) (pts : Points) (w : Vector)
    (i : Fin pts.length) :
    (activeScores d pts w).getD i 0 ≤ maximum (activeScores d pts w) := by
  have hi : i.val < (activeScores d pts w).length := by
    rw [activeScores_length]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact (foldl_max_bounds (activeScores d pts w) 0).2 _ (List.getElem_mem hi)

private theorem clean_maximum_pos (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (π R : ℚ) (w : Vector) (hc : Clean D idx π w) (hf : ¬ Passed d pts π R w) :
    0 < maximum (activeScores d pts w) := by
  let st := liftState idx d pts w
  have hi := hc.invariant
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hi.1.2.2.2.2.1
  have hW : 0 < st.mass D.block := by
    have hh := hi.2.2.2.2.2.2.2.2.2.2.2.1
    linarith only [hh, hN]
  have hπ : (0 : ℝ) < π := hi.1.1.1
  have hσ : 0 < Robust.sigmaSq π R :=
    add_pos_of_pos_of_nonneg (div_pos (by norm_num) (sq_pos_of_pos hπ))
      (mul_nonneg (by norm_num) (sq_nonneg (R : ℝ)))
  have hlarge := Robust.FilterAux.failed_trace_large st.featureCov
    hi.2.2.2.2.2.1 st.power hi.2.2.2.2.2.2.2.1 (Robust.sigmaSq π R) hσ
    (by simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using
      hi.2.2.2.2.2.2.2.2.1)
    (lt_of_not_ge (fun hp ↦ hf ((passed_agrees pts idx π R w).mpr hp)))
  have htrace0 : 0 ≤ (st.featureCov ^ st.power).trace :=
    (hi.2.2.2.2.2.1.pow st.power).trace_nonneg
  have htrace : 0 < (st.featureCov ^ (st.power + 1)).trace :=
    lt_of_le_of_lt (by positivity) hlarge
  have hs0 (l : Fin n) : 0 ≤ st.score D l := by
    exact (hi.2.2.2.2.2.1.pow st.power).dotProduct_mulVec_nonneg _
  have htotal : 0 < ∑ l ∈ D.block, st.weights l * st.score D l := by
    rw [typed_score_total D st π hi hc.normalized hW]
    exact mul_pos hW htrace
  obtain ⟨l, hl, hpos⟩ := Finset.sum_pos_iff_of_nonneg
    (fun l (_ : l ∈ D.block) ↦ mul_nonneg (hi.2.2.1 l).1 (hs0 l)) |>.mp htotal
  have hlrange : l ∈ Set.range idx := by rwa [hrange]
  obtain ⟨i, rfl⟩ := hlrange
  have hwi : 0 < w.getD i 0 := by
    have hw' := Robust.RBAux.FrameLoop.liftWeights_apply idx hinj
      (fun i ↦ (w.getD i 0 : ℝ)) i
    have hp : 0 < st.weights (idx i) := by
      nlinarith only [hpos, hs0 (idx i), (hi.2.2.1 (idx i)).1]
    change 0 < Robust.RBAux.FrameLoop.liftWeights idx _ (idx i) at hp
    rw [hw'] at hp
    exact_mod_cast hp
  have hsi : 0 < (scores (d * d) (Robust.RBAux.FrameLoop.power d)
      (iterationFeatures d pts w) w).getD i 0 := by
    have hp : 0 < st.score D (idx i) := by
      nlinarith only [hpos, hs0 (idx i), (hi.2.2.1 (idx i)).1]
    rw [← scores_agree D pts idx hinj hrange hx w i] at hp
    exact_mod_cast hp
  have ha : 0 < (activeScores d pts w).getD i 0 := by
    rw [activeScores_entry]
    simp only [hwi, ↓reduceIte]
    exact hsi.trans_le (le_max_right _ _)
  exact ha.trans_le (activeScores_le d pts w i)

private theorem reset_getD {m : ℕ} (p : ℕ) (M : ℚ) (w s : Vector)
    (hw : w.length = m) (hs : s.length = m) (i : Fin m) :
    (reset p M w s).getD i 0 = Robust.updateWeight p (w.getD i 0) (s.getD i 0) M := by
  have hiw : i.val < w.length := by rw [hw]; exact i.isLt
  have his : i.val < s.length := by rw [hs]; exact i.isLt
  have hi : i.val < (reset p M w s).length := by
    simpa only [reset_length, hw, hs, min_self] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [reset, List.getElem_map, List.getElem_zip]
  rw [List.getD_eq_getElem _ _ hiw, List.getD_eq_getElem _ _ his]

private theorem vector_encoding_bound (w : Vector) (b : ℕ)
    (h : ∀ q ∈ w, (encRat q).length ≤ b) :
    (encVector w).length ≤ w.length * (2 * b + 1) := by
  induction w with
  | nil => simp [encVector]
  | cons q w ih =>
    have hq := h q List.mem_cons_self
    have hw := ih (fun r hr ↦ h r (List.mem_cons_of_mem _ hr))
    simp only [encVector, length_encList, List.map_cons, List.sum_cons] at *
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem reset_encoding_bound (p : ℕ) (M : ℚ) (w s : Vector)
    (h : ∀ q ∈ reset p M w s, 0 ≤ q ∧ q ≤ 1) :
    (encVector (reset p M w s)).length ≤ (reset p M w s).length * (6 * p + 13) := by
  apply (vector_encoding_bound _ (3 * p + 6) ?_).trans_eq
  · ring
  · intro q hq
    obtain ⟨ws, _, rfl⟩ := List.mem_map.mp hq
    suffices hsmall : SoS.PolyTime.Small p 0 (Robust.updateWeight p ws.1 ws.2 M) by
      simpa only [Nat.zero_add] using SoS.PolyTime.length_encRat_le_of_small hsmall
    refine ⟨?_, ⌊(2 : ℚ) ^ p * (ws.1 * (1 - ws.2 / M))⌋, ?_⟩
    · simpa only [pow_zero, abs_of_nonneg (h _ hq).1] using (h _ hq).2
    · unfold Robust.updateWeight roundRat
      field_simp

private theorem grid_fuel_bound (m d : ℕ) :
    m * (6 * resetPrecision m + 13) ≤ (m + d + 2) ^ 100 := by
  by_cases hm : m = 0
  · simp [hm]
  have h3 : 3 ≤ m + 2 := by omega
  have hp := Nat.pow_le_pow_left h3 5
  norm_num at hp
  have hpoly : m * (6 * resetPrecision m + 13) ≤ 133 * (m + 2) ^ 2 := by
    dsimp only [resetPrecision]
    nlinarith only
  calc
    _ ≤ 133 * (m + 2) ^ 2 := hpoly
    _ ≤ (m + 2) ^ 5 * (m + 2) ^ 2 := Nat.mul_le_mul_right _ (by omega : 133 ≤ (m + 2) ^ 5)
    _ = (m + 2) ^ 7 := by rw [← pow_add]
    _ ≤ (m + d + 2) ^ 7 := Nat.pow_le_pow_left (by omega) 7
    _ ≤ (m + d + 2) ^ 100 := Nat.pow_le_pow_right (by omega) (by omega)

private theorem reset_good (d : ℕ) (pts : Points) (w : Vector)
    (hw : Ready d pts w) (fuel : ℕ) (hf : (pts.length + d + 2) ^ 100 ≤ fuel)
    (hM : 0 < maximum (activeScores d pts w)) :
    let s := activeScores d pts w
    let M := maximum s
    let v := reset (resetPrecision pts.length) M w s
    v.length = pts.length ∧ (∀ q ∈ v, 0 ≤ q ∧ q ≤ 1) ∧
      cap encVector fuel [] v = v ∧
      (support (fun i : Fin pts.length ↦ v.getD i 0)).card <
        (support (fun i : Fin pts.length ↦ w.getD i 0)).card := by
  let s := activeScores d pts w
  let M := maximum s
  let p := resetPrecision pts.length
  let v := reset p M w s
  have hs : s.length = pts.length := activeScores_length d pts w
  have hv : v.length = pts.length := by simp only [v, reset_length, hw.1, hs, min_self]
  have hwb (i : Fin pts.length) : 0 ≤ w.getD i 0 ∧ w.getD i 0 ≤ 1 := by
    exact_mod_cast weights_bounds hw i
  have hsb (i : Fin pts.length) : 0 ≤ s.getD i 0 := by
    have hi : i.val < s.length := by rw [hs]; exact i.isLt
    rw [List.getD_eq_getElem _ _ hi]
    exact activeScores_nonneg d pts w _ (List.getElem_mem hi)
  have hvb : ∀ q ∈ v, 0 ≤ q ∧ q ≤ 1 := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hq
    have hin : i < pts.length := by rwa [hv] at hi
    have hreset := reset_getD p M w s hw.1 hs ⟨i, hin⟩
    rw [List.getD_eq_getElem _ _ hi] at hreset
    rw [hreset]
    have hh := updateWeight_bounds p (hwb ⟨i, hin⟩).1 (hsb ⟨i, hin⟩) hM
      (activeScores_le d pts w ⟨i, hin⟩)
    exact ⟨hh.1, hh.2.trans (hwb ⟨i, hin⟩).2⟩
  have hcap : cap encVector fuel [] v = v := by
    apply cap_eq
    exact (reset_encoding_bound p M w s hvb).trans
      (by rw [hv]; exact (grid_fuel_bound pts.length d).trans hf)
  have hmem : M ∈ s := by
    rcases List.mem_cons.mp (foldl_max_mem s 0) with hz | hmem
    · exact False.elim (hM.ne' hz)
    · exact hmem
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
  have hin : i < pts.length := by rwa [hs] at hi
  have he' : s.getD i 0 = M := by rw [List.getD_eq_getElem _ _ hi]; exact he
  have hwi : 0 < w.getD i 0 := by
    by_contra hn
    have hh := activeScores_entry d pts w ⟨i, hin⟩
    simp only [hn, ↓reduceIte] at hh
    have hz : M = 0 := he'.symm.trans hh
    exact hM.ne' hz
  refine ⟨hv, hvb, hcap, ?_⟩
  have hh := reset_support_lt p (fun i : Fin pts.length ↦ w.getD i 0)
    (fun i : Fin pts.length ↦ s.getD i 0) M (fun i ↦ (hwb i).1) hsb hM
    (activeScores_le d pts w) ⟨i, hin⟩ hwi he'
  change (support (fun i : Fin pts.length ↦ v.getD i 0)).card < _
  have hvfun : (fun i : Fin pts.length ↦ v.getD i 0) =
      fun i : Fin pts.length ↦ Robust.updateWeight p (w.getD i 0) (s.getD i 0) M :=
    funext (reset_getD p M w s hw.1 hs)
  rw [hvfun]
  exact hh

private def preimage {pts : Points} (idx : Fin pts.length → Fin n) (S : Finset (Fin n)) :
    Finset (Fin pts.length) := Finset.univ.filter fun i ↦ idx i ∈ S

private def balance (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (w : Vector) (e : ℚ) : Prop :=
    (∑ i ∈ preimage idx D.good, (1 - w.getD i 0)) ≤
      (∑ i ∈ preimage idx (D.block \ D.good), (1 - w.getD i 0)) + e

private theorem sum_preimage {α : Type} [AddCommMonoid α]
    (D : Robust.Reference n k d) (pts : Points) (idx : Fin pts.length → Fin n)
    (hinj : Function.Injective idx) (hrange : Set.range idx = {l | l ∈ D.block})
    (S : Finset (Fin n)) (hS : S ⊆ D.block) (f : Fin n → α) :
    (∑ l ∈ S, f l) = ∑ i ∈ preimage idx S, f (idx i) := by
  symm
  apply Finset.sum_bij (fun i _ ↦ idx i)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact hinj hij
  · intro l hl
    have hh : l ∈ Set.range idx := by rw [hrange]; exact hS hl
    obtain ⟨i, rfl⟩ := hh
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩
  · intro i _
    rfl

private theorem loss_preimage (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (S : Finset (Fin n)) (hS : S ⊆ D.block) (w : Vector) :
    (S.card : ℝ) - (liftState idx d pts w).mass S =
      ((∑ i ∈ preimage idx S, (1 - w.getD i 0) : ℚ) : ℝ) := by
  have hh := sum_preimage D pts idx hinj hrange S hS
    (fun l ↦ (1 : ℝ) - (liftState idx d pts w).weights l)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    liftState, Robust.RBAux.FrameLoop.liftWeights_apply idx hinj] at hh
  push_cast
  simpa only [Robust.FilterState.mass, liftState, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_one] using hh

private theorem balance_clean (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (π R : ℚ) (hD : D.Valid π) (hres : D.Resilient 4 (1 / 10000)) (hπ1 : π ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R)
    (w : Vector) (hlen : w.length = pts.length) (hwb : ∀ q ∈ w, 0 ≤ q ∧ q ≤ 1)
    (e : ℚ) (he0 : (e : ℝ) ≤ D.contamination * D.reference.card)
    (hbal : balance D pts idx w e) :
    Ready d pts w ∧ Clean D idx π w ∧ Eligible pts π w := by
  apply clean_of_slack D pts idx hinj hrange hx π R hD hres hπ1 he w hlen hwb e he0
  rw [loss_preimage D pts idx hinj hrange D.good hD.2.2.1,
    loss_preimage D pts idx hinj hrange (D.block \ D.good) Finset.sdiff_subset]
  exact_mod_cast hbal

private theorem active_weighted (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (π : ℚ) (w : Vector) (hw : Ready d pts w) (hc : Clean D idx π w)
    (i : Fin pts.length) :
    ((w.getD i 0 * (activeScores d pts w).getD i 0 : ℚ) : ℝ) =
      (liftState idx d pts w).weights (idx i) * (liftState idx d pts w).score D (idx i) := by
  have hw' := Robust.RBAux.FrameLoop.liftWeights_apply idx hinj
    (fun i ↦ (w.getD i 0 : ℝ)) i
  change _ = Robust.RBAux.FrameLoop.liftWeights idx _ (idx i) * _
  rw [hw']
  by_cases hwi : 0 < w.getD i 0
  · have hs0 : 0 ≤ (liftState idx d pts w).score D (idx i) :=
      (hc.invariant.2.2.2.2.2.1.pow (liftState idx d pts w).power).dotProduct_mulVec_nonneg _
    rw [← scores_agree D pts idx hinj hrange hx w i] at hs0 ⊢
    have hs0' : 0 ≤ (scores (d * d) (Robust.RBAux.FrameLoop.power d)
        (iterationFeatures d pts w) w).getD i 0 := by exact_mod_cast hs0
    rw [activeScores_entry]
    simp only [hwi, ↓reduceIte, max_eq_right hs0', Rat.cast_mul]
  · have hw0 : w.getD i 0 = 0 := by
      have hh : 0 ≤ w.getD i 0 := by exact_mod_cast (weights_bounds hw i).1
      linarith only [hh, not_lt.mp hwi]
    simp only [hw0, zero_mul, Rat.cast_zero]

private theorem balance_reset (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (π : ℚ) (w : Vector) (hw : Ready d pts w) (hc : Clean D idx π w)
    (hA : Robust.TypeA D (liftState idx d pts w)) (e : ℚ)
    (hbal : balance D pts idx w e) (hM : 0 < maximum (activeScores d pts w)) :
    balance D pts idx (reset (resetPrecision pts.length) (maximum (activeScores d pts w))
      w (activeScores d pts w))
      (e + pts.length / (2 : ℚ) ^ resetPrecision pts.length) := by
  let G := preimage idx D.good
  let B := preimage idx (D.block \ D.good)
  let s := activeScores d pts w
  let M := maximum s
  let p := resetPrecision pts.length
  have hA' : (∑ i ∈ G, w.getD i 0 * s.getD i 0) ≤
      ∑ i ∈ B, w.getD i 0 * s.getD i 0 := by
    unfold Robust.TypeA at hA
    rw [sum_preimage D pts idx hinj hrange D.good hc.invariant.1.2.2.1,
      sum_preimage D pts idx hinj hrange (D.block \ D.good) Finset.sdiff_subset] at hA
    simp_rw [← active_weighted D pts idx hinj hrange hx π w hw hc] at hA
    exact_mod_cast hA
  have hh := reset_accounting p (fun i : Fin pts.length ↦ w.getD i 0)
    (fun i : Fin pts.length ↦ s.getD i 0) M e G B hM hA' hbal
  have hcard : G.card ≤ pts.length := by
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  have hcard' : (G.card : ℚ) / 2 ^ p ≤ pts.length / (2 : ℚ) ^ p :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  change (∑ i ∈ G, (1 - (reset p M w s).getD i 0)) ≤
    (∑ i ∈ B, (1 - (reset p M w s).getD i 0)) + (e + pts.length / (2 : ℚ) ^ p)
  simp_rw [reset_getD p M w s hw.1 (activeScores_length d pts w)]
  exact hh.trans (by linarith only [hcard'])

private def roundingSlack (m t : ℕ) : ℚ := t * (m / (2 : ℚ) ^ resetPrecision m)

private theorem roundingSlack_budget (D : Robust.Reference n k d) (pts : Points)
    (π R : ℚ) (hD : D.Valid π) (hπ1 : π ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R) (t : ℕ) (ht : t ≤ pts.length) :
    (roundingSlack pts.length t : ℝ) ≤ D.contamination * D.reference.card := by
  have hπr : (π : ℝ) ≤ 1 := by exact_mod_cast hπ1
  have heπ := Robust.RBAux.contamination_small_pi D π R hD.1.1 hπr he
  have he1 : D.contamination ≤ 1 / 10000 := by linarith only [heπ, hπr]
  have hε : 0 ≤ D.contamination := by unfold Robust.Reference.contamination; positivity
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  obtain ⟨_, hgR, hmN⟩ := Robust.RBAux.FrameLoop.reference_count_bounds D π hD he1
  have hgm : (D.good.card : ℝ) ≤ D.block.card := by
    exact_mod_cast Finset.card_le_card hD.2.2.1
  have hm : (0 : ℝ) < D.block.card := by
    nlinarith only [hgR, hgm, mul_le_mul_of_nonneg_right he1 hN.le, hN]
  have hlow : 2 / (D.block.card : ℝ) ≤ D.contamination :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hlow' := (div_le_iff₀ hm).mp hlow
  have hupper := mul_le_mul_of_nonneg_left hmN hε
  have hεN : 1 ≤ D.contamination * D.reference.card := by
    nlinarith only [hlow', hupper]
  apply le_trans _ hεN
  have hs : roundingSlack pts.length t ≤ 1 := by
    have hh : (t : ℚ) ≤ pts.length := by exact_mod_cast ht
    have hh' := mul_le_mul_of_nonneg_right hh
      (show (0 : ℚ) ≤ pts.length / (2 : ℚ) ^ resetPrecision pts.length by positivity)
    have herr := resetPrecision_error pts.length
    have hunit : 1 / ((pts.length : ℚ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hn : (0 : ℚ) ≤ pts.length := by positivity
      linarith only [hn]
    have htop : (pts.length : ℚ) *
        (pts.length / (2 : ℚ) ^ resetPrecision pts.length) =
        (pts.length : ℚ) ^ 2 / (2 : ℚ) ^ resetPrecision pts.length := by ring
    rw [htop] at hh'
    exact hh'.trans (herr.trans hunit)
  exact_mod_cast hs

private theorem clean_support_pos (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (π : ℚ) (w : Vector) (hw : Ready d pts w) (hc : Clean D idx π w) :
    0 < (support (fun i : Fin pts.length ↦ w.getD i 0)).card := by
  have hN : (0 : ℝ) < D.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hc.invariant.1.2.2.2.2.1
  have hmass := hc.invariant.2.2.2.2.2.2.2.2.2.2.2.1
  have htotal : (0 : ℝ) < (total pts.length w : ℝ) := by
    rw [← decoded_mass D pts idx hinj hrange w]
    linarith only [hmass, hN]
  have hsum : (0 : ℚ) < ∑ i : Fin pts.length, w.getD i 0 := by
    rw [← total_eq (w' := fun i : Fin pts.length ↦ w.getD i 0) (fun _ ↦ rfl)]
    exact_mod_cast htotal
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) ↦ by exact_mod_cast (weights_bounds hw i).1) |>.mp hsum
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

private theorem loop_clean_dichotomy (D : Robust.Reference n k d) (pts : Points)
    (idx : Fin pts.length → Fin n) (hinj : Function.Injective idx)
    (hrange : Set.range idx = {l | l ∈ D.block})
    (hx : ∀ (i : Fin pts.length) (j : Fin d),
      (ent pts i j : ℝ) = D.observed (idx i) j)
    (π R : ℚ) (hD : D.Valid π) (hres : D.Resilient 4 (1 / 10000)) (hπ1 : π ≤ 1)
    (he : D.contamination ≤ Robust.maxContamination π R)
    (fuel : ℕ) (hf : (pts.length + d + 2) ^ 100 ≤ fuel) :
    ∀ (steps t : ℕ) (w : Vector), t + steps ≤ pts.length →
      (support (fun i : Fin pts.length ↦ w.getD i 0)).card ≤ steps →
      w.length = pts.length → (∀ q ∈ w, 0 ≤ q ∧ q ≤ 1) →
      balance D pts idx w (roundingSlack pts.length t) →
      let result := loop d pts π R fuel steps w
      (∃ v ∈ result.2.1, Clean D idx π v ∧ Eligible pts π v ∧
        ¬ Robust.TypeA D (liftState idx d pts v)) ∨
      (Clean D idx π result.2.2 ∧ result.1 = true ∧
        Robust.Pass (liftState idx d pts result.2.2) π R) := by
  intro steps
  induction steps with
  | zero =>
    intro t w ht hs hlen hwb hbal
    obtain ⟨hw, hc, _⟩ := balance_clean D pts idx hinj hrange hx π R hD hres hπ1 he
      w hlen hwb _ (roundingSlack_budget D pts π R hD hπ1 he t (by omega)) hbal
    have hh := clean_support_pos D pts idx hinj hrange π w hw hc
    omega
  | succ steps ih =>
    intro t w ht hs hlen hwb hbal
    obtain ⟨hw, hc, hel⟩ := balance_clean D pts idx hinj hrange hx π R hD hres hπ1 he
      w hlen hwb _ (roundingSlack_budget D pts π R hD hπ1 he t (by omega)) hbal
    by_cases hp : Passed d pts π R w
    · right
      simp only [loop, hw, hp, ↓reduceIte]
      exact ⟨hc, trivial, (passed_agrees pts idx π R w).mp hp⟩
    have hM := clean_maximum_pos D pts idx hinj hrange hx π R w hc hp
    let v := reset (resetPrecision pts.length) (maximum (activeScores d pts w))
      w (activeScores d pts w)
    obtain ⟨hvlen, hvb, hcap, hsupport⟩ := reset_good d pts w hw fuel hf hM
    have heq : loop d pts π R fuel (steps + 1) w =
        let r := loop d pts π R fuel steps v
        (r.1, w :: r.2.1, r.2.2) := by
      simp only [loop, hw, hp, hM, ↓reduceIte, hcap, v]
    rw [heq]
    by_cases hA : Robust.TypeA D (liftState idx d pts w)
    · have hb := balance_reset D pts idx hinj hrange hx π w hw hc hA _ hbal hM
      have hb' : balance D pts idx v (roundingSlack pts.length (t + 1)) := by
        convert hb using 1
        dsimp only [roundingSlack]
        push_cast
        ring
      rcases ih (t + 1) v (by omega) (by dsimp only [v]; omega) hvlen hvb hb' with
        hbad | hpass
      · left
        obtain ⟨u, hu, huc, hue, huA⟩ := hbad
        exact ⟨u, List.mem_cons_of_mem w hu, huc, hue, huA⟩
      · exact Or.inr hpass
    · left
      exact ⟨w, List.mem_cons_self, hc, hel, hA⟩

/-- Rounded type-A prefixes preserve the clean-state bounds until PASS or the first type B.
The first type-B state is recorded and eligible. Support decrease forces the clean branch
to PASS in at most `pts.length` iterations, and the prescribed fuel never cuts its weights.
-/
theorem rounded_loop_invariant (D : Robust.Reference n k d) (pts : Points)
    (π R ζ : ℚ) (fuel : ℕ) (hrep : Robust.Represents D pts) (hD : D.Valid π)
    (hres : D.Resilient 4 (min (1 / 10 ^ 8) ((ζ : ℝ) ^ 2 / 10 ^ 8)))
    (hπ : 0 < π) (hπ1 : π ≤ 1 / 2) (hR : 0 ≤ R) (hζ : 0 < ζ)
    (he : D.contamination ≤ min (Robust.maxContamination π R) ((π : ℝ) / 400))
    (hn : 2 / Robust.maxContamination π R ≤ (pts.length : ℝ))
    (hf : (pts.length + d + 2) ^ 100 ≤ fuel) :
    ∃ idx : Fin pts.length → Fin n, Function.Injective idx ∧
      Set.range idx = {l | l ∈ D.block} ∧
      let result := loop d pts π R fuel pts.length (List.replicate pts.length 1)
      (∃ w ∈ result.2.1, Clean D idx π w ∧ Eligible pts π w ∧
        ¬ Robust.TypeA D (liftState idx d pts w)) ∨
      (Clean D idx π result.2.2 ∧ result.1 = true ∧
        Robust.Pass (liftState idx d pts result.2.2) π R) := by
  have _ := hπ
  have _ := hR
  have _ := hζ
  have _ := hn
  obtain ⟨idx, hinj, hrange, hx⟩ := hrep.2
  refine ⟨idx, hinj, hrange, ?_⟩
  have hobs (i : Fin pts.length) (j : Fin d) :
      (ent pts i j : ℝ) = D.observed (idx i) j := by
    simpa only [ent, List.getD_eq_getElem _ _ i.isLt, Fin.getElem_fin] using (hx i).2 j
  have hπ' : π ≤ 1 := hπ1.trans (by norm_num)
  have hθ : min (1 / 10 ^ 8 : ℝ) ((ζ : ℝ) ^ 2 / 10 ^ 8) ≤ 1 / 10000 :=
    (min_le_left _ _).trans (by norm_num)
  have hres' : D.Resilient 4 (1 / 10000) := by
    intro T a j r hr
    apply (hres T a j r hr).trans
    apply mul_le_mul_of_nonneg_right
    · exact div_le_div_of_nonneg_right hθ (by positivity)
    · exact pow_nonneg (add_nonneg
        (add_nonneg zero_le_one (SoS.coeffNorm1_nonneg _))
        (SoS.coeffNorm1_nonneg _)) r
  apply loop_clean_dichotomy D pts idx hinj hrange hobs π R hD hres' hπ'
    (he.trans (min_le_left _ _)) fuel hf pts.length 0 (List.replicate pts.length 1)
  · omega
  · exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
  · simp only [List.length_replicate]
  · intro q hq
    have hq' : q = 1 := List.eq_of_mem_replicate hq
    rw [hq']
    norm_num
  · simp [balance, roundingSlack]

/-- The executable output uses the affine filter in both modes. The contract asks for a
zero exported center in centered mode; it imposes no centered-mode internal moment identity.
-/
def run (mode : Mode) (q : Args × ℕ) : DataL :=
  let d := q.1.1
  let pts := q.1.2.1
  let π := q.1.2.2.1
  let R := q.1.2.2.2.1
  let ζ := q.1.2.2.2.2
  let result := loop d pts π R q.2 pts.length (List.replicate pts.length 1)
  let pool := certificatePool d pts π result.2.1
  let C := covariance d pts result.2.2
  (result.1, normalizedL d C ζ,
    (if mode = .centered then List.replicate d 0 else mean d pts result.2.2), C,
    pool.map Prod.fst, pool.map Prod.snd)

noncomputable def decode (d : ℕ) (F : DataL) : Robust.FrameResult d :=
  ⟨F.1, matrixOf d F.2.1, vectorOf d F.2.2.1, matrixOf d F.2.2.2.1,
    F.2.2.2.2.1.map (quadOf d), F.2.2.2.2.2⟩

/-- The typed result has exactly the decoded rational coefficients and paired flags. -/
theorem rounded_frame_agrees (d : ℕ) (pts : Points) (mode : Mode)
    (π R ζ : ℚ) (fuel : ℕ) :
    let result := loop d pts π R fuel pts.length (List.replicate pts.length 1)
    let pool := certificatePool d pts π result.2.1
    decode d (run mode ((d, pts, π, R, ζ), fuel)) =
      { passed := result.1
        transform := matrixOf d (normalizedL d (covariance d pts result.2.2) ζ)
        center := if mode = .centered then 0 else vectorOf d (mean d pts result.2.2)
        covariance := matrixOf d (covariance d pts result.2.2)
        certificates := pool.map (fun p ↦ quadOf d p.1)
        eligible := pool.map Prod.snd } := by
  have hz : vectorOf d (List.replicate d (0 : ℚ)) = 0 := by
    ext i
    simp [vectorOf]
  dsimp only [run, decode]
  split_ifs <;> simp only [hz, List.map_map, Function.comp_def]

private theorem decide_and_polytime {α : Type} {input : α ↪ List Bool}
    {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ComputableInPolyTime (fun x ↦ decide (p x)) input encBool)
    (hq : ComputableInPolyTime (fun x ↦ decide (q x)) input encBool) :
    ComputableInPolyTime (fun x ↦ decide (p x ∧ q x)) input encBool := by
  refine (bool_and.comp (hp.prod hq)).of_enc_eq fun x ↦ ?_
  congr 1

private theorem ready_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ decide (Ready (d x) (pts x) (w x)))
      input encBool := by
  have hn := (length_list encVector).comp hx
  have hall := ComputableTidilyInPolyTime.allWithInput
    (test := fun (_ : α) (q : ℚ) ↦ decide (0 ≤ q ∧ q ≤ 1)) hw.tidy
    (decide_and_polytime (rat_le' (const 0) (snd input encRat))
      (rat_le' (snd input encRat) (const 1))).tidy
  have hall' : ComputableInPolyTime (fun x ↦ decide (∀ q ∈ w x, 0 ≤ q ∧ q ≤ 1))
      input encBool := by
    convert ComputableInPolyTime.of_tidy hall using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, List.all_eq_true]
  unfold Ready
  apply decide_and_polytime (unary_eq' ((length_list encRat).comp hw) hn)
  apply decide_and_polytime hall'
  apply decide_and_polytime
    (rat_le' (rat_div' (rat_natCast' (unary_to_binary.comp hn)) (const 2))
      (total_polytime hn hw))
  exact decide_eq' (SoS.PDTestRat.test_polytime.comp (covariance_polytime hd hx hw))
    (const none)

private theorem frame_power_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} (hd : ComputableInPolyTime d input encUnary) :
    ComputableInPolyTime (fun x ↦ Robust.RBAux.FrameLoop.power (d x)) input encUnary :=
  unary_mul' (const 2) (unary_add' (unary_mul' hd hd) (const 1))

private theorem passed_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {π R : α → ℚ} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hπ : ComputableInPolyTime π input encRat)
    (hR : ComputableInPolyTime R input encRat)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ decide (Passed (d x) (pts x) (π x) (R x) (w x)))
      input encBool := by
  exact rat_le'
    (powerTrace_polytime (unary_mul' hd hd) (frame_power_polytime hd)
      (iterationCov_polytime hd hx hw))
    (rat_pow' (rat_mul' (const 16)
      (rat_add' (rat_div' (const 600) (rat_sq' hπ))
        (rat_mul' (const 2) (rat_sq' hR)))) (frame_power_polytime hd))

private theorem activeScores_polytime {α : Type} {input : α ↪ List Bool}
    {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ activeScores (d x) (pts x) (w x)) input encVector := by
  have hs := scores_polytime (unary_mul' hd hd) (frame_power_polytime hd)
    (iterationFeatures_polytime hd hx hw) hw
  unfold activeScores
  apply mapWithInput (range.comp ((length_list encVector).comp hx))
  exact ite_prop (rat_lt' (const 0) (vget' (hw.comp (fst _ _)) (snd _ _)))
    (rat_max' (const 0) (vget' (hs.comp (fst _ _)) (snd _ _))) (const 0)


private theorem maximum_polytime {α : Type} {input : α ↪ List Bool}
    {s : α → Vector} (hs : ComputableInPolyTime s input encVector) :
    ComputableInPolyTime (fun x ↦ maximum (s x)) input encRat := by
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.foldl' hs.tidy (ComputableTidilyInPolyTime.const 0)
    (rat_max' (fst _ _) (snd _ _)).tidy
    (hs.polyBounded_length.add (.const ((encRat 0).length)))
  intro x i _
  rcases List.mem_cons.mp (foldl_max_mem ((s x).take i) 0) with h | h
  · rw [h]
    exact Nat.le_add_left _ _
  · have hm := length_le_encList_of_mem encRat (List.mem_of_mem_take h)
    exact hm.trans (Nat.le_add_right _ _)

private theorem cap_polytime {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {fuel : α → ℕ} {f fallback : α → β}
    (hn : ComputableInPolyTime fuel input encUnary)
    (hf : ComputableInPolyTime f input output)
    (hb : ComputableInPolyTime fallback input output) :
    ComputableInPolyTime (fun x ↦ cap output (fuel x) (fallback x) (f x))
      input output := by
  unfold cap
  apply ite_prop _ hf hb
  exact .of_tidy (ComputableTidilyInPolyTime.unary_le'
    (ComputableTidilyInPolyTime.encoding_length output |>.comp hf.tidy) hn.tidy)

/-! The machine stores the current weights at the head, followed by failures in reverse order.
This shares the current vector with the history and adds at most one capped vector per step. -/

private abbrev Machine := Bool × Bool × List Vector
private abbrev encMachine := encPair encBool (encPair encBool (encList encVector))
private abbrev encLoopInput := encPair encArgs encUnary

private def advance (x : Args × ℕ) (st : Machine) : Machine :=
  if st.1 then
    let w := st.2.2.getD 0 []
    if Ready x.1.1 x.1.2.1 w then
      if Passed x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 w then
        (false, true, st.2.2)
      else
        let s := activeScores x.1.1 x.1.2.1 w
        let M := maximum s
        if 0 < M then
          (true, false, cap encVector x.2 []
            (reset (resetPrecision x.1.2.1.length) M w s) :: st.2.2)
        else (false, false, st.2.2)
    else (false, false, st.2.2)
  else st

private def finish (st : Machine) : Bool × List Vector × Vector :=
  (st.2.1, st.2.2.tail.reverse, st.2.2.getD 0 [])

private theorem advance_halted (x : Args × ℕ) (b : Bool) (ws : List Vector) (i : ℕ) :
    (advance x)^[i] (false, b, ws) = (false, b, ws) := by
  induction i with
  | zero => rfl
  | succ i ih => simpa only [Function.iterate_succ_apply, advance, Bool.false_eq_true,
      ↓reduceIte] using ih

private theorem advance_agrees (x : Args × ℕ) (steps : ℕ) (w : Vector)
    (hist : List Vector) :
    finish ((advance x)^[steps] (true, false, w :: hist)) =
      let r := loop x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.2 steps w
      (r.1, hist.reverse ++ r.2.1, r.2.2) := by
  induction steps generalizing w hist with
  | zero => simp [finish, loop]
  | succ steps ih =>
    rw [Function.iterate_succ_apply]
    simp only [advance, ↓reduceIte, List.getD_cons_zero, loop]
    split_ifs with hr hp hm
    · rw [advance_halted]
      simp [finish]
    · rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    · rw [advance_halted]
      simp [finish]
    · rw [advance_halted]
      simp [finish]

private theorem advance_polytime : ComputableInPolyTime
    (fun p : (Args × ℕ) × Machine ↦ advance p.1 p.2)
      (encPair encLoopInput encMachine) encMachine := by
  have hb := (fst encArgs encUnary).comp (fst encLoopInput encMachine)
  have hd := (fst _ _).comp hb
  have ht := (snd _ _).comp hb
  have hx := (fst _ _).comp ht
  have hp := (snd _ _).comp ht
  have hπ := (fst _ _).comp hp
  have hR := (fst _ _).comp ((snd _ _).comp hp)
  have hf := (snd _ _).comp (fst encLoopInput encMachine)
  have hst := snd encLoopInput encMachine
  have hws := (snd _ _).comp ((snd _ _).comp hst)
  have hw := listGetDWithInput hws (const 0) []
  have hs := activeScores_polytime hd hx hw
  have hM := maximum_polytime hs
  unfold advance
  apply ite_prop (by simpa only [Bool.decide_coe, Function.comp_def] using (fst _ _).comp hst) _ hst
  apply ite_prop (ready_polytime hd hx hw) _ ((const false).prod ((const false).prod hws))
  apply ite_prop (passed_polytime hd hx hπ hR hw)
    ((const false).prod ((const true).prod hws))
  apply ite_prop (rat_lt' (const 0) hM) _ ((const false).prod ((const false).prod hws))
  exact (const true).prod ((const false).prod
    (cons' (cap_polytime hf (reset_polytime
      (resetPrecision_polytime ((length_list encVector).comp hx)) hM hw hs) (const [])) hws))

private theorem advance_growth (x : Args × ℕ) (st : Machine) :
    (encMachine (advance x st)).length ≤ (encMachine st).length + (2 * x.2 + 1) := by
  unfold advance
  dsimp only
  split_ifs
  all_goals try { simp [encMachine] }
  have hcap : (encVector (cap encVector x.2 []
      (reset (resetPrecision x.1.2.1.length) (maximum
        (activeScores x.1.1 x.1.2.1 (st.2.2.getD 0 []))) (st.2.2.getD 0 [])
        (activeScores x.1.1 x.1.2.1 (st.2.2.getD 0 []))))).length ≤ x.2 := by
    unfold cap
    split_ifs with h
    · exact h
    · simp [encVector]
  have hbool (b : Bool) : (encBool b).length = 1 := rfl
  simp only [encMachine, length_encPair, hbool]
  simp only [length_encList, List.map_cons, List.sum_cons] at *
  omega

private theorem rounded_loop_polytime : ComputableInPolyTime
    (fun x : Args × ℕ ↦ loop x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.2
      x.1.2.1.length (List.replicate x.1.2.1.length 1))
    encLoopInput (encPair encBool (encPair (encList encVector) encVector)) := by
  have hx := (fst _ _).comp ((snd _ _).comp (fst encArgs encUnary))
  have hn := (length_list encVector).comp hx
  have hi : ComputableInPolyTime
      (fun x : Args × ℕ ↦ (true, false, [List.replicate x.1.2.1.length (1 : ℚ)]))
      encLoopInput encMachine :=
    (const true).prod ((const false).prod (cons' (replicate hn (const 1)) (const [])))
  have hg : PolyBounded (fun x : Args × ℕ ↦ (encLoopInput x).length)
      (fun x ↦ 2 * x.2 + 1) :=
    ((PolyBounded.const 2).mul (snd encArgs encUnary).tidy.polyBounded).add (.const 1)
  have hit := ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    ComputableTidilyInPolyTime.id' hn.tidy hi.tidy advance_polytime.tidy hg advance_growth
  have hfinish : ComputableInPolyTime finish encMachine
      (encPair encBool (encPair (encList encVector) encVector)) := by
    have hws := (snd _ _).comp (snd encBool (encPair encBool (encList encVector)))
    exact ((fst _ _).comp (snd _ _)).prod
      (((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listReverse _)).comp
        ((ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listTail _)).comp hws)).prod
        (listGetDWithInput hws (const 0) []))
  convert hfinish.comp (ComputableInPolyTime.of_tidy hit) using 1
  funext x
  simpa using (advance_agrees x x.1.2.1.length
    (List.replicate x.1.2.1.length 1) []).symm

/-- The rounded, capped loop and final rational normalization run in polynomial time on all
inputs. Unary fuel bounds stored weights; the history has at most `n` such vectors.
-/
theorem rounded_frame_polytime (mode : Mode) : ComputableInPolyTime (run mode)
    (encPair encArgs encUnary) encDataL := by
  have hb := fst encArgs encUnary
  have hd := (fst _ _).comp hb
  have ht := (snd _ _).comp hb
  have hx := (fst _ _).comp ht
  have hp := (snd _ _).comp ht
  have hπ := (fst _ _).comp hp
  have hz := (snd _ _).comp ((snd _ _).comp hp)
  have hr := rounded_loop_polytime
  have hw := (snd _ _).comp ((snd _ _).comp hr)
  have hC := covariance_polytime hd hx hw
  have hpool := certificate_pool_polytime.comp
    ((hd.prod (hx.prod hπ)).prod ((fst _ _).comp ((snd _ _).comp hr)))
  have hT := normalizedL_polytime.comp ((hd.prod hC).prod hz)
  have ha : ComputableInPolyTime
      (fun x : Args × ℕ ↦ if mode = .centered then List.replicate x.1.1 0
        else mean x.1.1 x.1.2.1 (loop x.1.1 x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 x.2
          x.1.2.1.length (List.replicate x.1.2.1.length 1)).2.2)
      encLoopInput encVector := by
    split_ifs
    · exact replicate hd (const 0)
    · exact mean_polytime hd hx hw
  exact ((fst _ _).comp hr).prod (hT.prod (ha.prod (hC.prod
    ((mapWithInput hpool ((fst _ _).comp (snd _ _))).prod
      (mapWithInput hpool ((snd _ _).comp (snd _ _)))))))

end ABBKS26.Assembly.Exec.FrameProgram
