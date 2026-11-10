module

public import ABBKS26.Assembly.ExecFrameAuxLinear
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Algebra.Ring.GeomSum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-! Rational weighted moments and quadratic features for the executable frame filter. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameAux.Features

open Matrix
open Linear
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators Kronecker

variable {α : Type} {input : α ↪ List Bool} {m d : ℕ}

def table (m d : ℕ) (f : ℕ → ℕ → ℚ) : MatrixL :=
  (List.range m).map fun i ↦ (List.range d).map (f i)

theorem table_length (m d : ℕ) (f : ℕ → ℕ → ℚ) : (table m d f).length = m := by
  simp [table]

theorem table_rep (f : ℕ → ℕ → ℚ) :
    RepT (table m d f) (fun (i : Fin m) (j : Fin d) ↦ f i j) :=
  repT_map_range _ _ fun _ _ ↦ rfl

theorem table_polytime {rows cols : α → ℕ} {f : α → ℕ → ℕ → ℚ}
    (hm : ComputableInPolyTime rows input encUnary)
    (hd : ComputableInPolyTime cols input encUnary)
    (hf : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ f p.1.1 p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encRat) :
    ComputableInPolyTime (fun x ↦ table (rows x) (cols x) (f x)) input encMatrix := by
  unfold table
  exact mapWithInput (range.comp hm)
    (mapWithInput (range.comp (hd.comp (fst _ _))) hf)

theorem sum_polytime {count : α → ℕ} {f : α → ℕ → ℚ}
    (hn : ComputableInPolyTime count input encUnary)
    (hf : ComputableInPolyTime (fun p : α × ℕ ↦ f p.1 p.2)
      (encPair input encUnary) encRat) :
    ComputableInPolyTime (fun x ↦ ((List.range (count x)).map (f x)).sum)
      input encRat := rat_sum' (mapWithInput (range.comp hn) hf)

def total (m : ℕ) (w : Vector) : ℚ :=
  ((List.range m).map fun i ↦ w.getD i 0).sum

def mean (d : ℕ) (pts : Points) (w : Vector) : Vector :=
  (List.range d).map fun j ↦
    ((List.range pts.length).map fun i ↦ w.getD i 0 * ent pts i j).sum /
      total pts.length w

def translate (d : ℕ) (pts : Points) (a : Vector) : Points :=
  table pts.length d fun i j ↦ ent pts i j - a.getD j 0

def second (d : ℕ) (pts : Points) (w : Vector) : MatrixL :=
  table d d fun j k ↦
    ((List.range pts.length).map fun i ↦ w.getD i 0 * (ent pts i j * ent pts i k)).sum /
      total pts.length w

def covariance (d : ℕ) (pts : Points) (w : Vector) : MatrixL :=
  second d (translate d pts (mean d pts w)) w

def transform (d : ℕ) (T : MatrixL) (pts : Points) : Points :=
  pts.map (mulVecL d T)

/-- The feature index is the row-major encoding of a pair of coordinates. -/
def feature (d : ℕ) (v : Vector) : Vector :=
  (List.range (d * d)).map fun a ↦ v.getD (a / d) 0 * v.getD (a % d) 0

def features (d : ℕ) (pts : Points) : Points := pts.map (feature d)

def featurePoints (d : ℕ) (T : MatrixL) (pts : Points) (w : Vector) : Points :=
  features d (transform d T (translate d pts (mean d pts w)))

def featureCovariance (d : ℕ) (T : MatrixL) (pts : Points) (w : Vector) : MatrixL :=
  covariance (d * d) (featurePoints d T pts w) w

theorem translate_length (d : ℕ) (pts : Points) (a : Vector) :
    (translate d pts a).length = pts.length := table_length _ _ _

theorem transform_length (d : ℕ) (T : MatrixL) (pts : Points) :
    (transform d T pts).length = pts.length := List.length_map _

theorem features_length (d : ℕ) (pts : Points) :
    (features d pts).length = pts.length := List.length_map _

theorem featurePoints_length (d : ℕ) (T : MatrixL) (pts : Points) (w : Vector) :
    (featurePoints d T pts w).length = pts.length := by
  rw [featurePoints, features_length, transform_length, translate_length]

theorem total_polytime {n : α → ℕ} {w : α → Vector}
    (hn : ComputableInPolyTime n input encUnary)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ total (n x) (w x)) input encRat :=
  sum_polytime hn (vget' (hw.comp (fst _ _)) (snd _ _))

theorem mean_polytime {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ mean (d x) (pts x) (w x)) input encVector := by
  unfold mean
  apply mapWithInput (range.comp hd)
  apply rat_div' _ ((total_polytime ((length_list _).comp hx) hw).comp (fst _ _))
  apply sum_polytime (((length_list _).comp hx).comp (fst _ _))
  exact rat_mul'
    (vget' (hw.comp ((fst _ _).comp (fst _ _))) (snd _ _))
    (ent' (hx.comp ((fst _ _).comp (fst _ _))) (snd _ _) ((snd _ _).comp (fst _ _)))

theorem translate_polytime {d : α → ℕ} {pts : α → Points} {a : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (ha : ComputableInPolyTime a input encVector) :
    ComputableInPolyTime (fun x ↦ translate (d x) (pts x) (a x)) input encPoints := by
  apply table_polytime ((length_list _).comp hx) hd
  exact rat_sub'
    (ent' (hx.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _)) (snd _ _))
    (vget' (ha.comp ((fst _ _).comp (fst _ _))) (snd _ _))

theorem second_polytime {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ second (d x) (pts x) (w x)) input encMatrix := by
  apply table_polytime hd hd
  have hfst := (fst input encUnary).comp (fst _ encUnary)
  apply rat_div' _ ((total_polytime ((length_list _).comp hx) hw).comp hfst)
  apply sum_polytime (((length_list _).comp hx).comp hfst)
  have hbase := hfst.comp (fst _ encUnary)
  exact rat_mul' (vget' (hw.comp hbase) (snd _ _))
    (rat_mul' (ent' (hx.comp hbase) (snd _ _) ((snd _ _).comp ((fst _ _).comp (fst _ _))))
      (ent' (hx.comp hbase) (snd _ _) ((snd _ _).comp (fst _ _))))

theorem covariance_polytime {d : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ covariance (d x) (pts x) (w x)) input encMatrix :=
  second_polytime hd (translate_polytime hd hx (mean_polytime hd hx hw)) hw

theorem transform_polytime {d : α → ℕ} {T : α → MatrixL} {pts : α → Points}
    (hd : ComputableInPolyTime d input encUnary)
    (hT : ComputableInPolyTime T input encMatrix)
    (hx : ComputableInPolyTime pts input encPoints) :
    ComputableInPolyTime (fun x ↦ transform (d x) (T x) (pts x)) input encPoints :=
  mapWithInput hx (mulVecL' (hd.comp (fst _ _)) (hT.comp (fst _ _)) (snd _ _))

theorem feature_polytime {d : α → ℕ} {v : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hv : ComputableInPolyTime v input encVector) :
    ComputableInPolyTime (fun x ↦ feature (d x) (v x)) input encVector := by
  unfold feature
  apply mapWithInput (range.comp (unary_mul' hd hd))
  exact rat_mul'
    (vget' (hv.comp (fst _ _)) (unary_div.comp ((snd _ _).prod (hd.comp (fst _ _)))))
    (vget' (hv.comp (fst _ _)) (unary_mod.comp ((snd _ _).prod (hd.comp (fst _ _)))))

theorem features_polytime {d : α → ℕ} {pts : α → Points}
    (hd : ComputableInPolyTime d input encUnary)
    (hx : ComputableInPolyTime pts input encPoints) :
    ComputableInPolyTime (fun x ↦ features (d x) (pts x)) input encPoints :=
  mapWithInput hx (feature_polytime (hd.comp (fst _ _)) (snd _ _))

theorem featurePoints_polytime {d : α → ℕ} {T : α → MatrixL} {pts : α → Points}
    {w : α → Vector} (hd : ComputableInPolyTime d input encUnary)
    (hT : ComputableInPolyTime T input encMatrix)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ featurePoints (d x) (T x) (pts x) (w x))
      input encPoints :=
  features_polytime hd (transform_polytime hd hT
    (translate_polytime hd hx (mean_polytime hd hx hw)))


/-! Decoder agreement, including zero total mass and missing entries. -/

theorem total_eq {w : Vector} {w' : Fin m → ℚ} (hw : RepV w w') :
    total m w = ∑ i, w' i :=
  (sum_fin_eq_list _ _ fun i ↦ hw i).symm

theorem mean_rep {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    {w : Vector} {w' : Fin m → ℚ} (hx : RepT pts x) (hw : RepV w w') :
    RepV (mean d pts w) ((∑ i, w' i)⁻¹ • ∑ i, w' i • x i) := by
  apply repV_map_range
  intro j
  rw [hlen, total_eq hw]
  have hsum := sum_fin_eq_list (fun i ↦ w' i * x i j)
    (fun i ↦ w.getD i 0 * ent pts i j) (fun i ↦ by rw [hw i, hx i j])
  rw [← hsum]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem translate_rep {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    {a : Vector} {a' : Fin d → ℚ} (hx : RepT pts x) (ha : RepV a a') :
    RepT (translate d pts a) (fun i ↦ x i - a') := by
  unfold translate
  rw [hlen]
  exact repT_map_range _ _ fun i j ↦ by rw [hx i j, ha j]; rfl

theorem second_rep {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    {w : Vector} {w' : Fin m → ℚ} (hx : RepT pts x) (hw : RepV w w') :
    RepT (second d pts w) ((∑ i, w' i)⁻¹ • ∑ i, w' i • vecMulVec (x i) (x i)) := by
  apply repT_map_range
  intro j k
  rw [hlen, total_eq hw]
  have hsum := sum_fin_eq_list (fun i ↦ w' i * (x i j * x i k))
    (fun i ↦ w.getD i 0 * (ent pts i j * ent pts i k))
    (fun i ↦ by rw [hw i, hx i j, hx i k])
  rw [← hsum]
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul,
    div_eq_mul_inv, mul_comm]

theorem covariance_rep {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    {w : Vector} {w' : Fin m → ℚ} (hx : RepT pts x) (hw : RepV w w') :
    let a := (∑ i, w' i)⁻¹ • ∑ i, w' i • x i
    RepT (covariance d pts w)
      ((∑ i, w' i)⁻¹ • ∑ i, w' i • vecMulVec (x i - a) (x i - a)) :=
  second_rep ((translate_length _ _ _).trans hlen)
    (translate_rep hlen hx (mean_rep hlen hx hw)) hw

theorem transform_rep {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    {T : MatrixL} {T' : Matrix (Fin d) (Fin d) ℚ} (hx : RepT pts x) (hT : RepT T T') :
    RepT (transform d T pts) (fun i ↦ T' *ᵥ x i) := by
  intro i j
  have hi : i.val < pts.length := by omega
  have hrow : (transform d T pts).getD i [] = mulVecL d T (pts.getD i []) := by
    rw [transform, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  change ((transform d T pts).getD i []).getD j 0 = _
  rw [hrow]
  exact mulVecL_rep hT (hx.row i) j

theorem feature_rep {v : Vector} {v' : Fin d → ℚ} (hv : RepV v v') :
    RepV (feature d v) (fun a ↦ v' (finProdFinEquiv.symm a).1 *
      v' (finProdFinEquiv.symm a).2) := by
  apply repV_map_range
  intro a
  exact congrArg₂ (· * ·) (hv (finProdFinEquiv.symm a).1) (hv (finProdFinEquiv.symm a).2)

theorem features_rep {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    (hx : RepT pts x) :
    RepT (features d pts) (fun i a ↦ x i (finProdFinEquiv.symm a).1 *
      x i (finProdFinEquiv.symm a).2) := by
  intro i a
  have hi : i.val < pts.length := by omega
  have hrow : (pts.map (feature d)).getD i [] = feature d (pts.getD i []) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.getD_eq_getElem _ _ hi]
  change ((pts.map (feature d)).getD i []).getD a 0 = _
  rw [hrow]
  exact feature_rep (hx.row i) a

theorem featurePoints_rep {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {w : Vector} {w' : Fin m → ℚ}
    {T : MatrixL} {T' : Matrix (Fin d) (Fin d) ℚ}
    (hx : RepT pts x) (hw : RepV w w') (hT : RepT T T') :
    let a := (∑ i, w' i)⁻¹ • ∑ i, w' i • x i
    let y := fun i ↦ T' *ᵥ (x i - a)
    RepT (featurePoints d T pts w) (fun i b ↦ y i (finProdFinEquiv.symm b).1 *
      y i (finProdFinEquiv.symm b).2) :=
  features_rep ((transform_length _ _ _).trans ((translate_length _ _ _).trans hlen))
    (transform_rep ((translate_length _ _ _).trans hlen)
      (translate_rep hlen hx (mean_rep hlen hx hw)) hT)

theorem mean_real {pts : Points} (hlen : pts.length = m) {x : Fin m → Fin d → ℚ}
    {w : Vector} {w' : Fin m → ℚ} (hx : RepT pts x) (hw : RepV w w') :
    (fun j ↦ (vectorOf d (mean d pts w) j : ℝ)) =
      Robust.RBAux.FrameLoop.center (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ)) := by
  funext j
  have h := congrArg (Rat.cast : ℚ → ℝ) (mean_rep hlen hx hw j)
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h
  push_cast at h
  simpa only [vectorOf, Robust.RBAux.FrameLoop.center, Robust.RBAux.FrameLoop.mass,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h

theorem covariance_real {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {w : Vector} {w' : Fin m → ℚ}
    (hx : RepT pts x) (hw : RepV w w') :
    (matrixOf d (covariance d pts w)).map (algebraMap ℚ ℝ) =
      Robust.RBAux.FrameLoop.covariance (fun i j ↦ (x i j : ℝ))
        (fun i ↦ (w' i : ℝ)) := by
  ext j k
  have h := congrArg (Rat.cast : ℚ → ℝ) (covariance_rep hlen hx hw j k)
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul] at h
  push_cast at h
  simpa only [matrixOf, ent, Matrix.map_apply, eq_ratCast,
    Robust.RBAux.FrameLoop.covariance, Robust.RBAux.FrameLoop.center,
    Robust.RBAux.FrameLoop.mass, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply,
    Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h

theorem featurePoints_real {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {w : Vector} {w' : Fin m → ℚ}
    {T : MatrixL} {T' : Matrix (Fin d) (Fin d) ℚ}
    (hx : RepT pts x) (hw : RepV w w') (hT : RepT T T')
    (i : Fin m) (b : Fin (d * d)) :
    (ent (featurePoints d T pts w) i b : ℝ) =
      Robust.feature (T'.map (algebraMap ℚ ℝ) *ᵥ
        ((fun j ↦ (x i j : ℝ)) - Robust.RBAux.FrameLoop.center
          (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ))))
        (finProdFinEquiv.symm b) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (featurePoints_rep hlen hx hw hT i b)
  dsimp only at h
  simp only [mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
    smul_eq_mul] at h ⊢
  push_cast at h
  simpa only [Robust.feature, Robust.RBAux.FrameLoop.center, Robust.RBAux.FrameLoop.mass,
    mulVec, dotProduct, Matrix.map_apply, eq_ratCast, Pi.sub_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul] using h

theorem featureCovariance_real {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {w : Vector} {w' : Fin m → ℚ}
    {T : MatrixL} {T' : Matrix (Fin d) (Fin d) ℚ}
    (hx : RepT pts x) (hw : RepV w w') (hT : RepT T T') :
    let y := fun i ↦ T'.map (algebraMap ℚ ℝ) *ᵥ
      ((fun j ↦ (x i j : ℝ)) - Robust.RBAux.FrameLoop.center
        (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ)))
    let μ := ((∑ i, (w' i : ℝ))⁻¹ • ∑ i, (w' i : ℝ) • Robust.feature (y i))
    (fun a b : Fin d × Fin d ↦
      ((matrixOf (d * d) (featureCovariance d T pts w))
        (finProdFinEquiv a) (finProdFinEquiv b) : ℝ)) =
      (∑ i, (w' i : ℝ))⁻¹ • ∑ i, (w' i : ℝ) •
        vecMulVec (Robust.feature (y i) - μ) (Robust.feature (y i) - μ) := by
  let P := featurePoints d T pts w
  let z : Fin m → Fin (d * d) → ℚ := fun i a ↦ ent P i a
  have hz : RepT P z := fun _ _ ↦ rfl
  have hc := covariance_real ((featurePoints_length _ _ _ _).trans hlen) hz hw
  have he : (fun i a ↦ (z i a : ℝ)) = fun i a ↦
      Robust.feature (T'.map (algebraMap ℚ ℝ) *ᵥ
        ((fun j ↦ (x i j : ℝ)) - Robust.RBAux.FrameLoop.center
          (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ))))
        (finProdFinEquiv.symm a) := by
    funext i a
    exact featurePoints_real hlen hx hw hT i a
  rw [he] at hc
  ext a b
  have hh := congrFun (congrFun hc (finProdFinEquiv a)) (finProdFinEquiv b)
  simpa only [featureCovariance, Robust.RBAux.FrameLoop.covariance,
    Robust.RBAux.FrameLoop.center, Robust.RBAux.FrameLoop.mass, Matrix.map_apply,
    eq_ratCast, Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply,
    Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Equiv.symm_apply_apply] using hh

def quadraticScores (d : ℕ) (A : MatrixL) (pts : Points) : Vector :=
  pts.map (quadL d A)

theorem quadraticScores_polytime {d : α → ℕ} {A : α → MatrixL} {pts : α → Points}
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrix)
    (hx : ComputableInPolyTime pts input encPoints) :
    ComputableInPolyTime (fun x ↦ quadraticScores (d x) (A x) (pts x))
      input encVector :=
  mapWithInput hx (quadL' (hd.comp (fst _ _)) (hA.comp (fst _ _)) (snd _ _))

theorem quadraticScores_rep {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {A : MatrixL} {M : Matrix (Fin d) (Fin d) ℚ}
    (hx : RepT pts x) (hA : RepT A M) :
    RepV (quadraticScores d A pts) (fun i ↦ quad M (x i)) := by
  intro i
  have hi : i.val < pts.length := by omega
  have hrow : (quadraticScores d A pts).getD i 0 = quadL d A (pts.getD i []) := by
    rw [quadraticScores, List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_map, List.getD_eq_getElem _ _ hi]
  rw [hrow]
  exact quadL_eq hA (hx.row i)

/-! Matrix powers can be obtained from one polynomial-size block linear system. -/

def determinant (A : MatrixL) : ℚ :=
  (Cslib.Circuits.Rational.detRows (SoS.PDTestRat.scale A) : ℚ) /
    (SoS.PDTestRat.commonDen A : ℚ) ^ A.length

theorem determinant_polytime {A : α → MatrixL}
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ determinant (A x)) input encRat := by
  apply rat_div'
  · exact rat_intCast' (SoS.PDTestRows.detRows' (SoS.PDTestRat.scale_polytime.comp hA))
  · exact rat_pow' (rat_intCast' (SoS.PDTestRat.commonDen_polytime.comp hA))
      ((length_list _).comp hA)

theorem determinant_eq {A : MatrixL} (hlen : A.length = d)
    {M : Matrix (Fin d) (Fin d) ℚ} (hA : RepT A M) : determinant A = M.det := by
  let N : Matrix (Fin d) (Fin d) ℤ := fun i j ↦ Cslib.rowEntry (SoS.PDTestRat.scale A) i j
  have hdet : Cslib.Circuits.Rational.detRows (SoS.PDTestRat.scale A) = N.det :=
    Cslib.Circuits.Rational.detRows_eq_det_of_rowEntry N (by simpa [SoS.PDTestRat.scale])
      (fun _ _ ↦ rfl)
  have hN : N.map (Int.cast : ℤ → ℚ) = (SoS.PDTestRat.commonDen A : ℚ) • M := by
    ext i j
    change (Cslib.rowEntry (SoS.PDTestRat.scale A) i j : ℚ) =
      SoS.PDTestRat.commonDen A * M i j
    rw [SoS.PDTestRat.rowEntry_scale]
    exact congrArg ((SoS.PDTestRat.commonDen A : ℚ) * ·) (hA i j)
  have hD : (SoS.PDTestRat.commonDen A : ℚ) ≠ 0 := by
    exact_mod_cast (SoS.PDTestRat.commonDen_pos A).ne'
  rw [determinant, hdet, Int.cast_det, hN, det_smul, Fintype.card_fin, hlen,
    mul_div_cancel_left₀ _ (pow_ne_zero _ hD)]

def replaceRow (d : ℕ) (A : MatrixL) (i j : ℕ) : MatrixL :=
  table d d fun r c ↦ if r = i then (if c = j then 1 else 0) else ent A r c

def inverse (d : ℕ) (A : MatrixL) : MatrixL :=
  table d d fun i j ↦ determinant (replaceRow d A j i) /
    determinant (table d d (ent A))

theorem replaceRow_polytime {d i j : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrix)
    (hi : ComputableInPolyTime i input encUnary)
    (hj : ComputableInPolyTime j input encUnary) :
    ComputableInPolyTime (fun x ↦ replaceRow (d x) (A x) (i x) (j x))
      input encMatrix := by
  apply table_polytime hd hd
  have hb := (fst input encUnary).comp (fst _ encUnary)
  apply ite_prop (unary_eq' ((snd _ _).comp (fst _ _)) (hi.comp hb))
  · exact ite_prop (unary_eq' (snd _ _) (hj.comp hb)) (const 1) (const 0)
  · exact ent' (hA.comp hb) ((snd _ _).comp (fst _ _)) (snd _ _)

theorem inverse_polytime {d : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ inverse (d x) (A x)) input encMatrix := by
  apply table_polytime hd hd
  have hb := (fst input encUnary).comp (fst _ encUnary)
  apply rat_div'
  · exact determinant_polytime
      (replaceRow_polytime (hd.comp hb) (hA.comp hb) (snd _ _) ((snd _ _).comp (fst _ _)))
  · apply determinant_polytime
    apply table_polytime (hd.comp hb) (hd.comp hb)
    exact ent' (hA.comp (hb.comp ((fst _ _).comp (fst _ _))))
      ((snd _ _).comp (fst _ _)) (snd _ _)

theorem replaceRow_rep {A : MatrixL} {M : Matrix (Fin d) (Fin d) ℚ}
    (hA : RepT A M) (i j : Fin d) :
    RepT (replaceRow d A i j) (M.updateRow i (Pi.single j 1)) := by
  apply repT_map_range
  intro r c
  simp only [updateRow_apply, Pi.single_apply, Fin.ext_iff]
  by_cases hr : r.val = i.val
  · simp only [hr, ite_true]
  · simp only [hr, ite_false]
    exact hA r c

theorem inverse_rep {A : MatrixL} {M : Matrix (Fin d) (Fin d) ℚ}
    (hA : RepT A M) : RepT (inverse d A) (M⁻¹ : Matrix (Fin d) (Fin d) ℚ) := by
  apply repT_map_range
  intro i j
  rw [determinant_eq (by simp [replaceRow, table]) (replaceRow_rep hA j i)]
  have hcopy : RepT (table d d (ent A)) M := repT_map_range _ _ hA
  rw [determinant_eq (table_length _ _ _) hcopy, ← adjugate_apply M i j, inv_def,
    Ring.inverse_eq_inv]
  simp only [Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

def shift (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j ↦ if i.val = j.val + 1 then 1 else 0

theorem mul_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (A * shift n) i j = if h : j.val + 1 < n then A i ⟨j.val + 1, h⟩ else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : j.val + 1 < n
  · rw [dite_eq_left hj, Finset.sum_eq_single (⟨j.val + 1, hj⟩ : Fin n)]
    · simp [shift]
    · intro b _ hb
      have hb' : b.val ≠ j.val + 1 := fun h ↦ hb (Fin.ext h)
      simp [shift, hb']
    · simp
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.val ≠ j.val + 1 := by omega
    simp [shift, hb]

theorem shift_pow (n p : ℕ) (i j : Fin n) :
    (shift n ^ p : Matrix (Fin n) (Fin n) ℚ) i j =
      if i.val = j.val + p then 1 else 0 := by
  induction p generalizing j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff]
  | succ p ih =>
    rw [pow_succ, mul_shift]
    by_cases hj : j.val + 1 < n
    · rw [dite_eq_left hj, ih]
      have he : (⟨j.val + 1, hj⟩ : Fin n).val + p = j.val + (p + 1) := by
        change j.val + 1 + p = j.val + (p + 1)
        omega
      rw [he]
    · rw [dite_eq_right hj]
      have hh : i.val ≠ j.val + (p + 1) := by omega
      rw [ite_eq_right hh]

theorem shift_nilpotent (n : ℕ) : shift n ^ n = 0 := by
  ext i j
  rw [shift_pow]
  have hh : i.val ≠ j.val + n := by omega
  simp [hh]

theorem kronecker_pow (A : Matrix (Fin m) (Fin m) ℚ)
    (B : Matrix (Fin d) (Fin d) ℚ) (p : ℕ) :
    (A ⊗ₖ B) ^ p = (A ^ p) ⊗ₖ (B ^ p) := by
  induction p with
  | zero => simp only [pow_zero, one_kronecker_one]
  | succ p ih => rw [pow_succ, ih, ← mul_kronecker_mul, ← pow_succ, ← pow_succ]

def blockRows (d p : ℕ) (A : MatrixL) : MatrixL :=
  table ((p + 1) * d) ((p + 1) * d) fun r c ↦
    (if r / d = c / d ∧ r % d = c % d then 1 else 0) -
      (if r / d = c / d + 1 then ent A (r % d) (c % d) else 0)

/-- Read the bottom-left block of the inverse of the block bidiagonal system. -/
def power (d p : ℕ) (A : MatrixL) : MatrixL :=
  let B := inverse ((p + 1) * d) (blockRows d p A)
  table d d fun i j ↦ ent B (i + d * p) j

theorem blockRows_polytime {d p : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime p input encUnary)
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ blockRows (d x) (p x) (A x)) input encMatrix := by
  apply table_polytime (unary_mul' (unary_add' hp (const 1)) hd)
    (unary_mul' (unary_add' hp (const 1)) hd)
  have hb := (fst input encUnary).comp (fst _ encUnary)
  have hdr := hd.comp hb
  have hr := (snd (encPair input encUnary) encUnary)
  have hi := (snd input encUnary).comp (fst _ encUnary)
  have hri := unary_div.comp (hi.prod hdr)
  have hrj := unary_div.comp (hr.prod hdr)
  have hci := unary_mod.comp (hi.prod hdr)
  have hcj := unary_mod.comp (hr.prod hdr)
  apply rat_sub'
  · apply ite_prop _ (const 1) (const 0)
    refine (bool_and.comp ((unary_eq' hri hrj).prod (unary_eq' hci hcj))).of_enc_eq ?_
    intro x
    simp only [Function.comp_apply, Bool.decide_and]
  · exact ite_prop (unary_eq' hri (unary_add' hrj (const 1)))
      (ent' (hA.comp hb) hci hcj) (const 0)

theorem power_polytime {d p : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime p input encUnary)
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ power (d x) (p x) (A x)) input encMatrix := by
  have hB := inverse_polytime (unary_mul' (unary_add' hp (const 1)) hd)
    (blockRows_polytime hd hp hA)
  apply table_polytime hd hd
  have hb := (fst input encUnary).comp (fst _ encUnary)
  exact ent' (hB.comp hb)
    (unary_add' ((snd _ _).comp (fst _ _)) ((unary_mul' hd hp).comp hb)) (snd _ _)

theorem blockRows_rep {A : MatrixL} {M : Matrix (Fin d) (Fin d) ℚ}
    (hA : RepT A M) (p : ℕ) :
    RepT (blockRows d p A)
      (reindexRingEquiv ℚ finProdFinEquiv (1 - shift (p + 1) ⊗ₖ M)) := by
  apply repT_map_range
  intro i j
  change (if i.val / d = j.val / d ∧ i.val % d = j.val % d then 1 else 0) -
    (if i.val / d = j.val / d + 1 then ent A (i.val % d) (j.val % d) else 0) =
      (1 - shift (p + 1) ⊗ₖ M :
        Matrix (Fin (p + 1) × Fin d) (Fin (p + 1) × Fin d) ℚ)
          (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.kroneckerMap_apply, shift]
  simp only [Prod.ext_iff, Fin.ext_iff]
  rw [← hA (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2]
  split_ifs <;> simp_all

theorem block_inverse (M : Matrix (Fin d) (Fin d) ℚ) (p : ℕ) :
    (1 - shift (p + 1) ⊗ₖ M)⁻¹ =
      ∑ k ∈ Finset.range (p + 1), (shift (p + 1) ⊗ₖ M) ^ k := by
  apply Matrix.inv_eq_right_inv
  rw [mul_neg_geom_sum, kronecker_pow, shift_nilpotent, zero_kronecker, sub_zero]

theorem block_inverse_entry (M : Matrix (Fin d) (Fin d) ℚ) (p : ℕ) (i j : Fin d) :
    ((1 - shift (p + 1) ⊗ₖ M)⁻¹ :
      Matrix (Fin (p + 1) × Fin d) (Fin (p + 1) × Fin d) ℚ) (Fin.last p, i) (0, j) =
        (M ^ p : Matrix (Fin d) (Fin d) ℚ) i j := by
  rw [block_inverse]
  simp only [Matrix.sum_apply, kronecker_pow, kronecker_apply, shift_pow, Fin.val_last,
    Fin.val_zero, Nat.zero_add, ite_mul, one_mul, zero_mul]
  simp

theorem power_rep {A : MatrixL} {M : Matrix (Fin d) (Fin d) ℚ}
    (hA : RepT A M) (p : ℕ) :
    RepT (power d p A) (M ^ p : Matrix (Fin d) (Fin d) ℚ) := by
  let e : Fin (p + 1) × Fin d ≃ Fin ((p + 1) * d) := finProdFinEquiv
  let K := shift (p + 1) ⊗ₖ M
  let S := ∑ k ∈ Finset.range (p + 1), K ^ k
  let f := reindexRingEquiv ℚ e
  have hKS : (1 - K) * S = 1 := by
    rw [mul_neg_geom_sum, kronecker_pow, shift_nilpotent, zero_kronecker, sub_zero]
  have hmap : (f (1 - K))⁻¹ = f S := Matrix.inv_eq_right_inv (by
    rw [← map_mul, hKS, map_one])
  apply repT_map_range
  intro i j
  have hrep := inverse_rep (blockRows_rep hA p) (e (Fin.last p, i)) (e (0, j))
  change ent (inverse ((p + 1) * d) (blockRows d p A)) (i.val + d * p) j.val = _
  have hleft : (e (Fin.last p, i)).val = i.val + d * p := rfl
  have hright : (e (0, j)).val = j.val := by simp [e]
  rw [← hleft, ← hright, hrep]
  change (f (1 - K))⁻¹ (e (Fin.last p, i)) (e (0, j)) = _
  rw [hmap]
  change S (e.symm (e (Fin.last p, i))) (e.symm (e (0, j))) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]
  change (∑ k ∈ Finset.range (p + 1), K ^ k) (Fin.last p, i) (0, j) = _
  change (∑ k ∈ Finset.range (p + 1), (shift (p + 1) ⊗ₖ M) ^ k)
    (Fin.last p, i) (0, j) = _
  rw [← block_inverse]
  exact block_inverse_entry M p i j

theorem matrixOf_power (d p : ℕ) (A : MatrixL) :
    matrixOf d (power d p A) = matrixOf d A ^ p := by
  ext i j
  exact power_rep (fun _ _ ↦ rfl) p i j

theorem matrixOf_power_real (d p : ℕ) (A : MatrixL) :
    (matrixOf d (power d p A)).map (algebraMap ℚ ℝ) =
      (matrixOf d A).map (algebraMap ℚ ℝ) ^ p := by
  rw [matrixOf_power, Matrix.map_pow]

theorem power_reindex_real (d p : ℕ) (A : MatrixL) :
    reindexRingEquiv ℝ (finProdFinEquiv.symm : Fin (d * d) ≃ Fin d × Fin d)
      ((matrixOf (d * d) (power (d * d) p A)).map (algebraMap ℚ ℝ)) =
        (reindexRingEquiv ℝ (finProdFinEquiv.symm : Fin (d * d) ≃ Fin d × Fin d)
          ((matrixOf (d * d) A).map (algebraMap ℚ ℝ))) ^ p := by
  let f := reindexRingEquiv ℝ (finProdFinEquiv.symm : Fin (d * d) ≃ Fin d × Fin d)
  have h := f.map_pow ((matrixOf (d * d) A).map (algebraMap ℚ ℝ)) p
  have hmap := matrixOf_power_real (d * d) p A
  have hh := congrArg f hmap
  exact hh.trans h

def trace (d : ℕ) (A : MatrixL) : ℚ :=
  ((List.range d).map fun i ↦ ent A i i).sum

theorem trace_polytime {d : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ trace (d x) (A x)) input encRat :=
  sum_polytime hd (ent' (hA.comp (fst _ _)) (snd _ _) (snd _ _))

theorem trace_eq {A : MatrixL} {M : Matrix (Fin d) (Fin d) ℚ} (hA : RepT A M) :
    trace d A = M.trace := (sum_fin_eq_list _ _ fun i ↦ hA i i).symm

def powerTrace (d p : ℕ) (A : MatrixL) : ℚ := trace d (power d p A)

theorem powerTrace_polytime {d p : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime p input encUnary)
    (hA : ComputableInPolyTime A input encMatrix) :
    ComputableInPolyTime (fun x ↦ powerTrace (d x) (p x) (A x)) input encRat :=
  trace_polytime hd (power_polytime hd hp hA)

theorem powerTrace_eq (d p : ℕ) (A : MatrixL) :
    powerTrace d p A = (matrixOf d A ^ p).trace :=
  trace_eq (power_rep (fun _ _ ↦ rfl) p)

/-- Scores from a feature table and its weighted covariance. -/
def scores (d p : ℕ) (pts : Points) (w : Vector) : Vector :=
  quadraticScores d (power d p (covariance d pts w))
    (translate d pts (mean d pts w))

theorem scores_polytime {d p : α → ℕ} {pts : α → Points} {w : α → Vector}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime p input encUnary)
    (hx : ComputableInPolyTime pts input encPoints)
    (hw : ComputableInPolyTime w input encVector) :
    ComputableInPolyTime (fun x ↦ scores (d x) (p x) (pts x) (w x)) input encVector :=
  quadraticScores_polytime hd (power_polytime hd hp (covariance_polytime hd hx hw))
    (translate_polytime hd hx (mean_polytime hd hx hw))


theorem scores_rep {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {w : Vector} {w' : Fin m → ℚ}
    (hx : RepT pts x) (hw : RepV w w') (p : ℕ) :
    let a := (∑ i, w' i)⁻¹ • ∑ i, w' i • x i
    let C : Matrix (Fin d) (Fin d) ℚ :=
      (∑ i, w' i)⁻¹ • ∑ i, w' i • vecMulVec (x i - a) (x i - a)
    RepV (scores d p pts w) (fun i ↦ quad (C ^ p) (x i - a)) :=
  quadraticScores_rep ((translate_length _ _ _).trans hlen)
    (translate_rep hlen hx (mean_rep hlen hx hw)) (power_rep (covariance_rep hlen hx hw) p)

theorem scores_real {pts : Points} (hlen : pts.length = m)
    {x : Fin m → Fin d → ℚ} {w : Vector} {w' : Fin m → ℚ}
    (hx : RepT pts x) (hw : RepV w w') (p : ℕ) (i : Fin m) :
    (vectorOf m (scores d p pts w) i : ℝ) =
      let y := (fun j ↦ (x i j : ℝ)) - Robust.RBAux.FrameLoop.center
        (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ))
      y ⬝ᵥ ((Robust.RBAux.FrameLoop.covariance
        (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ)) ^ p) *ᵥ y) := by
  let a := (∑ i, w' i)⁻¹ • ∑ i, w' i • x i
  let C : Matrix (Fin d) (Fin d) ℚ :=
    (∑ i, w' i)⁻¹ • ∑ i, w' i • vecMulVec (x i - a) (x i - a)
  have h := congrArg (Rat.cast : ℚ → ℝ) (scores_rep hlen hx hw p i)
  change (vectorOf m (scores d p pts w) i : ℝ) =
    ((quad (C ^ p) (x i - a) : ℚ) : ℝ) at h
  rw [← quad_cast] at h
  change (vectorOf m (scores d p pts w) i : ℝ) =
    quad ((C ^ p).map (algebraMap ℚ ℝ)) (fun j ↦ ((x i - a) j : ℝ)) at h
  rw [Matrix.map_pow] at h
  have hmean : (fun j ↦ (a j : ℝ)) = Robust.RBAux.FrameLoop.center
      (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ)) := by
    ext j
    simp [a, Robust.RBAux.FrameLoop.center, Robust.RBAux.FrameLoop.mass]
  have hcov : C.map (algebraMap ℚ ℝ) = Robust.RBAux.FrameLoop.covariance
      (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ)) := by
    have hC : matrixOf d (covariance d pts w) = C := by
      ext j k
      exact covariance_rep hlen hx hw j k
    rw [← hC]
    exact covariance_real hlen hx hw
  have hsub : (fun j ↦ ((x i - a) j : ℝ)) = (fun j ↦ (x i j : ℝ)) -
      Robust.RBAux.FrameLoop.center (fun i j ↦ (x i j : ℝ)) (fun i ↦ (w' i : ℝ)) := by
    rw [← hmean]
    ext j
    simp
  change (vectorOf m (scores d p pts w) i : ℝ) =
    quad (C.map (algebraMap ℚ ℝ) ^ p) (fun j ↦ ((x i - a) j : ℝ)) at h
  rw [hcov, hsub] at h
  exact h

end ABBKS26.Assembly.Exec.FrameAux.Features
