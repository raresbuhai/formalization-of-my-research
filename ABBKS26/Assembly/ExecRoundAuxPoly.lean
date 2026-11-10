module

public import ABBKS26.Assembly.ExecRoundAuxFacts
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq

/-! Absolute-degree machine certificates for the planner's rational matrix operations. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RoundProgram

open Common Rounding FrameAux.Linear
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

@[local fun_prop]
private theorem binary_of_unary {n : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) : ComputableInPolyTime n enc encNat :=
  unary_to_binary.comp hn

private theorem binary_add' {m n : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hn : ComputableInPolyTime n enc encNat) :
    ComputableInPolyTime (fun x ↦ m x + n x) enc encNat :=
  .of_tidy (ComputableTidilyInPolyTime.binary_add' hm.tidy hn.tidy)

/-- Two unary ranges suffice to construct a rational square table. -/
@[fun_prop]
theorem table_polytime {d : α → ℕ} {f : α → ℕ → ℕ → ℚ}
    (hd : ComputableInPolyTime d enc encUnary)
    (hf : ComputableInPolyTime (fun p : α × ℕ × ℕ ↦ f p.1 p.2.1 p.2.2)
      (encPair enc (encPair encUnary encUnary)) encRat) :
    ComputableInPolyTime (fun x ↦ table (d x) (f x)) enc encMatrix := by
  have hd' : ComputableInPolyTime (fun p : α × ℕ ↦ d p.1)
      (encPair enc encUnary) encUnary := hd.comp (fst _ _)
  have hf' : ComputableInPolyTime (fun p : (α × ℕ) × ℕ ↦ f p.1.1 p.1.2 p.2)
      (encPair (encPair enc encUnary) encUnary) encRat :=
    hf.comp (g := fun p : (α × ℕ) × ℕ ↦ (p.1.1, p.1.2, p.2))
      (((fst _ _).comp (fst _ _)).prod (((snd _ _).comp (fst _ _)).prod (snd _ _)))
  have hr : ComputableInPolyTime
      (fun p : α × ℕ ↦ (List.range (d p.1)).map (f p.1 p.2))
      (encPair enc encUnary) encVector := mapWithInput (range.comp hd') hf'
  exact mapWithInput (range.comp hd) hr

@[fun_prop]
theorem identity_polytime {d : α → ℕ} (hd : ComputableInPolyTime d enc encUnary) :
    ComputableInPolyTime (fun x ↦ identity (d x)) enc encMatrix := by
  unfold identity
  exact table_polytime hd (ite_prop (by fun_prop) (const 1) (const 0))

@[fun_prop]
theorem subtract_polytime {d : α → ℕ} {A B : α → MatrixL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hA : ComputableInPolyTime A enc encMatrix)
    (hB : ComputableInPolyTime B enc encMatrix) :
    ComputableInPolyTime (fun x ↦ subtract (d x) (A x) (B x)) enc encMatrix := by
  unfold subtract
  apply table_polytime hd
  fun_prop

@[fun_prop]
theorem multiply_polytime {d : α → ℕ} {A B : α → MatrixL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hA : ComputableInPolyTime A enc encMatrix)
    (hB : ComputableInPolyTime B enc encMatrix) :
    ComputableInPolyTime (fun x ↦ multiply (d x) (A x) (B x)) enc encMatrix := by
  unfold multiply
  apply table_polytime hd
  apply rat_sum'
  apply mapWithInput (range.comp (hd.comp (fst _ _)))
  fun_prop

@[fun_prop]
theorem trace_polytime {d : α → ℕ} {A : α → MatrixL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hA : ComputableInPolyTime A enc encMatrix) :
    ComputableInPolyTime (fun x ↦ trace (d x) (A x)) enc encRat := by
  unfold trace
  exact rat_sum' (mapWithInput (range.comp hd) (by fun_prop))

/-- Denominator clearing and integer determinants have an absolute polynomial degree. -/
@[fun_prop]
theorem determinant_polytime {A : α → MatrixL}
    (hA : ComputableInPolyTime A enc encMatrix) :
    ComputableInPolyTime (fun x ↦ determinant (A x)) enc encRat := by
  unfold determinant
  exact rat_div'
    (rat_intCast' (SoS.PDTestRows.detRows' (SoS.PDTestRat.scale_polytime.comp hA)))
    (rat_pow' (rat_intCast' (SoS.PDTestRat.commonDen_polytime.comp hA))
      ((length_list encVector).comp hA))

@[fun_prop]
theorem replaceRow_polytime {A : α → MatrixL} {i j : α → ℕ}
    (hA : ComputableInPolyTime A enc encMatrix)
    (hi : ComputableInPolyTime i enc encUnary)
    (hj : ComputableInPolyTime j enc encUnary) :
    ComputableInPolyTime (fun x ↦ replaceRow (A x) (i x) (j x)) enc encMatrix := by
  unfold replaceRow
  apply table_polytime ((length_list encVector).comp hA)
  apply ite_prop (by fun_prop)
  · exact ite_prop (by fun_prop) (const 1) (const 0)
  · fun_prop

@[fun_prop]
theorem inverse_polytime {A : α → MatrixL}
    (hA : ComputableInPolyTime A enc encMatrix) :
    ComputableInPolyTime (fun x ↦ inverse (A x)) enc encMatrix := by
  unfold inverse
  apply table_polytime ((length_list encVector).comp hA)
  fun_prop

@[fun_prop]
theorem gram_polytime {d : α → ℕ} {B : α → Points}
    (hd : ComputableInPolyTime d enc encUnary)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun x ↦ gram (d x) (B x)) enc encMatrix := by
  unfold gram
  apply table_polytime ((length_list encVector).comp hB)
  fun_prop

/-- Exact projectors are recomputed from the rounded stored basis by Cramer's rule.
The bound is polynomial in dimension, basis size, and stored bits with an absolute exponent. -/
@[fun_prop]
theorem projection_polytime {d : α → ℕ} {B : α → Points}
    (hd : ComputableInPolyTime d enc encUnary)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun x ↦ projection (d x) (B x)) enc encMatrix := by
  have hG := inverse_polytime (gram_polytime hd hB)
  unfold projection
  apply table_polytime hd
  apply rat_sum'
  apply mapWithInput (range.comp ((length_list encVector).comp (hB.comp (fst _ _))))
  apply rat_sum'
  apply mapWithInput (range.comp ((length_list encVector).comp
    (hB.comp ((fst _ _).comp (fst _ _)))))
  fun_prop

@[fun_prop]
theorem complement_polytime {d : α → ℕ} {B : α → Points}
    (hd : ComputableInPolyTime d enc encUnary)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun x ↦ complement (d x) (B x)) enc encMatrix := by
  unfold complement
  exact subtract_polytime hd (identity_polytime hd) (projection_polytime hd hB)

/-- The packing bound is computed in binary; its value need not be polynomially bounded. -/
theorem packCount_polytime : ComputableInPolyTime
    (fun q : ℚ × ℕ ↦ packCount q.1 q.2) (encPair encRat encUnary) encNat := by
  have hr := binary_of_unary (snd encRat encUnary)
  have hs : ComputableInPolyTime (fun q : ℚ × ℕ ↦ sqrtUp (q.2 : ℚ))
      (encPair encRat encUnary) encRat := by
    have h := rat_natCast' (binary_add' (binary_sqrt' hr) (const 1))
    convert h using 1
    funext q
    simp [sqrtUp]
  unfold packCount
  exact binary_pow' (binary_mul' (const 2)
    (rat_natCeil' (rat_div' (rat_mul' (const 40) hs) (fst _ _)))) (snd _ _)

theorem threshold_polytime : ComputableInPolyTime
    (fun q : ℚ × ℕ ↦ greedyThreshold q.1 q.2) (encPair encRat encUnary) encRat := by
  have hr := rat_natCast' (binary_of_unary (snd encRat encUnary))
  unfold greedyThreshold
  exact rat_div' (const 1) (rat_two_pow' (binary_clog_two.comp
    (rat_natCeil' (rat_div' (rat_mul' (const 1280000) (rat_add' hr (const 1)))
      (rat_pow' (fst _ _) (const 4))))))

theorem greedyCap_polytime : ComputableInPolyTime
    (fun q : ℚ × ℕ ↦ greedyCap q.1 q.2) (encPair encRat encUnary) encNat := by
  unfold greedyCap
  exact binary_add' (rat_natCeil' (rat_div' (const 32) threshold_polytime)) (const 1)

theorem rankCap_polytime : ComputableInPolyTime
    (fun q : ℚ × ℕ ↦ rankCap q.1 q.2) (encPair encRat encUnary) encNat := by
  unfold rankCap
  exact binary_mul' (binary_add' packCount_polytime (const 1)) greedyCap_polytime

private theorem radiusRank_polytime : ComputableInPolyTime
    (fun a : RoundArgs ↦ (a.2.2.1, a.2.2.2.1)) encRoundArgs
      (encPair encRat encUnary) := by fun_prop

theorem objectivePrecision_polytime : ComputableInPolyTime objectivePrecision
    encRoundArgs encUnary := by
  have hd : ComputableInPolyTime (fun a : RoundArgs ↦ (a.2.1 : ℚ)) encRoundArgs encRat :=
    rat_natCast' (binary_of_unary (by fun_prop))
  unfold objectivePrecision
  exact binary_clog_two.comp (rat_natCeil' (rat_div'
    (rat_mul' (const 1024) (rat_add' hd (const 1))) (rat_pow' (by fun_prop) (const 2))))

private theorem gridPrecision_polytime : ComputableInPolyTime
    (fun q : ℕ × ℚ ↦ Nat.clog 2 ⌈120 * (q.1 + 1 : ℚ) / q.2⌉₊ + 2)
    (encPair encUnary encRat) encUnary := by
  have hd := rat_natCast' (binary_of_unary (fst encUnary encRat))
  have hq := rat_div' (rat_mul' (const 120) (rat_add' hd (const 1))) (snd _ _)
  exact unary_add' (binary_clog_two.comp (rat_natCeil' hq)) (const 2)

theorem greedyPrecision_polytime : ComputableInPolyTime greedyPrecision
    encRoundArgs encUnary := by
  have hd : ComputableInPolyTime (fun a : RoundArgs ↦ a.2.1) encRoundArgs encUnary := by
    fun_prop
  have ht := threshold_polytime.comp (g := fun a : RoundArgs ↦
    (a.2.2.1, a.2.2.2.1)) radiusRank_polytime
  have hp := gridPrecision_polytime.comp (g := fun a : RoundArgs ↦
    (a.2.1, greedyThreshold a.2.2.1 a.2.2.2.1))
    (hd.prod ht)
  exact hp.of_enc_eq fun _ ↦ rfl

@[fun_prop]
theorem round_polytime {p : α → ℕ} {q : α → ℚ}
    (hp : ComputableInPolyTime p enc encUnary)
    (hq : ComputableInPolyTime q enc encRat) :
    ComputableInPolyTime (fun x ↦ roundRat (p x) (q x)) enc encRat := by
  unfold roundRat
  fun_prop

@[fun_prop]
theorem roundedProjection_polytime {a : α → RoundArgs} {B : α → Points}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hB : ComputableInPolyTime B enc encPoints) :
    ComputableInPolyTime (fun x ↦ roundedProjection (a x) (B x)) enc encMatrix := by
  have hp := objectivePrecision_polytime.comp ha
  have hP := projection_polytime (((fst _ _).comp (snd _ _)).comp ha) hB
  unfold roundedProjection
  apply mapWithInput hP
  apply mapWithInput (snd _ _)
  exact round_polytime (hp.comp ((fst _ _).comp (fst _ _))) (snd _ _)

/-- Rational normalization and the fixed greedy grid are polynomial on arbitrary witnesses. -/
theorem candidate_polytime {a : α → RoundArgs} {B : α → Points} {y : α → List ℤ}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hB : ComputableInPolyTime B enc encPoints)
    (hy : ComputableInPolyTime y enc (encList encIntBin)) :
    ComputableInPolyTime (fun x ↦ candidate (a x) (B x) (y x)) enc encVector := by
  have hd : ComputableInPolyTime (fun x ↦ (a x).2.1) enc encUnary :=
    ((fst _ _).comp (snd _ _)).comp ha
  have hyRat : ComputableInPolyTime (fun x ↦ (y x).map fun (z : ℤ) ↦ (z : ℚ))
      enc encVector :=
    mapWithInput (list := y) (f := fun _ (z : ℤ) ↦ (z : ℚ)) hy
      (rat_intCast' (snd _ _))
  have hx : ComputableInPolyTime (fun x ↦ mulVecL (a x).2.1
      (complement (a x).2.1 (B x)) ((y x).map fun (z : ℤ) ↦ (z : ℚ))) enc encVector :=
    mulVecL' hd (complement_polytime hd hB) hyRat
  have hs : ComputableInPolyTime (fun x ↦ scaleL (dotL (a x).2.1
      (mulVecL (a x).2.1 (complement (a x).2.1 (B x)) ((y x).map fun (z : ℤ) ↦ (z : ℚ)))
      (mulVecL (a x).2.1 (complement (a x).2.1 (B x)) ((y x).map fun (z : ℤ) ↦ (z : ℚ)))) / 2)
      enc encRat := rat_div' (scaleL_polytime.comp (dotL' hd hx hx)) (const 2)
  have hp := greedyPrecision_polytime.comp ha
  unfold candidate
  exact mapWithInput hx (round_polytime (hp.comp (fst _ _))
    (rat_mul' (hs.comp (fst _ _)) (snd _ _)))

private theorem decide_and_polytime {p q : α → Prop} [DecidablePred p] [DecidablePred q]
    (hp : ComputableInPolyTime (fun x ↦ decide (p x)) enc encBool)
    (hq : ComputableInPolyTime (fun x ↦ decide (q x)) enc encBool) :
    ComputableInPolyTime (fun x ↦ decide (p x ∧ q x)) enc encBool := by
  refine (bool_and.comp (hp.prod hq)).of_enc_eq fun x ↦ ?_
  congr 1

/-- The append guard is a finite list scan and rational residual comparisons. -/
theorem acceptable_polytime {a : α → RoundArgs} {B : α → Points} {v : α → Vector}
    (ha : ComputableInPolyTime a enc encRoundArgs)
    (hB : ComputableInPolyTime B enc encPoints)
    (hv : ComputableInPolyTime v enc encVector) :
    ComputableInPolyTime (fun x ↦ decide (acceptable (a x) (B x) (v x))) enc encBool := by
  have hd := ((fst _ _).comp (snd _ _)).comp ha
  have hz := mulVecL' hd (complement_polytime hd hB) hv
  have hq := dotL' hd hz hz
  have hall := ComputableTidilyInPolyTime.allWithInput
    (test := fun (_ : α) (q : ℚ) ↦ decide (-1 ≤ q ∧ q ≤ 1)) hv.tidy
    (decide_and_polytime (rat_le' (const (-1)) (snd enc encRat))
      (rat_le' (snd enc encRat) (const 1))).tidy
  have hall' : ComputableInPolyTime (fun x ↦ decide (∀ q ∈ v x, -1 ≤ q ∧ q ≤ 1))
      enc encBool := by
    convert ComputableInPolyTime.of_tidy hall using 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, List.all_eq_true]
  unfold acceptable
  exact decide_and_polytime (unary_eq' ((length_list encRat).comp hv) hd)
    (decide_and_polytime hall' (decide_and_polytime
      (rat_le' (const (9 / 64)) hq) (rat_le' hq (const (81 / 64)))))

end ABBKS26.Assembly.Exec.RoundProgram
