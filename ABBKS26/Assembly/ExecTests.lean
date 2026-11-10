module

public import ABBKS26.Assembly.ExecRefine
import all ABBKS26.Select.Pairwise

/-! # Pairwise rational tests and least-winner reclustering -/

@[expose] public section

namespace ABBKS26.Assembly.Exec

open Common _root_.ABBKS26.Tree Select
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators
open FrameAux.Linear Matrix MeasureTheory

abbrev TestArgs := ℕ × ℚ × EstimateL × EstimateL
abbrev encTestArgs := encPair encUnary (encPair encRat (encPair encEstimate encEstimate))

structure TestCode where
  tests : TestBuilder
  run : Mode → TestArgs × ℕ → TestL

structure TestSpecL (T : TestCode) : Prop where
  contract : TestSpec T.tests
  polytime : ∀ mode, ComputableInPolyTime (T.run mode)
    (encPair encTestArgs encUnary) encTest
  agrees : ∀ {d} mode Δ (A B : Robust.Estimate d) fuel,
    T.run mode ((d, Δ, estimateList A, estimateList B), fuel) =
      testList (T.tests mode Δ A B fuel)

private def testScale (Δ : ℚ) : ℚ := SoS.Loop.sqrtP 0 (SoS.Loop.sqrtP 0 Δ)

private def comparisonL (d : ℕ) (Δ : ℚ) (A B : MatrixL) : MatrixL :=
  RoundProgram.table d fun i j ↦ 2 * testScale Δ ^ 2 * ent B i j - ent A i j

private def spectralL (d : ℕ) (Δ : ℚ) (B : MatrixL) (z : List ℤ)
    (left : Bool) : TestL :=
  let u := z.map (Int.cast : ℤ → ℚ)
  ((RoundProgram.table d fun i j ↦ u.getD i 0 * u.getD j 0, [], 0),
    2 * testScale Δ * quadL d B u, left)

private def meanL (d : ℕ) (A B : EstimateL) : TestL :=
  let δ := (List.range d).map fun i ↦ A.1.getD i 0 - B.1.getD i 0
  let u := mulVecL d (FrameAux.Features.inverse d A.2) δ
  (([], u, 0), (dotL d u A.1 + dotL d u B.1) / 2, false)

private def differenceL (d : ℕ) (A B : MatrixL) : MatrixL :=
  let S := RoundProgram.table d fun i j ↦ ent A i j + ent B i j
  let I := FrameAux.Features.inverse d S
  RoundProgram.multiply d (RoundProgram.multiply d I (RoundProgram.subtract d B A)) I

private def quadraticL (d : ℕ) (A B : EstimateL) : TestL :=
  let Q := differenceL d A.2 B.2
  ((Q, [], 0), (RoundProgram.trace d (RoundProgram.multiply d Q A.2) +
    RoundProgram.trace d (RoundProgram.multiply d Q B.2)) / 2, true)

private def rawTestL (mode : Mode) (d : ℕ) (Δ : ℚ) (A B : EstimateL) : TestL :=
  match mode with
  | .identical => meanL d A B
  | .centered =>
    (SoS.PDTestRat.test (comparisonL d Δ A.2 B.2)).elim
      ((SoS.PDTestRat.test (comparisonL d Δ B.2 A.2)).elim
        (quadraticL d A B) (fun z ↦ spectralL d Δ A.2 z true))
      (fun z ↦ spectralL d Δ B.2 z false)

/-- Store exactly the requested dimension, also on malformed list inputs. -/
private def canonicalTestL (d : ℕ) (T : TestL) : TestL :=
  ((RoundProgram.table d (ent T.1.1),
    (List.range d).map fun i ↦ T.1.2.1.getD i 0, T.1.2.2), T.2)

@[local fun_prop]
private theorem testScale_polytime {α : Type} {enc : α ↪ List Bool} {Δ : α → ℚ}
    (hΔ : ComputableInPolyTime Δ enc encRat) :
    ComputableInPolyTime (fun a ↦ testScale (Δ a)) enc encRat := by
  unfold testScale
  exact SoS.PolyTime.sqrtP' (const 0) (SoS.PolyTime.sqrtP' (const 0) hΔ)

@[local fun_prop]
private theorem comparisonL_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {Δ : α → ℚ} {A B : α → MatrixL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hΔ : ComputableInPolyTime Δ enc encRat)
    (hA : ComputableInPolyTime A enc encMatrix)
    (hB : ComputableInPolyTime B enc encMatrix) :
    ComputableInPolyTime (fun a ↦ comparisonL (d a) (Δ a) (A a) (B a))
      enc encMatrix := by
  unfold comparisonL
  apply RoundProgram.table_polytime hd
  fun_prop

@[local fun_prop]
private theorem spectralL_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {Δ : α → ℚ} {B : α → MatrixL}
    {z : α → List ℤ} {left : α → Bool}
    (hd : ComputableInPolyTime d enc encUnary)
    (hΔ : ComputableInPolyTime Δ enc encRat)
    (hB : ComputableInPolyTime B enc encMatrix)
    (hz : ComputableInPolyTime z enc (encList encIntBin))
    (hl : ComputableInPolyTime left enc encBool) :
    ComputableInPolyTime (fun a ↦ spectralL (d a) (Δ a) (B a) (z a) (left a))
      enc encTest := by
  have hu : ComputableInPolyTime (fun a ↦ (z a).map (Int.cast : ℤ → ℚ))
      enc encVector := mapWithInput hz (by fun_prop)
  unfold spectralL
  apply ComputableInPolyTime.prod
  · apply ComputableInPolyTime.prod
    · apply RoundProgram.table_polytime hd
      fun_prop
    · exact (const []).prod (const 0)
  · fun_prop

@[local fun_prop]
private theorem meanL_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {A B : α → EstimateL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hA : ComputableInPolyTime A enc encEstimate)
    (hB : ComputableInPolyTime B enc encEstimate) :
    ComputableInPolyTime (fun a ↦ meanL (d a) (A a) (B a)) enc encTest := by
  have hδ : ComputableInPolyTime
      (fun a ↦ (List.range (d a)).map fun i ↦ (A a).1.getD i 0 - (B a).1.getD i 0)
      enc encVector := mapWithInput (range.comp hd) (by fun_prop)
  have hI := FrameAux.Features.inverse_polytime hd hA.snd'
  have hu := mulVecL' hd hI hδ
  exact ((const []).prod (hu.prod (const 0))).prod
    ((rat_div' (rat_add' (dotL' hd hu hA.fst') (dotL' hd hu hB.fst'))
      (const 2)).prod (const false))

@[local fun_prop]
private theorem differenceL_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {A B : α → MatrixL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hA : ComputableInPolyTime A enc encMatrix)
    (hB : ComputableInPolyTime B enc encMatrix) :
    ComputableInPolyTime (fun a ↦ differenceL (d a) (A a) (B a)) enc encMatrix := by
  have hS : ComputableInPolyTime
      (fun a ↦ RoundProgram.table (d a) fun i j ↦ ent (A a) i j + ent (B a) i j)
      enc encMatrix := RoundProgram.table_polytime hd (by fun_prop)
  have hI := FrameAux.Features.inverse_polytime hd hS
  exact RoundProgram.multiply_polytime hd
    (RoundProgram.multiply_polytime hd hI (RoundProgram.subtract_polytime hd hB hA)) hI

@[local fun_prop]
private theorem quadraticL_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {A B : α → EstimateL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hA : ComputableInPolyTime A enc encEstimate)
    (hB : ComputableInPolyTime B enc encEstimate) :
    ComputableInPolyTime (fun a ↦ quadraticL (d a) (A a) (B a)) enc encTest := by
  have hQ := differenceL_polytime hd hA.snd' hB.snd'
  exact (hQ.prod ((const []).prod (const 0))).prod
    ((rat_div' (rat_add'
      (RoundProgram.trace_polytime hd (RoundProgram.multiply_polytime hd hQ hA.snd'))
      (RoundProgram.trace_polytime hd (RoundProgram.multiply_polytime hd hQ hB.snd')))
      (const 2)).prod (const true))

private theorem rawTestL_polytime (mode : Mode) : ComputableInPolyTime
    (fun a : TestArgs × ℕ ↦ rawTestL mode a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2)
    (encPair encTestArgs encUnary) encTest := by
  cases mode with
  | identical => exact meanL_polytime (by fun_prop) (by fun_prop) (by fun_prop)
  | centered =>
    unfold rawTestL
    apply optionElimWithInput
      (SoS.PDTestRat.test_polytime.comp (comparisonL_polytime
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)))
    · apply optionElimWithInput
        (SoS.PDTestRat.test_polytime.comp (comparisonL_polytime
          (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)))
      · exact quadraticL_polytime (by fun_prop) (by fun_prop) (by fun_prop)
      · exact spectralL_polytime (by fun_prop) (by fun_prop) (by fun_prop)
          (by fun_prop) (const true)
    · exact spectralL_polytime (by fun_prop) (by fun_prop) (by fun_prop)
        (by fun_prop) (const false)

private theorem canonicalTestL_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {T : α → TestL}
    (hd : ComputableInPolyTime d enc encUnary)
    (hT : ComputableInPolyTime T enc encTest) :
    ComputableInPolyTime (fun a ↦ canonicalTestL (d a) (T a)) enc encTest := by
  unfold canonicalTestL
  apply ComputableInPolyTime.prod
  · apply ComputableInPolyTime.prod
    · exact RoundProgram.table_polytime hd (by fun_prop)
    · exact (mapWithInput (range.comp hd) (by fun_prop)).prod (by fun_prop)
  · exact hT.snd'

private theorem canonicalTestL_eq (d : ℕ) (T : TestL) :
    canonicalTestL d T = testList (testOf d T) := by
  have hv {β : Type} (f : ℕ → β) :
      (List.range d).map f = List.ofFn (fun i : Fin d ↦ f i) := by
    rw [← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
    rfl
  simp only [canonicalTestL, RoundProgram.table, testList, testOf, statisticList,
    statisticOf, hv]
  rfl

private theorem decode_table (d : ℕ) (f : ℕ → ℕ → ℚ) :
    matrixOf d (RoundProgram.table d f) = fun (i j : Fin d) ↦ f i j := by
  ext i j
  exact (repT_map_range f _ (fun _ _ ↦ rfl)) i j

private theorem decode_multiply (d : ℕ) (A B : MatrixL) :
    matrixOf d (RoundProgram.multiply d A B) = matrixOf d A * matrixOf d B := by
  rw [RoundProgram.multiply, decode_table]
  ext i j
  exact (sum_fin_eq_list _ _ (fun _ ↦ rfl)).symm

private theorem decode_inverse (d : ℕ) (A : MatrixL) :
    matrixOf d (FrameAux.Features.inverse d A) = (matrixOf d A)⁻¹ := by
  ext i j
  exact FrameAux.Features.inverse_rep (fun _ _ ↦ rfl) i j

private theorem decode_trace (d : ℕ) (A : MatrixL) :
    RoundProgram.trace d A = (matrixOf d A).trace := by
  exact (sum_fin_eq_list _ _ (fun _ ↦ rfl)).symm

private theorem decode_difference (d : ℕ) (A B : MatrixL) :
    matrixOf d (differenceL d A B) = PairwiseAux.differenceMatrix
      (matrixOf d A) (matrixOf d B) := by
  simp only [differenceL, decode_multiply, decode_inverse,
    RoundProgram.subtract, decode_table, PairwiseAux.differenceMatrix]
  rfl

private theorem decode_nil_matrix (d : ℕ) : matrixOf d [] = 0 := by
  ext i j
  simp [matrixOf]

private theorem decode_nil_vector (d : ℕ) : vectorOf d [] = 0 := by
  ext i
  simp [vectorOf]

private theorem decode_mulVec (d : ℕ) (A : MatrixL) (v : Vector) :
    vectorOf d (mulVecL d A v) = matrixOf d A *ᵥ vectorOf d v := by
  ext i
  exact mulVecL_rep (fun _ _ ↦ rfl) (fun _ ↦ rfl) i

private theorem decode_dot (d : ℕ) (u v : Vector) :
    dotL d u v = vectorOf d u ⬝ᵥ vectorOf d v :=
  dotL_eq (fun _ ↦ rfl) (fun _ ↦ rfl)

private theorem decode_mean (d : ℕ) (A B : EstimateL) :
    testOf d (meanL d A B) = meanTest (estimateOf d A) (estimateOf d B) := by
  have hδ : vectorOf d ((List.range d).map fun i ↦ A.1.getD i 0 - B.1.getD i 0) =
      vectorOf d A.1 - vectorOf d B.1 := by
    ext i
    exact getD_map_range _ _ i.isLt
  simp only [meanL, testOf, statisticOf, decode_nil_matrix, decode_mulVec,
    decode_inverse, hδ, decode_dot, meanTest, meanDirection, estimateOf]

private theorem decode_quadratic (d : ℕ) (A B : EstimateL) :
    testOf d (quadraticL d A B) = quadraticPair (estimateOf d A) (estimateOf d B)
      (PairwiseAux.differenceMatrix (matrixOf d A.2) (matrixOf d B.2)) := by
  simp only [quadraticL, testOf, statisticOf, decode_nil_vector, decode_trace,
    decode_multiply, decode_difference, quadraticPair, estimateOf]

private theorem decode_spectral (d : ℕ) (Δ : ℚ) (B : MatrixL) (z : List ℤ)
    (left : Bool) :
    testOf d (spectralL d Δ B z left) =
      ⟨squareStatistic (vectorOf d (z.map (Int.cast : ℤ → ℚ))),
        2 * testScale Δ * quadL d B (z.map (Int.cast : ℤ → ℚ)), left⟩ := by
  simp only [spectralL, testOf, statisticOf, decode_table, decode_nil_vector,
    squareStatistic, Matrix.vecMulVec]
  rfl

private theorem testScale_bounds (Δ : ℚ) (hΔ : (2 : ℝ) ^ 40 ≤ Δ) :
    let r := (Δ : ℝ) ^ (1 / 8 : ℝ)
    r ^ 2 / 4 ≤ testScale Δ ∧ (testScale Δ : ℝ) ≤ r ^ 2 := by
  obtain ⟨hr, hr8⟩ := eighth_root_bounds Δ hΔ
  let r := (Δ : ℝ) ^ (1 / 8 : ℝ)
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hΔ0 : 0 ≤ Δ := by exact_mod_cast (by linarith only [hΔ] : (0 : ℝ) ≤ Δ)
  have hs : Real.sqrt Δ = r ^ 4 := by
    rw [← hr8, show r ^ 8 = (r ^ 4) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  let s := SoS.Loop.sqrtP 0 Δ
  have hs0 : 0 ≤ s := FrameAux.sqrtP_nonneg _ _
  have hsle : (s : ℝ) ≤ r ^ 4 := hs ▸ FrameAux.sqrtP_le 0 hΔ0
  have hserr : r ^ 4 ≤ (s : ℝ) + 1 := by
    have h := (abs_le.mp (SoS.Loop.abs_sqrtP_sub_le 0 hΔ0)).1
    rw [hs] at h
    norm_num at h
    linarith only [h]
  have ht0 : 0 ≤ (testScale Δ : ℝ) := by
    exact_mod_cast FrameAux.sqrtP_nonneg 0 s
  have ht : (testScale Δ : ℝ) ≤ Real.sqrt s := FrameAux.sqrtP_le 0 hs0
  have hterr : Real.sqrt s ≤ (testScale Δ : ℝ) + 1 := by
    have h := (abs_le.mp (SoS.Loop.abs_sqrtP_sub_le 0 hs0)).1
    change -(1 / 2 ^ 0 : ℝ) ≤ (testScale Δ : ℝ) - Real.sqrt s at h
    norm_num only [pow_zero, div_one] at h
    linarith only [h]
  have hsqrt : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt (by exact_mod_cast hs0)
  have hr2 : 1024 ≤ r ^ 2 := by nlinarith only [hr]
  change r ^ 2 / 4 ≤ testScale Δ ∧ (testScale Δ : ℝ) ≤ r ^ 2
  constructor
  · have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg (s : ℝ)) hterr 2
    rw [hsqrt] at hsq
    by_contra h
    have hlt : (testScale Δ : ℝ) + 1 ≤ r ^ 2 / 4 + 1 := by linarith only [h]
    have hh := pow_le_pow_left₀ (by linarith only [ht0] :
      0 ≤ (testScale Δ : ℝ) + 1) hlt 2
    nlinarith only [hserr, hsq, hh, hr2, sq_nonneg (r ^ 2 - 1)]
  · have hsq := pow_le_pow_left₀ ht0 ht 2
    rw [hsqrt] at hsq
    nlinarith only [hsq, hsle, ht0, hr2]

private theorem approximate_spectral_spec {d : ℕ} (A B : Robust.Estimate d) (Δ : ℚ)
    (u : Fin d → ℚ) (τ : ℚ) (hu : u ≠ 0)
    (hτb : 2 * ((Δ : ℝ) ^ (1 / 8 : ℝ) / 2) ^ 2 *
      qform (B.cov.map (algebraMap ℚ ℝ)) (fun i ↦ (u i : ℝ)) ≤ τ)
    (hτa : (τ : ℝ) * ((Δ : ℝ) ^ (1 / 8 : ℝ) / 2) ^ 2 ≤
      qform (A.cov.map (algebraMap ℚ ℝ)) (fun i ↦ (u i : ℝ))) :
    PairSpec .centered Δ A B (spectralPair u τ) := by
  intro k M a b hM hcenter _ _ ha hb hΔ w η hw hweights hη0 hη
  let r := (Δ : ℝ) ^ (1 / 8 : ℝ) / 2
  let v : Vec d := fun i ↦ (u i : ℝ)
  have hv : v ≠ 0 := by
    intro hz
    apply hu
    ext i
    have hi := congrFun hz i
    change (u i : ℝ) = 0 at hi
    exact_mod_cast hi
  have hva : 0 < qform (M.S a) v := by
    simpa only [qform, star_trivial] using (hM.posDef a).dotProduct_mulVec_pos hv
  have hvb : 0 < qform (M.S b) v := by
    simpa only [qform, star_trivial] using (hM.posDef b).dotProduct_mulVec_pos hv
  obtain ⟨hr32, _⟩ := eighth_root_bounds Δ hΔ
  have hr : 2 ≤ r := by dsimp only [r]; linarith only [hr32]
  have hηr : η * r ^ 2 ≤ 1 / 100 := by
    have h := (test_parameters M a Δ w η hM hΔ hw hweights hη0 hη).2
    dsimp only [r]
    nlinarith only [h, mul_nonneg hη0 (sq_nonneg ((Δ : ℝ) ^ (1 / 8 : ℝ)))]
  have hτa' : (τ : ℝ) * r ^ 2 ≤ (11 / 10 : ℝ) * qform (M.S a) v := by
    have hh := ha.2.2.1 v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
    norm_num only [show (1.1 : ℝ) = 11 / 10 by norm_num] at hh
    exact hτa.trans hh
  have hτb' : (9 / 5 : ℝ) * r ^ 2 * qform (M.S b) v ≤ τ := by
    have hh := hb.2.1 v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * r ^ 2)
    have hl : (9 / 5 : ℝ) * r ^ 2 * qform (M.S b) v ≤
        2 * r ^ 2 * qform (B.cov.map (algebraMap ℚ ℝ)) v := by
      dsimp only [qform]
      nlinarith only [hm]
    exact hl.trans hτb
  let ν := fun j ↦ ProbabilityTheory.multivariateGaussian
    (WithLp.toLp 2 (M.μ j)) (M.S j)
  let margin := fun j ↦ 2 * η * Real.sqrt
    (ProbabilityTheory.variance
      (fun y ↦ (squareStatistic u).eval y.ofLp) (ν j))
  have hν (j : Fin k) : ν j = ProbabilityTheory.multivariateGaussian 0 (M.S j) := by
    simp only [ν, show M.μ j = 0 from hcenter j, WithLp.toLp_zero]
  have hmargin (j : Fin k) : margin j ≤ 4 * η * qform (M.S j) v := by
    dsimp only [margin]
    rw [hν, squareStatistic_variance u _ (hM.posDef j).posSemidef]
    have hq : 0 ≤ qform (M.S j) v := by
      simpa only [qform, star_trivial] using
        (hM.posDef j).posSemidef.dotProduct_mulVec_nonneg v
    have hs : Real.sqrt (2 * qform (M.S j) v ^ 2) ≤ 2 * qform (M.S j) v := by
      apply (Real.sqrt_le_iff).mpr
      exact ⟨by positivity, by nlinarith only [sq_nonneg (qform (M.S j) v)]⟩
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)
  obtain ⟨hea, heb⟩ := spectral_margin_bound
    (qform (M.S a) v) (qform (M.S b) v) τ r η (margin a) (margin b)
    hva hvb hr hη0 hηr hτa' hτb' (hmargin a) (hmargin b)
  have herror : 2 / r ≤ pairError .centered Δ := by
    have hΔ0 : (0 : ℝ) < Δ := lt_of_lt_of_le (by norm_num) hΔ
    simp only [pairError, Real.rpow_neg hΔ0.le]
    dsimp only [r]
    rw [div_div_eq_mul_div, div_eq_mul_inv]
    norm_num only [mul_one, one_mul]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  constructor
  · change (ν a).real {y | ¬ (spectralPair u τ).contracted (margin a) y.ofLp} ≤ _
    have hevent : {y | ¬ (spectralPair u τ).contracted (margin a) y.ofLp} =
        {y : EuclideanSpace ℝ (Fin d) | (v ⬝ᵥ y.ofLp) ^ 2 ≤ τ + margin a} := by
      ext y
      simp only [PairTest.contracted, spectralPair, Bool.false_eq_true, ↓reduceIte,
        squareStatistic_eval, not_lt, v]
    rw [hevent, hν, Population.measureReal_dotProduct_multivariateGaussian
      (hM.posDef a).posSemidef v (p := fun x : ℝ ↦ x ^ 2 ≤ τ + margin a)
      (measurableSet_le (by fun_prop) measurable_const)]
    simpa only [WithLp.ofLp_zero, dotProduct_zero, qform] using hea.trans herror
  · change (ν b).real {y | (spectralPair u τ).expanded (margin b) y.ofLp} ≤ _
    have hevent : {y | (spectralPair u τ).expanded (margin b) y.ofLp} =
        {y : EuclideanSpace ℝ (Fin d) | τ - margin b < (v ⬝ᵥ y.ofLp) ^ 2} := by
      ext y
      simp only [PairTest.expanded, spectralPair, Bool.false_eq_true, ↓reduceIte,
        squareStatistic_eval, v]
    rw [hevent, hν, Population.measureReal_dotProduct_multivariateGaussian
      (hM.posDef b).posSemidef v (p := fun x : ℝ ↦ τ - margin b < x ^ 2)
      (measurableSet_lt measurable_const (by fun_prop))]
    simpa only [WithLp.ofLp_zero, dotProduct_zero, qform] using heb.trans herror

private theorem estimate_cov_rep {d : ℕ} (A : Robust.Estimate d) :
    RepT (estimateList A).2 A.cov := by
  intro i j
  simp [ent, estimateList, List.getD_eq_getElem?_getD]

private theorem comparison_properties {d : ℕ} (A B : Robust.Estimate d) (Δ : ℚ)
    (hA : (A.cov.map (algebraMap ℚ ℝ)).PosDef)
    (hB : (B.cov.map (algebraMap ℚ ℝ)).PosDef)
    (hΔ : (2 : ℝ) ^ 40 ≤ Δ) :
    let C := comparisonL d Δ (estimateList A).2 (estimateList B).2
    (SoS.PDTestRat.test C = none → LE (A.cov.map (algebraMap ℚ ℝ))
      ((2 * ((Δ : ℝ) ^ (1 / 8 : ℝ)) ^ 4) • B.cov.map (algebraMap ℚ ℝ))) ∧
    ∀ z, SoS.PDTestRat.test C = some z →
      PairSpec .centered Δ A B
        (testOf d (spectralL d Δ (estimateList B).2 z false)) := by
  let C := comparisonL d Δ (estimateList A).2 (estimateList B).2
  let EA := A.cov.map (algebraMap ℚ ℝ)
  let EB := B.cov.map (algebraMap ℚ ℝ)
  let s : ℝ := testScale Δ
  let r := (Δ : ℝ) ^ (1 / 8 : ℝ)
  let D := (2 * s ^ 2) • EB - EA
  have hAt : EAᵀ = EA := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hA.1
  have hBt : EBᵀ = EB := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hB.1
  have hDt : Dᵀ = D := by simp only [D, transpose_sub, transpose_smul, hAt, hBt]
  have hentry (i j : Fin d) : D i j = SoS.PDTestRat.entry C i j := by
    have he : ent C i j = 2 * testScale Δ ^ 2 * B.cov i j - A.cov i j := by
      change matrixOf d C i j = _
      rw [show matrixOf d C = _ from decode_table d _]
      change 2 * testScale Δ ^ 2 * ent (estimateList B).2 i j -
        ent (estimateList A).2 i j = _
      rw [estimate_cov_rep B i j, estimate_cov_rep A i j]
    change D i j = (ent C i j : ℝ)
    rw [he]
    simp only [D, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, EA, EB,
      map_apply, s, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, eq_ratCast]
  obtain ⟨hnone, hsome⟩ := SoS.PDTestRat.test_spec C
    (by simp [C, comparisonL, RoundProgram.table]) D hentry hDt
  obtain ⟨hslo, hshi⟩ := testScale_bounds Δ hΔ
  have hs0 : 0 ≤ s := by
    change 0 ≤ (SoS.Loop.sqrtP 0 (SoS.Loop.sqrtP 0 Δ) : ℝ)
    exact_mod_cast FrameAux.sqrtP_nonneg 0 (SoS.Loop.sqrtP 0 Δ)
  have hs2 : s ^ 2 ≤ r ^ 4 := by
    have hh := pow_le_pow_left₀ hs0 hshi 2
    nlinarith only [hh]
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by linarith only [hΔ]) _
  constructor
  · intro hn v
    by_cases hv : v = 0
    · simp [hv, qform]
    have hh := hnone hn v hv
    simp only [D, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul] at hh
    have hb0 : 0 ≤ qform EB v := by
      simpa only [qform, star_trivial] using hB.posSemidef.dotProduct_mulVec_nonneg v
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs2 (by norm_num : (0 : ℝ) ≤ 2)) hb0
    change qform EA v ≤ qform ((2 * r ^ 4) • EB) v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at hm ⊢
    linarith only [hh, hm]
  · intro z hz
    obtain ⟨v, hzv, hv, hq⟩ := hsome z hz
    let u : Fin d → ℚ := fun i ↦ v i
    have hu : u ≠ 0 := by
      intro hu
      apply hv
      ext i
      have hi := congrFun hu i
      change (v i : ℚ) = 0 at hi
      exact_mod_cast hi
    have hvec : vectorOf d (z.map (Int.cast : ℤ → ℚ)) = u := by
      rw [hzv, List.map_ofFn]
      exact vector_roundtrip u
    let τ := 2 * testScale Δ * quadL d (estimateList B).2 (z.map (Int.cast : ℤ → ℚ))
    have hτ : (τ : ℝ) = 2 * s * qform EB (fun i ↦ (u i : ℝ)) := by
      have hquad := quadL_eq (estimate_cov_rep B) (fun i ↦ congrFun hvec i)
      simp only [τ, Rat.cast_mul, Rat.cast_ofNat, hquad, FrameAux.Linear.quad,
        qform, dotProduct, mulVec, Rat.cast_sum, EB, s, map_apply, eq_ratCast]
    rw [decode_spectral, hvec]
    change PairSpec .centered Δ A B (spectralPair u τ)
    apply approximate_spectral_spec A B Δ u τ hu
    · rw [hτ]
      have hb0 : 0 ≤ qform EB (fun i ↦ (u i : ℝ)) := by
        simpa only [qform, star_trivial] using
          hB.posSemidef.dotProduct_mulVec_nonneg (fun i ↦ (u i : ℝ))
      have hh := mul_le_mul_of_nonneg_right hslo hb0
      change 2 * (r / 2) ^ 2 * qform EB (fun i ↦ (u i : ℝ)) ≤ _
      nlinarith only [hh]
    · rw [hτ]
      have hcast : (fun i ↦ (u i : ℝ)) = fun i ↦ (v i : ℝ) := by
        ext i
        simp only [u, Rat.cast_intCast]
      rw [hcast]
      simp only [D, sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
        smul_eq_mul] at hq
      have hb0 : 0 ≤ qform EB (fun i ↦ (v i : ℝ)) := by
        simpa only [qform, star_trivial] using
          hB.posSemidef.dotProduct_mulVec_nonneg (fun i ↦ (v i : ℝ))
      have hm := mul_le_mul_of_nonneg_left hslo (by positivity :
        0 ≤ 2 * s * qform EB (fun i ↦ (v i : ℝ)))
      change (2 * s * qform EB (fun i ↦ (v i : ℝ))) * (r / 2) ^ 2 ≤ _
      dsimp only [qform] at hm ⊢
      nlinarith only [hq, hm]

private theorem rawTestL_spec : TestSpec (fun {d} mode Δ A B _ ↦
    testOf d (rawTestL mode d Δ (estimateList A) (estimateList B))) := by
  intro k d mode M a b A B Δ fuel hM hc hs hab ha hb hΔ w η hw hweights hη0 hη
  have hp : PairSpec mode Δ A B
      (testOf d (rawTestL mode d Δ (estimateList A) (estimateList B))) := by
    cases mode with
    | identical =>
      have ht : testOf d (rawTestL .identical d Δ (estimateList A) (estimateList B)) =
          meanTest A B := by
        rw [rawTestL, decode_mean, estimate_roundtrip, estimate_roundtrip]
      rw [ht]
      intro k'
      exact meanTest_spec A B Δ
    | centered =>
      obtain ⟨hnA, hsA⟩ := comparison_properties A B Δ ha.1 hb.1 hΔ
      obtain ⟨hnB, hsB⟩ := comparison_properties B A Δ hb.1 ha.1 hΔ
      cases hAB : SoS.PDTestRat.test
          (comparisonL d Δ (estimateList A).2 (estimateList B).2) with
      | some z =>
        have ht : testOf d (rawTestL .centered d Δ (estimateList A) (estimateList B)) =
            testOf d (spectralL d Δ (estimateList B).2 z false) := by
          rw [rawTestL, hAB, Option.elim_some]
        rw [ht]
        intro k'
        exact hsA z hAB
      | none =>
        cases hBA : SoS.PDTestRat.test
            (comparisonL d Δ (estimateList B).2 (estimateList A).2) with
        | some z =>
          have ht : testOf d (rawTestL .centered d Δ (estimateList A) (estimateList B)) =
              (testOf d (spectralL d Δ (estimateList A).2 z false)).flip := by
            simp only [rawTestL, hAB, hBA, Option.elim_none, Option.elim_some,
              decode_spectral, PairTest.flip, Bool.not_false]
          rw [ht]
          intro k'
          exact PairSpec.flip (hsB z hBA)
        | none =>
          let Q := PairwiseAux.differenceMatrix A.cov B.cov
          obtain ⟨hQt, hgap, hvariance⟩ :=
            PairwiseAux.differenceMatrix_properties A.cov B.cov ha.1 hb.1
          obtain ⟨hr, hr8⟩ := eighth_root_bounds Δ hΔ
          have hsize : let R := Q.map (algebraMap ℚ ℝ)
              let E := A.cov.map (algebraMap ℚ ℝ) + B.cov.map (algebraMap ℚ ℝ)
              2 * (Δ : ℝ) ^ (1 / 8 : ℝ) ≤ (R * E * R * E).trace := by
            dsimp only [Q]
            rw [hvariance]
            apply PairwiseAux.large_normalized_difference
              (A.cov.map (algebraMap ℚ ℝ)) (B.cov.map (algebraMap ℚ ℝ))
              (M.S a) (M.S b) ha.1 hb.1 (hM.posDef a) (hM.posDef b)
              ha.2.1 ha.2.2.1 hb.2.1 hb.2.2.1 ha.2.2.2.1 hb.2.2.2.1 _ hr
              ?_ (hnA hAB) (hnB hBA)
            rw [hr8]
            exact hs a b hab
          have ht : testOf d (rawTestL .centered d Δ (estimateList A) (estimateList B)) =
              quadraticPair A B Q := by
            rw [rawTestL, hAB, Option.elim_none, hBA, Option.elim_none, decode_quadratic]
            rw [estimate_roundtrip, estimate_roundtrip]
            simp only [estimateList, matrix_roundtrip, Q]
          rw [ht]
          intro k'
          exact quadraticPair_spec A B Δ Q hQt hgap hsize
  exact hp M a b hM hc hs hab ha hb hΔ w η hw hweights hη0 hη

/-- Rational linear algebra realizes all three pairwise test types. -/
theorem exists_test_code : ∃ T : TestCode, TestSpecL T := by
  let T : TestCode :=
    { tests := fun {d} mode Δ A B _ ↦
        testOf d (rawTestL mode d Δ (estimateList A) (estimateList B))
      run := fun mode a ↦ canonicalTestL a.1.1
        (rawTestL mode a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2) }
  refine ⟨T, rawTestL_spec, ?_, ?_⟩
  · intro mode
    exact canonicalTestL_polytime (by fun_prop) (rawTestL_polytime mode)
  · intro d mode Δ A B fuel
    exact canonicalTestL_eq d _

def firstL (d : ℕ) (T : TestL) (x : Vector) : Bool :=
  if evalL d T.1 x ≤ T.2.1 then T.2.2 else !T.2.2

def winsL (d : ℕ) (tests : List (List TestL)) (a b : ℕ) (x : Vector) : Bool :=
  let fallback : TestL := (([], [], 0), 0, false)
  if a < b then firstL d ((tests.getD a []).getD b fallback) x
  else if b < a then !firstL d ((tests.getD b []).getD a fallback) x else true

def labelL (d k : ℕ) (tests : List (List TestL)) (x : Vector) : ℕ :=
  ((List.range k).find? fun a ↦ (List.range k).all fun b ↦ winsL d tests a b x).getD 0

def reclusterL (d k : ℕ) (tests : List (List TestL)) (pts : Points) : Output :=
  pts.map (labelL d k tests)

/-- The rational quadratic evaluation agrees with the typed finite sums. -/
theorem eval_agrees {d : ℕ} (q : Statistic d) (x : Fin d → ℚ) :
    evalL d (statisticList q) (List.ofFn x) = q.evalQ x := by
  have hr (f : ℕ → ℚ) : ((List.range d).map f).sum = ∑ i : Fin d, f i.val := by
    rw [Fin.sum_univ_eq_sum_range f d, ← List.toFinset_range d]
    simpa using (List.sum_toFinset f (List.nodup_range (n := d))).symm
  simp only [evalL]
  simp_rw [hr]
  simp [statisticList, List.getD_eq_getElem?_getD, Statistic.evalQ,
    dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem eval_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {q : α → StatisticL} {x : α → Vector}
    (hd : ComputableInPolyTime d enc encUnary)
    (hq : ComputableInPolyTime q enc encStatistic)
    (hx : ComputableInPolyTime x enc encVector) :
    ComputableInPolyTime (fun a ↦ evalL (d a) (q a) (x a)) enc encRat := by
  unfold evalL
  apply rat_add' (rat_add' ?_ ?_) (by fun_prop)
  · apply rat_sum'
    apply mapWithInput (range.comp hd)
    apply rat_sum'
    apply mapWithInput (range.comp (hd.comp (fst _ _)))
    fun_prop
  · apply rat_sum'
    apply mapWithInput (range.comp hd)
    fun_prop

private theorem first_polytime {α : Type} {enc : α ↪ List Bool}
    {d : α → ℕ} {T : α → TestL} {x : α → Vector}
    (hd : ComputableInPolyTime d enc encUnary)
    (hT : ComputableInPolyTime T enc encTest)
    (hx : ComputableInPolyTime x enc encVector) :
    ComputableInPolyTime (fun a ↦ firstL (d a) (T a) (x a)) enc encBool := by
  unfold firstL
  apply ite_prop
  · exact rat_le' (eval_polytime hd (by fun_prop) hx) (by fun_prop)
  · fun_prop
  · fun_prop

private theorem wins_polytime {α : Type} {enc : α ↪ List Bool}
    {d a b : α → ℕ} {tests : α → List (List TestL)} {x : α → Vector}
    (hd : ComputableInPolyTime d enc encUnary)
    (ha : ComputableInPolyTime a enc encUnary)
    (hb : ComputableInPolyTime b enc encUnary)
    (ht : ComputableInPolyTime tests enc (encList (encList encTest)))
    (hx : ComputableInPolyTime x enc encVector) :
    ComputableInPolyTime (fun p ↦ winsL (d p) (tests p) (a p) (b p) (x p))
      enc encBool := by
  unfold winsL
  apply ite_prop (by fun_prop)
  · exact first_polytime hd (by fun_prop) hx
  · apply ite_prop (by fun_prop)
    · exact bool_not.comp (first_polytime hd (by fun_prop) hx)
    · exact const true

private theorem label_polytime {α : Type} {enc : α ↪ List Bool}
    {d k : α → ℕ} {tests : α → List (List TestL)} {x : α → Vector}
    (hd : ComputableInPolyTime d enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (ht : ComputableInPolyTime tests enc (encList (encList encTest)))
    (hx : ComputableInPolyTime x enc encVector) :
    ComputableInPolyTime (fun p ↦ labelL (d p) (k p) (tests p) (x p))
      enc encUnary := by
  unfold labelL
  apply optionGetDWithInput ?_ (const 0)
  apply findWithInput (range.comp hk)
  apply ComputableInPolyTime.of_tidy
  apply ComputableTidilyInPolyTime.allWithInput
    (range.comp (hk.comp (fst _ _))).tidy
  exact (wins_polytime (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)).tidy

/-- Least-winner comparison and output writing have an absolute polynomial cost. -/
theorem recluster_polytime : ComputableInPolyTime
    (fun q : (ℕ × ℕ × List (List TestL)) × Points ↦ reclusterL q.1.1 q.1.2.1 q.1.2.2 q.2)
    (encPair (encPair encUnary (encPair encUnary (encList (encList encTest)))) encPoints)
    encOutput := by
  unfold reclusterL
  apply mapWithInput (by fun_prop)
  apply unary_to_binary.comp
  exact label_polytime (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

theorem recluster_agrees {n k d : ℕ} (tests : Fin k → Fin k → PairTest d)
    (x : Fin n → Fin d → ℚ) :
    reclusterL d k (List.ofFn fun a ↦ List.ofFn fun b ↦ testList (tests a b)) (pointsOf x) =
      recluster tests x := by
  let ts := List.ofFn fun a ↦ List.ofFn fun b ↦ testList (tests a b)
  have hfirst (T : PairTest d) (v : Fin d → ℚ) :
      firstL d (testList T) (List.ofFn v) = T.first v := by
    simp only [firstL, testList, eval_agrees, PairTest.first]
  have hw (a b : Fin k) (v : Fin d → ℚ) :
      winsL d ts a.val b.val (List.ofFn v) = wins tests a b v := by
    simp [ts, winsL, wins, List.getD_eq_getElem?_getD, hfirst]
  have hl (v : Fin d → ℚ) : labelL d k ts (List.ofFn v) = label tests v := by
    simp only [labelL, label, ← List.map_coe_finRange_eq_range (n := k),
      List.find?_map, List.all_map, Function.comp_def, hw]
  simp only [reclusterL, pointsOf, List.map_ofFn, recluster]
  congr 1
  funext l
  exact hl (x l)


end ABBKS26.Assembly.Exec
