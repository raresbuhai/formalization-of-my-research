module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobGuard

/-! Bounded dyadic replacements for pure quadratic certificates. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobRound

open Common _root_.ABBKS26.Tree Matrix
open Sources Builders
open Turing.MultiTapeTM ComputableInPolyTime
open scoped BigOperators

/-- Round after contraction, and bound the result on arbitrary rational inputs. -/
def entry (p b : ℕ) (s a : ℚ) : ℚ :=
  SoS.Loop.clamp (2 ^ b) (roundRat p (s * a))

theorem entry_small (p b : ℕ) (s a : ℚ) : SoS.PolyTime.Small p b (entry p b s a) := by
  have he : roundRat p (s * a) = SoS.Loop.roundP p (s * a) := by
    unfold roundRat SoS.Loop.roundP
    rw [mul_comm]
  rw [entry, he]
  exact SoS.PolyTime.small_clamp_roundP p b (s * a)

theorem entry_bits (p b : ℕ) (s a : ℚ) :
    (Encoding.encRat (entry p b s a)).length ≤ 3 * (b + p) + 6 :=
  SoS.PolyTime.length_encRat_le_of_small (entry_small p b s a)

private theorem clamp_error {B a z e : ℚ} (ha : |a| ≤ B) (he : |z - a| ≤ e) :
    |SoS.Loop.clamp B z - a| ≤ e := by
  rw [abs_le] at ha he ⊢
  unfold SoS.Loop.clamp
  constructor
  · have hz := le_max_right (-B) (min B z)
    have hm : a - e ≤ min B z := le_min (by linarith only [ha.2, he.1, he.2])
      (by linarith only [he.1])
    linarith only [hz, hm]
  · exact sub_le_iff_le_add.mpr (max_le (by linarith only [ha.1, he.1, he.2])
      ((min_le_right B z).trans (by linarith only [he.2])))

/-- Clamping does not increase the rounding error when the contracted entry fits. -/
theorem entry_error (p b : ℕ) (s a : ℚ) (ha : |s * a| ≤ 2 ^ b) :
    |entry p b s a - s * a| ≤ 1 / (2 : ℚ) ^ p := by
  apply clamp_error ha
  rw [abs_sub_comm, abs_of_nonneg (FrameAux.roundRat_error p (s * a)).1]
  exact (FrameAux.roundRat_error p (s * a)).2.le

theorem entry_polytime {α : Type} {input : α ↪ List Bool}
    {p b : α → ℕ} {s a : α → ℚ}
    (hp : ComputableInPolyTime p input encUnary)
    (hb : ComputableInPolyTime b input encUnary)
    (hs : ComputableInPolyTime s input Encoding.encRat)
    (ha : ComputableInPolyTime a input Encoding.encRat) :
    ComputableInPolyTime (fun x ↦ entry (p x) (b x) (s x) (a x))
      input Encoding.encRat := by
  unfold entry
  exact SoS.PolyTime.clamp' (rat_two_pow' hb)
    (FrameAux.roundRat_polytime hp (rat_mul' hs ha))

/-- Affine coefficients are discarded; the same scalar map is used in both matrix positions. -/
def rounded {d : ℕ} (p b : ℕ) (s : ℚ) (q : Statistic d) : Statistic d :=
  ⟨fun i j ↦ entry p b s (q.A i j), 0, 0⟩

def roundedL (d p b : ℕ) (s : ℚ) (q : StatisticL) : StatisticL :=
  (FrameAux.Features.table d d (fun i j ↦ entry p b s ((q.1.getD i []).getD j 0)),
    List.replicate d 0, 0)

theorem roundedL_agrees (d p b : ℕ) (s : ℚ) (q : StatisticL) :
    roundedL d p b s q = statisticList (rounded p b s (statisticOf d q)) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [roundedL, statisticList, FrameAux.Features.table]
    · intro i hi hi'
      simp only [roundedL, statisticList, FrameAux.Features.table, List.getElem_map,
        List.getElem_range, List.getElem_ofFn]
      apply List.ext_getElem
      · simp
      · intro j hj hj'
        simp [rounded, statisticOf, matrixOf]
  · apply Prod.ext
    · change List.replicate d 0 = List.ofFn (fun _ : Fin d ↦ (0 : ℚ))
      simp
    · rfl

theorem rounded_symmetric {d : ℕ} (p b : ℕ) (s : ℚ) (q : Statistic d)
    (hq : q.Aᵀ = q.A) : (rounded p b s q).Aᵀ = (rounded p b s q).A := by
  ext i j
  exact congrArg (entry p b s) (congrFun (congrFun hq i) j)

theorem roundedL_polytime {α : Type} {input : α ↪ List Bool}
    {d p b : α → ℕ} {s : α → ℚ} {q : α → StatisticL}
    (hd : ComputableInPolyTime d input encUnary)
    (hp : ComputableInPolyTime p input encUnary)
    (hb : ComputableInPolyTime b input encUnary)
    (hs : ComputableInPolyTime s input Encoding.encRat)
    (hq : ComputableInPolyTime q input encStatistic) :
    ComputableInPolyTime (fun x ↦ roundedL (d x) (p x) (b x) (s x) (q x))
      input encStatistic := by
  unfold roundedL
  apply ComputableInPolyTime.prod
  · apply FrameAux.Features.table_polytime hd hd
    have hbase := (fst input encUnary).comp (fst _ encUnary)
    exact entry_polytime (hp.comp hbase) (hb.comp hbase) (hs.comp hbase) (by fun_prop)
  · exact (replicate hd (const 0)).prod (const 0)

private theorem vector_bits (xs : Vector) (B : ℕ)
    (h : ∀ a ∈ xs, (Encoding.encRat a).length ≤ B) :
    (encVector xs).length ≤ xs.length * (2 * B + 1) := by
  induction xs with
  | nil => simp [encVector]
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have hx := ih (fun z hz ↦ h z (List.mem_cons_of_mem _ hz))
    simp only [encVector, length_encList, List.map_cons, List.sum_cons] at *
    simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- A uniform bit bound, including matrix/vector framing, independent of the input coefficients. -/
theorem roundedL_bits (d p b : ℕ) (s : ℚ) (q : StatisticL) :
    (encStatistic (roundedL d p b s q)).length ≤
      2 * (d * (2 * (d * (6 * (b + p) + 13)) + 1)) +
        2 * (d * (2 * (Encoding.encRat 0).length + 1)) +
          (Encoding.encRat 0).length + 2 := by
  have hrow (i : ℕ) : (encVector ((List.range d).map fun j ↦
      entry p b s ((q.1.getD i []).getD j 0))).length ≤ d * (6 * (b + p) + 13) := by
    apply (vector_bits _ (3 * (b + p) + 6) ?_).trans_eq
    · simp only [List.length_map, List.length_range]
      ring
    · intro a ha
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
      exact entry_bits p b s _
  have hmat : (encMatrix (roundedL d p b s q).1).length ≤
      d * (2 * (d * (6 * (b + p) + 13)) + 1) := by
    simp only [roundedL, FrameAux.Features.table, encMatrix, length_encList]
    calc
      _ ≤ ((List.range d).map fun _ ↦
          2 * (d * (6 * (b + p) + 13)) + 1).sum := by
        simp only [List.map_map]
        apply List.sum_le_sum
        intro i hi
        simpa only [encVector, length_encList, Function.comp_apply] using
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hrow i)) 1
      _ = _ := by simp
  have hv : (encVector (List.replicate d 0)).length ≤
      d * (2 * (Encoding.encRat 0).length + 1) := by
    apply (vector_bits _ (Encoding.encRat 0).length ?_).trans_eq
    · rw [List.length_replicate]
    · intro a ha
      have he : a = 0 := (List.mem_replicate.mp ha).2
      rw [he]
  change (encPair encMatrix (encPair encVector Encoding.encRat)
    (roundedL d p b s q)).length ≤ _
  rw [length_encPair, length_encPair]
  change 2 * (encMatrix (roundedL d p b s q).1).length + 1 +
    (2 * (encVector (List.replicate d 0)).length + 1 + (Encoding.encRat 0).length) ≤ _
  omega

theorem roundedL_bits_envelope (d p b z : ℕ) (s : ℚ) (q : StatisticL)
    (hz : 2 ≤ z) (hd : d ≤ z) (hpb : b + p + 1 ≤ z ^ 4) :
    (encStatistic (roundedL d p b s q)).length ≤ 200 * z ^ 6 := by
  have hzero : (Encoding.encRat 0).length ≤ 6 := by
    simpa using SoS.PolyTime.length_encRat_le_of_small (SoS.PolyTime.small_zero 0 0)
  have hZ : 1 ≤ z ^ 4 := one_le_pow₀ (by omega)
  have hcoeff : 6 * (b + p) + 13 ≤ 19 * z ^ 4 := by omega
  have hsimple : (encStatistic (roundedL d p b s q)).length ≤
      4 * d ^ 2 * (6 * (b + p) + 13) + 28 * d + 8 := by
    have hb := roundedL_bits d p b s q
    nlinarith only [hb, hzero, Nat.mul_le_mul_left (4 * d) hzero]
  have hz6 : 1 ≤ z ^ 6 := one_le_pow₀ (by omega)
  have hz16 : z ≤ z ^ 6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ z) (by norm_num : 1 ≤ 6)
  calc
    _ ≤ 4 * d ^ 2 * (6 * (b + p) + 13) + 28 * d + 8 := hsimple
    _ ≤ 4 * z ^ 2 * (19 * z ^ 4) + 28 * z + 8 := by gcongr
    _ = 76 * z ^ 6 + 28 * z + 8 := by ring
    _ ≤ 200 * z ^ 6 := by omega

theorem frobSq_le_of_entries {d : ℕ} (A : Mat d) (e : ℝ) (he : 0 ≤ e)
    (hA : ∀ i j, |A i j| ≤ e) : frobSq A ≤ (d : ℝ) ^ 2 * e ^ 2 := by
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, e ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr (hA i j)
    _ = _ := by simp; ring

private theorem trace_quadratic_nonneg {d : ℕ} (A S : Mat d) (hA : Aᵀ = A)
    (hS : S.PosSemidef) : 0 ≤ (A * S * A * S).trace := by
  have hASA : (A * S * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      hS.mul_mul_conjTranspose_same A
  exact Separation.trace_mul_nonneg hASA hS

/-- The Gaussian quadratic-variance form is convex on symmetric matrices. -/
theorem trace_quadratic_convex {d : ℕ} (A C S : Mat d)
    (hA : Aᵀ = A) (hC : Cᵀ = C) (hS : S.PosSemidef)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ((s • A + (1 - s) • C) * S * (s • A + (1 - s) • C) * S).trace ≤
      s * (A * S * A * S).trace + (1 - s) * (C * S * C * S).trace := by
  have hsym : (A - C)ᵀ = A - C := by rw [transpose_sub, hA, hC]
  have h := mul_nonneg (mul_nonneg hs (sub_nonneg.mpr hs1))
    (trace_quadratic_nonneg (A - C) S hsym hS)
  simp only [sub_mul, mul_sub, trace_sub] at h
  simp only [add_mul, mul_add, smul_mul, Matrix.mul_smul, smul_smul, trace_add,
    trace_smul, smul_eq_mul]
  nlinarith only [h]

private theorem real_symmetric {d : ℕ} (q : Statistic d) (hq : q.Aᵀ = q.A) :
    (q.A.map (algebraMap ℚ ℝ))ᵀ = q.A.map (algebraMap ℚ ℝ) := by
  rw [← transpose_map, hq]

private theorem pure_variance {d : ℕ} (q : Statistic d) (hq : q.Aᵀ = q.A)
    (S : Mat d) (hS : S.PosSemidef) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) =
        2 * (q.A.map (algebraMap ℚ ℝ) * S * q.A.map (algebraMap ℚ ℝ) * S).trace := by
  rw [Variance.centered_variance_eq _ (FrobPure.pure_symmetric q hq) S hS]
  simp [FrobPure.pure, qform]

/-- Contraction creates enough variance slack for a Frobenius-bounded perturbation.
The conclusion concerns actual Gaussian variance, with no empirical variance surrogate. -/
theorem variance_of_frob_error {d : ℕ} (q q' : Statistic d)
    (hq : q.Aᵀ = q.A) (hq' : q'.Aᵀ = q'.A) (S : Mat d) (hS : S.PosSemidef)
    (s c e B : ℝ) (hs : 0 ≤ s) (hs1 : s < 1) (hc : 0 ≤ c)
    (hupper : ∀ v, qform S v ≤ c * sqnorm v)
    (hv : ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤ B ^ 2)
    (he : frobSq (q'.A.map (algebraMap ℚ ℝ) - s • q.A.map (algebraMap ℚ ℝ)) ≤ e ^ 2)
    (hprec : 2 * c ^ 2 * e ^ 2 ≤ (1 - s) ^ 2 * B ^ 2) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q').eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤ B ^ 2 := by
  let A := q.A.map (algebraMap ℚ ℝ)
  let A' := q'.A.map (algebraMap ℚ ℝ)
  let E := A' - s • A
  let C := (1 - s)⁻¹ • E
  have ht : 0 < 1 - s := sub_pos.mpr hs1
  have hA : Aᵀ = A := real_symmetric q hq
  have hA' : A'ᵀ = A' := real_symmetric q' hq'
  have hE : Eᵀ = E := by simp only [E, transpose_sub, transpose_smul, hA, hA']
  have hC : Cᵀ = C := by simp only [C, transpose_smul, hE]
  have htf : (E * S * E * S).trace ≤ c ^ 2 * e ^ 2 :=
    (Robust.FilterAux.trace_quadratic_le E S hE hS c hc hupper).trans
      (mul_le_mul_of_nonneg_left he (sq_nonneg c))
  have hCbound : 2 * (C * S * C * S).trace ≤ B ^ 2 := by
    have hscale : (C * S * C * S).trace = (1 - s)⁻¹ ^ 2 * (E * S * E * S).trace := by
      simp only [C, smul_mul, Matrix.mul_smul, smul_smul, trace_smul, smul_eq_mul,
        pow_two]
    calc
      _ = (2 * (E * S * E * S).trace) / (1 - s) ^ 2 := by
        rw [hscale, div_eq_mul_inv, inv_pow]
        ring
      _ ≤ B ^ 2 := (div_le_iff₀ (sq_pos_of_pos ht)).mpr (by nlinarith only [htf, hprec])
  have hdecomp : s • A + (1 - s) • C = A' := by
    dsimp only [C]
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    exact add_sub_cancel _ _
  have hconv := trace_quadratic_convex A C S hA hC hS s hs hs1.le
  rw [hdecomp] at hconv
  rw [pure_variance q hq S hS] at hv
  rw [pure_variance q' hq' S hS]
  have hleft := mul_le_mul_of_nonneg_left hv hs
  have hright := mul_le_mul_of_nonneg_left hCbound ht.le
  change 2 * (A' * S * A' * S).trace ≤ _
  nlinarith only [hconv, hleft, hright]

theorem rounded_error {d : ℕ} (p b : ℕ) (s : ℚ) (q : Statistic d)
    (hmag : ∀ i j, |s * q.A i j| ≤ 2 ^ b) :
    frobSq ((rounded p b s q).A.map (algebraMap ℚ ℝ) -
      (s : ℝ) • q.A.map (algebraMap ℚ ℝ)) ≤
        ((d : ℝ) * (1 / (2 : ℝ) ^ p)) ^ 2 := by
  apply (frobSq_le_of_entries _ (1 / (2 : ℝ) ^ p) (by positivity) ?_).trans_eq
  · ring
  · intro i j
    change |(entry p b s (q.A i j) : ℝ) - (s : ℝ) * (q.A i j : ℝ)| ≤ _
    have h := (Rat.cast_le (K := ℝ)).mpr (entry_error p b s (q.A i j) (hmag i j))
    push_cast at h
    exact h

/-- Actual Gaussian validity for bounded, rounded pure certificates. The precision condition
pays for rounding after contraction; clamping also bounds coefficients on junk inputs. -/
theorem rounded_variance {d : ℕ} (p b : ℕ) (s : ℚ) (q : Statistic d)
    (hq : q.Aᵀ = q.A) (S : Mat d) (hS : S.PosSemidef)
    (c B : ℝ) (hs : 0 ≤ (s : ℝ)) (hs1 : (s : ℝ) < 1) (hc : 0 ≤ c)
    (hupper : ∀ v, qform S v ≤ c * sqnorm v)
    (hv : ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤ B ^ 2)
    (hmag : ∀ i j, |s * q.A i j| ≤ 2 ^ b)
    (hprec : 2 * c ^ 2 * ((d : ℝ) * (1 / (2 : ℝ) ^ p)) ^ 2 ≤
      (1 - (s : ℝ)) ^ 2 * B ^ 2) :
    ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (rounded p b s q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤ B ^ 2 := by
  exact variance_of_frob_error q (rounded p b s q) hq (rounded_symmetric p b s q hq)
    S hS s c _ B hs hs1 hc hupper hv (rounded_error p b s q hmag) hprec

/-- Entrywise perturbations give a dimension-explicit error for a component center. -/
theorem trace_error {d : ℕ} (E S : Mat d) (e C : ℝ) (he : 0 ≤ e)
    (hE : ∀ i j, |E i j| ≤ e) (hS : ∀ i j, |S i j| ≤ C) :
    |(E * S).trace| ≤ (d : ℝ) ^ 2 * e * C := by
  calc
    _ = |∑ i : Fin d, ∑ j : Fin d, E i j * S j i| := rfl
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, |E i j * S j i| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, e * C := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hE i j) (hS j i) (abs_nonneg _) he
    _ = _ := by simp; ring

theorem rounded_center_error {d : ℕ} (p b : ℕ) (s : ℚ) (q : Statistic d)
    (S : Mat d) (C : ℝ)
    (hmag : ∀ i j, |s * q.A i j| ≤ 2 ^ b) (hS : ∀ i j, |S i j| ≤ C) :
    |((rounded p b s q).A.map (algebraMap ℚ ℝ) * S).trace -
      (s : ℝ) * (q.A.map (algebraMap ℚ ℝ) * S).trace| ≤
        (d : ℝ) ^ 2 * (1 / (2 : ℝ) ^ p) * C := by
  have hE (i j : Fin d) :
      |((rounded p b s q).A.map (algebraMap ℚ ℝ) -
        (s : ℝ) • q.A.map (algebraMap ℚ ℝ)) i j| ≤ 1 / (2 : ℝ) ^ p := by
    change |(entry p b s (q.A i j) : ℝ) - (s : ℝ) * (q.A i j : ℝ)| ≤ _
    have h := (Rat.cast_le (K := ℝ)).mpr (entry_error p b s (q.A i j) (hmag i j))
    push_cast at h
    exact h
  simpa only [sub_mul, smul_mul, trace_sub, trace_smul, smul_eq_mul] using
    trace_error _ S _ C (by positivity) hE hS

/-- The coefficient cap is checked before rounding, so accepted entries have a proved error. -/
def magFits (d b : ℕ) (s : ℚ) (q : StatisticL) : Bool :=
  (List.range d).all fun i ↦ (List.range d).all fun j ↦
    decide (|s * (q.1.getD i []).getD j 0| ≤ 2 ^ b)

theorem magFits_iff (d b : ℕ) (s : ℚ) (q : StatisticL) :
    magFits d b s q = true ↔ ∀ i j, |s * (statisticOf d q).A i j| ≤ 2 ^ b := by
  simp only [magFits, List.all_eq_true, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h i j
    exact h i i.isLt j j.isLt
  · intro h i hi j hj
    exact h ⟨i, hi⟩ ⟨j, hj⟩

theorem magFits_polytime {α : Type} {input : α ↪ List Bool}
    {d b : α → ℕ} {s : α → ℚ} {q : α → StatisticL}
    (hd : ComputableInPolyTime d input encUnary)
    (hb : ComputableInPolyTime b input encUnary)
    (hs : ComputableInPolyTime s input Encoding.encRat)
    (hq : ComputableInPolyTime q input encStatistic) :
    ComputableInPolyTime (fun x ↦ magFits (d x) (b x) (s x) (q x)) input encBool := by
  unfold magFits
  apply allWithInput (range.comp hd)
  apply allWithInput ((range.comp hd).comp (fst _ _))
  have hbase := (fst input encUnary).comp (fst _ encUnary)
  exact rat_le' (rat_abs' (rat_mul' (hs.comp hbase) (by fun_prop)))
    (rat_two_pow' (hb.comp hbase))

/-- Original eligibility flags remain paired with the rounded replacements. Only entries
whose contraction fits the magnitude cap are sent to the replacement map. -/
def run (F : FrameCode) (p b : Args → ℕ) (s : Args → ℚ) (a : Args) : PoolL :=
  ((FrobPure.run F a).filter fun q ↦ magFits a.1.1 (b a) (s a) q.1).map fun q ↦
    (roundedL a.1.1 (p a) (b a) (s a) q.1, q.2)

theorem run_polytime (F : FrameCode) (hF : FrameSpec F)
    (p b : Args → ℕ) (s : Args → ℚ)
    (hp : ComputableInPolyTime p encArgs encUnary)
    (hb : ComputableInPolyTime b encArgs encUnary)
    (hs : ComputableInPolyTime s encArgs Encoding.encRat) :
    ComputableInPolyTime (run F p b s) encArgs encPool := by
  unfold run
  apply mapWithInput
  · apply filterWithInput (FrobPure.run_polytime F hF)
    exact magFits_polytime (by fun_prop) (hb.comp (fst _ _)) (hs.comp (fst _ _))
      (by fun_prop)
  · exact (roundedL_polytime (by fun_prop) (hp.comp (fst _ _)) (hb.comp (fst _ _))
      (hs.comp (fst _ _)) (by fun_prop)).prod (by fun_prop)

theorem pool_symmetric {n d : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (p : StepParams) (x : Fin n → Fin d → ℚ) (fuel : ℕ) (N : Finset (Fin n))
    (q : Statistic d) (hq : (q, true) ∈ FrobPure.pool F p x fuel N) : q.Aᵀ = q.A := by
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hq
  have hflag : u.2 = true := congrArg Prod.snd he
  have hstat : FrobPure.pure u.1 = q := congrArg Prod.fst he
  rw [← hstat]
  apply FrobPure.pure_symmetric
  exact FrobVariance.paired_symmetric F hF .centered
    ((d, (N.sort (· ≤ ·)).map (fun l ↦ List.ofFn (x l)), p.w / 2, |p.R|,
      p.frameAccuracy), fuel) u.1 (hflag ▸ hu)

/-- A retained replacement has an eligible original, a proved magnitude check, and the
exact rounded matrix. The all-threshold guard does not alter any of these facts. -/
theorem retained_origin {n d : ℕ} (B : Budget .centered) (F : FrameCode)
    (p b : Args → ℕ) (s : Args → ℚ) (k : ℕ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n)) (hh : h < k)
    (q : Statistic d)
    (hq : (q, true) ∈ (frobSource B (run F p b s)).pool k ps x fuel h N) :
    ∃ q₀, (q₀, true) ∈ FrobPure.pool F (ps h) x fuel N ∧
      (∀ i j, |s (args k ps x h N, fuel) * q₀.A i j| ≤
        2 ^ b (args k ps x h N, fuel)) ∧
      q = rounded (p (args k ps x h N, fuel)) (b (args k ps x h N, fuel))
        (s (args k ps x h N, fuel)) q₀ := by
  let a := (args k ps x h N, fuel)
  obtain ⟨r, hr, hdecode, _⟩ := (FrobGuard.retained_iff B (run F p b s) a q).mp hq
  obtain ⟨u, hu, he⟩ := List.mem_map.mp hr
  obtain ⟨hraw, hmag⟩ := List.mem_filter.mp hu
  have hflag : u.2 = true := congrArg Prod.snd he
  have hrstat : roundedL d (p a) (b a) (s a) u.1 = r := congrArg Prod.fst he
  change u ∈ FrobPure.run F (args k ps x h N, fuel) at hraw
  rw [FrobPure.run_agrees F k ps x fuel h N hh] at hraw
  obtain ⟨v, hv, huv⟩ := List.mem_map.mp hraw
  have huflag : v.2 = u.2 := congrArg Prod.snd huv
  have hustat : statisticList v.1 = u.1 := congrArg Prod.fst huv
  have hstat : statisticOf d u.1 = v.1 := by rw [← hustat, statistic_roundtrip]
  refine ⟨v.1, (huflag.trans hflag) ▸ hv, ?_, ?_⟩
  · have hm := (magFits_iff d (b a) (s a) u.1).mp hmag
    rwa [hstat] at hm
  · change statisticOf d r = q at hdecode
    rw [← hrstat, roundedL_agrees, statistic_roundtrip, hstat] at hdecode
    exact hdecode.symm

/-- The replacement source has genuine Gaussian validity whenever the data-derived
covariance upper bound and precision inequality hold. Magnitude is checked by the program. -/
theorem validity {n k d : ℕ} (B : Budget .centered) (F : FrameCode) (hF : FrameSpec F)
    (p b : Args → ℕ) (s : Args → ℚ) (ps : ℕ → StepParams)
    (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hprep : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card)
    (c : ℝ) (hc : 0 ≤ c)
    (hs : 0 ≤ (s (args k ps x h N, fuel) : ℝ))
    (hs1 : (s (args k ps x h N, fuel) : ℝ) < 1)
    (hupper : ∀ j ∈ I, ∀ v, qform (M.S j) v ≤ c * sqnorm v)
    (hprec : 2 * c ^ 2 * ((d : ℝ) * (1 / (2 : ℝ) ^ p (args k ps x h N, fuel))) ^ 2 ≤
      (1 - (s (args k ps x h N, fuel) : ℝ)) ^ 2 * (40 / ((ps h).w : ℝ)) ^ 2)
    (q : Statistic d)
    (hq : (q, true) ∈ (frobSource B (run F p b s)).pool k ps x fuel h N) :
    ∀ j ∈ I, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        (40 / ((ps h).w : ℝ)) ^ 2 := by
  obtain ⟨q₀, hq₀, hmag, rfl⟩ := retained_origin B F p b s k ps x fuel h N
    (by omega) q hq
  have hsym := pool_symmetric F hF (ps h) x fuel N q₀ hq₀
  have hv := FrobPure.prepared_variance F hF ps x fuel h N M ε w η Δ D ω r I hI
    hx hprep hf hh hl hN q₀ hq₀
  intro j hj
  have hvj := hv j hj
  rw [hprep.2.1 j, WithLp.toLp_zero] at hvj ⊢
  exact rounded_variance _ _ _ q₀ hsym _ (hprep.1.posDef j).posSemidef c _ hs hs1 hc
    (hupper j hj) ((FrobPure.variance_le q₀ hsym _ (hprep.1.posDef j).posSemidef).trans hvj)
    hmag hprec

end ABBKS26.Assembly.Exec.RefineSynth.FrobRound
