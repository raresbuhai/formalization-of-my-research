module

public import ABBKS26.Robust.MomentSDPAuxPopulation

/-!
# Certified moment estimation

Robust estimation of moments with sum-of-squares certificates ([ABBKS26, Fact 5.14 and
Theorem 6.11], from [KSS17]) by one semidefinite program over weights on the points.
-/

@[expose] public section

namespace ABBKS26.Robust

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {n k d : ℕ}

def empiricalMoment (s : Finset (Fin n)) (x : Fin n → Vec d) (r : ℕ) : RPoly d :=
  C (s.card : ℝ)⁻¹ * ∑ i ∈ s, lin (x i) ^ r

def populationMoment (F : FrameModel k d) (r : ℕ) : RPoly d :=
  ∑ j, C (F.weight j) * IdCov.hmom r (lin (F.mean j)) (quad (F.cov j))

def clipped (x : ℝ) : ℝ := min (max x 0) 1

def weightedMoment (w : Fin n → ℝ) (x : Fin n → Vec d) (r : ℕ) : RPoly d :=
  C (∑ i, w i)⁻¹ * ∑ i, C (w i) * lin (x i) ^ r

def momentBudget (w : ℝ) (r : ℕ) : ℝ := 2 * (20 * r / w) ^ r

def Certified (F : FrameModel k d) (M : ℕ → RPoly d) (J : Finset ℕ)
    (η : ℕ → ℝ) : Prop := ∀ r ∈ J,
  (M r).IsHomogeneous r ∧ IsSumSq (C (η r) * nsq ^ r - (M r - populationMoment F r) ^ 2)

/-- Gram blocks for the degree-two weight/moment SDP; each equality is a ± pair. -/
def momentGramOffset (n d : ℕ) (J : List ℕ) (a : ℕ) : ℕ :=
  n + ((J.take a).map fun r ↦ (Rounding.monos d r).length ^ 2).sum

def momentVars (n d : ℕ) (J : List ℕ) : ℕ := momentGramOffset n d J J.length

def momentTemplate (x : Fin n → Vec d) (J : List ℕ) (B : ℕ → ℝ)
    (a : Fin J.length) : Rounding.Template d :=
  Rounding.embedCoeff (C (B J[a] * n) * nsq ^ J[a]) -
    (∑ i : Fin n, C (X i.val : Rounding.NPoly) *
      Rounding.embedCoeff (lin (x i) ^ (2 * J[a]))) -
    Rounding.gram (momentGramOffset n d J a) (Rounding.monos d J[a])

def momentConstraints (x : Fin n → Vec d) (J : List ℕ) (B : ℕ → ℝ)
    (ε ball : ℝ) : List Rounding.NPoly :=
  [C ball - ∑ i ∈ Finset.range (momentVars n d J), X i ^ 2] ++
  (List.finRange n).flatMap (fun i ↦
    [(X i.val : Rounding.NPoly), 1 - (X i.val : Rounding.NPoly)]) ++
  [(∑ i : Fin n, X i.val) - C ((1 - ε) * n)] ++
  (List.finRange J.length).flatMap (fun a ↦
    (Rounding.monos d (2 * J[a])).flatMap fun μ ↦
      let c := (momentTemplate x J B a).coeff μ
      [c, -c])

abbrev MomentProc := {n d : ℕ} → (Fin n → Fin d → ℚ) → Finset (Fin n) →
  Finset ℕ → ℚ → ℚ → ℕ → (ℕ → QPoly d)

def MomentContract (run : MomentProc) : Prop :=
  ∀ {n k d} (D : Reference n k d) (x : Fin n → Fin d → ℚ)
    (J : Finset ℕ) (w ε : ℚ) (θ : ℝ) fuel,
    D.Valid w → (∀ l i, D.observed l i = (x l i : ℝ)) →
    (∀ j ∈ J, 1 ≤ j) →
    D.Resilient (2 * J.sup id) θ → 0 ≤ θ → θ ≤ 1 / 100000000 →
    D.contamination ≤ ε → ε ≤ 1 / 8 →
    (∀ j, sqnorm (D.model.mean j) ≤ 2 / w) →
    (∀ j, LE (D.model.cov j) ((1.1 / (w : ℝ)) • (1 : Mat d))) →
    (n + d + 2) ^ (100 * (J.sup id + 1)) ≤ fuel →
    Certified D.model
      (fun r ↦ SoS.toReal (run x D.block J w ε fuel r)) J
      (fun r ↦ 250 * ε * momentBudget w r + 3 * θ ^ 2 * momentBudget w r)

private theorem sos_nsq_pow (s : ℕ) : IsSumSq ((nsq : RPoly d) ^ s) :=
  SoS.isSumSq_pow (IsSumSq.sum_sq _ _) s

private theorem sos_budget_mono {a b : ℝ} (hab : a ≤ b) (s : ℕ) :
    IsSumSq (C b * (nsq : RPoly d) ^ s - C a * nsq ^ s) := by
  rw [← sub_mul, ← C_sub]
  exact SoS.isSumSq_C_mul (sub_nonneg.mpr hab) (sos_nsq_pow s)

private theorem sos_lin_pow (u : Vec d) (s : ℕ) :
    IsSumSq (C (sqnorm u ^ s) * nsq ^ s - lin u ^ (2 * s)) := by
  have h := SoS.isSumSq_lagrange Finset.univ (fun i ↦ C (u i)) X
  have he : (∑ i, (C (u i) : RPoly d) ^ 2) = C (sqnorm u) := by
    simp only [sqnorm, dotProduct, map_sum, map_mul, sq]
  rw [he] at h
  have hp := SoS.isSumSq_pow_sub_pow (SoS.isSumSq_sq (lin u)) h s
  simpa only [mul_pow, ← C_pow, ← pow_mul, nsq, lin] using hp

private theorem homogeneous_lin (u : Vec d) : (lin u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ ↦ (isHomogeneous_X ℝ i).C_mul (u i)


private theorem homogeneous_quad (A : Mat d) : (quad A).IsHomogeneous 2 := by
  refine IsHomogeneous.sum _ _ _ fun i _ ↦ IsHomogeneous.sum _ _ _ fun j _ ↦ ?_
  rw [mul_assoc]
  exact ((isHomogeneous_X ℝ i).mul (isHomogeneous_X ℝ j)).C_mul _

private theorem homogeneous_hmom (a : Vec d) (A : Mat d) (r : ℕ) :
    (IdCov.hmom r (lin a) (quad A)).IsHomogeneous r := by
  refine IsHomogeneous.sum _ _ _ fun i hi ↦ ?_
  have hi' : 2 * i ≤ r := by simp only [Finset.mem_range] at hi; omega
  rw [← map_natCast (C : ℝ →+* RPoly d), mul_assoc]
  convert (((homogeneous_lin a).pow (r - 2 * i)).mul
    ((homogeneous_quad A).pow i)).C_mul (IdCov.hermCoeff r i : ℝ) using 1
  omega

private theorem homogeneous_empirical (S : Finset (Fin n)) (x : Fin n → Vec d)
    (r : ℕ) : (empiricalMoment S x r).IsHomogeneous r := by
  apply IsHomogeneous.C_mul
  exact IsHomogeneous.sum _ _ _ fun i _ ↦ by simpa using (homogeneous_lin (x i)).pow r


/-- Gaussian projected moments have dimension-free SoS upper bounds. -/
theorem population_sos
    (F : FrameModel k d) (w : ℝ) (hF : F.Valid w) (r : ℕ) (hr : 1 ≤ r)
    (hm : ∀ j, sqnorm (F.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (F.cov j) ((1.1 / w) • (1 : Mat d))) :
    IsSumSq (C ((10 * r / w) ^ r) * nsq ^ r - populationMoment F (2 * r)) := by
  let A : ℝ := 2 / w
  let V : ℝ := 1.1 / w
  let K : ℝ := ∑ i ∈ Finset.range (r + 1),
    (IdCov.hermCoeff (2 * r) i : ℝ) * A ^ (r - i) * V ^ i
  have hw : 0 < w := hF.1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hlin (j : Fin k) : IsSumSq (C A * nsq - lin (F.mean j) ^ 2) := by
    have h := sos_lin_pow (F.mean j) 1
    simp only [pow_one] at h
    exact SoS.isSumSq_sub_trans h (by simpa only [pow_one] using
      (sos_budget_mono (d := d) (hm j) 1))
  have hquad (j : Fin k) : IsSumSq (C V * nsq - quad (F.cov j)) := by
    have hpsd : (V • (1 : Mat d) - F.cov j).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg
        ((PosSemidef.one.smul hV).1.sub (hF.2.2.2 j).1) fun v ↦ ?_
      simpa only [qform, sub_mulVec, dotProduct_sub, star_trivial] using
        sub_nonneg.mpr (hc j v)
    have hshift : quad (V • (1 : Mat d) - F.cov j) =
        C V * nsq - quad (F.cov j) := by
      simp [quad, nsq, Matrix.one_apply, C_sub, sub_mul, Finset.sum_sub_distrib,
        Finset.mul_sum, pow_two, mul_assoc, apply_ite, ite_mul]
    simpa only [hshift] using SoSKit.psd_quad _ hpsd
  have hcomponent (j : Fin k) : IsSumSq (C K * nsq ^ r -
      IdCov.hmom (2 * r) (lin (F.mean j)) (quad (F.cov j))) := by
    have hi (i : ℕ) (hi : i ∈ Finset.range (r + 1)) :
        IsSumSq (C ((IdCov.hermCoeff (2 * r) i : ℝ) * A ^ (r - i) * V ^ i) *
          nsq ^ r - (IdCov.hermCoeff (2 * r) i : RPoly d) *
            lin (F.mean j) ^ (2 * r - 2 * i) * quad (F.cov j) ^ i) := by
      have hir : i ≤ r := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hh := SoSKit.mixed_powers (lin (F.mean j) ^ 2) (quad (F.cov j)) A V
        hA hV (SoS.isSumSq_sq _) (SoSKit.psd_quad _ (hF.2.2.2 j).posSemidef)
        (hlin j) (hquad j) (r - i) i
      have he : r - i + i = r := Nat.sub_add_cancel hir
      have he' : 2 * (r - i) = 2 * r - 2 * i := by omega
      convert SoS.isSumSq_C_mul
        (Nat.cast_nonneg (IdCov.hermCoeff (2 * r) i)) hh using 1
      rw [he, ← pow_mul, he']
      simp only [C_mul, map_natCast]
      ring
    have hh := IsSumSq.sum hi
    simpa only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
      K, IdCov.hmom, Nat.mul_div_cancel_left r (by omega : 0 < 2)] using hh
  have hmix := IsSumSq.sum fun j (_ : j ∈ Finset.univ) ↦
    SoS.isSumSq_C_mul (hF.1.le.trans (hF.2.1 j)) (hcomponent j)
  have hmix' : IsSumSq (C K * nsq ^ r - populationMoment F (2 * r)) := by
    convert hmix using 1
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum,
      hF.2.2.1, C_1, one_mul, populationMoment]
  have hK : K ≤ (10 * r / w) ^ r := by
    refine (MomentAux.even_moment_bound A V hA hV r).trans ?_
    apply pow_le_pow_left₀ (by positivity : 0 ≤ 2 * A + 4 * r * V)
    dsimp only [A, V]
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    apply (le_div_iff₀ hF.1).mpr
    have he : (2 * (2 / w) + 4 * r * (1.1 / w)) * w = 4 + 4.4 * r := by
      field_simp
      ring
    rw [he]
    linarith only [hrR]
  exact SoS.isSumSq_sub_trans hmix' (sos_budget_mono hK r)

private theorem reference_partition_poly (D : Reference n k d) (w : ℝ)
    (hD : D.Valid w) (f : Fin n → RPoly d) :
    (∑ j, C (D.model.weight j) *
      (C ((D.reference.filter fun l ↦ D.label l = j).card : ℝ)⁻¹ *
        ∑ l ∈ D.reference.filter (fun l ↦ D.label l = j), f l)) =
      C (D.reference.card : ℝ)⁻¹ * ∑ l ∈ D.reference, f l := by
  classical
  have hc (j : Fin k) :
      ((D.reference.filter fun l ↦ D.label l = j).card : ℝ) ≠ 0 := by
    have hh : 0 < D.model.weight j := hD.1.1.trans_le (hD.1.2.1 j)
    rw [hD.2.2.2.2.2.2 j] at hh
    intro hz
    simp only [hz, zero_div] at hh
    exact lt_irrefl 0 hh
  have he (j : Fin k) : D.model.weight j *
      ((D.reference.filter fun l ↦ D.label l = j).card : ℝ)⁻¹ =
        (D.reference.card : ℝ)⁻¹ := by
    rw [hD.2.2.2.2.2.2 j, div_eq_mul_inv]
    field_simp [hc j]
  simp only [← mul_assoc, ← C_mul, he, ← Finset.mul_sum, Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp

private theorem reference_error_even (D : Reference n k d) (w θ : ℝ)
    (hD : D.Valid w) (s : ℕ) (hr : D.Resilient (2 * s) θ) (hθ : 0 ≤ θ)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / w) • (1 : Mat d))) :
    SoS.coeffNorm1 (empiricalMoment D.reference D.clean (2 * s) -
      populationMoment D.model (2 * s)) ≤ θ * (2 / w) ^ s := by
  let c := Real.sqrt (w / 2)
  have hw : 0 < w := hD.1.1
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = w / 2 := Real.sq_sqrt (by positivity)
  let S (j : Fin k) := D.reference.filter fun l ↦ D.label l = j
  let E (j : Fin k) : RPoly d :=
    C ((S j).card : ℝ)⁻¹ * ∑ l ∈ S j, lin (D.clean l) ^ (2 * s) -
      IdCov.hmom (2 * s) (lin (D.model.mean j)) (quad (D.model.cov j))
  have hcomp (j : Fin k) : SoS.coeffNorm1 (E j) ≤ θ * (2 / w) ^ s := by
    have hh := hr (c • (1 : Mat d)) 0 j (2 * s) le_rfl
    dsimp only at hh
    simp only [sub_zero, smul_mulVec, one_mulVec, transpose_smul, transpose_one,
      Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, ← pow_two] at hh
    have hscale : C ((S j).card : ℝ)⁻¹ *
        (∑ l ∈ S j, lin (c • D.clean l) ^ (2 * s)) -
          IdCov.hmom (2 * s) (lin (c • D.model.mean j))
            (quad (c ^ 2 • D.model.cov j)) = C (c ^ (2 * s)) * E j := by
      simp only [MomentAux.lin_smul, MomentAux.quad_smul, C_pow, MomentAux.hmom_scale,
        mul_pow, ← Finset.mul_sum, E]
      ring
    change SoS.coeffNorm1 (C ((S j).card : ℝ)⁻¹ *
      (∑ l ∈ S j, lin (c • D.clean l) ^ (2 * s)) - _) ≤ _ at hh
    rw [hscale, SoS.coeffNorm1_C_mul, abs_of_nonneg (pow_nonneg hc0.le _)] at hh
    have hnorm := MomentAux.scaled_norms w c (D.model.mean j) (D.model.cov j)
      hw hc2 (hm j) (hD.1.2.2.2 j).posSemidef (hc j)
    have hbase : 1 + SoS.coeffNorm1 (lin (c • D.model.mean j)) +
        SoS.coeffNorm1 (quad (c ^ 2 • D.model.cov j)) ≤ (d + 1 : ℝ) ^ 2 := by
      nlinarith only [hnorm.1, hnorm.2, Nat.cast_nonneg (α := ℝ) d]
    have hpow : (1 + SoS.coeffNorm1 (lin (c • D.model.mean j)) +
        SoS.coeffNorm1 (quad (c ^ 2 • D.model.cov j))) ^ (2 * s) ≤
        (d + 1 : ℝ) ^ (2 * (2 * s)) := by
      simpa only [pow_mul] using pow_le_pow_left₀
        (add_nonneg (add_nonneg zero_le_one (SoS.coeffNorm1_nonneg _))
          (SoS.coeffNorm1_nonneg _)) hbase (2 * s)
    have hsmall : c ^ (2 * s) * SoS.coeffNorm1 (E j) ≤ θ := by
      refine hh.trans ?_
      calc
        _ ≤ (θ / (d + 1 : ℝ) ^ (2 * (2 * s))) *
            (d + 1 : ℝ) ^ (2 * (2 * s)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = θ := div_mul_cancel₀ _ (by positivity)
    have hinv : c ^ (2 * s) * (2 / w) ^ s = 1 := by
      rw [pow_mul, hc2, ← mul_pow]
      have he : w / 2 * (2 / w) = 1 := by field_simp
      rw [he, one_pow]
    calc
      _ = (2 / w) ^ s * (c ^ (2 * s) * SoS.coeffNorm1 (E j)) := by
        rw [← mul_assoc, mul_comm ((2 / w) ^ s), hinv, one_mul]
      _ ≤ (2 / w) ^ s * θ := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := mul_comm _ _
  have hid : (∑ j, C (D.model.weight j) * E j) =
      empiricalMoment D.reference D.clean (2 * s) - populationMoment D.model (2 * s) := by
    simp only [E, mul_sub, Finset.sum_sub_distrib]
    rw [reference_partition_poly D w hD]
    rfl
  rw [← hid]
  calc
    _ ≤ ∑ j, SoS.coeffNorm1 (C (D.model.weight j) * E j) :=
      SoS.coeffNorm1_sum_le _ _
    _ = ∑ j, D.model.weight j * SoS.coeffNorm1 (E j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (hD.1.1.le.trans (hD.1.2.1 j))]
    _ ≤ ∑ j, D.model.weight j * (θ * (2 / w) ^ s) := Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_left (hcomp j) (hD.1.1.le.trans (hD.1.2.1 j))
    _ = _ := by rw [← Finset.sum_mul, hD.1.2.2.1, one_mul]

/-- Moment resilience transfers Gaussian SoS upper bounds to the reference set. -/
theorem reference_sos
    (D : Reference n k d) (w θ : ℝ) (hD : D.Valid w)
    (s : ℕ) (hs : 1 ≤ s) (hr : D.Resilient (2 * s) θ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / w) • (1 : Mat d))) :
    IsSumSq (C (momentBudget w s) * nsq ^ s - empiricalMoment D.reference D.clean (2 * s)) := by
  let E := empiricalMoment D.reference D.clean (2 * s) - populationMoment D.model (2 * s)
  have hhom : E.IsHomogeneous (2 * s) := by
    apply (homogeneous_empirical D.reference D.clean (2 * s)).sub
    exact IsHomogeneous.sum _ _ _ fun j _ ↦
      (homogeneous_hmom (D.model.mean j) (D.model.cov j) (2 * s)).C_mul _
  have herror := SoS.isSumSq_l1 hhom
  have hpop := population_sos D.model w hD.1 s hs hm hc
  have hnorm := reference_error_even D w θ hD s hr hθ.1 hm hc
  have hw : 0 < w := hD.1.1
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpow : (2 / w) ^ s ≤ (10 * s / w) ^ s := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right (by linarith only [hsR]) hw.le
  have hnorm' : SoS.coeffNorm1 E ≤ (10 * s / w) ^ s := by
    calc
      _ ≤ θ * (2 / w) ^ s := hnorm
      _ ≤ 1 * (2 / w) ^ s := mul_le_mul_of_nonneg_right (by linarith only [hθ.2])
        (by positivity)
      _ ≤ _ := by simpa only [one_mul] using hpow
  have hbudget : (10 * s / w) ^ s + SoS.coeffNorm1 E ≤ momentBudget w s := by
    have hh : (10 * s / w) ^ s ≤ (20 * s / w) ^ s := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right (by nlinarith only [hsR]) hw.le
    dsimp only [momentBudget]
    linarith only [hnorm', hh]
  have hh := (hpop.add herror).add (sos_budget_mono (d := d) hbudget s)
  convert hh using 1
  simp only [C_add, E, nsq]
  ring


/-- Clipped solver weights preserve total mass and moment certificates. -/
theorem clipping_sos
    (x : Fin n → Vec d) (w : Fin n → ℝ) (B ρ : ℝ) (s : ℕ)
    (hρ : 0 ≤ ρ) (hw : ∀ i, -ρ ≤ w i ∧ w i ≤ 1 + ρ)
    (hb : IsSumSq (C B * nsq ^ s - ∑ i, C (w i) * lin (x i) ^ (2 * s))) :
    IsSumSq (C (B + ρ * ∑ i, sqnorm (x i) ^ s) * nsq ^ s -
      ∑ i, C (clipped (w i)) * lin (x i) ^ (2 * s)) := by
  have hi (i : Fin n) :
      IsSumSq (C (ρ * sqnorm (x i) ^ s) * nsq ^ s -
        C (clipped (w i) - w i) * lin (x i) ^ (2 * s)) := by
    have hclip : clipped (w i) - w i ≤ ρ := by
      unfold clipped
      by_cases h : 0 ≤ w i
      · rw [max_eq_left h]
        have hh := min_le_left (w i) 1
        linarith
      · rw [max_eq_right (le_of_not_ge h), min_eq_left (by norm_num)]
        linarith [(hw i).1]
    have hp : IsSumSq (lin (x i) ^ (2 * s)) := by
      rw [pow_mul']
      exact SoS.isSumSq_sq _
    convert (SoS.isSumSq_C_mul hρ (sos_lin_pow (x i) s)).add
      (SoS.isSumSq_C_mul (sub_nonneg.mpr hclip) hp) using 1
    simp only [C_mul, C_sub]
    ring
  have hh := hb.add (IsSumSq.sum fun i (_ : i ∈ Finset.univ) ↦ hi i)
  convert hh using 1
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum, ← Finset.mul_sum,
    C_add, C_mul, C_sub]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring


/-- The interpolation bound for one Gram block. -/
def momentTraceBound (n d r : ℕ) (B : ℝ) : ℝ :=
  Gram.gridConst d r * (r + 1 : ℝ) ^ d * (B * n * (d * (r : ℝ) ^ 2) ^ r)

/-- Good-set mass, SOS bounds, and the explicit budget for weights and Gram blocks. -/
structure MomentGramBudget (x : Fin n → Vec d) (G : Finset (Fin n))
    (J : List ℕ) (B : ℕ → ℝ) (ε ball : ℝ) : Prop where
  mass : (1 - ε) * n ≤ G.card
  nonneg : ∀ r ∈ J, 0 ≤ B r
  sos : ∀ r ∈ J, IsSumSq (C (B r * n) * nsq ^ r -
    ∑ i ∈ G, lin (x i) ^ (2 * r))
  ball_bound : n + ∑ a : Fin J.length, momentTraceBound n d J[a] (B J[a]) ≤ ball

/-- A specified ball suffices when it bounds the sum of the Gram traces. -/
theorem momentProgram_feasible_at_ball
    (x : Fin n → Vec d) (G : Finset (Fin n)) (J : List ℕ) (B : ℕ → ℝ)
    (ε ball : ℝ) (h : MomentGramBudget x G J B ε ball) :
    ∃ y : ℕ → ℝ, ∀ f ∈ momentConstraints x J B ε ball, 0 ≤ eval y f := by
  classical
  rcases h with ⟨hG, hB, hs, hball⟩
  let P (r : ℕ) : RPoly d :=
    C (B r * n) * nsq ^ r - ∑ i ∈ G, lin (x i) ^ (2 * r)
  have hdeg (r : ℕ) : (P r).totalDegree ≤ 2 * r := by
    have hN : (nsq ^ r : RPoly d).IsHomogeneous (2 * r) := by
      simpa only [nsq, Nat.mul_comm] using
        (IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_X_pow i 2).pow r
    have hsum : (∑ i ∈ G, lin (x i) ^ (2 * r)).IsHomogeneous (2 * r) :=
      IsHomogeneous.sum _ _ _ fun i _ ↦ by
        simpa only [lin, one_mul] using (IsHomogeneous.sum _ _ _ fun j _ ↦
          (isHomogeneous_X ℝ j).C_mul (x i j)).pow (2 * r)
    exact ((hN.C_mul (B r * n)).sub hsum).totalDegree_le
  have hfactor (a : Fin J.length) :
      ∃ H : Matrix (Fin (Rounding.monos d J[a]).length)
          (Fin (Rounding.monos d J[a]).length) ℝ,
        P J[a] = ∑ c, (∑ b, C (H b c) * monomial (Rounding.monos d J[a])[b] 1) ^ 2 ∧
          (∑ b, ∑ c, H b c ^ 2) ≤ momentTraceBound n d J[a] (B J[a]) := by
    obtain ⟨H, hH, htrace⟩ := Gram.gram_factor (P J[a]) J[a]
      (hs J[a] (List.getElem_mem a.isLt)) (hdeg J[a])
    refine ⟨H, hH, htrace.trans ?_⟩
    unfold momentTraceBound
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    calc
      _ ≤ ∑ _z : Fin d → Fin (J[a] + 1),
          B J[a] * n * (d * (J[a] : ℝ) ^ 2) ^ J[a] := by
        apply Finset.sum_le_sum
        intro z _
        dsimp only [P]
        simp only [map_sub, map_mul, eval_C, map_pow, map_sum]
        have hdata : 0 ≤ ∑ i ∈ G, eval (fun j ↦ (z j : ℝ))
            (lin (x i) ^ (2 * J[a])) := by
          apply Finset.sum_nonneg
          intro i _
          rw [map_pow, pow_mul']
          exact sq_nonneg _
        have hnorm : eval (fun j ↦ (z j : ℝ)) (nsq : RPoly d) ≤
            d * (J[a] : ℝ) ^ 2 := by
          simp only [nsq, map_sum, map_pow, eval_X]
          calc
            _ ≤ ∑ _i : Fin d, (J[a] : ℝ) ^ 2 := by
              apply Finset.sum_le_sum
              intro i _
              have hz : (z i : ℝ) ≤ J[a] := by
                exact_mod_cast Nat.le_of_lt_succ (z i).isLt
              exact pow_le_pow_left₀ (by positivity) hz 2
            _ = _ := by simp
        have hN0 : 0 ≤ eval (fun j ↦ (z j : ℝ)) (nsq : RPoly d) := by
          simp only [nsq, map_sum, map_pow, eval_X]
          exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
        have hmul := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hN0 hnorm J[a])
          (mul_nonneg (hB J[a] (List.getElem_mem a.isLt)) (Nat.cast_nonneg n))
        simp only [map_pow] at hdata
        linarith only [hmul, hdata]
      _ = _ := by simp
  choose H hH htrace using hfactor
  let blocks : ℕ → List ℝ := fun a ↦
    if ha : a < J.length then Rounding.NestedAux.matrixData (H ⟨a, ha⟩) else []
  have hprefix (a : ℕ) (ha : a ≤ J.length) :
      ((List.range a).map fun b ↦ (blocks b).length).sum =
        ((J.take a).map fun r ↦ (Rounding.monos d r).length ^ 2).sum := by
    congr 1
    apply List.ext_getElem
    · simp [List.length_take, Nat.min_eq_left ha]
    · intro b hb hb'
      have hbJ : b < J.length := by
        simp only [List.length_map, List.length_range] at hb
        omega
      simp [blocks, hbJ, pow_two]
  let pre : List ℝ := List.ofFn fun i : Fin n ↦ if i ∈ G then 1 else 0
  let data := pre ++ Rounding.NestedAux.pack blocks J.length
  let y : ℕ → ℝ := fun i ↦ data.getD i 0
  have hy (i : Fin n) : y i = if i ∈ G then 1 else 0 := by
    dsimp only [y, data]
    rw [List.getD_append _ _ _ _ (by simp [pre])]
    simp [pre, i.isLt]
  have hyH (a : Fin J.length) (b c : Fin (Rounding.monos d J[a]).length) :
      y (momentGramOffset n d J a + b * (Rounding.monos d J[a]).length + c) =
        H a b c := by
    have hbc : b * (Rounding.monos d J[a]).length + c < (blocks a).length := by
      simp only [blocks, dite_eq_left a.isLt, Rounding.NestedAux.matrixData_length]
      have hh := (finProdFinEquiv (b, c)).isLt
      simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.add_comm, Nat.mul_comm] using hh
    have hh := Rounding.NestedAux.pack_get_inside blocks pre [] a.isLt hbc
    rw [hprefix a (by omega)] at hh
    have hh' : (blocks a).getD
        (b * (Rounding.monos d J[a]).length + c) 0 = H a b c := by
      simp only [blocks, dite_eq_left a.isLt]
      exact Rounding.NestedAux.matrixData_get _ b c
    convert hh.trans hh' using 1
    simp [y, data, pre, momentGramOffset, add_assoc]
  have hemb (p : RPoly d) : (Rounding.embedCoeff p).map (eval y) = p := by
    have he : (eval y).comp (MvPolynomial.C : ℝ →+* Rounding.NPoly) = RingHom.id ℝ := by
      ext r
      simp
    simp only [Rounding.embedCoeff, MvPolynomial.map_map, he, MvPolynomial.map_id]
  have hgram (a : Fin J.length) :
      (Rounding.gram (momentGramOffset n d J a) (Rounding.monos d J[a])).map (eval y) =
        P J[a] := by
    rw [hH a]
    simp only [Rounding.gram, map_sum, map_pow, map_mul, map_C, map_monomial,
      map_one, eval_X, hyH]
  have htemplate (a : Fin J.length) : (momentTemplate x J B a).map (eval y) = 0 := by
    simp only [momentTemplate, map_sub, map_sum, map_mul, hemb, map_C, eval_X,
      hy, hgram]
    simp [P, ite_mul]
  have hcoeff (a : Fin J.length) (μ : Fin d →₀ ℕ) :
      eval y ((momentTemplate x J B a).coeff μ) = 0 := by
    have hh := congrArg (fun p : RPoly d ↦ p.coeff μ) (htemplate a)
    simpa only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hh
  have hlen : data.length = momentVars n d J := by
    simp only [data, List.length_append, pre, List.length_ofFn, Rounding.NestedAux.pack_length,
      hprefix _ le_rfl, momentVars, momentGramOffset]
  have hpre : (pre.map fun z ↦ z ^ 2).sum ≤ (n : ℝ) := by
    simp only [pre, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> norm_num
      _ = _ := by simp
  have hpack : ((Rounding.NestedAux.pack blocks J.length).map fun z ↦ z ^ 2).sum ≤
      ∑ a : Fin J.length, momentTraceBound n d J[a] (B J[a]) := by
    rw [Rounding.NestedAux.pack_sq, SoS.Coords.sum_range_map]
    apply Finset.sum_le_sum
    intro a _
    simp only [blocks, dite_eq_left a.isLt, Rounding.NestedAux.matrixData_sq]
    exact htrace a
  have hyball : ∑ i ∈ Finset.range (momentVars n d J), y i ^ 2 ≤ ball := by
    change ∑ i ∈ Finset.range (momentVars n d J), data.getD i 0 ^ 2 ≤ ball
    rw [← hlen, Rounding.NestedAux.sum_getD_sq]
    simp only [data, List.map_append, List.sum_append]
    exact (add_le_add hpre hpack).trans hball
  refine ⟨y, ?_⟩
  · intro f hf
    simp only [momentConstraints, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap] at hf
    rcases hf with ((rfl | hf) | rfl) | hf
    · simpa only [map_sub, eval_C, map_sum, map_pow, eval_X] using sub_nonneg.mpr hyball
    · obtain ⟨i, _, rfl | rfl⟩ := hf
      · simp only [eval_X, hy]
        split_ifs <;> norm_num
      · simp only [map_sub, map_one, eval_X, hy]
        split_ifs <;> norm_num
    · simp only [map_sub, map_sum, eval_X, eval_C, hy]
      simpa using sub_nonneg.mpr hG
    · obtain ⟨a, _, μ, _, rfl | rfl⟩ := hf
      · rw [hcoeff]
      · rw [map_neg, hcoeff]
        norm_num


-- Exact subset selection suffices for the existential interface, which has no runtime clause.
-- The chosen subset depends only on the rational input and its weight and contamination budgets.


end

end ABBKS26.Robust
