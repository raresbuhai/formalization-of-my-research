module

public import ABBKS26.Assembly.ExecMomentAuxSDP

/-! Quantitative feasibility and moment transfer for the weight and Gram program. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.MomentAnalytic

noncomputable section

open Common Robust MvPolynomial Matrix
open scoped BigOperators

variable {n k d : ℕ}

private theorem cube_ge (q : ℕ) (hq : 1 ≤ q) : q ≤ q ^ 3 ∧ q ^ 2 ≤ q ^ 3 := by
  have hsq : q ≤ q ^ 2 := Nat.le_pow (by omega)
  have hcu : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨hsq.trans hcu, hcu⟩

theorem interpBound_le (r R : ℕ) (hr : r ≤ R) :
    SoS.interpBound r ≤ 2 ^ ((R + 1) ^ 3) := by
  have hbase : r + 1 ≤ 2 ^ (R + 1) := by
    exact (by omega : r + 1 ≤ R + 2).trans (Nat.lt_two_pow_self)
  calc
    _ ≤ (r + 1) ^ (r + 1) * ((r + 1) ^ r) ^ (r + 1) :=
      Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
    _ = (r + 1) ^ ((r + 1) ^ 2) := by rw [← pow_mul, ← pow_add]; congr 1; ring
    _ ≤ (2 ^ (R + 1)) ^ ((R + 1) ^ 2) := by
      exact (Nat.pow_le_pow_left hbase _).trans
        (Nat.pow_le_pow_right (by positivity) (Nat.pow_le_pow_left (by omega) _))
    _ = _ := by rw [← pow_mul]; congr 1; ring

theorem radial_budget_le {b R r : ℕ} {w : ℝ} (hb : 1 ≤ b) (hr : r ≤ R)
    (hw : 0 < w) (hinv : w⁻¹ ≤ 2 ^ b) :
    4 * (20 * r / w) ^ r ≤ (2 : ℝ) ^ (10 * b * (R + 1) ^ 3) := by
  have hrpow : (r : ℝ) ≤ 2 ^ (R + 1) := by
    exact_mod_cast (show r ≤ 2 ^ (R + 1) from
      (by omega : r ≤ R + 1).trans (Nat.lt_two_pow_self).le)
  have hbase : 20 * r / w ≤ (2 : ℝ) ^ (5 + (R + 1) + b) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ (2 : ℝ) ^ 5 * 2 ^ (R + 1) * 2 ^ b := by gcongr; norm_num
      _ = _ := by simp only [← pow_add]
  have hexp : 2 + (5 + (R + 1) + b) * r ≤ 10 * b * (R + 1) ^ 3 := by
    obtain ⟨hQ, hQ2⟩ := cube_ge (R + 1) (by omega)
    have h1 := Nat.mul_le_mul_left b hQ
    have h2 := Nat.mul_le_mul_right ((R + 1) ^ 3) hb
    have h3 := Nat.mul_le_mul_left (R + 1) hr
    have h4 := Nat.mul_le_mul_left b hr
    nlinarith
  calc
    _ ≤ 2 ^ 2 * ((2 : ℝ) ^ (5 + (R + 1) + b)) ^ r := by
      gcongr
      norm_num
    _ = (2 : ℝ) ^ (2 + (5 + (R + 1) + b) * r) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp

theorem traceBound_le {b R n d r : ℕ} {B : ℝ} (hb : 1 ≤ b) (hn : n ≤ b)
    (hd : d ≤ b) (hr : r ≤ R) (hB : 0 ≤ B)
    (hbudget : B ≤ (2 : ℝ) ^ (10 * b * (R + 1) ^ 3)) :
    momentTraceBound n d r B ≤ (2 : ℝ) ^ (20 * b * (R + 1) ^ 3) := by
  let T := b * (R + 1) ^ 3
  obtain ⟨hQ, hQ2⟩ := cube_ge (R + 1) (by omega)
  have hd2 : (d + 1 : ℝ) ≤ 2 ^ b := by
    exact_mod_cast (show d + 1 ≤ 2 ^ b from
      (by omega : d + 1 ≤ b + 1).trans (Nat.lt_two_pow_self))
  have hr2 : (r + 1 : ℝ) ≤ 2 ^ (R + 1) := by
    exact_mod_cast (show r + 1 ≤ 2 ^ (R + 1) from
      (by omega : r + 1 ≤ R + 2).trans (Nat.lt_two_pow_self))
  have hdpow : (d + 1 : ℝ) ^ r ≤ 2 ^ T := by
    refine (pow_le_pow_left₀ (by positivity) hd2 r).trans ?_
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left b (by omega))
  have hipow : (SoS.interpBound r : ℝ) ^ (2 * d) ≤ 2 ^ (2 * T) := by
    have hi : (SoS.interpBound r : ℝ) ≤ 2 ^ ((R + 1) ^ 3) := by
      exact_mod_cast interpBound_le r R hr
    refine (pow_le_pow_left₀ (by positivity) hi _).trans ?_
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [T]
    nlinarith
  have hrpow : (r + 1 : ℝ) ^ d ≤ 2 ^ T := by
    refine (pow_le_pow_left₀ (by positivity) hr2 d).trans ?_
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [T]
    nlinarith [Nat.mul_le_mul_left b hQ, Nat.mul_le_mul_left (R + 1) hd]
  have hn2 : (n : ℝ) ≤ 2 ^ T := by
    have hn' : n ≤ 2 ^ b := hn.trans (Nat.lt_two_pow_self).le
    have hbT : b ≤ T := Nat.le_mul_of_pos_right _ (by positivity)
    exact_mod_cast hn'.trans (Nat.pow_le_pow_right (by omega) hbT)
  have hnorm : (d * (r : ℝ) ^ 2) ^ r ≤ 2 ^ (3 * T) := by
    have hd' : (d : ℝ) ≤ 2 ^ b := by linarith only [hd2]
    have hr' : (r : ℝ) ≤ 2 ^ (R + 1) := by linarith only [hr2]
    have hbase : d * (r : ℝ) ^ 2 ≤ 2 ^ (b + 2 * (R + 1)) := by
      calc
        _ ≤ 2 ^ b * ((2 : ℝ) ^ (R + 1)) ^ 2 := by gcongr
        _ = _ := by rw [← pow_mul, ← pow_add, mul_comm (R + 1) 2]
    refine (pow_le_pow_left₀ (by positivity) hbase r).trans ?_
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    dsimp only [T]
    nlinarith [Nat.mul_le_mul_left b hr, Nat.mul_le_mul_left (R + 1) hr,
      Nat.mul_le_mul_right ((R + 1) ^ 3) hb, Nat.mul_le_mul_left b hQ]
  unfold momentTraceBound Gram.gridConst
  push_cast
  calc
    _ ≤ (2 : ℝ) ^ T * 2 ^ (2 * T) * 2 ^ T * 2 ^ T *
        (2 ^ (10 * T) * 2 ^ T * 2 ^ (3 * T)) := by
      gcongr
      simpa only [T, mul_assoc] using hbudget
    _ = (2 : ℝ) ^ (19 * T) := by simp only [← pow_add]; congr 1; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by dsimp [T]; nlinarith)

theorem ball_exponent_bound (b R : ℕ) (hb : 7 ≤ b) :
    20 * b * (R + 1) ^ 3 + b + 1 ≤ (b + 2) ^ 4 * (R + 1) ^ 4 := by
  have hQ : 1 ≤ (R + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hQ4 : (R + 1) ^ 3 ≤ (R + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hbig : 21 * b + 1 ≤ (b + 2) ^ 4 := by
    have hs : 81 ≤ (b + 2) ^ 2 := by nlinarith
    have hh := Nat.mul_le_mul_right ((b + 2) ^ 2) hs
    nlinarith
  calc
    _ ≤ (21 * b + 1) * (R + 1) ^ 3 := by nlinarith
    _ ≤ (b + 2) ^ 4 * (R + 1) ^ 3 := Nat.mul_le_mul_right _ hbig
    _ ≤ _ := Nat.mul_le_mul_left _ hQ4

private theorem sos_nsq_pow (s : ℕ) : IsSumSq ((nsq : RPoly d) ^ s) :=
  SoS.isSumSq_pow (IsSumSq.sum_sq _ _) s

private theorem sos_budget_mono {a b : ℝ} (hab : a ≤ b) (s : ℕ) :
    IsSumSq (C b * (nsq : RPoly d) ^ s - C a * nsq ^ s) := by
  rw [← sub_mul, ← C_sub]
  exact SoS.isSumSq_C_mul (sub_nonneg.mpr hab) (sos_nsq_pow s)

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

private theorem normalized_weights (u v : Fin n → ℝ) (ε : ℝ)
    (he : 0 < ε ∧ ε ≤ 1 / 4) (hn : 0 < n)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hmu : (1 - ε) * n ≤ ∑ i, u i) (hmv : (1 - ε) * n ≤ ∑ i, v i) :
    (∑ i, |(∑ j, u j)⁻¹ * u i - (∑ j, v j)⁻¹ * v i|) ≤ 4 * ε ∧
    ∀ i, |(∑ j, u j)⁻¹ * u i - (∑ j, v j)⁻¹ * v i| ≤
      (2 / n) * (u i + v i) := by
  let U := ∑ i, u i
  let V := ∑ i, v i
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hUn : U ≤ n := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ (hu i).2)
  have hVn : V ≤ n := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ (hv i).2)
  have hU : 0 < U := lt_of_lt_of_le (mul_pos (by linarith only [he.2]) hnR) hmu
  have hV : 0 < V := lt_of_lt_of_le (mul_pos (by linarith only [he.2]) hnR) hmv
  have hUi : U⁻¹ ≤ 2 / n := by
    rw [inv_eq_one_div, div_le_div_iff₀ hU hnR]
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2) hnR.le]
  have hVi : V⁻¹ ≤ 2 / n := by
    rw [inv_eq_one_div, div_le_div_iff₀ hV hnR]
    nlinarith [mul_nonneg (sub_nonneg.mpr he.2) hnR.le]
  have hdiff : (∑ i, |u i - v i|) ≤ 2 * ε * n := by
    have hi (i : Fin n) : |u i - v i| ≤ (1 - u i) + (1 - v i) := by
      rw [abs_le]
      constructor <;> linarith [(hu i).2, (hv i).2]
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hi i)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hh
    change (∑ i, |u i - v i|) ≤ (n - U) + (n - V) at hh
    linarith only [hh, hmu, hmv]
  have hmass : |V - U| ≤ ε * n := by
    rw [abs_le]
    constructor <;> linarith only [hmu, hmv, hUn, hVn]
  have hinv : |U⁻¹ - V⁻¹| * V = U⁻¹ * |V - U| := by
    have hh : U⁻¹ - V⁻¹ = (V - U) / (U * V) := by field_simp
    rw [hh, abs_div, abs_mul, abs_of_pos hU, abs_of_pos hV]
    field_simp
  constructor
  · have hi (i : Fin n) : |U⁻¹ * u i - V⁻¹ * v i| ≤
        U⁻¹ * |u i - v i| + |U⁻¹ - V⁻¹| * v i := by
      calc
        _ = |U⁻¹ * (u i - v i) + (U⁻¹ - V⁻¹) * v i| := by congr 1; ring
        _ ≤ |U⁻¹ * (u i - v i)| + |(U⁻¹ - V⁻¹) * v i| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (inv_nonneg.mpr hU.le),
          abs_of_nonneg (hv i).1]
    calc
      _ ≤ ∑ i, (U⁻¹ * |u i - v i| + |U⁻¹ - V⁻¹| * v i) :=
        Finset.sum_le_sum fun i _ ↦ hi i
      _ = U⁻¹ * (∑ i, |u i - v i|) + U⁻¹ * |V - U| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hinv]
      _ ≤ U⁻¹ * (2 * ε * n) + U⁻¹ * (ε * n) :=
        add_le_add (mul_le_mul_of_nonneg_left hdiff (inv_nonneg.mpr hU.le))
          (mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hU.le))
      _ = (3 * ε * n) / U := by rw [div_eq_mul_inv]; ring
      _ ≤ 4 * ε := by
        rw [div_le_iff₀ hU]
        have hh : 0 ≤ 4 * U - 3 * (n : ℝ) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr he.2) hnR.le]
        nlinarith only [mul_nonneg he.1.le hh]
  · intro i
    calc
      _ ≤ |U⁻¹ * u i| + |V⁻¹ * v i| := abs_sub _ _
      _ = U⁻¹ * u i + V⁻¹ * v i := by
        rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hU.le) (hu i).1),
          abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hV.le) (hv i).1)]
      _ ≤ (2 / n) * u i + (2 / n) * v i :=
        add_le_add (mul_le_mul_of_nonneg_right hUi (hu i).1)
          (mul_le_mul_of_nonneg_right hVi (hv i).1)
      _ = _ := by ring

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

theorem resilient_mono (D : Reference n k d) {s t : ℕ} {θ : ℝ}
    (h : D.Resilient s θ) (ht : t ≤ s) (hθ : 0 ≤ θ) : D.Resilient t θ := by
  intro T a j r hr
  exact (h T a j r (hr.trans ht)).trans (by
    apply mul_le_mul_of_nonneg_right
    · exact div_le_div_of_nonneg_left hθ (by positivity)
        (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) d]) (by omega))
    · exact pow_nonneg (add_nonneg
        (add_nonneg zero_le_one (SoS.coeffNorm1_nonneg _))
        (SoS.coeffNorm1_nonneg _)) r)

theorem reference_error_square (D : Reference n k d) (w θ : ℝ)
    (hD : D.Valid w) (r : ℕ) (hr : D.Resilient r θ) (hθ : 0 ≤ θ)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / w) • (1 : Mat d))) :
    IsSumSq (C (θ ^ 2 * (2 / w) ^ r) * nsq ^ r -
      (empiricalMoment D.reference D.clean r - populationMoment D.model r) ^ 2) := by
  let c := Real.sqrt (w / 2)
  have hw : 0 < w := hD.1.1
  have hc0 : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = w / 2 := Real.sq_sqrt (by positivity)
  let S (j : Fin k) := D.reference.filter fun l ↦ D.label l = j
  let E (j : Fin k) : RPoly d :=
    C ((S j).card : ℝ)⁻¹ * ∑ l ∈ S j, lin (D.clean l) ^ r -
      IdCov.hmom r (lin (D.model.mean j)) (quad (D.model.cov j))
  have hcomp (j : Fin k) : c ^ r * SoS.coeffNorm1 (E j) ≤ θ := by
    have hh := hr (c • (1 : Mat d)) 0 j r le_rfl
    dsimp only at hh
    simp only [sub_zero, smul_mulVec, one_mulVec, transpose_smul, transpose_one,
      Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul, ← pow_two] at hh
    have hscale : C ((S j).card : ℝ)⁻¹ *
        (∑ l ∈ S j, lin (c • D.clean l) ^ r) -
          IdCov.hmom r (lin (c • D.model.mean j))
            (quad (c ^ 2 • D.model.cov j)) = C (c ^ r) * E j := by
      simp only [_root_.ABBKS26.Robust.MomentAux.lin_smul,
        _root_.ABBKS26.Robust.MomentAux.quad_smul, C_pow,
        _root_.ABBKS26.Robust.MomentAux.hmom_scale, mul_pow, ← Finset.mul_sum, E]
      ring
    change SoS.coeffNorm1 (C ((S j).card : ℝ)⁻¹ *
      (∑ l ∈ S j, lin (c • D.clean l) ^ r) - _) ≤ _ at hh
    rw [hscale, SoS.coeffNorm1_C_mul, abs_of_nonneg (pow_nonneg hc0.le _)] at hh
    have hnorm := _root_.ABBKS26.Robust.MomentAux.scaled_norms w c (D.model.mean j) (D.model.cov j)
      hw hc2 (hm j) (hD.1.2.2.2 j).posSemidef (hc j)
    have hbase : 1 + SoS.coeffNorm1 (lin (c • D.model.mean j)) +
        SoS.coeffNorm1 (quad (c ^ 2 • D.model.cov j)) ≤ (d + 1 : ℝ) ^ 2 := by
      nlinarith only [hnorm.1, hnorm.2, Nat.cast_nonneg (α := ℝ) d]
    have hpow : (1 + SoS.coeffNorm1 (lin (c • D.model.mean j)) +
        SoS.coeffNorm1 (quad (c ^ 2 • D.model.cov j))) ^ r ≤
        (d + 1 : ℝ) ^ (2 * r) := by
      simpa only [pow_mul] using pow_le_pow_left₀
        (add_nonneg (add_nonneg zero_le_one (SoS.coeffNorm1_nonneg _))
          (SoS.coeffNorm1_nonneg _)) hbase r
    refine hh.trans ?_
    calc
      _ ≤ (θ / (d + 1 : ℝ) ^ (2 * r)) * (d + 1 : ℝ) ^ (2 * r) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = θ := div_mul_cancel₀ _ (by positivity)
  let P := empiricalMoment D.reference D.clean r - populationMoment D.model r
  have hid : (∑ j, C (D.model.weight j) * E j) = P := by
    simp only [E, mul_sub, Finset.sum_sub_distrib]
    rw [reference_partition_poly D w hD]
    rfl
  have hsmall : c ^ r * SoS.coeffNorm1 P ≤ θ := by
    calc
      _ ≤ c ^ r * ∑ j, SoS.coeffNorm1 (C (D.model.weight j) * E j) :=
        mul_le_mul_of_nonneg_left (hid ▸ SoS.coeffNorm1_sum_le _ _)
          (pow_nonneg hc0.le _)
      _ = ∑ j, D.model.weight j * (c ^ r * SoS.coeffNorm1 (E j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (hw.le.trans (hD.1.2.1 j))]
        ring
      _ ≤ ∑ j, D.model.weight j * θ := Finset.sum_le_sum fun j _ ↦
        mul_le_mul_of_nonneg_left (hcomp j) (hw.le.trans (hD.1.2.1 j))
      _ = θ := by rw [← Finset.sum_mul, hD.1.2.2.1, one_mul]
  have hinv : (c ^ r) ^ 2 * (2 / w) ^ r = 1 := by
    rw [← pow_mul, Nat.mul_comm r 2, pow_mul, hc2, ← mul_pow]
    have he : w / 2 * (2 / w) = 1 := by field_simp
    rw [he, one_pow]
  have hnorm : SoS.coeffNorm1 P ^ 2 ≤ θ ^ 2 * (2 / w) ^ r := by
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hc0.le r) (SoS.coeffNorm1_nonneg P)) hsmall 2)
      (by positivity : 0 ≤ (2 / w) ^ r)
    simpa only [mul_pow, mul_right_comm _ (SoS.coeffNorm1 P ^ 2), hinv, one_mul]
      using hh
  have hhom : P.IsHomogeneous r := by
    apply (homogeneous_empirical D.reference D.clean r).sub
    exact IsHomogeneous.sum _ _ _ fun j _ ↦
      (homogeneous_hmom (D.model.mean j) (D.model.cov j) r).C_mul _
  exact SoS.isSumSq_sub_trans (SoSKit.l1_square P r hhom) (sos_budget_mono hnorm r)

theorem reference_counts (D : Reference n k d) (w ε : ℝ)
    (hD : D.Valid w) (he : D.contamination ≤ ε) (he8 : ε ≤ 1 / 8) :
    0 < ε ∧ 0 < (D.block.card : ℝ) ∧
      (1 - ε) * D.block.card ≤ D.good.card ∧
      (1 - ε) * D.reference.card ≤ D.good.card ∧
      (D.reference.card : ℝ) ≤ 2 * D.block.card := by
  have hR : 0 < (D.reference.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hdelR : ((D.reference \ D.good).card : ℝ) / D.reference.card ≤ ε :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans he
  have hdelB : ((D.block \ D.good).card : ℝ) / D.block.card ≤ ε :=
    (le_max_left _ _).trans he
  have hfloor : 2 / (D.block.card : ℝ) ≤ ε :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans he
  have hgr : (1 - ε) * D.reference.card ≤ D.good.card := by
    rw [div_le_iff₀ hR, Finset.card_sdiff_of_subset hD.2.1,
      Nat.cast_sub (Finset.card_le_card hD.2.1)] at hdelR
    nlinarith only [hdelR]
  have hg : 0 < (D.good.card : ℝ) :=
    lt_of_lt_of_le (mul_pos (by linarith only [he8]) hR) hgr
  have hgb : (D.good.card : ℝ) ≤ D.block.card := by
    exact_mod_cast Finset.card_le_card hD.2.2.1
  have hB : 0 < (D.block.card : ℝ) := hg.trans_le hgb
  have hε : 0 < ε := (div_pos (by norm_num) hB).trans_le hfloor
  have hgood : (1 - ε) * D.block.card ≤ D.good.card := by
    rw [div_le_iff₀ hB, Finset.card_sdiff_of_subset hD.2.2.1,
      Nat.cast_sub (Finset.card_le_card hD.2.2.1)] at hdelB
    nlinarith only [hdelB]
  refine ⟨hε, hB, hgood, hgr, ?_⟩
  have hh := mul_le_mul_of_nonneg_right he8 hR.le
  nlinarith only [hh, hgr, hgb]

theorem moment_cs_sharp
    (x : Fin n → Vec d) (G : Finset (Fin n)) (w : Fin n → ℝ)
    (ε B : ℝ) (s : ℕ) (he : 0 < ε ∧ ε ≤ 1 / 4) (hB : 0 ≤ B) (hn : 0 < n)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hg : (1 - ε) * n ≤ G.card) (hmass : (1 - ε) * n ≤ ∑ i, w i)
    (hG : IsSumSq (C (B * n) * nsq ^ s - ∑ i ∈ G, lin (x i) ^ (2 * s)))
    (hW : IsSumSq (C (B * n) * nsq ^ s -
      ∑ i, C (w i) * lin (x i) ^ (2 * s))) :
    IsSumSq (C (16 * ε * B) * nsq ^ s -
      (weightedMoment w x s - empiricalMoment G x s) ^ 2) := by
  classical
  let v : Fin n → ℝ := fun i ↦ if i ∈ G then 1 else 0
  have hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1 := by
    intro i
    dsimp only [v]
    split_ifs <;> norm_num
  have hvs : ∑ i, v i = (G.card : ℝ) := by simp [v]
  let a : Fin n → ℝ := fun i ↦ (∑ j, w j)⁻¹ * w i - (∑ j, v j)⁻¹ * v i
  let p : Fin n → RPoly d := fun i ↦ lin (x i) ^ s
  let A : ℝ := ∑ i, |a i|
  have ha := normalized_weights w v ε he hn hw hv (by simpa [hvs] using hmass)
    (by simpa [hvs] using hg)
  have hp (i : Fin n) : p i ^ 2 = lin (x i) ^ (2 * s) := by
    dsimp only [p]
    rw [← pow_mul, Nat.mul_comm]
  have hG' : IsSumSq (C (B * n) * nsq ^ s - ∑ i, C (v i) * p i ^ 2) := by
    simpa [hp, v, ite_mul, ← Finset.sum_filter] using hG
  have hW' : IsSumSq (C (B * n) * nsq ^ s - ∑ i, C (w i) * p i ^ 2) := by
    simpa only [hp] using hW
  have hdom : IsSumSq (∑ i, C ((2 / n) * (w i + v i) - |a i|) * p i ^ 2) :=
    IsSumSq.sum fun i _ ↦ SoS.isSumSq_C_mul (sub_nonneg.mpr (ha.2 i))
      (SoS.isSumSq_sq _)
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have heq : (2 / n : ℝ) * (B * n) = 2 * B := by field_simp
  have hsecond : IsSumSq (C (4 * B) * nsq ^ s - ∑ i, C |a i| * p i ^ 2) := by
    have hh := (SoS.isSumSq_C_mul (by positivity : (0 : ℝ) ≤ 2 / n)
      (hW'.add hG')).add hdom
    convert hh using 1
    rw [show 4 * B = (2 / n : ℝ) * (B * n) + (2 / n) * (B * n) by rw [heq]; ring]
    simp only [C_sub, C_mul, C_add, sub_mul, add_mul, mul_assoc,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have hcs := (SoSKit.weighted_cs a p).1
  have hbound : IsSumSq (C (A * (4 * B)) * nsq ^ s - (∑ i, C (a i) * p i) ^ 2) := by
    convert (SoS.isSumSq_C_mul
      (Finset.sum_nonneg fun i _ ↦ abs_nonneg (a i)) hsecond).add hcs using 1 <;>
      (simp only [C_mul, A]; ring)
  have hbudget : A * (4 * B) ≤ 16 * ε * B := by
    have hh := mul_le_mul_of_nonneg_right ha.1 (show 0 ≤ 4 * B by positivity)
    dsimp only [A]
    nlinarith only [hh, mul_nonneg he.1.le hB]
  have hid : (∑ i, C (a i) * p i) = weightedMoment w x s - empiricalMoment G x s := by
    have hvg : (∑ i, C (v i) * lin (x i) ^ s) = ∑ i ∈ G, lin (x i) ^ s := by
      simp [v, ite_mul]
    simp only [a, p, C_sub, C_mul, sub_mul, Finset.sum_sub_distrib,
      mul_assoc, ← Finset.mul_sum, hvs, hvg, weightedMoment, empiricalMoment]
  rw [hid] at hbound
  exact SoS.isSumSq_sub_trans hbound (sos_budget_mono hbudget s)

private theorem sos_subset (x : Fin n → Vec d) {S T : Finset (Fin n)}
    (h : S ⊆ T) (r : ℕ) :
    IsSumSq ((∑ i ∈ T, lin (x i) ^ (2 * r)) - ∑ i ∈ S, lin (x i) ^ (2 * r)) := by
  rw [← Finset.sum_sdiff h, add_sub_cancel_right]
  exact IsSumSq.sum fun i _ ↦ by
    rw [pow_mul']
    exact SoS.isSumSq_sq _

theorem reference_sum_bound (D : Reference n k d) (w θ : ℝ)
    (hD : D.Valid w) (r : ℕ) (hr : 1 ≤ r) (hres : D.Resilient (2 * r) θ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / w) • (1 : Mat d)))
    (hsize : (D.reference.card : ℝ) ≤ 2 * D.block.card) :
    IsSumSq (C (2 * momentBudget w r * D.block.card) * nsq ^ r -
      ∑ i ∈ D.reference, lin (D.clean i) ^ (2 * r)) := by
  have hR : 0 < (D.reference.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hB : 0 ≤ momentBudget w r := by
    dsimp only [momentBudget]
    have hw := hD.1.1
    positivity
  have hh := SoS.isSumSq_C_mul hR.le (reference_sos D w θ hD r hr hres hθ hm hc)
  have hh' : IsSumSq (C (momentBudget w r * D.reference.card) * nsq ^ r -
      ∑ i ∈ D.reference, lin (D.clean i) ^ (2 * r)) := by
    simpa only [empiricalMoment, mul_sub, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hR.ne', C_1, one_mul,
      mul_comm (D.reference.card : ℝ) (momentBudget w r)] using hh
  refine SoS.isSumSq_sub_trans hh' (sos_budget_mono ?_ r)
  nlinarith only [mul_le_mul_of_nonneg_left hsize hB]


/-- Three squared errors can be combined without changing their polynomial degree. -/
theorem three_errors {d : ℕ} (M G R P : RPoly d) (r : ℕ) (A B C₀ : ℝ)
    (h1 : IsSumSq (C A * nsq ^ r - (M - G) ^ 2))
    (h2 : IsSumSq (C B * nsq ^ r - (G - R) ^ 2))
    (h3 : IsSumSq (C C₀ * nsq ^ r - (R - P) ^ 2)) :
    IsSumSq (C (3 * A + 3 * B + 3 * C₀) * nsq ^ r - (M - P) ^ 2) := by
  have h := ((SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 3) h1).add
    (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 3) h2)).add
    (SoS.isSumSq_C_mul (by norm_num : (0 : ℝ) ≤ 3) h3)
  have hh := ((h.add (SoS.isSumSq_sq (M - G - (G - R)))).add
    (SoS.isSumSq_sq (M - G - (R - P)))).add
    (SoS.isSumSq_sq (G - R - (R - P)))
  convert hh using 1
  simp only [C_add, C_mul, map_ofNat]
  ring

private theorem image_filter {m n : ℕ} (e : Fin m ↪ Fin n) (R G : Finset (Fin n))
    (he : Finset.univ.image e = R) (hG : G ⊆ R) :
    (Finset.univ.filter fun i ↦ e i ∈ G).image e = G := by
  classical
  ext l
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hl
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (he.symm ▸ hG hl)
    exact ⟨i, hl, rfl⟩

theorem deletion_certificate (D : Reference n k d) (w θ ε : ℝ) (hD : D.Valid w)
    (he : D.contamination ≤ ε) (he8 : ε ≤ 1 / 8)
    (r : ℕ) (hr : 1 ≤ r) (hres : D.Resilient (2 * r) θ)
    (hθ : 0 ≤ θ ∧ θ ≤ 1 / 10000)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / w) • (1 : Mat d))) :
    IsSumSq (C (16 * ε * momentBudget w r) * nsq ^ r -
      (empiricalMoment D.good D.clean r - empiricalMoment D.reference D.clean r) ^ 2) := by
  classical
  obtain ⟨hε, _, _, hgood, _⟩ := reference_counts D w ε hD he he8
  let e : Fin D.reference.card ↪ Fin n := (D.reference.orderEmbOfFin rfl).toEmbedding
  have heR : Finset.univ.image e = D.reference :=
    D.reference.image_orderEmbOfFin_univ rfl
  let G := Finset.univ.filter fun i ↦ e i ∈ D.good
  have hG : G.image e = D.good := image_filter e _ _ heR hD.2.1
  have hcard : G.card = D.good.card := by
    have h := congrArg Finset.card hG
    simpa only [Finset.card_image_of_injective _ e.injective] using h
  let z := D.clean ∘ e
  have hsumG (s : ℕ) : (∑ i ∈ G, lin (z i) ^ s) =
      ∑ l ∈ D.good, lin (D.clean l) ^ s := by
    rw [← hG, Finset.sum_image (fun i _ j _ hij ↦ e.injective hij)]
    rfl
  have hsumR (s : ℕ) : (∑ i, lin (z i) ^ s) =
      ∑ l ∈ D.reference, lin (D.clean l) ^ s := by
    calc
      _ = ∑ l ∈ Finset.univ.image e, lin (D.clean l) ^ s := by
        rw [Finset.sum_image (fun i _ j _ hij ↦ e.injective hij)]
        rfl
      _ = _ := congrArg (fun T ↦ ∑ l ∈ T, lin (D.clean l) ^ s) heR
  have hR : 0 < (D.reference.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD.2.2.2.2.1
  have hB : 0 ≤ momentBudget w r := by
    unfold momentBudget
    have hw := hD.1.1
    positivity
  have hbound : IsSumSq (C (momentBudget w r * D.reference.card) * nsq ^ r -
      ∑ i, lin (z i) ^ (2 * r)) := by
    have h := SoS.isSumSq_C_mul hR.le (reference_sos D w θ hD r hr hres hθ hm hc)
    rw [hsumR]
    simpa only [empiricalMoment, mul_sub, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hR.ne', C_1, one_mul, mul_comm (D.reference.card : ℝ)] using h
  have hgoodBound : IsSumSq
      (C (momentBudget w r * D.reference.card) * nsq ^ r -
        ∑ i ∈ G, lin (z i) ^ (2 * r)) := by
    convert hbound.add (sos_subset z (Finset.subset_univ G) r) using 1
    ring
  let u : Fin D.reference.card → ℝ := fun i ↦ if i ∈ G then 1 else 0
  have hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1 := by intro i; dsimp [u]; split_ifs <;> norm_num
  have hmass : (1 - ε) * D.reference.card ≤ ∑ i, u i := by simpa [u, hcard] using hgood
  have hcomp := moment_cs_sharp z Finset.univ u ε (momentBudget w r) r
    ⟨hε, by linarith⟩ hB (by exact_mod_cast hR) hu
    (by
      simp only [Finset.card_univ, Fintype.card_fin]
      nlinarith only [mul_nonneg hε.le hR.le]) hmass (by simpa using hbound)
    (by simpa [u, ite_mul] using hgoodBound)
  have hWG : weightedMoment u z r = empiricalMoment D.good D.clean r := by
    simp only [weightedMoment, u, apply_ite C, C_1, C_0, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, hcard, hsumG, empiricalMoment]
  have hER : empiricalMoment Finset.univ z r = empiricalMoment D.reference D.clean r := by
    simp only [empiricalMoment, Finset.card_univ, Fintype.card_fin, hsumR]
  rwa [hWG, hER] at hcomp

theorem certified_transfer {m : ℕ} (D : Reference n k d) (z : Fin m → Vec d)
    (G : Finset (Fin m)) (u : Fin m → ℝ) (J : Finset ℕ) (w ε θ α : ℝ)
    (hD : D.Valid w) (he : D.contamination ≤ ε) (he8 : ε ≤ 1 / 8)
    (hres : D.Resilient (2 * J.sup id) θ) (hθ : 0 ≤ θ) (hθsmall : θ ≤ 1 / 100000000)
    (hm : ∀ j, sqnorm (D.model.mean j) ≤ 2 / w)
    (hc : ∀ j, LE (D.model.cov j) ((1.1 / w) • (1 : Mat d)))
    (hJ : ∀ r ∈ J, 1 ≤ r) (hmpos : 0 < m)
    (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    (hα : 0 < α ∧ α ≤ 1 / 4) (hαε : α ≤ 5 / 4 * ε)
    (hGmass : (1 - α) * m ≤ G.card) (humass : (1 - α) * m ≤ ∑ i, u i)
    (hGmom : ∀ r ∈ J, empiricalMoment G z r = empiricalMoment D.good D.clean r)
    (hGsos : ∀ r ∈ J, IsSumSq (C (2 * momentBudget w r * m) * nsq ^ r -
      ∑ i ∈ G, lin (z i) ^ (2 * r)))
    (husos : ∀ r ∈ J, IsSumSq (C (3 * momentBudget w r * m) * nsq ^ r -
      ∑ i, C (u i) * lin (z i) ^ (2 * r))) :
    Certified D.model (weightedMoment u z) J
      (fun r ↦ 250 * ε * momentBudget w r + 3 * θ ^ 2 * momentBudget w r) := by
  intro r hr
  have hB : 0 ≤ momentBudget w r := by
    unfold momentBudget
    have hw := hD.1.1
    positivity
  refine ⟨?_, ?_⟩
  · apply IsHomogeneous.C_mul
    exact IsHomogeneous.sum _ _ _ fun i _ ↦ by
      simpa only [one_mul] using ((homogeneous_lin (z i)).pow r).C_mul (u i)
  · have hG3 : IsSumSq (C (3 * momentBudget w r * m) * nsq ^ r -
        ∑ i ∈ G, lin (z i) ^ (2 * r)) := by
      exact SoS.isSumSq_sub_trans (hGsos r hr)
        (sos_budget_mono (by nlinarith [Nat.cast_nonneg (α := ℝ) m]) r)
    have h1 := moment_cs_sharp z G u α (3 * momentBudget w r) r hα
      (by positivity) hmpos hu hGmass humass hG3 (husos r hr)
    rw [hGmom r hr] at h1
    have hrmax : r ≤ J.sup id := Finset.le_sup (f := id) hr
    have h2 := deletion_certificate D w θ ε hD he he8 r (hJ r hr)
      (resilient_mono D hres (by omega) hθ) ⟨hθ, by linarith⟩ hm hc
    have h3 := reference_error_square D w θ hD r
      (resilient_mono D hres (by omega) hθ) hθ hm hc
    have hh := three_errors (weightedMoment u z r) (empiricalMoment D.good D.clean r)
      (empiricalMoment D.reference D.clean r) (populationMoment D.model r) r
      (16 * α * (3 * momentBudget w r)) (16 * ε * momentBudget w r)
      (θ ^ 2 * (2 / w) ^ r) h1 h2 h3
    have hpow : (2 / w) ^ r ≤ momentBudget w r := by
      have hw := hD.1.1
      have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hJ r hr
      have h : (2 / w) ^ r ≤ (20 * r / w) ^ r := by
        apply pow_le_pow_left₀ (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) hw.le
      unfold momentBudget
      linarith only [h, pow_nonneg (by positivity : 0 ≤ 20 * r / w) r]
    apply SoS.isSumSq_sub_trans hh
    apply sos_budget_mono
    have hαB := mul_le_mul_of_nonneg_right hαε hB
    have hε : 0 ≤ ε := by linarith only [hα.1, hαε]
    have hεB := mul_nonneg hε hB
    have hθB := mul_le_mul_of_nonneg_left hpow (sq_nonneg θ)
    nlinarith only [hαB, hεB, hθB]

end

end ABBKS26.Assembly.Exec.MomentAnalytic
