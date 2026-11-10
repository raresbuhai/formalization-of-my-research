module

public import ABBKS26.IdCov.IdentAux

/-!
# Identifiability for identical covariances

[ABBKS26, Lemmas 6.8 and 6.9]: in sum-of-squares, a solution of the moment system has small
energy on the means, so its projection on the span of the large-variance directions is small.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
open Finset IdentAux
variable {k d : ℕ}

def NormLedger (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (π ε W : ℝ) : Prop :=
  64 * (d + 1 : ℝ) ^ 2 * t ≤ W ∧ 4 / π ≤ W ∧ 1 / ε ≤ W ∧
    (∀ s, 1 ≤ s → s ≤ 2 * t → SoS.coeffNorm1 (M (2 * s)) ≤ W ^ (2 * s)) ∧
    (∀ r, r ≤ 4 * t → SoS.coeffNorm1 (moment D r) ≤ W ^ (2 * r))

private theorem deviation_core
    (D : Data k d) (π γ ε W : ℝ) (t s : ℕ)
    (hD : D.Valid π γ) (ht : 2 ≤ t) (hs : 2 ≤ s ∧ s ≤ 2 * t)
    (he : 0 < ε ∧ ε ≤ 1) (hW : NormLedger D (moment D) t π ε W) :
    SoS.DerivesNq (system (moment D) t ε) (4 * s) (16 * W ^ (10 * s)) 1
      (C (K s ^ 2 * (1 + γ) ^ (2 * s) * ε) * nsq ^ (2 * s) -
        (powerMoment D (2 * s) - C (alpha s) * Q D ^ s) ^ 2) := by
  have hb := size_bounds ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hW0 : 0 ≤ W := by linarith
  have hc := coefficient_bounds ht hs.2 hW.1
  have hl : 1 ≤ 1 + γ := by linarith [hD.2.1.1]
  have hlW : 1 + γ ≤ W := by linarith [hD.2.2, hb.1]
  have hN : IsSumSq (nsq : RPoly d) := IsSumSq.sum_sq _ _
  have hS := (sos_bounds D π γ hD).1
  have hSn := (quadratic_norms D π γ hD).1.trans hb.2.2.1
  have hNd := nsq_degree (d := d)
  have hSd : (S D).totalDegree ≤ 2 := quad_degree D.cov
  let Z : ℕ → RPoly d := fun j ↦ S D ^ j * dev (moment D) (s - j)
  have hZ (j : ℕ) (hj : j ∈ range (s - 1)) :
      (Z j).totalDegree ≤ 2 * s ∧ SoS.coeffNorm1 (Z j) ≤ 2 * W ^ (4 * s) := by
    have hj' := mem_range.mp hj
    have hu : s - j ≤ 2 * t := by omega
    have hn := dev_norm D hD ht hu hW.1 (by
      simpa only [show 4 * (s - j) = 2 * (2 * (s - j)) by omega] using
        hW.2.2.2.2 (2 * (s - j)) (by omega))
    constructor
    · have hd := (homogeneity D 0 (s - j)).2.totalDegree_le
      change (S D ^ j * dev (moment D) (s - j)).totalDegree ≤ 2 * s
      have hp : (S D ^ j).totalDegree ≤ 2 * j :=
        (totalDegree_pow _ _).trans (by nlinarith)
      exact (totalDegree_mul _ _).trans (by omega)
    · calc SoS.coeffNorm1 (Z j) ≤ W ^ j * (2 * W ^ (4 * (s - j))) :=
            norm_mul (norm_pow hSn j) hn
        _ = 2 * W ^ (j + 4 * (s - j)) := by rw [pow_add]; ring
        _ ≤ 2 * W ^ (4 * s) := by
          exact mul_le_mul_of_nonneg_left
            (SoS.pow_le_pow_of_two_le hW2 (by omega)) (by norm_num)
  let E : RPoly d := C ((1 + γ) ^ (2 * s) * ε) * nsq ^ (2 * s)
  have hterm (j : ℕ) (hj : j ∈ range (s - 1)) :
      SoS.DerivesNq (system (moment D) t ε) (4 * s) (3 * W ^ (4 * s)) 1
        (E - Z j ^ 2) := by
    have hj' := mem_range.mp hj
    let u := s - j
    have hu : 2 ≤ u ∧ u ≤ 2 * t := by dsimp [u]; omega
    have hsum : u + j = s := by dsimp [u]; omega
    let B : RPoly d := C ((1 + γ) ^ (2 * s)) * nsq ^ (2 * j) - S D ^ (2 * j)
    let T : RPoly d := C ε * nsq ^ (2 * u) * B
    have hB : IsSumSq B := by
      have hp := SoSKit.powers (S D) (C (1 + γ) * nsq) hS
        ((SoS.isSumSq_C (by linarith : 0 ≤ 1 + γ)).mul hN)
        (sos_bounds D π γ hD).2.2.1 (2 * j)
      have hdiff : 0 ≤ (1 + γ) ^ (2 * s) - (1 + γ) ^ (2 * j) :=
        sub_nonneg.mpr (pow_le_pow_right₀ hl (by omega))
      convert (SoS.isSumSq_C_mul hdiff (SoS.isSumSq_pow hN (2 * j))).add hp using 1
      simp only [B, mul_pow, C_pow, C_sub]
      ring
    have hT : IsSumSq T :=
      ((SoS.isSumSq_C he.1.le).mul (SoS.isSumSq_pow hN (2 * u))).mul hB
    have hBd : B.totalDegree ≤ 4 * j := by
      apply (totalDegree_sub _ _).trans
      apply max_le
      · exact (totalDegree_mul _ _).trans (by
          rw [totalDegree_C, zero_add]
          exact (totalDegree_pow _ _).trans (by nlinarith))
      · exact (totalDegree_pow _ _).trans (by nlinarith)
    have hTd : T.totalDegree ≤ 4 * s := by
      have hd : (C ε * (nsq : RPoly d) ^ (2 * u)).totalDegree ≤ 4 * u :=
        (totalDegree_mul _ _).trans (by
          rw [totalDegree_C, zero_add]
          exact (totalDegree_pow _ _).trans (by nlinarith))
      exact (totalDegree_mul _ _).trans (by omega)
    have hBn : SoS.coeffNorm1 B ≤ 2 * W ^ (2 * s + 2 * j) := by
      have hn : SoS.coeffNorm1 (C ((1 + γ) ^ (2 * s)) *
          (nsq : RPoly d) ^ (2 * j)) ≤ W ^ (2 * s + 2 * j) := by
        rw [SoS.coeffNorm1_C_mul, abs_of_nonneg (by positivity)]
        exact (mul_le_mul (pow_le_pow_left₀ (by linarith) hlW _)
          (norm_pow (norm_nsq.trans hb.2.1) _) (SoS.coeffNorm1_nonneg _)
          (by positivity)).trans_eq (pow_add _ _ _).symm
      have hn' : SoS.coeffNorm1 (S D ^ (2 * j)) ≤ W ^ (2 * s + 2 * j) :=
        (norm_pow hSn _).trans (SoS.pow_le_pow_of_two_le hW2 (by omega))
      exact (SoS.coeffNorm1_sub_le _ _).trans (by linarith)
    have hTn : SoS.coeffNorm1 T ≤ 2 * W ^ (4 * s) := by
      have hn : SoS.coeffNorm1 (C ε * (nsq : RPoly d) ^ (2 * u)) ≤ W ^ (2 * u) := by
        rw [SoS.coeffNorm1_C_mul, abs_of_pos he.1]
        exact (mul_le_mul he.2 (norm_pow (norm_nsq.trans hb.2.1) _)
          (SoS.coeffNorm1_nonneg _) zero_le_one).trans_eq (one_mul _)
      calc SoS.coeffNorm1 T ≤ W ^ (2 * u) * (2 * W ^ (2 * s + 2 * j)) :=
            norm_mul hn hBn
        _ = 2 * W ^ (4 * s) := by
          rw [mul_left_comm, ← pow_add, show 2 * u + (2 * s + 2 * j) = 4 * s by omega]
    have hfd : (constraint (moment D) ε u).totalDegree ≤ 4 * u := by
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_mul _ _).trans (by
          rw [totalDegree_C, zero_add]
          exact (totalDegree_pow _ _).trans (by nlinarith))
      · exact (totalDegree_pow _ _).trans (by
          have := (homogeneity D 0 u).2.totalDegree_le
          omega)
    have hmult := (constraint_derives (moment D) t u ε hu hfd).mulSOS
      (s := S D ^ (2 * j))
      (by simpa only [SoS.IsSOS, SoS.toReal_real] using SoS.isSumSq_pow hS (2 * j))
    have hmult' : SoS.DerivesNq (system (moment D) t ε) (4 * s)
        (W ^ (4 * s)) 1 (S D ^ (2 * j) * constraint (moment D) ε u) := by
      apply hmult.mono
      · have hd := totalDegree_pow (S D) (2 * j)
        nlinarith
      · simpa using (norm_pow hSn (2 * j)).trans
          (SoS.pow_le_pow_of_two_le hW2 (by omega))
    have hp := hmult'.add (SoS.DerivesNq.ofIsSOS _
      (by simpa only [SoS.IsSOS, SoS.toReal_real] using hT) hTd hTn)
    convert hp.congr ?_ using 1
    · ring
    · dsimp [E, Z, T, B, constraint]
      rw [show 2 * s = 2 * u + 2 * j by omega, pow_add]
      simp only [C_mul, mul_pow, ← pow_mul]
      ring
  have hcs := range_cs s Z
  let F : RPoly d := C (K s) *
    (∑ j ∈ range (s - 1), C (hermCoeff (2 * s) j : ℝ) * Z j ^ 2) -
    (∑ j ∈ range (s - 1),
      C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) * Z j) ^ 2
  have hFd : F.totalDegree ≤ 4 * s := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply (totalDegree_mul _ _).trans
      rw [totalDegree_C, zero_add]
      exact totalDegree_finsetSum_le fun j hj ↦ (totalDegree_mul _ _).trans (by
        rw [totalDegree_C, zero_add]
        exact (totalDegree_pow _ _).trans (by have := (hZ j hj).1; omega))
    · apply (totalDegree_pow _ _).trans
      have hd : (∑ j ∈ range (s - 1),
          C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) * Z j).totalDegree ≤ 2 * s :=
        totalDegree_finsetSum_le fun j hj ↦ (totalDegree_mul _ _).trans (by
          rw [totalDegree_C, zero_add]; exact (hZ j hj).1)
      omega
  have hFn : SoS.coeffNorm1 F ≤ 8 * W ^ (10 * s) := by
    have hn : (∑ j ∈ range (s - 1), (hermCoeff (2 * s) j : ℝ) *
        SoS.coeffNorm1 (Z j) ^ 2) ≤ K s * (2 * W ^ (4 * s)) ^ 2 := by
      rw [K, sum_mul]
      exact sum_le_sum fun j hj ↦ mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) (hZ j hj).2 2) (by positivity)
    calc SoS.coeffNorm1 F ≤ 2 * K s * (K s * (2 * W ^ (4 * s)) ^ 2) :=
          hcs.2.trans (mul_le_mul_of_nonneg_left hn (mul_nonneg (by norm_num) hc.1))
      _ = 8 * K s ^ 2 * W ^ (8 * s) := by rw [mul_pow, ← pow_mul]; ring
      _ ≤ 8 * (W ^ s) ^ 2 * W ^ (8 * s) := by
          gcongr
          · exact hc.1
          · exact hc.2.1
      _ = 8 * W ^ (10 * s) := by rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; omega
  have hsum := SoS.DerivesNq.sum (range (s - 1)) fun j hj ↦
    (hterm j hj).smul (mul_nonneg hc.1 (Nat.cast_nonneg (hermCoeff (2 * s) j)))
  have hsum' := hsum.mono le_rfl (show
      (∑ j ∈ range (s - 1), K s * (hermCoeff (2 * s) j : ℝ) *
        (3 * W ^ (4 * s))) ≤ 3 * W ^ (6 * s) by
    calc _ = 3 * K s ^ 2 * W ^ (4 * s) := by
          rw [← sum_mul, ← mul_sum, ← K]; ring
      _ ≤ 3 * (W ^ s) ^ 2 * W ^ (4 * s) := by
          gcongr
          · exact hc.1
          · exact hc.2.1
      _ = _ := by rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; omega)
  have hproof := hsum'.add (SoS.DerivesNq.ofIsSOS _
    (by simpa only [SoS.IsSOS, SoS.toReal_real] using hcs.1) hFd hFn)
  have hnorm : 3 * W ^ (6 * s) + 8 * W ^ (10 * s) ≤ 16 * W ^ (10 * s) := by
    have hpow := SoS.pow_le_pow_of_two_le hW2 (show 6 * s ≤ 10 * s by omega)
    nlinarith [pow_nonneg hW0 (10 * s)]
  apply (hproof.mono le_rfl hnorm).congr
  rw [deviation_identity D hD.1.2.2.1 s]
  dsimp [F, E]
  have hcoeff : (∑ j ∈ range (s - 1), C (hermCoeff (2 * s) j : ℝ)) =
      (C (K s) : RPoly d) := by rw [← map_sum]; rfl
  simp only [C_mul, C_pow, mul_sum, mul_sub, sum_sub_distrib, ← sum_mul]
  rw [← mul_sum, hcoeff]
  simp only [Z, mul_assoc]
  ring


private theorem mismatch_norm
    (D : Data k d) (π γ ε W : ℝ) (t s : ℕ)
    (hD : D.Valid π γ) (ht : 2 ≤ t) (hs : s ≤ 2 * t)
    (hW : NormLedger D (moment D) t π ε W) :
    SoS.coeffNorm1 (powerMoment D (2 * s) - C (alpha s) * Q D ^ s) ≤
      2 * W ^ (5 * s) := by
  have hb := size_bounds ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hSn := (quadratic_norms D π γ hD).1.trans hb.2.2.1
  have hK := coefficient_bounds ht hs hW.1
  rw [deviation_identity D hD.1.2.2.1 s]
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ range (s - 1),
        (hermCoeff (2 * s) j : ℝ) * (2 * W ^ (4 * s)) := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_range.mp hj
      have hn := dev_norm D hD ht (show s - j ≤ 2 * t by omega) hW.1 (by
        simpa only [show 4 * (s - j) = 2 * (2 * (s - j)) by omega] using
          hW.2.2.2.2 (2 * (s - j)) (by omega))
      rw [mul_assoc, SoS.coeffNorm1_C_mul, abs_mul, abs_pow, abs_neg,
        abs_one, one_pow, one_mul, Nat.abs_cast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ W ^ j * (2 * W ^ (4 * (s - j))) := norm_mul (norm_pow hSn j) hn
        _ = 2 * W ^ (j + 4 * (s - j)) := by rw [pow_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (SoS.pow_le_pow_of_two_le hW2 (by omega)) (by norm_num)
    _ = K s * (2 * W ^ (4 * s)) := by rw [← sum_mul]; rfl
    _ ≤ W ^ s * (2 * W ^ (4 * s)) := by gcongr; exact hK.2.1
    _ = _ := by rw [mul_left_comm, ← pow_add]; congr 2; omega

private theorem mismatch_bounds_core
    (D : Data k d) (π γ ε W : ℝ) (t : ℕ) (hD : D.Valid π γ)
    (ht : 2 ≤ t) (he : 0 < ε ∧ ε ≤ 1) (hW : NormLedger D (moment D) t π ε W) :
    SoS.DerivesNq (system (moment D) t ε) (4 * t) (W ^ (22 * t)) 1
      (C (K t ^ 2 * (1 + γ) ^ (2 * t) * ε) -
        (powerMoment D (2 * t) - C (alpha t) * Q D ^ t) ^ 2) ∧
    SoS.DerivesNq (system (moment D) t ε) (8 * t) (W ^ (22 * t)) 1
      (powerMoment D (4 * t) - C (alpha (2 * t)) * Q D ^ (2 * t) +
        C (K (2 * t) * (1 + γ) ^ (2 * t) * Real.sqrt ε)) := by
  have hb := size_bounds ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hW0 : 0 ≤ W := by linarith
  have hl : 1 ≤ 1 + γ := by linarith [hD.2.1.1]
  have hlW : 1 + γ ≤ W := by linarith [hD.2.2, hb.1]
  have hdW : (d + 1 : ℝ) ≤ W := by nlinarith [hb.2.1]
  have hball : 1 - (nsq : RPoly d) ∈ system (moment D) t ε := by simp [system]
  have hdehom (s : ℕ) (hs : 2 ≤ s ∧ s ≤ 2 * t) :
      SoS.DerivesNq (system (moment D) t ε) (4 * s) (17 * W ^ (10 * s)) 1
        (C (K s ^ 2 * (1 + γ) ^ (2 * s) * ε) -
          (powerMoment D (2 * s) - C (alpha s) * Q D ^ s) ^ 2) := by
    have hK := coefficient_bounds ht hs.2 hW.1
    have h := (deviation_core D π γ ε W t s hD ht hs he hW).dehomogenize hball
      (mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) he.1.le)
    apply h.mono (by omega)
    have hn : K s ^ 2 * (1 + γ) ^ (2 * s) * ε * (d + 1 : ℝ) ^ (2 * s) ≤
        W ^ (10 * s) := by
      calc _ ≤ (W ^ s) ^ 2 * W ^ (2 * s) * 1 * W ^ (2 * s) := by
            have hK0 := hK.1
            have hKle := hK.2.1
            have hε0 := he.1.le
            gcongr
            exact he.2
        _ = W ^ (6 * s) := by simp only [mul_one, ← pow_mul, ← pow_add];
                                 congr 2; omega
        _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
    simpa only [Fintype.card_fin] using (show
      16 * W ^ (10 * s) + K s ^ 2 * (1 + γ) ^ (2 * s) * ε *
        (d + 1 : ℝ) ^ (2 * s) ≤ 17 * W ^ (10 * s) by linarith)
  constructor
  · apply (hdehom t ⟨ht, by omega⟩).mono le_rfl
    calc 17 * W ^ (10 * t) ≤ W * W ^ (10 * t) := by gcongr; linarith [hb.1]
      _ = W ^ (10 * t + 1) := by rw [pow_succ]; ring
      _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
  · let e := K (2 * t) * (1 + γ) ^ (2 * t) * Real.sqrt ε
    have hK := coefficient_bounds ht (le_refl (2 * t)) hW.1
    have he0 : 0 < e := mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one
      (K_one_le (by omega))) (pow_pos (by linarith) _)) (Real.sqrt_pos.mpr he.1)
    have heW : e ≤ W ^ (4 * t) := by
      have hs : Real.sqrt ε ≤ 1 := (Real.sqrt_le_one).mpr he.2
      calc e ≤ W ^ (2 * t) * W ^ (2 * t) * 1 := by
            dsimp [e]; gcongr; exact hK.2.1
        _ = _ := by rw [mul_one, ← pow_add]; congr 2; omega
    have heε : ε ≤ e := by
      have hs : ε ≤ Real.sqrt ε :=
        (Real.le_sqrt he.1.le he.1.le).mpr (by nlinarith : ε ^ 2 ≤ ε)
      have hp : 1 ≤ K (2 * t) * (1 + γ) ^ (2 * t) :=
        one_le_mul_of_one_le_of_one_le (K_one_le (by omega)) (one_le_pow₀ hl)
      exact hs.trans (le_mul_of_one_le_left (Real.sqrt_nonneg _) hp)
    have hinv : 1 / (2 * e) ≤ W := by
      exact (one_div_le_one_div_of_le he.1 (by linarith)).trans hW.2.2.1
    have heq : e ^ 2 = K (2 * t) ^ 2 * (1 + γ) ^ (2 * (2 * t)) * ε := by
      dsimp [e]
      rw [mul_pow, mul_pow, Real.sq_sqrt he.1.le, ← pow_mul]
      rw [show 2 * t * 2 = 2 * (2 * t) by omega]
    have h : SoS.DerivesNq (system (moment D) t ε) (4 * (2 * t))
        (17 * W ^ (10 * (2 * t))) 1
        (C (e ^ 2) - (powerMoment D (2 * (2 * t)) -
          C (alpha (2 * t)) * Q D ^ (2 * t)) ^ 2) := by
      rw [heq]
      exact hdehom (2 * t) ⟨by omega, le_rfl⟩
    have hroot := h.sqrt_add he0
    have hYn := mismatch_norm D π γ ε W t (2 * t) hD ht le_rfl hW
    have hnum : (SoS.coeffNorm1 (powerMoment D (2 * (2 * t)) -
        C (alpha (2 * t)) * Q D ^ (2 * t)) + e) ^ 2 ≤ 9 * W ^ (20 * t) := by
      have hep : e ≤ W ^ (10 * t) := heW.trans
        (SoS.pow_le_pow_of_two_le hW2 (by omega))
      have hsum : SoS.coeffNorm1 (powerMoment D (2 * (2 * t)) -
          C (alpha (2 * t)) * Q D ^ (2 * t)) + e ≤ 3 * W ^ (10 * t) := by
        rw [show 5 * (2 * t) = 10 * t by omega] at hYn
        linarith
      calc
        _ ≤ (3 * W ^ (10 * t)) ^ 2 := by
          exact pow_le_pow_left₀ (add_nonneg (SoS.coeffNorm1_nonneg _) he0.le) hsum 2
        _ = _ := by
          rw [mul_pow, ← pow_mul, show 10 * t * 2 = 20 * t by omega]
          norm_num
    have hnorm : (17 * W ^ (10 * (2 * t)) +
        (SoS.coeffNorm1 (powerMoment D (2 * (2 * t)) -
          C (alpha (2 * t)) * Q D ^ (2 * t)) + e) ^ 2) / (2 * e) ≤ W ^ (22 * t) := by
      calc _ ≤ (26 * W ^ (20 * t)) * W := by
            rw [div_eq_mul_one_div]
            apply mul_le_mul _ hinv (by positivity) (by positivity)
            rw [show 10 * (2 * t) = 20 * t by omega]
            linarith
        _ ≤ W * W ^ (20 * t) * W := by gcongr; linarith [hb.1]
        _ = W ^ (20 * t + 2) := by rw [pow_add, pow_two]; ring
        _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
    have hd := mismatch_degree D (2 * t)
    have hdegree : max (4 * (2 * t)) (2 *
        (powerMoment D (2 * (2 * t)) - C (alpha (2 * t)) * Q D ^ (2 * t)).totalDegree)
        ≤ 8 * t := by omega
    have hout := (hroot.mono hdegree hnorm).congr
      (show C e + (powerMoment D (2 * (2 * t)) -
        C (alpha (2 * t)) * Q D ^ (2 * t)) =
        powerMoment D (2 * (2 * t)) - C (alpha (2 * t)) * Q D ^ (2 * t) + C e by ring)
    simpa only [show 2 * (2 * t) = 4 * t by omega] using hout


private theorem powerMoment_norm
    (D : Data k d) (π γ ε W : ℝ) (t s : ℕ)
    (hD : D.Valid π γ) (ht : 2 ≤ t) (hs : s ≤ 2 * t)
    (hW : NormLedger D (moment D) t π ε W) :
    SoS.coeffNorm1 (powerMoment D (2 * s)) ≤ 3 * W ^ (5 * s) := by
  have hb := size_bounds ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hn := mismatch_norm D π γ ε W t s hD ht hs hW
  have hK := coefficient_bounds ht hs hW.1
  have hq := (quadratic_norms D π γ hD).2.trans hb.2.2.1
  have hg : SoS.coeffNorm1 (C (alpha s) * Q D ^ s) ≤ W ^ (5 * s) := by
    rw [SoS.coeffNorm1_C_mul, abs_of_pos hK.2.2.1]
    calc _ ≤ W ^ s * W ^ s := mul_le_mul hK.2.2.2 (norm_pow hq s)
            (SoS.coeffNorm1_nonneg _) (by positivity)
      _ = W ^ (2 * s) := by rw [← pow_add]; congr 2; omega
      _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
  have h := SoS.coeffNorm1_add_le
    (powerMoment D (2 * s) - C (alpha s) * Q D ^ s) (C (alpha s) * Q D ^ s)
  rw [sub_add_cancel] at h
  linarith

private theorem mismatch_sos_core
    (D : Data k d) (π γ ε W : ℝ) (t : ℕ) (hD : D.Valid π γ)
    (ht : 2 ≤ t) (hp : 2 ≤ π * 2 ^ (t - 1)) (he : 0 < ε ∧ ε ≤ π ^ 2)
    (hW : NormLedger D (moment D) t π ε W) :
    SoS.DerivesNq (system (moment D) t ε) (8 * t) (W ^ (24 * t)) 1
      (C ((4 : ℝ) * 512 ^ t * (t : ℝ) ^ (2 * t) * Real.sqrt ε) - Q D ^ (2 * t)) := by
  have hb := size_bounds ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hW0 : 0 ≤ W := by linarith
  have hπ : 0 < π := hD.1.1
  have hπ1 := pi_le_one D hD
  have hγ0 : 0 ≤ γ := hD.2.1.1
  have he1 : ε ≤ 1 := he.2.trans (pow_le_one₀ hπ.le hπ1)
  have hK := coefficient_bounds ht (show t ≤ 2 * t by omega) hW.1
  have hK2 := coefficient_bounds ht (le_refl (2 * t)) hW.1
  let κ := π * alpha (2 * t) - 2 * alpha t ^ 2
  let e₁ := K t ^ 2 * (1 + γ) ^ (2 * t) * ε
  let e₂ := K (2 * t) * (1 + γ) ^ (2 * t) * Real.sqrt ε
  let B := (4 : ℝ) * 512 ^ t * (t : ℝ) ^ (2 * t) * Real.sqrt ε
  let a := (π * e₂ + 2 * e₁) / κ
  have hgap : (2 : ℝ) ^ t * alpha t ^ 2 ≤ alpha (2 * t) := by
    simpa only [alpha, show 2 * (2 * t) = 4 * t by omega,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr (doubleFactorial_gap t)
  have hp4 : 4 ≤ π * (2 : ℝ) ^ t := by
    rw [show t = (t - 1) + 1 by omega, pow_succ]
    nlinarith [hp]
  have hfour : 4 * alpha t ^ 2 ≤ π * alpha (2 * t) := by
    calc _ ≤ (π * 2 ^ t) * alpha t ^ 2 :=
          mul_le_mul_of_nonneg_right hp4 (sq_nonneg _)
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgap hπ.le
  have hκ : 1 ≤ κ := by
    have ha := alpha_one_le t
    dsimp [κ]
    nlinarith
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hB : a ≤ B := by
    have h := mismatch_constant t π ε (1 + γ) ht hπ hp he
      ⟨by linarith [hD.2.1.1], by linarith [hD.2.2]⟩
    dsimp [a, e₁, e₂, κ, B]
    convert h using 1; ring
  have ha0 : 0 ≤ a := by
    have he₁ : 0 ≤ e₁ := mul_nonneg (mul_nonneg (sq_nonneg _)
      (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + γ) _)) he.1.le
    have he₂ : 0 ≤ e₂ := mul_nonneg (mul_nonneg hK2.1
      (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 + γ) _))
      (Real.sqrt_nonneg _)
    exact div_nonneg (add_nonneg (mul_nonneg hπ.le he₂) (by positivity)) hκ0.le
  have hBn : B ≤ W ^ (5 * t) := by
    have htW : (t : ℝ) ≤ W := by linarith [hb.2.2.2]
    have h512 : (512 : ℝ) ≤ W ^ 2 := by nlinarith [hb.1]
    have hsqrt : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr he1
    calc B ≤ W ^ t * (W ^ 2) ^ t * W ^ (2 * t) * 1 := by
          dsimp [B]
          gcongr
          exact (by linarith [hb.1] : (4 : ℝ) ≤ W).trans
            (SoS.le_pow_of_two_le hW2 (by omega))
      _ = _ := by simp only [mul_one, ← pow_mul, ← pow_add]; congr 2; omega
  let U := powerMoment D (2 * t)
  let V := powerMoment D (4 * t)
  let R : RPoly d := U ^ 2 - C π * V + (2 * C (alpha t) * Q D ^ t - U) ^ 2
  have hR : IsSumSq R := (discrete_mismatch D π hπ.le (hD.1.2.1) t).add
    (SoS.isSumSq_sq _)
  have hUn := powerMoment_norm D π γ ε W t t hD ht (by omega) hW
  have hVn : SoS.coeffNorm1 V ≤ 3 * W ^ (10 * t) := by
    simpa only [V, show 4 * t = 2 * (2 * t) by omega,
      show 5 * (2 * t) = 10 * t by omega] using
      powerMoment_norm D π γ ε W t (2 * t) hD ht le_rfl hW
  have hQn := (quadratic_norms D π γ hD).2.trans hb.2.2.1
  have hAn : SoS.coeffNorm1 (C (alpha t) * Q D ^ t) ≤ W ^ (5 * t) := by
    rw [SoS.coeffNorm1_C_mul, abs_of_pos hK.2.2.1]
    calc _ ≤ W ^ t * W ^ t := mul_le_mul hK.2.2.2 (norm_pow hQn t)
            (SoS.coeffNorm1_nonneg _) (by positivity)
      _ = W ^ (2 * t) := by rw [← pow_add]; congr 2; omega
      _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
  have hRn : SoS.coeffNorm1 R ≤ W ^ (10 * t + 1) := by
    have hsq : SoS.coeffNorm1 (U ^ 2) ≤ 9 * W ^ (10 * t) := by
      calc _ ≤ (3 * W ^ (5 * t)) ^ 2 := norm_pow hUn 2
        _ = _ := by
          rw [mul_pow, ← pow_mul, show 5 * t * 2 = 10 * t by omega]
          norm_num
    have hπV : SoS.coeffNorm1 (C π * V) ≤ 3 * W ^ (10 * t) := by
      rw [SoS.coeffNorm1_C_mul, abs_of_pos hπ]
      exact (mul_le_mul hπ1 hVn (SoS.coeffNorm1_nonneg _) zero_le_one).trans_eq
        (one_mul _)
    have hlin : SoS.coeffNorm1 (2 * C (alpha t) * Q D ^ t - U) ≤
        5 * W ^ (5 * t) := by
      have htwo : SoS.coeffNorm1 (2 * C (alpha t) * Q D ^ t) ≤ 2 * W ^ (5 * t) := by
        rw [mul_assoc, ← map_ofNat (C : ℝ →+* RPoly d) 2,
          SoS.coeffNorm1_C_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left hAn (by norm_num)
      exact (SoS.coeffNorm1_sub_le _ _).trans (by linarith)
    have hlin2 : SoS.coeffNorm1 ((2 * C (alpha t) * Q D ^ t - U) ^ 2) ≤
        25 * W ^ (10 * t) := by
      calc _ ≤ (5 * W ^ (5 * t)) ^ 2 := norm_pow hlin 2
        _ = _ := by
          rw [mul_pow, ← pow_mul, show 5 * t * 2 = 10 * t by omega]
          norm_num
    have hn := (SoS.coeffNorm1_add_le (U ^ 2 - C π * V)
      ((2 * C (alpha t) * Q D ^ t - U) ^ 2)).trans
      (add_le_add (SoS.coeffNorm1_sub_le _ _) le_rfl)
    calc _ ≤ 37 * W ^ (10 * t) := by dsimp [R]; linarith
      _ ≤ W * W ^ (10 * t) := by gcongr; linarith [hb.1]
      _ = _ := by rw [pow_succ]; ring
  have hRd : R.totalDegree ≤ 8 * t := by
    have hUd : U.totalDegree ≤ 2 * t := powerMoment_degree D _
    have hVd : V.totalDegree ≤ 4 * t := powerMoment_degree D _
    have hQd : (Q D).totalDegree ≤ 2 := quad_degree (between D)
    have hAd : (2 * C (alpha t) * Q D ^ t).totalDegree ≤ 2 * t := by
      have hC : (2 * C (alpha t) : RPoly d).totalDegree = 0 := by
        rw [← map_ofNat (C : ℝ →+* RPoly d) 2, ← C_mul, totalDegree_C]
      exact (totalDegree_mul _ _).trans (by
        rw [hC, zero_add]
        exact (totalDegree_pow _ _).trans (by nlinarith))
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_sub _ _).trans (max_le
        ((totalDegree_pow _ _).trans (by omega))
        ((totalDegree_mul _ _).trans (by rw [totalDegree_C]; omega)))
    · exact (totalDegree_pow _ _).trans (by
        have := totalDegree_sub (2 * C (alpha t) * Q D ^ t) U
        omega)
  have hm := mismatch_bounds_core D π γ ε W t hD ht ⟨he.1, he1⟩ hW
  have hE1 := hm.1.mono (show 4 * t ≤ 8 * t by omega) le_rfl
  have hproof := ((hm.2.smul hπ.le).add
    (hE1.smul (by norm_num : (0 : ℝ) ≤ 2))).add
      (SoS.DerivesNq.ofIsSOS _ (by simpa only [SoS.IsSOS, SoS.toReal_real] using hR) hRd hRn)
  have hnorm : π * W ^ (22 * t) + 2 * W ^ (22 * t) + W ^ (10 * t + 1) ≤
      W ^ (22 * t + 1) := by
    have hpow := SoS.pow_le_pow_of_two_le hW2 (show 10 * t + 1 ≤ 22 * t by omega)
    rw [pow_succ W (22 * t)]
    have hπpow := mul_le_mul_of_nonneg_right hπ1 (pow_nonneg hW0 (22 * t))
    nlinarith [pow_nonneg hW0 (22 * t)]
  have hidentity : C π * (V - C (alpha (2 * t)) * Q D ^ (2 * t) + C e₂) +
      C 2 * (C e₁ - (U - C (alpha t) * Q D ^ t) ^ 2) + R =
      C κ * (C a - Q D ^ (2 * t)) := by
    have hκa : κ * a = π * e₂ + 2 * e₁ := by
      dsimp [a]; exact mul_div_cancel₀ _ hκ0.ne'
    have hcκa := congrArg (C : ℝ →+* RPoly d) hκa
    dsimp [κ] at hcκa
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat] at hcκa
    dsimp [R, κ]
    simp only [C_sub, C_mul, C_pow, map_ofNat]
    rw [show Q D ^ (2 * t) = (Q D ^ t) ^ 2 by
      rw [← pow_mul]; congr 1; omega]
    linear_combination -hcκa
  have hscaled := ((hproof.mono le_rfl hnorm).congr hidentity).smul
    (show 0 ≤ κ⁻¹ by positivity)
  have hcκ : (C κ⁻¹ * C κ : RPoly d) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hκ0.ne', C_1]
  have haProof := hscaled.congr (by rw [← mul_assoc, hcκ, one_mul])
  have haProof' : SoS.DerivesNq (system (moment D) t ε) (8 * t)
      (W ^ (22 * t + 1)) 1 (C a - Q D ^ (2 * t)) := by
    apply haProof.mono le_rfl
    exact mul_le_of_le_one_left (by positivity) ((inv_le_one₀ hκ0).mpr hκ)
  have hconst := SoS.DerivesNq.ofIsSOS (q := 1) (system (moment D) t ε)
    (SoS.IsSOS.const (sub_nonneg.mpr hB))
    (show (C (B - a) : RPoly d).totalDegree ≤ 8 * t by rw [totalDegree_C]; omega)
    (show SoS.coeffNorm1 (C (B - a) : RPoly d) ≤ W ^ (5 * t) by
      rw [SoS.coeffNorm1_C, abs_of_nonneg (sub_nonneg.mpr hB)]
      linarith)
  have hfinal := haProof'.add hconst
  have hnfinal : W ^ (22 * t + 1) + W ^ (5 * t) ≤ W ^ (24 * t) :=
    (SoS.add_le_pow_succ hW2 le_rfl
      (SoS.pow_le_pow_of_two_le hW2 (by omega))).trans
      (SoS.pow_le_pow_of_two_le hW2 (by omega))
  exact (hfinal.mono le_rfl hnfinal).congr (by rw [C_sub]; ring)


/-- The exact moment system proves small mean energy with linear multipliers. -/
theorem identifiability
    (D : Data k d) (π γ ε c W : ℝ) (t : ℕ) (hD : D.Valid π γ)
    (ht : 2 ≤ t) (hp : 2 ≤ π * 2 ^ (t - 1)) (hc : 0 < c ∧ c ≤ 1)
    (he : 0 < ε ∧ ε ≤ min (π ^ 2) ((c / (64 * t)) ^ (4 * t)))
    (hW : NormLedger D (moment D) t π ε W) :
    SoS.DerivesNq (system (moment D) t ε) (8 * t) (W ^ (29 * t)) 1 (C c - Q D) := by
  have hb := size_bounds ht hW.1
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hW0 : 0 ≤ W := by linarith
  have hc0 : 0 < c := hc.1
  have hε0 : 0 < ε := he.1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hrt : (0 : ℝ) ≤ 2 * t - 1 := by
    have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  have htW : (2 * t : ℝ) ≤ W := by linarith [hb.2.2.2]
  have hx0 : 0 < c / (64 * t) := by positivity
  have hxc : c / (64 * t) ≤ c :=
    div_le_self hc.1.le (by norm_cast; omega)
  have hεc : ε ≤ c := by
    calc ε ≤ (c / (64 * t)) ^ (4 * t) := he.2.trans (min_le_right _ _)
      _ ≤ c ^ (4 * t) := pow_le_pow_left₀ hx0.le hxc _
      _ ≤ c := pow_le_of_le_one hc.1.le hc.2 (by omega)
  have hcW : 1 / c ≤ W :=
    (one_div_le_one_div_of_le he.1 hεc).trans hW.2.2.1
  let B := (4 : ℝ) * 512 ^ t * (t : ℝ) ^ (2 * t) * Real.sqrt ε
  have hBc : B ≤ c ^ (2 * t) := by
    have hsqrt : Real.sqrt ε ≤ (c / (64 * t)) ^ (2 * t) := by
      apply (Real.sqrt_le_left (pow_nonneg hx0.le _)).mpr
      simpa only [← pow_mul, show 2 * t * 2 = 4 * t by omega] using
        he.2.trans (min_le_right _ _)
    have hfour : (4 : ℝ) ≤ 8 ^ t := by
      exact (by norm_num : (4 : ℝ) ≤ 8).trans
        (le_self_pow₀ (by norm_num) (by omega))
    have hcoef : (4 : ℝ) * 512 ^ t * (t : ℝ) ^ (2 * t) ≤
        (64 * t : ℝ) ^ (2 * t) := by
      calc _ ≤ 8 ^ t * 512 ^ t * (t : ℝ) ^ (2 * t) := by gcongr
        _ = _ := by
          rw [mul_pow (64 : ℝ) (t : ℝ) (2 * t), pow_mul (64 : ℝ) 2 t,
            ← mul_pow (8 : ℝ) 512 t]
          norm_num
    calc B ≤ 4 * 512 ^ t * (t : ℝ) ^ (2 * t) *
          (c / (64 * t)) ^ (2 * t) := by
            dsimp [B]
            exact mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ ≤ (64 * t : ℝ) ^ (2 * t) * (c / (64 * t)) ^ (2 * t) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = c ^ (2 * t) := by
        rw [← mul_pow, mul_div_cancel₀ _ (by positivity : (64 * t : ℝ) ≠ 0)]
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hgap : 0 ≤ c ^ (2 * t) - B := sub_nonneg.mpr hBc
  have hgapn : SoS.coeffNorm1 (C (c ^ (2 * t) - B) : RPoly d) ≤ 1 := by
    rw [SoS.coeffNorm1_C, abs_of_nonneg hgap]
    have := pow_le_one₀ hc.1.le hc.2 (n := 2 * t)
    linarith
  have hm := mismatch_sos_core D π γ ε W t hD ht hp
    ⟨he.1, he.2.trans (min_le_left _ _)⟩ hW
  have hconst := SoS.DerivesNq.ofIsSOS (q := 1) (system (moment D) t ε)
    (SoS.IsSOS.const hgap)
    (show (C (c ^ (2 * t) - B) : RPoly d).totalDegree ≤ 8 * t by
      rw [totalDegree_C]; omega) hgapn
  have hsum := (hm.add hconst).congr
    (show C B - Q D ^ (2 * t) + C (c ^ (2 * t) - B) =
      C (c ^ (2 * t)) - Q D ^ (2 * t) by rw [C_sub]; ring)
  have hsum' := hsum.mono le_rfl
    (SoS.add_le_pow_succ hW2 le_rfl (SoS.one_le_pow_of_two_le hW2 (24 * t)))
  have hQ : SoS.IsSOS (Q D) := by
    simpa only [SoS.IsSOS, SoS.toReal_real] using (sos_bounds D π γ hD).2.1
  have hroot := hsum'.root hQ hc.1 (show 1 ≤ 2 * t by omega)
  have hQd : (Q D).totalDegree ≤ 2 := quad_degree (between D)
  have hQn := (quadratic_norms D π γ hD).2.trans hb.2.2.1
  have hQn0 := SoS.coeffNorm1_nonneg (Q D)
  have hnum : W ^ (24 * t + 1) + SoS.coeffNorm1 (Q D) ^ (2 * t) +
      (2 * t : ℝ) * c ^ (2 * t - 1) * SoS.coeffNorm1 (Q D) +
      ((2 * t : ℝ) - 1) * c ^ (2 * t) ≤ W ^ (24 * t + 2) := by
    have hterm1 : SoS.coeffNorm1 (Q D) ^ (2 * t) ≤ W ^ (24 * t + 1) :=
      (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) hQn _).trans
        (SoS.pow_le_pow_of_two_le hW2 (by omega))
    have hterm2 : (2 * t : ℝ) * c ^ (2 * t - 1) * SoS.coeffNorm1 (Q D) ≤
        W ^ (24 * t + 1) := by
      calc _ ≤ W * 1 * W := mul_le_mul
            (mul_le_mul htW (pow_le_one₀ hc.1.le hc.2) (by positivity) hW0)
            hQn (SoS.coeffNorm1_nonneg _) (by positivity)
        _ = W ^ 2 := by ring
        _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
    have hterm3 : ((2 * t : ℝ) - 1) * c ^ (2 * t) ≤ W ^ (24 * t + 1) := by
      calc _ ≤ W * 1 := mul_le_mul (by linarith) (pow_le_one₀ hc.1.le hc.2)
            (by positivity) hW0
        _ ≤ _ := by simpa using SoS.le_pow_of_two_le hW2 (by omega)
    rw [pow_succ W (24 * t + 1)]
    have hpow : 0 ≤ W ^ (24 * t + 1) := by positivity
    nlinarith
  have hden : 1 / ((2 * t : ℝ) * c ^ (2 * t - 1)) ≤ W ^ (2 * t) := by
    calc _ ≤ 1 / c ^ (2 * t - 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          exact le_mul_of_one_le_left (by positivity) (by norm_cast; omega)
      _ = (1 / c) ^ (2 * t - 1) := (one_div_pow _ _).symm
      _ ≤ W ^ (2 * t - 1) := pow_le_pow_left₀ (by positivity) hcW _
      _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
  have hnorm : (W ^ (24 * t + 1) + SoS.coeffNorm1 (Q D) ^ (2 * t) +
      (2 * t : ℝ) * c ^ (2 * t - 1) * SoS.coeffNorm1 (Q D) +
      ((2 * t : ℝ) - 1) * c ^ (2 * t)) / ((2 * t : ℝ) * c ^ (2 * t - 1)) ≤
      W ^ (29 * t) := by
    calc _ ≤ W ^ (24 * t + 2) * W ^ (2 * t) := by
          rw [div_eq_mul_one_div]
          apply mul_le_mul hnum hden (by positivity) (by positivity)
      _ = W ^ (26 * t + 2) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := SoS.pow_le_pow_of_two_le hW2 (by omega)
  apply hroot.mono (max_le le_rfl (by nlinarith))
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnorm

end

end ABBKS26.IdCov
