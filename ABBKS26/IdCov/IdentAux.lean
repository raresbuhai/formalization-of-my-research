module

public import ABBKS26.IdCov.Mismatch

/-! Local degree and coefficient estimates for exact identifiability. -/

@[expose] public section

namespace ABBKS26.IdCov.IdentAux

noncomputable section

open Common MvPolynomial Matrix Finset
open scoped BigOperators

variable {k d : ℕ}

theorem norm_mul {p q : RPoly d} {a b : ℝ}
    (hp : SoS.coeffNorm1 p ≤ a) (hq : SoS.coeffNorm1 q ≤ b) :
    SoS.coeffNorm1 (p * q) ≤ a * b :=
  (SoS.coeffNorm1_mul_le _ _).trans
    (mul_le_mul hp hq (SoS.coeffNorm1_nonneg _) ((SoS.coeffNorm1_nonneg _).trans hp))

theorem norm_pow {p : RPoly d} {a : ℝ} (hp : SoS.coeffNorm1 p ≤ a) (n : ℕ) :
    SoS.coeffNorm1 (p ^ n) ≤ a ^ n :=
  (SoS.coeffNorm1_pow_le _ _).trans
    (pow_le_pow_left₀ (SoS.coeffNorm1_nonneg _) hp n)

theorem norm_nsq : SoS.coeffNorm1 (nsq : RPoly d) ≤ d := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := sum_le_sum fun i _ ↦ by
      simpa [SoS.coeffNorm1_X] using SoS.coeffNorm1_pow_le (X i : RPoly d) 2
    _ = d := by simp

theorem quad_degree (A : Mat d) : (quad A).totalDegree ≤ 2 := by
  apply totalDegree_finsetSum_le
  intro i _
  apply totalDegree_finsetSum_le
  intro j _
  exact (totalDegree_mul _ _).trans (by
    have := totalDegree_mul (C (A i j) : RPoly d) (X i)
    simp only [totalDegree_C, totalDegree_X] at *
    omega)

theorem nsq_degree : (nsq : RPoly d).totalDegree ≤ 2 :=
  totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X_pow]

theorem norm_quad (A : Mat d) (e : ℝ) (he : ∀ i j, |A i j| ≤ e) :
    SoS.coeffNorm1 (quad A) ≤ d ^ 2 * e := by
  refine (SoS.coeffNorm1_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, e := by
      apply sum_le_sum
      intro i _
      refine (SoS.coeffNorm1_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
      simpa only [SoS.coeffNorm1_X, mul_one, SoS.coeffNorm1_C_mul] using
        norm_mul (by simpa [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X] using he i j)
          (SoS.coeffNorm1_X j).le
    _ = _ := by simp; ring

theorem psd_entry (A : Mat d) (hA : A.PosSemidef)
    (hb : ∀ v, qform A v ≤ 2 * sqnorm v) (i j : Fin d) : |A i j| ≤ 2 := by
  have hs : A j i = A i j := by
    simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial,
      Matrix.ext_iff, transpose_apply] using congrFun (congrFun hA.1 i) j
  have hi0 : 0 ≤ A i i := by
    simpa [dotProduct_single, star_trivial] using
      hA.dotProduct_mulVec_nonneg (Pi.single i 1)
  have hj0 : 0 ≤ A j j := by
    simpa [dotProduct_single, star_trivial] using
      hA.dotProduct_mulVec_nonneg (Pi.single j 1)
  have hi : A i i ≤ 2 := by
    simpa [qform, sqnorm, dotProduct_single] using hb (Pi.single i 1)
  have hj : A j j ≤ 2 := by
    simpa [qform, sqnorm, dotProduct_single] using hb (Pi.single j 1)
  have hp := hA.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hA.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, mulVec_add, mulVec_sub, dotProduct_add, dotProduct_sub,
    add_dotProduct, sub_dotProduct, single_dotProduct, mulVec_single_one,
    Matrix.col_apply, one_mul, hs] at hp hm
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem quadratic_norms (D : Data k d) (π γ : ℝ) (hD : D.Valid π γ) :
    SoS.coeffNorm1 (S D) ≤ 2 * d ^ 2 ∧
      SoS.coeffNorm1 (Q D) ≤ 2 * d ^ 2 := by
  have hs := sos_bounds D π γ hD
  have hquad (A : Mat d) (hA : A.IsHermitian) (h0 : IsSumSq (quad A))
      (hup : IsSumSq (C (1 + γ) * nsq - quad A)) :
      SoS.coeffNorm1 (quad A) ≤ 2 * d ^ 2 := by
    have heval (v : Vec d) : eval v (quad A) = qform A v := by
      simp only [quad, qform, Matrix.mulVec, dotProduct, map_sum, map_mul, eval_C,
        eval_X, mul_sum]
      exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
    have hn (v : Vec d) : eval v (nsq : RPoly d) = sqnorm v := by
      simp [nsq, sqnorm, dotProduct, pow_two]
    have hp : A.PosSemidef := PosSemidef.of_dotProduct_mulVec_nonneg hA fun v ↦ by
      simp only [star_trivial]
      change 0 ≤ qform A v
      rw [← heval]
      exact (SoS.isSumSq_map (eval v) h0).nonneg
    have hb (v : Vec d) : qform A v ≤ 2 * sqnorm v := by
      have hu := (SoS.isSumSq_map (eval v) hup).nonneg
      simp only [map_sub, map_mul, eval_C, hn, heval] at hu
      have hv : 0 ≤ sqnorm v := by
        change 0 ≤ ∑ i, v i * v i
        exact sum_nonneg fun i _ ↦ mul_self_nonneg (v i)
      nlinarith [hD.2.2]
    calc _ ≤ (d : ℝ) ^ 2 * 2 := norm_quad A 2 (psd_entry A hp hb)
      _ = _ := by ring
  have hcov : D.cov.IsHermitian := by
    have hw := hD.1.2.2.1
    have hk : 0 < k := by
      by_contra hk
      have : k = 0 := by omega
      subst k
      simp at hw
    exact (hD.1.2.2.2 ⟨0, hk⟩).isHermitian
  have hbet : (between D).IsHermitian := by
    change (between D)ᴴ = between D
    ext i j
    simp [between, conjTranspose_apply, Matrix.sum_apply, Matrix.smul_apply,
      vecMulVec_apply, mul_comm]
  exact ⟨hquad D.cov hcov hs.1 hs.2.2.1, hquad (between D) hbet hs.2.1 hs.2.2.2⟩

theorem size_bounds {t : ℕ} {W : ℝ} (ht : 2 ≤ t)
    (hW : 64 * (d + 1 : ℝ) ^ 2 * t ≤ W) :
    64 ≤ W ∧ (d : ℝ) ≤ W ∧ 2 * (d : ℝ) ^ 2 ≤ W ∧ 16 * t ≤ W := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have hsq : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hsq (show (0 : ℝ) ≤ t by positivity)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem alpha_bound (s : ℕ) : alpha s ≤ (2 * s : ℝ) ^ s := by
  have hn : Nat.doubleFactorial (2 * s - 1) ≤ (2 * s) ^ s := by
    induction s with
    | zero => simp
    | succ s ih =>
      rw [show 2 * (s + 1) - 1 = 2 * s + 1 by omega,
        Nat.doubleFactorial_add_one]
      calc (2 * s + 1) * Nat.doubleFactorial (2 * s - 1)
          ≤ (2 * (s + 1)) * (2 * (s + 1)) ^ s :=
            Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) _))
        _ = _ := by ring
  unfold alpha
  exact_mod_cast hn

theorem coefficient_bounds {t s : ℕ} {W : ℝ} (ht : 2 ≤ t) (hs : s ≤ 2 * t)
    (hW : 64 * (d + 1 : ℝ) ^ 2 * t ≤ W) :
    0 ≤ K s ∧ K s ≤ W ^ s ∧ 0 < alpha s ∧ alpha s ≤ W ^ s := by
  have hb := size_bounds ht hW
  have h8 : 8 * (s : ℝ) ≤ W := by
    have hs' : (s : ℝ) ≤ 2 * t := by exact_mod_cast hs
    linarith [hb.2.2.2]
  have ha := alpha_bound s
  refine ⟨sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _), ?_, ?_, ?_⟩
  · calc K s ≤ 4 ^ s * alpha s := hermite_coeff_sum s
      _ ≤ 4 ^ s * (2 * s : ℝ) ^ s := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (8 * s : ℝ) ^ s := by rw [← mul_pow]; congr 1; ring
      _ ≤ W ^ s := pow_le_pow_left₀ (by positivity) h8 s
  · unfold alpha; positivity
  · exact ha.trans (pow_le_pow_left₀ (by positivity) (by linarith) s)

theorem K_one_le {s : ℕ} (hs : 2 ≤ s) : 1 ≤ K s := by
  have h0 : (0 : ℕ) ∈ range (s - 1) := mem_range.mpr (by omega)
  have h := single_le_sum (fun j (_ : j ∈ range (s - 1)) ↦
    (Nat.cast_nonneg (hermCoeff (2 * s) j) : (0 : ℝ) ≤ _)) h0
  simpa [K, hermCoeff] using h

theorem dev_norm (D : Data k d) {π γ W : ℝ} {t u : ℕ}
    (hD : D.Valid π γ) (ht : 2 ≤ t) (hu : u ≤ 2 * t)
    (hW : 64 * (d + 1 : ℝ) ^ 2 * t ≤ W)
    (hM : SoS.coeffNorm1 (moment D (2 * u)) ≤ W ^ (4 * u)) :
    SoS.coeffNorm1 (dev (moment D) u) ≤ 2 * W ^ (4 * u) := by
  have hb := size_bounds ht hW
  have hW2 : 2 ≤ W := by linarith [hb.1]
  have hq := quadratic_norms D π γ hD
  have h2 : SoS.coeffNorm1 (moment D 2) ≤ W ^ 2 := by
    rw [second_moment D hD.1.2.2.1]
    refine (SoS.coeffNorm1_add_le _ _).trans ?_
    have hQ := hq.2.trans hb.2.2.1
    have hS := hq.1.trans hb.2.2.1
    have := SoS.add_le_pow_succ (c := 1) hW2 (by simpa using hQ) (by simpa using hS)
    simpa using this
  have ha := coefficient_bounds ht hu hW
  have hgauss : SoS.coeffNorm1 (C (alpha u) * moment D 2 ^ u) ≤ W ^ (4 * u) := by
    rw [SoS.coeffNorm1_C_mul, abs_of_pos ha.2.2.1]
    calc alpha u * SoS.coeffNorm1 (moment D 2 ^ u)
        ≤ W ^ u * (W ^ 2) ^ u := mul_le_mul ha.2.2.2 (norm_pow h2 u)
          (SoS.coeffNorm1_nonneg _) (by positivity)
      _ = W ^ (3 * u) := by rw [← pow_mul, ← pow_add]; congr 1; omega
      _ ≤ W ^ (4 * u) := SoS.pow_le_pow_of_two_le hW2 (by omega)
  exact (SoS.coeffNorm1_sub_le _ _).trans (by linarith)

theorem range_cs (s : ℕ) (Z : ℕ → RPoly d) :
    IsSumSq (C (K s) * (∑ j ∈ range (s - 1),
      C (hermCoeff (2 * s) j : ℝ) * Z j ^ 2) -
      (∑ j ∈ range (s - 1),
        C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) * Z j) ^ 2) ∧
    SoS.coeffNorm1 (C (K s) * (∑ j ∈ range (s - 1),
      C (hermCoeff (2 * s) j : ℝ) * Z j ^ 2) -
      (∑ j ∈ range (s - 1),
        C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) * Z j) ^ 2) ≤
      2 * K s * ∑ j ∈ range (s - 1),
        (hermCoeff (2 * s) j : ℝ) * SoS.coeffNorm1 (Z j) ^ 2 := by
  have h := SoSKit.weighted_cs
    (fun j : Fin (s - 1) ↦ (-1 : ℝ) ^ (j : ℕ) * (hermCoeff (2 * s) j : ℝ))
    (fun j ↦ Z j)
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast] at h
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (hermCoeff (2 * s) j : ℝ)),
    Fin.sum_univ_eq_sum_range (fun j ↦ C (hermCoeff (2 * s) j : ℝ) * Z j ^ 2),
    Fin.sum_univ_eq_sum_range (fun j ↦
      C ((-1) ^ j * (hermCoeff (2 * s) j : ℝ)) * Z j),
    Fin.sum_univ_eq_sum_range (fun j ↦
      (hermCoeff (2 * s) j : ℝ) * SoS.coeffNorm1 (Z j) ^ 2)] at h
  exact h

theorem constraint_derives (M : ℕ → RPoly d) (t u : ℕ) (ε : ℝ)
    (hu : 2 ≤ u ∧ u ≤ 2 * t)
    (hd : (constraint M ε u).totalDegree ≤ 4 * u) :
    SoS.DerivesNq (system M t ε) (4 * u) 1 1 (constraint M ε u) := by
  by_cases hz : constraint M ε u = 0
  · rw [hz]
    exact SoS.DerivesNq.zero _ _ _ zero_le_one
  · apply SoS.DerivesNq.of_mem _ hd le_rfl
    simp only [system, List.mem_append, List.mem_singleton, List.mem_filter,
      List.mem_map, List.mem_range, ne_eq, decide_eq_true_eq]
    right
    exact ⟨⟨u - 2, by omega, by congr 1; omega⟩, hz⟩

theorem powerMoment_degree (D : Data k d) (r : ℕ) :
    (powerMoment D r).totalDegree ≤ r := by
  have hlin (v : Vec d) : (lin v).totalDegree ≤ 1 :=
    totalDegree_finsetSum_le fun i _ ↦ (totalDegree_mul _ _).trans (by simp)
  exact totalDegree_finsetSum_le fun i _ ↦ (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left r (hlin (D.mean i))))

theorem mismatch_degree (D : Data k d) (s : ℕ) :
    (powerMoment D (2 * s) - C (alpha s) * Q D ^ s).totalDegree ≤ 2 * s := by
  refine (totalDegree_sub _ _).trans (max_le (powerMoment_degree D _) ?_)
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact (totalDegree_pow _ _).trans (by
      have hd : (Q D).totalDegree ≤ 2 := quad_degree (between D)
      simpa only [mul_comm s 2] using Nat.mul_le_mul_left s hd))

theorem pi_le_one (D : Data k d) {π γ : ℝ} (hD : D.Valid π γ) : π ≤ 1 := by
  have hk : 0 < k := by
    by_contra hk
    have : k = 0 := by omega
    subst k
    simpa using hD.1.2.2.1
  let i : Fin k := ⟨0, hk⟩
  have hs : ∑ j, D.weight j = 1 := hD.1.2.2.1
  have hw : π ≤ D.weight i := hD.1.2.1 i
  exact hw.trans (by
    have h := single_le_sum (s := univ) (f := D.weight)
      (fun j _ ↦ hD.1.1.le.trans (hD.1.2.1 j)) (mem_univ i)
    simpa only [hs] using h)

theorem alpha_one_le (s : ℕ) : 1 ≤ alpha s := by
  unfold alpha
  exact_mod_cast (Nat.doubleFactorial_pos (2 * s - 1))

end

end ABBKS26.IdCov.IdentAux
