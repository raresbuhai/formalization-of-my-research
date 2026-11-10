module

public import ABBKS26.IdCov.MomPoly

/-!
# Moment mismatch

The moment-mismatch estimates used for identical covariances, following [BS23]: a discrete
distribution of minimum weight `wmin` has a moment of degree `O(log (1/wmin))` far from the
Gaussian one, with explicit Hermite-coefficient bounds.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial
open scoped BigOperators
variable {k d : ℕ}

open Finset
open scoped Nat

private theorem odd_doubleFactorial_succ (n : ℕ) :
    (2 * (n + 1) - 1)‼ = (2 * n + 1) * (2 * n - 1)‼ := by
  rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
  exact Nat.doubleFactorial_add_one (2 * n)

private theorem odd_doubleFactorial_mono {i j : ℕ} (h : i ≤ j) :
    (2 * i - 1)‼ ≤ (2 * j - 1)‼ := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    rw [odd_doubleFactorial_succ]
    exact ih.trans (Nat.le_mul_of_pos_left _ (by omega))

private theorem doubleFactorial_product_gap {t j : ℕ} (h : j ≤ t) :
    2 ^ j * (2 * j - 1)‼ * (2 * t - 1)‼ ≤ (2 * (t + j) - 1)‼ := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc 2 ^ (j + 1) * (2 * (j + 1) - 1)‼ * (2 * t - 1)‼
        = 2 * (2 * j + 1) * (2 ^ j * (2 * j - 1)‼ * (2 * t - 1)‼) := by
          rw [odd_doubleFactorial_succ, pow_succ]
          ring
      _ ≤ 2 * (2 * j + 1) * (2 * (t + j) - 1)‼ :=
        Nat.mul_le_mul_left _ (ih (by omega))
      _ ≤ (2 * (t + j) + 1) * (2 * (t + j) - 1)‼ :=
        Nat.mul_le_mul_right _ (by omega)
      _ = (2 * (t + (j + 1)) - 1)‼ := by
        rw [show t + (j + 1) = t + j + 1 by ring, odd_doubleFactorial_succ]

/-- Gaussian double factorials exhibit exponential mismatch. -/
theorem doubleFactorial_gap
    (t : ℕ) : 2 ^ t * Nat.doubleFactorial (2 * t - 1) ^ 2 ≤
      Nat.doubleFactorial (4 * t - 1) := by
  have h := doubleFactorial_product_gap (le_refl t)
  simpa only [show t + t = 2 * t by ring, show 2 * (2 * t) = 4 * t by ring,
    pow_two, mul_assoc] using h

/-- Hermite coefficients have the required finite sum bound. -/
theorem hermite_coeff_sum
    (s : ℕ) : K s ≤ 4 ^ s * alpha s := by
  have hchoose : ∑ i ∈ range (s - 1), (2 * s).choose (2 * i) ≤ 4 ^ s := by
    calc ∑ i ∈ range (s - 1), (2 * s).choose (2 * i)
        = ∑ p ∈ (range (s - 1)).image (fun i ↦ 2 * i), (2 * s).choose p := by
          rw [sum_image]
          intro i _ j _ h
          simpa using h
      _ ≤ ∑ p ∈ range (2 * s + 1), (2 * s).choose p := by
          apply sum_le_sum_of_subset
          intro p hp
          simp only [mem_image, mem_range] at hp ⊢
          omega
      _ = 4 ^ s := by rw [Nat.sum_range_choose, pow_mul]; norm_num
  have hsum : ∑ i ∈ range (s - 1), hermCoeff (2 * s) i ≤
      4 ^ s * (2 * s - 1)‼ := by
    calc ∑ i ∈ range (s - 1), hermCoeff (2 * s) i
        ≤ ∑ i ∈ range (s - 1), (2 * s).choose (2 * i) * (2 * s - 1)‼ := by
          apply sum_le_sum
          intro i hi
          exact Nat.mul_le_mul_left _ (odd_doubleFactorial_mono (by
            simp only [mem_range] at hi
            omega))
      _ = (∑ i ∈ range (s - 1), (2 * s).choose (2 * i)) * (2 * s - 1)‼ := by
        rw [sum_mul]
      _ ≤ 4 ^ s * (2 * s - 1)‼ := Nat.mul_le_mul_right _ hchoose
  unfold K alpha
  exact_mod_cast hsum

private theorem sum_sq_sub_sum_sq {ι R : Type*} [CommRing R]
    (s : Finset ι) (f : ι → R) (hf : ∀ i ∈ s, IsSumSq (f i)) :
    IsSumSq ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, f i ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hsum : IsSumSq (∑ i ∈ s, f i) := IsSumSq.sum fun i hi ↦ hf i (mem_insert_of_mem hi)
    have hcross := ((hf a (mem_insert_self a s)).mul hsum).add
      ((hf a (mem_insert_self a s)).mul hsum)
    convert (ih (fun i hi ↦ hf i (mem_insert_of_mem hi))).add hcross using 1
    simp only [sum_insert ha]
    ring

/-- A positive minimum weight bounds the discrete fourth moment in SoS. -/
theorem discrete_mismatch
    (D : Data k d) (π : ℝ) (hπ : 0 ≤ π) (hw : ∀ i, π ≤ D.weight i)
    (t : ℕ) : IsSumSq (powerMoment D (2 * t) ^ 2 - C π * powerMoment D (4 * t)) := by
  have hweight (i : Fin k) : 0 ≤ D.weight i := hπ.trans (hw i)
  have heven (i : Fin k) : IsSumSq (lin (D.mean i) ^ (2 * t)) := by
    rw [mul_comm 2 t, pow_mul]
    exact SoS.isSumSq_sq _
  have hcross := sum_sq_sub_sum_sq univ
    (fun i ↦ C (D.weight i) * lin (D.mean i) ^ (2 * t))
    (fun i _ ↦ SoS.isSumSq_C_mul (hweight i) (heven i))
  have hdiag : IsSumSq (∑ i, C (D.weight i * (D.weight i - π)) *
      (lin (D.mean i) ^ (2 * t)) ^ 2) := by
    exact IsSumSq.sum fun i _ ↦ SoS.isSumSq_C_mul
      (mul_nonneg (hweight i) (sub_nonneg.mpr (hw i))) (SoS.isSumSq_sq _)
  have hid : (∑ i, C (D.weight i * (D.weight i - π)) *
      (lin (D.mean i) ^ (2 * t)) ^ 2) =
      (∑ i, (C (D.weight i) * lin (D.mean i) ^ (2 * t)) ^ 2) -
        C π * powerMoment D (4 * t) := by
    simp only [powerMoment, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    rw [show 4 * t = 2 * t * 2 by ring, pow_mul, map_mul, map_sub]
    ring
  rw [hid] at hdiag
  convert hcross.add hdiag using 1
  simp only [powerMoment]
  ring

/-- The explicit mismatch constant is controlled by a square-root tolerance. -/
theorem mismatch_constant
    (t : ℕ) (π ε lam : ℝ) (ht : 2 ≤ t) (hπ : 0 < π)
    (hp : 2 ≤ π * 2 ^ (t - 1)) (he : 0 < ε ∧ ε ≤ π ^ 2)
    (hl : 1 ≤ lam ∧ lam ≤ 2) :
    (π * K (2 * t) * lam ^ (2 * t) * Real.sqrt ε +
      2 * K t ^ 2 * lam ^ (2 * t) * ε) /
      (π * alpha (2 * t) - 2 * alpha t ^ 2) ≤
        (4 : ℝ) * 512 ^ t * (t : ℝ) ^ (2 * t) * Real.sqrt ε := by
  have ha : 0 < alpha t := by unfold alpha; positivity
  have hb : 0 < alpha (2 * t) := by unfold alpha; positivity
  have hlam : 0 ≤ lam := le_trans (by norm_num) hl.1
  have he0 : 0 ≤ ε := he.1.le
  have hK : 0 ≤ K t := sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
  have hgap : (2 : ℝ) ^ t * alpha t ^ 2 ≤ alpha (2 * t) := by
    simpa only [alpha, show 2 * (2 * t) = 4 * t by ring,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (Nat.cast_le (α := ℝ)).mpr (doubleFactorial_gap t)
  have hpow : 4 ≤ π * (2 : ℝ) ^ t := by
    rw [show t = (t - 1) + 1 by omega, pow_succ]
    nlinarith [hp]
  have hfour : 4 * alpha t ^ 2 ≤ π * alpha (2 * t) := by
    calc 4 * alpha t ^ 2 ≤ (π * 2 ^ t) * alpha t ^ 2 :=
        mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
      _ ≤ π * alpha (2 * t) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hgap hπ.le
  have hden : π * alpha (2 * t) / 2 ≤ π * alpha (2 * t) - 2 * alpha t ^ 2 := by
    linarith
  have hdenpos : 0 < π * alpha (2 * t) - 2 * alpha t ^ 2 :=
    lt_of_lt_of_le (by positivity) hden
  have hab : alpha t ^ 2 ≤ alpha (2 * t) := by
    calc alpha t ^ 2 ≤ 2 ^ t * alpha t ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num))
      _ ≤ alpha (2 * t) := hgap
  have hsqrt : ε ≤ π * Real.sqrt ε := by
    have hs : Real.sqrt ε ≤ π := (Real.sqrt_le_left hπ.le).mpr he.2
    calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt he0).symm
      _ ≤ π * Real.sqrt ε := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
  have hKsq : K t ^ 2 ≤ (4 : ℝ) ^ (2 * t) * alpha (2 * t) := by
    calc K t ^ 2 ≤ (4 ^ t * alpha t) ^ 2 :=
        pow_le_pow_left₀ hK (hermite_coeff_sum t) 2
      _ = 4 ^ (2 * t) * alpha t ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm t 2]
      _ ≤ 4 ^ (2 * t) * alpha (2 * t) :=
        mul_le_mul_of_nonneg_left hab (by positivity)
  have hscale : (4 : ℝ) ^ (2 * t) * lam ^ (2 * t) ≤ 64 ^ t := by
    calc (4 : ℝ) ^ (2 * t) * lam ^ (2 * t)
        ≤ 4 ^ (2 * t) * 2 ^ (2 * t) := by gcongr; exact hl.2
      _ = 64 ^ t := by rw [← mul_pow, pow_mul]; norm_num
  have hfirst : π * K (2 * t) * lam ^ (2 * t) * Real.sqrt ε ≤
      π * alpha (2 * t) * 64 ^ t * Real.sqrt ε := by
    calc π * K (2 * t) * lam ^ (2 * t) * Real.sqrt ε
        ≤ π * (4 ^ (2 * t) * alpha (2 * t)) * lam ^ (2 * t) *
            Real.sqrt ε := by gcongr; exact hermite_coeff_sum (2 * t)
      _ = π * alpha (2 * t) * (4 ^ (2 * t) * lam ^ (2 * t)) *
            Real.sqrt ε := by ring
      _ ≤ π * alpha (2 * t) * 64 ^ t * Real.sqrt ε := by gcongr
  have hsecond : 2 * K t ^ 2 * lam ^ (2 * t) * ε ≤
      2 * π * alpha (2 * t) * 64 ^ t * Real.sqrt ε := by
    calc 2 * K t ^ 2 * lam ^ (2 * t) * ε
        ≤ 2 * (4 ^ (2 * t) * alpha (2 * t)) * lam ^ (2 * t) *
            (π * Real.sqrt ε) := by gcongr
      _ = 2 * π * alpha (2 * t) * (4 ^ (2 * t) * lam ^ (2 * t)) *
            Real.sqrt ε := by ring
      _ ≤ 2 * π * alpha (2 * t) * 64 ^ t * Real.sqrt ε := by gcongr
  have hnum : π * K (2 * t) * lam ^ (2 * t) * Real.sqrt ε +
      2 * K t ^ 2 * lam ^ (2 * t) * ε ≤
      3 * π * alpha (2 * t) * 64 ^ t * Real.sqrt ε := by
    linarith
  have hratio : (π * K (2 * t) * lam ^ (2 * t) * Real.sqrt ε +
      2 * K t ^ 2 * lam ^ (2 * t) * ε) /
      (π * alpha (2 * t) - 2 * alpha t ^ 2) ≤ 6 * 64 ^ t * Real.sqrt ε := by
    apply (div_le_iff₀ hdenpos).mpr
    calc _ ≤ 3 * π * alpha (2 * t) * 64 ^ t * Real.sqrt ε := hnum
      _ = (6 * 64 ^ t * Real.sqrt ε) * (π * alpha (2 * t) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  have hconst : (6 : ℝ) * 64 ^ t ≤ 512 ^ t := by
    calc (6 : ℝ) * 64 ^ t ≤ 8 ^ t * 64 ^ t := by
          gcongr
          exact (by norm_num : (6 : ℝ) ≤ 8).trans
            (le_self_pow₀ (by norm_num) (by omega))
      _ = 512 ^ t := by rw [← mul_pow]; norm_num
  have htone : (1 : ℝ) ≤ (t : ℝ) ^ (2 * t) :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ t by omega))
  calc _ ≤ 6 * 64 ^ t * Real.sqrt ε := hratio
    _ ≤ 512 ^ t * Real.sqrt ε := mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _)
    _ ≤ (4 * (t : ℝ) ^ (2 * t)) * (512 ^ t * Real.sqrt ε) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    _ = 4 * 512 ^ t * (t : ℝ) ^ (2 * t) * Real.sqrt ε := by ring

end

end ABBKS26.IdCov
