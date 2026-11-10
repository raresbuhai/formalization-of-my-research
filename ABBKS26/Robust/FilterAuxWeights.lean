module

public import ABBKS26.Common.Basic

/-! Finite weighted mean and variance estimates used by the quadratic filter. -/

@[expose] public section

namespace ABBKS26.Robust.FilterAux

open scoped BigOperators

private theorem weighted_cs {ι : Type*} (S : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * x i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * x i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S hw
    (fun i hi ↦ mul_nonneg (hw i hi) (sq_nonneg _))
  intro i _
  exact le_of_eq (by ring)

theorem weighted_mean_shift {n : ℕ}
    (x w : Fin n → ℝ) (G B : Finset (Fin n)) (hdis : Disjoint G B)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hG : G.Nonempty)
    (μG μw VG Vw β ρ ω : ℝ)
    (hg : μG = (G.card : ℝ)⁻¹ * ∑ i ∈ G, x i)
    (hwmean : μw = (∑ i ∈ G ∪ B, w i)⁻¹ * ∑ i ∈ G ∪ B, w i * x i)
    (hb : β = (G.card : ℝ)⁻¹ * ∑ i ∈ B, w i)
    (hr : ρ = (G.card : ℝ)⁻¹ * ∑ i ∈ G, (1 - w i))
    (ho : ω = 1 - ρ + β) (ho0 : 0.9 ≤ ω) (hβ : β ≤ ω / 16)
    (hVG : VG = (G.card : ℝ)⁻¹ * ∑ i ∈ G, (x i - μG) ^ 2)
    (hVw : Vw = (∑ i ∈ G ∪ B, w i)⁻¹ *
      ∑ i ∈ G ∪ B, w i * (x i - μw) ^ 2) :
    (μw - μG) ^ 2 ≤ 4 * β * Vw + 5 * ρ * VG := by
  let N : ℝ := G.card
  let W : ℝ := ∑ i ∈ G ∪ B, w i
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast Finset.card_pos.mpr hG
  have hb' : ∑ i ∈ B, w i = N * β := by
    rw [hb]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hr' : ∑ i ∈ G, (1 - w i) = N * ρ := by
    rw [hr]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hwG : ∑ i ∈ G, w i = N * (1 - ρ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hr'
    dsimp only [N] at *
    linarith
  have hW : W = N * ω := by
    dsimp only [W]
    rw [Finset.sum_union hdis, hb', hwG, ho]
    ring
  have hW0 : 0 < W := by
    rw [hW]
    exact mul_pos hN (lt_of_lt_of_le (by norm_num) ho0)
  have hg' : ∑ i ∈ G, x i = N * μG := by
    rw [hg]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hm' : ∑ i ∈ G ∪ B, w i * x i = W * μw := by
    rw [hwmean]
    change _ = W * (W⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hW0.ne', one_mul]
  have hVG' : ∑ i ∈ G, (x i - μG) ^ 2 = N * VG := by
    rw [hVG]
    change _ = N * (N⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
  have hVw' : ∑ i ∈ G ∪ B, w i * (x i - μw) ^ 2 = W * Vw := by
    rw [hVw]
    change _ = W * (W⁻¹ * _)
    rw [← mul_assoc, mul_inv_cancel₀ hW0.ne', one_mul]
  have hβ0 : 0 ≤ β := by
    rw [hb]
    exact mul_nonneg (inv_nonneg.mpr hN.le)
      (Finset.sum_nonneg fun i _ ↦ (hw i).1)
  have hρ0 : 0 ≤ ρ := by
    rw [hr]
    apply mul_nonneg (inv_nonneg.mpr hN.le)
    exact Finset.sum_nonneg fun i _ ↦ sub_nonneg.mpr (hw i).2
  have hVG0 : 0 ≤ VG := by
    rw [hVG]
    exact mul_nonneg (inv_nonneg.mpr hN.le)
      (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hVw0 : 0 ≤ Vw := by
    rw [hVw]
    exact mul_nonneg (inv_nonneg.mpr hW0.le)
      (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i).1 (sq_nonneg _))
  let b := ∑ i ∈ B, w i * (x i - μw)
  let r := ∑ i ∈ G, (1 - w i) * (x i - μG)
  have hbid : N * (ω - β) * (μw - μG) = b - r := by
    dsimp only [b, r]
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Finset.sum_const, nsmul_eq_mul, one_mul]
    rw [Finset.sum_union hdis] at hm'
    rw [hb', hwG, hg']
    rw [hW] at hm'
    change N * ω * μw - N * β * μw - (N * ω * μG - N * β * μG) =
      ∑ i ∈ B, w i * x i - N * β * μw -
        (N * μG - ∑ i ∈ G, w i * x i - (N * μG - N * (1 - ρ) * μG))
    linear_combination -hm' - N * μG * ho
  have hbc : b ^ 2 ≤ N ^ 2 * β * ω * Vw := by
    have hc := weighted_cs B w (fun i ↦ x i - μw) (fun i _ ↦ (hw i).1)
    have hs : (∑ i ∈ B, w i * (x i - μw) ^ 2) ≤
        ∑ i ∈ G ∪ B, w i * (x i - μw) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        (fun i _ _ ↦ mul_nonneg (hw i).1 (sq_nonneg _))
    rw [hb', hVw', hW] at *
    calc
      b ^ 2 ≤ (N * β) * ∑ i ∈ B, w i * (x i - μw) ^ 2 := hc
      _ ≤ (N * β) * (N * ω * Vw) := mul_le_mul_of_nonneg_left hs (mul_nonneg hN.le hβ0)
      _ = _ := by ring
  have hrc : r ^ 2 ≤ N ^ 2 * ρ * VG := by
    have hc := weighted_cs G (fun i ↦ 1 - w i) (fun i ↦ x i - μG)
      (fun i _ ↦ sub_nonneg.mpr (hw i).2)
    have hs : (∑ i ∈ G, (1 - w i) * (x i - μG) ^ 2) ≤
        ∑ i ∈ G, (x i - μG) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left (sq_nonneg _) (by linarith [(hw i).1])
    rw [hr', hVG'] at *
    calc
      r ^ 2 ≤ (N * ρ) * ∑ i ∈ G, (1 - w i) * (x i - μG) ^ 2 := hc
      _ ≤ (N * ρ) * (N * VG) := mul_le_mul_of_nonneg_left hs (mul_nonneg hN.le hρ0)
      _ = _ := by ring
  have ht : (ω - β) ^ 2 * (μw - μG) ^ 2 ≤ 2 * β * ω * Vw + 2 * ρ * VG := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hN)).mp
    have he : N ^ 2 * ((ω - β) ^ 2 * (μw - μG) ^ 2) = (b - r) ^ 2 := by
      calc
        _ = (N * (ω - β) * (μw - μG)) ^ 2 := by ring
        _ = _ := by rw [hbid]
    rw [he]
    nlinarith only [hbc, hrc, sq_nonneg (b + r)]
  have hω : 0 < ω := by linarith
  have hg0 : (4 / 5 : ℝ) ≤ ω - β := by linarith only [ho0, hβ]
  have hgω : (5 / 8 : ℝ) * ω ≤ ω - β := by linarith only [ho0, hβ]
  have hgω' : ω / 2 ≤ (ω - β) ^ 2 := by
    calc
      ω / 2 = (4 / 5 : ℝ) * ((5 / 8 : ℝ) * ω) := by ring
      _ ≤ (ω - β) * (ω - β) := mul_le_mul hg0 hgω
        (by linarith only [ho0]) (by linarith only [hg0])
      _ = _ := by ring
  have hgs : (2 / 5 : ℝ) ≤ (ω - β) ^ 2 := by nlinarith only [hg0]
  have hcoef : 2 * β * ω * Vw + 2 * ρ * VG ≤
      (ω - β) ^ 2 * (4 * β * Vw + 5 * ρ * VG) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hgω') (mul_nonneg hβ0 hVw0),
      mul_nonneg (sub_nonneg.mpr hgs) (mul_nonneg hρ0 hVG0)]
  exact (mul_le_mul_iff_right₀ (by nlinarith only [hg0] : 0 < (ω - β) ^ 2)).mp (ht.trans hcoef)

private theorem retained_cs {ι : Type*} (s : Finset ι) (r x : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i ∧ r i ≤ 1) :
    (∑ i ∈ s, r i * x i) ^ 2 ≤ (∑ i ∈ s, r i) * ∑ i ∈ s, x i ^ 2 := by
  have hc := weighted_cs s r x (fun i hi ↦ (hr i hi).1)
  apply hc.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun i hi ↦ (hr i hi).1)
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_of_le_one_left (sq_nonneg _) (hr i hi).2

theorem retained_variance_lower {ι : Type*} (s : Finset ι) (r x : ι → ℝ)
    (hr : ∀ i ∈ s, 0 ≤ r i ∧ r i ≤ 1)
    (N g π a : ℝ) (hN : 0 < N) (hcard : (s.card : ℝ) = N) (hg : 0 ≤ g)
    (hπ : 0 < π ∧ π ≤ 1) (hmean : ∑ i ∈ s, x i = 0)
    (hsecond : ∑ i ∈ s, x i ^ 2 = N * g)
    (hfourth : ∑ i ∈ s, x i ^ 4 ≤ N * (4 / π) * g ^ 2)
    (hremoved : ∑ i ∈ s, (1 - r i) ≤ N * π / 100) :
    (3 / 4 : ℝ) * N * g ≤ ∑ i ∈ s, r i * (x i - a) ^ 2 := by
  let b := ∑ i ∈ s, (1 - r i)
  let m := ∑ i ∈ s, r i
  let B := ∑ i ∈ s, r i * x i ^ 2
  let S := ∑ i ∈ s, r i * x i
  let C := ∑ i ∈ s, (1 - r i) * x i ^ 2
  have hmissing (i : ι) (hi : i ∈ s) : 0 ≤ 1 - r i ∧ 1 - r i ≤ 1 := by
    constructor <;> linarith only [(hr i hi).1, (hr i hi).2]
  have hb : 0 ≤ b := Finset.sum_nonneg fun i hi ↦ (hmissing i hi).1
  have hb' : b ≤ N / 100 := hremoved.trans (by nlinarith only [hπ.2, hN.le])
  have hm : m = N - b := by
    dsimp only [m, b]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
    ring
  have hm' : (99 / 100 : ℝ) * N ≤ m := by linarith only [hm, hb']
  have hm0 : 0 < m := by linarith only [hm', hN]
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun i hi ↦
    mul_nonneg (hmissing i hi).1 (sq_nonneg _)
  have hC : C ≤ N * g / 5 := by
    have hh := retained_cs s (fun i ↦ 1 - r i) (fun i ↦ x i ^ 2) hmissing
    have hsq : C ^ 2 ≤ (N * g / 5) ^ 2 := by
      calc
        _ ≤ b * ∑ i ∈ s, (x i ^ 2) ^ 2 := hh
        _ = b * ∑ i ∈ s, x i ^ 4 := by simp only [← pow_mul]
        _ ≤ b * (N * (4 / π) * g ^ 2) := mul_le_mul_of_nonneg_left hfourth hb
        _ ≤ (N * π / 100) * (N * (4 / π) * g ^ 2) :=
          mul_le_mul_of_nonneg_right hremoved (mul_nonneg
            (mul_nonneg hN.le (div_nonneg (by norm_num) hπ.1.le)) (sq_nonneg g))
        _ = _ := by field_simp [hπ.1.ne']; ring
    exact (sq_le_sq₀ hC0 (by positivity)).mp hsq
  have hB : (4 / 5 : ℝ) * N * g ≤ B := by
    have he : B + C = N * g := by
      dsimp only [B, C]
      rw [← Finset.sum_add_distrib]
      calc
        _ = ∑ i ∈ s, x i ^ 2 := Finset.sum_congr rfl fun i _ ↦ by ring
        _ = _ := hsecond
    linarith only [he, hC]
  have hS : S ^ 2 ≤ N ^ 2 * g / 100 := by
    have he : S = -(∑ i ∈ s, (1 - r i) * x i) := by
      dsimp only [S]
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib, hmean, zero_sub, neg_neg]
    rw [he, neg_sq]
    have hh := retained_cs s (fun i ↦ 1 - r i) x hmissing
    rw [hsecond] at hh
    calc
      _ ≤ b * (N * g) := hh
      _ ≤ (N / 100) * (N * g) := mul_le_mul_of_nonneg_right hb' (by positivity)
      _ = _ := by ring
  have he : (∑ i ∈ s, r i * (x i - a) ^ 2) = B - 2 * a * S + a ^ 2 * m := by
    dsimp only [B, S, m]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hmargin : 0 ≤ m * ((∑ i ∈ s, r i * (x i - a) ^ 2) - (3 / 4 : ℝ) * N * g) := by
    have hB' : N * g / 20 ≤ B - (3 / 4 : ℝ) * N * g := by linarith only [hB]
    have hh := mul_le_mul hm' hB' (by positivity : 0 ≤ N * g / 20) hm0.le
    rw [he]
    nlinarith only [hh, hS, sq_nonneg (m * a - S), mul_nonneg hN.le hg]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hmargin hm0)

end ABBKS26.Robust.FilterAux
