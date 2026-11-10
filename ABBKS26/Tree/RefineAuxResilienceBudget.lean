module

public import ABBKS26.Tree.RefineAuxResilience

/-! The sample and moment budgets imply the affine resilience bounds at every required degree. -/

@[expose] public section

namespace ABBKS26.RefineAux.Resilience

noncomputable section

open Common Matrix MvPolynomial Finset _root_.ABBKS26.Tree
open scoped BigOperators

variable {n k d : ℕ}

/-- Keep the full dimension power in the monomial budget. -/
theorem momentAccuracy_scaled (w η : ℝ) (d D : ℕ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hη : 0 ≤ η) (hD : 8 ≤ D) :
    (2 * momentAccuracy w η d D / w) * (d + 1 : ℝ) ^ (4 * D) ≤ η / 10 ^ 12 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hbase : (512 : ℝ) ≤ 64 * D := by exact_mod_cast (by omega : 512 ≤ 64 * D)
  have hpow : (2 : ℝ) * 10 ^ 12 ≤ (64 * D : ℝ) ^ (4 * D) := by
    calc
      _ ≤ (512 : ℝ) ^ 32 := by norm_num
      _ ≤ (64 * D : ℝ) ^ 32 := pow_le_pow_left₀ (by norm_num) hbase 32
      _ ≤ _ := pow_le_pow_right₀ (by linarith only [hbase]) (by omega)
  have hwD : w ^ (4 * D) ≤ w := pow_le_of_le_one hw.le hw1 (by omega)
  have heq : (2 * momentAccuracy w η d D / w) * (d + 1 : ℝ) ^ (4 * D) =
      (2 * η / (64 * D : ℝ) ^ (4 * D)) * (w ^ (4 * D) / w) := by
    unfold momentAccuracy
    rw [div_pow]
    have ht : (64 * (d + 1 : ℝ) * D) ^ (4 * D) =
        (64 * D : ℝ) ^ (4 * D) * (d + 1 : ℝ) ^ (4 * D) := by
      rw [← mul_pow]
      congr 1
      ring
    rw [ht]
    field_simp
  rw [heq]
  calc
    _ ≤ (2 * η / (64 * D : ℝ) ^ (4 * D)) * 1 :=
      mul_le_mul_of_nonneg_left ((div_le_one hw).mpr hwD) (by positivity)
    _ ≤ η / 10 ^ 12 := by
      rw [mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [mul_le_mul_of_nonneg_left hpow hη]

/-- The inverse sample bound retains the degree-dependent coefficient allowance. -/
theorem inverse_sample_scaled
    (M : Mixture k d) (w η : ℝ) (D : ℕ) (hM : M.Valid)
    (hw : 0 < w) (hwj : ∀ j, w ≤ M.w j) (hη : 0 < η) (hη100 : η ≤ 1 / 100)
    (hD : 8 ≤ D) (hn : sampleNeed w η (1 / 2) k d D ≤ n) (j : Fin k) :
    (1 / (n : ℝ)) * (64 * D / w) ^ (4 * D) * (d + 1 : ℝ) ^ (9 * D) ≤
      η / 10 ^ 12 := by
  have hw1 : w ≤ 1 := (hwj j).trans (hM.sum_w ▸
    single_le_sum (fun i _ ↦ hM.nonneg_w i) (mem_univ j))
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast j.pos
  have hD8 : (8 : ℝ) ≤ D := by exact_mod_cast hD
  let K : ℝ := (64 * D / w) ^ (4 * D)
  have hbase : (512 : ℝ) ≤ 64 * D / w := by
    rw [le_div_iff₀ hw]
    nlinarith only [hD8, hw1]
  have hK : (10 : ℝ) ^ 12 ≤ K := by
    calc
      _ ≤ (512 : ℝ) ^ 32 := by norm_num
      _ ≤ (64 * D / w) ^ 32 := pow_le_pow_left₀ (by norm_num) hbase 32
      _ ≤ K := pow_le_pow_right₀ (by linarith only [hbase]) (by omega)
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 10 ^ 12).trans hK
  have hpow : (1 : ℝ) ≤ (2 * D : ℝ) ^ D :=
    one_le_pow₀ (by linarith only [hD8])
  have hcoef : 10 ^ 12 * K ≤ 32 * k * K ^ 2 * (2 * D : ℝ) ^ D := by
    calc
      _ ≤ K ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hK hK0]
      _ = 1 * 1 * K ^ 2 * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have hden : 0 < w * η ^ 2 * (1 / 2) := by positivity
  have hdenη : w * η ^ 2 * (1 / 2) ≤ η := by
    have hh := mul_le_mul_of_nonneg_right hw1 (sq_nonneg η)
    nlinarith only [hh, hη, hη100]
  have hlast : 32 * k * K ^ 2 * (2 * D : ℝ) ^ D *
      (d + 1 : ℝ) ^ (9 * D) / (w * η ^ 2 * (1 / 2)) ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans hn))
  have hsize : 10 ^ 12 * K * (d + 1 : ℝ) ^ (9 * D) ≤ (n : ℝ) * η := by
    calc
      _ ≤ 32 * k * K ^ 2 * (2 * D : ℝ) ^ D * (d + 1 : ℝ) ^ (9 * D) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ (n : ℝ) * (w * η ^ 2 * (1 / 2)) := (div_le_iff₀ hden).mp hlast
      _ ≤ (n : ℝ) * η := mul_le_mul_of_nonneg_left hdenη (Nat.cast_nonneg n)
  have hn0 : (0 : ℝ) < n := by
    have hKpos : 0 < K := (by norm_num : (0 : ℝ) < 10 ^ 12).trans_le hK
    have hh : 0 < (n : ℝ) * η := lt_of_lt_of_le (by positivity) hsize
    rcases mul_pos_iff.mp hh with hh | hh
    · exact hh.1
    · exact False.elim (not_lt_of_ge hη.le hh.2)
  change (1 / (n : ℝ)) * K * (d + 1 : ℝ) ^ (9 * D) ≤ _
  rw [one_div_mul_eq_div, div_mul_eq_mul_div, div_le_div_iff₀ hn0 (by norm_num)]
  nlinarith only [hsize]

/-- The degree allowance pays for the coefficient in the even-moment rounding bound. -/
theorem rounding_coefficient_le (w δ : ℝ) (s D : ℕ)
    (hw : 0 < w) (hw1 : w ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (hD : 8 ≤ D) (hs : s ≤ D) (heven : Even s) :
    (s : ℝ) * 2 ^ s * (1 + (gaussMom s : ℝ) + δ) ≤
      (64 * D / w) ^ (4 * D) := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (by omega : 1 ≤ D)
  have hgm : (gaussMom s : ℝ) ≤ (2 * D : ℝ) ^ D := by
    obtain ⟨a, ha⟩ := heven
    have heq : s = 2 * a := by omega
    have hg : (gaussMom (2 * a) : ℝ) ≤ (2 * a : ℝ) ^ a := by
      exact_mod_cast Gauss.gaussMom_two_mul_le a
    rw [heq]
    exact hg.trans ((pow_le_pow_left₀ (by positivity)
      (by exact_mod_cast (by omega : 2 * a ≤ 2 * D)) a).trans
        (pow_le_pow_right₀ (by linarith only [hD1]) (by omega)))
  let b : ℝ := 64 * D / w
  have hbD : (64 * D : ℝ) ≤ b := by
    dsimp only [b]
    rw [le_div_iff₀ hw]
    exact mul_le_of_le_one_right (by positivity) hw1
  have hb1 : 1 ≤ b := by linarith only [hbD, hD1]
  have hsp : (s : ℝ) ≤ b ^ D := by
    have hsR : (s : ℝ) ≤ D := by exact_mod_cast hs
    exact (by linarith only [hsR, hbD, hD1] : (s : ℝ) ≤ b).trans
      (le_self_pow₀ hb1 (by omega))
  have htwo : (2 : ℝ) ^ s ≤ b ^ D :=
    (pow_le_pow_left₀ (by norm_num) (by linarith only [hbD, hD1]) s).trans
      (pow_le_pow_right₀ hb1 hs)
  have hgp : 1 + (gaussMom s : ℝ) + δ ≤ b ^ D := by
    have hp1 : (1 : ℝ) ≤ (2 * D : ℝ) ^ D := one_le_pow₀ (by linarith only [hD1])
    calc
      _ ≤ 3 * (2 * D : ℝ) ^ D := by linarith only [hgm, hδ, hp1]
      _ ≤ (3 : ℝ) ^ D * (2 * D : ℝ) ^ D :=
        mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num) (by omega)) (by positivity)
      _ = (6 * D : ℝ) ^ D := by rw [← mul_pow]; congr 1; ring
      _ ≤ b ^ D := pow_le_pow_left₀ (by positivity) (by linarith only [hbD, hD1]) D
  calc
    _ ≤ b ^ D * b ^ D * b ^ D :=
      mul_le_mul (mul_le_mul hsp htwo (by positivity) (by positivity)) hgp
        (by positivity) (by positivity)
    _ = b ^ (3 * D) := by rw [show 3 * D = D + D + D by omega, pow_add, pow_add]
    _ ≤ b ^ (4 * D) := pow_le_pow_right₀ hb1 (by omega)

/-- The good-event budgets give rounded coefficient accuracy through any required even degree. -/
theorem rounded_moments_scheduled
    (M : Mixture k d) (ε w η : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d)
    (hM : M.Valid) (hg : Good M ε w η D ω) (hr : IsRounding M (1 / n) r)
    (hw : 0 < w) (hwj : ∀ j, w ≤ M.w j) (hη : 0 < η) (hη100 : η ≤ 1 / 100)
    (hD : 8 ≤ D) (hn : sampleNeed w η (1 / 2) k d D ≤ n)
    (j : Fin k) (s : ℕ) (hs0 : 0 < s) (hs : s ≤ D) (heven : Even s)
    (q : ℕ) (hq : q ≤ s) :
    SoS.coeffNorm1 (empMom (cluster (labels ω) j) (standardizedRounded M ω r) q -
      gaussPoly q) ≤ (η / 10 ^ 8) / (d + 1 : ℝ) ^ (3 * s) := by
  let S := cluster (labels ω) j
  let g : Fin n → Vec d := fun l i ↦ stdClean M ω l i
  let δ := 2 * momentAccuracy w η d D / w
  let τ : ℝ := 1 / n
  let t : ℝ := d + 1
  let K : ℝ := (64 * D / w) ^ (4 * D)
  let B : ℝ := (s : ℝ) * 2 ^ s * (1 + (gaussMom s : ℝ) + δ)
  have ht : 1 ≤ t := by dsimp only [t]; linarith only [Nat.cast_nonneg (α := ℝ) d]
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hδ : 0 ≤ δ := by dsimp only [δ, momentAccuracy]; positivity
  have hτ : 0 ≤ τ := by dsimp only [τ]; positivity
  have hw1 : w ≤ 1 := (hwj j).trans (hM.sum_w ▸
    single_le_sum (fun i _ ↦ hM.nonneg_w i) (mem_univ j))
  have hδscaled := momentAccuracy_scaled w η d D hw hw1 hη.le hD
  change δ * t ^ (4 * D) ≤ η / 10 ^ 12 at hδscaled
  have hδ1 : δ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ ht (n := 4 * D)) hδ
    nlinarith only [hh, hδscaled, hη100]
  have hm (α : Fin d → ℕ) (hα : (∑ i, α i) ≤ s) :
      |(S.card : ℝ)⁻¹ * ∑ l ∈ S, ∏ i, g l i ^ α i - gaussMomMulti α| ≤ δ := by
    simpa only [S, g, δ, div_eq_inv_mul] using
      moment_resilience M ε w η D ω r hM hg hr hw hwj ⟨hη, hη100⟩
        (by omega) j s hs α hα
  have hne : S.Nonempty := card_pos.mp (SoundAux.good_cluster_pos M ε w η D ω hg j)
  have hτsmall : (d : ℝ) * τ ≤ 1 := by
    have hi := inverse_sample_relative M w η D hM hw hwj hη hη100 hD hn j
    have hd : (d : ℝ) ≤ t ^ 20 :=
      (by dsimp only [t]; linarith : (d : ℝ) ≤ t).trans (le_self_pow₀ ht (by omega))
    apply (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg d)).trans
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have hh := mul_le_mul_of_nonneg_right hη100 (Nat.cast_nonneg (α := ℝ) d)
    nlinarith only [hd, hh, Nat.cast_nonneg (α := ℝ) d]
  have hc := rounded_moments_even S hne g (standardizedRounded M ω r) s hs0 heven
    δ τ hδ hτ hτsmall hm (standardizedRounded_error M ω r hM hr) q hq
  have hB : B ≤ K := rounding_coefficient_le w δ s D hw hw1 hδ hδ1 hD hs heven
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hτscaled := inverse_sample_scaled M w η D hM hw hwj hη hη100 hD hn j
  change τ * K * t ^ (9 * D) ≤ η / 10 ^ 12 at hτscaled
  have hclean : δ * (d : ℝ) ^ q * t ^ (3 * s) ≤ η / 10 ^ 12 := by
    calc
      _ ≤ δ * t ^ s * t ^ (3 * s) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hδ
        exact (pow_le_pow_left₀ (Nat.cast_nonneg d)
          (by dsimp only [t]; linarith) q).trans (pow_le_pow_right₀ ht hq)
      _ = δ * t ^ (4 * s) := by rw [show 4 * s = s + 3 * s by omega, pow_add]; ring
      _ ≤ δ * t ^ (4 * D) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (by omega)) hδ
      _ ≤ η / 10 ^ 12 := hδscaled
  have hround : (τ * B * t ^ (s + 1)) * t ^ (3 * s) ≤ η / 10 ^ 12 := by
    calc
      _ = τ * B * t ^ (s + 1 + 3 * s) := by rw [pow_add]; ring
      _ ≤ τ * K * t ^ (9 * D) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hB hτ)
          (pow_le_pow_right₀ ht (by omega)) (by positivity) (mul_nonneg hτ hK)
      _ ≤ η / 10 ^ 12 := hτscaled
  apply hc.trans
  rw [le_div_iff₀ (pow_pos ht0 _), add_mul]
  change δ * (d : ℝ) ^ q * t ^ (3 * s) + (τ * B * t ^ (s + 1)) * t ^ (3 * s) ≤ _
  nlinarith only [hclean, hround, hη]

end

end ABBKS26.RefineAux.Resilience
