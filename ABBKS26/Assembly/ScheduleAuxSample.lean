module

public import ABBKS26.Select.Recluster

/-! # Polynomial bounds for the explicit sample ledger -/

@[expose] public section

namespace ABBKS26.Schedule.SampleAux

open _root_.ABBKS26.Tree

private lemma powers {X : ℝ} (hX : 2 ≤ X) {i j : ℕ} (hij : i ≤ j) : X ^ i ≤ X ^ j :=
  pow_le_pow_right₀ (by linarith) hij

/-- A common upper bound on the elementary factors bounds the probability ledger. -/
lemma sampleNeed_bound {w η δ X : ℝ} {k d D : ℕ}
    (hw : 0 < w) (hη : 0 < η) (hδ : 0 < δ) (hk : 0 < k) (hX : 2 ≤ X)
    (hwi : w⁻¹ ≤ X) (hηi : η⁻¹ ≤ X) (hδi : δ⁻¹ ≤ X)
    (hki : (k : ℝ) ≤ X) (hdi : (d : ℝ) + 1 ≤ X)
    (hKD : (64 * D / w) ^ (4 * D) ≤ X)
    (hTD : (2 * (D : ℝ)) ^ D ≤ X)
    (hd2D : ((d : ℝ) + 1) ^ (2 * D) ≤ X)
    (hd9D : ((d : ℝ) + 1) ^ (9 * D) ≤ X) :
    sampleNeed w η δ k d D ≤ X ^ 40 := by
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdX : (d : ℝ) ≤ X := by linarith
  have hX2 : 4 ≤ X ^ 2 := by nlinarith only [pow_le_pow_left₀ (by norm_num) hX 2]
  have hX4 : 16 ≤ X ^ 4 := by nlinarith only [pow_le_pow_left₀ (by norm_num) hX 4]
  have hdiv : (d : ℝ) / η ≤ X ^ 2 := by
    calc
      _ = (d : ℝ) * η⁻¹ := div_eq_mul_inv _ _
      _ ≤ X * X := by gcongr
      _ = _ := (pow_two _).symm
  have hroot : Real.sqrt ((d : ℝ) / η) ≤ X ^ 2 + 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hdiv, sq_nonneg (X ^ 2), hX2]
  have hR : radius d η ≤ X ^ 6 := by
    have hp : 16 * X ^ 2 ≤ X ^ 6 := by
      calc
        _ ≤ X ^ 4 * X ^ 2 := by gcongr
        _ = _ := by ring
    unfold radius
    nlinarith only [hroot, hp, hX2]
  have hR0 : 0 ≤ radius d η := by unfold radius; positivity
  have hprod : (d : ℝ) * radius d η ≤ X ^ 7 := by
    calc
      _ ≤ X * X ^ 6 := by gcongr
      _ = _ := by ring
  have hsum : (d : ℝ) * radius d η + 1 ≤ X ^ 8 := by
    have hp : 2 * X ^ 7 ≤ X ^ 8 := by
      calc
        _ ≤ X * X ^ 7 := by gcongr
        _ = _ := by ring
    have h1 := one_le_pow₀ hX1 (n := 7)
    linarith only [hprod, hp, h1]
  have hlog1 : Real.log (11 * Unif.phi d (radius d η) / (η / 4)) ≤ X ^ 23 := by
    have harg : 11 * Unif.phi d (radius d η) / (η / 4) ≤ X ^ 23 := by
      have hc : 44 ≤ X ^ 6 := (by norm_num : (44 : ℝ) ≤ 2 ^ 6).trans
        (pow_le_pow_left₀ (by norm_num) hX 6)
      calc
        _ = 44 * ((d : ℝ) * radius d η + 1) ^ 2 * η⁻¹ := by
          unfold Unif.phi
          field_simp
          ring
        _ ≤ X ^ 6 * (X ^ 8) ^ 2 * X := by gcongr
        _ = _ := by ring
    exact (Real.log_le_self (by unfold Unif.phi; positivity)).trans harg
  have hlog2 : Real.log (3 / (δ / (4 * k))) ≤ X ^ 6 := by
    have hc : (12 : ℝ) ≤ X ^ 4 := by linarith only [hX4]
    have harg : 3 / (δ / (4 * k)) ≤ X ^ 6 := by
      calc
        _ = 12 * k * δ⁻¹ := by field_simp; ring
        _ ≤ X ^ 4 * X * X := by gcongr
        _ = _ := by ring
    exact (Real.log_le_self (by positivity)).trans harg
  have hdim : (d : ℝ) * d + d + 3 ≤ X ^ 4 := by
    have hs : ((d : ℝ) + 1) ^ 2 ≤ X ^ 2 := by gcongr
    have hp : 4 * X ^ 2 ≤ X ^ 4 := by
      calc
        _ ≤ X ^ 2 * X ^ 2 := by gcongr
        _ = _ := by ring
    nlinarith only [hs, hp, hd0, hX2]
  have hbracket : ((d : ℝ) * d + d + 3) *
      Real.log (11 * Unif.phi d (radius d η) / (η / 4)) +
        Real.log (3 / (δ / (4 * k))) ≤ X ^ 28 := by
    have ht : ((d : ℝ) * d + d + 3) *
        Real.log (11 * Unif.phi d (radius d η) / (η / 4)) ≤ X ^ 27 := by
      calc
        _ ≤ ((d : ℝ) * d + d + 3) * X ^ 23 :=
          mul_le_mul_of_nonneg_left hlog1 (by positivity)
        _ ≤ X ^ 4 * X ^ 23 := by gcongr
        _ = _ := by ring
    have hp : 2 * X ^ 27 ≤ X ^ 28 := by
      calc
        _ ≤ X * X ^ 27 := by gcongr
        _ = _ := by ring
    linarith only [ht, hlog2, powers hX (by norm_num : 6 ≤ 27), hp]
  have hpref : 8 / (η / 4) ^ 2 ≤ X ^ 9 := by
    have hc : (128 : ℝ) ≤ X ^ 7 := (by norm_num : (128 : ℝ) ≤ 2 ^ 7).trans
      (pow_le_pow_left₀ (by norm_num) hX 7)
    calc
      _ = 128 * (η⁻¹) ^ 2 := by field_simp; ring
      _ ≤ X ^ 7 * X ^ 2 := by gcongr
      _ = _ := by ring
  have hunif : Unif.sampleSize d (η / 4) (η / 4) (radius d η) (δ / (4 * k)) ≤
      X ^ 37 := by
    unfold Unif.sampleSize
    calc
      _ ≤ (8 / (η / 4) ^ 2) * X ^ 28 :=
        mul_le_mul_of_nonneg_left hbracket (by positivity)
      _ ≤ X ^ 9 * X ^ 28 := by gcongr
      _ = _ := by ring
  have hcomponent : componentThreshold w η δ k d ≤ X ^ 39 := by
    unfold componentThreshold
    calc
      _ ≤ X ^ 37 / (0.9 * w) := div_le_div_of_nonneg_right hunif (by positivity)
      _ = X ^ 37 * (10 / 9) * w⁻¹ := by field_simp; ring
      _ ≤ X ^ 37 * X * X := by gcongr; norm_num; linarith only [hX]
      _ = _ := by ring
  have hsmall : 32 * ((d : ℝ) + 1) / η ^ 2 ≤ X ^ 8 := by
    have hc : (32 : ℝ) ≤ X ^ 5 := (by norm_num : (32 : ℝ) ≤ 2 ^ 5).trans
      (pow_le_pow_left₀ (by norm_num) hX 5)
    calc
      _ = 32 * ((d : ℝ) + 1) * (η⁻¹) ^ 2 := by field_simp
      _ ≤ X ^ 5 * X * X ^ 2 := by gcongr
      _ = _ := by ring
  have htransfer : 2 * (64 * D / w) ^ (4 * D) * ((d : ℝ) + 1) ^ (2 * D) / η ≤
      X ^ 4 := by
    calc
      _ = 2 * (64 * D / w) ^ (4 * D) * ((d : ℝ) + 1) ^ (2 * D) * η⁻¹ :=
        div_eq_mul_inv _ _
      _ ≤ X * X * X * X := by gcongr
      _ = _ := by ring
  have hlast : 32 * k * ((64 * D / w) ^ (4 * D)) ^ 2 * (2 * (D : ℝ)) ^ D *
      ((d : ℝ) + 1) ^ (9 * D) / (w * η ^ 2 * δ) ≤ X ^ 14 := by
    have hc : (32 : ℝ) ≤ X ^ 5 := (by norm_num : (32 : ℝ) ≤ 2 ^ 5).trans
      (pow_le_pow_left₀ (by norm_num) hX 5)
    calc
      _ = 32 * k * ((64 * D / w) ^ (4 * D)) ^ 2 * (2 * (D : ℝ)) ^ D *
          ((d : ℝ) + 1) ^ (9 * D) * w⁻¹ * (η⁻¹) ^ 2 * δ⁻¹ := by
        field_simp
      _ ≤ X ^ 5 * X * X ^ 2 * X * X * X * X ^ 2 * X := by gcongr
      _ = _ := by ring
  exact max_le (hcomponent.trans (powers hX (by norm_num)))
    (max_le (hsmall.trans (powers hX (by norm_num)))
      (max_le (htransfer.trans (powers hX (by norm_num)))
        (hlast.trans (powers hX (by norm_num)))))

/-- The elementary sample factors fit a dimension and weight monomial. -/
lemma sampleNeed_envelope {w η δ Δ A B : ℝ} {k d D : ℕ}
    (hw : 0 < w) (hη : 0 < η) (hδ : 0 < δ) (hk : 0 < k)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hwi : w⁻¹ ≤ A)
    (hηi : η⁻¹ ≤ 10000 * Δ / w ^ 4) (hδi : δ⁻¹ ≤ B)
    (hkA : (k : ℝ) ≤ A) (hdA : (d : ℝ) + 1 ≤ A)
    (hD : (D : ℝ) ≤ 64 / w) (hΔ : Δ ≤ B) (hΔ0 : 0 ≤ Δ) :
    sampleNeed w η δ k d D ≤ A ^ (40000 * (D + 1)) * B ^ 200 := by
  let E := 1000 * (D + 1)
  let X := A ^ E * B ^ 5
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hAX : A ≤ X := by
    calc
      A ≤ A ^ E := le_self_pow₀ hA1 (by dsimp [E]; omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB1)
  have hBX : B ≤ X := by
    calc
      B ≤ B ^ 5 := le_self_pow₀ hB1 (by norm_num)
      _ ≤ X := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hA1)
  have hX : 2 ≤ X := hA.trans hAX
  have hc64 : (64 : ℝ) ≤ A ^ 6 := (by norm_num : (64 : ℝ) ≤ 2 ^ 6).trans
    (pow_le_pow_left₀ (by norm_num) hA 6)
  have hD7 : (D : ℝ) ≤ A ^ 7 := by
    calc
      _ ≤ 64 / w := hD
      _ = 64 * w⁻¹ := div_eq_mul_inv _ _
      _ ≤ A ^ 6 * A := by gcongr
      _ = _ := by ring
  have hbase : 64 * D / w ≤ A ^ 14 := by
    calc
      _ = 64 * D * w⁻¹ := div_eq_mul_inv _ _
      _ ≤ A ^ 6 * A ^ 7 * A := by gcongr
      _ = _ := by ring
  have hKD : (64 * D / w) ^ (4 * D) ≤ X := by
    calc
      _ ≤ (A ^ 14) ^ (4 * D) := by gcongr
      _ = A ^ (56 * D) := by rw [← pow_mul]; congr 1; omega
      _ ≤ A ^ E := pow_le_pow_right₀ hA1 (by dsimp [E]; omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB1)
  have hbaseT : 2 * (D : ℝ) ≤ A ^ 8 := by
    calc
      _ ≤ A * A ^ 7 := by gcongr
      _ = _ := by ring
  have hTD : (2 * (D : ℝ)) ^ D ≤ X := by
    calc
      _ ≤ (A ^ 8) ^ D := by gcongr
      _ = A ^ (8 * D) := (pow_mul ..).symm
      _ ≤ A ^ E := pow_le_pow_right₀ hA1 (by dsimp [E]; omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB1)
  have hd2D : ((d : ℝ) + 1) ^ (2 * D) ≤ X := by
    calc
      _ ≤ A ^ (2 * D) := by gcongr
      _ ≤ A ^ E := pow_le_pow_right₀ hA1 (by dsimp [E]; omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB1)
  have hd9D : ((d : ℝ) + 1) ^ (9 * D) ≤ X := by
    calc
      _ ≤ A ^ (9 * D) := by gcongr
      _ ≤ A ^ E := pow_le_pow_right₀ hA1 (by dsimp [E]; omega)
      _ ≤ X := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hB1)
  have hηX : η⁻¹ ≤ X := by
    have hc : (10000 : ℝ) ≤ A ^ 14 := (by norm_num : (10000 : ℝ) ≤ 2 ^ 14).trans
      (pow_le_pow_left₀ (by norm_num) hA 14)
    calc
      _ ≤ 10000 * Δ / w ^ 4 := hηi
      _ = 10000 * Δ * (w⁻¹) ^ 4 := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ A ^ 14 * B * A ^ 4 := by gcongr
      _ = A ^ 18 * B := by ring
      _ ≤ X := by
        dsimp [X]
        apply mul_le_mul (pow_le_pow_right₀ hA1 (by dsimp [E]; omega))
          (le_self_pow₀ hB1 (by norm_num)) (by positivity) (by positivity)
  have hh := sampleNeed_bound hw hη hδ hk hX (hwi.trans hAX) hηX
    (hδi.trans hBX) (hkA.trans hAX) (hdA.trans hAX) hKD hTD hd2D hd9D
  dsimp only [X, E] at hh
  simpa only [mul_pow, ← pow_mul,
    show 1000 * (D + 1) * 40 = 40000 * (D + 1) by omega,
    show 5 * 40 = 200 by norm_num] using hh

end ABBKS26.Schedule.SampleAux
