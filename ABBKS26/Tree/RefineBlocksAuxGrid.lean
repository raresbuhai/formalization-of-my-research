module

public import ABBKS26.Tree.RefineAuxCore

/-! A finite dyadic grid meets a multiplicative gap between component deviations. -/

@[expose] public section

namespace ABBKS26.Tree.RefineBlocksAux

noncomputable section

open Common Matrix
open scoped BigOperators

private theorem sqrtUp_le (C : ℚ) (hC : 1 ≤ C) : sqrtUp C ≤ 3 * C := by
  have hc : (⌈C⌉₊ : ℚ) < C + 1 := Nat.ceil_lt_add_one (by linarith only [hC])
  have hs : (Nat.sqrt ⌈C⌉₊ : ℚ) ≤ ⌈C⌉₊ := by
    exact_mod_cast Nat.sqrt_le_self ⌈C⌉₊
  have he : max 0 C = C := max_eq_right (by linarith only [hC])
  unfold sqrtUp
  rw [he]
  push_cast
  linarith only [hc, hs, hC]

private theorem grid_last (p : StepParams) (C : ℚ) (hC : C = 4 / p.w)
    (hC1 : 1 ≤ C) (hβ : 0 < p.subspaceAccuracy) :
    (2 * (sqrtUp C : ℝ)) / 2 ^ (ABBKS26.RefineAux.spectralThresholdCount p - 1) ≤
      (p.subspaceAccuracy : ℝ) ^ 2 / C := by
  let J := ⌈256 * C ^ 2 / p.subspaceAccuracy ^ 2⌉₊
  have hp : (256 * (C : ℝ) ^ 2 / (p.subspaceAccuracy : ℝ) ^ 2) ≤
      (2 : ℝ) ^ Nat.clog 2 J := by
    have hc : 256 * C ^ 2 / p.subspaceAccuracy ^ 2 ≤ J := Nat.le_ceil _
    have hh := Nat.le_pow_clog (by norm_num : 1 < 2) J
    have hcR : 256 * (C : ℝ) ^ 2 / (p.subspaceAccuracy : ℝ) ^ 2 ≤ J := by
      exact_mod_cast hc
    exact hcR.trans (by exact_mod_cast hh)
  have hβR : (0 : ℝ) < p.subspaceAccuracy := by exact_mod_cast hβ
  have hCR : (1 : ℝ) ≤ C := by exact_mod_cast hC1
  have hs : (sqrtUp C : ℝ) ≤ 3 * C := by exact_mod_cast sqrtUp_le C hC1
  have he : ABBKS26.RefineAux.spectralThresholdCount p - 1 = Nat.clog 2 J + 4 := by
    simp only [ABBKS26.RefineAux.spectralThresholdCount, ← hC, J]
    omega
  rw [he, pow_add]
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ Nat.clog 2 J * 16)).mpr
  have hp' := (div_le_iff₀ (sq_pos_of_pos hβR)).mp hp
  have hC0 : (0 : ℝ) < C := by linarith only [hCR]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hC0).mpr
  nlinarith only [hp', hs, hCR, sq_nonneg ((C : ℝ) - 1)]

/-- Clip deviations below the input-determined floor before finding the gap. -/
theorem spectral_grid {m : ℕ} (p : StepParams) (σ : Fin m → ℝ)
    (hm : 2 ≤ m) (hw : 0 < p.w ∧ p.w ≤ 1 / 2)
    (hβ : 0 < p.subspaceAccuracy) (hK : 1 ≤ p.K)
    (htail : 0 < p.tail ∧ p.tail ≤ 1)
    (hbudget : (p.subspaceAccuracy : ℝ) *
      (1024 * (p.K : ℝ) ^ 2 / p.tail) ^ (2 * (m - 1)) ≤ 1 / (128 * (4 / p.w : ℝ)))
    (hupper : ∀ j, σ j ≤ 2 * (sqrtUp (4 / p.w) : ℝ))
    (hsmall : ∃ j, σ j ≤ 64 * (4 / p.w : ℝ) * p.subspaceAccuracy)
    (hlarge : ∃ j, 1 / 2 < σ j) :
    ∃ i < ABBKS26.RefineAux.spectralThresholdCount p,
      let t : ℚ := 2 * sqrtUp (4 / p.w) / 2 ^ i
      let R : ℝ := 8 / p.tail
      (∀ j, σ j ≤ (t : ℝ) / (2 * p.K * R) ∨ (t : ℝ) * p.K * R ≤ σ j) ∧
      (∃ j, σ j ≤ (t : ℝ) / (2 * p.K * R)) ∧
      (∃ j, (t : ℝ) * p.K * R ≤ σ j) := by
  classical
  let C : ℝ := 4 / p.w
  let β : ℝ := p.subspaceAccuracy
  let B : ℝ := 1024 * (p.K : ℝ) ^ 2 / p.tail
  let R : ℝ := 8 / p.tail
  let L : ℝ := 64 * C * β
  let Q : ℝ := (B ^ 2) ^ (m - 1)
  let H : ℝ := 2 * (sqrtUp (4 / p.w) : ℝ)
  have hwR : (0 : ℝ) < p.w := by exact_mod_cast hw.1
  have hw2 : (p.w : ℝ) ≤ 1 / 2 := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr hw.2
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hC : 1 ≤ C := by dsimp only [C]; rw [le_div_iff₀ hwR]; linarith only [hw2]
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hβ0 : 0 < β := by change 0 < (p.subspaceAccuracy : ℝ); exact_mod_cast hβ
  have hKR : (1 : ℝ) ≤ p.K := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < p.K := zero_lt_one.trans_le hKR
  have ht0 : (0 : ℝ) < p.tail := by exact_mod_cast htail.1
  have ht1 : (p.tail : ℝ) ≤ 1 := by exact_mod_cast htail.2
  have hR : 1 ≤ R := by dsimp only [R]; rw [le_div_iff₀ ht0]; linarith only [ht1]
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hB : 1 < B := by
    dsimp only [B]
    rw [lt_div_iff₀ ht0]
    nlinarith only [one_le_pow₀ hKR (n := 2), ht1]
  have hQ : 1 < Q := one_lt_pow₀ (one_lt_pow₀ hB (by norm_num : 2 ≠ 0)) (by omega)
  have hQ1 : 1 ≤ Q := hQ.le
  have hL : 0 < L := by dsimp only [L]; positivity
  have hQL : Q * L ≤ 1 / 2 := by
    have he : Q = B ^ (2 * (m - 1)) := by dsimp only [Q]; rw [← pow_mul]
    rw [he]
    have hh := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 64 * C)
    change 64 * C * (β * B ^ (2 * (m - 1))) ≤ 64 * C * (1 / (128 * C)) at hh
    have hc : 64 * C * (1 / (128 * C)) = 1 / 2 := by field_simp; ring
    rw [hc] at hh
    nlinarith only [hh]
  have hLhalf : L ≤ 1 / 2 := (le_mul_of_one_le_left hL.le hQ1).trans hQL
  have hH : 1 / 2 ≤ H := by
    have hs : (1 : ℚ) ≤ sqrtUp (4 / p.w) := by unfold sqrtUp; norm_cast; omega
    have hsR : (1 : ℝ) ≤ sqrtUp (4 / p.w) := by exact_mod_cast hs
    dsimp only [H]
    linarith only [hsR]
  let s : Fin m → ℝ := fun j ↦ max L (σ j)
  obtain ⟨a, ha⟩ := hsmall
  obtain ⟨b, hb⟩ := hlarge
  have hab : Q * s a < s b := by
    have ha' : s a = L := max_eq_left ha
    rw [ha']
    exact hQL.trans_lt (hb.trans_le (le_max_right _ _))
  obtain ⟨lo, hi, hlo, _, hloI, hhiI, hgap, hside⟩ :=
    CompleteAux.multiplicative_gap Finset.univ s Q hQ
      (fun j _ ↦ hL.trans_le (le_max_left _ _)) hm a b (by simp) (by simp) hab
  have hroot : Q ^ (1 / ((m : ℝ) - 1)) = B ^ 2 := by
    have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [← hmcast, one_div]
    exact Real.pow_rpow_inv_natCast (sq_nonneg B) (by omega)
  rw [hroot] at hgap
  obtain ⟨a', _, ha'⟩ := Finset.mem_image.mp hloI
  obtain ⟨b', _, hb'⟩ := Finset.mem_image.mp hhiI
  have hLlo : L ≤ lo := ha' ▸ le_max_left L (σ a')
  have hhi : lo < hi :=
    (le_mul_of_one_le_left hlo.le (one_le_pow₀ hB.le)).trans_lt hgap
  have hLhi : L < hi := hLlo.trans_lt hhi
  have hσb : σ b' = hi := by
    change max L (σ b') = hi at hb'
    have hh : L < max L (σ b') := hb'.symm ▸ hLhi
    have hh' : L < σ b' := (lt_max_iff.mp hh).resolve_left (lt_irrefl L)
    simpa only [max_eq_right hh'.le] using hb' 
  have hhiH : hi ≤ H := hσb ▸ hupper b'
  let t₀ := hi / (2 * p.K * R)
  have ht₀ : 0 < t₀ := by dsimp only [t₀]; positivity
  have htH : t₀ ≤ H :=
    (div_le_self (hL.trans hLhi).le (by nlinarith only [hKR, hR])).trans hhiH
  have hBKR : 8 * (p.K : ℝ) ^ 2 * R ^ 2 ≤ B ^ 2 := by
    dsimp only [B, R]
    field_simp
    nlinarith only [one_le_pow₀ hKR (n := 2)]
  have hβB : β * B ≤ 1 := by
    have hBB : B ≤ B ^ (2 * (m - 1)) :=
      le_self_pow₀ hB.le (by omega)
    have hh := (mul_le_mul_of_nonneg_left hBB hβ0.le).trans hbudget
    have hc : 1 / (128 * C) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 128 * C)]
      linarith only [hC]
    exact hh.trans hc
  have hKRβ : β * (2 * (p.K : ℝ) * R) ≤ 1 := by
    have hh : 2 * (p.K : ℝ) * R ≤ B := by
      dsimp only [R, B]
      rw [← mul_div_assoc, div_le_div_iff_of_pos_right ht0]
      nlinarith only [hKR, sq_nonneg ((p.K : ℝ) - 1)]
    exact (mul_le_mul_of_nonneg_left hh hβ0.le).trans hβB
  have hfloor : β ^ 2 / C ≤ t₀ := by
    rw [div_le_iff₀ hC0]
    dsimp only [t₀]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hKRβ hβ0.le
    have hhC := mul_le_mul_of_nonneg_right (hLlo.trans hhi.le) hC0.le
    have hCC : β ≤ 64 * C ^ 2 * β := by
      have hc : 1 ≤ 64 * C ^ 2 := by nlinarith only [hC]
      nlinarith only [mul_le_mul_of_nonneg_right hc hβ0.le]
    dsimp only [L] at hhC
    nlinarith only [hh, hhC, hCC]
  have hlast : H / (2 : ℝ) ^ (ABBKS26.RefineAux.spectralThresholdCount p - 1) ≤ t₀ :=
    (by
      have hcQ : (1 : ℚ) ≤ 4 / p.w := by
        rw [le_div_iff₀ hw.1]
        linarith only [hw.2]
      have hh := grid_last p (4 / p.w) rfl hcQ hβ
      push_cast at hh
      exact hh.trans hfloor)
  obtain ⟨i, hiT, hti, hit⟩ := ABBKS26.RefineAux.dyadic_cover H t₀
    (ABBKS26.RefineAux.spectralThresholdCount p) ht₀.le
    (by unfold ABBKS26.RefineAux.spectralThresholdCount; omega) htH hlast
  let t : ℚ := 2 * sqrtUp (4 / p.w) / 2 ^ i
  have htcast : (t : ℝ) = H / (2 : ℝ) ^ i := by dsimp only [t, H]; push_cast; rfl
  have htlo : t₀ / 2 ≤ (t : ℝ) := by rwa [← htcast] at hti
  have hthi : (t : ℝ) ≤ t₀ := by rwa [← htcast] at hit
  have hlow (j) (hj : s j ≤ lo) : σ j ≤ (t : ℝ) / (2 * p.K * R) := by
    have hjlo : σ j ≤ lo := (le_max_right _ _).trans hj
    rw [le_div_iff₀ (by positivity)]
    have hh : lo * (8 * (p.K : ℝ) ^ 2 * R ^ 2) ≤ hi :=
      (mul_le_mul_of_nonneg_left hBKR hlo.le).trans (by nlinarith only [hgap])
    have hht := (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp htlo
    change hi / (2 * (p.K : ℝ) * R) ≤ (t : ℝ) * 2 at hht
    have hhe := (div_le_iff₀ (by positivity : 0 < 2 * (p.K : ℝ) * R)).mp hht
    have hmul := mul_le_mul_of_nonneg_right hjlo
      (by positivity : 0 ≤ 8 * (p.K : ℝ) ^ 2 * R ^ 2)
    apply (mul_le_mul_iff_left₀ (show 0 < 4 * (p.K : ℝ) * R by positivity)).mp
    nlinarith only [hh, hhe, hmul]
  have hhigh (j) (hj : hi ≤ s j) : (t : ℝ) * p.K * R ≤ σ j := by
    have hjσ : hi ≤ σ j := by
      rcases le_max_iff.mp hj with hh | hh
      · exact (not_le_of_gt hLhi hh).elim
      · exact hh
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * (p.K : ℝ) * R)).mp hthi
    nlinarith only [hh, hjσ, (hL.trans hLhi).le]
  refine ⟨i, hiT, ?_, ⟨a', hlow a' ha'.le⟩, ⟨b', hhigh b' hb'.ge⟩⟩
  intro j
  exact (hside j (by simp)).imp (hlow j) (hhigh j)

end

end ABBKS26.Tree.RefineBlocksAux
