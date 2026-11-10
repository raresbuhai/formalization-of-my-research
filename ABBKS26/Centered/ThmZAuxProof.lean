module

public import ABBKS26.Centered.Feasible
public import ABBKS26.Centered.Norms
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Support for the centered subspace theorem

Quantitative estimates, common complement feasibility, thin-direction geometry, and RC2
packaging. The contract is existential: a complement of one compatible model works for all
models with the same empirical quartic, so no uniform coefficient-norm ledger is needed here.
-/

@[expose] public section

namespace ABBKS26.Centered.ThmZAux

noncomputable section

open Common MvPolynomial Matrix

private theorem scales (w m : ℝ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hm : 0 < m ∧ m ≤ 1 / 64) :
    0 < w ^ 8 * m ^ 32 ∧ w ^ 8 * m ^ 32 ≤ m ^ 32 ∧
      m ^ 32 ≤ m ^ 8 ∧ m ^ 8 ≤ 1 / 4096 ∧ m ^ 32 ≤ 1 / 10000000000 := by
  have hw0 := hw.1
  have hm0 := hm.1
  have hw1 : w ≤ 1 := by linarith only [hw.2]
  have hm1 : m ≤ 1 := by linarith only [hm.2]
  have h8 : m ^ 8 ≤ m ^ 2 := pow_le_pow_of_le_one hm.1.le hm1 (by norm_num)
  have h2 : m ^ 2 ≤ 1 / 4096 := by nlinarith only [hm.1, hm.2]
  have h32 : m ^ 32 ≤ m ^ 8 := pow_le_pow_of_le_one hm.1.le hm1 (by norm_num)
  have hsmall : m ^ 32 ≤ (1 / 64 : ℝ) ^ 32 := pow_le_pow_left₀ hm.1.le hm.2 32
  refine ⟨by positivity, ?_, h32, h8.trans h2, ?_⟩
  · exact mul_le_of_le_one_left (pow_nonneg hm.1.le _) (pow_le_one₀ hw.1.le hw1)
  · exact hsmall.trans (by norm_num)

private theorem ev_schedule (w m : ℝ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hm : 0 < m ∧ m ≤ 1 / 64) :
    let t := w ^ 8 * m ^ 32
    0 < 513 * t ^ 2 / w ^ 2 ∧ 513 * t ^ 2 / w ^ 2 ≤ 16 * w ^ 2 ∧
    ((2 * (513 * t ^ 2 / w ^ 2) + 32 * (1.1 / w) ^ 6 * (12 * t ^ 2)) /
      (32 * w ^ 2)) ^ (1 / 4 : ℝ) ≤ m ^ 8 / 100 := by
  have hw0 := hw.1
  have hm0 := hm.1
  let t := w ^ 8 * m ^ 32
  obtain ⟨ht0, _, _, _, hm32⟩ := scales w m hw hm
  change 0 < t at ht0
  have hw1 : w ≤ 1 := by linarith only [hw.2]
  have hm1 : m ≤ 1 := by linarith only [hm.2]
  have hw4 : w ^ 4 ≤ 1 := pow_le_one₀ hw.1.le hw1
  have hw12 : w ^ 12 ≤ 1 := pow_le_one₀ hw.1.le hw1
  have hm64 : m ^ 64 ≤ 1 / 4096 :=
    (pow_le_pow_of_le_one hm.1.le hm1 (by norm_num : 8 ≤ 64)).trans
      (scales w m hw hm).2.2.2.1
  refine ⟨div_pos (mul_pos (by norm_num) (sq_pos_of_pos ht0))
    (sq_pos_of_pos hw.1), ?_, ?_⟩
  · apply (div_le_iff₀ (sq_pos_of_pos hw.1)).mpr
    have hprod : w ^ 12 * m ^ 64 ≤ 1 / 4096 :=
      (mul_le_mul hw12 hm64 (by positivity) (by norm_num)).trans_eq (by ring)
    have he : t ^ 2 = w ^ 4 * (w ^ 12 * m ^ 64) := by dsimp only [t]; ring
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hprod (pow_nonneg hw.1.le 4)]
  · rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (by positivity) (by positivity)
      (by norm_num : (0 : ℝ) < 4)).2
    change (2 * (513 * t ^ 2 / w ^ 2) +
      32 * (1.1 / w) ^ 6 * (12 * t ^ 2)) / (32 * w ^ 2) ≤ (m ^ 8 / 100) ^ 4
    have hid : (2 * (513 * t ^ 2 / w ^ 2) +
        32 * (1.1 / w) ^ 6 * (12 * t ^ 2)) / (32 * w ^ 2) =
        (1026 / 32 * w ^ 4 + 12 * (1.1 : ℝ) ^ 6) * (t ^ 2 / w ^ 8) := by
      field_simp [hw.1.ne']; ring
    have hc : 1026 / 32 * w ^ 4 + 12 * (1.1 : ℝ) ^ 6 ≤ 100 := by
      norm_num
      linarith only [hw4]
    have ht : t ^ 2 / w ^ 8 ≤ m ^ 64 := by
      have he : t ^ 2 / w ^ 8 = w ^ 8 * m ^ 64 := by
        dsimp only [t]
        field_simp [hw.1.ne']
      rw [he]
      exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ hw.1.le hw1)
    rw [hid]
    calc
      _ ≤ 100 * m ^ 64 := mul_le_mul hc ht (by positivity) (by norm_num)
      _ = 100 * (m ^ 32) ^ 2 := by ring
      _ ≤ m ^ 32 / 100000000 := by
        nlinarith only [mul_le_mul_of_nonneg_left hm32 (pow_nonneg hm.1.le 32)]
      _ = (m ^ 8 / 100) ^ 4 := by ring
    norm_num

private theorem transfer_schedule (w t g : ℝ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (ht : 0 < t ∧ t ≤ 1 / 64) (hg : 0 ≤ g ∧ g ≤ t) :
    2 * (t + g) ^ 4 + 2 / 9 * t ^ 4 ≤ (8 * t ^ 2) ^ 2 ∧
    2 * (64 * (t + g) ^ 4 + 16 * (1.1 / w) ^ 2 * (t + g) ^ 2) +
      192 * t ^ 4 ≤ 256 * t ^ 2 / w ^ 2 ∧
    2 * (8 * t ^ 2) ^ 2 + 2 / 9 * t ^ 4 ≤ (12 * t ^ 2) ^ 2 ∧
    2 * (256 * t ^ 2 / w ^ 2) + 192 * t ^ 4 ≤ 513 * t ^ 2 / w ^ 2 := by
  have hw0 := hw.1
  have h4 : (t + g) ^ 4 ≤ 16 * t ^ 4 := by
    convert pow_le_pow_left₀ (show 0 ≤ t + g by linarith only [ht.1, hg.1])
      (by linarith only [hg.2] : t + g ≤ 2 * t) 4 using 1; ring
  have h2 : (t + g) ^ 2 ≤ 4 * t ^ 2 := by
    convert pow_le_pow_left₀ (show 0 ≤ t + g by linarith only [ht.1, hg.1])
      (by linarith only [hg.2] : t + g ≤ 2 * t) 2 using 1; ring
  have ht2 : t ^ 2 ≤ 1 / 4096 := by nlinarith only [ht.1, ht.2]
  have hw2 : w ^ 2 ≤ 1 := pow_le_one₀ hw.1.le (by linarith only [hw.2])
  have ht4 : t ^ 4 * w ^ 2 ≤ t ^ 2 / 4096 := by
    have htw := mul_le_mul ht2 hw2 (sq_nonneg w) (by norm_num : (0 : ℝ) ≤ 1 / 4096)
    nlinarith only [mul_le_mul_of_nonneg_left htw (sq_nonneg t)]
  have hid : (1.1 / w) ^ 2 * w ^ 2 = (1.1 : ℝ) ^ 2 := by field_simp [hw.1.ne']
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [h4, pow_nonneg ht.1.le 4]
  · apply (le_div_iff₀ (sq_pos_of_pos hw.1)).mpr
    have ha := mul_le_mul_of_nonneg_right h4 (sq_nonneg w)
    have hb := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (1.1 / w) ^ 2)
    have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg w)
    have hb'' : (1.1 / w) ^ 2 * (t + g) ^ 2 * w ^ 2 ≤
        4 * t ^ 2 * (1.1 : ℝ) ^ 2 := by
      calc
        _ ≤ (1.1 / w) ^ 2 * (4 * t ^ 2) * w ^ 2 := hb'
        _ = _ := by rw [mul_right_comm _ _ (w ^ 2), hid]; ring
    have he : (2 * (64 * (t + g) ^ 4 +
        16 * (1.1 / w) ^ 2 * (t + g) ^ 2) + 192 * t ^ 4) * w ^ 2 =
        128 * ((t + g) ^ 4 * w ^ 2) +
          32 * ((1.1 / w) ^ 2 * (t + g) ^ 2 * w ^ 2) +
          192 * (t ^ 4 * w ^ 2) := by ring
    rw [he]
    nlinarith only [ha, hb'', ht4, sq_nonneg t]
  · nlinarith only [pow_nonneg ht.1.le 4]
  · apply (le_div_iff₀ (sq_pos_of_pos hw.1)).mpr
    have he : (2 * (256 * t ^ 2 / w ^ 2) + 192 * t ^ 4) * w ^ 2 =
        512 * t ^ 2 + 192 * (t ^ 4 * w ^ 2) := by field_simp [hw.1.ne']; ring
    rw [he]
    nlinarith only [ht4, sq_nonneg t]

/-- Scalar estimates for feasibility, transfer, and evaluation identifiability. -/
theorem schedule (w m g : ℝ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hm : 0 < m ∧ m ≤ 1 / 64) (hg : 0 ≤ g ∧ g ≤ (w ^ 8 * m ^ 32) ^ 2 / 20) :
    let t := w ^ 8 * m ^ 32
    0 < t ∧ t ≤ 1 / 64 ∧ g ≤ t ∧ g ^ 2 ≤ m ^ 8 / 400 ∧
    0 < m ^ 8 / 100 ∧ m ^ 8 / 100 ≤ 1 ∧
    0 < 513 * t ^ 2 / w ^ 2 ∧ 513 * t ^ 2 / w ^ 2 ≤ 16 * w ^ 2 ∧
    ((2 * (513 * t ^ 2 / w ^ 2) + 32 * (1.1 / w) ^ 6 * (12 * t ^ 2)) /
      (32 * w ^ 2)) ^ (1 / 4 : ℝ) ≤ m ^ 8 / 100 ∧
    2 * (t + g) ^ 4 + 2 / 9 * t ^ 4 ≤ (8 * t ^ 2) ^ 2 ∧
    2 * (64 * (t + g) ^ 4 + 16 * (1.1 / w) ^ 2 * (t + g) ^ 2) +
      192 * t ^ 4 ≤ 256 * t ^ 2 / w ^ 2 ∧
    2 * (8 * t ^ 2) ^ 2 + 2 / 9 * t ^ 4 ≤ (12 * t ^ 2) ^ 2 ∧
    2 * (256 * t ^ 2 / w ^ 2) + 192 * t ^ 4 ≤ 513 * t ^ 2 / w ^ 2 := by
  have hm0 := hm.1
  obtain ⟨ht0, htm32, hm32, hm8, _⟩ := scales w m hw hm
  let t := w ^ 8 * m ^ 32
  have ht : t ≤ 1 / 64 := (htm32.trans (hm32.trans hm8)).trans (by norm_num)
  have hgt : g ≤ t := by change 0 ≤ g ∧ g ≤ t ^ 2 / 20 at hg; nlinarith only [hg.2, ht0, ht]
  have hg20 : g ≤ t / 20 := by
    change 0 ≤ g ∧ g ≤ t ^ 2 / 20 at hg
    nlinarith only [hg.2, ht0, ht]
  have hg2 : g ^ 2 ≤ m ^ 8 / 400 := by
    have ht8 : t ≤ m ^ 8 := htm32.trans hm32
    have hs : t ^ 2 ≤ m ^ 8 := by
      have hh := pow_le_pow_left₀ ht0.le ht8 2
      nlinarith only [hh, hm8, pow_nonneg hm.1.le 8]
    have hh := pow_le_pow_left₀ hg.1 hg20 2
    nlinarith only [hh, hs]
  obtain ⟨he0, he1, hev⟩ := ev_schedule w m hw hm
  obtain ⟨h₁, h₂, h₃, h₄⟩ := transfer_schedule w t g hw ⟨ht0, ht⟩ ⟨hg.1, hgt⟩
  exact ⟨ht0, ht, hgt, hg2, by positivity, by linarith only [hm8],
    he0, he1, hev, h₁, h₂, h₃, h₄⟩

end

end ABBKS26.Centered.ThmZAux

namespace ABBKS26.Centered.ThmZAux

noncomputable section

open Common MvPolynomial Matrix
open scoped BigOperators

variable {k d : ℕ}


theorem empirical_homogeneous (p : RPoly d) (hp : p.IsHomogeneous 4) :
    (p - 3 * nsq ^ 2).IsHomogeneous 4 := by
  exact hp.sub (by simpa only [map_ofNat] using
    (IdentAux.nsq_homogeneous.pow 2).C_mul 3)


end

end ABBKS26.Centered.ThmZAux

namespace ABBKS26.Centered.ThmZAux

noncomputable section

open Common MvPolynomial Matrix
open scoped BigOperators

variable {k d : ℕ}


end

end ABBKS26.Centered.ThmZAux

namespace ABBKS26.Centered.ThmZAux

noncomputable section

open Common MvPolynomial Matrix

variable {d : ℕ}


end

end ABBKS26.Centered.ThmZAux

namespace ABBKS26.Centered.ThmZAux

noncomputable section

open Common MvPolynomial Matrix

variable {k d : ℕ}

theorem delta_cast (w m : ℚ) : (delta w m : ℝ) = (w : ℝ) ^ 8 * (m : ℝ) ^ 32 := by
  simp only [delta, nu, Rat.cast_pow, Rat.cast_mul]
  ring

theorem gamma_cast (w m : ℚ) :
    (gammaStar w m : ℝ) = ((w : ℝ) ^ 8 * (m : ℝ) ^ 32) ^ 2 / 20 := by
  simp only [gammaStar, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, delta_cast]


end

end ABBKS26.Centered.ThmZAux
