module

public import BHSV25.Spectral.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Parameters for independent sets

The thresholds and the loss function of [BHSV25, Theorem 1.1], as functions of `λ`.

* `τ = 2λ / (1 + λ)` (`BHSV25.Alg.tauOf`) lies in `(λ, 1)` for `λ ∈ (0, 1)`: the eigenvalues at
  least `τ` are larger than `λ`, and [BHSV25, Corollary 4.2] with `σ = τ` bounds the number of
  eigenvalues at most `-θ₀`, for `θ₀ = √(τ (1 - τ) + τ) < 1` (`BHSV25.Alg.thetaLow`,
  `BHSV25.Alg.card_eig_le_neg_thetaLow_le`).
* The algorithm uses rational thresholds between `θ₀` and `θ₁ = √θ₀ ∈ (θ₀, 1)`
  (`BHSV25.Alg.thetaUp`), and the loss `f λ = (1 + θ₁) 4 / (1 - θ₁) - 4 + θ₁`
  (`BHSV25.Alg.indepLoss`), which tends to `0` as `λ → 0` (`BHSV25.Alg.tendsto_indepLoss`).
-/

@[expose] public section

namespace BHSV25.Alg

open Filter Topology

/-- `τ = 2λ / (1 + λ)`, between `λ` and `1` for `λ ∈ (0, 1)`. -/
noncomputable def tauOf (lam : ℝ) : ℝ := 2 * lam / (1 + lam)

/-- `θ₀ = √(τ (1 - τ) + τ)`, the threshold of [BHSV25, Corollary 4.2] with `σ = τ`. -/
noncomputable def thetaLow (lam : ℝ) : ℝ := Real.sqrt (tauOf lam * (1 - tauOf lam) + tauOf lam)

/-- `θ₁ = √θ₀`, between `θ₀` and `1`. -/
noncomputable def thetaUp (lam : ℝ) : ℝ := Real.sqrt (thetaLow lam)

/-- **The loss** `f λ = (1 + θ₁) 4 / (1 - θ₁) - 4 + θ₁` of [BHSV25, Theorem 1.1]. -/
noncomputable def indepLoss (lam : ℝ) : ℝ :=
  (1 + thetaUp lam) * 4 / (1 - thetaUp lam) - 4 + thetaUp lam

section

variable {lam : ℝ}

theorem tauOf_pos (h0 : 0 < lam) : 0 < tauOf lam := by
  unfold tauOf
  positivity

theorem lt_tauOf (h0 : 0 < lam) (h1 : lam < 1) : lam < tauOf lam := by
  unfold tauOf
  rw [lt_div_iff₀ (by linarith only [h0])]
  have := mul_pos h0 (sub_pos.2 h1)
  linarith only [this]

theorem tauOf_lt_one (h0 : 0 < lam) (h1 : lam < 1) : tauOf lam < 1 := by
  unfold tauOf
  rw [div_lt_one (by linarith only [h0])]
  linarith only [h1]

theorem thetaLow_pos (h0 : 0 < lam) (h1 : lam < 1) : 0 < thetaLow lam := by
  have ht := tauOf_pos h0
  have ht1 := tauOf_lt_one h0 h1
  unfold thetaLow
  refine Real.sqrt_pos.2 ?_
  have := mul_pos ht (by linarith only [ht1] : 0 < 1 - tauOf lam)
  linarith only [this, ht]

theorem thetaLow_lt_one (h0 : 0 < lam) (h1 : lam < 1) : thetaLow lam < 1 := by
  have ht1 := tauOf_lt_one h0 h1
  unfold thetaLow
  rw [Real.sqrt_lt' one_pos]
  have := mul_pos (by linarith only [ht1] : 0 < 1 - tauOf lam)
    (by linarith only [ht1] : 0 < 1 - tauOf lam)
  linarith only [this]

theorem thetaLow_lt_thetaUp (h0 : 0 < lam) (h1 : lam < 1) : thetaLow lam < thetaUp lam := by
  have hp := thetaLow_pos h0 h1
  have h1' := thetaLow_lt_one h0 h1
  unfold thetaUp
  rw [Real.lt_sqrt hp.le, sq]
  have := mul_lt_mul_of_pos_left h1' hp
  linarith only [this]

theorem thetaUp_pos (h0 : 0 < lam) (h1 : lam < 1) : 0 < thetaUp lam :=
  (thetaLow_pos h0 h1).trans (thetaLow_lt_thetaUp h0 h1)

theorem thetaUp_lt_one (h0 : 0 < lam) (h1 : lam < 1) : thetaUp lam < 1 := by
  unfold thetaUp
  rw [Real.sqrt_lt' one_pos, one_pow]
  exact thetaLow_lt_one h0 h1

theorem indepLoss_nonneg (h0 : 0 < lam) (h1 : lam < 1) : 0 ≤ indepLoss lam := by
  have hp := thetaUp_pos h0 h1
  have hl := thetaUp_lt_one h0 h1
  unfold indepLoss
  have h4 : 4 ≤ (1 + thetaUp lam) * 4 / (1 - thetaUp lam) := by
    rw [le_div_iff₀ (by linarith only [hl])]
    linarith only [hp]
  linarith only [h4, hp]

/-- The constant of one candidate is at most `4 + f λ`, for thresholds `θ < θ₁` and precisions
`κ < θ₁ / 2`. -/
theorem const_le_indepLoss (h0 : 0 < lam) (h1 : lam < 1) {θ κ : ℝ} (hθ : θ < thetaUp lam)
    (hκ0 : 0 < κ) (hκ : κ < thetaUp lam / 2) :
    (1 + thetaUp lam) * 4 / (1 - θ) + 2 * (1 + 1 / thetaUp lam) * κ ^ 2 ≤ 4 + indepLoss lam ∧
      (1 + 1 / thetaUp lam) * κ ^ 2 < 1 := by
  set η := thetaUp lam with hη
  have hp : 0 < η := thetaUp_pos h0 h1
  have hl : η < 1 := thetaUp_lt_one h0 h1
  have h1 : (1 + η) * 4 / (1 - θ) ≤ (1 + η) * 4 / (1 - η) :=
    div_le_div_of_nonneg_left (by positivity) (by linarith only [hl]) (by linarith only [hθ])
  have hκ2 : κ ^ 2 < η ^ 2 / 4 := by
    have := mul_lt_mul'' hκ hκ hκ0.le hκ0.le
    rw [sq, sq]
    linarith only [this]
  have h2 : (1 + 1 / η) * κ ^ 2 < η / 2 := by
    have e : (1 + 1 / η) * (η ^ 2 / 4) = (1 + η) * η / 4 := by
      field_simp
      ring
    have h3 := mul_lt_mul_of_pos_left hκ2 (by positivity : (0 : ℝ) < 1 + 1 / η)
    have h4 : η * η ≤ η := mul_le_of_le_one_left hp.le hl.le
    rw [e] at h3
    linarith only [h3, h4]
  refine ⟨?_, by linarith only [h2, hl]⟩
  unfold indepLoss
  rw [← hη]
  linarith only [h1, h2]

/-- **[BHSV25, Corollary 4.2] at `σ = τ`**: a graph with at most `t` eigenvalues larger than `λ`
has at most `t / τ²` eigenvalues at most `-θ₀`. -/
theorem card_eig_le_neg_thetaLow_le (G : Graph) (h0 : 0 < lam) (h1 : lam < 1) {t : ℕ}
    (ht : G.numEigGT lam ≤ t) :
    (Finset.univ.filter fun i ↦ G.eig i ≤ -thetaLow lam).card ≤ ⌊(t : ℝ) / tauOf lam ^ 2⌋₊ := by
  have hτ := tauOf_pos h0
  have hτ1 := tauOf_lt_one h0 h1
  have hc := G.card_eig_le_neg_le hτ.le hτ1 hτ hτ1
  have hsub : (Finset.univ.filter fun i ↦ tauOf lam ≤ G.eig i).card ≤ G.numEigGT lam :=
    Finset.card_le_card fun i hi ↦ by
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1, (lt_tauOf h0 h1).trans_le hi.2⟩
  have hct : ((Finset.univ.filter fun i ↦ tauOf lam ≤ G.eig i).card : ℝ) ≤ t := by
    exact_mod_cast hsub.trans ht
  refine Nat.le_floor ?_
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact hc.trans hct

/-- `θ₁ → 0` as `λ → 0`. -/
theorem tendsto_thetaUp : Tendsto thetaUp (𝓝 0) (𝓝 0) := by
  have htau : Tendsto tauOf (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun lam : ℝ ↦ 2 * lam / (1 + lam)) (𝓝 0) (𝓝 (2 * 0 / (1 + 0))) :=
      ((tendsto_id.const_mul 2).div (tendsto_id.const_add 1) (by norm_num))
    rw [show (2 : ℝ) * 0 / (1 + 0) = 0 by norm_num] at h
    exact h
  have hin : Tendsto (fun lam ↦ tauOf lam * (1 - tauOf lam) + tauOf lam) (𝓝 0) (𝓝 0) := by
    have h := (htau.mul (htau.const_sub 1)).add htau
    simpa using h
  have hlow : Tendsto thetaLow (𝓝 0) (𝓝 0) := by
    have h := hin.sqrt
    rw [Real.sqrt_zero] at h
    exact h
  have h := hlow.sqrt
  rw [Real.sqrt_zero] at h
  exact h

/-- **`f λ → 0` as `λ → 0⁺`.** -/
theorem tendsto_indepLoss : Tendsto indepLoss (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto indepLoss (𝓝 0) (𝓝 ((1 + 0) * 4 / (1 - 0) - 4 + 0)) :=
    ((((tendsto_thetaUp.const_add 1).mul_const 4).div (tendsto_thetaUp.const_sub 1)
      (by norm_num)).sub_const 4).add tendsto_thetaUp
  have e : ((1 : ℝ) + 0) * 4 / (1 - 0) - 4 + 0 = 0 := by norm_num
  rw [e] at h
  exact h.mono_left nhdsWithin_le_nhds

end

end BHSV25.Alg
