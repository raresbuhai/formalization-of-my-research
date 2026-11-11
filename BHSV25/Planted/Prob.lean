module

public import Complexity.Probability.BoundedDifferences
public import BHSV25.Model

/-!
# Uniform colorings

The probability space of random planting [BHSV25, Definition 7.11]: the `k^n` colorings
`χ : Fin n → Fin k`, each with probability `1 / k^n`, which is how `BHSV25.Graph.plantProb`
counts.

* **McDiarmid's inequality** in counting form (`BHSV25.Planted.card_dev_le`): a function of the
  colors that changes by at most `c` when one color changes is `ε` away from its average on at
  most `2 exp(-2 ε² / (n c²)) k^n` colorings. This is complexitylib's
  `Cslib.Probability.HasBoundedDifferences.pi_abs_sub_mean_ge` for the product of uniform
  distributions.
* **Resampling one color** (`BHSV25.Planted.sum_sum_update`): summing over all colorings and all
  values of the color of `x` counts every coloring `k` times. Hence the factorization of averages
  (`BHSV25.Planted.sum_mul_of_indep`): the average of `h(χ x) F(χ)`, for `F` not depending on the
  color of `x`, is the average of `h` times that of `F`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {n k : ℕ}

/-! ### McDiarmid's inequality for uniform colorings -/

/-- The uniform distribution on the `k` colors. -/
noncomputable def unifColor (hk : 0 < k) : PMF (Fin k) :=
  PMF.ofFintype (fun _ ↦ (k : ENNReal)⁻¹) (by
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hk.ne') (ENNReal.natCast_ne_top k))

theorem pi_unifColor_toReal (hk : 0 < k) (χ : Fin n → Fin k) :
    (Cslib.Probability.PMF.pi (fun _ : Fin n ↦ unifColor hk) χ).toReal = 1 / (k : ℝ) ^ n := by
  rw [Cslib.Probability.PMF.pi_apply]
  simp only [unifColor, PMF.ofFintype_apply, prod_const, card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div, inv_pow]

theorem toOuterMeasure_pi_unifColor (hk : 0 < k) (s : Set (Fin n → Fin k)) [DecidablePred (· ∈ s)] :
    ((Cslib.Probability.PMF.pi (fun _ : Fin n ↦ unifColor hk)).toOuterMeasure s).toReal =
      ((univ.filter (· ∈ s)).card : ℝ) / (k : ℝ) ^ n := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype, ENNReal.toReal_sum fun χ _ ↦ by
    by_cases h : χ ∈ s
    · rw [Set.indicator_of_mem h]; exact PMF.apply_ne_top _ _
    · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top]
  have e : ∀ χ, (s.indicator (Cslib.Probability.PMF.pi (fun _ : Fin n ↦ unifColor hk)) χ).toReal =
      if χ ∈ s then 1 / (k : ℝ) ^ n else 0 := by
    intro χ
    by_cases h : χ ∈ s
    · rw [Set.indicator_of_mem h, pi_unifColor_toReal, ite_eq_left h]
    · rw [Set.indicator_of_notMem h, ite_eq_right h, ENNReal.toReal_zero]
  simp only [e]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one_div]

/-- **McDiarmid's inequality for uniform colorings**: a function that changes by at most `c` when
one color changes is at least `ε` away from its average on at most `2 exp(-2 ε² / (n c²)) k^n`
colorings. -/
theorem card_dev_le (hk : 0 < k) (f : (Fin n → Fin k) → ℝ) {c : ℝ}
    (hf : ∀ χ i a, |f (Function.update χ i a) - f χ| ≤ c) {ε : ℝ} (hε : 0 ≤ ε) :
    ((univ.filter fun χ ↦ ε ≤ |f χ - (∑ χ', f χ') / (k : ℝ) ^ n|).card : ℝ) ≤
      2 * Real.exp (-2 * ε ^ 2 / (n * c ^ 2)) * (k : ℝ) ^ n := by
  classical
  have hbd : Cslib.Probability.HasBoundedDifferences f (fun _ : Fin n ↦ c) := hf
  have h := hbd.pi_abs_sub_mean_ge (fun _ ↦ unifColor hk) hε
  have hmean : ∑ y, (Cslib.Probability.PMF.pi (fun _ : Fin n ↦ unifColor hk) y).toReal * f y =
      (∑ χ', f χ') / (k : ℝ) ^ n := by
    simp only [pi_unifColor_toReal, one_div, ← mul_sum]
    rw [inv_mul_eq_div]
  rw [hmean, toOuterMeasure_pi_unifColor] at h
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  have hkn : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hkn] at h
  simpa using h

/-- **McDiarmid's inequality for uniform colorings**, with a bound `c i` for each coordinate. -/
theorem card_dev_le' (hk : 0 < k) (f : (Fin n → Fin k) → ℝ) (c : Fin n → ℝ)
    (hf : ∀ χ i a, |f (Function.update χ i a) - f χ| ≤ c i) {ε : ℝ} (hε : 0 ≤ ε) :
    ((univ.filter fun χ ↦ ε ≤ |f χ - (∑ χ', f χ') / (k : ℝ) ^ n|).card : ℝ) ≤
      2 * Real.exp (-2 * ε ^ 2 / ∑ i, c i ^ 2) * (k : ℝ) ^ n := by
  classical
  have hbd : Cslib.Probability.HasBoundedDifferences f c := hf
  have h := hbd.pi_abs_sub_mean_ge (fun _ ↦ unifColor hk) hε
  have hmean : ∑ y, (Cslib.Probability.PMF.pi (fun _ : Fin n ↦ unifColor hk) y).toReal * f y =
      (∑ χ', f χ') / (k : ℝ) ^ n := by
    simp only [pi_unifColor_toReal, one_div, ← mul_sum]
    rw [inv_mul_eq_div]
  rw [hmean, toOuterMeasure_pi_unifColor] at h
  have hkn : (0 : ℝ) < (k : ℝ) ^ n := by positivity
  rw [div_le_iff₀ hkn] at h
  simpa using h

/-! ### Resampling one color -/

/-- **Resampling the color of `x`**: `∑_χ ∑_c g(χ[x ↦ c]) = k ∑_χ g(χ)`. -/
theorem sum_sum_update {M : Type*} [AddCommMonoid M] (x : Fin n) (g : (Fin n → Fin k) → M) :
    ∑ χ : Fin n → Fin k, ∑ c, g (Function.update χ x c) = k • ∑ χ, g χ := by
  classical
  set e := Equiv.funSplitAt x (Fin k)
  have h1 : ∀ χ c, Function.update χ x c = e.symm (c, (e χ).2) := by
    intro χ c
    funext y
    by_cases hy : y = x
    · subst hy; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hy]
  simp only [h1]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [← Equiv.sum_comp e.symm (fun χ ↦ g χ), Fintype.sum_prod_type, Finset.sum_comm]
  simp only [sum_const, card_univ, Fintype.card_fin]
  rw [Finset.sum_comm, smul_sum]

/-- **Independence of one color**: if `F` does not depend on the color of `x`, the sum of
`h(χ x) F(χ)` over the colorings is `(∑_c h c) / k` times the sum of `F`. -/
theorem sum_mul_of_indep (hk : 0 < k) (x : Fin n) (h : Fin k → ℝ) (F : (Fin n → Fin k) → ℝ)
    (hF : ∀ χ c, F (Function.update χ x c) = F χ) :
    ∑ χ : Fin n → Fin k, h (χ x) * F χ = (∑ c, h c) / k * ∑ χ, F χ := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have := sum_sum_update x (fun χ : Fin n → Fin k ↦ h (χ x) * F χ)
  simp only [Function.update_self, hF, nsmul_eq_mul] at this
  rw [Finset.sum_comm] at this
  simp only [← mul_sum] at this
  rw [← sum_mul] at this
  field_simp
  linarith

/-- The number of colorings with a given color at `x`: `k^n / k`. -/
theorem sum_ite_eq_color (hk : 0 < k) (x : Fin n) (a : Fin k) :
    ∑ χ : Fin n → Fin k, (if χ x = a then (1 : ℝ) else 0) = (k : ℝ) ^ n / k := by
  have := sum_mul_of_indep hk x (fun c ↦ if c = a then (1 : ℝ) else 0) (fun _ ↦ 1)
    (fun _ _ ↦ rfl)
  simp only [mul_one, sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow] at this
  rw [this]
  ring

end Planted

end BHSV25
