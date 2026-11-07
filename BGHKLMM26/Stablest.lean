module

public import OAI

/-!
# Majority is Stablest, in the cut form

[BGHKLMM26, Corollary 4.3] for `ρ ∈ (-1, 0)`: a table `g : {0,1}^n → [0,1]` whose `±1` version
`2g - 1` has small low-degree influences cuts at most an `arccos ρ / π + ξ` fraction of the
`ρ`-correlated pairs (`BGHKLMM26.Hard.cut_le_of_lowInfluence`).

It follows from Majority is Stablest for balanced functions and positive correlation,
`OAI.OptimalMaxCut.MISProof.majority_is_stablest`, from OpenAI's library (`Imported/OAI/`). With
`h = 2g - 1`, the cut value is `(1 - Stab_ρ h)/2`, and for `ρ < 0`,
`Stab_ρ h ≥ -Stab_{|ρ|} h_odd` for the odd part `h_odd(x) = (h(x) - h(-x))/2` of `h`, which is
balanced, `[-1,1]`-valued, and has no larger influences.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman OAI.OptimalMaxCut.MISProof

variable {n : ℕ}

/-! ### The antipode and the odd part -/

/-- The antipodal point: every bit flipped. -/
def antipode (x : Cube (Fin n)) : Cube (Fin n) := fun i ↦ !x i

theorem antipode_antipode (x : Cube (Fin n)) : antipode (antipode x) = x := by
  funext i; simp [antipode]

/-- The antipode as a permutation of the cube. -/
def antipodeEquiv : Cube (Fin n) ≃ Cube (Fin n) :=
  ⟨antipode, antipode, antipode_antipode, antipode_antipode⟩

theorem walsh_antipode (s x : Cube (Fin n)) :
    walsh s (antipode x) = (-1) ^ degree s * walsh s x := by
  have h : ∀ i, bitSign (s i && !x i) = (if s i then -1 else 1) * bitSign (s i && x i) := by
    intro i; cases s i <;> cases x i <;> simp [bitSign]
  simp only [walsh, antipode, h, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, degree]

theorem expect_antipode (f : Cube (Fin n) → ℝ) : (𝔼 x, f (antipode x)) = 𝔼 x, f x :=
  Fintype.expect_equiv antipodeEquiv _ _ fun _ ↦ rfl

theorem coefficient_antipode (h : Cube (Fin n) → ℝ) (s : Cube (Fin n)) :
    coefficient (fun x ↦ h (antipode x)) s = (-1) ^ degree s * coefficient h s := by
  simp only [coefficient]
  rw [← expect_antipode (fun x ↦ h (antipode x) * walsh s x)]
  simp only [antipode_antipode, walsh_antipode, Finset.mul_expect]
  refine Finset.expect_congr rfl fun x _ ↦ ?_
  ring

/-- The odd part `(h(x) - h(-x))/2`. -/
noncomputable def oddPart (h : Cube (Fin n) → ℝ) (x : Cube (Fin n)) : ℝ :=
  (h x - h (antipode x)) / 2

/-- The odd part keeps the coefficients of odd degree and kills the others. -/
theorem coefficient_oddPart (h : Cube (Fin n) → ℝ) (s : Cube (Fin n)) :
    coefficient (oddPart h) s = (1 - (-1) ^ degree s) / 2 * coefficient h s := by
  have e : coefficient (oddPart h) s =
      (coefficient h s - coefficient (fun x ↦ h (antipode x)) s) / 2 := by
    unfold coefficient oddPart
    rw [← Finset.expect_sub_distrib, Finset.expect_div]
    refine Finset.expect_congr rfl fun x _ ↦ ?_
    ring
  rw [e, coefficient_antipode]
  ring

theorem oddFactor_sq (d : ℕ) : ((1 - (-1 : ℝ) ^ d) / 2) ^ 2 ≤ 1 := by
  rcases Nat.even_or_odd d with h | h
  · rw [h.neg_one_pow]; norm_num
  · rw [h.neg_one_pow]; norm_num

theorem oddPart_mem {h : Cube (Fin n) → ℝ} (hh : ∀ x, -1 ≤ h x ∧ h x ≤ 1) (x : Cube (Fin n)) :
    -1 ≤ oddPart h x ∧ oddPart h x ≤ 1 := by
  have h1 := hh x
  have h2 := hh (antipode x)
  unfold oddPart
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem expect_oddPart (h : Cube (Fin n) → ℝ) : (𝔼 x, oddPart h x) = 0 := by
  unfold oddPart
  rw [← Finset.expect_div, Finset.expect_sub_distrib, expect_antipode, sub_self, zero_div]

theorem cutoffInfluence_oddPart_le (K : ℕ) (i : Fin n) (h : Cube (Fin n) → ℝ) :
    cutoffInfluence K i (oddPart h) ≤ cutoffInfluence K i h := by
  unfold cutoffInfluence
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [coefficient_oddPart, mul_pow]
  exact mul_le_of_le_one_left (sq_nonneg _) (oddFactor_sq _)

/-- **Negative correlation**: for `t ≥ 0`, `Stab_{-t} h ≥ -Stab_t h_odd`. -/
theorem neg_stability_oddPart_le {t : ℝ} (ht : 0 ≤ t) (h : Cube (Fin n) → ℝ) :
    -stability t (oddPart h) ≤ stability (-t) h := by
  unfold stability
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  rw [coefficient_oddPart, mul_pow]
  have hc := sq_nonneg (coefficient h s)
  have htd : 0 ≤ t ^ degree s := pow_nonneg ht _
  rcases Nat.even_or_odd (degree s) with he | ho
  · rw [he.neg_one_pow, neg_pow, he.neg_one_pow]
    norm_num
    positivity
  · rw [ho.neg_one_pow, neg_pow, ho.neg_one_pow]
    norm_num

/-! ### The cut form -/

/-- The cut value `Cut(g(x), g(y)) = g(x) + g(y) - 2 g(x) g(y)` of `g` on `ρ`-correlated pairs is
`(1 - Stab_ρ (2g - 1))/2`. -/
theorem corrAverage_cut (ρ : ℝ) (g : Cube (Fin n) → ℝ) :
    corrAverage ρ n (fun x y ↦ g x + g y - 2 * g x * g y) =
      (1 - stability ρ (fun x ↦ 2 * g x - 1)) / 2 := by
  rw [← corrAverage_stability]
  have e1 : (fun x y : Cube (Fin n) ↦ g x + g y - 2 * g x * g y) =
      fun x y ↦ (1 / 2 : ℝ) * 1 - (1 / 2) * ((2 * g x - 1) * (2 * g y - 1)) := by
    funext x y; ring
  have e2 : (fun x y : Cube (Fin n) ↦ (1 / 2 : ℝ) * 1 -
      (1 / 2) * ((2 * g x - 1) * (2 * g y - 1))) =
      fun x y ↦ (1 / 2 : ℝ) * 1 + (-(1 / 2) * ((2 * g x - 1) * (2 * g y - 1))) := by
    funext x y; ring
  rw [e1, e2, corrAverage_add, corrAverage_const_mul, corrAverage_const_mul]
  have h1 : corrAverage ρ n (fun (_ : BitCube n) (_ : BitCube n) ↦ (1 : ℝ)) = 1 := by
    have := corrAverage_fst ρ n (fun _ ↦ (1 : ℝ))
    rw [Fintype.expect_const] at this
    exact this
  rw [h1]
  ring

/-- **Majority is Stablest, the cut form** [BGHKLMM26, Corollary 4.3]: for `ρ ∈ (-1, 0)` and
`ξ > 0`, a table `g : {0,1}^n → [0,1]` whose `±1` version has small influences of degree at most `K`
cuts at most `arccos ρ / π + ξ` of the `ρ`-correlated pairs. -/
theorem cut_le_of_lowInfluence {ρ : ℝ} (hρ1 : -1 < ρ) (hρ0 : ρ < 0) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ τ : ℝ, 0 < τ ∧ ∀ (n : ℕ) (g : Cube (Fin n) → ℝ),
      (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
      (∀ i, cutoffInfluence K i (fun x ↦ 2 * g x - 1) < τ) →
      corrAverage ρ n (fun x y ↦ g x + g y - 2 * g x * g y) ≤ Real.arccos ρ / Real.pi + ξ := by
  obtain ⟨K, hK, τ, hτ, hmis⟩ := majority_is_stablest (-ρ) (by linarith) (by linarith)
    (2 * ξ) (by linarith)
  refine ⟨K, hK, τ, hτ, fun n g hg hinf ↦ ?_⟩
  set h : Cube (Fin n) → ℝ := fun x ↦ 2 * g x - 1
  have hh : ∀ x, -1 ≤ h x ∧ h x ≤ 1 := fun x ↦ by
    have := hg x; constructor <;> simp only [h] <;> linarith [this.1, this.2]
  have hst := hmis n (oddPart h) (oddPart_mem hh) (expect_oddPart h)
    fun i ↦ (cutoffInfluence_oddPart_le K i h).trans_lt (hinf i)
  have hneg := neg_stability_oddPart_le (t := -ρ) (by linarith) h
  rw [neg_neg] at hneg
  rw [corrAverage_cut]
  have harc : Real.arccos ρ / Real.pi = 1 / 2 - Real.arcsin ρ / Real.pi := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    field_simp
  have hasin : Real.arcsin (-ρ) = -Real.arcsin ρ := Real.arcsin_neg ρ
  rw [harc]
  rw [hasin] at hst
  have : 2 / Real.pi * -Real.arcsin ρ = -(2 * (Real.arcsin ρ / Real.pi)) := by ring
  rw [this] at hst
  linarith

end BGHKLMM26.Hard
