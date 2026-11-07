module

public import BBKS24.SparseNorm.Tail

/-!
# Maurey's empirical method

A function `f = E_{o ∼ D} val o` that is an average of functions `val o` bounded by `1` is
approximated by the average `avg val ω` of `L` independent samples `ω l ∼ D`: at each point `x`,
`|avg val ω x - f x| > b` with probability at most `2 exp(-L b² / 8)`, by Hoeffding
(`BBKS24.SparseNorm.prob_far`). Averaging over `x`, some choice of samples is `b`-close to `f`
outside a set of small measure under a given measure `μ` and under the empirical measure of a
given sample `g` (`BBKS24.SparseNorm.exists_approx`) [HR17, Lemma 3.5].

The approximations range over the finite set of averages of `L` elements of `val`, whatever `f`
is: this is what makes a union bound over them possible.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real

namespace BBKS24.SparseNorm

variable {X Ω₀ : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Fintype Ω₀] [MeasurableSpace Ω₀] [MeasurableSingletonClass Ω₀]

/-- The average `(1/L) ∑ₗ val (ω l)` of `L` samples `ω l`. -/
noncomputable def avg (val : Ω₀ → X → ℝ) {L : ℕ} (ω : Fin L → Ω₀) (x : X) : ℝ :=
  (∑ l, val (ω l) x) / L

variable (D : Measure Ω₀) [IsProbabilityMeasure D] {val : Ω₀ → X → ℝ} {f : X → ℝ}

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] in
/-- **Hoeffding for Maurey's sampling**: `P(|avg val ω x - f x| > b) ≤ 2 exp(-L b² / 8)`. -/
theorem prob_far (hval : ∀ o x, |val o x| ≤ 1) (hf : ∀ x, mean D (fun o ↦ val o x) = f x)
    {L : ℕ} (hL : 0 < L) {b : ℝ} (hb : 0 ≤ b) (x : X) :
    (Measure.infinitePi fun _ : Fin L ↦ D).real {ω | b < |avg val ω x - f x|} ≤
      2 * exp (-(L * b ^ 2) / 8) := by
  set P := Measure.infinitePi fun _ : Fin L ↦ D
  have hfx : |f x| ≤ 1 := by
    rw [← hf x]
    exact abs_mean_le D fun o ↦ hval o x
  set Y : Ω₀ → ℝ := fun o ↦ val o x - f x with hYdef
  have hYb : ∀ o, |Y o| ≤ 2 := fun o ↦ (abs_sub _ _).trans (by linarith [hval o x])
  have hYc : ∫ o, Y o ∂D = 0 := by
    rw [integral_eq_mean, hYdef, mean_sub_const, hf x, sub_self]
  have hL' : (0 : ℝ) < L := Nat.cast_pos.2 hL
  have hsub : {ω : Fin L → Ω₀ | b < |avg val ω x - f x|} ⊆
      {ω | L * b ≤ ∑ l, Y (ω l)} ∪ {ω | L * b ≤ ∑ l, (fun o ↦ -Y o) (ω l)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
    have heq : avg val ω x - f x = (∑ l, Y (ω l)) / L := by
      simp only [avg, Y, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [heq, abs_div, abs_of_pos hL', lt_div_iff₀ hL'] at hω
    rcases le_or_gt 0 (∑ l, Y (ω l)) with h | h
    · left
      rw [abs_of_nonneg h] at hω
      linarith
    · right
      rw [abs_of_neg h] at hω
      rw [sum_neg_distrib]
      linarith
  have hLb : 0 ≤ (L : ℝ) * b := by positivity
  have h1 := hoeffding_pi (κ := Fin L) D (Y := Y) (B := 2) Measurable.of_discrete (by norm_num)
    hYb hYc hLb
  have h2 := hoeffding_pi (κ := Fin L) D (Y := fun o ↦ -Y o) (B := 2) Measurable.of_discrete
    (by norm_num) (fun o ↦ by rw [abs_neg]; exact hYb o)
    (by rw [integral_neg, hYc, neg_zero]) hLb
  have hexp : exp (-(L * b) ^ 2 / (2 * (Fintype.card (Fin L) * 2 ^ 2))) =
      exp (-(L * b ^ 2) / 8) := by
    congr 1
    rw [Fintype.card_fin]
    field_simp
    ring
  rw [hexp] at h1 h2
  calc P.real {ω | b < |avg val ω x - f x|}
      ≤ P.real ({ω | L * b ≤ ∑ l, Y (ω l)} ∪ {ω | L * b ≤ ∑ l, (fun o ↦ -Y o) (ω l)}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-(L * b ^ 2) / 8) := by linarith

omit [Fintype X] in
/-- **Maurey's empirical method** [HR17, Lemma 3.5]: some `L` samples `ω` give an average that is
`b`-close to `f` outside a set whose `μ`-measure plus empirical measure under the sample `g` is at
most `4 exp(-L b² / 8)`. -/
theorem exists_approx [Finite X] (hval : ∀ o x, |val o x| ≤ 1)
    (hf : ∀ x, mean D (fun o ↦ val o x) = f x) {L : ℕ} (hL : 0 < L) {b : ℝ} (hb : 0 ≤ b)
    (μ : Measure X) [IsProbabilityMeasure μ] {R : Type*} [Fintype R] (g : R → X) :
    ∃ ω : Fin L → Ω₀, μ.real {x | b < |avg val ω x - f x|} +
      ((univ.filter fun j ↦ b < |avg val ω (g j) - f (g j)|).card : ℝ) / Fintype.card R ≤
      4 * exp (-(L * b ^ 2) / 8) := by
  classical
  have : Fintype X := Fintype.ofFinite X
  set P := Measure.infinitePi fun _ : Fin L ↦ D
  set e := 2 * exp (-(L * b ^ 2) / 8) with he
  have he0 : 0 ≤ e := by positivity
  obtain ⟨ω, hω⟩ := exists_le_mean P fun ω ↦ μ.real {x | b < |avg val ω x - f x|} +
    ((univ.filter fun j ↦ b < |avg val ω (g j) - f (g j)|).card : ℝ) / Fintype.card R
  refine ⟨ω, hω.trans ?_⟩
  have hfar : ∀ x, mean P (fun ω ↦ if b < |avg val ω x - f x| then 1 else 0) ≤ e := fun x ↦ by
    rw [← measureReal_eq_mean]
    exact prob_far D hval hf hL hb x
  have h1 : mean P (fun ω ↦ μ.real {x | b < |avg val ω x - f x|}) ≤ e := by
    simp_rw [measureReal_eq_mean μ]
    rw [mean_comm]
    exact mean_le_of_le μ hfar
  have h2 : mean P (fun ω ↦
      ((univ.filter fun j ↦ b < |avg val ω (g j) - f (g j)|).card : ℝ) / Fintype.card R) ≤ e := by
    have : ∀ ω : Fin L → Ω₀,
        ((univ.filter fun j ↦ b < |avg val ω (g j) - f (g j)|).card : ℝ) / Fintype.card R =
          (Fintype.card R : ℝ)⁻¹ * ∑ j, (if b < |avg val ω (g j) - f (g j)| then 1 else 0) := by
      intro ω
      rw [card_filter]
      push_cast
      ring
    simp_rw [this]
    rw [mean_const_mul, mean_finsetSum]
    rcases Nat.eq_zero_or_pos (Fintype.card R) with h0 | h0
    · rw [h0, Nat.cast_zero, inv_zero, zero_mul]
      exact he0
    · calc (Fintype.card R : ℝ)⁻¹ *
            ∑ j, mean P (fun ω ↦ if b < |avg val ω (g j) - f (g j)| then 1 else 0)
          ≤ (Fintype.card R : ℝ)⁻¹ * ∑ _j : R, e := by
            gcongr with j
            exact hfar (g j)
        _ = e := by
            rw [sum_const, card_univ, nsmul_eq_mul]
            field_simp
  calc mean P (fun ω ↦ μ.real {x | b < |avg val ω x - f x|} +
        ((univ.filter fun j ↦ b < |avg val ω (g j) - f (g j)|).card : ℝ) / Fintype.card R)
      = _ := mean_add P _ _
    _ ≤ e + e := add_le_add h1 h2
    _ = 4 * exp (-(L * b ^ 2) / 8) := by rw [he]; ring

end BBKS24.SparseNorm
