module

public import BGHKLMM26.Hardness.Sparsify
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.UniformOn

/-!
# Concentration for independent uniform samples

Tail bounds for `S` independent samples `ω : Fin S → Ω` from a finite uniform space, in terms of
`BGHKLMM26.Hard.frac`: Hoeffding's and Bernstein's inequalities (Lemma 6.3) for sums of a bounded
score, a binomial tail by the union bound, Markov's inequality, and the size of Hamming balls
(Lemma B.2).

All bounds go through `BGHKLMM26.Hard.frac_le_mean_of_le` (an indicator dominated by a
nonnegative function) and the product formula `BGHKLMM26.Hard.mean_pi_prod` for the mean of a
product of functions of distinct coordinates; this gives the Chernoff bound
`BGHKLMM26.Hard.frac_sum_ge_le_exp`. Hoeffding's lemma is Mathlib's
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, for the uniform measure
(`BGHKLMM26.Hard.mean_exp_le_hoeffding`); for Bernstein, `e^y ≤ 1 + y + y²` for `|y| ≤ 1`.
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset
open scoped BigOperators

variable {Ω : Type} [Fintype Ω] [Nonempty Ω]

/-- The mean of a score over `Ω`. -/
noncomputable def mean (X : Ω → ℝ) : ℝ := (∑ ω, X ω) / Fintype.card Ω

/-! ### Basic facts about `frac` and `mean` -/

/-- A set is at most the sum of a nonnegative function that is at least `1` on it. -/
theorem card_filter_le_sum {β : Type*} [Fintype β] (p : β → Prop) [DecidablePred p]
    (G : β → ℝ) (h1 : ∀ b, p b → 1 ≤ G b) (h0 : ∀ b, 0 ≤ G b) :
    ((univ.filter p).card : ℝ) ≤ ∑ b, G b :=
  calc ((univ.filter p).card : ℝ) = ∑ b ∈ univ.filter p, (1 : ℝ) := by simp
    _ ≤ ∑ b ∈ univ.filter p, G b := sum_le_sum fun b hb ↦ h1 b (mem_filter.1 hb).2
    _ ≤ ∑ b, G b := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun b _ _ ↦ h0 b

/-- The fraction where `p` holds is at most the mean of a nonnegative function that is at least `1`
where `p` holds. -/
theorem frac_le_mean_of_le {β : Type} [Fintype β] [Nonempty β] (p : β → Prop) (G : β → ℝ)
    (h1 : ∀ b, p b → 1 ≤ G b) (h0 : ∀ b, 0 ≤ G b) : frac p ≤ mean G := by
  classical
  unfold frac mean
  exact div_le_div_of_nonneg_right (card_filter_le_sum p G h1 h0) (Nat.cast_nonneg _)

theorem zero_le_frac {β : Type*} [Fintype β] (p : β → Prop) : 0 ≤ frac p :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `frac` is monotone. -/
theorem frac_le_of_imp {β : Type*} [Fintype β] {p q : β → Prop} (h : ∀ b, p b → q b) :
    frac p ≤ frac q := by
  classical
  unfold frac
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Nat.cast_le.2 (card_le_card fun b hb ↦ ?_)
  simp only [mem_filter] at hb ⊢
  exact ⟨hb.1, h b hb.2⟩

omit [Nonempty Ω] in
theorem mean_le_mean {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) : mean X ≤ mean Y :=
  div_le_div_of_nonneg_right (sum_le_sum fun ω _ ↦ h ω) (Nat.cast_nonneg _)

omit [Nonempty Ω] in
theorem mean_nonneg {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) : 0 ≤ mean X :=
  div_nonneg (sum_nonneg fun ω _ ↦ h ω) (Nat.cast_nonneg _)

theorem mean_const (c : ℝ) : mean (fun _ : Ω ↦ c) = c := by
  have : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  unfold mean
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Nonempty Ω] in
theorem mean_add (X Y : Ω → ℝ) : mean (fun ω ↦ X ω + Y ω) = mean X + mean Y := by
  unfold mean
  rw [sum_add_distrib, add_div]

omit [Nonempty Ω] in
theorem mean_sub (X Y : Ω → ℝ) : mean (fun ω ↦ X ω - Y ω) = mean X - mean Y := by
  unfold mean
  rw [sum_sub_distrib, sub_div]

omit [Nonempty Ω] in
theorem mean_const_mul (c : ℝ) (X : Ω → ℝ) : mean (fun ω ↦ c * X ω) = c * mean X := by
  unfold mean
  rw [← mul_sum, mul_div_assoc]

omit [Nonempty Ω] in
theorem mean_sum {ι : Type*} (s : Finset ι) (X : ι → Ω → ℝ) :
    mean (fun ω ↦ ∑ j ∈ s, X j ω) = ∑ j ∈ s, mean (X j) := by
  unfold mean
  rw [sum_comm, sum_div]

omit [Nonempty Ω] in
/-- The mean of an indicator is the fraction where the event holds. -/
theorem mean_ite (A : Ω → Prop) [DecidablePred A] :
    mean (fun ω ↦ if A ω then (1 : ℝ) else 0) = frac A := by
  unfold mean frac
  rw [sum_boole]
  congr

/-! ### Products over independent coordinates -/

/-- The sum over `ι → α` of a product of functions of distinct coordinates. -/
theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} [Fintype α]
    (f : ι → α → ℝ) : ∑ ω : ι → α, ∏ i, f i (ω i) = ∏ i, ∑ x, f i x := by
  rw [prod_univ_sum, Fintype.piFinset_univ]

omit [Nonempty Ω] in
/-- **Independence of the coordinates**: the mean of a product of functions of distinct
coordinates is the product of the means. -/
theorem mean_pi_prod {S : ℕ} (f : Fin S → Ω → ℝ) :
    mean (fun ω : Fin S → Ω ↦ ∏ i, f i (ω i)) = ∏ i, mean (f i) := by
  unfold mean
  rw [sum_pi_prod, Fintype.card_pi, prod_div_distrib]
  push_cast
  rfl

omit [Nonempty Ω] in
theorem mean_pi_prod_const {S : ℕ} (g : Ω → ℝ) :
    mean (fun ω : Fin S → Ω ↦ ∏ i, g (ω i)) = mean g ^ S := by
  rw [mean_pi_prod (fun _ ↦ g), prod_const, card_univ, Fintype.card_fin]

/-- The mean of a product of one function over a set of coordinates. -/
theorem mean_prod_mem {S : ℕ} (T : Finset (Fin S)) (g : Ω → ℝ) :
    mean (fun ω : Fin S → Ω ↦ ∏ i ∈ T, g (ω i)) = mean g ^ T.card := by
  obtain ⟨F, hF⟩ : ∃ F : Fin S → Ω → ℝ, F = fun i x ↦ if i ∈ T then g x else 1 := ⟨_, rfl⟩
  have h : (fun ω : Fin S → Ω ↦ ∏ i ∈ T, g (ω i)) = fun ω ↦ ∏ i, F i (ω i) := by
    funext ω
    rw [hF]
    exact (by rw [prod_ite_mem, univ_inter] :
      ∏ i, (if i ∈ T then g (ω i) else 1) = ∏ i ∈ T, g (ω i)).symm
  have hm : ∀ i, mean (F i) = if i ∈ T then mean g else 1 := by
    intro i
    rw [hF]
    by_cases hi : i ∈ T
    · simp only [hi, ite_true]
    · simp only [hi, ite_false]
      exact mean_const 1
  rw [h, mean_pi_prod, Finset.prod_congr rfl fun i _ ↦ hm i, prod_ite_mem, univ_inter, prod_const]

/-! ### Exponential moments -/

/-- **The Chernoff bound**: for `l ≥ 0`, `P(a ≤ ∑ Z(ωᵢ)) ≤ e^{-l a} (E e^{l Z})^S`. -/
theorem frac_sum_ge_le_exp (Z : Ω → ℝ) (S : ℕ) (a : ℝ) {l : ℝ} (hl : 0 ≤ l) :
    frac (fun ω : Fin S → Ω ↦ a ≤ ∑ i, Z (ω i)) ≤
      Real.exp (-(l * a)) * mean (fun x ↦ Real.exp (l * Z x)) ^ S := by
  have h := frac_le_mean_of_le (fun ω : Fin S → Ω ↦ a ≤ ∑ i, Z (ω i))
    (fun ω ↦ Real.exp (-(l * a)) * ∏ i, Real.exp (l * Z (ω i))) ?_ ?_
  · refine h.trans_eq ?_
    rw [mean_const_mul]
    exact congrArg _ (mean_pi_prod_const fun x ↦ Real.exp (l * Z x))
  · intro ω hω
    rw [← Real.exp_sum, ← Real.exp_add]
    apply Real.one_le_exp
    rw [← mul_sum]
    nlinarith
  · intro ω
    positivity

/-! ### Hoeffding's lemma, from Mathlib -/

omit [Nonempty Ω] in
open MeasureTheory ProbabilityTheory in
/-- Integrals for the uniform measure on a finite type are means. -/
theorem integral_uniformOn_eq_mean [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (f : Ω → ℝ) : ∫ x, f x ∂(uniformOn (Set.univ : Set Ω)) = mean f := by
  rw [integral_fintype .of_finite]
  simp only [measureReal_def, uniformOn_univ, Measure.count_singleton, smul_eq_mul]
  unfold mean
  rw [sum_div]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [ENNReal.toReal_div]
  simp
  ring

/-- **Hoeffding's lemma** (from Mathlib): a centered score with values in an interval of length
`1` has `E e^{t Y} ≤ e^{t²/8}`. -/
theorem mean_exp_le_hoeffding (Y : Ω → ℝ) {a : ℝ} (hY : ∀ ω, a ≤ Y ω ∧ Y ω ≤ a + 1)
    (h0 : mean Y = 0) (t : ℝ) :
    mean (fun ω ↦ Real.exp (t * Y ω)) ≤ Real.exp (t ^ 2 / 8) := by
  let _ : MeasurableSpace Ω := ⊤
  have _ : DiscreteMeasurableSpace Ω := ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩
  have h := (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := ProbabilityTheory.uniformOn (Set.univ : Set Ω)) (X := Y) (a := a) (b := a + 1)
    Measurable.of_discrete.aemeasurable (MeasureTheory.ae_of_all _ fun ω ↦ hY ω)
    (by rw [integral_uniformOn_eq_mean, h0])).mgf_le t
  rw [ProbabilityTheory.mgf, integral_uniformOn_eq_mean] at h
  refine h.trans_eq ?_
  congr 1
  simp
  ring

/-- Hoeffding's inequality for a centered score with values in an interval of length `1`. -/
theorem frac_sum_ge_hoeffding (Z : Ω → ℝ) {a : ℝ} (hZ : ∀ ω, a ≤ Z ω ∧ Z ω ≤ a + 1)
    (h0 : mean Z = 0) (S : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    frac (fun ω : Fin S → Ω ↦ S * t ≤ ∑ i, Z (ω i)) ≤ Real.exp (-2 * S * t ^ 2) := by
  refine (frac_sum_ge_le_exp Z S (S * t) (l := 4 * t) (by linarith)).trans ?_
  calc Real.exp (-(4 * t * (S * t))) * mean (fun x ↦ Real.exp (4 * t * Z x)) ^ S
      ≤ Real.exp (-(4 * t * (S * t))) * Real.exp ((4 * t) ^ 2 / 8) ^ S := by
        gcongr
        · exact mean_nonneg fun _ ↦ (Real.exp_pos _).le
        · exact mean_exp_le_hoeffding Z hZ h0 _
    _ = Real.exp (-2 * S * t ^ 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring

/-- **Hoeffding, upper tail**, for a `[0,1]`-valued score. -/
theorem frac_sum_ge_le (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) (S : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    frac (fun ω : Fin S → Ω ↦ S * (mean X + t) ≤ ∑ i, X (ω i)) ≤ Real.exp (-2 * S * t ^ 2) := by
  refine (frac_le_of_imp ?_).trans
    (frac_sum_ge_hoeffding (fun ω ↦ X ω - mean X) (a := -mean X) ?_ ?_ S ht)
  · intro ω h
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  · intro ω
    constructor <;> linarith [hX ω]
  · rw [mean_sub, mean_const, sub_self]

/-- **Hoeffding, lower tail**, for a `[0,1]`-valued score. -/
theorem frac_sum_le_le (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 1) (S : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    frac (fun ω : Fin S → Ω ↦ ∑ i, X (ω i) ≤ S * (mean X - t)) ≤ Real.exp (-2 * S * t ^ 2) := by
  refine (frac_le_of_imp ?_).trans
    (frac_sum_ge_hoeffding (fun ω ↦ mean X - X ω) (a := mean X - 1) ?_ ?_ S ht)
  · intro ω h
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  · intro ω
    constructor <;> linarith [hX ω]
  · have h := mean_sub (fun _ : Ω ↦ mean X) X
    simp only [mean_const] at h
    rw [h, sub_self]

/-- The exponential moment bound behind Bernstein's inequality: for `0 ≤ l` with `l M ≤ 1`,
`E e^{l X} ≤ e^{l E X + l² σ²}`. -/
theorem mean_exp_le_bernstein (X : Ω → ℝ) {M σ2 l : ℝ} (hM : ∀ ω, |X ω| ≤ M)
    (hσ : mean (fun ω ↦ X ω ^ 2) ≤ σ2) (hl : 0 ≤ l) (hlM : l * M ≤ 1) :
    mean (fun ω ↦ Real.exp (l * X ω)) ≤ Real.exp (l * mean X + l ^ 2 * σ2) := by
  have h1 : ∀ ω, Real.exp (l * X ω) ≤ 1 + l * X ω + l ^ 2 * X ω ^ 2 := by
    intro ω
    have hx : |l * X ω| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hl]
      exact (mul_le_mul_of_nonneg_left (hM ω) hl).trans hlM
    have h2 := (abs_le.1 (Real.abs_exp_sub_one_sub_id_le hx)).2
    have h3 : (l * X ω) ^ 2 = l ^ 2 * X ω ^ 2 := by ring
    linarith
  have hlin : mean (fun ω ↦ 1 + l * X ω + l ^ 2 * X ω ^ 2) =
      1 + l * mean X + l ^ 2 * mean (fun ω ↦ X ω ^ 2) := by
    have hc : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [mean, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
    field_simp
  calc mean (fun ω ↦ Real.exp (l * X ω)) ≤ mean (fun ω ↦ 1 + l * X ω + l ^ 2 * X ω ^ 2) :=
        mean_le_mean h1
    _ ≤ 1 + l * mean X + l ^ 2 * σ2 := by
        rw [hlin]
        have := mul_le_mul_of_nonneg_left hσ (sq_nonneg l)
        linarith
    _ ≤ Real.exp (l * mean X + l ^ 2 * σ2) := by
        linarith [Real.add_one_le_exp (l * mean X + l ^ 2 * σ2)]

/-- **Bernstein** [BGHKLMM26, Lemma 6.3], in a slightly weaker form: for a score with
`|X| ≤ M` and `E X² ≤ σ²`, the sum of `S` samples exceeds `S (E X + t)` with probability at most
`exp(-S t² / (4 σ² + 4 M t))`. -/
theorem frac_sum_ge_bernstein (X : Ω → ℝ) {M σ2 : ℝ} (hM : ∀ ω, |X ω| ≤ M)
    (hσ : mean (fun ω ↦ X ω ^ 2) ≤ σ2) (S : ℕ) {t : ℝ} (ht : 0 < t) (hMt : 0 < σ2 + M * t) :
    frac (fun ω : Fin S → Ω ↦ S * (mean X + t) ≤ ∑ i, X (ω i)) ≤
      Real.exp (-(S * t ^ 2) / (4 * σ2 + 4 * M * t)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (Classical.arbitrary Ω))
  have hσ0 : 0 ≤ σ2 := (mean_nonneg fun ω ↦ sq_nonneg (X ω)).trans hσ
  obtain ⟨D, hD⟩ : ∃ D, D = 4 * σ2 + 4 * M * t := ⟨_, rfl⟩
  have hD0 : 0 < D := by rw [hD]; linarith
  obtain ⟨l, hl⟩ : ∃ l, l = 2 * t / D := ⟨_, rfl⟩
  have hlD : l * D = 2 * t := by rw [hl]; field_simp
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  have hMt0 : 0 ≤ M * t := mul_nonneg hM0 ht.le
  have hlM : l * M ≤ 1 := by
    have h : l * M * D ≤ 1 * D := by
      have : l * M * D = M * (l * D) := by ring
      rw [this, hlD, hD]
      nlinarith
    exact le_of_mul_le_mul_right h hD0
  have key : -(l * t) + l ^ 2 * σ2 ≤ -t ^ 2 / D := by
    rw [le_div_iff₀ hD0]
    have e1 : (-(l * t) + l ^ 2 * σ2) * D = -(t * (l * D)) + l * σ2 * (l * D) := by ring
    rw [e1, hlD]
    -- -2t² + 2 t l σ2 ≤ -t², i.e. 2 l σ2 ≤ t
    have h2 : 2 * l * σ2 * D ≤ t * D := by
      have : 2 * l * σ2 * D = 2 * σ2 * (l * D) := by ring
      rw [this, hlD, hD]
      nlinarith
    have h3 : 2 * l * σ2 ≤ t := le_of_mul_le_mul_right h2 hD0
    nlinarith
  refine (frac_sum_ge_le_exp X S (S * (mean X + t)) hl0).trans ?_
  calc Real.exp (-(l * (S * (mean X + t)))) * mean (fun x ↦ Real.exp (l * X x)) ^ S
      ≤ Real.exp (-(l * (S * (mean X + t)))) * Real.exp (l * mean X + l ^ 2 * σ2) ^ S := by
        gcongr
        · exact mean_nonneg fun _ ↦ (Real.exp_pos _).le
        · exact mean_exp_le_bernstein X hM hσ hl0 hlM
    _ ≤ Real.exp (-(S * t ^ 2) / (4 * σ2 + 4 * M * t)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← hD]
        apply Real.exp_le_exp.2
        have e1 : -(l * (S * (mean X + t))) + S * (l * mean X + l ^ 2 * σ2) =
            S * (-(l * t) + l ^ 2 * σ2) := by ring
        have e2 : -(S * t ^ 2) / D = S * (-t ^ 2 / D) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left key (Nat.cast_nonneg S)

/-- **A binomial tail**: at least `k` of `S` samples fall in an event of probability `p`, with
probability at most `(S p)^k / k!`. -/
theorem frac_count_ge_le (A : Ω → Prop) [DecidablePred A] (S k : ℕ) :
    frac (fun ω : Fin S → Ω ↦ k ≤ (univ.filter fun i ↦ A (ω i)).card) ≤
      (S * frac A) ^ k / k.factorial := by
  obtain ⟨g, hg⟩ : ∃ g : Ω → ℝ, g = fun x ↦ if A x then 1 else 0 := ⟨_, rfl⟩
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦ by rw [hg]; dsimp only; split_ifs <;> norm_num
  have hmg : mean g = frac A := by rw [hg]; exact mean_ite A
  have h := frac_le_mean_of_le (fun ω : Fin S → Ω ↦ k ≤ (univ.filter fun i ↦ A (ω i)).card)
    (fun ω ↦ ∑ T ∈ powersetCard k univ, ∏ i ∈ T, g (ω i)) ?_ ?_
  · refine h.trans ?_
    rw [mean_sum]
    simp_rw [mean_prod_mem]
    rw [sum_congr rfl fun T hT ↦ by rw [(mem_powersetCard.1 hT).2], sum_const, card_powersetCard,
      card_univ, Fintype.card_fin, nsmul_eq_mul, hmg, mul_pow, mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div k S) (pow_nonneg (zero_le_frac A) _)
  · intro ω hω
    obtain ⟨T, hTs, hTk⟩ := exists_subset_card_eq hω
    have hT : T ∈ powersetCard k univ := mem_powersetCard.2 ⟨subset_univ _, hTk⟩
    have h1 : ∏ i ∈ T, g (ω i) = 1 :=
      prod_eq_one fun i hi ↦ by rw [hg]; simp [(mem_filter.1 (hTs hi)).2]
    calc (1 : ℝ) = ∏ i ∈ T, g (ω i) := h1.symm
      _ ≤ ∑ T' ∈ powersetCard k univ, ∏ i ∈ T', g (ω i) :=
        single_le_sum (f := fun T' ↦ ∏ i ∈ T', g (ω i))
          (fun T' _ ↦ prod_nonneg fun i _ ↦ hg0 _) hT
  · intro ω
    exact sum_nonneg fun T _ ↦ prod_nonneg fun i _ ↦ hg0 _

/-- **Markov's inequality** on a finite uniform space. -/
theorem frac_ge_le_mean {β : Type} [Fintype β] [Nonempty β] (Y : β → ℝ) (hY : ∀ b, 0 ≤ Y b)
    {a : ℝ} (ha : 0 < a) : frac (fun b ↦ a ≤ Y b) ≤ mean Y / a := by
  refine (frac_le_mean_of_le (fun b ↦ a ≤ Y b) (fun b ↦ Y b / a)
    (fun b hb ↦ (one_le_div ha).2 hb) (fun b ↦ div_nonneg (hY b) ha.le)).trans_eq ?_
  unfold mean
  rw [← sum_div]
  ring

/-- **Hamming balls** [BGHKLMM26, Lemma B.2]: at most `(e/δ)^(δ n)` functions differ from a given
one in at most `δ n` points, `0 < δ ≤ 1`. -/
theorem card_hammingBall_le {n : ℕ} (f : Fin n → Bool) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ((univ.filter fun g : Fin n → Bool ↦
        ((univ.filter fun a ↦ f a ≠ g a).card : ℝ) ≤ δ * n).card : ℝ) ≤
      Real.exp (δ * n * Real.log (Real.exp 1 / δ)) := by
  obtain ⟨h, hh⟩ : ∃ h : Fin n → Bool → ℝ, h = fun a b ↦ if f a ≠ b then δ else 1 := ⟨_, rfl⟩
  have hlog : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
  have hprod : ∀ g : Fin n → Bool,
      ∏ a, h a (g a) = δ ^ (univ.filter fun a ↦ f a ≠ g a).card := by
    intro g
    rw [hh]
    simp only
    rw [prod_ite, prod_const, prod_const_one, mul_one]
  have hpow : ∀ m : ℕ, δ ^ m = Real.exp (m * Real.log δ) := by
    intro m
    rw [Real.exp_nat_mul, Real.exp_log hδ0]
  refine (card_filter_le_sum _
    (fun g ↦ Real.exp (-Real.log δ * (δ * n)) * ∏ a, h a (g a)) ?_ ?_).trans ?_
  · intro g hg
    rw [hprod, hpow, ← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  · intro g
    rw [hprod]
    positivity
  · rw [← mul_sum, sum_pi_prod]
    have hb : ∀ a, ∑ b, h a b = 1 + δ := by
      intro a
      rw [hh, Fintype.sum_bool]
      cases hfa : f a <;> simp [hfa, add_comm]
    rw [prod_congr rfl fun a _ ↦ hb a, prod_const, card_univ, Fintype.card_fin]
    calc Real.exp (-Real.log δ * (δ * n)) * (1 + δ) ^ n
        ≤ Real.exp (-Real.log δ * (δ * n)) * Real.exp δ ^ n := by
          gcongr
          linarith [Real.add_one_le_exp δ]
      _ = Real.exp (δ * n * Real.log (Real.exp 1 / δ)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, Real.log_div (Real.exp_ne_zero 1) hδ0.ne',
            Real.log_exp]
          congr 1
          ring

end BGHKLMM26.Hard
