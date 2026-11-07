module

public import BBKS24.SparseNorm.Levels
public import BBKS24.SparseNorm.Maurey
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The core of the sparse norm bound

[HR17, Section 3], one-sided, for functions `ψ a` bounded by `1` and independent samples
`g r ∼ μ`, `r ∈ R`. For `w` with `∑ₐ |w a| = 1`, let `f_w = ∑ₐ w a ψ a`
(`BBKS24.SparseNorm.comb`).

* **The Chernoff event** (`BBKS24.SparseNorm.ChernoffEvent`): for every level `i < t` and every
  choice of samples for the levels `0, …, i`, the empirical sum of the `i`-th piece is below
  `|R| ((1 + 1/10) E_μ piece + α)`. It fails with probability at most
  `∑_{i<t} |Ω₀|^(L 0 + ⋯ + L i) exp(-|R| α 2^i / 40)` (`BBKS24.SparseNorm.prob_not_chernoffEvent`),
  by Chernoff's bound and a union bound: the `i`-th piece is at most `4 · 2^(-i)`.
* **On the Chernoff event** (`BBKS24.SparseNorm.sum_sq_le_of_chernoffEvent`), every `f_w` has
  `∑_r f_w(g r)² ≤ |R| ((1331/810) E_μ f_w² + 5.324 β + 1.21 t α + 2.42 · 2^(-t))`, when the
  Maurey approximations with `L j` samples at level `j` fail with probability at most `β / t`.
  The proof writes `f_w` as the mean of the signed columns `± ψ a` under the distribution with
  weights `|w a|` (`BBKS24.SparseNorm.mDist`), picks approximations at every level by Maurey's
  method (`BBKS24.SparseNorm.exists_approx`), and compares `f_w²` with the sum of the pieces at
  the good points (`BBKS24.SparseNorm.sq_le_total`, `BBKS24.SparseNorm.total_le_sq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Real

namespace BBKS24.SparseNorm

variable {X Ω₀ R : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
  [Fintype Ω₀] [MeasurableSpace Ω₀] [MeasurableSingletonClass Ω₀] [Fintype R]

/-- The approximations of the levels `j < n` given by the samples `ω j`, and `0` beyond. -/
noncomputable def gsOf (val : Ω₀ → X → ℝ) {n : ℕ} {L : ℕ → ℕ}
    (ω : (j : Fin n) → Fin (L j) → Ω₀) : ℕ → X → ℝ :=
  fun j ↦ if h : j < n then avg val (ω ⟨j, h⟩) else 0

/-- **The Chernoff event** for the sample `g`: for every level `i < t` and all samples `ω` for the
levels `0, …, i`, the empirical sum of the `i`-th piece is below its bound. -/
def ChernoffEvent (μ : Measure X) (val : Ω₀ → X → ℝ) (L : ℕ → ℕ) (t : ℕ) (α : ℝ)
    (g : R → X) : Prop :=
  ∀ i < t, ∀ ω : (j : Fin (i + 1)) → Fin (L j) → Ω₀,
    ∑ r, piece (gsOf val ω) i (g r) <
      Fintype.card R * ((1 + 1 / 10) * mean μ (piece (gsOf val ω) i) + α)

omit [MeasurableSpace Ω₀] [MeasurableSingletonClass Ω₀] in
theorem card_samples (n : ℕ) (L : ℕ → ℕ) :
    Fintype.card ((j : Fin n) → Fin (L j) → Ω₀) = Fintype.card Ω₀ ^ ∑ j ∈ range n, L j := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun j ↦ L j)]

omit [MeasurableSpace Ω₀] [MeasurableSingletonClass Ω₀] in
/-- **The Chernoff event is likely**: Chernoff's bound for each piece, at most `4 · 2^(-i)`, and a
union bound over the levels and the samples. -/
theorem prob_not_chernoffEvent (μ : Measure X) [IsProbabilityMeasure μ] (val : Ω₀ → X → ℝ)
    (L : ℕ → ℕ) (t : ℕ) (α : ℝ) :
    (Measure.infinitePi fun _ : R ↦ μ).real {g | ¬ ChernoffEvent μ val L t α g} ≤
      ∑ i ∈ range t, (Fintype.card Ω₀ : ℝ) ^ (∑ j ∈ range (i + 1), L j) *
        exp (-(Fintype.card R * α * 2 ^ i / 40)) := by
  set P := Measure.infinitePi fun _ : R ↦ μ
  have hsub : {g | ¬ ChernoffEvent μ val L t α g} ⊆
      ⋃ i ∈ range t, ⋃ ω : (j : Fin (i + 1)) → Fin (L j) → Ω₀,
        {g : R → X | Fintype.card R * ((1 + 1 / 10) * mean μ (piece (gsOf val ω) i) + α) ≤
          ∑ r, piece (gsOf val ω) i (g r)} := by
    intro g hg
    simp only [ChernoffEvent, not_forall, not_lt, Set.mem_ofPred_eq] at hg
    obtain ⟨i, hi, ω, hω⟩ := hg
    simp only [Set.mem_iUnion, mem_range]
    exact ⟨i, hi, ω, hω⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun i _ ↦ ?_))
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc ∑ ω : (j : Fin (i + 1)) → Fin (L j) → Ω₀, P.real {g : R → X |
        Fintype.card R * ((1 + 1 / 10) * mean μ (piece (gsOf val ω) i) + α) ≤
          ∑ r, piece (gsOf val ω) i (g r)}
      ≤ ∑ _ω : (j : Fin (i + 1)) → Fin (L j) → Ω₀,
          exp (-(Fintype.card R * α * 2 ^ i / 40)) := by
        refine sum_le_sum fun ω _ ↦ ?_
        refine (chernoff μ (h := piece (gsOf val ω) i) (a := 4 * (1 / 2) ^ i) (ε := 1 / 10)
          (by positivity) (by norm_num) (by norm_num) (piece_nonneg _ i)
          (piece_le _ i)).trans_eq ?_
        congr 1
        rw [one_div_pow]
        field_simp
        ring
    _ = _ := by
        rw [sum_const, card_univ, card_samples, nsmul_eq_mul]
        push_cast
        ring

/-! ### Maurey's distribution for `w` -/

section Maurey

variable {ι : Type*} [Fintype ι]

/-- `f_w = ∑ₐ w a ψ a`. -/
noncomputable def comb (ψ : ι → X → ℝ) (w : ι → ℝ) (x : X) : ℝ := ∑ a, w a * ψ a x

/-- The signed columns `(a, true) ↦ ψ a` and `(a, false) ↦ -ψ a`, with the columns numbered by
`Fin |ι|`. -/
noncomputable def signed (ψ : ι → X → ℝ) (o : Fin (Fintype.card ι) × Bool) (x : X) : ℝ :=
  if o.2 then ψ ((Fintype.equivFin ι).symm o.1) x else -ψ ((Fintype.equivFin ι).symm o.1) x

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem abs_signed_le {ψ : ι → X → ℝ} (hψ : ∀ a x, |ψ a x| ≤ 1) (o : Fin (Fintype.card ι) × Bool)
    (x : X) : |signed ψ o x| ≤ 1 := by
  unfold signed
  split_ifs
  · exact hψ _ x
  · rw [abs_neg]
    exact hψ _ x

/-- The weights `|w a|` of Maurey's distribution for `w`, split by sign. -/
noncomputable def mWeight (w : ι → ℝ) (o : Fin (Fintype.card ι) × Bool) : ℝ :=
  if o.2 then max (w ((Fintype.equivFin ι).symm o.1)) 0
  else max (-w ((Fintype.equivFin ι).symm o.1)) 0

theorem mWeight_nonneg (w : ι → ℝ) (o : Fin (Fintype.card ι) × Bool) : 0 ≤ mWeight w o := by
  unfold mWeight
  split_ifs <;> exact le_max_right _ _

theorem sum_mWeight (w : ι → ℝ) : ∑ o, mWeight w o = ∑ a, |w a| := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, mWeight, ite_true, Bool.false_eq_true, ite_false,
    max_zero_add_max_neg_zero_eq_abs_self]
  exact Equiv.sum_comp (Fintype.equivFin ι).symm fun a ↦ |w a|

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem sum_mWeight_mul (ψ : ι → X → ℝ) (w : ι → ℝ) (x : X) :
    ∑ o, mWeight w o * signed ψ o x = comb ψ w x := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, mWeight, signed, ite_true, Bool.false_eq_true, ite_false]
  have : ∀ a, max (w a) 0 * ψ a x + max (-w a) 0 * -ψ a x = w a * ψ a x := fun a ↦ by
    rw [mul_neg, ← sub_eq_add_neg, ← sub_mul, max_zero_sub_max_neg_zero_eq_self]
  simp only [this]
  exact Equiv.sum_comp (Fintype.equivFin ι).symm fun a ↦ w a * ψ a x

/-- Maurey's distribution for `w` with `∑ₐ |w a| = 1`: `± ψ a` with probability `|w a|`, the sign
of `w a`. -/
noncomputable def mDist (w : ι → ℝ) (hw : ∑ a, |w a| = 1) :
    Measure (Fin (Fintype.card ι) × Bool) :=
  (PMF.ofFintype (fun o ↦ ENNReal.ofReal (mWeight w o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun o _ ↦ mWeight_nonneg w o, sum_mWeight, hw,
      ENNReal.ofReal_one])).toMeasure

theorem isProbabilityMeasure_mDist (w : ι → ℝ) (hw : ∑ a, |w a| = 1) :
    IsProbabilityMeasure (mDist w hw) := by
  unfold mDist
  infer_instance

theorem mDist_real_singleton (w : ι → ℝ) (hw : ∑ a, |w a| = 1)
    (o : Fin (Fintype.card ι) × Bool) : (mDist w hw).real {o} = mWeight w o := by
  rw [measureReal_def, mDist, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton o),
    PMF.ofFintype_apply, ENNReal.toReal_ofReal (mWeight_nonneg w o)]

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem mean_mDist (ψ : ι → X → ℝ) (w : ι → ℝ) (hw : ∑ a, |w a| = 1) (x : X) :
    mean (mDist w hw) (fun o ↦ signed ψ o x) = comb ψ w x := by
  simp only [mean, mDist_real_singleton]
  exact sum_mWeight_mul ψ w x

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem abs_comb_le {ψ : ι → X → ℝ} (hψ : ∀ a x, |ψ a x| ≤ 1) {w : ι → ℝ}
    (hw : ∑ a, |w a| = 1) (x : X) : |comb ψ w x| ≤ 1 :=
  calc |comb ψ w x| ≤ ∑ a, |w a * ψ a x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |w a| := sum_le_sum fun a _ ↦ by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hψ a x)
    _ = 1 := hw

end Maurey

/-! ### The bound on the Chernoff event -/

variable {ι : Type*} [Fintype ι]

/-- **On the Chernoff event**, every `f_w` with `∑ₐ |w a| = 1` has
`∑_r f_w(g r)² ≤ |R| ((1331/810) E_μ f_w² + 5.324 β + 1.21 t α + 2.42 · 2^(-t))`, when the Maurey
approximations at level `j` fail with probability at most `β / t`. -/
theorem sum_sq_le_of_chernoffEvent (μ : Measure X) [IsProbabilityMeasure μ]
    {ψ : ι → X → ℝ} (hψ : ∀ a x, |ψ a x| ≤ 1) {L : ℕ → ℕ} (hL : ∀ j, 0 < L j) {t : ℕ}
    (ht : 1 ≤ t) {α β : ℝ}
    (hβ : ∀ j < t, 4 * exp (-(L j * (lvl j / 10) ^ 2) / 8) ≤ β / t)
    {g : R → X} (hg : ChernoffEvent μ (signed ψ) L t α g) (w : ι → ℝ) (hw : ∑ a, |w a| = 1) :
    ∑ r, comb ψ w (g r) ^ 2 ≤ Fintype.card R * (1331 / 810 * mean μ (fun x ↦ comb ψ w x ^ 2) +
      5324 / 1000 * β + 121 / 100 * t * α + 242 / 100 * (1 / 2) ^ t) := by
  classical
  have := isProbabilityMeasure_mDist w hw
  set f := comb ψ w with hfdef
  have hf1 : ∀ x, |f x| ≤ 1 := abs_comb_le hψ hw
  have hD : ∀ x, mean (mDist w hw) (fun o ↦ signed ψ o x) = f x := mean_mDist ψ w hw
  -- Maurey approximations at every level.
  have happrox : ∀ j : Fin t, ∃ ω : Fin (L j) → Fin (Fintype.card ι) × Bool,
      μ.real {x | lvl j / 10 < |avg (signed ψ) ω x - f x|} +
        ((univ.filter fun r ↦ lvl j / 10 < |avg (signed ψ) ω (g r) - f (g r)|).card : ℝ) /
          Fintype.card R ≤ β / t := by
    intro j
    obtain ⟨ω, hω⟩ := exists_approx (mDist w hw) (abs_signed_le hψ) hD (hL j) (b := lvl j / 10)
      (div_nonneg (lvl_pos j).le (by norm_num)) μ g
    exact ⟨ω, hω.trans (hβ j j.2)⟩
  choose Ω hΩ using happrox
  set gs := gsOf (signed ψ) Ω with hgs
  set q : ℝ := (Fintype.card R : ℝ) with hq
  have hq0 : 0 ≤ q := Nat.cast_nonneg _
  -- The bad points.
  set bad : X → ℝ := fun x ↦ if Good gs f t x then 0 else 1 with hbaddef
  set far : Fin t → X → ℝ := fun j x ↦
    if lvl j / 10 < |avg (signed ψ) (Ω j) x - f x| then 1 else 0 with hfardef
  have hfar0 : ∀ j x, 0 ≤ far j x := fun j x ↦ by
    simp only [hfardef]
    split_ifs <;> norm_num
  have hbad0 : ∀ x, 0 ≤ bad x := fun x ↦ by
    simp only [hbaddef]
    split_ifs <;> norm_num
  have hbad : ∀ x, bad x ≤ ∑ j, far j x := by
    intro x
    simp only [hbaddef]
    split_ifs with hgood
    · exact sum_nonneg fun j _ ↦ hfar0 j x
    · simp only [Good, not_forall, not_le] at hgood
      obtain ⟨j, hj, hjx⟩ := hgood
      have h1 : far ⟨j, hj⟩ x = 1 := by
        simp only [hfardef]
        refine ite_eq_left ?_
        simpa [hgs, gsOf, hj] using hjx
      rw [← h1]
      exact single_le_sum (fun j _ ↦ hfar0 j x) (mem_univ _)
  -- Each level, from the Chernoff event.
  have hlev : ∀ i ∈ range t, ∑ r, piece gs i (g r) ≤
      q * ((1 + 1 / 10) * mean μ (piece gs i) + α) := by
    intro i hi
    have hit := mem_range.1 hi
    have hcongr : piece gs i =
        piece (gsOf (signed ψ) (fun j : Fin (i + 1) ↦ Ω ⟨j, by omega⟩)) i := by
      refine piece_congr fun j hj ↦ ?_
      ext x
      simp [hgs, gsOf, show j < t by omega, show j < i + 1 by omega]
    rw [hcongr]
    exact (hg i hit _).le
  -- (A) the empirical sum of `f²`.
  have hA : ∑ r, f (g r) ^ 2 ≤ 121 / 100 * ∑ r, total gs t (g r) +
      q * (242 / 100 * (1 / 2) ^ t) + ∑ r, bad (g r) := by
    calc ∑ r, f (g r) ^ 2
        ≤ ∑ r, (121 / 100 * total gs t (g r) + 242 / 100 * (1 / 2) ^ t + bad (g r)) :=
          sum_le_sum fun r _ ↦ sq_le_total (hf1 (g r)) ht
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  -- (B) the empirical sum of the pieces.
  have hB : ∑ r, total gs t (g r) ≤ q * (11 / 10 * mean μ (total gs t) + t * α) := by
    have hmean : mean μ (total gs t) = ∑ i ∈ range t, mean μ (piece gs i) :=
      mean_finsetSum μ (range t) (piece gs)
    calc ∑ r, total gs t (g r) = ∑ i ∈ range t, ∑ r, piece gs i (g r) := by
          simp only [total]
          exact sum_comm
      _ ≤ ∑ i ∈ range t, q * ((1 + 1 / 10) * mean μ (piece gs i) + α) := sum_le_sum hlev
      _ = q * (11 / 10 * mean μ (total gs t) + t * α) := by
          rw [hmean, ← mul_sum, sum_add_distrib, ← mul_sum, sum_const, card_range,
            nsmul_eq_mul]
          ring
  -- (C) the mean of the pieces.
  have hC : mean μ (total gs t) ≤ 100 / 81 * mean μ (fun x ↦ f x ^ 2) + 4 * mean μ bad := by
    calc mean μ (total gs t) ≤ mean μ (fun x ↦ 100 / 81 * f x ^ 2 + 4 * bad x) := by
          refine mean_mono μ fun x ↦ (total_le_sq (hf1 x)).trans_eq ?_
          simp only [hbaddef]
          split_ifs <;> ring
      _ = _ := by rw [mean_add, mean_const_mul, mean_const_mul]
  -- (D) the bad points are rare.
  have hD1 : mean μ bad ≤
      ∑ j : Fin t, μ.real {x | lvl j / 10 < |avg (signed ψ) (Ω j) x - f x|} := by
    calc mean μ bad ≤ mean μ (fun x ↦ ∑ j, far j x) := mean_mono μ hbad
      _ = ∑ j, mean μ (far j) := mean_finsetSum μ univ far
      _ = _ := sum_congr rfl fun j _ ↦ (measureReal_eq_mean μ _).symm
  have hD2 : ∑ r, bad (g r) ≤
      ∑ j : Fin t,
        ((univ.filter fun r ↦ lvl j / 10 < |avg (signed ψ) (Ω j) (g r) - f (g r)|).card : ℝ) := by
    calc ∑ r, bad (g r) ≤ ∑ r, ∑ j, far j (g r) := sum_le_sum fun r _ ↦ hbad (g r)
      _ = ∑ j, ∑ r, far j (g r) := sum_comm
      _ = _ := sum_congr rfl fun j _ ↦ by
          rw [card_filter]
          push_cast
          rfl
  have hE : ∀ j : Fin t, q * μ.real {x | lvl j / 10 < |avg (signed ψ) (Ω j) x - f x|} +
      ((univ.filter fun r ↦ lvl j / 10 < |avg (signed ψ) (Ω j) (g r) - f (g r)|).card : ℝ) ≤
      q * (β / t) := by
    intro j
    have h := hΩ j
    rcases hq0.eq_or_lt with h0 | h0
    · have hR : Fintype.card R = 0 := by
        have : (Fintype.card R : ℝ) = 0 := h0.symm
        exact_mod_cast this
      have : (univ.filter fun r ↦ lvl j / 10 < |avg (signed ψ) (Ω j) (g r) - f (g r)|).card = 0 :=
        Nat.eq_zero_of_le_zero ((card_filter_le _ _).trans (by rw [card_univ, hR]))
      rw [this, ← h0]
      simp
    · have := mul_le_mul_of_nonneg_left h h0.le
      rw [mul_add, mul_div_cancel₀ _ h0.ne'] at this
      exact this
  have hF : q * mean μ bad + ∑ r, bad (g r) ≤ q * β := by
    have hsum := sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin t))) ↦ hE j
    rw [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
    have : (t : ℝ) * (q * (β / t)) = q * β := by field_simp
    have hD1' := mul_le_mul_of_nonneg_left hD1 hq0
    linarith
  -- Combine.
  have hC' := mul_le_mul_of_nonneg_left hC hq0
  have hBQ : 0 ≤ ∑ r, bad (g r) := sum_nonneg fun r _ ↦ hbad0 (g r)
  have hBμ : 0 ≤ mean μ bad := mean_nonneg μ hbad0
  nlinarith

end BBKS24.SparseNorm
