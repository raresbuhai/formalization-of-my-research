module

public import BMW26.Cube.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Moments.Bernstein

/-!
# Independent coins

The probability space of the analysis: independent `p`-coins `a i : Ω → Bool` (`BMW26.IsCoins`),
and the tools the probabilistic lemmas use.

* `BMW26.bit b`: `1` for `true`, `0` for `false`.
* `BMW26.coinW a ω`: edge weights of the hypercube from coins indexed by `Fin m × Cube m` (the coin
  `a (i, x)` with `xᵢ = false` decides the edge `{x, flip x i}`; the other coins play no role).
* Second moments of linear forms in the centred coins, Bernstein's inequality (from TauCeti,
  `ProbabilityTheory.iIndepFun.measureReal_abs_sum_ge_le_of_abs_le`), Markov's inequality, and
  independence of functions of disjoint sets of coins.
-/

@[expose] public section

namespace BMW26

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*}

/-- Independent `p`-coins `a i`, `i ∈ ι`, on the probability space `(Ω, μ)`. -/
structure IsCoins (μ : Measure Ω) (a : ι → Ω → Bool) (p : ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  meas : ∀ i, Measurable (a i)
  indep : iIndepFun a μ
  prob_true : ∀ i, μ.real {ω | a i ω = true} = p

/-- The value of a coin: `1` for `true`, `0` for `false`. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The edge weights given by coins indexed by `Fin m × Cube m`: the weight of the edge
`{x, flip x i}` with `xᵢ = false` is the coin `a (i, x)`. -/
def coinW {m : ℕ} (a : Fin m × Cube m → Ω → Bool) (ω : Ω) (i : Fin m) (x : Cube m) : ℝ :=
  bit (a (i, x) ω)

namespace Coins

/-! ### Helpers -/

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp [bit]

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

theorem measurable_bit : Measurable bit := measurable_of_countable _

/-- `|bit b - p| ≤ 1` for `p ∈ [0, 1]`. -/
theorem abs_bit_sub_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) : |bit b - p| ≤ 1 := by
  rw [abs_le]
  cases b
  · simp only [bit]; constructor <;> norm_num <;> linarith
  · simp only [bit]; constructor <;> norm_num <;> linarith

/-- `(bit b - p)² = (1 - 2p) bit b + p²`. -/
theorem bit_sub_sq (p : ℝ) (b : Bool) : (bit b - p) ^ 2 = (1 - 2 * p) * bit b + p ^ 2 := by
  cases b <;> simp only [bit, Bool.false_eq_true, ↓reduceIte] <;> ring

/-- A real function of a measurable map into a finite type is integrable. -/
theorem integrable_comp {μ : Measure Ω} [IsFiniteMeasure μ] {β : Type*} [MeasurableSpace β]
    [Finite β] [MeasurableSingletonClass β] {f : Ω → β} (hf : Measurable f) (F : β → ℝ) :
    Integrable (fun ω ↦ F (f ω)) μ :=
  (Integrable.of_finite (μ := μ.map f) (f := F)).comp_measurable hf

end Coins

namespace IsCoins

variable {μ : Measure Ω} {a : ι → Ω → Bool} {p : ℝ}

theorem p_nonneg (h : IsCoins μ a p) [Nonempty ι] : 0 ≤ p := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [← h.prob_true i]
  exact measureReal_nonneg

theorem p_le_one (h : IsCoins μ a p) [Nonempty ι] : p ≤ 1 := by
  have := h.isProb
  obtain ⟨i⟩ := ‹Nonempty ι›
  rw [← h.prob_true i]
  exact measureReal_le_one

/-- A subfamily of independent coins, reindexed injectively, is a family of independent coins. -/
theorem precomp {κ : Type*} (h : IsCoins μ a p) {f : κ → ι} (hf : Function.Injective f) :
    IsCoins μ (fun k ↦ a (f k)) p :=
  ⟨h.isProb, fun k ↦ h.meas (f k), h.indep.precomp hf, fun k ↦ h.prob_true (f k)⟩

/-- With finitely many coins, every event about them is measurable. -/
theorem measurableSet_preimage [Finite ι] (h : IsCoins μ a p) (s : Set (ι → Bool)) :
    MeasurableSet {ω | (fun i ↦ a i ω) ∈ s} :=
  (measurable_pi_iff.2 h.meas) s.to_countable.measurableSet

theorem integral_bit (h : IsCoins μ a p) (i : ι) : ∫ ω, bit (a i ω) ∂μ = p := by
  have hs : MeasurableSet {ω | a i ω = true} := h.meas i (measurableSet_singleton true)
  have : (fun ω ↦ bit (a i ω)) = Set.indicator {ω | a i ω = true} 1 := by
    ext ω
    by_cases hω : a i ω = true <;> simp [bit, hω, Set.indicator]
  rw [this, integral_indicator_one hs, h.prob_true]

theorem _root_.BMW26.Coins.integrable_coin (h : IsCoins μ a p) (i : ι) (F : Bool → ℝ) :
    Integrable (fun ω ↦ F (a i ω)) μ :=
  have := h.isProb
  Coins.integrable_comp (h.meas i) F

/-- `p ∈ [0, 1]` as soon as there is one coin. -/
theorem _root_.BMW26.Coins.p_mem (h : IsCoins μ a p) (i : ι) : 0 ≤ p ∧ p ≤ 1 := by
  have := h.isProb
  rw [← h.prob_true i]
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem _root_.BMW26.Coins.integral_centered (h : IsCoins μ a p) (i : ι) :
    ∫ ω, (bit (a i ω) - p) ∂μ = 0 := by
  have := h.isProb
  rw [integral_sub (Coins.integrable_coin h i bit) (integrable_const p), integral_bit h i]
  simp

/-- Centred coins are uncorrelated, with variance `p (1 - p)`. -/
theorem _root_.BMW26.Coins.integral_centered_mul [DecidableEq ι] (h : IsCoins μ a p) (i j : ι) :
    ∫ ω, (bit (a i ω) - p) * (bit (a j ω) - p) ∂μ = if i = j then p * (1 - p) else 0 := by
  have := h.isProb
  split_ifs with hij
  · subst hij
    simp_rw [← sq, Coins.bit_sub_sq]
    rw [integral_add ((Coins.integrable_coin h i bit).const_mul _) (integrable_const _),
      integral_const_mul, integral_bit h i]
    simp; ring
  · have hφ : Measurable fun b : Bool ↦ bit b - p := measurable_of_countable _
    have hind : IndepFun (fun ω ↦ bit (a i ω) - p) (fun ω ↦ bit (a j ω) - p) μ :=
      (h.indep.indepFun hij).comp hφ hφ
    rw [IndepFun.integral_fun_mul_eq_mul_integral hind
      (hφ.comp (h.meas i)).aestronglyMeasurable (hφ.comp (h.meas j)).aestronglyMeasurable]
    have h0 : ∫ ω, (bit (a i ω) - p) ∂μ = 0 := Coins.integral_centered h i
    rw [h0, zero_mul]

/-- **Second moments of linear forms in the centred coins.** -/
theorem integral_sum_mul_sum (h : IsCoins μ a p) (s : Finset ι) (c c' : ι → ℝ) :
    ∫ ω, (∑ i ∈ s, c i * (bit (a i ω) - p)) * (∑ i ∈ s, c' i * (bit (a i ω) - p)) ∂μ =
      p * (1 - p) * ∑ i ∈ s, c i * c' i := by
  classical
  have hpt : ∀ ω, (∑ i ∈ s, c i * (bit (a i ω) - p)) * (∑ i ∈ s, c' i * (bit (a i ω) - p)) =
      ∑ i ∈ s, ∑ j ∈ s, c i * c' j * ((bit (a i ω) - p) * (bit (a j ω) - p)) := by
    intro ω
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have hint : ∀ i j, Integrable (fun ω ↦ (bit (a i ω) - p) * (bit (a j ω) - p)) μ := by
    intro i j
    have := h.isProb
    exact Coins.integrable_comp ((h.meas i).prodMk (h.meas j))
      (fun q : Bool × Bool ↦ (bit q.1 - p) * (bit q.2 - p))
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ (hint i j).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ ↦ (hint _ j).const_mul _, integral_const_mul,
    Coins.integral_centered_mul h, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp [hi]; ring

theorem integral_sum_sq (h : IsCoins μ a p) (s : Finset ι) (c : ι → ℝ) :
    ∫ ω, (∑ i ∈ s, c i * (bit (a i ω) - p)) ^ 2 ∂μ = p * (1 - p) * ∑ i ∈ s, c i ^ 2 := by
  simp_rw [sq]
  exact h.integral_sum_mul_sum s c c

/-- **Bernstein's inequality** for a linear form in the centred coins with coefficients at most
`b` in absolute value. -/
theorem measureReal_abs_sum_ge_le (h : IsCoins μ a p) (s : Finset ι) (c : ι → ℝ) {b t : ℝ}
    (hb : ∀ i ∈ s, |c i| ≤ b) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |∑ i ∈ s, c i * (bit (a i ω) - p)|} ≤
      2 * Real.exp (-t ^ 2 / (2 * (p * ∑ i ∈ s, c i ^ 2 + b * t / 3))) := by
  classical
  have := h.isProb
  have hφ : ∀ i, Measurable fun b : Bool ↦ c i * (bit b - p) := fun i ↦ measurable_of_countable _
  have hind : iIndepFun (fun i ω ↦ c i * (bit (a i ω) - p)) μ :=
    h.indep.comp (fun i b ↦ c i * (bit b - p)) hφ
  have hbd : ∀ i ∈ s, ∀ᵐ ω ∂μ, |c i * (bit (a i ω) - p)| ≤ b := by
    intro i hi
    refine ae_of_all _ fun ω ↦ ?_
    obtain ⟨hp0, hp1⟩ := Coins.p_mem h i
    rw [abs_mul]
    calc |c i| * |bit (a i ω) - p| ≤ |c i| * 1 :=
          mul_le_mul_of_nonneg_left (Coins.abs_bit_sub_le hp0 hp1 _) (abs_nonneg _)
      _ ≤ b := by rw [mul_one]; exact hb i hi
  have hmean : ∀ i ∈ s, ∫ ω, c i * (bit (a i ω) - p) ∂μ = 0 := by
    intro i _
    rw [integral_const_mul, Coins.integral_centered h i, mul_zero]
  refine (hind.measureReal_abs_sum_ge_le_of_abs_le (s := s) (b := b)
    (fun i _ ↦ ((hφ i).comp (h.meas i)).aemeasurable) hmean hbd ht).trans ?_
  have hv : ∑ i ∈ s, ∫ ω, (c i * (bit (a i ω) - p)) ^ 2 ∂μ = p * (1 - p) * ∑ i ∈ s, c i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp_rw [mul_pow, sq (bit _ - p)]
    simp only [integral_const_mul, Coins.integral_centered_mul h i i, ↓reduceIte]
    ring
  rw [hv]
  gcongr 2 * Real.exp ?_
  set S := ∑ i ∈ s, c i ^ 2 with hS_def
  rcases eq_or_lt_of_le ht with ht0 | ht0
  · subst ht0; simp
  by_cases hS : S = 0
  · rw [hS]; simp
  obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  replace hci : c i ≠ 0 := fun h0 ↦ hci (by rw [h0]; ring)
  obtain ⟨hp0, hp1⟩ := Coins.p_mem h i
  have hb0 : 0 < b := (abs_pos.2 hci).trans_le (hb i hi)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hA : 0 < p * (1 - p) * S + b * t / 3 := by
    have : 0 ≤ p * (1 - p) * S := mul_nonneg (mul_nonneg hp0 (by linarith)) hS0
    have : 0 < b * t / 3 := by positivity
    linarith
  rw [neg_div, neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (sq_nonneg t) (by linarith)
  have : p * (1 - p) * S ≤ p * S := by nlinarith [mul_nonneg (mul_nonneg hp0 hp0) hS0]
  linarith

/-- **Independence of functions of disjoint sets of coins.** If `F` depends only on the coins in
`s`, and `G` only on those in `t`, with `s` and `t` disjoint, then `E[F G] = E[F] E[G]`. -/
theorem integral_mul_of_disjoint (h : IsCoins μ a p) {s t : Finset ι}
    (hst : Disjoint s t) {F G : (ι → Bool) → ℝ}
    (hF : ∀ v v' : ι → Bool, (∀ i ∈ s, v i = v' i) → F v = F v')
    (hG : ∀ v v' : ι → Bool, (∀ i ∈ t, v i = v' i) → G v = G v') :
    ∫ ω, F (fun i ↦ a i ω) * G (fun i ↦ a i ω) ∂μ =
      (∫ ω, F (fun i ↦ a i ω) ∂μ) * ∫ ω, G (fun i ↦ a i ω) ∂μ := by
  classical
  have := h.isProb
  have hind := h.indep.indepFun_finset s t hst h.meas
  let F' : (s → Bool) → ℝ := fun u ↦ F fun i ↦ if hi : i ∈ s then u ⟨i, hi⟩ else false
  let G' : (t → Bool) → ℝ := fun u ↦ G fun i ↦ if hi : i ∈ t then u ⟨i, hi⟩ else false
  have hF' : ∀ ω, F (fun i ↦ a i ω) = F' (fun i : s ↦ a i ω) :=
    fun ω ↦ hF _ _ fun i hi ↦ by simp [hi]
  have hG' : ∀ ω, G (fun i ↦ a i ω) = G' (fun i : t ↦ a i ω) :=
    fun ω ↦ hG _ _ fun i hi ↦ by simp [hi]
  have hmF : Measurable F' := measurable_of_finite _
  have hmG : Measurable G' := measurable_of_finite _
  have hms : Measurable fun ω (i : s) ↦ a i ω := measurable_pi_iff.2 fun i ↦ h.meas i
  have hmt : Measurable fun ω (i : t) ↦ a i ω := measurable_pi_iff.2 fun i ↦ h.meas i
  have hind' : IndepFun (fun ω ↦ F' fun i : s ↦ a i ω) (fun ω ↦ G' fun i : t ↦ a i ω) μ :=
    hind.comp hmF hmG
  simp_rw [hF', hG']
  exact IndepFun.integral_fun_mul_eq_mul_integral hind' (hmF.comp hms).aestronglyMeasurable
    (hmG.comp hmt).aestronglyMeasurable

/-- **Markov's inequality** for a nonnegative function of finitely many coins. -/
theorem measureReal_ge_le [Finite ι] (h : IsCoins μ a p) {F : (ι → Bool) → ℝ}
    (hF : ∀ v, 0 ≤ F v) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ F (fun i ↦ a i ω)} ≤ (∫ ω, F (fun i ↦ a i ω) ∂μ) / t := by
  have := h.isProb
  rw [le_div_iff₀ ht, mul_comm]
  exact mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω ↦ hF _)
    (Coins.integrable_comp (measurable_pi_iff.2 h.meas) F) t

end IsCoins

end BMW26
