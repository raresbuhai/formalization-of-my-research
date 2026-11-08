module

public import BMW26.Spec.Defs

/-!
# Few bad vertices

[BMW26, Lemma 5.2]: with probability at least `1 - 1/m³`, at most `2^m / m^K` vertices of
`Q_m(p)` have a degree outside `(1 ± γ) p m`, when `p ≥ C log m / m` for `C` large enough
depending on `γ` and `K`; more generally (`BMW26.badSmall_whp_pow`) with probability at least
`1 - 1/m^q`. Each vertex is bad with probability at most
`2 exp(-γ² p m / (2 (1 + γ/3))) ≤ 2 exp(-3 γ² p m / 8) ≤ 2 / m^(K+q+1)` with
`C = 8 (K + q + 1) / (3 γ²)` (Bernstein, `BMW26.IsCoins.measureReal_abs_sum_ge_le`, for the `m`
coins at the vertex), so the expected number of bad vertices is at most `2 · 2^m / m^(K+q+1)`;
then Markov.
-/

@[expose] public section

namespace BMW26

open MeasureTheory Finset

namespace BadS

variable {Ω : Type*} {m : ℕ}

theorem mem_badSet {w : Fin m → Cube m → ℝ} {p γ : ℝ} {x : Cube m} :
    x ∈ badSet w p γ ↔ γ * p * m < |deg w x - p * m| := by
  unfold badSet
  simp

/-- A function of finitely many coins is integrable. -/
theorem integrable [MeasurableSpace Ω] {ι : Type*} [Finite ι] {μ : Measure Ω}
    {a : ι → Ω → Bool} {p : ℝ}
    (h : IsCoins μ a p) (F : (ι → Bool) → ℝ) : Integrable (fun ω ↦ F (fun i ↦ a i ω)) μ := by
  classical
  have := Fintype.ofFinite ι
  have := h.isProb
  have hm : Measurable fun ω ↦ F (fun i ↦ a i ω) :=
    (measurable_of_countable F).comp (Measurable.of_eval h.meas)
  refine Integrable.of_bound hm.aestronglyMeasurable (∑ v, |F v|) (Filter.Eventually.of_forall ?_)
  intro ω
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun v ↦ |F v|) (fun v _ ↦ abs_nonneg _) (mem_univ _)

/-- The degree of `x` minus its mean, as a linear form in the centred coins at `x`. -/
theorem deg_sub (a : Fin m × Cube m → Ω → Bool) (ω : Ω) (p : ℝ) (x : Cube m) :
    deg (coinW a ω) x - p * m = ∑ i : Fin m, 1 * (bit (a (i, lowPt x i) ω) - p) := by
  simp [deg, coinW, Finset.sum_sub_distrib, mul_comm]

/-- **One vertex is rarely bad** (Bernstein). -/
theorem measureReal_bad_le [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p γ : ℝ}
    (h : IsCoins μ a p) (hγ : 0 ≤ γ) (hp : 0 ≤ p) (x : Cube m) :
    μ.real {ω | x ∈ badSet (coinW a ω) p γ} ≤
      2 * Real.exp (-(γ * p * m) ^ 2 / (2 * (p * m + 1 * (γ * p * m) / 3))) := by
  have := h.isProb
  have hx : Function.Injective fun i : Fin m ↦ ((i, lowPt x i) : Fin m × Cube m) :=
    fun i j hij ↦ congrArg Prod.fst hij
  have hc := h.precomp hx
  have hB := hc.measureReal_abs_sum_ge_le univ (fun _ ↦ 1) (b := 1) (t := γ * p * m)
    (fun _ _ ↦ by simp) (by positivity)
  simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hB
  refine le_trans (measureReal_mono ?_) hB
  intro ω hω
  simp only [Set.mem_ofPred_eq, mem_badSet, deg_sub] at hω ⊢
  exact hω.le

/-- The exponent of the Bernstein bound is at least `(K + 4) log m`. -/
theorem exponent_le {γ P L : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hP : 0 < P) (N : ℝ)
    (hPL : 8 * N / (3 * γ ^ 2) * L ≤ P) :
    N * L ≤ (γ * P) ^ 2 / (2 * (P + 1 * (γ * P) / 3)) := by
  have hγ2 : 0 < γ ^ 2 := by positivity
  have h1 : N * L ≤ 3 * γ ^ 2 / 8 * P := by
    have := mul_le_mul_of_nonneg_left hPL (by positivity : (0 : ℝ) ≤ 3 * γ ^ 2 / 8)
    calc N * L = 3 * γ ^ 2 / 8 * (8 * N / (3 * γ ^ 2) * L) := by
          field_simp
      _ ≤ 3 * γ ^ 2 / 8 * P := this
  refine h1.trans ?_
  rw [le_div_iff₀ (by positivity)]
  have : 0 ≤ γ ^ 2 * P ^ 2 * (1 - γ) := mul_nonneg (by positivity) (by linarith)
  nlinarith [this]

/-- `exp (-n log m) = 1 / m^n`. -/
theorem exp_neg_log {m : ℝ} (hm : 0 < m) (n : ℕ) :
    Real.exp (-((n : ℝ) * Real.log m)) = 1 / m ^ n := by
  rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hm, one_div]

end BadS

open BadS in
/-- **Few bad vertices**, with failure probability at most `1/m^q` for any `q`. -/
theorem badSmall_whp_pow {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (K q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, C * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ q ≤
          μ.real {ω | ((badSet (coinW a ω) p γ).card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ K} := by
  refine ⟨8 * ((K + q + 1 : ℕ) : ℝ) / (3 * γ ^ 2), by positivity, 2, ?_⟩
  intro m hm p hpC hp1 Ω _ μ a h
  have := h.isProb
  have hm0 : (0 : ℝ) < m := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 0 < Real.log m := Real.log_pos (by linarith)
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hpC
  have hP : 0 < p * m := mul_pos hp0 hm0
  have hPL : 8 * ((K + q + 1 : ℕ) : ℝ) / (3 * γ ^ 2) * Real.log m ≤ p * m := by
    rw [div_le_iff₀ hm0] at hpC
    linarith
  -- each vertex is bad with probability at most `2 / m^(K+q+1)`
  have hvert : ∀ x : Cube m,
      μ.real {ω | x ∈ badSet (coinW a ω) p γ} ≤ 2 * (1 / m ^ (K + q + 1)) := by
    intro x
    refine (measureReal_bad_le h hγ.le hp0.le x).trans ?_
    rw [← exp_neg_log hm0 (K + q + 1)]
    gcongr
    have := exponent_le hγ hγ1 hP _ hPL
    rw [neg_div]
    simpa [mul_assoc] using this
  -- the expected number of bad vertices
  set F : (Fin m × Cube m → Bool) → ℝ :=
    fun v ↦ ((badSet (fun i y ↦ bit (v (i, y))) p γ).card : ℝ) with hF
  have hFsum : ∀ v, F v =
      ∑ x, if x ∈ badSet (fun i y ↦ bit (v (i, y))) p γ then (1 : ℝ) else 0 := by
    intro v
    simp [hF]
  have hint : ∫ ω, F (fun j ↦ a j ω) ∂μ ≤ 2 ^ m * (2 * (1 / m ^ (K + q + 1))) := by
    simp_rw [hFsum]
    rw [integral_finsetSum _ (fun x _ ↦ integrable h
      (fun v ↦ if x ∈ badSet (fun i y ↦ bit (v (i, y))) p γ then (1 : ℝ) else 0))]
    have hcard : (2 : ℝ) ^ m = ∑ _x : Cube m, (1 : ℝ) := by simp
    rw [hcard, Finset.sum_mul]
    refine Finset.sum_le_sum fun x _ ↦ ?_
    rw [one_mul]
    have hmeas : MeasurableSet {ω | x ∈ badSet (coinW a ω) p γ} :=
      h.measurableSet_preimage {v | x ∈ badSet (fun i y ↦ bit (v (i, y))) p γ}
    have heq : (fun ω ↦ if x ∈ badSet (fun i y ↦ bit (a (i, y) ω)) p γ then (1 : ℝ) else 0) =
        Set.indicator {ω | x ∈ badSet (coinW a ω) p γ} 1 := by
      funext ω
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
      rfl
    rw [heq, integral_indicator_one hmeas]
    exact hvert x
  -- Markov
  have ht : (0 : ℝ) < 2 ^ m / (m : ℝ) ^ K := by positivity
  have hM := h.measureReal_ge_le (F := F) (fun v ↦ by simp [hF]) ht
  have hMb : μ.real {ω | 2 ^ m / (m : ℝ) ^ K ≤ F (fun j ↦ a j ω)} ≤ 1 / (m : ℝ) ^ q := by
    refine hM.trans ?_
    refine (div_le_div_of_nonneg_right hint ht.le).trans ?_
    have : 2 ^ m * (2 * (1 / (m : ℝ) ^ (K + q + 1))) / (2 ^ m / (m : ℝ) ^ K) =
        2 / (m : ℝ) ^ (q + 1) := by
      field_simp
      ring
    rw [this, div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
    have : (0 : ℝ) ≤ (m : ℝ) ^ q := by positivity
    nlinarith
  -- the complement
  have hU : (Set.univ : Set Ω) ⊆ {ω | ((badSet (coinW a ω) p γ).card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ K} ∪
      {ω | 2 ^ m / (m : ℝ) ^ K ≤ F (fun j ↦ a j ω)} := by
    intro ω _
    rcases le_total ((badSet (coinW a ω) p γ).card : ℝ) (2 ^ m / (m : ℝ) ^ K) with hle | hle
    · exact Or.inl hle
    · exact Or.inr hle
  have h1 : (1 : ℝ) ≤ μ.real {ω | ((badSet (coinW a ω) p γ).card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ K} +
      μ.real {ω | 2 ^ m / (m : ℝ) ^ K ≤ F (fun j ↦ a j ω)} := by
    have := (measureReal_mono hU).trans (measureReal_union_le (μ := μ) _ _)
    simpa using this
  linarith

/-- **Few bad vertices.** -/
theorem badSmall_whp {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, C * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 3 ≤
          μ.real {ω | ((badSet (coinW a ω) p γ).card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ K} :=
  badSmall_whp_pow hγ hγ1 K 3

end BMW26
