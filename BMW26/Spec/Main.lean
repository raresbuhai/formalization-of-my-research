module

public import BMW26.Spec.Deterministic
public import BMW26.Spec.BadSet
public import BMW26.Spec.BadFourier
public import BMW26.Spec.LowDegree
public import BMW26.Spec.BiluLinial
public import BMW26.Spec.Discrepancy

/-!
# Spectral concentration of the percolated hypercube

[BMW26, Lemma 5.1], in the diagonal form used by the sum-of-squares proof
(`BMW26.spectral_whp`): for every `ε > 0` and `K`, if `p ≥ C log m / m` with `C` large enough,
then with probability at least `1 - 1/m²` the percolated hypercube `Q_m(p)` is spectrally close
to `p Q_m` with relative error `ε` and a diagonal error of trace at most `p 2^m / m^K`.

The parameters: `γ = ε / 1000`, `r = m / 100`, `η` from `BMW26.goodNorm_of_disc`, at most
`2^m / m^K'` bad vertices with `K' = 2K + 10`, `κ = |R|/2^m + 2^(-m/10)` and
`λ = m^(-K'/2) = m^(-(K+5))` in `BMW26.specClose_of_facts`, and
`C = max(C_bad, C_disc, 3200/ε²)`, so that `√(2/(p(r+1))) ≤ ε/4` and `p ≥ 1/m`. The five facts
each fail with probability at most `1/m³`, so all hold with probability at least
`1 - 5/m³ ≥ 1 - 1/m²`. The real-number estimates of the trace are in `BMW26.SpecM`.
-/

@[expose] public section

namespace BMW26

open MeasureTheory

namespace SpecM

/-- `m^K 2^(-m/10) ≤ c` for `m` large enough. -/
theorem eventually_pow_mul_rpow_le (K : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, (m : ℝ) ^ K * (2 : ℝ) ^ (-(m : ℝ) / 10) ≤ c := by
  have hb : 1 < (2 : ℝ) ^ ((1 : ℝ) / 10) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have ht := tendsto_pow_const_div_const_pow_of_one_lt K hb
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hc))
  refine ⟨m₀, fun m hm ↦ ?_⟩
  have e : (2 : ℝ) ^ (-(m : ℝ) / 10) = (((2 : ℝ) ^ ((1 : ℝ) / 10)) ^ m)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_neg (by norm_num)]
    congr 1; ring
  rw [e, ← div_eq_mul_inv]
  exact (hm₀ m hm).le

theorem piece1 {M p γ a t : ℝ} {K : ℕ} (hM : 1 ≤ M) (hpM : 1 ≤ p * M) (hγ : 0 < γ)
    (ha0 : 0 ≤ a) (ha : a * M ^ (2 * K + 10) ≤ 1)
    (h7 : 160 / M ≤ γ / 2) (h6 : M ^ (K + 3) * t ≤ γ / 320) :
    40 * M * (a + t) / (γ * p) ≤ p / (4 * M ^ K) := by
  have hM0 : 0 < M := by linarith
  have hp0 : 0 < p := by
    by_contra hp
    have := not_lt.mp hp
    nlinarith
  have hpow : M ^ (K + 4) ≤ M ^ (2 * K + 10) := pow_le_pow_right₀ hM (by omega)
  have h1 : M ^ (K + 3) * a * M ≤ 1 := by
    calc M ^ (K + 3) * a * M = a * M ^ (K + 4) := by ring
      _ ≤ a * M ^ (2 * K + 10) := mul_le_mul_of_nonneg_left hpow ha0
      _ ≤ 1 := ha
  have h2 : 160 * (M ^ (K + 3) * a) ≤ γ / 2 := by
    have : M ^ (K + 3) * a ≤ 1 / M := by rw [le_div_iff₀ hM0]; exact h1
    calc 160 * (M ^ (K + 3) * a) ≤ 160 * (1 / M) := by gcongr
      _ = 160 / M := by ring
      _ ≤ γ / 2 := h7
  have hκ : 160 * M ^ (K + 3) * (a + t) ≤ γ := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : 1 ≤ (p * M) ^ 2 := one_le_pow₀ hpM
  have : M ^ 2 * (40 * M * (a + t) * (4 * M ^ K)) ≤ M ^ 2 * (p * (γ * p)) := by
    calc M ^ 2 * (40 * M * (a + t) * (4 * M ^ K)) = 160 * M ^ (K + 3) * (a + t) := by ring
      _ ≤ γ := hκ
      _ = γ * 1 := by ring
      _ ≤ γ * (p * M) ^ 2 := by gcongr
      _ = M ^ 2 * (p * (γ * p)) := by ring
  exact le_of_mul_le_mul_left this (by positivity)

theorem piece2 {M p : ℝ} {K : ℕ} (hM : 2 ≤ M) (hpM : 1 ≤ p * M) :
    1 / M ^ (K + 5) ≤ p / (4 * M ^ K) := by
  have hM0 : 0 < M := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 : (4 : ℝ) ≤ M ^ 4 :=
    calc (4 : ℝ) ≤ 2 ^ 4 := by norm_num
      _ ≤ M ^ 4 := pow_le_pow_left₀ (by norm_num) hM 4
  have hMK : 0 < M ^ K := by positivity
  calc 1 * (4 * M ^ K) ≤ M ^ 4 * M ^ K := by nlinarith
    _ ≤ (p * M) * (M ^ 4 * M ^ K) := le_mul_of_one_le_left (by positivity) hpM
    _ = p * M ^ (K + 5) := by ring

theorem piece3 {M p a : ℝ} {K : ℕ} (hM : 8 ≤ M) (hpM : 1 ≤ p * M) (ha0 : 0 ≤ a)
    (ha : a * M ^ (2 * K + 10) ≤ 1) :
    a * (16 * M ^ 2 / (1 / M ^ (K + 5)) + 16 * M) ≤ p / (2 * M ^ K) := by
  have hM0 : 0 < M := by linarith
  have e : 16 * M ^ 2 / (1 / M ^ (K + 5)) = 16 * M ^ (K + 7) := by
    rw [div_div_eq_mul_div, div_one]; ring
  rw [e, le_div_iff₀ (by positivity)]
  have hpow : M ^ (K + 4) ≤ M ^ (2 * K + 10) := pow_le_pow_right₀ (by linarith) (by omega)
  have h2 : a * M ^ (K + 4) ≤ 1 := (mul_le_mul_of_nonneg_left hpow ha0).trans ha
  have hM2 : 64 ≤ M ^ 2 := by nlinarith
  have key : M ^ 3 * (a * (16 * M ^ (K + 7) + 16 * M) * (2 * M ^ K)) ≤ M ^ 3 * p := by
    calc M ^ 3 * (a * (16 * M ^ (K + 7) + 16 * M) * (2 * M ^ K))
        = 32 * (a * M ^ (2 * K + 10)) + 32 * (a * M ^ (K + 4)) := by ring
      _ ≤ 32 * 1 + 32 * 1 := by gcongr
      _ ≤ M ^ 2 * 1 := by linarith
      _ ≤ M ^ 2 * (p * M) := by gcongr
      _ = M ^ 3 * p := by ring
  exact le_of_mul_le_mul_left key (by positivity)

/-- The trace bound of `BMW26.specClose_of_facts` with `λ = m^-(K+5)`, `κ = |R|/2^m + t`. -/
theorem trace_le {M n N p γ t : ℝ} {K : ℕ} (hM : 8 ≤ M) (hn : 0 < n) (hN0 : 0 ≤ N)
    (hN : N ≤ n / M ^ (2 * K + 10)) (hpM : 1 ≤ p * M) (hγ : 0 < γ)
    (h7 : 160 / M ≤ γ / 2) (h6 : M ^ (K + 3) * t ≤ γ / 320) :
    n * (40 * M * (N / n + t) / (γ * p) + 1 / M ^ (K + 5)) +
      N * (16 * M ^ 2 / (1 / M ^ (K + 5)) + 16 * M) ≤ p * n / M ^ K := by
  have hM0 : 0 < M := by linarith
  have ha0 : 0 ≤ N / n := div_nonneg hN0 hn.le
  have ha : N / n * M ^ (2 * K + 10) ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hn]
    rwa [le_div_iff₀ (by positivity)] at hN
  have p1 := piece1 (by linarith) hpM hγ ha0 ha h7 h6
  have p2 := piece2 (K := K) (by linarith) hpM
  have p3 := piece3 hM hpM ha0 ha
  have hNa : N = n * (N / n) := by field_simp
  have e : p * n / M ^ K = n * (p / (4 * M ^ K) + p / (4 * M ^ K) + p / (2 * M ^ K)) := by
    field_simp; ring
  calc n * (40 * M * (N / n + t) / (γ * p) + 1 / M ^ (K + 5)) +
        N * (16 * M ^ 2 / (1 / M ^ (K + 5)) + 16 * M)
      = n * (40 * M * (N / n + t) / (γ * p) + 1 / M ^ (K + 5)) +
          n * (N / n) * (16 * M ^ 2 / (1 / M ^ (K + 5)) + 16 * M) := by rw [← hNa]
    _ = n * (40 * M * (N / n + t) / (γ * p) + 1 / M ^ (K + 5) +
          N / n * (16 * M ^ 2 / (1 / M ^ (K + 5)) + 16 * M)) := by ring
    _ ≤ n * (p / (4 * M ^ K) + p / (4 * M ^ K) + p / (2 * M ^ K)) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hn.le
    _ = p * n / M ^ K := e.symm

/-- `μ(A ∩ B) ≥ μ(A) + μ(B) - 1`. -/
theorem inter_ge {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A B : Set Ω} (hB : MeasurableSet B) : μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B) := by
  have := measureReal_union_add_inter (μ := μ) (s := A) hB
  have h1 : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  linarith

/-- Events about the coin weights are measurable. -/
theorem meas_coinW {m : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {a : Fin m × Cube m → Ω → Bool} {p : ℝ} (ha : IsCoins μ a p)
    (P : (Fin m → Cube m → ℝ) → Prop) : MeasurableSet {ω | P (coinW a ω)} :=
  ha.measurableSet_preimage {v | P (fun i x ↦ bit (v (i, x)))}

theorem coinW_01 {m : ℕ} {Ω : Type*} (a : Fin m × Cube m → Ω → Bool) (ω : Ω) (i : Fin m)
    (x : Cube m) : coinW a ω i x = 0 ∨ coinW a ω i x = 1 := by
  unfold coinW bit
  split_ifs <;> simp

end SpecM

/-- **Spectral concentration of the percolated hypercube**, with a diagonal error. -/
theorem spectral_whp {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ p : ℝ, C * Real.log m / m ≤ p → p ≤ 1 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Fin m × Cube m → Ω → Bool),
        IsCoins μ a p →
        1 - 1 / (m : ℝ) ^ 2 ≤ μ.real {ω | ∃ D : Cube m → ℝ, (∀ x, 0 ≤ D x) ∧
          ∑ x, D x ≤ p * 2 ^ m / (m : ℝ) ^ K ∧ SpecClose (coinW a ω) 1 p ε D} := by
  set γ : ℝ := ε / 1000 with hγdef
  have hγ : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by rw [hγdef]; linarith
  obtain ⟨C₁, hC₁, m₁, hbad⟩ := badSmall_whp hγ hγ1 (2 * K + 10)
  obtain ⟨m₂, hlow⟩ := badLow_whp hγ
  obtain ⟨m₃, hrel⟩ := lowRel_whp hγ
  obtain ⟨m₄, hsq⟩ := lowSq_whp
  obtain ⟨η, hη, hη1, hgood⟩ := goodNorm_of_disc hγ hγ1
  obtain ⟨C₅, hC₅, m₅, hdisc⟩ := disc_whp hγ hγ1 hη hη1
  obtain ⟨m₆, hm₆⟩ := SpecM.eventually_pow_mul_rpow_le (K + 3) (c := γ / 320) (by positivity)
  refine ⟨max (max C₁ C₅) (3200 / ε ^ 2), by positivity,
    max (max (max m₁ m₂) (max m₃ m₄)) (max (max m₅ m₆) (⌈320 / γ⌉₊ + ⌈Real.exp 1⌉₊ + 8)), ?_⟩
  intro m hm p hpC hp1 Ω _ μ a ha
  simp only [ge_iff_le, max_le_iff] at hm
  obtain ⟨⟨⟨hm₁, hm₂⟩, hm₃, hm₄⟩, ⟨hm₅, hm₆'⟩, hm₇⟩ := hm
  have := ha.isProb
  set C := max (max C₁ C₅) (3200 / ε ^ 2) with hCdef
  -- the size of `m`
  have hm₇' : ((⌈320 / γ⌉₊ + ⌈Real.exp 1⌉₊ + 8 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm₇
  push_cast at hm₇'
  have hc1 := Nat.le_ceil (320 / γ)
  have hc2 := Nat.le_ceil (Real.exp 1)
  have hc3 : (0 : ℝ) ≤ ⌈320 / γ⌉₊ := Nat.cast_nonneg _
  have hc4 : (0 : ℝ) ≤ ⌈Real.exp 1⌉₊ := Nat.cast_nonneg _
  have hM8 : (8 : ℝ) ≤ m := by linarith
  have hM0 : (0 : ℝ) < m := by linarith
  have hMγ : 320 / γ ≤ m := by linarith
  have hMe : Real.exp 1 ≤ m := by linarith
  have hlog : 1 ≤ Real.log m := (Real.le_log_iff_exp_le hM0).mpr hMe
  have h7 : 160 / (m : ℝ) ≤ γ / 2 := by
    rw [div_le_div_iff₀ hM0 two_pos]
    have := (div_le_iff₀ hγ).mp hMγ
    linarith
  -- the constants
  have hC1 : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC5 : C₅ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hC6 : 3200 / ε ^ 2 ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := by positivity
  have hpC' : C * Real.log m ≤ p * m := (div_le_iff₀ hM0).mp hpC
  have hpm : ∀ C' : ℝ, C' ≤ C → C' * Real.log m / m ≤ p := fun C' h ↦
    le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h (by linarith)) hM0.le)
      hpC
  have hε2 : 3200 ≤ C * ε ^ 2 := (div_le_iff₀ (by positivity)).mp hC6
  have hε2' : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le hε1
  have hC3200 : 3200 ≤ C := hε2.trans (mul_le_of_le_one_right hC0 hε2')
  have hCge : C ≤ C * Real.log m := le_mul_of_one_le_right hC0 hlog
  have hpM : 1 ≤ p * m := by linarith
  have hp0 : 0 < p := by
    by_contra hp
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hp) hM0.le
    linarith
  have hpm1 : 1 / (m : ℝ) ≤ p := by rw [div_le_iff₀ hM0]; linarith
  -- the parameter `θ`
  have hmr : (m : ℝ) ≤ 100 * ((m / 100 : ℕ) + 1) := by
    have : m ≤ 100 * (m / 100 + 1) := by omega
    exact_mod_cast this
  have hθ : 2 * (151 * γ + Real.sqrt (2 / (p * ((m / 100 : ℕ) + 1)))) ≤ ε := by
    have hr0 : (0 : ℝ) < (m / 100 : ℕ) + 1 := by positivity
    have hsq : Real.sqrt (2 / (p * ((m / 100 : ℕ) + 1))) ≤ ε / 4 := by
      rw [Real.sqrt_le_left (by positivity), div_le_iff₀ (by positivity)]
      have h1 : C ≤ 100 * (p * ((m / 100 : ℕ) + 1)) := by
        have := mul_le_mul_of_nonneg_left hmr hp0.le
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ε)
      have e : (ε / 4) ^ 2 * (p * ((m / 100 : ℕ) + 1)) =
          ε ^ 2 * (100 * (p * ((m / 100 : ℕ) + 1))) / 1600 := by ring
      rw [e]
      linarith
    rw [hγdef]; linarith
  -- the five events
  have E1 := hbad m hm₁ p (hpm C₁ hC1) hp1 μ a ha
  have E2 := hlow m hm₂ p hp0.le hp1 μ a ha
  have E3 := hrel m hm₃ p hpm1 hp1 μ a ha
  have E4 := hsq m hm₄ p hpm1 hp1 μ a ha
  have E5 := hdisc m hm₅ p (hpm C₅ hC5) hp1 μ a ha
  set A₁ := {ω | ((badSet (coinW a ω) p γ).card : ℝ) ≤ 2 ^ m / (m : ℝ) ^ (2 * K + 10)}
  set A₂ := {ω | BadLow (coinW a ω) p γ
    ((badSet (coinW a ω) p γ).card / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10)) (m / 100)}
  set A₃ := {ω | LowRel (coinW a ω) p γ (m / 100)}
  set A₄ := {ω | LowSq (coinW a ω) p (m / 100)}
  set A₅ := {ω | Disc (coinW a ω) p γ η}
  have hA₂ : MeasurableSet A₂ := SpecM.meas_coinW ha (fun w ↦ BadLow w p γ
    ((badSet w p γ).card / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10)) (m / 100))
  have hA₃ : MeasurableSet A₃ := SpecM.meas_coinW ha (fun w ↦ LowRel w p γ (m / 100))
  have hA₄ : MeasurableSet A₄ := SpecM.meas_coinW ha (fun w ↦ LowSq w p (m / 100))
  have hA₅ : MeasurableSet A₅ := SpecM.meas_coinW ha (fun w ↦ Disc w p γ η)
  have I2 := SpecM.inter_ge (μ := μ) (A := A₁) hA₂
  have I3 := SpecM.inter_ge (μ := μ) (A := A₁ ∩ A₂) hA₃
  have I4 := SpecM.inter_ge (μ := μ) (A := A₁ ∩ A₂ ∩ A₃) hA₄
  have I5 := SpecM.inter_ge (μ := μ) (A := A₁ ∩ A₂ ∩ A₃ ∩ A₄) hA₅
  -- on the intersection, `specClose_of_facts`
  have hsub : A₁ ∩ A₂ ∩ A₃ ∩ A₄ ∩ A₅ ⊆ {ω | ∃ D : Cube m → ℝ, (∀ x, 0 ≤ D x) ∧
      ∑ x, D x ≤ p * 2 ^ m / (m : ℝ) ^ K ∧ SpecClose (coinW a ω) 1 p ε D} := by
    rintro ω ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    have hw := SpecM.coinW_01 a ω
    have hG := hgood hw hp0 hp1 h5
    have hκ : 0 ≤ ((badSet (coinW a ω) p γ).card : ℝ) / 2 ^ m + (2 : ℝ) ^ (-(m : ℝ) / 10) := by
      positivity
    obtain ⟨D, hD0, hDsum, hD⟩ := specClose_of_facts hw hp0 hp1 hγ hγ1 hκ
      (lam := 1 / (m : ℝ) ^ (K + 5)) (by positivity) hmr hθ h3 h4 hG h2
    refine ⟨D, hD0, hDsum.trans ?_, hD⟩
    exact SpecM.trace_le hM8 (by positivity) (Nat.cast_nonneg _) h1 hpM hγ h7 (hm₆ m hm₆')
  have hmono := measureReal_mono (μ := μ) hsub
  have hfin : 1 - 1 / (m : ℝ) ^ 2 ≤ 1 - 5 / (m : ℝ) ^ 3 := by
    have : 5 / (m : ℝ) ^ 3 ≤ 1 / (m : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc 5 * (m : ℝ) ^ 2 ≤ m * (m : ℝ) ^ 2 := by gcongr; linarith
        _ = 1 * (m : ℝ) ^ 3 := by ring
    linarith
  have h5m : 1 - 1 / (m : ℝ) ^ 3 + (1 - 1 / (m : ℝ) ^ 3) + (1 - 1 / (m : ℝ) ^ 3) +
      (1 - 1 / (m : ℝ) ^ 3) + (1 - 1 / (m : ℝ) ^ 3) - 4 = 1 - 5 / (m : ℝ) ^ 3 := by ring
  linarith

end BMW26
