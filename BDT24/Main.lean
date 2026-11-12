module

public import BDT24.Alg.RunTime
public import BDT24.Analysis.Planted
public import BDT24.Analysis.Null

/-!
# Theorem 3.1

`BDT24.Main.negSPCA_of_sparse_regression_main`: the statement of `BDT24/Challenge.lean`.

The algorithm is `BDT24.Alg.algB A e` with `M = rounds δ n = min ⌊√⌊1/(2δ)⌋⌋ 2^(n / K₀)`
rounds. On planted input it fails with probability at most `M · 2 (δ + η)`
(`BDT24.Analysis.output_false_le`, `BDT24.Analysis.planted_calls`), on null input with probability
at most `1/(M+1) + M η'` (`BDT24.Analysis.null_true`), where `η, η' ≤ C exp(-n/10⁶)`
(`BDT24.Analysis.prob_not_goodP`, `BDT24.Analysis.prob_not_samp`). As `M² ≤ 1/(2δ)`,
`2 M δ ≤ √(2δ)`; as `M ≤ 2^(n/K₀)` and `log 2 / K₀ ≤ 1/(2 · 10⁶)`, `M η ≤ C exp(-c n)` with
`c = log 2 / K₀`; and `1/(M+1)` is at most `√(2δ)` when `M = ⌊√⌊1/(2δ)⌋⌋`, and at most
`2 exp(-c n)` when `M = 2^(n/K₀)`.
-/

@[expose] public section

namespace BDT24.Main

open MeasureTheory ProbabilityTheory BDT24.Alg BDT24.Prob BDT24.Analysis

/-- The rate `c = log 2 / K₀` of the exponential. -/
noncomputable def rate : ℝ := Real.log 2 / K0

theorem rate_pos : 0 < rate := by
  unfold rate K0
  positivity

theorem rate_le : rate ≤ 1 / 2000000 := by
  unfold rate K0
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have := Real.log_two_lt_d9
  norm_num at this ⊢
  linarith

/-- `M² ≤ 1/(2δ)`. -/
theorem rounds_sq_le {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    (rounds δ n : ℝ) ^ 2 ≤ 1 / (2 * (δ : ℝ)) := by
  have h1 : rounds δ n ≤ Nat.sqrt ⌊1 / (2 * δ)⌋₊ := min_le_left _ _
  have h2 : Nat.sqrt ⌊1 / (2 * δ)⌋₊ ^ 2 ≤ ⌊1 / (2 * δ)⌋₊ := Nat.sqrt_le' _
  have h3 : ((⌊1 / (2 * δ)⌋₊ : ℕ) : ℚ) ≤ 1 / (2 * δ) := Nat.floor_le (by positivity)
  have h4 : ((rounds δ n : ℕ) : ℚ) ^ 2 ≤ 1 / (2 * δ) := by
    have : rounds δ n ^ 2 ≤ ⌊1 / (2 * δ)⌋₊ :=
      (Nat.pow_le_pow_left h1 2).trans h2
    calc ((rounds δ n : ℕ) : ℚ) ^ 2 = ((rounds δ n ^ 2 : ℕ) : ℚ) := by push_cast; ring
      _ ≤ ((⌊1 / (2 * δ)⌋₊ : ℕ) : ℚ) := by exact_mod_cast this
      _ ≤ 1 / (2 * δ) := h3
  have h5 : (((rounds δ n : ℕ) : ℚ) ^ 2 : ℝ) ≤ ((1 / (2 * δ) : ℚ) : ℝ) := by exact_mod_cast h4
  push_cast at h5
  exact h5

/-- `2 M δ ≤ √(2δ)`. -/
theorem two_mul_rounds_le {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    2 * (rounds δ n : ℝ) * δ ≤ √(2 * (δ : ℝ)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have h := rounds_sq_le hδ n
  have hsq : (2 * (rounds δ n : ℝ) * δ) ^ 2 ≤ 2 * (δ : ℝ) := by
    have : (2 * (rounds δ n : ℝ) * δ) ^ 2 = 4 * (δ : ℝ) ^ 2 * (rounds δ n : ℝ) ^ 2 := by ring
    rw [this]
    calc 4 * (δ : ℝ) ^ 2 * (rounds δ n : ℝ) ^ 2 ≤ 4 * (δ : ℝ) ^ 2 * (1 / (2 * (δ : ℝ))) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 2 * δ := by field_simp; ring
  calc 2 * (rounds δ n : ℝ) * δ = √((2 * (rounds δ n : ℝ) * δ) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ √(2 * (δ : ℝ)) := Real.sqrt_le_sqrt hsq

/-- `M ≤ exp(c n)`. -/
theorem rounds_le_exp (δ : ℚ) (n : ℕ) : (rounds δ n : ℝ) ≤ Real.exp (rate * n) := by
  have h1 : rounds δ n ≤ 2 ^ (n / K0) := min_le_right _ _
  have h2 : ((n / K0 : ℕ) : ℝ) ≤ (n : ℝ) / K0 := Nat.cast_div_le
  calc (rounds δ n : ℝ) ≤ ((2 ^ (n / K0) : ℕ) : ℝ) := by exact_mod_cast h1
    _ = Real.exp (Real.log 2 * (n / K0 : ℕ)) := by
        rw [Real.exp_mul, Real.exp_log (by norm_num)]; push_cast; rw [Real.rpow_natCast]
    _ ≤ Real.exp (rate * n) := by
        refine Real.exp_le_exp.2 ?_
        unfold rate
        rw [div_mul_eq_mul_div]
        calc Real.log 2 * ((n / K0 : ℕ) : ℝ) ≤ Real.log 2 * ((n : ℝ) / K0) :=
              mul_le_mul_of_nonneg_left h2 (Real.log_nonneg (by norm_num))
          _ = Real.log 2 * n / K0 := by ring

/-- `M C exp(-n/10⁶) ≤ C exp(-c n)` for `C ≥ 0`. -/
theorem rounds_mul_le (δ : ℚ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    (rounds δ n : ℝ) * (C * Real.exp (-(n : ℝ) / 1000000)) ≤ C * Real.exp (-(rate * n)) := by
  have h1 := rounds_le_exp δ n
  have h2 : Real.exp (rate * n) * Real.exp (-(n : ℝ) / 1000000) ≤ Real.exp (-(rate * n)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := rate_le
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  calc (rounds δ n : ℝ) * (C * Real.exp (-(n : ℝ) / 1000000))
      ≤ Real.exp (rate * n) * (C * Real.exp (-(n : ℝ) / 1000000)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = C * (Real.exp (rate * n) * Real.exp (-(n : ℝ) / 1000000)) := by ring
    _ ≤ C * Real.exp (-(rate * n)) := mul_le_mul_of_nonneg_left h2 hC

/-- `1/(M+1) ≤ √(2δ) + 2 exp(-c n)`. -/
theorem inv_rounds_le {δ : ℚ} (hδ : 0 < δ) (n : ℕ) :
    1 / ((rounds δ n : ℝ) + 1) ≤ √(2 * (δ : ℝ)) + 2 * Real.exp (-(rate * n)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hpos : (0 : ℝ) < (rounds δ n : ℝ) + 1 := by positivity
  rcases le_total (Nat.sqrt ⌊1 / (2 * δ)⌋₊) (2 ^ (n / K0)) with h | h
  · -- `M = ⌊√⌊1/(2δ)⌋⌋`: `(M + 1)² > 1/(2δ)`
    have hM : rounds δ n = Nat.sqrt ⌊1 / (2 * δ)⌋₊ := min_eq_left h
    have h1 : ⌊1 / (2 * δ)⌋₊ < (Nat.sqrt ⌊1 / (2 * δ)⌋₊ + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have h2 : 1 / (2 * δ) < (⌊1 / (2 * δ)⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one _
    have h3 : (1 / (2 * δ) : ℚ) < ((Nat.sqrt ⌊1 / (2 * δ)⌋₊ + 1) ^ 2 : ℕ) := by
      have : ((⌊1 / (2 * δ)⌋₊ : ℕ) : ℚ) + 1 ≤ ((Nat.sqrt ⌊1 / (2 * δ)⌋₊ + 1) ^ 2 : ℕ) := by
        exact_mod_cast h1
      linarith
    have h4 : 1 / (2 * (δ : ℝ)) < ((rounds δ n : ℝ) + 1) ^ 2 := by
      rw [hM]
      have : ((1 / (2 * δ) : ℚ) : ℝ) < (((Nat.sqrt ⌊1 / (2 * δ)⌋₊ + 1) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast h3
      push_cast at this
      exact this
    have h5 : (1 / ((rounds δ n : ℝ) + 1)) ^ 2 < 2 * δ := by
      rw [div_pow, one_pow, div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at h4
      nlinarith
    have h6 : 1 / ((rounds δ n : ℝ) + 1) ≤ √(2 * (δ : ℝ)) := by
      calc 1 / ((rounds δ n : ℝ) + 1) = √((1 / ((rounds δ n : ℝ) + 1)) ^ 2) :=
            (Real.sqrt_sq (by positivity)).symm
        _ ≤ √(2 * (δ : ℝ)) := Real.sqrt_le_sqrt h5.le
    have : 0 ≤ 2 * Real.exp (-(rate * n)) := by positivity
    linarith
  · -- `M = 2^(n/K₀)`: `exp(c n) ≤ 2 M`
    have hM : rounds δ n = 2 ^ (n / K0) := min_eq_right h
    have hK : (0 : ℝ) < K0 := by unfold K0; positivity
    have h1 : (n : ℝ) / K0 ≤ ((n / K0 : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hK]
      have hK0 : 0 < K0 := by unfold K0; positivity
      have h' : n ≤ (n / K0 + 1) * K0 := by
        have := Nat.div_add_mod n K0
        have := Nat.mod_lt n hK0
        nlinarith
      exact_mod_cast h'
    have h2 : Real.exp (rate * n) ≤ 2 * (rounds δ n : ℝ) := by
      rw [hM]
      calc Real.exp (rate * n) = Real.exp (Real.log 2 * ((n : ℝ) / K0)) := by
            unfold rate; ring_nf
        _ ≤ Real.exp (Real.log 2 * (((n / K0 : ℕ) : ℝ) + 1)) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h1 (Real.log_nonneg (by norm_num)))
        _ = 2 * ((2 ^ (n / K0) : ℕ) : ℝ) := by
            rw [mul_add, Real.exp_add, mul_one, Real.exp_log (by norm_num), mul_comm,
              Real.exp_mul, Real.exp_log (by norm_num), Real.rpow_natCast]
            push_cast; ring
    have hexp : 0 < Real.exp (rate * n) := Real.exp_pos _
    have h3 : 1 / ((rounds δ n : ℝ) + 1) ≤ 2 * Real.exp (-(rate * n)) := by
      calc 1 / ((rounds δ n : ℝ) + 1) ≤ 2 / Real.exp (rate * n) := by
            rw [div_le_div_iff₀ hpos hexp]; nlinarith
        _ = 2 * Real.exp (-(rate * n)) := by rw [Real.exp_neg]; ring
    have : 0 ≤ √(2 * (δ : ℝ)) := Real.sqrt_nonneg _
    linarith

/-- There is a sign pattern: `spikeSigns d k` is nonempty for `k ≤ d`. -/
theorem card_spikeSigns_pos {d k : ℕ} (hkd : k ≤ d) : 0 < (spikeSigns d k).card := by
  refine Finset.card_pos.2 ⟨fun i ↦ if (i : ℕ) < k then 1 else 0, ?_⟩
  simp only [spikeSigns, Finset.mem_filter, Finset.mem_univ, true_and]
  have : (Finset.univ.filter fun i : Fin d ↦ (if (i : ℕ) < k then (1 : SignType) else 0) ≠ 0) =
      Finset.univ.filter fun i : Fin d ↦ (i : ℕ) < k := by
    ext i; by_cases h : (i : ℕ) < k <;> simp [h]
  rw [this]
  have : (Finset.univ.filter fun i : Fin d ↦ (i : ℕ) < k) =
      Finset.univ.map (Fin.castLEEmb hkd) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩; simp
  rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem spcaOutputProb_nonneg {m : ℕ} (B : SPCAInput × List Bool → Bool) (T : SPCAInput → ℕ)
    (δ : ℚ) (p k q n : ℕ) (S : Matrix (Fin m) (Fin m) ℝ) (b : Bool) :
    0 ≤ spcaOutputProb B T δ p k q n S b :=
  ENNReal.toReal_nonneg

/-- **[BDT24, Theorem 3.1]**, the statement of `BDT24/Challenge.lean`. -/
theorem negSPCA_of_sparse_regression_main :
    ∃ c C : ℝ, 0 < c ∧
      ∀ (A : SLRInput × List Bool → Estimate) (e : ℕ),
        RunsInTime encSLRInput encEstimate A (slrTime e) →
      ∃ (B : SPCAInput × List Bool → Bool) (e' E : ℕ),
        RunsInTime encSPCAInput Encoding.encBool B (spcaTime e') ∧
        ∀ δ : ℚ, 0 < δ → ∀ n d k p : ℕ, k ≤ d →
          SolvesSLR A (slrTime e) n (2 * d) k p δ →
          ∀ q : ℕ, (n + d + p + 2) ^ E ≤ q →
            SolvesNegSPCA B (spcaTime e') δ p q n d k (√(2 * δ) + C * Real.exp (-c * n)) := by
  obtain ⟨C₁, hC₁⟩ := prob_not_goodP
  obtain ⟨C₂, hC₂⟩ := prob_not_samp
  set C : ℝ := 3 + 2 * |C₁| + |C₂| with hCdef
  refine ⟨rate, C, rate_pos, fun A e hA ↦ ?_⟩
  obtain ⟨e', hrun, hT⟩ := algB_runsInTime hA
  obtain ⟨E₀, hE₀⟩ := planted_calls hA
  refine ⟨algB A e, e', E₀ + 2, hrun, fun δ hδ n d k p hkd hSLR q hq ↦ ?_⟩
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hexp : Real.exp (-rate * n) = Real.exp (-(rate * n)) := by ring_nf
  rw [hexp]
  set ε : ℝ := √(2 * (δ : ℝ)) + C * Real.exp (-(rate * n)) with hε
  have hC1 : 0 ≤ |C₁| := abs_nonneg _
  have hC2 : 0 ≤ |C₂| := abs_nonneg _
  have hepos : 0 < Real.exp (-(rate * n)) := Real.exp_pos _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- no samples: the error is at least `C ≥ 1`
    have h1 : 1 ≤ ε := by
      have : Real.exp (-(rate * ((0 : ℕ) : ℝ))) = 1 := by simp
      rw [hε, this]
      have := Real.sqrt_nonneg (2 * (δ : ℝ))
      nlinarith
    refine ⟨(sub_nonpos.2 h1).trans (spcaOutputProb_nonneg _ _ _ _ _ _ _ _ _), ?_⟩
    refine (sub_nonpos.2 h1).trans (div_nonneg (Finset.sum_nonneg fun v _ ↦ ?_) (by positivity))
    exact spcaOutputProb_nonneg _ _ _ _ _ _ _ _ _
  have hbase : 2 ≤ n + d + p + 2 := by omega
  have hqE : (n + d + p + 2) ^ E₀ ≤ q :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hq
  have hq2 : p + n + 2 ≤ q := by
    calc p + n + 2 ≤ n + d + p + 2 := by omega
      _ ≤ (n + d + p + 2) ^ (E₀ + 2) := Nat.le_self_pow (by omega) _
      _ ≤ q := hq
  set M := rounds δ n with hMdef
  refine ⟨?_, ?_⟩
  · -- null input
    have hnull := null_true (A := A) (e := e) (spcaTime e') hT δ n (d + 1) p k q hn
    have hsum := spcaOutputProb_false_add_true (algB A e) (spcaTime e') δ p k q n
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    have hs := hC₂ n (d + 1) q
    have hsC : (M : ℝ) * (gRows n (d + 1)).real {g | ¬ Samp q n (d + 1) g} ≤
        |C₂| * Real.exp (-(rate * n)) := by
      calc (M : ℝ) * (gRows n (d + 1)).real {g | ¬ Samp q n (d + 1) g}
          ≤ (M : ℝ) * (|C₂| * Real.exp (-(n : ℝ) / 1000000)) :=
            mul_le_mul_of_nonneg_left (hs.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
              (Real.exp_pos _).le)) (Nat.cast_nonneg _)
        _ ≤ |C₂| * Real.exp (-(rate * n)) := rounds_mul_le δ n hC2
    have hinv := inv_rounds_le hδ n
    have : spcaOutputProb (algB A e) (spcaTime e') δ p k q n
        (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) true ≤ ε := by
      calc _ ≤ _ := hnull
        _ ≤ √(2 * (δ : ℝ)) + 2 * Real.exp (-(rate * n)) + |C₂| * Real.exp (-(rate * n)) :=
            add_le_add hinv hsC
        _ ≤ ε := by rw [hε, hCdef]; nlinarith
    linarith
  · -- planted input
    have hv : ∀ v ∈ spikeSigns d k,
        1 - ε ≤ spcaOutputProb (algB A e) (spcaTime e') δ p k q n
          (spikedCov (theta k) (spikeVector k v)) true := by
      intro v hvs
      have hfalse := output_false_le (A := A) (e := e) (spcaTime e') hT δ p k q n
        (spikedCov (theta k) (spikeVector k v))
      have hcall := hE₀ δ n d k p q v hn hkd hvs hSLR hqE
      have hbad := hC₁ n d k p q v hvs hq2
      have hsum := spcaOutputProb_false_add_true (algB A e) (spcaTime e') δ p k q n
        (spikedCov (theta k) (spikeVector k v))
      have hM2 := two_mul_rounds_le hδ n
      set bad := ((Measure.pi fun _ : Fin n ↦ plantedLaw d k v).prod (gRows n (d + 1))).real
        {zg | ¬ GoodP n d p q v zg}
      have hbad' : (M : ℝ) * bad ≤ |C₁| * Real.exp (-(rate * n)) := by
        calc (M : ℝ) * bad ≤ (M : ℝ) * (|C₁| * Real.exp (-(n : ℝ) / 1000000)) :=
              mul_le_mul_of_nonneg_left (hbad.trans (mul_le_mul_of_nonneg_right
                (le_abs_self _) (Real.exp_pos _).le)) (Nat.cast_nonneg _)
          _ ≤ |C₁| * Real.exp (-(rate * n)) := rounds_mul_le δ n hC1
      have hF : spcaOutputProb (algB A e) (spcaTime e') δ p k q n
          (spikedCov (theta k) (spikeVector k v)) false ≤ ε := by
        calc _ ≤ _ := hfalse
          _ ≤ (M : ℝ) * (2 * (δ + bad)) :=
              mul_le_mul_of_nonneg_left hcall (Nat.cast_nonneg _)
          _ = 2 * (M : ℝ) * δ + 2 * ((M : ℝ) * bad) := by ring
          _ ≤ √(2 * (δ : ℝ)) + 2 * (|C₁| * Real.exp (-(rate * n))) := by linarith
          _ ≤ ε := by rw [hε, hCdef]; nlinarith
      linarith
    have hcard := card_spikeSigns_pos hkd
    rw [le_div_iff₀ (by exact_mod_cast hcard)]
    calc (1 - ε) * ((spikeSigns d k).card : ℝ) = ∑ _v ∈ spikeSigns d k, (1 - ε) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum hv

end BDT24.Main
