module

public import B25.RE.Main
public import B25.Lasso.Basic
public import B25.Lasso.Noise

/-!
# Corollary 1.6

`B25.lasso_of_partiallyRotated_main`: the statement of `B25.lasso_of_partiallyRotated` in
`B25/Challenge.lean`. The proof is the paper's [B25, Appendix B]. Write `T = supp β`, `k = |T|`,
`γ = γ_T(X_S)` and `Δ = b - β` for a Lasso estimate `b`.

* **Existence**: `B25.exists_isLasso` (the radius `‖β‖₁` is nonnegative).
* **Constants.** Theorem 1.5 (`B25.re_of_partiallyRotated_main`) gives `C₁, c₁`. Choose
  `C₂ ≥ C₁` large (see below) and split on whether `C₂ k log d ≤ n γ`.
* **Large `n γ`.** Then also `C₁ k log d ≤ n γ`, so outside the bad event of Theorem 1.5
  (with `S' = T`) `γ_T(X) ≥ 0.9 γ`, and outside the noise event of `B25.noise_max_tail`
  (with `t² = 2 (1 + τ) σ² n log d`) `B25.lasso_fast` gives
  `γ ‖XΔ‖₂² ≤ (10/9) γ_T(X) ‖XΔ‖₂² ≤ (10/9) 32 (1 + τ) σ² k log d`.
* **Small `n γ`.** `B25.lasso_le_noise` and `B25.noise_norm_tail` give
  `γ ‖XΔ‖₂² ≤ 4 γ ‖w‖₂² ≤ 16 σ² n γ < 16 C₂ σ² k log d` outside an event of probability `e^(-n/4)`.
  So `C = max ((320/9)(1 + τ), 16 C₂) + 1` works.
* **Probability.** The bad event lies in the union of: (the bad event of Theorem 1.5 restricted
  to `C₂ k log d ≤ n γ`, and the null set of unnormalized columns) `× univ`; the set of `(ω, w)`
  with `X ω` normalized and `w` in the event of `B25.noise_max_tail` for `X ω`, of probability at
  most `2 d^(-τ)` (it is measurable because `X` is, and its measure is the integral over `ω` of
  the measures of its sections, `Measure.prod_apply`); and `univ ×` the event of
  `B25.noise_norm_tail`. `(P.prod ν) (A ×ˢ univ) = P A` holds for every set (`Measure.prod_prod`).
* **One exponential.** The first set is empty unless `n ≥ C₂ log 2` (for `d ≥ 2` and `k ≥ 1`,
  `γ ≤ 1` by `B25.reConst_cols_le_one`, so `C₂ k log d ≤ n γ` forces `n ≥ C₂ log 2`; for `k = 0`
  both sides vanish; for `d ≤ 1` the bound `2 d^(-τ)` is at least `1` when `d = 1`, and the event is
  empty when `d = 0`). With `a = min c₁ (1/4)` and `C₂ ≥ 2/a`, `e^(-c₁ n) + e^(-n/4) ≤ e^(-a n / 2)`
  when `n ≥ C₂ log 2`, and `e^(-n/4) ≤ e^(-a n/2)` always; so `c' = a/2`.
-/

@[expose] public section

namespace B25

open MeasureTheory ProbabilityTheory Matrix

namespace LS

/-- The deterministic core of Corollary 1.6. For a design `M` and noise `w` with
`‖w‖₂² ≤ 4 σ² n` and `⟨Mⱼ, w⟩² ≤ 2 (1 + τ) σ² n log d` for every column, if
`γ_T(M) ≥ 0.9 γ` whenever `C₂ |T| log d ≤ n γ` (`T = supp β`, `γ = γ_T(M_S)`), then every Lasso
estimate has `γ ‖M(b - β)‖₂² ≤ C σ² |T| log d`. -/
theorem lasso_pointQuokka {n d : ℕ} {M : Matrix (Fin n) (Fin d) ℝ} {S : Finset (Fin d)}
    {β : Fin d → ℝ} {w : Fin n → ℝ} {b : Fin d → ℝ} {σ τ C C₂ : ℝ}
    (hb : IsLasso M (M *ᵥ β + w) (l1 β) b) (hτ : 0 ≤ τ)
    (hCa : 320 / 9 * (1 + τ) ≤ C) (hCb : 16 * C₂ ≤ C) (hw : w ⬝ᵥ w ≤ 4 * σ ^ 2 * n)
    (hcol : ∀ j, (∑ i, M i j * w i) ^ 2 ≤ 2 * (1 + τ) * σ ^ 2 * n * Real.log d)
    (hRE : C₂ * (supp β).card * Real.log d ≤
        n * reConst (cols M S) ((supp β).subtype (· ∈ S)) →
      9 / 10 * reConst (cols M S) ((supp β).subtype (· ∈ S)) ≤ reConst M (supp β)) :
    reConst (cols M S) ((supp β).subtype (· ∈ S)) * ((M *ᵥ (b - β)) ⬝ᵥ (M *ᵥ (b - β))) ≤
      C * σ ^ 2 * (supp β).card * Real.log d := by
  have hγ0 : 0 ≤ reConst (cols M S) ((supp β).subtype (· ∈ S)) := reConst_nonneg _ _
  have hQ0 : 0 ≤ (M *ᵥ (b - β)) ⬝ᵥ (M *ᵥ (b - β)) :=
    Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _
  set γ := reConst (cols M S) ((supp β).subtype (· ∈ S))
  set Q := (M *ᵥ (b - β)) ⬝ᵥ (M *ᵥ (b - β))
  set k : ℝ := ((supp β).card : ℝ)
  set L := Real.log d
  have hL : 0 ≤ L := Real.log_natCast_nonneg d
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hK : 0 ≤ σ ^ 2 * k * L := by positivity
  have hfin : C * σ ^ 2 * k * L = C * (σ ^ 2 * k * L) := by ring
  rw [hfin]
  by_cases h : C₂ * k * L ≤ n * γ
  · have hγT := hRE h
    have hv : 0 ≤ 2 * (1 + τ) * σ ^ 2 * n * L :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (by linarith)) (sq_nonneg σ))
        (Nat.cast_nonneg n)) hL
    have ht : ∀ j, |∑ i, M i j * w i| ≤ √(2 * (1 + τ) * σ ^ 2 * n * L) :=
      fun j ↦ Real.abs_le_sqrt (hcol j)
    have hfast := lasso_fast hb ht
    rw [Real.sq_sqrt hv] at hfast
    have hrate : 16 * k * (2 * (1 + τ) * σ ^ 2 * n * L) / n ≤
        32 * (1 + τ) * (σ ^ 2 * k * L) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hn, Nat.cast_zero, div_zero]; exact mul_nonneg (by linarith) hK
      · have hn' : (n : ℝ) ≠ 0 := by positivity
        exact le_of_eq (by field_simp; ring)
    have h1 : 9 / 10 * γ * Q ≤ reConst M (supp β) * Q := mul_le_mul_of_nonneg_right hγT hQ0
    have h2 : 320 / 9 * (1 + τ) * (σ ^ 2 * k * L) ≤ C * (σ ^ 2 * k * L) :=
      mul_le_mul_of_nonneg_right hCa hK
    linarith
  · push Not at h
    have h1 := lasso_le_noise hb
    have h2 : γ * Q ≤ γ * (16 * σ ^ 2 * n) := mul_le_mul_of_nonneg_left (by linarith) hγ0
    have h3 : σ ^ 2 * (n * γ) ≤ σ ^ 2 * (C₂ * k * L) :=
      mul_le_mul_of_nonneg_left h.le (sq_nonneg σ)
    have h4 : 16 * C₂ * (σ ^ 2 * k * L) ≤ C * (σ ^ 2 * k * L) :=
      mul_le_mul_of_nonneg_right hCb hK
    linarith

/-- Splitting a bad event: a set covered by `(N ∪ B) × univ`, `univ × W` and `E`, with `N` null,
has measure at most `P B + ν W + (P ⊗ ν) E`. -/
theorem prod_cover_leQuokka {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) (ν : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure ν]
    {A E : Set (Ω × α)} {N B : Set Ω} {W : Set α}
    (h : A ⊆ (N ∪ B) ×ˢ Set.univ ∪ Set.univ ×ˢ W ∪ E) (hN : P N = 0) :
    P.prod ν A ≤ P B + ν W + P.prod ν E := by
  calc P.prod ν A ≤ P.prod ν ((N ∪ B) ×ˢ Set.univ ∪ Set.univ ×ˢ W ∪ E) := measure_mono h
    _ ≤ P.prod ν ((N ∪ B) ×ˢ Set.univ) + P.prod ν (Set.univ ×ˢ W) + P.prod ν E :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ P B + ν W + P.prod ν E := by
        rw [Measure.prod_prod, Measure.prod_prod, measure_univ, measure_univ, mul_one, one_mul]
        have hNB : P (N ∪ B) ≤ P B := (measure_union_le N B).trans (by rw [hN, zero_add])
        exact add_le_add (add_le_add hNB le_rfl) le_rfl

/-- The event of `B25.noise_max_tail` for a measurable design, on the event that its columns have
norm `√n`, has probability at most `2 d^(-τ)` under `P ⊗ N(0, σ² Iₙ)`: its sections have. -/
theorem prod_noise_maxQuokka {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {n d : ℕ} {X : Ω → Matrix (Fin n) (Fin d) ℝ} (hX : Measurable X)
    (σ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    P.prod (noiseLaw n σ) {p | HasNormalizedColumns (X p.1) ∧
        ∃ j, 2 * (1 + τ) * σ ^ 2 * n * Real.log d < (∑ i, X p.1 i j * p.2 i) ^ 2} ≤
      ENNReal.ofReal (2 * (d : ℝ) ^ (-τ)) := by
  have : IsProbabilityMeasure (noiseLaw n σ) := by unfold noiseLaw; infer_instance
  have hent : ∀ i j, Measurable fun p : Ω × (Fin n → ℝ) ↦ X p.1 i j := fun i j ↦
    (hX.comp measurable_fst).eval_matrix
  have hmeas : MeasurableSet {p : Ω × (Fin n → ℝ) | HasNormalizedColumns (X p.1) ∧
      ∃ j, 2 * (1 + τ) * σ ^ 2 * n * Real.log d < (∑ i, X p.1 i j * p.2 i) ^ 2} := by
    simp only [HasNormalizedColumns, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
    refine (MeasurableSet.iInter fun j ↦ measurableSet_eq_fun ?_ measurable_const).inter
      (MeasurableSet.iUnion fun j ↦ measurableSet_lt measurable_const ?_)
    · exact Finset.measurable_sum _ fun i _ ↦ (hent i j).pow_const 2
    · exact (Finset.measurable_sum _ fun i _ ↦
        (hent i j).mul ((measurable_pi_apply i).comp measurable_snd)).pow_const 2
  rw [Measure.prod_apply hmeas]
  calc ∫⁻ ω, noiseLaw n σ (Prod.mk ω ⁻¹' _) ∂P
      ≤ ∫⁻ _, ENNReal.ofReal (2 * (d : ℝ) ^ (-τ)) ∂P := by
        refine lintegral_mono fun ω ↦ ?_
        by_cases hω : HasNormalizedColumns (X ω)
        · exact le_trans (measure_mono fun _ hw ↦ hw.2) (noise_max_tail (X ω) hω σ hτ)
        · exact le_trans (measure_mono (t := ∅) fun _ hw ↦ (hω hw.1).elim) (by simp)
    _ = ENNReal.ofReal (2 * (d : ℝ) ^ (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-- Merging the two exponentials: `e^(-c₁ x) + e^(-x/4) ≤ e^(-a x / 2)` for `a ≤ min c₁ (1/4)`
and `x ≥ C₂ log 2 ≥ 2 log 2 / a`. -/
theorem exp_mergeQuokka {a c₁ C₂ x : ℝ} (ha : 0 < a) (hac : a ≤ c₁) (ha4 : a ≤ 1 / 4)
    (hC₂ : 2 / a ≤ C₂) (hx : C₂ * Real.log 2 ≤ x) :
    Real.exp (-(c₁ * x)) + Real.exp (-(x / 4)) ≤ Real.exp (-(a / 2 * x)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hx' : 2 / a * Real.log 2 ≤ x := le_trans (mul_le_mul_of_nonneg_right hC₂ hlog.le) hx
  have hx0 : 0 ≤ x := le_trans (by positivity) hx'
  have hax : Real.log 2 ≤ a / 2 * x :=
    calc Real.log 2 = a / 2 * (2 / a * Real.log 2) := by field_simp
      _ ≤ a / 2 * x := mul_le_mul_of_nonneg_left hx' (by positivity)
  have e1 : Real.exp (-(c₁ * x)) ≤ Real.exp (-(a * x)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hac hx0))
  have e2 : Real.exp (-(x / 4)) ≤ Real.exp (-(a * x)) := Real.exp_le_exp.2 (by nlinarith)
  have e3 : Real.exp (-(a * x)) = Real.exp (-(a / 2 * x)) * Real.exp (-(a / 2 * x)) := by
    rw [← Real.exp_add]; ring_nf
  have e4 : 2 * Real.exp (-(a / 2 * x)) ≤ 1 := by
    have : Real.exp (-(a / 2 * x)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg (Real.log 2), Real.exp_log two_pos] at this
    linarith
  have hpos := Real.exp_pos (-(a / 2 * x))
  nlinarith

end LS

/-- **Corollary 1.6** of [B25]: the statement of `B25.lasso_of_partiallyRotated`. -/
theorem lasso_of_partiallyRotated_main :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 1 ≤ τ → ∃ C c' : ℝ, 0 < C ∧ 0 < c' ∧
      ∀ (n d : ℕ) (S : Finset (Fin d)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : Ω → Matrix (Fin n) (Fin d) ℝ), Measurable X →
        (∀ᵐ ω ∂P, HasNormalizedColumns (X ω)) → PartiallyRotated P X S (1 / 100) c →
        ∀ (σ : ℝ) (β : Fin d → ℝ), supp β ⊆ S →
          (∀ ω w, ∃ b, IsLasso (X ω) (X ω *ᵥ β + w) (l1 β) b) ∧
          (P.prod (noiseLaw n σ))
              {p | ∃ b, IsLasso (X p.1) (X p.1 *ᵥ β + p.2) (l1 β) b ∧
                C * σ ^ 2 * (supp β).card * Real.log d <
                  reConst (cols (X p.1) S) ((supp β).subtype (· ∈ S)) *
                    ((X p.1 *ᵥ (b - β)) ⬝ᵥ (X p.1 *ᵥ (b - β)))} ≤
            ENNReal.ofReal (Real.exp (-(c' * n)) + 2 * (d : ℝ) ^ (-τ)) := by
  intro c hc τ hτ
  obtain ⟨C₁, c₁, hC₁, hc₁, hRE⟩ := re_of_partiallyRotated_main c hc
  obtain ⟨a, ha, hac, ha4⟩ : ∃ a : ℝ, 0 < a ∧ a ≤ c₁ ∧ a ≤ 1 / 4 :=
    ⟨min c₁ (1 / 4), lt_min hc₁ (by norm_num), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨C₂, hC₁₂, hC₂a⟩ : ∃ C₂ : ℝ, C₁ ≤ C₂ ∧ 2 / a ≤ C₂ :=
    ⟨max C₁ (2 / a), le_max_left _ _, le_max_right _ _⟩
  have hC₂ : 0 < C₂ := lt_of_lt_of_le hC₁ hC₁₂
  have hτ0 : 0 ≤ τ := by linarith
  obtain ⟨C, hCa, hCb, hC⟩ : ∃ C : ℝ, 320 / 9 * (1 + τ) ≤ C ∧ 16 * C₂ ≤ C ∧ 0 < C :=
    ⟨max (320 / 9 * (1 + τ)) (16 * C₂) + 1, by linarith [le_max_left (320 / 9 * (1 + τ)) (16 * C₂)],
      by linarith [le_max_right (320 / 9 * (1 + τ)) (16 * C₂)],
      by linarith [le_max_right (320 / 9 * (1 + τ)) (16 * C₂)]⟩
  refine ⟨C, a / 2, hC, by positivity, ?_⟩
  intro n d S Ω _ P _ X hXm hXn hPR σ β hβS
  refine ⟨fun ω w ↦ exists_isLasso _ _ (Finset.sum_nonneg fun j _ ↦ abs_nonneg (β j)), ?_⟩
  have : IsProbabilityMeasure (noiseLaw n σ) := by unfold noiseLaw; infer_instance
  -- `|supp β| = 0`: `γ = 0`, and the bad event is empty.
  rcases Nat.eq_zero_or_pos (supp β).card with hk | hk
  · refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    rintro ⟨ω, w⟩ ⟨b, -, hlt⟩
    have hsub : (supp β).subtype (· ∈ S) = ∅ := by
      rw [Finset.card_eq_zero.1 hk]; exact Finset.subtype_eq_empty.2 fun _ _ h ↦ by simp at h
    rw [hk, hsub, reConst_empty] at hlt
    simp at hlt
  have hTne : (supp β).Nonempty := Finset.card_pos.1 hk
  have hd : 0 < d := hTne.choose.pos
  -- `d = 1`: the bound is at least `1`.
  rcases Nat.lt_or_ge d 2 with hd2 | hd2
  · have hd1 : d = 1 := by omega
    refine le_trans prob_le_one ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hd1, Nat.cast_one, Real.one_rpow]
    linarith [Real.exp_pos (-(a / 2 * n))]
  -- `d ≥ 2`.
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlogd : Real.log 2 ≤ Real.log d := Real.log_le_log two_pos (by exact_mod_cast hd2)
  set B : Set Ω := {ω | HasNormalizedColumns (X ω) ∧
      C₂ * (supp β).card * Real.log d ≤ n * reConst (cols (X ω) S) ((supp β).subtype (· ∈ S)) ∧
      reConst (X ω) (supp β) < 9 / 10 * reConst (cols (X ω) S) ((supp β).subtype (· ∈ S))}
  have hcover : {p : Ω × (Fin n → ℝ) | ∃ b, IsLasso (X p.1) (X p.1 *ᵥ β + p.2) (l1 β) b ∧
        C * σ ^ 2 * (supp β).card * Real.log d <
          reConst (cols (X p.1) S) ((supp β).subtype (· ∈ S)) *
            ((X p.1 *ᵥ (b - β)) ⬝ᵥ (X p.1 *ᵥ (b - β)))} ⊆
      ({ω | ¬ HasNormalizedColumns (X ω)} ∪ B) ×ˢ Set.univ ∪
        Set.univ ×ˢ {w | 4 * σ ^ 2 * n < w ⬝ᵥ w} ∪
        {p | HasNormalizedColumns (X p.1) ∧
          ∃ j, 2 * (1 + τ) * σ ^ 2 * n * Real.log d < (∑ i, X p.1 i j * p.2 i) ^ 2} := by
    rintro ⟨ω, w⟩ ⟨b, hb, hlt⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, not_or] at hcon
    obtain ⟨⟨⟨hN, hB⟩, hW⟩, hE⟩ := hcon
    have hnorm : HasNormalizedColumns (X ω) := not_not.1 hN
    exact absurd (LS.lasso_pointQuokka hb hτ0 hCa hCb (not_lt.1 hW)
      (fun j ↦ not_lt.1 fun h ↦ hE ⟨hnorm, j, h⟩)
      (fun h ↦ not_lt.1 fun h' ↦ hB ⟨hnorm, h, h'⟩)) (not_le.2 hlt)
  have hBsub : B ⊆ {ω | ∃ S' ⊆ S, C₁ * S'.card * Real.log d ≤
      n * reConst (cols (X ω) S) (S'.subtype (· ∈ S)) ∧
        reConst (X ω) S' < 9 / 10 * reConst (cols (X ω) S) (S'.subtype (· ∈ S))} := by
    rintro ω ⟨-, h1, h2⟩
    exact ⟨supp β, hβS, le_trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₁₂ (Nat.cast_nonneg _)) (Real.log_natCast_nonneg d)) h1, h2⟩
  have hBbound : P B + ENNReal.ofReal (Real.exp (-(n / 4 : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-(a / 2 * n))) := by
    by_cases hn : C₂ * Real.log 2 ≤ n
    · calc _ ≤ ENNReal.ofReal (Real.exp (-(c₁ * n))) + ENNReal.ofReal (Real.exp (-(n / 4 : ℝ))) :=
            add_le_add ((measure_mono hBsub).trans (hRE n d S P X hXn hPR)) le_rfl
        _ = ENNReal.ofReal (Real.exp (-(c₁ * n)) + Real.exp (-(n / 4 : ℝ))) :=
            (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal (LS.exp_mergeQuokka ha hac ha4 hC₂a hn)
    · have hB0 : B = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ω hω ↦ hn ?_
        obtain ⟨hnorm, h1, -⟩ := hω
        have hnγ : (n : ℝ) * reConst (cols (X ω) S) ((supp β).subtype (· ∈ S)) ≤ n := by
          rcases Nat.eq_zero_or_pos n with hn0 | hn0
          · simp [hn0]
          · exact mul_le_of_le_one_right (Nat.cast_nonneg _)
              (reConst_cols_le_one hn0 hnorm hβS hTne)
        have hk1 : (1 : ℝ) ≤ (supp β).card := by exact_mod_cast hk
        have hlow : C₂ * Real.log 2 ≤ C₂ * (supp β).card * Real.log d := by
          have := mul_le_mul hk1 hlogd hlog2.le (Nat.cast_nonneg _)
          nlinarith
        linarith
      rw [hB0, measure_empty, zero_add]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have := Nat.cast_nonneg (α := ℝ) n
      nlinarith
  calc _ ≤ _ := LS.prod_cover_leQuokka P (noiseLaw n σ) hcover (ae_iff.1 hXn)
    _ ≤ P B + ENNReal.ofReal (Real.exp (-(n / 4 : ℝ))) + ENNReal.ofReal (2 * (d : ℝ) ^ (-τ)) :=
      add_le_add (add_le_add le_rfl (noise_norm_tail n σ)) (LS.prod_noise_maxQuokka P hXm σ hτ0)
    _ ≤ ENNReal.ofReal (Real.exp (-(a / 2 * n))) + ENNReal.ofReal (2 * (d : ℝ) ^ (-τ)) :=
      add_le_add hBbound le_rfl
    _ = _ := (ENNReal.ofReal_add (Real.exp_pos _).le
      (mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg _) _))).symm

end B25
