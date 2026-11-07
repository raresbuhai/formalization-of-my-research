module

public import BBKS24.Statistic
public import BBKS24.SparseNorm

/-!
# The random cut is good

The probabilistic part of [BBKS24, §3–4]: with high probability the random edges between the
planted set `S` and the other vertices satisfy the three hypotheses of recovery
(`BBKS24.exists_refine_eq`), for the edge probability `1/2 ≤ q < 1`
(`BBKS24.GoodCut`, `BBKS24.prob_goodCut`).

* **All good** [BBKS24, Lemmas 3.2, 4.2]: for every triple `α ⊆ S` and `j ∈ S`, the correlation
  over the cut `∑_{i ∉ S} H_α(i) χ(j ~ i)` is at most `t₁` (`BBKS24.prob_not_allGood`). For fixed
  `α` and `j` the terms are independent across `i`, bounded by `p₋⁴`, and have mean zero (the
  sets `α` and `{j}` differ), so Hoeffding and a union bound over the `C(k, 3) k` pairs apply.
  The paper uses Bernstein; Hoeffding loses a factor `p₋⁴` in `t₁`, which the paper's bound on `k`
  absorbs.
* **Degrees** [BBKS24, Lemma 4.3 and the proof of Theorem 4.1]: for every `j ∉ S`,
  `|∑_{w ∈ S} χ(j ~ w)| ≤ t₂` (`BBKS24.prob_not_degrees`), by Hoeffding within the block of `j`.
  This bounds both the part of the statistic inside `S` and the degree of `j` into `S`.
* **Few bad** [BBKS24, Lemmas 3.3–3.5, 4.4]: no vector with entries at most `p₋` correlates with
  `s` columns `H_α` (`BBKS24.prob_not_fewBad`), by `BBKS24.SparseNorm.few_large_correlations` for
  the triple characters `H_α = ∏_{a ∈ α} χ(a ~ ·)`, which are orthonormal under the law of a block
  and bounded by `p₋³`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval Finset Real RandomGraph SimpleGraph

namespace BBKS24

variable {n : ℕ}

/-- **The good cut**: the three hypotheses of recovery, for the cut `x` between `S` and the rest. -/
def GoodCut (q : ℝ) (S : Finset (Fin n)) (t₁ t₂ τ : ℝ) (s : ℕ)
    (x : {v // v ∉ S} → {w // w ∈ S} → Prop) : Prop :=
  (∀ α ∈ S.powersetCard 3, ∀ j (hj : j ∈ S), |inCorr q S α ⟨j, hj⟩ x| ≤ t₁) ∧
  (∀ j (hj : j ∉ S), |∑ w, chi q (x ⟨j, hj⟩ w)| ≤ t₂) ∧
  (∀ u : {v // v ∉ S} → ℝ, (∀ i, |u i| ≤ pminus q) →
    ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s)

/-- **Recovery on a good cut** (`BBKS24.exists_refine_eq`). -/
theorem GoodCut.exists_refine_eq {q : ℝ} {G R : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    {t₁ t₂ τ : ℝ} {s : ℕ} (h : GoodCut q S t₁ t₂ τ s (cut S R)) (hP : Planted G R S)
    (hq : 1 / 2 ≤ q) (hq1 : q < 1) {k : ℕ} (hk : S.card = k) (hk3 : 3 ≤ k)
    (h1 : t₁ ≤ k * pplus q ^ 4 / 2) (h2 : τ ≤ k * pplus q ^ 4 / 2 - pplus q ^ 3 * t₂)
    (h3 : q * k + √(q * (1 - q)) * t₂ + (n - k) * s / k.choose 3 < k - 1) :
    ∃ α ∈ S.powersetCard 3, refine G k (selected q G k α) = S :=
  BBKS24.exists_refine_eq hP hq hq1 hk hk3
    (fun α hα h3 j hj ↦ h.1 α (mem_powersetCard.2 ⟨hα, h3⟩) j hj) h.2.1 h.2.2 h1 h2
    (by rwa [Fintype.card_fin])

variable (S : Finset (Fin n)) {q : I}

/-! ### Two-sided Hoeffding -/

/-- `t < |a|` implies `t ≤ a` or `t ≤ -a`. -/
theorem lt_abs_imp {t a : ℝ} (h : t < |a|) : t ≤ a ∨ t ≤ -a := by
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha] at h
    exact Or.inl h.le
  · rw [abs_of_neg ha] at h
    exact Or.inr h.le

/-- **Two-sided Hoeffding** for independent samples of a centred variable bounded by `B`. -/
theorem hoeffding_abs {X κ : Type*} [MeasurableSpace X] [DiscreteMeasurableSpace X] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] {Y : X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, |Y x| ≤ B) (hc : ∫ x, Y x ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.infinitePi fun _ : κ ↦ μ).real {g | t < |∑ j, Y (g j)|} ≤
      2 * exp (-t ^ 2 / (2 * (Fintype.card κ * B ^ 2))) := by
  set P := Measure.infinitePi fun _ : κ ↦ μ
  have h1 := SparseNorm.hoeffding_pi (κ := κ) μ (Y := Y) Measurable.of_discrete hB hb hc ht
  have h2 := SparseNorm.hoeffding_pi (κ := κ) μ (Y := fun x ↦ -Y x) Measurable.of_discrete hB
    (fun x ↦ by rw [abs_neg]; exact hb x) (by rw [integral_neg, hc, neg_zero]) ht
  have hsub : {g : κ → X | t < |∑ j, Y (g j)|} ⊆
      {g | t ≤ ∑ j, Y (g j)} ∪ {g | t ≤ ∑ j, (fun x ↦ -Y x) (g j)} := by
    intro g hg
    rcases lt_abs_imp hg with h | h
    · exact Or.inl h
    · right
      simp only [Set.mem_ofPred_eq, sum_neg_distrib]
      exact h
  calc P.real {g | t < |∑ j, Y (g j)|}
      ≤ P.real ({g | t ≤ ∑ j, Y (g j)} ∪ {g | t ≤ ∑ j, (fun x ↦ -Y x) (g j)}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **Two-sided Hoeffding** with any `M ≥ |κ|` in place of `|κ|` (with no samples the
sum is `0`). -/
theorem hoeffding_abs_le {X κ : Type*} [MeasurableSpace X] [DiscreteMeasurableSpace X] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] {Y : X → ℝ} {B : ℝ} (hB : 0 < B)
    (hb : ∀ x, |Y x| ≤ B) (hc : ∫ x, Y x ∂μ = 0) {t : ℝ} (ht : 0 ≤ t) {M : ℝ}
    (hκM : (Fintype.card κ : ℝ) ≤ M) :
    (Measure.infinitePi fun _ : κ ↦ μ).real {g | t < |∑ j, Y (g j)|} ≤
      2 * exp (-t ^ 2 / (2 * (M * B ^ 2))) := by
  rcases Nat.eq_zero_or_pos (Fintype.card κ) with h0 | h0
  · have : IsEmpty κ := Fintype.card_eq_zero_iff.1 h0
    have hempty : {g : κ → X | t < |∑ j, Y (g j)|} = ∅ := by
      ext g
      simp [not_lt.2 ht]
    rw [hempty, measureReal_empty]
    positivity
  · refine (hoeffding_abs μ hB.le hb hc ht).trans ?_
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num)
    rw [neg_div, neg_div, neg_le_neg_iff]
    have hκ : (0 : ℝ) < Fintype.card κ := by exact_mod_cast h0
    exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by gcongr)

/-! ### All good -/

/-- **All good** [BBKS24, Lemmas 3.2, 4.2]: the correlations over the cut exceed `t₁` with
probability at most `2 C(k, 3) k exp(-t₁² / (2 (n - k) p₋⁸))`. -/
theorem prob_not_allGood (hq : 1 / 2 ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    {M : ℝ} (hcard : (Fintype.card {v // v ∉ S} : ℝ) ≤ M) :
    (cutLaw (Fin n) S q).real
        {x | ¬ ∀ α ∈ S.powersetCard 3, ∀ j (hj : j ∈ S), |inCorr q S α ⟨j, hj⟩ x| ≤ t₁} ≤
      (S.powersetCard 3).card * S.card *
        (2 * exp (-t₁ ^ 2 / (2 * (M * (pminus q ^ 4) ^ 2)))) := by
  have hq0 : 0 < (q : ℝ) := by linarith
  set e := 2 * exp (-t₁ ^ 2 / (2 * (M * (pminus q ^ 4) ^ 2)))
  have hsub : {x | ¬ ∀ α ∈ S.powersetCard 3, ∀ j (hj : j ∈ S), |inCorr q S α ⟨j, hj⟩ x| ≤ t₁} ⊆
      ⋃ α ∈ S.powersetCard 3, ⋃ j : {w // w ∈ S}, {x | t₁ < |inCorr q S α j x|} := by
    intro x hx
    simp only [not_forall, not_le, Set.mem_ofPred_eq] at hx
    obtain ⟨α, hα, j, hj, h⟩ := hx
    simp only [Set.mem_iUnion]
    exact ⟨α, hα, ⟨j, hj⟩, h⟩
  have hpair : ∀ α ∈ S.powersetCard 3, ∀ j : {w // w ∈ S},
      (cutLaw (Fin n) S q).real {x | t₁ < |inCorr q S α j x|} ≤ e := by
    intro α hα j
    obtain ⟨hαS, hα3⟩ := mem_powersetCard.1 hα
    have hB := one_le_pminus hq hq1
    have hb : ∀ y, |blockChar S q α y * chi q (y j)| ≤ pminus q ^ 4 := by
      intro y
      rw [abs_mul, pow_succ, ← hα3]
      exact mul_le_mul (abs_blockChar_le_pow S (abs_chi_le hq hq1) hαS y) (abs_chi_le hq hq1 _)
        (abs_nonneg _) (by positivity)
    have hc : ∫ y, blockChar S q α y * chi q (y j) ∂blockLaw (Fin n) S q = 0 := by
      have hj := j.2
      rw [← integral_blockChar_mul_of_ne S hq0 hq1 hαS (singleton_subset_iff.2 hj)
        (B := {(j : Fin n)}) (fun h ↦ by simp [h] at hα3)]
      congr 1
      ext y
      rw [blockChar_singleton S q hj]
    rw [cutLaw_eq]
    exact hoeffding_abs_le (κ := {v // v ∉ S}) (blockLaw (Fin n) S q)
      (pow_pos (pminus_pos hq0 hq1) 4) hb hc ht₁ hcard
  calc (cutLaw (Fin n) S q).real
        {x | ¬ ∀ α ∈ S.powersetCard 3, ∀ j (hj : j ∈ S), |inCorr q S α ⟨j, hj⟩ x| ≤ t₁}
      ≤ (cutLaw (Fin n) S q).real
          (⋃ α ∈ S.powersetCard 3, ⋃ j : {w // w ∈ S}, {x | t₁ < |inCorr q S α j x|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ α ∈ S.powersetCard 3,
          (cutLaw (Fin n) S q).real (⋃ j : {w // w ∈ S}, {x | t₁ < |inCorr q S α j x|}) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _α ∈ S.powersetCard 3, ∑ _j : {w // w ∈ S}, e :=
        sum_le_sum fun α hα ↦ (measureReal_iUnion_fintype_le _).trans
          (sum_le_sum fun j _ ↦ hpair α hα j)
    _ = _ := by
        rw [sum_const, sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, nsmul_eq_mul]
        ring

/-! ### Degrees -/

/-- **Degrees**: some `j ∉ S` has `|∑_{w ∈ S} χ(j ~ w)| > t₂` with probability at most
`2 (n - k) exp(-t₂² / (2 k p₋²))`. -/
theorem prob_not_degrees (hq : 1 / 2 ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) {t₂ : ℝ} (ht₂ : 0 ≤ t₂) :
    (cutLaw (Fin n) S q).real {x | ¬ ∀ j (hj : j ∉ S), |∑ w, chi q (x ⟨j, hj⟩ w)| ≤ t₂} ≤
      Fintype.card {v // v ∉ S} * (2 * exp (-t₂ ^ 2 / (2 * (S.card * pminus q ^ 2)))) := by
  have hq0 : 0 < (q : ℝ) := by linarith
  set e := 2 * exp (-t₂ ^ 2 / (2 * (S.card * pminus q ^ 2)))
  have hsub : {x : {v // v ∉ S} → {w // w ∈ S} → Prop |
      ¬ ∀ j (hj : j ∉ S), |∑ w, chi q (x ⟨j, hj⟩ w)| ≤ t₂} ⊆
      ⋃ j : {v // v ∉ S}, (fun x ↦ x j) ⁻¹' {y | t₂ < |∑ w, chi q (y w)|} := by
    intro x hx
    simp only [not_forall, not_le, Set.mem_ofPred_eq] at hx
    obtain ⟨j, hj, h⟩ := hx
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq]
    exact ⟨⟨j, hj⟩, h⟩
  have hone : ∀ j : {v // v ∉ S}, (cutLaw (Fin n) S q).real
      ((fun x ↦ x j) ⁻¹' {y | t₂ < |∑ w, chi q (y w)|}) ≤ e := by
    intro j
    have hmp := measurePreserving_eval_infinitePi (fun _ : {v // v ∉ S} ↦ blockLaw (Fin n) S q) j
    rw [cutLaw_eq, measureReal_def,
      hmp.measure_preimage MeasurableSet.of_discrete.nullMeasurableSet, ← measureReal_def, blockLaw]
    have := hoeffding_abs (κ := {w // w ∈ S}) (Ber(True, False, q)) (Y := chi q)
      (pminus_pos hq0 hq1).le (abs_chi_le hq hq1) (integral_chi hq0 hq1) ht₂
    rwa [Fintype.card_coe] at this
  calc (cutLaw (Fin n) S q).real {x | ¬ ∀ j (hj : j ∉ S), |∑ w, chi q (x ⟨j, hj⟩ w)| ≤ t₂}
      ≤ (cutLaw (Fin n) S q).real
          (⋃ j : {v // v ∉ S}, (fun x ↦ x j) ⁻¹' {y | t₂ < |∑ w, chi q (y w)|}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ _j : {v // v ∉ S}, e := (measureReal_iUnion_fintype_le _).trans (sum_le_sum
        fun j _ ↦ hone j)
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

/-! ### Few bad -/

/-- The triple characters are orthonormal under the law of a block. -/
theorem integral_tripleChar (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (α β : {α // α ∈ S.powersetCard 3}) :
    ∫ y, blockChar S q α.1 y * blockChar S q β.1 y ∂blockLaw (Fin n) S q =
      if α = β then 1 else 0 := by
  split_ifs with h
  · rw [h]
    exact integral_blockChar_mul_self S hq0 hq1 _
  · exact integral_blockChar_mul_of_ne S hq0 hq1 (mem_powersetCard.1 α.2).1
      (mem_powersetCard.1 β.2).1 fun h' ↦ h (Subtype.ext h')

/-- Filtering the triples of `S` as a subtype or as a finset. -/
theorem card_filter_subtype (T : Finset (Finset (Fin n))) [Fintype {α // α ∈ T}]
    (P : Finset (Fin n) → Prop) [DecidablePred P] :
    (univ.filter fun α : {α // α ∈ T} ↦ P α.1).card = (T.filter P).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext β
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
  exact ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ⟨a.2, ha⟩, fun ⟨hβ, h⟩ ↦ ⟨⟨β, hβ⟩, h, rfl⟩⟩

/-- **Few bad** [BBKS24, Lemmas 3.3–3.5, 4.4], from the sparse norm bound. -/
theorem prob_not_fewBad : ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (S : Finset (Fin n)) {q : I},
    1 / 2 ≤ (q : ℝ) → (q : ℝ) < 1 → ∀ {δ τ : ℝ} {s : ℕ}, 0 < δ → δ ≤ 1 →
    pminus q ^ 6 ≤ (S.card.choose 3 : ℝ) + 2 →
    C * pminus q ^ 6 * s * Real.log (S.card.choose 3 + 2) ^ 4 * Real.log (2 / δ) ≤
      Fintype.card {v // v ∉ S} →
    0 < τ → 2 * Fintype.card {v // v ∉ S} * pminus q ^ 2 * Fintype.card {v // v ∉ S} <
      s * τ ^ 2 →
    (cutLaw (Fin n) S q).real {x | ¬ ∀ u : {v // v ∉ S} → ℝ, (∀ i, |u i| ≤ pminus q) →
      ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s} ≤ δ := by
  classical
  obtain ⟨C, hC, h⟩ := SparseNorm.few_large_correlations
  refine ⟨C, hC, fun {n} S {q} hq hq1 {δ τ s} hδ hδ1 hK hm hτ hs ↦ ?_⟩
  have hq0 : 0 < (q : ℝ) := by linarith
  set ι := {α // α ∈ S.powersetCard 3}
  have hι : Fintype.card ι = S.card.choose 3 := by
    rw [Fintype.card_coe, card_powersetCard]
  have hbound : ∀ (α : ι) y, |blockChar S q α.1 y| ≤ pminus q ^ 3 := fun α y ↦ by
    have := abs_blockChar_le_pow S (abs_chi_le hq hq1) (mem_powersetCard.1 α.2).1 y
    rwa [(mem_powersetCard.1 α.2).2] at this
  have hgood := h (blockLaw (Fin n) S q) (fun (α : ι) y ↦ blockChar S q α.1 y) (pminus q ^ 3) δ
    (pminus q) τ s (integral_tripleChar S hq0 hq1) hbound
    (by rw [hι, ← pow_mul]; exact hK) hδ hδ1
    (by rw [hι, ← pow_mul]; exact hm) hτ hs
  rw [← cutLaw_eq] at hgood
  have hcardeq : ∀ (x : {v // v ∉ S} → {w // w ∈ S} → Prop) (u : {v // v ∉ S} → ℝ),
      (univ.filter fun α : ι ↦ τ ≤ ∑ i, blockChar S q α.1 (x i) * u i).card =
        ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card :=
    fun x u ↦ by
      convert card_filter_subtype (S.powersetCard 3)
        (fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i) using 2
  have hcompl : {x : {v // v ∉ S} → {w // w ∈ S} → Prop | ¬ ∀ u : {v // v ∉ S} → ℝ,
      (∀ i, |u i| ≤ pminus q) →
      ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s} =
      {x | ∀ u : {v // v ∉ S} → ℝ, (∀ i, |u i| ≤ pminus q) →
        (univ.filter fun α : ι ↦ τ ≤ ∑ i, blockChar S q α.1 (x i) * u i).card < s}ᶜ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hcardeq]
  rw [hcompl, probReal_compl_eq_one_sub MeasurableSet.of_discrete]
  linarith

/-- **Few bad, with few outside vertices**: if `|R| p₋⁴ < τ`, no correlation reaches `τ`. -/
theorem fewBad_of_small (hq : 1 / 2 ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) {τ : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hτ : Fintype.card {v // v ∉ S} * pminus q ^ 4 < τ)
    (x : {v // v ∉ S} → {w // w ∈ S} → Prop) (u : {v // v ∉ S} → ℝ)
    (hu : ∀ i, |u i| ≤ pminus q) :
    ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s := by
  have hB := pminus_pos (q := (q : ℝ)) (by linarith) hq1
  have hempty : (S.powersetCard 3).filter (fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i) = ∅ := by
    refine filter_eq_empty_iff.2 fun α hα ↦ not_le.2 ?_
    obtain ⟨hαS, hα3⟩ := mem_powersetCard.1 hα
    calc ∑ i, blockChar S q α (x i) * u i ≤ ∑ _i : {v // v ∉ S}, pminus q ^ 4 := by
          refine sum_le_sum fun i _ ↦ (le_abs_self _).trans ?_
          rw [abs_mul, pow_succ, ← hα3]
          exact mul_le_mul (abs_blockChar_le_pow S (abs_chi_le hq hq1) hαS (x i)) (hu i)
            (abs_nonneg _) (by positivity)
      _ = Fintype.card {v // v ∉ S} * pminus q ^ 4 := by rw [sum_const, card_univ, nsmul_eq_mul]
      _ < τ := hτ
  rw [hempty, card_empty]
  exact hs

/-! ### The good cut -/

/-- **The cut is good** with probability at least `1` minus the three failure probabilities,
under `G(n, q)`; the third, `δ`, is given (`BBKS24.prob_not_fewBad`, `BBKS24.fewBad_of_small`). -/
theorem prob_goodCut (hq : 1 / 2 ≤ (q : ℝ)) (hq1 : (q : ℝ) < 1) {t₁ t₂ δ τ : ℝ} {s : ℕ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) {M : ℝ}
    (hcard : (Fintype.card {v // v ∉ S} : ℝ) ≤ M)
    (h3 : (cutLaw (Fin n) S q).real {x | ¬ ∀ u : {v // v ∉ S} → ℝ, (∀ i, |u i| ≤ pminus q) →
      ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s} ≤ δ) :
    1 - ((S.powersetCard 3).card * S.card * (2 * exp (-t₁ ^ 2 / (2 * (M * (pminus q ^ 4) ^ 2)))) +
      Fintype.card {v // v ∉ S} * (2 * exp (-t₂ ^ 2 / (2 * (S.card * pminus q ^ 2)))) + δ) ≤
    (G(Fin n, q)).real {R | GoodCut q S t₁ t₂ τ s (cut S R)} := by
  set F : Set ({v // v ∉ S} → {w // w ∈ S} → Prop) := {x | GoodCut q S t₁ t₂ τ s x}
  have hG : (G(Fin n, q)).real {R | GoodCut q S t₁ t₂ τ s (cut S R)} =
      (cutLaw (Fin n) S q).real F := by
    rw [measureReal_def, measureReal_def, ← binomialRandom_cut_preimage S q
      MeasurableSet.of_discrete]
    rfl
  rw [hG]
  set A := {x : {v // v ∉ S} → {w // w ∈ S} → Prop | ¬ ∀ α ∈ S.powersetCard 3, ∀ j (hj : j ∈ S),
    |inCorr q S α ⟨j, hj⟩ x| ≤ t₁} with hA
  set B := {x : {v // v ∉ S} → {w // w ∈ S} → Prop |
    ¬ ∀ j (hj : j ∉ S), |∑ w, chi q (x ⟨j, hj⟩ w)| ≤ t₂} with hB
  set D := {x : {v // v ∉ S} → {w // w ∈ S} → Prop | ¬ ∀ u : {v // v ∉ S} → ℝ,
    (∀ i, |u i| ≤ pminus q) →
      ((S.powersetCard 3).filter fun α ↦ τ ≤ ∑ i, blockChar S q α (x i) * u i).card < s} with hD
  have hFc : Fᶜ ⊆ A ∪ B ∪ D := by
    intro x hx
    simp only [F, GoodCut, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or] at hx
    simp only [hA, hB, hD, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hc := probReal_compl_eq_one_sub (μ := cutLaw (Fin n) S q) (s := F)
    MeasurableSet.of_discrete
  have u0 := measureReal_mono (μ := cutLaw (Fin n) S q) hFc (measure_ne_top _ _)
  have u1 := measureReal_union_le (μ := cutLaw (Fin n) S q) (A ∪ B) D
  have u2 := measureReal_union_le (μ := cutLaw (Fin n) S q) A B
  have e1 := prob_not_allGood S hq hq1 ht₁ hcard
  have e2 := prob_not_degrees S hq hq1 ht₂
  linarith

end BBKS24
