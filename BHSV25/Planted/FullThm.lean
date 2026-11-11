module

public import BHSV25.Planted.FullCorrect
public import BHSV25.Planted.FullPolyTime
public import BHSV25.Planted.PartialThm

/-!
# Theorem 7.17

[BHSV25, Theorem 7.17] as stated in `BHSV25/Challenge.lean`
(`BHSV25.Planted.plantedColoring_full`): with `λ₀ = 1 / (16384 k⁶)`,
`d₀ = (5 · 2³¹ k²³)⁴`, and `P = (k (4k + 1))⁴ + k + 2k² + 16/α⁴ + 12288 k⁹/α + 1` for
`α = 1 / (1024 k¹²)`.

* **The probability** (`BHSV25.Planted.plantProb_full`): a coloring fails only if it is not good
  (at most `(k + 2k²) k^n / n` colorings, `BHSV25.Planted.card_not_good_le`), makes more than
  `α n` vertices statistically bad (`BHSV25.Planted.card_many_bad_le`), or leaves a large
  connected set stuck (at most `k^n / n⁵`, `BHSV25.Planted.card_bad_stuck_le`, with the vertex
  expansion of Lemma 7.19 at `β = 4α`); the others succeed (`BHSV25.Planted.isColoring_full`).
* **The running time**: one machine for all parameters (`BHSV25.Planted.fullAlg_polytime`), fixed
  at the parameters of `k` (`BHSV25.exists_runsInTime_graph_fix`), so the degree is universal and
  the factor depends only on `k`.
-/

@[expose] public section

namespace BHSV25

namespace Planted

open Finset

variable {k : ℕ}

/-! ### The output is always a partial coloring -/

theorem isPartialColoring_fullAlg (hk : 0 < k) (G : Graph) (K t : ℕ) :
    G.IsPartialColoring k (fullAlg (planParams k K t) (G.1, adjTable G)) := by
  set L := (clusterList G.1 k (gridS k) (gridK k)
      (((3 + 12 * K) ^ numT k t + 1) ^ k + (2 * gridK k + 1) ^ (k * k))
      (Alg.expNet (planParams k K t).2 (G.1, adjTable G))).flatMap
      fun q ↦ (List.range (G.1 + 1)).map fun d ↦ pipeline G.1 k d (adjTable G) q with hL
  have hrun : fullAlg (planParams k K t) (G.1, adjTable G) = Alg.bestColoring G.1 k L := by
    rw [fullAlg, Alg.numV_graph]
    rfl
  rw [hrun]
  obtain ⟨hmem, -⟩ := Alg.bestColoring_spec G.1 k L
  rcases hmem with h | h
  · rw [hL, List.mem_flatMap] at h
    obtain ⟨q', -, h⟩ := h
    obtain ⟨d', -, h⟩ := List.mem_map.1 h
    rw [← h]
    refine Alg.isPartialColoring_colorOf G le_rfl _ fun v ↦ ?_
    rw [getD_clampK _ v.2]
    split_ifs with h'
    · exact h'
    · exact hk
  · rw [h]; intro u v _ hu; simp [Graph.color] at hu

/-! ### The constants -/

/-- The bound `16 / α⁴ + 12288 k⁹ / α` on the bad colorings for statistically bad vertices. -/
noncomputable def badC (k : ℕ) : ℝ := 16 / alphaF k ^ 4 + 12288 * (k : ℝ) ^ 9 / alphaF k

/-- The constant `P` of Theorem 7.17. -/
noncomputable def fullP (k : ℕ) : ℝ := (minN k : ℝ) + k + 2 * (k : ℝ) ^ 2 + badC k + 1

theorem exp_le_alphaF (hk : 0 < k) {d : ℕ} (hd : fullD k ≤ d) :
    4 * k * Real.exp (-(d : ℝ) / (2 * (k : ℝ) ^ 2)) ≤ alphaF k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hD : (2 : ℝ) ^ 21 * (k : ℝ) ^ 21 ≤ d := by
    have h1 : ((fullD k : ℕ) : ℝ) ≤ d := by exact_mod_cast hd
    have h2 : (2 : ℝ) ^ 21 * (k : ℝ) ^ 21 ≤ ((fullD k : ℕ) : ℝ) := by
      rw [fullD]; push_cast
      have h3 : (2 : ℝ) ^ 21 * (k : ℝ) ^ 21 ≤ 5 * 2 ^ 31 * (k : ℝ) ^ 23 := by
        have h5 : (k : ℝ) ^ 21 ≤ (k : ℝ) ^ 23 := pow_le_pow_right₀ hk1 (by norm_num)
        have h6 : (0 : ℝ) ≤ (k : ℝ) ^ 21 := by positivity
        nlinarith
      have h4 : 5 * 2 ^ 31 * (k : ℝ) ^ 23 ≤ (5 * 2 ^ 31 * (k : ℝ) ^ 23) ^ 4 := by
        have : (1 : ℝ) ≤ 5 * 2 ^ 31 * (k : ℝ) ^ 23 := by
          nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 23]
        exact le_self_pow₀ this (by norm_num)
      linarith
    linarith
  have hk21 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 21
  have hd1 : (1 : ℝ) ≤ d := le_trans (by nlinarith) hD
  have hy : 0 < (d : ℝ) / (2 * (k : ℝ) ^ 2) := by positivity
  have he := exp_neg_le_div_pow_four hy
  rw [neg_div]
  have h1 : 24 / ((d : ℝ) / (2 * (k : ℝ) ^ 2)) ^ 4 = 384 * (k : ℝ) ^ 8 / (d : ℝ) ^ 4 := by
    field_simp; ring
  rw [h1] at he
  have h2 : (d : ℝ) ≤ (d : ℝ) ^ 4 := le_self_pow₀ hd1 (by norm_num)
  calc 4 * (k : ℝ) * Real.exp (-((d : ℝ) / (2 * (k : ℝ) ^ 2)))
      ≤ 4 * k * (384 * (k : ℝ) ^ 8 / (d : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ alphaF k := by
        rw [alphaF, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos (by positivity : (0 : ℝ) < k) 9,
          pow_pos (by positivity : (0 : ℝ) < k) 12,
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 12]

theorem inv_expansion_ge (hk : 0 < k) : 8 * (k : ℝ) ^ 6 ≤ 1 / (lamF k + Real.sqrt (betaF k)) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : Real.sqrt (betaF k) = 1 / (16 * (k : ℝ) ^ 6) := by
    rw [betaF, show (256 : ℝ) * (k : ℝ) ^ 12 = (16 * (k : ℝ) ^ 6) ^ 2 by ring, Real.sqrt_div' 1
      (sq_nonneg _), Real.sqrt_one, Real.sqrt_sq (by positivity)]
  have h1 : lamF k + Real.sqrt (betaF k) ≤ 1 / (8 * (k : ℝ) ^ 6) := by
    rw [hsq, lamF, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (by positivity : (0 : ℝ) < k) 6, pow_pos (by positivity : (0 : ℝ) < k) 12]
  have hpos : 0 < lamF k + Real.sqrt (betaF k) := by
    have := lamF_pos hk; have := Real.sqrt_nonneg (betaF k); linarith
  rw [le_div_iff₀ hpos]
  calc 8 * (k : ℝ) ^ 6 * (lamF k + Real.sqrt (betaF k)) ≤ 8 * (k : ℝ) ^ 6 * (1 / (8 * k ^ 6)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := by field_simp

theorem expansion_le (hk : 0 < k) : 4 * k ^ 6 ≤
    ⌊1 / (lamF k + Real.sqrt (betaF k)) - 1⌋₊ := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 := inv_expansion_ge hk
  refine Nat.le_floor ?_
  push_cast
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 6]

/-! ### The probability -/

open Classical in
/-- **The probability of Theorem 7.17.** -/
theorem plantProb_full (hk : 3 ≤ k) (H : Graph) {d : ℕ} (hreg : H.2.IsRegularOfDegree d)
    (hd : fullD k ≤ d) (hexp : H.IsOneSidedExpander (lamF k)) :
    1 - fullP k / H.1 ≤ H.plantProb k fun G ↦
      G.IsColoring k 0 (fullAlg (fullParams k) (G.1, adjTable G)) := by
  have hk0 : 0 < k := by omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hpart := isPartialColoring_fullAlg hk0 (K := fullK k) (t := 1)
  have hfullD : 1 ≤ fullD k := Nat.one_le_pow _ _ (by positivity)
  have hd0 : d ≠ 0 := by omega
  have hα := alphaF_pos hk0
  have hbC : 0 ≤ badC k := by unfold badC; positivity
  have hP0 : 0 ≤ fullP k := by unfold fullP; positivity
  -- every coloring succeeds
  have hall : (∀ χ : Fin H.1 → Fin k, (H.plant χ).IsColoring k 0
      (fullAlg (fullParams k) ((H.plant χ).1, adjTable (H.plant χ)))) →
      1 - fullP k / H.1 ≤ H.plantProb k fun G ↦
        G.IsColoring k 0 (fullAlg (fullParams k) (G.1, adjTable G)) := by
    intro h
    have h1 : H.plantProb k (fun G ↦ G.IsColoring k 0
        (fullAlg (fullParams k) (G.1, adjTable G))) = 1 := by
      rw [Graph.plantProb, filter_true_of_mem fun χ _ ↦ h χ, card_univ, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin]
      push_cast
      exact div_self (by positivity)
    rw [h1]
    have : (0 : ℝ) ≤ fullP k / H.1 := by positivity
    linarith
  rcases Nat.eq_zero_or_pos H.1 with hn0 | hn0
  · exact hall fun χ ↦ isColoring_of_zero (hpart _) hn0
  have hnR : (0 : ℝ) < H.1 := by exact_mod_cast hn0
  by_cases hsmall : (H.1 : ℝ) < fullP k
  · have h1 : (1 : ℝ) ≤ fullP k / H.1 := by rw [le_div_iff₀ hnR, one_mul]; exact hsmall.le
    have h2 : 0 ≤ H.plantProb k fun G ↦
        G.IsColoring k 0 (fullAlg (fullParams k) (G.1, adjTable G)) := by
      unfold Graph.plantProb; positivity
    linarith
  push Not at hsmall
  have hn : minN k ≤ H.1 := by
    have : (minN k : ℝ) ≤ H.1 := by
      have : (minN k : ℝ) ≤ fullP k := by
        unfold fullP
        have h1 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ 2 * (k : ℝ) ^ 2 := by positivity
        linarith
      linarith
    exact_mod_cast this
  -- the three kinds of bad colorings
  set X : Fin H.1 → Fin H.1 → ℝ := fun x y ↦ H.normAdj x y
  have hX : IsWeight X (1 / d) := isWeight_normAdj H hreg hd0
  set F1 := univ.filter fun χ : Fin H.1 → Fin k ↦ ¬ Good X χ
  set F2 := univ.filter fun χ : Fin H.1 → Fin k ↦ alphaF k * H.1 < (badSet H d χ).card
  set F3 := univ.filter fun χ : Fin H.1 → Fin k ↦ ∃ S : Finset (Fin H.1), S.Nonempty ∧
    ConnSet H.2 S ∧ (S.card : ℝ) ≤ betaF k * H.1 ∧ H.1 ^ 2 < k ^ S.card ∧ Stuck H S χ
  have h1 : (F1.card : ℝ) ≤ (k + 2 * (k : ℝ) ^ 2) * ((k : ℝ) ^ H.1 / H.1) :=
    card_not_good_le hk0 hn0 hX
  have h2 : (F2.card : ℝ) ≤ badC k * ((k : ℝ) ^ H.1 / H.1) :=
    card_many_bad_le hreg hd0 hk0 hn0 hα (exp_le_alphaF hk0 hd)
  have hexpS : ∀ S : Finset (Fin H.1), ConnSet H.2 S → (S.card : ℝ) ≤ betaF k * H.1 →
      4 * k ^ 6 * S.card ≤ (boundary H S).card := by
    intro S _ hS
    have hb := card_boundary_ge hreg hd0 (lamF_pos hk0).le (lamF_lt_one hk0) hexp
      (by unfold betaF; positivity) S hS
    have hfl := expansion_le hk0
    have h3 : ((4 * k ^ 6 : ℕ) : ℝ) * S.card ≤ (1 / (lamF k + Real.sqrt (betaF k)) - 1) *
        S.card := by
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      refine le_trans (by exact_mod_cast hfl) (Nat.floor_le ?_)
      have h4 := inv_expansion_ge hk0
      have h5 : (1 : ℝ) ≤ 8 * (k : ℝ) ^ 6 := by
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hk1 6]
      linarith
    have := h3.trans hb
    exact_mod_cast this
  have h3 : (F3.card : ℝ) ≤ (k : ℝ) ^ H.1 / (H.1 : ℝ) ^ 5 :=
    card_bad_stuck_le (by omega) le_rfl hexpS
  have h3' : (F3.card : ℝ) ≤ 1 * ((k : ℝ) ^ H.1 / H.1) := by
    refine h3.trans ?_
    rw [one_mul]
    apply div_le_div_of_nonneg_left (by positivity) hnR
    have : (1 : ℝ) ≤ H.1 := by exact_mod_cast hn0
    nlinarith [pow_le_pow_left₀ zero_le_one this 4]
  -- the good colorings succeed
  have hcover : (univ : Finset (Fin H.1 → Fin k)) ⊆
      (univ.filter fun χ : Fin H.1 → Fin k ↦ (H.plant χ).IsColoring k 0
        (fullAlg (fullParams k) ((H.plant χ).1, adjTable (H.plant χ)))) ∪ (F1 ∪ F2 ∪ F3) := by
    intro χ _
    by_cases hg : Good X χ
    · by_cases hb : alphaF k * H.1 < (badSet H d χ).card
      · exact mem_union_right _
          (mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨mem_univ _, hb⟩)))
      · by_cases hs : ∃ S : Finset (Fin H.1), S.Nonempty ∧ ConnSet H.2 S ∧
            (S.card : ℝ) ≤ betaF k * H.1 ∧ H.1 ^ 2 < k ^ S.card ∧ Stuck H S χ
        · exact mem_union_right _ (mem_union_right _ (mem_filter.2 ⟨mem_univ _, hs⟩))
        · push Not at hb
          refine mem_union_left _ (mem_filter.2 ⟨mem_univ _, isColoring_full hk H hreg hd hexp χ
            hn hg hb fun S hne hc hS hbig hst ↦ hs ⟨S, hne, hc, hS, hbig, hst⟩⟩)
    · exact mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨mem_univ _, hg⟩)))
  have hkn : (0 : ℝ) < (k : ℝ) ^ H.1 := by positivity
  have hcard : (k : ℝ) ^ H.1 ≤ ((univ.filter fun χ : Fin H.1 → Fin k ↦ (H.plant χ).IsColoring k 0
      (fullAlg (fullParams k) ((H.plant χ).1, adjTable (H.plant χ)))).card : ℝ) +
      ((F1.card : ℝ) + F2.card + F3.card) := by
    have := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left ((card_union_le _ _).trans
        (Nat.add_le_add_right (card_union_le _ _) _)) _))
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
    exact_mod_cast this
  rw [Graph.plantProb, le_div_iff₀ hkn]
  have e : (1 - fullP k / H.1) * (k : ℝ) ^ H.1 =
      (k : ℝ) ^ H.1 -
        ((minN k : ℝ) + k + 2 * (k : ℝ) ^ 2 + badC k + 1) * ((k : ℝ) ^ H.1 / H.1) := by
    unfold fullP; ring
  rw [e]
  have hmin : 0 ≤ (minN k : ℝ) * ((k : ℝ) ^ H.1 / H.1) := by positivity
  nlinarith

/-! ### The theorem -/

open Classical in
/-- **Theorem 7.17** of [BHSV25] (random planting, full recovery). -/
theorem plantedColoring_full :
    ∃ C : ℕ, ∀ k : ℕ, 3 ≤ k → ∃ lam₀ P : ℝ, 0 < lam₀ ∧ ∃ d₀ : ℕ, ∃ K : ℝ,
      ∃ A : Graph → List ℕ, RunsInTime A encGraph encColoring K C ∧
        ∀ (H : Graph) (d : ℕ), H.2.IsRegularOfDegree d → d₀ ≤ d →
          H.IsOneSidedExpander lam₀ →
          1 - P / H.1 ≤ H.plantProb k fun G ↦ G.IsColoring k 0 (A G) := by
  obtain ⟨C₀, hrun⟩ := exists_runsInTime_graph_fix
    (V := fun z : ((ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ)) × (ℕ × List Bool) ↦ fullAlg z.1 z.2)
    fullAlg_polytime
  refine ⟨C₀, fun k hk ↦ ⟨lamF k, fullP k, lamF_pos (by omega), fullD k, ?_⟩⟩
  obtain ⟨K, hK⟩ := hrun (fullParams k)
  exact ⟨K, _, hK, fun H d hreg hd hexp ↦ plantProb_full hk H hreg hd hexp⟩

end Planted

end BHSV25
