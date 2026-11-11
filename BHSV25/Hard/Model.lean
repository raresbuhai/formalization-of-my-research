module

public import BHSV25.Hard.ModelNo

/-!
# Theorem 1.9 (2): hardness of `(M, α - γ)`-expander-coloring

[BHSV25, Theorem 8.2], in the form of `BHSV25.expanderColoring_hardness`
(`BHSV25.Hard.expanderColoring_hardness`). The reduction is the blow-up of the design of
`BHSV25/Hard/ModelDesign.lean` by the input graph `G` of the gap problem of Bansal and Khot,
following the pattern of Theorem 1.6 (`BHSV25/Hard/LowRank.lean`).

* **The design** (`BHSV25.Hard.ModelRed.Data.design`): its groups are the colors `i`, with
  densities `q_ij ∝ w_ij / (s_i s_j)` for the symmetric rounding `w_ij = ⌊D π_i M_ij⌋` of
  `π_i M_ij` and its row sums `s_i`, and `s_i` host units per group, which makes the template
  exactly regular. Each host unit carries `2H` color units, colored by the distribution of the
  class of `i` (the colors with the row of `i`) along an interval, and the unit `u` is paired with
  `u + H`; units whose pair has another color are copies of `G`, the others independent; the
  absorbers make the correction sum to `0` on every row.
* **Yes-instances** (`BHSV25.Hard.ModelRed.Data.yes`): the planted matrix is `κ M_ij / π_j` up
  to `κ δ₀`, at most `0` on the vectors of sum `0` (`BHSV25.Hard.model_quad_nonpos`), so the
  blow-up is a `λ`-one-sided expander; the coloring by the labels of the types is an
  `(M, ε)`-coloring, its model being computed by the bilinear approximation
  (`BHSV25.Hard.Design.bil_blow_sub_le`).
* **No-instances** (`BHSV25.Hard.ModelRed.Data.no`): the copies and the absorbers have color
  classes of fewer than `γ_B n` vertices, and the independent types are at most a
  `1 - α + o(1)` fraction of the types, so at most `(1 - α + 3γ/4) N` vertices are colored.

The parameters `m` (absorbers), `H` (color units), `D` (weights), `a` (pseudo-random sets) and
`η` (maximum degree of `G`) are chosen in this order.
-/

@[expose] public section

namespace BHSV25.Hard

open Finset Turing.MultiTapeTM Cslib.Complexity

/-- Theorem 8.2 for `ε ≤ α - γ`, where an `(M, ε)`-coloring is a `(k, α - γ)`-coloring. -/
theorem expanderColoring_hardness_le (hUGC : UniqueGames.KhotUGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (π : Fin k → ℝ) (hπ : IsStationary M π)
    {γ ε lam : ℝ} (hγ : 0 < γ) (hε : 0 < ε) (hεγ : ε ≤ alpha M π - γ) (hlam : 0 < lam) :
    PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
      G.IsOneSidedExpander lam ∧ G.MColorable M ε) k (alpha M π - γ)) := by
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · have h1 := hπ.2.1
      subst h
      simp at h1
    · exact h
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨i₀, -, hi₀⟩ := exists_min_image univ π ⟨⟨0, hk⟩, mem_univ _⟩
  set pm := π i₀
  have hpm : 0 < pm := hπ.1 i₀
  have hπpm : ∀ i, pm ≤ π i := fun i ↦ hi₀ i (mem_univ i)
  obtain ⟨ε₀, hε₀, hBK⟩ := bansalKhot hUGC
  set εB := min ε₀ (ε / 8) with hεB
  set γB := min ε₀ (γ / (4 * k)) with hγB
  have hεB0 : 0 < εB := lt_min hε₀ (by positivity)
  have hγB0 : 0 < γB := lt_min hε₀ (by positivity)
  have hεB8 : εB ≤ ε / 8 := min_le_right _ _
  have hγBk : k * γB ≤ γ / 4 := by
    have : γB ≤ γ / (4 * k) := min_le_right _ _
    calc k * γB ≤ k * (γ / (4 * k)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = γ / 4 := by field_simp
  -- the absorber blocks
  obtain ⟨m, hm1, hm⟩ : ∃ m : ℕ, 0 < m ∧ 1 / ((m : ℝ) + 1) ≤ ε / 4 := by
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt (4 / ε)
    refine ⟨m₀ + 1, by omega, ?_⟩
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (4 / ε) * ε = 4 := by field_simp
    push_cast
    nlinarith
  -- the color units
  obtain ⟨H, hH1, hHpm, hHγ, hHε⟩ : ∃ H : ℕ, 0 < H ∧ (k : ℝ) + 1 ≤ 2 * H * pm ∧
      (k : ℝ) / H ≤ γ / 4 ∧ (k : ℝ) / (2 * H) ≤ ε * pm / 8 := by
    obtain ⟨H₀, hH₀⟩ := exists_nat_gt ((k + 1) / pm + 4 * k / γ + 4 * k / (ε * pm))
    have h1 : (0 : ℝ) ≤ (k + 1) / pm := by positivity
    have h2 : (0 : ℝ) ≤ 4 * k / γ := by positivity
    have h3 : (0 : ℝ) ≤ 4 * k / (ε * pm) := by positivity
    have hH : (H₀ : ℝ) + 1 > 0 := by positivity
    refine ⟨H₀ + 1, by omega, ?_, ?_, ?_⟩ <;> push_cast
    · have : (k + 1) / pm ≤ (H₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hpm] at this
      nlinarith
    · rw [div_le_iff₀ hH]
      have : 4 * k / γ ≤ (H₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hγ] at this
      linarith
    · rw [div_le_iff₀ (by positivity)]
      have : 4 * k / (ε * pm) ≤ (H₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
  -- the precision of the weights
  obtain ⟨D, hDπ, hDγ, hDε, hDδε, hDδl⟩ : ∃ D : ℕ, 2 * (k : ℝ) + 1 ≤ D * pm ∧
      2 * (k : ℝ) ^ 2 / D ≤ γ / 4 ∧ (k : ℝ) ^ 2 / D ≤ ε * pm / 8 ∧
      8 * (k : ℝ) / (D * pm ^ 3) ≤ ε / 4 ∧ 8 * (k : ℝ) / (D * pm ^ 3) ≤ lam / 2 := by
    obtain ⟨D₀, hD₀⟩ := exists_nat_gt ((2 * k + 1) / pm + 8 * k ^ 2 / γ + 8 * k ^ 2 / (ε * pm) +
      32 * k / (ε * pm ^ 3) + 16 * k / (lam * pm ^ 3))
    have h1 : (0 : ℝ) ≤ (2 * k + 1) / pm := by positivity
    have h2 : (0 : ℝ) ≤ 8 * k ^ 2 / γ := by positivity
    have h3 : (0 : ℝ) ≤ 8 * k ^ 2 / (ε * pm) := by positivity
    have h4 : (0 : ℝ) ≤ 32 * k / (ε * pm ^ 3) := by positivity
    have h5 : (0 : ℝ) ≤ 16 * k / (lam * pm ^ 3) := by positivity
    have hD : (D₀ : ℝ) + 1 > 0 := by positivity
    refine ⟨D₀ + 1, ?_, ?_, ?_, ?_, ?_⟩ <;> push_cast
    · have : (2 * k + 1) / pm ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hpm] at this
      linarith
    · rw [div_le_iff₀ hD]
      have : 8 * k ^ 2 / γ ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ hγ] at this
      linarith
    · rw [div_le_iff₀ hD]
      have : 8 * k ^ 2 / (ε * pm) ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    · rw [div_le_iff₀ (by positivity)]
      have : 32 * k / (ε * pm ^ 3) ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
    · rw [div_le_iff₀ (by positivity)]
      have : 16 * k / (lam * pm ^ 3) ≤ (D₀ : ℝ) + 1 := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      nlinarith
  have hD : ∀ i, 2 * (k : ℝ) + 1 ≤ D * π i := fun i ↦
    hDπ.trans (mul_le_mul_of_nonneg_left (hπpm i) (Nat.cast_nonneg _))
  set X : ModelRed.Data := ⟨k, M, π, hM, hπ, D, H, m, hD, hH1, hm1⟩
  -- the pseudo-random sets and the maximum degree
  set T : ℝ := min (ε / 8 / (1 + 2 * H * D)) (lam / 4) with hT
  have hT0 : 0 < T := lt_min (by positivity) (by positivity)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, 2 * (D : ℝ) * 8 ^ X.r / 2 ^ a ≤ T := by
    obtain ⟨a, ha⟩ :=
      pow_unbounded_of_one_lt (2 * (D : ℝ) * 8 ^ X.r / T) (by norm_num : (1 : ℝ) < 2)
    refine ⟨a, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hT0] at ha
    linarith
  set η : ℝ := T / (2 * m) with hη
  have hη0 : 0 < η := by positivity
  have hξ : X.ξ a η ≤ 2 * T := by
    change 2 * (D : ℝ) * 8 ^ X.r / 2 ^ a + 2 * m * η ≤ 2 * T
    have : 2 * (m : ℝ) * η = T := by simp only [hη]; field_simp
    linarith
  have hξ0 : 0 ≤ X.ξ a η := by unfold ModelRed.Data.ξ; positivity
  have hδ : X.δ₀ pm ≤ ε / 4 ∧ X.δ₀ pm ≤ lam / 2 := ⟨hDδε, hDδl⟩
  have hNP := hBK εB γB η hεB0 (min_le_left _ _) hγB0 (min_le_left _ _) hη0
  refine npHard_of_reduction hεB0.le hγB0 hη0.le hNP (X.design.template a).blowup
    (X.design.template a).blowup_polytime (fun G hG hn ↦ ?_) fun G hG ↦ ?_
  · -- yes-instances
    obtain ⟨hdeg, I, J, hIJ, hI, hJ, hIc, hJc⟩ := hG
    have hcov : 1 / ((m : ℝ) + 1) + 2 * εB ≤ ε := by linarith
    have hmod : X.ξ a η * (1 + 2 * H * D) + X.δ₀ pm +
        ((k : ℝ) ^ 2 / D + k / (2 * H)) / pm ≤ ε := by
      have h1 : X.ξ a η * (1 + 2 * H * D) ≤ ε / 4 := by
        have hTe : T ≤ ε / 8 / (1 + 2 * H * D) := min_le_left _ _
        have hpos : (0 : ℝ) < 1 + 2 * H * D := by positivity
        calc X.ξ a η * (1 + 2 * H * D) ≤ 2 * T * (1 + 2 * H * D) :=
              mul_le_mul_of_nonneg_right hξ hpos.le
          _ ≤ 2 * (ε / 8 / (1 + 2 * H * D)) * (1 + 2 * H * D) := by gcongr
          _ = ε / 4 := by field_simp; ring
      have h2 : ((k : ℝ) ^ 2 / D + k / (2 * H)) / pm ≤ ε / 4 := by
        rw [div_le_iff₀ hpm]
        linarith
      linarith [hδ.1]
    have hl : X.ξ a η + X.δ₀ pm ≤ lam := by
      have : T ≤ lam / 4 := min_le_right _ _
      linarith [hδ.2]
    obtain ⟨hreg, hexp, hcol⟩ := X.yes a G hn hη0.le hpm hπpm hHpm hdeg hIJ hI hJ hIc hJc hcov
      hmod hl
    exact ⟨⟨hreg, hexp, hcol⟩, hasColoring_mono (hasColoring_of_mColorable _ hcol) hεγ⟩
  · -- no-instances
    have hn := pos_of_mem_no hγB0 hG
    obtain ⟨-, -, hno⟩ := hG
    have hC : 0 < Fintype.card (X.design.Cell a) := by
      have : (0 : ℝ) < Fintype.card (X.design.Cell a) := by
        rw [X.card_cells a]
        have : (1 : ℝ) ≤ ∑ i, (X.s i : ℝ) :=
          le_trans (by exact_mod_cast X.one_le_s ⟨0, hk⟩)
            (single_le_sum (f := fun i ↦ (X.s i : ℝ)) (fun i _ ↦ Nat.cast_nonneg _)
              (mem_univ _))
        have := X.one_le_cnt
        positivity
      exact_mod_cast this
    refine not_hasColoring_of_le (Nat.mul_pos hC hn) (q := 1 - alpha M π + 3 * γ / 4)
      (by linarith) fun c hc ↦ ?_
    have h := X.no a G hγB0.le hno c hc
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
    change 1 - alpha M π + 2 * (k : ℝ) ^ 2 / D + k / H + k * γB ≤ 1 - alpha M π + 3 * γ / 4
    linarith

/-- **Theorem 1.9 (2)** of [BHSV25] (Theorem 8.2): assuming the Unique Games Conjecture, for
every model `M` with stationary distribution `π`, all `ε, λ > 0` and `γ ∈ (0, α)`, it is NP-hard
to find a `(k, α - γ)`-coloring of a regular `λ`-one-sided expander with an `(M, ε)`-coloring. -/
theorem expanderColoring_hardness (hUGC : UniqueGames.KhotUGC) {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (hM : IsModel M) (π : Fin k → ℝ) (hπ : IsStationary M π) :
    ∀ γ ε lam : ℝ, 0 < γ → γ < alpha M π → 0 < ε → 0 < lam →
      PromiseProblem.NPHard encGraph (coloringGap (fun G ↦ G.IsRegular ∧
        G.IsOneSidedExpander lam ∧ G.MColorable M ε) k (alpha M π - γ)) := by
  intro γ ε lam hγ hγα hε hlam
  have h := expanderColoring_hardness_le hUGC M hM π hπ (ε := min ε (alpha M π - γ)) hγ
    (lt_min hε (by linarith)) (min_le_right _ _) hlam
  exact h.mono (fun G hG ↦ ⟨⟨hG.1.1, hG.1.2.1, mColorable_mono hG.1.2.2 (min_le_left _ _)⟩, hG.2⟩)
    fun _ h ↦ h

end BHSV25.Hard
