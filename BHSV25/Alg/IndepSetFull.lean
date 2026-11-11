module

public import BHSV25.Alg.IndepSetGS
public import BHSV25.Spectral.ThresholdRank

/-!
# Theorem 7.20 with a given number of rounds

The guarantee of the algorithm `BHSV25.Alg.indepAlgGS` of [BHSV25, Theorem 7.20] with `t` rounds,
on regular graphs with at most `t` eigenvalues at most `-λ`
(`BHSV25.Alg.card_indepAlgGS_final`): an independent set of at least
`(1/2 - γ - (4 + c) γ / (1 - λ)) n` vertices if the graph has one of `(1/2 - γ) n` vertices. The
vertex cover algorithm of Corollary 1.2 and the algorithm of Corollary 1.4 run it for fixed `t`
(`BHSV25.Alg.exists_indep_params`, `BHSV25.Alg.exists_indep_params_top`); Theorem 7.20 itself is
stated for the algorithm that finds the number of rounds (`BHSV25/Alg/IndepSetUnif.lean`).

**The parameters**, for `c₁ = min(c, 1)` and `c'' = η = c₁/32`:
`K = ⌈A (1 + (1 - λ)/γ)⌉` with `A = 32 (1 + 32/c₁) / c + 1`, so that the precision `ρ = 4/K`
costs `(1 + 1/η) ρ² ≤ (c/2) γ / (1 - λ)`; the radius `N = (⌊√t⌋ + 1) K` and the budget
`B = (3 + 12 K)^t` of the grid; the power `a n⁵` of the filter with `a = ⌈8 (t + 2 + K/2) / c''⌉`.

Corollary 7.21 follows from Corollary 4.2: at most `t` eigenvalues above `λ < 1/2` leave at most
`t / λ²` at most `-√(2λ)` (`BHSV25.Alg.card_eig_le_neg_sqrt_le`).
-/

@[expose] public section

namespace BHSV25.Alg

/-! ### The arithmetic of the guarantee -/

/-- The coefficient of the loss: `(1 + c'') 4 / ((1 - c'') (1 - λ)) ≤ (4 + c/2) / (1 - λ)` for
`c'' = c₁ / 32`, `c₁ ≤ min(c, 1)`. -/
theorem coef_loss_le {c c₁ cc lam : ℝ} (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₁c : c₁ ≤ c)
    (hcc : cc = c₁ / 32) (hl1 : lam < 1) :
    (1 + cc) * 4 / ((1 - cc) * (1 - lam)) ≤ (4 + c / 2) / (1 - lam) := by
  have hl' : 0 < 1 - lam := by linarith
  have hcc1 : cc < 1 := by rw [hcc]; linarith
  rw [div_le_div_iff₀ (mul_pos (by linarith) hl') hl']
  have h1 : (1 + cc) * 4 ≤ (4 + c / 2) * (1 - cc) := by
    rw [hcc]
    nlinarith
  nlinarith

/-- The cost of the precision: `(1 + 1/c'') (4/K)² ≤ (c/2) γ / (1 - λ)` for
`K ≥ (32 (1 + 32/c₁) / c + 1) (1 + (1 - λ)/γ)`. -/
theorem coef_prec_le {c c₁ cc lam γ A₁ W : ℝ} {K : ℕ} (hc : 0 < c) (hc₁0 : 0 < c₁)
    (hcc : cc = c₁ / 32) (hl1 : lam < 1) (hγ0 : 0 < γ) (hA₁ : A₁ = 32 * (1 + 32 / c₁) / c + 1)
    (hW : W = 1 + (1 - lam) / γ) (hKge : A₁ * W ≤ K) :
    (1 + 1 / cc) * (4 / K) ^ 2 ≤ c / 2 * γ / (1 - lam) := by
  have hl' : 0 < 1 - lam := by linarith
  set X := 32 * (1 + 32 / c₁) / c with hX
  set Q := (1 - lam) / γ with hQ
  have hX0 : 0 ≤ X := by positivity
  have hQ0 : 0 ≤ Q := div_nonneg hl'.le hγ0.le
  have hK1 : (1 : ℝ) ≤ K := by
    have : (1 : ℝ) ≤ A₁ * W := by rw [hA₁, hW]; nlinarith
    linarith
  have hK2 : X * Q ≤ (K : ℝ) ^ 2 := by
    have : X * Q ≤ A₁ * W := by rw [hA₁, hW]; nlinarith
    nlinarith
  have e : (1 + 1 / cc) * (4 / K) ^ 2 = (c / 2 * γ / (1 - lam)) * (X * Q) / (K : ℝ) ^ 2 := by
    rw [hcc, hX, hQ]
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left hK2 (by positivity)

/-- The final count: `|I| - X g - B n ≤ out` with `0 ≤ g = n/2 - |I| ≤ γ n`,
`X ≤ (4 + c/2) / (1 - λ)` and `B ≤ (c/2) γ / (1 - λ)` give
`(1/2 - γ - (4 + c) γ / (1 - λ)) n ≤ out`. -/
theorem final_count_le {c lam γ n Ic out X Bρ : ℝ} (hl1 : lam < 1) (hc : 0 < c) (hn : 0 ≤ n)
    (hg0 : 0 ≤ n / 2 - Ic) (hgγ : n / 2 - Ic ≤ γ * n)
    (hX : X ≤ (4 + c / 2) / (1 - lam)) (hB : Bρ ≤ c / 2 * γ / (1 - lam))
    (hmain : Ic - X * (n / 2 - Ic) - Bρ * n ≤ out) :
    (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * n ≤ out := by
  have hl' : 0 < 1 - lam := by linarith
  have h1 := mul_le_mul_of_nonneg_right hX hg0
  have h2 := mul_le_mul_of_nonneg_left hgγ (by positivity : (0 : ℝ) ≤ (4 + c / 2) / (1 - lam))
  have h3 := mul_le_mul_of_nonneg_right hB hn
  have e : (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * n =
      n / 2 - γ * n - (4 + c / 2) / (1 - lam) * (γ * n) - c / 2 * γ / (1 - lam) * n := by
    field_simp
    ring
  rw [e]
  linarith

open Classical in
/-- **The guarantee for the chosen parameters.** -/
theorem card_indepAlgGS_final (G : Graph) (hreg : G.IsRegular) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1) {t : ℕ} (ht : (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t)
    {c c₁ cc γ A₁ W : ℝ} (hc : 0 < c) (hc₁0 : 0 < c₁) (hc₁1 : c₁ ≤ 1) (hc₁c : c₁ ≤ c)
    (hcc : cc = c₁ / 32) (hγ0 : 0 < γ) (hA₁ : A₁ = 32 * (1 + 32 / c₁) / c + 1)
    (hW : W = 1 + (1 - lam) / γ) {K a : ℕ} (hKpos : 0 < K) (hKge : A₁ * W ≤ K)
    (hage : 8 / cc * (t + 2 + K / 2 : ℝ) ≤ a) (hInd : G.HasIndepSet ((1 / 2 - γ) * G.1)) :
    (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤
      (G.vertexSet (indepAlgGS (a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t)
        (G.1, adjTable G))).card := by
  obtain ⟨I, hI, hIcard⟩ := hInd
  obtain ⟨d, hd⟩ := hreg
  have hl' : 0 < 1 - lam := by linarith
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcc1 : cc < 1 := by rw [hcc]; linarith
  rcases Nat.eq_zero_or_pos G.1 with hn0 | hn
  · have : (G.1 : ℝ) = 0 := by exact_mod_cast hn0
    rw [this, mul_zero]
    exact Nat.cast_nonneg _
  by_cases hd0 : d = 0
  · -- no edges: all vertices
    subst hd0
    have h := card_indepAlg_of_degree_zero (indepNet (a, t, (Nat.sqrt t + 1) * K,
      (3 + 12 * K) ^ t)) G hd
    have h' : (G.1 : ℝ) ≤ (G.vertexSet (indepAlgGS (a, t, (Nat.sqrt t + 1) * K,
        (3 + 12 * K) ^ t) (G.1, adjTable G))).card := by exact_mod_cast h
    have hn' : (0 : ℝ) ≤ G.1 := Nat.cast_nonneg _
    have hloss0 : 0 ≤ (4 + c) * γ / (1 - lam) := by positivity
    have : (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤ G.1 := by nlinarith
    linarith
  have hmain := card_indepAlgGS_ge G hd hd0 hn hl0 hl1 ht hcc0 hcc1 hKpos hage hI hcc0
  have hg0 : 0 ≤ (G.1 : ℝ) / 2 - I.card := by
    have : (2 * I.card : ℝ) ≤ G.1 := by exact_mod_cast two_mul_card_le G hd hd0 hI
    linarith
  exact final_count_le hl1 hc (Nat.cast_nonneg _) hg0 (by linarith)
    (coef_loss_le hc₁0 hc₁1 hc₁c hcc hl1) (coef_prec_le hc hc₁0 hcc hl1 hγ0 hA₁ hW hKge) hmain

/-! ### Corollary 7.21: the count of the bottom eigenvalues -/

/-- At most `t` eigenvalues above `λ < 1/2` leave at most `t / λ²` eigenvalues at most `-√(2λ)`
(Corollary 4.2, through Theorem 4.1 with `τ = √(2λ)` and `τ' = λ + λ²/2`). -/
theorem card_eig_le_neg_sqrt_le (G : Graph) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1 / 2)
    {t : ℕ} (ht : G.numEigGT lam ≤ t) :
    (Finset.univ.filter fun i ↦ G.eig i ≤ -Real.sqrt (2 * lam)).card ≤ ⌈(t : ℝ) / lam ^ 2⌉₊ := by
  set τ := Real.sqrt (2 * lam) with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.2 (by linarith)
  have hτ2 : τ ^ 2 = 2 * lam := Real.sq_sqrt (by linarith)
  set τ' := lam + lam ^ 2 / 2 with hτ'
  have hτ'lt : τ' < τ ^ 2 := by rw [hτ2, hτ']; nlinarith
  have h := Spectral.thresholdRank_graph G τ τ' hτ0.le hτ'lt
  have hcount : (Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card ≤ t := by
    refine le_trans (Finset.card_le_card fun i hi ↦ ?_) ht
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨hi.1, lt_of_lt_of_le ?_ hi.2⟩
    rw [hτ']
    nlinarith
  have hσ : lam ≤ (τ ^ 2 - τ') / (1 - τ') := by
    have h1 : 0 < 1 - τ' := by rw [hτ']; nlinarith
    rw [le_div_iff₀ h1, hτ2, hτ']
    nlinarith
  have hσ0 : 0 ≤ lam := hl0.le
  have h2 : lam ^ 2 * ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤ t := by
    have h3 : lam ^ 2 ≤ ((τ ^ 2 - τ') / (1 - τ')) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    have h4 : ((Finset.univ.filter fun i ↦ τ' ≤ G.eig i).card : ℝ) ≤ t := by
      exact_mod_cast hcount
    have h5 := mul_le_mul_of_nonneg_right h3
      (Nat.cast_nonneg (α := ℝ) (Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card)
    linarith
  have h6 : ((Finset.univ.filter fun i ↦ G.eig i ≤ -τ).card : ℝ) ≤ t / lam ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact h2
  exact_mod_cast h6.trans (Nat.le_ceil _)

/-! ### The parameters, for the corollaries -/

open Classical in
/-- **The parameters of Theorem 7.20** for `c`, `λ`, `t` and `γ`: the algorithm
`BHSV25.Alg.indepAlgGS p` has the guarantee of Theorem 7.20. -/
theorem exists_indep_params {c : ℝ} (hc : 0 < c) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1)
    (t : ℕ) {γ : ℝ} (hγ0 : 0 < γ) :
    ∃ p : ℕ × ℕ × ℕ × ℕ, ∀ G : Graph, G.IsRegular →
      (Finset.univ.filter fun i ↦ G.eig i ≤ -lam).card ≤ t →
      G.HasIndepSet ((1 / 2 - γ) * G.1) →
        (1 / 2 - γ - (4 + c) * γ / (1 - lam)) * G.1 ≤
          (G.vertexSet (indepAlgGS p (G.1, adjTable G))).card := by
  obtain ⟨c₁, hc₁⟩ : ∃ x : ℝ, x = min c 1 := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := hc₁ ▸ lt_min hc one_pos
  have hc₁1 : c₁ ≤ 1 := hc₁ ▸ min_le_right _ _
  have hc₁c : c₁ ≤ c := hc₁ ▸ min_le_left _ _
  obtain ⟨cc, hcc⟩ : ∃ x : ℝ, x = c₁ / 32 := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ x : ℝ, x = 32 * (1 + 32 / c₁) / c + 1 := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ x : ℝ, x = 1 + (1 - lam) / γ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈A₁ * W⌉₊ := ⟨_, rfl⟩
  have hKge : A₁ * W ≤ K := hK ▸ Nat.le_ceil _
  have hA₁1 : 1 ≤ A₁ := by
    have : 0 ≤ 32 * (1 + 32 / c₁) / c := by positivity
    rw [hA₁]
    linarith
  have hW1 : 1 ≤ W := by
    rw [hW]
    have : 0 ≤ (1 - lam) / γ := div_nonneg (by linarith) hγ0.le
    linarith
  have hK1 : 1 ≤ K := by
    have : (1 : ℝ) ≤ K := le_trans (by nlinarith) hKge
    exact_mod_cast this
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = ⌈8 / cc * (t + 2 + K / 2 : ℝ)⌉₊ := ⟨_, rfl⟩
  have hage : 8 / cc * (t + 2 + K / 2 : ℝ) ≤ a := ha ▸ Nat.le_ceil _
  exact ⟨(a, t, (Nat.sqrt t + 1) * K, (3 + 12 * K) ^ t), fun G hreg ht hInd ↦
    card_indepAlgGS_final G hreg hl0 hl1 ht hc hc₁0 hc₁1 hc₁c hcc hγ0 hA₁ hW hK1 hKge hage hInd⟩

/-- **The parameters of Corollary 7.21** for `c`, `λ < 1/2`, `t` and `γ`. -/
theorem exists_indep_params_top {c : ℝ} (hc : 0 < c) {lam : ℝ} (hl0 : 0 < lam)
    (hl1 : lam < 1 / 2) (t : ℕ) {γ : ℝ} (hγ0 : 0 < γ) :
    ∃ p : ℕ × ℕ × ℕ × ℕ, ∀ G : Graph, G.IsRegular → G.numEigGT lam ≤ t →
      G.HasIndepSet ((1 / 2 - γ) * G.1) →
        (1 / 2 - γ - (4 + c) * γ / (1 - Real.sqrt (2 * lam))) * G.1 ≤
          (G.vertexSet (indepAlgGS p (G.1, adjTable G))).card := by
  have hτ0 : 0 < Real.sqrt (2 * lam) := Real.sqrt_pos.2 (by linarith)
  have hτ1 : Real.sqrt (2 * lam) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    linarith
  obtain ⟨p, hp⟩ := exists_indep_params hc hτ0 hτ1 ⌈(t : ℝ) / lam ^ 2⌉₊ hγ0
  exact ⟨p, fun G hreg ht hInd ↦ hp G hreg (card_eig_le_neg_sqrt_le G hl0 hl1 ht) hInd⟩

end BHSV25.Alg
