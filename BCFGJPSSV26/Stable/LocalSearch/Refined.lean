module

public import BCFGJPSSV26.Stable.LocalSearch.Defs
public import BCFGJPSSV26.Stable.LocalSearch.StarForest

/-!
# The refined local-search bound

[BCFGJPSSV26b, Theorem 3.6]: for an approximate local optimum `S`
with swaps of size `24 N` and threshold `1/(N k)`, a benchmark set `B`, assignments
`μA : clients → S` and `μB : clients → B`, and a set `D₀` of clients such that
`|B| + |μA(D \ D₀)| ≤ k` and the two clusterings are cross-free with respect to `D₀`
(`BCFGJPSSV26.Stable.CrossFreeWrt`, [BCFGJPSSV26b, Definition 3.5]),

  `cost(S) ≤ cost_μB(D₀) + (cost(μA) - cost_S(D₀)) + (10/N) (cost(μA) + cost_μB(D₀))`

(`BCFGJPSSV26.Stable.refined_ls`). The paper's `O(ε)` is `10/N` here.

Proof: the intersection graph of the `A`-clusters inside `D₀` and the
`B`-clusters is star-like by cross-freeness, and `|B| ≤ |A'|`; apply
`BCFGJPSSV26.Stable.BiGraph.exists_swap_families`, test every swap `T = (S \ A'ᵢ) ∪ Bᵢ` against
approximate local optimality with the test assignment of the paper, sum over the swaps of a
family and average over the families.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

variable (I) in
open Classical in
/-- **Cross-free with respect to `D₀`**: with `A'` the facilities of `S` all of whose `μA`-clients
are in `D₀`, `D̂₀ = μA⁻¹(A')`, `A_c = μA⁻¹(c)` and `B'_{c*} = μB⁻¹(c*) ∩ D̂₀`, every `A_c`,
`c ∈ A'`, and every `B'_{c*}` are disjoint or nested. -/
def CrossFreeWrt (S : Finset (Fin I.m)) (μA μB : Fin I.n → Fin I.m) (D₀ : Finset (Fin I.n)) :
    Prop :=
  ∀ c ∈ S.filter (fun c ↦ ∀ j, μA j = c → j ∈ D₀), ∀ c' : Fin I.m,
    Disjoint (univ.filter fun j ↦ μA j = c)
        (univ.filter fun j ↦ μB j = c' ∧ ∀ j', μA j' = μA j → j' ∈ D₀) ∨
      (univ.filter fun j ↦ μA j = c) ⊆
        (univ.filter fun j ↦ μB j = c' ∧ ∀ j', μA j' = μA j → j' ∈ D₀) ∨
      (univ.filter fun j ↦ μB j = c' ∧ ∀ j', μA j' = μA j → j' ∈ D₀) ⊆
        (univ.filter fun j ↦ μA j = c)

/-- Summing an indicator along the positions of a list counts. -/
private theorem sum_fin_countP {γ : Type*} (l : List γ) (p : γ → Bool) :
    (∑ i : Fin l.length, if p l[i] then (1 : ℕ) else 0) = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, ← ih]
    change (∑ i : Fin (l.length + 1), if p (a :: l)[i] then (1 : ℕ) else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ]
    rw [add_comm]
    rfl

/-- The same, in `ℝ`. -/
private theorem sum_fin_countP_real {γ : Type*} (l : List γ) (p : γ → Bool) :
    (∑ i : Fin l.length, if p l[i] then (1 : ℝ) else 0) = l.countP p := by
  rw [← sum_fin_countP l p]
  push_cast
  rfl

/-- One swap tested against approximate local optimality, with the test assignment: the clients
of `X` go to `μB`, the other clients of closed facilities to `μA`, the rest stay. -/
private theorem swap_test (hv : I.Valid) {p : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {S : Finset (Fin I.m)}
    (hS : IsALO I p δ S) (hSne : S.Nonempty) {μA μB : Fin I.n → Fin I.m} (hA : ∀ j, μA j ∈ S)
    {Ls Rs : Finset (Fin I.m)} (hLs : Ls ⊆ S) (hcard : Rs.card ≤ Ls.card) (hp : Ls.card ≤ p)
    (X : Fin I.n → Prop) [DecidablePred X] (hX : ∀ j, X j → μB j ∈ Rs)
    (hXA : ∀ j, μA j ∈ Ls → X j) :
    ∑ j, (if X j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j)) else 0) ≤
      ∑ j, (if ¬ X j ∧ I.near S hSne (.inl j) ∈ Ls then
        I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) + δ * I.costF S := by
  classical
  set T := (S \ Ls) ∪ Rs with hT
  have hT1 : (1 - δ) * I.costF S ≤ I.costF T := by
    rcases T.eq_empty_or_nonempty with hT0 | hT0
    · have h1 : I.costF S ≤ I.costF T := by
        rw [hT0]
        exact sum_le_sum fun j _ ↦ by
          rw [Instance.dSet_empty]
          exact Instance.dSet_le_dMax hv _ _
      nlinarith [Instance.costF_nonneg hv S]
    · refine hS.2 T hT0 ?_ ?_
      · have h1 : T.card ≤ (S \ Ls).card + Rs.card := card_union_le _ _
        have h2 : (S \ Ls).card = S.card - Ls.card := card_sdiff_of_subset hLs
        have h3 := card_le_card hLs
        have h4 := hS.1
        omega
      · refine (card_le_card fun c hc ↦ ?_).trans hp
        rw [mem_sdiff, hT, mem_union, mem_sdiff] at hc
        by_contra h
        exact hc.2 (Or.inl ⟨hc.1, h⟩)
  have hT2 : I.costF T ≤ ∑ j, (if X j then I.dd (.inl j) (.inr (μB j)) else
      if I.near S hSne (.inl j) ∈ Ls then I.dd (.inl j) (.inr (μA j)) else
        I.dSet (.inl j) S) := by
    unfold Instance.costF
    refine sum_le_sum fun j _ ↦ ?_
    split_ifs with h1 h2
    · exact Instance.dSet_le (mem_union_right _ (hX j h1)) _
    · exact Instance.dSet_le (mem_union_left _ (mem_sdiff.2 ⟨hA j, fun h ↦ h1 (hXA j h)⟩)) _
    · calc I.dSet (.inl j) T ≤ I.dd (.inl j) (.inr (I.near S hSne (.inl j))) :=
            Instance.dSet_le (mem_union_left _
              (mem_sdiff.2 ⟨Instance.near_mem hSne _, h2⟩)) _
        _ = I.dSet (.inl j) S := Instance.dd_near hSne _
  have hsplit : (∑ j, (if X j then I.dd (.inl j) (.inr (μB j)) else
      if I.near S hSne (.inl j) ∈ Ls then I.dd (.inl j) (.inr (μA j)) else
        I.dSet (.inl j) S)) = I.costF S -
      ∑ j, (if X j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j)) else 0) +
      ∑ j, (if ¬ X j ∧ I.near S hSne (.inl j) ∈ Ls then
        I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) := by
    unfold Instance.costF
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases h1 : X j
    · simp [h1]
    · by_cases h2 : I.near S hSne (.inl j) ∈ Ls
      · simp [h1, h2]
      · simp [h1, h2]
  linarith

/-- **The refined local-search bound** ([BCFGJPSSV26b, Theorem 3.6]). -/
theorem refined_ls (hv : I.Valid) {N : ℕ} (hN : 200 ≤ N) {S B : Finset (Fin I.m)}
    (hS : IsALO I (24 * N) (1 / (N * I.k)) S) {μA μB : Fin I.n → Fin I.m}
    (hA : ∀ j, μA j ∈ S) (hB : ∀ j, μB j ∈ B) {D₀ : Finset (Fin I.n)}
    (hsize : B.card + (D₀ᶜ.image μA).card ≤ I.k) (hcf : CrossFreeWrt I S μA μB D₀) :
    I.costF S ≤ I.costMap μB D₀ + (I.costMap μA univ - I.costOn S D₀) +
      10 / N * (I.costMap μA univ + I.costMap μB D₀) := by
  classical
  have hk : 1 ≤ I.k := hv.one_le_k
  have hSne : S.Nonempty := by rw [← card_pos, hS.1]; omega
  set Ap := S.filter (fun c ↦ ∀ j, μA j = c → j ∈ D₀) with hAp
  have mem_Ap : ∀ j, μA j ∈ Ap ↔ ∀ j', μA j' = μA j → j' ∈ D₀ := fun j ↦ by
    simp [hAp, hA j]
  have hApS : Ap ⊆ S := filter_subset _ _
  set G : BiGraph (Fin I.m) (Fin I.m) :=
    ⟨Ap, B, fun c c' ↦ decide (∃ j, μA j = c ∧ μB j = c')⟩ with hG
  have hadj : ∀ c c', G.adj c c' = true ↔ ∃ j, μA j = c ∧ μB j = c' := fun c c' ↦ by
    simp [hG]
  have hdegL : ∀ c, G.degL c = (B.filter fun c' ↦ ∃ j, μA j = c ∧ μB j = c').card := by
    intro c; unfold BiGraph.degL; simp [hG]
  have hdegR : ∀ c', G.degR c' = (Ap.filter fun c ↦ ∃ j, μA j = c ∧ μB j = c').card := by
    intro c'; unfold BiGraph.degR; simp [hG]
  -- the cross-free structure at a client of `D̂₀`
  have hBsub : ∀ j, μA j ∈ Ap → (∀ j', μB j' = μB j → μA j' ∈ Ap → μA j' = μA j) →
      G.degR (μB j) = 1 := by
    intro j hj h
    rw [hdegR, card_eq_one]
    refine ⟨μA j, eq_singleton_iff_unique_mem.2 ⟨mem_filter.2 ⟨hj, j, rfl, rfl⟩, ?_⟩⟩
    intro c hc
    obtain ⟨hc, j', rfl, hj'⟩ := mem_filter.1 hc
    exact h j' hj' hc
  have hcf' : ∀ j, μA j ∈ Ap → (∀ j', μB j' = μB j → μA j' ∈ Ap → μA j' = μA j) ∨
      (∀ j', μA j' = μA j → μB j' = μB j) := by
    intro j hj
    rcases hcf (μA j) hj (μB j) with h | h | h
    · exfalso
      exact disjoint_left.1 h (mem_filter.2 ⟨mem_univ j, rfl⟩)
        (mem_filter.2 ⟨mem_univ j, rfl, (mem_Ap j).1 hj⟩)
    · right
      intro j' hj'
      have := h (by simp [hj'] : j' ∈ univ.filter fun i ↦ μA i = μA j)
      exact (mem_filter.1 this).2.1
    · left
      intro j' hj' hj'A
      have : j' ∈ univ.filter fun i ↦ μB i = μB j ∧ ∀ i', μA i' = μA i → i' ∈ D₀ := by
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨hj', (mem_Ap j').1 hj'A⟩
      exact (mem_filter.1 (h this)).2
  have hAsub : ∀ j, (∀ j', μA j' = μA j → μB j' = μB j) → G.degL (μA j) ≤ 1 := by
    intro j h
    rw [hdegL]
    refine card_le_one.2 fun c₁ h₁ c₂ h₂ ↦ ?_
    obtain ⟨-, j₁, hj₁, rfl⟩ := mem_filter.1 h₁
    obtain ⟨-, j₂, hj₂, rfl⟩ := mem_filter.1 h₂
    rw [h j₁ hj₁, h j₂ hj₂]
  have hstar : G.IsStarLike := by
    intro c hc c' hc' h
    obtain ⟨j, rfl, rfl⟩ := (hadj _ _).1 h
    rcases hcf' j hc with h' | h'
    · right
      rw [hBsub j hc h']
    · left
      exact hAsub j h'
  have hcard : G.R.card ≤ G.L.card := by
    change B.card ≤ Ap.card
    have h1 : S ⊆ Ap ∪ D₀ᶜ.image μA := by
      intro c hc
      by_cases h : ∀ j, μA j = c → j ∈ D₀
      · exact mem_union_left _ (mem_filter.2 ⟨hc, h⟩)
      · push Not at h
        obtain ⟨j, rfl, hj⟩ := h
        exact mem_union_right _ (mem_image.2 ⟨j, by simpa using hj, rfl⟩)
    have h2 := (card_le_card h1).trans (card_union_le _ _)
    rw [hS.1] at h2
    omega
  obtain ⟨b, hb, 𝒮, hgood, hmult⟩ := G.exists_swap_families hN hstar hcard
  have hmem : ∀ (r : Fin b) (i : Fin (𝒮 r).length), (𝒮 r)[i] ∈ 𝒮 r :=
    fun r i ↦ List.getElem_mem i.2
  have hpick : ∀ (r : Fin b) (j : Fin I.n), ∃ i : Fin (𝒮 r).length, μB j ∈ ((𝒮 r)[i]).Rs := by
    intro r j
    obtain ⟨σ, hσ, hv'⟩ := (hgood r).coverR (μB j) (hB j)
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hσ
    exact ⟨i, by simpa using hv'⟩
  choose pk hpk using hpick
  obtain ⟨X, hX⟩ : ∃ X : (r : Fin b) → Fin (𝒮 r).length → Fin I.n → Prop, ∀ r i j, X r i j ↔
      (μA j ∈ ((𝒮 r)[i]).Ls ∨ (j ∈ D₀ ∧ μB j ∈ ((𝒮 r)[i]).Rs ∧ G.degR (μB j) = 1) ∨
        (j ∈ D₀ ∧ μA j ∉ Ap ∧ G.degR (μB j) ≠ 1 ∧ pk r j = i)) := ⟨_, fun _ _ _ ↦ Iff.rfl⟩
  have hLsAp : ∀ (r : Fin b) (i : Fin (𝒮 r).length), ((𝒮 r)[i]).Ls ⊆ Ap :=
    fun r i ↦ ((hgood r).subset _ (hmem r i)).1
  set δ : ℝ := 1 / (N * I.k) with hδ
  have hδ0 : 0 ≤ δ := by positivity
  -- the test of every swap
  have hsw : ∀ (r : Fin b) (i : Fin (𝒮 r).length),
      ∑ j, (if X r i j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j)) else 0) ≤
      ∑ j, (if ¬ X r i j ∧ I.near S hSne (.inl j) ∈ ((𝒮 r)[i]).Ls then
        I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) + δ * I.costF S := by
    intro r i
    have hσ := hmem r i
    obtain ⟨hc1, hc2⟩ := (hgood r).card _ hσ
    refine swap_test hv hδ0 hS hSne hA ((hLsAp r i).trans hApS) hc1 hc2 (X r i)
      (fun j hj ↦ ?_) (fun j hj ↦ (hX r i j).2 (Or.inl hj))
    rcases (hX r i j).1 hj with h | h | h
    · exact (hgood r).closed _ hσ _ h _ (hB j) ((hadj _ _).2 ⟨j, rfl, rfl⟩)
    · exact h.2.1
    · rw [← h.2.2.2]; exact hpk r j
  -- counting
  have hcount : ∀ (r : Fin b) (P : Fin (𝒮 r).length → Prop) [DecidablePred P]
      (q : Swap (Fin I.m) (Fin I.m) → Prop) [DecidablePred q], (∀ i, P i ↔ q ((𝒮 r)[i])) →
      ∑ i, (if P i then (1 : ℝ) else 0) = ((𝒮 r).countP (fun σ ↦ decide (q σ)) : ℝ) := by
    intro r P _ q _ h
    rw [← sum_fin_countP_real]
    refine sum_congr rfl fun i _ ↦ ?_
    simp only [h i, decide_eq_true_eq]
  have hR1 : ∀ j, G.degR (μB j) = 1 → ∀ r,
      ((𝒮 r).countP (fun σ ↦ decide (μB j ∈ σ.Rs)) : ℝ) = 1 := by
    intro j h1 r
    have h1' := (hgood r).leafR (μB j) (hB j) h1.le
    obtain ⟨σ, hσ, hv'⟩ := (hgood r).coverR (μB j) (hB j)
    have h2 : 0 < (𝒮 r).countP (fun σ ↦ decide (μB j ∈ σ.Rs)) :=
      List.countP_pos_iff.2 ⟨σ, hσ, by simpa using hv'⟩
    have : (𝒮 r).countP (fun σ ↦ decide (μB j ∈ σ.Rs)) = 1 := by omega
    rw [this]
    simp
  have hcntX : ∀ j ∈ D₀, (∀ r, ∑ i, (if X r i j then (1 : ℝ) else 0) = 1) ∨
      (∃ c ∈ Ap, G.degL c ≤ 1 ∧ ∀ r, ∑ i, (if X r i j then (1 : ℝ) else 0) =
        ((𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) : ℝ)) := by
    intro j hj
    by_cases h1 : G.degR (μB j) = 1
    · left
      intro r
      rw [hcount r _ (fun σ ↦ μB j ∈ σ.Rs) (fun i ↦ ?_), hR1 j h1 r]
      rw [hX]
      constructor
      · rintro (h | h | h)
        · exact (hgood r).closed _ (hmem r i) _ h _ (hB j) ((hadj _ _).2 ⟨j, rfl, rfl⟩)
        · exact h.2.1
        · exact absurd h1 h.2.2.1
      · intro h
        exact Or.inr (Or.inl ⟨hj, h, h1⟩)
    · by_cases hjA : μA j ∈ Ap
      · right
        have h2 : G.degL (μA j) ≤ 1 := by
          rcases hcf' j hjA with h' | h'
          · exact absurd (hBsub j hjA h') h1
          · exact hAsub j h'
        refine ⟨μA j, hjA, h2, fun r ↦ hcount r _ _ fun i ↦ ?_⟩
        rw [hX]
        constructor
        · rintro (h | h | h)
          · exact h
          · exact absurd h.2.2 h1
          · exact absurd hjA h.2.1
        · exact Or.inl
      · left
        intro r
        calc ∑ i, (if X r i j then (1 : ℝ) else 0) = ∑ i, (if pk r j = i then (1 : ℝ) else 0) := by
              refine sum_congr rfl fun i _ ↦ ?_
              have : X r i j ↔ pk r j = i := by
                rw [hX]
                constructor
                · rintro (h | h | h)
                  · exact absurd (hLsAp r i h) hjA
                  · exact absurd h.2.2 h1
                  · exact h.2.2.2
                · intro h
                  exact Or.inr (Or.inr ⟨hj, hjA, h1, h⟩)
              simp only [this]
          _ = 1 := by simp
  have hb8 : (b : ℝ) ≤ (1 + 8 / N) * b := by
    have : (0 : ℝ) ≤ 8 / N := by positivity
    nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hX0 : ∀ j ∉ D₀, ∀ r i, ¬ X r i j := by
    intro j hj r i h
    rcases (hX r i j).1 h with h | h | h
    · exact hj ((mem_Ap j).1 (hLsAp r i h) j rfl)
    · exact hj h.1
    · exact hj h.1
  have hLcount : ∀ c, ∑ r, ((𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) : ℝ) ≤
      (1 + 8 / N) * b := by
    intro c
    by_cases hc : c ∈ Ap ∧ G.degL c ≤ 1
    · exact hmult c hc.1 hc.2
    · have h1 : ∀ r, ((𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) : ℝ) ≤ 1 := by
        intro r
        have : (𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) ≤ 1 := by
          by_cases hcA : c ∈ Ap
          · refine (hgood r).hubL c hcA ?_
            have := hc
            push Not at this
            have := this hcA
            omega
          · rw [List.countP_eq_zero.2]
            · omega
            · intro σ hσ
              simpa using fun h ↦ hcA (((hgood r).subset σ hσ).1 h)
        exact_mod_cast this
      calc ∑ r, ((𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) : ℝ) ≤ ∑ _r : Fin b, (1 : ℝ) :=
            sum_le_sum fun r _ ↦ h1 r
        _ = b := by simp
        _ ≤ (1 + 8 / N) * b := hb8
  have hXc : ∀ j ∈ D₀, (b : ℝ) ≤ ∑ r, ∑ i, (if X r i j then (1 : ℝ) else 0) ∧
      ∑ r, ∑ i, (if X r i j then (1 : ℝ) else 0) ≤ (1 + 8 / N) * b := by
    intro j hj
    rcases hcntX j hj with h | ⟨c, hc, hdeg, h⟩
    · simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact ⟨le_rfl, hb8⟩
    · simp only [h]
      refine ⟨?_, hmult c hc hdeg⟩
      calc (b : ℝ) = ∑ _r : Fin b, (1 : ℝ) := by simp
        _ ≤ _ := sum_le_sum fun r _ ↦ by
          obtain ⟨σ, hσ, hcσ⟩ := (hgood r).coverL c hc (by omega)
          have : 0 < (𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) :=
            List.countP_pos_iff.2 ⟨σ, hσ, by simpa using hcσ⟩
          exact_mod_cast this
  have hYc : ∀ j, ∑ r, ∑ i, (if ¬ X r i j ∧ I.near S hSne (.inl j) ∈ ((𝒮 r)[i]).Ls then
      I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) ≤
      (1 + 8 / N) * b * (I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S) := by
    intro j
    set a := I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S with ha_def
    have ha : 0 ≤ a := by
      have := Instance.dSet_le (hA j) (.inl j)
      rw [ha_def]
      linarith
    set c := I.near S hSne (.inl j)
    calc _ ≤ ∑ r, ∑ i : Fin (𝒮 r).length, (if c ∈ ((𝒮 r)[i]).Ls then a else 0) :=
          sum_le_sum fun r _ ↦ sum_le_sum fun i _ ↦ by
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd h1.2 h2
            · exact ha
            · exact le_rfl
      _ = ∑ r, ((𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) : ℝ) * a := by
          refine sum_congr rfl fun r _ ↦ ?_
          rw [← hcount r (fun i ↦ c ∈ ((𝒮 r)[i]).Ls) (fun σ ↦ c ∈ σ.Ls) (fun i ↦ Iff.rfl),
            sum_mul]
          refine sum_congr rfl fun i _ ↦ ?_
          split_ifs <;> simp
      _ = (∑ r, ((𝒮 r).countP (fun σ ↦ decide (c ∈ σ.Ls)) : ℝ)) * a := by rw [sum_mul]
      _ ≤ (1 + 8 / N) * b * a := mul_le_mul_of_nonneg_right (hLcount c) ha
  have hswap : ∀ f : (r : Fin b) → Fin (𝒮 r).length → Fin I.n → ℝ,
      ∑ r, ∑ i, ∑ j, f r i j = ∑ j, ∑ r, ∑ i, f r i j := by
    intro f
    calc ∑ r, ∑ i, ∑ j, f r i j = ∑ r, ∑ j, ∑ i, f r i j := sum_congr rfl fun r _ ↦ sum_comm
      _ = _ := sum_comm
  have hsum := sum_le_sum fun r (_ : r ∈ (univ : Finset (Fin b))) ↦
    sum_le_sum fun i (_ : i ∈ (univ : Finset (Fin (𝒮 r).length))) ↦ hsw r i
  simp only [sum_add_distrib] at hsum
  rw [hswap (fun r i j ↦ if X r i j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j)) else 0),
    hswap (fun r i j ↦ if ¬ X r i j ∧ I.near S hSne (.inl j) ∈ ((𝒮 r)[i]).Ls then
      I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0)] at hsum
  -- the left side
  have hLHS : (b : ℝ) * I.costOn S D₀ - (1 + 8 / N) * b * I.costMap μB D₀ ≤
      ∑ j, ∑ r, ∑ i, (if X r i j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j))
        else 0) := by
    have h : ∀ j, (if j ∈ D₀ then (b : ℝ) * I.dSet (.inl j) S -
        (1 + 8 / N) * b * I.dd (.inl j) (.inr (μB j)) else 0) ≤
        ∑ r, ∑ i, (if X r i j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j))
          else 0) := by
      intro j
      have heq : ∑ r, ∑ i, (if X r i j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j))
          else 0) = (∑ r, ∑ i, (if X r i j then (1 : ℝ) else 0)) *
            (I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j))) := by
        rw [sum_mul]
        refine sum_congr rfl fun r _ ↦ ?_
        rw [sum_mul]
        refine sum_congr rfl fun i _ ↦ ?_
        split_ifs <;> simp
      rw [heq]
      split_ifs with hj
      · obtain ⟨h1, h2⟩ := hXc j hj
        have hdS : 0 ≤ I.dSet (.inl j) S := Instance.dSet_nonneg hv _ _
        have hdB : 0 ≤ I.dd (.inl j) (.inr (μB j)) := Instance.dd_nonneg hv _ _
        nlinarith [mul_le_mul_of_nonneg_right h1 hdS, mul_le_mul_of_nonneg_right h2 hdB]
      · have : ∑ r, ∑ i, (if X r i j then (1 : ℝ) else 0) = 0 :=
          sum_eq_zero fun r _ ↦ sum_eq_zero fun i _ ↦ by simp [hX0 j hj r i]
        rw [this, zero_mul]
    calc (b : ℝ) * I.costOn S D₀ - (1 + 8 / N) * b * I.costMap μB D₀ =
        ∑ j, (if j ∈ D₀ then (b : ℝ) * I.dSet (.inl j) S -
          (1 + 8 / N) * b * I.dd (.inl j) (.inr (μB j)) else 0) := by
          rw [sum_ite_mem, univ_inter, sum_sub_distrib, ← mul_sum, ← mul_sum]
          rfl
      _ ≤ _ := sum_le_sum fun j _ ↦ h j
  -- the right side
  have hRHS : ∑ j, ∑ r, ∑ i, (if ¬ X r i j ∧ I.near S hSne (.inl j) ∈ ((𝒮 r)[i]).Ls then
      I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) ≤
      (1 + 8 / N) * b * (I.costMap μA univ - I.costF S) := by
    calc _ ≤ ∑ j, (1 + 8 / N) * b * (I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S) :=
          sum_le_sum fun j _ ↦ hYc j
      _ = _ := by
          rw [← mul_sum, sum_sub_distrib]
          rfl
  have hlen : ∑ r, ∑ _i : Fin (𝒮 r).length, δ * I.costF S ≤
      b * (I.k + 2) * (δ * I.costF S) := by
    have hδC : 0 ≤ δ * I.costF S := mul_nonneg hδ0 (Instance.costF_nonneg hv S)
    calc ∑ r, ∑ _i : Fin (𝒮 r).length, δ * I.costF S =
        ∑ r, ((𝒮 r).length : ℝ) * (δ * I.costF S) := by simp
      _ ≤ ∑ _r : Fin b, ((I.k : ℝ) + 2) * (δ * I.costF S) := sum_le_sum fun r _ ↦ by
          refine mul_le_mul_of_nonneg_right ?_ hδC
          have h1 := (hgood r).length
          have h2 : Ap.card ≤ S.card := card_le_card hApS
          rw [hS.1] at h2
          have h3 : (𝒮 r).length ≤ I.k + 2 := h1.trans (by change Ap.card + 2 ≤ _; omega)
          exact_mod_cast h3
      _ = _ := by simp; ring
  have hN' : (200 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h3 : ((I.k : ℝ) + 2) * δ ≤ 3 / N := by
    have hk' : (1 : ℝ) ≤ I.k := by exact_mod_cast hk
    rw [hδ, mul_one_div, div_le_div_iff₀ (by positivity) hNpos]
    nlinarith
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hC := Instance.costF_nonneg hv S
  have hkey : (b : ℝ) * (I.costOn S D₀ - (1 + 8 / N) * I.costMap μB D₀) ≤
      b * ((1 + 8 / N) * (I.costMap μA univ - I.costF S) + 3 / N * I.costF S) := by
    have h4 : (b : ℝ) * (I.k + 2) * (δ * I.costF S) ≤ b * (3 / N * I.costF S) := by
      have := mul_le_mul_of_nonneg_right h3 hC
      have := mul_le_mul_of_nonneg_left this hbpos.le
      nlinarith
    nlinarith
  have hkey' := le_of_mul_le_mul_left hkey hbpos
  have hAC : I.costF S ≤ I.costMap μA univ := by
    rw [← Instance.costOn_univ]
    exact Instance.costOn_le_costMap fun j _ ↦ hA j
  have hP : 0 ≤ I.costMap μB D₀ := sum_nonneg fun j _ ↦ Instance.dd_nonneg hv _ _
  set t : ℝ := 1 / N with ht
  have ht0 : 0 ≤ t := by positivity
  have e8 : (8 : ℝ) / N = 8 * t := by rw [ht]; ring
  have e3 : (3 : ℝ) / N = 3 * t := by rw [ht]; ring
  have e10 : (10 : ℝ) / N = 10 * t := by rw [ht]; ring
  rw [e8, e3] at hkey'
  rw [e10]
  nlinarith [mul_nonneg ht0 hC, mul_nonneg ht0 hP, mul_nonneg ht0 (sub_nonneg.2 hAC)]

end BCFGJPSSV26.Stable
