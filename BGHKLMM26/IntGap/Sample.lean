module

public import BGHKLMM26.Hardness.SparsifyMain

/-!
# Sampling preserves an average over the edges

`BGHKLMM26.IntGap.sparsify_yes_score`: the completeness of the sparsification
(`BGHKLMM26.Hard.sparsify_yes`) for any symmetric edge score `h` with values in `[0, 1]` in place
of a cut: if the law of a decoded edge has mean score at least `c`, then with probability `9/10`
the sampled graph has average score over its edges (`BGHKLMM26.IntGap.edgeAvg`) at least
`c - C₀/D`. The proof is that of `sparsify_yes`: Hoeffding for the sum of the scores of the
`nD` samples (`BGHKLMM26.Hard.frac_sum_le_le`), at most `180 n` dropped samples with probability
`19/20` (`BGHKLMM26.Hard.frac_drops_ge_le`), and the kept samples are the edges of the graph,
each once (`BGHKLMM26.Hard.simpleList_keptEdges`), each of score at most `1`.

The SDP value of a solution is the average of the score `‖vᵢ - vⱼ‖²/4`
(`BGHKLMM26.IntGap.sdpValue_eq_edgeAvg`).
-/

@[expose] public section

namespace BGHKLMM26.IntGap

open Finset Hard

/-- The simple graph of the samples, on `Fin n` (so that statements about it need not unfold
`n`). -/
def sgraph (n Δ : ℕ) {Ω : Type} {S : ℕ} (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) :
    SimpleGraph (Fin n) :=
  (sampledGraph n Δ dec ω).2

theorem sampledGraph_eq (n Δ : ℕ) {Ω : Type} {S : ℕ} (dec : Ω → Fin n × Fin n)
    (ω : Fin S → Ω) : sampledGraph n Δ dec ω = ⟨n, sgraph n Δ dec ω⟩ := rfl

open Classical in
/-- The average over the edges `{i, j}` of a graph of `(h i j + h j i) / 2`, and `0` without
edges. -/
noncomputable def edgeAvg (H : Graph) (h : Fin H.1 → Fin H.1 → ℝ) : ℝ :=
  (∑ e ∈ H.2.edgeFinset,
    Sym2.lift ⟨fun i j ↦ (h i j + h j i) / 2, fun i j ↦ by dsimp only; ring⟩ e) /
    H.2.edgeFinset.card

/-- The SDP value is the average of a score that agrees with `‖vᵢ - vⱼ‖²/4` off the diagonal. -/
theorem sdpValue_eq_edgeAvg (H : Graph) (v : Fin H.1 → EuclideanSpace ℝ (Fin H.1))
    (h : Fin H.1 → Fin H.1 → ℝ) (hh : ∀ i j, i ≠ j → (h i j + h j i) / 2 = ‖v i - v j‖ ^ 2 / 4) :
    sdpValue H v = edgeAvg H h := by
  classical
  unfold sdpValue edgeAvg
  congr 1
  refine Finset.sum_congr rfl fun e he ↦ ?_
  induction e using Sym2.ind with
  | _ i j =>
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
  simp only [Sym2.lift_mk]
  exact (hh i j he.ne).symm

/-- Dropping entries of a list of `[0, 1]` values lowers its sum by at most the number of dropped
entries. -/
theorem sum_map_le_of_sublist {α : Type*} {l₁ l₂ : List α} (hs : List.Sublist l₁ l₂)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    (l₂.map f).sum ≤ (l₁.map f).sum + ((l₂.length : ℝ) - l₁.length) := by
  induction hs with
  | slnil => simp
  | cons a _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith [hf a]
  | cons_cons a _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

/-- Sums over the edges of `graphOf n kept` are sums over the kept pairs. -/
theorem sum_edgeFinset_graphOf {n : ℕ} {kept : List (ℕ × ℕ)}
    (hin : ∀ p ∈ kept, p.1 < n ∧ p.2 < n) (hs : SimpleList kept)
    {_ : Fintype (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).edgeSet}
    (g : Sym2 (Fin n) → ℝ) (g' : ℕ × ℕ → ℝ)
    (hg : ∀ a b : Fin n, a ≠ b → g s(a, b) = g' (a.1, b.1)) :
    ∑ e ∈ (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).edgeFinset, g e =
      (kept.map g').sum := by
  classical
  obtain ⟨hl, hn, hr⟩ := hs
  rw [← List.sum_toFinset g' hn]
  symm
  refine Finset.sum_bij (fun p hp ↦
      s(⟨p.1, (hin p (List.mem_toFinset.1 hp)).1⟩, ⟨p.2, (hin p (List.mem_toFinset.1 hp)).2⟩))
    ?_ ?_ ?_ ?_
  · intro p hp
    rw [List.mem_toFinset] at hp
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.fromRel_adj]
    have hne : (⟨p.1, (hin p hp).1⟩ : Fin n) ≠ ⟨p.2, (hin p hp).2⟩ :=
      fun h ↦ hl p hp (congrArg Fin.val h)
    exact ⟨hne, Or.inl hp⟩
  · intro p hp q hq hpq
    rw [List.mem_toFinset] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Fin.mk.injEq] at h1 h2
      exact Prod.ext h1 h2
    · simp only [Fin.mk.injEq] at h1 h2
      exact absurd (show (q.2, q.1) ∈ kept by rw [← h1, ← h2]; exact hp) (hr q hq)
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.fromRel_adj] at he
    obtain ⟨hab, h | h⟩ := he
    · exact ⟨(a.1, b.1), List.mem_toFinset.2 h, rfl⟩
    · exact ⟨(b.1, a.1), List.mem_toFinset.2 h, Sym2.eq_swap⟩
  · intro p hp
    rw [List.mem_toFinset] at hp
    rw [hg _ _ fun h ↦ hl p hp (congrArg Fin.val h)]

/-- A score on `Fin n`, read on pairs of numbers (`0` outside `Fin n`). -/
noncomputable def scoreN {n : ℕ} (h : Fin n → Fin n → ℝ) (p : ℕ × ℕ) : ℝ :=
  if hp : p.1 < n ∧ p.2 < n then h ⟨p.1, hp.1⟩ ⟨p.2, hp.2⟩ else 0

/-- `scoreN h` takes values in `[0, 1]` when `h` does. -/
theorem scoreN_mem {n : ℕ} {h : Fin n → Fin n → ℝ} (h01 : ∀ i j, 0 ≤ h i j ∧ h i j ≤ 1)
    (p : ℕ × ℕ) : 0 ≤ scoreN h p ∧ scoreN h p ≤ 1 := by
  unfold scoreN
  split_ifs
  · exact h01 _ _
  · norm_num

/-- On `Fin n`, `scoreN h` is `h`. -/
theorem scoreN_val {n : ℕ} (h : Fin n → Fin n → ℝ) (a b : Fin n) :
    scoreN h (a.1, b.1) = h a b := by
  simp [scoreN, a.2, b.2]

/-- **A lower bound on the average score** of the sampled graph: the total score of the samples,
minus the number of dropped samples, over `S`. -/
theorem sum_sub_drops_le_edgeAvg {n : ℕ} (Δ : ℕ) {Ω : Type} {S : ℕ} (dec : Ω → Fin n × Fin n)
    (ω : Fin S → Ω) (h : Fin n → Fin n → ℝ) (h01 : ∀ i j, 0 ≤ h i j ∧ h i j ≤ 1)
    (hsym : ∀ i j, h i j = h j i) :
    ∑ i, h (dec (ω i)).1 (dec (ω i)).2 - drops Δ dec ω ≤ S * edgeAvg ⟨n, sgraph n Δ dec ω⟩ h := by
  classical
  have hsum : ∑ i, h (dec (ω i)).1 (dec (ω i)).2 =
      ((List.ofFn (sampleEdge dec ω)).map (scoreN h)).sum := by
    rw [List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Function.comp_apply, sampleEdge, scoreN_val]
  have hsub := sum_map_le_of_sublist (keptEdges_sublist Δ (List.ofFn (sampleEdge dec ω)))
    (scoreN h) (scoreN_mem h01)
  rw [List.length_ofFn] at hsub
  change _ ≤ ((keptS Δ dec ω).map (scoreN h)).sum + ((S : ℝ) - (keptS Δ dec ω).length) at hsub
  have hedge : ∑ e ∈ (sgraph n Δ dec ω).edgeFinset,
      Sym2.lift ⟨fun i j ↦ (h i j + h j i) / 2, fun i j ↦ by dsimp only; ring⟩ e =
      ((keptS Δ dec ω).map (scoreN h)).sum := by
    refine sum_edgeFinset_graphOf (keptS_lt Δ dec ω) (simpleList_keptEdges Δ _) _ _ ?_
    intro a b _
    rw [Sym2.lift_mk]
    dsimp only
    rw [scoreN_val, hsym b a]
    ring
  have hcard : (sgraph n Δ dec ω).edgeFinset.card = (keptS Δ dec ω).length :=
    card_edgeFinset_graphOf (keptS_lt Δ dec ω) (simpleList_keptEdges Δ _)
  unfold edgeAvg
  dsimp only
  rw [hedge, hcard, drops_cast, hsum]
  have hk := length_keptS_le Δ dec ω
  have hK0 : 0 ≤ ((keptS Δ dec ω).map (scoreN h)).sum :=
    List.sum_nonneg fun x hx ↦ by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      exact (scoreN_mem h01 p).1
  rcases Nat.eq_zero_or_pos (keptS Δ dec ω).length with h0 | h0
  · rw [List.length_eq_zero_iff.1 h0] at hsub ⊢
    simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.cast_zero] at hsub ⊢
    linarith
  · have hpos : (0 : ℝ) < (keptS Δ dec ω).length := by exact_mod_cast h0
    have hkS : ((keptS Δ dec ω).length : ℝ) ≤ S := by exact_mod_cast hk
    have : ((keptS Δ dec ω).map (scoreN h)).sum ≤
        S * (((keptS Δ dec ω).map (scoreN h)).sum / (keptS Δ dec ω).length) := by
      rw [mul_div_assoc', le_div_iff₀ hpos, mul_comm]
      exact mul_le_mul_of_nonneg_right hkS hK0
    linarith

/-- **Completeness of the sparsification for scores.** -/
theorem sparsify_yes_score : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ D : ℕ, 1 ≤ D → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ Δ : ℕ, 10 * D ≤ Δ → ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (dec : Ω → Fin n × Fin n),
      (∀ a, frac (fun ω ↦ (dec ω).1 = a ∨ (dec ω).2 = a) ≤ 3 / n) →
      (∀ e, frac (fun ω ↦ dec ω = e) ≤ 1 / (n * D ^ 2)) →
      ∀ h : Fin n → Fin n → ℝ, (∀ i j, 0 ≤ h i j ∧ h i j ≤ 1) → (∀ i j, h i j = h j i) →
      ∀ c : ℝ, c ≤ mean (fun ω ↦ h (dec ω).1 (dec ω).2) →
        9 / 10 ≤ frac fun ω : Fin (n * D) → Ω ↦
          c - C₀ / D ≤ edgeAvg ⟨n, sgraph n Δ dec ω⟩ h := by
  refine ⟨181, by norm_num, fun D hD ↦ ⟨3 * D, fun n hn Δ hΔ Ω _ _ dec htouch hmax h h01 hsym c
    hc ↦ ?_⟩⟩
  have hn0 : 0 < n := Fin.pos (dec (Classical.arbitrary Ω)).1
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hD0 : (0 : ℝ) < D := by linarith
  have hS : ((n * D : ℕ) : ℝ) = n * D := by push_cast; ring
  have hSpos : (0 : ℝ) < n * D := by positivity
  -- the bad events
  have hB1 := frac_sum_le_le (fun x ↦ h (dec x).1 (dec x).2) (fun x ↦ h01 _ _) (n * D)
    (t := 1 / D) (by positivity)
  have hB1' : Real.exp (-2 * ((n * D : ℕ) : ℝ) * (1 / D) ^ 2) ≤ 1 / 20 := by
    rw [hS]
    have h3 : (3 * D : ℝ) ≤ n := by exact_mod_cast hn
    have : -2 * (n * D : ℝ) * (1 / D) ^ 2 = -(2 * n / D) := by field_simp
    rw [this]
    have h6 : (6 : ℝ) ≤ 2 * n / D := by rw [le_div_iff₀ hD0]; linarith
    have := Real.quadratic_le_exp_of_nonneg (x := 2 * n / D) (by positivity)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    nlinarith
  have hB2 := frac_drops_ge_le hD hΔ dec htouch hmax
  have hU := frac_or_le (fun ω : Fin (n * D) → Ω ↦
      ∑ i, h (dec (ω i)).1 (dec (ω i)).2 ≤
        ((n * D : ℕ) : ℝ) * (mean (fun x ↦ h (dec x).1 (dec x).2) - 1 / D))
    (fun ω ↦ (180 * n : ℝ) ≤ drops Δ dec ω)
  have hgood : ∀ ω : Fin (n * D) → Ω,
      ¬ (∑ i, h (dec (ω i)).1 (dec (ω i)).2 ≤
          ((n * D : ℕ) : ℝ) * (mean (fun x ↦ h (dec x).1 (dec x).2) - 1 / D) ∨
        (180 * n : ℝ) ≤ drops Δ dec ω) → c - 181 / D ≤ edgeAvg ⟨n, sgraph n Δ dec ω⟩ h := by
    intro ω hω
    push Not at hω
    obtain ⟨h1, h2⟩ := hω
    rw [hS] at h1
    have h3 := sum_sub_drops_le_edgeAvg Δ dec ω h h01 hsym
    rw [hS] at h3
    have h4 : (n * D : ℝ) * (c - 181 / D) ≤ n * D * edgeAvg ⟨n, sgraph n Δ dec ω⟩ h := by
      have : (n * D : ℝ) * (c - 181 / D) = n * D * (c - 1 / D) - 180 * n := by
        field_simp
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hc (le_of_lt hSpos)
      nlinarith
    exact le_of_mul_le_mul_left h4 hSpos
  calc (9 / 10 : ℝ) ≤ 1 - (1 / 20 + 1 / 20) := by norm_num
    _ ≤ 1 - frac (fun ω : Fin (n * D) → Ω ↦
        ∑ i, h (dec (ω i)).1 (dec (ω i)).2 ≤
          ((n * D : ℕ) : ℝ) * (mean (fun x ↦ h (dec x).1 (dec x).2) - 1 / D) ∨
          (180 * n : ℝ) ≤ drops Δ dec ω) := by linarith
    _ = frac (fun ω : Fin (n * D) → Ω ↦
        ¬ (∑ i, h (dec (ω i)).1 (dec (ω i)).2 ≤
          ((n * D : ℕ) : ℝ) * (mean (fun x ↦ h (dec x).1 (dec x).2) - 1 / D) ∨
          (180 * n : ℝ) ≤ drops Δ dec ω)) := (frac_not_eq _).symm
    _ ≤ _ := frac_imp_le hgood

end BGHKLMM26.IntGap
