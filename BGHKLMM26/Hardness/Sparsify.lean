module

public import BGHKLMM26.Hardness.Defs

/-!
# Sparsification

[BGHKLMM26, Section 6], for an abstract dense graph: the law of a decoder `dec : Ω → [n] × [n]`
from a finite uniform space `Ω`. Sample `n D` edges independently, drop loops and repeated edges,
and cap the degrees at `Δ ≥ 10 D` greedily (`BGHKLMM26.Hard.sampledGraph`).

* `BGHKLMM26.Hard.maxDegree_sampledGraph`: the result has maximum degree at most `Δ` (the greedy
  step keeps `degIn kept a ≤ Δ`, and the degree of `a` is at most the number of kept pairs at `a`).
* `BGHKLMM26.Hard.sparsify_yes` (completeness, Lemma 6.2, in `SparsifyMain.lean`): a cut of weight
  `c` in the dense graph gives Max-Cut value at least `c - C₀/D` with probability `9/10`.
* `BGHKLMM26.Hard.sparsify_no` (soundness, Lemmas 6.5–6.7, in `SparsifyMain.lean`): if every cut
  has weight at most
  `s + λ/2`, `λ = K log² D / D` with `K = 2 (96 C₁² + 16)`, and every cut of weight at least
  `s - η` is within `C₁ √(η log(1/η)) n` vertices of one of at most `exp(n/A₀)` given cuts, then
  the Max-Cut value is at most `s + C₀ λ` with probability `9/10`. (The paper's robust inverse
  gives `C √η` and takes `λ = log² D / D`; with Eldan's `√(η log(1/η))` the scale `K log² D / D`
  still suffices.)

The hypotheses on the law: each vertex is an end of a sampled edge with probability at most `3/n`,
and each ordered pair has probability at most `1/(n D²)` (so that few edges repeat).

The two probabilistic statements are in `BGHKLMM26/Hardness/SparsifyMain.lean`, which can use the
tail bounds of `BGHKLMM26/Hardness/Concentration.lean` (which imports this file); see also
`SparsifyGraph.lean` (the kept edges, the dropped samples, and the Max-Cut value of the sampled
graph), `SparsifyProb.lean` (few samples are dropped, Lemmas 6.9 and 6.10) and `SparsifyArith.lean`
(the arithmetic of the dyadic levels).
-/

@[expose] public section

namespace BGHKLMM26.Hard

open Finset
open scoped BigOperators

open Classical in
/-- The fraction of a finite type on which `p` holds. -/
noncomputable def frac {β : Type*} [Fintype β] (p : β → Prop) : ℝ :=
  ((univ.filter p).card : ℝ) / Fintype.card β

/-- The weight of the edges cut by `f` in the dense graph given by the law of `dec`. -/
noncomputable def lawCut {Ω : Type} [Fintype Ω] {n : ℕ} (dec : Ω → Fin n × Fin n)
    (f : Fin n → Bool) : ℝ :=
  frac fun ω ↦ f (dec ω).1 ≠ f (dec ω).2

/-- The sparse graph from the samples `ω`. -/
def sampledGraph (n Δ : ℕ) {Ω : Type} {S : ℕ} (dec : Ω → Fin n × Fin n) (ω : Fin S → Ω) : Graph :=
  graphOf n (keptEdges Δ (List.ofFn fun i ↦ ((dec (ω i)).1.val, (dec (ω i)).2.val)))

/-- The constant `K = 2 (96 C₁² + 16)` of the smallest level `λ = K log² D / D`. -/
def lamK (C₁ : ℝ) : ℝ := 2 * (96 * C₁ ^ 2 + 16)

/-- The smallest level `λ = K log² D / D` of the multiscale union bound, `K = lamK C₁` for the
constant `C₁` of the robust inverse. -/
noncomputable def lam (C₁ : ℝ) (D : ℕ) : ℝ := lamK C₁ * Real.log D ^ 2 / D

/-- Appending a pair adds one to the count at each of its ends. -/
theorem degIn_append_single (kept : List (ℕ × ℕ)) (e : ℕ × ℕ) (a : ℕ) :
    degIn (kept ++ [e]) a = degIn kept a + if e.1 = a ∨ e.2 = a then 1 else 0 := by
  unfold degIn
  rw [List.filter_append, List.length_append]
  by_cases h : e.1 = a ∨ e.2 = a <;> simp [h]

/-- A greedy step keeps every count at most `Δ`. -/
theorem degIn_keepStep_le (Δ : ℕ) (kept : List (ℕ × ℕ)) (e : ℕ × ℕ)
    (h : ∀ a, degIn kept a ≤ Δ) (a : ℕ) : degIn (keepStep Δ kept e) a ≤ Δ := by
  unfold keepStep
  split_ifs with hk
  · rw [degIn_append_single]
    simp only [keepOK, Bool.and_eq_true, decide_eq_true_eq] at hk
    split_ifs with he
    · rcases he with he | he <;> subst he <;> omega
    · simpa using h a
  · exact h a

theorem degIn_foldl_le (Δ : ℕ) (es : List (ℕ × ℕ)) :
    ∀ kept : List (ℕ × ℕ), (∀ a, degIn kept a ≤ Δ) →
      ∀ a, degIn (es.foldl (keepStep Δ) kept) a ≤ Δ := by
  induction es with
  | nil => intro kept h; simpa using h
  | cons e es ih =>
    intro kept h
    exact ih _ (degIn_keepStep_le Δ kept e h)

/-- Every vertex has at most `Δ` kept pairs. -/
theorem degIn_keptEdges_le (Δ : ℕ) (es : List (ℕ × ℕ)) (a : ℕ) :
    degIn (keptEdges Δ es) a ≤ Δ :=
  degIn_foldl_le Δ es [] (fun a ↦ by simp [degIn]) a

/-- The degree of a vertex of `graphOf n kept` is at most the number of kept pairs at it. -/
theorem degree_graphOf_le (n : ℕ) (kept : List (ℕ × ℕ)) (v : Fin n)
    [Fintype ((SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).neighborSet v)] :
    (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).degree v ≤ degIn kept v.1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hN : (SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).neighborFinset v =
      univ.filter ((SimpleGraph.fromRel fun a b : Fin n ↦ (a.1, b.1) ∈ kept).Adj v) := by
    ext; simp
  rw [hN]
  unfold degIn
  refine le_trans ?_ (List.toFinset_card_le _)
  refine Finset.card_le_card_of_injOn
    (fun b ↦ if (v.1, b.1) ∈ kept then (v.1, b.1) else (b.1, v.1)) ?_ ?_
  · intro b hb
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
      SimpleGraph.fromRel_adj] at hb
    simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    split_ifs with h
    · exact ⟨h, Or.inl rfl⟩
    · exact ⟨hb.2.resolve_left h, Or.inr rfl⟩
  · intro b hb b' hb' hbb
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq,
      SimpleGraph.fromRel_adj] at hb hb'
    have h1 : v.1 ≠ b.1 := fun h ↦ hb.1 (Fin.ext h)
    have h2 : v.1 ≠ b'.1 := fun h ↦ hb'.1 (Fin.ext h)
    simp only at hbb
    split_ifs at hbb <;> simp only [Prod.mk.injEq] at hbb <;> apply Fin.ext <;> omega

/-- The greedy simplification caps the degrees. -/
theorem maxDegree_graphOf_keptEdges (n Δ : ℕ) (es : List (ℕ × ℕ)) :
    MaxDegreeAtMost (graphOf n (keptEdges Δ es)) Δ := by
  classical
  intro v
  exact (degree_graphOf_le n _ v).trans (degIn_keptEdges_le Δ es v.1)

theorem maxDegree_sampledGraph (n Δ : ℕ) {Ω : Type} {S : ℕ} (dec : Ω → Fin n × Fin n)
    (ω : Fin S → Ω) : MaxDegreeAtMost (sampledGraph n Δ dec ω) Δ :=
  maxDegree_graphOf_keptEdges n Δ _

end BGHKLMM26.Hard
