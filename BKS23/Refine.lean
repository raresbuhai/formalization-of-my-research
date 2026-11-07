module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The refinement

[BKS23, Claim 5.9], deterministically and without `p`: if a set `S` differs from the planted
clique `U` in few vertices and every vertex outside `U` has many non-neighbours in `U`, then the
vertices with at least `τ` neighbours in `S` are exactly `U`, for some `τ ≤ n`
(`BKS23.Refine.exists_threshold`). A vertex of `U` has at least `|S ∩ U| - 1` neighbours in `S`;
a vertex outside `U` has at most `|U| - N₀ + |S ∖ U|`.
-/

@[expose] public section

namespace BKS23.Refine

open Finset

variable {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- **The refinement** [BKS23, Claim 5.9]. If `U` is a `k`-clique of `G`, every vertex outside `U`
has at least `N₀` non-neighbours in `U`, and `|S ∖ U| + |U ∖ S| + 1 < N₀`, then some threshold
`τ ≤ n` has `{v | τ ≤ |N(v) ∩ S|} = U`. -/
theorem exists_threshold {U S : Finset (Fin n)} (hU : G.IsNClique k U) {N₀ : ℕ}
    (hnon : ∀ v ∉ U, N₀ ≤ (U.filter fun u ↦ ¬ G.Adj u v).card)
    (hsmall : (S \ U).card + (U \ S).card + 1 < N₀) :
    ∃ τ ≤ n, (univ.filter fun v ↦ τ ≤ (S.filter fun u ↦ G.Adj u v).card) = U := by
  set τ := (U ∩ S).card - 1 with hτ
  have hUn : U.card ≤ n := by simpa using card_le_univ U
  refine ⟨τ, ?_, ?_⟩
  · have : (U ∩ S).card ≤ U.card := card_le_card inter_subset_left
    omega
  ext v
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · -- A vertex outside `U` has too few neighbours in `S`.
    intro hv
    by_contra hvU
    have hN := hnon v hvU
    -- `|N(v) ∩ S| ≤ |N(v) ∩ U| + |S ∖ U|` and `|N(v) ∩ U| = |U| - |non-neighbours|`.
    have h1 : (S.filter fun u ↦ G.Adj u v).card ≤
        (U.filter fun u ↦ G.Adj u v).card + (S \ U).card := by
      have hsub : S.filter (fun u ↦ G.Adj u v) ⊆ U.filter (fun u ↦ G.Adj u v) ∪ (S \ U) := by
        intro u hu
        rw [mem_filter] at hu
        by_cases huU : u ∈ U
        · exact mem_union_left _ (mem_filter.2 ⟨huU, hu.2⟩)
        · exact mem_union_right _ (mem_sdiff.2 ⟨hu.1, huU⟩)
      exact (card_le_card hsub).trans (card_union_le _ _)
    have h2 := card_filter_add_card_filter_not (s := U) (fun u ↦ G.Adj u v)
    have h3 : (U ∩ S).card + (U \ S).card = U.card := card_inter_add_card_sdiff U S
    omega
  · -- A vertex of `U` is adjacent to every other vertex of `U ∩ S`.
    intro hv
    have hsub : (U ∩ S).erase v ⊆ S.filter fun u ↦ G.Adj u v := by
      intro u hu
      obtain ⟨huv, hu⟩ := mem_erase.1 hu
      exact mem_filter.2 ⟨(mem_inter.1 hu).2, hU.isClique (mem_inter.1 hu).1 hv huv⟩
    have := card_le_card hsub
    have h' : (U ∩ S).card - 1 ≤ ((U ∩ S).erase v).card := by
      rw [card_erase_eq_ite]
      split_ifs <;> omega
    omega

end BKS23.Refine
