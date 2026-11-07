module

public import BCFGJPSSV26.Basic.Metric

/-!
# Approximate local optima

A set `S` of exactly `k` facilities is an **approximate local optimum** for swaps of size `p` and
improvement threshold `δ` (`BCFGJPSSV26.Stable.IsALO`) if no nonempty set `T` of at most `k`
facilities with `|S \ T| ≤ p` costs less than `(1 - δ) cost(S)`. The local search of
`BCFGJPSSV26/Stable/Alg/LocalSearch.lean` stops at one, with `p = 24 N` and `δ = 1/(N k)`.
It checks only the sets `T` of exactly `k` facilities, which suffices
(`BCFGJPSSV26.Stable.isALO_of_card_eq`): adding facilities of `S \ T` to a smaller
`T` lowers its cost and keeps `|S \ T| ≤ p`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

variable (I) in
/-- **Approximate local optimality**: `|S| = k`, and every nonempty `T` with `|T| ≤ k` and
`|S \ T| ≤ p` costs at least `(1 - δ) cost(S)`. -/
def IsALO (p : ℕ) (δ : ℝ) (S : Finset (Fin I.m)) : Prop :=
  S.card = I.k ∧ ∀ T : Finset (Fin I.m), T.Nonempty → T.card ≤ I.k → (S \ T).card ≤ p →
    (1 - δ) * I.costF S ≤ I.costF T

/-- **Swaps to sets of exactly `k` facilities suffice.** -/
theorem isALO_of_card_eq (hv : I.Valid) {p : ℕ} {δ : ℝ} {S : Finset (Fin I.m)}
    (hS : S.card = I.k)
    (h : ∀ T : Finset (Fin I.m), T.card = I.k → (S \ T).card ≤ p →
      (1 - δ) * I.costF S ≤ I.costF T) : IsALO I p δ S := by
  classical
  refine ⟨hS, fun T hT hTk hST ↦ ?_⟩
  have hcard : I.k ≤ (T ∪ S).card := hS ▸ card_le_card subset_union_right
  obtain ⟨T', hTT', hT'S, hT'⟩ := exists_subsuperset_card_eq subset_union_left hTk hcard
  have hST' : (S \ T').card ≤ p :=
    (card_le_card (sdiff_subset_sdiff (subset_refl S) hTT')).trans hST
  exact (h T' hT' hST').trans (Instance.costF_anti hv hTT')

end BCFGJPSSV26.Stable
