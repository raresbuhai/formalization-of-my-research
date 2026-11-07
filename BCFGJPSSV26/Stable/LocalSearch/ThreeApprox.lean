module

public import BCFGJPSSV26.Stable.LocalSearch.Refined

/-!
# Local search is a `3 + O(1/N)`-approximation

[BCFGJPSSV26b, Corollary 1.5]: an approximate local optimum `S` with swaps
of size `24 N` and threshold `1/(N k)`, `N ≥ 201`, costs at most `(3 + 100/N) opt k ≤ 4 opt k`
(`BCFGJPSSV26.Stable.costF_le_three_add`, `BCFGJPSSV26.Stable.costF_le_four_opt`).

Proof: the refined bound (`BCFGJPSSV26.Stable.refined_ls`) with `B = O` optimal, `D₀` all
clients, `μB = near(O, ·)` and `μA = near(S, near(O, ·))`, which are cross-free since every
`A`-cluster is a union of `O`-clusters (`BCFGJPSSV26.Stable.crossFree_near_near`), and
`cost(μA) ≤ cost(S) + 2 opt` by the triangle inequality through the optimal centers
(`BCFGJPSSV26.Stable.costMap_near_near_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

/-- `μA = near(S, near(O, ·))` and `μB = near(O, ·)` are cross-free with respect to all clients:
every `A`-cluster is a union of `O`-clusters. -/
theorem crossFree_near_near {S O : Finset (Fin I.m)} (hS : S.Nonempty) (hO : O.Nonempty) :
    CrossFreeWrt I S (fun j ↦ I.near S hS (.inr (I.near O hO (.inl j))))
      (fun j ↦ I.near O hO (.inl j)) univ := by
  intro c _ c'
  by_cases h : I.near S hS (.inr c') = c
  · refine Or.inr (Or.inr fun j hj ↦ ?_)
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rw [hj.1, h]
  · refine Or.inl (disjoint_left.2 fun j hj hj' ↦ h ?_)
    simp only [mem_filter, mem_univ, true_and] at hj hj'
    rw [← hj'.1]
    exact hj

/-- `cost(near(S, near(O, ·))) ≤ cost(S) + 2 cost(O)`: a client `j` with optimal center `o` pays
at most `d(j, o) + d(o, S)`, and `∑_j d(o_j, S) ≤ cost(O) + cost(S)`. -/
theorem costMap_near_near_le (hv : I.Valid) {S O : Finset (Fin I.m)} (hS : S.Nonempty)
    (hO : O.Nonempty) :
    I.costMap (fun j ↦ I.near S hS (.inr (I.near O hO (.inl j)))) univ ≤
      I.costF S + 2 * I.costF O := by
  unfold Instance.costMap Instance.costF
  rw [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun j _ ↦ ?_
  set o := I.near O hO (.inl j)
  have h1 := Instance.dd_triangle hv (.inl j) (.inr o) (.inr (I.near S hS (.inr o)))
  have h2 : I.dd (.inl j) (.inr o) = I.dSet (.inl j) O := Instance.dd_near hO _
  have h3 : I.dd (.inr o) (.inr (I.near S hS (.inr o))) = I.dSet (.inr o) S :=
    Instance.dd_near hS _
  have h4 := Instance.dSet_triangle hv (.inr o) (.inl j) S
  rw [Instance.dd_comm hv, h2] at h4
  linarith

/-- **Local search is a `(3 + 100/N)`-approximation.** -/
theorem costF_le_three_add (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ} (hN : 201 ≤ N)
    {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S) :
    I.costF S ≤ (3 + 100 / N) * I.opt I.k := by
  obtain ⟨O, hO⟩ := Instance.exists_isOpt hv hk
  have hOne := hO.nonempty hv
  have hSne : S.Nonempty := by
    rw [← card_pos, hS.1]
    exact hv.one_le_k
  set μB : Fin I.n → Fin I.m := fun j ↦ I.near O hOne (.inl j)
  set μA : Fin I.n → Fin I.m := fun j ↦ I.near S hSne (.inr (μB j))
  have hsize : O.card + ((univ : Finset (Fin I.n))ᶜ.image μA).card ≤ I.k := by
    simp [hO.card]
  have h := refined_ls hv (by omega) hS (μA := μA) (μB := μB)
    (fun j ↦ Instance.near_mem hSne _) (fun j ↦ Instance.near_mem hOne _) hsize
    (crossFree_near_near hSne hOne)
  have hB : I.costMap μB univ = I.opt I.k := by
    rw [← hO.cost]
    exact sum_congr rfl fun j _ ↦ Instance.dd_near hOne _
  have hA : I.costMap μA univ ≤ I.costF S + 2 * I.opt I.k := by
    rw [← hO.cost]
    exact costMap_near_near_le hv hSne hOne
  rw [hB, Instance.costOn_univ] at h
  have hopt := Instance.opt_nonneg' hv I.k
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set t : ℝ := 10 / N with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 10 / 201 := by
    rw [ht]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN'
  have h100 : (100 : ℝ) / N = 10 * t := by rw [ht]; ring
  rw [h100]
  have hc := Instance.costF_nonneg hv S
  have h1 : I.costF S ≤ 3 * I.opt I.k + t * (I.costF S + 3 * I.opt I.k) := by
    have := mul_le_mul_of_nonneg_left (add_le_add_right hA (I.opt I.k)) ht0.le
    nlinarith
  have h2 : (1 - t) * I.costF S ≤ (1 - t) * ((3 + 10 * t) * I.opt I.k) := by
    nlinarith [mul_nonneg (mul_nonneg ht0.le (by linarith : (0 : ℝ) ≤ 4 - 10 * t)) hopt]
  exact le_of_mul_le_mul_left h2 (by linarith)

/-- **Local search is a `4`-approximation.** -/
theorem costF_le_four_opt (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ} (hN : 201 ≤ N)
    {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S) :
    I.costF S ≤ 4 * I.opt I.k := by
  have h := costF_le_three_add hv hk hN hS
  have hopt := Instance.opt_nonneg' hv I.k
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  have : (100 : ℝ) / N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  nlinarith

end BCFGJPSSV26.Stable
