module

public import BCFGJPSSV26.Stable.Stability.Defs

/-!
# Substitutes for synced and close clusters

* [BCFGJPSSV26b, Proposition 4.3] (`BCFGJPSSV26.Stable.Hyp.syncSub`): the synced clusters, sent
  to their partners, cost at most `(1 + 4ε) ∑_{O_sync} cost_OPT(C*) + 5 ε cost(S)`. The proof
  adapts that of [CGLSS25, Lemma 4.4] to `ε`-synced clusters and approximate local optima: it
  swaps the partner `c'` for `c*` (one swap, allowed by approximate local optimality): the
  clients of `C* ∩ C_{c'}` move to `c*`, those of `C_{c'} \ C*` too at cost at most
  `d(j, S) + d(c', c*)`, with `d(c', c*)` at most the average of `d(·, S) + d(·, c*)` over
  `C* ∩ C_{c'}`; the error `cost(S)/(N k)` per swap sums to `ε cost(S)` over the `k` swaps.
* [BCFGJPSSV26b, Proposition 4.4] (`BCFGJPSSV26.Stable.Hyp.closeSub`): a close cluster sent to
  the nearest local-search center of its center costs at most
  `(1 + η) cost_OPT(C*) + 2 ε cost_S(C*)`, by the triangle inequality through `c*`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- The optimal clusters are disjoint, so their local-search costs add up to at most
`cost(S)`. -/
private theorem sum_costS_C_le (A : Finset (Fin X.I.m)) :
    ∑ c ∈ A, X.costS (X.C c) ≤ X.I.costF X.S := by
  classical
  have hdisj : (A : Set (Fin X.I.m)).PairwiseDisjoint X.C :=
    fun c _ c' _ h ↦ Instance.disjoint_cluster _ h
  calc ∑ c ∈ A, X.costS (X.C c) = X.I.costOn X.S (A.biUnion X.C) := by
        change ∑ c ∈ A, ∑ j ∈ X.C c, X.I.dSet (.inl j) X.S =
          ∑ j ∈ A.biUnion X.C, X.I.dSet (.inl j) X.S
        rw [sum_biUnion hdisj]
    _ ≤ X.I.costF X.S := Instance.costOn_le_costF H.valid _ _

/-- The swap `T = (S \ {c'}) ∪ {c*}` of a synced center `c*` with its partner `c'`: by approximate
local optimality, the clients of `C* ∩ C_{c'}` pay in `S` at most their distance to `c*`, plus
`|C_{c'} \ C*| d(c', c*)` and the error `cost(S)/(N k)`. -/
private theorem swap_bound {c c' : Fin X.I.m} (hc'S : c' ∈ X.S) :
    ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S ≤ ∑ j ∈ X.C c ∩ X.CS c', X.dist j c +
      (X.CS c' \ X.C c).card * X.dF c' c + X.I.costF X.S / (X.P.N * X.I.k) := by
  classical
  have hv := H.valid
  have hSne := H.S_nonempty
  have hTne : (insert c (X.S.erase c')).Nonempty := insert_nonempty _ _
  have hTk : (insert c (X.S.erase c')).card ≤ X.I.k := by
    have h1 := card_insert_le c (X.S.erase c')
    have h2 := card_erase_of_mem hc'S
    have h3 := H.alo.1
    have h4 := H.two_le_k
    omega
  have hST : (X.S \ insert c (X.S.erase c')).card ≤ Par.p X.P.N := by
    have hsub : X.S \ insert c (X.S.erase c') ⊆ {c'} := by
      intro x hx
      obtain ⟨hxS, hxT⟩ := mem_sdiff.1 hx
      by_contra hxc
      exact hxT (mem_insert_of_mem (mem_erase.2 ⟨by simpa using hxc, hxS⟩))
    have h1 := card_le_card hsub
    rw [card_singleton] at h1
    unfold Par.p
    have := X.P.hN
    omega
  have halo := H.alo.2 _ hTne hTk hST
  have hpt : ∀ j, X.I.dSet (.inl j) (insert c (X.S.erase c')) ≤ X.I.dSet (.inl j) X.S +
      ((if j ∈ X.C c ∩ X.CS c' then X.dist j c - X.I.dSet (.inl j) X.S else 0) +
        (if j ∈ X.CS c' \ X.C c then X.dF c' c else 0)) := by
    intro j
    by_cases hjC' : j ∈ X.CS c'
    · have hjS : X.I.dSet (.inl j) X.S = X.dist j c' := Instance.dSet_of_mem_cluster hjC'
      have hjT : X.I.dSet (.inl j) (insert c (X.S.erase c')) ≤ X.dist j c :=
        Instance.dSet_le (mem_insert_self _ _) _
      by_cases hjC : j ∈ X.C c
      · rw [ite_eq_left (mem_inter.2 ⟨hjC, hjC'⟩),
          ite_eq_right fun h ↦ (mem_sdiff.1 h).2 hjC]
        linarith
      · rw [ite_eq_right fun h ↦ hjC (mem_inter.1 h).1, ite_eq_left (mem_sdiff.2 ⟨hjC', hjC⟩)]
        have := Instance.dd_triangle hv (.inl j) (.inr c') (.inr c)
        unfold Ctx.dist at hjS hjT
        unfold Ctx.dF
        linarith
    · rw [ite_eq_right fun h ↦ hjC' (mem_inter.1 h).2, ite_eq_right fun h ↦ hjC' (mem_sdiff.1 h).1,
        add_zero, add_zero]
      have hnear : X.I.near X.S hSne (.inl j) ∈ insert c (X.S.erase c') :=
        mem_insert_of_mem (mem_erase.2 ⟨fun h ↦ hjC' ((Instance.mem_cluster hSne).2 h),
          Instance.near_mem _ _⟩)
      calc _ ≤ X.I.dd (.inl j) (.inr (X.I.near X.S hSne (.inl j))) := Instance.dSet_le hnear _
        _ = _ := Instance.dd_near _ _
  have hTcost : X.I.costF (insert c (X.S.erase c')) ≤ X.I.costF X.S +
      ((∑ j ∈ X.C c ∩ X.CS c', X.dist j c - ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S) +
        (X.CS c' \ X.C c).card * X.dF c' c) := by
    calc X.I.costF (insert c (X.S.erase c'))
        ≤ ∑ j, (X.I.dSet (.inl j) X.S +
          ((if j ∈ X.C c ∩ X.CS c' then X.dist j c - X.I.dSet (.inl j) X.S else 0) +
            (if j ∈ X.CS c' \ X.C c then X.dF c' c else 0))) := sum_le_sum fun j _ ↦ hpt j
      _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, sum_ite_mem, sum_ite_mem, univ_inter, univ_inter,
          sum_const, nsmul_eq_mul, sum_sub_distrib]
        rfl
  have : (1 - 1 / ((X.P.N : ℝ) * X.I.k)) * X.I.costF X.S =
      X.I.costF X.S - X.I.costF X.S / (X.P.N * X.I.k) := by ring
  linarith

/-- One synced cluster: `∑_{j ∈ C*} d(j, c') ≤ (1 + 2ε) cost_OPT(C*) + 2ε cost_S(C*) +
cost(S)/(N k)`. -/
private theorem syncSub_one {c : Fin X.I.m} (hc : c ∈ X.Osync) :
    ∑ j ∈ X.C c, X.dist j (X.σsync c) ≤ (1 + 2 * X.ε) * X.costO c +
      2 * X.ε * X.costS (X.C c) + X.I.costF X.S / (X.P.N * X.I.k) := by
  classical
  have hv := H.valid
  obtain ⟨hcO, hsync⟩ := mem_filter.1 hc
  obtain ⟨hc'S, hsym⟩ := H.σsync_spec hsync
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hstar := H.swap_bound (c := c) hc'S
  set c' := X.σsync c
  -- `d(c', c*)` is at most the average of `d(·, S) + d(·, c*)` over `C* ∩ C_{c'}`
  have hdF : ((X.C c ∩ X.CS c').card : ℝ) * X.dF c' c ≤
      ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) := by
    calc ((X.C c ∩ X.CS c').card : ℝ) * X.dF c' c = ∑ j ∈ X.C c ∩ X.CS c', X.dF c' c := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun j hj ↦ by
        have hjS : X.I.dSet (.inl j) X.S = X.dist j c' :=
          Instance.dSet_of_mem_cluster (mem_inter.1 hj).2
        have := Instance.dd_triangle hv (.inr c') (.inl j) (.inr c)
        rw [Instance.dd_comm hv (.inr c') (.inl j)] at this
        unfold Ctx.dist at hjS ⊢
        unfold Ctx.dF
        linarith
  have hsplit : ∑ j ∈ X.C c, X.dist j c' =
      ∑ j ∈ X.C c ∩ X.CS c', X.dist j c' + ∑ j ∈ X.C c \ X.CS c', X.dist j c' :=
    (sum_inter_add_sum_sdiff _ _ _).symm
  have hsplitO : X.costO c =
      ∑ j ∈ X.C c ∩ X.CS c', X.dist j c + ∑ j ∈ X.C c \ X.CS c', X.dist j c :=
    (sum_inter_add_sum_sdiff _ _ _).symm
  have hA : ∑ j ∈ X.C c ∩ X.CS c', X.dist j c' =
      ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S :=
    sum_congr rfl fun j hj ↦ (Instance.dSet_of_mem_cluster (mem_inter.1 hj).2).symm
  have hD : ∑ j ∈ X.C c \ X.CS c', X.dist j c' ≤
      ∑ j ∈ X.C c \ X.CS c', X.dist j c + (X.C c \ X.CS c').card * X.dF c' c := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr c')
    rw [Instance.dd_comm hv (.inr c) (.inr c')] at this
    exact this
  -- cardinalities
  have hBD : ((X.CS c' \ X.C c).card : ℝ) + (X.C c \ X.CS c').card ≤ X.ε * (X.C c).card := by
    have h1 : (X.C c \ X.CS c').card + (X.CS c' \ X.C c).card = X.symmCard c c' := by
      unfold Ctx.symmCard
      rw [card_union_of_disjoint disjoint_sdiff_sdiff]
    have h2 : X.ε * min ((X.C c).card : ℝ) (X.CS c').card ≤ X.ε * (X.C c).card :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le
    have h3 : ((X.C c \ X.CS c').card : ℝ) + (X.CS c' \ X.C c).card = X.symmCard c c' := by
      exact_mod_cast h1
    linarith
  have hAcard : (1 - X.ε) * (X.C c).card ≤ (X.C c ∩ X.CS c').card := by
    have h1 : ((X.C c ∩ X.CS c').card : ℝ) + (X.C c \ X.CS c').card = (X.C c).card := by
      exact_mod_cast card_inter_add_card_sdiff _ _
    have : (0 : ℝ) ≤ (X.CS c' \ X.C c).card := Nat.cast_nonneg _
    linarith
  -- the averaged bound on `d(c', c*)`
  have hdF0 : 0 ≤ X.dF c' c := Instance.dd_nonneg hv _ _
  have hY : ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) ≤
      X.costS (X.C c) + X.costO c := by
    rw [sum_add_distrib]
    have h1 : ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S ≤ X.costS (X.C c) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left fun j _ _ ↦ Instance.dSet_nonneg hv _ _
    have h2 : 0 ≤ ∑ j ∈ X.C c \ X.CS c', X.dist j c :=
      sum_nonneg fun j _ ↦ Instance.dd_nonneg hv _ _
    linarith
  have hP : ((X.C c).card : ℝ) * X.dF c' c ≤
      2 * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) := by
    have h1 : (1 - X.ε) * ((X.C c).card * X.dF c' c) ≤
        ((X.C c ∩ X.CS c').card : ℝ) * X.dF c' c := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hAcard hdF0
    have h2 : 0 ≤ ((X.C c).card : ℝ) * X.dF c' c := mul_nonneg (Nat.cast_nonneg _) hdF0
    nlinarith
  have hBDdF : (((X.CS c' \ X.C c).card : ℝ) + (X.C c \ X.CS c').card) * X.dF c' c ≤
      2 * X.ε * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) := by
    calc (((X.CS c' \ X.C c).card : ℝ) + (X.C c \ X.CS c').card) * X.dF c' c
        ≤ X.ε * (X.C c).card * X.dF c' c := mul_le_mul_of_nonneg_right hBD hdF0
      _ = X.ε * ((X.C c).card * X.dF c' c) := by ring
      _ ≤ X.ε * (2 * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c)) :=
          mul_le_mul_of_nonneg_left hP hε.le
      _ = _ := by ring
  have hfin : 2 * X.ε * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) ≤
      2 * X.ε * (X.costS (X.C c) + X.costO c) :=
    mul_le_mul_of_nonneg_left hY (by linarith)
  rw [hsplit, hA]
  nlinarith

/-- **Substitutes for synced clusters** ([BCFGJPSSV26b, Proposition 4.3]). -/
theorem syncSub :
    ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σsync c) ≤
      (1 + 4 * X.ε) * ∑ c ∈ X.Osync, X.costO c + 5 * X.ε * X.I.costF X.S := by
  classical
  have hv := H.valid
  have hε := H.eps_pos
  have hcostS := Instance.costF_nonneg hv X.S
  have hO : 0 ≤ ∑ c ∈ X.Osync, X.costO c :=
    sum_nonneg fun c _ ↦ sum_nonneg fun j _ ↦ Instance.dd_nonneg hv _ _
  have hS := H.sum_costS_C_le X.Osync
  have hcard : ((X.Osync.card : ℝ)) ≤ X.I.k := by
    have : X.Osync.card ≤ X.O.card := card_filter_le _ _
    rw [H.isOpt.card] at this
    exact_mod_cast this
  have hk : (0 : ℝ) < X.I.k := by
    have := H.two_le_k
    have : (2 : ℝ) ≤ X.I.k := by exact_mod_cast this
    linarith
  have hN := X.P.N_pos'
  have herr : (X.Osync.card : ℝ) * (X.I.costF X.S / (X.P.N * X.I.k)) ≤ X.ε * X.I.costF X.S := by
    have he : X.ε = 1 / X.P.N := rfl
    rw [he, mul_div_assoc', div_le_iff₀ (by positivity)]
    have : (X.Osync.card : ℝ) * X.I.costF X.S ≤ X.I.k * X.I.costF X.S :=
      mul_le_mul_of_nonneg_right hcard hcostS
    calc (X.Osync.card : ℝ) * X.I.costF X.S ≤ X.I.k * X.I.costF X.S := this
      _ = 1 / X.P.N * X.I.costF X.S * (X.P.N * X.I.k) := by field_simp
  calc ∑ c ∈ X.Osync, ∑ j ∈ X.C c, X.dist j (X.σsync c)
      ≤ ∑ c ∈ X.Osync, ((1 + 2 * X.ε) * X.costO c + 2 * X.ε * X.costS (X.C c) +
          X.I.costF X.S / (X.P.N * X.I.k)) := sum_le_sum fun c hc ↦ H.syncSub_one hc
    _ = (1 + 2 * X.ε) * ∑ c ∈ X.Osync, X.costO c + 2 * X.ε * ∑ c ∈ X.Osync, X.costS (X.C c) +
          X.Osync.card * (X.I.costF X.S / (X.P.N * X.I.k)) := by
        rw [sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum, mul_sum]
    _ ≤ _ := by nlinarith

/-- **Substitutes for close clusters** ([BCFGJPSSV26b, Proposition 4.4]). -/
theorem closeSub {c : Fin X.I.m} (hc : c ∈ X.Ocl) :
    ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ (1 + eta) * X.costO c + 2 * X.ε * X.costS (X.C c) := by
  classical
  have hv := H.valid
  obtain ⟨hcO, -, hclose⟩ := mem_filter.1 hc
  have hcard : (0 : ℝ) < (X.C c).card := by exact_mod_cast (H.cluster_nonempty hcO).card_pos
  have h1 : ∀ j ∈ X.C c, X.dist j (X.σcl c) ≤ X.dist j c + X.dOS c := by
    intro j _
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr (X.σcl c))
    have h2 := H.dF_σcl c
    unfold Ctx.dist
    unfold Ctx.dF at h2
    linarith
  calc ∑ j ∈ X.C c, X.dist j (X.σcl c) ≤ ∑ j ∈ X.C c, (X.dist j c + X.dOS c) := sum_le_sum h1
    _ = X.costO c + (X.C c).card * X.dOS c := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul]
        rfl
    _ ≤ X.costO c + (X.C c).card * (eta * X.avgO c + 2 * X.ε * X.avgS c) := by gcongr
    _ = _ := by
        unfold Ctx.avgO Ctx.avgS
        field_simp
        ring

end Hyp

end BCFGJPSSV26.Stable
