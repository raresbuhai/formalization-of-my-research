module

public import BCFGJPSSV26.Stable.LSBound.NiceMaps
public import BCFGJPSSV26.Stable.Submod.Candidate
public import BCFGJPSSV26.Stable.WinWin

/-!
# The win-win combination

* [BCFGJPSSV26b, Section 3.5]: the `(a, 1 - a)` combination of the local
  search bound `Ψ_LS` and the submodular bound `Ψ_T` is at most `(1 + η + 10 ε) opt`
  (`BCFGJPSSV26.Stable.Partition.psi_combo`), cluster by cluster: each row is a multiple of
  `cost_OPT(C*)` by `|C*| per = x cost_OPT(C*)` and
  `cost_OPT(core_κ) + |core_κ| per = y_κ cost_OPT(C*)`, and the rows satisfy the win-win
  inequalities (`BCFGJPSSV26.Stable.row_early`, `BCFGJPSSV26.Stable.row_late`,
  `BCFGJPSSV26.Stable.row_R`). So the local search or the candidate of a good trial costs at most
  `(1 + η + 100 ε) opt` (`BCFGJPSSV26.Stable.Partition.min_le_bound`).
* When `k = 1` or `opt = 0`, the local search alone costs at most
  `(1.89 + 1000/N) opt` (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`): for `k = 1`, swapping
  to an optimal center gives `(1 - 1/N) cost(S) ≤ opt`; for `opt = 0`, `cost(S) ≤ 4 opt = 0`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- The ratio `x = per/avg_OPT` of a cluster: `0 ≤ x ≤ 1 + 2ε` and `|C*| per = x cost_OPT(C*)`. -/
private theorem Hyp.xr_spec {X : Ctx} (H : Hyp X) (c : Fin X.I.m) :
    0 ≤ X.xr c ∧ X.xr c ≤ 1 + 2 * X.ε ∧ (X.C c).card * X.per c = X.xr c * X.costO c := by
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hp : 0 ≤ X.per c := per_nonneg H.valid _ _ _
  have hA : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _
  rcases (X.C c).eq_empty_or_nonempty with hC | hC
  · have hA0 : X.costO c = 0 := by rw [Ctx.costO, costAt, hC, sum_empty]
    have havg : X.avgO c = 0 := by rw [Ctx.avgO, hA0, zero_div]
    unfold Ctx.xr xRatio
    rw [ite_eq_left havg, hC, card_empty, hA0]
    refine ⟨zero_le_one, by linarith, by simp⟩
  · have hle : X.per c ≤ (1 + 2 * X.ε) * X.avgO c :=
      per_le_avg H.valid hε (by linarith) hC c
    have hn : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
    have havg0 : 0 ≤ X.avgO c := div_nonneg hA hn.le
    have hAn : X.costO c = X.avgO c * (X.C c).card := by
      rw [Ctx.avgO]
      field_simp
    unfold Ctx.xr xRatio
    by_cases havg : X.avgO c = 0
    · rw [ite_eq_left havg]
      rw [havg, mul_zero] at hle
      have hp0 : X.per c = 0 := le_antisymm hle hp
      rw [hp0, hAn, havg]
      refine ⟨zero_le_one, by linarith, by ring⟩
    · rw [ite_eq_right havg]
      have hpos : 0 < X.avgO c := lt_of_le_of_ne havg0 (Ne.symm havg)
      refine ⟨div_nonneg hp hpos.le, (div_le_iff₀ hpos).2 hle, ?_⟩
      rw [hAn]
      field_simp


/-- **The row of a far cluster** (`O_R`). -/
private theorem Hyp.rowR_le {X : Ctx} (H : Hyp X) {c : Fin X.I.m} (hc : X.IsFar c) :
    aW * (costAt X.I c (X.core (X.kap c) c) +
        2 * (X.costO c - costAt X.I c (X.core (X.kap c) c)) +
        ((X.C c).card - (X.core (X.kap c) c).card) * X.per c) +
      (1 - aW) * (X.costO c + (X.C c).card * X.per c) ≤
        (1 + eta + 10 * X.ε) * X.costO c := by
  classical
  have hε := H.eps_pos
  have hε' := H.eps_lt
  obtain ⟨hx0, hx1, hxA⟩ := H.xr_spec c
  have hA := hc.costO_pos
  have hp := hc.per_pos
  have hC : (X.C c).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    have : X.costO c = 0 := by rw [Ctx.costO, costAt, h, sum_empty]
    linarith
  have hn : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
  have havg : 0 < X.avgO c := div_pos hA hn
  have hxavg : X.xr c * X.avgO c = X.per c := by
    unfold Ctx.xr xRatio
    rw [ite_eq_right havg.ne', div_mul_cancel₀ _ havg.ne']
  -- `x ≥ η/(1 + ε)`
  have hx : eta / (1 + X.ε) ≤ X.xr c := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := hc.avg_le
    have he : (0 : ℝ) < eta := by unfold eta; norm_num
    rw [le_div_iff₀ he] at h1
    have h2 : eta * X.avgO c ≤ X.xr c * (1 + X.ε) * X.avgO c := by nlinarith
    exact le_of_mul_le_mul_right (by linarith) havg
  -- the clients outside the core pay more than `(1 + κ) per`
  set κ := X.kap c with hκ
  set p := X.per c with hpdef
  set A := X.costO c with hAdef
  set D := X.core κ c with hD
  set cK := costAt X.I c D with hcK
  have hκ0 : 0 < κ := kappa_pos _
  have hDf : D = (X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p := rfl
  have hsplit := sum_filter_add_sum_filter_not (X.C c)
    (fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p) fun j ↦ X.I.dd (.inl j) (.inr c)
  rw [← hDf] at hsplit
  have hcardsplit := card_filter_add_card_filter_not (s := X.C c)
    (fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p)
  rw [← hDf] at hcardsplit
  have hout : (1 + κ) * p * (((X.C c).card : ℝ) - D.card) ≤
      ∑ j ∈ (X.C c).filter (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p),
        X.I.dd (.inl j) (.inr c) := by
    have : ((X.C c).card : ℝ) - D.card =
        ((X.C c).filter (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p)).card := by
      rw [← hcardsplit]
      push_cast
      ring
    rw [this, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun j hj ↦ ?_
    exact (not_le.1 (mem_filter.1 hj).2).le
  -- the core pays at least `per`, except fewer than `ε |C*|` clients
  have hcore : p * D.card - X.ε * (X.C c).card * p ≤ cK := by
    have hlt := per_count_lt (I := X.I) hε (by linarith) hC c
    have hsub : (D.filter fun j ↦ X.I.dd (.inl j) (.inr c) < p) ⊆
        (X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) < p :=
      filter_subset_filter _ (core_subset _ _ _ _)
    have hle : ((D.filter fun j ↦ X.I.dd (.inl j) (.inr c) < p).card : ℝ) <
        X.ε * (X.C c).card :=
      lt_of_le_of_lt (by exact_mod_cast card_le_card hsub) hlt
    have hs2 := sum_filter_add_sum_filter_not D
      (fun j ↦ X.I.dd (.inl j) (.inr c) < p) fun j ↦ X.I.dd (.inl j) (.inr c)
    have hc2 := card_filter_add_card_filter_not (s := D)
      (fun j ↦ X.I.dd (.inl j) (.inr c) < p)
    have h1 : 0 ≤ ∑ j ∈ D.filter (fun j ↦ X.I.dd (.inl j) (.inr c) < p),
        X.I.dd (.inl j) (.inr c) := sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _
    have h2 : p * ((D.filter fun j ↦ ¬ X.I.dd (.inl j) (.inr c) < p).card : ℝ) ≤
        ∑ j ∈ D.filter (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) < p), X.I.dd (.inl j) (.inr c) := by
      rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun j hj ↦ not_lt.1 (mem_filter.1 hj).2
    have h3 : (D.card : ℝ) = (D.filter fun j ↦ X.I.dd (.inl j) (.inr c) < p).card +
        (D.filter fun j ↦ ¬ X.I.dd (.inl j) (.inr c) < p).card := by
      rw [← hc2]
      push_cast
      ring
    have h4 : cK = ∑ j ∈ D, X.I.dd (.inl j) (.inr c) := rfl
    rw [h4, ← hs2, h3]
    nlinarith
  -- the bound on `y_κ`
  have hy : 2 * ((1 + kappa (X.xr c)) * X.xr c - 1) / kappa (X.xr c) -
      X.ε * X.xr c * (1 + 2 / kappa (X.xr c)) ≤ (cK + D.card * p) / A := by
    change 2 * ((1 + κ) * X.xr c - 1) / κ - X.ε * X.xr c * (1 + 2 / κ) ≤ (cK + D.card * p) / A
    rw [le_div_iff₀ hA]
    have e : κ * ((2 * ((1 + κ) * X.xr c - 1) / κ - X.ε * X.xr c * (1 + 2 / κ)) * A) =
        2 * ((1 + κ) * (X.xr c * A) - A) - X.ε * (X.xr c * A) * (κ + 2) := by
      field_simp
    rw [← hxA] at e
    have hA' : A = cK + ∑ j ∈ (X.C c).filter
        (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p), X.I.dd (.inl j) (.inr c) := by
      exact hsplit.symm
    have hprod : 0 ≤ (2 + κ) * (cK - p * D.card + X.ε * (X.C c).card * p) :=
      mul_nonneg (by linarith) (by linarith)
    refine le_of_mul_le_mul_left ?_ hκ0
    rw [e]
    nlinarith
  have hR := row_R hε.le hε' hx hx1 hy
  have e2 : (cK + D.card * p) / A * A = cK + D.card * p := div_mul_cancel₀ _ hA.ne'
  have hR' := mul_le_mul_of_nonneg_right hR hA.le
  unfold aW at hR' ⊢
  nlinarith


namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

/-- **The win-win combination of one row.** -/
private theorem row_combo (H : Hyp X) {c : Fin X.I.m} (hc : c ∈ X.O) :
    aW * Q.rowLS c + (1 - aW) * Q.rowT c ≤ (1 + eta + 10 * X.ε) * X.costO c := by
  obtain ⟨hx0, hx1, hxA⟩ := H.xr_spec c
  have hA : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hεA : 0 ≤ X.ε * X.costO c := mul_nonneg hε.le hA
  unfold rowLS rowT
  by_cases h1 : c ∈ X.OSall w₁.OL
  · rw [ite_eq_left h1, ite_eq_left h1]
    unfold aW
    nlinarith
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : c ∈ w₁.OLe
  · rw [ite_eq_left h2, ite_eq_left h2, hxA]
    have h := mul_le_mul_of_nonneg_right (row_early hε.le hε' hx0 hx1) hA
    have e : aW * (3 * X.costO c) + (1 - aW) * (X.costO c + 2 / Real.exp 1 *
        (X.xr c * X.costO c)) = (aW * 3 + (1 - aW) * (1 + 2 * X.xr c / Real.exp 1)) *
          X.costO c := by ring
    rw [e]
    nlinarith
  rw [ite_eq_right h2, ite_eq_right h2]
  by_cases h3 : c ∈ Q.OLam ∪ Q.OP
  · rw [ite_eq_left h3, ite_eq_left h3, hxA]
    have h := mul_le_mul_of_nonneg_right (row_late hε.le hε' hx0 hx1) hA
    have e : aW * (X.costO c + X.xr c * X.costO c) + (1 - aW) * (X.costO c + 2 / Real.exp 1 *
        ((1 + X.kap c) * (X.xr c * X.costO c))) = (aW * (1 + X.xr c) + (1 - aW) *
          (1 + 2 * (1 + kappa (X.xr c)) * X.xr c / Real.exp 1)) * X.costO c := by
      simp only [Ctx.kap]
      ring
    rw [e]
    nlinarith
  rw [ite_eq_right h3, ite_eq_right h3]
  have hR : c ∈ Q.OR := by
    obtain ⟨hcov, -⟩ := Q.cover H
    rw [← hcov] at hc
    simp only [mem_union] at hc h3
    tauto
  exact H.rowR_le (Q.far_R c hR)

/-- **The win-win combination** of the two row sums. -/
theorem psi_combo (H : Hyp X) :
    aW * Q.PsiLS + (1 - aW) * Q.PsiT ≤ (1 + eta + 10 * X.ε) * X.opt := by
  rw [H.opt_eq_sum, Partition.PsiLS, Partition.PsiT, mul_sum, mul_sum, mul_sum,
    ← sum_add_distrib]
  exact sum_le_sum fun c hc ↦ Q.row_combo H hc

/-- **The final bound**: the local search or a candidate within `Ψ_T + 60 ε opt` costs at most
`(1 + η + 100 ε) opt`. -/
theorem min_le_bound (H : Hyp X) {cT : ℝ} (hT : cT ≤ Q.PsiT + 60 * X.ε * X.opt) :
    X.I.costF X.S ≤ (1 + eta + 100 * X.ε) * X.opt ∨ cT ≤ (1 + eta + 100 * X.ε) * X.opt := by
  by_contra h
  rw [not_or, not_le, not_le] at h
  have h1 := Q.costF_S_le_PsiLS H
  have h2 := Q.psi_combo H
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hε := H.eps_pos
  unfold aW at h2
  nlinarith [mul_nonneg hε.le hopt]

end Partition

/-- **The degenerate cases** `k = 1` and `opt = 0`. -/
theorem costF_le_bound_of_degenerate {I : Instance} (hv : I.Valid) (hk : I.k ≤ I.m) {N : ℕ}
    (hN : 201 ≤ N) {S : Finset (Fin I.m)} (hS : IsALO I (24 * N) (1 / (N * I.k)) S)
    (h : I.k = 1 ∨ I.opt I.k = 0) : I.costF S ≤ (1.89 + 1000 / N) * I.opt I.k := by
  have hopt := Instance.opt_nonneg' hv I.k
  have hN' : (201 : ℝ) ≤ N := by exact_mod_cast hN
  rcases h with h1 | h0
  · obtain ⟨O, hO⟩ := Instance.exists_isOpt hv hk
    have hOne := hO.nonempty hv
    have hSO : (S \ O).card ≤ 24 * N := by
      have := card_le_card (sdiff_subset (s := S) (t := O))
      rw [hS.1, h1] at this
      omega
    have h := hS.2 O hOne (by rw [hO.card]) hSO
    have hδ : (1 : ℝ) / (N * I.k) = 1 / N := by rw [h1]; simp
    rw [hO.cost, hδ] at h
    have hc := Instance.costF_nonneg hv S
    have hNpos : (0 : ℝ) < N := by linarith
    have h1N : 1 / (N : ℝ) ≤ 1 / 201 := one_div_le_one_div_of_le (by norm_num) hN'
    have h1N' : 0 < 1 / (N : ℝ) := by positivity
    have h1000 : (1000 : ℝ) / N = 1000 * (1 / N) := by ring
    rw [h1000]
    nlinarith
  · have h4 := costF_le_four_opt hv hk hN hS
    rw [h0] at h4 ⊢
    linarith

end BCFGJPSSV26.Stable
