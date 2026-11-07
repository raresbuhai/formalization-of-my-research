module

public import BCFGJPSSV26.Stable.Time.RunTime
public import BCFGJPSSV26.Combine

/-!
# Theorem 1.1 of Part II

[BCFGJPSSV26b, Theorem 1.1] (Theorem 1.3 of Part I), in the form of
`BCFGJPSSV26.stable_kMedian_approximation` (`BCFGJPSSV26.Combine.Thm13`):
`BCFGJPSSV26.Stable.stable_main`.

One algorithm serves every accuracy: `BCFGJPSSV26.Stable.algQ` reads `ε` with the instance and
`L`, and runs the algorithm `BCFGJPSSV26.Stable.alg` for `N = BCFGJPSSV26.Stable.accN ε ≥ 256`:

* it runs in time `O(stableTimeOf a 2 ((I, L), ε))` plus the length of the input, for an absolute
  constant `a` (`BCFGJPSSV26.Stable.exists_runsInTime`);
* it always outputs exactly `k` distinct facilities (`BCFGJPSSV26.Stable.alg_valid`);
* for `ε ∈ (0, 1/200)`, `1/N < ε` (`BCFGJPSSV26.Stable.inv_lt_accN`), so on a `β`-stable instance
  with `L ≥ 1/β` its output costs at most `(1.89 + 1000/N) opt ≤ (1.89 + 1000 ε) opt` with
  probability at least `1 - 1/N ≥ 1 - ε` (`BCFGJPSSV26.Stable.success_prob`), over the
  `stableTimeOf a 2 ((I, L), ε) ≥ B ≥ R Ctr b` coins, where `B` is the budget
  (`BCFGJPSSV26.Stable.Par.coinLen_le_budget`).

So the constants of the theorem are this `a`, `b = 2` and `C = 1000`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Encoding

/-- **Theorem 1.1 of Part II.** -/
theorem stable_main : Combine.Thm13 := by
  obtain ⟨a, hrun, hbud⟩ := exists_runsInTime
  refine ⟨algQ, a, 2, 1000, hrun, fun I hv hk L ε ↦
    ⟨fun r ↦ alg_valid (prmOf ε) hv hk L r, fun hε _ β hβ hst hL ↦ ?_⟩⟩
  set P := prmOf ε
  have hNpos : (0 : ℝ) < P.N := P.N_pos'
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  -- the accuracy `1/N`
  have h1N : 1 / (P.N : ℝ) ≤ ε := by
    have h : ((1 / ε : ℚ) : ℝ) < ((accN ε : ℚ) : ℝ) := Rat.cast_lt.2 (inv_lt_accN hε)
    push_cast at h
    exact ((one_div_lt hε' hNpos).1 h).le
  -- the probability
  have hT : Par.coinLen P.N I L ≤ stableTimeOf a 2 ((I, L), ε) :=
    (Par.coinLen_le_budget hk P.N_pos).trans (hbud ((I, L), ε))
  have h := success_prob P hv hk hβ hst hL hT
  have hopt := Instance.opt_nonneg' hv I.k
  refine le_trans (by linarith) (h.trans (Combine.coinProb_mono fun r hr ↦ ?_))
  rw [algQ_eq]
  have hne := Instance.centers_nonempty (alg_valid P hv hk L r).1.1 (alg_valid P hv hk L r).1.2.2
  rw [← Instance.costF_eq_cost hne]
  refine hr.trans ?_
  unfold bound
  refine mul_le_mul_of_nonneg_right ?_ hopt
  have : (1000 : ℝ) / P.N ≤ 1000 * ε := by
    rw [show (1000 : ℝ) / P.N = 1000 * (1 / P.N) by ring]
    exact mul_le_mul_of_nonneg_left h1N (by norm_num)
  linarith

end BCFGJPSSV26.Stable
