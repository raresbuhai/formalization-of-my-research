module

public import BCFGJPSSV26.Stable.Alg.Trial
public import BCFGJPSSV26.Stable.Alg.LocalSearch
public import BCFGJPSSV26.Stable.Time.Budget
public import BCFGJPSSV26.Combine.Analysis

/-!
# The algorithm

**The core** (`BCFGJPSSV26.Stable.coreAlg`): on `(N, I, L, coins, B)`, run the local
search with budget `B`, then `min(R, B)` trials, trial `t` on the chunks `t Ctr, …` of the coins;
make every candidate, and the local search, into exactly `k` facilities with
`BCFGJPSSV26.sanitizeK`, and output the cheapest by exact cost (`BCFGJPSSV26.Combine.bestOf`),
once more through `BCFGJPSSV26.sanitizeK`. All of `N`, `L` and `B` are inputs, so one polynomial
bound serves all `N`.

**The algorithm for one `N`** (`BCFGJPSSV26.Stable.alg`): the core with the budget
`B = 2^(e₁ L) (|I| + 2)^(e₁)` and the first `R Ctr b` coins.

* **Valid output on every input** (`BCFGJPSSV26.Stable.alg_valid`): a list of exactly `k`
  distinct facilities, for every valid instance with `k ≤ m`, every `L` and every coin string,
  since it is an output of `BCFGJPSSV26.sanitizeK`.
* **At most the cost of every candidate** (`BCFGJPSSV26.Stable.cost_coreAlg_le`).
* **Success probability** (`BCFGJPSSV26.Stable.success_prob`): for a `β`-stable instance and
  `L ≥ 1/β`, with probability at least `1 - 1/N` over any number `T ≥ R Ctr b` of coins, the output
  costs at most `(1.89 + 1000/N) opt`. For `k = 1` or `opt = 0` the local search alone suffices
  (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`); otherwise the standing hypotheses hold,
  each trial is good with probability at least `q` (`BCFGJPSSV26.Stable.Hyp.card_trialGood`), the
  trials are independent blocks of chunks (`BCFGJPSSV26.Stable.card_exists_block_ge`), and the
  coins give uniform chunks (`BCFGJPSSV26.Stable.coinProb_ge_of_chunks`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset Sampling

/-- The candidates of the core: the local search and the candidates of `min(R, B)` trials. -/
def coreCands (N : ℕ) (x : Raw) (L : ℕ) (coins : List Bool) (B : ℕ) : List (List ℕ) :=
  localSearch N x B :: (List.range (min (Par.R N L) B)).flatMap fun t ↦
    trial N x L (localSearch N x B) B fun i ↦
      chunkVal (Par.bits N (encRaw x).length) coins (t * Par.Ctr N L x.k + i)

/-- **The core of the algorithm**: the cheapest candidate, made into `k` facilities. -/
def coreAlg (N : ℕ) (x : Raw) (L : ℕ) (coins : List Bool) (B : ℕ) : List ℕ :=
  sanitizeK x.m x.k
    (Combine.bestOf x.n x.table ((coreCands N x L coins B).map (sanitizeK x.m x.k)))

/-- **The algorithm for accuracy `1/N`**: the core with the budget and the first `R Ctr b`
coins. -/
def alg (P : Prm) (y : (Instance × ℕ) × List Bool) : List ℕ :=
  coreAlg P.N (toRaw y.1.1) y.1.2 (y.2.take (Par.coinLen P.N y.1.1 y.1.2))
    (Par.budget P.N y.1.1 y.1.2)

variable {I : Instance}

/-- **The output is always a list of exactly `k` distinct facilities.** -/
theorem coreAlg_valid (hv : I.Valid) (hk : I.k ≤ I.m) (N L : ℕ) (coins : List Bool) (B : ℕ) :
    I.IsCenterList (coreAlg N (toRaw I) L coins B) ∧
      (coreAlg N (toRaw I) L coins B).length = I.k :=
  isCenterList_sanitizeK hv hk _

theorem alg_valid (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) (L : ℕ) (r : List Bool) :
    I.IsCenterList (alg P ((I, L), r)) ∧ (alg P ((I, L), r)).length = I.k :=
  coreAlg_valid hv hk _ _ _ _

/-- **The output is at most as expensive as every candidate.** -/
theorem cost_coreAlg_le (hv : I.Valid) (hk : I.k ≤ I.m) {N L : ℕ} {coins : List Bool} {B : ℕ}
    {X : List ℕ} (hX : X ∈ coreCands N (toRaw I) L coins B) :
    I.costF (I.centers (coreAlg N (toRaw I) L coins B)) ≤
      I.costF (I.centers (sanitizeK I.m I.k X)) := by
  set Ys := (coreCands N (toRaw I) L coins B).map (sanitizeK I.m I.k) with hYs
  have hXY : sanitizeK I.m I.k X ∈ Ys := List.mem_map.2 ⟨X, hX, rfl⟩
  obtain ⟨Y, hY, hYmem, hYmin⟩ := Combine.find?_min ((toRaw I).cost) (List.ne_nil_of_mem hXY)
  have hbest : Combine.bestOf I.n (distTable I) Ys = Y := by
    unfold Combine.bestOf
    rw [show (fun S ↦ Ys.all fun S' ↦ decide (Combine.costQ I.n (distTable I) S ≤
      Combine.costQ I.n (distTable I) S')) = (fun S ↦ Ys.all fun S' ↦
        decide ((toRaw I).cost S ≤ (toRaw I).cost S')) from rfl, hY]
    rfl
  obtain ⟨Z, -, rfl⟩ := List.mem_map.1 hYmem
  obtain ⟨hnd, hlen, hm⟩ := sanitizeK_spec hk Z
  have hcore : coreAlg N (toRaw I) L coins B = sanitizeK I.m I.k Z := by
    unfold coreAlg
    change sanitizeK I.m I.k (Combine.bestOf I.n (distTable I) Ys) = _
    rw [hbest, sanitizeK_eq_self hnd hm hlen]
  have hne : ∀ W, W ∈ Ys → W ≠ [] := by
    intro W hW
    obtain ⟨W', -, rfl⟩ := List.mem_map.1 hW
    exact (isCenterList_sanitizeK hv hk W').1.1
  obtain ⟨hnd', -, hm'⟩ := sanitizeK_spec hk X
  rw [hcore, ← Raw.cost_toRaw (hne _ hYmem) hm, ← Raw.cost_toRaw (hne _ hXY) hm']
  exact_mod_cast hYmin _ hXY

/-- The candidates of trial `t < R` are candidates of the algorithm. -/
theorem cost_alg_le_of_trial (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) {L : ℕ} (r : List Bool)
    {t : ℕ} (ht : t < Par.R P.N L) {X : List ℕ}
    (hX : X ∈ localSearch P.N (toRaw I) (Par.budget P.N I L) ::
      trial P.N (toRaw I) L (localSearch P.N (toRaw I) (Par.budget P.N I L)) (Par.budget P.N I L)
        (window (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length) r i)
          (t * Par.Ctr P.N L I.k) (Par.Ctr P.N L I.k))) :
    I.costF (I.centers (alg P ((I, L), r))) ≤ I.costF (I.centers (sanitizeK I.m I.k X)) := by
  refine cost_coreAlg_le hv hk ?_
  rcases List.mem_cons.1 hX with rfl | hX
  · exact List.mem_cons_self
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨t, List.mem_range.2 ?_, ?_⟩)
  · exact lt_min ht (lt_of_lt_of_le ht (Par.R_le_budget P.N_pos))
  · have hwin : window (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length)
          (r.take (Par.coinLen P.N I L)) (t * Par.Ctr P.N L I.k + i)) 0 (Par.Ctr P.N L I.k) =
        window (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length) r i)
          (t * Par.Ctr P.N L I.k) (Par.Ctr P.N L I.k) := by
      funext i
      unfold window
      split_ifs with hi
      · rw [zero_add]
        refine chunkVal_take ?_ r
        unfold Par.coinLen
        have h1 : t * Par.Ctr P.N L I.k + i + 1 ≤ Par.R P.N L * Par.Ctr P.N L I.k := by
          calc t * Par.Ctr P.N L I.k + i + 1 ≤ t * Par.Ctr P.N L I.k + Par.Ctr P.N L I.k := by
                omega
            _ = (t + 1) * Par.Ctr P.N L I.k := by ring
            _ ≤ Par.R P.N L * Par.Ctr P.N L I.k := Nat.mul_le_mul_right _ ht
        exact Nat.mul_le_mul_right _ h1
      · rfl
    change X ∈ trial P.N (toRaw I) L (localSearch P.N (toRaw I) (Par.budget P.N I L))
      (Par.budget P.N I L) (fun i ↦ chunkVal (Par.bits P.N (encInstance I).length)
        (r.take (Par.coinLen P.N I L)) (t * Par.Ctr P.N L I.k + i))
    rw [← trial_window, Raw.k_toRaw, hwin]
    exact hX

/-- Some trial `t < R` is good, on the chunks `ch` of the coins. -/
def TrialsGood (P : Prm) (I : Instance) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) : Prop :=
  ∃ t < Par.R P.N L, TrialGood P I L LS B (window ch (t * Par.Ctr P.N L I.k) (Par.Ctr P.N L I.k))

open Classical in
/-- **The success probability** of the algorithm. -/
theorem success_prob (P : Prm) (hv : I.Valid) (hk : I.k ≤ I.m) {L : ℕ} {β : ℝ} (hβ : 0 < β)
    (hst : I.IsStable β) (hL : 1 / β ≤ L) {T : ℕ} (hT : Par.coinLen P.N I L ≤ T) :
    1 - 1 / (P.N : ℝ) ≤
      coinProb T fun r ↦ I.costF (I.centers (alg P ((I, L), r))) ≤ bound P I := by
  set B := Par.budget P.N I L with hB
  set LS := localSearch P.N (toRaw I) B with hLSdef
  have hN1 := P.N_pos
  have halo : IsALO I (Par.p P.N) (1 / (P.N * I.k)) (I.centers LS) :=
    isALO_localSearch hv hk hN1 (Par.budget_ls₁ hk hN1) (Par.budget_ls₂ hk hN1)
  obtain ⟨hnd, hlen, hm⟩ := localSearch_spec hk P.N B
  have hNpos := P.N_pos'
  have h1N : 0 ≤ 1 - 1 / (P.N : ℝ) := by
    rw [sub_nonneg, div_le_one hNpos]
    exact_mod_cast hN1
  -- the degenerate cases: the local search alone
  by_cases hdeg : I.k = 1 ∨ I.opt I.k = 0
  · have hLS := costF_le_bound_of_degenerate hv hk P.hN halo hdeg
    rw [Combine.coinProb_of_forall fun r ↦ ?_]
    · linarith [div_pos one_pos hNpos]
    have h := cost_alg_le_of_trial (L := L) P hv hk r (t := 0) (by unfold Par.R; positivity)
      (X := LS) List.mem_cons_self
    refine h.trans ((costF_sanitizeK_le hv hnd hm hlen.le).trans hLS)
  -- the standing hypotheses
  rw [not_or] at hdeg
  obtain ⟨O, hO⟩ := Instance.exists_isOpt hv hk
  set X : Ctx := ⟨P, I, β, L, O, I.centers LS⟩ with hX
  have H : Hyp X :=
    { valid := hv
      k_le_m := hk
      two_le_k := by
        change 2 ≤ I.k
        have := hv.one_le_k
        have := hdeg.1
        omega
      opt_pos := lt_of_le_of_ne (Instance.opt_nonneg' hv I.k) (Ne.symm hdeg.2)
      β_pos := hβ
      stable := hst
      L_ge := hL
      isOpt := hO
      alo := halo }
  -- the trials
  set C := Par.Ctr P.N L I.k with hC
  set b := Par.bits P.N (encInstance I).length with hb
  let G : (Fin C → Fin (2 ^ b)) → Prop := fun v ↦ TrialGood P I L LS B (toCh v)
  have hG : P.q L * (Fintype.card (Fin (2 ^ b)) : ℝ) ^ C ≤ (univ.filter G).card := by
    have h := H.card_trialGood (LS := LS) rfl hnd hm (B := B) (Par.pow_s_le_budget hN1)
    simpa using h
  have hrep := card_exists_block_ge G (P.q_nonneg L) (P.q_le_one L) (R := Par.R P.N L) hG
  -- the coins
  let Q : (ℕ → ℕ) → Prop := TrialsGood P I L LS B
  have hQ : ∀ ch ch' : ℕ → ℕ, (∀ i < Par.R P.N L * C, ch i = ch' i) → Q ch → Q ch' := by
    rintro ch ch' h ⟨t, ht, hgood⟩
    refine ⟨t, ht, ?_⟩
    rw [← window_congr (o := t * C) (M := C) fun i hi ↦ h _ ?_]
    · exact hgood
    · calc t * C + i < t * C + C := by omega
        _ = (t + 1) * C := by ring
        _ ≤ Par.R P.N L * C := Nat.mul_le_mul_right _ ht
  have hPQ : ∀ r : List Bool, Q (fun i ↦ chunkVal b r i) →
      I.costF (I.centers (alg P ((I, L), r))) ≤ bound P I := by
    rintro r ⟨t, ht, X', hX', hcost⟩
    exact (cost_alg_le_of_trial P hv hk r ht hX').trans hcost
  have hprob := coinProb_ge_of_chunks (T := T) (M := Par.R P.N L * C) (b := b)
    (by unfold Par.coinLen at hT; exact hT) hQ hPQ
  have hcount : (1 - (1 - P.q L) ^ Par.R P.N L) * ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) ≤
      ((univ.filter fun u : Fin (Par.R P.N L * C) → Fin (2 ^ b) ↦ Q (toCh u)).card : ℝ) := by
    have h1 : (Fintype.card (Fin (2 ^ b)) : ℝ) = (2 : ℝ) ^ b := by simp
    rw [h1] at hrep
    refine hrep.trans ?_
    exact_mod_cast card_le_card fun u hu ↦ by
      simp only [mem_filter, mem_univ, true_and] at hu
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      obtain ⟨t, ht⟩ := hu
      refine ⟨t, t.2, ?_⟩
      rw [window_toCh_block]
      exact ht
  have hpos : (0 : ℝ) < ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) := by positivity
  have hq := P.one_sub_q_pow_le L
  refine le_trans ?_ hprob
  rw [le_div_iff₀ hpos]
  have h2 : (1 - 1 / (P.N : ℝ)) * ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) ≤
      (1 - (1 - P.q L) ^ Par.R P.N L) * ((2 : ℝ) ^ b) ^ (Par.R P.N L * C) :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  exact h2.trans hcount

end BCFGJPSSV26.Stable
