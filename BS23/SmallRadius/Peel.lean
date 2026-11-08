module

public import BS23.SmallRadius.RoundStep
public import BS23.SmallRadius.Ident

/-!
# Peeling: all `k` rounds succeed with high probability

The algorithm of [BS23, Theorem 1.3] peels off one cluster per round
(`BS23.SmallRadius.peelState`). This file shows that on a good frame, with probability at least
`1 - δ'/2` over the coins, the labels after `k` rounds cluster the sample within `δ'`
(`BS23.SmallRadius.peel_good`).

**Success of a round** (`BS23.SmallRadius.RoundOK`): the extracted set `C` is within
`E = δ' n / (2k)` in symmetric difference of the remaining part `T = S_j ∩ Rem` of a cluster `j`
that has more than `E_tot = δ' n / 2` points left.

**Bookkeeping** (abstract, on finsets: `BS23.SmallRadius.IsPeel`, `BS23.SmallRadius.RoundsOK`).
If rounds `0, …, r - 1` succeeded with clusters `j₀, …, j_{r-1}`:

* an unchosen cluster has lost at most `r E` points, the misclassified points of the earlier
  rounds (`BS23.SmallRadius.IsPeel.card_sdiff_le`);
* a chosen cluster `j_{r'}` keeps at most `E` points (`BS23.SmallRadius.IsPeel.card_chosen_le`), so
  the chosen clusters are distinct (`BS23.SmallRadius.IsPeel.js_ne`);
* for `r < k`, a cluster `c` with the most remaining points is unchosen, keeps at least half of its
  points and at least `w n / 2 - E_tot` of them (`BS23.SmallRadius.IsPeel.exists_cluster`): the
  hypotheses of `BS23.SmallRadius.round_hyp`;
* after `k` successful rounds, `π(r) = j_r` is a permutation, and every misclassified point lies in
  some `C_r ∆ T_r`, so at most `k E = δ' n / 2` points are misclassified
  (`BS23.SmallRadius.IsPeel.card_correct`). The points never extracted have label `0`; they are
  counted as errors unless they belong to `S_{j₀}`.

**One round** (`BS23.SmallRadius.card_round_bad_le`). On the program of the round, the solver
gives a pseudo-expectation (`BS23.SmallRadius.exists_roundPE`, valid by
`BS23.SmallRadius.SRFrame.Good.valid_problem_list`), whose tables satisfy the hypotheses of the
rounding lemma (`BS23.SmallRadius.round_hyp`) with the cross bound `εc` (a hypothesis,
`BS23.SmallRadius.CrossBound`). If the pivot has `|C ∆ T| ≤ E` and a cluster of more than
`τ* - θ = E_tot` points (`θ = τ* - E_tot ≥ w n / 4`), the round succeeds. By
`BS23.SmallRadius.RoundData.weighted_fail_le` and `BS23.SmallRadius.card_pick_mem_le`, at most a
`δ'/(2k)` fraction of the `2^b` coin values fail (`BS23.SmallRadius.round_arith`), as long as
`640 k² εc ≤ δ'² w n²` and `2^11 k² n ≤ δ'² w 2^n` (the soundness error is `2^{-n}`, the
accuracy of the solver at most `2^{-n}`, and `b = n + 8`).

**All rounds** (`BS23.SmallRadius.peel_good`): `BS23.SmallRadius.coinProb_seq_blockNat` sums the
failure probabilities over the `k` rounds.

**The cross bound** (`BS23.SmallRadius.crossBound_of_good`): identifiability
(`BS23.SmallRadius.IdCtx.cross_pairs_le`, on the context of the remaining points) gives
`εc = k² (2 n² ρ^s + 1)`, `ρ = 2^18 s / (Csep ln (1/w))`; its soundness error at norm
`n^(50t) ≤ 2^n` is at most `1/4` (`BS23.SmallRadius.sosErr_accOf_le`).
`BS23.SmallRadius.peel_good_of_sep` is `peel_good` with this `εc`.
-/

@[expose] public section

namespace BS23.SmallRadius

open Finset MvPolynomial SoS SoS.Solver
open scoped symmDiff

/-! ### Coin probabilities are monotone -/

theorem coinProb_mono {m : ℕ} {P P' : List Bool → Prop} (h : ∀ c, P c → P' c) :
    coinProb m P ≤ coinProb m P' := by
  classical
  rw [coinProb_eq_sum, coinProb_eq_sum]
  gcongr with c
  by_cases hc : P (List.ofFn c)
  · simp [hc, h _ hc]
  · simp only [hc, ite_false]
    split_ifs <;> norm_num

/-! ### Bookkeeping of the peeling -/

section Book

variable {n k : ℕ} {ℓ : Fin n → Fin k} {Rm Cs : ℕ → Finset (Fin n)} {js : ℕ → Fin k}

/-- The remaining points `Rm r` before round `r` are those that no earlier round extracted. -/
def IsPeel (Rm Cs : ℕ → Finset (Fin n)) : Prop := ∀ r i, i ∈ Rm r ↔ ∀ r' < r, i ∉ Cs r'

/-- **Rounds `0, …, r - 1` succeeded** with the clusters `js`: round `r'` extracted a set `Cs r'`
within `E` of the remaining part `T_{r'} = S_{js r'} ∩ Rm r'` of cluster `js r'`, which had more
than `Etot` points left. -/
def RoundsOK (ℓ : Fin n → Fin k) (Rm Cs : ℕ → Finset (Fin n)) (js : ℕ → Fin k) (Etot E : ℝ)
    (r : ℕ) : Prop :=
  ∀ r' < r, Etot < ((cluster ℓ (js r') ∩ Rm r').card : ℝ) ∧
    ((Cs r' ∆ (cluster ℓ (js r') ∩ Rm r')).card : ℝ) ≤ E

theorem IsPeel.mono (h : IsPeel Rm Cs) {r r' : ℕ} (hr : r' ≤ r) {i : Fin n} (hi : i ∈ Rm r) :
    i ∈ Rm r' :=
  (h r' i).2 fun r'' hr'' => (h r i).1 hi r'' (by omega)

theorem IsPeel.exists_of_not_mem (h : IsPeel Rm Cs) {r : ℕ} {i : Fin n} (hi : i ∉ Rm r) :
    ∃ r' < r, i ∈ Cs r' := by
  by_contra hne
  push Not at hne
  exact hi ((h r i).2 hne)

/-- **An unchosen cluster loses few points**: only the misclassified points of earlier rounds,
at most `r E`. -/
theorem IsPeel.card_sdiff_le (h : IsPeel Rm Cs) {Etot E : ℝ} {r : ℕ}
    (hok : RoundsOK ℓ Rm Cs js Etot E r) {j : Fin k} (hj : ∀ r' < r, js r' ≠ j) :
    ((cluster ℓ j \ Rm r).card : ℝ) ≤ r * E := by
  classical
  have hsub : cluster ℓ j \ Rm r ⊆
      (range r).biUnion fun r' => Cs r' ∆ (cluster ℓ (js r') ∩ Rm r') := by
    intro i hi
    obtain ⟨hiS, hiR⟩ := mem_sdiff.1 hi
    obtain ⟨r', hr', hiC⟩ := h.exists_of_not_mem hiR
    refine mem_biUnion.2 ⟨r', mem_range.2 hr',
      mem_symmDiff.2 (Or.inl ⟨hiC, fun h' => hj r' hr' ?_⟩)⟩
    have h1 : ℓ i = js r' := by simpa [cluster] using (mem_inter.1 h').1
    have h2 : ℓ i = j := by simpa [cluster] using hiS
    rw [← h1, h2]
  calc ((cluster ℓ j \ Rm r).card : ℝ)
      ≤ (((range r).biUnion fun r' => Cs r' ∆ (cluster ℓ (js r') ∩ Rm r')).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ r' ∈ range r, ((Cs r' ∆ (cluster ℓ (js r') ∩ Rm r')).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _r' ∈ range r, E := sum_le_sum fun r' hr' => (hok r' (mem_range.1 hr')).2
    _ = r * E := by rw [sum_const, card_range, nsmul_eq_mul]

/-- **A chosen cluster keeps few points**: after round `r'`, cluster `js r'` keeps at most
`|T_{r'} \ C_{r'}| ≤ E` points. -/
theorem IsPeel.card_chosen_le (h : IsPeel Rm Cs) {Etot E : ℝ} {r : ℕ}
    (hok : RoundsOK ℓ Rm Cs js Etot E r) {r' : ℕ} (hr' : r' < r) :
    ((cluster ℓ (js r') ∩ Rm r).card : ℝ) ≤ E := by
  have hsub : cluster ℓ (js r') ∩ Rm r ⊆ Cs r' ∆ (cluster ℓ (js r') ∩ Rm r') := by
    intro i hi
    obtain ⟨hiS, hiR⟩ := mem_inter.1 hi
    exact mem_symmDiff.2 (Or.inr ⟨mem_inter.2 ⟨hiS, h.mono hr'.le hiR⟩, (h r i).1 hiR r' hr'⟩)
  exact le_trans (by exact_mod_cast card_le_card hsub) (hok r' hr').2

/-- **The chosen clusters are distinct** (when `E ≤ Etot`). -/
theorem IsPeel.js_ne (h : IsPeel Rm Cs) {Etot E : ℝ} (hEE : E ≤ Etot) {r : ℕ}
    (hok : RoundsOK ℓ Rm Cs js Etot E r) {r₁ r₂ : ℕ} (h₁₂ : r₁ < r₂) (h₂ : r₂ < r) :
    js r₁ ≠ js r₂ := by
  intro he
  have h1 := h.card_chosen_le (r := r₂) (fun r' hr' => hok r' (by omega)) h₁₂
  rw [he] at h1
  linarith [(hok r₂ h₂).1]

/-- **The cluster of the next round.** If rounds `0, …, r - 1 < k - 1` succeeded, with
`E ≤ Etot`, `r E ≤ Etot`, `0 < Etot`, and every cluster has at least `a ≥ 4 Etot` points, then a
cluster `c` with the most remaining points keeps at least half of its points and at least
`a - Etot` of them. -/
theorem IsPeel.exists_cluster (h : IsPeel Rm Cs) {Etot E a : ℝ} {r : ℕ} (hr : r < k)
    (hok : RoundsOK ℓ Rm Cs js Etot E r) (hEtot : 0 < Etot) (hEE : E ≤ Etot)
    (hrE : r * E ≤ Etot) (hS : ∀ j, a ≤ (cluster ℓ j).card) (ha : 4 * Etot ≤ a) :
    ∃ c, (cluster ℓ c).card ≤ 2 * (cluster ℓ c ∩ Rm r).card ∧
      (∀ j, (cluster ℓ j ∩ Rm r).card ≤ (cluster ℓ c ∩ Rm r).card) ∧
      a - Etot ≤ ((cluster ℓ c ∩ Rm r).card : ℝ) := by
  classical
  obtain ⟨j₀, -, hj₀⟩ := exists_mem_notMem_of_card_lt_card (s := (range r).image js)
    (t := univ) (by
      rw [card_univ, Fintype.card_fin]
      exact (card_image_le.trans_eq (card_range r)).trans_lt hr)
  have hj₀' : ∀ r' < r, js r' ≠ j₀ := fun r' hr' he =>
    hj₀ (mem_image.2 ⟨r', mem_range.2 hr', he⟩)
  obtain ⟨c, -, hc⟩ := exists_max_image univ (fun j => (cluster ℓ j ∩ Rm r).card)
    ⟨j₀, mem_univ _⟩
  have hsplit : ∀ j, ((cluster ℓ j ∩ Rm r).card : ℝ) + ((cluster ℓ j \ Rm r).card : ℝ) =
      (cluster ℓ j).card := fun j => by exact_mod_cast card_inter_add_card_sdiff _ _
  have h0 : a - Etot ≤ ((cluster ℓ j₀ ∩ Rm r).card : ℝ) := by
    have := h.card_sdiff_le hok hj₀'
    linarith [hsplit j₀, hS j₀]
  have hc0 : ((cluster ℓ j₀ ∩ Rm r).card : ℝ) ≤ (cluster ℓ c ∩ Rm r).card := by
    exact_mod_cast hc j₀ (mem_univ _)
  have hcalive : ∀ r' < r, js r' ≠ c := by
    intro r' hr' he
    have := h.card_chosen_le hok hr'
    rw [he] at this
    linarith
  have hcS := h.card_sdiff_le hok hcalive
  refine ⟨c, ?_, fun j => hc j (mem_univ _), h0.trans hc0⟩
  have : ((cluster ℓ c).card : ℝ) ≤ 2 * (cluster ℓ c ∩ Rm r).card := by
    linarith [hsplit c, hS c]
  exact_mod_cast this

/-- **The final count.** If all `k` rounds succeeded with `E ≤ Etot`, and every point extracted in
round `r < k` has label `r`, then for the permutation `π(r) = js r`, at most `k E` points are
misclassified. -/
theorem IsPeel.card_correct (h : IsPeel Rm Cs) {Etot E : ℝ} (hEE : E ≤ Etot)
    (hok : RoundsOK ℓ Rm Cs js Etot E k) (lab : Fin n → ℕ)
    (hlab : ∀ r < k, ∀ i ∈ Cs r, lab i = r) :
    ∃ π : Equiv.Perm (Fin k), (n : ℝ) - k * E ≤
      ∑ i : Fin k, (((univ.filter fun j => lab j = (i : ℕ)) ∩ cluster ℓ (π i)).card : ℝ) := by
  classical
  have hinj : Function.Injective fun i : Fin k => js i := by
    intro i₁ i₂ he
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · exact h.js_ne hEE hok hlt i₂.2 he
    · exact h.js_ne hEE hok hlt i₁.2 he.symm
  set π : Equiv.Perm (Fin k) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    with hπ
  have hπi : ∀ i, π i = js i := fun i => rfl
  refine ⟨π, ?_⟩
  set G := univ.filter fun x : Fin n => lab x = (π.symm (ℓ x) : ℕ) with hG
  have hset : ∀ i : Fin k, (univ.filter fun j => lab j = (i : ℕ)) ∩ cluster ℓ (π i) =
      G.filter fun x => π.symm (ℓ x) = i := by
    intro i
    ext x
    simp only [hG, mem_filter, mem_univ, true_and, mem_inter, cluster]
    constructor
    · rintro ⟨h1, h2⟩
      have : π.symm (ℓ x) = i := by rw [h2, Equiv.symm_apply_apply]
      exact ⟨by rw [this]; exact h1, this⟩
    · rintro ⟨h1, h2⟩
      rw [h2] at h1
      exact ⟨h1, by rw [← h2, Equiv.apply_symm_apply]⟩
  have hsum : ∑ i : Fin k, (((univ.filter fun j => lab j = (i : ℕ)) ∩ cluster ℓ (π i)).card : ℝ) =
      G.card := by
    simp_rw [hset]
    rw [card_eq_sum_card_fiberwise (s := G) (t := univ) (f := fun x => π.symm (ℓ x))
      (fun x _ => mem_coe.2 (mem_univ _))]
    push_cast
    rfl
  have hbad : univ.filter (fun x : Fin n => ¬ lab x = (π.symm (ℓ x) : ℕ)) ⊆
      (range k).biUnion fun r => Cs r ∆ (cluster ℓ (js r) ∩ Rm r) := by
    intro x hx
    have hx' : ¬ lab x = (π.symm (ℓ x) : ℕ) := (mem_filter.1 hx).2
    set i := π.symm (ℓ x) with hi
    have hji : js i = ℓ x := by rw [← hπi, hi, Equiv.apply_symm_apply]
    have hxC : x ∉ Cs i := fun hC => hx' (hlab i i.2 x hC)
    rw [mem_biUnion]
    by_cases hR : x ∈ Rm i
    · exact ⟨i, mem_range.2 i.2, mem_symmDiff.2 (Or.inr ⟨mem_inter.2
        ⟨by simp [cluster, hji], hR⟩, hxC⟩)⟩
    · obtain ⟨r', hr', hxC'⟩ := h.exists_of_not_mem hR
      refine ⟨r', mem_range.2 (hr'.trans i.2), mem_symmDiff.2 (Or.inl ⟨hxC', fun hT => ?_⟩)⟩
      have h1 : ℓ x = js r' := by simpa [cluster] using (mem_inter.1 hT).1
      exact h.js_ne hEE hok hr' i.2 (h1.symm.trans hji.symm)
  have hcard : (G.card : ℝ) +
      ((univ.filter fun x : Fin n => ¬ lab x = (π.symm (ℓ x) : ℕ)).card : ℝ) = n := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun x : Fin n => lab x = (π.symm (ℓ x) : ℕ))
    rw [card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have hb : ((univ.filter fun x : Fin n => ¬ lab x = (π.symm (ℓ x) : ℕ)).card : ℝ) ≤ k * E := by
    calc ((univ.filter fun x : Fin n => ¬ lab x = (π.symm (ℓ x) : ℕ)).card : ℝ)
        ≤ (((range k).biUnion fun r => Cs r ∆ (cluster ℓ (js r) ∩ Rm r)).card : ℝ) := by
          exact_mod_cast card_le_card hbad
      _ ≤ ∑ r ∈ range k, ((Cs r ∆ (cluster ℓ (js r) ∩ Rm r)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ _r ∈ range k, E := sum_le_sum fun r hr => (hok r (mem_range.1 hr)).2
      _ = k * E := by rw [sum_const, card_range, nsmul_eq_mul]
  rw [hsum]
  linarith

end Book

/-! ### The peeling as bookkeeping -/

section PeelBook

variable {n d k : ℕ}

/-- **A successful round** on the remaining points `Rem`: the extracted list `C` is within `E` in
symmetric difference of the remaining part `S_j ∩ Rem` of a cluster `j` with more than `Etot`
remaining points. -/
def RoundOK (ℓ : Fin n → Fin k) (Etot E : ℝ) (Rem C : List (Fin n)) : Prop :=
  ∃ j : Fin k, Etot < ((cluster ℓ j ∩ Rem.toFinset).card : ℝ) ∧
    ((C.toFinset ∆ (cluster ℓ j ∩ Rem.toFinset)).card : ℝ) ≤ E

variable (Q : RoundPar) (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) (us : ℕ → ℕ)

/-- The peeling, as finsets, satisfies the bookkeeping hypothesis `IsPeel`. -/
theorem isPeel_peel :
    IsPeel (fun r => (peelRem Q z b us r).toFinset) (fun r => (peelC Q z b us r).toFinset) := by
  intro r i
  simp only [List.mem_toFinset]
  exact mem_peelRem_iff

variable {Q z b us}

/-- Choosing the clusters of successful rounds. -/
theorem exists_roundsOK (hk : 1 ≤ k) {ℓ : Fin n → Fin k} {Etot E : ℝ} {r : ℕ}
    (hok : ∀ r' < r, RoundOK ℓ Etot E (peelRem Q z b us r') (peelC Q z b us r')) :
    ∃ js : ℕ → Fin k, RoundsOK ℓ (fun r => (peelRem Q z b us r).toFinset)
      (fun r => (peelC Q z b us r).toFinset) js Etot E r := by
  have h : ∀ r', ∃ j : Fin k, r' < r →
      Etot < ((cluster ℓ j ∩ (peelRem Q z b us r').toFinset).card : ℝ) ∧
        (((peelC Q z b us r').toFinset ∆ (cluster ℓ j ∩ (peelRem Q z b us r').toFinset)).card :
          ℝ) ≤ E := fun r' => by
    by_cases hr : r' < r
    · obtain ⟨j, hj⟩ := hok r' hr
      exact ⟨j, fun _ => hj⟩
    · exact ⟨⟨0, hk⟩, fun h => absurd h hr⟩
  choose js hjs using h
  exact ⟨js, fun r' hr' => hjs r' hr'⟩

/-- **After `k` successful rounds**, the labels cluster the sample within `ε`, when
`k E ≤ ε n` and `E ≤ Etot`. -/
theorem clustersWithin_peel {ℓ : Fin n → Fin k} {Etot E ε : ℝ} (hk : 1 ≤ k) (hn : 0 < n)
    (hEE : E ≤ Etot) (hkE : k * E ≤ ε * n)
    (hok : ∀ r < k, RoundOK ℓ Etot E (peelRem Q z b us r) (peelC Q z b us r)) :
    ClustersWithin ε ℓ (List.ofFn (peelLab Q z b us k)) := by
  classical
  obtain ⟨js, hjs⟩ := exists_roundsOK hk hok
  obtain ⟨π, hπ⟩ := (isPeel_peel Q z b us).card_correct hEE hjs (peelLab Q z b us k)
    fun r hr i hi => peelLab_of_mem_peelC (List.mem_toFinset.1 hi) hr
  refine ⟨List.length_ofFn, fun j => by rw [outCluster_ofFn]; exact peelLab_lt hk j, π, ?_⟩
  simp_rw [outCluster_ofFn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hnR]
  linarith

/-- The remaining points after `r` rounds only read the first `r nb` coins. -/
theorem peelRem_blockNat_take (c : List Bool) (r : ℕ) :
    peelRem Q z b (blockNat (c.take (r * Q.nb)) Q.nb) r = peelRem Q z b (blockNat c Q.nb) r := by
  rw [peelRem, peelRem, peelState_take]

/-- **Round `r` in terms of its coins**: with the first `r nb` coins and the `r`-th block. -/
theorem roundOK_take_iff {ℓ : Fin n → Fin k} {Etot E : ℝ} (c : List Bool) (r : ℕ) :
    RoundOK ℓ Etot E (peelRem Q z b (blockNat (c.take (r * Q.nb)) Q.nb) r)
        (srRound Q z b (peelRem Q z b (blockNat (c.take (r * Q.nb)) Q.nb) r) (blockNat c Q.nb r)) ↔
      RoundOK ℓ Etot E (peelRem Q z b (blockNat c Q.nb) r) (peelC Q z b (blockNat c Q.nb) r) := by
  rw [← peelC_eq_take, peelRem_blockNat_take]

end PeelBook

/-! ### One round -/

section RoundSet

variable {n d k : ℕ} {Q : RoundPar} {z : Fin n → Fin d → ℚ} {b : List ℕ → ℚ} {Rem : List (Fin n)}
  {E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)}

/-- **The error of a round, in the tables**: the symmetric difference of the output of the round
and the remaining part `S_j ∩ Rem` of a cluster `j` has the size of
`roundSet i₀ ∆ clSet j` for the pivot `i₀`. -/
theorem card_symmDiff_srRound (hE : RoundPE Q z b Rem E) [NeZero Rem.length] (hnd : Rem.Nodup)
    (lab : Fin n → Fin k) (u : ℕ) (j : Fin k) :
    ((srRound Q z b Rem u).toFinset ∆ (cluster lab j ∩ Rem.toFinset)).card =
      ((roundData lab Q Rem E).roundSet (pivotE Q Rem E u) ∆
        (roundData lab Q Rem E).clSet j).card := by
  classical
  have hinj : Function.Injective Rem.get := List.nodup_iff_injective_get.1 hnd
  have h1 : (srRound Q z b Rem u).toFinset =
      ((roundData lab Q Rem E).roundSet (pivotE Q Rem E u)).image Rem.get := by
    ext x
    simp only [List.mem_toFinset, mem_image]
    constructor
    · intro hx
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 (srRound_subset Q z b Rem hx)
      exact ⟨i, (hE.mem_srRound_iff hnd lab u i).1 hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact (hE.mem_srRound_iff hnd lab u i).2 hi
  have h2 : cluster lab j ∩ Rem.toFinset = ((roundData lab Q Rem E).clSet j).image Rem.get := by
    ext x
    simp only [mem_inter, List.mem_toFinset, mem_image, RoundData.mem_clSet, cluster, mem_filter,
      mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxR⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hxR
      exact ⟨i, hx, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨hi, List.get_mem _ _⟩
  rw [h1, h2, ← image_symmDiff _ _ hinj, card_image_of_injective _ hinj]

end RoundSet

/-- The accuracy of the solver in a round is at most `2^{-ne}`. -/
theorem roundAcc_le {n d : ℕ} (Q : RoundPar) (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ)
    (Rem : List (Fin n)) : (roundAcc Q z b Rem : ℝ) ≤ 1 / 2 ^ Q.ne := by
  change (accOf Q.ne (roundProb Q z b Rem) : ℝ) ≤ _
  rw [accOf_cast]
  refine one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) ?_)
  unfold accExp
  calc Q.ne ≤ Q.ne + (encProblem (roundProb Q z b Rem)).length + 2 := by omega
    _ ≤ _ := Nat.le_self_pow (by norm_num) _

/-! ### The arithmetic of one round -/

/-- **The consequences of `2^11 k² n ≤ δ'² w 2^n`** used for the errors of a round. -/
theorem err_facts {k n : ℕ} {w δ' : ℝ} (hk : (1 : ℝ) ≤ k) (hn : (1 : ℝ) ≤ n) (hw : 0 < w)
    (hw1 : w ≤ 1) (hδ : 0 < δ') (hδw : δ' ≤ w / 4)
    (herr : 2 ^ 11 * (k : ℝ) ^ 2 * n ≤ δ' ^ 2 * w * 2 ^ n) :
    48 * (k : ℝ) ^ 2 * (1 / 2 ^ n) ≤ δ' ^ 2 * n ∧
      1152 * (k : ℝ) ^ 2 * (1 / 2 ^ n) ≤ δ' ^ 2 * w ∧
      (n : ℝ) ≤ δ' / (8 * k) * 2 ^ (n + 8) := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk
  have hk2k : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hkn : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * n := le_mul_of_one_le_right (by positivity) hn
  have hδ2 : 0 ≤ δ' ^ 2 * 2 ^ n := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_one_div, div_le_iff₀ h2n]
    have : δ' ^ 2 * w * 2 ^ n ≤ δ' ^ 2 * n * 2 ^ n := by
      have := mul_le_mul_of_nonneg_left (hw1.trans hn) hδ2
      linarith
    nlinarith
  · rw [mul_one_div, div_le_iff₀ h2n]
    nlinarith
  · have hδw1 : δ' * w ≤ 1 := by nlinarith
    have h1 : δ' ^ 2 * w * 2 ^ n ≤ δ' * 2 ^ n := by
      have := mul_le_mul_of_nonneg_left hδw1 (by positivity : (0 : ℝ) ≤ δ' * 2 ^ n)
      nlinarith
    have h2 : (n : ℝ) * (8 * k) ≤ δ' * 2 ^ (n + 8) := by
      rw [pow_add]
      have : (8 : ℝ) * k * n ≤ 2 ^ 11 * (k : ℝ) ^ 2 * n := by
        have := mul_le_mul_of_nonneg_right hk2k (by positivity : (0 : ℝ) ≤ n)
        nlinarith
      nlinarith
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith

/-- **The arithmetic of one round**: with `E = δ' n / (2k) ≤ θ`, `Z ≥ w n / 8`, `N ≤ n` and the
error bounds, the bound of `weighted_fail_le` and `card_pick_mem_le` on the failing coin values
is at most `δ'/(2k)` times their number `P = 2^b`. -/
theorem round_arith {k n N : ℕ} {w δ' γ ε err Z θ P : ℝ} (hk : (1 : ℝ) ≤ k) (hn : (0 : ℝ) < n)
    (hw : 0 < w) (hδ : 0 < δ') (hθ : δ' * n / (2 * k) ≤ θ) (hZ : w * n / 8 ≤ Z) (hγ0 : 0 ≤ γ)
    (hε0 : 0 ≤ ε) (herr0 : 0 ≤ err) (hN : (N : ℝ) ≤ n)
    (hγ : 48 * (k : ℝ) ^ 2 * γ ≤ δ' ^ 2 * n) (hε : 640 * (k : ℝ) ^ 2 * ε ≤ δ' ^ 2 * w * (n : ℝ) ^ 2)
    (herr : 1152 * (k : ℝ) ^ 2 * err ≤ δ' ^ 2 * w) (hP : 0 < P)
    (hNP : (N : ℝ) ≤ δ' / (8 * k) * P) :
    P * (2 * (γ * Z + 2 * ε + 3 * (N : ℝ) ^ 2 * err) / (δ' * n / (2 * k)) +
        (γ * Z + ε + 3 * (N : ℝ) ^ 2 * err) / θ) / Z + N ≤ δ' / (2 * k) * P := by
  set A := 2 * (γ * Z + 2 * ε + 3 * (N : ℝ) ^ 2 * err) with hA
  set B := γ * Z + ε + 3 * (N : ℝ) ^ 2 * err with hB
  set E := δ' * n / (2 * k) with hE
  have hk0 : (0 : ℝ) < k := by linarith
  have hE0 : 0 < E := by positivity
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity) hZ
  have hθ0 : 0 < θ := hE0.trans_le hθ
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hB0 : 0 ≤ B := by positivity
  have h2 : A / E + B / θ ≤ (A + B) / E := by
    rw [add_div A B E]
    exact add_le_add le_rfl (div_le_div_of_nonneg_left hB0 hE0 hθ)
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hmain : 16 * (k : ℝ) ^ 2 * (A + B) ≤ 3 * δ' ^ 2 * n * Z := by
    have e1 : 48 * (k : ℝ) ^ 2 * γ * Z ≤ δ' ^ 2 * n * Z := mul_le_mul_of_nonneg_right hγ hZ0.le
    have e2 : δ' ^ 2 * w * (n : ℝ) ^ 2 ≤ 8 * (δ' ^ 2 * n * Z) := by
      have := mul_le_mul_of_nonneg_left hZ (by positivity : (0 : ℝ) ≤ δ' ^ 2 * n)
      nlinarith
    have e3 : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ hN0 hN 2
    have e4 : 144 * (k : ℝ) ^ 2 * (N : ℝ) ^ 2 * err ≤ 144 * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * err := by
      have := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 144 * (k : ℝ) ^ 2 * err)
      nlinarith
    have e5 : 1152 * (k : ℝ) ^ 2 * err * (n : ℝ) ^ 2 ≤ δ' ^ 2 * w * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right herr (by positivity)
    rw [hA, hB]
    nlinarith
  have h3 : (A + B) / E ≤ 3 * δ' / (8 * k) * Z := by
    rw [div_le_iff₀ hE0]
    have hR : 3 * δ' / (8 * k) * Z * E = 3 * δ' ^ 2 * n * Z / (16 * (k : ℝ) ^ 2) := by
      rw [hE]
      field_simp
      ring
    rw [hR, le_div_iff₀ (by positivity)]
    linarith
  have h4 : P * (A / E + B / θ) / Z ≤ P * (3 * δ' / (8 * k)) := by
    rw [div_le_iff₀ hZ0]
    calc P * (A / E + B / θ) ≤ P * ((A + B) / E) := mul_le_mul_of_nonneg_left h2 hP.le
      _ ≤ P * (3 * δ' / (8 * k) * Z) := mul_le_mul_of_nonneg_left h3 hP.le
      _ = P * (3 * δ' / (8 * k)) * Z := by ring
  have h5 : P * (3 * δ' / (8 * k)) + δ' / (8 * k) * P = δ' / (2 * k) * P := by
    field_simp
    ring
  linarith

/-! ### The hypotheses on the rounds -/

section Hyps

variable {n d k : ℕ}

/-- **The budget suffices for every round**: `(|P| + 2)^(64 t + 1) ≤ Lb` for the program `P` of
the round on any list `Rem` of remaining points without repetitions (`roundBudgetOK`). -/
def BudgetFits (Q : RoundPar) (z : Fin n → Fin d → ℚ) (b : List ℕ → ℚ) : Prop :=
  ∀ Rem : List (Fin n), Rem.Nodup →
    ((encProblem (roundProb Q z b Rem)).length + 2) ^ (64 * Q.t + 1) ≤ Q.Lb

/-- **The cross bound `εc`** (identifiability): on any list `Rem` of remaining points without
repetitions, every pseudo-expectation behind the round (`RoundPE`) puts mass at most `εc` on the
pairs of points of different clusters. -/
def CrossBound (F : SRFrame n d k) (Q : RoundPar) (b : List ℕ → ℚ) (εc : ℝ) : Prop :=
  ∀ (Rem : List (Fin n)) (E : PseudoExpectation (Fin (remLay Q Rem d).N) (64 * Q.t)),
    Rem.Nodup → RoundPE Q F.z b Rem E →
      ∑ i, ∑ i' with F.ℓ (Rem.get i) ≠ F.ℓ (Rem.get i'),
        E (X ((remLay Q Rem d).wv i) * X ((remLay Q Rem d).wv i')) ≤ εc

end Hyps

/-! ### One round fails rarely -/

section Round

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {wq Rq : ℚ} {Lb : ℕ}

/-- **One round fails for few coin values.** On a good frame with the degrees `s = sDeg wq`,
`t = tDeg wq Rq` of the algorithm, a budget that cuts nothing and suffices for the solver, and a
cross bound `εc`, let `Rem` (without repetitions) be the remaining points and `c` a cluster with
the most remaining points, keeping at least half of its points and at least
`w n / 2 - δ' n / 2` of them. Then at most a `δ'/(2k)` fraction of the `2^(n + 8)` coin values
make the round fail (`RoundOK` with `Etot = δ' n / 2`, `E = δ' n / (2k)`), when `δ' ≤ w / 4`,
`640 k² εc ≤ δ'² w n²` and `2^11 k² n ≤ δ'² w 2^n`. -/
theorem card_round_bad_le (hF : F.Good w R Csep (sDeg wq) (tDeg wq Rq))
    (hfit : Fits d (sDeg wq) (tDeg wq Rq) (tDeg wq Rq / sDeg wq) Lb)
    (hbud : BudgetFits (srPar wq Rq n Lb) F.z (bOf F.z (tDeg wq Rq) Lb))
    {εc : ℝ} (hcross : CrossBound F (srPar wq Rq n Lb) (bOf F.z (tDeg wq Rq) Lb) εc)
    {δ' : ℝ} (hδ : 0 < δ') (hδw : δ' ≤ w / 4)
    (hε : 640 * (k : ℝ) ^ 2 * εc ≤ δ' ^ 2 * w * (n : ℝ) ^ 2)
    (herr : 2 ^ 11 * (k : ℝ) ^ 2 * n ≤ δ' ^ 2 * w * 2 ^ n)
    {Rem : List (Fin n)} (hRem : Rem.Nodup) {c : Fin k}
    (hT : (cluster F.ℓ c).card ≤ 2 * (cluster F.ℓ c ∩ Rem.toFinset).card)
    (hmax : ∀ j, (cluster F.ℓ j ∩ Rem.toFinset).card ≤ (cluster F.ℓ c ∩ Rem.toFinset).card)
    (hτ : w * n / 2 - δ' * n / 2 ≤ ((cluster F.ℓ c ∩ Rem.toFinset).card : ℝ)) :
    (Nat.card {u : Fin (2 ^ (srPar wq Rq n Lb).nb) // ¬ RoundOK F.ℓ (δ' * n / 2)
      (δ' * n / (2 * k)) Rem (srRound (srPar wq Rq n Lb) F.z (bOf F.z (tDeg wq Rq) Lb) Rem u)} :
        ℝ) ≤ δ' / (2 * k) * 2 ^ (srPar wq Rq n Lb).nb := by
  classical
  set Q := srPar wq Rq n Lb with hQ
  set bb := bOf F.z (tDeg wq Rq) Lb with hbb
  have hk1 : (1 : ℝ) ≤ k := by
    have := hF.params.two_le_k
    exact_mod_cast (by omega : 1 ≤ k)
  have hk0 : (0 : ℝ) < k := by linarith
  have hn := hF.n_pos_real
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hF.n_pos
  have hw := hF.w_pos
  have hw1 := hF.params.w_le_one
  -- the solver's pseudo-expectation and the hypotheses of the rounding lemma
  have hval : (roundProb Q F.z bb Rem).Valid := hF.valid_problem_list hfit hRem c hT
  obtain ⟨E, hE⟩ := exists_roundPE hval (roundBudgetOK hval (hbud Rem hRem))
  have hH := round_hyp hF (Q := Q) rfl rfl rfl rfl rfl hfit hRem hT hmax hE (ε := max εc 0)
    ((hcross Rem E hRem hE).trans (le_max_left _ _))
  set D := roundData F.ℓ Q Rem E with hD
  set τs : ℝ := ((cluster F.ℓ c ∩ Rem.toFinset).card : ℝ) with hτs
  set Etot : ℝ := δ' * n / 2 with hEtot
  set Er : ℝ := δ' * n / (2 * k) with hEr
  set θ : ℝ := τs - Etot with hθ
  have hδn : δ' * n ≤ w * n / 4 := by nlinarith
  have hwn : 0 < w * n := mul_pos hw hn
  have hτpos : 0 < τs := by linarith
  have hθge : w * n / 4 ≤ θ := by linarith
  have hEr0 : 0 < Er := by positivity
  have hEr2 : Er ≤ δ' * n / 2 := by
    rw [hEr, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hk1 (mul_pos hδ hn).le]
  have hErθ : Er ≤ θ := by linarith
  have hθ0 : 0 < θ := by linarith
  have hZ : w * n / 8 ≤ D.Z := by have := hH.half_le_Z; linarith
  have hZ0 : 0 < D.Z := by linarith
  have hN0 : 0 < Rem.length := by
    have := hH.le_card
    exact_mod_cast hτpos.trans_le this
  have : NeZero Rem.length := ⟨hN0.ne'⟩
  have hNn : (Rem.length : ℝ) ≤ n := by
    have := hRem.length_le_card
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  -- the failing pivots
  set ω : Fin Rem.length → ℝ := fun i => max (D.mw i) 0 with hω
  set Fail := univ.filter fun i₀ : Fin Rem.length =>
    Er < ((D.roundSet i₀ ∆ D.clSet (D.cl i₀)).card : ℝ) ∨ (D.csize (D.cl i₀) : ℝ) ≤ τs - θ
    with hFail
  have hbad : ∀ u : ℕ, ¬ RoundOK F.ℓ Etot Er Rem (srRound Q F.z bb Rem u) →
      pick ω Q.nb u ∈ Fail := by
    intro u hu
    by_contra hnot
    apply hu
    have hpe : pivotE Q Rem E u = pick ω Q.nb u := pivotE_eq_pick F.ℓ E u
    rw [← hpe] at hnot
    simp only [hFail, mem_filter, mem_univ, true_and, not_or, not_lt, not_le] at hnot
    obtain ⟨h1, h2⟩ := hnot
    refine ⟨F.ℓ (Rem.get (pivotE Q Rem E u)), ?_, ?_⟩
    · have hc : (D.csize (D.cl (pivotE Q Rem E u)) : ℝ) =
          ((cluster F.ℓ (F.ℓ (Rem.get (pivotE Q Rem E u))) ∩ Rem.toFinset).card : ℝ) := by
        exact_mod_cast SRFrame.Good.card_filter_get_eq hRem F.ℓ _
      rw [← hc]
      linarith
    · rw [card_symmDiff_srRound hE hRem F.ℓ u]
      exact h1
  -- counting the failing coin values
  have hcard1 : (Nat.card {u : Fin (2 ^ Q.nb) // ¬ RoundOK F.ℓ Etot Er Rem
      (srRound Q F.z bb Rem u)} : ℝ) ≤
      ((#{u : Fin (2 ^ Q.nb) | pick ω Q.nb u ∈ Fail} : ℕ) : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hsub : (univ.filter fun u : Fin (2 ^ Q.nb) =>
        ¬ RoundOK F.ℓ Etot Er Rem (srRound Q F.z bb Rem u)) ⊆
        univ.filter fun u : Fin (2 ^ Q.nb) => pick ω Q.nb u ∈ Fail :=
      fun u hu => mem_filter.2 ⟨mem_univ _, hbad u (mem_filter.1 hu).2⟩
    exact_mod_cast card_le_card hsub
  have hpick := card_pick_mem_le (K := ℝ) (ω := ω) (fun i => le_max_right _ _) hZ0 Q.nb Fail
  have hwf : ∑ i ∈ Fail, ω i ≤ 2 * ((roundAcc Q F.z bb Rem : ℝ) * D.Z + 2 * max εc 0 +
      3 * (Rem.length : ℝ) ^ 2 * (1 / 2 ^ Q.ne)) / Er +
      ((roundAcc Q F.z bb Rem : ℝ) * D.Z + max εc 0 + 3 * (Rem.length : ℝ) ^ 2 * (1 / 2 ^ Q.ne)) /
        θ := RoundData.weighted_fail_le hH hEr0 hθ0
  have hFailN : ((#Fail : ℕ) : ℝ) ≤ Rem.length := by
    exact_mod_cast (card_le_univ _).trans_eq (Fintype.card_fin _)
  have hZeq : ∑ j, ω j = D.Z := rfl
  have h2b : (0 : ℝ) < 2 ^ Q.nb := by positivity
  -- the arithmetic
  have hγle := roundAcc_le Q F.z bb Rem
  have hne : Q.ne = n := rfl
  have hnb : Q.nb = n + 8 := rfl
  rw [hne] at hγle hwf
  obtain ⟨e1, e2, e3⟩ := err_facts hk1 hn1 hw hw1 hδ hδw herr
  have hγ0 : (0 : ℝ) ≤ roundAcc Q F.z bb Rem := by exact_mod_cast (roundAcc_pos Q F.z bb Rem).le
  have hεp : 640 * (k : ℝ) ^ 2 * max εc 0 ≤ δ' ^ 2 * w * (n : ℝ) ^ 2 := by
    rcases le_total εc 0 with h | h
    · rw [max_eq_right h, mul_zero]
      positivity
    · rw [max_eq_left h]
      exact hε
  have harith : (2 : ℝ) ^ Q.nb * (2 * ((roundAcc Q F.z bb Rem : ℝ) * D.Z + 2 * max εc 0 +
        3 * (Rem.length : ℝ) ^ 2 * (1 / 2 ^ n)) / Er +
        ((roundAcc Q F.z bb Rem : ℝ) * D.Z + max εc 0 + 3 * (Rem.length : ℝ) ^ 2 * (1 / 2 ^ n)) /
          θ) / D.Z + Rem.length ≤ δ' / (2 * k) * 2 ^ Q.nb :=
    round_arith (k := k) (n := n) (N := Rem.length) (w := w) (δ' := δ')
    (γ := (roundAcc Q F.z bb Rem : ℝ)) (ε := max εc 0) (err := 1 / 2 ^ n) (Z := D.Z) (θ := θ)
    (P := 2 ^ Q.nb) hk1 hn hw hδ hErθ hZ hγ0 (le_max_right _ _) (by positivity) hNn
    (le_trans (mul_le_mul_of_nonneg_left hγle (by positivity)) e1)
    hεp e2 h2b
    (hNn.trans (by rw [hnb]; exact e3))
  have hstep : (2 : ℝ) ^ Q.nb * (∑ i ∈ Fail, ω i) / (∑ j, ω j) ≤
      2 ^ Q.nb * (2 * ((roundAcc Q F.z bb Rem : ℝ) * D.Z + 2 * max εc 0 +
        3 * (Rem.length : ℝ) ^ 2 * (1 / 2 ^ n)) / Er +
        ((roundAcc Q F.z bb Rem : ℝ) * D.Z + max εc 0 + 3 * (Rem.length : ℝ) ^ 2 * (1 / 2 ^ n)) /
          θ) / D.Z := by
    rw [hZeq]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwf h2b.le) hZ0.le
  linarith

end Round

/-! ### All rounds -/

section Main

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {wq Rq : ℚ} {Lb : ℕ}

/-- **Peeling succeeds with high probability** [BS23, §7]. On a good frame with
the degrees `s = sDeg wq`, `t = tDeg wq Rq` of the algorithm, a budget that cuts nothing
(`Fits`) and suffices for the solver in every round (`BudgetFits`), and a cross bound `εc`
(`CrossBound`), for `0 < δ' ≤ w / 4` with `640 k² εc ≤ δ'² w n²` and `2^11 k² n ≤ δ'² w 2^n`:
over `T ≥ k (n + 8)` coins, the labels after `k` rounds of peeling cluster the sample within `δ'`
with probability at least `1 - δ'/2`. -/
theorem peel_good (hF : F.Good w R Csep (sDeg wq) (tDeg wq Rq))
    (hfit : Fits d (sDeg wq) (tDeg wq Rq) (tDeg wq Rq / sDeg wq) Lb)
    (hbud : BudgetFits (srPar wq Rq n Lb) F.z (bOf F.z (tDeg wq Rq) Lb))
    {εc : ℝ} (hcross : CrossBound F (srPar wq Rq n Lb) (bOf F.z (tDeg wq Rq) Lb) εc)
    {δ' : ℝ} (hδ : 0 < δ') (hδw : δ' ≤ w / 4)
    (hε : 640 * (k : ℝ) ^ 2 * εc ≤ δ' ^ 2 * w * (n : ℝ) ^ 2)
    (herr : 2 ^ 11 * (k : ℝ) ^ 2 * n ≤ δ' ^ 2 * w * 2 ^ n)
    {T : ℕ} (hT : k * coinBits n ≤ T) :
    1 - δ' / 2 ≤ coinProb T (fun c => ClustersWithin δ' F.ℓ (List.ofFn
      (peelLab (srPar wq Rq n Lb) F.z (bOf F.z (tDeg wq Rq) Lb) (blockNat c (coinBits n)) k))) := by
  classical
  set Q := srPar wq Rq n Lb with hQ
  set bb := bOf F.z (tDeg wq Rq) Lb with hbb
  have hk1 : 1 ≤ k := by have := hF.params.two_le_k; omega
  have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0 : ℝ) < k := by linarith
  have hn := hF.n_pos_real
  have hw := hF.w_pos
  set Etot : ℝ := δ' * n / 2 with hEtot
  set Er : ℝ := δ' * n / (2 * k) with hEr
  have hEtot0 : 0 < Etot := by positivity
  have hkEr : (k : ℝ) * Er = Etot := by
    rw [hEr, hEtot]
    field_simp
  have hEr0 : 0 < Er := by positivity
  have hErEtot : Er ≤ Etot := by nlinarith
  have hseq := coinProb_seq_blockNat (k := k) (b := Q.nb) (T := T) hT (δ := δ' / (2 * k))
    (fun r p u => ¬ RoundOK F.ℓ Etot Er (peelRem Q F.z bb (blockNat p Q.nb) r)
      (srRound Q F.z bb (peelRem Q F.z bb (blockNat p Q.nb) r) u)) ?_
  · have hkδ : (k : ℝ) * (δ' / (2 * k)) = δ' / 2 := by
      field_simp
    rw [hkδ] at hseq
    refine hseq.trans (coinProb_mono fun c hc => ?_)
    change ClustersWithin δ' F.ℓ (List.ofFn (peelLab Q F.z bb (blockNat c Q.nb) k))
    refine clustersWithin_peel hk1 hF.n_pos hErEtot ?_ fun r hr => ?_
    · rw [hkEr]
      nlinarith
    · have h := hc r hr
      simp only [not_not] at h
      exact (roundOK_take_iff c r).1 h
  · intro r hr p hp hprev
    have hprev' : ∀ r' < r, RoundOK F.ℓ Etot Er (peelRem Q F.z bb (blockNat p Q.nb) r')
        (peelC Q F.z bb (blockNat p Q.nb) r') := by
      intro r' hr'
      have h := hprev r' hr'
      simp only [not_not] at h
      exact (roundOK_take_iff p r').1 h
    obtain ⟨js, hjs⟩ := exists_roundsOK hk1 hprev'
    have hrE : (r : ℝ) * Er ≤ Etot := by
      rw [← hkEr]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hr.le) hEr0.le
    have h4 : 4 * Etot ≤ w * n / 2 := by
      rw [hEtot]
      nlinarith
    obtain ⟨c, hTc, hmax, hτ⟩ := (isPeel_peel Q F.z bb (blockNat p Q.nb)).exists_cluster hr hjs
      hEtot0 hErEtot hrE (fun j => hF.w_mul_le_card j) h4
    exact card_round_bad_le hF hfit hbud hcross hδ hδw hε herr (peelRem_nodup Q F.z bb _ r) hTc
      hmax hτ

end Main

/-! ### The cross bound from identifiability -/

/-- `2 (2^X 2^Y) 4 ≤ 2^Z` when `X + Y + 3 ≤ Z`. -/
theorem two_mul_pow_mul_four_le {X Y Z : ℕ} (h : X + Y + 3 ≤ Z) :
    2 * ((2 : ℝ) ^ X * 2 ^ Y) * 4 ≤ 2 ^ Z := by
  have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h
  rw [pow_add, pow_add] at this
  norm_num at this
  linarith

/-- **The soundness error of a round at norm `M ≤ 2^ne`** is at most `1/4`: for the accuracy
`η = 2^{-(ne + |P| + 2)²}` of the solver,
`2η (M + |A| (M + 1)²) ∏ᵢ (1 + ‖fᵢ‖₂) ≤ 1/4` (`BS23.SmallRadius.Core.sosErr`). -/
theorem sosErr_accOf_le (P : Problem) (ne : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hM : M ≤ 2 ^ ne) :
    Core.sosErr (P.system.map toReal) ((accOf ne P : ℝ) + accOf ne P) M ≤ 1 / 4 := by
  set L := (encProblem P).length with hL
  have hL4 : 4 ≤ L := by rw [hL, SoS.Correct.length_encProblem]; omega
  have hacc : (accOf ne P : ℝ) = 1 / 2 ^ ((ne + L + 2) ^ 2) := by
    rw [accOf_cast, accExp]
  have hlen : ((P.system.map toReal).length : ℝ) ≤ 2 ^ L := by
    have h := length_map_system_le P
    have h2 : (L : ℝ) < 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self
    have : ((P.system.map toReal).length : ℝ) ≤ L := by exact_mod_cast h
    linarith
  have h1n : (1 : ℝ) ≤ 2 ^ ne := one_le_pow₀ (by norm_num)
  have hM1 : (M + 1) ^ 2 ≤ 2 ^ (2 * ne + 2) := by
    have h : M + 1 ≤ 2 ^ (ne + 1) := by rw [pow_succ]; linarith
    calc (M + 1) ^ 2 ≤ (2 ^ (ne + 1)) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
      _ = 2 ^ (2 * ne + 2) := by rw [← pow_mul]; ring_nf
  have hMle : M ≤ 2 ^ (2 * ne + 2) := hM.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  have hmid : M + ((P.system.map toReal).length : ℝ) * (M + 1) ^ 2 ≤ 2 ^ (2 * ne + L + 3) := by
    have h1 : ((P.system.map toReal).length : ℝ) * (M + 1) ^ 2 ≤ 2 ^ L * 2 ^ (2 * ne + 2) :=
      mul_le_mul hlen hM1 (by positivity) (by positivity)
    have h2 : (2 : ℝ) ^ (2 * ne + L + 3) = 2 * (2 ^ L * 2 ^ (2 * ne + 2)) := by
      rw [← pow_add, ← pow_succ']
      ring_nf
    have h3 : (2 : ℝ) ^ (2 * ne + 2) ≤ 2 ^ L * 2 ^ (2 * ne + 2) :=
      le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
    linarith
  have hprod := prod_one_add_coeffNorm_le P
  have hP0 : 0 ≤ ∏ i : Fin (P.system.map toReal).length,
      (1 + coeffNorm ((P.system.map toReal).get i)) :=
    Finset.prod_nonneg fun i _ => add_nonneg zero_le_one (coeffNorm_nonneg _)
  have key := two_mul_pow_mul_four_le (X := 2 * ne + L + 3) (Y := (L + 1) * L)
    (Z := (ne + L + 2) ^ 2) (by nlinarith)
  unfold Core.sosErr
  rw [hacc]
  have ha : (0 : ℝ) < 2 ^ ((ne + L + 2) ^ 2) := by positivity
  calc (1 / 2 ^ ((ne + L + 2) ^ 2) + 1 / 2 ^ ((ne + L + 2) ^ 2)) *
        (M + ((P.system.map toReal).length : ℝ) * (M + 1) ^ 2) *
        ∏ i : Fin (P.system.map toReal).length, (1 + coeffNorm ((P.system.map toReal).get i))
      ≤ (1 / 2 ^ ((ne + L + 2) ^ 2) + 1 / 2 ^ ((ne + L + 2) ^ 2)) * 2 ^ (2 * ne + L + 3) *
          2 ^ ((L + 1) * L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hmid (by positivity)) hprod hP0 (by positivity)
    _ = 2 * (2 ^ (2 * ne + L + 3) * 2 ^ ((L + 1) * L)) / 2 ^ ((ne + L + 2) ^ 2) := by ring
    _ ≤ 1 / 4 := by
        rw [div_le_iff₀ ha]
        linarith

section Cross

variable {n d k : ℕ} {F : SRFrame n d k} {w R Csep : ℝ} {wq Rq : ℚ} {Lb : ℕ}

/-- **The cross bound of the rounds** (`BS23.SmallRadius.IdCtx.cross_pairs_le`): on a good frame
with `Csep > 0` and a budget that cuts nothing, every round has cross mass at most
`k² (2 n² ρ^s + 1)`, `ρ = 2^18 s / (Csep ln (1/w))`. -/
theorem crossBound_of_good (hF : F.Good w R Csep (sDeg wq) (tDeg wq Rq))
    (hfit : Fits d (sDeg wq) (tDeg wq Rq) (tDeg wq Rq / sDeg wq) Lb) (hCsep : 0 < Csep) :
    CrossBound F (srPar wq Rq n Lb) (bOf F.z (tDeg wq Rq) Lb)
      ((k : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 *
        (2 ^ 18 * (sDeg wq : ℝ) / (Csep * Real.log (1 / w))) ^ sDeg wq + 1)) := by
  intro Rem E hRem hE
  have hKeq : (((srPar wq Rq n Lb).K : ℚ) : ℝ) = (256 * (sDeg wq : ℝ)) ^ tDeg wq Rq := by
    rw [srPar_K, Kc]
    push_cast
    ring
  have hM : ((n : ℝ) ^ (50 * tDeg wq Rq)) ≤ 2 ^ (srPar wq Rq n Lb).ne := hF.params.pow_fifty_le
  exact IdCtx.cross_pairs_le ⟨F, Rem.length, Rem.get, sDeg wq, tDeg wq Rq, Lb⟩ hF E
    roundAcc_cast_nonneg hE.approx.map_toReal (by change 22 * tDeg wq Rq ≤ 64 * tDeg wq Rq; omega)
    (sosErr_accOf_le _ _ (by positivity) hM) (List.nodup_iff_injective_get.1 hRem) hfit
    (by rw [hKeq]; positivity) hKeq.le hCsep

/-- **Peeling succeeds with high probability**, with the cross bound from identifiability
(`crossBound_of_good`): `peel_good` with `εc = k² (2 n² ρ^s + 1)`,
`ρ = 2^18 s / (Csep ln (1/w))`, for `Csep > 0`. -/
theorem peel_good_of_sep (hF : F.Good w R Csep (sDeg wq) (tDeg wq Rq))
    (hfit : Fits d (sDeg wq) (tDeg wq Rq) (tDeg wq Rq / sDeg wq) Lb)
    (hbud : BudgetFits (srPar wq Rq n Lb) F.z (bOf F.z (tDeg wq Rq) Lb)) (hCsep : 0 < Csep)
    {δ' : ℝ} (hδ : 0 < δ') (hδw : δ' ≤ w / 4)
    (hε : 640 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (2 * (n : ℝ) ^ 2 *
        (2 ^ 18 * (sDeg wq : ℝ) / (Csep * Real.log (1 / w))) ^ sDeg wq + 1)) ≤
      δ' ^ 2 * w * (n : ℝ) ^ 2)
    (herr : 2 ^ 11 * (k : ℝ) ^ 2 * n ≤ δ' ^ 2 * w * 2 ^ n)
    {T : ℕ} (hT : k * coinBits n ≤ T) :
    1 - δ' / 2 ≤ coinProb T (fun c => ClustersWithin δ' F.ℓ (List.ofFn
      (peelLab (srPar wq Rq n Lb) F.z (bOf F.z (tDeg wq Rq) Lb) (blockNat c (coinBits n)) k))) :=
  peel_good hF hfit hbud (crossBound_of_good hF hfit hCsep) hδ hδw hε herr hT

end Cross

end BS23.SmallRadius
