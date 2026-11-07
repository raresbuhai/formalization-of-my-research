module

public import BCFGJPSSV26.Stable.Alg.ClientSampling
public import BCFGJPSSV26.Stable.Alg.ClusterSamplingAnalysis
public import BCFGJPSSV26.Stable.Alg.Submod
public import BCFGJPSSV26.Stable.Final.Combine

/-!
# One trial

A trial (`BCFGJPSSV26.Stable.trial`) reads `Ctr = 6 s + M₂ + k` chunks: the client sampling reads
the first `6 s`, the cluster sampling the next `M₂`, and the coloring of the kept centers the last
`k`; it returns the candidates of all guesses `p' ≤ s`
(`BCFGJPSSV26.Stable.trialCands`).

A trial is **good** (`BCFGJPSSV26.Stable.TrialGood`) if the local search or one of its candidates,
made into `k` facilities by `BCFGJPSSV26.sanitizeK`, costs at most `(1.89 + 1000/N) opt`
(`BCFGJPSSV26.Stable.bound`).

* `BCFGJPSSV26.Stable.Hyp.trialCands_good` ([BCFGJPSSV26b, Section 3.5]): if the client sampling
  and the cluster sampling give good outcomes and the coloring satisfies the color event of a
  partition, the candidate of the guess `|O_P|` exists and the local search or it is within the
  bound, by `BCFGJPSSV26.Stable.Partition.costF_candidate_le`,
  `BCFGJPSSV26.Stable.Partition.costF_S_le_PsiLS` and
  `BCFGJPSSV26.Stable.Partition.min_le_bound`.
* `BCFGJPSSV26.Stable.Hyp.card_trialGood`: at least `q K^Ctr` chunk vectors give a good trial,
  `q = N^(-200 s)`, by `BCFGJPSSV26.Stable.card_append_ge` from the process lemmas of the two
  samplings and the color coding.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- The candidates of a trial, from the chunks of its three parts. -/
def trialCands (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch₁ ch₂ ch₃ : ℕ → ℕ) :
    List (List ℕ) :=
  let s := Par.s N L
  let b := Par.bits N (encRaw x).length
  let Λ₁ := csRun N x LS s b ch₁
  let st := ksRun N x LS Λ₁ s b ch₂
  let LS' := ksLS' LS st
  (List.range (s + 1)).filterMap fun p' ↦
    candidate N x s B LS' (Λ₁ ++ st.dums) (colors b LS' ch₃) p'

/-- **A trial**, reading its chunks through `ch`. -/
def trial (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) : List (List ℕ) :=
  trialCands N x L LS B (window ch 0 (6 * Par.s N L)) (window ch (6 * Par.s N L) (Par.M₂ N L))
    (window ch (6 * Par.s N L + Par.M₂ N L) x.k)

/-- The bound of the main theorem: `(1.89 + 1000/N) opt k`. -/
noncomputable def bound (P : Prm) (I : Instance) : ℝ := (1.89 + 1000 / P.N) * I.opt I.k

/-- **A good trial**: the local search or a candidate is within the bound. -/
def TrialGood (P : Prm) (I : Instance) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) : Prop :=
  ∃ T ∈ LS :: trial P.N (toRaw I) L LS B ch, I.costF (I.centers (sanitizeK I.m I.k T)) ≤ bound P I

/-- A trial reads only its `Ctr` chunks. -/
theorem trial_window (N : ℕ) (x : Raw) (L : ℕ) (LS : List ℕ) (B : ℕ) (ch : ℕ → ℕ) :
    trial N x L LS B (window ch 0 (Par.Ctr N L x.k)) = trial N x L LS B ch := by
  unfold trial
  rw [window_window ch (o := 0) (M := Par.Ctr N L x.k) (o' := 0) (M' := 6 * Par.s N L)
      (by unfold Par.Ctr; omega),
    window_window ch (o := 0) (M := Par.Ctr N L x.k) (o' := 6 * Par.s N L) (M' := Par.M₂ N L)
      (by unfold Par.Ctr; omega),
    window_window ch (o := 0) (M := Par.Ctr N L x.k) (o' := 6 * Par.s N L + Par.M₂ N L)
      (M' := x.k) (by unfold Par.Ctr; omega)]
  simp only [zero_add]

/-- A trial on a vector of chunks reads its three parts. -/
theorem trial_toCh (N : ℕ) (I : Instance) (L : ℕ) (LS : List ℕ) (B : ℕ) {K : ℕ}
    (z : Fin (Par.Ctr N L I.k) → Fin K) :
    trial N (toRaw I) L LS B (toCh z) = trialCands N (toRaw I) L LS B
      (toCh fun i ↦ z (Fin.castAdd _ (Fin.castAdd _ i)))
      (toCh fun i ↦ z (Fin.castAdd _ (Fin.natAdd _ i)))
      (toCh fun i ↦ z (Fin.natAdd _ i)) := by
  unfold trial
  have h₀ : window (toCh z) 0 (6 * Par.s N L + Par.M₂ N L) =
      toCh fun i ↦ z (Fin.castAdd I.k i) := window_toCh_castAdd z
  have h₁ : window (toCh z) 0 (6 * Par.s N L) =
      toCh fun i ↦ z (Fin.castAdd _ (Fin.castAdd _ i)) := by
    have := window_window (toCh z) (o := 0) (M := 6 * Par.s N L + Par.M₂ N L) (o' := 0)
      (M' := 6 * Par.s N L) (by omega)
    rw [zero_add] at this
    rw [← this, h₀, window_toCh_castAdd]
  have h₂ : window (toCh z) (6 * Par.s N L) (Par.M₂ N L) =
      toCh fun i ↦ z (Fin.castAdd _ (Fin.natAdd _ i)) := by
    have := window_window (toCh z) (o := 0) (M := 6 * Par.s N L + Par.M₂ N L)
      (o' := 6 * Par.s N L) (M' := Par.M₂ N L) le_rfl
    rw [zero_add] at this
    rw [← this, h₀, window_toCh_natAdd]
  have h₃ : window (toCh z) (6 * Par.s N L + Par.M₂ N L) I.k =
      toCh fun i ↦ z (Fin.natAdd _ i) := window_toCh_natAdd z
  rw [h₁, h₂, Raw.k_toRaw, h₃]

namespace Ctx

variable (X : Ctx)

/-- The outcome of the client sampling on the chunks `ch`. -/
def csOut (LS : List ℕ) (ch : ℕ → ℕ) : List DumQ := csRun X.P.N (toRaw X.I) LS X.s X.b ch

/-- The final state of the cluster sampling on the chunks `ch₁`, `ch₂`. -/
def ksOut (LS : List ℕ) (ch₁ ch₂ : ℕ → ℕ) : KSState :=
  ksRun X.P.N (toRaw X.I) LS (X.csOut LS ch₁) X.s X.b ch₂

end Ctx

/-- The per-trial success probability is at most the product of those of the parts. -/
theorem Hyp.q_le_prod {X : Ctx} (H : Hyp X) :
    X.P.q X.L ≤ X.P.q₁ ^ (2 * X.s) * X.P.q₂ ^ Par.M₂ X.P.N X.L * (1 / 4) ^ X.s := by
  have hN := X.P.N_ge
  have hN0 := X.P.N_pos'
  have hs : 1 ≤ Par.s X.P.N X.L :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) X.P.N_pos) H.one_le_L
  have h₁ : 1 / (X.P.N : ℝ) ^ 10 ≤ X.P.q₁ := by
    unfold Prm.q₁
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (440 : ℝ) ≤ (X.P.N : ℝ) ^ 2 := by nlinarith
    calc 440 * (X.P.N : ℝ) ^ 8 ≤ (X.P.N : ℝ) ^ 2 * (X.P.N : ℝ) ^ 8 :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = (X.P.N : ℝ) ^ 10 := by ring
  have h₂ : 1 / (X.P.N : ℝ) ^ 4 ≤ X.P.q₂ := by
    unfold Prm.q₂
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc 12 * (X.P.N : ℝ) ^ 3 ≤ (X.P.N : ℝ) * (X.P.N : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (X.P.N : ℝ) ^ 4 := by ring
  have h₃ : 1 / (X.P.N : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hq₁ : 0 ≤ X.P.q₁ := le_trans (by positivity) h₁
  have hq₂ : 0 ≤ X.P.q₂ := le_trans (by positivity) h₂
  have hexp : 10 * (2 * X.s) + 4 * Par.M₂ X.P.N X.L + X.s ≤ 200 * X.s := by
    change 10 * (2 * Par.s X.P.N X.L) + 4 * (20 * Par.s X.P.N X.L + 20) + Par.s X.P.N X.L ≤
      200 * Par.s X.P.N X.L
    omega
  calc X.P.q X.L = 1 / (X.P.N : ℝ) ^ (200 * X.s) := rfl
    _ ≤ 1 / (X.P.N : ℝ) ^ (10 * (2 * X.s) + 4 * Par.M₂ X.P.N X.L + X.s) :=
        one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_right₀ (by linarith) hexp)
    _ = (1 / (X.P.N : ℝ) ^ 10) ^ (2 * X.s) * (1 / (X.P.N : ℝ) ^ 4) ^ Par.M₂ X.P.N X.L *
          (1 / (X.P.N : ℝ)) ^ X.s := by
        ring
    _ ≤ _ :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) h₁ _)
          (pow_le_pow_left₀ (by positivity) h₂ _) (by positivity) (pow_nonneg hq₁ _))
          (pow_le_pow_left₀ (by positivity) h₃ _) (by positivity)
          (mul_nonneg (pow_nonneg hq₁ _) (pow_nonneg hq₂ _))

/-- **Good outcomes make a good candidate**: for the outcome `Λ₁` of the client
sampling, `(LS', dums)` of the cluster sampling and a coloring `col` satisfying the color event,
the local search or the candidate of some guess is within the bound. -/
theorem Hyp.exists_good_candidate {X : Ctx} (H : Hyp X) {LS : List ℕ}
    (hLS : X.I.centers LS = X.S) (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ}
    (hB : X.P.N ^ X.s ≤ B) {Λ₁ dums : List DumQ} (hval₁ : (toRaw X.I).ValidDums Λ₁)
    (hval₂ : (toRaw X.I).ValidDums dums) {LS' : List ℕ} (hLS'nd : LS'.Nodup)
    (hLS'm : ∀ i ∈ LS', i < X.I.m) {col : List Bool} (hcol_len : col.length = LS'.length)
    (w₁ : ClientWitness X (toDums X.I Λ₁))
    (w₂ : ClusterWitness w₁ (X.I.centers LS') (toDums X.I dums)) (Q : Partition w₂)
    (hcol : Q.ColorEvent (X.I.centers (redOf LS' col)) (X.I.centers (blueOf LS' col))) :
    X.I.costF (X.I.centers (sanitizeK X.I.m X.I.k LS)) ≤ bound X.P X.I ∨
      ∃ p' ≤ X.s, ∃ T, candidate X.P.N (toRaw X.I) X.s B LS' (Λ₁ ++ dums) col p' = some T ∧
        X.I.costF (X.I.centers (sanitizeK X.I.m X.I.k T)) ≤ bound X.P X.I := by
  classical
  have hval : (toRaw X.I).ValidDums (Λ₁ ++ dums) := by
    intro l hl
    rcases List.mem_append.1 hl with h | h
    · exact hval₁ l h
    · exact hval₂ l h
  have hΛeq : toDums X.I (Λ₁ ++ dums) = toDums X.I Λ₁ ++ toDums X.I dums := toDums_append _ _ _
  have hlenΛ : (toDums X.I Λ₁).length + (toDums X.I dums).length = (Λ₁ ++ dums).length := by
    rw [← List.length_append, ← hΛeq, Raw.length_toDums hval]
  -- the guess `|O_P|`
  have hρ : (Λ₁ ++ dums).length + Q.OP.card ≤ X.s := by
    have := Q.card_OLam_add_OP_le H
    rw [List.length_append, hlenΛ] at this
    exact this
  have hz : Q.z = (LS'.length + ((Λ₁ ++ dums).length + Q.OP.card)) - X.I.k := by
    unfold Partition.z
    rw [Instance.card_centers hLS'nd hLS'm, hlenΛ]
  have hball : ∀ l ∈ Λ₁ ++ dums, (toRaw X.I).ballQ l ≠ [] := by
    refine Raw.ballQ_ne_nil hval ?_
    obtain ⟨o, ho, -⟩ := Q.exists_ball_choice H
    rw [hΛeq]
    intro l hl
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
    exact ⟨o i, ho i⟩
  have hzc : Q.Zstar.card = Q.z := Q.Zstar_card
  have hzred : (LS'.length + ((Λ₁ ++ dums).length + Q.OP.card)) - X.I.k ≤
      (redOf LS' col).length := by
    rw [← hz, ← hzc]
    exact (card_le_card hcol.1).trans (Instance.card_centers_le _)
  obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1
    (candidate_isSome (I := X.I) (N := X.P.N) (B := B) hρ hzred hball)
  have hB' : X.P.N ^ ((Λ₁ ++ dums).length + Q.OP.card) ≤ B :=
    (Nat.pow_le_pow_right X.P.N_pos hρ).trans hB
  obtain ⟨hTnd, hTm, hTk, Y, Zh, hTeq, hY, hZ, hZc, hZs, hG⟩ :=
    candidate_spec H.valid X.P.N_pos hLS'nd hLS'm hval hcol_len hB' hT
  rw [hΛeq] at hY hZs hG
  rw [← hz] at hZc hZs hG
  obtain ⟨hred, hblue⟩ := centers_red_blue (I := X.I) hLS'nd hcol_len
  have hcT := Q.costF_candidate_le H hred hblue hcol hY hZ hZc hZs hG
  rw [← hTeq] at hcT
  -- the bound
  have hopt : 0 ≤ X.opt := H.opt_pos.le
  have hfin : (1 + eta + 100 * X.ε) * X.opt ≤ bound X.P X.I := by
    unfold bound eta
    have hN := X.P.N_pos'
    have hε : X.ε = 1 / X.P.N := rfl
    have h1 : (1 : ℝ) + 89 / 100 + 100 * X.ε ≤ 1.89 + 1000 / X.P.N := by
      rw [hε]
      have : (100 : ℝ) * (1 / X.P.N) ≤ 1000 / X.P.N := by
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (by norm_num) hN.le
      norm_num at this ⊢
      linarith
    exact mul_le_mul_of_nonneg_right h1 hopt
  rcases Q.min_le_bound H hcT with h | h
  · left
    have hLSk : LS.length ≤ X.I.k := by
      rw [← Instance.card_centers hnd hm, hLS, H.alo.1]
    refine (costF_sanitizeK_le H.valid hnd hm hLSk).trans ?_
    rw [hLS]
    exact h.trans hfin
  · exact .inr ⟨Q.OP.card, by omega, T, hT,
      (costF_sanitizeK_le H.valid hTnd hTm hTk).trans (h.trans hfin)⟩

/-- **Good outcomes make a good trial.** -/
theorem Hyp.trialCands_good {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ} (hB : X.P.N ^ X.s ≤ B)
    {ch₁ ch₂ ch₃ : ℕ → ℕ} (w₁ : ClientWitness X (toDums X.I (X.csOut LS ch₁)))
    (w₂ : ClusterWitness w₁ (X.I.centers (ksLS' LS (X.ksOut LS ch₁ ch₂)))
      (toDums X.I (X.ksOut LS ch₁ ch₂).dums)) (Q : Partition w₂)
    (hcol : Q.ColorEvent
      (X.I.centers (redOf (ksLS' LS (X.ksOut LS ch₁ ch₂))
        (colors X.b (ksLS' LS (X.ksOut LS ch₁ ch₂)) ch₃)))
      (X.I.centers (blueOf (ksLS' LS (X.ksOut LS ch₁ ch₂))
        (colors X.b (ksLS' LS (X.ksOut LS ch₁ ch₂)) ch₃)))) :
    ∃ T ∈ LS :: trialCands X.P.N (toRaw X.I) X.L LS B ch₁ ch₂ ch₃,
      X.I.costF (X.I.centers (sanitizeK X.I.m X.I.k T)) ≤ bound X.P X.I := by
  have hval₂ : (toRaw X.I).ValidDums (X.ksOut LS ch₁ ch₂).dums := by
    intro l hl
    obtain ⟨i, hi, h⟩ := ksRun_dums hm _ _ _ _ _ l hl
    have := hm i hi
    rw [h]
    change X.I.n + i < X.I.n + X.I.m
    omega
  rcases H.exists_good_candidate hLS hnd hm hB (csRun_valid H.one_le_n _ _ _ _ _) hval₂
    (hnd.filter _) (fun i hi ↦ hm i (List.mem_of_mem_filter hi)) (by simp [colors, ksLS']) w₁ w₂ Q
    hcol with h | ⟨p', hp', T, hT, h⟩
  · exact ⟨LS, List.mem_cons_self, h⟩
  · exact ⟨T, List.mem_cons_of_mem _
      (List.mem_filterMap.2 ⟨p', List.mem_range.2 (Nat.lt_succ_of_le hp'), hT⟩), h⟩

open Classical in
/-- **A trial is good with probability at least `q`.** -/
theorem Hyp.card_trialGood {X : Ctx} (H : Hyp X) {LS : List ℕ} (hLS : X.I.centers LS = X.S)
    (hnd : LS.Nodup) (hm : ∀ i ∈ LS, i < X.I.m) {B : ℕ} (hB : X.P.N ^ X.s ≤ B) :
    X.P.q X.L * ((2 : ℝ) ^ X.b) ^ Par.Ctr X.P.N X.L X.I.k ≤
      (univ.filter fun v : Fin (Par.Ctr X.P.N X.L X.I.k) → Fin (2 ^ X.b) ↦
        TrialGood X.P X.I X.L LS B (toCh v)).card := by
  have hK : (Fintype.card (Fin (2 ^ X.b)) : ℝ) = (2 : ℝ) ^ X.b := by simp
  have hLSk : LS.length ≤ X.I.k := by
    rw [← Instance.card_centers hnd hm, hLS, H.alo.1]
  -- the client sampling, then the cluster sampling
  let P₁ : (Fin (6 * X.s) → Fin (2 ^ X.b)) → Prop := fun u ↦
    Nonempty (ClientWitness X (toDums X.I (X.csOut LS (toCh u))))
  let P₂ : (Fin (6 * X.s) → Fin (2 ^ X.b)) → (Fin (Par.M₂ X.P.N X.L) → Fin (2 ^ X.b)) → Prop :=
    fun u v ↦ ∃ w₁ : ClientWitness X (toDums X.I (X.csOut LS (toCh u))),
      Nonempty (ClusterWitness w₁ (X.I.centers (ksLS' LS (X.ksOut LS (toCh u) (toCh v))))
        (toDums X.I (X.ksOut LS (toCh u) (toCh v)).dums))
  have h12 := card_append_ge P₁ P₂ (q₁ := X.P.q₁ ^ (2 * X.s))
    (q₂ := X.P.q₂ ^ Par.M₂ X.P.N X.L) (by unfold Prm.q₂; positivity)
    (by rw [hK]; exact H.card_clientWitness hLS hnd hm)
    (fun u hu ↦ by
      obtain ⟨w₁⟩ := hu
      have h := H.card_clusterWitness hLS hnd hm (csRun_valid H.one_le_n _ _ _ _ _) w₁
      rw [hK]
      refine h.trans ?_
      exact_mod_cast card_le_card fun v hv ↦ by
        simp only [mem_filter, mem_univ, true_and] at hv ⊢
        exact ⟨w₁, hv⟩)
  -- the coloring
  let P₁₂ : (Fin (6 * X.s + Par.M₂ X.P.N X.L) → Fin (2 ^ X.b)) → Prop := fun z ↦
    P₁ (fun i ↦ z (Fin.castAdd _ i)) ∧ P₂ (fun i ↦ z (Fin.castAdd _ i)) (fun i ↦ z (Fin.natAdd _ i))
  let P₃ : (Fin (6 * X.s + Par.M₂ X.P.N X.L) → Fin (2 ^ X.b)) → (Fin X.I.k → Fin (2 ^ X.b)) →
      Prop := fun z u ↦
    ∃ (w₁ : ClientWitness X (toDums X.I (X.csOut LS (toCh fun i ↦ z (Fin.castAdd _ i)))))
      (w₂ : ClusterWitness w₁ (X.I.centers (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
        (toCh fun i ↦ z (Fin.natAdd _ i)))))
        (toDums X.I (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
          (toCh fun i ↦ z (Fin.natAdd _ i))).dums))
      (Q : Partition w₂),
      Q.ColorEvent
        (X.I.centers (redOf (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
          (toCh fun i ↦ z (Fin.natAdd _ i))))
          (colors X.b (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
            (toCh fun i ↦ z (Fin.natAdd _ i)))) (toCh u))))
        (X.I.centers (blueOf (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
          (toCh fun i ↦ z (Fin.natAdd _ i))))
          (colors X.b (ksLS' LS (X.ksOut LS (toCh fun i ↦ z (Fin.castAdd _ i))
            (toCh fun i ↦ z (Fin.natAdd _ i)))) (toCh u))))
  have h123 := card_append_ge P₁₂ P₃ (q₁ := X.P.q₁ ^ (2 * X.s) * X.P.q₂ ^ Par.M₂ X.P.N X.L)
    (q₂ := (1 / 4) ^ X.s) (by positivity) (by convert h12)
    (fun z hz ↦ by
      obtain ⟨-, w₁, ⟨w₂⟩⟩ := hz
      obtain ⟨Q⟩ := H.exists_partition w₁ w₂
      have h := Q.card_colorEvent H (hnd.filter _)
        (fun i hi ↦ hm i (List.mem_of_mem_filter hi)) ((List.length_filter_le _ _).trans hLSk)
      rw [hK]
      refine h.trans ?_
      exact_mod_cast card_le_card fun u hu ↦ by
        simp only [mem_filter, mem_univ, true_and] at hu ⊢
        exact ⟨w₁, w₂, Q, hu⟩)
  rw [hK] at h123
  have hq := H.q_le_prod
  refine (mul_le_mul_of_nonneg_right hq (by positivity)).trans (h123.trans ?_)
  exact_mod_cast card_le_card fun z hz ↦ by
    simp only [mem_filter, mem_univ, true_and] at hz
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    obtain ⟨-, w₁, w₂, Q, hcol⟩ := hz
    unfold TrialGood
    rw [trial_toCh]
    exact H.trialCands_good hLS hnd hm hB w₁ w₂ Q hcol

end BCFGJPSSV26.Stable
