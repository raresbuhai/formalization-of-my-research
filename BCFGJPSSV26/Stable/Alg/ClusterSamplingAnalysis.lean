module

public import BCFGJPSSV26.Stable.Alg.ClusterSampling
public import BCFGJPSSV26.Stable.Alg.ClusterSamplingDensity
public import BCFGJPSSV26.Stable.Structure.ClusterWitness

/-!
# The analysis of the cluster sampling

The cluster-sampling theorem of [BCFGJPSSV26b, Section 4.4] as a process lemma
(`BCFGJPSSV26.Stable.Hyp.card_clusterWitness`): given a good outcome `w₁` of the client sampling,
at least `q₂^(M₂) K^(M₂)` of the chunk vectors give a good outcome of the cluster sampling
(`BCFGJPSSV26.Stable.ClusterWitness`), `q₂ = 1/(12 N³)`.

Proof: `BCFGJPSSV26.Stable.guided_count` with the invariant `BCFGJPSSV26.Stable.KSData.Inv`, a
structure with one field per clause, about ghost data that are functions of the state: the greedy
matching of the dummies to clusters of `O_B` sharing a loose satellite with
their leader. The good chunks of each mode: `START` skips exactly when the current cost condition
holds; `SAMPLE` picks a satellite of an unmatched cluster (phase `0`) or such a satellite or a
center outside `LS_X` (phase `1`), of weight at least `ε³ opt` out of at most `6 opt`
(`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`); the other modes follow the case analysis of
the paper with `BCFGJPSSV26.Stable.Hyp.no_dense_cores` and `BCFGJPSSV26.Stable.Hyp.comparable_per`.
A skipped iteration leaves the state unchanged, so the cost condition that made it skip still
holds afterwards; the second cost condition is not monotone in the state (deleting centers changes
the mixed clusters), so this is what keeps it. The run ends in phase `2`
(`BCFGJPSSV26.Stable.ksRun_phase`), where the invariant gives the witness
(`BCFGJPSSV26.Stable.KSData.witness`).

The witness asks for one dummy per matched cluster, all distinct; the dummies of one leader are
distinct thanks to the shift of their radii by the number of dummies
(`BCFGJPSSV26.Stable.ksRad`, `BCFGJPSSV26.Stable.KSData.ksRad_inj`), also when two clusters are
at the same distance from the leader.

The pieces: the ghost matching and the invariant (`ClusterSamplingGhost`), the exact weights and
counting facts (`ClusterSamplingBridge`), one step mode by mode (`ClusterSamplingStep`,
`BCFGJPSSV26.Stable.KSData.inv_step`), and the densities (`ClusterSamplingDensity`,
`BCFGJPSSV26.Stable.KSData.card_good`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

/-- The run as an iteration of one chunk per step. -/
theorem foldl_range_eq_runFin {σ : Type*} {Kc : ℕ} (f : σ → ℕ → σ) (x₀ : σ) (ch : ℕ → ℕ) :
    ∀ (M : ℕ) (u : Fin M → Fin Kc), (∀ i (h : i < M), ch i = u ⟨i, h⟩) →
      (List.range M).foldl (fun st t ↦ f st (ch t)) x₀ =
        runFin (fun _ st v ↦ f st v.1) x₀ M u
  | 0, _, _ => rfl
  | M + 1, u, hu => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      foldl_range_eq_runFin f x₀ ch M (fun i ↦ u i.castSucc) fun i h ↦ hu i (by omega), hu M
        (by omega)]
    rfl

theorem inv_init : K.Inv ksInit := by
  refine Inv.mk_start K (del := []) (D := []) ?_ (by norm_num) (Nat.zero_le _)
    (fun _ h ↦ absurd h List.not_mem_nil) (fun _ _ h ↦ List.not_mem_nil h)
    (fun h ↦ absurd h (by norm_num)) (.inr le_rfl)
  exact ⟨List.nodup_nil, by simp [matched_nil], by simp [matched_nil], List.nodup_nil,
    fun _ h ↦ absurd h List.not_mem_nil⟩

/-- **The outcome at the end**: the invariant in phase `2` is a good outcome. -/
theorem witness {st : KSState} (hI : K.Inv st) (h2 : st.phase = 2) :
    Nonempty (ClusterWitness K.w₁ (K.X.I.centers (ksLS' K.LS st)) (toDums K.X.I st.dums)) := by
  obtain ⟨hcc1, htag⟩ := hI.ph2 h2
  have hcc0 : K.cc 0 st.del st.dums := hI.ph1 (by omega)
  have hb : K.Base st.del st.dums := hI.base
  have hg : K.GamSub st.del st.dums := hI.gam (by omega)
  have hlead : ∀ d ∈ st.dums, ∃ i ∈ st.del, d.1 = K.X.I.n + i := fun d hd ↦
    (hI.leaders d hd).resolve_right fun h ↦ by omega
  have hD : (toRaw K.X.I).ValidDums st.dums := fun d hd ↦ by
    obtain ⟨i, hi, he⟩ := hlead d hd
    have := (hb.del_sub i hi).1
    rw [he, Raw.n_toRaw, Raw.m_toRaw]
    omega
  have hLS' : K.X.I.centers (ksLS' K.LS st) = K.LSp st.del := rfl
  rw [hLS']
  unfold cc GoodL wt at hcc0 hcc1
  simp only [one_ne_zero, ↓reduceIte] at hcc0 hcc1
  refine ⟨{
    OL2 := K.matched st.dums
    φ := K.phi st.dums
    LS'_sub := K.LSp_subset _
    LSX_sub := hb.LSX_subset
    card_del := (card_le_card (sdiff_subset_sdiff subset_rfl hb.LSX_subset)).trans
      (K.H.card_S_sdiff_LSX_le K.w₁)
    OL2_sub := K.matched_subset _
    length_eq := by rw [K.length_toDums hD, hb.card]
    φ_mem := fun c hc ↦ K.phi_mem hD hc
    φ_inj := K.phi_injOn hb.dums_nodup
    leader := fun c hc ↦ by
      obtain ⟨i, hi, he⟩ := K.dumOf_cand hc
      refine ⟨i, (K.mem_GamE.1 hi).1, ?_⟩
      unfold phi
      rw [K.toDum_leader i.2 he]
    radius_ge := fun c hc ↦ (hb.rad c hc).1
    radius_le := fun c hc ↦ (hb.rad c hc).2
    Gam_sub := fun c hc ↦ by
      obtain ⟨c', -, hc'⟩ := mem_biUnion.1 hc
      exact K.mem_LSp.2 ⟨K.X.Gam_subset_S c' hc', hg c hc⟩
    cost₀ := hcc0
    cost₁ := hcc1 }⟩

end KSData

open Classical in
/-- **The process lemma of the cluster sampling.** -/
theorem Hyp.card_clusterWitness {X : Ctx} (H : Hyp X) {LS : List ℕ}
    (hLS : X.I.centers LS = X.S) (hLSnd : LS.Nodup) (hLSm : ∀ i ∈ LS, i < X.I.m)
    {Λ₁ : List DumQ} (hΛ₁ : (toRaw X.I).ValidDums Λ₁) (w₁ : ClientWitness X (toDums X.I Λ₁)) :
    X.P.q₂ ^ Par.M₂ X.P.N X.L * ((2 : ℝ) ^ X.b) ^ Par.M₂ X.P.N X.L ≤
      (univ.filter fun u : Fin (Par.M₂ X.P.N X.L) → Fin (2 ^ X.b) ↦
        Nonempty (ClusterWitness w₁
          (X.I.centers (ksLS' LS (ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u))))
          (toDums X.I (ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u)).dums))).card := by
  let K : KSData := ⟨X, H, LS, hLS, hLSnd, hLSm, Λ₁, hΛ₁, w₁⟩
  have hg := guided_count (fun _ st (v : Fin (2 ^ X.b)) ↦ K.step st v) ksInit
    (fun _ st ↦ K.Inv st) (fun _ st v ↦ K.Good st v) K.q₂_nonneg (Par.M₂ X.P.N X.L) K.inv_init
    (fun _ _ _ _ hI hG ↦ K.inv_step hI hG) (fun _ _ _ hI ↦ K.card_good hI)
  rw [K.card_fin_b] at hg
  refine hg.trans (Nat.cast_le.2 (card_le_card fun u hu ↦ ?_))
  rw [mem_filter] at hu ⊢
  refine ⟨mem_univ _, ?_⟩
  have hrun : ksRun X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u) =
      runFin (fun _ st (v : Fin (2 ^ X.b)) ↦ K.step st v) ksInit (Par.M₂ X.P.N X.L) u :=
    KSData.foldl_range_eq_runFin (fun st t ↦ K.step st t) ksInit (toCh u) _ u
      fun i h ↦ by unfold toCh; rw [dite_eq_left h]
  have h2 := ksRun_phase X.P.N (toRaw X.I) LS Λ₁ X.s X.b (toCh u)
  rw [hrun] at h2 ⊢
  exact K.witness hu.2 h2

end BCFGJPSSV26.Stable
