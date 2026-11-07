module

public import BCFGJPSSV26.Stable.Alg.ClusterSamplingGhost

/-!
# The analysis of the cluster sampling: exact computations and counting facts

The exact weights of the algorithm are the real weights of the analysis
(`BCFGJPSSV26.Stable.KSData.wq_eq`), the exact nearest other center is the nearest one
(`BCFGJPSSV26.Stable.KSData.nearOther_spec`), and the counting facts of the invariant: at most
`s` deleted centers and dummies, and the total weight is at most `6 opt`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

/-! ### Generic facts -/

/-- The sum of a function over a list of distinct numbers below `n`. -/
theorem cast_sum_map_eq {n : ℕ} {L : List ℕ} (hL : L.Nodup) (hn : ∀ j ∈ L, j < n)
    (f : ℕ → ℚ) :
    ((L.map f).sum : ℝ) = ∑ j ∈ (univ : Finset (Fin n)).filter (fun j ↦ j.1 ∈ L), (f j.1 : ℝ) := by
  classical
  have hmap : ((univ : Finset (Fin n)).filter fun j ↦ j.1 ∈ L).map Fin.valEmbedding =
      L.toFinset := by
    ext j
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset]
    exact ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun h ↦ ⟨⟨j, hn j h⟩, h, rfl⟩⟩
  rw [Rat.cast_list_sum, List.map_map, ← List.sum_toFinset _ hL, ← hmap, Finset.sum_map]
  rfl

/-- An injective map of a finite set into a list as long as the set is onto the list. -/
theorem exists_eq_of_injOn {α β : Type*} {A : Finset α} {L : List β}
    {f : α → β} (hf : Set.InjOn f A) (hmem : ∀ a ∈ A, f a ∈ L) (hc : A.card = L.length) :
    ∀ b ∈ L, ∃ a ∈ A, f a = b := by
  classical
  have hsub : A.image f ⊆ L.toFinset := fun b hb ↦ by
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    exact List.mem_toFinset.2 (hmem a ha)
  have hcard : L.toFinset.card ≤ (A.image f).card := by
    rw [card_image_of_injOn hf, hc]
    exact List.toFinset_card_le L
  have he := eq_of_subset_of_card_le hsub hcard
  intro b hb
  have : b ∈ A.image f := he ▸ List.mem_toFinset.2 hb
  exact mem_image.1 this

/-- **Weighted sampling from a list of distinct centers**: a set `A` of them is sampled by at
least `2^b w(A)/W - |A|` chunks. -/
theorem card_sample_ge {m b : ℕ} {cand : List ℕ} (hnd : cand.Nodup) (hlt : ∀ i ∈ cand, i < m)
    (g : ℕ → ℚ) (f : Fin m → ℝ) (hgf : ∀ c : Fin m, c.1 ∈ cand → (g c.1 : ℝ) = f c)
    (hf : ∀ c : Fin m, c.1 ∈ cand → 0 ≤ f c) (A : Finset (Fin m)) (hA : ∀ c ∈ A, c.1 ∈ cand)
    (hpos : 0 < ∑ c ∈ A, f c) :
    (2 ^ b : ℝ) * (∑ c ∈ A, f c) / (∑ c ∈ (univ.filter fun c : Fin m ↦ c.1 ∈ cand), f c) -
        A.card ≤
      ((univ : Finset (Fin (2 ^ b))).filter fun u ↦
        ∃ c ∈ A, c.1 = cand.getD (wsample b (cand.map g) u.1) 0).card := by
  classical
  set w := cand.map g with hw
  set G : Finset ℕ := A.image fun c ↦ cand.idxOf c.1 with hG
  have hinj : Set.InjOn (fun c : Fin m ↦ cand.idxOf c.1) A := by
    intro c hc c' hc' he
    have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hA c hc))
    have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hA c' hc'))
    simp only at he
    exact Fin.ext (by rw [← h1, ← h2]; simp only [he])
  have hGlt : ∀ i ∈ G, i < w.length := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hi
    rw [hw, List.length_map]
    exact List.idxOf_lt_length_of_mem (hA c hc)
  have hgetD : ∀ c ∈ A, cand.getD (cand.idxOf c.1) 0 = c.1 := by
    intro c hc
    have hlt' := List.idxOf_lt_length_of_mem (hA c hc)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt', Option.getD_some,
      List.getElem_idxOf hlt']
  have hsumG : ∑ i ∈ G, (w.getD i 0 : ℝ) = ∑ c ∈ A, f c := by
    rw [hG, sum_image hinj]
    refine sum_congr rfl fun c hc ↦ ?_
    have hlt' := List.idxOf_lt_length_of_mem (hA c hc)
    have : w.getD (cand.idxOf c.1) 0 = g c.1 := by
      rw [hw, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt',
        Option.map_some, Option.getD_some, List.getElem_idxOf hlt']
    rw [this, hgf c (hA c hc)]
  have hW : (w.sum : ℝ) = ∑ c ∈ (univ.filter fun c : Fin m ↦ c.1 ∈ cand), f c := by
    rw [hw, cast_sum_map_eq hnd hlt]
    exact sum_congr rfl fun c hc ↦ hgf c (mem_filter.1 hc).2
  have hAsub : A ⊆ univ.filter fun c : Fin m ↦ c.1 ∈ cand :=
    fun c hc ↦ mem_filter.2 ⟨mem_univ _, hA c hc⟩
  have hWge : ∑ c ∈ A, f c ≤ (w.sum : ℝ) := by
    rw [hW]
    exact sum_le_sum_of_subset_of_nonneg hAsub fun c hc _ ↦ hf c (mem_filter.1 hc).2
  have hnn : ∀ q ∈ w, 0 ≤ q := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hq
    have h := hf ⟨i, hlt i hi⟩ hi
    rw [← hgf ⟨i, hlt i hi⟩ hi] at h
    exact_mod_cast h
  have hWpos : 0 < w.sum := by exact_mod_cast hpos.trans_le hWge
  have h := card_wsample (b := b) hnn hWpos G hGlt
  rw [hsumG, card_image_of_injOn hinj] at h
  have hsub : (univ.filter fun u : Fin (2 ^ b) ↦ wsample b w u ∈ G) ⊆
      (univ.filter fun u : Fin (2 ^ b) ↦ ∃ c ∈ A, c.1 = cand.getD (wsample b w u.1) 0) := by
    intro u hu
    rw [mem_filter] at hu ⊢
    obtain ⟨c, hc, he⟩ := mem_image.1 hu.2
    refine ⟨mem_univ _, c, hc, ?_⟩
    rw [← he, hgetD c hc]
  rw [← hW]
  exact h.trans (by exact_mod_cast card_le_card hsub)

variable (K : KSData)

/-! ### Exact weights -/

/-- The exact sampling weight of the algorithm. -/
def wq (ph : ℕ) (del : List ℕ) (D : List DumQ) (c : ℕ) : ℚ :=
  if ph = 0 then (toRaw K.X.I).costOn K.LS ((toRaw K.X.I).clusterQ K.LS c)
  else (((toRaw K.X.I).clusterMixQ (K.cand del) (K.Λ₁ ++ D) c).map
    fun y ↦ (toRaw K.X.I).fdist y c).sum

theorem ksWeights_eq (ph : ℕ) (del : List ℕ) (D : List DumQ) :
    ksWeights (toRaw K.X.I) K.LS K.Λ₁ ph del D (K.cand del) =
      (K.cand del).map (K.wq ph del D) := by
  unfold ksWeights wq
  split_ifs <;> rfl

theorem LS_ne_nil : K.LS ≠ [] := by
  intro h
  obtain ⟨c, hc⟩ := K.H.S_nonempty
  rw [K.mem_S, h] at hc
  exact List.not_mem_nil hc

theorem centers_cand (del : List ℕ) : K.X.I.centers (K.cand del) = K.LSp del := rfl

/-- The exact weights are the real ones. -/
theorem wq_eq {ph : ℕ} {del : List ℕ} {D : List DumQ} (hD : (toRaw K.X.I).ValidDums D)
    (hne : K.cand del ≠ []) (c : Fin K.X.I.m) : (K.wq ph del D c.1 : ℝ) = K.wt ph del D c := by
  classical
  have hv := K.H.valid
  unfold wq wt
  split_ifs with h0
  · have hnd : ((toRaw K.X.I).clusterQ K.LS c).Nodup := List.nodup_range.filter _
    have hn : ∀ j ∈ (toRaw K.X.I).clusterQ K.LS c, j < K.X.I.n := fun j hj ↦
      List.mem_range.1 (List.mem_of_mem_filter hj)
    rw [Raw.costOn_toRaw K.hm hnd hn, K.hLS]
    unfold Ctx.costS Ctx.CS
    congr 1
    ext j
    rw [mem_filter, Raw.mem_clusterQ K.LS_ne_nil K.hm, K.hLS]
    simp
  · have hval : (toRaw K.X.I).ValidDums (K.Λ₁ ++ D) := fun l hl ↦ by
      rcases List.mem_append.1 hl with hl | hl
      · exact K.hΛ₁ l hl
      · exact hD l hl
    have hFm : ∀ i ∈ K.cand del, i < K.X.I.m := fun i hi ↦ K.cand_lt hi
    have hnd : ((toRaw K.X.I).clusterMixQ (K.cand del) (K.Λ₁ ++ D) c).Nodup :=
      List.nodup_range.filter _
    have hn : ∀ j ∈ (toRaw K.X.I).clusterMixQ (K.cand del) (K.Λ₁ ++ D) c, j < K.X.I.n :=
      fun j hj ↦ List.mem_range.1 (List.mem_of_mem_filter hj)
    rw [cast_sum_map_eq hnd hn]
    unfold costMixOn
    have hset : ((univ : Finset (Fin K.X.I.n)).filter fun j ↦
        j.1 ∈ (toRaw K.X.I).clusterMixQ (K.cand del) (K.Λ₁ ++ D) c) =
        clusterMix K.X.I (K.LSp del) (K.mixL D) c := by
      ext j
      rw [mem_filter, Raw.mem_clusterMixQ hne hFm hval, centers_cand, toDums_append]
      simp [mixL]
    rw [hset]
    refine sum_congr rfl fun j hj ↦ ?_
    have h1 : ((toRaw K.X.I).fdist j c : ℝ) = K.X.I.dd (.inl j) (.inr c) := by
      have := Raw.fdist_toRaw (I := K.X.I) (.inl j) c
      rw [Instance.ptIdx_inl] at this
      rw [this]
      rfl
    rw [h1]
    unfold clusterMix at hj
    rw [mem_filter] at hj
    unfold dMix
    rw [min_eq_left hj.2, Instance.dSet_of_mem_cluster hj.1]

theorem wt_nonneg (ph : ℕ) (del : List ℕ) (D : List DumQ) (c : Fin K.X.I.m) :
    0 ≤ K.wt ph del D c := by
  have hv := K.H.valid
  unfold wt
  split_ifs
  · exact Instance.costOn_nonneg hv _ _
  · unfold costMixOn
    refine sum_nonneg fun j hj ↦ ?_
    unfold clusterMix at hj
    rw [mem_filter] at hj
    unfold dMix
    rw [min_eq_left hj.2]
    exact Instance.dSet_nonneg hv _ _

/-! ### Counting -/

theorem card_OO_le : K.OO.card ≤ K.X.s :=
  (card_le_card fun _ hc ↦ K.w₁.O2_subset (mem_sdiff.1 hc).1).trans K.H.card_O1_le

section

variable {K}

theorem Base.card_del_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    del.length ≤ K.X.s := by
  classical
  have hinj : Set.InjOn K.fac {i | i ∈ del} := fun i hi i' hi' he ↦ by
    rw [← K.fac_val (hb.del_sub i hi).1, ← K.fac_val (hb.del_sub i' hi').1, he]
  have h1 : (del.toFinset.image K.fac).card = del.length := by
    rw [card_image_of_injOn (fun i hi i' hi' he ↦ hinj (List.mem_toFinset.1 hi)
      (List.mem_toFinset.1 hi') he), List.toFinset_card_of_nodup hb.del_nodup]
  have h2 : del.toFinset.image K.fac ⊆ K.X.S \ K.X.LSX K.w₁.OL := fun _ hc ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
    exact (hb.del_sub i (List.mem_toFinset.1 hi)).2
  rw [← h1]
  exact (card_le_card h2).trans (K.H.card_S_sdiff_LSX_le K.w₁)

theorem Base.card_dums_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    D.length ≤ K.X.s := by
  rw [← hb.card]
  exact (card_le_card (K.matched_subset D)).trans K.card_OO_le

theorem Base.card_add_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    D.length + del.length ≤ 2 * K.X.s := by
  have := hb.card_dums_le
  have := hb.card_del_le
  omega

/-- If `s` centers are deleted, all of `S \ LS_X` is. -/
theorem Base.LSp_subset_LSX {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (h : K.X.s ≤ del.length) : K.LSp del ⊆ K.X.LSX K.w₁.OL := by
  classical
  intro c hc
  by_contra hcX
  rw [K.mem_LSp] at hc
  have hinj : Set.InjOn K.fac ↑del.toFinset := fun i hi i' hi' he ↦ by
    rw [← K.fac_val (hb.del_sub i (List.mem_toFinset.1 hi)).1,
      ← K.fac_val (hb.del_sub i' (List.mem_toFinset.1 hi')).1, he]
  have h1 : (del.toFinset.image K.fac).card = del.length := by
    rw [card_image_of_injOn hinj, List.toFinset_card_of_nodup hb.del_nodup]
  have h2 : del.toFinset.image K.fac ⊆ K.X.S \ K.X.LSX K.w₁.OL := fun _ hc ↦ by
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hc
    exact (hb.del_sub i (List.mem_toFinset.1 hi)).2
  have h3 := eq_of_subset_of_card_le h2 (by
    rw [h1]
    exact (K.H.card_S_sdiff_LSX_le K.w₁).trans h)
  have : c ∈ del.toFinset.image K.fac := h3 ▸ mem_sdiff.2 ⟨hc.1, hcX⟩
  obtain ⟨i, hi, rfl⟩ := mem_image.1 this
  exact hc.2 (by rw [K.fac_val (hb.del_sub i (List.mem_toFinset.1 hi)).1];
                 exact List.mem_toFinset.1 hi)

end

theorem GamOf_OB_subset_GamE (D : List DumQ) :
    K.X.GamOf (K.OB D) ⊆ K.X.GamEOf K.OO := by
  intro c hc
  obtain ⟨c', hc', hc⟩ := mem_biUnion.1 hc
  exact mem_biUnion.2 ⟨c', (K.mem_OB.1 hc').1, K.X.Gam_subset_GamE K.H.valid c' hc⟩

theorem not_mem_LSX_of_GamE {c : Fin K.X.I.m} (hc : c ∈ K.X.GamEOf K.OO) :
    c ∉ K.X.LSX K.w₁.OL := fun h ↦ disjoint_left.1 (K.H.GamE_disjoint_LSX K.w₁) hc h

theorem GoodL_subset {ph : ℕ} {del : List ℕ} {D : List DumQ} (hg : K.GamSub del D) :
    K.GoodL ph del D ⊆ K.LSp del := by
  have hΓ : K.X.GamOf (K.OB D) ⊆ K.LSp del := fun c hc ↦ by
    obtain ⟨c', -, hc'⟩ := mem_biUnion.1 hc
    exact K.mem_LSp.2 ⟨K.X.Gam_subset_S c' hc', hg c hc⟩
  unfold GoodL
  split_ifs
  · exact hΓ
  · exact union_subset hΓ sdiff_subset

/-- If `s` centers are deleted, there are no good centers left. -/
theorem Base.GoodL_eq_empty {K : KSData} {ph : ℕ} {del : List ℕ} {D : List DumQ}
    (hb : K.Base del D)
    (hg : K.GamSub del D) (h : K.X.s ≤ del.length) : K.GoodL ph del D = ∅ := by
  refine eq_empty_of_forall_notMem fun c hc ↦ ?_
  have hX := hb.LSp_subset_LSX h
  have hcL := K.GoodL_subset hg hc
  unfold GoodL at hc
  split_ifs at hc
  · exact K.not_mem_LSX_of_GamE (K.GamOf_OB_subset_GamE D hc) (hX hcL)
  · rcases mem_union.1 hc with hc | hc
    · exact K.not_mem_LSX_of_GamE (K.GamOf_OB_subset_GamE D hc) (hX hcL)
    · exact (mem_sdiff.1 hc).2 (hX hcL)

theorem cc_of_empty {ph : ℕ} {del : List ℕ} {D : List DumQ} (h : K.GoodL ph del D = ∅) :
    K.cc ph del D := by
  unfold cc
  rw [h, sum_empty]
  have := K.H.opt_pos
  have := K.H.eps_pos
  unfold Ctx.opt
  positivity

/-! ### The nearest other center -/

theorem nearOther_spec {del : List ℕ} {l : ℕ} (hl : l < K.X.I.m) {w : Fin K.X.I.m}
    (hw : w ∈ K.X.S) (hwd : w.1 ∉ del) (hwl : w.1 ≠ l) :
    K.nearOther del l < K.X.I.m ∧ K.fac (K.nearOther del l) ∈ K.X.S ∧
      K.nearOther del l ∉ del ∧ K.nearOther del l ≠ l ∧
      ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ) =
        K.X.dF (K.fac l) (K.fac (K.nearOther del l)) ∧
      K.X.dF (K.fac l) (K.fac (K.nearOther del l)) ≤ K.X.dF (K.fac l) w := by
  set F := K.LS.filter fun c ↦ decide (c ∉ del ∧ c ≠ l) with hF
  have hmemF : ∀ i, i ∈ F ↔ i ∈ K.LS ∧ i ∉ del ∧ i ≠ l := fun i ↦ by
    rw [hF, List.mem_filter, decide_eq_true_iff]
  have hwF : w.1 ∈ F := (hmemF _).2 ⟨K.mem_S.1 hw, hwd, hwl⟩
  have hFne : F ≠ [] := List.ne_nil_of_mem hwF
  have hFm : ∀ i ∈ F, i < K.X.I.m := fun i hi ↦ K.hm i ((hmemF i).1 hi).1
  have hne := Instance.centers_nonempty hFne hFm
  have hq := Raw.nearQ_toRaw (I := K.X.I) (.inr (K.fac l)) hFne hFm
  rw [Instance.ptIdx_inr, K.fac_val hl] at hq
  set c' := K.X.I.near (K.X.I.centers F) hne (.inr (K.fac l)) with hc'
  have he : K.nearOther del l = c'.1 := hq
  have hc'F : c'.1 ∈ F := Instance.mem_centers.1 (Instance.near_mem hne _)
  obtain ⟨h1, h2, h3⟩ := (hmemF _).1 hc'F
  rw [he, K.fac_fin]
  refine ⟨c'.2, K.mem_S.2 h1, h2, h3, ?_, ?_⟩
  · have := Raw.fdist_toRaw (I := K.X.I) (.inr (K.fac l)) c'
    rw [Instance.ptIdx_inr, K.fac_val hl] at this
    rw [this]
    rfl
  · unfold Ctx.dF
    rw [Instance.dd_near]
    exact Instance.dSet_le (Instance.mem_centers.2 hwF) _

/-! ### Dummies and the total weight -/

/-- The real dummy of a matched cluster. -/
noncomputable def phi (D : List DumQ) (c : Fin K.X.I.m) : Dummy K.X.I := K.toDum (K.dumOf D c)

theorem dumOf_lt {D : List DumQ} {c : Fin K.X.I.m} (hc : c ∈ K.matched D) :
    (K.dumOf D c).1 < K.X.I.n + K.X.I.m := by
  obtain ⟨i, -, hi⟩ := K.dumOf_cand hc
  omega

theorem phi_injOn {D : List DumQ} (hD : D.Nodup) : Set.InjOn (K.phi D) (K.matched D) :=
  fun _ hc _ hc' he ↦ K.dumOf_injOn hD hc hc' (K.toDum_inj (K.dumOf_lt hc) (K.dumOf_lt hc') he)

theorem phi_mem {D : List DumQ} (hD : (toRaw K.X.I).ValidDums D) {c : Fin K.X.I.m}
    (hc : c ∈ K.matched D) : K.phi D c ∈ toDums K.X.I D := by
  rw [K.toDums_eq_map hD]
  exact List.mem_map_of_mem (K.dumOf_mem hc)

theorem length_toDums {D : List DumQ} (hD : (toRaw K.X.I).ValidDums D) :
    (toDums K.X.I D).length = D.length := by
  rw [K.toDums_eq_map hD, List.length_map]

section

variable {K}

theorem Base.radius_nonneg {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (hD : (toRaw K.X.I).ValidDums D) : ∀ l ∈ K.mixL D, 0 ≤ l.radius := by
  classical
  have hv := K.H.valid
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨c, hc, rfl⟩ := exists_eq_of_injOn K.w₁.φ_inj K.w₁.φ_mem K.w₁.length_eq.symm l hl
    exact (Instance.dd_nonneg hv _ _).trans (K.w₁.radius_ge c hc)
  · obtain ⟨c, hc, rfl⟩ := exists_eq_of_injOn (K.phi_injOn hb.dums_nodup)
      (fun c hc ↦ K.phi_mem hD hc) (by rw [K.length_toDums hD, hb.card]) l hl
    exact (Instance.dd_nonneg hv _ _).trans (hb.rad c hc).1

theorem Base.LSX_subset {del : List ℕ} {D : List DumQ} (hb : K.Base del D) :
    K.X.LSX K.w₁.OL ⊆ K.LSp del := fun c hc ↦ by
  refine K.mem_LSp.2 ⟨K.H.LSX_subset K.w₁ hc, fun hd ↦ ?_⟩
  have := (hb.del_sub c.1 hd).2
  rw [K.fac_fin] at this
  exact (mem_sdiff.1 this).2 hc

/-- **The mixed set costs less than `6 opt`** (`BCFGJPSSV26.Stable.Hyp.costMix_intermediate_lt`). -/
theorem Base.costMix_lt {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (hD : (toRaw K.X.I).ValidDums D) (hg : K.GamSub del D) :
    costMix K.X.I (K.LSp del) (K.mixL D) < 6 * K.X.opt :=
  K.H.costMix_intermediate_lt K.w₁ (Λ₂ := toDums K.X.I D) (M := K.matched D) (φ := K.phi D)
    hb.LSX_subset (K.LSp_subset del) (K.matched_subset D)
    (fun c hc ↦ by
      obtain ⟨c', -, hc'⟩ := mem_biUnion.1 hc
      exact K.mem_LSp.2 ⟨K.X.Gam_subset_S c' hc', hg c hc⟩)
    (fun c hc ↦ ⟨K.phi_mem hD hc, hb.rad c hc⟩)

/-- **The total weight** is at most `6 opt`. -/
theorem Base.sum_wt_le {del : List ℕ} {D : List DumQ} (hb : K.Base del D)
    (hD : (toRaw K.X.I).ValidDums D) (hg : K.GamSub del D) (ph : ℕ) :
    ∑ c ∈ K.LSp del, K.wt ph del D c ≤ 6 * K.X.opt := by
  classical
  have hv := K.H.valid
  have hopt : 0 < K.X.opt := K.H.opt_pos
  by_cases h0 : ph = 0
  · have h1 : ∑ c ∈ K.LSp del, K.wt ph del D c ≤ ∑ c ∈ K.X.S, K.wt ph del D c :=
      sum_le_sum_of_subset_of_nonneg (K.LSp_subset del) fun c _ _ ↦ K.wt_nonneg _ _ _ c
    have h2 : ∑ c ∈ K.X.S, K.wt ph del D c = K.X.I.costF K.X.S := by
      unfold wt
      simp only [h0, ↓reduceIte]
      rw [Instance.costF, Instance.sum_clusters K.H.S_nonempty]
      rfl
    have h3 := costF_le_four_opt hv K.H.k_le_m K.X.P.hN K.H.alo
    unfold Ctx.opt at hopt ⊢
    linarith
  · have h1 : ∑ c ∈ K.LSp del, K.wt ph del D c ≤ costMix K.X.I (K.LSp del) (K.mixL D) := by
      unfold wt costMix costMixOn
      simp only [h0, ↓reduceIte]
      rw [← sum_biUnion]
      · refine sum_le_sum_of_subset_of_nonneg (subset_univ _) fun j _ _ ↦ ?_
        exact dMix_nonneg hv (hb.radius_nonneg hD) _ _
      · intro c _ c' _ hcc'
        exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right
          (filter_subset _ _) (Instance.disjoint_cluster _ hcc'))
    linarith [hb.costMix_lt hD hg]

end

/-! ### Constants -/

theorem m_le_length : K.X.I.m ≤ (encInstance K.X.I).length := by
  have h : (distTable K.X.I).length ≤ (Encoding.encList (Encoding.encList Encoding.encRat)
      (distTable K.X.I)).length :=
    Turing.MultiTapeTM.length_le_length_encList _ _
  have hlen : (distTable K.X.I).length = K.X.I.n + K.X.I.m := by simp [distTable]
  rw [Combine.length_encInstance]
  omega

/-- `2^b ≥ 12 N³ m`. -/
theorem twoPow_b_ge : 12 * K.X.P.N ^ 3 * K.X.I.m ≤ 2 ^ K.X.b := by
  have hN := K.X.P.hN
  have h1 : K.X.I.m ≤ 2 ^ (encInstance K.X.I).length :=
    K.m_le_length.trans Nat.lt_two_pow_self.le
  have h2 : 12 * K.X.P.N ^ 3 ≤ 2 ^ (7 * K.X.P.N) := by
    have h3 : K.X.P.N ^ 7 ≤ 2 ^ (7 * K.X.P.N) := by
      rw [pow_mul']
      exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le 7
    have h4 : 12 * K.X.P.N ^ 3 ≤ K.X.P.N ^ 7 := by
      have : 12 ≤ K.X.P.N ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hN 4)
      calc 12 * K.X.P.N ^ 3 ≤ K.X.P.N ^ 4 * K.X.P.N ^ 3 := Nat.mul_le_mul_right _ this
        _ = K.X.P.N ^ 7 := by ring
    exact h4.trans h3
  calc 12 * K.X.P.N ^ 3 * K.X.I.m ≤ 2 ^ (7 * K.X.P.N) * 2 ^ (encInstance K.X.I).length :=
        Nat.mul_le_mul h2 h1
    _ = 2 ^ K.X.b := by
      rw [← pow_add]
      unfold Ctx.b Par.bits
      ring_nf

end KSData

end BCFGJPSSV26.Stable
