module

public import BCFGJPSSV26.Stable.Alg.ClusterSamplingStep

/-!
# The analysis of the cluster sampling: densities

From every invariant state, at least a fraction `q₂ = 1/(12 N³)` of the chunks is good
(`BCFGJPSSV26.Stable.KSData.card_good`): fair bits give `1/2`; the sampling step gives
`ε³/6 - m/2^b ≥ ε³/12` (the good centers weigh at least `ε³ opt` out of at most `6 opt`); the
radius step gives `1/(2 G_r)`, a grid point being in the right interval.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

theorem one_le_b : 1 ≤ K.X.b := by
  have := K.X.P.hN
  unfold Ctx.b Par.bits
  omega

theorem N_pos' : (0 : ℝ) < K.X.P.N := K.X.P.N_pos'

theorem q₂_eq : K.X.P.q₂ = 1 / (12 * (K.X.P.N : ℝ) ^ 3) := rfl

theorem q₂_nonneg : 0 ≤ K.X.P.q₂ := by
  rw [q₂_eq]
  have := K.N_pos'
  positivity

theorem q₂_le_half : K.X.P.q₂ ≤ 1 / 2 := by
  rw [q₂_eq]
  have : (201 : ℝ) ≤ K.X.P.N := K.X.P.N_ge
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 201) this 3]

theorem card_fin_b : (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) = 2 ^ K.X.b := by
  rw [Fintype.card_fin]
  push_cast
  rfl

/-- Fair bits: half of the chunks. -/
theorem card_bit_iff (P : Prop) [Decidable P] :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
        (cbit K.X.b u = true ↔ P)).card := by
  have h := card_cbit K.one_le_b (decide P)
  have he : ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
      (cbit K.X.b u = true ↔ P)) =
      (univ.filter fun u : Fin (2 ^ K.X.b) ↦ cbit K.X.b u = decide P) := by
    ext u
    simp only [mem_filter, mem_univ, true_and]
    cases cbit K.X.b u <;> by_cases hP : P <;> simp [hP]
  rw [he, h, K.card_fin_b]
  have h2 : (2 : ℝ) ^ K.X.b = 2 * 2 ^ (K.X.b - 1) := by
    rw [← pow_succ']
    congr 1
    have := K.one_le_b
    omega
  have hq := K.q₂_le_half
  push_cast
  rw [h2]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (K.X.b - 1)]

theorem card_mono {P Q : Fin (2 ^ K.X.b) → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ u, P u → Q u) :
    (((univ : Finset (Fin (2 ^ K.X.b))).filter P).card : ℝ) ≤ (univ.filter Q).card := by
  exact_mod_cast card_le_card fun u hu ↦ mem_filter.2 ⟨mem_univ _, h u (mem_filter.1 hu).2⟩

theorem card_all (P : Fin (2 ^ K.X.b) → Prop) [DecidablePred P] (hP : ∀ u, P u) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter P).card := by
  rw [filter_true_of_mem fun u _ ↦ hP u, card_univ]
  have hq := K.q₂_le_half
  have : (0 : ℝ) ≤ Fintype.card (Fin (2 ^ K.X.b)) := Nat.cast_nonneg _
  nlinarith

open Classical in
/-- **Density of the sampling step.** -/
theorem card_good_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hI : K.Inv (ph, j, del, D, 1, l, r₀)) (hph : ph ≠ 2) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
        K.Good (ph, j, del, D, 1, l, r₀) u).card := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hns : ¬ K.cc ph del D := hI.sample hph2 rfl
  have hD : (toRaw K.X.I).ValidDums D := fun d hd ↦ by
    obtain ⟨i, hi, he⟩ := (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
    have := (hb.del_sub i hi).1
    rw [he, Raw.n_toRaw, Raw.m_toRaw]
    omega
  have hopt : 0 < K.X.opt := K.H.opt_pos
  have he := K.H.eps_pos
  have hcc : K.X.ε ^ 3 * K.X.opt ≤ ∑ c ∈ K.GoodL ph del D, K.wt ph del D c := by
    unfold cc at hns
    exact not_lt.1 hns
  have hpos : 0 < ∑ c ∈ K.GoodL ph del D, K.wt ph del D c :=
    lt_of_lt_of_le (by positivity) hcc
  have hne : K.cand del ≠ [] := by
    intro hc
    have he : K.LSp del = ∅ := by
      ext c
      rw [LSp, hc]
      simp [Instance.centers]
    exact hns (K.cc_of_empty (subset_empty.1 (he ▸ K.GoodL_subset hg)))
  have hA : ∀ c ∈ K.GoodL ph del D, c.1 ∈ K.cand del := fun c hc ↦
    Instance.mem_centers.1 (K.GoodL_subset hg hc)
  have h := card_sample_ge (b := K.X.b) (K.cand_nodup del) (fun i hi ↦ K.cand_lt hi)
    (K.wq ph del D) (K.wt ph del D) (fun c _ ↦ K.wq_eq hD hne c)
    (fun c _ ↦ K.wt_nonneg ph del D c) (K.GoodL ph del D) hA hpos
  rw [← K.ksWeights_eq] at h
  have hW : ∑ c ∈ (univ.filter fun c : Fin K.X.I.m ↦ c.1 ∈ K.cand del), K.wt ph del D c ≤
      6 * K.X.opt := hb.sum_wt_le hD hg ph
  have hWpos : 0 < ∑ c ∈ (univ.filter fun c : Fin K.X.I.m ↦ c.1 ∈ K.cand del),
      K.wt ph del D c :=
    lt_of_lt_of_le hpos (sum_le_sum_of_subset_of_nonneg (fun c hc ↦ mem_filter.2
      ⟨mem_univ _, hA c hc⟩) fun c _ _ ↦ K.wt_nonneg ph del D c)
  -- the good centers are at most `m`
  have hAcard : ((K.GoodL ph del D).card : ℝ) ≤ K.X.I.m := by
    have h1 : (K.GoodL ph del D).card ≤ K.X.S.card :=
      card_le_card ((K.GoodL_subset hg).trans (K.LSp_subset del))
    have h2 : K.X.S.card ≤ K.X.I.m := K.H.alo.1 ▸ K.H.k_le_m
    exact_mod_cast h1.trans h2
  -- the sampled center is good
  have hsub : ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
      ∃ c ∈ K.GoodL ph del D, c.1 = (K.cand del).getD (wsample K.X.b
        (ksWeights (toRaw K.X.I) K.LS K.Λ₁ ph del D (K.cand del)) u.1) 0) ⊆
      (univ.filter fun u ↦ K.Good (ph, j, del, D, 1, l, r₀) u) := by
    intro u hu
    rw [mem_filter] at hu ⊢
    obtain ⟨c, hc, hce⟩ := hu.2
    refine ⟨mem_univ _, (K.good_tag1 hph).2 ?_⟩
    change K.fac ((K.cand del).getD (wsample K.X.b (ksWeights (toRaw K.X.I) K.LS K.Λ₁ ph del D
      (K.cand del)) u.1) 0) ∈ _
    rw [← hce, K.fac_fin]
    exact hc
  refine le_trans ?_ (le_trans h (by exact_mod_cast card_le_card hsub))
  -- arithmetic: `2^b ε³/6 - m ≥ 2^b ε³/12 = q₂ 2^b`
  rw [K.card_fin_b]
  set W := ∑ c ∈ (univ.filter fun c : Fin K.X.I.m ↦ c.1 ∈ K.cand del), K.wt ph del D c
  set A := ∑ c ∈ K.GoodL ph del D, K.wt ph del D c
  have hK : (12 : ℝ) * (K.X.P.N : ℝ) ^ 3 * K.X.I.m ≤ 2 ^ K.X.b := by
    exact_mod_cast K.twoPow_b_ge
  have hN := K.N_pos'
  have heps : K.X.ε = 1 / (K.X.P.N : ℝ) := rfl
  have hK0 : (0 : ℝ) < 2 ^ K.X.b := by positivity
  have h1 : (2 : ℝ) ^ K.X.b * (K.X.ε ^ 3 / 6) ≤ 2 ^ K.X.b * A / W := by
    rw [le_div_iff₀ hWpos]
    have : K.X.ε ^ 3 / 6 * W ≤ A := by
      have : K.X.ε ^ 3 / 6 * W ≤ K.X.ε ^ 3 / 6 * (6 * K.X.opt) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      linarith
    nlinarith
  have h2 : (K.X.I.m : ℝ) ≤ 2 ^ K.X.b * (K.X.ε ^ 3 / 12) := by
    rw [heps]
    have : (2 : ℝ) ^ K.X.b * ((1 / (K.X.P.N : ℝ)) ^ 3 / 12) =
        2 ^ K.X.b / (12 * (K.X.P.N : ℝ) ^ 3) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  rw [q₂_eq]
  have h3 : 1 / (12 * (K.X.P.N : ℝ) ^ 3) * 2 ^ K.X.b = 2 ^ K.X.b * (K.X.ε ^ 3 / 12) := by
    rw [heps]
    field_simp
  rw [h3]
  linarith

open Classical in
/-- **Density of the radius step.** -/
theorem card_good_tag4 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hI : K.Inv (ph, j, del, D, 4, l, r₀)) (hph : ph ≠ 2) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
        K.Good (ph, j, del, D, 4, l, r₀) u).card := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hm : K.Mid del D l := hI.mid hph2 (by simp)
  have hr : K.Rad0 D l r₀ := hI.rad0 hph2 (by simp)
  rcases hpick : K.pick (K.matched D) (K.X.I.n + l) with _ | c
  · refine K.card_all _ fun u ↦ (K.good_tag4 hph).2 fun c h ↦ ?_
    rw [hpick] at h
    exact absurd h (by simp)
  obtain ⟨hcO, hcM, hcand⟩ := K.pick_some hpick
  have hcOB : c ∈ K.OB D := K.mem_OB.2 ⟨hcO, hcM⟩
  have hlc : K.fac l ∈ K.X.GamE c := by
    rw [← K.fac_val hm.lt] at hcand
    exact K.cand_iff.1 hcand
  have hfar := K.isFar_of_OB hcOB
  have hp := hfar.per_pos
  have hN := K.N_pos'
  have hN' : (201 : ℝ) ≤ K.X.P.N := K.X.P.N_ge
  have heps : K.X.ε = 1 / (K.X.P.N : ℝ) := rfl
  have he := K.H.eps_pos
  have he1 : K.X.ε ≤ 1 / 201 := K.X.P.eps_le
  obtain ⟨hr0, hr1, hr2⟩ : 0 < (r₀ : ℝ) ∧ K.X.ε ^ 2 * K.X.per c / 3 ≤ r₀ ∧
      (r₀ : ℝ) ≤ 15 * K.X.per c := ⟨hr.1, hr.2 c hcOB hlc⟩
  set d := K.X.dF c (K.fac l) with hd
  -- `d` is at least `η per/(1 + 2ε)`, at most `(1 + κ + 3ε) per`
  have hdlo : eta * (K.X.per c / (1 + 2 * K.X.ε)) < d := by
    have h1 := hfar.far
    have h2 := hfar.avg_ge
    have h3 : 0 ≤ K.X.avgS c := by
      unfold Ctx.avgS
      exact div_nonneg (Instance.costOn_nonneg K.H.valid _ _) (Nat.cast_nonneg _)
    have h4 : K.X.dOS c ≤ d := Instance.dSet_le (mem_sdiff.1 hm.mem).1 _
    have : eta * (K.X.per c / (1 + 2 * K.X.ε)) ≤ eta * K.X.avgO c :=
      mul_le_mul_of_nonneg_left h2 (by unfold eta; norm_num)
    nlinarith
  have hdhi : d ≤ 2 * K.X.per c := by
    have h1 := (K.mem_GamE.1 hlc).2.1
    rw [K.dF_comm] at h1
    have := K.kap_le c
    nlinarith
  have hlo : (r₀ : ℝ) / (K.X.P.N : ℝ) ^ 3 ≤ d := by
    have h1 : (r₀ : ℝ) / (K.X.P.N : ℝ) ^ 3 = (r₀ : ℝ) * K.X.ε ^ 3 := by rw [heps]; field_simp
    rw [h1]
    have h2 : (r₀ : ℝ) * K.X.ε ^ 3 ≤ 15 * K.X.per c * K.X.ε ^ 3 :=
      mul_le_mul_of_nonneg_right hr2 (by positivity)
    have h3 : 15 * K.X.ε ^ 3 ≤ eta / (1 + 2 * K.X.ε) := by
      rw [le_div_iff₀ (by positivity)]
      unfold eta
      have : K.X.ε ^ 3 ≤ (1 / 201) ^ 3 := pow_le_pow_left₀ he.le he1 3
      nlinarith
    have h4 : 15 * K.X.per c * K.X.ε ^ 3 ≤ eta * (K.X.per c / (1 + 2 * K.X.ε)) :=
      calc 15 * K.X.per c * K.X.ε ^ 3 = K.X.per c * (15 * K.X.ε ^ 3) := by ring
        _ ≤ K.X.per c * (eta / (1 + 2 * K.X.ε)) := mul_le_mul_of_nonneg_left h3 hp.le
        _ = eta * (K.X.per c / (1 + 2 * K.X.ε)) := by ring
    linarith
  have hhi : (1 + 1 / (K.X.P.N : ℝ)) * d ≤ (K.X.P.N : ℝ) ^ 7 * r₀ := by
    have h1 : K.X.per c ≤ 3 * (K.X.P.N : ℝ) ^ 2 * r₀ := by
      have : K.X.ε ^ 2 * K.X.per c / 3 = K.X.per c / (3 * (K.X.P.N : ℝ) ^ 2) := by
        rw [heps]; field_simp
      rw [this, div_le_iff₀ (by positivity)] at hr1
      linarith
    have h2 : (1 + 1 / (K.X.P.N : ℝ)) ≤ 2 := by
      have : 1 / (K.X.P.N : ℝ) ≤ 1 := by rw [div_le_one hN]; linarith
      linarith
    have h3 : 12 * (K.X.P.N : ℝ) ^ 2 ≤ (K.X.P.N : ℝ) ^ 7 := by
      have : (12 : ℝ) ≤ (K.X.P.N : ℝ) ^ 5 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 201) hN' 5
        linarith
      nlinarith [pow_pos hN 2]
    have hd0 : 0 ≤ d := Instance.dd_nonneg K.H.valid _ _
    calc (1 + 1 / (K.X.P.N : ℝ)) * d ≤ 2 * (2 * K.X.per c) :=
          mul_le_mul h2 hdhi hd0 (by norm_num)
      _ ≤ 12 * (K.X.P.N : ℝ) ^ 2 * r₀ := by nlinarith
      _ ≤ (K.X.P.N : ℝ) ^ 7 * r₀ := mul_le_mul_of_nonneg_right h3 hr0.le
  obtain ⟨x, hx, hx1, hx2⟩ := exists_grid_mem (by have := K.X.P.hN; omega) hr0 hlo hhi r₀ rfl
  have hGr0 : 0 < Par.Gr K.X.P.N := by unfold Par.Gr; omega
  have hGrK : Par.Gr K.X.P.N ≤ 2 ^ K.X.b := by
    have := K.twoPow_b_ge
    have hm := K.m_pos
    have hN2 : 10 * K.X.P.N ^ 2 + 1 ≤ 12 * K.X.P.N ^ 3 := by
      have : 1 ≤ K.X.P.N := by have := K.X.P.hN; omega
      nlinarith [Nat.pow_le_pow_left this 2]
    unfold Par.Gr
    nlinarith
  have hc := card_cunif hGr0 hGrK hx
  have hsub : ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
      cunif (Par.Gr K.X.P.N) u = x) ⊆
      (univ.filter fun u ↦ K.Good (ph, j, del, D, 4, l, r₀) u) := by
    intro u hu
    rw [mem_filter] at hu ⊢
    refine ⟨mem_univ _, (K.good_tag4 hph).2 fun c' hc' ↦ ?_⟩
    rw [hpick] at hc'
    obtain rfl := Option.some.inj hc'
    rw [hu.2, heps]
    exact ⟨hx1, hx2⟩
  refine le_trans ?_ (le_trans hc (by exact_mod_cast card_le_card hsub))
  rw [K.card_fin_b, q₂_eq]
  have hGr : (2 : ℝ) * (Par.Gr K.X.P.N : ℕ) ≤ 12 * (K.X.P.N : ℝ) ^ 3 := by
    unfold Par.Gr
    push_cast
    nlinarith [pow_pos hN 2]
  have hK0 : (0 : ℝ) < 2 ^ K.X.b := by positivity
  rw [div_mul_eq_mul_div, one_mul]
  exact div_le_div_of_nonneg_left hK0.le (by positivity) hGr

open Classical in
/-- **Density**: from every invariant state, at least `q₂ 2^b` chunks are good. -/
theorem card_good {st : KSState} (hI : K.Inv st) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦ K.Good st u).card := by
  obtain ⟨ph, j, del, D, tag, l, r₀⟩ := st
  by_cases hph : ph = 2
  · refine K.card_all _ fun u ↦ ?_
    rw [Good, KSState.phase_mk, ite_eq_left hph]
    trivial
  have ht : tag ≤ 5 := hI.tag_le
  interval_cases tag
  · by_cases hjs : j = K.X.s
    · exact K.card_all _ fun u ↦ (K.good_tag0 hph).2 (.inl hjs)
    · exact le_trans (K.card_bit_iff (K.cc ph del D))
        (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 0, l, r₀) u)
          fun u hu ↦ (K.good_tag0 hph).2 (.inr hu))
  · exact K.card_good_tag1 hI hph
  · exact le_trans (K.card_bit_iff (K.fac l ∉ K.X.GamOf (K.OB D)))
      (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 2, l, r₀) u)
        fun u hu ↦ (K.good_tag2 hph).2 hu)
  · exact le_trans (K.card_bit_iff (∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c ∧
        K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ)))
      (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 3, l, r₀) u)
        fun u hu ↦ (K.good_tag3 hph).2 hu)
  · exact K.card_good_tag4 hI hph
  · exact le_trans (K.card_bit_iff (¬ ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c))
      (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 5, l, r₀) u)
        fun u hu ↦ (K.good_tag5 hph).2 hu)

end KSData

end BCFGJPSSV26.Stable
