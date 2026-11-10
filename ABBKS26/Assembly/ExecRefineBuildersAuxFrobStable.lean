module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobRound

/-! Stability of buffered Frobenius separators under bounded coefficient rounding. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobStable

noncomputable section

open Matrix Common MeasureTheory ProbabilityTheory _root_.ABBKS26.Tree
open _root_.ABBKS26.Tree.RefineAux

variable {n k d : ℕ}

theorem buffered_frob_recorded (M : Mixture k d) (I : Finset (Fin k)) (p : StepParams)
    (N : Finset (Fin n)) (q : Statistic d) (c : Fin k → ℝ) (η : ℝ) (h : ℕ)
    (hI : 2 ≤ I.card) (hw : 0 < (p.w : ℝ)) (hη : 0 ≤ η)
    (hmass : (p.windowMass : ℝ) ≤ 1 / 2)
    (hR : (k - 1 : ℝ) * (2 * (p.DF : ℝ)) < p.R)
    (hspread : ∃ a ∈ I, ∃ b ∈ I, (p.R : ℝ) ≤ |c a - c b|)
    (hc : ∀ j ∈ I, c j = ∫ y : EuclideanSpace ℝ (Fin d), q.eval y.ofLp
      ∂multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
    (hvar : ∀ j ∈ I, variance (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤ (40 / (p.w : ℝ)) ^ 2)
    (htail : 4 * (40 / (p.w : ℝ)) ^ 2 / (p.DF : ℝ) ^ 2 ≤ p.tail)
    (hDF : 4 * p.WF ≤ p.DF) (hW : 0 < p.WF)
    (hmargin : 2 * η * (40 / (p.w : ℝ)) ≤ p.WF) :
    ∃ (e : Edge n d) (J : Finset (Fin k)), e.parent = N ∧ e.depth = h ∧
      e.statistic = q ∧ e.kind = .frobenius ∧
      ScaleValid M I p e ∧ BufferedComplete M I J p η e := by
  classical
  let s := I.image c
  have hsk : s.card ≤ k := Finset.card_image_le.trans (by simpa using Finset.card_le_univ I)
  have hk : (2 : ℝ) ≤ k := by
    exact_mod_cast hI.trans (by simpa using Finset.card_le_univ I)
  have hW' : (0 : ℝ) < p.WF := by exact_mod_cast hW
  have hDF' : 4 * (p.WF : ℝ) ≤ p.DF := by exact_mod_cast hDF
  have hDF0 : (0 : ℝ) < p.DF := by linarith only [hW', hDF']
  obtain ⟨a, ha, b, hb, hab⟩ := hspread
  have hbound : ((s.card : ℝ) - 1) * (2 * (p.DF : ℝ)) < p.R := by
    have hsk' : (s.card : ℝ) ≤ k := by exact_mod_cast hsk
    have hh := mul_le_mul_of_nonneg_right (sub_le_sub_right hsk' 1)
      (show 0 ≤ 2 * (p.DF : ℝ) by positivity)
    linarith only [hR, hh, hk]
  obtain ⟨lo, hlo, hi, hhi, hgap, hside⟩ :
      ∃ lo ∈ s, ∃ hi ∈ s, lo + 2 * (p.DF : ℝ) < hi ∧
        ∀ x ∈ s, x ≤ lo ∨ hi ≤ x := by
    have hca : c a ∈ s := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hcb : c b ∈ s := Finset.mem_image.mpr ⟨b, hb, rfl⟩
    rcases le_total (c a) (c b) with h | h
    · apply _root_.ABBKS26.Tree.CompleteAux.expectation_gap hca hcb
      rw [abs_of_nonpos (sub_nonpos.mpr h)] at hab
      linarith only [hab, hbound]
    · apply _root_.ABBKS26.Tree.CompleteAux.expectation_gap hcb hca
      rw [abs_of_nonneg (sub_nonneg.mpr h)] at hab
      linarith only [hab, hbound]
  obtain ⟨t, htlo, hthi⟩ := exists_rat_btwn (show lo + (p.DF : ℝ) < hi - p.DF by
    linarith only [hgap])
  let J := I.filter (fun j ↦ c j ≤ lo)
  let e : Edge n d := ⟨h, N, q, .frobenius, t, t - p.WF, t + p.WF⟩
  refine ⟨e, J, rfl, rfl, rfl, rfl, ?_, Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · exact ⟨by dsimp [e]; linarith only [hW], by dsimp [e]; linarith only [hW],
      hmass, rfl, rfl, hvar⟩
  · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hlo
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, heq.le⟩⟩
  · obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hhi
    refine ⟨j, Finset.mem_sdiff.mpr ⟨hj, ?_⟩⟩
    intro hh
    have hh' := (Finset.mem_filter.mp hh).2
    rw [heq] at hh'
    linarith only [hh', hgap, hDF0]
  · intro j hj C
    have hs : C.s ≤ 40 / (p.w : ℝ) := by
      have hh : 0 < 40 / (p.w : ℝ) := by positivity
      nlinarith only [C.variance, hvar j hj, C.nonneg, hh]
    have hm : 2 * η * C.s ≤ p.WF :=
      (mul_le_mul_of_nonneg_left hs (by positivity)).trans hmargin
    have hjgap := hside (c j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    apply frob_complete M j p e (c j) ((p.DF : ℝ) / 2)
      ((40 / (p.w : ℝ)) ^ 2) η C.s (j ∈ J) (hc j hj) (by positivity)
      (hvar j hj) (by convert htail using 1; ring)
    constructor
    · intro z hy
      change ((t - p.WF : ℚ) : ℝ) - 2 * η * C.s ≤ z ∧
        z ≤ ((t + p.WF : ℚ) : ℝ) + 2 * η * C.s at hy
      push_cast at hy
      rcases hjgap with hl | hr
      · have hh := le_abs_self (z - c j)
        change (p.DF : ℝ) / 2 ≤ |z - c j|
        linarith only [hy.1, hm, htlo, hl, hDF', hh]
      · have hh := neg_le_abs (z - c j)
        change (p.DF : ℝ) / 2 ≤ |z - c j|
        linarith only [hy.2, hm, hthi, hr, hDF', hh]
    · intro z hy
      by_cases hjJ : j ∈ J
      · simp only [hjJ, ite_true] at hy
        have hl := (Finset.mem_filter.mp hjJ).2
        have hh := le_abs_self (z - c j)
        change (t : ℝ) - 2 * η * C.s < z at hy
        linarith only [hy, hm, htlo, hl, hDF', hW', hh]
      · simp only [hjJ, ite_false] at hy
        have hr := hjgap.resolve_left (fun hl ↦ hjJ (Finset.mem_filter.mpr ⟨hj, hl⟩))
        have hh := neg_le_abs (z - c j)
        change z ≤ (t : ℝ) + 2 * η * C.s at hy
        linarith only [hy, hm, hthi, hr, hDF', hW', hh]


theorem recorded_half_margin
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : 2 ≤ I.card)
    (hleak : leakage ω N I ≤ leakageBudget params η h) (hsize : w * n / 4 ≤ N.card)
    (q : Statistic d) (c : Fin k → ℝ)
    (hspread : ∃ a ∈ I, ∃ b ∈ I, ((params h).R : ℝ) - 1 / 2 ≤ |c a - c b|)
    (hc : ∀ j ∈ I, c j = ∫ y : EuclideanSpace ℝ (Fin d), q.eval y.ofLp
      ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
    (hvar : ∀ j ∈ I, ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        (40 / ((params h).w : ℝ)) ^ 2) :
    ∃ e : Edge n d, e.parent = N ∧ e.depth = h ∧ e.statistic = q ∧ e.kind = .frobenius ∧
      ScaleValid M I (params h) e ∧
      Verify (params h) (fun l i ↦ r ((ω l).1, (ω l).2.2) i) e := by
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, _, _, _, hready, _⟩ := hp'
  obtain ⟨hw, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hcen⟩ := hready h hh
  obtain ⟨hmass, _, hWF, hDF, hCheb, hR, _⟩ := hcen
  have hroot : (1 : ℚ) ≤ sqrtUp (1 / (params h).straddle) := by
    unfold sqrtUp
    norm_cast
    omega
  have h8 : 8 * (40 / (params h).w) ≤ (params h).WF :=
    (le_mul_of_one_le_right (by positivity) hroot).trans hWF
  have hW : 0 < (params h).WF := (by positivity : 0 < 8 * (40 / (params h).w)).trans_le h8
  have hD : 0 < (params h).DF := (by positivity : 0 < 4 * (params h).WF).trans_le hDF
  have hwR : (0 : ℝ) < (params h).w := by exact_mod_cast hw
  have hDR : (0 : ℝ) < (params h).DF := by exact_mod_cast hD
  have hmargin : 2 * η * (40 / ((params h).w : ℝ)) ≤ (params h).WF := by
    have h8R : 8 * (40 / ((params h).w : ℝ)) ≤ (params h).WF := by exact_mod_cast h8
    apply le_trans _ h8R
    exact mul_le_mul_of_nonneg_right (by linarith only [hη100]) (by positivity)
  have htail : 4 * (40 / ((params h).w : ℝ)) ^ 2 / ((params h).DF : ℝ) ^ 2 ≤
      (params h).tail := by
    apply (div_le_iff₀ (sq_pos_of_pos hDR)).mpr
    exact_mod_cast hCheb
  have hmassR : ((params h).windowMass : ℝ) ≤ 1 / 2 := by
    rw [hmass]
    norm_num
  have hRR : 2 * (k - 1 : ℝ) * (2 * ((params h).DF : ℝ) +
      3 * (params h).WF) + 1 ≤ (params h).R := by exact_mod_cast hR
  let p' : StepParams := { params h with R := (params h).R - 1 / 2 }
  have hR' : (k - 1 : ℝ) * (2 * (p'.DF : ℝ)) < p'.R := by
    have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hW' : (0 : ℝ) < (params h).WF := by exact_mod_cast hW
    have hDF' : (0 : ℝ) < (params h).DF := by exact_mod_cast hD
    have ht := mul_nonneg (sub_nonneg.mpr hk) hW'.le
    have ht' := mul_nonneg (sub_nonneg.mpr hk) hDF'.le
    dsimp only [p']
    push_cast
    nlinarith only [hRR, ht, ht']
  have hspread' : ∃ a ∈ I, ∃ b ∈ I, (p'.R : ℝ) ≤ |c a - c b| := by
    simpa only [p', Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      using hspread
  obtain ⟨e, J, hparent, hdepth, hstat, hkind, hscale, hpop⟩ :=
    buffered_frob_recorded M I p' N q c η h hI hwR hη.le hmassR hR'
      hspread' hc hvar htail hDF hW hmargin
  change ScaleValid M I (params h) e at hscale
  change BufferedComplete M I J (params h) η e at hpop
  refine ⟨e, hparent, hdepth, hstat, hkind, hscale, ?_⟩
  exact hp.verify_of_bufferedComplete .centered M ε w η Δ D ω r params h hh e I J
    (Finset.card_pos.mp (by omega)) (by rwa [hparent]) (by rwa [hparent]) hpop

/-- Contracting and perturbing the two centers loses at most the displayed additive margin. -/
theorem center_gap_lower (a b a' b' R s e : ℝ) (hs : 0 ≤ s)
    (hgap : R ≤ |a - b|) (ha : |a' - s * a| ≤ e) (hb : |b' - s * b| ≤ e) :
    s * R - 2 * e ≤ |a' - b'| := by
  have h := calc
    s * R ≤ s * |a - b| := mul_le_mul_of_nonneg_left hgap hs
    _ = |s * a - s * b| := by rw [← mul_sub, abs_mul, abs_of_nonneg hs]
    _ = |(s * a - a') + (a' - b') + (b' - s * b)| := by congr 1; ring
    _ ≤ |s * a - a'| + |a' - b'| + |b' - s * b| := abs_add_three _ _ _
    _ ≤ e + |a' - b'| + e := by rw [abs_sub_comm (s * a) a']; gcongr
  linarith only [h]

/-- The shared FAR call supplies a pure certificate with the original trace gap. -/
theorem far_trace_witness (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (N : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hfar : centeredFar F M ω r (ps h) fuel N I hI) :
    ∃ q, (q, true) ∈ FrobPure.pool F (ps h) x fuel N ∧
      ∃ i ∈ I, ∃ j ∈ I, ((ps h).R : ℝ) ≤
        |(q.A.map (algebraMap ℚ ℝ) * M.S i).trace -
          (q.A.map (algebraMap ℚ ℝ) * M.S j).trace| := by
  subst x
  let p := ps h
  let ref := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let a : FrameArgs × ℕ := ((d, (N.sort (· ≤ ·)).map (fun l ↦
    List.ofFn fun i ↦ r ((ω l).1, (ω l).2.2) i), p.w / 2, |p.R|,
      p.frameAccuracy), fuel)
  obtain ⟨q, hq, _, i, j, hgap⟩ := FrobPure.far_certificate F hF a ref
    (|p.R| : ℚ) (20 / ((p.w / 2 : ℚ) : ℝ)) (fun j ↦ hp.2.1 _)
    (fun j ↦ (hp.1.posDef _).posSemidef) hfar
  refine ⟨q, hq, ABBKS26.RefineAux.component I i, I.orderEmbOfFin_mem rfl i,
    ABBKS26.RefineAux.component I j, I.orderEmbOfFin_mem rfl j, ?_⟩
  have hR : (p.R : ℝ) ≤ (|p.R| : ℚ) := by exact_mod_cast le_abs_self p.R
  apply hR.trans
  have hcenter (j : Fin I.card) : ref.model.mean j = 0 := hp.2.1 _
  change ((|p.R| : ℚ) : ℝ) ≤ |(q.A.map (algebraMap ℚ ℝ) * ref.model.cov i).trace -
    (q.A.map (algebraMap ℚ ℝ) * ref.model.cov j).trace|
  simpa only [Robust.statCenter, FrameProgram.quadOf, statisticList, matrix_roundtrip,
    vector_roundtrip, hcenter, qform, mulVec_zero, dotProduct_zero, zero_add, add_zero,
    add_sub_add_right_eq_sub] using hgap

/-- A rounded symmetric quadratic retains a verified buffered separator whenever its
variance precision and the half-unit center-error allowance are met. -/
theorem rounded_recorded
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (ps : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : 2 ≤ I.card)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card)
    (q : Statistic d) (hq : q.Aᵀ = q.A) (p b : ℕ) (s : ℚ) (c : ℝ)
    (hs : 0 ≤ (s : ℝ)) (hs1 : (s : ℝ) < 1) (hc : 0 ≤ c)
    (hupper : ∀ j ∈ I, ∀ v, qform (M.S j) v ≤ c * sqnorm v)
    (hv : ∀ j ∈ I, variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (multivariateGaussian 0 (M.S j)) ≤ (40 / ((ps h).w : ℝ)) ^ 2)
    (hmag : ∀ i j, |s * q.A i j| ≤ 2 ^ b)
    (hprec : 2 * c ^ 2 * ((d : ℝ) * (1 / (2 : ℝ) ^ p)) ^ 2 ≤
      (1 - (s : ℝ)) ^ 2 * (40 / ((ps h).w : ℝ)) ^ 2)
    (hgap : ∃ i ∈ I, ∃ j ∈ I, ((ps h).R : ℝ) ≤
      |(q.A.map (algebraMap ℚ ℝ) * M.S i).trace -
        (q.A.map (algebraMap ℚ ℝ) * M.S j).trace|)
    (hloss : (1 - (s : ℝ)) * ((ps h).R : ℝ) +
      2 * (d : ℝ) ^ 2 * (1 / (2 : ℝ) ^ p) * c ≤ 1 / 2) :
    ∃ t, Verify (ps h) (fun l i ↦ r ((ω l).1, (ω l).2.2) i)
      (Thresholds.typedEdge h N (FrobRound.rounded p b s q) (ps h).WF t) := by
  let q' := FrobRound.rounded p b s q
  let centers : Fin k → ℝ := fun j ↦ (q'.A.map (algebraMap ℚ ℝ) * M.S j).trace
  have hsym := FrobRound.rounded_symmetric p b s q hq
  have hspread : ∃ i ∈ I, ∃ j ∈ I, ((ps h).R : ℝ) - 1 / 2 ≤
      |centers i - centers j| := by
    obtain ⟨i, hi, j, hj, hgap⟩ := hgap
    have hiS := Robust.FilterAux.entries_le_of_qform_le (M.S i)
      (hp.1.posDef i).posSemidef c (hupper i hi)
    have hjS := Robust.FilterAux.entries_le_of_qform_le (M.S j)
      (hp.1.posDef j).posSemidef c (hupper j hj)
    have hiE := FrobRound.rounded_center_error p b s q (M.S i) c hmag hiS
    have hjE := FrobRound.rounded_center_error p b s q (M.S j) c hmag hjS
    have hb := center_gap_lower _ _ _ _ _ _ _ hs hgap hiE hjE
    refine ⟨i, hi, j, hj, ?_⟩
    dsimp only [centers, q']
    nlinarith only [hb, hloss]
  have hcenters (j : Fin k) (_hj : j ∈ I) : centers j =
      ∫ y : EuclideanSpace ℝ (Fin d), q'.eval y.ofLp
        ∂multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j) := by
    rw [hp.2.1 j, WithLp.toLp_zero]
    exact (ABBKS26.RefineAux.pureStatistic_integral q'.A hsym
      (M.S j) (hp.1.posDef j).posSemidef).symm
  have hvar (j : Fin k) (hj : j ∈ I) : variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ q'.eval y.ofLp)
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
        (40 / ((ps h).w : ℝ)) ^ 2 := by
    rw [hp.2.1 j, WithLp.toLp_zero]
    exact FrobRound.rounded_variance p b s q hq (M.S j) (hp.1.posDef j).posSemidef
      c _ hs hs1 hc (hupper j hj) (hv j hj) hmag hprec
  obtain ⟨e, heN, heh, heq, hekind, hes, hev⟩ := recorded_half_margin
    M ε w η Δ D ω r ps hp h hh N I hI hl hN q' centers hspread hcenters hvar
  have hsides := hes.2.2
  rw [hekind] at hsides
  have he : e = Thresholds.typedEdge h N q' (ps h).WF e.threshold := by
    cases e
    simp only [Thresholds.typedEdge, Edge.mk.injEq] at *
    exact ⟨heh, heN, heq, hekind, trivial, hsides.2.1, hsides.2.2.1⟩
  exact ⟨e.threshold, he ▸ hev⟩

end

end ABBKS26.Assembly.Exec.RefineSynth.FrobStable
