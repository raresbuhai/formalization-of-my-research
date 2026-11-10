module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdModel

/-! High-moment certificates in the executable common-covariance affine frame. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdMoments

open Common Matrix _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

private theorem moment_weight_allowance
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .identical M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1) :
    η ≤ 1 / (100 * IdCov.tDegree (params h).w : ℝ) := by
  let p := params h
  let t := IdCov.tDegree p.w
  have hηc := IdFrame.eta_contamination .identical M ε w η Δ D ω r params hp h hh
  obtain ⟨_, _, _, _, _, _, hη, _, _, _, _, _, _, _, hready, _⟩ := hp
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hready h hh
  obtain ⟨_, _, _, _, heq, hc, _⟩ := hm
  have ht : (1 : ℚ) ≤ t := by
    exact_mod_cast (show 1 ≤ t by unfold t IdCov.tDegree; omega)
  have hbase : (1 : ℚ) ≤ 80 * t / p.w := by
    rw [le_div_iff₀ hw]
    linarith only [hw2, ht]
  have hB : (1 : ℚ) ≤ 10000 * (2 * (80 * t / p.w) ^ (4 * t)) := by
    have hh := one_le_pow₀ hbase (n := 4 * t)
    linarith only [hh]
  have he0 : (0 : ℚ) ≤ p.momentError := by
    rw [heq]
    unfold IdCov.etaStar IdCov.epsilonSys IdCov.epsilonId IdCov.cStar IdCov.epsilonR
    positivity
  have hcE : p.contamination ≤ p.momentError :=
    hc.trans (div_le_self he0 hB)
  have hEQ : p.momentError ≤ 1 / (1000 * t) := by
    rw [heq]
    exact ABBKS26.RefineAux.etaStar_weight_allowance p.w p.subspaceAccuracy ⟨hβ, hβ100⟩
  have hcER : (p.contamination : ℝ) ≤ p.momentError := by exact_mod_cast hcE
  have hER : (p.momentError : ℝ) ≤ 1 / (1000 * t : ℝ) := by
    have hc := Rat.cast_le (K := ℝ) |>.mpr hEQ
    push_cast at hc
    exact hc
  have hηE : η ≤ p.momentError := by linarith only [hηc, hcER, hη.le]
  apply hηE.trans (hER.trans ?_)
  have htRpos : (0 : ℝ) < t := by
    exact_mod_cast (show (0 : ℚ) < t by linarith only [ht])
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have htR : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  linarith only [htR]

private theorem reference_valid_moment
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .identical M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty) :
    (ABBKS26.RefineAux.roundedReference M ω r N I hI).Valid
      (ABBKS26.RefineAux.momentWeight (params h).w (IdCov.tDegree (params h).w)) := by
  let p := params h
  let t := IdCov.tDegree p.w
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let w' := ABBKS26.RefineAux.momentWeight p.w t
  have hv := hp.reference_valid_at .identical M ε w η Δ D ω r params N I hI
  have hw := hp.weight_at .identical M ε w η Δ D ω r params h (by omega)
  have hηsmall := moment_weight_allowance M ε w η Δ D ω r params hp h hh
  obtain ⟨_, _, _, hw0, hwj, _, hη, hη100, _, hg, _, _, _, _, hready, _⟩ := hp
  have hpw := (hready h hh).1
  have ht : 1 ≤ t := by unfold t IdCov.tDegree; omega
  have hw' : (0 : ℝ) < w' := by
    exact_mod_cast ABBKS26.RefineAux.momentWeight_pos p.w t hpw ht
  have hle : (w' : ℝ) ≤ (1 - η) * w := by
    dsimp only [w', ABBKS26.RefineAux.momentWeight]
    push_cast
    rw [hw]
    have hm := mul_le_mul_of_nonneg_left hηsmall hw0.le
    dsimp only [p, t] at hm ⊢
    nlinarith only [hm]
  have hG : (0 : ℝ) < R.reference.card := by
    exact_mod_cast Finset.card_pos.mpr hv.2.2.2.2.1
  have hGn : (R.reference.card : ℝ) ≤ n := by
    exact_mod_cast (Finset.card_le_card (Finset.subset_univ R.reference)).trans_eq
      (Finset.card_fin n)
  refine ⟨⟨hw', ?_, hv.1.2.2.1, hv.1.2.2.2⟩, hv.2⟩
  intro j
  change (w' : ℝ) ≤ ((cluster (labels ω) (ABBKS26.RefineAux.component I j)).card : ℝ) /
    R.reference.card
  rw [le_div_iff₀ hG]
  have hcount := (abs_le.mp (hg.1 (ABBKS26.RefineAux.component I j))).1
  have hweight := mul_le_mul_of_nonneg_left (hwj (ABBKS26.RefineAux.component I j))
    (by linarith only [hη100] : 0 ≤ 1 - η)
  have hweightn := mul_le_mul_of_nonneg_right hweight (Nat.cast_nonneg (α := ℝ) n)
  have hlen := mul_le_mul_of_nonneg_left hGn hw'.le
  have hlen' := mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg (α := ℝ) n)
  nlinarith only [hcount, hweightn, hlen, hlen']

theorem certificate_of_center_bound
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared .identical M ε w η Δ D ω r params) (h : ℕ) (hh : h < k - 1)
    (N : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω N I ≤ leakageBudget params η h) (hN : w * n / 4 ≤ N.card)
    (F : Robust.FrameResult d)
    (hF : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r N I hI) F
      (((params h).w / 2 : ℚ) : ℝ) (|(params h).R| : ℚ)
        (((params h).isotropy / 10000 : ℚ) : ℝ))
    (MC : MomentCode) (hMC : MomentSpec MC) (fuel : ℕ)
    (a : Fin d → ℚ)
    (ha : sqnorm (F.transform.map (algebraMap ℚ ℝ) *ᵥ
      ((fun i ↦ (a i : ℝ)) - (ABBKS26.RefineAux.roundedReference M ω r N I hI).mean)) ≤
        1 / 100)
    (hfu : momentFuel n d (Finset.Icc 1 (4 * IdCov.tDegree (params h).w)) ≤ fuel)
    (J : Finset ℕ) (hJ : ∀ j ∈ J, 1 ≤ j)
    (hJt : ∀ j ∈ J, j ≤ 4 * IdCov.tDegree (params h).w) :
    let p := params h
    let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
    let T := F.transform.map (algebraMap ℚ ℝ)
    let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
    let w' := ABBKS26.RefineAux.momentWeight p.w (IdCov.tDegree p.w)
    Robust.Certified
      (ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))).model
      (fun q ↦ SoS.toReal (momentProc MC
        (ABBKS26.RefineAux.affinePoints x F.transform a) N J w' p.contamination fuel q)) J
      (fun _ ↦ (p.momentError : ℝ)) := by
  classical
  by_cases hJe : J = ∅
  · subst J
    dsimp only
    exact fun q hq ↦ (Finset.notMem_empty q hq).elim
  let p := params h
  let t := IdCov.tDegree p.w
  let x := fun l i ↦ r ((ω l).1, (ω l).2.2) i
  let R := ABBKS26.RefineAux.roundedReference M ω r N I hI
  let T := F.transform.map (algebraMap ℚ ℝ)
  let w' := ABBKS26.RefineAux.momentWeight p.w t
  have hv := reference_valid_moment M ε w η Δ D ω r params hp h hh N I hI
  have hv' := hp.reference_valid_at .identical M ε w η Δ D ω r params N I hI
  have hdeg := hp.moment_degree_at .identical M ε w η Δ D ω r params h (by omega)
  change 8 * t ≤ D at hdeg
  have ht : 1 ≤ t := by unfold t IdCov.tDegree; omega
  have hr4 := hp.reference_resilient_at .identical M ε w η Δ D ω r params N I hI 4
    (by omega) (by omega) (by decide)
  have htop : J.sup id ≤ 4 * t := Finset.sup_le hJt
  obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hJe
  have hs0 := hJ s hs
  have hssup : s ≤ J.sup id := Finset.le_sup (f := id) hs
  have hres := hp.reference_resilient_at .identical M ε w η Δ D ω r params N I hI
    (2 * J.sup id) (by omega) (by omega) (even_two_mul _)
  have hc := hp.contamination_at .identical M ε w η Δ D ω r params h (by omega)
    N I hI hl hN
  obtain ⟨hT, _⟩ := hp.frame_population_cov_at .identical M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  have he := hp.close_frame_error_at .identical M ε w η Δ D ω r params h hh
    N I hI hl hN F hF
  have hηc := IdFrame.eta_contamination .identical M ε w η Δ D ω r params hp h hh
  have hp' := hp
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, _, _, _, hready, _⟩ := hp'
  have hstep := hready h hh
  have hγ1 : (p.isotropy : ℝ) ≤ 1 := by
    exact_mod_cast IdFrame.isotropy_le_one .identical k _ _ hstep
  obtain ⟨hw, hw2, _, _, _, _, _, _, _, _, _, _, _, hreq, hζ, hζle, hm⟩ := hstep
  have hγ0 : (0 : ℝ) ≤ p.isotropy := by
    exact_mod_cast (show 0 ≤ (params h).isotropy by linarith only [hζ, hζle])
  obtain ⟨_, _, _, _, _, hmoment, _⟩ := hm
  have hreqw := hreq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have he8 : p.contamination ≤ 1 / 8 := by
    change p.contamination ≤ p.w / 800 at hreqw
    change p.w ≤ 1 / 2 at hw2
    linarith only [hreqw, hw2]
  have hw'1 : (w' : ℝ) ≤ 1 := by
    have hh := (ABBKS26.RefineAux.momentWeight_le p.w t hw.le).trans hw2
    have hhR := Rat.cast_le (K := ℝ) |>.mpr hh
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hhR
    linarith only [hhR]
  have he' : frobSq (T * R.cov * Tᵀ - 1) ≤ (1 / 100 : ℝ) ^ 2 := by
    apply he.trans
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hγ1]
  have hcov := (ABBKS26.RefineAux.empirical_frame_bounds R.cov T
    hv'.2.2.2.2.2.1.posSemidef he').2
  let A := ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))
  have hAv : A.Valid (w' : ℝ) :=
    ABBKS26.RefineAux.affineReference_valid R T _ _ hv hT
  have hAr : A.Resilient (2 * J.sup id) (η / 10 ^ 8) :=
    ABBKS26.RefineAux.affineReference_resilient R T _ _ _ hT hres
  have hobs := ABBKS26.RefineAux.affineReference_observed R x F.transform a
    (fun _ _ ↦ rfl)
  have hfuel : momentFuel n d J ≤ fuel := by
    apply le_trans _ hfu
    unfold momentFuel
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by omega)
    have htop' : (Finset.Icc 1 (4 * IdCov.tDegree (params h).w)).sup id = 4 * t := by
      apply le_antisymm
      · exact Finset.sup_le fun q hq ↦ (Finset.mem_Icc.mp hq).2
      · exact Finset.le_sup (f := id) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    rw [htop']
    gcongr
  have hcert := hMC.adequate A (ABBKS26.RefineAux.affinePoints x F.transform a)
    J w' p.contamination (η / 10 ^ 8) fuel hAv hobs hJ hAr (by positivity)
      (by linarith only [hη100]) hc he8
      (ABBKS26.RefineAux.population_component_mean_bound R T _ w' (η / 10 ^ 8) hv
        hw'1 ⟨by positivity, by linarith only [hη100]⟩ hr4 hcov ha)
      (ABBKS26.RefineAux.population_component_cov_bound R T w' (η / 10 ^ 8) hv
        ⟨by positivity, by linarith only [hη100]⟩ hr4 hcov) hfuel
  dsimp only
  intro q hq
  obtain ⟨hhom, hsos⟩ := hcert q hq
  have hbudget := ABBKS26.RefineAux.identical_moment_budget p η t q hw hw2 ht (hJt q hq)
    ⟨hη.le, hη100⟩ hηc hmoment
  refine ⟨hhom, ?_⟩
  have hmono := SoS.isSumSq_C_mul (sub_nonneg.mpr hbudget)
    (SoS.isSumSq_pow (IsSumSq.sum_sq _ _) q : IsSumSq ((nsq : RPoly d) ^ q))
  change IsSumSq (MvPolynomial.C (p.momentError : ℝ) * nsq ^ q -
    (SoS.toReal (momentProc MC
      (ABBKS26.RefineAux.affinePoints x F.transform a) R.block J w' p.contamination fuel q) -
        Robust.populationMoment
          (ABBKS26.RefineAux.affineReference R T (fun i ↦ (a i : ℝ))).model q) ^ 2)
  convert hmono.add hsos using 1
  dsimp only [A, w', ABBKS26.RefineAux.affineReference]
  simp only [nsq, MvPolynomial.C_sub, sub_mul]
  ring


/-- A single certified even-moment family has precisely the SUB certificate shape. -/
theorem to_certificate {m : ℕ} (S : IdCov.Data m d) (A : FrameModel m d)
    (hframe : S.frame = A) (Q : ℕ → QPoly d) (t : ℕ) (η : ℝ)
    (hc : Robust.Certified A (fun q ↦ SoS.toReal (Q q)) (Finset.Icc 1 (4 * t))
      (fun _ ↦ η)) :
    IdCov.momentCertificate S (fun q ↦ SoS.toReal (Q q)) t η := by
  have hpop (q : ℕ) : Robust.populationMoment S.frame q = IdCov.moment S q := rfl
  rw [hframe] at hpop
  constructor
  · intro s hs hsmax
    exact (hc (2 * s) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).1
  · intro s hs hsmax
    have hq := (hc (2 * s) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)).2
    rwa [hpop] at hq

end

end ABBKS26.Assembly.Exec.RefineSynth.IdMoments
