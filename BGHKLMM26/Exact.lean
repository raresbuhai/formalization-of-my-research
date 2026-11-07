module

public import BGHKLMM26.Algorithm
public import BGHKLMM26.Factor

/-!
# What the algorithm computes exactly

Over `ℚ`, the algorithm computes exactly the quantities of the analysis for the vectors
`v = BGHKLMM26.Factor.sosVec` of the solver's output:

* the coefficients `cₖₗ` and `Dₖ` of `v` (`BGHKLMM26.Alg.coefL_eq`, `BGHKLMM26.Alg.diagL_eq`):
  the positive definiteness test runs on `A` scaled by the common denominator `s` of its entries,
  which multiplies `adj(B) b` and `det B` by `sᵏ` and the Schur complement by `sᵏ⁺¹`;
* `ρ = b ⟨vᵢ, vⱼ⟩`, the window, the SDP values and the branch (`BGHKLMM26.Alg.rhoQ_eq`,
  `BGHKLMM26.Alg.winList_eq`, `BGHKLMM26.Alg.sdpQ_eq`, `BGHKLMM26.Alg.sdpOutQ_eq`).
-/

@[expose] public section

namespace BGHKLMM26.Alg

open Matrix SoS SoS.PDTest Factor
open scoped RealInnerProductSpace

/-! ### Scaling and changing the ring in the positive definiteness test -/

section Scale

variable {k : ℕ}

theorem cof_smul (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (s : ℝ) :
    cof (s • B) = s ^ k • cof B := by
  rcases k with _ | k
  · funext i; exact i.elim0
  · have hlead : lead (s • B) = s • lead B := rfl
    have hcol : SoS.PDTest.col (s • B) = s • SoS.PDTest.col B := rfl
    rw [cof, cof, hlead, hcol, adjugate_smul, Fintype.card_fin, Nat.add_sub_cancel,
      smul_mulVec, mulVec_smul, smul_smul, ← pow_succ]

theorem det_lead_smul (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (s : ℝ) :
    (lead (s • B)).det = s ^ k * (lead B).det := by
  have hlead : lead (s • B) = s • lead B := rfl
  rw [hlead, det_smul, Fintype.card_fin]

theorem schur_smul (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) (s : ℝ) :
    schur (s • B) = s ^ (k + 1) * schur B := by
  have hcol : SoS.PDTest.col (s • B) = s • SoS.PDTest.col B := rfl
  rw [schur, schur, cof_smul, det_lead_smul, hcol, Matrix.smul_apply, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

theorem cof_map (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) (l : Fin k) :
    ((cof B l : ℤ) : ℝ) = cof (B.map (Int.castRingHom ℝ)) l := by
  have hadj : ((lead B).map (Int.castRingHom ℝ)).adjugate =
      (lead B).adjugate.map (Int.castRingHom ℝ) :=
    (RingHom.map_adjugate (Int.castRingHom ℝ) (lead B)).symm
  have hlead : lead (B.map (Int.castRingHom ℝ)) = (lead B).map (Int.castRingHom ℝ) := rfl
  have hcol : SoS.PDTest.col (B.map (Int.castRingHom ℝ)) =
      (Int.castRingHom ℝ) ∘ SoS.PDTest.col B := rfl
  simp only [cof, hlead, hcol, hadj, mulVec, dotProduct, map_apply, Function.comp_apply]
  push_cast
  rfl

theorem det_lead_map (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) :
    (((lead B).det : ℤ) : ℝ) = (lead (B.map (Int.castRingHom ℝ))).det := by
  have hlead : lead (B.map (Int.castRingHom ℝ)) = (lead B).map (Int.castRingHom ℝ) := rfl
  rw [hlead]
  exact RingHom.map_det (Int.castRingHom ℝ) (lead B)

theorem schur_map (B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ) :
    ((schur B : ℤ) : ℝ) = schur (B.map (Int.castRingHom ℝ)) := by
  rw [schur, schur, ← det_lead_map]
  simp only [dotProduct, ← cof_map]
  push_cast
  rfl

end Scale

/-! ### The moments and their scaled rows -/

section Rows

variable (Q₀ : ℕ) (I : Instance)

/-- The matrix of the analysis for the algorithm's solver output. -/
noncomputable abbrev aMat : Matrix (Fin I.1) (Fin I.1) ℝ :=
  sosMat I (solverOut Q₀ I) (tauS Q₀ I)

/-- The vectors of the analysis for the algorithm's solver output. -/
noncomputable abbrev vAlg : ℕ → EuclideanSpace ℝ (Fin I.1) :=
  sosVec I (solverOut Q₀ I) (tauS Q₀ I)

theorem length_zRows : (zRows Q₀ I).length = I.1 := by
  simp [zRows, PDTestRat.scale, rowsQ]

theorem entry_rowsQ {i j : ℕ} (hi : i < I.1) (hj : j < I.1) :
    PDTestRat.entry (rowsQ Q₀ I) i j = aQ Q₀ I i j := by
  simp [PDTestRat.entry, rowsQ, List.getD_eq_getElem?_getD, hi, hj]

theorem rowEntry_zRows {i j : ℕ} (hi : i < I.1) (hj : j < I.1) :
    ((Cslib.rowEntry (zRows Q₀ I) i j : ℤ) : ℝ) =
      (PDTestRat.commonDen (rowsQ Q₀ I) : ℝ) * aQ Q₀ I i j := by
  have h := PDTestRat.rowEntry_scale (rowsQ Q₀ I) i j
  rw [entry_rowsQ Q₀ I hi hj] at h
  have h' := congrArg (fun q : ℚ ↦ (q : ℝ)) h
  simp only [Rat.cast_intCast, Rat.cast_mul] at h'
  exact h'

theorem leadBlock_zRows {k : ℕ} (hk : k < I.1) :
    (leadBlock (Cslib.Circuits.Rational.ofRows (zRows Q₀ I))
        ⟨k, (length_zRows Q₀ I).symm ▸ hk⟩).map (Int.castRingHom ℝ) =
      (PDTestRat.commonDen (rowsQ Q₀ I) : ℝ) • leadBlock (aMat Q₀ I) ⟨k, hk⟩ := by
  ext i j
  have hi : (i : ℕ) < I.1 := lt_of_lt_of_le i.2 hk
  have hj : (j : ℕ) < I.1 := lt_of_lt_of_le j.2 hk
  simp only [map_apply, leadBlock, submatrix_apply,
    Cslib.Circuits.Rational.ofRows, of_apply, Fin.val_castLE, eq_intCast]
  rw [rowEntry_zRows Q₀ I hi hj, Matrix.smul_apply, smul_eq_mul]
  rfl

theorem commonDen_ne_zero : (PDTestRat.commonDen (rowsQ Q₀ I) : ℝ) ≠ 0 := by
  have := PDTestRat.commonDen_pos (rowsQ Q₀ I)
  positivity

/-- **The coefficients `cₖₗ` are exact.** -/
theorem coefL_eq {k l : ℕ} (hk : k < I.1) (hl : l < k) :
    (((coefL Q₀ I k).getD l 0 : ℚ) : ℝ) = coef (aMat Q₀ I) k l := by
  have hkZ : k < (zRows Q₀ I).length := (length_zRows Q₀ I).symm ▸ hk
  set s : ℝ := ((PDTestRat.commonDen (rowsQ Q₀ I) : ℤ) : ℝ)
  set BZ := leadBlock (Cslib.Circuits.Rational.ofRows (zRows Q₀ I)) ⟨k, hkZ⟩
  set BA := leadBlock (aMat Q₀ I) ⟨k, hk⟩
  have hmap : BZ.map (Int.castRingHom ℝ) = s • BA := leadBlock_zRows Q₀ I hk
  have hcof : (((PDTestRows.cof (zRows Q₀ I) k).getD l 0 : ℤ) : ℝ) = s ^ k * cof BA ⟨l, hl⟩ := by
    have h1 : (PDTestRows.cof (zRows Q₀ I) k).getD l 0 =
        Cslib.Circuits.Rational.detRows (PDTestRows.cramerBlock (zRows Q₀ I) k l) := by
      simp [PDTestRows.cof, List.getD_eq_getElem?_getD, hl]
    rw [h1, ← PDTestRows.cof_leadBlock (zRows Q₀ I) ⟨k, hkZ⟩ ⟨l, hl⟩, cof_map, hmap, cof_smul]
    rfl
  have hdet : ((detB Q₀ I k : ℤ) : ℝ) = s ^ k * (lead BA).det := by
    rw [detB, ← PDTestRows.det_lead_leadBlock (zRows Q₀ I) ⟨k, hkZ⟩, det_lead_map, hmap,
      det_lead_smul]
  have hget : (coefL Q₀ I k).getD l 0 =
      (((PDTestRows.cof (zRows Q₀ I) k).getD l 0 : ℤ) : ℚ) / detB Q₀ I k := by
    unfold coefL
    exact PDTestRat.getD_map_of_eq _ _ _ (d' := 0) (by simp)
  rw [hget, coef, dite_eq_left ⟨hk, hl⟩]
  push_cast
  rw [hcof, hdet, mul_div_mul_left _ _ (pow_ne_zero _ (commonDen_ne_zero Q₀ I))]

/-- **The diagonal `Dₖ` is exact.** -/
theorem diagL_eq {k : ℕ} (hk : k < I.1) : ((diagL Q₀ I k : ℚ) : ℝ) = diagD (aMat Q₀ I) k := by
  have hkZ : k < (zRows Q₀ I).length := (length_zRows Q₀ I).symm ▸ hk
  set s : ℝ := ((PDTestRat.commonDen (rowsQ Q₀ I) : ℤ) : ℝ)
  set BZ := leadBlock (Cslib.Circuits.Rational.ofRows (zRows Q₀ I)) ⟨k, hkZ⟩
  set BA := leadBlock (aMat Q₀ I) ⟨k, hk⟩
  have hmap : BZ.map (Int.castRingHom ℝ) = s • BA := leadBlock_zRows Q₀ I hk
  have hschur : ((PDTestRows.schur (zRows Q₀ I) k : ℤ) : ℝ) = s ^ (k + 1) * schur BA := by
    rw [PDTestRows.schur_eq (zRows Q₀ I) ⟨k, hkZ⟩, schur_map, hmap, schur_smul]
  have hdet : ((detB Q₀ I k : ℤ) : ℝ) = s ^ k * (lead BA).det := by
    rw [detB, ← PDTestRows.det_lead_leadBlock (zRows Q₀ I) ⟨k, hkZ⟩, det_lead_map, hmap,
      det_lead_smul]
  have hs := commonDen_ne_zero Q₀ I
  rw [diagL, diagD, dite_eq_left hk]
  push_cast
  rw [hschur, hdet, show s ^ k * (lead BA).det * s = s ^ (k + 1) * (lead BA).det by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ hs)]

end Rows

/-! ### The solver's output and the window -/

section Window

open SDP

variable {Q₀ : ℕ} {I : Instance}

theorem wTot_cast (I : Instance) : ((wTot I : ℚ) : ℝ) = totalWeight I := by
  rw [wTot, totalWeight, Rat.cast_list_sum, List.map_map]
  rfl

theorem wTot_nonneg (hI : Valid I) : 0 ≤ wTot I :=
  List.sum_nonneg fun a ha ↦ by
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
    exact (hI.1 c hc).2.2

theorem etaS_pos : 0 < etaS Q₀ I := by unfold etaS; positivity

theorem tauS_pos : 0 < tauS Q₀ I := by unfold tauS; positivity

theorem gammaS_pos (hI : Valid I) : 0 < gammaS Q₀ I := by
  unfold gammaS
  split_ifs with h
  · positivity
  · have : 0 < wTot I := lt_of_le_of_ne (wTot_nonneg hI) (Ne.symm h)
    have : 0 < min (wTot I) 1 := lt_min this one_pos
    positivity

theorem gammaS_le : gammaS Q₀ I ≤ 1 / 2 ^ qPar Q₀ I := by
  unfold gammaS
  have h2 : (0 : ℚ) < 2 ^ qPar Q₀ I := by positivity
  split_ifs
  · exact le_rfl
  · exact div_le_div_of_nonneg_right (min_le_right _ _) h2.le

theorem two_pow_qPar_ge (hQ : 10 ≤ Q₀) : (4096 : ℚ) ≤ 2 ^ qPar Q₀ I :=
  calc (4096 : ℚ) = 2 ^ 12 := by norm_num
    _ ≤ 2 ^ qPar Q₀ I := pow_le_pow_right₀ (by norm_num) (by unfold qPar zPar; omega)

theorem etaS_add_gammaS_le (hQ : 10 ≤ Q₀) : etaS Q₀ I + gammaS Q₀ I ≤ 1 / 1000 := by
  have h := two_pow_qPar_ge (I := I) hQ
  have hg := gammaS_le (Q₀ := Q₀) (I := I)
  have : etaS Q₀ I + gammaS Q₀ I ≤ 2 / 2 ^ qPar Q₀ I := by
    unfold etaS; rw [show (2 : ℚ) / 2 ^ qPar Q₀ I = 1 / 2 ^ qPar Q₀ I + 1 / 2 ^ qPar Q₀ I by ring]
    linarith
  refine this.trans ?_
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

theorem tauS_le (hQ : 10 ≤ Q₀) : tauS Q₀ I ≤ 1 / 1000 := by
  have h := two_pow_qPar_ge (I := I) hQ
  unfold tauS
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- The solver's output is correct. -/
theorem solver_correct (hI : Valid I) :
    SoS.Solver.Correct (problem I) (etaS Q₀ I) (gammaS Q₀ I) (solverOut Q₀ I) :=
  SoS.Correct.core_correct _ (problem_valid I) _ _ etaS_pos (gammaS_pos hI)

/-- The properties of the vectors of the analysis. -/
theorem vAlg_spec (hI : Valid I) (hQ : 10 ≤ Q₀) :
    (∀ i < I.1, ‖vAlg Q₀ I i‖ = 1) ∧
    (∀ i j, i < I.1 → j < I.1 → ⟪vAlg Q₀ I i, vAlg Q₀ I j⟫ = aQ Q₀ I i j) ∧
    Triangle (vAlg Q₀ I) I.1 (1 / 20) ∧
    opt I - gammaS Q₀ I - (2 * ((etaS Q₀ I : ℝ) + gammaS Q₀ I) + tauS Q₀ I) * totalWeight I ≤
      sdp (vAlg Q₀ I) I :=
  sosVec_spec hI etaS_pos (gammaS_pos hI) tauS_pos (etaS_add_gammaS_le hQ) (tauS_le hQ)
    (solver_correct hI)

theorem rhoQ_eq (hI : Valid I) (hQ : 10 ≤ Q₀) {c : Constraint} (hc : c ∈ I.2) :
    (rhoQ Q₀ I c : ℝ) = rho (vAlg Q₀ I) c.1.1 c.1.2 c.2.1 := by
  obtain ⟨hij, hj, -⟩ := hI.1 c hc
  rw [rhoQ, rho, (vAlg_spec hI hQ).2.1 _ _ (hij.trans hj) hj]
  push_cast
  rw [bsignQ_cast]

theorem inWin_iff (hI : Valid I) (hQ : 10 ≤ Q₀) {c : Constraint} (hc : c ∈ I.2) :
    inWin Q₀ I c = true ↔ window (vAlg Q₀ I) c := by
  have e1 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by push_cast; ring
  have e2 : ((4 / 5 : ℚ) : ℝ) = 4 / 5 := by push_cast; ring
  rw [inWin, window, ← rhoQ_eq hI hQ hc, decide_eq_true_iff, ← e1, ← e2, Rat.cast_lt, Rat.cast_lt]

/-- **The window is exact.** -/
theorem winList_eq (hI : Valid I) (hQ : 10 ≤ Q₀) : winList Q₀ I = windowSet (vAlg Q₀ I) I := by
  classical
  rw [winList, windowSet]
  refine List.filter_congr fun c hc ↦ ?_
  rw [Bool.eq_iff_iff, inWin_iff hI hQ hc, decide_eq_true_iff]

theorem sdpQ_eq (hI : Valid I) (hQ : 10 ≤ Q₀) : (sdpQ Q₀ I : ℝ) = sdp (vAlg Q₀ I) I := by
  rw [sdpQ, sdp, Rat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  simp only [Function.comp_apply, sdpTerm]
  push_cast
  rw [rhoQ_eq hI hQ hc]

theorem sdpOutQ_eq (hI : Valid I) (hQ : 10 ≤ Q₀) : (sdpOutQ Q₀ I : ℝ) = sdpOut (vAlg Q₀ I) I := by
  classical
  rw [sdpOutQ, sdpOut, Rat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc ↦ ?_
  simp only [Function.comp_apply]
  by_cases h : window (vAlg Q₀ I) c
  · rw [ite_eq_left ((inWin_iff hI hQ hc).2 h), ite_eq_left h, Rat.cast_zero]
  · rw [ite_eq_right (fun h' ↦ h ((inWin_iff hI hQ hc).1 h')), ite_eq_right h, sdpTerm]
    push_cast
    rw [rhoQ_eq hI hQ hc]

/-- **The branch is exact.** -/
theorem branch0_iff (hI : Valid I) (hQ : 10 ≤ Q₀) :
    branch0 Q₀ I = true ↔ (epsQ I : ℝ) * sdp (vAlg Q₀ I) I ≤ sdpOut (vAlg Q₀ I) I := by
  rw [branch0, decide_eq_true_iff, ← sdpQ_eq hI hQ, ← sdpOutQ_eq hI hQ, ← Rat.cast_mul,
    Rat.cast_le]

end Window

end BGHKLMM26.Alg
