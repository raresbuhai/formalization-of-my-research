module

public import ABBKS26.Assembly.ExecFrameLoop

/-! The CLOSE branch controls each centered component in the exported rational frame. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.FrameAux.Component

open Common Matrix _root_.ABBKS26.Tree
open scoped BigOperators

noncomputable section

variable {n k d : ℕ}

/-- The component part of CLOSE, at the level reserved by the centered schedule. -/
def Bound (run : Robust.FrameProc) : Prop :=
  ∀ {n k d} (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (ps : ℕ → StepParams),
    Prepared .centered M ε w η Δ D ω r ps →
    ∀ h, h < k - 1 → ∀ fuel, localBudget .centered k n d ps ≤ fuel →
    ∀ (P : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty),
    leakage ω P I ≤ leakageBudget ps η h → w * n / 4 ≤ P.card →
    let p := ps h
    let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
    let pts := (P.sort (· ≤ ·)).map fun l ↦ List.ofFn fun i ↦ r ((ω l).1, (ω l).2.2) i
    let Y := run d pts .centered (p.w / 2) |p.R| p.frameAccuracy fuel
    ¬ Robust.Far ref Y (|p.R| : ℚ) (20 / (((p.w / 2 : ℚ) : ℝ))) →
    ∀ j, frobSq ((ABBKS26.RefineAux.affineReference ref
      (Y.transform.map (algebraMap ℚ ℝ)) 0).model.cov j - 1) ≤
        ((10000 * p.sigmaSq / (p.w / 2) + 10 : ℚ) : ℝ)

private theorem diagonal_contraction (r : Vec d) (A : Mat d)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 1) :
    frobSq (diagonal r * A * diagonal r) ≤ frobSq A := by
  unfold frobSq
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  rw [mul_diagonal, diagonal_mul]
  have hi : r i ^ 2 ≤ 1 := by nlinarith only [(hr i).1, (hr i).2]
  have hj : r j ^ 2 ≤ 1 := by nlinarith only [(hr j).1, (hr j).2]
  calc
    _ = r i ^ 2 * r j ^ 2 * A i j ^ 2 := by ring
    _ ≤ 1 * 1 * A i j ^ 2 := by gcongr
    _ = _ := by ring

/-- The final diagonal normalization contracts pairwise Frobenius distances. -/
theorem normalizedL_pairwise (D : Robust.Reference n k d)
    (st : Robust.FilterState n d) (π R : ℝ) (C : MatrixL) (ζ : ℚ)
    (hC : ((matrixOf d C).map (algebraMap ℚ ℝ)).PosDef)
    (hframe : st.frame = (Linear.whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ))
    (hi : Robust.IterationInvariant D st π) (hf : Robust.FrameNormalized D st)
    (he : D.contamination ≤ min (Robust.maxContamination π R) (π / 400))
    (hp : Robust.Pass st π R) (hcen : ∀ j, D.model.mean j = 0) (i j : Fin k) :
    let T := (matrixOf d (Linear.normalizedL d C ζ)).map (algebraMap ℚ ℝ)
    frobSq (T * D.model.cov i * Tᵀ - T * D.model.cov j * Tᵀ) ≤
      1000 * Robust.sigmaSq π R / π := by
  let L := (Linear.whitenMat (matrixOf d C)).map (algebraMap ℚ ℝ)
  let q := Linear.whitenDiag (matrixOf d C)
  let s := fun i ↦ (invSqrt (normalizePrecision d ζ) (q i) : ℝ)
  have hs (i : Fin d) : 0 ≤ s i ∧ s i ≤ 1 := by
    have hq := Linear.whitenDiag_spec (matrixOf d C) hC i
    dsimp only [s, q]
    exact ⟨by exact_mod_cast (invSqrt_spec (normalizePrecision d ζ) hq).1.le,
      by exact_mod_cast invSqrt_le_one (normalizePrecision d ζ) hq.1⟩
  have hc := diagonal_contraction s
    (L * D.model.cov i * Lᵀ - L * D.model.cov j * Lᵀ) hs
  have hb := ABBKS26.RefineAux.centered_pass_pairwise D st π R hi hf he hp hcen i j
  rw [hframe] at hb
  dsimp only
  rw [Linear.matrixOf_normalizedL_real]
  have heq :
      (diagonal s * L) * D.model.cov i * (diagonal s * L)ᵀ -
        (diagonal s * L) * D.model.cov j * (diagonal s * L)ᵀ =
      diagonal s * (L * D.model.cov i * Lᵀ - L * D.model.cov j * Lᵀ) *
        diagonal s := by
    simp only [transpose_mul, diagonal_transpose, mul_sub, sub_mul, mul_assoc]
  change frobSq ((diagonal s * L) * _ * (diagonal s * L)ᵀ -
    (diagonal s * L) * _ * (diagonal s * L)ᵀ) ≤ _
  rw [heq, le_div_iff₀ hi.1.1.1]
  have hh := mul_le_mul_of_nonneg_left hc hi.1.1.1.le
  have hσ : 0 ≤ Robust.sigmaSq π R := by unfold Robust.sigmaSq; positivity
  dsimp only [L] at hh
  nlinarith only [hh, hb, hσ]

/-- Population resilience and CLOSE accuracy turn pairwise control into component control. -/
theorem prepared_bound (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (ps : ℕ → StepParams)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (h : ℕ) (hh : h < k - 1)
    (P : Finset (Fin n)) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (Y : Robust.FrameResult d)
    (hc : Robust.CloseFrame (ABBKS26.RefineAux.roundedReference M ω r P I hI) Y
      ((ps h).w / 2 : ℚ) (|(ps h).R| : ℚ) (((ps h).isotropy / 10000 : ℚ) : ℝ))
    (hpair : ∀ i j,
      let T := Y.transform.map (algebraMap ℚ ℝ)
      let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
      frobSq (T * ref.model.cov i * Tᵀ - T * ref.model.cov j * Tᵀ) ≤
        1000 * ((ps h).sigmaSq : ℝ) / (((ps h).w / 2 : ℚ) : ℝ)) :
    ∀ j, frobSq ((ABBKS26.RefineAux.affineReference
      (ABBKS26.RefineAux.roundedReference M ω r P I hI)
      (Y.transform.map (algebraMap ℚ ℝ)) 0).model.cov j - 1) ≤
        ((10000 * (ps h).sigmaSq / ((ps h).w / 2) + 10 : ℚ) : ℝ) := by
  let p := ps h
  let ref := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let T := Y.transform.map (algebraMap ℚ ℝ)
  let A := ABBKS26.RefineAux.affineReference ref T 0
  let π : ℝ := ((p.w / 2 : ℚ) : ℝ)
  obtain ⟨hT, _⟩ := hp.frame_population_cov_at .centered M ε w η Δ D ω r ps h hh
    P I hI hl hP Y hc
  have hv := (hp.centered_reference_compatible_at M ε w η Δ D ω r ps
    h hh P I hI hl hP).1.1
  have hAv : A.Valid π := ABBKS26.RefineAux.affineReference_valid ref T 0 _ hv hT
  have hiso := hp.centered_isotropic_at M ε w η Δ D ω r ps h hh P I hI hl hP Y hc
  have hAcen : ∀ j, A.model.mean j = 0 := by
    intro j
    change T *ᵥ (M.μ (ABBKS26.RefineAux.component I j) - 0) = 0
    rw [hp.2.1 _, sub_self, mulVec_zero]
  have hAr : A.Resilient 4 (η / 10 ^ 8) :=
    ABBKS26.RefineAux.affineReference_resilient ref T 0 _ _ hT
      (hp.reference_resilient_at .centered M ε w η Δ D ω r ps P I hI 4
        (by omega) ((by omega : 4 ≤ 8).trans
          (hp.eight_le_degree .centered M ε w η Δ D ω r ps)) (by decide))
  have herr := hp.close_frame_error_at .centered M ε w η Δ D ω r ps h hh
    P I hI hl hP Y hc
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, _, _, _, hready, _⟩ := hp
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, hσ, _, _, _, hm⟩ := hready h hh
  obtain ⟨_, _, _, _, _, _, _, _, hγeq, _⟩ := hm
  have hγsmall : p.isotropy ≤ (p.w / 2) / 20 := by
    rw [hγeq]
    exact ABBKS26.RefineAux.centered_gamma_le (p.w / 2) p.subspaceAccuracy
      ⟨by positivity, by linarith only [hw2]⟩ ⟨hβ, by linarith only [hβ100]⟩
  have hγ : (p.isotropy : ℝ) ≤ 1 / 10 := by
    have hh : p.isotropy ≤ 1 / 10 := by linarith only [hγsmall, hw2]
    have hb := Rat.cast_le (K := ℝ) |>.mpr hh
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hb
    exact hb
  have hσpos : (0 : ℝ) < p.sigmaSq := by
    have hσ1 := ABBKS26.RefineAux.sigmaSq_one_le p hw hw2 hσ
    exact_mod_cast (lt_of_lt_of_le zero_lt_one hσ1)
  have hB : 0 ≤ 1000 * (p.sigmaSq : ℝ) / π := by
    exact div_nonneg (by positivity) hv.1.1.le
  have hAe : frobSq (A.cov - 1) ≤ (1 / 100 : ℝ) ^ 2 := by
    rw [ABBKS26.RefineAux.affineReference_cov ref T 0 hv.2.2.2.2.1]
    apply herr.trans
    apply pow_le_pow_left₀ (div_nonneg hiso.1 (by norm_num))
    linarith only [hγ]
  intro i
  have hb := ABBKS26.RefineAux.centered_component_frob A π (η / 10 ^ 8)
    p.isotropy (1000 * (p.sigmaSq : ℝ) / π) (1 / 100) hAv hAcen
    ⟨by positivity, by linarith only [hη100]⟩ hAr hiso (by linarith only [hγ])
    hB (by norm_num) hAe hpair i
  have hθ : (10 * (η / 10 ^ 8) + 1 / 100) ^ 2 ≤ 1 := by
    have he0 : 0 ≤ 10 * (η / 10 ^ 8) + 1 / 100 := by positivity
    exact pow_le_one₀ he0 (by linarith only [hη100])
  change frobSq (A.model.cov i - 1) ≤
    ((10000 * p.sigmaSq / (p.w / 2) + 10 : ℚ) : ℝ)
  push_cast
  rw [← show π = (p.w : ℝ) / 2 by
    simp only [π, Rat.cast_div, Rat.cast_ofNat]]
  rw [show 10000 * (p.sigmaSq : ℝ) / π =
    10 * (1000 * (p.sigmaSq : ℝ) / π) by ring]
  linarith only [hb, hθ, hB]

end

end ABBKS26.Assembly.Exec.FrameAux.Component
