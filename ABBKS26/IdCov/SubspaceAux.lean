module

public import ABBKS26.IdCov.RoundCond
public import ABBKS26.IdCov.Norms

/-! Parameter estimates and certificates used by the identical-covariance subspace step. -/

@[expose] public section

namespace ABBKS26.IdCov.SubspaceAux

noncomputable section

open Common MvPolynomial Matrix

variable {k d : ℕ}

theorem radius_bound (β : ℚ) (hβ : 0 < β) :
    25 * (epsilonR β : ℝ) ^ (1 / 8 : ℝ) ≤ β := by
  have hb : (0 : ℝ) ≤ (β : ℝ) / 25 := by positivity
  have he : (epsilonR β : ℝ) = ((β : ℝ) / 25) ^ 8 := by
    simp only [epsilonR, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
  have hr : (((β : ℝ) / 25) ^ 8) ^ (1 / 8 : ℝ) = (β : ℝ) / 25 := by
    simpa only [Nat.cast_ofNat, one_div] using
      Real.pow_rpow_inv_natCast hb (by norm_num : 8 ≠ 0)
  rw [he, hr]
  linarith

theorem identities (w β : ℚ) (hβ : 0 < β) :
    cStar β / tauStar β = epsilonR β ∧
      2 * gammaStar β + tauStar β + tauStar β = epsilonR β ∧
      2 * epsilonSys w β + 2 * etaStar w β *
        (8 * tDegree w : ℚ) ^ (4 * tDegree w + 2) = epsilonId w β := by
  have he : epsilonR β ≠ 0 := by unfold epsilonR; positivity
  have ht : (0 : ℚ) < tDegree w := by
    exact_mod_cast (show 0 < tDegree w by unfold tDegree; omega)
  refine ⟨?_, ?_, ?_⟩
  · dsimp [cStar, tauStar]
    field_simp
  · dsimp [gammaStar, tauStar]
    ring
  · dsimp [etaStar, epsilonSys]
    field_simp
    ring

structure Bounds (w β : ℚ) : Prop where
  degree : 3 ≤ tDegree w
  rounding : 0 < epsilonR β ∧ epsilonR β ≤ 1
  energy : 0 < cStar β ∧ cStar β ≤ 1
  exact : 0 < epsilonId w β ∧ epsilonId w β ≤ 1
  system : 0 < epsilonSys w β ∧ epsilonSys w β ≤ 1 / 4
  error : 0 < etaStar w β ∧ etaStar w β ≤ 1 / 4
  small : (gammaStar β : ℝ) + Real.sqrt (etaStar w β) ≤ 1

theorem bounds (w β : ℚ) (hβ : 0 < β ∧ β ≤ 1 / 4) : Bounds w β := by
  have hβ0 := hβ.1
  have ht : (3 : ℚ) ≤ tDegree w := by
    exact_mod_cast (show 3 ≤ tDegree w by unfold tDegree; omega)
  have he : 0 < epsilonR β ∧ epsilonR β ≤ 1 := by
    refine ⟨by unfold epsilonR; positivity, ?_⟩
    exact pow_le_one₀ (by positivity : 0 ≤ β / 25) (by linarith : β / 25 ≤ 1)
  have hc : 0 < cStar β ∧ cStar β ≤ 1 := by
    dsimp [cStar]
    have := pow_le_one₀ he.1.le he.2 (n := 2)
    constructor
    · exact div_pos (pow_pos he.1 _) (by norm_num)
    · linarith
  have hc0 := hc.1
  have hid : 0 < epsilonId w β ∧ epsilonId w β ≤ 1 := by
    refine ⟨by unfold epsilonId; positivity, ?_⟩
    exact pow_le_one₀ (by positivity)
      ((div_le_one (by positivity)).mpr (by linarith))
  have hs : 0 < epsilonSys w β ∧ epsilonSys w β ≤ 1 / 4 := by
    dsimp [epsilonSys]
    constructor <;> linarith [hid.1, hid.2]
  have hs0 := hs.1
  have hg : (1 : ℚ) ≤ (8 * tDegree w : ℚ) ^ (4 * tDegree w + 2) :=
    one_le_pow₀ (by linarith)
  have heta : 0 < etaStar w β ∧ etaStar w β ≤ 1 / 4 := by
    refine ⟨by unfold etaStar; positivity, ?_⟩
    exact (div_le_self hs.1.le hg).trans hs.2
  refine ⟨by unfold tDegree; omega, he, hc, hid, hs, heta, ?_⟩
  have hetaR : (etaStar w β : ℝ) ≤ 1 / 4 := by
    have h := Rat.cast_le (K := ℝ) |>.mpr heta.2
    norm_num at h ⊢
    exact h
  have her : (epsilonR β : ℝ) ≤ 1 := by exact_mod_cast he.2
  have hsqrt : Real.sqrt (etaStar w β) ≤ 1 / 2 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num at *; linarith)
  have hgamma : (gammaStar β : ℝ) = (epsilonR β : ℝ) / 6 := by
    simp only [gammaStar, Rat.cast_div, Rat.cast_ofNat]
  linarith

theorem rounded_certificate (D : Data k d) (M : ℕ → QPoly d) (w β : ℚ)
    (hβ : 0 < β ∧ β ≤ 1 / 4)
    (hM : momentCertificate D (fun r ↦ SoS.toReal (M r)) (tDegree w)
      (etaStar w β / 4)) :
    momentCertificate D
      (fun r ↦ SoS.toReal (roundPoly (robustPrecision d w β) (M r)))
      (tDegree w) (etaStar w β) := by
  have hb := bounds w β hβ
  have heta : (0 : ℝ) < etaStar w β := by exact_mod_cast hb.error.1
  have heta1 : (etaStar w β : ℝ) ≤ 1 := by
    exact_mod_cast (hb.error.2.trans (by norm_num : (1 / 4 : ℚ) ≤ 1))
  have hpow : (d + 1 : ℝ) ^ (4 * tDegree w) / (etaStar w β : ℝ) ≤
      (2 : ℝ) ^ Nat.clog 2 ⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊ := by
    have hn : (⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊ : ℚ) ≤
        (2 : ℚ) ^ Nat.clog 2 ⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊ := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2)
        (⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊)
    have hq := (Nat.le_ceil ((d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β)).trans hn
    exact_mod_cast hq
  have hsqrt : (etaStar w β : ℝ) / 2 ≤ Real.sqrt ((etaStar w β : ℝ) / 4) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    nlinarith
  have hp : (d + 1 : ℝ) ^ (4 * tDegree w) /
      Real.sqrt ((etaStar w β : ℝ) / 4) ≤ (2 : ℝ) ^ robustPrecision d w β := by
    calc _ ≤ (d + 1 : ℝ) ^ (4 * tDegree w) / ((etaStar w β : ℝ) / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
      _ = 2 * ((d + 1 : ℝ) ^ (4 * tDegree w) / (etaStar w β : ℝ)) := by ring
      _ ≤ 2 * (2 : ℝ) ^ Nat.clog 2
          ⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊ := by gcongr
      _ ≤ _ := by
          rw [robustPrecision, pow_add]
          nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2)
            (Nat.clog 2 ⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊)]
  simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using
    rounding D M (tDegree w) (robustPrecision d w β) (etaStar w β / 4)
      (by positivity) hM hp

theorem exact_tolerance (w β : ℚ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hβ : 0 < β ∧ β ≤ 1 / 4) : (epsilonId w β : ℝ) ≤ ((w : ℝ) / 2) ^ 2 := by
  have hb := bounds w β hβ
  have ht : (3 : ℝ) ≤ tDegree w := by exact_mod_cast hb.degree
  have hc : (cStar β : ℝ) ≤ 1 := by exact_mod_cast hb.energy.2
  have hc0 : (0 : ℝ) < cStar β := by exact_mod_cast hb.energy.1
  have hbase : (cStar β : ℝ) / (64 * tDegree w) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hpow : (1 / 2 : ℝ) ^ tDegree w ≤ (w : ℝ) / 2 := by
    have hp := (degree_bounds w hw).1
    have hcancel : (1 / 2 : ℝ) ^ tDegree w * 2 ^ tDegree w = 1 := by
      rw [← mul_pow]
      norm_num
    have hprev : (2 : ℝ) ^ (tDegree w - 1) ≤ 2 ^ tDegree w :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    apply (mul_le_mul_iff_left₀ (by positivity : (0 : ℝ) < 2 ^ (tDegree w - 1))).mp
    have hl : (1 / 2 : ℝ) ^ tDegree w * 2 ^ (tDegree w - 1) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hprev (by positivity)).trans_eq hcancel
    exact hl.trans ((by norm_num : (1 : ℝ) ≤ 2).trans hp)
  calc
    (epsilonId w β : ℝ) =
        ((cStar β : ℝ) / (64 * tDegree w)) ^ (4 * tDegree w) := by
      simp only [epsilonId, Rat.cast_pow, Rat.cast_div, Rat.cast_mul,
        Rat.cast_ofNat, Rat.cast_natCast]
    _ ≤ (1 / 2 : ℝ) ^ (4 * tDegree w) := pow_le_pow_left₀ (by positivity) hbase _
    _ ≤ (1 / 2 : ℝ) ^ (2 * tDegree w) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = ((1 / 2 : ℝ) ^ tDegree w) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ ((w : ℝ) / 2) ^ 2 := pow_le_pow_left₀ (by positivity) hpow _

theorem system_valid (D : Data k d) (M : ℕ → RPoly d) (t : ℕ) (η ε : ℝ)
    (ht : 1 ≤ t) (hM : momentCertificate D M t η) :
    (Rounding.plainSystem (system M t ε)).Valid (8 * t) := by
  classical
  refine ⟨by simp [Rounding.plainSystem, system], ?_, by simp [Rounding.plainSystem]⟩
  intro f hf
  change f ∈ system M t ε at hf
  simp only [system, List.mem_append, List.mem_singleton, List.mem_filter,
    List.mem_map, List.mem_range] at hf
  rcases hf with rfl | ⟨⟨j, hj, rfl⟩, _⟩
  · exact (totalDegree_sub _ _).trans
      (max_le (by simp) (IdentAux.nsq_degree.trans (by omega)))
  · have hs : j + 2 ≤ 2 * t := by omega
    exact (ApproxAux.constraint_homogeneous M ε (j + 2)
      (hM.1 1 (by omega) (by omega)) (hM.1 _ (by omega) hs)).totalDegree_le.trans
      (by omega)

theorem system_length (M : ℕ → RPoly d) (t : ℕ) (ε : ℝ) :
    (system M t ε).length ≤ 2 * t + 1 := by
  unfold system
  have := List.length_filter_le
    (fun p : RPoly d ↦ decide (p ≠ 0))
    ((List.range (2 * t - 1)).map (fun j ↦ constraint M ε (j + 2)))
  simp only [List.length_append, List.length_singleton, List.length_map,
    List.length_range] at *
  omega

def roundedMoments (d : ℕ) (w β : ℚ) (M : ℕ → QPoly d) : ℕ → RPoly d :=
  fun r ↦ SoS.toReal (roundPoly (robustPrecision d w β) (M r))

def identBound (d : ℕ) (w β : ℚ) : ℝ :=
  (sizeParameter d w β ^ 2) ^ (29 * tDegree w) *
    (1 + (2 * tDegree w + 1 : ℕ) * sizeParameter d w β ^ (16 * tDegree w + 1))

def projectionBound (d : ℕ) (w β : ℚ) : ℝ :=
  max 1 ((identBound d w β + (2 + (tauStar β : ℝ)) * (d : ℝ) ^ 2) / tauStar β)

theorem mean_ident (D : Data k d) (M : ℕ → QPoly d) (w β : ℚ) (γ : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hβ : 0 < β ∧ β ≤ 1 / 4)
    (hD : D.Valid (w / 2) γ) (hγ : γ ≤ gammaStar β)
    (hM : momentCertificate D (fun r ↦ SoS.toReal (M r)) (tDegree w)
      (etaStar w β / 4)) :
    SoS.DerivesNq (system (roundedMoments d w β M) (tDegree w) (epsilonSys w β))
      (8 * tDegree w) (identBound d w β) 1 (C (cStar β : ℝ) - Q D) := by
  let t := tDegree w
  let W := sizeParameter d w β
  have hb := bounds w β hβ
  have hdegree := hb.degree
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hw' : NormLedger D (roundedMoments d w β M) t (w / 2) (epsilonSys w β) W :=
    norm_ledger D M w β γ hw hβ hD hγ hM
  have hW2 : 2 ≤ W := by
    have h := (IdentAux.size_bounds ht hw'.1).1
    linarith
  have hWW : W ≤ W ^ 2 := le_self_pow₀ (by linarith) (by norm_num)
  have he0 : (0 : ℝ) < epsilonId w β := by exact_mod_cast hb.exact.1
  have hs0 : (0 : ℝ) < epsilonSys w β := by exact_mod_cast hb.system.1
  have hsid : (epsilonSys w β : ℝ) ≤ epsilonId w β := by
    have he : epsilonSys w β ≤ epsilonId w β := by
      dsimp [epsilonSys]
      linarith [hb.exact.1]
    exact_mod_cast he
  have hpop : NormLedger D (moment D) t (w / 2) (epsilonId w β) (W ^ 2) := by
    refine ⟨hw'.1.trans hWW, hw'.2.1.trans hWW,
      ((one_div_le_one_div_of_le hs0 hsid).trans hw'.2.2.1).trans hWW, ?_, ?_⟩
    · intro s hs hs'
      simpa only [← pow_mul] using
        hw'.2.2.2.2 (2 * s) (by omega)
    · intro r hr
      exact (hw'.2.2.2.2 r hr).trans
        (pow_le_pow_left₀ (by linarith) hWW _)
  have hid := identifiability D (w / 2) γ (epsilonId w β) (cStar β) (W ^ 2) t hD ht
    (degree_bounds w hw).1
    ⟨by exact_mod_cast hb.energy.1, by exact_mod_cast hb.energy.2⟩
    ⟨he0, le_min (exact_tolerance w β hw hβ) (by
      simp only [epsilonId, Rat.cast_pow, Rat.cast_div, Rat.cast_mul,
        Rat.cast_ofNat, Rat.cast_natCast]; rfl)⟩ hpop
  have hr := rounded_certificate D M w β hβ hM
  have heta : (0 : ℝ) ≤ etaStar w β := by exact_mod_cast hb.error.1.le
  have hsmall : γ + Real.sqrt (etaStar w β) ≤ 1 := by linarith [hb.small]
  have htrans := transfer D (roundedMoments d w β M) t (w / 2) γ
    (etaStar w β) (epsilonSys w β) W hD heta hsmall hs0 hr hw'
  have heq : 2 * (epsilonSys w β : ℝ) + 2 * (etaStar w β : ℝ) * gammaD t =
      (epsilonId w β : ℝ) := by
    have h := (identities w β hβ.1).2.2
    dsimp [gammaD, t]
    exact_mod_cast h
  rw [heq] at htrans
  apply (SoS.DerivesNq.trans htrans hid).mono le_rfl
  dsimp [identBound, W, t]
  gcongr
  exact_mod_cast system_length (moment D) (tDegree w) (epsilonId w β)

theorem projection_ident (D : Data k d) (M : ℕ → QPoly d) (w β : ℚ) (γ : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hβ : 0 < β ∧ β ≤ 1 / 4)
    (hD : D.Valid (w / 2) γ) (hγ : γ ≤ gammaStar β)
    (hM : momentCertificate D (fun r ↦ SoS.toReal (M r)) (tDegree w)
      (etaStar w β / 4)) (P : Mat d) (hP : Projection P)
    (hle : LE ((tauStar β : ℝ) • P) (between D)) :
    SoS.DerivesNq (system (roundedMoments d w β M) (tDegree w) (epsilonSys w β))
      (8 * tDegree w) (projectionBound d w β) 1 (C (epsilonR β : ℝ) - quad P) := by
  have hb := bounds w β hβ
  have he0 : (0 : ℝ) < epsilonR β := by exact_mod_cast hb.rounding.1
  have hτ : (0 : ℝ) < tauStar β := by
    simpa only [tauStar, Rat.cast_div, Rat.cast_ofNat] using
      div_pos he0 (by norm_num : (0 : ℝ) < 3)
  have heq : (cStar β : ℝ) / (tauStar β : ℝ) = (epsilonR β : ℝ) := by
    exact_mod_cast (identities w β hβ.1).1
  have hpsd : P.PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hP.1, hP.2] using
      posSemidef_conjTranspose_mul_self P
  have hnP : SoS.coeffNorm1 (quad P) ≤ (d : ℝ) ^ 2 := by
    simpa only [mul_one] using
      IdentAux.norm_quad P 1 (RoundCondAux.projection_entry P hP)
  have hnQ := (IdentAux.quadratic_norms D (w / 2) γ hD).2
  have hgap : SoS.coeffNorm1 (Q D - C (tauStar β : ℝ) * quad P) ≤
      (2 + (tauStar β : ℝ)) * (d : ℝ) ^ 2 := by
    apply (SoS.coeffNorm1_sub_le _ _).trans
    rw [SoS.coeffNorm1_C_mul, abs_of_pos hτ]
    nlinarith [mul_le_mul_of_nonneg_left hnP hτ.le]
  have hid := mean_ident D M w β γ hw hβ hD hγ hM
  have hp := round_ident _ D P (8 * tDegree w) (cStar β) (tauStar β)
    (epsilonR β) (identBound d w β) hτ heq.le hpsd hle hid
    (by have := hb.degree; omega)
  apply hp.mono le_rfl
  rw [heq, sub_self, abs_zero, add_zero]
  calc _ = (identBound d w β +
        SoS.coeffNorm1 (Q D - C (tauStar β : ℝ) * quad P)) / tauStar β :=
          (add_div ..).symm
    _ ≤ (identBound d w β + (2 + (tauStar β : ℝ)) * (d : ℝ) ^ 2) / tauStar β := by
      gcongr
    _ ≤ projectionBound d w β := le_max_right _ _

theorem plain_derives (A : List (RPoly d)) (deg : ℕ) (M X : ℝ) (g : RPoly d)
    (h : SoS.DerivesNq A deg M 1 g) : (Rounding.plainSystem A).Derives deg M X g := by
  let Ξ : Fin (Rounding.plainSystem A).slots.length → Mat d := fun i ↦ Fin.elim0 i
  refine ⟨Ξ, fun i ↦ Fin.elim0 i, ?_⟩
  have hi : (Rounding.plainSystem A).instances Ξ = A := by
    simp [Rounding.FamilySystem.instances, Rounding.plainSystem]
  have h' : SoS.DerivesNq ((Rounding.plainSystem A).instances Ξ) deg M 1 g := hi.symm ▸ h
  obtain ⟨P, hn, hq⟩ := h'
  exact ⟨P, hn, hq, fun i ↦ Fin.elim0 i⟩

def input (k d : ℕ) (w β : ℚ) (M : ℕ → QPoly d) : Rounding.ComplementInput d :=
  ⟨Rounding.plainSystem (system (roundedMoments d w β M) (tDegree w) (epsilonSys w β)),
    8 * tDegree w, epsilonR β, β, k, projectionBound d w β,
    max 1 (sizeParameter d w β ^ (20 * tDegree w)), 1⟩

/-- The same rounded moment system works for every component count below its public cap. -/
theorem input_hypotheses_bounded (D : Data k d) (cap : ℕ) (hkcap : k ≤ cap)
    (M : ℕ → QPoly d) (w β : ℚ) (γ : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hβ : 0 < β ∧ β ≤ 1 / 4)
    (hD : D.Valid (w / 2) γ) (hγ : γ ≤ gammaStar β)
    (hM : momentCertificate D (fun r ↦ SoS.toReal (M r)) (tDegree w)
      (etaStar w β / 4)) :
    ∃ P : Mat d, (input cap d w β M).Hypotheses [P] ∧
      ∀ u, sqnorm u = 1 → qform D.cov u ≤ tauStar β →
        1 - (epsilonR β : ℝ) ≤ sqnorm (P *ᵥ u) := by
  have hb := bounds w β hβ
  have he0 : (0 : ℝ) < epsilonR β := by exact_mod_cast hb.rounding.1
  have he1 : (epsilonR β : ℝ) ≤ 1 := by exact_mod_cast hb.rounding.2
  have hτeq : (tauStar β : ℝ) = (epsilonR β : ℝ) / 3 := by
    simp only [tauStar, Rat.cast_div, Rat.cast_ofNat]
  have hgeq : (gammaStar β : ℝ) = (epsilonR β : ℝ) / 6 := by
    simp only [gammaStar, Rat.cast_div, Rat.cast_ofNat]
  have hτ : (0 : ℝ) < tauStar β := by rw [hτeq]; positivity
  have hr := rounded_certificate D M w β hβ hM
  have hW := norm_ledger D M w β γ hw hβ hD hγ hM
  have heta : (0 : ℝ) ≤ etaStar w β := by exact_mod_cast hb.error.1.le
  have hsmall : γ + Real.sqrt (etaStar w β) ≤ 1 := by linarith [hb.small]
  have hε : (etaStar w β : ℝ) * gammaD (tDegree w) = epsilonSys w β := by
    dsimp [etaStar, gammaD]
    push_cast
    exact div_mul_cancel₀ _ (by have := hb.degree; positivity)
  obtain ⟨P, hP, hlo, hhi⟩ := spectral_projection D (w / 2) γ (tauStar β) hD hτ
  obtain ⟨R, hR, hrank, hcomp⟩ := round_feasible D (roundedMoments d w β M)
    (tDegree w) (w / 2) γ (etaStar w β) (epsilonSys w β) (sizeParameter d w β)
    hD heta hsmall hr hε.le (by exact_mod_cast hb.system.2.trans (by norm_num)) hW
  have hk : 1 ≤ k := by
    by_contra! h
    have hk : k = 0 := by omega
    subst k
    have hs := hD.1.2.2.1
    simp [Data.frame] at hs
  refine ⟨P, ?_, ?_⟩
  · refine ⟨system_valid D _ _ _ _ (by have := hb.degree; omega) hr,
      ⟨4 * tDegree w, by dsimp [input]; omega⟩,
      by dsimp [input]; have := hb.degree; omega,
      hb.rounding.1, hβ.1, hβ.2.trans (by norm_num), hk.trans hkcap,
      le_max_left _ _, le_max_left _ _, le_rfl, radius_bound β hβ.1, ?_,
      R, hR, hrank.trans hkcap, ?_⟩
    · intro Q hQ
      have hQP : Q = P := List.mem_singleton.mp hQ
      subst Q
      exact ⟨hP, plain_derives _ _ _ _ _
        (projection_ident D M w β γ hw hβ hD hγ hM P hP hlo)⟩
    · refine ⟨fun f hf ↦ (hcomp.1 f hf).mono le_rfl (le_max_right _ _), ?_⟩
      simp [input, Rounding.plainSystem]
  · intro u hu hthin
    have hg := geometry D P (w / 2) γ (tauStar β) (tauStar β) u hD hP hu
      ⟨by linarith, by linarith⟩ hτ.le hlo hhi hthin
    have heq : 2 * (gammaStar β : ℝ) + (tauStar β : ℝ) + tauStar β = epsilonR β := by
      exact_mod_cast (identities w β hβ.1).2.1
    linarith


end

end ABBKS26.IdCov.SubspaceAux
