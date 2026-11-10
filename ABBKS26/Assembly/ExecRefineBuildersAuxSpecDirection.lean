module

public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecGuard
public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobFloor

/-! Magnitude and covariance-error bounds for pulled-back rounded directions. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.SpecDirection

open Common _root_.ABBKS26.Tree Matrix Sources Builders Rounding
open scoped BigOperators

noncomputable section

variable {n k d : ℕ}

def rounded (p b : ℕ) (v : Fin d → ℚ) : Fin d → ℚ :=
  fun i ↦ FrobRound.entry p b 1 (v i)

theorem covBound_bound (a : Args) :
    FrobSize.RatBound (5 * FrobScan.key a + 4) (FrobBounds.covBound a) := by
  let z := FrobScan.key a
  have hd : a.1.1 ≤ z := (FrobScan.key_bounds a).2.1
  have hx : (encPoints a.1.2.2.2.1).length ≤ z := (FrobScan.key_bounds a).2.2.2.1
  have hdim : FrobSize.RatBound z (a.1.1 : ℚ) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hd.trans (Nat.lt_two_pow_self (n := z)).le
    · simpa only [Rat.den_natCast] using Nat.one_le_two_pow
  have h16 : FrobSize.RatBound 4 16 := by constructor <;> norm_num
  have hpow : FrobSize.RatBound (encPoints a.1.2.2.2.1).length
      ((2 : ℚ) ^ (encPoints a.1.2.2.2.1).length) := by
    constructor
    · rw [abs_of_nonneg (by positivity)]
    · simpa using Nat.one_le_two_pow
  have hb := ((h16.mul hdim).mul (hpow.mul hpow)).mul
    (SpecWindows.inverse_bound (FrobScan.field_bound a 0))
  simp only [FrobBounds.covBound, pow_two, div_eq_mul_inv]
  exact hb.mono (by dsimp only [z] at hx ⊢; omega)

/-- The cubic local precision pays for the original covariance scale and arbitrarily
small encoded subspace accuracies. -/
theorem precision_error (a : Args) (hμ : 0 < field a 10) :
    (FrobBounds.covBound a : ℝ) * a.1.1 * (1 / (2 : ℝ) ^ SpecGuard.precision a) ^ 2 ≤
      (field a 10 : ℝ) ^ 2 / 16 := by
  let z := FrobScan.key a
  have hz : 64 ≤ z := (FrobScan.key_bounds a).1
  have hμR : (0 : ℝ) < field a 10 := by exact_mod_cast hμ
  have hi : (field a 10 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (2 * z) := by
    have hb := (SpecWindows.inverse_bound (FrobScan.field_bound a 10)).magnitude
    have hh : |(field a 10 : ℝ)⁻¹| ≤ (2 : ℝ) ^ (2 * z) := by exact_mod_cast hb
    exact (le_abs_self _).trans hh
  have hlow : 1 / (2 : ℝ) ^ (2 * z) ≤ field a 10 := by
    have hm := mul_le_mul_of_nonneg_right hi hμR.le
    rw [inv_mul_cancel₀ hμR.ne'] at hm
    exact (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hm)
  have hc : (FrobBounds.covBound a : ℝ) ≤ (2 : ℝ) ^ (5 * z + 4) := by
    exact_mod_cast (le_abs_self _).trans (covBound_bound a).magnitude
  have hd : (a.1.1 : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast (FrobScan.key_bounds a).2.1.trans (Nat.lt_two_pow_self (n := z)).le
  have hcd : (FrobBounds.covBound a : ℝ) * a.1.1 ≤ (2 : ℝ) ^ (6 * z + 4) := by
    have hh := mul_le_mul hc hd (Nat.cast_nonneg _) (by positivity)
    convert hh using 1
    rw [← pow_add]
    congr 1
    omega
  have hpower : 10 * z + 8 ≤ 2 * z ^ 3 := by
    have hz2 := Nat.pow_le_pow_left hz 2
    have hz3 : 4096 * z ≤ z ^ 3 := by nlinarith only [hz2]
    omega
  have hp : 16 * (2 : ℝ) ^ (6 * z + 4) * ((2 : ℝ) ^ (2 * z)) ^ 2 ≤
      ((2 : ℝ) ^ SpecGuard.precision a) ^ 2 := by
    change _ ≤ ((2 : ℝ) ^ (z ^ 3)) ^ 2
    calc
      _ = (2 : ℝ) ^ (4 + (6 * z + 4) + (2 * z) * 2) := by
        rw [← pow_mul, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add, ← pow_add]
      _ = (2 : ℝ) ^ (10 * z + 8) :=
        congrArg (fun t : ℕ ↦ (2 : ℝ) ^ t) (by omega)
      _ ≤ (2 : ℝ) ^ (z ^ 3 * 2) := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
      _ = _ := pow_mul _ _ _
  have hpaid : (FrobBounds.covBound a : ℝ) * a.1.1 *
      (((2 : ℝ) ^ (2 * z)) ^ 2 * 16) ≤ ((2 : ℝ) ^ SpecGuard.precision a) ^ 2 := by
    apply le_trans _ hp
    nlinarith only [mul_le_mul_of_nonneg_right hcd
      (by positivity : 0 ≤ 16 * ((2 : ℝ) ^ (2 * z)) ^ 2)]
  have herr : (FrobBounds.covBound a : ℝ) * a.1.1 /
      ((2 : ℝ) ^ SpecGuard.precision a) ^ 2 ≤ (1 / (2 : ℝ) ^ (2 * z)) ^ 2 / 16 := by
    rw [div_pow, one_pow, div_div]
    exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hpaid)
  calc
    _ = (FrobBounds.covBound a : ℝ) * a.1.1 /
        ((2 : ℝ) ^ SpecGuard.precision a) ^ 2 := by ring
    _ ≤ (1 / (2 : ℝ) ^ (2 * z)) ^ 2 / 16 := herr
    _ ≤ (field a 10 : ℝ) ^ 2 / 16 := by gcongr

theorem covariance_upper (G : FrameModel k d) (π γ r : ℝ)
    (hG : Centered.DataValid G π γ r) (j : Fin k) (v : Vec d) :
    qform (G.cov j) v ≤ (1.1 / π) * sqnorm v := by
  have hn (i : Fin k) : 0 ≤ qform (G.cov i) v :=
    (hG.1.2.2.2 i).posSemidef.dotProduct_mulVec_nonneg v
  have hw (i : Fin k) : 0 ≤ G.weight i := hG.1.1.le.trans (hG.1.2.1 i)
  have hsum : G.weight j * qform (G.cov j) v ≤ qform G.second v := by
    rw [ABBKS26.RefineAux.frame_second_qform]
    simp only [hG.2.1, dotProduct_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    exact Finset.single_le_sum (fun i _ ↦ mul_nonneg (hw i) (hn i)) (Finset.mem_univ j)
  have hu := hG.2.2.1.2.2 v
  simp only [qform, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul] at hu
  change qform G.second v ≤ (1 + γ) * sqnorm v at hu
  have hπ := mul_le_mul_of_nonneg_right (hG.1.2.1 j) (hn j)
  have hγ := mul_le_mul_of_nonneg_right hG.2.2.2.1 (DetRoundAux.sqnorm_nonneg v)
  rw [div_mul_eq_mul_div, le_div_iff₀ hG.1.1]
  change π * qform (G.cov j) v ≤ _ at hπ
  nlinarith only [hπ, hsum, hu, hγ]

theorem magnitude_of_floor (S : Mat d) (c : ℝ) (b : ℕ) (v : Fin d → ℚ)
    (hc : 0 < c)
    (hfloor : ∀ z, (c / (2 : ℝ) ^ b) * sqnorm z ≤ qform S z)
    (hv : qform S (fun i ↦ (v i : ℝ)) ≤ c) :
    ∀ i, |v i| ≤ (2 : ℚ) ^ b := by
  let z : Vec d := fun i ↦ (v i : ℝ)
  have hn : sqnorm z ≤ (2 : ℝ) ^ b := by
    have hf := (hfloor z).trans hv
    have hp : (0 : ℝ) < 2 ^ b := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hp] at hf
    nlinarith only [hf, hc]
  intro i
  have hi : z i ^ 2 ≤ sqnorm z := by
    simpa only [sqnorm, dotProduct, pow_two] using
      Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i)
  have hp : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have hb : |z i| ≤ (2 : ℝ) ^ b := by
    have hh : z i ^ 2 ≤ ((2 : ℝ) ^ b) ^ 2 := by
      nlinarith only [hi, hn, hp]
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (z i)) (by positivity)).mp
      (by simpa only [sq_abs] using hh)
  change |(v i : ℝ)| ≤ (2 : ℝ) ^ b at hb
  exact_mod_cast hb

/-- The rational sample floor controls pulled-back vectors too. No bound on the bits of
the arbitrary specified frame is needed. -/
theorem prepared_magnitude (F : FrameCode) (hF : FrameSpec F)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (hnf : ¬ centeredFar F M ω r (ps h) fuel P I hI)
    (u : Fin d → ℚ) (hu : sqnorm (fun i ↦ (u i : ℝ)) ≤ 4) :
    ∀ i, |((SpecFrame.frame F (ps h) x fuel P).transformᵀ *ᵥ u) i| ≤
      (2 : ℚ) ^ FrobScan.coefficientExponent (args k ps x h P, fuel) := by
  let T := (SpecFrame.frame F (ps h) x fuel P).transform
  let a := (args k ps x h P, fuel)
  let v := Tᵀ *ᵥ u
  have hdata := SpecFrame.prepared_data F hF ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hf hh hl hP hnf
  obtain ⟨j, hj, hfloor⟩ := FrobFloor.prepared_floor k ps x fuel h P M ε w η Δ D ω r I
    hx hp hf hh hI hl hP
  have hj' : j ∈ Set.range (I.orderEmbOfFin rfl) := by
    rw [I.range_orderEmbOfFin]
    exact hj
  obtain ⟨s, rfl⟩ := hj'
  have hupper := covariance_upper _ _ _ _ hdata s (fun i ↦ (u i : ℝ))
  have hcast : (fun i ↦ (v i : ℝ)) =
      (T.map (algebraMap ℚ ℝ))ᵀ *ᵥ (fun i ↦ (u i : ℝ)) := by
    rw [← transpose_map]
    funext i
    exact (algebraMap ℚ ℝ).map_mulVec Tᵀ u i
  have he : qform (M.S (I.orderEmbOfFin rfl s)) (fun i ↦ (v i : ℝ)) =
      qform ((ABBKS26.RefineAux.affineReference
        (ABBKS26.RefineAux.roundedReference M ω r P I hI)
        (T.map (algebraMap ℚ ℝ)) 0).model.cov s) (fun i ↦ (u i : ℝ)) := by
    rw [hcast]
    exact (Separation.dotProduct_congr_mulVec _ _ _).symm
  have hw : (0 : ℝ) < (ps h).w := by
    exact_mod_cast (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh).1
  apply magnitude_of_floor _ (40 / ((ps h).w : ℝ)) (FrobScan.coefficientExponent a) v
    (by positivity) hfloor
  rw [he]
  apply hupper.trans
  push_cast
  have hb := mul_le_mul_of_nonneg_left hu
    (by positivity : (0 : ℝ) ≤ 1.1 / (((ps h).w : ℝ) / 2))
  calc
    _ ≤ 1.1 / (((ps h).w : ℝ) / 2) * 4 := hb
    _ ≤ 40 / ((ps h).w : ℝ) := by
      field_simp
      norm_num

theorem rounding_error (p b : ℕ) (v : Fin d → ℚ)
    (hv : ∀ i, |v i| ≤ (2 : ℚ) ^ b) :
    sqnorm ((fun i ↦ (rounded p b v i : ℝ)) - fun i ↦ (v i : ℝ)) ≤
      d * (1 / (2 : ℝ) ^ p) ^ 2 := by
  have he (i : Fin d) : |(rounded p b v i : ℝ) - v i| ≤ 1 / (2 : ℝ) ^ p := by
    have hh := FrobRound.entry_error p b 1 (v i) (by simpa only [one_mul] using hv i)
    simp only [one_mul] at hh
    change |(FrobRound.entry p b 1 (v i) : ℝ) - v i| ≤ _
    have hhR := Rat.cast_mono (K := ℝ) hh
    push_cast at hhR
    exact hhR
  calc
    _ = ∑ i : Fin d, ((rounded p b v i : ℝ) - v i) ^ 2 := by
      simp only [sqnorm, dotProduct, Pi.sub_apply, pow_two]
    _ ≤ ∑ _i : Fin d, (1 / (2 : ℝ) ^ p) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (he i) 2
    _ = _ := by simp

theorem covariance_error (p b : ℕ) (v : Fin d → ℚ) (S : Mat d) (C : ℝ)
    (hv : ∀ i, |v i| ≤ (2 : ℚ) ^ b) (hC : 0 ≤ C)
    (hS : ∀ z, qform S z ≤ C * sqnorm z) :
    qform S ((fun i ↦ (rounded p b v i : ℝ)) - fun i ↦ (v i : ℝ)) ≤
      C * d * (1 / (2 : ℝ) ^ p) ^ 2 := by
  exact (hS _).trans ((mul_le_mul_of_nonneg_left (rounding_error p b v hv) hC).trans_eq
    (mul_assoc _ _ _).symm)

/-- The rounding error has small variance in every compatible component, independently
of frame and solver output bits. -/
theorem prepared_covariance_error
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (v : Fin d → ℚ)
    (hv : ∀ i, |v i| ≤ (2 : ℚ) ^ SpecGuard.exponent (args k ps x h P, fuel)) :
    let a := (args k ps x h P, fuel)
    ∀ j ∈ I, qform (M.S j)
      ((fun i ↦ (rounded (SpecGuard.precision a) (SpecGuard.exponent a) v i : ℝ)) -
        fun i ↦ (v i : ℝ)) ≤ ((ps h).subspaceAccuracy : ℝ) ^ 2 / 16 := by
  let a := (args k ps x h P, fuel)
  have hstep := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hw : field a 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hμ : field a 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hw0 : 0 < field a 0 := hw ▸ hstep.1
  have hc : (0 : ℝ) ≤ FrobBounds.covBound a := by
    have hcQ : 0 ≤ FrobBounds.covBound a := by unfold FrobBounds.covBound; positivity
    exact_mod_cast hcQ
  have hu := FrobBounds.prepared_cov_upper ps x h P M ε w η Δ D ω r I hI
    hx hp hh hl hP
  rw [← FrobBounds.covBound_agrees k ps x fuel h P (by omega)] at hu
  dsimp only
  intro j hj
  exact (covariance_error (SpecGuard.precision a) (SpecGuard.exponent a) v (M.S j)
    (FrobBounds.covBound a) hv hc (hu j hj)).trans (by
      have he := precision_error a (by rw [hμ]; exact hstep.2.2.1)
      change (FrobBounds.covBound a : ℝ) * d *
        (1 / (2 : ℝ) ^ SpecGuard.precision a) ^ 2 ≤ (field a 10 : ℝ) ^ 2 / 16 at he
      rwa [hμ] at he)

end

end ABBKS26.Assembly.Exec.RefineSynth.SpecDirection
