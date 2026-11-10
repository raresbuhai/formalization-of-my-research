module

public import ABBKS26.IdCov.NormsAux
public import ABBKS26.IdCov.Ident
public import ABBKS26.Rounding.Raw

/-!
# IdCov precision, coefficient norms and logarithmic degrees

Coefficient norm estimates and logarithmic degree bounds for the IdCov step.
-/

@[expose] public section

namespace ABBKS26.IdCov

noncomputable section


open Matrix

open Common MvPolynomial Finset
open scoped BigOperators
variable {k d : ℕ}

def robustPrecision (d : ℕ) (w β : ℚ) : ℕ :=
  Nat.clog 2 ⌈(d + 1 : ℚ) ^ (4 * tDegree w) / etaStar w β⌉₊ + 2

def sizeParameter (d : ℕ) (w β : ℚ) : ℝ :=
  2 ^ robustPrecision d w β * 64 * (d + 1 : ℝ) ^ 2 * tDegree w *
    ⌈8 / w⌉₊ * ⌈1 / epsilonSys w β⌉₊

/-- Rounded moments satisfy the explicit IdCov norm ledger. -/
theorem norm_ledger
    (D : Data k d) (M : ℕ → QPoly d) (w β : ℚ) (γ : ℝ)
    (hw : 0 < w ∧ w ≤ 1 / 2) (hβ : 0 < β ∧ β ≤ 1 / 4)
    (hD : D.Valid (w / 2) γ) (hγ : γ ≤ gammaStar β)
    (hM : momentCertificate D (fun r ↦ SoS.toReal (M r)) (tDegree w) (etaStar w β / 4)) :
    NormLedger D (fun r ↦ SoS.toReal (roundPoly (robustPrecision d w β) (M r)))
      (tDegree w) (w / 2) (epsilonSys w β) (sizeParameter d w β) := by
  classical
  -- The coarse ledger only needs the isotropy bound already contained in `hD`.
  have _ := hγ
  let t := tDegree w
  let Cw : ℝ := ⌈8 / w⌉₊
  let E : ℝ := ⌈1 / epsilonSys w β⌉₊
  let A : ℝ := (d + 1) * Cw
  let B : ℝ := 8 * t * A
  let H : ℝ := 64 * (d + 1) ^ 2 * t
  let W := sizeParameter d w β
  have ht : 3 ≤ t := by dsimp [t, tDegree]; omega
  have htR : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have hd : (1 : ℝ) ≤ d + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hwR' : (w : ℝ) ≤ 1 / 2 := by
    have h : (w : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.mpr hw.2
    norm_num at h ⊢
    exact h
  have hCdiv : 8 / (w : ℝ) ≤ Cw := by
    dsimp [Cw]
    exact_mod_cast Nat.le_ceil (8 / w)
  have hC : 2 ≤ Cw := by
    have h : (2 : ℝ) ≤ 8 / w := (le_div_iff₀ hwR).mpr (by linarith)
    linarith
  have hC1 : 1 ≤ Cw := by linarith
  have hp := NormsAux.parameter_bounds w β hβ
  have he : (1 : ℝ) ≤ 1 / (epsilonSys w β : ℝ) := by
    have he0 : (0 : ℝ) < epsilonSys w β := by exact_mod_cast hp.1
    have he1 : (epsilonSys w β : ℝ) ≤ 1 := by exact_mod_cast hp.2.1
    exact (le_div_iff₀ he0).mpr (by simpa using he1)
  have hEinv : 1 / (epsilonSys w β : ℝ) ≤ E := by
    dsimp [E]
    exact_mod_cast Nat.le_ceil (1 / epsilonSys w β)
  have hE : 1 ≤ E := he.trans hEinv
  have hH : 1 ≤ H := by dsimp [H]; nlinarith [sq_nonneg (d : ℝ)]
  have hHC : 1 ≤ H * Cw := one_le_mul_of_one_le_of_one_le hH hC1
  have hWfull : H * Cw * E ≤ W := by
    calc _ ≤ 2 ^ robustPrecision d w β * (H * Cw * E) :=
          le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      _ = W := by dsimp [W, H, E, Cw, sizeParameter]; ring
  have hHCW : H * Cw ≤ W :=
    (le_mul_of_one_le_right (by positivity) hE).trans hWfull
  have hHW : H ≤ W :=
    (le_mul_of_one_le_right (by positivity) hC1).trans hHCW
  have hCW : Cw ≤ W :=
    (le_mul_of_one_le_left (by positivity) hH).trans hHCW
  have hEW : E ≤ W :=
    (le_mul_of_one_le_left (by positivity) hHC).trans hWfull
  have hA : 1 ≤ A := one_le_mul_of_one_le_of_one_le hd hC1
  have hA2 : 2 * (d + 1 : ℝ) ≤ A := by
    dsimp [A]
    nlinarith
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hBW : 8 * B ≤ W := by
    apply le_trans (b := H * Cw) _ hHCW
    dsimp [B, A, H]
    have hd2 : (d + 1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 := by nlinarith
    calc 8 * (8 * t * ((d + 1 : ℝ) * Cw)) =
          64 * (d + 1 : ℝ) * t * Cw := by ring
      _ ≤ 64 * (d + 1 : ℝ) ^ 2 * t * Cw := by gcongr
  have hBW' : B ≤ W := (by linarith : B ≤ 8 * B).trans hBW
  have hW1 : 1 ≤ W := hB.trans hBW'
  have hlin (i : Fin k) : SoS.coeffNorm1 (lin (D.mean i)) ≤ A := by
    calc _ ≤ ∑ j : Fin d, |D.mean i j| := by
          apply (SoS.coeffNorm1_sum_le _ _).trans
          exact sum_le_sum fun j _ ↦ by
            simp only [SoS.coeffNorm1_C_mul, SoS.coeffNorm1_X, mul_one, le_refl]
      _ ≤ ∑ _j : Fin d, Cw := sum_le_sum fun j _ ↦ NormsAux.mean_entry D w γ hw hD i j
      _ ≤ A := by simp [A]; nlinarith
  have hS : SoS.coeffNorm1 (S D) ≤ A ^ 2 := by
    apply (IdentAux.quadratic_norms D (w / 2) γ hD).1.trans
    nlinarith [sq_nonneg (d : ℝ), sq_nonneg A]
  have hpop (r : ℕ) (hr : r ≤ 4 * t) : SoS.coeffNorm1 (moment D r) ≤ B ^ r :=
    NormsAux.moment_norm D (w / 2) γ A hD hA hlin hS r hr
  have hη : 0 ≤ (etaStar w β / 4 : ℝ) ∧ (etaStar w β / 4 : ℝ) ≤ 1 := by
    constructor
    · exact_mod_cast (div_nonneg hp.2.2.1.le (by norm_num : (0 : ℚ) ≤ 4))
    · exact_mod_cast hp.2.2.2
  refine ⟨hHW, ?_, hEinv.trans hEW, ?_, ?_⟩
  · have hdiv : (4 : ℝ) / (w / 2) = 8 / w := by ring
    rw [hdiv]
    exact hCdiv.trans hCW
  · intro s hs hs'
    have hr : 2 * s ≤ 4 * t := by omega
    have herr := NormsAux.error_norm D (fun r ↦ SoS.toReal (M r))
      (etaStar w β / 4) hη ⟨hs, hs'⟩ hM
    have hbase : 4 * s * (d + 1 : ℝ) ≤ B := by
      have hsR : (s : ℝ) ≤ 2 * t := by exact_mod_cast hs'
      have hda : (d + 1 : ℝ) ≤ A := by linarith
      dsimp [B]
      nlinarith
    have herr' : SoS.coeffNorm1 (SoS.toReal (M (2 * s)) - moment D (2 * s)) ≤
        B ^ (2 * s) := herr.trans (pow_le_pow_left₀ (by positivity) hbase _)
    have hhom : (M (2 * s)).IsHomogeneous (2 * s) :=
      IsHomogeneous.of_map (algebraMap ℚ ℝ).injective (hM.1 s hs hs')
    have hround : SoS.coeffNorm1
        (SoS.toReal (roundPoly (robustPrecision d w β) (M (2 * s)) - M (2 * s))) ≤
        B ^ (2 * s) := by
      apply (ApproxAux.rounding_norm _ _ _ hhom).trans
      have hdb : (d + 1 : ℝ) ≤ B := by dsimp [B]; nlinarith
      exact (div_le_self (by positivity) (one_le_pow₀ (by norm_num))).trans
        (pow_le_pow_left₀ (by positivity) hdb _)
    have hnorm : SoS.coeffNorm1
        (SoS.toReal (roundPoly (robustPrecision d w β) (M (2 * s)))) ≤
        3 * B ^ (2 * s) := by
      have h₂ := SoS.coeffNorm1_add_le
        (SoS.toReal (M (2 * s)) - moment D (2 * s)) (moment D (2 * s))
      have h₃ := SoS.coeffNorm1_add_le
        (SoS.toReal (roundPoly (robustPrecision d w β) (M (2 * s))) -
          SoS.toReal (M (2 * s))) (SoS.toReal (M (2 * s)))
      simp only [SoS.toReal, map_sub] at hround
      change SoS.coeffNorm1
        (SoS.toReal (roundPoly (robustPrecision d w β) (M (2 * s))) -
          SoS.toReal (M (2 * s))) ≤ B ^ (2 * s) at hround
      simp only [sub_add_cancel] at h₂ h₃
      linarith [hpop (2 * s) hr]
    apply hnorm.trans
    calc 3 * B ^ (2 * s) ≤ (8 : ℝ) ^ (2 * s) * B ^ (2 * s) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact (by norm_num : (3 : ℝ) ≤ 8).trans
            (le_self_pow₀ (by norm_num) (by omega))
      _ = (8 * B) ^ (2 * s) := (mul_pow ..).symm
      _ ≤ W ^ (2 * s) := pow_le_pow_left₀ (by positivity) hBW _
  · intro r hr
    exact (hpop r hr).trans ((pow_le_pow_left₀ (by positivity) hBW' r).trans
      (pow_le_pow_right₀ hW1 (by omega)))

/-- The moment degree is logarithmic and its square fits the frozen time exponent. -/
theorem degree_bounds
    (w : ℚ) (hw : 0 < w ∧ w ≤ 1 / 2) :
    2 ≤ (w / 2 : ℝ) * 2 ^ (tDegree w - 1) ∧
      (tDegree w) ^ 2 ≤ 16 * (logInv w ^ 2 + 1) ∧
      (logInv w : ℝ) ≤ 1.45 * Real.log (1 / w) + 2 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw.1
  have hinv : (1 : ℝ) / w ≤ 2 ^ logInv w := by
    have hq : w⁻¹ ≤ (2 : ℚ) ^ logInv w :=
      (Nat.le_ceil _).trans (by
        exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈w⁻¹⌉₊)
    simpa only [one_div] using (show (w : ℝ)⁻¹ ≤ (2 : ℝ) ^ logInv w from by
      exact_mod_cast hq)
  have hL : 1 ≤ logInv w := by
    apply Nat.clog_pos (by norm_num : 1 < 2)
    apply Nat.one_lt_iff_ne_zero_and_ne_one.mpr
    have htwo : (2 : ℚ) ≤ w⁻¹ :=
      (le_inv_comm₀ (by norm_num) hw.1).mpr (by simpa only [one_div] using hw.2)
    have hn : 2 ≤ ⌈w⁻¹⌉₊ := by exact_mod_cast htwo.trans (Nat.le_ceil _)
    omega
  refine ⟨?_, ?_, ?_⟩
  · have hprod : 1 ≤ (2 : ℝ) ^ logInv w * w := (div_le_iff₀ hwR).mp hinv
    rw [tDegree, show logInv w + 3 - 1 = logInv w + 2 by omega, pow_add]
    norm_num
    nlinarith
  · dsimp only [tDegree]
    nlinarith [sq_nonneg (logInv w : ℤ)]
  · have hn := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2)
      (show 1 < ⌈w⁻¹⌉₊ from by
        have htwo : (2 : ℚ) ≤ w⁻¹ :=
          (le_inv_comm₀ (by norm_num) hw.1).mpr (by simpa only [one_div] using hw.2)
        have : 2 ≤ ⌈w⁻¹⌉₊ := by exact_mod_cast htwo.trans (Nat.le_ceil _)
        omega)
    have hpow : (2 : ℝ) ^ (logInv w - 1) < 1 / w := by
      have hq : (2 : ℚ) ^ (logInv w - 1) < w⁻¹ := by
        exact_mod_cast (Nat.lt_ceil.mp hn : ((2 ^ (logInv w - 1) : ℕ) : ℚ) < w⁻¹)
      simpa only [one_div] using (show (2 : ℝ) ^ (logInv w - 1) < (w : ℝ)⁻¹ from by
        exact_mod_cast hq)
    have hl := Real.log_le_log (by positivity) hpow.le
    rw [Real.log_pow, Nat.cast_sub hL, Nat.cast_one] at hl
    have hL' : (1 : ℝ) ≤ logInv w := by exact_mod_cast hL
    have hlog := Real.log_two_gt_d9
    have hsmall : (20 / 29 : ℝ) ≤ Real.log 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hsmall (sub_nonneg.mpr hL')
    nlinarith

end

end ABBKS26.IdCov
