module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdInput
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdRound
public import ABBKS26.Assembly.ExecRefineBuildersAuxIdFuel

/-! Canonical rounded high moments and their sample-independent coefficient ledger. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdPayload

open Common MvPolynomial
open _root_.ABBKS26.Tree Sources Builders
open Encoding (encRat)
open Turing.MultiTapeTM ComputableInPolyTime
open SoS.Solver (RawPoly encRawPoly)

def tolerance (a : Args) : ℚ := IdCov.epsilonR (field a 10)

def systemError (a : Args) : ℚ := IdCov.epsilonSys (field a 0) (field a 10)

def momentError (a : Args) : ℚ := IdCov.etaStar (field a 0) (field a 10)

theorem tolerance_polytime : ComputableInPolyTime tolerance encArgs encRat :=
  FrameAux.Linear.rat_pow' (rat_div' (field_polytime 10) (const 25)) (const 8)

theorem systemError_polytime : ComputableInPolyTime systemError encArgs encRat := by
  have ht := rat_natCast' (unary_to_binary.comp IdInput.degree_polytime)
  exact rat_div' (FrameAux.Linear.rat_pow'
    (rat_div' (rat_div' (FrameAux.Linear.rat_pow' tolerance_polytime (const 2))
      (const 3)) (rat_mul' (const 64) ht))
    (unary_mul' (const 4) IdInput.degree_polytime)) (const 4)

theorem momentError_polytime : ComputableInPolyTime momentError encArgs encRat := by
  exact rat_div' systemError_polytime (FrameAux.Linear.rat_pow'
    (rat_mul' (const 8) (rat_natCast' (unary_to_binary.comp IdInput.degree_polytime)))
    (unary_add' (unary_mul' (const 4) IdInput.degree_polytime) (const 2)))

def precision (a : Args) : ℕ :=
  IdCov.robustPrecision a.1.1 (field a 0) (field a 10)

theorem precision_polytime : ComputableInPolyTime precision encArgs encUnary := by
  have hd := rat_add' (rat_natCast' (unary_to_binary.comp
    (show ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary by fun_prop)))
    (const 1)
  exact unary_add' (binary_clog_two.comp (FrameAux.Linear.rat_natCeil'
    (rat_div' (FrameAux.Linear.rat_pow' hd
      (unary_mul' (const 4) IdInput.degree_polytime)) momentError_polytime))) (const 2)

def size (a : Args) : ℚ :=
  2 ^ precision a * 64 * (a.1.1 + 1 : ℚ) ^ 2 * IdInput.degree a *
    ⌈8 / field a 0⌉₊ * ⌈1 / systemError a⌉₊

theorem size_polytime : ComputableInPolyTime size encArgs encRat := by
  have hd := rat_add' (rat_natCast' (unary_to_binary.comp
    (show ComputableInPolyTime (fun a : Args ↦ a.1.1) encArgs encUnary by fun_prop)))
    (const 1)
  exact rat_mul' (rat_mul' (rat_mul' (rat_mul' (rat_mul'
    (rat_two_pow' precision_polytime) (const 64))
    (FrameAux.Linear.rat_pow' hd (const 2)))
    (rat_natCast' (unary_to_binary.comp IdInput.degree_polytime)))
    (rat_natCast' (FrameAux.Linear.rat_natCeil'
      (rat_div' (const 8) (field_polytime 0)))))
    (rat_natCast' (FrameAux.Linear.rat_natCeil'
      (rat_div' (const 1) systemError_polytime)))

def magnitude (a : Args) : ℚ := 2 * size a ^ (4 * IdInput.degree a)

def exponent (a : Args) : ℕ := (encRat (magnitude a)).length

theorem magnitude_polytime : ComputableInPolyTime magnitude encArgs encRat :=
  rat_mul' (const 2) (FrameAux.Linear.rat_pow' size_polytime
    (unary_mul' (const 4) IdInput.degree_polytime))

theorem exponent_polytime : ComputableInPolyTime exponent encArgs encUnary :=
  .of_tidy ((ComputableTidilyInPolyTime.encoding_length encRat).comp
    magnitude_polytime.tidy)

def moment (MC : MomentCode) (a : Args) (q : ℕ) : RawPoly :=
  IdRound.run a.1.1 q a.2 (precision a) (exponent a) ((IdInput.run MC a).getD q [])

theorem moment_polytime (MC : MomentCode) (hMC : MomentSpec MC) :
    ComputableInPolyTime (fun a : Args × ℕ ↦ moment MC a.1 a.2)
      (encPair encArgs encUnary) encRawPoly :=
  IdRound.run_polytime_of (by fun_prop) (snd _ _) (by fun_prop)
    (precision_polytime.comp (fst _ _)) (exponent_polytime.comp (fst _ _))
    (listGetDWithInput ((IdInput.run_polytime MC hMC).comp (fst _ _))
      (snd _ _) [])

noncomputable section

theorem size_cast (a : Args) :
    (size a : ℝ) = IdCov.sizeParameter a.1.1 (field a 0) (field a 10) := by
  simp only [size, precision, systemError, IdInput.degree, IdCov.sizeParameter,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one]

/-- The unrounded moments also have bounded coefficients. The norm ledger controls the
rounded moment, and the coefficient-rounding error pays for the difference. -/
theorem coefficient_bound {m d : ℕ} (S : IdCov.Data m d) (Q : ℕ → QPoly d)
    (w β : ℚ) (γ : ℝ) (hw : 0 < w ∧ w ≤ 1 / 2)
    (hβ : 0 < β ∧ β ≤ 1 / 4) (hS : S.Valid (w / 2) γ)
    (hγ : γ ≤ IdCov.gammaStar β)
    (hQ : IdCov.momentCertificate S (fun q ↦ SoS.toReal (Q q))
      (IdCov.tDegree w) (IdCov.etaStar w β / 4))
    (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 2 * IdCov.tDegree w) :
    ∀ α, |((Q (2 * s)).coeff α : ℝ)| ≤
      2 * IdCov.sizeParameter d w β ^ (4 * IdCov.tDegree w) := by
  let W := IdCov.sizeParameter d w β
  have hledger := IdCov.norm_ledger S Q w β γ hw hβ hS hγ hQ
  have ht : 3 ≤ IdCov.tDegree w := by unfold IdCov.tDegree; omega
  have htR : (3 : ℝ) ≤ IdCov.tDegree w := by exact_mod_cast ht
  have hd : (1 : ℝ) ≤ d + 1 := by
    linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hW : 1 ≤ W := by
    have hb := hledger.1
    change 64 * (d + 1 : ℝ) ^ 2 * IdCov.tDegree w ≤ W at hb
    nlinarith only [hb, htR, hd, sq_nonneg (d : ℝ)]
  have hdW : (d + 1 : ℝ) ≤ W := by
    have hb := hledger.1
    change 64 * (d + 1 : ℝ) ^ 2 * IdCov.tDegree w ≤ W at hb
    have hsq : (d + 1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 := by nlinarith only [hd]
    have he := mul_le_mul_of_nonneg_left htR
      (by positivity : (0 : ℝ) ≤ 64 * (d + 1 : ℝ) ^ 2)
    linarith only [hb, he, hsq]
  have hhom : (Q (2 * s)).IsHomogeneous (2 * s) :=
    IsHomogeneous.of_map (algebraMap ℚ ℝ).injective (hQ.1 s hs.1 hs.2)
  have hround := IdCov.ApproxAux.rounding_norm (Q (2 * s))
    (IdCov.robustPrecision d w β) (2 * s) hhom
  have herror : SoS.coeffNorm1
      (SoS.toReal (roundPoly (IdCov.robustPrecision d w β) (Q (2 * s)) -
        Q (2 * s))) ≤ W ^ (4 * IdCov.tDegree w) := by
    apply hround.trans
    apply (div_le_self (by positivity) (one_le_pow₀ (by norm_num))).trans
    exact (pow_le_pow_left₀ (by positivity) hdW _).trans
      (pow_le_pow_right₀ hW (by omega))
  have hrounded : SoS.coeffNorm1
      (SoS.toReal (roundPoly (IdCov.robustPrecision d w β) (Q (2 * s)))) ≤
        W ^ (4 * IdCov.tDegree w) :=
    (hledger.2.2.2.1 s hs.1 hs.2).trans (pow_le_pow_right₀ hW (by omega))
  have he := SoS.coeffNorm1_sub_le
    (SoS.toReal (roundPoly (IdCov.robustPrecision d w β) (Q (2 * s))))
    (SoS.toReal (roundPoly (IdCov.robustPrecision d w β) (Q (2 * s)) - Q (2 * s)))
  simp only [SoS.toReal, map_sub, sub_sub_cancel] at he herror hrounded
  intro α
  have hc := SoS.abs_coeff_le_coeffNorm1 (SoS.toReal (Q (2 * s))) α
  simp only [SoS.toReal, coeff_map] at hc
  exact hc.trans (he.trans (by linarith only [hrounded, herror]))

variable {n k d : ℕ}

/-- Canonical dense reification agrees with SUB's mathematical rounding at each needed
even order. The two enumeration fuel premises are explicit. -/
theorem prepared_agrees (MC : MomentCode) (hMC : MomentSpec MC)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 2 * IdCov.tDegree (ps h).w)
    (hr : 2 * s ≤ fuel) (he : (d + 1) ^ (2 * s) ≤ fuel) :
    (moment MC (args k ps x h P, fuel) (2 * s)).toPoly d =
      roundPoly (IdCov.robustPrecision d (ps h).w (ps h).subspaceAccuracy)
        (((IdInput.run MC (args k ps x h P, fuel)).getD (2 * s) []).toPoly d) := by
  obtain ⟨S, _, hS, hcert⟩ := IdInput.prepared_certificate MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hstep := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨hw, hw2, hβ, hβ100, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hstep
  have hγ := hm.2.2.2.1
  have hη := hm.2.2.2.2.1
  rw [hη] at hcert
  have hwf : field (args k ps x h P, fuel) 0 = (ps h).w := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hβf : field (args k ps x h P, fuel) 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hbound := coefficient_bound S
    (fun q ↦ ((IdInput.run MC (args k ps x h P, fuel)).getD q []).toPoly d)
    (ps h).w (ps h).subspaceAccuracy (ps h).isotropy ⟨hw, hw2⟩
    ⟨hβ, hβ100.trans (by norm_num)⟩
    (by simpa only [Rat.cast_div, Rat.cast_ofNat] using hS) (by rw [hγ]) (by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hcert) s hs
  have hmag (α) :
      |(((IdInput.run MC (args k ps x h P, fuel)).getD (2 * s) []).toPoly d).coeff α| ≤
        (2 : ℚ) ^ exponent (args k ps x h P, fuel) := by
    have heq : (magnitude (args k ps x h P, fuel) : ℝ) =
        2 * IdCov.sizeParameter d (ps h).w (ps h).subspaceAccuracy ^
          (4 * IdCov.tDegree (ps h).w) := by
      simp only [magnitude, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, size_cast,
        IdInput.degree, hwf, hβf]
      rfl
    have hb :
        |(((IdInput.run MC (args k ps x h P, fuel)).getD (2 * s) []).toPoly d).coeff α| ≤
          magnitude (args k ps x h P, fuel) := by
      exact_mod_cast (hbound α).trans_eq heq.symm
    exact hb.trans ((le_abs_self _).trans
      (FrobSize.of_encoding (le_refl _)).magnitude)
  unfold moment
  have hp' : precision (args k ps x h P, fuel) =
      IdCov.robustPrecision d (ps h).w (ps h).subspaceAccuracy := by
    simp only [precision, hwf, hβf]
    rfl
  rw [hp']
  apply IdRound.run_agrees fuel _ _ _ hr he _ hmag
  exact IsHomogeneous.of_map (algebraMap ℚ ℝ).injective (hcert.1 s hs.1 hs.2)

end

end ABBKS26.Assembly.Exec.RefineSynth.IdPayload
