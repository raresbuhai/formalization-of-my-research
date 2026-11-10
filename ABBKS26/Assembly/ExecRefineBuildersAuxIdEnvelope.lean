module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdFloor

/-! Prepared coefficient and population mean-error bounds for the affine SUB grid. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdEnvelope

open Common Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders
open scoped BigOperators

noncomputable section

variable {n k d : ℕ}

theorem mean_precision (a : Args) (X : ℝ)
    (hX : X ≤ (2 : ℝ) ^ (FrobScan.key a + 1)) :
    ((a.1.1 : ℝ) * X + 1) / (2 : ℝ) ^ IdGuard.precision a ≤ 1 / 100 := by
  let z := FrobScan.key a
  have hz : 64 ≤ z := (FrobScan.key_bounds a).1
  have hd : (a.1.1 : ℝ) ≤ (2 : ℝ) ^ z := by
    exact_mod_cast (FrobScan.key_bounds a).2.1.trans (Nat.lt_two_pow_self (n := z)).le
  have hp : 2 * z + 9 ≤ z ^ 3 := by
    have h2 : 2 * z + 9 ≤ z ^ 2 := by nlinarith only [hz]
    exact h2.trans (Nat.pow_le_pow_right (by omega) (by norm_num : 2 ≤ 3))
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  simp only [one_mul]
  calc
    _ ≤ ((2 : ℝ) ^ z * (2 : ℝ) ^ (z + 1) + 1) * 100 := by
      have hh := (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg a.1.1)).trans
        (mul_le_mul_of_nonneg_right hd (by positivity))
      exact mul_le_mul_of_nonneg_right (by linarith only [hh]) (by norm_num)
    _ ≤ (2 : ℝ) ^ (2 * z + 9) := by
      rw [show 2 * z + 9 = (z + (z + 1)) + 8 by omega]
      simp only [pow_add, pow_one]
      norm_num only [show (2 : ℝ) ^ 8 = 256 by norm_num]
      have hh : (1 : ℝ) ≤ ((2 : ℝ) ^ z) ^ 2 :=
        one_le_pow₀ (one_le_pow₀ (by norm_num))
      nlinarith only [hh]
    _ ≤ (2 : ℝ) ^ IdGuard.precision a := pow_le_pow_right₀ (by norm_num) hp

/-- Neither the raw coefficient cap nor the final mean-error bound needs an extra
prepared hypothesis. The rational sample supplies both through augmented Gram matrices. -/
theorem prepared (MC : MomentCode) (hMC : MomentSpec MC) (NC : NestedCode)
    (RC : RoundCode) : IdFinish.Envelope MC NC RC := by
  intro n d k ps x fuel h P M ε w η Δ D ω r I hx hp hf hh hI hl hP u hu
  classical
  let a := (args k ps x h P, fuel)
  let z := FrobScan.key a
  let R := ABBKS26.RefineAux.roundedReference M ω r P I hI
  let q := statisticOf d (IdProgram.statistic a u)
  let v : Vec d := fun i ↦ (vectorOf d u i : ℝ)
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hw : (0 : ℝ) < (ps h).w := by exact_mod_cast hs.1
  have hw2 : ((ps h).w : ℝ) ≤ 1 / 2 := by
    have hb := Rat.cast_le (K := ℝ) |>.mpr hs.2.1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hb
    exact hb
  have hβ : 0 < (ps h).subspaceAccuracy ∧ (ps h).subspaceAccuracy ≤ 1 / 100 :=
    ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hγ : ((ps h).isotropy : ℝ) ≤ 1 := by
    exact_mod_cast IdFrame.isotropy_le_one .identical k _ _ hs
  obtain ⟨hR, hres, hπ, he⟩ := IdAffine.compatible ps h P M ε w η Δ D ω r I hI
    hp hh hl hP
  have hobs : R.observed = fun l i ↦ (x l i : ℝ) := by rw [hx]; rfl
  have hxz : (encPoints (pointsOf x)).length ≤ z := (FrobScan.key_bounds a).2.2.2.1
  have hn : n ≤ z := by
    have hc := Rounding.RawAux.length_count (Encoding.encList Encoding.encRat) (pointsOf x)
    simpa only [pointsOf, List.length_ofFn] using hc.trans hxz
  have hscale : 40 / ((ps h).w : ℝ) ≤ (2 : ℝ) ^ (z + 6) := by
    have heq : field a 0 = (ps h).w := by
      rw [field_args _ _ _ _ _ _ (by omega)]; rfl
    simpa only [heq] using FrobScan.scale_bound a
  have hβf : IdFuel.accuracy a = (ps h).subspaceAccuracy :=
    IdFuel.fields k ps x fuel h P (by omega)
  have hnorm := (IdCoverage.norms (IdProgram.problem MC NC) IdNorms.normInput RC a
    (by rwa [hβf]) u hu).2
  rw [hβf] at hnorm
  have hnorm4 : sqnorm v ≤ 4 := by
    have hb : ((ps h).subspaceAccuracy : ℝ) ≤ 1 := by
      exact_mod_cast hβ.2.trans (by norm_num : (1 / 100 : ℚ) ≤ 1)
    have hb0 : (0 : ℝ) ≤ (ps h).subspaceAccuracy := by exact_mod_cast hβ.1.le
    apply hnorm.trans
    exact (pow_le_pow_left₀ (by linarith only [hb0]) (by linarith only [hb]) 2).trans_eq
      (by norm_num : (2 : ℝ) ^ 2 = 4)
  obtain ⟨S, hframe, hS, _⟩ := IdInput.prepared_certificate MC hMC ps x fuel h P
    M ε w η Δ D ω r I hI hx hp hf hh hl hP
  have hvar (j : Fin I.card) := ABBKS26.RefineAux.identical_covariance_le S.frame
    (((ps h).w / 2 : ℚ) : ℝ) (ps h).isotropy hS.1 hS.2.1 (fun _ _ ↦ rfl) j v
  have hmean (j : Fin I.card) := ABBKS26.RefineAux.projected_mean_bound S.frame
    (((ps h).w / 2 : ℚ) : ℝ) (ps h).isotropy hS.1 hS.2.1 j v
  have hqA : q.A = 0 := by
    dsimp only [q, a]
    rw [IdProgram.statistic_decoded ps x fuel h P (by omega)]
    rfl
  have heval (j : Fin I.card) : q.eval (R.model.mean j) = v ⬝ᵥ S.mean j := by
    dsimp only [q, a]
    rw [IdProgram.statistic_decoded ps x fuel h P (by omega),
      ABBKS26.RefineAux.meanStatistic_eval]
    exact congrArg (fun F : FrameModel I.card d ↦ v ⬝ᵥ F.mean j) hframe.symm
  have hm (j : Fin I.card) :
      ((fun i ↦ (q.b i : ℝ)) ⬝ᵥ R.model.mean j + q.c) ^ 2 +
        qform (R.model.cov j) (fun i ↦ (q.b i : ℝ)) ≤ 20 / ((ps h).w : ℝ) := by
    have hv := hvar j
    have hμ := hmean j
    change qform S.cov v ≤ (1 + ((ps h).isotropy : ℝ)) * sqnorm v at hv
    change (((ps h).w / 2 : ℚ) : ℝ) * (v ⬝ᵥ S.mean j) ^ 2 ≤
      (1 + ((ps h).isotropy : ℝ)) * sqnorm v at hμ
    push_cast at hμ
    have hv8 : qform S.cov v ≤ 8 := by
      nlinarith only [hv, mul_le_mul_of_nonneg_right hγ (DetRoundAux.sqnorm_nonneg v),
        hnorm4]
    have hμ8 : ((ps h).w : ℝ) * (v ⬝ᵥ S.mean j) ^ 2 ≤ 16 := by
      nlinarith only [hμ, mul_le_mul_of_nonneg_right hγ (DetRoundAux.sqnorm_nonneg v),
        hnorm4]
    have hpull := IdValidity.pullback ps x fuel h P (by omega) M ω r I hI
      S hframe u j
    change qform S.cov v = qform (R.model.cov j) (fun i ↦ (q.b i : ℝ)) at hpull
    have hev : (fun i ↦ (q.b i : ℝ)) ⬝ᵥ R.model.mean j + q.c =
        v ⬝ᵥ S.mean j := by
      rw [← heval]
      simp [Statistic.eval, hqA, qform]
    rw [hev, ← hpull, le_div_iff₀ hw]
    nlinarith only [hμ8, mul_le_mul_of_nonneg_right hv8 hw.le,
      mul_le_mul_of_nonneg_left hw2 (by norm_num : (0 : ℝ) ≤ 8)]
  let j : Fin I.card := ⟨0, Finset.card_pos.mpr hI⟩
  obtain ⟨hb, hc⟩ := IdFloor.coefficients R _ _ _ hR hres hπ he x hobs j z
    (FrobScan.key_bounds a).1 hn (FrobScan.key_bounds a).2.1 hxz hw hscale q.b q.c (hm j)
  refine ⟨hb, ?_⟩
  intro j hj
  have hj' : j ∈ Set.range (I.orderEmbOfFin rfl) := by
    rw [I.range_orderEmbOfFin]; exact hj
  obtain ⟨j', rfl⟩ := hj'
  have hμ (i : Fin d) : |M.μ (I.orderEmbOfFin rfl j') i| ≤ (2 : ℝ) ^ (z + 1) := by
    have hm := IdFloor.component_mean_bound R _ _ hR hres hπ he x hobs
      ((2 : ℝ) ^ z) (by positivity)
      (fun l i ↦ (FrobBounds.sample_entry x l i).trans
        (pow_le_pow_right₀ (by norm_num) hxz)) j' i
    simpa only [R, ABBKS26.RefineAux.roundedReference, ABBKS26.RefineAux.component,
      pow_succ, mul_comm] using hm
  exact (IdAffine.eval_error (IdGuard.precision a) (IdGuard.exponent a) q _
    ((2 : ℝ) ^ (z + 1)) hqA hb hc hμ).trans (mean_precision a _ le_rfl)

end

end ABBKS26.Assembly.Exec.RefineSynth.IdEnvelope
