module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdGeometry
public import ABBKS26.Assembly.ExecRefineBuildersAuxSpecDirection

/-! Affine rounding errors and sample bounds in the common-covariance branch. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdAffine

open Common Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders
open scoped BigOperators

noncomputable section

variable {n k d : ℕ}

def rounded (p b : ℕ) (q : Statistic d) : Statistic d :=
  ⟨0, SpecDirection.rounded p b q.b, FrobRound.entry p b 1 q.c⟩

theorem decoded (p b : ℕ) (q : StatisticL) :
    statisticOf d (IdLinear.run d p b q) = rounded p b (statisticOf d q) :=
  IdLinear.decoded d p b q

theorem entry_error (p b : ℕ) (q : ℚ) (hq : |q| ≤ (2 : ℚ) ^ b) :
    |(FrobRound.entry p b 1 q : ℝ) - q| ≤ 1 / (2 : ℝ) ^ p := by
  have he := FrobRound.entry_error p b 1 q (by simpa only [one_mul] using hq)
  have heR := Rat.cast_mono (K := ℝ) he
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_one, one_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using heR

theorem integral (q : Statistic d) (hA : q.A = 0) (μ : Vec d) (S : Mat d) :
    (∫ y : EuclideanSpace ℝ (Fin d), q.eval y.ofLp
      ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 μ) S) = q.eval μ := by
  let b : Vec d := fun i ↦ (q.b i : ℝ)
  have hint : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin d) ↦ b ⬝ᵥ y.ofLp)
      (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 μ) S) :=
    (Population.memLp_dotProduct_multivariateGaussian b 1 (by norm_num)).integrable
      (by norm_num)
  have he (y : Vec d) : q.eval y = b ⬝ᵥ y + q.c := by
    simp [Statistic.eval, hA, qform, b]
  simp_rw [he]
  rw [MeasureTheory.integral_add hint (MeasureTheory.integrable_const _),
    Population.integral_dotProduct_multivariateGaussian]
  simp

/-- The constant coefficient is rounded too, so this estimate controls actual affine
means rather than just differences between component means. -/
theorem eval_error (p b : ℕ) (q : Statistic d) (μ : Vec d) (X : ℝ)
    (hA : q.A = 0) (hb : ∀ i, |q.b i| ≤ (2 : ℚ) ^ b)
    (hc : |q.c| ≤ (2 : ℚ) ^ b) (hμ : ∀ i, |μ i| ≤ X) :
    |(rounded p b q).eval μ - q.eval μ| ≤
      ((d : ℝ) * X + 1) / (2 : ℝ) ^ p := by
  have he (i : Fin d) :
      |(SpecDirection.rounded p b q.b i : ℝ) - q.b i| ≤ 1 / (2 : ℝ) ^ p :=
    entry_error p b (q.b i) (hb i)
  have hec := entry_error p b q.c hc
  have hdiff : (rounded p b q).eval μ - q.eval μ =
      (∑ i, ((SpecDirection.rounded p b q.b i : ℝ) - q.b i) * μ i) +
        ((FrobRound.entry p b 1 q.c : ℝ) - q.c) := by
    simp only [Statistic.eval, rounded, hA, dotProduct, Finset.sum_sub_distrib, sub_mul]
    ring
  rw [hdiff]
  calc
    _ ≤ (∑ i, |((SpecDirection.rounded p b q.b i : ℝ) - q.b i) * μ i|) +
        |(FrobRound.entry p b 1 q.c : ℝ) - q.c| :=
      (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl)
    _ ≤ (∑ _i : Fin d, (1 / (2 : ℝ) ^ p) * X) + 1 / (2 : ℝ) ^ p := by
      apply add_le_add _ hec
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (he i) (hμ i) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

/-- The compatibility facts needed for sample bounds do not require centered means. -/
theorem compatible (ps : ℕ → StepParams) (h : ℕ) (P : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hp : Prepared .identical M ε w η Δ D ω r ps) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    let R := ABBKS26.RefineAux.roundedReference M ω r P I hI
    R.Valid (((ps h).w / 2 : ℚ) : ℝ) ∧ R.Resilient 4 (1 / 10000) ∧
      (((ps h).w / 2 : ℚ) : ℝ) ≤ 1 ∧
      R.contamination ≤ Robust.maxContamination (((ps h).w / 2 : ℚ) : ℝ)
        (|(ps h).R| : ℚ) := by
  let p := ps h
  let R := ABBKS26.RefineAux.roundedReference M ω r P I hI
  have hw := hp.weight_at .identical M ε w η Δ D ω r ps h (by omega)
  have hv := hp.reference_valid_at .identical M ε w η Δ D ω r ps P I hI
  have hr := hp.reference_resilient_at .identical M ε w η Δ D ω r ps P I hI 4
    (by omega) ((by omega : 4 ≤ 8).trans
      (hp.eight_le_degree .identical M ε w η Δ D ω r ps)) (by decide)
  have hc := hp.contamination_at .identical M ε w η Δ D ω r ps h (by omega)
    P I hI hl hP
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨_, hw2, _, _, _, _, _, _, _, _, _, _, hσ, hreq, _⟩ := hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_ofNat, hw] using hv
  · apply ABBKS26.RefineAux.resilient_tolerance_mono R 4 _ _ hr
    linarith only [hp.2.2.2.2.2.2.2.1]
  · have hπ : (ps h).w / 2 ≤ 1 := by linarith only [hw2]
    exact_mod_cast hπ
  · apply hc.trans
    unfold Robust.maxContamination
    rw [ABBKS26.RefineAux.frame_sigmaSq p hσ]
    exact_mod_cast hreq.trans (min_le_left _ _)

/-- Identical-covariance components have the same sample-determined upper bound as the
centered components; centering is absent from the covariance comparison theorem. -/
theorem covariance_upper (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card) :
    ∀ j ∈ I, ∀ v, qform (M.S j) v ≤
      (FrobBounds.covBound (args k ps x h P, fuel) : ℝ) * sqnorm v := by
  classical
  let R := ABBKS26.RefineAux.roundedReference M ω r P I hI
  obtain ⟨hv, hr, hπ, hc⟩ := compatible ps h P M ε w η Δ D ω r I hI hp hh hl hP
  have hw : (0 : ℝ) < (ps h).w := by
    exact_mod_cast (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh).1
  intro j hj v
  have hj' : j ∈ Set.range (I.orderEmbOfFin rfl) := by
    rw [I.range_orderEmbOfFin]
    exact hj
  obtain ⟨a, rfl⟩ := hj'
  have hb := ABBKS26.RefineAux.component_cov_le_observed R _ _ hv hr hπ hc a v
  have ho := FrobBounds.observedCov_upper (fun l i ↦ (x l i : ℝ)) P
    ((2 : ℝ) ^ (encPoints (pointsOf x)).length) (by positivity)
    (fun l _ i ↦ FrobBounds.sample_entry x l i) v
  have hobs : R.observed = fun l i ↦ (x l i : ℝ) := by rw [hx]; rfl
  rw [hobs] at hb
  change (((ps h).w / 2 : ℚ) : ℝ) * qform (M.S _) v ≤
    2 * qform (ABBKS26.RefineAux.observedCov (fun l i ↦ (x l i : ℝ)) P) v at hb
  push_cast at hb
  change (ps h).w / 2 * qform (M.S ((I.orderEmbOfFin rfl) a)) v ≤ _ at hb
  rw [FrobBounds.covBound_agrees k ps x fuel h P (by omega)]
  rw [div_mul_eq_mul_div, le_div_iff₀ hw]
  nlinarith only [hb, ho]

theorem covariance_error (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ)
    (fuel h : ℕ) (P : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (v : Fin d → ℚ)
    (hv : ∀ i, |v i| ≤ (2 : ℚ) ^ IdGuard.exponent (args k ps x h P, fuel)) :
    let a := (args k ps x h P, fuel)
    ∀ j ∈ I, qform (M.S j)
      ((fun i ↦ (SpecDirection.rounded (IdGuard.precision a)
        (IdGuard.exponent a) v i : ℝ)) - fun i ↦ (v i : ℝ)) ≤
          ((ps h).subspaceAccuracy : ℝ) ^ 2 / 16 := by
  let a := (args k ps x h P, fuel)
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  have hβ : field a 10 = (ps h).subspaceAccuracy := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    rfl
  have hw : 0 < field a 0 := by
    rw [field_args _ _ _ _ _ _ (by omega)]
    exact hs.1
  have hc : (0 : ℝ) ≤ FrobBounds.covBound a := by
    have hcQ : 0 ≤ FrobBounds.covBound a := by unfold FrobBounds.covBound; positivity
    exact_mod_cast hcQ
  have hu := covariance_upper ps x fuel h P M ε w η Δ D ω r I hI hx hp hh hl hP
  dsimp only
  intro j hj
  apply (SpecDirection.covariance_error (IdGuard.precision a) (IdGuard.exponent a)
    v (M.S j) (FrobBounds.covBound a) hv hc (hu j hj)).trans
  have he := SpecDirection.precision_error a (by rw [hβ]; exact hs.2.2.1)
  change (FrobBounds.covBound a : ℝ) * d *
    (1 / (2 : ℝ) ^ IdGuard.precision a) ^ 2 ≤ (field a 10 : ℝ) ^ 2 / 16 at he
  rwa [hβ] at he

end

end ABBKS26.Assembly.Exec.RefineSynth.IdAffine
