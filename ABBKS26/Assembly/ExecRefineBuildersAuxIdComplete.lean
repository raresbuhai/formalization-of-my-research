module

public import ABBKS26.Assembly.ExecRefineBuildersAuxIdAffine

/-! Fixed mean-grid completeness after affine coefficient rounding. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.IdComplete

open Common Matrix Rounding
open _root_.ABBKS26.Tree Sources Builders

noncomputable section

variable {n k d : ℕ}

theorem mean_margins (I : Finset (Fin k)) (c c' : Fin k → ℝ) (B : ℝ)
    (hB : 1 ≤ B) (he : ∀ j ∈ I, |c' j - c j| ≤ 1 / 100)
    (hb : ∀ j ∈ I, |c j| ≤ 3 * B)
    (hs : ∃ a ∈ I, ∃ b ∈ I, 19 / 20 ≤ |c a - c b|) :
    (∀ j ∈ I, |c' j| ≤ 4 * B) ∧
      ∃ a ∈ I, ∃ b ∈ I, 9 / 10 ≤ |c' a - c' b| := by
  refine ⟨?_, ?_⟩
  · intro j hj
    have ht := abs_add_le (c' j - c j) (c j)
    rw [sub_add_cancel] at ht
    linarith only [ht, he j hj, hb j hj, hB]
  · obtain ⟨a, ha, b, hb, hs⟩ := hs
    have ht : |c a - c b| ≤ |c' a - c a| + |c' a - c' b| + |c' b - c b| := by
      calc
        _ ≤ |c a - c' a| + |c' a - c b| := abs_sub_le _ _ _
        _ ≤ |c a - c' a| + (|c' a - c' b| + |c' b - c b|) :=
          add_le_add le_rfl (abs_sub_le _ _ _)
        _ = _ := by rw [abs_sub_comm (c a) (c' a)]; ring
    exact ⟨a, ha, b, hb, by linarith only [ht, he a ha, he b hb, hs]⟩

/-- A bounded affine statistic with a population mean gap supplies an actual guarded
pair on the fixed additive grid. The guard never evaluates an empirical window test. -/
theorem separator (g : Args → IdGuard.Statistics)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (qL : StatisticL) (hqL : qL ∈ g (args k ps x h P, fuel))
    (c : Fin k → ℝ)
    (hc : let a := (args k ps x h P, fuel)
      let q := IdAffine.rounded (IdGuard.precision a) (IdGuard.exponent a)
        (statisticOf d qL)
      ∀ j ∈ I, c j = ∫ y : EuclideanSpace ℝ (Fin d), q.eval y.ofLp
        ∂ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
    (hv : let a := (args k ps x h P, fuel)
      let q := IdAffine.rounded (IdGuard.precision a) (IdGuard.exponent a)
        (statisticOf d qL)
      ∀ j ∈ I, ProbabilityTheory.variance
        (fun y : EuclideanSpace ℝ (Fin d) ↦ q.eval y.ofLp)
        (ProbabilityTheory.multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤
          9 * ((ps h).subspaceAccuracy : ℝ) ^ 2)
    (hb : ∀ j ∈ I, |c j| ≤ 4 * (sqrtUp (1 / (ps h).w) : ℝ))
    (hgap : ∃ a ∈ I, ∃ b ∈ I, 9 / 10 ≤ |c a - c b|) :
    ∃ q ∈ (IdGuard.run g (args k ps x h P, fuel)).1.map (statisticOf d),
      ∃ t ∈ (IdGuard.run g (args k ps x h P, fuel)).2,
        Verify (ps h) x (pairEdge .identical h P q t) := by
  let a := (args k ps x h P, fuel)
  let p := ps h
  let q := IdAffine.rounded (IdGuard.precision a) (IdGuard.exponent a)
    (statisticOf d qL)
  have hs := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh
  obtain ⟨_, _, hβ, hβ100, hφ, _, _, _, _, _, _, _, _, _, _, _, hm⟩ := hs
  have hmass : (p.windowMass : ℝ) =
      (1 / (16 * k : ℝ)) * (p.straddle / 2) ^ 9 / 16 := by
    have he := congrArg (fun t : ℚ ↦ (t : ℝ)) hm.1
    push_cast at he ⊢
    exact he
  have hsound := (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h (by omega)).2.2.2.2.2.2 hh
  obtain ⟨_, _, hφ1, _, _, hηmass, _⟩ := hsound
  have hφle : (p.straddle : ℝ) ≤ 1 :=
    hφ1.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hφ0 : (0 : ℝ) ≤ p.straddle := by exact_mod_cast hφ.le
  have hpower : ((p.straddle : ℝ) / 2) ^ 9 ≤ 1 :=
    pow_le_one₀ (by positivity) (by linarith only [hφle])
  have hwidth : (0 : ℝ) ≤ 1 / (16 * k : ℝ) := by positivity
  have hmasswidth : (p.windowMass : ℝ) ≤ 1 / (16 * k : ℝ) := by
    rw [hmass]
    have he := mul_le_mul_of_nonneg_left hpower hwidth
    linarith only [he, hwidth]
  have hmargin : 4 * η ≤ 1 / (16 * k : ℝ) := by
    linarith only [hηmass, hmasswidth, hwidth]
  obtain ⟨t, ht, J, _, hpop⟩ := ABBKS26.RefineAux.meanGrid_complete M I p P q c η h
    hp.1 rfl ⟨hβ, hβ100⟩ hp.2.2.2.2.2.2.1.le hmargin hmass.le
    (by exact_mod_cast hm.2.2.1) hc hv hb hgap
  let win : Window := (t, t - 1 / (16 * k : ℚ), t + 1 / (16 * k : ℚ))
  have hrun : IdGuard.run g a =
      ((g a).map (IdLinear.run d (IdGuard.precision a) (IdGuard.exponent a)),
        IdWindows.run a) := by
    unfold IdGuard.run
    rw [ite_eq_left (show a.1.2.2.2.2.1 < a.1.2.1 by change h < k; omega)]
    rfl
  have hmem : q ∈ (IdGuard.run g a).1.map (statisticOf d) := by
    rw [hrun]
    apply List.mem_map.mpr
    refine ⟨_, List.mem_map.mpr ⟨qL, hqL, rfl⟩, ?_⟩
    exact IdAffine.decoded _ _ qL
  have hwin : win ∈ (IdGuard.run g a).2 := by
    rw [hrun]
    have hcap := (IdFuel.caps ps x fuel h P hf hh ⟨hβ, hβ100⟩).2.2.2
    rw [IdWindows.agrees k ps x fuel h P (by omega) hcap]
    exact List.mem_map.mpr ⟨t, ht, rfl⟩
  refine ⟨q, hmem, win, hwin, ?_⟩
  rw [hx]
  exact hp.verify_of_bufferedComplete .identical M ε w η Δ D ω r ps h hh
    (pairEdge .identical h P q win) I J hI hl hP hpop

/-- The stronger raw variance and mean margins pay for coefficient rounding before
invoking the fixed mean-grid separator theorem. -/
theorem rounded_separator (g : Args → IdGuard.Statistics)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ)
    (P : Finset (Fin n)) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .identical M ε w η Δ D ω r ps)
    (hf : localBudget .identical k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω P I ≤ leakageBudget ps η h) (hP : w * n / 4 ≤ P.card)
    (qL : StatisticL) (hqL : qL ∈ g (args k ps x h P, fuel))
    (hmag : ∀ i, |(statisticOf d qL).b i| ≤
      (2 : ℚ) ^ IdGuard.exponent (args k ps x h P, fuel))
    (hvar : ∀ j ∈ I, qform (M.S j) (fun i ↦ ((statisticOf d qL).b i : ℝ)) ≤
      61 / 10 * ((ps h).subspaceAccuracy : ℝ) ^ 2)
    (hbound : ∀ j ∈ I, |(statisticOf d qL).eval (M.μ j)| ≤
      3 * (sqrtUp (1 / (ps h).w) : ℝ))
    (hspread : ∃ a ∈ I, ∃ b ∈ I, 19 / 20 ≤
      |(statisticOf d qL).eval (M.μ a) - (statisticOf d qL).eval (M.μ b)|)
    (he : let a := (args k ps x h P, fuel)
      ∀ j ∈ I, |(IdAffine.rounded (IdGuard.precision a) (IdGuard.exponent a)
        (statisticOf d qL)).eval (M.μ j) - (statisticOf d qL).eval (M.μ j)| ≤ 1 / 100) :
    ∃ q ∈ (IdGuard.run g (args k ps x h P, fuel)).1.map (statisticOf d),
      ∃ t ∈ (IdGuard.run g (args k ps x h P, fuel)).2,
        Verify (ps h) x (pairEdge .identical h P q t) := by
  let a := (args k ps x h P, fuel)
  let q := IdAffine.rounded (IdGuard.precision a) (IdGuard.exponent a)
    (statisticOf d qL)
  let c : Fin k → ℝ := fun j ↦ (statisticOf d qL).eval (M.μ j)
  let c' : Fin k → ℝ := fun j ↦ q.eval (M.μ j)
  have hB : (1 : ℝ) ≤ sqrtUp (1 / (ps h).w) := by
    unfold sqrtUp
    exact_mod_cast (show 1 ≤ Nat.sqrt ⌈max 0 (1 / (ps h).w)⌉₊ + 1 by omega)
  obtain ⟨hbound', hspread'⟩ := mean_margins I c c' _ hB he hbound hspread
  apply separator g ps x fuel h P M ε w η Δ D ω r I hI hx hp hf hh hl hP
    qL hqL c' (fun j _ ↦ (IdAffine.integral q rfl (M.μ j) (M.S j)).symm)
    _ hbound' hspread'
  dsimp only
  intro j hj
  rw [SoundAux.mean_variance M hp.1 j q rfl]
  have herror := IdAffine.covariance_error ps x fuel h P M ε w η Δ D ω r I hI
    hx hp hh hl hP (statisticOf d qL).b hmag j hj
  exact IdGeometry.rounded_variance (M.S j) (hp.1.posDef j).posSemidef
    (ps h).subspaceAccuracy (fun i ↦ ((statisticOf d qL).b i : ℝ))
    (fun i ↦ (q.b i : ℝ)) (hvar j hj) herror

end

end ABBKS26.Assembly.Exec.RefineSynth.IdComplete
