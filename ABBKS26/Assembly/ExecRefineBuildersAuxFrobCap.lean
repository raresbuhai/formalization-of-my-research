module

public import ABBKS26.Assembly.ExecRefineBuildersAuxFrobRound

/-! Coefficient bounds from a quantitative lower covariance bound. -/

@[expose] public section

namespace ABBKS26.Assembly.Exec.RefineSynth.FrobCap

open Common _root_.ABBKS26.Tree Matrix Sources Builders
open scoped BigOperators

private theorem trace_square {d : ℕ} (A : Mat d) (hA : Aᵀ = A) :
    (A * A).trace = frobSq A := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, frobSq]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show A j i = A i j from congrFun (congrFun hA i) j, pow_two]

/-- A covariance bounded below controls every symmetric quadratic coefficient. -/
theorem trace_quadratic_lower {d : ℕ} (A S : Mat d) (hA : Aᵀ = A)
    (hS : S.PosSemidef) (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ v, c * sqnorm v ≤ qform S v) :
    c ^ 2 * frobSq A ≤ (A * S * A * S).trace := by
  have hdiff : (S - c • (1 : Mat d)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hself : IsSelfAdjoint c := by simp only [IsSelfAdjoint, star_trivial]
      exact hS.1.sub (Matrix.isHermitian_one.smul hself)
    · intro v
      simpa only [qform, sqnorm, sub_mulVec, smul_mulVec, one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul, star_trivial, sub_nonneg]
        using hlower v
  have hAA : (A * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have hASA : (A * S * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, hA] using
      hS.mul_mul_conjTranspose_same A
  have h₁ := Separation.trace_mul_le_trace_mul hdiff hASA
  have h₂ := Separation.trace_mul_le_trace_mul hdiff hAA
  simp only [smul_mul, one_mul, trace_smul, smul_eq_mul, trace_square A hA] at h₁ h₂
  have he : (A * S * A).trace = (S * (A * A)).trace := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [← he] at h₂
  calc
    _ = c * (c * frobSq A) := by ring
    _ ≤ c * (A * S * A).trace := mul_le_mul_of_nonneg_left h₂ hc
    _ ≤ (S * (A * S * A)).trace := h₁
    _ = _ := Matrix.trace_mul_comm _ _

private theorem entry_sq_le_frobSq {d : ℕ} (A : Mat d) (i j : Fin d) :
    A i j ^ 2 ≤ frobSq A := by
  exact (Finset.single_le_sum (fun a _ ↦ sq_nonneg (A i a)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ ↦
      Finset.sum_nonneg (fun b _ ↦ sq_nonneg (A a b))) (Finset.mem_univ i))

/-- One component with a known covariance floor suffices; a lower bound on every
component is unnecessary. The variance here is the genuine Gaussian variance. -/
theorem entries_of_variance {d : ℕ} (q : Statistic d) (hq : q.Aᵀ = q.A)
    (S : Mat d) (hS : S.PosSemidef) (c B : ℝ) (hc : 0 < c) (hB : 0 ≤ B)
    (hlower : ∀ v, c * sqnorm v ≤ qform S v)
    (hv : ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤ B ^ 2) :
    ∀ i j, |(q.A i j : ℝ)| ≤ B / c := by
  have hsym : (q.A.map (algebraMap ℚ ℝ))ᵀ = q.A.map (algebraMap ℚ ℝ) := by
    rw [← transpose_map, hq]
  have ht := trace_quadratic_lower _ S hsym hS c hc.le hlower
  rw [Variance.centered_variance_eq _ (FrobPure.pure_symmetric q hq) S hS] at hv
  have hv' : 2 * (q.A.map (algebraMap ℚ ℝ) * S *
      q.A.map (algebraMap ℚ ℝ) * S).trace ≤ B ^ 2 := by
    simpa [FrobPure.pure, qform] using hv
  intro i j
  have he := entry_sq_le_frobSq (q.A.map (algebraMap ℚ ℝ)) i j
  have he' := mul_le_mul_of_nonneg_left he (sq_nonneg c)
  have hf : 0 ≤ frobSq (q.A.map (algebraMap ℚ ℝ)) :=
    Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  have htrace : 0 ≤ (q.A.map (algebraMap ℚ ℝ) * S *
      q.A.map (algebraMap ℚ ℝ) * S).trace := by
    exact (mul_nonneg (sq_nonneg c) hf).trans ht
  have hsquare : (c * |(q.A i j : ℝ)|) ^ 2 ≤ B ^ 2 := by
    change c ^ 2 * (q.A i j : ℝ) ^ 2 ≤ _ at he'
    nlinarith only [he', ht, hv', htrace, sq_abs (q.A i j : ℝ)]
  have hprod := (sq_le_sq₀ (mul_nonneg hc.le (abs_nonneg _)) hB).mp hsquare
  exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hprod)


/-- Express the sufficient covariance floor directly at the chosen coefficient cap. -/
theorem entries_of_scaled_floor {d : ℕ} (q : Statistic d) (hq : q.Aᵀ = q.A)
    (S : Mat d) (hS : S.PosSemidef) (b : ℕ) (B : ℝ) (hB : 0 < B)
    (hlower : ∀ v, (B / (2 : ℝ) ^ b) * sqnorm v ≤ qform S v)
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hv : ProbabilityTheory.variance
      (fun y : EuclideanSpace ℝ (Fin d) ↦ (FrobPure.pure q).eval y.ofLp)
      (ProbabilityTheory.multivariateGaussian 0 S) ≤ B ^ 2) :
    ∀ i j, |s * q.A i j| ≤ (2 : ℚ) ^ b := by
  have hb := entries_of_variance q hq S hS (B / (2 : ℝ) ^ b) B
    (by positivity) hB.le hlower hv
  have heq : B / (B / (2 : ℝ) ^ b) = (2 : ℝ) ^ b := by field_simp
  intro i j
  have heQ : |q.A i j| ≤ (2 : ℚ) ^ b := by
    exact_mod_cast heq ▸ hb i j
  rw [abs_mul, abs_of_nonneg hs]
  exact (mul_le_of_le_one_left (abs_nonneg _) hs1).trans heQ

/-- A precise sufficient condition for capping every eligible certificate. The exponent
must depend on the encoded data rather than the unknown population covariance. -/
def PreparedFloor (b : Args → ℕ) : Prop :=
  ∀ {n d} k ps (x : Fin n → Fin d → ℚ) fuel h N,
    ∀ (M : Mixture k d) ε w η Δ D (ω : Fin n → Triple k d) r (I : Finset (Fin k)),
      x = (fun l i ↦ r ((ω l).1, (ω l).2.2) i) →
      Prepared .centered M ε w η Δ D ω r ps →
      localBudget .centered k n d ps ≤ fuel → h < k - 1 → I.Nonempty →
      leakage ω N I ≤ leakageBudget ps η h → w * n / 4 ≤ N.card →
      ∃ j ∈ I, ∀ v,
        ((40 / ((ps h).w : ℝ)) / (2 : ℝ) ^ b (args k ps x h N, fuel)) * sqnorm v ≤
          qform (M.S j) v

/-- The covariance-floor obligation pays for the cap independently of which specified
frame produced the eligible certificate and independently of its output bit length. -/
theorem prepared_entries {n k d : ℕ} (F : FrameCode) (hF : FrameSpec F)
    (b : Args → ℕ) (hb : PreparedFloor b)
    (ps : ℕ → StepParams) (x : Fin n → Fin d → ℚ) (fuel h : ℕ) (N : Finset (Fin n))
    (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ) (ω : Fin n → Triple k d)
    (r : Rounding k d) (I : Finset (Fin k)) (hI : I.Nonempty)
    (hx : x = fun l i ↦ r ((ω l).1, (ω l).2.2) i)
    (hp : Prepared .centered M ε w η Δ D ω r ps)
    (hf : localBudget .centered k n d ps ≤ fuel) (hh : h < k - 1)
    (hl : leakage ω N I ≤ leakageBudget ps η h) (hN : w * n / 4 ≤ N.card)
    (s : ℚ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (q : Statistic d)
    (hq : (q, true) ∈ FrobPure.pool F (ps h) x fuel N) :
    ∀ i j, |s * q.A i j| ≤ (2 : ℚ) ^ b (args k ps x h N, fuel) := by
  obtain ⟨j, hj, hfloor⟩ := hb k ps x fuel h N M ε w η Δ D ω r I hx hp hf hh hI hl hN
  have hsym := FrobRound.pool_symmetric F hF (ps h) x fuel N q hq
  have hv := FrobPure.prepared_variance F hF ps x fuel h N M ε w η Δ D ω r I hI
    hx hp hf hh hl hN q hq j hj
  rw [hp.2.1 j, WithLp.toLp_zero] at hv
  have hv' := (FrobPure.variance_le q hsym (M.S j) (hp.1.posDef j).posSemidef).trans hv
  have hw : (0 : ℝ) < (ps h).w := by
    exact_mod_cast (hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h hh).1
  exact entries_of_scaled_floor q hsym (M.S j) (hp.1.posDef j).posSemidef
    (b (args k ps x h N, fuel)) (40 / ((ps h).w : ℝ)) (by positivity)
      hfloor s hs hs1 hv'

end ABBKS26.Assembly.Exec.RefineSynth.FrobCap
