module

public import ABBKS26.Tree.Sound
public import ABBKS26.Tree.CompleteAuxFrob
public import ABBKS26.Tree.CompleteAuxSpec

/-!
# Population completeness for supplied rational windows

The componentwise conclusions assemble into `BufferedComplete`. Window providers prove
scalar gap inequalities; no provider assumes a probability bound or empirical verification.
-/

@[expose] public section

namespace ABBKS26.Tree

noncomputable section

open Matrix Common MeasureTheory ProbabilityTheory

variable {n k d : ℕ}

/-- The two population bounds for one supplied component, window and buffer scale. -/
def PopulationComplete (M : Mixture k d) (j : Fin k) (p : StepParams)
    (e : Edge n d) (η s : ℝ) (left : Prop) [Decidable left] : Prop :=
  let ν := multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)
  ν.real {y | (e.lower : ℝ) - 2 * η * s ≤ e.statistic.eval y.ofLp ∧
    e.statistic.eval y.ofLp ≤ e.upper + 2 * η * s} ≤ p.tail ∧
  ν.real {y | if left then (e.threshold : ℝ) - 2 * η * s < e.statistic.eval y.ofLp
    else e.statistic.eval y.ofLp ≤ e.threshold + 2 * η * s} ≤ p.tail

/-- Explicit scalar gaps for the expanded window and the buffered wrong side. -/
def WindowGap (e : Edge n d) (c r η s : ℝ) (left : Prop) [Decidable left] : Prop :=
  (∀ x : ℝ, (e.lower : ℝ) - 2 * η * s ≤ x ∧ x ≤ e.upper + 2 * η * s →
    r ≤ |x - c|) ∧
  (∀ x : ℝ, (if left then (e.threshold : ℝ) - 2 * η * s < x
    else x ≤ e.threshold + 2 * η * s) → r ≤ |x - c|)

/-- Chebyshev completeness for any supplied statistic and rational window.
The window provider supplies only scalar separation inequalities, including its buffer. -/
theorem frob_complete (M : Mixture k d) (j : Fin k) (p : StepParams)
    (e : Edge n d) (c r V η s : ℝ) (left : Prop) [Decidable left]
    (hc : c = ∫ y : EuclideanSpace ℝ (Fin d), e.statistic.eval y.ofLp
      ∂multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
    (hr : 0 < r)
    (hvar : variance (fun y : EuclideanSpace ℝ (Fin d) ↦ e.statistic.eval y.ofLp)
      (multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j)) ≤ V)
    (htail : V / r ^ 2 ≤ p.tail) (hgap : WindowGap e c r η s left) :
    PopulationComplete M j p e η s left := by
  have ht := (CompleteAux.tail_bound _ _ (CompleteAux.statistic_memLp e.statistic _ _)
    c r V hc hr hvar).trans htail
  exact ⟨(measureReal_mono (fun y hy ↦ hgap.1 _ hy)).trans ht,
    (measureReal_mono (fun y hy ↦ hgap.2 _ hy)).trans ht⟩

/-- Affine completeness for a supplied direction and arbitrary rational window.
Fixed grids and rational-density providers use the same population argument. -/
theorem mean_complete (M : Mixture k d) (j : Fin k) (p : StepParams)
    (e : Edge n d) (c r V η s : ℝ) (left : Prop) [Decidable left]
    (hM : M.Valid) (hA : e.statistic.A = 0)
    (hc : c = ∫ y : EuclideanSpace ℝ (Fin d), e.statistic.eval y.ofLp
      ∂multivariateGaussian (WithLp.toLp 2 (M.μ j)) (M.S j))
    (hr : 0 < r)
    (hvar : qform (M.S j) (fun i ↦ (e.statistic.b i : ℝ)) ≤ V)
    (htail : V / r ^ 2 ≤ p.tail) (hgap : WindowGap e c r η s left) :
    PopulationComplete M j p e η s left := by
  apply frob_complete M j p e c r V η s left hc hr _ htail hgap
  rw [SoundAux.mean_variance M hM j e.statistic hA]
  exact hvar

/-- Spectral completeness for a supplied rational direction and window.
Low and high variance providers supply explicit inequalities; the Gaussian population
argument pays for the same rounding buffers as the executable squared statistic. -/
theorem spectral_complete (M : Mixture k d) (j : Fin k) (p : StepParams)
    (e : Edge n d) (u : Fin d → ℚ) (a b R η s : ℝ)
    (left : Prop) [Decidable left] (hM : M.Valid) (hcen : M.IsCentered)
    (hq : ∀ x, e.statistic.evalQ x = (u ⬝ᵥ x) ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hR : 1 ≤ R) (hη : 0 ≤ η) (_hs : 0 ≤ s)
    (hscale : s ^ 2 ≤ 2 * (qform (M.S j) (fun i ↦ (u i : ℝ))) ^ 2)
    (htail : 1 / R + 2 * Real.sqrt η ≤ p.tail)
    (hlow : left → qform (M.S j) (fun i ↦ (u i : ℝ)) ≤ (a / R) ^ 2)
    (hhigh : ¬ left → (b * R) ^ 2 ≤ qform (M.S j) (fun i ↦ (u i : ℝ)))
    (hgap : left → a ^ 2 + 4 * η * qform (M.S j) (fun i ↦ (u i : ℝ)) ≤ e.lower)
    (hlower : e.lower ≤ e.threshold) (hupper : e.threshold ≤ e.upper)
    (hbound : (e.upper : ℝ) ≤ b ^ 2) :
    PopulationComplete M j p e η s left := by
  let z : Vec d := fun i ↦ (u i : ℝ)
  let V := qform (M.S j) z
  have hV : 0 ≤ V := (hM.posDef j).posSemidef.dotProduct_mulVec_nonneg z
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have heval (x : Vec d) : e.statistic.eval x = (z ⬝ᵥ x) ^ 2 :=
    SoundAux.spectral_eval e.statistic u hq x
  have hsV : s ≤ 2 * V := by
    nlinarith only [hscale, _hs, hV, sq_nonneg (s - 2 * V)]
  have hbuffer : 2 * η * s ≤ 4 * η * V := by
    nlinarith only [mul_le_mul_of_nonneg_left hsV (by positivity : 0 ≤ 2 * η)]
  have hcenter : WithLp.toLp 2 (M.μ j) = (0 : EuclideanSpace ℝ (Fin d)) := by
    simp [hcen j]
  have hlowR : (e.lower : ℝ) ≤ e.threshold := by exact_mod_cast hlower
  have huppR : (e.threshold : ℝ) ≤ e.upper := by exact_mod_cast hupper
  by_cases hj : left
  · have hv := hlow hj
    have hgap' := hgap hj
    have htail0 : 1 / R ≤ (p.tail : ℝ) := by
      linarith only [htail, Real.sqrt_nonneg η]
    have hprob := (CompleteAux.square_small (M.S j) (hM.posDef j).posSemidef
      z a R ha hR hv).trans htail0
    constructor
    · rw [hcenter]
      apply le_trans (measureReal_mono (s₂ :=
        {y : EuclideanSpace ℝ (Fin d) | a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2}) ?_) hprob
      intro y hy
      change (e.lower : ℝ) - 2 * η * s ≤ e.statistic.eval y.ofLp ∧
        e.statistic.eval y.ofLp ≤ (e.upper : ℝ) + 2 * η * s at hy
      rw [heval] at hy
      change a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2
      linarith only [hy.1, hgap', hbuffer]
    · simp only [hj, ite_true]
      rw [hcenter]
      apply le_trans (measureReal_mono (s₂ :=
        {y : EuclideanSpace ℝ (Fin d) | a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2}) ?_) hprob
      intro y hy
      change (e.threshold : ℝ) - 2 * η * s < e.statistic.eval y.ofLp at hy
      rw [heval] at hy
      change a ^ 2 ≤ (z ⬝ᵥ y.ofLp) ^ 2
      linarith only [hy, hlowR, hgap', hbuffer]
  · have hv := hhigh hj
    have hV0 : 0 < V := (sq_pos_of_pos (mul_pos hb hR0)).trans_le hv
    let σ := Real.sqrt V
    let B := 1 / R + 2 * Real.sqrt η
    have hσ : 0 < σ := Real.sqrt_pos.mpr hV0
    have hσsq : σ ^ 2 = V := Real.sq_sqrt hV
    have hB : 0 < B := add_pos_of_pos_of_nonneg (by positivity) (by positivity)
    have hroot : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt hη
    have hnum : b ^ 2 ≤ V / R ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hR0)]
      simpa only [mul_pow] using hv
    have he : (σ * B) ^ 2 = V / R ^ 2 + 4 * V * Real.sqrt η / R + 4 * η * V := by
      dsimp only [B]
      rw [mul_pow, hσsq]
      field_simp
      nlinarith only [hroot]
    have hbound' : b ^ 2 + 4 * η * V ≤ (σ * B) ^ 2 := by
      rw [he]
      have hh : 0 ≤ 4 * V * Real.sqrt η / R := by positivity
      linarith only [hnum, hh]
    have hprob : (multivariateGaussian 0 (M.S j)).real
        {y | |z ⬝ᵥ y.ofLp| ≤ σ * B} ≤ p.tail := by
      have hh := Population.multivariateGaussian_abs_le_le_of_ge
        (hM.posDef j).posSemidef z hσ hB (by norm_num : (0 : ℝ) < 1)
        (by simpa only [mul_one, V, qform] using hσsq.le)
      exact (by simpa only [div_one] using hh :
        (multivariateGaussian 0 (M.S j)).real {y | |z ⬝ᵥ y.ofLp| ≤ σ * B} ≤ B).trans htail
    have hsub : {y : EuclideanSpace ℝ (Fin d) |
        e.statistic.eval y.ofLp ≤ (e.upper : ℝ) + 2 * η * s} ⊆
        {y | |z ⬝ᵥ y.ofLp| ≤ σ * B} := by
      intro y hy
      change e.statistic.eval y.ofLp ≤ (e.upper : ℝ) + 2 * η * s at hy
      rw [heval] at hy
      apply (sq_le_sq₀ (abs_nonneg _) (mul_pos hσ hB).le).mp
      rw [sq_abs]
      linarith only [hy, hbuffer, hbound', hbound]
    constructor
    · rw [hcenter]
      apply le_trans (measureReal_mono ?_) hprob
      intro y hy
      exact hsub hy.2
    · simp only [hj, ite_false]
      rw [hcenter]
      apply le_trans (measureReal_mono ?_) hprob
      intro y hy
      change e.statistic.eval y.ofLp ≤ (e.threshold : ℝ) + 2 * η * s at hy
      apply hsub
      change e.statistic.eval y.ofLp ≤ (e.upper : ℝ) + 2 * η * s
      linarith only [hy, huppR]

namespace RefineAux

/-- Completeness with the population buffers used by rounded window comparison. -/
def BufferedComplete (M : Mixture k d) (I J : Finset (Fin k)) (p : StepParams)
    (η : ℝ) (e : Edge n d) : Prop :=
  J ⊆ I ∧ J.Nonempty ∧ (I \ J).Nonempty ∧
    ∀ j ∈ I, ∀ C : SoundAux.CoordinateSpec M j e.statistic,
      PopulationComplete M j p e η C.s (j ∈ J)


end RefineAux

end

end ABBKS26.Tree
