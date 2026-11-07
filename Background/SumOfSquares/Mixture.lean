module

public import Background.SumOfSquares.PseudoExpectation

/-!
# Mixtures of pseudo-expectations

The mixture `(1 - t) Ẽ + t Ẽ'` of two pseudo-expectations is one
(`SoS.PseudoExpectation.mix`), and it satisfies a system up to the mixture of the errors
(`SoS.PseudoExpectation.ApproxSatisfies.mix`). Arguments by approximate optimality, like
maximal coverage [BKS23, Lemma 5.3], compare the output of the algorithm with such mixtures.
-/

@[expose] public section

namespace SoS.PseudoExpectation

open MvPolynomial

variable {σ : Type*} {ℓ : ℕ}

/-- The mixture `(1 - t) Ẽ + t Ẽ'`, for `0 ≤ t ≤ 1`. -/
noncomputable def mix (E E' : PseudoExpectation σ ℓ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    PseudoExpectation σ ℓ where
  toLinearMap := (1 - t) • E.toLinearMap + t • E'.toLinearMap
  map_one' := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [E.map_one', E'.map_one']
    ring
  map_mul_self_nonneg' f hf := by
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    have := E.map_mul_self_nonneg' f hf
    have := E'.map_mul_self_nonneg' f hf
    have : 0 ≤ 1 - t := by linarith
    positivity

theorem mix_apply (E E' : PseudoExpectation σ ℓ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (f : MvPolynomial σ ℝ) : mix E E' t h0 h1 f = (1 - t) * E f + t * E' f := rfl

/-- A mixture satisfies a system up to the mixture of the errors. -/
theorem ApproxSatisfies.mix {K : Type*} [Field K] [Algebra K ℝ] {A : System σ K}
    {E E' : PseudoExpectation σ ℓ} {η η' : ℝ} {r : ℕ} (hE : E.ApproxSatisfies A η r)
    (hE' : E'.ApproxSatisfies A η' r) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (mix E E' t h0 h1).ApproxSatisfies A ((1 - t) * η + t * η') r := by
  intro S h hh hdeg
  rw [mix_apply]
  have e1 := hE S h hh hdeg
  have e2 := hE' S h hh hdeg
  have : 0 ≤ 1 - t := by linarith
  have := mul_le_mul_of_nonneg_left e1 this
  have := mul_le_mul_of_nonneg_left e2 h0
  nlinarith

end SoS.PseudoExpectation
