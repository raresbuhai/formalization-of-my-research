module

public import BKS23.Model
public import Background.RandomGraph

/-!
# Random graphs

The probability theory of the model, on Mathlib's binomial random graph `G(V, p)`
(`SimpleGraph.binomialRandom`). The generic part (the coins on the pairs, the coupling for
monotonicity in `p`, the law of the cut, the characters) is in `Background/RandomGraph.lean`,
and its names are exported here as `BKS23.Random.*`.

* **The model's weights.** `BKS23.erdosRenyiProb p R` is the mass of `R` under `G(Fin n, p)`
  (`BKS23.Random.erdosRenyiProb_eq`), so the sums in `BKS23.successProb` are integrals.
* **The success probability.** `BKS23.successProb` is the expected success probability of the
  coins over `G(Fin n, p)` (`BKS23.Random.successProb_eq`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph

namespace BKS23.Random

export RandomGraph (Pair graphOf graphOf_adj graphOf_mono coins binomialRandom_eq_map_graphOf
  measurable_graphOf uniforms measurable_le_const map_volume_le coins_eq_map measurable_threshold
  binomialRandom_le_of_antitone cut measurable_cut cutLaw cutPair cutPair_injective
  map_cut_binomialRandom binomialRandom_cut_preimage mul_measureReal_le_integral chi integral_chi
  blockChar card_subtype_of_subset blockChar_eq_prod_univ blockLaw cutLaw_eq
  integral_blockChar_mul prob_biclique NoBiclique prob_not_noBiclique)

/-! ### The model's weights -/

/-- `erdosRenyiProb p R` is the mass of `R` under `G(Fin n, p)`. -/
theorem erdosRenyiProb_eq {n : ℕ} (p : I) (R : SimpleGraph (Fin n)) :
    erdosRenyiProb p R = (G(Fin n, p)).real {R} :=
  (RandomGraph.binomialRandom_real_singleton p R).symm

/-- Sums weighted by `erdosRenyiProb` are integrals over `G(Fin n, p)`. -/
theorem sum_erdosRenyiProb_mul {n : ℕ} (p : I) (f : SimpleGraph (Fin n) → ℝ) :
    ∑ R, erdosRenyiProb p R * f R = ∫ R, f R ∂G(Fin n, p) :=
  RandomGraph.sum_mass_mul p f

/-! ### The success probability -/

/-- **The graph.** `BKS23.successProb` is the expectation over `G(Fin n, p)` of the coins'
success probability. -/
theorem successProb_eq {n k : ℕ} (p : I) (S : Finset (Fin n)) (Adv : Adversary n)
    (A : Input × List Bool → Output) (T : ℕ → ℕ) (bound : ℝ) :
    successProb n k p S Adv A T bound =
      ∫ R, coinProb (T (encInput (input (Adv.graph S R) k)).length)
        (fun r ↦ Succeeds k (Adv.graph S R) S bound (A (input (Adv.graph S R) k, r)))
        ∂G(Fin n, p) :=
  sum_erdosRenyiProb_mul p _

end BKS23.Random
