module

public import BHSV25.BK.Basic
import BHSV25.BK.AintProof

/-!
# It Ain't Over Till It's Over

The analytic theorem behind the soundness of Bansal and Khot's long code test, in the form the
reduction uses (`BHSV25.BK.ItAintOver`): a `[0,1]`-valued table `g` on `{0,1}^R` of mean at most
`1/2` with small low-degree influences is rarely almost `1` on a random subcube. The subcube
`C_D(z)` fixes the coordinates outside `D` to `z`, and a coordinate is free (in `D`) when `a_j = 0`
for a uniform `a_j ∈ [M]`, so with probability `1/M` (`BHSV25.BK.mix`). The statement bounds the
`t`-th moment of the average of `g` on the subcube, which is how the `t` queries of the test use
it.

It follows (`BHSV25.BK.itAintOver_of_prob`) from Mossel, O'Donnell and Oleszkiewicz's "It Ain't
Over Till It's Over" [MOO10, Theorem 4.9] in the probability form `BHSV25.BK.ItAintOverProb`: the
average of `g` on `C_D(z)` is at least `1 - δ` with probability at most `ζ / 2` once the
influences are small, and `(1 - δ)^t ≤ ζ / 2` for large `t`. Bansal and Khot use the same
theorem. The probability form (`BHSV25.BK.itAintOverProb`) is proved in
`BHSV25/BK/AintProof.lean` (`BHSV25.BK.Aint.itAintOverProb_main`; route in `BHSV25/BK/README.md`,
Section 7): an invariance principle between the three-valued ensemble of the random subcube and
uniform signs, and reverse hypercontractivity on the cube.

Reference: E. Mossel, R. O'Donnell, K. Oleszkiewicz, *Noise stability of functions with low
influences: invariance and optimality*, Annals of Mathematics 171 (2010), Theorem 4.9.
-/

@[expose] public section

namespace BHSV25.BK

open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
open scoped BigOperators

/-- The point of the subcube `C_D(z)` read off `y`: `y` on the free coordinates
`D = {j : a_j = 0}` and `z` on the others. -/
def mix {R M : ℕ} (a : Fin R → Fin M) (z y : Cube (Fin R)) : Cube (Fin R) :=
  fun j ↦ if (a j : ℕ) = 0 then y j else z j

/-- **It Ain't Over Till It's Over**, in the moment form used by the reduction: for every `M ≥ 2`
and `ζ > 0` there are a degree `K`, an influence bound `τ > 0` and a number `t` of queries such
that every table `g : {0,1}^R → [0,1]` (any `R`) of mean at most `1/2` whose degree-`K` influences
in `2g - 1` are all below `τ` satisfies `E_{z,a} [(E_{y} g(mix a z y))^t] ≤ ζ`: the `t`-th moment
of the average of `g` on a random subcube with free coordinates of density `1/M`. -/
def ItAintOver : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ ζ : ℝ, 0 < ζ → ∃ K : ℕ, ∃ τ : ℝ, 0 < τ ∧ ∃ t : ℕ,
    ∀ (R : ℕ) (g : Cube (Fin R) → ℝ), (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (𝔼 x, g x) ≤ 1 / 2 →
      (∀ i, cutoffInfluence K i (fun x ↦ 2 * g x - 1) < τ) →
        (𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M, (𝔼 y : Cube (Fin R), g (mix a z y)) ^ t) ≤ ζ

/-- **It Ain't Over Till It's Over** [MOO10, Theorem 4.9], in the probability form: for every
`M ≥ 2` and `ζ > 0` there are `δ > 0`, a degree `K` and an influence bound `τ > 0` such that every
table `g : {0,1}^R → [0,1]` of mean at most `1/2` whose degree-`K` influences in `2g - 1` are all
below `τ` has average at least `1 - δ` on a random subcube (free coordinates of density `1/M`)
with probability at most `ζ`. -/
def ItAintOverProb : Prop :=
  ∀ M : ℕ, 2 ≤ M → ∀ ζ : ℝ, 0 < ζ → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∃ τ : ℝ, 0 < τ ∧
    ∀ (R : ℕ) (g : Cube (Fin R) → ℝ), (∀ x, 0 ≤ g x ∧ g x ≤ 1) → (𝔼 x, g x) ≤ 1 / 2 →
      (∀ i, cutoffInfluence K i (fun x ↦ 2 * g x - 1) < τ) →
        (𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M,
          ind (1 - δ ≤ 𝔼 y : Cube (Fin R), g (mix a z y))) ≤ ζ

/-- The moment form follows from the probability form: `F^t ≤ (1 - δ)^t + [F ≥ 1 - δ]` for
`F ∈ [0, 1]`, and `(1 - δ)^t ≤ ζ / 2` for large `t`. -/
theorem itAintOver_of_prob (h : ItAintOverProb) : ItAintOver := by
  intro M hM ζ hζ
  obtain ⟨δ, hδ, K, τ, hτ, hP⟩ := h M hM (ζ / 2) (by positivity)
  have hδ1 : 0 ≤ 1 - min δ 1 := by linarith [min_le_right δ 1]
  have hδ2 : 1 - min δ 1 < 1 := by linarith [lt_min hδ one_pos]
  obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (half_pos hζ) hδ2
  refine ⟨K, τ, hτ, t, fun R g hg hmean hinf ↦ ?_⟩
  have hM0 : Nonempty (Fin M) := ⟨⟨0, by omega⟩⟩
  have hpt : ∀ (z : Cube (Fin R)) (a : Fin R → Fin M),
      (𝔼 y : Cube (Fin R), g (mix a z y)) ^ t ≤
        (1 - min δ 1) ^ t + ind (1 - δ ≤ 𝔼 y : Cube (Fin R), g (mix a z y)) := by
    intro z a
    have hF0 : 0 ≤ 𝔼 y : Cube (Fin R), g (mix a z y) :=
      Finset.expect_nonneg fun y _ ↦ (hg _).1
    have hF1 : (𝔼 y : Cube (Fin R), g (mix a z y)) ≤ 1 :=
      Finset.expect_le Finset.univ_nonempty fun y _ ↦ (hg _).2
    have hp0 : 0 ≤ (1 - min δ 1) ^ t := pow_nonneg hδ1 t
    by_cases hc : 1 - δ ≤ 𝔼 y : Cube (Fin R), g (mix a z y)
    · rw [ind_of hc]
      linarith [pow_le_one₀ hF0 hF1 (n := t)]
    · rw [ind_of_not hc, add_zero]
      exact pow_le_pow_left₀ hF0 (by linarith [min_le_left δ 1]) t
  calc (𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M, (𝔼 y : Cube (Fin R), g (mix a z y)) ^ t)
      ≤ 𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M,
          ((1 - min δ 1) ^ t + ind (1 - δ ≤ 𝔼 y : Cube (Fin R), g (mix a z y))) :=
        Finset.expect_le_expect fun z _ ↦ Finset.expect_le_expect fun a _ ↦ hpt z a
    _ = (1 - min δ 1) ^ t + 𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M,
          ind (1 - δ ≤ 𝔼 y : Cube (Fin R), g (mix a z y)) := by
        simp only [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
    _ ≤ ζ / 2 + ζ / 2 := add_le_add ht.le (hP R g hg hmean hinf)
    _ = ζ := by ring

/-- **It Ain't Over Till It's Over** [MOO10, Theorem 4.9], in the probability form
`BHSV25.BK.ItAintOverProb` (`BHSV25.BK.Aint.itAintOverProb_main`). -/
theorem itAintOverProb : ItAintOverProb := Aint.itAintOverProb_main

/-- **It Ain't Over Till It's Over**, in the moment form `BHSV25.BK.ItAintOver`. -/
theorem itAintOver : ItAintOver := itAintOver_of_prob itAintOverProb

end BHSV25.BK
