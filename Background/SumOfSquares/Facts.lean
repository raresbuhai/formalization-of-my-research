module

public import Background.SumOfSquares.PseudoExpectation
public import Background.SumOfSquares.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Basic facts about pseudo-distributions

[BKS23, Facts 3.2–3.4]. Of Hölder's inequality (Fact 3.2), only the case `t = 2` is here.

* `SoS.PseudoExpectation.cauchy_schwarz`: the Cauchy–Schwarz inequality, Fact 3.2 for `t = 2`.
* `SoS.PseudoExpectation.reweight`: reweighting by a sum of squares (Fact 3.3).
* `SoS.PseudoExpectation.Satisfies.apply_proof`, `SoS.PseudoExpectation.Satisfies.of_entails`:
  soundness (Fact 3.4), assuming `r ≤ ℓ`.

Fact 3.6, efficient optimization over pseudo-distributions, is stated in
`Background/SumOfSquares/Solver.lean`.
-/

@[expose] public section

namespace SoS

namespace PseudoExpectation

open MvPolynomial

variable {σ K : Type*} [Field K] [Algebra K ℝ] {ℓ : ℕ}

/-- The Cauchy–Schwarz inequality for pseudo-expectations, the case `t = 2` of [BKS23, Fact 3.2]. -/
theorem cauchy_schwarz {d : ℕ} (E : PseudoExpectation σ (2 * d)) {f g : MvPolynomial σ ℝ}
    (hf : f.totalDegree ≤ d) (hg : g.totalDegree ≤ d) :
    E (f * g) ≤ Real.sqrt (E (f ^ 2)) * Real.sqrt (E (g ^ 2)) := by
  -- `t ↦ Ẽ[(t f - g)²] = Ẽ[f²] t² - 2 Ẽ[f g] t + Ẽ[g²]` is nonnegative, so its discriminant
  -- `4 Ẽ[f g]² - 4 Ẽ[f²] Ẽ[g²]` is not positive.
  have hquad : ∀ t : ℝ, 0 ≤ E (f ^ 2) * (t * t) + (-2 * E (f * g)) * t + E (g ^ 2) := by
    intro t
    have hdeg : (C t * f - g).totalDegree ≤ d := by
      refine (totalDegree_sub _ _).trans (max_le ?_ hg)
      exact (totalDegree_mul _ _).trans (by simpa [totalDegree_C] using hf)
    have hnn := E.map_mul_self_nonneg (f := C t * f - g) (by omega)
    have hexp : (C t * f - g) * (C t * f - g) =
        C (t * t) * f ^ 2 - (C t * (f * g) + C t * (f * g)) + g ^ 2 := by
      rw [map_mul]
      ring
    rw [hexp, map_add, map_sub, map_add, map_C_mul, map_C_mul] at hnn
    linarith
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  have hf2 : 0 ≤ E (f ^ 2) := by
    rw [sq]
    exact E.map_mul_self_nonneg (by omega)
  have hc : E (f * g) ^ 2 ≤ E (f ^ 2) * E (g ^ 2) := by nlinarith
  rw [← Real.sqrt_mul hf2]
  calc E (f * g) ≤ |E (f * g)| := le_abs_self _
    _ = Real.sqrt (E (f * g) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (E (f ^ 2) * E (g ^ 2)) := Real.sqrt_le_sqrt hc

/-- If `p` is a sum of squares of degree at most `t ≤ k` and `Ẽ p ≠ 0`, then `Ẽ p > 0`. -/
theorem pos_of_isSumSq {k t : ℕ} (E : PseudoExpectation σ k) {p : MvPolynomial σ ℝ}
    (hp : IsSumSq p) (hdeg : p.totalDegree ≤ t) (htk : t ≤ k) (hE : E p ≠ 0) : 0 < E p :=
  lt_of_le_of_ne (E.nonneg_of_isSumSq hp (hdeg.trans htk)) (Ne.symm hE)

/-- **Fact 3.3** (reweighting [BKS17]): for a sum of squares `p` of degree at most `t ≤ k` with
`Ẽ p ≠ 0`, the functional `f ↦ Ẽ[p f] / Ẽ[p]` is a pseudo-expectation of degree `k - t`. -/
noncomputable def reweight {k : ℕ} (E : PseudoExpectation σ k) (t : ℕ) (p : MvPolynomial σ ℝ)
    (hp : IsSumSq p) (hdeg : p.totalDegree ≤ t) (htk : t ≤ k) (hE : E p ≠ 0) :
    PseudoExpectation σ (k - t) where
  toLinearMap := (E p)⁻¹ • (E.toLinearMap ∘ₗ LinearMap.mulLeft ℝ p)
  map_one' := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one,
      smul_eq_mul]
    exact inv_mul_cancel₀ hE
  map_mul_self_nonneg' f hf := by
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, smul_eq_mul]
    refine mul_nonneg (inv_nonneg.2 (E.pos_of_isSumSq hp hdeg htk hE).le) ?_
    refine E.nonneg_of_isSumSq (hp.mul (IsSumSq.mul_self f)) ?_
    refine (totalDegree_mul _ _).trans ?_
    have := totalDegree_mul f f
    omega

theorem reweight_apply {k : ℕ} (E : PseudoExpectation σ k) (t : ℕ) (p : MvPolynomial σ ℝ)
    (hp : IsSumSq p) (hdeg : p.totalDegree ≤ t) (htk : t ≤ k) (hE : E p ≠ 0)
    (f : MvPolynomial σ ℝ) :
    E.reweight t p hp hdeg htk hE f = E (p * f) / E p := by
  change (E p)⁻¹ * E (p * f) = _
  rw [div_eq_inv_mul]

/-- **Fact 3.3**, continued: the reweighting still satisfies every system that `Ẽ` satisfies, at
the same degree `r`. -/
theorem Satisfies.reweight {k : ℕ} {E : PseudoExpectation σ k} {t : ℕ} {p : MvPolynomial σ ℝ}
    {hp : IsSumSq p} {hdeg : p.totalDegree ≤ t} {htk : t ≤ k} {hE : E p ≠ 0} {A : System σ K}
    {r : ℕ} (hA : E.Satisfies A r) : (E.reweight t p hp hdeg htk hE).Satisfies A r := by
  intro S h hh hdeg'
  rw [reweight_apply, ← mul_assoc]
  refine div_nonneg (hA S (p * h) (hp.mul hh) ?_) (E.pos_of_isSumSq hp hdeg htk hE).le
  have := totalDegree_mul p h
  omega

/-- If `Ẽ` satisfies `A` at a degree `r ≤ ℓ`, every constant constraint of `A` is a nonnegative
constant. -/
theorem Satisfies.toReal_eq_C_of_totalDegree_eq_zero {E : PseudoExpectation σ ℓ} {A : System σ K}
    {r : ℕ} (hr : r ≤ ℓ) (hA : E.Satisfies A r) {i : Fin A.length}
    (hi : (A.get i).totalDegree = 0) :
    ∃ a : ℝ, 0 ≤ a ∧ toReal (A.get i) = C a := by
  have hC : toReal (A.get i) = C (algebraMap K ℝ ((A.get i).coeff 0)) := by
    conv_lhs => rw [totalDegree_eq_zero_iff_eq_C.1 hi]
    simp [toReal]
  refine ⟨_, ?_, hC⟩
  have h := hA {i} 1 IsSumSq.one (by rw [Finset.sum_singleton, hi]; simpa using hr)
  rwa [one_mul, System.prod, Finset.prod_singleton, hC, E.map_C] at h

/-- The heart of soundness: if `Ẽ` satisfies `A` at a degree `r ≤ ℓ`, then
`Ẽ (h ∏ i ∈ S, fᵢ) ≥ 0` for every sum of squares `h` such that `deg h` plus the sum of
`max (deg fᵢ) r` over the *nonconstant* constraints in `S` is at most `ℓ`. The constant
constraints are nonnegative constants, which factor out. -/
theorem Satisfies.apply_prod {E : PseudoExpectation σ ℓ} {A : System σ K} {r : ℕ} (hr : r ≤ ℓ)
    (hA : E.Satisfies A r) (S : Finset (Fin A.length)) {h : MvPolynomial σ ℝ} (hh : IsSumSq h)
    (hdeg : h.totalDegree +
      ∑ i ∈ S with (A.get i).totalDegree ≠ 0, max (A.get i).totalDegree r ≤ ℓ) :
    0 ≤ E (h * toReal (A.prod S)) := by
  classical
  -- A set of constant constraints multiplies to a nonnegative constant.
  have hconst : ∀ T : Finset (Fin A.length), (∀ i ∈ T, (A.get i).totalDegree = 0) →
      ∃ a : ℝ, 0 ≤ a ∧ toReal (A.prod T) = C a := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => exact ⟨1, zero_le_one, by simp⟩
    | insert j T hj ih =>
      obtain ⟨a, ha, hTa⟩ := ih fun i hi ↦ hT i (Finset.mem_insert_of_mem hi)
      obtain ⟨b, hb, hjb⟩ :=
        hA.toReal_eq_C_of_totalDegree_eq_zero hr (hT j (Finset.mem_insert_self j T))
      refine ⟨b * a, mul_nonneg hb ha, ?_⟩
      have : A.prod (insert j T) = A.get j * A.prod T := Finset.prod_insert hj
      rw [this, toReal_mul, hjb, hTa, C_mul]
  have hsplit : A.prod S = A.prod (S.filter fun i ↦ (A.get i).totalDegree = 0) *
      A.prod (S.filter fun i ↦ (A.get i).totalDegree ≠ 0) := by
    unfold System.prod
    exact (Finset.prod_filter_mul_prod_filter_not S (fun i ↦ (A.get i).totalDegree = 0) _).symm
  obtain ⟨a, ha, hca⟩ := hconst _ fun i hi ↦ (Finset.mem_filter.1 hi).2
  rw [hsplit, toReal_mul, hca, ← mul_assoc, mul_comm h (C a), mul_assoc, E.map_C_mul]
  exact mul_nonneg ha (hA _ h hh hdeg)

/-- Soundness for one derived polynomial: if `Ẽ` satisfies `A` at a degree `r ≤ ℓ` and
`A ⊢[k] g`, then `Ẽ (h g) ≥ 0` for every sum of squares `h` with `deg h + r k + k ≤ ℓ`. -/
theorem Satisfies.apply_proof {E : PseudoExpectation σ ℓ} {A : System σ K} {r : ℕ} (hr : r ≤ ℓ)
    (hA : E.Satisfies A r) {g : MvPolynomial σ K} {k : ℕ} (P : Proof A g k)
    (h : MvPolynomial σ ℝ) (hh : IsSumSq h) (hdeg : h.totalDegree + (r * k + k) ≤ ℓ) :
    0 ≤ E (h * toReal g) := by
  classical
  rw [P.eq_sum, toReal_sum, Finset.mul_sum, E.map_sum]
  refine Finset.sum_nonneg fun S _ ↦ ?_
  by_cases hS : P.mult S = 0
  · simp [hS]
  rw [toReal_mul, ← mul_assoc]
  refine hA.apply_prod hr S (hh.mul (P.isSOS_mult S)) ?_
  -- Each nonconstant constraint has degree at least `1`, so there are at most `k` of them in `S`.
  have hP := P.degree_le S hS
  have hm := totalDegree_toReal_le (P.mult S)
  have hmul := totalDegree_mul h (toReal (P.mult S))
  set S₁ := S.filter fun i ↦ (A.get i).totalDegree ≠ 0
  have h₁ : ∑ i ∈ S₁, max (A.get i).totalDegree r ≤ ∑ i ∈ S₁, ((A.get i).totalDegree + r) :=
    Finset.sum_le_sum fun i _ ↦ max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at h₁
  have h₂ : S₁.card ≤ ∑ i ∈ S₁, (A.get i).totalDegree := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun i hi ↦ Nat.one_le_iff_ne_zero.2 (Finset.mem_filter.1 hi).2
  have h₃ : ∑ i ∈ S₁, (A.get i).totalDegree ≤ A.degree S :=
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h₄ : S₁.card * r ≤ k * r := Nat.mul_le_mul_right r (by omega)
  have : r * k = k * r := Nat.mul_comm r k
  omega

/-- **Fact 3.4** (soundness): if `Ẽ` satisfies `A` at degree `r` and every constraint of `B` has a
degree-`r'` proof from `A`, then `Ẽ` satisfies `B` at degree `r r' + r'`.

It assumes `r ≤ ℓ`, so that satisfying `A` at degree `r` constrains `Ẽ`. -/
theorem Satisfies.of_entails {E : PseudoExpectation σ ℓ} {A B : System σ K} {r r' : ℕ}
    (hr : r ≤ ℓ) (hA : E.Satisfies A r) (hAB : A.Entails B r') :
    E.Satisfies B (r * r' + r') := by
  intro T h hh hdeg
  have hprod : Derives A (T.card * r') (B.prod T) :=
    Derives.prod T fun j _ ↦ hAB _ (List.get_mem B j)
  refine hA.apply_proof hr hprod.some h hh ?_
  have hsum : T.card * (r * r' + r') ≤ ∑ j ∈ T, max (B.get j).totalDegree (r * r' + r') := by
    rw [← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j _ ↦ le_max_right _ _
  have : r * (T.card * r') + T.card * r' = T.card * (r * r' + r') := by ring
  omega

end PseudoExpectation

/-!
## Fact 3.6: efficient optimization over pseudo-distributions

Specified in `Background/SumOfSquares/Solver.lean` and proved in
`Background/SumOfSquares/Algorithm/Correct.lean` (`SoS.Solver.exists_solver`), for multitape Turing
machines.
-/

end SoS
