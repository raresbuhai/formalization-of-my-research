module

public import BKS23.RandomCut
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Non-neighbours across the cut

What the refinement of [BKS23, Claim 5.9] needs from the random graph: every vertex outside the
planted set `U` has at least `(1 - q) |U| / 2` non-neighbours in `U`
(`BKS23.Random.NonNbrGE`). It fails under `G(V, q)` with probability at most
`|Uᶜ| exp(-(1 - q) |U| / 8)` (`BKS23.Random.prob_not_nonNbrGE`).

The number of non-neighbours of a vertex is a sum of independent `(1 - q)`-coins, and the bound is
the Chernoff bound for its lower tail at `t = -log 2`: `P(X ≤ β k / 2) ≤ 2^(βk/2) (1 - β/2)^k ≤
exp(-(1 - log 2) β k / 2)`. Hoeffding's inequality, used for the degrees in
`BKS23/RandomCut.lean`, does not suffice here: when `1 - q` is of order `n^(-1/2)` the deviation
`√(k log n)` it allows exceeds the mean `(1 - q) k`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph Finset Real

namespace BKS23.Random

variable {V : Type*} [DecidableEq V] [Fintype V] (U : Finset V)

open Classical in
/-- Every vertex outside `U` has at least `β |U| / 2` non-neighbours in `U`. -/
def NonNbrGE (β : ℝ) (R : SimpleGraph V) : Prop :=
  ∀ v ∈ Uᶜ, β * U.card / 2 ≤ ((U.filter fun u ↦ ¬ R.Adj u v).card : ℝ)

/-- The tails indicator of a coin: `1` for tails, `0` for heads. -/
noncomputable def tails (b : Prop) : ℝ := by
  classical
  exact if b then 0 else 1

theorem integral_exp_tails (q : I) (t : ℝ) :
    ∫ b, exp (t * tails b) ∂Ber(True, False, q) = q + (1 - q) * exp t := by
  rw [integral_bernoulliMeasure]
  simp [tails, smul_eq_mul]

omit [DecidableEq V] [Fintype V] in
/-- **The Chernoff bound for one vertex.** Under the law of a block of `q`-coins, fewer than
`(1 - q) |U| / 2` tails has probability at most `exp(-(1 - q) |U| / 8)`. -/
theorem blockLaw_tails_le (q : I) :
    (blockLaw V U q).real {x | ∑ w : {w // w ∈ U}, tails (x w) ≤ (1 - q) * U.card / 2} ≤
      exp (-((1 - q) * U.card / 8)) := by
  set β : ℝ := 1 - q with hβ
  have hβ0 : 0 ≤ β := by have := q.2.2; linarith
  set t : ℝ := -Real.log 2 with ht
  have ht0 : t ≤ 0 := by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hind : iIndepFun (fun (w : {w // w ∈ U}) (x : {w // w ∈ U} → Prop) ↦ tails (x w))
      (blockLaw V U q) :=
    iIndepFun_infinitePi (P := fun _ ↦ Ber(True, False, q)) (X := fun _ ↦ tails)
      fun _ ↦ Measurable.of_discrete
  have hmgf1 : ∀ w : {w // w ∈ U},
      mgf (fun x : {w // w ∈ U} → Prop ↦ tails (x w)) (blockLaw V U q) t = 1 - β / 2 := by
    intro w
    have hmap : (blockLaw V U q).map (fun x : {w // w ∈ U} → Prop ↦ x w) = Ber(True, False, q) :=
      Measure.infinitePi_map_eval _ w
    have hint := integral_map (μ := blockLaw V U q) (φ := fun x : {w // w ∈ U} → Prop ↦ x w)
      (f := fun b : Prop ↦ exp (t * tails b)) (measurable_pi_apply w).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable
    rw [hmap, integral_exp_tails] at hint
    change ∫ x, exp (t * tails (x w)) ∂(blockLaw V U q) = _
    rw [← hint, ht, Real.exp_neg, Real.exp_log (by norm_num), hβ]
    ring
  have hmgf : mgf (fun x : {w // w ∈ U} → Prop ↦ ∑ w : {w // w ∈ U}, tails (x w))
      (blockLaw V U q) t = (1 - β / 2) ^ U.card := by
    have h := hind.mgf_sum (t := t) (fun w ↦ Measurable.of_discrete) univ
    have e : (∑ w ∈ (univ : Finset {w // w ∈ U}),
        fun x : {w // w ∈ U} → Prop ↦ tails (x w)) =
        fun x ↦ ∑ w : {w // w ∈ U}, tails (x w) := by
      funext x
      simp
    rw [e] at h
    rw [h, prod_congr rfl fun w _ ↦ hmgf1 w, prod_const, card_univ, Fintype.card_coe]
  have hch := measure_le_le_exp_mul_mgf (μ := blockLaw V U q)
    (X := fun x : {w // w ∈ U} → Prop ↦ ∑ w : {w // w ∈ U}, tails (x w))
    (β * U.card / 2) ht0 (Integrable.of_finite)
  rw [hmgf] at hch
  refine hch.trans ?_
  -- `2^(βk/2) (1 - β/2)^k ≤ exp(βk log 2 / 2 - βk/2) ≤ exp(-βk/8)`.
  have h1 : (1 - β / 2) ^ U.card ≤ exp (-(β / 2)) ^ U.card := by
    have : 0 ≤ 1 - β / 2 := by have := q.2.1; linarith
    exact pow_le_pow_left₀ this (by linarith [Real.add_one_le_exp (-(β / 2))]) _
  have h2 : exp (-(β / 2)) ^ U.card = exp (-(β * U.card / 2)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hlog : Real.log 2 ≤ 3 / 4 := by
    have := Real.log_two_lt_d9; linarith
  have hk0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  calc exp (-t * (β * U.card / 2)) * (1 - β / 2) ^ U.card
      ≤ exp (-t * (β * U.card / 2)) * exp (-(β * U.card / 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2.le) (exp_pos _).le
    _ = exp (Real.log 2 * (β * U.card / 2) - β * U.card / 2) := by
        rw [← Real.exp_add, ht]; ring_nf
    _ ≤ exp (-(β * U.card / 8)) := by
        refine Real.exp_le_exp.2 ?_
        have : 0 ≤ β * U.card := mul_nonneg hβ0 hk0
        nlinarith

/-- **Non-neighbours** [BKS23, Claim 5.9]: under `G(V, q)`, some vertex outside `U` has fewer than
`(1 - q) |U| / 2` non-neighbours in `U` with probability at most `|Uᶜ| exp(-(1 - q) |U| / 8)`. -/
theorem prob_not_nonNbrGE (q : I) :
    (G(V, q)).real {R | ¬ NonNbrGE U (1 - q) R} ≤
      Uᶜ.card * exp (-((1 - q) * U.card / 8)) := by
  classical
  -- The number of non-neighbours of `v`, from its block.
  have hcount : ∀ (R : SimpleGraph V) (v : V) (hv : v ∉ U),
      ((U.filter fun u ↦ ¬ R.Adj u v).card : ℝ) =
        ∑ w : {w // w ∈ U}, tails (cut U R ⟨v, hv⟩ w) := by
    intro R v hv
    rw [card_filter, Nat.cast_sum, ← sum_coe_sort U]
    refine sum_congr rfl fun w _ ↦ ?_
    by_cases h : R.Adj w v <;> simp [tails, cut, h]
  have hvertex : ∀ v (hv : v ∉ U), (G(V, q)).real {R | ((U.filter fun u ↦ ¬ R.Adj u v).card : ℝ) <
      (1 - q) * U.card / 2} ≤ exp (-((1 - q) * U.card / 8)) := by
    intro v hv
    have hsub : {R : SimpleGraph V | ((U.filter fun u ↦ ¬ R.Adj u v).card : ℝ) <
        (1 - q) * U.card / 2} ⊆ cut U ⁻¹' ((fun ω ↦ ω ⟨v, hv⟩) ⁻¹'
          {x | ∑ w : {w // w ∈ U}, tails (x w) ≤ (1 - q) * U.card / 2}) := by
      intro R hR
      simp only [Set.mem_ofPred_eq] at hR
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ← hcount R v hv]
      exact hR.le
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    rw [measureReal_def, binomialRandom_cut_preimage U q MeasurableSet.of_discrete,
      ← Measure.map_apply (measurable_pi_apply _) MeasurableSet.of_discrete, cutLaw_eq,
      Measure.infinitePi_map_eval, ← measureReal_def]
    exact blockLaw_tails_le U q
  have hsub : {R : SimpleGraph V | ¬ NonNbrGE U (1 - q) R} ⊆
      ⋃ v ∈ Uᶜ, {R | ((U.filter fun u ↦ ¬ R.Adj u v).card : ℝ) < (1 - q) * U.card / 2} := by
    intro R hR
    simp only [NonNbrGE, Set.mem_ofPred_eq, not_forall, not_le] at hR
    obtain ⟨v, hv, hlt⟩ := hR
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨v, hv, hlt⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  calc ∑ v ∈ Uᶜ, (G(V, q)).real {R | ((U.filter fun u ↦ ¬ R.Adj u v).card : ℝ) <
        (1 - q) * U.card / 2}
      ≤ ∑ _v ∈ Uᶜ, exp (-((1 - q) * U.card / 8)) :=
        sum_le_sum fun v hv ↦ hvertex v (mem_compl.1 hv)
    _ = _ := by rw [sum_const, nsmul_eq_mul]

end BKS23.Random
