module

public import BDT24.Analysis.Good
public import BDT24.Prob.Exch

/-!
# The null case [BDT24, Lemma 4.1]

On null input, the algorithm says `true` with probability `P(round passes)^M`
(`BDT24.Alg.coinProb_algB_true`), integrated over the input. A round passes when the paired test
says the input is planted against the own sample and the own sample is not planted against the
input (`BDT24.Alg.coinProb_blockTest_true`). On a good own sample the own sample is the
quantization of independent Gaussian rows (`BDT24.Analysis.ownCells_eq`), so it has the law of the
input; this changes the probability that a round passes by at most `P(not good)`, and its power
by at most `M P(not good)`. With the own sample exactly a copy of the input, the power is at most
`1/(M+1)` by exchangeability (`BDT24.Prob.exch`), on the countable set of quantized samples.
-/

@[expose] public section

namespace BDT24.Analysis

open MeasureTheory ProbabilityTheory BDT24.Alg BDT24.Prob

namespace NL

/-! ### Generalities -/

/-- Coin probabilities are nonnegative. -/
theorem cProb_nonneg (L : ℕ) (P : List Bool → Prop) : 0 ≤ coinProb L P := by
  unfold coinProb
  positivity

/-- Coin probabilities are at most `1`. -/
theorem cProb_le_one (L : ℕ) (P : List Bool → Prop) : coinProb L P ≤ 1 := by
  classical
  unfold coinProb
  rw [div_le_one (by positivity)]
  have h := Fintype.card_subtype_le (fun r : Fin L → Bool ↦ P (List.ofFn r))
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  exact_mod_cast h

/-- A probability `P` that exceeds `a ∈ [0, 1]` by at most `b ≥ 0` has `P^M ≤ a^M + M b`. -/
theorem pow_le_pow_add_mul {P a b : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (hb : 0 ≤ b) (hPab : P ≤ a + b) (M : ℕ) : P ^ M ≤ a ^ M + M * b := by
  induction M with
  | zero => simp
  | succ M ih =>
    have haM0 : 0 ≤ a ^ M := pow_nonneg ha0 M
    have haM : a ^ M ≤ 1 := pow_le_one₀ ha0 ha1
    have h1 : P * a ^ M ≤ (a + b) * a ^ M := mul_le_mul_of_nonneg_right hPab haM0
    have h3 : b * a ^ M ≤ b := mul_le_of_le_one_right hb haM
    have h4 : P * (M * b) ≤ M * b := mul_le_of_le_one_left (by positivity) hP1
    calc P ^ (M + 1) = P * P ^ M := by ring
      _ ≤ P * (a ^ M + M * b) := mul_le_mul_of_nonneg_left ih hP0
      _ ≤ a ^ (M + 1) + ((M + 1 : ℕ) : ℝ) * b := by
        rw [pow_succ]; push_cast; nlinarith

/-! ### Quantized samples as integer arrays -/

/-- Real points to `q` bits, as an integer array. -/
noncomputable def qArr (q : ℕ) {n m : ℕ} (z : Fin n → EuclideanSpace ℝ (Fin m)) :
    Fin n → Fin m → ℤ :=
  fun i j ↦ quantize q (z i j)

/-- An integer array as a sample, one list per point. -/
def ptsOf {n m : ℕ} (y : Fin n → Fin m → ℤ) : Pts :=
  List.ofFn fun i ↦ List.ofFn (y i)

/-- Quantization is measurable. -/
theorem measurable_qArr (q n m : ℕ) :
    Measurable (qArr q : (Fin n → EuclideanSpace ℝ (Fin m)) → Fin n → Fin m → ℤ) := by
  refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
  exact Int.measurable_floor.comp
    (by fun_prop : Continuous fun z : Fin n → EuclideanSpace ℝ (Fin m) ↦
      (2 : ℝ) ^ q * z i j).measurable

/-- The paired test on integer arrays. -/
def pairArr (A : SLRInput × List Bool → Estimate) (e k p q n m : ℕ)
    (y y' : Fin n → Fin m → ℤ) (r : List Bool) : Bool :=
  pairTest A e k p q (ptsOf y) (ptsOf y') r

/-- Good own samples form a measurable set. -/
theorem measSet_samp (q n m : ℕ) :
    MeasurableSet {g : Fin n → EuclideanSpace ℝ (Fin m) | Samp q n m g} := by
  have e : {g : Fin n → EuclideanSpace ℝ (Fin m) | Samp q n m g} =
      ⋂ i, ⋂ j, ({g | |g i j| ≤ (rad n m : ℝ)} ∩
        (⋃ c : ℤ, {g | |(2 : ℝ) ^ q * g i j - c| ≤ 1 / 2 ^ (n + m + 4)})ᶜ) := by
    ext g
    simp [Samp, NearInt]
  rw [e]
  refine MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦ ?_
  refine (measurableSet_le (by fun_prop) measurable_const).inter
    (MeasurableSet.iUnion fun c ↦ measurableSet_le (by fun_prop) measurable_const).compl

/-- The coins of one run of the regression algorithm, on a quantized sample. -/
theorem lenA_spcaInput_eq (e : ℕ) (δ : ℚ) {n m : ℕ} (p k q : ℕ) (hn : 0 < n)
    (ω : Fin n → EuclideanSpace ℝ (Fin m)) :
    lenA e (spcaInput δ p k q ω) = (linB n m k p + 2) ^ e := by
  unfold lenA
  rw [spcaInput_points, nOf_qz, mOf_qz q hn]
  rfl

/-- The number of rounds, on a quantized sample. -/
theorem rounds_spcaInput_eq (δ : ℚ) {n m : ℕ} (p k q : ℕ)
    (ω : Fin n → EuclideanSpace ℝ (Fin m)) :
    rounds (spcaInput δ p k q ω).δ (nOf (spcaInput δ p k q ω).points) = rounds δ n := by
  rw [spcaInput_points, nOf_qz]
  rfl

/-- **One round, against a copy of the input**: the probability that a round passes is at most
the probability that the input wins against an independent quantized null sample, plus the
probability of a bad own sample. -/
theorem blockTest_le_win (A : SLRInput × List Bool → Estimate) (e : ℕ) (δ : ℚ)
    (n m p k q : ℕ) (hn : 0 < n) (ω : Fin n → EuclideanSpace ℝ (Fin m)) :
    coinProb (lenBlk e (spcaInput δ p k q ω))
        (fun b ↦ blockTest A e (spcaInput δ p k q ω) b = true) ≤
      ∫ g, X.win ((linB n m k p + 2) ^ e) (pairArr A e k p q n m) (qArr q ω) (qArr q g)
          ∂(gRows n m) + (gRows n m).real {g | ¬ Samp q n m g} := by
  rw [coinProb_blockTest_true A e _ (nOf_qz q ω) (mOf_qz q hn ω), lenA_spcaInput_eq e δ p k q hn]
  set L := (linB n m k p + 2) ^ e
  set S := {g : Fin n → EuclideanSpace ℝ (Fin m) | Samp q n m g}
  have hS : MeasurableSet S := measSet_samp q n m
  have hw : Integrable (fun g ↦ X.win L (pairArr A e k p q n m) (qArr q ω) (qArr q g))
      (gRows n m) := by
    refine Integrable.of_bound
      ((measurable_of_countable fun y ↦ X.win L (pairArr A e k p q n m) (qArr q ω) y).comp
        (measurable_qArr q n m)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun g ↦ ?_)
    obtain ⟨h0, h1⟩ := X.win_mem L (pairArr A e k p q n m) (qArr q ω) (qArr q g)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hI : Integrable (Sᶜ.indicator (1 : (Fin n → EuclideanSpace ℝ (Fin m)) → ℝ))
      (gRows n m) :=
    (integrable_const (1 : ℝ)).indicator hS.compl
  have hη : (gRows n m).real {g | ¬ Samp q n m g} =
      ∫ g, Sᶜ.indicator (1 : (Fin n → EuclideanSpace ℝ (Fin m)) → ℝ) g ∂(gRows n m) :=
    (integral_indicator_one hS.compl).symm
  rw [hη, ← integral_add hw hI]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun g ↦ ?_) (hw.add hI)
    (Filter.Eventually.of_forall fun g ↦ ?_)
  · exact mul_nonneg (cProb_nonneg _ _) (cProb_nonneg _ _)
  · beta_reduce
    by_cases hg : g ∈ S
    · have hc : g ∉ Sᶜ := fun h ↦ h hg
      rw [Set.indicator_of_notMem hc, add_zero]
      refine le_of_eq ?_
      change coinProb L (fun r ↦ pairTest A e k p q (qz q ω) (ownCells n m q g) r = true) *
          coinProb L (fun r ↦ pairTest A e k p q (ownCells n m q g) (qz q ω) r = false) = _
      rw [ownCells_eq g hg]
      rfl
    · rw [Set.indicator_of_mem (show g ∈ Sᶜ from hg), Pi.one_apply]
      have h0 := (X.win_mem L (pairArr A e k p q n m) (qArr q ω) (qArr q g)).1
      refine (mul_le_mul (cProb_le_one _ _) (cProb_le_one _ _) (cProb_nonneg _ _)
        zero_le_one).trans ?_
      linarith

end NL

open NL in
/-- **On null input the algorithm says `true` with probability at most `1/(M+1)` plus `M` times
the probability of a bad own sample.** -/
theorem null_true {A : SLRInput × List Bool → Estimate} {e : ℕ} (T : SPCAInput → ℕ)
    (hT : ∀ x, rounds x.δ (nOf x.points) * lenBlk e x ≤ T x) (δ : ℚ) (n m p k q : ℕ)
    (hn : 0 < n) :
    spcaOutputProb (algB A e) T δ p k q n (1 : Matrix (Fin m) (Fin m) ℝ) true ≤
      1 / ((rounds δ n : ℝ) + 1) + rounds δ n * (gRows n m).real {g | ¬ Samp q n m g} := by
  set M := rounds δ n
  set L := (linB n m k p + 2) ^ e
  set D := pairArr A e k p q n m
  set η := (gRows n m).real {g | ¬ Samp q n m g}
  set μ := (gRows n m).map (qArr q) with hμ
  have hμP : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  set h : (Fin n → Fin m → ℤ) → ℝ := fun y ↦ ∫ y', X.win L D y y' ∂μ
  have hh01 : ∀ y, 0 ≤ h y ∧ h y ≤ 1 := fun y ↦ by
    refine ⟨integral_nonneg fun y' ↦ (X.win_mem L D y y').1, ?_⟩
    calc h y ≤ ∫ _, (1 : ℝ) ∂μ :=
          integral_mono (X.integrable_of_abs_le μ _ 1 fun y' ↦ by
              rw [abs_of_nonneg (X.win_mem L D y y').1]; exact (X.win_mem L D y y').2)
            (integrable_const 1) fun y' ↦ (X.win_mem L D y y').2
      _ = 1 := by simp
  have hη0 : 0 ≤ η := measureReal_nonneg
  have hPt : ∀ ω, ∫ g, X.win L D (qArr q ω) (qArr q g) ∂(gRows n m) = h (qArr q ω) :=
    fun ω ↦ (integral_map (measurable_qArr q n m).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable).symm
  have hpt : ∀ ω, coinProb (T (spcaInput δ p k q ω))
      (fun c ↦ algB A e (spcaInput δ p k q ω, c) = true) ≤ h (qArr q ω) ^ M + M * η := by
    intro ω
    rw [coinProb_algB_true A e _ _ (hT _), rounds_spcaInput_eq]
    have h1 := blockTest_le_win A e δ n m p k q hn ω
    rw [hPt] at h1
    exact pow_le_pow_add_mul (cProb_nonneg _ _) (cProb_le_one _ _) (hh01 _).1 (hh01 _).2 hη0
      h1 M
  set G : (Fin n → EuclideanSpace ℝ (Fin m)) → ℝ := fun ω ↦ h (qArr q ω) ^ M + M * η
  have hGm : Measurable G :=
    (((measurable_of_countable h).comp (measurable_qArr q n m)).pow_const M).add_const _
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω ↦ add_nonneg (pow_nonneg (hh01 _).1 M) (by positivity)
  have hGi : Integrable G (gRows n m) := by
    refine Integrable.of_bound hGm.aestronglyMeasurable (1 + M * η)
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 ω)]
    have := pow_le_one₀ (hh01 (qArr q ω)).1 (hh01 (qArr q ω)).2 (n := M)
    simp only [G]
    linarith
  have hint : ∫ ω, G ω ∂(gRows n m) ≤ 1 / ((M : ℝ) + 1) + M * η := by
    have hi : Integrable (fun ω ↦ h (qArr q ω) ^ M) (gRows n m) := by
      refine Integrable.of_bound (((measurable_of_countable h).comp
        (measurable_qArr q n m)).pow_const M).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hh01 _).1 M)]
      exact pow_le_one₀ (hh01 (qArr q ω)).1 (hh01 (qArr q ω)).2
    rw [show G = fun ω ↦ h (qArr q ω) ^ M + M * η from rfl,
      integral_add hi (integrable_const _), integral_const, probReal_univ, one_smul]
    have hx : ∫ ω, h (qArr q ω) ^ M ∂(gRows n m) = ∫ y, h y ^ M ∂μ :=
      (integral_map (measurable_qArr q n m).aemeasurable
        (measurable_of_countable fun y ↦ h y ^ M).aestronglyMeasurable).symm
    rw [hx]
    have : ∫ y, h y ^ M ∂μ ≤ 1 / ((M : ℝ) + 1) := exch μ L D M
    linarith
  unfold spcaOutputProb
  calc _ ≤ (∫⁻ ω, ENNReal.ofReal (G ω) ∂(gRows n m)).toReal :=
        ENNReal.toReal_mono hGi.lintegral_lt_top.ne
          (lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal (hpt ω))
    _ = ∫ ω, G ω ∂(gRows n m) :=
        (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hG0)
          hGm.aestronglyMeasurable).symm
    _ ≤ _ := hint

end BDT24.Analysis
