module

public import B25.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Probability.Independence.InfinitePi
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
import TauCeti.Probability.Moments.Basic

/-!
# Lemma 1.4: sub-Gaussian rotations

`B25.partiallyRotated_of_subgaussian_main`: the statement of `B25.partiallyRotated_of_subgaussian`
in `B25/Challenge.lean`, with `c = 1/960000` and `K = 1920000`. The proof is the paper's
[B25, Appendix B], except for the lower tail of `‖R w‖₂²`, where a Chernoff bound with second and
fourth moments replaces the Hanson–Wright inequality.

**Reduction.** As for Lemma 1.3 (`B25.rotateCols_mulVec_of_mem`,
`B25.rotateCols_mulVec_of_not_mem`, `B25.corr_smul_left`, `B25.corr_smul_right`), it suffices to
bound `P(|corr u (R w)| > 1/100)` for fixed unit vectors `u, w` (`B25.SG.fixed_unit_qz`). When
`‖R w‖₂² > θ = σ² n / 4`, such a correlation forces `|⟨u, R w⟩| ≥ √θ / 100`
(`B25.SG.corr_gt_imp_qz`).

1. **The rows.** The coordinates `Yᵢ = (R w)ᵢ = ∑ⱼ wⱼ Rᵢⱼ` are independent, since the rows of `R`
   are (`B25.SG.rows_iIndepFun_qz`, from `Measure.infinitePi_map_curry`). Each `Yᵢ` is
   sub-Gaussian with variance proxy `(σ')²` (`B25.SG.wsum_subG_qz`, from
   `HasSubgaussianMGF.sum_of_iIndepFun`) and has `E Yᵢ² = σ²` (`B25.SG.wsum_sq_integral_qz`, from
   `IndepFun.variance_sum`).
2. **The numerator.** `⟨u, R w⟩ = ∑ᵢ uᵢ Yᵢ` is sub-Gaussian with proxy `(σ')²`, so
   `P(|⟨u, R w⟩| ≥ √θ / 100) ≤ 2 e^(-σ² n / (80000 σ'²))` (`HasSubgaussianMGF.measure_ge_le` for
   the sum and for its negative).
3. **The denominator.** From `t⁴ Y⁴ ≤ 24 (e^(tY) + e^(-tY))` at `t² = 2/σ'²`, `E Yᵢ⁴ ≤ 36 σ'⁴`
   (`B25.SG.integral_pow_four_le_qz`). For `λ ≥ 0`, `e^(-λ Y²) ≤ 1 - λ Y² + λ² Y⁴ / 2` (TauCeti's
   `Real.exp_le_one_add_add_sq_div_two_of_nonpos`), so `E e^(-λ Yᵢ²) ≤ exp(-λ σ² + 18 λ² σ'⁴)`
   (`B25.SG.integral_exp_neg_sq_le_qz`). By Chernoff (`B25.SG.lower_tail_sum_sq_qz`, with TauCeti's
   `ProbabilityTheory.iIndepFun.mgf_sum_of_aemeasurable`) at `λ = σ² / (36 σ'⁴)`,
   `P(‖R w‖₂² ≤ σ² n / 4) ≤ e^(-m/144)` for `m = n σ⁴ / σ'⁴`.
4. **Together.** `σ⁴ = (E Y²)² ≤ E Y⁴ ≤ 36 σ'⁴` (`B25.SG.sq_integral_sq_le_qz`), so `σ² ≤ 6 σ'²`
   and the bound on the numerator is at most `2 e^(-m/480000)`. The probability is at most
   `3 e^(-m/480000) ≤ e^(-m/960000)` once `m ≥ 1920000`, which is `n ≥ K (σ'/σ)⁴`. The cases
   `n = 0` and `σ' = 0` are trivial: the bound `e^(-δ n)` is then `1`.
-/

@[expose] public section

namespace B25.SG

open MeasureTheory ProbabilityTheory Matrix Real

/-- `x⁴ ≤ 24 (eˣ + e⁻ˣ)`. -/
theorem pow_four_le_exp_add_exp_qz (x : ℝ) : x ^ 4 ≤ 24 * (exp x + exp (-x)) := by
  have h := pow_div_factorial_le_exp _ (abs_nonneg x) 4
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [h4] at h
  have hf : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hf] at h
  have hab : exp |x| ≤ exp x + exp (-x) := by
    rcases abs_cases x with ⟨hx, _⟩ | ⟨hx, _⟩ <;> rw [hx] <;>
      linarith [exp_pos x, exp_pos (-x)]
  linarith

/-- The fourth moment of a variable with a sub-Gaussian moment-generating function of proxy
`c > 0`: `E Y⁴ ≤ 36 c²`. -/
theorem integral_pow_four_le_qz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} {c : NNReal} (hY : HasSubgaussianMGF Y c P)
    (hc : 0 < (c : ℝ)) :
    Integrable (fun ω ↦ Y ω ^ 4) P ∧ ∫ ω, Y ω ^ 4 ∂P ≤ 36 * (c : ℝ) ^ 2 := by
  set t : ℝ := √(2 / c) with ht
  have ht2 : t ^ 2 = 2 / c := Real.sq_sqrt (by positivity)
  have htpos : 0 < t := Real.sqrt_pos.2 (by positivity)
  have hint : Integrable (fun ω ↦ 24 * (exp (t * Y ω) + exp ((-t) * Y ω))) P :=
    ((hY.integrable_exp_mul t).add (hY.integrable_exp_mul (-t))).const_mul 24
  have hpt : ∀ ω, t ^ 4 * Y ω ^ 4 ≤ 24 * (exp (t * Y ω) + exp ((-t) * Y ω)) := fun ω ↦ by
    have := pow_four_le_exp_add_exp_qz (t * Y ω)
    rw [mul_pow, neg_mul] at *
    exact this
  have hmeas : AEStronglyMeasurable (fun ω ↦ Y ω ^ 4) P :=
    (hY.aestronglyMeasurable.pow 4)
  have hint4 : Integrable (fun ω ↦ Y ω ^ 4) P := by
    refine Integrable.mono' (hint.const_mul (t ^ 4)⁻¹) hmeas (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [le_inv_mul_iff₀ (by positivity)]
    exact hpt ω
  refine ⟨hint4, ?_⟩
  have hI : t ^ 4 * ∫ ω, Y ω ^ 4 ∂P ≤ 24 * (mgf Y P t + mgf Y P (-t)) := by
    rw [← integral_const_mul, mgf, mgf, ← integral_add (hY.integrable_exp_mul t)
      (hY.integrable_exp_mul (-t)), ← integral_const_mul]
    exact integral_mono (hint4.const_mul _) hint hpt
  have hm1 := hY.mgf_le t
  have hm2 := hY.mgf_le (-t)
  rw [neg_sq, ht2] at hm2
  rw [ht2] at hm1
  have he : (c : ℝ) * (2 / c) / 2 = 1 := by field_simp
  rw [he] at hm1 hm2
  have h3 := exp_one_lt_three
  have ht4 : t ^ 4 = 4 / (c : ℝ) ^ 2 := by
    rw [show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2]; ring
  rw [ht4] at hI
  have hI' : ∫ ω, Y ω ^ 4 ∂P ≤ 6 * (mgf Y P t + mgf Y P (-t)) * (c : ℝ) ^ 2 := by
    have hc2 : 0 < (c : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hI hc2.le
    field_simp at this
    nlinarith
  nlinarith [mgf_nonneg (X := Y) (μ := P) (t := t)]


/-- A weighted sum `∑ⱼ aⱼ Xⱼ` of independent variables with sub-Gaussian proxy `c`, with
`∑ⱼ aⱼ² = 1`, has proxy `c`. -/
theorem wsum_subG_qz {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {X : ι → Ω → ℝ} (hX : iIndepFun X P) {c : NNReal} (hc : ∀ j, HasSubgaussianMGF (X j) c P)
    (a : ι → ℝ) (ha : ∑ j, a j ^ 2 = 1) :
    HasSubgaussianMGF (fun ω ↦ ∑ j, a j * X j ω) c P := by
  have hind : iIndepFun (fun j ω ↦ a j * X j ω) P :=
    hX.comp (fun j x ↦ a j * x) (fun j ↦ measurable_const.mul measurable_id)
  have h := HasSubgaussianMGF.sum_of_iIndepFun hind (s := Finset.univ)
    (fun j _ ↦ (hc j).const_mul (a j))
  convert h using 1
  apply NNReal.eq
  rw [NNReal.coe_sum]
  change (c : ℝ) = ∑ i, a i ^ 2 * (c : ℝ)
  rw [← Finset.sum_mul, ha, one_mul]

/-- Grouping: if the entries `E (i, j)` are independent, the rows `j ↦ E (i, j)` are. -/
theorem rows_iIndepFun_qz {Ω ι κ : Type*} [MeasurableSpace Ω] [Countable ι] [Countable κ]
    {P : Measure Ω} {E : ι × κ → Ω → ℝ} (hE : iIndepFun E P) (hm : ∀ p, AEMeasurable (E p) P) :
    iIndepFun (fun i ω j ↦ E (i, j) ω) P := by
  have := hE.isProbabilityMeasure
  have hrow : ∀ i, iIndepFun (fun j ↦ E (i, j)) P := fun i ↦
    hE.precomp (g := fun j ↦ (i, j)) (fun _ _ h ↦ (Prod.mk.inj h).2)
  have hmr : ∀ i, AEMeasurable (fun ω j ↦ E (i, j) ω) P := fun i ↦
    aemeasurable_pi_iff.2 fun j ↦ hm (i, j)
  have hmF : AEMeasurable (fun ω p ↦ E p ω) P := aemeasurable_pi_iff.2 hm
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map₀' hmr]
  have hF := hE.map_fun_eq_infinitePi_map₀' hm
  have hcomp : (fun ω i j ↦ E (i, j) ω) =
      (MeasurableEquiv.curry ι κ ℝ) ∘ (fun ω p ↦ E p ω) := by
    ext ω i j; rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable
    (MeasurableEquiv.curry ι κ ℝ).measurable.aemeasurable hmF, hF]
  rw [Measure.infinitePi_map_curry (fun i j ↦ P.map (E (i, j)))]
  congr 1
  ext1 i
  exact ((hrow i).map_fun_eq_infinitePi_map₀' fun j ↦ hm (i, j)).symm


/-- The second moment of a weighted sum `∑ⱼ aⱼ Xⱼ` of independent centred variables of variance
`s`, with `∑ⱼ aⱼ² = 1`, is `s`. -/
theorem wsum_sq_integral_qz {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ι → Ω → ℝ} (hX : iIndepFun X P)
    (hL : ∀ j, MemLp (X j) 2 P) (hmean : ∀ j, ∫ ω, X j ω ∂P = 0) {s : ℝ}
    (hvar : ∀ j, Var[X j; P] = s) (a : ι → ℝ) (ha : ∑ j, a j ^ 2 = 1) :
    ∫ ω, (∑ j, a j * X j ω) ^ 2 ∂P = s := by
  set Z : ι → Ω → ℝ := fun j ω ↦ a j * X j ω with hZ
  have hind : iIndepFun Z P :=
    hX.comp (fun j x ↦ a j * x) (fun j ↦ measurable_const.mul measurable_id)
  have hZL : ∀ j, MemLp (Z j) 2 P := fun j ↦ (hL j).const_mul (a j)
  have hsum : (fun ω ↦ ∑ j, a j * X j ω) = ∑ j, Z j := by
    ext ω; simp [hZ, Finset.sum_apply]
  have hv : Var[∑ j, Z j; P] = ∑ j, Var[Z j; P] :=
    IndepFun.variance_sum (fun j _ ↦ hZL j) (fun i _ j _ hij ↦ hind.indepFun hij)
  have hvZ : ∀ j, Var[Z j; P] = a j ^ 2 * s := fun j ↦ by
    rw [hZ, variance_const_mul, hvar]
  rw [Finset.sum_congr rfl (fun j _ ↦ hvZ j), ← Finset.sum_mul, ha, one_mul] at hv
  have hm0 : ∫ ω, (∑ j, Z j) ω ∂P = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ (fun j _ ↦ (hZL j).integrable one_le_two)]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    simp only [hZ]
    rw [integral_const_mul, hmean, mul_zero]
  have hmeas : AEMeasurable (∑ j, Z j) P :=
    (memLp_finsetSum' Finset.univ (fun j _ ↦ hZL j)).aemeasurable
  rw [variance_of_integral_eq_zero hmeas hm0] at hv
  simpa only [Finset.sum_apply, hZ] using hv

/-- For `λ ≥ 0`, `E e^(-λ Y²) ≤ 1 - λ E Y² + λ² E Y⁴ / 2`. -/
theorem integral_exp_neg_sq_le_qz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hm : AEStronglyMeasurable Y P)
    (h2 : Integrable (fun ω ↦ Y ω ^ 2) P) (h4 : Integrable (fun ω ↦ Y ω ^ 4) P) {l : ℝ}
    (hl : 0 ≤ l) :
    Integrable (fun ω ↦ exp (-l * Y ω ^ 2)) P ∧
      ∫ ω, exp (-l * Y ω ^ 2) ∂P ≤
        1 - l * ∫ ω, Y ω ^ 2 ∂P + l ^ 2 / 2 * ∫ ω, Y ω ^ 4 ∂P := by
  have hint : Integrable (fun ω ↦ exp (-l * Y ω ^ 2)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun ω ↦ ?_)
    · exact (continuous_exp.comp_aestronglyMeasurable ((hm.pow 2).const_mul (-l)))
    · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      have := sq_nonneg (Y ω)
      nlinarith
  refine ⟨hint, ?_⟩
  have hR : Integrable (fun ω ↦ 1 - l * Y ω ^ 2 + l ^ 2 / 2 * Y ω ^ 4) P :=
    ((integrable_const 1).sub (h2.const_mul l)).add (h4.const_mul _)
  calc ∫ ω, exp (-l * Y ω ^ 2) ∂P ≤ ∫ ω, (1 - l * Y ω ^ 2 + l ^ 2 / 2 * Y ω ^ 4) ∂P := by
        refine integral_mono hint hR fun ω ↦ ?_
        have hx : -l * Y ω ^ 2 ≤ 0 := by
          have := sq_nonneg (Y ω)
          nlinarith
        have := exp_le_one_add_add_sq_div_two_of_nonpos hx
        calc exp (-l * Y ω ^ 2) ≤ 1 + -l * Y ω ^ 2 + (-l * Y ω ^ 2) ^ 2 / 2 := this
          _ = 1 - l * Y ω ^ 2 + l ^ 2 / 2 * Y ω ^ 4 := by ring
    _ = 1 - l * ∫ ω, Y ω ^ 2 ∂P + l ^ 2 / 2 * ∫ ω, Y ω ^ 4 ∂P := by
        have hA : Integrable (fun ω ↦ 1 - l * Y ω ^ 2) P :=
          (integrable_const 1).sub (h2.const_mul l)
        rw [integral_add (f := fun ω ↦ 1 - l * Y ω ^ 2) hA (h4.const_mul _),
          integral_sub (f := fun _ ↦ (1 : ℝ)) (integrable_const 1) (h2.const_mul l),
          integral_const_mul, integral_const_mul]
        simp

/-- **Chernoff bound** for the lower tail of `∑ᵢ Yᵢ²` with independent `Yᵢ` of second moment `s₂`
and fourth moment at most `m₄`: for `λ ≥ 0`,
`P(∑ᵢ Yᵢ² ≤ θ) ≤ exp(λ θ + N (-λ s₂ + λ² m₄ / 2))`. -/
theorem lower_tail_sum_sq_qz {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : ι → Ω → ℝ} (hind : iIndepFun Y P)
    (hm : ∀ i, AEStronglyMeasurable (Y i) P) (h2 : ∀ i, Integrable (fun ω ↦ Y i ω ^ 2) P)
    (h4 : ∀ i, Integrable (fun ω ↦ Y i ω ^ 4) P) {s₂ m₄ : ℝ}
    (hs : ∀ i, ∫ ω, Y i ω ^ 2 ∂P = s₂) (hq : ∀ i, ∫ ω, Y i ω ^ 4 ∂P ≤ m₄) {l : ℝ} (hl : 0 ≤ l)
    (θ : ℝ) :
    P.real {ω | ∑ i, Y i ω ^ 2 ≤ θ} ≤
      exp (l * θ + Fintype.card ι * (-(l * s₂) + l ^ 2 * m₄ / 2)) := by
  have hind2 : iIndepFun (fun i ω ↦ Y i ω ^ 2) P :=
    hind.comp (fun _ x ↦ x ^ 2) (fun _ ↦ measurable_id.pow_const 2)
  have hm2 : ∀ i ∈ (Finset.univ : Finset ι), AEMeasurable (fun ω ↦ Y i ω ^ 2) P :=
    fun i _ ↦ ((hm i).pow 2).aemeasurable
  have hint : Integrable (fun ω ↦ exp (-l * ∑ i, Y i ω ^ 2)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ (ae_of_all _ fun ω ↦ ?_)
    · exact continuous_exp.comp_aestronglyMeasurable
        ((Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦ (hm i).pow 2).const_mul (-l))
    · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      have : 0 ≤ ∑ i, Y i ω ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
      nlinarith
  have hch := measure_le_le_exp_mul_mgf (X := fun ω ↦ ∑ i, Y i ω ^ 2) (μ := P) θ
    (neg_nonpos.2 hl) hint
  rw [hind2.mgf_sum_of_aemeasurable hm2] at hch
  have hfac : ∀ i ∈ (Finset.univ : Finset ι),
      mgf (fun ω ↦ Y i ω ^ 2) P (-l) ≤ exp (-(l * s₂) + l ^ 2 * m₄ / 2) := fun i _ ↦ by
    obtain ⟨-, hle⟩ := integral_exp_neg_sq_le_qz (hm i) (h2 i) (h4 i) hl
    rw [hs i] at hle
    have : l ^ 2 / 2 * ∫ ω, Y i ω ^ 4 ∂P ≤ l ^ 2 / 2 * m₄ :=
      mul_le_mul_of_nonneg_left (hq i) (by positivity)
    calc mgf (fun ω ↦ Y i ω ^ 2) P (-l) = ∫ ω, exp (-l * Y i ω ^ 2) ∂P := rfl
      _ ≤ 1 - l * s₂ + l ^ 2 / 2 * m₄ := by linarith
      _ = (-(l * s₂) + l ^ 2 * m₄ / 2) + 1 := by ring
      _ ≤ exp (-(l * s₂) + l ^ 2 * m₄ / 2) := add_one_le_exp _
  have hprod := Finset.prod_le_prod₀ (fun i _ ↦ mgf_nonneg) hfac
  rw [Finset.prod_const, Finset.card_univ, ← exp_nat_mul] at hprod
  calc P.real {ω | ∑ i, Y i ω ^ 2 ≤ θ}
      ≤ exp (-(-l) * θ) * ∏ i, mgf (fun ω ↦ Y i ω ^ 2) P (-l) := hch
    _ ≤ exp (-(-l) * θ) * exp (Fintype.card ι * (-(l * s₂) + l ^ 2 * m₄ / 2)) :=
        mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp (l * θ + Fintype.card ι * (-(l * s₂) + l ^ 2 * m₄ / 2)) := by
        rw [← exp_add, neg_neg]


/-- `(E Y²)² ≤ E Y⁴` on a probability space. -/
theorem sq_integral_sq_le_qz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (h2 : Integrable (fun ω ↦ Y ω ^ 2) P)
    (h4 : Integrable (fun ω ↦ Y ω ^ 4) P) :
    (∫ ω, Y ω ^ 2 ∂P) ^ 2 ≤ ∫ ω, Y ω ^ 4 ∂P := by
  set s := ∫ ω, Y ω ^ 2 ∂P
  have hA : Integrable (fun ω ↦ 2 * s * Y ω ^ 2 - s ^ 2) P :=
    (h2.const_mul (2 * s)).sub (integrable_const _)
  have hle : ∫ ω, (2 * s * Y ω ^ 2 - s ^ 2) ∂P ≤ ∫ ω, Y ω ^ 4 ∂P :=
    integral_mono hA h4 fun ω ↦ by nlinarith [sq_nonneg (Y ω ^ 2 - s)]
  rw [integral_sub (f := fun ω ↦ 2 * s * Y ω ^ 2) (h2.const_mul (2 * s)) (integrable_const _),
    integral_const_mul] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  nlinarith

/-- The deterministic part: if `‖u‖₂ = 1` and `|corr u v| > 1/100`, then
`|⟨u, v⟩| ≥ √θ / 100` or `‖v‖₂² ≤ θ`. -/
theorem corr_gt_imp_qz {n : ℕ} {u v : Fin n → ℝ} (hu : u ⬝ᵥ u = 1) {θ : ℝ} (hθ : 0 < θ)
    (h : 1 / 100 < |corr u v|) :
    1 / 100 * √θ ≤ u ⬝ᵥ v ∨ 1 / 100 * √θ ≤ -(u ⬝ᵥ v) ∨ v ⬝ᵥ v ≤ θ := by
  by_cases hv : v ⬝ᵥ v ≤ θ
  · exact Or.inr (Or.inr hv)
  replace hv := not_le.1 hv
  have hl2u : l2 u = 1 := by simp [l2, hu]
  have hsq : √θ ≤ l2 v := Real.sqrt_le_sqrt hv.le
  have hpos : 0 < l2 v := lt_of_lt_of_le (Real.sqrt_pos.2 hθ) hsq
  rw [corr, hl2u, one_mul, abs_div, abs_of_pos hpos, lt_div_iff₀ hpos] at h
  have : 1 / 100 * √θ ≤ |u ⬝ᵥ v| := by linarith
  rcases le_abs.1 this with h' | h'
  · exact Or.inl h'
  · exact Or.inr (Or.inl h')

/-- The rows `Yᵢ = ∑ⱼ wⱼ Rᵢⱼ = (R w)ᵢ` for a unit vector `w`: they are independent, sub-Gaussian
with the proxy of the entries, and have second moment `σ²`. -/
theorem rows_facts_qz {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {R : Ω → Matrix (Fin n) (Fin n) ℝ} {σ : ℝ} {c : NNReal}
    (hind : iIndepFun (fun (ij : Fin n × Fin n) (ω : Ω) ↦ R ω ij.1 ij.2) P)
    (hmean : ∀ i j, ∫ ω, R ω i j ∂P = 0)
    (hvar : ∀ i j, Var[fun ω ↦ R ω i j; P] = σ ^ 2)
    (hsg : ∀ i j, HasSubgaussianMGF (fun ω ↦ R ω i j) c P)
    {w : Fin n → ℝ} (hw : ∑ j, w j ^ 2 = 1) :
    iIndepFun (fun i ω ↦ ∑ j, w j * R ω i j) P ∧
      (∀ i, HasSubgaussianMGF (fun ω ↦ ∑ j, w j * R ω i j) c P) ∧
      ∀ i, ∫ ω, (∑ j, w j * R ω i j) ^ 2 ∂P = σ ^ 2 := by
  have hrow : ∀ i, iIndepFun (fun j ω ↦ R ω i j) P := fun i ↦
    hind.precomp (g := fun j ↦ (i, j)) (fun _ _ h ↦ (Prod.mk.inj h).2)
  have hrows := rows_iIndepFun_qz hind (fun p ↦ (hsg p.1 p.2).aemeasurable)
  refine ⟨?_, fun i ↦ wsum_subG_qz (hrow i) (hsg i) w hw, fun i ↦ ?_⟩
  · exact hrows.comp (fun _ v ↦ ∑ j, w j * v j) (fun _ ↦ by fun_prop)
  · exact wsum_sq_integral_qz (hrow i) (fun j ↦ (hsg i j).memLp 2) (hmean i) (hvar i) w hw

/-- A bound on `μ.real s` gives a bound on `μ s`. -/
theorem measure_le_ofReal_qz {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {S : Set Ω} {b : ℝ} (h : P.real S ≤ b) : P S ≤ ENNReal.ofReal b := by
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h

/-- **Lemma 1.4 for fixed unit vectors** `u, w`: with `m = n σ⁴ / σ'⁴`,
`P(|corr u (R w)| > 1/100) ≤ 3 e^(-m/480000)`. -/
theorem fixed_unit_qz {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {R : Ω → Matrix (Fin n) (Fin n) ℝ} {σ σ' : ℝ} (hσ : 0 < σ)
    (hσ' : σ' ≠ 0) (hn : 0 < n)
    (hind : iIndepFun (fun (ij : Fin n × Fin n) (ω : Ω) ↦ R ω ij.1 ij.2) P)
    (hmean : ∀ i j, ∫ ω, R ω i j ∂P = 0)
    (hvar : ∀ i j, Var[fun ω ↦ R ω i j; P] = σ ^ 2)
    (hsg : ∀ i j, HasSubgaussianMGF (fun ω ↦ R ω i j) (σ' ^ 2).toNNReal P)
    {u w : Fin n → ℝ} (hu : u ⬝ᵥ u = 1) (hw : w ⬝ᵥ w = 1) :
    P {ω | 1 / 100 < |corr u (R ω *ᵥ w)|} ≤
      ENNReal.ofReal (3 * exp (-(n * σ ^ 4 / σ' ^ 4 / 480000))) := by
  set c : NNReal := (σ' ^ 2).toNNReal with hcdef
  have hc : (c : ℝ) = σ' ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hσ'2 : 0 < σ' ^ 2 := by positivity
  have hcpos : 0 < (c : ℝ) := by rw [hc]; exact hσ'2
  have hw' : ∑ j, w j ^ 2 = 1 := by simpa [dotProduct, sq] using hw
  have hu' : ∑ i, u i ^ 2 = 1 := by simpa [dotProduct, sq] using hu
  set Y : Fin n → Ω → ℝ := fun i ω ↦ ∑ j, w j * R ω i j with hY
  obtain ⟨hYind, hYsg, hY2⟩ := rows_facts_qz hind hmean hvar hsg hw'
  have hY4 : ∀ i, Integrable (fun ω ↦ Y i ω ^ 4) P ∧ ∫ ω, Y i ω ^ 4 ∂P ≤ 36 * (c : ℝ) ^ 2 :=
    fun i ↦ integral_pow_four_le_qz (hYsg i) hcpos
  have hY2i : ∀ i, Integrable (fun ω ↦ Y i ω ^ 2) P := fun i ↦
    ((hYsg i).memLp 2).integrable_sq
  have hσσ' : σ ^ 2 ≤ 6 * σ' ^ 2 := by
    have h := (sq_integral_sq_le_qz (hY2i ⟨0, hn⟩) (hY4 ⟨0, hn⟩).1).trans (hY4 ⟨0, hn⟩).2
    rw [hY2, hc] at h
    nlinarith [sq_nonneg σ, sq_nonneg σ']
  have hRw : ∀ ω i, (R ω *ᵥ w) i = Y i ω := fun ω i ↦ by
    simp [hY, Matrix.mulVec, dotProduct, mul_comm]
  set Z : Ω → ℝ := fun ω ↦ ∑ i, u i * Y i ω with hZ
  have hZsg : HasSubgaussianMGF Z c P := wsum_subG_qz hYind hYsg u hu'
  have huRw : ∀ ω, u ⬝ᵥ (R ω *ᵥ w) = Z ω := fun ω ↦ by
    simp [dotProduct, hRw, hZ]
  have hRwRw : ∀ ω, (R ω *ᵥ w) ⬝ᵥ (R ω *ᵥ w) = ∑ i, Y i ω ^ 2 := fun ω ↦ by
    simp [dotProduct, hRw, sq]
  set θ : ℝ := σ ^ 2 * n / 4 with hθ
  have hθpos : 0 < θ := by positivity
  set s : ℝ := 1 / 100 * √θ with hs
  have hs0 : 0 ≤ s := by positivity
  have hsub : {ω | 1 / 100 < |corr u (R ω *ᵥ w)|} ⊆
      ({ω | s ≤ Z ω} ∪ {ω | s ≤ (-Z) ω}) ∪ {ω | ∑ i, Y i ω ^ 2 ≤ θ} := by
    intro ω hω
    rcases corr_gt_imp_qz hu hθpos hω with h | h | h
    · exact Or.inl (Or.inl (by rw [Set.mem_ofPred_eq, ← huRw]; exact h))
    · exact Or.inl (Or.inr (by rw [Set.mem_ofPred_eq, Pi.neg_apply, ← huRw]; exact h))
    · exact Or.inr (by rw [Set.mem_ofPred_eq, ← hRwRw]; exact h)
  set E : ℝ := exp (-(n * σ ^ 4 / σ' ^ 4 / 480000)) with hE
  have hs2 : s ^ 2 = σ ^ 2 * n / 40000 := by
    rw [hs, mul_pow, Real.sq_sqrt hθpos.le, hθ]; ring
  have hB : exp (-s ^ 2 / (2 * c)) ≤ E := by
    rw [hE, exp_le_exp, hs2, hc, neg_div, neg_le_neg_iff]
    have key : n * σ ^ 4 / σ' ^ 4 / 480000 =
        σ ^ 2 * n / 40000 / (2 * σ' ^ 2) * (σ ^ 2 / (6 * σ' ^ 2)) := by
      field_simp; ring
    have hle1 : σ ^ 2 / (6 * σ' ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; exact hσσ'
    rw [key]
    exact mul_le_of_le_one_right (by positivity) hle1
  set l : ℝ := σ ^ 2 / (36 * σ' ^ 4) with hl
  have hC : exp (l * θ + Fintype.card (Fin n) *
      (-(l * σ ^ 2) + l ^ 2 * (36 * (c : ℝ) ^ 2) / 2)) ≤ E := by
    rw [hE, exp_le_exp, Fintype.card_fin, hc, hl, hθ]
    have key : σ ^ 2 / (36 * σ' ^ 4) * (σ ^ 2 * n / 4) + n * (-(σ ^ 2 / (36 * σ' ^ 4) * σ ^ 2) +
        (σ ^ 2 / (36 * σ' ^ 4)) ^ 2 * (36 * (σ' ^ 2) ^ 2) / 2) = -(n * σ ^ 4 / σ' ^ 4 / 144) := by
      field_simp; ring
    rw [key, neg_le_neg_iff]
    have : 0 ≤ n * σ ^ 4 / σ' ^ 4 := by positivity
    linarith
  have hP1 : P {ω | s ≤ Z ω} ≤ ENNReal.ofReal E :=
    measure_le_ofReal_qz ((hZsg.measure_ge_le hs0).trans hB)
  have hP2 : P {ω | s ≤ (-Z) ω} ≤ ENNReal.ofReal E :=
    measure_le_ofReal_qz ((hZsg.neg.measure_ge_le hs0).trans hB)
  have hP3 : P {ω | ∑ i, Y i ω ^ 2 ≤ θ} ≤ ENNReal.ofReal E :=
    measure_le_ofReal_qz ((lower_tail_sum_sq_qz hYind (fun i ↦ (hYsg i).aestronglyMeasurable)
      hY2i (fun i ↦ (hY4 i).1) hY2 (fun i ↦ (hY4 i).2) (by positivity) θ).trans hC)
  have hE0 : 0 ≤ E := (exp_pos _).le
  calc P {ω | 1 / 100 < |corr u (R ω *ᵥ w)|}
      ≤ P (({ω | s ≤ Z ω} ∪ {ω | s ≤ (-Z) ω}) ∪ {ω | ∑ i, Y i ω ^ 2 ≤ θ}) := measure_mono hsub
    _ ≤ P ({ω | s ≤ Z ω} ∪ {ω | s ≤ (-Z) ω}) + P {ω | ∑ i, Y i ω ^ 2 ≤ θ} :=
        measure_union_le _ _
    _ ≤ (P {ω | s ≤ Z ω} + P {ω | s ≤ (-Z) ω}) + P {ω | ∑ i, Y i ω ^ 2 ≤ θ} := by
        gcongr; exact measure_union_le _ _
    _ ≤ (ENNReal.ofReal E + ENNReal.ofReal E) + ENNReal.ofReal E := by gcongr
    _ = ENNReal.ofReal (3 * E) := by
        rw [← ENNReal.ofReal_add hE0 hE0, ← ENNReal.ofReal_add (by positivity) hE0]
        congr 1; ring

end B25.SG

namespace B25

open MeasureTheory ProbabilityTheory Matrix Real

/-- **Lemma 1.4** of [B25]: the statement of `B25.partiallyRotated_of_subgaussian`. -/
theorem partiallyRotated_of_subgaussian_main :
    ∃ c K : ℝ, 0 < c ∧
      ∀ (n d : ℕ) (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) {Ω : Type}
        [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : Ω → Matrix (Fin n) (Fin n) ℝ) (σ σ' : ℝ), 0 < σ → K * (σ' / σ) ^ 4 ≤ n →
        iIndepFun (fun (ij : Fin n × Fin n) (ω : Ω) ↦ R ω ij.1 ij.2) P →
        (∀ i j, ∫ ω, R ω i j ∂P = 0) →
        (∀ i j, Var[fun ω ↦ R ω i j; P] = σ ^ 2) →
        (∀ i j, HasSubgaussianMGF (fun ω ↦ R ω i j) (σ' ^ 2).toNNReal P) →
        PartiallyRotated P (fun ω ↦ rotateCols X S (R ω)) S (1 / 100) (c * σ ^ 4 / σ' ^ 4) := by
  refine ⟨1 / 960000, 1920000, by norm_num, ?_⟩
  intro n d X S Ω _ P _ R σ σ' hσ hK hind hmean hvar hsg α β hα hβ
  simp only [rotateCols_mulVec_of_mem _ _ _ hα, rotateCols_mulVec_of_not_mem _ _ _ hβ]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, mul_zero, neg_zero, exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  by_cases hσ' : σ' = 0
  · subst hσ'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, zero_mul,
      neg_zero, exp_zero, ENNReal.ofReal_one]
    exact prob_le_one
  have hm : 1920000 ≤ n * σ ^ 4 / σ' ^ 4 := by
    have h4 : 0 < σ' ^ 4 := by positivity
    have hσ4 : 0 < σ ^ 4 := by positivity
    rw [div_pow] at hK
    rw [le_div_iff₀ h4]
    calc 1920000 * σ' ^ 4 = 1920000 * (σ' ^ 4 / σ ^ 4) * σ ^ 4 := by field_simp
      _ ≤ n * σ ^ 4 := mul_le_mul_of_nonneg_right hK hσ4.le
  set a := X *ᵥ α with ha_def
  set b := X *ᵥ β with hb_def
  by_cases ha : a = 0
  · have : {ω | 1 / 100 < |corr a (R ω *ᵥ b)|} = ∅ := by
      ext ω; simp [ha, corr]
    rw [this, measure_empty]; exact zero_le
  by_cases hb : b = 0
  · have : {ω | 1 / 100 < |corr a (R ω *ᵥ b)|} = ∅ := by
      ext ω; simp [hb, corr]
    rw [this, measure_empty]; exact zero_le
  have hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < l2 x := fun x hx ↦ by
    refine lt_of_le_of_ne (l2_nonneg x) fun h ↦ hx ?_
    have := l2_sq x
    rw [← h] at this
    exact dotProduct_self_eq_zero.1 (by rw [← this]; ring)
  have hla := hpos a ha
  have hlb := hpos b hb
  have hunit : ∀ x : Fin n → ℝ, 0 < l2 x → ((l2 x)⁻¹ • x) ⬝ᵥ ((l2 x)⁻¹ • x) = 1 :=
    fun x hx ↦ by
      rw [smul_dotProduct, dotProduct_smul, ← l2_sq, smul_eq_mul, smul_eq_mul]
      field_simp
  have hset : {ω | 1 / 100 < |corr a (R ω *ᵥ b)|} =
      {ω | 1 / 100 < |corr ((l2 a)⁻¹ • a) (R ω *ᵥ ((l2 b)⁻¹ • b))|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [Matrix.mulVec_smul, corr_smul_left (inv_pos.2 hla), corr_smul_right (inv_pos.2 hlb)]
  rw [hset]
  refine (SG.fixed_unit_qz hσ hσ' hn hind hmean hvar hsg (hunit a hla) (hunit b hlb)).trans ?_
  apply ENNReal.ofReal_le_ofReal
  set m := n * σ ^ 4 / σ' ^ 4 with hm_def
  have h3 : (3 : ℝ) ≤ exp (m / 960000) := by
    have := add_one_le_exp (m / 960000)
    have : 2 ≤ m / 960000 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  calc 3 * exp (-(m / 480000)) ≤ exp (m / 960000) * exp (-(m / 480000)) := by gcongr
    _ = exp (-(1 / 960000 * σ ^ 4 / σ' ^ 4 * n)) := by
        rw [← exp_add, hm_def]; congr 1; ring

end B25
