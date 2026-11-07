module

public import BHSV25.BK.InvarianceBonami
public import Mathlib.Probability.UniformOn

/-!
# The three-valued ensemble of a random subcube

For `M ≥ 2`, `ρ = 1 - 1/M` and `r = √ρ` (`BHSV25.BK.Aint.rM`), a uniform pair
`(zᵢ, aᵢ) ∈ {0,1} × [M]` gives the normalized variable `Uᵢ = [aᵢ ≠ 0] χ(zᵢ) / r`
(`BHSV25.BK.Aint.u3`, `χ = bitSign`): `0` with probability `1/M` and `±1/r` with probability
`(1 - 1/M)/2` each. Its law `law3 M` has mean `0`, variance `1`, third moment `0` and fourth moment
`1/ρ ≤ 2`, so it is a good law for the Bonami lemma and the Lindeberg replacement
(`BHSV25.BK.Aint.goodLaw_law3`).

* `BHSV25.BK.Aint.expect_eq_integral_law3`: `E_{z,a} F(U(z,a)) = ∫ F d(law3 M)^{⊗R}` for
  continuous `F`.
* `BHSV25.BK.Aint.subcube_eq`: the average of `g` on the subcube that frees the coordinates
  `{j : aⱼ = 0}` and fixes the others to `z` is `Σ_S ĝ(S) Π_{i∈S} [aᵢ ≠ 0] χ(zᵢ)`, i.e. the
  smoothed polynomial `mlEval (smoothC r ĝ)` evaluated at `U(z, a)`.
-/

@[expose] public section

namespace BHSV25.BK.Aint

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic

variable {R M : ℕ}

/-- The noise rate `r = √(1 - 1/M)`. -/
noncomputable def rM (M : ℕ) : ℝ := √(1 - 1 / M)

/-- The normalized coordinate `[a ≠ 0] χ(z) / r` of the ensemble. -/
noncomputable def u3 (M : ℕ) (p : Bool × Fin M) : ℝ :=
  if (p.2 : ℕ) = 0 then 0 else bitSign p.1 / rM M

/-- The uniform probability measure on `{0,1} × [M]`. -/
noncomputable def unifΩ (M : ℕ) : Measure (Bool × Fin M) := uniformOn Set.univ

/-- The law of `u3` under the uniform measure. -/
noncomputable def law3 (M : ℕ) : Measure ℝ := (unifΩ M).map (u3 M)

/-! ### The noise rate -/

theorem one_sub_inv_pos (hM : 2 ≤ M) : 0 < 1 - 1 / (M : ℝ) := by
  have h : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

theorem rM_pos (hM : 2 ≤ M) : 0 < rM M := Real.sqrt_pos.2 (one_sub_inv_pos hM)

theorem rM_sq (hM : 2 ≤ M) : rM M ^ 2 = 1 - 1 / M := Real.sq_sqrt (one_sub_inv_pos hM).le

theorem rM_lt_one (hM : 2 ≤ M) : rM M < 1 := by
  have h : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have h1 : 0 < 1 / (M : ℝ) := by positivity
  have := rM_sq hM
  nlinarith [rM_pos hM]

/-- `r ≤ 1 - 1/(2M)`, so the reverse hypercontractive inequality applies with `k = 2M`. -/
theorem rM_le (hM : 2 ≤ M) : rM M ≤ 1 - 1 / (2 * M) := by
  have h : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hb : 0 ≤ 1 - 1 / (2 * (M : ℝ)) := by
    rw [sub_nonneg, div_le_one (by linarith)]
    linarith
  have hsq : rM M ^ 2 ≤ (1 - 1 / (2 * (M : ℝ))) ^ 2 := by
    rw [rM_sq hM]
    have e : (1 - 1 / (2 * (M : ℝ))) ^ 2 = 1 - 1 / M + (1 / (2 * M)) ^ 2 := by
      field_simp
      ring
    rw [e]
    nlinarith [sq_nonneg (1 / (2 * (M : ℝ)))]
  exact (pow_le_pow_iff_left₀ (rM_pos hM).le hb (by norm_num)).1 hsq

/-! ### The uniform measure and the law of `u3` -/

theorem nonempty_fin (hM : 0 < M) : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩

theorem isProb_unifΩ (hM : 0 < M) : IsProbabilityMeasure (unifΩ M) := by
  have := nonempty_fin hM
  unfold unifΩ
  infer_instance

theorem unifΩ_real_singleton (p : Bool × Fin M) :
    (unifΩ M).real {p} = ((2 * M : ℕ) : ℝ)⁻¹ := by
  rw [Measure.real, unifΩ, uniformOn_univ, Measure.count_singleton, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin, ENNReal.toReal_div, ENNReal.toReal_one]
  simp

theorem integral_unifΩ (hM : 0 < M) (f : Bool × Fin M → ℝ) :
    ∫ p, f p ∂unifΩ M = 𝔼 p, f p := by
  have := isProb_unifΩ hM
  rw [integral_fintype Integrable.of_finite, Finset.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [unifΩ_real_singleton, smul_eq_mul, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin]
  field_simp

theorem measurable_u3 : Measurable (u3 M) := measurable_of_countable _

theorem isProb_law3 (hM : 0 < M) : IsProbabilityMeasure (law3 M) := by
  have := isProb_unifΩ hM
  unfold law3
  infer_instance

theorem integral_law3 (hM : 0 < M) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂law3 M = 𝔼 p, f (u3 M p) := by
  rw [law3, integral_map measurable_u3.aemeasurable hf.aestronglyMeasurable]
  exact integral_unifΩ hM _

/-- `E φ(U) = φ(0)/M + ((M-1)/(2M)) (φ(1/r) + φ(-1/r))`. -/
theorem expect_u3 (hM : 0 < M) (φ : ℝ → ℝ) :
    𝔼 p, φ (u3 M p) = φ 0 / M + (M - 1) / (2 * M) * (φ (1 / rM M) + φ (-(1 / rM M))) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin, Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  have hs : ∀ (b : Bool) (j : Fin m), u3 (m + 1) (b, j.succ) = bitSign b / rM (m + 1) := by
    intro b j
    simp [u3]
  have h0 : ∀ b : Bool, u3 (m + 1) (b, 0) = 0 := fun b ↦ by simp [u3]
  simp only [hs, h0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [bitSign, ite_true, Bool.false_eq_true, ite_false]
  push_cast
  field_simp
  ring

theorem goodLaw_law3 (hM : 2 ≤ M) : GoodLaw (law3 M) := by
  have hM0 : 0 < M := by omega
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have := isProb_unifΩ hM0
  have hr := rM_pos hM
  have hr2 := rM_sq hM
  have mom : ∀ k : ℕ, ∫ x, x ^ k ∂law3 M =
      (0 : ℝ) ^ k / M + (M - 1) / (2 * M) * ((1 / rM M) ^ k + (-(1 / rM M)) ^ k) := fun k ↦ by
    rw [integral_law3 hM0 (continuous_pow k)]
    exact expect_u3 hM0 (fun x ↦ x ^ k)
  have hrinv : (1 / rM M) ^ 2 = M / (M - 1) := by
    rw [div_pow, hr2]
    field_simp
  refine ⟨isProb_law3 hM0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [law3, integrable_map_measure (continuous_pow 4).aestronglyMeasurable
      measurable_u3.aemeasurable]
    exact Integrable.of_finite
  · have := mom 1
    simp only [pow_one] at this
    rw [this]
    ring
  · rw [mom 2, neg_sq, hrinv]
    have : (M : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  · rw [mom 3]
    ring
  · rw [mom 4, show (-(1 / rM M)) ^ 4 = ((1 / rM M) ^ 2) ^ 2 by ring,
      show (1 / rM M) ^ 4 = ((1 / rM M) ^ 2) ^ 2 by ring, hrinv]
    have h1 : (0 : ℝ) < M - 1 := by linarith
    rw [show (0 : ℝ) ^ 4 / M + (M - 1) / (2 * M) * ((M / (M - 1)) ^ 2 + (M / (M - 1)) ^ 2) =
      M / (M - 1) by field_simp; ring]
    rw [div_le_iff₀ h1]
    linarith

/-! ### Products -/

/-- The expectation of a product of functions of distinct coordinates. -/
theorem expect_pi_prod {α : Type*} [Fintype α] [Nonempty α] (h : Fin R → α → ℝ) :
    𝔼 y : Fin R → α, ∏ j, h j (y j) = ∏ j, 𝔼 b, h j b := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Fintype.prod_sum]
  push_cast
  ring

theorem expect_prod_univ {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    𝔼 p, f p = 𝔼 a, 𝔼 b, f (a, b) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

/-- `E_{z,a} F(U(z, a)) = ∫ F d(law3 M)^{⊗R}`. -/
theorem expect_eq_integral_law3 (hM : 0 < M) (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    (𝔼 z : Cube (Fin R), 𝔼 a : Fin R → Fin M, F (fun j ↦ u3 M (z j, a j))) =
      ∫ y, F y ∂Measure.pi (fun _ : Fin R ↦ law3 M) := by
  have := isProb_unifΩ hM
  have := nonempty_fin hM
  have : ∀ _ : Fin R, SigmaFinite ((unifΩ M).map (u3 M)) := fun _ ↦ by
    have := isProb_law3 hM
    unfold law3 at this
    infer_instance
  have hmap : Measure.pi (fun _ : Fin R ↦ law3 M) =
      (Measure.pi fun _ : Fin R ↦ unifΩ M).map (fun ω j ↦ u3 M (ω j)) := by
    rw [Measure.pi_map_pi (fun _ ↦ measurable_u3.aemeasurable)]
    rfl
  rw [hmap, integral_map (measurable_of_countable _).aemeasurable hF.aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  have hsing : ∀ ω : Fin R → Bool × Fin M,
      (Measure.pi fun _ : Fin R ↦ unifΩ M).real {ω} = (((2 * M : ℕ) : ℝ)⁻¹) ^ R := by
    intro ω
    rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod]
    simp only [← Measure.real_def, unifΩ_real_singleton, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  simp only [hsing, smul_eq_mul]
  rw [← Finset.mul_sum]
  have e1 : 𝔼 ω : Fin R → Bool × Fin M, F (fun j ↦ u3 M (ω j)) =
      (((2 * M : ℕ) : ℝ)⁻¹) ^ R * ∑ ω : Fin R → Bool × Fin M, F (fun j ↦ u3 M (ω j)) := by
    rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fun, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rw [inv_pow, div_eq_inv_mul]
  rw [← e1]
  rw [Fintype.expect_equiv (Equiv.arrowProdEquivProdArrow (Fin R) (fun _ ↦ Bool)
    (fun _ ↦ Fin M)) (fun ω ↦ F (fun j ↦ u3 M (ω j)))
    (fun p ↦ F (fun j ↦ u3 M (p.1 j, p.2 j))) (fun ω ↦ rfl)]
  rw [expect_prod_univ]

/-! ### Subcube averages -/

theorem expect_bitSign_and (b : Bool) : 𝔼 y : Bool, bitSign (b && y) = if b then 0 else 1 := by
  cases b <;> simp [Finset.expect_eq_sum_div_card, bitSign]

/-- The average of `g` on the subcube that frees `{j : aⱼ = 0}` and fixes the other coordinates
to `z` is the smoothed polynomial `mlEval (smoothC r ĝ)` at `U(z, a)`. -/
theorem subcube_eq (hM : 2 ≤ M) (g : Cube (Fin R) → ℝ) (z : Cube (Fin R))
    (a : Fin R → Fin M) :
    (𝔼 y : Cube (Fin R), g (fun j ↦ if (a j : ℕ) = 0 then y j else z j)) =
      mlEval (smoothC (rM M) (coefficient g)) (fun j ↦ u3 M (z j, a j)) := by
  have hr := (rM_pos hM).ne'
  rw [← MultilinearGauss.mlEval_mul_arg]
  have hU : (fun j ↦ rM M * u3 M (z j, a j)) =
      fun j ↦ if (a j : ℕ) = 0 then 0 else bitSign (z j) := by
    funext j
    unfold u3
    split_ifs
    · simp
    · field_simp
  rw [hU, mlEval]
  simp_rw [← walsh_inversion g]
  rw [Finset.expect_sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← Finset.mul_expect]
  congr 1
  unfold walsh
  rw [expect_pi_prod (fun i y ↦ bitSign (s i && if (a i : ℕ) = 0 then y else z i))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  by_cases ha : (a i : ℕ) = 0
  · simp only [ha, ite_true]
    rw [expect_bitSign_and]
  · simp only [ha, ite_false]
    cases s i <;> simp [bitSign]

end BHSV25.BK.Aint
