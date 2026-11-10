module

public import BGHKLMM26.Boolean
public import BGHKLMM26.RobustMIS.Final
public import BGHKLMM26.Hardness.Decoder

/-!
# Robust Majority is Stablest in the definitions of `Boolean.lean`

[BGHKLMM26, Theorem 7.1] as stated in `BGHKLMM26/Challenge.lean`
(`BGHKLMM26.RobustMIS.robust_majority_is_stablest_cube`), from `BGHKLMM26.RobustMIS.robustMIS`.

* **The definitions agree** with those of the proof: the influence with OpenAI's Walsh influence
  (`cubeInfluence_eq`, the characters differ by the sign `(-1)^{|S|}`), the cut value with
  `BGHKLMM26.Hard.cutValue` (`cubeCut_eq`, through the pair probabilities of `corrAverage`), and the
  LTFs of `BGHKLMM26.Hard.IsLTF` are LTFs here (`isCubeLTF_of_isLTF`).
* **The form of the statement.** `robustMIS` gives, for each `ξ > 0`, a `τ` below which the error is
  `C √η + ξ`, for `η ≤ η₀`; here the function `h(τ)` is the least such `ξ`, capped at `1`, and
  `η > η₀` is covered by `L¹` distances at most `1` and a larger constant.
-/

public section

namespace BGHKLMM26.RobustMIS.Statement

open Finset
open scoped BigOperators
open OAI.MaxCutGames.Foundations.Hastad OAI.OptimalMaxCut.Analytic
  OAI.OptimalMaxCut.GaussianBellman OAI.OptimalMaxCut.MISProof

variable {R : ℕ}

/-! ### Influences -/

/-- Subsets of `Fin R` and their indicators. -/
def subsetEquiv (R : ℕ) : (Fin R → Bool) ≃ Finset (Fin R) where
  toFun s := univ.filter fun i ↦ s i = true
  invFun S i := decide (i ∈ S)
  left_inv s := by funext i; simp
  right_inv S := by ext i; simp

theorem mem_subsetEquiv (s : Fin R → Bool) (i : Fin R) : i ∈ subsetEquiv R s ↔ s i = true := by
  simp [subsetEquiv]

/-- OpenAI's Walsh character is `(-1)^{|S|} χ_S`. -/
theorem walsh_eq (s x : Fin R → Bool) :
    walsh s x = (-1) ^ (subsetEquiv R s).card * ∏ i ∈ subsetEquiv R s, cubeSign (x i) := by
  rw [← prod_neg]
  simp only [subsetEquiv, Equiv.coe_fn_mk, prod_filter, walsh]
  refine prod_congr rfl fun i _ ↦ ?_
  cases s i <;> cases x i <;> norm_num [bitSign, cubeSign]

theorem card_cube : (Fintype.card (Fin R → Bool) : ℝ) = 2 ^ R := by
  simp

theorem coefficient_eq (f : (Fin R → Bool) → ℝ) (s : Fin R → Bool) :
    coefficient f s = (-1) ^ (subsetEquiv R s).card * cubeFourier f (subsetEquiv R s) := by
  rw [coefficient, expect_eq_sum_div_card, card_univ, card_cube, cubeFourier, mul_div_assoc',
    mul_sum]
  congr 1
  refine sum_congr rfl fun x _ ↦ ?_
  rw [walsh_eq]
  ring

theorem cubeInfluence_eq (f : (Fin R → Bool) → ℝ) (i : Fin R) :
    cubeInfluence f i = influence i f := by
  rw [cubeInfluence, influence, sum_filter, sum_filter]
  refine (Fintype.sum_equiv (subsetEquiv R) _ _ fun s ↦ ?_).symm
  rw [coefficient_eq, mul_pow, ← pow_mul, mul_comm _ 2, pow_mul]
  simp [mem_subsetEquiv]

/-! ### The cut value -/

theorem prod_bitPairWeight (t : ℝ) (x y : Fin R → Bool) :
    ∏ i, bitPairWeight t (x i) (y i) = corrProb t x y := by
  have h (i : Fin R) : bitPairWeight t (x i) (y i) =
      (if x i = y i then (1 + t) / 2 else (1 - t) / 2) / 2 := by
    cases x i <;> cases y i <;> norm_num [bitPairWeight, sign] <;> ring
  simp only [h, prod_div_distrib, prod_const, card_univ, Fintype.card_fin, corrProb]

/-- `corrAverage` is the expectation over `t`-correlated pairs. -/
theorem corrAverage_eq_sum (t : ℝ) (F : (Fin R → Bool) → (Fin R → Bool) → ℝ) :
    corrAverage t R F = ∑ x, ∑ y, corrProb t x y * F x y := by
  have hF : F = fun x y ↦ ∑ x₀, ∑ y₀,
      F x₀ y₀ * ((if x = x₀ then (1 : ℝ) else 0) * (if y = y₀ then 1 else 0)) := by
    funext x y
    simp [mul_ite]
  conv_lhs => rw [hF]
  rw [corrAverage_sum]
  refine sum_congr rfl fun x₀ _ ↦ ?_
  rw [corrAverage_sum]
  refine sum_congr rfl fun y₀ _ ↦ ?_
  rw [corrAverage_const_mul, Hard.corrAverage_point, prod_bitPairWeight, mul_comm]

theorem cubeCut_eq (ρ : ℝ) (f : (Fin R → Bool) → ℝ) : cubeCut ρ f = Hard.cutValue ρ f := by
  rw [cubeCut, Hard.cutValue, corrAverage_eq_sum]

/-! ### Linear threshold functions -/

theorem isCubeLTF_of_isLTF {L : (Fin R → Bool) → Bool} (hL : Hard.IsLTF L) :
    IsCubeLTF fun x ↦ Hard.bitVal (L x) := by
  obtain ⟨w, θ, h⟩ := hL
  refine ⟨fun i ↦ -w i, -θ, fun x ↦ ?_⟩
  dsimp only
  have hs : ∑ i, -w i * cubeSign (x i) + -θ = ∑ i, w i * bitSign (x i) - θ := by
    rw [sub_eq_add_neg]
    congr 1
    refine sum_congr rfl fun i _ ↦ ?_
    cases x i <;> norm_num [cubeSign, bitSign]
  rw [h x, hs]
  by_cases hθ : θ ≤ ∑ i, w i * bitSign (x i)
  · simp [Hard.bitVal, hθ]
  · have h0 : ¬ 0 ≤ ∑ i, w i * bitSign (x i) - θ := fun h0 ↦ hθ (by linarith)
    simp [Hard.bitVal, hθ, h0]

theorem cubeL1_bitVal (f : (Fin R → Bool) → ℝ) (L : (Fin R → Bool) → Bool) :
    cubeL1 f (fun x ↦ Hard.bitVal (L x)) = 𝔼 x, |f x - Hard.bitVal (L x)| := by
  rw [cubeL1, expect_eq_sum_div_card, card_univ, card_cube]

instance (R : ℕ) : Nonempty {L : (Fin R → Bool) → Bool // Hard.IsLTF L} :=
  ⟨⟨fun _ ↦ false, 0, 1, fun x ↦ by simp⟩⟩

/-- The distance to the LTFs is attained. -/
theorem exists_ltf_le_ltfDist (f : (Fin R → Bool) → ℝ) :
    ∃ L : (Fin R → Bool) → Bool, Hard.IsLTF L ∧
      𝔼 x, |f x - Hard.bitVal (L x)| ≤ Hard.ltfDist f := by
  obtain ⟨⟨L, hL⟩, hmin⟩ :=
    Finite.exists_min fun L : {L : (Fin R → Bool) → Bool // Hard.IsLTF L} ↦
      𝔼 x, |f x - Hard.bitVal (L.1 x)|
  exact ⟨L, hL, le_ciInf hmin⟩

/-- A function with values in `[0, 1]` is within `1` of the LTF `0`. -/
theorem ltfDist_le_one {f : (Fin R → Bool) → ℝ} (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    Hard.ltfDist f ≤ 1 := by
  have hbdd : BddBelow (Set.range fun L : {L : (Fin R → Bool) → Bool // Hard.IsLTF L} ↦
      𝔼 x, |f x - Hard.bitVal (L.1 x)|) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨L, rfl⟩
    exact expect_nonneg fun x _ ↦ abs_nonneg _
  refine (ciInf_le hbdd ⟨fun _ ↦ false, 0, 1, fun x ↦ by simp⟩).trans ?_
  refine expect_le univ_nonempty fun x _ ↦ ?_
  simp only [Hard.bitVal, Bool.false_eq_true, ↓reduceIte, sub_zero]
  rw [abs_of_nonneg (hf x).1]
  exact (hf x).2

/-! ### Theorem 7.1 -/

/-- **Robust Majority is Stablest** [BGHKLMM26, Theorem 7.1], as stated in `Challenge.lean`. -/
theorem robust_majority_is_stablest_cube :
    ∀ ρ : ℝ, -1 < ρ → ρ < 0 →
      ∃ (C : ℝ) (h : ℝ → ℝ), (∀ τ ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ h τ) ∧
        Filter.Tendsto h (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ (R : ℕ) (f : (Fin R → Bool) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
          ∀ τ ∈ Set.Ioc (0 : ℝ) 1, (∀ i, cubeInfluence f i ≤ τ) →
          ∀ η : ℝ, 0 ≤ η → Real.arccos ρ / Real.pi - η ≤ cubeCut ρ f →
            ∃ L, IsCubeLTF L ∧ cubeL1 f L ≤ C * Real.sqrt η + h τ := by
  intro ρ hρ1 hρ0
  obtain ⟨C, η₀, hC, hη₀, -, H⟩ := robustMIS ρ hρ1 hρ0
  set C' := max C (1 / Real.sqrt η₀) with hC'def
  have hC' : 0 < C' := lt_max_of_lt_left hC
  -- `ξ ∈ S τ`: the error `C' √η + ξ` holds for every function with influences at most `τ`.
  let S : ℝ → Set ℝ := fun τ ↦ {ξ | ξ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ (R : ℕ) (f : (Fin R → Bool) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, cubeInfluence f i ≤ τ) → ∀ η : ℝ, 0 ≤ η →
        Real.arccos ρ / Real.pi - η ≤ cubeCut ρ f → Hard.ltfDist f ≤ C' * Real.sqrt η + ξ}
  have h1 (τ : ℝ) : (1 : ℝ) ∈ S τ := by
    refine ⟨⟨zero_le_one, le_rfl⟩, fun R f hf _ η _ _ ↦ (ltfDist_le_one hf).trans ?_⟩
    have := mul_nonneg hC'.le (Real.sqrt_nonneg η)
    linarith
  have hbdd (τ : ℝ) : BddBelow (S τ) := ⟨0, fun ξ hξ ↦ hξ.1.1⟩
  have hh0 (τ : ℝ) : 0 ≤ sInf (S τ) := le_csInf ⟨1, h1 τ⟩ fun ξ hξ ↦ hξ.1.1
  -- Each `ξ ∈ (0, 1]` is in `S τ` for small `τ`.
  have hgood (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) : ∃ τ₀ > 0, ∀ τ ≤ τ₀, ξ ∈ S τ := by
    obtain ⟨τ₀, hτ₀, Hτ⟩ := H ξ hξ
    refine ⟨τ₀, hτ₀, fun τ hτ ↦ ⟨⟨hξ.le, hξ1⟩, fun R f hf hinf η hη hcut ↦ ?_⟩⟩
    by_cases hηη : η ≤ η₀
    · have hd := Hτ R f (fun x ↦ hf x) (fun i ↦ (cubeInfluence_eq f i ▸ hinf i).trans hτ) η hη
        hηη (cubeCut_eq ρ f ▸ hcut)
      have : C * Real.sqrt η ≤ C' * Real.sqrt η :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg η)
      linarith
    · have hs0 : 0 < Real.sqrt η₀ := Real.sqrt_pos.mpr hη₀
      have hs : Real.sqrt η₀ ≤ Real.sqrt η := Real.sqrt_le_sqrt (le_of_not_ge hηη)
      have h1' : 1 ≤ C' * Real.sqrt η :=
        calc (1 : ℝ) = 1 / Real.sqrt η₀ * Real.sqrt η₀ := by field_simp
          _ ≤ C' * Real.sqrt η := mul_le_mul (le_max_right _ _) hs hs0.le hC'.le
      linarith [ltfDist_le_one hf]
  refine ⟨C', fun τ ↦ sInf (S τ), fun τ _ ↦ hh0 τ, ?_, ?_⟩
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨τ₀, hτ₀, Hτ⟩ := hgood (min (ε / 2) 1) (by positivity) (min_le_right _ _)
    refine ⟨τ₀, hτ₀, fun {τ} hτ hτd ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (Set.mem_Ioi.mp hτ)] at hτd
    have hle : sInf (S τ) ≤ min (ε / 2) 1 := csInf_le (hbdd τ) (Hτ τ hτd.le)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hh0 τ)]
    linarith [min_le_left (ε / 2) 1]
  · intro R f hf τ _ hinf η hη hcut
    obtain ⟨L, hL, hLd⟩ := exists_ltf_le_ltfDist f
    refine ⟨fun x ↦ Hard.bitVal (L x), isCubeLTF_of_isLTF hL, ?_⟩
    rw [cubeL1_bitVal]
    have : Hard.ltfDist f - C' * Real.sqrt η ≤ sInf (S τ) :=
      le_csInf ⟨1, h1 τ⟩ fun ξ hξ ↦ by linarith [hξ.2 R f hf hinf η hη hcut]
    linarith

end BGHKLMM26.RobustMIS.Statement
