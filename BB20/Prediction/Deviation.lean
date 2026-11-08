module

public import BB20.Prediction.Contraction
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Jensen

/-!
# Uniform deviation of empirical means

`M` independent samples `X₁, …, X_M` from a law `μ` on a finite set `Ω` have the law
`∏ₖ μ(Xₖ)` on `Fin M → Ω`; expectations are finite sums. For a finite class of functions
`f_i : Ω → ℝ` that are contractions of linear scores `t_i = ∑_{j ∈ F} W_{ij} z_j` (features
`|z_j| ≤ 1`, weights `∑_j |W_{ij}| ≤ B`): `|f_i - f_{i'}| ≤ |t_i - t_{i'}|` and `|f_i| ≤ |t_i|`
pointwise, the deviation `D_i(X) = ∑ₖ (E f_i - f_i(Xₖ))` satisfies
`P(∃ i, D_i(X) > M η) ≤ 2 |F| exp(-M η² / (8 B²))` (`BB20.Prediction.prob_sup_dev_le`), whatever
the number of functions.

The proof bounds `E exp(c sup_i D_i) ≤ 2 |F| exp(2 c² B² M)`
(`BB20.Prediction.sum_exp_sup_dev_le`):
* **ghost sample**: `D_i(X) = E_Y ∑ₖ (f_i(Yₖ) - f_i(Xₖ))` for an independent copy `Y`, and Jensen's
  inequality for `exp`;
* **symmetrization**: exchanging `Xₖ` and `Yₖ` for any set of `k` preserves the law of `(X, Y)`
  (`BB20.Prediction.sum_swap`), so random signs `εₖ` can be inserted; then
  `exp(½ a + ½ b) ≤ ½ eᵃ + ½ eᵇ` separates `X` from `Y`;
* **contraction and Massart's lemma** (`BB20.Prediction.sum_exp_sup_le`);
* then **Chernoff's bound** with `c = η / (4 B²)`.
-/

@[expose] public section

namespace BB20.Prediction

open Real Finset

variable {Ω : Type*} {μ : Ω → ℝ}

theorem sum_prod_weight [Fintype Ω] (hμ1 : ∑ x, μ x = 1) (M : ℕ) :
    ∑ X : Fin M → Ω, ∏ k, μ (X k) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin M) x ↦ μ x)]
  simp [hμ1]

theorem prod_weight_nonneg (hμ : ∀ x, 0 ≤ μ x) {M : ℕ} (X : Fin M → Ω) :
    0 ≤ ∏ k, μ (X k) :=
  Finset.prod_nonneg fun _ _ ↦ hμ _

/-- The `k`-th sample has law `μ`. -/
theorem sum_prod_weight_mul_apply [Fintype Ω] (hμ1 : ∑ x, μ x = 1) {M : ℕ} (k : Fin M) (g : Ω → ℝ) :
    ∑ X : Fin M → Ω, (∏ j, μ (X j)) * g (X k) = ∑ x, μ x * g x := by
  have h : ∀ X : Fin M → Ω, (∏ j, μ (X j)) * g (X k) =
      ∏ j, (μ (X j) * if j = k then g (X j) else 1) := by
    intro X
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']
    simp
  simp_rw [h]
  rw [← Fintype.prod_sum (fun j x ↦ μ x * if j = k then g x else 1)]
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [hj, hμ1]
  · simp

/-- Jensen's inequality for `exp`. -/
theorem exp_sum_le_sum_exp {α : Type*} (s : Finset α) (w a : α → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) : exp (∑ i ∈ s, w i * a i) ≤ ∑ i ∈ s, w i * exp (a i) := by
  simpa [smul_eq_mul] using convexOn_exp.map_sum_le hw hw1 (fun i _ ↦ Set.mem_univ (a i))

/-- Exchange the `k`-th coordinates of two samples for the `k` with `ε k = false`. -/
def swapPair {M : ℕ} (ε : Fin M → Bool) (p : (Fin M → Ω) × (Fin M → Ω)) :
    (Fin M → Ω) × (Fin M → Ω) :=
  (fun k ↦ if ε k then p.1 k else p.2 k, fun k ↦ if ε k then p.2 k else p.1 k)

theorem swapPair_involutive {M : ℕ} (ε : Fin M → Bool) :
    Function.Involutive (swapPair (Ω := Ω) ε) := by
  intro p
  ext k <;> simp only [swapPair] <;> split_ifs <;> rfl

/-- Exchanging coordinates of two independent samples preserves their joint law. -/
theorem sum_swap [Fintype Ω] (μ : Ω → ℝ) {M : ℕ} (ε : Fin M → Bool)
    (H : (Fin M → Ω) → (Fin M → Ω) → ℝ) :
    ∑ X : Fin M → Ω, ∑ Y : Fin M → Ω, (∏ k, μ (X k)) * (∏ k, μ (Y k)) * H X Y =
      ∑ X : Fin M → Ω, ∑ Y : Fin M → Ω, (∏ k, μ (X k)) * (∏ k, μ (Y k)) *
        H (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
    ← Equiv.sum_comp (swapPair_involutive (Ω := Ω) ε).toPerm]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  simp only [Function.Involutive.coe_toPerm, swapPair]
  congr 1
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  split_ifs <;> ring

variable [Fintype Ω] {ι κ : Type*} [Finite ι] [Nonempty ι]

/-- The exponential moment of the largest deviation: `E exp(c sup_i D_i) ≤ 2 |F| exp(2 c² B² M)`
for `c ≥ 0`. -/
theorem sum_exp_sup_dev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (F : Finset κ) (hF : F.Nonempty) (feat : κ → Ω → ℝ) (hfeat : ∀ j ∈ F, ∀ x, |feat j x| ≤ 1)
    (W : ι → κ → ℝ) {B : ℝ} (hW : ∀ i, ∑ j ∈ F, |W i j| ≤ B) (f : ι → Ω → ℝ)
    (hf1 : ∀ i i' x,
      |f i x - f i' x| ≤ |∑ j ∈ F, W i j * feat j x - ∑ j ∈ F, W i' j * feat j x|)
    (hf2 : ∀ i x, |f i x| ≤ |∑ j ∈ F, W i j * feat j x|) (M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ∑ X : Fin M → Ω, (∏ k, μ (X k)) *
        exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k))) ≤
      2 * F.card * exp (2 * c ^ 2 * B ^ 2 * M) := by
  set P : (Fin M → Ω) → ℝ := fun X ↦ ∏ k, μ (X k) with hP
  have hP0 : ∀ X, 0 ≤ P X := fun X ↦ prod_weight_nonneg hμ X
  have hP1 : ∑ X, P X = 1 := sum_prod_weight hμ1 M
  set K : ℝ := 2 * (F.card : ℝ) * exp (2 * c ^ 2 * B ^ 2 * M) with hK
  set G : (Fin M → Ω) → (Fin M → Ω) → ℝ := fun X Y ↦ ⨆ i, c * ∑ k, (f i (Y k) - f i (X k))
    with hG
  -- the ghost sample
  have ha : ∀ X, exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k))) ≤
      ∑ Y, P Y * exp (G X Y) := by
    intro X
    have h1 : ∀ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)) =
        ∑ Y, P Y * (c * ∑ k, (f i (Y k) - f i (X k))) := by
      intro i
      have e : ∀ Y, P Y * (c * ∑ k, (f i (Y k) - f i (X k))) =
          ∑ k, c * (P Y * f i (Y k) - P Y * f i (X k)) := by
        intro Y
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
      simp_rw [e]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1, one_mul]
      simp only [hP]
      rw [sum_prod_weight_mul_apply hμ1 k (f i)]
    have h2 : (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k))) ≤ ∑ Y, P Y * G X Y := by
      refine ciSup_le fun i ↦ ?_
      rw [h1 i]
      exact Finset.sum_le_sum fun Y _ ↦ mul_le_mul_of_nonneg_left
        (le_ciSup_of_finite (fun i ↦ c * ∑ k, (f i (Y k) - f i (X k))) i) (hP0 Y)
    calc exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)))
        ≤ exp (∑ Y, P Y * G X Y) := exp_le_exp.2 h2
      _ ≤ ∑ Y, P Y * exp (G X Y) := exp_sum_le_sum_exp _ _ _ (fun Y _ ↦ hP0 Y) hP1
  -- symmetrization, contraction and Massart's lemma, for fixed samples
  have hb : ∀ X Y : Fin M → Ω, (2 ^ M : ℝ)⁻¹ * ∑ ε : Fin M → Bool,
      exp (G (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k)) ≤ K := by
    intro X Y
    have hsw : ∀ ε : Fin M → Bool,
        G (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k) ≤
          1 / 2 * (⨆ i, ∑ k, spin (ε k) * (2 * c * f i (Y k))) +
            1 / 2 * (⨆ i, ∑ k, spin (ε k) * (-(2 * c * f i (X k)))) := by
      intro ε
      refine ciSup_le fun i ↦ ?_
      have e : c * ∑ k, (f i (if ε k then Y k else X k) - f i (if ε k then X k else Y k)) =
          1 / 2 * (∑ k, spin (ε k) * (2 * c * f i (Y k))) +
            1 / 2 * (∑ k, spin (ε k) * (-(2 * c * f i (X k)))) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        cases ε k <;> simp [spin] <;> ring
      rw [e]
      gcongr
      · exact le_ciSup_of_finite (fun i ↦ ∑ k, spin (ε k) * (2 * c * f i (Y k))) i
      · exact le_ciSup_of_finite (fun i ↦ ∑ k, spin (ε k) * (-(2 * c * f i (X k)))) i
    have hc2 : 0 ≤ 2 * c := by linarith
    have hY := sum_exp_sup_le F hF feat hfeat W hc2 hW M Y (fun k i ↦ 2 * c * f i (Y k))
      (fun k i i' ↦ by
        rw [← mul_sub, abs_mul, abs_of_nonneg hc2]
        exact mul_le_mul_of_nonneg_left (hf1 i i' _) hc2)
      (fun k i ↦ by
        rw [abs_mul, abs_of_nonneg hc2]
        exact mul_le_mul_of_nonneg_left (hf2 i _) hc2)
    have hX := sum_exp_sup_le F hF feat hfeat W hc2 hW M X (fun k i ↦ -(2 * c * f i (X k)))
      (fun k i i' ↦ by
        rw [neg_sub_neg, ← mul_sub, abs_mul, abs_of_nonneg hc2, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (hf1 i i' _) hc2)
      (fun k i ↦ by
        rw [abs_neg, abs_mul, abs_of_nonneg hc2]
        exact mul_le_mul_of_nonneg_left (hf2 i _) hc2)
    have hexp : (2 * c) ^ 2 * B ^ 2 * M / 2 = 2 * c ^ 2 * B ^ 2 * M := by ring
    rw [hexp] at hX hY
    have hsum : ∑ ε : Fin M → Bool,
        exp (G (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k)) ≤
          2 ^ M * K := by
      calc ∑ ε : Fin M → Bool,
            exp (G (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k))
          ≤ ∑ ε : Fin M → Bool, (1 / 2 * exp (⨆ i, ∑ k, spin (ε k) * (2 * c * f i (Y k))) +
              1 / 2 * exp (⨆ i, ∑ k, spin (ε k) * (-(2 * c * f i (X k))))) := by
            refine Finset.sum_le_sum fun ε _ ↦ ?_
            refine (exp_le_exp.2 (hsw ε)).trans ?_
            have := convexOn_exp.2 (Set.mem_univ (⨆ i, ∑ k, spin (ε k) * (2 * c * f i (Y k))))
              (Set.mem_univ (⨆ i, ∑ k, spin (ε k) * (-(2 * c * f i (X k)))))
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
            simpa [smul_eq_mul] using this
        _ = 1 / 2 * ∑ ε : Fin M → Bool, exp (⨆ i, ∑ k, spin (ε k) * (2 * c * f i (Y k))) +
              1 / 2 * ∑ ε : Fin M → Bool,
                exp (⨆ i, ∑ k, spin (ε k) * (-(2 * c * f i (X k)))) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 1 / 2 * (2 * F.card * 2 ^ M * exp (2 * c ^ 2 * B ^ 2 * M)) +
              1 / 2 * (2 * F.card * 2 ^ M * exp (2 * c ^ 2 * B ^ 2 * M)) := by
            gcongr
        _ = 2 ^ M * K := by rw [hK]; ring
    rw [inv_mul_le_iff₀ (by positivity)]
    exact hsum
  -- exchanging coordinates preserves the law of the two samples
  have hswap : ∑ X, ∑ Y, P X * P Y * exp (G X Y) =
      ∑ X, ∑ Y, P X * P Y * ((2 ^ M : ℝ)⁻¹ * ∑ ε : Fin M → Bool,
        exp (G (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k))) := by
    have hcard : ((Finset.univ : Finset (Fin M → Bool)).card : ℝ) = 2 ^ M := by
      simp [Finset.card_univ, Fintype.card_bool, Fintype.card_fin]
    calc ∑ X, ∑ Y, P X * P Y * exp (G X Y)
        = (2 ^ M : ℝ)⁻¹ * ∑ _ε : Fin M → Bool, ∑ X, ∑ Y, P X * P Y * exp (G X Y) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard, ← mul_assoc, inv_mul_cancel₀ (by positivity),
            one_mul]
      _ = (2 ^ M : ℝ)⁻¹ * ∑ ε : Fin M → Bool, ∑ X, ∑ Y, P X * P Y *
            exp (G (fun k ↦ if ε k then X k else Y k) (fun k ↦ if ε k then Y k else X k)) := by
          congr 1
          exact Finset.sum_congr rfl fun ε _ ↦ sum_swap μ ε (fun X Y ↦ exp (G X Y))
      _ = _ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun X _ ↦ ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun Y _ ↦ Finset.sum_congr rfl fun ε _ ↦ by ring
  calc ∑ X : Fin M → Ω, (∏ k, μ (X k)) *
        exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)))
      ≤ ∑ X, P X * ∑ Y, P Y * exp (G X Y) :=
        Finset.sum_le_sum fun X _ ↦ mul_le_mul_of_nonneg_left (ha X) (hP0 X)
    _ = ∑ X, ∑ Y, P X * P Y * exp (G X Y) := by simp_rw [Finset.mul_sum, mul_assoc]
    _ = _ := hswap
    _ ≤ ∑ X, ∑ Y, P X * P Y * K := Finset.sum_le_sum fun X _ ↦ Finset.sum_le_sum fun Y _ ↦
        mul_le_mul_of_nonneg_left (hb X Y) (mul_nonneg (hP0 X) (hP0 Y))
    _ = K := by
        simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hP1]
        ring

open Classical in
/-- **Uniform deviation**: `P(∃ i, ∑ₖ (E f_i - f_i(Xₖ)) > M η) ≤ 2 |F| exp(-M η² / (8 B²))`. -/
theorem prob_sup_dev_le (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (F : Finset κ) (hF : F.Nonempty) (feat : κ → Ω → ℝ) (hfeat : ∀ j ∈ F, ∀ x, |feat j x| ≤ 1)
    (W : ι → κ → ℝ) {B : ℝ} (hB : 0 < B) (hW : ∀ i, ∑ j ∈ F, |W i j| ≤ B) (f : ι → Ω → ℝ)
    (hf1 : ∀ i i' x,
      |f i x - f i' x| ≤ |∑ j ∈ F, W i j * feat j x - ∑ j ∈ F, W i' j * feat j x|)
    (hf2 : ∀ i x, |f i x| ≤ |∑ j ∈ F, W i j * feat j x|) (M : ℕ) {η : ℝ} (hη : 0 < η) :
    ∑ X : Fin M → Ω,
        (if ∃ i, M * η < ∑ k, ((∑ x, μ x * f i x) - f i (X k)) then ∏ k, μ (X k) else 0) ≤
      2 * F.card * exp (-(M * η ^ 2 / (8 * B ^ 2))) := by
  set c := η / (4 * B ^ 2) with hc_def
  have hc : 0 ≤ c := by positivity
  have hE := sum_exp_sup_dev_le hμ hμ1 F hF feat hfeat W hW f hf1 hf2 M hc
  have hpt : ∀ X : Fin M → Ω,
      (if ∃ i, M * η < ∑ k, ((∑ x, μ x * f i x) - f i (X k)) then ∏ k, μ (X k) else 0) ≤
        exp (-(c * (M * η))) * ((∏ k, μ (X k)) *
          exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)))) := by
    intro X
    have hP0 := prod_weight_nonneg hμ X
    split_ifs with h
    · obtain ⟨i, hi⟩ := h
      have h1 : c * (M * η) ≤ ⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)) :=
        (mul_le_mul_of_nonneg_left hi.le hc).trans
          (le_ciSup_of_finite (fun i ↦ c * ∑ k, ((∑ x, μ x * f i x) - f i (X k))) i)
      have h2 : 1 ≤ exp (-(c * (M * η))) *
          exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k))) := by
        rw [← exp_add]
        exact one_le_exp (by linarith)
      calc ∏ k, μ (X k) = (∏ k, μ (X k)) * 1 := (mul_one _).symm
        _ ≤ (∏ k, μ (X k)) * (exp (-(c * (M * η))) *
              exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)))) :=
            mul_le_mul_of_nonneg_left h2 hP0
        _ = _ := by ring
    · positivity
  calc _ ≤ ∑ X : Fin M → Ω, exp (-(c * (M * η))) * ((∏ k, μ (X k)) *
          exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k)))) :=
        Finset.sum_le_sum fun X _ ↦ hpt X
    _ = exp (-(c * (M * η))) * ∑ X : Fin M → Ω, (∏ k, μ (X k)) *
          exp (⨆ i, c * ∑ k, ((∑ x, μ x * f i x) - f i (X k))) := by rw [Finset.mul_sum]
    _ ≤ exp (-(c * (M * η))) * (2 * F.card * exp (2 * c ^ 2 * B ^ 2 * M)) :=
        mul_le_mul_of_nonneg_left hE (exp_pos _).le
    _ = 2 * F.card * exp (-(M * η ^ 2 / (8 * B ^ 2))) := by
        rw [mul_left_comm, ← exp_add]
        congr 2
        rw [hc_def]
        field_simp
        ring

end BB20.Prediction
