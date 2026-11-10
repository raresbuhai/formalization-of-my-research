module

public import ABBKS26.Select.LearnAuxSingleton

/-! Population moment bounds for the singleton reference. -/

@[expose] public section

namespace ABBKS26.Select.LearnAux

noncomputable section

open Common Matrix MvPolynomial _root_.ABBKS26.Tree
open scoped BigOperators MatrixOrder Topology

variable {n k d : ℕ}

private theorem gaussMom_zero : gaussMom 0 = 1 := by
  norm_num [gaussMom]

private theorem gaussMom_one : gaussMom 1 = 0 := by
  norm_num [gaussMom]

private theorem gaussMom_two : gaussMom 2 = 1 := by
  norm_num [gaussMom]

private theorem gaussianValue_monomial (α : Fin d →₀ ℕ) (c : ℝ) :
    gaussianValue (monomial α c) = c * gaussMomMulti (fun i ↦ α i) := by
  classical
  by_cases hc : c = 0
  · simp [hc, gaussianValue]
  · simp [gaussianValue, support_monomial, hc]

private theorem gaussianValue_X (i : Fin d) : gaussianValue (X i) = 0 := by
  classical
  rw [X, gaussianValue_monomial]
  simp only [one_mul, gaussMomMulti, Nat.cast_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [Finsupp.single_eq_same, gaussMom_one, Nat.cast_zero]

private theorem gaussianValue_X_mul_X (i j : Fin d) :
    gaussianValue (X i * X j) = if i = j then 1 else 0 := by
  classical
  rw [X, X, monomial_mul_monomial, gaussianValue_monomial]
  by_cases hij : i = j
  · subst j
    simp only [one_mul, ite_true, gaussMomMulti, Nat.cast_prod]
    apply Finset.prod_eq_one
    intro a _
    by_cases ha : i = a
    · simp [ha, gaussMom_two]
    · simp [ha, gaussMom_zero]
  · have hzero : gaussMomMulti
        (fun a ↦ (Finsupp.single i 1 + Finsupp.single j 1 : Fin d →₀ ℕ) a) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hij, gaussMom_one]
    simp only [one_mul, ite_eq_right hij, Nat.cast_eq_zero]
    exact hzero

/-- First and second standardized clean moments, with the scheduled uniform tolerance. -/
theorem singleton_first_second
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) :
    let S := cluster (labels ω)
    let δ := 1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8)
    ∀ j : Fin k,
      (∀ i, |Robust.FilterAux.average (S j) (fun l ↦ stdClean M ω l i)| ≤ δ) ∧
      ∀ i a, |Robust.FilterAux.average (S j)
        (fun l ↦ stdClean M ω l i * stdClean M ω l a) -
          (if i = a then 1 else 0)| ≤ δ := by
  classical
  have hD := hp.eight_le_degree mode M ε w η Δ D ω r params
  dsimp only
  intro j
  constructor
  · intro i
    have h := singleton_polynomial_moments mode M ε w η Δ D ω r params hp j
      (X i) (by simpa using (show 1 ≤ D by omega))
    simpa only [eval_X, gaussianValue_X, sub_zero, SoS.coeffNorm1_X] using h
  · intro i a
    have hd : (X i * X a : RPoly d).totalDegree ≤ D :=
      (totalDegree_mul _ _).trans (by simp; omega)
    have h := singleton_polynomial_moments mode M ε w η Δ D ω r params hp j
      (X i * X a) hd
    have hn : SoS.coeffNorm1 (X i * X a : RPoly d) ≤ 1 := by
      simpa only [SoS.coeffNorm1_X, one_mul] using
        SoS.coeffNorm1_mul_le (X i : RPoly d) (X a)
    have hh : |Robust.FilterAux.average (cluster (labels ω) j)
        (fun l ↦ stdClean M ω l i * stdClean M ω l a) -
          (if i = a then 1 else 0)| ≤
        SoS.coeffNorm1 (X i * X a : RPoly d) / (10 ^ 12 * (d + 1 : ℝ) ^ 8) := by
      simpa only [map_mul, eval_X, gaussianValue_X_mul_X] using h
    exact hh.trans (div_le_div_of_nonneg_right hn (by positivity))

/-- Rounding the clean points in their population coordinates. -/
def standardizedRounded (M : Mixture k d) (ω : Fin n → Triple k d)
    (r : Rounding k d) (l : Fin n) : Vec d :=
  fun i ↦ stdPt M (ω l).1 (WithLp.toLp 2 fun a ↦ (r ((ω l).1, (ω l).2.1) a : ℝ)) i

theorem standardizedRounded_error (M : Mixture k d) (ω : Fin n → Triple k d)
    (r : Rounding k d) (hM : M.Valid) (hr : IsRounding M (1 / n) r)
    (l : Fin n) (i : Fin d) :
    |standardizedRounded M ω r l i - stdClean M ω l i| ≤ 1 / n := by
  exact (PiLp.norm_apply_le
    (stdPt M (ω l).1 (WithLp.toLp 2 fun a ↦ (r ((ω l).1, (ω l).2.1) a : ℝ)) -
      stdClean M ω l) i).trans
    (norm_stdPt_sub_le_of_isRounding hM (by positivity) hr _ _)

private theorem average_abs_le_two {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (g : ι → ℝ) (h : Robust.FilterAux.average S (fun l ↦ g l ^ 2) ≤ 2) :
    Robust.FilterAux.average S (fun l ↦ |g l|) ≤ 2 := by
  have hpoint (l : ι) : |g l| ≤ (g l ^ 2 + 1) / 2 := by
    nlinarith only [sq_nonneg (|g l| - 1), sq_abs (g l)]
  have hh := Robust.FilterAux.average_mono S _ _ (fun l _ ↦ hpoint l)
  have he : (fun l ↦ (g l ^ 2 + 1) / 2) =
      (1 / 2 : ℝ) • ((fun l ↦ g l ^ 2) + (1 : ι → ℝ)) := by
    funext l
    simp only [Pi.smul_apply, Pi.add_apply, Pi.one_apply, smul_eq_mul]
    ring
  rw [he, map_smul, map_add, Robust.FilterAux.average_one S hS] at hh
  change Robust.FilterAux.average S (fun l ↦ |g l|) ≤
    1 / 2 * (Robust.FilterAux.average S (fun l ↦ g l ^ 2) + 1) at hh
  linarith only [h, hh]

private theorem average_abs_bound {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) (b : ℝ) (hf : ∀ l ∈ S, |f l| ≤ b) :
    |Robust.FilterAux.average S f| ≤ b := by
  have hh : |Robust.FilterAux.average S f| ≤
      Robust.FilterAux.average S (fun l ↦ |f l|) := by
    dsimp only [Robust.FilterAux.average, LinearMap.coe_mk, AddHom.coe_mk]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (S.card : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  apply hh.trans
  have hmono := Robust.FilterAux.average_mono S (fun l ↦ |f l|) (b • (1 : ι → ℝ))
    (fun l hl ↦ by
      simpa only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one] using hf l hl)
  simpa only [map_smul, Robust.FilterAux.average_one S hS, smul_eq_mul, mul_one]
    using hmono

/-- Small pointwise perturbations preserve the first two standardized moments. -/
theorem perturbed_first_second {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (g h : ι → Vec d) (δ τ : ℝ) (hδ : δ ≤ 1) (hτ : 0 ≤ τ)
    (herr : ∀ l ∈ S, ∀ i, |h l i - g l i| ≤ τ)
    (hfirst : ∀ i, |Robust.FilterAux.average S (fun l ↦ g l i)| ≤ δ)
    (hsecond : ∀ i j, |Robust.FilterAux.average S (fun l ↦ g l i * g l j) -
      (if i = j then 1 else 0)| ≤ δ) :
    (∀ i, |Robust.FilterAux.average S (fun l ↦ h l i)| ≤ δ + τ) ∧
    ∀ i j, |Robust.FilterAux.average S (fun l ↦ h l i * h l j) -
      (if i = j then 1 else 0)| ≤ δ + 4 * τ + τ ^ 2 := by
  have habs (i : Fin d) :
      Robust.FilterAux.average S (fun l ↦ |g l i|) ≤ 2 := by
    apply average_abs_le_two S hS
    have hh := (abs_le.mp (hsecond i i)).2
    simp only [ite_true, ← pow_two] at hh
    linarith only [hh, hδ]
  constructor
  · intro i
    have he := average_abs_bound S hS (fun l ↦ h l i - g l i) τ
      (fun l hl ↦ herr l hl i)
    have heq : (fun l ↦ h l i) = (fun l ↦ g l i) + (fun l ↦ h l i - g l i) := by
      funext l
      simp
    rw [heq, map_add]
    exact (abs_add_le _ _).trans (add_le_add (hfirst i) he)
  · intro i j
    have hpoint (l : ι) (hl : l ∈ S) :
        |h l i * h l j - g l i * g l j| ≤
          τ * |g l i| + τ * |g l j| + τ ^ 2 := by
      have heq : h l i * h l j - g l i * g l j =
          (h l i - g l i) * g l j + (h l j - g l j) * g l i +
            (h l i - g l i) * (h l j - g l j) := by ring
      rw [heq]
      refine (abs_add_le
        ((h l i - g l i) * g l j + (h l j - g l j) * g l i)
        ((h l i - g l i) * (h l j - g l j))).trans ?_
      refine (add_le_add
        (abs_add_le ((h l i - g l i) * g l j) ((h l j - g l j) * g l i))
        (le_refl (|(h l i - g l i) * (h l j - g l j)|))).trans ?_
      simp only [abs_mul]
      have h₁ := mul_le_mul_of_nonneg_right (herr l hl i) (abs_nonneg (g l j))
      have h₂ := mul_le_mul_of_nonneg_right (herr l hl j) (abs_nonneg (g l i))
      have h₃ := mul_le_mul (herr l hl i) (herr l hl j) (abs_nonneg _) hτ
      nlinarith only [h₁, h₂, h₃]
    have he : |Robust.FilterAux.average S
        (fun l ↦ h l i * h l j - g l i * g l j)| ≤ 4 * τ + τ ^ 2 := by
      have hh : |Robust.FilterAux.average S
          (fun l ↦ h l i * h l j - g l i * g l j)| ≤
          Robust.FilterAux.average S (fun l ↦ |h l i * h l j - g l i * g l j|) := by
        dsimp only [Robust.FilterAux.average, LinearMap.coe_mk, AddHom.coe_mk]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (S.card : ℝ)⁻¹)]
        exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      apply hh.trans
      have hm := Robust.FilterAux.average_mono S _ _ hpoint
      have heq : (fun l ↦ τ * |g l i| + τ * |g l j| + τ ^ 2) =
          τ • (fun l ↦ |g l i|) + τ • (fun l ↦ |g l j|) +
            τ ^ 2 • (1 : ι → ℝ) := by
        funext l
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
      rw [heq, map_add, map_add, map_smul, map_smul, map_smul,
        Robust.FilterAux.average_one S hS] at hm
      change Robust.FilterAux.average S _ ≤
        τ * Robust.FilterAux.average S (fun l ↦ |g l i|) +
        τ * Robust.FilterAux.average S (fun l ↦ |g l j|) + τ ^ 2 * 1 at hm
      nlinarith only [hm, mul_le_mul_of_nonneg_left (habs i) hτ,
        mul_le_mul_of_nonneg_left (habs j) hτ]
    have heq : (fun l ↦ h l i * h l j) =
        (fun l ↦ g l i * g l j) + (fun l ↦ h l i * h l j - g l i * g l j) := by
      funext l
      simp
    rw [heq, map_add, add_sub_right_comm]
    exact (abs_add_le _ _).trans (by linarith only [hsecond i j, he])

/-- The rounded clean reference retains the first two standardized moment bounds. -/
theorem singleton_rounded_first_second
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (j : Fin k) :
    let S := cluster (labels ω) j
    let g := standardizedRounded M ω r
    let δ := 1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8)
    (∀ i, |Robust.FilterAux.average S (fun l ↦ g l i)| ≤ δ + 1 / n) ∧
    ∀ i a, |Robust.FilterAux.average S (fun l ↦ g l i * g l a) -
      (if i = a then 1 else 0)| ≤ δ + 4 / n + (1 / n : ℝ) ^ 2 := by
  have hne : (cluster (labels ω) j).Nonempty :=
    Finset.card_pos.mp (SoundAux.good_cluster_pos M ε w η D ω hp.2.2.2.2.2.2.2.2.2.1 j)
  obtain ⟨hfirst, hsecond⟩ :=
    singleton_first_second mode M ε w η Δ D ω r params hp j
  have hd : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 8 :=
    one_le_pow₀ (by linarith only [Nat.cast_nonneg (α := ℝ) d] : (1 : ℝ) ≤ d + 1)
  have hδ : 1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hd]
  simpa only [mul_one_div] using perturbed_first_second (cluster (labels ω) j) hne
    (fun l i ↦ stdClean M ω l i) (standardizedRounded M ω r) _ (1 / n) hδ
    (by positivity) (fun l _ i ↦ standardizedRounded_error M ω r hp.1
      hp.2.2.2.2.2.2.2.2.2.2.1 l i) hfirst hsecond

private theorem average_const {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (c : ℝ) :
    Robust.FilterAux.average S (fun _ ↦ c) = c := by
  have he : (fun _ : ι ↦ c) = c • (1 : ι → ℝ) := by ext; simp
  rw [he, map_smul, Robust.FilterAux.average_one S hS, smul_eq_mul, mul_one]

def empiricalMean {ι : Type*} (S : Finset ι) (x : ι → Vec d) : Vec d :=
  fun i ↦ Robust.FilterAux.average S (fun l ↦ x l i)

def empiricalCov {ι : Type*} (S : Finset ι) (x : ι → Vec d) : Mat d :=
  fun i j ↦ Robust.FilterAux.average S
    (fun l ↦ (x l i - empiricalMean S x i) * (x l j - empiricalMean S x j))

theorem empiricalCov_eq {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (x : ι → Vec d) (i j : Fin d) :
    empiricalCov S x i j = Robust.FilterAux.average S (fun l ↦ x l i * x l j) -
      empiricalMean S x i * empiricalMean S x j := by
  have he : (fun l ↦ (x l i - empiricalMean S x i) *
      (x l j - empiricalMean S x j)) =
      (fun l ↦ x l i * x l j) - empiricalMean S x j • (fun l ↦ x l i) -
      empiricalMean S x i • (fun l ↦ x l j) +
      (fun _ ↦ empiricalMean S x i * empiricalMean S x j) := by
    funext l
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [empiricalCov, he, map_add, map_sub, map_sub, map_smul, map_smul,
    average_const S hS]
  change _ - empiricalMean S x j * empiricalMean S x i -
    empiricalMean S x i * empiricalMean S x j + _ = _
  ring

theorem empiricalCov_symmetric {ι : Type*} (S : Finset ι) (x : ι → Vec d) :
    (empiricalCov S x)ᵀ = empiricalCov S x := by
  ext i j
  simp only [transpose_apply, empiricalCov, mul_comm]

theorem empirical_first_second_bounds {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (x : ι → Vec d) (α β : ℝ) (hα : 0 ≤ α)
    (hfirst : ∀ i, |Robust.FilterAux.average S (fun l ↦ x l i)| ≤ α)
    (hsecond : ∀ i j, |Robust.FilterAux.average S (fun l ↦ x l i * x l j) -
      (if i = j then 1 else 0)| ≤ β) :
    sqnorm (empiricalMean S x) ≤ d * α ^ 2 ∧
      frobSq (empiricalCov S x - 1) ≤ (d : ℝ) ^ 2 * (β + α ^ 2) ^ 2 := by
  have hm (i : Fin d) : |empiricalMean S x i| ≤ α := hfirst i
  have hc (i j : Fin d) : |(empiricalCov S x - 1) i j| ≤ β + α ^ 2 := by
    rw [Matrix.sub_apply, Matrix.one_apply, empiricalCov_eq S hS x]
    have he : Robust.FilterAux.average S (fun l ↦ x l i * x l j) -
        empiricalMean S x i * empiricalMean S x j - (if i = j then 1 else 0) =
        (Robust.FilterAux.average S (fun l ↦ x l i * x l j) -
          (if i = j then 1 else 0)) - empiricalMean S x i * empiricalMean S x j := by
      ring
    rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul]
    have hh := mul_le_mul (hm i) (hm j) (abs_nonneg _) hα
    nlinarith only [hsecond i j, hh]
  constructor
  · calc
      _ = ∑ i, (empiricalMean S x i) ^ 2 := by simp [sqnorm, dotProduct, pow_two]
      _ ≤ ∑ _i : Fin d, α ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hm i) 2
      _ = _ := by simp
  · calc
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, (β + α ^ 2) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc i j) 2
      _ = _ := by simp [pow_two, mul_assoc]

theorem empiricalMean_eq_sum {ι : Type*} (S : Finset ι) (x : ι → Vec d) :
    empiricalMean S x = (S.card : ℝ)⁻¹ • ∑ l ∈ S, x l := by
  ext i
  simp [empiricalMean, Robust.FilterAux.average, Finset.sum_apply]

theorem empiricalCov_eq_sum {ι : Type*} (S : Finset ι) (x : ι → Vec d) :
    empiricalCov S x = (S.card : ℝ)⁻¹ • ∑ l ∈ S,
      vecMulVec (x l - empiricalMean S x) (x l - empiricalMean S x) := by
  ext i j
  simp only [empiricalCov, Robust.FilterAux.average, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply, vecMulVec_apply, Pi.sub_apply]

theorem empiricalMean_transform {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (x : ι → Vec d) (T : Mat d) (a : Vec d) :
    empiricalMean S (fun l ↦ T *ᵥ (x l - a)) = T *ᵥ (empiricalMean S x - a) := by
  ext i
  have he : (fun l ↦ (T *ᵥ (x l - a)) i) =
      ∑ j, T i j • ((fun l ↦ x l j) - (fun _ ↦ a j)) := by
    funext l
    simp [mulVec, dotProduct]
  change Robust.FilterAux.average S (fun l ↦ (T *ᵥ (x l - a)) i) = _
  rw [he, map_sum]
  simp only [mulVec, dotProduct, Pi.sub_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, map_sub, average_const S hS]
  rfl

theorem empiricalCov_transform {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (x : ι → Vec d) (T : Mat d) (a : Vec d) :
    empiricalCov S (fun l ↦ T *ᵥ (x l - a)) = T * empiricalCov S x * Tᵀ := by
  rw [empiricalCov_eq_sum, empiricalCov_eq_sum, empiricalMean_transform S hS]
  have he (l : ι) : T *ᵥ (x l - a) - T *ᵥ (empiricalMean S x - a) =
      T *ᵥ (x l - empiricalMean S x) := by
    rw [← mulVec_sub]
    congr 1
    abel
  simp only [he]
  simpa only [one_smul] using (Robust.FilterAux.covariance_conjugate S (fun _ ↦ 1)
    (fun l ↦ x l - empiricalMean S x) S.card T).symm

theorem empiricalMean_congr {ι : Type*} (S : Finset ι) (x y : ι → Vec d)
    (h : ∀ l ∈ S, x l = y l) : empiricalMean S x = empiricalMean S y := by
  rw [empiricalMean_eq_sum, empiricalMean_eq_sum]
  exact congrArg (_ • ·) (Finset.sum_congr rfl h)

theorem empiricalCov_congr {ι : Type*} (S : Finset ι) (x y : ι → Vec d)
    (h : ∀ l ∈ S, x l = y l) : empiricalCov S x = empiricalCov S y := by
  rw [empiricalCov_eq_sum, empiricalCov_eq_sum, empiricalMean_congr S x y h]
  congr 1
  exact Finset.sum_congr rfl fun l hl ↦ by rw [h l hl]

theorem singleton_reference_standardized
    (M : Mixture k d) (ω : Fin n → Triple k d) (r : Rounding k d)
    (j : Fin k) (N : Finset (Fin n)) (hne : (cluster (labels ω) j).Nonempty) :
    let R := singletonReference M j ω r N
    let B := (CFC.sqrt (M.S j))⁻¹
    B *ᵥ (R.mean - M.μ j) =
      empiricalMean (cluster (labels ω) j) (standardizedRounded M ω r) ∧
    B * R.cov * Bᵀ =
      empiricalCov (cluster (labels ω) j) (standardizedRounded M ω r) := by
  let R := singletonReference M j ω r N
  let B := (CFC.sqrt (M.S j))⁻¹
  have he : ∀ l ∈ cluster (labels ω) j,
      B *ᵥ (R.clean l - M.μ j) = standardizedRounded M ω r l := by
    intro l hl
    have hj : (ω l).1 = j := (Finset.mem_filter.mp hl).2
    change B *ᵥ ((fun i ↦ (r ((ω l).1, (ω l).2.1) i : ℝ)) - M.μ j) = _
    ext i
    simp only [standardizedRounded, hj, stdPt_apply]
    rfl
  have hm : empiricalMean (cluster (labels ω) j) R.clean = R.mean := by
    rw [empiricalMean_eq_sum]
    rfl
  have hc : empiricalCov (cluster (labels ω) j) R.clean = R.cov := by
    rw [empiricalCov_eq_sum, hm]
    rfl
  constructor
  · rw [← hm, ← empiricalMean_transform _ hne]
    exact empiricalMean_congr _ _ _ he
  · rw [← hc, ← empiricalCov_transform _ hne _ B (M.μ j)]
    exact empiricalCov_congr _ _ _ he

private theorem inverse_sample_bound
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) :
    1 / (n : ℝ) ≤ 1 / (320000 * (d + 1 : ℝ)) := by
  obtain ⟨_, _, _, _, _, _, hη, hη100, _, _, _, hn, _⟩ := hp
  have hs : 32 * (d + 1 : ℝ) / η ^ 2 ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hηsq : η ^ 2 ≤ 1 / 10000 := by
    nlinarith only [sq_nonneg (η - 1 / 100), hη, hη100]
  have hh := (div_le_iff₀ (sq_pos_of_pos hη)).mp hs
  have hh' := mul_le_mul_of_nonneg_left hηsq (Nat.cast_nonneg (α := ℝ) n)
  have hb : 320000 * (d + 1 : ℝ) ≤ n := by linarith only [hh, hh']
  exact one_div_le_one_div_of_le (by positivity) hb

private theorem reference_numeric_bounds (d : ℕ) (δ τ : ℝ)
    (hτ0 : 0 ≤ τ)
    (hδ : δ ≤ 1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8))
    (hτ : τ ≤ 1 / (320000 * (d + 1 : ℝ))) :
    let α := 1 / (100000 * (d + 1 : ℝ))
    let β := 1 / (10000 * (d + 1 : ℝ))
    δ + τ ≤ α ∧ δ + 4 * τ + τ ^ 2 ≤ β ∧
      d * α ^ 2 ≤ 1 / 10 ^ 10 ∧
      (d : ℝ) ^ 2 * (β + α ^ 2) ^ 2 ≤ 1 / 10 ^ 6 := by
  let t : ℝ := d + 1
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht1 : 1 ≤ t := by dsimp only [t]; linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hpow : t ≤ t ^ 8 := le_self_pow₀ ht1 (by omega)
  have hδ' : δ ≤ 1 / (10 ^ 12 * t) := hδ.trans
    (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hδs : δ * t ≤ 1 / 10 ^ 12 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 10 ^ 12 * t)).mp hδ'
    nlinarith only [hh]
  have hτs : τ * t ≤ 1 / 320000 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 320000 * t)).mp hτ
    nlinarith only [hh]
  have hτ1 : τ ≤ 1 / 320000 := by
    nlinarith only [hτs, mul_le_mul_of_nonneg_left ht1 hτ0]
  have hτsq : τ ^ 2 * t ≤ 1 / 320000 ^ 2 := by
    have hh := mul_le_mul hτ1 hτs (mul_nonneg hτ0 ht.le) (by norm_num : (0 : ℝ) ≤ 1 / 320000)
    nlinarith only [hh]
  let α := 1 / (100000 * t)
  let β := 1 / (10000 * t)
  have hα : 0 < α := by dsimp only [α]; positivity
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hαs : α * t = 1 / 100000 := by dsimp only [α]; field_simp
  have hβs : β * t = 1 / 10000 := by dsimp only [β]; field_simp
  have hα1 : α ≤ 1 / 100000 := by
    nlinarith only [hαs, mul_le_mul_of_nonneg_left ht1 hα.le]
  have hαsq : α ^ 2 * t ≤ 1 / 10 ^ 10 := by
    calc
      _ = α * (α * t) := by ring
      _ = α * (1 / 100000) := by rw [hαs]
      _ ≤ _ := by nlinarith only [hα1]
  change δ + τ ≤ α ∧ δ + 4 * τ + τ ^ 2 ≤ β ∧
    d * α ^ 2 ≤ 1 / 10 ^ 10 ∧ (d : ℝ) ^ 2 * (β + α ^ 2) ^ 2 ≤ 1 / 10 ^ 6
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_iff_left₀ ht).mp (by nlinarith only [hδs, hτs, hαs])
  · exact (mul_le_mul_iff_left₀ ht).mp (by nlinarith only [hδs, hτs, hτsq, hβs])
  · have hh : (d : ℝ) ≤ t := by dsimp only [t]; linarith
    exact (mul_le_mul_of_nonneg_right hh (sq_nonneg α)).trans
      (by simpa only [mul_comm] using hαsq)
  · have hd : (d : ℝ) ≤ t := by dsimp only [t]; linarith
    have hh := mul_le_mul_of_nonneg_right hd (by positivity : 0 ≤ β + α ^ 2)
    have hb : (d : ℝ) * (β + α ^ 2) ≤ 1 / 1000 := by
      nlinarith only [hh, hβs, hαsq]
    have hn : 0 ≤ (d : ℝ) * (β + α ^ 2) := by positivity
    have hh' := pow_le_pow_left₀ hn hb 2
    nlinarith only [hh']

/-- Rounded empirical reference parameters are close to the population in its own geometry. -/
theorem singleton_reference_accuracy
    (mode : Mode) (M : Mixture k d) (ε w η Δ : ℝ) (D : ℕ)
    (ω : Fin n → Triple k d) (r : Rounding k d) (params : ℕ → StepParams)
    (hp : Prepared mode M ε w η Δ D ω r params) (j : Fin k) (N : Finset (Fin n)) :
    let R := singletonReference M j ω r N
    R.cov.PosDef ∧
      frobSq ((CFC.sqrt (M.S j))⁻¹ * R.cov * (CFC.sqrt (M.S j))⁻¹ - 1) ≤
        1 / 10 ^ 6 ∧
      sqNormIn (M.S j) (R.mean - M.μ j) ≤ 1 / 10 ^ 10 := by
  let R := singletonReference M j ω r N
  let S := cluster (labels ω) j
  let g := standardizedRounded M ω r
  let α : ℝ := 1 / (100000 * (d + 1 : ℝ))
  let β : ℝ := 1 / (10000 * (d + 1 : ℝ))
  have hne : S.Nonempty :=
    Finset.card_pos.mp (SoundAux.good_cluster_pos M ε w η D ω hp.2.2.2.2.2.2.2.2.2.1 j)
  obtain ⟨hfirst, hsecond⟩ :=
    singleton_rounded_first_second mode M ε w η Δ D ω r params hp j
  obtain ⟨hα, hβ, hαsmall, hβsmall⟩ := reference_numeric_bounds d
    (1 / (10 ^ 12 * (d + 1 : ℝ) ^ 8)) (1 / n) (by positivity)
    le_rfl (inverse_sample_bound mode M ε w η Δ D ω r params hp)
  obtain ⟨hm, hc⟩ := empirical_first_second_bounds S hne g α β (by positivity)
    (fun i ↦ (hfirst i).trans hα)
    (fun i a ↦ (hsecond i a).trans (by simpa only [mul_one_div] using hβ))
  have hmean : sqnorm (empiricalMean S g) ≤ 1 / 10 ^ 10 := hm.trans hαsmall
  have hcov : frobSq (empiricalCov S g - 1) ≤ 1 / 10 ^ 6 := hc.trans hβsmall
  obtain ⟨hmeq, hceq⟩ := singleton_reference_standardized M ω r j N hne
  have hBt : ((CFC.sqrt (M.S j))⁻¹)ᵀ = (CFC.sqrt (M.S j))⁻¹ := by
    rw [transpose_nonsing_inv, (Robust.RBAux.sqrt_properties _ (hp.1.posDef j)).1]
  have hcov' : frobSq ((CFC.sqrt (M.S j))⁻¹ * R.cov *
      (CFC.sqrt (M.S j))⁻¹ - 1) ≤ 1 / 10 ^ 6 := by
    rw [hBt] at hceq
    rw [hceq]
    exact hcov
  have hsym : R.covᵀ = R.cov := by
    have he : empiricalMean S R.clean = R.mean := by
      rw [empiricalMean_eq_sum]
      rfl
    have hecov : empiricalCov S R.clean = R.cov := by
      rw [empiricalCov_eq_sum, he]
      rfl
    rw [← hecov]
    exact empiricalCov_symmetric _ _
  refine ⟨(Robust.RBAux.relative_bounds (M.S j) R.cov (hp.1.posDef j) hsym
    (hcov'.trans (by norm_num))).1, hcov', ?_⟩
  rw [sqNormIn_eq_norm_sq (hp.1.posDef j), EuclideanSpace.real_norm_sq_eq]
  change sqnorm (empiricalMean (cluster (labels ω) j)
    (standardizedRounded M ω r)) ≤ _ at hmean
  rw [← hmeq] at hmean
  simpa only [sqnorm, dotProduct, pow_two] using hmean

theorem sqNormIn_comparison (S R : Mat d) (hS : S.PosDef) (hR : R.PosDef)
    (c : ℝ) (h : LE R (c • S)) (v : Vec d) :
    sqNormIn S v ≤ c * sqNormIn R v := by
  let u := S⁻¹ *ᵥ v
  let y := R⁻¹ *ᵥ v
  have hSu : S *ᵥ u = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hS.det_pos.ne'),
      one_mulVec]
  have hRy : R *ᵥ y = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hR.det_pos.ne'),
      one_mulVec]
  have hrnonneg : 0 ≤ sqNormIn R v := by
    simpa only [sqNormIn, star_trivial] using hR.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hcs := hR.star_dotProduct_mulVec_mul_le u y
  simp only [star_trivial, hRy] at hcs
  have hu : u ⬝ᵥ v = sqNormIn S v := dotProduct_comm _ _
  have hy : y ⬝ᵥ v = sqNormIn R v := dotProduct_comm _ _
  have hh := h u
  simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul, hSu, hu] at hh
  rw [hu, hy] at hcs
  have hb := hcs.trans (mul_le_mul_of_nonneg_right hh hrnonneg)
  by_cases hv : v = 0
  · simp [hv, sqNormIn]
  · have hm : 0 < sqNormIn S v := by
      simpa only [sqNormIn, star_trivial] using hS.inv.dotProduct_mulVec_pos hv
    nlinarith only [hb, hm]

theorem sqNormIn_add_le (S : Mat d) (hS : S.PosDef) (u v : Vec d) :
    sqNormIn S (u + v) ≤ (21 / 20 : ℝ) * sqNormIn S u + 21 * sqNormIn S v := by
  have hpos := hS.inv.posSemidef.dotProduct_mulVec_nonneg (u - (20 : ℝ) • v)
  have hcross : u ⬝ᵥ (S⁻¹ *ᵥ v) = v ⬝ᵥ (S⁻¹ *ᵥ u) := by
    simpa only [star_trivial] using hS.inv.isHermitian.star_dotProduct_mulVec_comm u v
  simp only [sqNormIn, star_trivial, mulVec_add, add_dotProduct, dotProduct_add,
    mulVec_sub, mulVec_smul, sub_dotProduct, smul_dotProduct, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, hcross] at hpos ⊢
  linarith only [hpos]

theorem frobSq_congruence_le (T E : Mat d) (hE : Eᵀ = E) (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ v, qform (Tᵀ * T) v ≤ c * sqnorm v) :
    frobSq (T * E * Tᵀ) ≤ c ^ 2 * frobSq E := by
  let P := Tᵀ * T
  have hP : P.PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self T
  have hF : (T * E * Tᵀ).IsHermitian := by
    change (T * E * Tᵀ)ᴴ = T * E * Tᵀ
    simp only [conjTranspose_eq_transpose_of_trivial, transpose_mul,
      transpose_transpose, hE, mul_assoc]
  rw [← CompleteAux.trace_sq _ hF]
  have he : (T * E * Tᵀ * (T * E * Tᵀ)).trace = (E * P * E * P).trace := by
    calc
      _ = (T * (E * P * E) * Tᵀ).trace := by simp only [P, mul_assoc]
      _ = _ := by
        rw [trace_mul_cycle]
        rw [trace_mul_comm (Tᵀ * T) (E * P * E)]
  rw [he]
  exact Robust.FilterAux.trace_quadratic_le E P hE hP c hc hT

theorem frobSq_add_le (A B : Mat d) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simp only [frobSq, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  nlinarith only [sq_nonneg (A i j - B i j)]

theorem sqNormIn_sqrt (S : Mat d) (hS : S.PosDef) (v : Vec d) :
    sqNormIn S (CFC.sqrt S *ᵥ v) = sqnorm v := by
  rw [sqNormIn_eq_norm_sq hS]
  have he : (CFC.sqrt S)⁻¹ *ᵥ (CFC.sqrt S *ᵥ v) = v := by
    rw [mulVec_mulVec, nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (Robust.RBAux.sqrt_properties S hS).2.1), one_mulVec]
  rw [he, EuclideanSpace.real_norm_sq_eq]
  simp [sqnorm, dotProduct, pow_two]


/-- A covariance close in its own frame is also close in a nearby population frame. -/
theorem covariance_transfer (S R C : Mat d) (hS : S.PosDef) (hR : R.PosDef)
    (hC : C.PosDef)
    (hRerr : frobSq ((CFC.sqrt S)⁻¹ * R * (CFC.sqrt S)⁻¹ - 1) ≤ 1 / 10 ^ 6)
    (hCerr : frobSq ((CFC.sqrt C)⁻¹ * (C - R) * (CFC.sqrt C)⁻¹) ≤ 1 / 500) :
    frobSq ((CFC.sqrt S)⁻¹ * C * (CFC.sqrt S)⁻¹ - 1) ≤ 3 / 500 := by
  let A := (CFC.sqrt C)⁻¹
  let B := (CFC.sqrt S)⁻¹
  let E := A * (C - R) * A
  let T := B * CFC.sqrt C
  obtain ⟨hCt, hCdet, hCC⟩ := Robust.RBAux.sqrt_properties C hC
  obtain ⟨hSt, _, _⟩ := Robust.RBAux.sqrt_properties S hS
  have hCunit : IsUnit (CFC.sqrt C).det := isUnit_iff_ne_zero.mpr hCdet
  have hAt : Aᵀ = A := by simp only [A, transpose_nonsing_inv, hCt]
  have hBt : Bᵀ = B := by simp only [B, transpose_nonsing_inv, hSt]
  have hwhite : A * C * A = 1 := by
    rw [← hCC]
    simp only [A, ← mul_assoc, nonsing_inv_mul _ hCunit, one_mul,
      mul_nonsing_inv _ hCunit]
  have hE : Eᵀ = E := by
    have hs : (C - R)ᵀ = C - R := by
      simpa only [conjTranspose_eq_transpose_of_trivial] using
        (hC.isHermitian.sub hR.isHermitian).eq
    simp only [E, transpose_mul, hAt, hs, mul_assoc]
  have hRself : A * R * A - 1 = -E := by
    dsimp only [E]
    rw [mul_sub, sub_mul, hwhite]
    abel
  have hRfrob : frobSq (A * R * A - 1) ≤ 1 / 100 := by
    rw [hRself]
    have he : frobSq (-E) = frobSq E := by simp [frobSq]
    rw [he]
    exact hCerr.trans (by norm_num)
  have hRsym : Rᵀ = R := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hCbelowR := (Robust.RBAux.relative_bounds C R hC hRsym hRfrob).2.1
  have hRbelowS := (Robust.RBAux.relative_bounds S R hS hRsym
    (hRerr.trans (by norm_num))).2.2
  have hCbelowS : LE C ((11 / 9 : ℝ) • S) := by
    intro v
    have h₁ := hCbelowR v
    have h₂ := hRbelowS v
    simp only [qform, smul_mulVec, dotProduct_smul, smul_eq_mul] at h₁ h₂ ⊢
    linarith only [h₁, h₂]
  have hT (v : Vec d) : qform (Tᵀ * T) v ≤ (11 / 9) * sqnorm v := by
    have he : qform (Tᵀ * T) v = sqNormIn S (CFC.sqrt C *ᵥ v) := by
      rw [sqNormIn_eq_norm_sq hS, EuclideanSpace.real_norm_sq_eq]
      have hnorm : qform (Tᵀ * T) v = sqnorm (T *ᵥ v) := by
        simp only [qform, sqnorm, ← mulVec_mulVec, dotProduct_mulVec,
          ← mulVec_transpose, transpose_transpose]
      rw [hnorm]
      simp [sqnorm, T, B, dotProduct, pow_two, ← mulVec_mulVec]
    rw [he]
    simpa only [sqNormIn_sqrt C hC] using
      sqNormIn_comparison S C hS hC (11 / 9) hCbelowS (CFC.sqrt C *ᵥ v)
  have heq : T * E * Tᵀ = B * (C - R) * B := by
    dsimp only [T, E]
    rw [transpose_mul, hCt, hBt]
    calc
      _ = B * (CFC.sqrt C * A) * (C - R) * (A * CFC.sqrt C) * B := by
        simp only [mul_assoc]
      _ = _ := by
        rw [show CFC.sqrt C * A = 1 from mul_nonsing_inv _ hCunit,
          show A * CFC.sqrt C = 1 from nonsing_inv_mul _ hCunit]
        simp only [mul_one]
  have herr := (frobSq_congruence_le T E hE (11 / 9) (by norm_num) hT).trans
    (mul_le_mul_of_nonneg_left hCerr (sq_nonneg (11 / 9 : ℝ)))
  rw [heq] at herr
  have hsum : B * C * B - 1 = B * (C - R) * B + (B * R * B - 1) := by
    rw [mul_sub, sub_mul]
    abel
  rw [hsum]
  have hh := frobSq_add_le (B * (C - R) * B) (B * R * B - 1)
  linarith only [hh, herr, hRerr]


end

end ABBKS26.Select.LearnAux
