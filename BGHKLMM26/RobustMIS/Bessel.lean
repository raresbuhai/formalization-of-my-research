module

public import BGHKLMM26.RobustMIS.Static

/-!
# Static Gaussian lemmas in `ℝⁿ`: Bessel bounds

Lemma 4.1 of `eldan-proof.tex`: `|E[h x]| ≤ ‖h‖₂`, `‖E[(x xᵀ - I) h]‖_HS ≤ √2 ‖h‖₂` (from
`E(yᵀ M y - tr M)² = 2‖M‖²_HS`, i.e. `E[(xᵢxⱼ - δᵢⱼ)(xₖxₗ - δₖₗ)] = δᵢₖδⱼₗ + δᵢₗδⱼₖ`),
`‖g - S‖₂² ≤ λ(S)`, hence `‖B‖²_HS ≤ 2 λ(S)` (as `E[x xᵀ - I] = 0`) and `|D(g)| ≤ 1/2`
(with `norm_hermite1_le` and `qf_mul_abs_Psi_le`); and `B` in an orthonormal basis.

All statements are proved. The fourth moments are computed in the coordinates of
`map_pi_eq_stdGaussian`: `E ∏ₘ xₘ^{cₘ} = ∏ₘ E Z^{cₘ}` (`Bessel.integral_prod_pow`), the moments
`E Z^k` for `k ≤ 4` from the moment generating function (`Bessel.mom_four`), and Wick's formula
`E[xᵢxⱼxₖxₗ] = δᵢⱼδₖₗ + δᵢₖδⱼₗ + δᵢₗδⱼₖ` by cases (`Bessel.wick4`). Then
`T = ‖M‖²_HS = E[Q h]` with `Q = Σ Mᵢⱼ (xᵢxⱼ - δᵢⱼ)`, `E Q² = 2T`, and Cauchy–Schwarz. The
orthonormal-basis formula is `‖A M Aᵀ‖_F = ‖M‖_F` for the orthogonal matrix `A = (bᵢ)ₖ`.
-/

@[expose] public section

namespace BGHKLMM26.RobustMIS

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

variable {n : ℕ}

namespace Bessel

/-- The moments `E Z^k` of a standard Gaussian. -/
noncomputable def mom (k : ℕ) : ℝ := ∫ t, t ^ k ∂gaussianReal 0 1

theorem integrable_pow (k : ℕ) : Integrable (fun t : ℝ ↦ t ^ k) (gaussianReal 0 1) := by
  have h := (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ENNReal) (by simp)).integrable_norm_pow'
  refine h.mono' (by fun_prop) (ae_of_all _ fun t ↦ ?_)
  simp [norm_pow]

theorem mom_eq_iteratedDeriv (k : ℕ) :
    mom k = iteratedDeriv k (fun t ↦ rexp (t ^ 2 / 2)) 0 := by
  have h := iteratedDeriv_mgf_zero (X := fun x : ℝ ↦ x) (μ := gaussianReal 0 1) (by simp) k
  rw [mgf_fun_id_gaussianReal] at h
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul] at h
  rw [mom, h]
  rfl

theorem hasDerivAt_e (t : ℝ) : HasDerivAt (fun t ↦ rexp (t ^ 2 / 2)) (t * rexp (t ^ 2 / 2)) t := by
  have := ((hasDerivAt_pow 2 t).div_const 2).exp
  convert this using 1
  push_cast
  ring

theorem iteratedDeriv_e_four :
    iteratedDeriv 4 (fun t ↦ rexp (t ^ 2 / 2)) 0 = 3 ∧
      iteratedDeriv 3 (fun t ↦ rexp (t ^ 2 / 2)) 0 = 0 ∧
      iteratedDeriv 2 (fun t ↦ rexp (t ^ 2 / 2)) 0 = 1 ∧
      iteratedDeriv 1 (fun t ↦ rexp (t ^ 2 / 2)) 0 = 0 := by
  have d1 : iteratedDeriv 1 (fun t ↦ rexp (t ^ 2 / 2)) = fun t ↦ t * rexp (t ^ 2 / 2) := by
    rw [iteratedDeriv_one]; funext t; exact (hasDerivAt_e t).deriv
  have d2 : iteratedDeriv 2 (fun t ↦ rexp (t ^ 2 / 2)) =
      fun t ↦ (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, d1]; funext t
    have h : HasDerivAt (fun t ↦ t * rexp (t ^ 2 / 2)) ((1 + t ^ 2) * rexp (t ^ 2 / 2)) t := by
      have := (hasDerivAt_id t).mul (hasDerivAt_e t)
      exact this.congr_deriv (by simp only [id]; ring)
    rw [h.deriv]
  have d3 : iteratedDeriv 3 (fun t ↦ rexp (t ^ 2 / 2)) =
      fun t ↦ (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, d2]; funext t
    have h : HasDerivAt (fun t ↦ (1 + t ^ 2) * rexp (t ^ 2 / 2))
        ((3 * t + t ^ 3) * rexp (t ^ 2 / 2)) t := by
      have := (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_pow 2 t))).mul (hasDerivAt_e t)
      exact this.congr_deriv (by simp only [Pi.add_apply]; push_cast; ring)
    rw [h.deriv]
  have d4 : iteratedDeriv 4 (fun t ↦ rexp (t ^ 2 / 2)) =
      fun t ↦ (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, d3]; funext t
    have h : HasDerivAt (fun t ↦ (3 * t + t ^ 3) * rexp (t ^ 2 / 2))
        ((3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2)) t := by
      have := ((((hasDerivAt_id t).const_mul (3 : ℝ)).add (hasDerivAt_pow 3 t))).mul
        (hasDerivAt_e t)
      exact this.congr_deriv (by simp only [Pi.add_apply, id]; push_cast; ring)
    rw [h.deriv]
  rw [d1, d2, d3, d4]
  simp

theorem mom_zero : mom 0 = 1 := by simp [mom]
theorem mom_one : mom 1 = 0 := by rw [mom_eq_iteratedDeriv]; exact iteratedDeriv_e_four.2.2.2
theorem mom_two : mom 2 = 1 := by rw [mom_eq_iteratedDeriv]; exact iteratedDeriv_e_four.2.2.1
theorem mom_three : mom 3 = 0 := by rw [mom_eq_iteratedDeriv]; exact iteratedDeriv_e_four.2.1
theorem mom_four : mom 4 = 3 := by rw [mom_eq_iteratedDeriv]; exact iteratedDeriv_e_four.1

/-- Monomials in the coordinates are integrable. -/
theorem integrable_prod_pow (c : Fin n → ℕ) :
    Integrable (fun x : Gs n ↦ ∏ m, x m ^ c m) (gm n) := by
  rw [show gm n = _ from (map_pi_eq_stdGaussian (ι := Fin n)).symm,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  exact Integrable.fintype_prod (f := fun m t ↦ t ^ c m) fun m ↦ integrable_pow (c m)

/-- Moments of monomials: `E ∏ xₘ^{cₘ} = ∏ E Z^{cₘ}`. -/
theorem integral_prod_pow (c : Fin n → ℕ) :
    ∫ x : Gs n, ∏ m, x m ^ c m ∂gm n = ∏ m, mom (c m) := by
  rw [show gm n = _ from (map_pi_eq_stdGaussian (ι := Fin n)).symm,
    integral_map (by fun_prop) (by fun_prop)]
  exact integral_fintype_prod_eq_prod (fun m t ↦ t ^ c m)


theorem mono2 (i j : Fin n) (x : Gs n) :
    x i * x j = ∏ m, x m ^ ((if m = i then 1 else 0) + (if m = j then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib]
  simp only [pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem mono4 (i j k l : Fin n) (x : Gs n) :
    x i * x j * x k * x l = ∏ m, x m ^ ((if m = i then 1 else 0) + (if m = j then 1 else 0) +
      (if m = k then 1 else 0) + (if m = l then 1 else 0)) := by
  simp only [pow_add, Finset.prod_mul_distrib]
  simp only [pow_ite, pow_one, pow_zero, Finset.prod_ite_eq', Finset.mem_univ, ite_true]

theorem integrable_mono2 (i j : Fin n) : Integrable (fun x : Gs n ↦ x i * x j) (gm n) := by
  simp_rw [mono2 i j]; exact integrable_prod_pow _

theorem integrable_mono4 (i j k l : Fin n) :
    Integrable (fun x : Gs n ↦ x i * x j * x k * x l) (gm n) := by
  simp_rw [mono4 i j k l]; exact integrable_prod_pow _

theorem integral_mono2 (i j : Fin n) :
    ∫ x : Gs n, x i * x j ∂gm n = if i = j then 1 else 0 := by
  simp_rw [mono2 i j]
  rw [integral_prod_pow]
  by_cases hij : i = j
  · subst hij
    rw [Finset.prod_eq_single i (fun m _ hm ↦ by simp [hm, mom_zero]) (by simp)]
    simp [mom_two]
  · rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hij, mom_one])]
    simp [hij]

theorem wick4 (i j k l : Fin n) :
    ∏ m, mom ((if m = i then 1 else 0) + (if m = j then 1 else 0) + (if m = k then 1 else 0) +
      (if m = l then 1 else 0)) =
    (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) := by
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        rw [Finset.prod_eq_single i (fun m _ hm ↦ by simp [hm, mom_zero]) (by simp)]
        simp [mom_four]; norm_num
      · rw [Finset.prod_eq_one (fun m _ ↦ by
          by_cases h1 : m = i <;> by_cases h2 : m = k <;> simp_all [mom_zero, mom_two])]
        simp [hik]
    · by_cases hik : k = i
      · subst hik
        have hli : l ≠ k := Ne.symm hkl
        rw [Finset.prod_eq_zero (Finset.mem_univ l) (by simp [hli, mom_one])]
        simp [hkl]
      · rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hik, hkl, mom_one])]
        simp [hkl, Ne.symm hik]
  · by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · subst hjl
        rw [Finset.prod_eq_one (fun m _ ↦ by
          by_cases h1 : m = i <;> by_cases h2 : m = j <;> simp_all [mom_zero, mom_two])]
        simp [hij]
      · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hij, hjl, mom_one])]
        simp [hij, hjl, Ne.symm hij]
    · by_cases hil : i = l
      · subst hil
        by_cases hjk : j = k
        · subst hjk
          rw [Finset.prod_eq_one (fun m _ ↦ by
            by_cases h1 : m = i <;> by_cases h2 : m = j <;> simp_all [mom_zero, mom_two])]
          simp [hij]
        · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Ne.symm hij, hjk, mom_one])]
          simp [hij, hik, hjk]
      · rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hij, hik, hil, mom_one])]
        simp [hij, hik, hil]

theorem integral_mono4 (i j k l : Fin n) :
    ∫ x : Gs n, x i * x j * x k * x l ∂gm n =
      (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) := by
  simp_rw [mono4 i j k l]
  rw [integral_prod_pow, wick4]


/-- `H_ij(x) = x_i x_j - δ_ij`. -/
noncomputable def H (i j : Fin n) (x : Gs n) : ℝ := x i * x j - if i = j then 1 else 0

theorem H_expand (i j k l : Fin n) : (fun x ↦ H i j x * H k l x) = fun x : Gs n ↦
    x i * x j * x k * x l - (if k = l then 1 else 0) * (x i * x j) -
      (if i = j then 1 else 0) * (x k * x l) +
        (if i = j then 1 else 0) * (if k = l then (1 : ℝ) else 0) := by
  funext x; unfold H; ring

theorem integrable_H_mul_H (i j k l : Fin n) :
    Integrable (fun x ↦ H i j x * H k l x) (gm n) := by
  rw [H_expand]
  exact (((integrable_mono4 i j k l).sub ((integrable_mono2 i j).const_mul _)).sub
    ((integrable_mono2 k l).const_mul _)).add (integrable_const _)

theorem integral_H_mul_H (i j k l : Fin n) :
    ∫ x, H i j x * H k l x ∂gm n =
      (if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0) := by
  have I1 : Integrable (fun x : Gs n ↦ (if k = l then (1 : ℝ) else 0) * (x i * x j)) (gm n) :=
    (integrable_mono2 i j).const_mul _
  have I2 : Integrable (fun x : Gs n ↦ (if i = j then (1 : ℝ) else 0) * (x k * x l)) (gm n) :=
    (integrable_mono2 k l).const_mul _
  have I3 : Integrable (fun x : Gs n ↦ x i * x j * x k * x l -
      (if k = l then (1 : ℝ) else 0) * (x i * x j)) (gm n) := (integrable_mono4 i j k l).sub I1
  have I4 : Integrable (fun x : Gs n ↦ x i * x j * x k * x l -
      (if k = l then (1 : ℝ) else 0) * (x i * x j) -
        (if i = j then (1 : ℝ) else 0) * (x k * x l)) (gm n) := I3.sub I2
  rw [H_expand, integral_add I4 (integrable_const _), integral_sub I3 I2,
    integral_sub (integrable_mono4 i j k l) I1,
    integral_const_mul, integral_const_mul, integral_mono4, integral_mono2, integral_mono2,
    integral_const]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]
  ring

theorem memLp_H (i j : Fin n) : MemLp (H i j) 2 (gm n) := by
  refine (memLp_two_iff_integrable_sq (Integrable.aestronglyMeasurable ?_)).2 ?_
  · exact (integrable_mono2 i j).sub (integrable_const _)
  · simpa only [sq] using integrable_H_mul_H i j i j

theorem integral_inner_sq (v : Gs n) : ∫ x, ⟪v, x⟫ ^ 2 ∂gm n = ‖v‖ ^ 2 := by
  have h := variance_dual_stdGaussian (E := Gs n) (innerSL ℝ v)
  rw [innerSL_apply_norm, variance_eq_integral (by fun_prop),
    integral_strongDual_stdGaussian] at h
  rw [← h]
  simp

theorem integral_sum2 {G : Fin n → Fin n → Gs n → ℝ} (hG : ∀ a b, Integrable (G a b) (gm n)) :
    ∫ x, ∑ a, ∑ b, G a b x ∂gm n = ∑ a, ∑ b, ∫ x, G a b x ∂gm n := by
  rw [integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun b _ ↦ hG a b))]
  congr 1; funext a
  rw [integral_finsetSum _ (fun b _ ↦ hG a b)]

theorem integral_sum4 (G : Fin n → Fin n → Fin n → Fin n → Gs n → ℝ)
    (hG : ∀ a b c d, Integrable (G a b c d) (gm n)) :
    ∫ x, ∑ a, ∑ b, ∑ c, ∑ d, G a b c d x ∂gm n =
      ∑ a, ∑ b, ∑ c, ∑ d, ∫ x, G a b c d x ∂gm n := by
  rw [integral_sum2 (G := fun a b x ↦ ∑ c, ∑ d, G a b c d x)
    (fun a b ↦ integrable_finsetSum _ (fun c _ ↦ integrable_finsetSum _ (fun d _ ↦ hG a b c d)))]
  congr 1; funext a; congr 1; funext b
  exact integral_sum2 (hG a b)

end Bessel

open Bessel

/-! ### Bessel bounds (Lemma 4.1) -/

theorem norm_integral_smul_le (h : Gs n → ℝ) (hh : MemLp h 2 (gm n)) :
    ‖∫ x, h x • x ∂gm n‖ ≤ √(∫ x, h x ^ 2 ∂gm n) := by
  have hint : Integrable (fun x ↦ h x • x) (gm n) := by
    have h2 : Integrable (fun x : Gs n ↦ ‖x‖ ^ 2) (gm n) :=
      (memLp_two_iff_integrable_sq_norm (by fun_prop)).1 IsGaussian.memLp_two_id
    refine Integrable.mono' ((hh.integrable_sq.add h2).div_const 2)
      (hh.aestronglyMeasurable.smul aestronglyMeasurable_id) (ae_of_all _ fun x ↦ ?_)
    rw [norm_smul, Real.norm_eq_abs, Pi.add_apply]
    nlinarith [sq_abs (h x), sq_nonneg (|h x| - ‖x‖)]
  obtain ⟨V, hV⟩ : ∃ V, ∫ x, h x • x ∂gm n = V := ⟨_, rfl⟩
  rw [hV]
  have h1 : ‖V‖ ^ 2 = ∫ x, h x * ⟪V, x⟫ ∂gm n := by
    rw [← real_inner_self_eq_norm_sq]
    have : ⟪V, V⟫ = ⟪V, ∫ x, h x • x ∂gm n⟫ := by rw [hV]
    rw [this, ← integral_inner hint V]
    congr 1; funext x
    rw [real_inner_smul_right]
  have hCS := Gaussian.sq_integral_mul_le hh (Static.memLp_inner V)
  rw [← h1, integral_inner_sq] at hCS
  have hI : 0 ≤ ∫ x, h x ^ 2 ∂gm n := integral_nonneg fun x ↦ sq_nonneg _
  have hV2 : ‖V‖ ^ 2 ≤ ∫ x, h x ^ 2 ∂gm n := by
    rcases eq_or_lt_of_le (sq_nonneg ‖V‖) with h0 | hpos
    · rw [← h0]; exact hI
    · have : ‖V‖ ^ 2 * ‖V‖ ^ 2 ≤ (∫ x, h x ^ 2 ∂gm n) * ‖V‖ ^ 2 := by nlinarith
      exact le_of_mul_le_mul_right this hpos
  calc ‖V‖ = √(‖V‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hV2

theorem hs_integral_le (h : Gs n → ℝ) (hh : MemLp h 2 (gm n)) :
    ∑ i, ∑ j, (∫ x, (x i * x j - if i = j then 1 else 0) * h x ∂gm n) ^ 2 ≤
      2 * ∫ x, h x ^ 2 ∂gm n := by
  obtain ⟨M, hM⟩ : ∃ M : Fin n → Fin n → ℝ, M = fun i j ↦ ∫ x, H i j x * h x ∂gm n :=
    ⟨_, rfl⟩
  have hMeq : ∀ i j, (∫ x, (x i * x j - if i = j then 1 else 0) * h x ∂gm n) = M i j :=
    fun i j ↦ by rw [hM]; rfl
  simp_rw [hMeq]
  have hMsymm : ∀ i j, M i j = M j i := by
    intro i j; rw [hM]; simp only [H]
    congr 1; funext x
    rw [mul_comm (x i) (x j)]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hHh : ∀ i j, Integrable (fun x ↦ H i j x * h x) (gm n) :=
    fun i j ↦ (memLp_H i j).integrable_mul hh
  obtain ⟨Q, hQ⟩ : ∃ Q : Gs n → ℝ, Q = fun x ↦ ∑ i, ∑ j, M i j * H i j x := ⟨_, rfl⟩
  have hQh : ∫ x, Q x * h x ∂gm n = ∑ i, ∑ j, M i j ^ 2 := by
    have hint1 : ∀ i j, Integrable (fun x ↦ M i j * H i j x * h x) (gm n) := fun i j ↦ by
      simp_rw [mul_assoc]; exact (hHh i j).const_mul _
    rw [hQ]
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hint1 i j))]
    congr 1; funext i
    rw [integral_finsetSum _ (fun j _ ↦ hint1 i j)]
    congr 1; funext j
    simp_rw [mul_assoc]
    rw [integral_const_mul, sq]
    congr 1
    rw [hM]
  have hQQ : ∫ x, Q x ^ 2 ∂gm n = 2 * ∑ i, ∑ j, M i j ^ 2 := by
    have hexp : ∀ x, Q x ^ 2 = ∑ i, ∑ k, ∑ j, ∑ l, M i j * M k l * (H i j x * H k l x) := by
      intro x
      rw [hQ, sq, Finset.sum_mul_sum]
      congr 1; funext i; congr 1; funext k
      rw [Finset.sum_mul_sum]
      congr 1; funext j; congr 1; funext l
      ring
    simp_rw [hexp]
    have hint : ∀ i j k l, Integrable (fun x ↦ M i j * M k l * (H i j x * H k l x)) (gm n) :=
      fun i j k l ↦ (integrable_H_mul_H i j k l).const_mul _
    rw [integral_sum4 (fun i k j l x ↦ M i j * M k l * (H i j x * H k l x))
      (fun i k j l ↦ hint i j k l)]
    simp_rw [integral_const_mul, integral_H_mul_H]
    simp only [mul_add, Finset.sum_add_distrib, ite_and, mul_ite, mul_one, mul_zero]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, Finset.mem_univ,
      ite_true, Finset.sum_const_zero]
    have hsq : ∀ x y, M x y * M y x = M x y ^ 2 := fun x y ↦ by rw [hMsymm y x]; ring
    simp only [hsq, ← sq]
    ring
  have hmemQ : MemLp Q 2 (gm n) := by
    rw [hQ]
    exact memLp_finsetSum _ fun i _ ↦ memLp_finsetSum _ fun j _ ↦ (memLp_H i j).const_mul (M i j)
  have hCS := Gaussian.sq_integral_mul_le hmemQ hh
  rw [hQh, hQQ] at hCS
  have hT : 0 ≤ ∑ i, ∑ j, M i j ^ 2 := by positivity
  have hI : 0 ≤ ∫ x, h x ^ 2 ∂gm n := integral_nonneg fun x ↦ sq_nonneg _
  rcases eq_or_lt_of_le hT with h0 | hpos
  · rw [← h0]; linarith
  · have : (∑ i, ∑ j, M i j ^ 2) * (∑ i, ∑ j, M i j ^ 2) ≤
        (∑ i, ∑ j, M i j ^ 2) * (2 * ∫ x, h x ^ 2 ∂gm n) := by nlinarith
    exact le_of_mul_le_mul_left this hpos


theorem integral_sub_mean_sq_le (h : Gs n → ℝ) (hh : Measurable h)
    (h01 : ∀ x, 0 ≤ h x ∧ h x ≤ 1) :
    ∫ x, (h x - gMean h) ^ 2 ∂gm n ≤ lam (gMean h) := by
  have hi : Integrable h (gm n) := Static.integrable_of_bdd hh (Static.abs_le_one h01)
  have hi2 : Integrable (fun x ↦ (h x - gMean h) ^ 2) (gm n) :=
    Static.integrable_of_bdd ((hh.sub measurable_const).pow_const 2) (C := 1) fun x ↦ by
      have := h01 x
      have hm := gMean_mem h h01
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [hm.1, hm.2]
  have hpt : ∀ x, (h x - gMean h) ^ 2 ≤ (1 - 2 * gMean h) * h x + gMean h ^ 2 := fun x ↦ by
    have := h01 x
    nlinarith
  calc ∫ x, (h x - gMean h) ^ 2 ∂gm n ≤ ∫ x, ((1 - 2 * gMean h) * h x + gMean h ^ 2) ∂gm n :=
        integral_mono hi2 ((hi.const_mul _).add (integrable_const _)) hpt
    _ = lam (gMean h) := by
        rw [integral_add (hi.const_mul _) (integrable_const _), integral_const_mul,
          integral_const]
        simp only [probReal_univ, smul_eq_mul, lam]
        unfold gMean
        ring

namespace Bessel

theorem integral_H (i j : Fin n) : ∫ x, H i j x ∂gm n = 0 := by
  unfold H
  rw [integral_sub (integrable_mono2 i j) (integrable_const _), integral_mono2, integral_const]
  simp

theorem integrable_H_mul {g : Gs n → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    (i j : Fin n) : Integrable (fun x ↦ H i j x * g x) (gm n) :=
  ((integrable_mono2 i j).sub (integrable_const _)).mul_bdd hg.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)

theorem bMat_eq (g : Gs n → ℝ) (i j : Fin n) : bMat g i j = ∫ x, H i j x * g x ∂gm n := rfl

end Bessel

/-- `‖B‖²_HS ≤ 2 λ(S)`. -/
theorem hs2_le (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    hs2 g ≤ 2 * lam (gMean g) := by
  have hc : ∀ x, |g x - gMean g| ≤ 1 := fun x ↦ by
    have := h01 x
    have hm := gMean_mem g h01
    rw [abs_le]; constructor <;> linarith [hm.1, hm.2]
  have hB : ∀ i j, bMat g i j =
      ∫ x, (x i * x j - if i = j then 1 else 0) * (g x - gMean g) ∂gm n := by
    intro i j
    rw [Bessel.bMat_eq]
    have h1 := Bessel.integrable_H_mul hg (Static.abs_le_one h01) i j
    have h2 : Integrable (fun x ↦ gMean g * Bessel.H i j x) (gm n) :=
      ((Bessel.integrable_mono2 i j).sub (integrable_const _)).const_mul _
    have : (fun x ↦ (x i * x j - if i = j then 1 else 0) * (g x - gMean g)) =
        fun x ↦ Bessel.H i j x * g x - gMean g * Bessel.H i j x := by
      funext x; unfold Bessel.H; ring
    rw [this, integral_sub h1 h2, integral_const_mul, Bessel.integral_H, mul_zero, sub_zero]
  have hmem : MemLp (fun x ↦ g x - gMean g) 2 (gm n) :=
    Gaussian.memLp_two_of_abs_le (hg.sub measurable_const) hc
  unfold hs2
  simp_rw [hB]
  calc _ ≤ 2 * ∫ x, (g x - gMean g) ^ 2 ∂gm n := hs_integral_le _ hmem
    _ ≤ 2 * lam (gMean g) := by
        have := integral_sub_mean_sq_le g hg h01
        linarith

/-- `|D(g)| ≤ 1/2`. -/
theorem abs_driftD_le_half (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |driftD g| ≤ 1 / 2 := by
  have hU := norm_hermite1_le g hg h01
  have hU0 := norm_nonneg (hermite1 g)
  have hq := qf_mul_abs_Psi_le (gMean g)
  have hq0 := qf_nonneg (gMean g)
  have hhs := hs2_le g hg h01
  have hhs0 : 0 ≤ hs2 g := by unfold hs2; positivity
  have hlam : lam (gMean g) ≤ 1 / 4 := by unfold lam; nlinarith [sq_nonneg (gMean g - 1 / 2)]
  have h1 : Psi (gMean g) ^ 2 * ‖hermite1 g‖ ^ 2 ≤ 1 / 16 := by
    have : |Psi (gMean g)| * ‖hermite1 g‖ ≤ 1 / 4 := by
      calc |Psi (gMean g)| * ‖hermite1 g‖ ≤ |Psi (gMean g)| * qf (gMean g) :=
            mul_le_mul_of_nonneg_left hU (abs_nonneg _)
        _ ≤ 1 / 4 := by linarith [mul_comm (qf (gMean g)) |Psi (gMean g)|]
    have h0 : 0 ≤ |Psi (gMean g)| * ‖hermite1 g‖ := by positivity
    have := pow_le_pow_left₀ h0 this 2
    rw [mul_pow, sq_abs] at this
    linarith
  have h2 : 0 ≤ Psi (gMean g) ^ 2 * ‖hermite1 g‖ ^ 2 := by positivity
  unfold driftD
  rw [abs_le]
  constructor <;> linarith

/-! ### `B` in an orthonormal basis -/

theorem bForm_eq_sum (g : Gs n → ℝ) (hg : Measurable g) (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (v w : Gs n) : bForm g v w = ∑ i, ∑ j, v i * w j * bMat g i j := by
  have hinner : ∀ a b : Gs n, ⟪a, b⟫ = ∑ i, a i * b i := fun a b ↦ by
    simp [PiLp.inner_apply, mul_comm]
  have hpt : ∀ x : Gs n, (⟪v, x⟫ * ⟪w, x⟫ - ⟪v, w⟫) * g x =
      ∑ i, ∑ j, v i * w j * (Bessel.H i j x * g x) := by
    intro x
    rw [hinner v x, hinner w x, hinner v w, Finset.sum_mul_sum]
    have : ∑ i, v i * w i = ∑ i, ∑ j, v i * w j * (if i = j then 1 else 0) := by
      congr 1; funext i
      simp [Finset.sum_ite_eq]
    rw [this, ← Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1; funext i
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1; funext j
    unfold Bessel.H; ring
  unfold bForm
  simp_rw [hpt]
  rw [Bessel.integral_sum2 (fun i j ↦
    (Bessel.integrable_H_mul hg (Static.abs_le_one h01) i j).const_mul _)]
  simp_rw [integral_const_mul, Bessel.bMat_eq]

theorem hs2_eq_orthonormalBasis (g : Gs n → ℝ) (hg : Measurable g)
    (h01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (b : OrthonormalBasis (Fin n) ℝ (Gs n)) :
    hs2 g = ∑ i, ∑ j, bForm g (b i) (b j) ^ 2 := by
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin n) (Fin n) ℝ, A = Matrix.of fun i k ↦ b i k := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℝ, M = Matrix.of fun k l ↦ bMat g k l :=
    ⟨_, rfl⟩
  have hfrob : ∀ B : Matrix (Fin n) (Fin n) ℝ, ∑ i, ∑ j, B i j ^ 2 = (B * B.transpose).trace := by
    intro B
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have horth : A.transpose * A = 1 := by
    ext k k'
    have : ∑ i, b i k * b i k' = if k' = k then 1 else 0 := by
      simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
        b.sum_inner_mul_inner (EuclideanSpace.single k 1) (EuclideanSpace.single k' 1)
    rw [Matrix.mul_apply, Matrix.one_apply, hA]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [this]
    by_cases hkk : k = k'
    · simp [hkk]
    · simp [hkk, Ne.symm hkk]
  have hB : ∀ i j, bForm g (b i) (b j) = (A * M * A.transpose) i j := by
    intro i j
    rw [bForm_eq_sum g hg h01, Matrix.mul_apply, Finset.sum_comm]
    congr 1; funext l
    rw [Matrix.mul_apply, Finset.sum_mul]
    congr 1; funext k
    rw [hA, hM]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    ring
  simp_rw [hB]
  rw [hfrob (A * M * A.transpose)]
  have hM' : hs2 g = ∑ i, ∑ j, M i j ^ 2 := by rw [hM]; rfl
  rw [hM', hfrob M, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc (M * M.transpose).trace = (M * M.transpose * (A.transpose * A)).trace := by
        rw [horth, Matrix.mul_one]
    _ = (A * (M * M.transpose * A.transpose)).trace := by
        rw [Matrix.trace_mul_comm A]; simp only [Matrix.mul_assoc]
    _ = _ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc A.transpose A, horth, Matrix.one_mul]

end BGHKLMM26.RobustMIS
