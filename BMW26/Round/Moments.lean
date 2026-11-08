module

public import BMW26.Cube.Basic
public import Background.SumOfSquares.PseudoExpectation

/-!
# The second moments of the pseudo-distribution

The rounding's analysis, before the rounding itself. With the renaming `z : Fin n ≃ Cube d` and the
coordinate cuts `χ̂ᵢ(v) = sgn (z v i)`:

* `BMW26.cutMixture`: the uniform mixture of the coordinate cuts, as a pseudo-expectation. It
  satisfies every system the cuts satisfy (`BMW26.cutMixture_approxSatisfies`), and its objective
  `∑_{u,v} Ẽ[f_u f_v]²` is `n² / d` (`BMW26.cutMixture_objective`).
* `BMW26.targetM z`: its second moments `M*_{uv} = (1/d) ∑ᵢ χ̂ᵢ(u) χ̂ᵢ(v)`.
* `BMW26.frobenius_bound`: if a pseudo-expectation has level-one mass
  `∑ᵢ Ẽ[(∑ᵥ χ̂ᵢ(v) f_v)²] ≥ (1 - ε') n²` and objective at most `n²/d + γ'`, its second moments are
  within `2 n² ε'/d + γ'` of `M*` in squared Frobenius norm: expand
  `‖M - M*‖² = ‖M‖² - 2 ⟨M, M*⟩ + ‖M*‖²` with `⟨M, M*⟩ = (1/d) ∑ᵢ Ẽ[(∑ᵥ χ̂ᵢ(v) f_v)²]`.
-/

@[expose] public section

namespace BMW26

open Finset MvPolynomial SoS

variable {n d : ℕ}

/-- The second moments of the uniform mixture of the coordinate cuts:
`M*_{uv} = (1/d) ∑ᵢ χ̂ᵢ(u) χ̂ᵢ(v)`. -/
noncomputable def targetM (z : Fin n ≃ Cube d) (u v : Fin n) : ℝ :=
  (∑ i, sgn (z u i) * sgn (z v i)) / d

/-- The coordinate cut `χ̂ᵢ`, as a point of `ℝ^n`. -/
def cutPt (z : Fin n ≃ Cube d) (i : Fin d) (v : Fin n) : ℝ := sgn (z v i)

/-- A sum of squares is nonnegative at every point. -/
theorem Rnd.eval_nonneg_of_isSumSq {h : MvPolynomial (Fin n) ℝ} (hh : IsSumSq h)
    (x : Fin n → ℝ) : 0 ≤ eval x h := by
  induction hh with
  | zero => simp
  | sq_add a _ ih =>
    rw [map_add, map_mul]
    nlinarith [mul_self_nonneg (eval x a)]

/-- **The uniform mixture of the coordinate cuts**, as a pseudo-expectation of every degree. -/
noncomputable def cutMixture (hd : 0 < d) (z : Fin n ≃ Cube d) (ℓ : ℕ) :
    PseudoExpectation (Fin n) ℓ where
  toLinearMap :=
    { toFun := fun q ↦ (∑ i, eval (cutPt z i) q) / d
      map_add' := fun f g ↦ by
        simp only [map_add, Finset.sum_add_distrib, add_div]
      map_smul' := fun c f ↦ by
        simp only [smul_eval, RingHom.id_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc] }
  map_one' := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    have : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    exact div_self this
  map_mul_self_nonneg' f _ := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul]
    exact div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _) (Nat.cast_nonneg _)

theorem cutMixture_apply (hd : 0 < d) (z : Fin n ≃ Cube d) (ℓ : ℕ)
    (q : MvPolynomial (Fin n) ℝ) :
    cutMixture hd z ℓ q = (∑ i, eval (cutPt z i) q) / d := rfl

/-- The mixture satisfies, up to any `η ≥ 0`, every system that all coordinate cuts satisfy. -/
theorem cutMixture_approxSatisfies {K : Type*} [Field K] [Algebra K ℝ] (hd : 0 < d)
    (z : Fin n ≃ Cube d) (ℓ : ℕ) (A : System (Fin n) K)
    (hA : ∀ f ∈ A, ∀ i, 0 ≤ eval (cutPt z i) (toReal f)) {η : ℝ} (hη : 0 ≤ η) :
    (cutMixture hd z ℓ).ApproxSatisfies A η 0 := by
  intro S h hh _
  have hl : -(η * coeffNorm h * ∏ i ∈ S, coeffNorm (toReal (A.get i))) ≤ 0 := by
    rw [neg_nonpos]
    exact mul_nonneg (mul_nonneg hη (Real.sqrt_nonneg _))
      (Finset.prod_nonneg fun i _ ↦ Real.sqrt_nonneg _)
  refine hl.trans ?_
  rw [cutMixture_apply]
  refine div_nonneg (Finset.sum_nonneg fun i _ ↦ ?_) (Nat.cast_nonneg _)
  rw [map_mul, System.prod, toReal, map_prod, map_prod]
  exact mul_nonneg (Rnd.eval_nonneg_of_isSumSq hh _)
    (Finset.prod_nonneg fun j _ ↦ hA _ (List.get_mem _ _) i)

/-- The second moments of the mixture are `M*`. -/
theorem Rnd.cutMixture_X_mul_X (hd : 0 < d) (z : Fin n ≃ Cube d) (ℓ : ℕ) (u v : Fin n) :
    cutMixture hd z ℓ (X u * X v) = targetM z u v := by
  rw [cutMixture_apply, targetM]
  simp only [map_mul, eval_X, cutPt]

/-- Orthogonality of the coordinate cuts: `∑ᵥ χ̂ᵢ(v) χ̂ⱼ(v) = n [i = j]`. -/
theorem Rnd.sum_sgn_mul_sgn (z : Fin n ≃ Cube d) (i j : Fin d) :
    ∑ v, sgn (z v i) * sgn (z v j) = if i = j then (n : ℝ) else 0 := by
  have hn : (n : ℝ) = 2 ^ d := by
    have := Fintype.card_congr z
    simp only [Fintype.card_fin, Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ] at this
    rw [this]; push_cast; ring
  rw [Equiv.sum_comp z (fun x ↦ sgn (x i) * sgn (x j))]
  have := sum_chi_mul_chi (m := d) {i} {j}
  simp only [chi_singleton, Finset.singleton_inj] at this
  rw [this, hn]

/-- `‖M*‖_F² = n²/d`. -/
theorem Rnd.sum_targetM_sq (hd : 0 < d) (z : Fin n ≃ Cube d) :
    ∑ u, ∑ v, targetM z u v ^ 2 = (n : ℝ) ^ 2 / d := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  set a : Fin n → Fin d → ℝ := fun u i ↦ sgn (z u i) with ha
  have key : ∀ u v, targetM z u v ^ 2 =
      (∑ i, ∑ j, (a u i * a u j) * (a v i * a v j)) / (d : ℝ) ^ 2 := by
    intro u v
    rw [targetM, div_pow, sq, Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [ha]
    ring
  have swap : ∀ F : Fin n → Fin d → Fin d → ℝ,
      ∑ x, ∑ i, ∑ j, F x i j = ∑ i, ∑ j, ∑ x, F x i j := by
    intro F
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
  have horth : ∀ i j, ∑ u, a u i * a u j = if i = j then (n : ℝ) else 0 :=
    Rnd.sum_sgn_mul_sgn z
  calc ∑ u, ∑ v, targetM z u v ^ 2
      = (∑ u, ∑ v, ∑ i, ∑ j, (a u i * a u j) * (a v i * a v j)) / (d : ℝ) ^ 2 := by
        simp_rw [key, div_eq_mul_inv, Finset.sum_mul]
    _ = (∑ i, ∑ j, (∑ u, a u i * a u j) * (∑ v, a v i * a v j)) / (d : ℝ) ^ 2 := by
        congr 1
        simp_rw [Finset.sum_mul_sum]
        calc ∑ u, ∑ v, ∑ i, ∑ j, a u i * a u j * (a v i * a v j)
            = ∑ u, ∑ i, ∑ j, ∑ v, a u i * a u j * (a v i * a v j) :=
              Finset.sum_congr rfl fun u _ ↦ swap _
          _ = ∑ i, ∑ j, ∑ u, ∑ v, a u i * a u j * (a v i * a v j) := swap _
    _ = (n : ℝ) ^ 2 / d := by
        have h3 : ∀ i j : Fin d, (∑ u, a u i * a u j) * (∑ v, a v i * a v j) =
            if i = j then (n : ℝ) ^ 2 else 0 := by
          intro i j
          rw [horth]
          split_ifs <;> ring
        simp_rw [h3]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

/-- The objective of the mixture is `n² / d`. -/
theorem cutMixture_objective (hd : 0 < d) (z : Fin n ≃ Cube d) (ℓ : ℕ) :
    ∑ u, ∑ v, cutMixture hd z ℓ (X u * X v) ^ 2 = (n : ℝ) ^ 2 / d := by
  simp_rw [Rnd.cutMixture_X_mul_X]
  exact Rnd.sum_targetM_sq hd z

/-- `Ẽ[(∑ᵥ aᵥ X_v)²] = ∑_{u,v} aᵤ aᵥ Ẽ[X_u X_v]`. -/
theorem Rnd.map_sum_sq {ℓ : ℕ} (E : PseudoExpectation (Fin n) ℓ) (a : Fin n → ℝ) :
    E ((∑ v, C (a v) * X v) ^ 2) = ∑ u, ∑ v, a u * a v * E (X u * X v) := by
  rw [sq, Finset.sum_mul_sum, E.map_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [E.map_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [show C (a u) * X u * (C (a v) * X v) = C (a u * a v) * (X u * X v) by
    rw [C_mul]; ring, E.map_C_mul]

/-- **The second moments are close to those of the mixture.** -/
theorem frobenius_bound (hd : 0 < d) (z : Fin n ≃ Cube d) {ℓ : ℕ}
    (E : PseudoExpectation (Fin n) ℓ) {ε' γ' : ℝ}
    (hmass : (1 - ε') * (n : ℝ) ^ 2 ≤ ∑ i, E ((∑ v, C (sgn (z v i)) * X v) ^ 2))
    (hobj : ∑ u, ∑ v, E (X u * X v) ^ 2 ≤ (n : ℝ) ^ 2 / d + γ') :
    ∑ u, ∑ v, (E (X u * X v) - targetM z u v) ^ 2 ≤ 2 * (n : ℝ) ^ 2 * ε' / d + γ' := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  -- the inner product `⟨M, M*⟩ = (1/d) ∑ᵢ Ẽ[(∑ᵥ χ̂ᵢ(v) X_v)²]`
  have hinner : ∑ u, ∑ v, E (X u * X v) * targetM z u v =
      (∑ i, E ((∑ v, C (sgn (z v i)) * X v) ^ 2)) / d := by
    have h1 : ∀ u v, E (X u * X v) * targetM z u v =
        (∑ i, sgn (z u i) * sgn (z v i) * E (X u * X v)) / d := by
      intro u v
      rw [targetM, ← Finset.sum_mul]
      ring
    have hdiv : ∀ (f : Fin n → ℝ) (c : ℝ), ∑ x, f x / c = (∑ x, f x) / c := by
      intro f c
      simp only [div_eq_mul_inv, Finset.sum_mul]
    simp_rw [h1, hdiv, Rnd.map_sum_sq]
    congr 1
    calc ∑ u, ∑ v, ∑ i, sgn (z u i) * sgn (z v i) * E (X u * X v)
        = ∑ u, ∑ i, ∑ v, sgn (z u i) * sgn (z v i) * E (X u * X v) :=
          Finset.sum_congr rfl fun u _ ↦ Finset.sum_comm
      _ = ∑ i, ∑ u, ∑ v, sgn (z u i) * sgn (z v i) * E (X u * X v) := Finset.sum_comm
  have hexp : ∑ u, ∑ v, (E (X u * X v) - targetM z u v) ^ 2 =
      ∑ u, ∑ v, E (X u * X v) ^ 2 - 2 * ∑ u, ∑ v, E (X u * X v) * targetM z u v +
        ∑ u, ∑ v, targetM z u v ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
    ring
  rw [hexp, hinner, Rnd.sum_targetM_sq hd z]
  have h1 : (1 - ε') * (n : ℝ) ^ 2 / d ≤ (∑ i, E ((∑ v, C (sgn (z v i)) * X v) ^ 2)) / d :=
    div_le_div_of_nonneg_right hmass hd'.le
  have h2 : 2 * (n : ℝ) ^ 2 * ε' / d = (n : ℝ) ^ 2 / d + (n : ℝ) ^ 2 / d -
      2 * ((1 - ε') * (n : ℝ) ^ 2 / d) := by
    field_simp
    ring
  rw [h2]
  linarith

end BMW26
