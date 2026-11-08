module

public import BB20.Basic.Cube

/-!
# Basic facts about the observed law of an RBM

Shared by the proofs of all four results. Helpers are in `BB20/Basic/`.

* The observed law is positive and normalized, and `P(X = x) ∝ exp(f(x))`.
* Walsh inversion: `f = ∑_S f̂(S) χ_S`.
* The local field `E_u(x) = ∑_{S ∋ u} f̂(S) χ_{S ∖ u}(x)`: `P(X_u = 1 | X_{∖u}) = σ(2 E_u(x))`,
  `|E_u(x)| ≤ γ` for width at most `γ`, and `E_u` depends only on the values on `N(u)`.
* Nonzero coefficients on at least two variables live inside the support of a latent variable,
  so they have at most `d` variables.
* Conditional probabilities are at least `δ = σ(-2γ)` per variable (`BB20.condLB`).
* The Markov property: given `X_S` with `N(u) ⊆ S`, `X_u` is independent of the other variables.
-/

@[expose] public section

namespace BB20

open Finset

variable {n m : ℕ}

theorem condLB_pos (γ : ℝ) : 0 < condLB γ := by
  unfold condLB
  positivity

theorem condLB_le_half {γ : ℝ} (hγ : 0 ≤ γ) : condLB γ ≤ 1 / 2 := by
  unfold condLB
  apply one_div_le_one_div_of_le (by norm_num)
  linarith [Real.one_le_exp (by linarith : 0 ≤ 2 * γ)]

theorem chi_sq {n : ℕ} (S : Finset (Fin n)) (x : Config n) : chi S x * chi S x = 1 := by
  exact chi_mul_self S x

namespace RBM

variable (R : RBM n m)

theorem obsWeight_pos (x : Config n) : 0 < R.obsWeight x := by
  exact sum_pos (fun _ _ ↦ Real.exp_pos _) univ_nonempty

theorem obsProb_pos (x : Config n) : 0 < R.obsProb x := by
  exact div_pos (R.obsWeight_pos x) (sum_pos (fun y _ ↦ R.obsWeight_pos y) univ_nonempty)

theorem sum_obsProb : ∑ x, R.obsProb x = 1 := by
  simp only [obsProb, ← sum_div]
  exact div_self (sum_pos (fun y _ ↦ R.obsWeight_pos y) univ_nonempty).ne'

/-- `P(X = x) = exp(f(x)) / ∑_y exp(f(y))`. -/
theorem obsProb_eq_exp (x : Config n) :
    R.obsProb x = Real.exp (R.potential x) / ∑ y, Real.exp (R.potential y) := by
  simp only [potential, Real.exp_log (R.obsWeight_pos _)]
  rfl

/-- **Walsh inversion**: `f(x) = ∑_S f̂(S) χ_S(x)`. -/
theorem potential_eq_sum (x : Config n) : R.potential x = ∑ S, R.fourier S * chi S x := by
  exact (walsh_inversion R.potential x).symm

/-- The **local field** of `u`: `E_u(x) = ∑_{S ∋ u} f̂(S) χ_{S ∖ u}(x)`, so that the terms of `f`
containing `u` add up to `x_u E_u(x)`. -/
noncomputable def field (u : Fin n) (x : Config n) : ℝ :=
  ∑ S ∈ univ.filter (u ∈ ·), R.fourier S * chi (S.erase u) x

/-- `P(X_u = 1 | X_{∖u} = x_{∖u}) = σ(2 E_u(x))`. -/
theorem condProb_eq (u : Fin n) (x : Config n) :
    R.condProb u x = sigmoid (2 * R.field u x) := by
  have hdiff : R.potential (Function.update x u true) - R.potential (Function.update x u false) =
      2 * R.field u x := by
    rw [potential_eq_sum, potential_eq_sum, ← sum_sub_distrib, field, mul_sum, sum_filter]
    refine sum_congr rfl fun S _ ↦ ?_
    split_ifs with hu
    · rw [chi_update_of_mem hu, chi_update_of_mem hu]
      simp only [spin, ite_true, Bool.false_eq_true, ite_false]
      ring
    · rw [chi_update_of_notMem hu, chi_update_of_notMem hu]
      ring
  rw [condProb, obsProb_eq_exp, obsProb_eq_exp, sigmoid, ← hdiff, neg_sub, Real.exp_sub]
  have hZ : 0 < ∑ y, Real.exp (R.potential y) := sum_pos (fun _ _ ↦ Real.exp_pos _) univ_nonempty
  have h1 := Real.exp_pos (R.potential (Function.update x u true))
  have h2 := Real.exp_pos (R.potential (Function.update x u false))
  field_simp

theorem field_update (u : Fin n) (x : Config n) (b : Bool) :
    R.field u (Function.update x u b) = R.field u x := by
  unfold field
  exact sum_congr rfl fun S _ ↦ by rw [chi_update_of_notMem (notMem_erase u S)]

theorem abs_field_le {γ : ℝ} (hW : R.WidthLE γ) (u : Fin n) (x : Config n) :
    |R.field u x| ≤ γ := by
  unfold field
  calc |∑ S ∈ univ.filter (u ∈ ·), R.fourier S * chi (S.erase u) x|
      ≤ ∑ S ∈ univ.filter (u ∈ ·), |R.fourier S * chi (S.erase u) x| := abs_sum_le_sum_abs _ _
    _ = ∑ S ∈ univ.filter (u ∈ ·), |R.fourier S| := by simp [abs_mul, abs_chi]
    _ ≤ γ := hW u

/-- `E_u` depends only on the values on `N(u)`. -/
theorem field_congr (u : Fin n) {x y : Config n} (h : ∀ i ∈ R.nbhd u, x i = y i) :
    R.field u x = R.field u y := by
  unfold field
  refine sum_congr rfl fun S hS ↦ ?_
  by_cases h0 : R.fourier S = 0
  · simp [h0]
  · congr 1
    refine chi_congr fun i hi ↦ h i ?_
    simp only [nbhd, mem_filter, mem_univ, true_and]
    exact ⟨ne_of_mem_erase hi, S, (mem_filter.mp hS).2, mem_of_mem_erase hi, h0⟩

/-- A nonzero Fourier coefficient on at least two variables lies inside the support of the column
of one latent variable. -/
theorem exists_latent_of_fourier_ne_zero (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (h : R.fourier S ≠ 0) : ∃ j : Fin m, ∀ i ∈ S, R.J i j ≠ 0 := by
  exact R.exists_latent_of_sum_ne_zero S hS fun h0 ↦ h (by simp [fourier, h0])

/-- The Markov random field has order at most `d`. -/
theorem card_le_of_fourier_ne_zero {d : ℕ} (hd : R.LatentDegreeLE d) (S : Finset (Fin n))
    (hS : 2 ≤ S.card) (h : R.fourier S ≠ 0) : S.card ≤ d := by
  classical
  obtain ⟨j, hj⟩ := R.exists_latent_of_fourier_ne_zero S hS h
  calc S.card ≤ (univ.filter fun i ↦ R.J i j ≠ 0).card :=
        card_le_card fun i hi ↦ by simp [hj i hi]
    _ ≤ d := by convert hd j

theorem marg_nonneg (A : Finset (Fin n)) (z : Config n) : 0 ≤ R.marg A z := by
  exact sum_nonneg fun x _ ↦ by split_ifs; exacts [(R.obsProb_pos x).le, le_rfl]

theorem marg_empty (z : Config n) : R.marg ∅ z = 1 := by
  simp [marg, sum_obsProb]

/-- Conditional probabilities are at least `δ = σ(-2γ)` per variable:
`P(X_{A ∪ B} = z_{A ∪ B}) ≥ δ^{|A ∖ B|} P(X_B = z_B)`. -/
theorem marg_ge {γ : ℝ} (hW : R.WidthLE γ) (A B : Finset (Fin n)) (z : Config n) :
    condLB γ ^ (A \ B).card * R.marg B z ≤ R.marg (A ∪ B) z := by
  classical
  have hpos := R.obsProb_pos
  have key : ∀ (u : Fin n) (x : Config n),
      condLB γ * (R.obsProb x + R.obsProb (flipAt u x)) ≤ R.obsProb x := by
    intro u x
    have hE := R.abs_field_le hW u x
    have hs := add_pos (hpos x) (hpos (flipAt u x))
    have h := R.obsProb_eq_condProb_mul hpos u x
    rw [R.condProb_eq u x] at h
    have hc : condLB γ ≤
        if x u then sigmoid (2 * R.field u x) else 1 - sigmoid (2 * R.field u x) := by
      split_ifs
      · exact condLB_le_sigmoid hE
      · rw [one_sub_sigmoid]
        exact condLB_le_sigmoid_neg hE
    calc condLB γ * (R.obsProb x + R.obsProb (flipAt u x))
        ≤ (if x u then sigmoid (2 * R.field u x) else 1 - sigmoid (2 * R.field u x)) *
          (R.obsProb x + R.obsProb (flipAt u x)) := mul_le_mul_of_nonneg_right hc hs.le
      _ = R.obsProb x := h.symm
  have hδ1 : condLB γ ≤ 1 := by
    unfold condLB
    rw [div_le_one (by positivity)]
    linarith [Real.exp_pos (2 * γ)]
  have step : ∀ (i : Fin n) (C : Finset (Fin n)),
      condLB γ * R.marg C z ≤ R.marg (insert i C) z := by
    intro i C
    by_cases hi : i ∈ C
    · rw [insert_eq_of_mem hi]
      nlinarith [R.marg_nonneg C z]
    · rw [marg, marg, sum_eq_sum_flipAt i (z i), mul_sum]
      refine sum_le_sum fun x _ ↦ ?_
      by_cases hxi : x i = z i
      · simp only [hxi, ite_true, agree_flipAt_iff hi]
        by_cases hC : ∀ j ∈ C, x j = z j
        · have hC' : ∀ j ∈ insert i C, x j = z j := by
            simpa [forall_mem_insert, hxi] using hC
          rw [ite_eq_left hC, ite_eq_left hC, ite_eq_left hC']
          exact key i x
        · have hC' : ¬ ∀ j ∈ insert i C, x j = z j := fun h ↦
            hC fun j hj ↦ h j (mem_insert_of_mem hj)
          rw [ite_eq_right hC, ite_eq_right hC, ite_eq_right hC']
          simp
      · simp only [hxi, ite_false, mul_zero]
        split_ifs
        exacts [(hpos x).le, le_rfl]
  have hind : ∀ C : Finset (Fin n), condLB γ ^ C.card * R.marg B z ≤ R.marg (C ∪ B) z := by
    intro C
    induction C using Finset.induction_on with
    | empty => simp
    | insert i C hiC ih =>
      rw [card_insert_of_notMem hiC, pow_succ, insert_union]
      calc condLB γ ^ C.card * condLB γ * R.marg B z
          = condLB γ * (condLB γ ^ C.card * R.marg B z) := by ring
        _ ≤ condLB γ * R.marg (C ∪ B) z := mul_le_mul_of_nonneg_left ih (condLB_pos γ).le
        _ ≤ _ := step i (C ∪ B)
  have := hind (A \ B)
  rwa [sdiff_union_self_eq_union] at this

/-- **The Markov property**: if `N(u) ⊆ S`, then given `X_S`, the variable `X_u` is independent
of `X_T` for every `T` not containing `u`:
`P(z_u, z_T, z_S) P(z_S) = P(z_u, z_S) P(z_T, z_S)`. -/
theorem marg_mul_eq_of_nbhd_subset (u : Fin n) (T S : Finset (Fin n)) (hu : u ∉ T ∪ S)
    (hN : R.nbhd u ⊆ S) (z : Config n) :
    R.marg (insert u (T ∪ S)) z * R.marg S z = R.marg (insert u S) z * R.marg (T ∪ S) z := by
  classical
  have hpos := R.obsProb_pos
  set c := if z u then sigmoid (2 * R.field u z) else 1 - sigmoid (2 * R.field u z) with hc
  have hx : ∀ x : Config n, x u = z u → (∀ i ∈ S, x i = z i) →
      R.obsProb x = c * (R.obsProb x + R.obsProb (flipAt u x)) := by
    intro x hxu hxS
    have h := R.obsProb_eq_condProb_mul hpos u x
    rwa [hxu, R.condProb_eq u x, R.field_congr u fun i hi ↦ hxS i (hN hi)] at h
  have hA : ∀ A : Finset (Fin n), S ⊆ A → u ∉ A → R.marg (insert u A) z = c * R.marg A z := by
    intro A hSA huA
    have e1 : R.marg (insert u A) z = ∑ x, if x u = z u then
        (if ∀ i ∈ A, x i = z i then R.obsProb x else 0) else 0 := by
      unfold marg
      refine sum_congr rfl fun x _ ↦ ?_
      by_cases h1 : x u = z u <;> by_cases h2 : ∀ i ∈ A, x i = z i <;>
        simp [h1, h2]
    have e2 : R.marg A z = ∑ x, if x u = z u then
        (if ∀ i ∈ A, x i = z i then R.obsProb x + R.obsProb (flipAt u x) else 0) else 0 := by
      unfold marg
      rw [sum_eq_sum_flipAt u (z u)]
      refine sum_congr rfl fun x _ ↦ ?_
      simp only [agree_flipAt_iff huA]
      split_ifs <;> simp
    rw [e1, e2, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    by_cases h1 : x u = z u
    · by_cases h2 : ∀ i ∈ A, x i = z i
      · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_left h2, ite_eq_left h2]
        exact hx x h1 fun i hi ↦ h2 i (hSA hi)
      · simp [h1, h2]
    · simp [h1]
  rw [hA (T ∪ S) subset_union_right hu,
    hA S subset_rfl fun h ↦ hu (mem_union_right _ h)]
  ring

theorem nu_nonneg (u : Fin n) (I S : Finset (Fin n)) : 0 ≤ R.nu u I S := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (pow_nonneg (by norm_num) _)

theorem nu_eq_zero_of_nbhd_subset (u : Fin n) (I S : Finset (Fin n)) (hu : u ∉ I ∪ S)
    (hN : R.nbhd u ⊆ S) : R.nu u I S = 0 := by
  unfold nu
  have h0 : ∀ z, R.marg (insert u (I ∪ S)) z -
      R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z = 0 := by
    intro z
    have hpos := R.marg_pos_of R.obsProb_pos S z
    have h := R.marg_mul_eq_of_nbhd_subset u I S hu hN z
    rw [sub_eq_zero, eq_div_iff hpos.ne', h]
  simp [h0]

end RBM

end BB20
