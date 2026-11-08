module

public import BB20.Model
public import Mathlib.Algebra.BigOperators.Field

/-!
# Characters, flips and the latent factorization

Facts about configurations used by the proofs in `BB20/Basic.lean`.

* `BB20.flipAt u x`: `x` with the value at `u` flipped; summing over configurations by pairs
  `{x, flipAt u x}` (`BB20.sum_eq_sum_flipAt`).
* Characters: `χ_S(x)² = 1`, `|χ_S(x)| = 1`, the effect of changing one value, the orthogonality
  relation `∑_S χ_S(x) χ_S(y) = 2ⁿ [x = y]` and Walsh inversion for any function.
* A function depending only on the values on `A` has zero Fourier coefficients outside the subsets
  of `A`.
* The latent factorization `∑_y exp(xᵀ J y + hᵀ x + gᵀ y) = exp(hᵀ x) ∏_j (e^{a_j} + e^{-a_j})`
  with `a_j = ∑_i J_{ij} xᵢ + g_j`, so `f(x) = hᵀ x + ∑_j log(e^{a_j} + e^{-a_j})`, and a
  nonzero coefficient on at least two variables lies inside the support of one latent variable
  (`BB20.RBM.exists_latent_of_sum_ne_zero`).
* The sigmoid bounds `σ(± 2t) ≥ σ(-2γ)` for `|t| ≤ γ`.
* `P(X = x) = P(X_u = x_u | X_{∖u} = x_{∖u}) (P(X = x) + P(X = flipAt u x))`, and
  `P(X_A = z_A) > 0`, for a positive law.
-/

@[expose] public section

namespace BB20

open Finset

variable {n m : ℕ}

/-! ### Spins and characters -/

theorem spin_mul_self (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num [spin]

theorem abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> norm_num [spin]

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> norm_num [spin]

theorem chi_mul_self (S : Finset (Fin n)) (x : Config n) : chi S x * chi S x = 1 := by
  simp only [chi, ← prod_mul_distrib, spin_mul_self, prod_const_one]

theorem abs_chi (S : Finset (Fin n)) (x : Config n) : |chi S x| = 1 := by
  simp only [chi, abs_prod, abs_spin, prod_const_one]

theorem chi_update_of_notMem {S : Finset (Fin n)} {u : Fin n} (hu : u ∉ S) (x : Config n)
    (b : Bool) : chi S (Function.update x u b) = chi S x := by
  unfold chi
  refine prod_congr rfl fun i hi ↦ ?_
  rw [Function.update_of_ne (by rintro rfl; exact hu hi)]

theorem chi_update_of_mem {S : Finset (Fin n)} {u : Fin n} (hu : u ∈ S) (x : Config n)
    (b : Bool) : chi S (Function.update x u b) = spin b * chi (S.erase u) x := by
  have h := chi_update_of_notMem (notMem_erase u S) x b
  unfold chi at h ⊢
  rw [← mul_prod_erase S _ hu, h, Function.update_self]

theorem chi_eq_spin_mul {S : Finset (Fin n)} {u : Fin n} (hu : u ∈ S) (x : Config n) :
    chi S x = spin (x u) * chi (S.erase u) x := by
  conv_lhs => rw [← Function.update_eq_self u x]
  exact chi_update_of_mem hu x (x u)

/-- `χ_S(x) = χ_S(y)` when `x` and `y` agree on `S`. -/
theorem chi_congr {S : Finset (Fin n)} {x y : Config n} (h : ∀ i ∈ S, x i = y i) :
    chi S x = chi S y :=
  prod_congr rfl fun i hi ↦ by rw [h i hi]

/-! ### Flips -/

/-- `x` with the value at `u` flipped. -/
def flipAt (u : Fin n) (x : Config n) : Config n := Function.update x u (!x u)

@[simp] theorem flipAt_self (u : Fin n) (x : Config n) : flipAt u x u = !x u := by
  simp [flipAt]

theorem flipAt_of_ne {u i : Fin n} (h : i ≠ u) (x : Config n) : flipAt u x i = x i := by
  simp [flipAt, Function.update_of_ne h]

@[simp] theorem flipAt_flipAt (u : Fin n) (x : Config n) : flipAt u (flipAt u x) = x := by
  funext i
  by_cases h : i = u
  · subst h; simp
  · rw [flipAt_of_ne h, flipAt_of_ne h]

theorem flipAt_involutive (u : Fin n) : Function.Involutive (flipAt (n := n) u) :=
  flipAt_flipAt u

/-- Summing over configurations by pairs `{x, flipAt u x}`, indexed by the member with value `b`
at `u`. -/
theorem sum_eq_sum_flipAt (u : Fin n) (b : Bool) (F : Config n → ℝ) :
    ∑ x, F x = ∑ x, if x u = b then F x + F (flipAt u x) else 0 := by
  have h : ∑ x, (if x u = b then F (flipAt u x) else 0) =
      ∑ x, (if x u = b then 0 else F x) := by
    rw [← Equiv.sum_comp ((flipAt_involutive u).toPerm _)]
    refine sum_congr rfl fun x _ ↦ ?_
    simp only [Function.Involutive.coe_toPerm, flipAt_flipAt, flipAt_self]
    cases x u <;> cases b <;> simp
  calc ∑ x, F x = ∑ x, ((if x u = b then F x else 0) + (if x u = b then 0 else F x)) := by
        refine sum_congr rfl fun x _ ↦ ?_
        split_ifs <;> simp
    _ = _ := by
        rw [sum_add_distrib, ← h, ← sum_add_distrib]
        refine sum_congr rfl fun x _ ↦ ?_
        split_ifs <;> simp

/-- Flipping a value outside `A` keeps the agreement with `z` on `A`. -/
theorem agree_flipAt_iff {A : Finset (Fin n)} {u : Fin n} (hu : u ∉ A) (x z : Config n) :
    (∀ i ∈ A, flipAt u x i = z i) ↔ ∀ i ∈ A, x i = z i := by
  refine forall₂_congr fun i hi ↦ ?_
  rw [flipAt_of_ne (by rintro rfl; exact hu hi)]

theorem chi_flipAt_of_mem {S : Finset (Fin n)} {u : Fin n} (hu : u ∈ S) (x : Config n) :
    chi S (flipAt u x) = -chi S x := by
  rw [flipAt, chi_update_of_mem hu, chi_eq_spin_mul hu x, spin_not, neg_mul]

/-! ### Walsh inversion -/

/-- **Orthogonality**: `∑_S χ_S(x) χ_S(y) = 2ⁿ [x = y]`. -/
theorem sum_chi_mul_chi (x y : Config n) :
    ∑ S, chi S x * chi S y = if x = y then (2 : ℝ) ^ n else 0 := by
  have h : ∑ S, chi S x * chi S y = ∏ i, (1 + spin (x i) * spin (y i)) := by
    rw [prod_one_add, powerset_univ]
    simp only [chi, prod_mul_distrib]
  rw [h]
  split_ifs with hxy
  · subst hxy
    simp only [spin_mul_self, prod_const, card_univ, Fintype.card_fin]
    norm_num
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra! h'
      exact hxy (funext h')
    apply prod_eq_zero (mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [spin]

/-- **Walsh inversion**: `g(x) = ∑_S ĝ(S) χ_S(x)` with `ĝ(S) = 2⁻ⁿ ∑_y g(y) χ_S(y)`. -/
theorem walsh_inversion (g : Config n → ℝ) (x : Config n) :
    ∑ S, (∑ y, g y * chi S y) / 2 ^ n * chi S x = g x := by
  have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  have h : ∑ S, (∑ y, g y * chi S y) * chi S x = ∑ y, g y * ∑ S, chi S y * chi S x := by
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have h3 : ∑ S, (∑ y, g y * chi S y) / 2 ^ n * chi S x =
      (∑ S, (∑ y, g y * chi S y) * chi S x) * (2 ^ n)⁻¹ := by
    rw [sum_mul]
    exact sum_congr rfl fun _ _ ↦ by ring
  rw [h3, h]
  simp [sum_chi_mul_chi, h2]

/-- A function that depends only on the values on `A` has `∑ₓ g(x) χ_S(x) = 0` unless
`S ⊆ A`. -/
theorem sum_mul_chi_eq_zero (g : Config n → ℝ) {A S : Finset (Fin n)} (hS : ¬ S ⊆ A)
    (hg : ∀ x y : Config n, (∀ i ∈ A, x i = y i) → g x = g y) : ∑ x, g x * chi S x = 0 := by
  obtain ⟨u, huS, huA⟩ := not_subset.mp hS
  have h : ∑ x, g x * chi S x = ∑ x, g (flipAt u x) * chi S (flipAt u x) :=
    (Equiv.sum_comp ((flipAt_involutive u).toPerm _) (fun x ↦ g x * chi S x)).symm
  have h' : ∑ x, g (flipAt u x) * chi S (flipAt u x) = -∑ x, g x * chi S x := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [chi_flipAt_of_mem huS, hg (flipAt u x) x fun i hi ↦
      flipAt_of_ne (by rintro rfl; exact huA hi) x]
    ring
  linarith

/-! ### The latent factorization -/

/-- The field `a_j(x) = ∑_i J_{ij} xᵢ + g_j` on the latent variable `j`. -/
noncomputable def RBM.latentField (R : RBM n m) (x : Config n) (j : Fin m) : ℝ :=
  ∑ i, R.J i j * spin (x i) + R.g j

theorem RBM.weight_eq (R : RBM n m) (x : Config n) (y : Config m) :
    R.weight x y = Real.exp (∑ i, R.h i * spin (x i)) *
      ∏ j, Real.exp (spin (y j) * R.latentField x j) := by
  rw [← Real.exp_sum, ← Real.exp_add, weight]
  congr 1
  simp only [latentField, mul_add, sum_add_distrib, mul_sum]
  rw [sum_comm (s := (univ : Finset (Fin n)))]
  have : ∀ i j, R.J i j * spin (x i) * spin (y j) = spin (y j) * (R.J i j * spin (x i)) :=
    fun _ _ ↦ by ring
  simp only [this]
  have : ∀ j, R.g j * spin (y j) = spin (y j) * R.g j := fun _ ↦ by ring
  simp only [this]
  ring

theorem RBM.obsWeight_eq (R : RBM n m) (x : Config n) :
    R.obsWeight x = Real.exp (∑ i, R.h i * spin (x i)) *
      ∏ j, (Real.exp (R.latentField x j) + Real.exp (-R.latentField x j)) := by
  have hj : ∀ j, Real.exp (R.latentField x j) + Real.exp (-R.latentField x j) =
      ∑ b : Bool, Real.exp (spin b * R.latentField x j) := by
    intro j
    simp [spin]
  simp only [hj, Fintype.prod_sum, mul_sum, obsWeight, RBM.weight_eq]

theorem RBM.potential_eq_latent (R : RBM n m) (x : Config n) :
    R.potential x = ∑ i, R.h i * spin (x i) +
      ∑ j, Real.log (Real.exp (R.latentField x j) + Real.exp (-R.latentField x j)) := by
  rw [potential, obsWeight_eq, Real.log_mul (Real.exp_pos _).ne'
    (prod_pos fun j _ ↦ by positivity).ne', Real.log_exp,
    Real.log_prod fun j _ ↦ by positivity]

/-- `a_j(x)` depends only on the values on the support of the column `j` of `J`. -/
theorem RBM.latentField_congr (R : RBM n m) (j : Fin m) {x y : Config n}
    (h : ∀ i ∈ univ.filter fun i ↦ R.J i j ≠ 0, x i = y i) :
    R.latentField x j = R.latentField y j := by
  unfold latentField
  congr 1
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases hi : R.J i j = 0
  · simp [hi]
  · rw [h i (by simp [hi])]

/-! ### Sigmoid bounds -/

theorem condLB_eq_sigmoid (γ : ℝ) : condLB γ = sigmoid (-(2 * γ)) := by
  simp [condLB, sigmoid]

theorem sigmoid_le_sigmoid {s t : ℝ} (h : s ≤ t) : sigmoid s ≤ sigmoid t := by
  unfold sigmoid
  apply one_div_le_one_div_of_le (by positivity)
  linarith [Real.exp_le_exp.mpr (neg_le_neg h)]

theorem one_sub_sigmoid (t : ℝ) : 1 - sigmoid t = sigmoid (-t) := by
  unfold sigmoid
  have h1 : 0 < 1 + Real.exp (-t) := by positivity
  have h2 : 0 < 1 + Real.exp (- -t) := by positivity
  rw [neg_neg] at h2 ⊢
  field_simp
  rw [Real.exp_neg]
  field_simp
  ring

theorem condLB_le_sigmoid {γ t : ℝ} (h : |t| ≤ γ) : condLB γ ≤ sigmoid (2 * t) := by
  rw [condLB_eq_sigmoid]
  exact sigmoid_le_sigmoid (by linarith [neg_abs_le t])

theorem condLB_le_sigmoid_neg {γ t : ℝ} (h : |t| ≤ γ) : condLB γ ≤ sigmoid (-(2 * t)) := by
  rw [condLB_eq_sigmoid]
  exact sigmoid_le_sigmoid (by linarith [le_abs_self t])

/-! ### Consequences of positivity -/

/-- `P(X = x) = P(X_u = x_u | X_{∖u} = x_{∖u}) (P(X = x) + P(X = flipAt u x))`. -/
theorem RBM.obsProb_eq_condProb_mul (R : RBM n m) (hpos : ∀ x, 0 < R.obsProb x) (u : Fin n)
    (x : Config n) :
    R.obsProb x = (if x u then R.condProb u x else 1 - R.condProb u x) *
      (R.obsProb x + R.obsProb (flipAt u x)) := by
  have hs := add_pos (hpos (Function.update x u true)) (hpos (Function.update x u false))
  unfold condProb
  cases hx : x u
  · have e1 : Function.update x u false = x := Function.update_eq_self_iff.mpr hx.symm
    have e2 : flipAt u x = Function.update x u true := by rw [flipAt, hx]; rfl
    rw [e1] at hs ⊢
    rw [e2]
    simp only [Bool.false_eq_true, ite_false]
    field_simp
    ring
  · have e1 : Function.update x u true = x := Function.update_eq_self_iff.mpr hx.symm
    have e2 : flipAt u x = Function.update x u false := by rw [flipAt, hx]; rfl
    rw [e1] at hs ⊢
    rw [e2]
    simp only [ite_true]
    field_simp

theorem RBM.marg_pos_of (R : RBM n m) (hpos : ∀ x, 0 < R.obsProb x) (A : Finset (Fin n))
    (z : Config n) : 0 < R.marg A z := by
  classical
  unfold marg
  calc 0 < R.obsProb z := hpos z
    _ = (if ∀ i ∈ A, z i = z i then R.obsProb z else 0) := by simp
    _ ≤ _ := single_le_sum (f := fun x ↦ if ∀ i ∈ A, x i = z i then R.obsProb x else 0)
        (fun x _ ↦ by split_ifs; exacts [(hpos x).le, le_rfl]) (mem_univ z)

/-- A coefficient that is nonzero on at least two variables lies inside the support of one
column of `J`. -/
theorem RBM.exists_latent_of_sum_ne_zero (R : RBM n m) (S : Finset (Fin n)) (hS : 2 ≤ S.card)
    (h : ∑ x, R.potential x * chi S x ≠ 0) : ∃ j : Fin m, ∀ i ∈ S, R.J i j ≠ 0 := by
  classical
  by_contra hc
  push Not at hc
  apply h
  have h1 : ∀ i, ∑ x : Config n, R.h i * spin (x i) * chi S x = 0 := by
    intro i
    refine sum_mul_chi_eq_zero (fun x : Config n ↦ R.h i * spin (x i)) (A := {i}) ?_ ?_
    · intro hsub
      have := card_le_card hsub
      simp at this
      omega
    · intro x y hxy
      simp [hxy i (mem_singleton_self i)]
  have h2 : ∀ j, ∑ x : Config n, Real.log (Real.exp (R.latentField x j) +
      Real.exp (-R.latentField x j)) * chi S x = 0 := by
    intro j
    obtain ⟨i, hiS, hij⟩ := hc j
    refine sum_mul_chi_eq_zero _ (A := univ.filter fun i ↦ R.J i j ≠ 0) ?_ ?_
    · intro hsub
      have := hsub hiS
      simp [hij] at this
    · intro x y hxy
      simp only [R.latentField_congr j hxy]
  calc ∑ x, R.potential x * chi S x
      = ∑ i, ∑ x : Config n, R.h i * spin (x i) * chi S x + ∑ j, ∑ x : Config n,
          Real.log (Real.exp (R.latentField x j) + Real.exp (-R.latentField x j)) * chi S x := by
        simp only [potential_eq_latent, add_mul, sum_mul, sum_add_distrib]
        rw [sum_comm (s := (univ : Finset (Config n)))]
        congr 1
        rw [sum_comm]
    _ = 0 := by simp [h1, h2]

end BB20
