module

public import BB20.Model
public import Mathlib.Algebra.BigOperators.Field

/-!
# Marginals of the observed variables through the latent variables

[BB20, Lemmas 13 and 14], without the normalization by `X_S`. For a latent configuration `q`
(spins `±1`), the observed variables are independent given `Y = q`: each `Xᵢ` takes the value `b`
with probability `pᵢ(b | q) = e^{b aᵢ(q)} / (e^{aᵢ(q)} + e^{-aᵢ(q)})`
(`BB20.Structural.latCond`), where `aᵢ(q) = ∑_j J_{ij} q_j + hᵢ` (`BB20.Structural.latField`), and
`Y` has the law `π(q) ∝ e^{g · q} ∏ᵢ (e^{aᵢ(q)} + e^{-aᵢ(q)})` (`BB20.Structural.latProb`). So

`P(X_A = z_A) = ∑_q π(q) ∏_{i ∈ A} pᵢ(zᵢ | q)` (`BB20.Structural.marg_eq_sum_latent`).

The proof sums the joint weight `e^{g·q} ∏ᵢ e^{xᵢ aᵢ(q)}` over the observed configurations that
agree with `z` on `A`: each variable outside `A` contributes `e^{aᵢ(q)} + e^{-aᵢ(q)}`.
-/

@[expose] public section

namespace BB20.Structural

open Finset

variable {n m : ℕ} (R : RBM n m)

/-- The field `aᵢ(q) = ∑_j J_{ij} q_j + hᵢ` that the latent configuration `q` puts on the observed
variable `i`. -/
noncomputable def latField (i : Fin n) (q : Config m) : ℝ :=
  ∑ j, R.J i j * spin (q j) + R.h i

/-- The conditional probability `pᵢ(b | q) = e^{b aᵢ(q)} / (e^{aᵢ(q)} + e^{-aᵢ(q)})` that
`Xᵢ = b` given the latent configuration `q`. -/
noncomputable def latCond (i : Fin n) (b : Bool) (q : Config m) : ℝ :=
  Real.exp (spin b * latField R i q) / (Real.exp (latField R i q) + Real.exp (-latField R i q))

/-- The unnormalized probability `e^{g · q} ∏ᵢ (e^{aᵢ(q)} + e^{-aᵢ(q)})` of the latent
configuration `q`. -/
noncomputable def latWeight (q : Config m) : ℝ :=
  Real.exp (∑ j, R.g j * spin (q j)) *
    ∏ i, (Real.exp (latField R i q) + Real.exp (-latField R i q))

/-- The law `π(q)` of the latent variables. -/
noncomputable def latProb (q : Config m) : ℝ :=
  latWeight R q / ∑ q', latWeight R q'

/-- The conditional probability `∏_{i ∈ A} pᵢ(zᵢ | q)` that `X_A = z_A` given `Y = q`. -/
noncomputable def latCondSet (A : Finset (Fin n)) (z : Config n) (q : Config m) : ℝ :=
  ∏ i ∈ A, latCond R i (z i) q

theorem latCond_pos (i : Fin n) (b : Bool) (q : Config m) : 0 < latCond R i b q := by
  unfold latCond
  positivity

theorem latCond_le_one (i : Fin n) (b : Bool) (q : Config m) : latCond R i b q ≤ 1 := by
  unfold latCond
  rw [div_le_one (by positivity)]
  have h1 := Real.exp_pos (latField R i q)
  have h2 := Real.exp_pos (-latField R i q)
  cases b <;> simp [spin] <;> linarith

theorem abs_latCond_le_one (i : Fin n) (b : Bool) (q : Config m) : |latCond R i b q| ≤ 1 := by
  rw [abs_of_pos (latCond_pos R i b q)]
  exact latCond_le_one R i b q

theorem latWeight_pos (q : Config m) : 0 < latWeight R q := by
  unfold latWeight
  exact mul_pos (Real.exp_pos _) (prod_pos fun i _ ↦ by positivity)

theorem latProb_pos (q : Config m) : 0 < latProb R q :=
  div_pos (latWeight_pos R q) (sum_pos (fun q _ ↦ latWeight_pos R q) univ_nonempty)

theorem latCondSet_pos (A : Finset (Fin n)) (z : Config n) (q : Config m) :
    0 < latCondSet R A z q :=
  prod_pos fun i _ ↦ latCond_pos R i (z i) q

/-- The joint weight `exp(xᵀ J y + hᵀ x + gᵀ y) = e^{g · y} ∏ᵢ e^{xᵢ aᵢ(y)}`. -/
theorem weight_eq_latent (x : Config n) (y : Config m) :
    R.weight x y = Real.exp (∑ j, R.g j * spin (y j)) *
      ∏ i, Real.exp (spin (x i) * latField R i y) := by
  rw [← Real.exp_sum, ← Real.exp_add]
  unfold RBM.weight
  congr 1
  simp only [latField, mul_add, mul_sum, sum_add_distrib]
  have h1 : ∑ i, ∑ j, R.J i j * spin (x i) * spin (y j) =
      ∑ i, ∑ j, spin (x i) * (R.J i j * spin (y j)) :=
    sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring
  have h2 : ∑ i, R.h i * spin (x i) = ∑ i, spin (x i) * R.h i :=
    sum_congr rfl fun _ _ ↦ by ring
  rw [h1, h2]
  ring

/-- Summing a product of functions of the coordinates over the configurations that agree with `z`
on `A`. -/
theorem sum_agree_prod (A : Finset (Fin n)) (z : Config n) (f : Fin n → Bool → ℝ) :
    ∑ x : Config n, (if ∀ i ∈ A, x i = z i then ∏ i, f i (x i) else 0) =
      ∏ i, (if i ∈ A then f i (z i) else f i true + f i false) := by
  classical
  have h : ∀ i, (if i ∈ A then f i (z i) else f i true + f i false) =
      ∑ b ∈ (if i ∈ A then {z i} else univ), f i b := by
    intro i
    split_ifs <;> simp
  rw [prod_congr rfl fun i _ ↦ h i, prod_univ_sum, ← sum_filter]
  congr 1
  ext x
  simp only [Fintype.mem_piFinset, mem_filter, mem_univ, true_and]
  refine forall_congr' fun i ↦ ?_
  split_ifs with hi <;> simp [hi]

/-- `∑_{x : x_A = z_A} ∑_y exp(xᵀ J y + hᵀ x + gᵀ y) = ∑_q w(q) ∏_{i ∈ A} pᵢ(zᵢ | q)`. -/
theorem sum_agree_obsWeight (A : Finset (Fin n)) (z : Config n) :
    ∑ x : Config n, (if ∀ i ∈ A, x i = z i then R.obsWeight x else 0) =
      ∑ q, latWeight R q * latCondSet R A z q := by
  have step : ∀ x : Config n, (if ∀ i ∈ A, x i = z i then R.obsWeight x else 0) =
      ∑ q, (if ∀ i ∈ A, x i = z i then R.weight x q else 0) := by
    intro x
    split_ifs <;> simp [RBM.obsWeight]
  rw [sum_congr rfl fun x _ ↦ step x, sum_comm]
  refine sum_congr rfl fun q _ ↦ ?_
  have step2 : ∀ x : Config n, (if ∀ i ∈ A, x i = z i then R.weight x q else 0) =
      Real.exp (∑ j, R.g j * spin (q j)) *
        (if ∀ i ∈ A, x i = z i then ∏ i, Real.exp (spin (x i) * latField R i q) else 0) := by
    intro x
    rw [weight_eq_latent R, mul_ite, mul_zero]
  rw [sum_congr rfl fun x _ ↦ step2 x, ← mul_sum,
    sum_agree_prod A z fun i b ↦ Real.exp (spin b * latField R i q)]
  unfold latWeight latCondSet
  rw [mul_assoc]
  congr 1
  have hA : ∏ i ∈ A, latCond R i (z i) q = ∏ i, if i ∈ A then latCond R i (z i) q else 1 := by
    rw [prod_ite_mem, univ_inter]
  rw [hA, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  have hpos : 0 < Real.exp (latField R i q) + Real.exp (-latField R i q) := by positivity
  split_ifs
  · unfold latCond
    field_simp
  · simp [spin]

theorem sum_obsWeight_eq_sum_latWeight : ∑ x, R.obsWeight x = ∑ q, latWeight R q := by
  have := sum_agree_obsWeight R ∅ (fun _ ↦ true)
  simpa [latCondSet] using this

/-- **The marginals through the latent variables**: `P(X_A = z_A) = ∑_q π(q) ∏_{i ∈ A} pᵢ(zᵢ | q)`.
-/
theorem marg_eq_sum_latent (A : Finset (Fin n)) (z : Config n) :
    R.marg A z = ∑ q, latProb R q * latCondSet R A z q := by
  unfold RBM.marg RBM.obsProb latProb
  have h : ∀ x : Config n, (if ∀ i ∈ A, x i = z i then R.obsWeight x / ∑ x', R.obsWeight x'
      else 0) = (if ∀ i ∈ A, x i = z i then R.obsWeight x else 0) / ∑ x', R.obsWeight x' := by
    intro x
    split_ifs <;> simp
  rw [sum_congr rfl fun x _ ↦ h x, ← sum_div, sum_agree_obsWeight,
    sum_obsWeight_eq_sum_latWeight, sum_div]
  refine sum_congr rfl fun q _ ↦ ?_
  ring

theorem marg_pos_latent (A : Finset (Fin n)) (z : Config n) : 0 < R.marg A z := by
  rw [marg_eq_sum_latent]
  exact sum_pos (fun q _ ↦ mul_pos (latProb_pos R q) (latCondSet_pos R A z q)) univ_nonempty

end BB20.Structural
