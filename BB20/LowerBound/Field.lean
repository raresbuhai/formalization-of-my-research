module

public import BB20.LowerBound.CondExp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The local field `E_u`: a large jump, its covariance with `X_u`, and its conditional variance

For the local field `E_u` of a variable `u` (`BB20.RBM.field`), under the observed law `P`:

* `f(x) - f(x^{⊕u}) = 2 xᵤ E_u(x)`, where `x^{⊕u}` is `x` with `xᵤ` flipped; so
  `∑ₓ E_u(x) χ_{T ∖ u}(x) = 2ⁿ f̂(T)` for `u ∈ T`, and for `i ∈ T ∖ u` some `x` has
  `|E_u(x) - E_u(x^{⊕i})| ≥ 2 |f̂(T)|` (`BB20.LowerBound.exists_abs_field_sub_ge`).
* Flipping a variable changes the probability of a configuration by a factor at least
  `δ = σ(-2γ)` (`BB20.LowerBound.condLB_mul_le_obsProb_flipAt`).
* `E[X_u | X_{∖u}] = tanh(E_u)`, so `E[H X_u] = E[H tanh(E_u)]` for `H` not depending on `xᵤ`.
* **Covariance**: for `u ∉ S`,
  `E[E_u (X_u - E[X_u | X_S])] ≥ E[(E_u - E[E_u | X_S])²] / cosh²(γ)`
  (`BB20.LowerBound.sum_sq_div_cosh_sq_le`), since `tanh` has slope at least `1 / cosh²(γ)` on
  `[-γ, γ]`.
* **Variance**: if `|E_u(x₀) - E_u(x₀^{⊕i})| ≥ 2κ` for a neighbour `i` of `u`, then
  `E[(E_u - c)²] ≥ 2κ² δ^{D+1}` for every `c` that does not depend on `xᵢ`
  (`BB20.LowerBound.le_sum_sq_sub`).
-/

@[expose] public section

namespace BB20.LowerBound

open Finset

variable {n m : ℕ} (R : RBM n m)

theorem field_flipAt (u : Fin n) (x : Config n) : R.field u (flipAt u x) = R.field u x :=
  R.field_update u x _

/-- `f(x) - f(x^{⊕u}) = 2 xᵤ E_u(x)`. -/
theorem potential_sub_flipAt (u : Fin n) (x : Config n) :
    R.potential x - R.potential (flipAt u x) = 2 * spin (x u) * R.field u x := by
  rw [R.potential_eq_sum, R.potential_eq_sum, ← sum_sub_distrib, RBM.field, mul_sum, sum_filter]
  refine sum_congr rfl fun S _ ↦ ?_
  split_ifs with hu
  · rw [chi_flipAt_of_mem hu, chi_eq_spin_mul hu x]
    ring
  · rw [flipAt, chi_update_of_notMem hu]
    ring

/-- `∑ₓ E_u(x) χ_{T ∖ u}(x) = 2ⁿ f̂(T)` for `u ∈ T`. -/
theorem sum_field_mul_chi (u : Fin n) {T : Finset (Fin n)} (hu : u ∈ T) :
    ∑ x, R.field u x * chi (T.erase u) x = 2 ^ n * R.fourier T := by
  have h1 : ∑ x, R.potential x * chi T x =
      ∑ x, R.potential (flipAt u x) * chi T (flipAt u x) :=
    (Equiv.sum_comp ((flipAt_involutive u).toPerm _) (fun x ↦ R.potential x * chi T x)).symm
  have h2 : ∀ x, R.potential x * chi T x + R.potential (flipAt u x) * chi T (flipAt u x) =
      2 * (R.field u x * chi (T.erase u) x) := by
    intro x
    rw [chi_flipAt_of_mem hu, chi_eq_spin_mul hu x]
    linear_combination (spin (x u) * chi (T.erase u) x) * potential_sub_flipAt R u x +
      (2 * R.field u x * chi (T.erase u) x) * spin_mul_self (x u)
  have h3 : ∑ x, R.potential x * chi T x = ∑ x, R.field u x * chi (T.erase u) x := by
    have h4 := sum_congr rfl fun x (_ : x ∈ univ) ↦ h2 x
    rw [sum_add_distrib, ← h1, ← mul_sum] at h4
    linarith
  rw [← h3, RBM.fourier]
  field_simp

/-- **A large jump**: for `u, i ∈ T` with `i ≠ u`, some `x` has
`|E_u(x) - E_u(x^{⊕i})| ≥ 2 |f̂(T)|`. -/
theorem exists_abs_field_sub_ge (u i : Fin n) {T : Finset (Fin n)} (hu : u ∈ T) (hi : i ∈ T)
    (hiu : i ≠ u) :
    ∃ x : Config n, 2 * |R.fourier T| ≤ |R.field u x - R.field u (flipAt i x)| := by
  by_contra h
  push Not at h
  have hi' : i ∈ T.erase u := mem_erase.mpr ⟨hiu, hi⟩
  have h1 : ∑ x, R.field u x * chi (T.erase u) x =
      ∑ x, R.field u (flipAt i x) * chi (T.erase u) (flipAt i x) :=
    (Equiv.sum_comp ((flipAt_involutive i).toPerm _)
      (fun x ↦ R.field u x * chi (T.erase u) x)).symm
  have h2 : 2 * ∑ x, R.field u x * chi (T.erase u) x =
      ∑ x, (R.field u x - R.field u (flipAt i x)) * chi (T.erase u) x := by
    rw [two_mul]
    nth_rewrite 2 [h1]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [chi_flipAt_of_mem hi']
    ring
  rw [sum_field_mul_chi R u hu] at h2
  have h3 : |∑ x, (R.field u x - R.field u (flipAt i x)) * chi (T.erase u) x| <
      ∑ _x : Config n, 2 * |R.fourier T| := by
    refine (abs_sum_le_sum_abs _ _).trans_lt
      (sum_lt_sum_of_nonempty univ_nonempty fun x _ ↦ ?_)
    rw [abs_mul, abs_chi, mul_one]
    exact h x
  rw [← h2, sum_const, card_univ] at h3
  simp only [Fintype.card_pi, Fintype.card_bool, prod_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, abs_mul, abs_two] at h3
  rw [abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)] at h3
  linarith

variable {R}

/-- The conditional probability of the value of `xᵤ` is at least `δ = σ(-2γ)`:
`δ (P(x) + P(x^{⊕u})) ≤ P(x)`. -/
theorem condLB_mul_le_obsProb {γ : ℝ} (hW : R.WidthLE γ) (u : Fin n) (x : Config n) :
    condLB γ * (R.obsProb x + R.obsProb (flipAt u x)) ≤ R.obsProb x := by
  have hE := R.abs_field_le hW u x
  have hs := add_pos (R.obsProb_pos x) (R.obsProb_pos (flipAt u x))
  have h := R.obsProb_eq_condProb_mul R.obsProb_pos u x
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

/-- Flipping one variable changes the probability by a factor at least `δ`. -/
theorem condLB_mul_le_obsProb_flipAt {γ : ℝ} (hW : R.WidthLE γ) (u : Fin n) (x : Config n) :
    condLB γ * R.obsProb x ≤ R.obsProb (flipAt u x) := by
  have h := condLB_mul_le_obsProb hW u (flipAt u x)
  rw [flipAt_flipAt] at h
  have := mul_pos (condLB_pos γ) (R.obsProb_pos (flipAt u x))
  linarith

/-- `2σ(2t) - 1 = tanh(t)`. -/
theorem two_mul_sigmoid_sub_one (t : ℝ) : 2 * sigmoid (2 * t) - 1 = Real.tanh t := by
  have he := Real.exp_pos t
  have h2 : Real.exp (2 * t) = Real.exp t * Real.exp t := by
    rw [← Real.exp_add]
    ring_nf
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, sigmoid, Real.exp_neg,
    Real.exp_neg, h2]
  field_simp
  ring

variable (R)

/-- `E[H X_u] = E[H tanh(E_u)]` for `H` not depending on `xᵤ`: `E[X_u | X_{∖u}] = tanh(E_u)`. -/
theorem sum_mul_spin_eq (u : Fin n) (H : Config n → ℝ) (hH : ∀ x, H (flipAt u x) = H x) :
    ∑ x, R.obsProb x * H x * spin (x u) =
      ∑ x, R.obsProb x * H x * Real.tanh (R.field u x) := by
  rw [← sub_eq_zero, ← sum_sub_distrib]
  set G : Config n → ℝ := fun x ↦
    R.obsProb x * H x * spin (x u) - R.obsProb x * H x * Real.tanh (R.field u x) with hG
  have h1 : ∑ x, G x = ∑ x, G (flipAt u x) :=
    (Equiv.sum_comp ((flipAt_involutive u).toPerm _) G).symm
  have h2 : ∀ x, G x + G (flipAt u x) = 0 := by
    intro x
    have hc := R.obsProb_eq_condProb_mul R.obsProb_pos u x
    rw [R.condProb_eq] at hc
    have ht := two_mul_sigmoid_sub_one (R.field u x)
    simp only [hG, hH x, flipAt_self, field_flipAt, spin_not]
    cases hx : x u
    · simp only [hx, Bool.false_eq_true, ite_false] at hc
      simp only [spin, Bool.false_eq_true, ite_false]
      linear_combination (-2 * H x) * hc + (H x * (R.obsProb x + R.obsProb (flipAt u x))) * ht
    · simp only [hx, ite_true] at hc
      simp only [spin, ite_true]
      linear_combination (2 * H x) * hc + (H x * (R.obsProb x + R.obsProb (flipAt u x))) * ht
  have h3 := sum_congr rfl fun x (_ : x ∈ univ) ↦ h2 x
  rw [sum_add_distrib, ← h1, sum_const_zero] at h3
  linarith

/-- `E[X_u | X_S] = E[tanh(E_u) | X_S]` for `u ∉ S`. -/
theorem condE_spin_eq (u : Fin n) (S : Finset (Fin n)) (huS : u ∉ S) (x : Config n) :
    condE R S (fun y ↦ spin (y u)) x = condE R S (fun y ↦ Real.tanh (R.field u y)) x := by
  unfold condE
  congr 1
  have h := sum_mul_spin_eq R u (fun y ↦ if ∀ i ∈ S, y i = x i then 1 else 0)
    (fun y ↦ by simp only [agree_flipAt_iff huS])
  simpa [mul_ite, ite_mul] using h

/-- `tanh` has slope at least `1 / cosh²(γ)` on `[-γ, γ]`. -/
theorem sq_div_cosh_sq_le {γ a b : ℝ} (ha : |a| ≤ γ) (hb : |b| ≤ γ) :
    (a - b) ^ 2 / Real.cosh γ ^ 2 ≤ (a - b) * (Real.tanh a - Real.tanh b) := by
  have hca := Real.cosh_pos a
  have hcb := Real.cosh_pos b
  have hγ : 0 ≤ γ := (abs_nonneg a).trans ha
  have htanh : Real.tanh a - Real.tanh b =
      Real.sinh (a - b) / (Real.cosh a * Real.cosh b) := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub]
    field_simp
  have hsinh : (a - b) ^ 2 ≤ (a - b) * Real.sinh (a - b) := by
    rcases le_total 0 (a - b) with h | h
    · have := Real.self_le_sinh_iff.mpr h
      nlinarith
    · have := Real.sinh_le_self_iff.mpr h
      nlinarith
  have h1 : Real.cosh a ≤ Real.cosh γ := Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hγ])
  have h2 : Real.cosh b ≤ Real.cosh γ := Real.cosh_le_cosh.mpr (by rwa [abs_of_nonneg hγ])
  have hcosh : Real.cosh a * Real.cosh b ≤ Real.cosh γ ^ 2 := by
    rw [sq]
    exact mul_le_mul h1 h2 hcb.le (Real.cosh_pos γ).le
  rw [htanh, mul_div_assoc']
  calc (a - b) ^ 2 / Real.cosh γ ^ 2 ≤ (a - b) ^ 2 / (Real.cosh a * Real.cosh b) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hcosh
    _ ≤ (a - b) * Real.sinh (a - b) / (Real.cosh a * Real.cosh b) :=
        div_le_div_of_nonneg_right hsinh (by positivity)

/-- **Covariance**: for `u ∉ S`,
`E[(E_u - E[E_u | X_S])²] / cosh²(γ) ≤ E[E_u (X_u - E[X_u | X_S])]`. -/
theorem sum_sq_div_cosh_sq_le {γ : ℝ} (hW : R.WidthLE γ) (u : Fin n) (S : Finset (Fin n))
    (huS : u ∉ S) :
    (∑ x, R.obsProb x * (R.field u x - condE R S (R.field u) x) ^ 2) / Real.cosh γ ^ 2 ≤
      ∑ x, R.obsProb x * R.field u x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x) := by
  set A := R.field u with hA
  set Ab := condE R S A with hAb
  set B : Config n → ℝ := fun x ↦ Real.tanh (A x) with hB
  set Bb := condE R S B with hBb
  have hAbS : ∀ x y : Config n, (∀ i ∈ S, x i = y i) → Ab x = Ab y :=
    fun x y h ↦ condE_congr R A h
  have hBbS : ∀ x y : Config n, (∀ i ∈ S, x i = y i) →
      (Bb x - Real.tanh (Ab x)) = (Bb y - Real.tanh (Ab y)) :=
    fun x y h ↦ by rw [hBb, condE_congr R B h, hAbS x y h]
  -- `E[A X_u] = E[A B]` and `E[X_u | X_S] = B̄`.
  have e1 : ∑ x, R.obsProb x * A x * spin (x u) = ∑ x, R.obsProb x * A x * B x :=
    sum_mul_spin_eq R u A (field_flipAt R u)
  have e2 : ∀ x, condE R S (fun y ↦ spin (y u)) x = Bb x := condE_spin_eq R u S huS
  -- The two vanishing cross terms.
  have e3 := sum_mul_sub_condE R S Ab B hAbS
  have e4 := sum_mul_sub_condE R S (fun x ↦ Bb x - Real.tanh (Ab x)) A hBbS
  have e5 : ∑ x, R.obsProb x * A x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x) =
      ∑ x, R.obsProb x * (A x - Ab x) * (B x - Real.tanh (Ab x)) := by
    simp only [e2]
    have : ∑ x, R.obsProb x * A x * (spin (x u) - Bb x) =
        ∑ x, R.obsProb x * A x * (B x - Bb x) := by
      simp only [mul_sub, sum_sub_distrib, e1]
    rw [this, ← sub_eq_zero]
    have e6 : ∑ x, R.obsProb x * A x * (B x - Bb x) -
        ∑ x, R.obsProb x * (A x - Ab x) * (B x - Real.tanh (Ab x)) =
        ∑ x, R.obsProb x * Ab x * (B x - condE R S B x) -
          ∑ x, R.obsProb x * (Bb x - Real.tanh (Ab x)) * (A x - condE R S A x) := by
      rw [← sum_sub_distrib, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ ↦ ?_
      rw [← hBb, ← hAb]
      ring
    rw [e6, e3, e4, sub_zero]
  rw [e5, sum_div]
  refine sum_le_sum fun x _ ↦ ?_
  have hAx : |A x| ≤ γ := R.abs_field_le hW u x
  have hAbx : |Ab x| ≤ γ := abs_condE_le R S A (R.abs_field_le hW u) x
  have := sq_div_cosh_sq_le hAx hAbx
  have hp := (R.obsProb_pos x).le
  calc R.obsProb x * (A x - Ab x) ^ 2 / Real.cosh γ ^ 2
      = R.obsProb x * ((A x - Ab x) ^ 2 / Real.cosh γ ^ 2) := by ring
    _ ≤ R.obsProb x * ((A x - Ab x) * (Real.tanh (A x) - Real.tanh (Ab x))) :=
        mul_le_mul_of_nonneg_left this hp
    _ = R.obsProb x * (A x - Ab x) * (B x - Real.tanh (Ab x)) := by rw [hB]; ring

/-- **Variance**: if `|E_u(x₀) - E_u(x₀^{⊕i})| ≥ 2κ` for a neighbour `i` of `u`, then
`E[(E_u - c)²] ≥ 2κ² δ^{D+1}` for every `c` that does not depend on `xᵢ`. -/
theorem le_sum_sq_sub {γ κ : ℝ} {D : ℕ} (hW : R.WidthLE γ) (hDeg : R.DegreeLE D)
    (u i : Fin n) (hi : i ∈ R.nbhd u) (hκ : 0 ≤ κ) (x₀ : Config n)
    (hx₀ : 2 * κ ≤ |R.field u x₀ - R.field u (flipAt i x₀)|) (c : Config n → ℝ)
    (hc : ∀ x, c (flipAt i x) = c x) :
    2 * κ ^ 2 * condLB γ ^ (D + 1) ≤ ∑ x, R.obsProb x * (R.field u x - c x) ^ 2 := by
  have hδ := condLB_pos γ
  have hδ1 : condLB γ ≤ 1 := by
    unfold condLB
    rw [div_le_one (by positivity)]
    linarith [Real.exp_pos (2 * γ)]
  have hjump : 4 * κ ^ 2 ≤ (R.field u x₀ - R.field u (flipAt i x₀)) ^ 2 := by
    have h := mul_le_mul hx₀ hx₀ (by positivity) (abs_nonneg _)
    rw [abs_mul_abs_self] at h
    nlinarith [h]
  set F : Config n → ℝ := fun x ↦ R.obsProb x * (R.field u x - c x) ^ 2 with hF
  have hF0 : ∀ x, 0 ≤ F x := fun x ↦ mul_nonneg (R.obsProb_pos x).le (sq_nonneg _)
  have hpair : ∀ x : Config n, (∀ j ∈ R.nbhd u, x j = x₀ j) →
      condLB γ * R.obsProb x * (2 * κ ^ 2) ≤ F x + F (flipAt i x) := by
    intro x hx
    have ha : R.field u x = R.field u x₀ := R.field_congr u hx
    have hb : R.field u (flipAt i x) = R.field u (flipAt i x₀) := by
      refine R.field_congr u fun j hj ↦ ?_
      by_cases hji : j = i
      · subst hji
        simp [hx j hj]
      · rw [flipAt_of_ne hji, flipAt_of_ne hji, hx j hj]
    have hP := condLB_mul_le_obsProb_flipAt hW i x
    have hPx := (R.obsProb_pos x).le
    simp only [hF, ha, hb, hc]
    set a := R.field u x₀
    set b := R.field u (flipAt i x₀)
    have h1 : (a - b) ^ 2 / 2 ≤ (a - c x) ^ 2 + (b - c x) ^ 2 := by
      nlinarith [sq_nonneg (a + b - 2 * c x)]
    have h2 : condLB γ * R.obsProb x * (a - c x) ^ 2 ≤ R.obsProb x * (a - c x) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hδ1 hPx
      nlinarith [sq_nonneg (a - c x)]
    have h3 : condLB γ * R.obsProb x * (b - c x) ^ 2 ≤ R.obsProb (flipAt i x) * (b - c x) ^ 2 :=
      mul_le_mul_of_nonneg_right hP (sq_nonneg _)
    have h4 : condLB γ * R.obsProb x * (2 * κ ^ 2) ≤
        condLB γ * R.obsProb x * ((a - c x) ^ 2 + (b - c x) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hδ.le hPx)
    linarith
  have hiN : ∀ x : Config n, (∀ j ∈ R.nbhd u, x j = x₀ j) → x i = x₀ i := fun x hx ↦ hx i hi
  calc 2 * κ ^ 2 * condLB γ ^ (D + 1)
      ≤ 2 * κ ^ 2 * condLB γ * (condLB γ ^ ((R.nbhd u) \ ∅).card * R.marg ∅ x₀) := by
        rw [R.marg_empty, mul_one, sdiff_empty, pow_succ (condLB γ) D]
        have : condLB γ ^ D ≤ condLB γ ^ (R.nbhd u).card :=
          pow_le_pow_of_le_one hδ.le hδ1 (hDeg u)
        have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * κ ^ 2 * condLB γ)
        linarith
    _ ≤ 2 * κ ^ 2 * condLB γ * R.marg (R.nbhd u ∪ ∅) x₀ :=
        mul_le_mul_of_nonneg_left (R.marg_ge hW _ _ x₀) (by positivity)
    _ = ∑ x, if ∀ j ∈ R.nbhd u, x j = x₀ j then condLB γ * R.obsProb x * (2 * κ ^ 2) else 0 := by
        rw [union_empty, RBM.marg, mul_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        split_ifs <;> ring
    _ ≤ ∑ x, if x i = x₀ i then F x + F (flipAt i x) else 0 := by
        refine sum_le_sum fun x _ ↦ ?_
        by_cases hx : ∀ j ∈ R.nbhd u, x j = x₀ j
        · rw [ite_eq_left hx, ite_eq_left (hiN x hx)]
          exact hpair x hx
        · rw [ite_eq_right hx]
          split_ifs
          · exact add_nonneg (hF0 x) (hF0 _)
          · exact le_rfl
    _ = ∑ x, F x := (sum_eq_sum_flipAt i (x₀ i) F).symm

end BB20.LowerBound
