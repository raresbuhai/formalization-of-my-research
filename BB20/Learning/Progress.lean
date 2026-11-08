module

public import BB20.Basic

/-!
# Conditional expectations of a variable and the variance potential

For a variable `u` and a set `A` of variables, `m_A(z) = E[X_u | X_A = z_A]` (with `X_u` as `±1`)
is `BB20.Learning.mu`. Everything is a finite sum over configurations weighted by the observed law:

* `BB20.Learning.condExp`: conditional expectations `E[h(X) | X_A = z_A]`, with the tower property
  (`BB20.Learning.condExp_condExp`) and the defining property
  `E[E[h | X_A] g] = E[h g]` for `g` depending only on `A` (`BB20.Learning.sum_condExp_mul`).
* `BB20.Learning.nu_eq`: the proxy through these conditional expectations,
  `ν_{u,I|S} = 2^{-(|I|+1)} E|m_{I ∪ S} - m_S|`.
* `BB20.Learning.psi_union_ge`: the potential `Ψ(S) = E[m_S²] ∈ [0, 1]` grows by at least
  `4 ν_{u,I|S}²` when `I` is added to `S`.
* `BB20.Learning.mu_eq_of_nbhd`: the Markov property, `m_B = m_A` when `N(u) ⊆ A ⊆ B`.
-/

@[expose] public section

namespace BB20.Learning

open Finset

variable {n m : ℕ}

/-- `g` depends only on the values on `A`. -/
def Dep (A : Finset (Fin n)) (g : Config n → ℝ) : Prop :=
  ∀ x y : Config n, (∀ i ∈ A, x i = y i) → g x = g y

theorem Dep.mono {A B : Finset (Fin n)} {g : Config n → ℝ} (h : Dep A g) (hAB : A ⊆ B) :
    Dep B g := fun x y hxy ↦ h x y fun i hi ↦ hxy i (hAB hi)

theorem Dep.comp₂ {A : Finset (Fin n)} {g₁ g₂ : Config n → ℝ} (h₁ : Dep A g₁) (h₂ : Dep A g₂)
    (f : ℝ → ℝ → ℝ) : Dep A fun x ↦ f (g₁ x) (g₂ x) := fun x y hxy ↦ by
  simp only [h₁ x y hxy, h₂ x y hxy]

theorem dep_const (A : Finset (Fin n)) (c : ℝ) : Dep A fun _ ↦ c := fun _ _ _ ↦ rfl

theorem spin_ne_zero (b : Bool) : spin b ≠ 0 := by cases b <;> simp [spin]

/-- The number of configurations agreeing with `y` on `A`. -/
theorem card_agree (A : Finset (Fin n)) (y : Config n) :
    (univ.filter fun z : Config n ↦ ∀ i ∈ A, y i = z i).card = 2 ^ (n - A.card) := by
  have h : (univ.filter fun z : Config n ↦ ∀ i ∈ A, y i = z i) =
      Fintype.piFinset fun i ↦ if i ∈ A then {y i} else univ := by
    ext z
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · simp [h i hi]
      · simp
    · intro h i hi
      have := h i
      rw [ite_eq_left hi, mem_singleton] at this
      exact this.symm
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, card_singleton, card_univ, Fintype.card_bool]
  rw [prod_ite]
  simp only [prod_const_one, prod_const, one_mul]
  congr 1
  have : (univ.filter fun i : Fin n ↦ i ∉ A) = Aᶜ := by ext; simp
  rw [this, card_compl, Fintype.card_fin]

variable (R : RBM n m)

/-- `∑_{y : y_A = z_A} P(y) h(y)`. -/
noncomputable def condNum (A : Finset (Fin n)) (h : Config n → ℝ) (z : Config n) : ℝ :=
  ∑ y, if ∀ i ∈ A, y i = z i then R.obsProb y * h y else 0

/-- The conditional expectation `E[h(X) | X_A = z_A]`. -/
noncomputable def condExp (A : Finset (Fin n)) (h : Config n → ℝ) (z : Config n) : ℝ :=
  condNum R A h z / R.marg A z

/-- The expectation `E[h(X)]`. -/
noncomputable def expect (h : Config n → ℝ) : ℝ := ∑ x, R.obsProb x * h x

/-- `m_A(z) = E[X_u | X_A = z_A]`, with `X_u` as `±1`. -/
noncomputable def mu (u : Fin n) (A : Finset (Fin n)) : Config n → ℝ :=
  condExp R A fun y ↦ spin (y u)

/-- The potential `Ψ(A) = E[m_A²]`. -/
noncomputable def psi (u : Fin n) (A : Finset (Fin n)) : ℝ := expect R fun x ↦ mu R u A x ^ 2

theorem marg_pos (A : Finset (Fin n)) (z : Config n) : 0 < R.marg A z := by
  unfold RBM.marg
  calc (0 : ℝ) < R.obsProb z := R.obsProb_pos z
    _ = if ∀ i ∈ A, z i = z i then R.obsProb z else 0 := by simp
    _ ≤ ∑ x, if ∀ i ∈ A, x i = z i then R.obsProb x else 0 :=
      single_le_sum (f := fun x ↦ if ∀ i ∈ A, x i = z i then R.obsProb x else 0)
        (fun x _ ↦ by split_ifs <;> simp [(R.obsProb_pos x).le]) (mem_univ z)

theorem marg_congr (A : Finset (Fin n)) {z z' : Config n} (h : ∀ i ∈ A, z i = z' i) :
    R.marg A z = R.marg A z' := by
  unfold RBM.marg
  refine sum_congr rfl fun x _ ↦ ?_
  have : (∀ i ∈ A, x i = z i) ↔ (∀ i ∈ A, x i = z' i) :=
    forall₂_congr fun i hi ↦ by rw [h i hi]
  simp only [this]

theorem condNum_congr (A : Finset (Fin n)) (f : Config n → ℝ) {z z' : Config n}
    (h : ∀ i ∈ A, z i = z' i) : condNum R A f z = condNum R A f z' := by
  unfold condNum
  refine sum_congr rfl fun x _ ↦ ?_
  have : (∀ i ∈ A, x i = z i) ↔ (∀ i ∈ A, x i = z' i) :=
    forall₂_congr fun i hi ↦ by rw [h i hi]
  simp only [this]

theorem dep_marg (A : Finset (Fin n)) : Dep A (R.marg A) := fun _ _ h ↦ marg_congr R A h

theorem dep_condExp (A : Finset (Fin n)) (f : Config n → ℝ) : Dep A (condExp R A f) :=
  fun _ _ h ↦ by rw [condExp, condExp, condNum_congr R A f h, marg_congr R A h]

theorem dep_mu (u : Fin n) (A : Finset (Fin n)) : Dep A (mu R u A) := dep_condExp R A _

theorem condNum_one (A : Finset (Fin n)) (z : Config n) :
    condNum R A (fun _ ↦ 1) z = R.marg A z := by
  simp [condNum, RBM.marg]

theorem marg_mono {A B : Finset (Fin n)} (hAB : A ⊆ B) (z : Config n) :
    R.marg B z ≤ R.marg A z := by
  unfold RBM.marg
  refine sum_le_sum fun x _ ↦ ?_
  by_cases hB : ∀ i ∈ B, x i = z i
  · rw [ite_eq_left hB, ite_eq_left fun i hi ↦ hB i (hAB hi)]
  · rw [ite_eq_right hB]
    split_ifs
    · exact (R.obsProb_pos x).le
    · exact le_rfl

/-- Summing a function of the values on `A` against `∑_{y_A = z_A} P(y) h(y)` over all `z`. -/
theorem sum_condNum_mul (A : Finset (Fin n)) (h F : Config n → ℝ) (hF : Dep A F) :
    ∑ z, condNum R A h z * F z = 2 ^ (n - A.card) * ∑ x, R.obsProb x * h x * F x := by
  have key : ∀ z, condNum R A h z * F z =
      ∑ y, if ∀ i ∈ A, y i = z i then R.obsProb y * h y * F y else 0 := by
    intro z
    rw [condNum, sum_mul]
    refine sum_congr rfl fun y _ ↦ ?_
    split_ifs with hy
    · rw [hF z y fun i hi ↦ (hy i hi).symm]
    · simp
  simp_rw [key]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun y _ ↦ ?_
  have : (∑ z : Config n, if ∀ i ∈ A, y i = z i then R.obsProb y * h y * F y else 0) =
      ∑ z ∈ univ.filter fun z : Config n ↦ ∀ i ∈ A, y i = z i, R.obsProb y * h y * F y :=
    (sum_filter _ _).symm
  rw [this, sum_const, card_agree, nsmul_eq_mul]
  push_cast
  ring

/-- Summing a function of the values on `A` against `P(X_A = z_A)` over all `z`. -/
theorem sum_marg_mul (A : Finset (Fin n)) (F : Config n → ℝ) (hF : Dep A F) :
    ∑ z, R.marg A z * F z = 2 ^ (n - A.card) * expect R F := by
  have := sum_condNum_mul R A (fun _ ↦ 1) F hF
  simp only [condNum_one, mul_one] at this
  exact this

/-- The defining property of the conditional expectation. -/
theorem sum_condExp_mul (A : Finset (Fin n)) (h g : Config n → ℝ) (hg : Dep A g) :
    ∑ x, R.obsProb x * condExp R A h x * g x = ∑ x, R.obsProb x * h x * g x := by
  have h1 := sum_marg_mul R A (fun z ↦ condExp R A h z * g z)
    ((dep_condExp R A h).comp₂ hg (· * ·))
  have h2 := sum_condNum_mul R A h g hg
  have h3 : ∑ z, R.marg A z * (condExp R A h z * g z) = ∑ z, condNum R A h z * g z := by
    refine sum_congr rfl fun z _ ↦ ?_
    have := (marg_pos R A z).ne'
    rw [condExp]
    field_simp
  have hpos : (0 : ℝ) < 2 ^ (n - A.card) := by positivity
  rw [h3, h2] at h1
  have := mul_left_cancel₀ hpos.ne' h1
  simp only [expect, mul_assoc] at this ⊢
  exact this.symm

theorem condExp_of_dep (A : Finset (Fin n)) {h : Config n → ℝ} (hh : Dep A h) (z : Config n) :
    condExp R A h z = h z := by
  have : condNum R A h z = h z * R.marg A z := by
    rw [condNum, RBM.marg, mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    split_ifs with hy
    · rw [hh y z hy]
      ring
    · simp
  rw [condExp, this, mul_div_assoc, div_self (marg_pos R A z).ne', mul_one]

theorem condNum_sub (A : Finset (Fin n)) (h₁ h₂ : Config n → ℝ) (z : Config n) :
    condNum R A (fun x ↦ h₁ x - h₂ x) z = condNum R A h₁ z - condNum R A h₂ z := by
  simp only [condNum, ← sum_sub_distrib]
  refine sum_congr rfl fun y _ ↦ ?_
  split_ifs <;> ring

theorem condExp_sub (A : Finset (Fin n)) (h₁ h₂ : Config n → ℝ) (z : Config n) :
    condExp R A (fun x ↦ h₁ x - h₂ x) z = condExp R A h₁ z - condExp R A h₂ z := by
  rw [condExp, condNum_sub, sub_div]
  rfl

theorem abs_condExp_le (A : Finset (Fin n)) (h : Config n → ℝ) (z : Config n) :
    |condExp R A h z| ≤ condExp R A (fun x ↦ |h x|) z := by
  rw [condExp, condExp, abs_div, abs_of_pos (marg_pos R A z)]
  refine div_le_div_of_nonneg_right ?_ (marg_pos R A z).le
  refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun y _ ↦ ?_))
  split_ifs
  · rw [abs_mul, abs_of_pos (R.obsProb_pos y)]
  · simp

theorem condNum_eq_sum (A : Finset (Fin n)) (f : Config n → ℝ) (z : Config n) :
    condNum R A f z =
      ∑ y, R.obsProb y * f y * (if ∀ i ∈ A, y i = z i then 1 else 0) := by
  simp only [condNum, mul_ite, mul_one, mul_zero]

/-- The tower property. -/
theorem condExp_condExp {A B : Finset (Fin n)} (hAB : A ⊆ B) (h : Config n → ℝ)
    (z : Config n) : condExp R A (condExp R B h) z = condExp R A h z := by
  have hdep : Dep B fun y ↦ if ∀ i ∈ A, y i = z i then (1 : ℝ) else 0 := by
    intro x y hxy
    have : (∀ i ∈ A, x i = z i) ↔ (∀ i ∈ A, y i = z i) :=
      forall₂_congr fun i hi ↦ by rw [hxy i (hAB hi)]
    simp only [this]
  rw [condExp, condExp, condNum_eq_sum, condNum_eq_sum, sum_condExp_mul R B h _ hdep]

theorem expect_condExp (A : Finset (Fin n)) (h : Config n → ℝ) :
    expect R (condExp R A h) = expect R h := by
  have := sum_condExp_mul R A h (fun _ ↦ 1) (dep_const A 1)
  simpa [expect] using this

theorem expect_mono {f g : Config n → ℝ} (hfg : ∀ x, f x ≤ g x) : expect R f ≤ expect R g :=
  sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hfg x) (R.obsProb_pos x).le

theorem expect_nonneg {f : Config n → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ expect R f :=
  sum_nonneg fun x _ ↦ mul_nonneg (R.obsProb_pos x).le (hf x)

theorem expect_const (c : ℝ) : expect R (fun _ ↦ c) = c := by
  simp [expect, ← sum_mul, R.sum_obsProb]

theorem expect_add (f g : Config n → ℝ) :
    expect R (fun x ↦ f x + g x) = expect R f + expect R g := by
  simp [expect, mul_add, sum_add_distrib]

theorem abs_mu_le (u : Fin n) (A : Finset (Fin n)) (z : Config n) : |mu R u A z| ≤ 1 := by
  refine (abs_condExp_le R A _ z).trans (le_of_eq ?_)
  simp only [abs_spin]
  exact condExp_of_dep R A (dep_const A 1) z

/-- `P(X_u = z_u, X_A = z_A) = (P(X_A = z_A) + z_u ∑_{y_A = z_A} P(y) y_u) / 2`. -/
theorem marg_insert (u : Fin n) (A : Finset (Fin n)) (z : Config n) :
    R.marg (insert u A) z =
      (R.marg A z + spin (z u) * condNum R A (fun y ↦ spin (y u)) z) / 2 := by
  simp only [RBM.marg, condNum, mul_sum, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun y _ ↦ ?_
  simp only [forall_mem_insert]
  by_cases hA : ∀ i ∈ A, y i = z i
  · rw [ite_eq_left hA, ite_eq_left hA]
    simp only [and_iff_left hA]
    cases y u <;> cases z u <;> simp [spin]
  · simp [hA]

theorem nu_empty (u : Fin n) (S : Finset (Fin n)) : R.nu u ∅ S = 0 := by
  simp [RBM.nu, mul_div_assoc, div_self (marg_pos R S _).ne']

/-- The proxy through conditional expectations: `ν_{u,I|S} = 2^{-(|I|+1)} E|m_{I ∪ S} - m_S|`. -/
theorem nu_eq (u : Fin n) {I S : Finset (Fin n)} (hIS : Disjoint I S) :
    R.nu u I S = expect R (fun x ↦ |mu R u (I ∪ S) x - mu R u S x|) / 2 ^ (I.card + 1) := by
  have hterm : ∀ z, |R.marg (insert u (I ∪ S)) z -
      R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z| =
      R.marg (I ∪ S) z * (|mu R u (I ∪ S) z - mu R u S z| / 2) := by
    intro z
    have hp := marg_pos R S z
    have hq := marg_pos R (I ∪ S) z
    rw [marg_insert, marg_insert, mu, mu, condExp, condExp]
    set p := R.marg S z
    set q := R.marg (I ∪ S) z
    set N₁ := condNum R (I ∪ S) (fun y ↦ spin (y u)) z
    set N₂ := condNum R S (fun y ↦ spin (y u)) z
    have hs : |spin (z u)| = 1 := abs_spin _
    rw [show (q + spin (z u) * N₁) / 2 - (p + spin (z u) * N₂) / 2 * q / p =
        spin (z u) * (q * ((N₁ / q - N₂ / p) / 2)) by field_simp; ring]
    rw [abs_mul, hs, one_mul, abs_mul, abs_of_pos hq, abs_div, abs_two]
  have hdep : Dep (I ∪ S) fun x ↦ |mu R u (I ∪ S) x - mu R u S x| / 2 :=
    (dep_mu R u (I ∪ S)).comp₂ ((dep_mu R u S).mono subset_union_right) (fun a b ↦ |a - b| / 2)
  have hsum := sum_marg_mul R (I ∪ S) _ hdep
  rw [RBM.nu]
  simp_rw [hterm]
  rw [hsum]
  have hcard : (I ∪ S).card = I.card + S.card := card_union_of_disjoint hIS
  have hle : I.card + S.card ≤ n := by
    rw [← hcard]
    exact (card_le_univ _).trans (by simp)
  have hn : n - S.card = (n - (I ∪ S).card) + I.card := by omega
  have hE : expect R (fun x ↦ |mu R u (I ∪ S) x - mu R u S x| / 2) =
      expect R (fun x ↦ |mu R u (I ∪ S) x - mu R u S x|) / 2 := by
    simp [expect, mul_div_assoc', sum_div]
  rw [hn, hE, pow_add, pow_succ]
  have : (0 : ℝ) < 2 ^ (n - (I ∪ S).card) := by positivity
  field_simp

theorem psi_nonneg (u : Fin n) (A : Finset (Fin n)) : 0 ≤ psi R u A :=
  expect_nonneg R fun _ ↦ sq_nonneg _

theorem psi_le_one (u : Fin n) (A : Finset (Fin n)) : psi R u A ≤ 1 := by
  calc psi R u A ≤ expect R (fun _ ↦ 1) :=
        expect_mono R fun x ↦ (sq_le_one_iff_abs_le_one _).2 (abs_mu_le R u A x)
    _ = 1 := expect_const R 1

/-- Pythagoras: `E(m_B - m_A)² = Ψ(B) - Ψ(A)` for `A ⊆ B`. -/
theorem expect_sq_sub (u : Fin n) {A B : Finset (Fin n)} (hAB : A ⊆ B) :
    expect R (fun x ↦ (mu R u B x - mu R u A x) ^ 2) = psi R u B - psi R u A := by
  have hcross : ∑ x, R.obsProb x * mu R u B x * mu R u A x =
      ∑ x, R.obsProb x * mu R u A x * mu R u A x := by
    have h1 := sum_condExp_mul R B (fun y ↦ spin (y u)) (mu R u A) ((dep_mu R u A).mono hAB)
    have h2 := sum_condExp_mul R A (fun y ↦ spin (y u)) (mu R u A) (dep_mu R u A)
    exact h1.trans h2.symm
  simp only [psi, expect]
  have : ∀ x, R.obsProb x * (mu R u B x - mu R u A x) ^ 2 =
      R.obsProb x * mu R u B x ^ 2 - 2 * (R.obsProb x * mu R u B x * mu R u A x) +
        R.obsProb x * mu R u A x * mu R u A x := fun x ↦ by ring
  simp_rw [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, hcross]
  have : ∀ x, R.obsProb x * mu R u A x * mu R u A x = R.obsProb x * mu R u A x ^ 2 :=
    fun x ↦ by ring
  simp_rw [this]
  ring

theorem sq_expect_abs_le (f : Config n → ℝ) :
    expect R (fun x ↦ |f x|) ^ 2 ≤ expect R (fun x ↦ f x ^ 2) := by
  obtain ⟨c, hc⟩ : ∃ c, c = expect R (fun x ↦ |f x|) := ⟨_, rfl⟩
  have h0 : 0 ≤ expect R (fun x ↦ (|f x| - c) ^ 2) := expect_nonneg R fun _ ↦ sq_nonneg _
  have h1 : expect R (fun x ↦ (|f x| - c) ^ 2) = expect R (fun x ↦ f x ^ 2) - c ^ 2 := by
    have : ∀ x, R.obsProb x * (|f x| - c) ^ 2 =
        R.obsProb x * f x ^ 2 - 2 * c * (R.obsProb x * |f x|) + c ^ 2 * R.obsProb x :=
      fun x ↦ by rw [sub_sq, sq_abs]; ring
    simp only [expect] at hc ⊢
    simp_rw [this, sum_add_distrib, sum_sub_distrib, ← mul_sum, R.sum_obsProb, ← hc]
    ring
  rw [← hc]
  linarith

/-- Adding `I` to `S` raises the potential by at least `4 ν_{u,I|S}²`. -/
theorem psi_union_ge (u : Fin n) {I S : Finset (Fin n)} (hIS : Disjoint I S) :
    4 * R.nu u I S ^ 2 ≤ psi R u (I ∪ S) - psi R u S := by
  rw [← expect_sq_sub R u subset_union_right]
  have h1 := sq_expect_abs_le R (fun x ↦ mu R u (I ∪ S) x - mu R u S x)
  have h2 : expect R (fun x ↦ |mu R u (I ∪ S) x - mu R u S x|) = 2 ^ (I.card + 1) * R.nu u I S := by
    rw [nu_eq R u hIS]
    field_simp
  have h3 : (2 : ℝ) ≤ 2 ^ (I.card + 1) := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (I.card + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 := R.nu_nonneg u I S
  rw [h2] at h1
  have h5 : 2 * R.nu u I S ≤ 2 ^ (I.card + 1) * R.nu u I S := mul_le_mul_of_nonneg_right h3 h4
  have h6 : (2 * R.nu u I S) ^ 2 ≤ (2 ^ (I.card + 1) * R.nu u I S) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h5 2
  nlinarith

/-- **The Markov property** for conditional expectations: `m_B = m_A` when `N(u) ⊆ A ⊆ B` and
`u ∉ B`. -/
theorem mu_eq_of_nbhd {u : Fin n} {A B : Finset (Fin n)} (hAB : A ⊆ B) (hN : R.nbhd u ⊆ A)
    (hu : u ∉ B) : mu R u B = mu R u A := by
  funext z
  have h := R.marg_mul_eq_of_nbhd_subset u (B \ A) A
    (by rw [sdiff_union_of_subset hAB]; exact hu) hN z
  rw [sdiff_union_of_subset hAB, marg_insert, marg_insert] at h
  have hA := marg_pos R A z
  have hB := marg_pos R B z
  rw [mu, mu, condExp, condExp, div_eq_div_iff hB.ne' hA.ne']
  have h' : spin (z u) * (condNum R B (fun y ↦ spin (y u)) z * R.marg A z -
      condNum R A (fun y ↦ spin (y u)) z * R.marg B z) = 0 := by
    linear_combination 2 * h
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd h0 (spin_ne_zero _)
  · linarith

end BB20.Learning
