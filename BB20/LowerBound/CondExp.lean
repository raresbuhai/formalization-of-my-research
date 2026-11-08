module

public import BB20.Basic

/-!
# Conditional expectations given `X_S`, and `ν` as an `L¹` distance

For the observed law `P` of an RBM:

* `BB20.LowerBound.condE R S F x = E[F(X) | X_S = x_S]`, written as a ratio of sums.
* The tower property (`BB20.LowerBound.sum_mul_condE`): `E[H F] = E[H E[F | X_S]]` when `H`
  depends only on the values on `S`.
* `ν` as an `L¹` distance (`BB20.LowerBound.sum_abs_sub_condE_eq_nu`): for disjoint `I`, `S`,
  with `m_A = E[X_u | X_A]` (`X_u` as `±1`),
  `E|m_{I ∪ S}(X) - m_S(X)| = 2^{|I| + 1} ν_{u,I|S}`.
* So the covariance of `X_u` with a function `F` of the values on `I ∪ S`, given `X_S`, is at most
  `‖F‖_∞ 2^{|I| + 1} ν_{u,I|S}` (`BB20.LowerBound.abs_sum_mul_spin_sub_le`).
-/

@[expose] public section

namespace BB20.LowerBound

open Finset

variable {n m : ℕ}

/-- The conditional expectation `E[F(X) | X_S = x_S]` under the observed law. -/
noncomputable def condE (R : RBM n m) (S : Finset (Fin n)) (F : Config n → ℝ) (x : Config n) :
    ℝ :=
  (∑ y, if ∀ i ∈ S, y i = x i then R.obsProb y * F y else 0) / R.marg S x

variable (R : RBM n m)

theorem marg_pos (S : Finset (Fin n)) (x : Config n) : 0 < R.marg S x :=
  R.marg_pos_of R.obsProb_pos S x

theorem marg_congr {S : Finset (Fin n)} {x y : Config n} (h : ∀ i ∈ S, x i = y i) :
    R.marg S x = R.marg S y := by
  unfold RBM.marg
  refine sum_congr rfl fun z _ ↦ ?_
  have : (∀ i ∈ S, z i = x i) ↔ (∀ i ∈ S, z i = y i) :=
    forall₂_congr fun i hi ↦ by rw [h i hi]
  simp only [this]

theorem condE_congr {S : Finset (Fin n)} (F : Config n → ℝ) {x y : Config n}
    (h : ∀ i ∈ S, x i = y i) : condE R S F x = condE R S F y := by
  unfold condE
  rw [marg_congr R h]
  congr 1
  refine sum_congr rfl fun z _ ↦ ?_
  have : (∀ i ∈ S, z i = x i) ↔ (∀ i ∈ S, z i = y i) :=
    forall₂_congr fun i hi ↦ by rw [h i hi]
  simp only [this]

/-- **The tower property**: `E[H F] = E[H E[F | X_S]]` when `H` depends only on the values on
`S`. -/
theorem sum_mul_condE (S : Finset (Fin n)) (H F : Config n → ℝ)
    (hH : ∀ x y : Config n, (∀ i ∈ S, x i = y i) → H x = H y) :
    ∑ x, R.obsProb x * H x * condE R S F x = ∑ x, R.obsProb x * H x * F x := by
  calc ∑ x, R.obsProb x * H x * condE R S F x
      = ∑ x, ∑ y, if ∀ i ∈ S, y i = x i then
          R.obsProb x * H x * (R.obsProb y * F y) / R.marg S x else 0 := by
        unfold condE
        refine sum_congr rfl fun x _ ↦ ?_
        rw [mul_div_assoc', mul_sum, sum_div]
        refine sum_congr rfl fun y _ ↦ ?_
        split_ifs <;> simp
    _ = ∑ y, ∑ x, if ∀ i ∈ S, y i = x i then
          R.obsProb x * H x * (R.obsProb y * F y) / R.marg S x else 0 := sum_comm
    _ = ∑ y, R.obsProb y * H y * F y *
          (∑ x, if ∀ i ∈ S, x i = y i then R.obsProb x else 0) / R.marg S y := by
        refine sum_congr rfl fun y _ ↦ ?_
        rw [mul_sum, sum_div]
        refine sum_congr rfl fun x _ ↦ ?_
        by_cases h : ∀ i ∈ S, y i = x i
        · have h' : ∀ i ∈ S, x i = y i := fun i hi ↦ (h i hi).symm
          rw [ite_eq_left h, ite_eq_left h', hH x y h', marg_congr R h']
          ring
        · have h' : ¬ ∀ i ∈ S, x i = y i := fun h' ↦ h fun i hi ↦ (h' i hi).symm
          rw [ite_eq_right h, ite_eq_right h']
          simp
    _ = ∑ y, R.obsProb y * H y * F y := by
        refine sum_congr rfl fun y _ ↦ ?_
        have hy := (marg_pos R S y).ne'
        rw [show (∑ x, if ∀ i ∈ S, x i = y i then R.obsProb x else 0) = R.marg S y from rfl]
        field_simp

theorem sum_mul_sub_condE (S : Finset (Fin n)) (H F : Config n → ℝ)
    (hH : ∀ x y : Config n, (∀ i ∈ S, x i = y i) → H x = H y) :
    ∑ x, R.obsProb x * H x * (F x - condE R S F x) = 0 := by
  simp only [mul_sub, sum_sub_distrib, sum_mul_condE R S H F hH, sub_self]

/-- `|E[F | X_S]| ≤ c` when `|F| ≤ c`. -/
theorem abs_condE_le (S : Finset (Fin n)) (F : Config n → ℝ) {c : ℝ}
    (hF : ∀ y, |F y| ≤ c) (x : Config n) : |condE R S F x| ≤ c := by
  unfold condE
  have hm := marg_pos R S x
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc |∑ y, if ∀ i ∈ S, y i = x i then R.obsProb y * F y else 0|
      ≤ ∑ y, |if ∀ i ∈ S, y i = x i then R.obsProb y * F y else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, (if ∀ i ∈ S, y i = x i then R.obsProb y else 0) * c := by
        refine sum_le_sum fun y _ ↦ ?_
        split_ifs
        · rw [abs_mul, abs_of_pos (R.obsProb_pos y), mul_comm, mul_comm _ c]
          exact mul_le_mul_of_nonneg_right (hF y) (R.obsProb_pos y).le
        · simp
    _ = c * R.marg S x := by rw [← sum_mul, mul_comm]; rfl

/-! ### Counting configurations -/

/-- `2^{n - |K|}` configurations agree with `x` on `K`. -/
theorem sum_agree (K : Finset (Fin n)) (x : Config n) :
    ∑ z : Config n, (if ∀ i ∈ K, x i = z i then (1 : ℝ) else 0) = 2 ^ (n - K.card) := by
  have h1 : ∀ z : Config n, (if ∀ i ∈ K, x i = z i then (1 : ℝ) else 0) =
      ∏ i, (if i ∈ K then (if x i = z i then (1 : ℝ) else 0) else 1) := by
    intro z
    by_cases h : ∀ i ∈ K, x i = z i
    · rw [ite_eq_left h]
      symm
      refine prod_eq_one fun i _ ↦ ?_
      split_ifs with hi hxz
      · rfl
      · exact absurd (h i hi) hxz
      · rfl
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i, hi, hne⟩ := h
      symm
      exact prod_eq_zero (mem_univ i) (by simp [hi, hne])
  simp only [h1]
  rw [← Fintype.prod_sum (fun i b ↦ if i ∈ K then (if x i = b then (1 : ℝ) else 0) else 1)]
  have h2 : ∀ i, (∑ b : Bool, if i ∈ K then (if x i = b then (1 : ℝ) else 0) else 1) =
      if i ∈ K then 1 else 2 := by
    intro i
    by_cases hi : i ∈ K
    · cases x i <;> simp [hi]
    · simp [hi]
  simp only [h2, prod_ite, prod_const_one, prod_const, one_mul]
  congr 1
  rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ K),
    card_univ, Fintype.card_fin]

/-- Summing a function of the values on `K` against `P(X_K = z_K)` over all `z`. -/
theorem sum_mul_marg (K : Finset (Fin n)) (G : Config n → ℝ)
    (hG : ∀ x y : Config n, (∀ i ∈ K, x i = y i) → G x = G y) :
    ∑ z, G z * R.marg K z = 2 ^ (n - K.card) * ∑ x, R.obsProb x * G x := by
  unfold RBM.marg
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← sum_agree K x, sum_mul]
  refine sum_congr rfl fun z _ ↦ ?_
  by_cases h : ∀ i ∈ K, x i = z i
  · have h' : ∀ i ∈ K, z i = x i := fun i hi ↦ (h i hi).symm
    rw [ite_eq_left h, ite_eq_left h, hG z x h']
    ring
  · rw [ite_eq_right h, ite_eq_right h]
    simp

/-! ### `ν` as an `L¹` distance -/

/-- `2 P(X_u = z_u, X_A = z_A) = P(X_A = z_A) (1 + z_u E[X_u | X_A = z_A])`. -/
theorem two_mul_marg_insert (u : Fin n) (A : Finset (Fin n)) (z : Config n) :
    2 * R.marg (insert u A) z =
      R.marg A z + spin (z u) * (condE R A (fun y ↦ spin (y u)) z * R.marg A z) := by
  have hm := (marg_pos R A z).ne'
  rw [condE, div_mul_cancel₀ _ hm]
  unfold RBM.marg
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun y _ ↦ ?_
  by_cases h1 : y u = z u <;> by_cases h2 : ∀ i ∈ A, y i = z i
  · have h3 : ∀ i ∈ insert u A, y i = z i := by
      simpa [forall_mem_insert, h1] using h2
    rw [ite_eq_left h3, ite_eq_left h2, ite_eq_left h2, h1]
    linear_combination (-R.obsProb y) * spin_mul_self (z u)
  · have h3 : ¬ ∀ i ∈ insert u A, y i = z i := fun h ↦ h2 fun i hi ↦ h i (mem_insert_of_mem hi)
    rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h2]
    simp
  · have h3 : ¬ ∀ i ∈ insert u A, y i = z i := fun h ↦ h1 (h u (mem_insert_self u A))
    rw [ite_eq_right h3, ite_eq_left h2, ite_eq_left h2]
    have : spin (z u) * spin (y u) = -1 := by
      cases hz : z u <;> cases hy : y u <;> simp_all [spin]
    rw [show spin (z u) * (R.obsProb y * spin (y u)) = R.obsProb y * (spin (z u) * spin (y u))
      by ring, this]
    ring
  · have h3 : ¬ ∀ i ∈ insert u A, y i = z i := fun h ↦ h1 (h u (mem_insert_self u A))
    rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h2]
    simp

/-- The term of `ν` at `z`: `P(z_u, z_I, z_S) - P(z_u, z_S) P(z_I, z_S) / P(z_S)
= ½ z_u P(z_I, z_S) (m_{I ∪ S}(z) - m_S(z))`. -/
theorem nu_term_eq (u : Fin n) (I S : Finset (Fin n)) (z : Config n) :
    R.marg (insert u (I ∪ S)) z - R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z =
      spin (z u) * R.marg (I ∪ S) z *
        (condE R (I ∪ S) (fun y ↦ spin (y u)) z - condE R S (fun y ↦ spin (y u)) z) / 2 := by
  have h1 := two_mul_marg_insert R u (I ∪ S) z
  have h2 := two_mul_marg_insert R u S z
  have hS := (marg_pos R S z).ne'
  rw [show R.marg (insert u (I ∪ S)) z = (R.marg (I ∪ S) z + spin (z u) *
      (condE R (I ∪ S) (fun y ↦ spin (y u)) z * R.marg (I ∪ S) z)) / 2 by linarith,
    show R.marg (insert u S) z = (R.marg S z + spin (z u) *
      (condE R S (fun y ↦ spin (y u)) z * R.marg S z)) / 2 by linarith]
  field_simp
  ring

/-- **`ν` as an `L¹` distance**: `E|m_{I ∪ S}(X) - m_S(X)| = 2^{|I| + 1} ν_{u,I|S}`, with
`m_A = E[X_u | X_A]`. -/
theorem sum_abs_sub_condE_eq_nu (u : Fin n) (I S : Finset (Fin n)) (hIS : Disjoint I S) :
    ∑ x, R.obsProb x * |condE R (I ∪ S) (fun y ↦ spin (y u)) x -
        condE R S (fun y ↦ spin (y u)) x| = 2 ^ (I.card + 1) * R.nu u I S := by
  set G : Config n → ℝ := fun x ↦ |condE R (I ∪ S) (fun y ↦ spin (y u)) x -
    condE R S (fun y ↦ spin (y u)) x| with hGdef
  have hG : ∀ x y : Config n, (∀ i ∈ I ∪ S, x i = y i) → G x = G y := by
    intro x y h
    simp only [hGdef]
    rw [condE_congr R _ h, condE_congr R _ fun i hi ↦ h i (mem_union_right _ hi)]
  have hsum := sum_mul_marg R (I ∪ S) G hG
  have hterm : ∀ z, |R.marg (insert u (I ∪ S)) z -
      R.marg (insert u S) z * R.marg (I ∪ S) z / R.marg S z| = G z * R.marg (I ∪ S) z / 2 := by
    intro z
    rw [nu_term_eq R u I S z, abs_div, abs_mul, abs_mul, abs_spin,
      abs_of_pos (marg_pos R _ z)]
    simp only [hGdef]
    norm_num
    ring
  have hcard : (I ∪ S).card = I.card + S.card := card_union_of_disjoint hIS
  have hle : (I ∪ S).card ≤ n := by
    simpa using card_le_card (subset_univ (I ∪ S))
  have hpow : (2 : ℝ) ^ (n - S.card) = 2 ^ (n - (I ∪ S).card) * 2 ^ I.card := by
    rw [← pow_add]
    congr 1
    omega
  unfold RBM.nu
  simp only [hterm, ← sum_div, hsum, hpow]
  have h2 : (0 : ℝ) < 2 ^ (n - (I ∪ S).card) := by positivity
  field_simp
  ring

/-- The covariance of `X_u` and a function `F` of the values on `I ∪ S` with `|F| ≤ 1`, given
`X_S`, is at most `2^{|I| + 1} ν_{u,I|S}`. -/
theorem abs_sum_mul_spin_sub_le (u : Fin n) (I S : Finset (Fin n)) (hIS : Disjoint I S)
    (F : Config n → ℝ) (hF1 : ∀ x, |F x| ≤ 1)
    (hF : ∀ x y : Config n, (∀ i ∈ I ∪ S, x i = y i) → F x = F y) :
    |∑ x, R.obsProb x * F x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x)| ≤
      2 ^ (I.card + 1) * R.nu u I S := by
  have h := sum_mul_condE R (I ∪ S) F (fun y ↦ spin (y u)) hF
  have heq : ∑ x, R.obsProb x * F x * (spin (x u) - condE R S (fun y ↦ spin (y u)) x) =
      ∑ x, R.obsProb x * F x * (condE R (I ∪ S) (fun y ↦ spin (y u)) x -
        condE R S (fun y ↦ spin (y u)) x) := by
    simp only [mul_sub, sum_sub_distrib, h]
  rw [heq, ← sum_abs_sub_condE_eq_nu R u I S hIS]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
  rw [abs_mul, abs_mul, abs_of_pos (R.obsProb_pos x)]
  simpa using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hF1 x) (R.obsProb_pos x).le) (abs_nonneg _)

end BB20.LowerBound
