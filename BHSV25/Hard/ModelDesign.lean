module

public import BHSV25.Hard.ModelUnits
public import BHSV25.Hard.LowRankDesign
public import BHSV25.Alg.ModelFacts

/-!
# The design for Theorem 1.9 (2)

The reduction of [BHSV25, Theorem 8.2] as a design (`BHSV25.Hard.ModelRed.Data.design`), for a
model `M` with stationary distribution `π` and integer parameters `D` (precision of the weights),
`2H` (color units) and `m` (absorber blocks), collected in `BHSV25.Hard.ModelRed.Data`.

* **Weights.** `w_ij = ⌊D π_i M_ij⌋` is symmetric (detailed balance), with row sums `s_i ≈ D π_i`.
  The groups of the design are the colors `i`; the types of group `i` are the tuples
  `(i, j, t, u, α, β)` with `t < w_ij`, a color unit `u < 2H`, `α < m` and `β ≤ m`, so group `i`
  has `s_i · 2H m (m + 1)` types. With `P = ∏ s_c`, `p_i = P / s_i` and the densities
  `q_ij = p_i p_j w_ij` (in units of `2^(-r)`), every type has degree `P² · 2H m (m + 1)` in
  types: the template is exactly regular.
* **Colors.** The units of group `i` are colored by `BHSV25.Hard.Units.col` for the distribution
  `ρ⁽ⁱ⁾_b = π_b / π(S)` on the class `S` of colors whose rows equal the row of `i`; the color unit
  `u` is paired with `u + H` (mod `2H`), which has another color unless the color has more than
  half of the class (`BHSV25.Hard.Units.card_col_sh_le`).
* **Copies and absorbers.** A type `(x, u, α, β)` with `β < m` whose unit `u` has another color
  than `u + H` is a **copy** of the input graph (`W⁰ = 1` on the diagonal). Its absorber is
  `(x*, u, α, m)`, where `(i, j, t)* = (j, i, t)`: a type of group `j`, adjacent to group `i`
  since `w_ij ≥ 1`, joined to the copy by the complement of the input graph (`W⁰ = -1`). The
  absorbers `(x*, u, α', m)`, `α' < m`, are joined to each other by copies of the input graph
  (`W⁰ = 1`), so all rows of `W⁰` sum to `0`. The other types are independent.
-/

@[expose] public section

namespace BHSV25.Hard.ModelRed

open Finset LowRank

/-- The data of the reduction for a model `M` with stationary distribution `π`: the precision `D`
of the weights, `2H` color units and absorber blocks of size `m`. -/
structure Data where
  /-- The number of colors. -/
  k : ℕ
  /-- The model. -/
  M : Matrix (Fin k) (Fin k) ℝ
  /-- Its stationary distribution. -/
  π : Fin k → ℝ
  hM : IsModel M
  hπ : IsStationary M π
  /-- The precision of the weights. -/
  D : ℕ
  /-- Half the number of color units. -/
  H : ℕ
  /-- The size of the absorber blocks. -/
  m : ℕ
  hD : ∀ i, 2 * (k : ℝ) + 1 ≤ D * π i
  hH : 0 < H
  hm : 0 < m

namespace Data

variable (X : Data)

/-! ### Basic facts about the model -/

theorem π_pos (i : Fin X.k) : 0 < X.π i := X.hπ.1 i

theorem π_le_one (i : Fin X.k) : X.π i ≤ 1 := by
  rw [← X.hπ.2.1]
  exact single_le_sum (fun j _ ↦ (X.π_pos j).le) (mem_univ i)

theorem M_nonneg (i j : Fin X.k) : 0 ≤ X.M i j := X.hM.nonneg i j

theorem M_le_one (i j : Fin X.k) : X.M i j ≤ 1 := by
  rw [← X.hM.rowSum i]
  exact single_le_sum (fun j _ ↦ X.M_nonneg i j) (mem_univ j)

/-! ### The weights -/

/-- The weights `⌊D π_i M_ij⌋`. -/
noncomputable def w (i j : Fin X.k) : ℕ := ⌊(X.D : ℝ) * X.π i * X.M i j⌋₊

theorem w_symm (i j : Fin X.k) : X.w i j = X.w j i := by
  unfold w
  rw [mul_assoc, X.hπ.2.2 i j, ← mul_assoc]

theorem nonneg_DπM (i j : Fin X.k) : 0 ≤ (X.D : ℝ) * X.π i * X.M i j :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (X.π_pos i).le) (X.M_nonneg i j)

theorem w_le (i j : Fin X.k) : (X.w i j : ℝ) ≤ X.D * X.π i * X.M i j :=
  Nat.floor_le (X.nonneg_DπM i j)

theorem lt_w (i j : Fin X.k) : (X.D : ℝ) * X.π i * X.M i j < X.w i j + 1 :=
  Nat.lt_floor_add_one _

theorem w_diag (i : Fin X.k) : X.w i i = 0 := by
  unfold w
  rw [X.hM.diag i, mul_zero, Nat.floor_zero]

theorem M_pos_of_w {i j : Fin X.k} (h : 0 < X.w i j) : 0 < X.M i j := by
  by_contra hc
  have h0 : X.M i j = 0 := le_antisymm (not_lt.1 hc) (X.M_nonneg i j)
  unfold w at h
  rw [h0, mul_zero, Nat.floor_zero] at h
  exact lt_irrefl _ h

theorem w_le_D (i j : Fin X.k) : X.w i j ≤ X.D := by
  have h1 := X.w_le i j
  have h2 : (X.D : ℝ) * X.π i * X.M i j ≤ X.D := by
    have := mul_le_mul (X.π_le_one i) (X.M_le_one i j) (X.M_nonneg i j) zero_le_one
    have hD : (0 : ℝ) ≤ X.D := Nat.cast_nonneg _
    nlinarith
  exact_mod_cast h1.trans h2

/-- The row sums of the weights. -/
noncomputable def s (i : Fin X.k) : ℕ := ∑ j, X.w i j

theorem s_le (i : Fin X.k) : (X.s i : ℝ) ≤ X.D * X.π i := by
  unfold s
  push_cast
  calc ∑ j, (X.w i j : ℝ) ≤ ∑ j, (X.D : ℝ) * X.π i * X.M i j := sum_le_sum fun j _ ↦ X.w_le i j
    _ = X.D * X.π i := by rw [← mul_sum, X.hM.rowSum i, mul_one]

theorem le_s (i : Fin X.k) : (X.D : ℝ) * X.π i - X.k ≤ X.s i := by
  unfold s
  push_cast
  have h : ∑ j, ((X.D : ℝ) * X.π i * X.M i j - 1) ≤ ∑ j, (X.w i j : ℝ) :=
    sum_le_sum fun j _ ↦ by linarith [X.lt_w i j]
  rw [sum_sub_distrib, ← mul_sum, X.hM.rowSum i, mul_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h

theorem half_le_s (i : Fin X.k) : (X.D : ℝ) * X.π i / 2 ≤ X.s i := by
  have := X.le_s i
  have := X.hD i
  linarith

theorem one_le_s (i : Fin X.k) : 1 ≤ X.s i := by
  have h1 := X.le_s i
  have h2 := X.hD i
  have : (1 : ℝ) ≤ X.s i := by linarith
  exact_mod_cast this

/-- The product of the row sums. -/
noncomputable def P : ℕ := ∏ c, X.s c

/-- The product of the other row sums. -/
noncomputable def p (i : Fin X.k) : ℕ := ∏ c ∈ univ.erase i, X.s c

theorem p_mul_s (i : Fin X.k) : X.p i * X.s i = X.P :=
  prod_erase_mul _ _ (mem_univ i)

theorem one_le_p (i : Fin X.k) : 1 ≤ X.p i :=
  Nat.one_le_iff_ne_zero.2
    (prod_ne_zero_iff.2 fun c _ ↦ Nat.one_le_iff_ne_zero.1 (X.one_le_s c))

theorem p_le_P (i : Fin X.k) : X.p i ≤ X.P := by
  rw [← X.p_mul_s i]
  exact Nat.le_mul_of_pos_right _ (X.one_le_s i)

/-- The densities between groups, in units of `2^(-r)`. -/
noncomputable def q (i j : Fin X.k) : ℕ := X.p i * X.p j * X.w i j

/-- The dyadic precision. -/
noncomputable def r : ℕ := X.P * X.P * X.D

/-- The number of slots `(u, α, β)` of a host unit. -/
def cnt : ℕ := 2 * X.H * (X.m * (X.m + 1))

/-- The degree in types. -/
noncomputable def d₀ : ℕ := X.P * X.P * X.cnt

theorem q_symm (i j : Fin X.k) : X.q i j = X.q j i := by
  unfold q; rw [X.w_symm, mul_comm (X.p i)]

theorem q_le (i j : Fin X.k) : X.q i j ≤ 2 ^ X.r := by
  unfold q r
  refine le_trans ?_ (Nat.lt_two_pow_self).le
  exact Nat.mul_le_mul (Nat.mul_le_mul (X.p_le_P i) (X.p_le_P j)) (X.w_le_D i j)

theorem q_diag (i : Fin X.k) : X.q i i = 0 := by
  unfold q; rw [X.w_diag, mul_zero]

/-! ### The classes -/

/-- The weight of the class of `i`. -/
noncomputable def Pi (i : Fin X.k) : ℝ := ∑ b ∈ Alg.rowGroup X.M i, X.π b

theorem Pi_pos (i : Fin X.k) : 0 < X.Pi i :=
  sum_pos (fun b _ ↦ X.π_pos b) ⟨i, Alg.self_mem_rowGroup i⟩

theorem Pi_congr {i j : Fin X.k} (h : X.M i = X.M j) : X.Pi i = X.Pi j := by
  unfold Pi; rw [Alg.rowGroup_eq_of_row_eq h]

/-- The distribution of the class of `i`. -/
noncomputable def ρ (i b : Fin X.k) : ℝ :=
  if b ∈ Alg.rowGroup X.M i then X.π b / X.Pi i else 0

theorem ρ_nonneg (i b : Fin X.k) : 0 ≤ X.ρ i b := by
  unfold ρ
  split_ifs
  · exact div_nonneg (X.π_pos b).le (X.Pi_pos i).le
  · exact le_rfl

theorem ρ_sum (i : Fin X.k) : ∑ b, X.ρ i b = 1 := by
  unfold ρ
  rw [← sum_filter, filter_mem_eq_inter, univ_inter, ← sum_div]
  exact div_self (X.Pi_pos i).ne'

theorem mem_of_ρ_pos {i b : Fin X.k} (h : 0 < X.ρ i b) : X.M b = X.M i := by
  unfold ρ at h
  split_ifs at h with hb
  · exact Alg.mem_rowGroup.1 hb
  · exact absurd h (lt_irrefl _)

/-- The coloring of the color units of group `i`. -/
noncomputable def colC (i : Fin X.k) : Fin (2 * X.H) → Fin X.k :=
  Units.col (X.ρ i) i (2 * X.H)

theorem row_colC (i : Fin X.k) (u : Fin (2 * X.H)) : X.M (X.colC i u) = X.M i :=
  X.mem_of_ρ_pos (Units.col_pos (X.ρ_sum i) i u)

/-! ### The types -/

/-- The host units: `(i, j, t)` with `t < w_ij`. -/
abbrev HU := {x : Fin X.k × Fin X.k × Fin X.D // (x.2.2 : ℕ) < X.w x.1 x.2.1}

/-- The partner `(j, i, t)` of a host unit `(i, j, t)`. -/
def swap (x : X.HU) : X.HU := ⟨(x.1.2.1, x.1.1, x.1.2.2), by rw [X.w_symm]; exact x.2⟩

theorem swap_swap (x : X.HU) : X.swap (X.swap x) = x := rfl

theorem fst_ne_snd (x : X.HU) : x.1.1 ≠ x.1.2.1 := by
  intro h
  have := x.2
  rw [h, X.w_diag] at this
  exact Nat.not_lt_zero _ this

theorem swap_ne (x : X.HU) : X.swap x ≠ x := by
  intro h
  exact X.fst_ne_snd x (congrArg (fun y : X.HU ↦ y.1.1) h).symm

/-- The types: a host unit, a color unit, `α < m` and `β ≤ m`. -/
abbrev Ty := X.HU × Fin (2 * X.H) × Fin X.m × Fin (X.m + 1)

/-- The color unit `u` of the host unit `x` has another color than `u + H`. -/
def cp (x : X.HU) (u : Fin (2 * X.H)) : Prop := X.colC x.1.1 u ≠ X.colC x.1.1 (Units.sh X.H u)

noncomputable instance (x : X.HU) (u : Fin (2 * X.H)) : Decidable (X.cp x u) := by
  unfold cp; infer_instance

/-- A copy of the input graph. -/
def copy (τ : X.Ty) : Prop := τ.2.2.2 ≠ Fin.last X.m ∧ X.cp τ.1 τ.2.1

/-- An absorber. -/
def absb (τ : X.Ty) : Prop := τ.2.2.2 = Fin.last X.m ∧ X.cp (X.swap τ.1) τ.2.1

noncomputable instance : DecidablePred X.copy := fun τ ↦ by unfold copy; infer_instance

noncomputable instance : DecidablePred X.absb := fun τ ↦ by unfold absb; infer_instance

theorem not_absb_of_copy {τ : X.Ty} (h : X.copy τ) : ¬ X.absb τ := fun h' ↦ h.1 h'.1

/-- The absorber of a copy. -/
def host (τ : X.Ty) : X.Ty := (X.swap τ.1, τ.2.1, τ.2.2.1, Fin.last X.m)

/-- The correction between types: copies on the diagonal, the complement between a copy and its
absorber, and copies between the absorbers of a block. -/
noncomputable def W0 (τ τ' : X.Ty) : ℤ :=
  zi (X.copy τ ∧ τ' = τ) + zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) -
  zi (X.copy τ ∧ τ' = X.host τ) -
  zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
    τ'.2.2.2 ≠ Fin.last X.m)

/-! ### Symmetry -/

theorem t3_iff (τ τ' : X.Ty) : (X.copy τ ∧ τ' = X.host τ) ↔
    (X.absb τ' ∧ τ.1 = X.swap τ'.1 ∧ τ.2.1 = τ'.2.1 ∧ τ.2.2.1 = τ'.2.2.1 ∧
      τ.2.2.2 ≠ Fin.last X.m) := by
  obtain ⟨x, u, α, β⟩ := τ
  obtain ⟨x', u', α', β'⟩ := τ'
  simp only [host, copy, absb, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hβ, hcp⟩, rfl, rfl, rfl, rfl⟩
    exact ⟨⟨rfl, hcp⟩, rfl, rfl, rfl, hβ⟩
  · rintro ⟨⟨rfl, hcp⟩, rfl, rfl, rfl, hβ⟩
    exact ⟨⟨hβ, hcp⟩, rfl, rfl, rfl, rfl⟩

theorem W0_symm (τ τ' : X.Ty) : X.W0 τ τ' = X.W0 τ' τ := by
  unfold W0
  have h1 : zi (X.copy τ ∧ τ' = τ) = zi (X.copy τ' ∧ τ = τ') := by
    refine zi_congr ⟨fun ⟨h, e⟩ ↦ ⟨e ▸ h, e.symm⟩, fun ⟨h, e⟩ ↦ ⟨e ▸ h, e.symm⟩⟩
  have h2 : zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) =
      zi (X.absb τ' ∧ X.absb τ ∧ τ.1 = τ'.1 ∧ τ.2.1 = τ'.2.1) :=
    zi_congr ⟨fun ⟨a, b, c, d⟩ ↦ ⟨b, a, c.symm, d.symm⟩, fun ⟨a, b, c, d⟩ ↦ ⟨b, a, c.symm, d.symm⟩⟩
  have h3 := zi_congr (X.t3_iff τ τ')
  have h4 := zi_congr (X.t3_iff τ' τ)
  rw [h1, h2, h3, h4]
  ring

/-! ### Row sums -/

theorem zi_of {P : Prop} [Decidable P] (h : P) : zi P = 1 := by unfold zi; rw [ite_eq_left h]

theorem zi_of_not {P : Prop} [Decidable P] (h : ¬ P) : zi P = 0 := by
  unfold zi; rw [ite_eq_right h]

theorem sum_ty4 (f : X.HU → ℤ) (g : Fin (2 * X.H) → ℤ) (h : Fin X.m → ℤ)
    (l : Fin (X.m + 1) → ℤ) :
    ∑ τ : X.Ty, f τ.1 * g τ.2.1 * h τ.2.2.1 * l τ.2.2.2 =
      (∑ x, f x) * (∑ u, g u) * (∑ α, h α) * ∑ β, l β := by
  simp only [Fintype.sum_prod_type, ← mul_sum, ← sum_mul]

theorem sum_t1 (τ : X.Ty) : ∑ τ' : X.Ty, zi (X.copy τ ∧ τ' = τ) = zi (X.copy τ) := by
  simp_rw [zi_and, ← mul_sum, sum_zi_eq, mul_one]

theorem sum_t3 (τ : X.Ty) : ∑ τ' : X.Ty, zi (X.copy τ ∧ τ' = X.host τ) = zi (X.copy τ) := by
  simp_rw [zi_and, ← mul_sum, sum_zi_eq, mul_one]

theorem sum_zi_ne_last : ∑ β : Fin (X.m + 1), zi (β ≠ Fin.last X.m) = X.m := by
  have : ∀ β : Fin (X.m + 1), zi (β ≠ Fin.last X.m) = 1 - zi (β = Fin.last X.m) := by
    intro β; unfold zi; by_cases h : β = Fin.last X.m <;> simp [h]
  simp_rw [this, sum_sub_distrib, sum_zi_eq]
  simp

theorem sum_t2 (τ : X.Ty) :
    ∑ τ' : X.Ty, zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) =
      zi (X.absb τ) * X.m := by
  by_cases hτ : X.absb τ
  · have hiff : ∀ τ' : X.Ty, (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) ↔
        (τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.2 = Fin.last X.m) := by
      intro τ'
      constructor
      · rintro ⟨_, ⟨hβ, _⟩, h1, h2⟩
        exact ⟨h1, h2, hβ⟩
      · rintro ⟨h1, h2, hβ⟩
        refine ⟨hτ, ⟨hβ, ?_⟩, h1, h2⟩
        rw [h1, h2]
        exact hτ.2
    have hpt : ∀ τ' : X.Ty, zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) =
        zi (τ'.1 = τ.1) * zi (τ'.2.1 = τ.2.1) * 1 * zi (τ'.2.2.2 = Fin.last X.m) := by
      intro τ'
      rw [zi_congr (hiff τ')]
      simp only [zi_and, mul_one]
      ring
    simp_rw [hpt]
    have h4 := X.sum_ty4 (fun x ↦ zi (x = τ.1)) (fun u ↦ zi (u = τ.2.1)) (fun _ ↦ 1)
      (fun β ↦ zi (β = Fin.last X.m))
    rw [h4, sum_zi_eq, sum_zi_eq, sum_zi_eq, zi_of hτ]
    simp
  · simp [zi, hτ]

theorem sum_t4 (τ : X.Ty) :
    ∑ τ' : X.Ty, zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
      τ'.2.2.2 ≠ Fin.last X.m) = zi (X.absb τ) * X.m := by
  have hpt : ∀ τ' : X.Ty, zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧
      τ'.2.2.1 = τ.2.2.1 ∧ τ'.2.2.2 ≠ Fin.last X.m) = zi (X.absb τ) *
        (zi (τ'.1 = X.swap τ.1) * zi (τ'.2.1 = τ.2.1) * zi (τ'.2.2.1 = τ.2.2.1) *
          zi (τ'.2.2.2 ≠ Fin.last X.m)) := by
    intro τ'; simp only [zi_and]; ring
  simp_rw [hpt]
  have h4 := X.sum_ty4 (fun x ↦ zi (x = X.swap τ.1)) (fun u ↦ zi (u = τ.2.1))
    (fun α ↦ zi (α = τ.2.2.1)) (fun β ↦ zi (β ≠ Fin.last X.m))
  rw [← mul_sum, h4, sum_zi_eq, sum_zi_eq, sum_zi_eq, sum_zi_ne_last]
  ring

theorem W0_sum (τ : X.Ty) : ∑ τ', X.W0 τ τ' = 0 := by
  unfold W0
  simp only [sum_add_distrib, sum_sub_distrib]
  rw [sum_t1, sum_t2, sum_t3, sum_t4]
  ring

/-! ### Entries -/

theorem W0_cases (τ τ' : X.Ty) : X.W0 τ τ' = -1 ∨ X.W0 τ τ' = 0 ∨ X.W0 τ τ' = 1 := by
  by_cases hc : X.copy τ
  · have ha := X.not_absb_of_copy hc
    simp only [W0, zi, hc, ha, true_and, false_and, ↓reduceIte, add_zero, sub_zero]
    by_cases he : τ' = τ
    · have hne : ¬ τ' = X.host τ := by
        intro h
        apply hc.1
        rw [he] at h
        exact congrArg (fun y : X.Ty ↦ y.2.2.2) h
      rw [ite_eq_left he, ite_eq_right hne]
      norm_num
    · rw [ite_eq_right he]
      split_ifs <;> norm_num
  · simp only [W0, zi, hc, false_and, ↓reduceIte, zero_add]
    by_cases hx : τ'.1 = τ.1
    · have hne : ¬ (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
          τ'.2.2.2 ≠ Fin.last X.m) := fun h ↦ X.swap_ne τ.1 (h.2.1.symm.trans hx)
      rw [ite_eq_right hne]
      split_ifs <;> norm_num
    · have hne : ¬ (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) :=
        fun h ↦ hx h.2.2.1
      rw [ite_eq_right hne]
      split_ifs <;> norm_num

theorem fst_eq_of_W0_neg {τ τ' : X.Ty} (h : X.W0 τ τ' = -1) : τ'.1 = X.swap τ.1 := by
  by_contra hne
  unfold W0 at h
  have e3 : zi (X.copy τ ∧ τ' = X.host τ) = 0 := zi_of_not (fun h' ↦ hne (by rw [h'.2]; rfl))
  have e4 : zi (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
      τ'.2.2.2 ≠ Fin.last X.m) = 0 := zi_of_not (fun h' ↦ hne h'.2.1)
  rw [e3, e4] at h
  have := zi_nonneg (X.copy τ ∧ τ' = τ)
  have := zi_nonneg (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1)
  linarith

theorem gr_eq_of_W0_pos {τ τ' : X.Ty} (h : X.W0 τ τ' = 1) : τ.1.1.1 = τ'.1.1.1 := by
  by_contra hne
  unfold W0 at h
  have e1 : zi (X.copy τ ∧ τ' = τ) = 0 := zi_of_not (fun h' ↦ hne (by rw [h'.2]))
  have e2 : zi (X.absb τ ∧ X.absb τ' ∧ τ'.1 = τ.1 ∧ τ'.2.1 = τ.2.1) = 0 :=
    zi_of_not (fun h' ↦ hne (by rw [h'.2.2.1]))
  rw [e1, e2] at h
  have := zi_nonneg (X.copy τ ∧ τ' = X.host τ)
  have := zi_nonneg (X.absb τ ∧ τ'.1 = X.swap τ.1 ∧ τ'.2.1 = τ.2.1 ∧ τ'.2.2.1 = τ.2.2.1 ∧
    τ'.2.2.2 ≠ Fin.last X.m)
  linarith

theorem W0_neg (τ τ' : X.Ty) (h : X.W0 τ τ' = -1) :
    τ.1.1.1 ≠ τ'.1.1.1 ∧ 1 ≤ X.q τ.1.1.1 τ'.1.1.1 := by
  have hx := X.fst_eq_of_W0_neg h
  have hj : τ'.1.1.1 = τ.1.1.2.1 := by rw [hx]; rfl
  rw [hj]
  refine ⟨X.fst_ne_snd τ.1, ?_⟩
  unfold q
  have hw : 1 ≤ X.w τ.1.1.1 τ.1.1.2.1 := lt_of_le_of_lt (Nat.zero_le _) τ.1.2
  exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero
    (Nat.one_le_iff_ne_zero.1 (X.one_le_p _)) (Nat.one_le_iff_ne_zero.1 (X.one_le_p _)))
    (by omega))

/-! ### Regularity -/

theorem sum_HU {R : Type*} [AddCommMonoid R] (G : Fin X.k → Fin X.k → R) :
    ∑ x : X.HU, G x.1.1 x.1.2.1 = ∑ i, ∑ j, X.w i j • G i j := by
  rw [← sum_subtype (univ.filter fun x : Fin X.k × Fin X.k × Fin X.D ↦
    (x.2.2 : ℕ) < X.w x.1 x.2.1) (by simp) (fun x ↦ G x.1 x.2.1), sum_filter]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [← sum_filter, sum_const, Fin.card_filter_val_lt, min_eq_right (X.w_le_D i j)]

theorem sum_ty_fst {R : Type*} [AddCommMonoid R] (F : X.HU → R) :
    ∑ τ : X.Ty, F τ.1 = X.cnt • ∑ x, F x := by
  rw [Fintype.sum_prod_type, smul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  change ∑ _y : Fin (2 * X.H) × Fin X.m × Fin (X.m + 1), F x = _
  rw [sum_const, card_univ]
  congr 1
  simp [cnt, Fintype.card_prod]

theorem reg (τ : X.Ty) :
    ∑ τ' : X.Ty, (if τ.1.1.1 ≠ τ'.1.1.1 then X.q τ.1.1.1 τ'.1.1.1 else 0) = X.d₀ := by
  have hif : ∀ τ' : X.Ty, (if τ.1.1.1 ≠ τ'.1.1.1 then X.q τ.1.1.1 τ'.1.1.1 else 0) =
      X.q τ.1.1.1 τ'.1.1.1 := by
    intro τ'
    split_ifs with h
    · rfl
    · rw [not_not] at h; rw [← h, X.q_diag]
  simp_rw [hif]
  rw [X.sum_ty_fst (fun x ↦ X.q τ.1.1.1 x.1.1), X.sum_HU (fun i _ ↦ X.q τ.1.1.1 i)]
  simp only [smul_eq_mul]
  have h1 : ∀ i, ∑ j, X.w i j * X.q τ.1.1.1 i = X.s i * X.q τ.1.1.1 i := by
    intro i; rw [← sum_mul]; rfl
  simp_rw [h1]
  have h2 : ∑ i, X.s i * X.q τ.1.1.1 i = X.P * X.P := by
    unfold q
    have : ∀ i, X.s i * (X.p τ.1.1.1 * X.p i * X.w τ.1.1.1 i) =
        X.p τ.1.1.1 * X.P * X.w τ.1.1.1 i := by
      intro i; rw [← X.p_mul_s i]; ring
    simp_rw [this]
    rw [← mul_sum]
    change X.p τ.1.1.1 * X.P * X.s τ.1.1.1 = X.P * X.P
    rw [mul_right_comm, X.p_mul_s]
  rw [h2]
  unfold d₀
  ring

/-! ### The design -/

/-- **The design of Theorem 1.9 (2).** -/
noncomputable abbrev design : Design where
  Ty := X.Ty
  K := X.k
  gr τ := τ.1.1.1
  r := X.r
  q := X.q
  d₀ := X.d₀
  W0 := X.W0
  q_symm := X.q_symm
  q_le := X.q_le
  reg := X.reg
  W0_symm := X.W0_symm
  W0_cases := X.W0_cases
  W0_neg := X.W0_neg
  W0_pos _ _ h := X.gr_eq_of_W0_pos h
  W0_sum := X.W0_sum

end Data

end BHSV25.Hard.ModelRed
