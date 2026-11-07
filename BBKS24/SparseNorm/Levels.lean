module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Levels

The deterministic part of [HR17, Lemma 3.6]. Let `f` be a function with `|f| ≤ 1`, and
`gs i`, for the levels `i < t`, approximations of `f` with `|gs i - f| ≤ lvl i / 10` at a point
`x` (`x` is *good*), where `lvl i = 2^(-i/2)`. The point `x` is *at level `i`* if `i` is the first
level with `|gs i x| ≥ lvl i` (`BBKS24.SparseNorm.AtLevel`); the `i`-th piece is `gs i x ^ 2` there,
capped at `4 · 2^(-i)`, and `0` elsewhere (`BBKS24.SparseNorm.piece`). At a good point the sum of
the pieces (`BBKS24.SparseNorm.total`) is `f x ^ 2` up to a factor `(1 ± 1/10)²` and an additive
`2.42 · 2^(-t)` (`BBKS24.SparseNorm.Good.sq_le`, `BBKS24.SparseNorm.Good.le_sq`). The point of the
pieces: the `i`-th is bounded by `4 · 2^(-i)` everywhere and depends only on `gs 0, …, gs i`, so
that Chernoff's bound for it is strong where its net is large.
-/

@[expose] public section

open Finset

namespace BBKS24.SparseNorm

variable {X : Type*}

/-! ### The scales -/

/-- The scale `2^(-i/2)` of level `i`. -/
noncomputable def lvl (i : ℕ) : ℝ := (√2)⁻¹ ^ i

theorem lvl_pos (i : ℕ) : 0 < lvl i := by
  unfold lvl
  positivity

@[simp] theorem lvl_zero : lvl 0 = 1 := by simp [lvl]

theorem lvl_sq (i : ℕ) : lvl i ^ 2 = (1 / 2) ^ i := by
  rw [lvl, ← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num), one_div]

theorem lvl_eq_sqrt_two_mul (i : ℕ) : lvl i = √2 * lvl (i + 1) := by
  rw [lvl, lvl, pow_succ, ← mul_assoc, mul_comm (√2), mul_assoc,
    mul_inv_cancel₀ (by positivity), mul_one]

theorem sqrt_two_le : √2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-! ### Levels and pieces -/

/-- `x` is at level `i` for the approximations `gs`: `i` is the first level with
`|gs i x| ≥ lvl i`. -/
def AtLevel (gs : ℕ → X → ℝ) (i : ℕ) (x : X) : Prop :=
  lvl i ≤ |gs i x| ∧ ∀ j < i, |gs j x| < lvl j

open Classical in
/-- The `i`-th piece: `gs i x ^ 2`, capped at `4 · 2^(-i)`, where `x` is at level `i`. -/
noncomputable def piece (gs : ℕ → X → ℝ) (i : ℕ) (x : X) : ℝ :=
  if AtLevel gs i x then min (gs i x ^ 2) (4 * (1 / 2) ^ i) else 0

/-- The sum of the pieces of the levels `i < t`. -/
noncomputable def total (gs : ℕ → X → ℝ) (t : ℕ) (x : X) : ℝ := ∑ i ∈ range t, piece gs i x

/-- The approximations `gs i`, `i < t`, are `lvl i / 10`-close to `f` at `x`. -/
def Good (gs : ℕ → X → ℝ) (f : X → ℝ) (t : ℕ) (x : X) : Prop :=
  ∀ i < t, |gs i x - f x| ≤ lvl i / 10

variable {gs : ℕ → X → ℝ} {f : X → ℝ} {t : ℕ} {x : X}

theorem piece_nonneg (gs : ℕ → X → ℝ) (i : ℕ) (x : X) : 0 ≤ piece gs i x := by
  unfold piece
  split_ifs
  · exact le_min (sq_nonneg _) (by positivity)
  · exact le_rfl

theorem piece_le (gs : ℕ → X → ℝ) (i : ℕ) (x : X) : piece gs i x ≤ 4 * (1 / 2) ^ i := by
  unfold piece
  split_ifs
  · exact min_le_right _ _
  · positivity

theorem atLevel_unique {i j : ℕ} (hi : AtLevel gs i x) (hj : AtLevel gs j x) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact absurd hi.1 (not_le.2 (hj.2 i h))
  · exact absurd hj.1 (not_le.2 (hi.2 j h))

open Classical in
/-- A piece depends only on the approximations of the levels up to its own. -/
theorem piece_congr {gs' : ℕ → X → ℝ} {i : ℕ} (h : ∀ j ≤ i, gs j = gs' j) :
    piece gs i = piece gs' i := by
  ext x
  have hA : AtLevel gs i x ↔ AtLevel gs' i x := by
    unfold AtLevel
    rw [h i le_rfl]
    exact and_congr_right fun _ ↦ forall₂_congr fun j hj ↦ by rw [h j hj.le]
  unfold piece
  rw [if_congr hA rfl rfl, h i le_rfl]

theorem total_nonneg (gs : ℕ → X → ℝ) (t : ℕ) (x : X) : 0 ≤ total gs t x :=
  sum_nonneg fun i _ ↦ piece_nonneg gs i x

theorem total_eq_of_atLevel {i : ℕ} (hi : AtLevel gs i x) (hit : i < t) :
    total gs t x = piece gs i x := by
  unfold total
  refine sum_eq_single_of_mem i (mem_range.2 hit) fun j _ hji ↦ ?_
  unfold piece
  rw [ite_eq_right fun hj ↦ hji (atLevel_unique hj hi)]

theorem total_eq_zero (h : ∀ i < t, ¬ AtLevel gs i x) : total gs t x = 0 := by
  unfold total
  refine sum_eq_zero fun i hi ↦ ?_
  unfold piece
  rw [ite_eq_right (h i (mem_range.1 hi))]

theorem total_le (gs : ℕ → X → ℝ) (t : ℕ) (x : X) : total gs t x ≤ 4 := by
  by_cases h : ∃ i < t, AtLevel gs i x
  · obtain ⟨i, hit, hi⟩ := h
    rw [total_eq_of_atLevel hi hit]
    refine (piece_le gs i x).trans ?_
    have : ((1 : ℝ) / 2) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith
  · simp only [not_exists, not_and] at h
    rw [total_eq_zero h]
    norm_num

/-- Without a level, every approximation is below its scale. -/
theorem lt_lvl_of_forall_not_atLevel (h : ∀ i < t, ¬ AtLevel gs i x) :
    ∀ i < t, |gs i x| < lvl i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hit
    by_contra hle
    exact h i hit ⟨not_lt.1 hle, fun j hj ↦ ih j hj (hj.trans hit)⟩

/-! ### Good points -/

theorem abs_le_abs_add {a b e : ℝ} (h : |a - b| ≤ e) : |b| ≤ |a| + e := by
  have := abs_sub_abs_le_abs_sub b a
  rw [abs_sub_comm] at this
  linarith

theorem abs_le_abs_add' {a b e : ℝ} (h : |a - b| ≤ e) : |a| ≤ |b| + e := by
  have := abs_sub_abs_le_abs_sub a b
  linarith

/-- At a good point at level `i`, the approximation is at most `2 lvl i`, so its piece is
`gs i x ^ 2`. -/
theorem Good.abs_le_two_mul (hg : Good gs f t x) (hf : |f x| ≤ 1) {i : ℕ} (hi : AtLevel gs i x)
    (hit : i < t) : |gs i x| ≤ 2 * lvl i := by
  have hgi := abs_le_abs_add' (hg i hit)
  cases i with
  | zero =>
    simp only [lvl_zero] at hgi ⊢
    linarith
  | succ k =>
    have hk := hi.2 k (Nat.lt_succ_self k)
    have hfk := abs_le_abs_add (hg k (by omega))
    rw [lvl_eq_sqrt_two_mul k] at hk hfk
    have h2 := sqrt_two_le
    have hl := lvl_pos (k + 1)
    nlinarith

theorem Good.piece_eq (hg : Good gs f t x) (hf : |f x| ≤ 1) {i : ℕ} (hi : AtLevel gs i x)
    (hit : i < t) : piece gs i x = gs i x ^ 2 := by
  have h := hg.abs_le_two_mul hf hi hit
  unfold piece
  rw [ite_eq_left hi, min_eq_left]
  rw [← sq_abs, ← lvl_sq]
  nlinarith [abs_nonneg (gs i x), lvl_pos i]

/-- At a good point, `f x ^ 2 ≤ (11/10)² · total + 2 (11/10)² 2^(-t)`. -/
theorem Good.sq_le (hg : Good gs f t x) (hf : |f x| ≤ 1) (ht : 1 ≤ t) :
    f x ^ 2 ≤ 121 / 100 * total gs t x + 242 / 100 * (1 / 2) ^ t := by
  have hpow : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
  by_cases h : ∃ i < t, AtLevel gs i x
  · obtain ⟨i, hit, hi⟩ := h
    rw [total_eq_of_atLevel hi hit, hg.piece_eq hf hi hit]
    have hfi := abs_le_abs_add (hg i hit)
    have hli := hi.1
    have : |f x| ≤ 11 / 10 * |gs i x| := by linarith
    have := pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sq_abs, mul_pow, sq_abs] at this
    linarith
  · simp only [not_exists, not_and] at h
    rw [total_eq_zero h]
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    have hk := lt_lvl_of_forall_not_atLevel h k (Nat.lt_succ_self k)
    have hfk := abs_le_abs_add (hg k (Nat.lt_succ_self k))
    have : |f x| ≤ 11 / 10 * lvl k := by linarith
    have := pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sq_abs, mul_pow, lvl_sq] at this
    rw [pow_succ (1 / 2 : ℝ) k]
    norm_num at this ⊢
    linarith

/-- At a good point, `(9/10)² · total ≤ f x ^ 2`. -/
theorem Good.le_sq (hg : Good gs f t x) (hf : |f x| ≤ 1) :
    81 / 100 * total gs t x ≤ f x ^ 2 := by
  by_cases h : ∃ i < t, AtLevel gs i x
  · obtain ⟨i, hit, hi⟩ := h
    rw [total_eq_of_atLevel hi hit, hg.piece_eq hf hi hit]
    have hgi := abs_le_abs_add' (hg i hit)
    have hli := hi.1
    have : 9 / 10 * |gs i x| ≤ |f x| := by linarith
    have := pow_le_pow_left₀ (by positivity) this 2
    rw [mul_pow, sq_abs, sq_abs] at this
    linarith
  · simp only [not_exists, not_and] at h
    rw [total_eq_zero h, mul_zero]
    exact sq_nonneg _

open Classical in
/-- `f x ^ 2 ≤ (11/10)² · total + 2 (11/10)² 2^(-t)`, plus `1` at a bad point. -/
theorem sq_le_total (hf : |f x| ≤ 1) (ht : 1 ≤ t) :
    f x ^ 2 ≤ 121 / 100 * total gs t x + 242 / 100 * (1 / 2) ^ t +
      if Good gs f t x then 0 else 1 := by
  split_ifs with hg
  · rw [add_zero]
    exact hg.sq_le hf ht
  · have h1 : f x ^ 2 ≤ 1 := by
      rw [← sq_abs]
      exact pow_le_one₀ (abs_nonneg _) hf
    have := total_nonneg gs t x
    have : (0 : ℝ) ≤ (1 / 2) ^ t := by positivity
    linarith

open Classical in
/-- `total ≤ (10/9)² f x ^ 2`, plus `4` at a bad point. -/
theorem total_le_sq (hf : |f x| ≤ 1) :
    total gs t x ≤ 100 / 81 * f x ^ 2 + if Good gs f t x then 0 else 4 := by
  split_ifs with hg
  · have := hg.le_sq hf
    linarith
  · have := total_le gs t x
    have := sq_nonneg (f x)
    linarith

end BBKS24.SparseNorm
