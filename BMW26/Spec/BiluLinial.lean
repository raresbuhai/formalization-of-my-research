module

public import BMW26.Spec.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Int.Log

/-!
# The converse expander mixing lemma, and spectral closeness on the good vertices

* `BMW26.bilu_linial` ([BL06, Lemma 3.3], cited as [BMW26, Lemma 5.5]): a symmetric matrix with
  zero diagonal, rows of `ℓ₁` norm at most `B`, and `|1_Sᵀ M 1_T| ≤ α √(|S||T|)` for all disjoint
  `S, T`, has `|vᵀ M v| ≤ c α (1 + log(B/α)) ‖v‖²`.
* `BMW26.goodNorm_of_disc` ([BMW26, Lemma 5.4]): on the good vertices the degrees are within
  `γ p m` of `p m`, and the discrepancy (`BMW26.Disc`) with a small enough `η` bounds the centred
  adjacency matrix by `γ p m` through `bilu_linial`; together `GoodNorm`.

The proof of `bilu_linial` avoids the rounding step of [BL06]: averaging over the random
partitions `(σ, σᶜ)` of the coordinates (`BMW26.BL.sum_partition`, which uses the zero diagonal)
reduces it to vectors `x, y` with disjoint supports (`BMW26.BL.core`); their entries are grouped
into dyadic levels `2^k ≤ |xᵢ| < 2^(k+1)`, pairs of levels at most `L ≈ log₂(B/α)` apart are
bounded by the discrepancy (a bilinear form bounded on indicators is bounded on boxes,
`BMW26.BL.abs_bilin_le`), and the other pairs by the row sums.

Reference: [BL06] Y. Bilu, N. Linial, *Lifts, discrepancy and nearly optimal spectral gap*,
Combinatorica 26 (2006).
-/

@[expose] public section

namespace BMW26

open Finset

namespace BL

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- The `ℓ₁` norm of `f` on `P` is at most twice the largest `|∑_{i ∈ S} f i|`, `S ⊆ P`. -/
theorem sum_abs_le_two_mul (f : ι → ℝ) (P : Finset ι) {β : ℝ}
    (hf : ∀ S ⊆ P, |∑ i ∈ S, f i| ≤ β) : ∑ i ∈ P, |f i| ≤ 2 * β := by
  have h1 := hf (P.filter fun i ↦ 0 ≤ f i) (filter_subset _ _)
  have h2 := hf (P.filter fun i ↦ ¬ 0 ≤ f i) (filter_subset _ _)
  have e : ∑ i ∈ P, |f i| = ∑ i ∈ P.filter (fun i ↦ 0 ≤ f i), f i
      - ∑ i ∈ P.filter (fun i ↦ ¬ 0 ≤ f i), f i := by
    rw [← sum_filter_add_sum_filter_not P (fun i ↦ 0 ≤ f i), sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    · exact sum_congr rfl fun i hi ↦ abs_of_nonneg (mem_filter.1 hi).2
    · exact sum_congr rfl fun i hi ↦ abs_of_neg (not_le.1 (mem_filter.1 hi).2)
  rw [e]
  have := le_abs_self (∑ i ∈ P.filter (fun i ↦ 0 ≤ f i), f i)
  have := neg_abs_le (∑ i ∈ P.filter (fun i ↦ ¬ 0 ≤ f i), f i)
  linarith

omit [DecidableEq ι] in
/-- A linear form bounded on the indicators of the subsets of `P` is bounded on the box
`[-μ, μ]^P`. -/
theorem abs_sum_mul_le (f x : ι → ℝ) (P : Finset ι) {β μ : ℝ} (hμ : 0 ≤ μ)
    (hf : ∀ S ⊆ P, |∑ i ∈ S, f i| ≤ β) (hx : ∀ i, |x i| ≤ μ) (hP : ∀ i ∉ P, x i = 0) :
    |∑ i, x i * f i| ≤ 2 * μ * β := by
  rw [← sum_subset (subset_univ P) (fun i _ hi ↦ by simp [hP i hi])]
  calc |∑ i ∈ P, x i * f i| ≤ ∑ i ∈ P, |x i * f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, μ * |f i| := by
        refine sum_le_sum fun i _ ↦ ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hx i) (abs_nonneg _)
    _ = μ * ∑ i ∈ P, |f i| := by rw [mul_sum]
    _ ≤ μ * (2 * β) := mul_le_mul_of_nonneg_left (sum_abs_le_two_mul f P hf) hμ
    _ = 2 * μ * β := by ring

omit [DecidableEq ι] in
/-- A bilinear form bounded on the indicators of the subsets of `P` and `Q` is bounded on the
boxes `[-μ, μ]^P × [-ν, ν]^Q`. -/
theorem abs_bilin_le (M : ι → ι → ℝ) (P Q : Finset ι) {γ μ ν : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hM : ∀ S ⊆ P, ∀ T ⊆ Q, |∑ i ∈ S, ∑ j ∈ T, M i j| ≤ γ)
    (x y : ι → ℝ) (hx : ∀ i, |x i| ≤ μ) (hxP : ∀ i ∉ P, x i = 0)
    (hy : ∀ j, |y j| ≤ ν) (hyQ : ∀ j ∉ Q, y j = 0) :
    |∑ i, ∑ j, x i * M i j * y j| ≤ 4 * μ * ν * γ := by
  have hg : ∀ T ⊆ Q, |∑ j ∈ T, ∑ i, x i * M i j| ≤ 2 * μ * γ := by
    intro T hT
    have := abs_sum_mul_le (fun i ↦ ∑ j ∈ T, M i j) x P hμ (fun S hS ↦ hM S hS T hT) hx hxP
    rw [sum_comm]
    simpa [mul_sum] using this
  have := abs_sum_mul_le (fun j ↦ ∑ i, x i * M i j) y Q hν hg hy hyQ
  have e : ∑ i, ∑ j, x i * M i j * y j = ∑ j, y j * ∑ i, x i * M i j := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [e]
  calc _ ≤ 2 * ν * (2 * μ * γ) := this
    _ = 4 * μ * ν * γ := by ring

theorem abs_sum_sum_le {κ κ' : Type*} (s : Finset κ) (t : Finset κ') (g h : κ → κ' → ℝ)
    (hgh : ∀ i ∈ s, ∀ j ∈ t, |g i j| ≤ h i j) :
    |∑ i ∈ s, ∑ j ∈ t, g i j| ≤ ∑ i ∈ s, ∑ j ∈ t, h i j :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi ↦
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj ↦ hgh i hi j hj))

/-- The dyadic level of `t`: `2 ^ lev t ≤ |t| < 2 ^ (lev t + 1)` for `t ≠ 0`. -/
noncomputable def lev (t : ℝ) : ℤ := Int.log 2 |t|

theorem zpow_lev_le {t : ℝ} (ht : t ≠ 0) : (2 : ℝ) ^ lev t ≤ |t| := by
  have := Int.zpow_log_le_self (b := 2) (R := ℝ) one_lt_two (abs_pos.2 ht)
  simpa [lev] using this

theorem lt_zpow_lev (t : ℝ) : |t| < (2 : ℝ) ^ (lev t + 1) := by
  have := Int.lt_zpow_succ_log_self (b := 2) (R := ℝ) one_lt_two |t|
  simpa [lev] using this

/-- A pair of entries at levels more than `L` apart. -/
theorem far_le {s t : ℝ} {L : ℕ} (h : lev t + L < lev s) (c : ℝ) :
    |s * c * t| ≤ |c| * s ^ 2 / 2 ^ L := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [mul_zero, abs_zero]; positivity
  rcases eq_or_ne s 0 with rfl | hs
  · simp only [zero_mul, abs_zero]; positivity
  have h1 : |t| ≤ |s| / 2 ^ L := by
    have h0 := lt_zpow_lev t
    have h2 : (2:ℝ) ^ (lev t + 1) ≤ 2 ^ (lev s - L) := zpow_le_zpow_right₀ one_le_two (by omega)
    have h3 : (2:ℝ) ^ (lev s - (L:ℤ)) = 2 ^ lev s / 2 ^ L := by
      rw [zpow_sub₀ two_ne_zero, zpow_natCast]
    have h4 := zpow_lev_le hs
    rw [h3] at h2
    calc |t| ≤ 2 ^ lev s / 2 ^ L := by linarith
      _ ≤ |s| / 2 ^ L := by gcongr
  rw [abs_mul, abs_mul]
  calc |s| * |c| * |t| ≤ |s| * |c| * (|s| / 2 ^ L) := by gcongr
    _ = |c| * s ^ 2 / 2 ^ L := by rw [← sq_abs s]; ring

omit [DecidableEq ι] in
theorem sum_shift_le (f : ι → ℤ) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i) (K : Finset ℤ) (e : ℤ) :
    ∑ k ∈ K, ∑ i, (if f i = k + e then g i else 0) ≤ ∑ i, g i := by
  rw [sum_comm]
  refine sum_le_sum fun i _ ↦ ?_
  have : ∑ k ∈ K, (if f i = k + e then g i else 0) =
      ∑ k ∈ K, (if f i - e = k then g i else 0) :=
    sum_congr rfl fun k _ ↦ if_congr ⟨fun h ↦ by omega, fun h ↦ by omega⟩ rfl rfl
  rw [this, sum_ite_eq]
  split_ifs
  · exact le_rfl
  · exact hg i

omit [DecidableEq ι] in
/-- The bilinear form between a level of `x` and a level of `y`, by discrepancy. -/
theorem near_block_le (M : ι → ι → ℝ) {α : ℝ} (hα : 0 < α)
    (hdisc : ∀ S T : Finset ι, Disjoint S T →
      |∑ i ∈ S, ∑ j ∈ T, M i j| ≤ α * Real.sqrt (S.card * T.card))
    (x y : ι → ℝ) (hxy : ∀ i, x i = 0 ∨ y i = 0) (k l : ℤ) :
    |∑ i, ∑ j, (if lev (x i) = k then x i else 0) * M i j * (if lev (y j) = l then y j else 0)|
      ≤ 8 * α * (∑ i, (if lev (x i) = k then x i ^ 2 else 0) +
        ∑ j, (if lev (y j) = l then y j ^ 2 else 0)) := by
  set P := univ.filter (fun i ↦ lev (x i) = k ∧ x i ≠ 0) with hP
  set Q := univ.filter (fun j ↦ lev (y j) = l ∧ y j ≠ 0) with hQ
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    simp only [hP, hQ, mem_filter, mem_univ, true_and] at hiP hiQ
    rcases hxy i with h | h
    · exact hiP.2 h
    · exact hiQ.2 h
  have hM : ∀ S ⊆ P, ∀ T ⊆ Q, |∑ i ∈ S, ∑ j ∈ T, M i j| ≤
      α * Real.sqrt (P.card * Q.card) := by
    intro S hS T hT
    refine (hdisc S T (hPQ.mono hS hT)).trans ?_
    gcongr
  have hx : ∀ i, |(if lev (x i) = k then x i else 0)| ≤ (2:ℝ) ^ (k + 1) := by
    intro i
    split_ifs with h
    · rw [← h]; exact (lt_zpow_lev _).le
    · simp only [abs_zero]; positivity
  have hy : ∀ j, |(if lev (y j) = l then y j else 0)| ≤ (2:ℝ) ^ (l + 1) := by
    intro j
    split_ifs with h
    · rw [← h]; exact (lt_zpow_lev _).le
    · simp only [abs_zero]; positivity
  have hxP : ∀ i ∉ P, (if lev (x i) = k then x i else 0) = 0 := by
    intro i hi
    simp only [hP, mem_filter, mem_univ, true_and, not_and, not_not] at hi
    split_ifs with h
    · exact hi h
    · rfl
  have hyQ : ∀ j ∉ Q, (if lev (y j) = l then y j else 0) = 0 := by
    intro j hj
    simp only [hQ, mem_filter, mem_univ, true_and, not_and, not_not] at hj
    split_ifs with h
    · exact hj h
    · rfl
  have key := abs_bilin_le M P Q (by positivity) (by positivity) hM _ _ hx hxP hy hyQ
  have hX : ((2:ℝ) ^ k) ^ 2 * P.card ≤ ∑ i, (if lev (x i) = k then x i ^ 2 else 0) := by
    calc ((2:ℝ) ^ k) ^ 2 * P.card = ∑ i ∈ P, ((2:ℝ) ^ k) ^ 2 := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ P, x i ^ 2 := by
          refine sum_le_sum fun i hi ↦ ?_
          simp only [hP, mem_filter, mem_univ, true_and] at hi
          rw [← hi.1, ← sq_abs (x i)]
          have := zpow_lev_le hi.2
          gcongr
      _ = ∑ i, (if lev (x i) = k then x i ^ 2 else 0) := by
          rw [hP, sum_filter]
          refine sum_congr rfl fun i _ ↦ ?_
          by_cases h1 : lev (x i) = k <;> by_cases h2 : x i = 0 <;> simp [h1, h2]
  have hY : ((2:ℝ) ^ l) ^ 2 * Q.card ≤ ∑ j, (if lev (y j) = l then y j ^ 2 else 0) := by
    calc ((2:ℝ) ^ l) ^ 2 * Q.card = ∑ j ∈ Q, ((2:ℝ) ^ l) ^ 2 := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ Q, y j ^ 2 := by
          refine sum_le_sum fun j hj ↦ ?_
          simp only [hQ, mem_filter, mem_univ, true_and] at hj
          rw [← hj.1, ← sq_abs (y j)]
          have := zpow_lev_le hj.2
          gcongr
      _ = ∑ j, (if lev (y j) = l then y j ^ 2 else 0) := by
          rw [hQ, sum_filter]
          refine sum_congr rfl fun j _ ↦ ?_
          by_cases h1 : lev (y j) = l <;> by_cases h2 : y j = 0 <;> simp [h1, h2]
  have e1 : (2:ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [zpow_add_one₀ two_ne_zero]; ring
  have e2 : (2:ℝ) ^ (l + 1) = 2 * 2 ^ l := by rw [zpow_add_one₀ two_ne_zero]; ring
  have hsq : Real.sqrt ((P.card : ℝ) * Q.card) = Real.sqrt P.card * Real.sqrt Q.card :=
    Real.sqrt_mul (Nat.cast_nonneg _) _
  rw [e1, e2, hsq] at key
  set u := (2:ℝ) ^ k * Real.sqrt P.card
  set w := (2:ℝ) ^ l * Real.sqrt Q.card
  have hu : u ^ 2 = ((2:ℝ) ^ k) ^ 2 * P.card := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hw : w ^ 2 = ((2:ℝ) ^ l) ^ 2 * Q.card := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h16 : 4 * (2 * 2 ^ k) * (2 * 2 ^ l) * (α * (Real.sqrt P.card * Real.sqrt Q.card)) =
      16 * α * (u * w) := by ring
  rw [h16] at key
  nlinarith [mul_nonneg hα.le (sq_nonneg (u - w))]

omit [Fintype ι] [DecidableEq ι] in
theorem sum_swap4 {κ κ' : Type*} (s t : Finset ι) (D : Finset κ) (K : Finset κ')
    (G : ι → ι → κ → κ' → ℝ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ d ∈ D, ∑ k ∈ K, G i j d k =
      ∑ d ∈ D, ∑ k ∈ K, ∑ i ∈ s, ∑ j ∈ t, G i j d k := by
  calc ∑ i ∈ s, ∑ j ∈ t, ∑ d ∈ D, ∑ k ∈ K, G i j d k
        = ∑ i ∈ s, ∑ d ∈ D, ∑ k ∈ K, ∑ j ∈ t, G i j d k := by
          refine sum_congr rfl fun i _ ↦ ?_
          rw [sum_comm]
          exact sum_congr rfl fun d _ ↦ sum_comm
    _ = ∑ d ∈ D, ∑ k ∈ K, ∑ i ∈ s, ∑ j ∈ t, G i j d k := by
          rw [sum_comm]
          exact sum_congr rfl fun d _ ↦ sum_comm

omit [DecidableEq ι] in
/-- **The core estimate**: the bilinear form between two vectors with disjoint supports, split
into dyadic levels; levels at most `L` apart by discrepancy, the others by the row sums. -/
theorem core (M : ι → ι → ℝ) (hsymm : ∀ i j, M i j = M j i) {B α : ℝ} (hα : 0 < α)
    (hB : ∀ i, ∑ j, |M i j| ≤ B)
    (hdisc : ∀ S T : Finset ι, Disjoint S T →
      |∑ i ∈ S, ∑ j ∈ T, M i j| ≤ α * Real.sqrt (S.card * T.card))
    (L : ℕ) (x y : ι → ℝ) (hxy : ∀ i, x i = 0 ∨ y i = 0) :
    |∑ i, ∑ j, x i * M i j * y j| ≤
      (8 * α * (2 * L + 1) + B / 2 ^ L) * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
  have hx2 : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  have hy2 : 0 ≤ ∑ i, y i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  have h2L : (0:ℝ) < 2 ^ L := by positivity
  set D : Finset ℤ := Icc (-(L:ℤ)) L with hD
  set K : Finset ℤ := univ.image (fun i ↦ lev (x i)) with hK
  have hsplit : ∀ i j, x i * M i j * y j =
      (if lev (y j) - lev (x i) ∈ D then x i * M i j * y j else 0) +
      (if lev (y j) + L < lev (x i) then x i * M i j * y j else 0) +
      (if lev (x i) + L < lev (y j) then x i * M i j * y j else 0) := by
    intro i j
    simp only [hD, mem_Icc]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hnear : ∀ i j, (if lev (y j) - lev (x i) ∈ D then x i * M i j * y j else 0) =
      ∑ d ∈ D, ∑ k ∈ K,
        (if lev (x i) = k then x i else 0) * M i j * (if lev (y j) = k + d then y j else 0) := by
    intro i j
    have h1 : ∀ d, ∑ k ∈ K,
        (if lev (x i) = k then x i else 0) * M i j * (if lev (y j) = k + d then y j else 0) =
        if lev (y j) - lev (x i) = d then x i * M i j * y j else 0 := by
      intro d
      rw [sum_eq_single_of_mem (lev (x i)) (mem_image.2 ⟨i, mem_univ i, rfl⟩)]
      · rw [ite_eq_left rfl]
        by_cases h : lev (y j) - lev (x i) = d
        · rw [ite_eq_left (by omega), ite_eq_left h]
        · rw [ite_eq_right (by omega), ite_eq_right h, mul_zero]
      · intro k _ hk
        rw [ite_eq_right (Ne.symm hk)]
        ring
    rw [sum_congr rfl fun d _ ↦ h1 d, sum_ite_eq]
  have e : ∑ i, ∑ j, x i * M i j * y j =
      ∑ d ∈ D, ∑ k ∈ K, ∑ i, ∑ j,
        (if lev (x i) = k then x i else 0) * M i j * (if lev (y j) = k + d then y j else 0) +
      ∑ i, ∑ j, (if lev (y j) + L < lev (x i) then x i * M i j * y j else 0) +
      ∑ i, ∑ j, (if lev (x i) + L < lev (y j) then x i * M i j * y j else 0) := by
    rw [← sum_swap4]
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ ↦ ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [← hnear]
    exact hsplit i j
  -- the near levels
  have hN : |∑ d ∈ D, ∑ k ∈ K, ∑ i, ∑ j,
      (if lev (x i) = k then x i else 0) * M i j * (if lev (y j) = k + d then y j else 0)| ≤
      8 * α * (2 * L + 1) * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
    refine (abs_sum_sum_le D K _ (fun d k ↦ 8 * α * (∑ i, (if lev (x i) = k then x i ^ 2 else 0)
      + ∑ j, (if lev (y j) = k + d then y j ^ 2 else 0)))
      fun d _ k _ ↦ near_block_le M hα hdisc x y hxy k (k + d)).trans ?_
    have hX := sum_shift_le (fun i ↦ lev (x i)) (fun i ↦ x i ^ 2) (fun i ↦ sq_nonneg _) K 0
    simp only [add_zero] at hX
    have hDc : ((D.card : ℕ) : ℝ) = 2 * L + 1 := by
      rw [hD, Int.card_Icc]
      have : ((L:ℤ) + 1 - -(L:ℤ)).toNat = 2 * L + 1 := by omega
      rw [this]
      push_cast
      ring
    calc ∑ d ∈ D, ∑ k ∈ K, 8 * α * (∑ i, (if lev (x i) = k then x i ^ 2 else 0)
          + ∑ j, (if lev (y j) = k + d then y j ^ 2 else 0))
        ≤ ∑ d ∈ D, 8 * α * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
          refine sum_le_sum fun d _ ↦ ?_
          rw [← mul_sum, sum_add_distrib]
          have hY := sum_shift_le (fun j ↦ lev (y j)) (fun j ↦ y j ^ 2) (fun j ↦ sq_nonneg _) K d
          gcongr
      _ = 8 * α * (2 * L + 1) * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) := by
          rw [sum_const, nsmul_eq_mul, hDc]
          ring
  -- the far levels
  have hF1 : |∑ i, ∑ j, (if lev (y j) + L < lev (x i) then x i * M i j * y j else 0)| ≤
      B / 2 ^ L * ∑ i, x i ^ 2 := by
    refine (abs_sum_sum_le _ _ _ (fun i j ↦ x i ^ 2 / 2 ^ L * |M i j|) fun i _ j _ ↦ ?_).trans ?_
    · split_ifs with h
      · have := far_le h (M i j)
        linarith [show |M i j| * x i ^ 2 / 2 ^ L = x i ^ 2 / 2 ^ L * |M i j| by ring]
      · simp only [abs_zero]; positivity
    · calc ∑ i, ∑ j, x i ^ 2 / 2 ^ L * |M i j| ≤ ∑ i, x i ^ 2 / 2 ^ L * B := by
            refine sum_le_sum fun i _ ↦ ?_
            rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left (hB i) (by positivity)
        _ = B / 2 ^ L * ∑ i, x i ^ 2 := by
            rw [mul_sum]
            exact sum_congr rfl fun i _ ↦ by ring
  have hF2 : |∑ i, ∑ j, (if lev (x i) + L < lev (y j) then x i * M i j * y j else 0)| ≤
      B / 2 ^ L * ∑ i, y i ^ 2 := by
    refine (abs_sum_sum_le _ _ _ (fun i j ↦ y j ^ 2 / 2 ^ L * |M i j|) fun i _ j _ ↦ ?_).trans ?_
    · split_ifs with h
      · have := far_le h (M i j)
        rw [show x i * M i j * y j = y j * M i j * x i by ring]
        linarith [show |M i j| * y j ^ 2 / 2 ^ L = y j ^ 2 / 2 ^ L * |M i j| by ring]
      · simp only [abs_zero]; positivity
    · rw [sum_comm]
      calc ∑ j, ∑ i, y j ^ 2 / 2 ^ L * |M i j| ≤ ∑ j, y j ^ 2 / 2 ^ L * B := by
            refine sum_le_sum fun j _ ↦ ?_
            rw [← mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            calc ∑ i, |M i j| = ∑ i, |M j i| := sum_congr rfl fun i _ ↦ by rw [hsymm]
              _ ≤ B := hB j
        _ = B / 2 ^ L * ∑ i, y i ^ 2 := by
            rw [mul_sum]
            exact sum_congr rfl fun i _ ↦ by ring
  rw [e]
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ 8 * α * (2 * L + 1) * (∑ i, x i ^ 2 + ∑ i, y i ^ 2) + B / 2 ^ L * ∑ i, x i ^ 2 +
        B / 2 ^ L * ∑ i, y i ^ 2 := by gcongr
    _ = _ := by ring

/-- A random subset contains `i` and misses `j ≠ i` with probability `1/4`. -/
theorem sum_ind_mul_ind {i j : ι} (hij : i ≠ j) :
    ∑ σ : ι → Bool, (if σ i then (1:ℝ) else 0) * (if σ j then 0 else 1) =
      2 ^ Fintype.card ι / 4 := by
  let τ : ι → (ι → Bool) → (ι → Bool) := fun k σ ↦ Function.update σ k (!σ k)
  have hτ : ∀ k, Function.Involutive (τ k) := by
    intro k σ
    funext l
    by_cases h : l = k
    · subst h; simp [τ]
    · simp [τ, Function.update_of_ne h]
  set f : (ι → Bool) → ℝ := fun σ ↦ (if σ i then (1:ℝ) else 0) * (if σ j then 0 else 1) with hf
  have h1 : ∑ σ, f (τ i σ) = ∑ σ, f σ := (hτ i).bijective.sum_comp f
  have h2 : ∑ σ, f (τ j σ) = ∑ σ, f σ := (hτ j).bijective.sum_comp f
  have h3 : ∑ σ, f (τ i (τ j σ)) = ∑ σ, f σ :=
    ((hτ i).bijective.comp (hτ j).bijective).sum_comp f
  have h4 : ∀ σ, f σ + f (τ i σ) + f (τ j σ) + f (τ i (τ j σ)) = 1 := by
    intro σ
    simp only [hf, τ, Function.update_self, Function.update_of_ne hij,
      Function.update_of_ne hij.symm]
    cases σ i <;> cases σ j <;> norm_num
  have h5 : ∑ σ : ι → Bool, (1:ℝ) = 2 ^ Fintype.card ι := by simp
  have h6 : ∑ σ, (f σ + f (τ i σ) + f (τ j σ) + f (τ i (τ j σ))) = ∑ σ : ι → Bool, (1:ℝ) :=
    sum_congr rfl fun σ _ ↦ h4 σ
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, h1, h2, h3, h5] at h6
  change ∑ σ, f σ = _
  linarith

/-- Averaging over the random partitions `(σ, σᶜ)`: with zero diagonal,
`∑_σ (v 1_σ)ᵀ M (v 1_σᶜ) = 2^n/4 · vᵀ M v`. -/
theorem sum_partition (M : ι → ι → ℝ) (hdiag : ∀ i, M i i = 0) (v : ι → ℝ) :
    ∑ σ : ι → Bool, ∑ i, ∑ j, (if σ i then v i else 0) * M i j * (if σ j then 0 else v j) =
      2 ^ Fintype.card ι / 4 * ∑ i, ∑ j, v i * M i j * v j := by
  have e : ∀ σ : ι → Bool, ∀ i j,
      (if σ i then v i else 0) * M i j * (if σ j then 0 else v j) =
      v i * M i j * v j * ((if σ i then (1:ℝ) else 0) * (if σ j then 0 else 1)) := by
    intro σ i j
    split_ifs <;> ring
  simp_rw [e]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← mul_sum]
  by_cases hij : i = j
  · subst hij; simp [hdiag]
  · rw [sum_ind_mul_ind hij]; ring

omit [DecidableEq ι] in
/-- The converse expander mixing lemma with the level cut-off `L` as a parameter. -/
theorem le_of_level (M : ι → ι → ℝ) (hsymm : ∀ i j, M i j = M j i) (hdiag : ∀ i, M i i = 0)
    {B α : ℝ} (hα : 0 < α) (hB : ∀ i, ∑ j, |M i j| ≤ B)
    (hdisc : ∀ S T : Finset ι, Disjoint S T →
      |∑ i ∈ S, ∑ j ∈ T, M i j| ≤ α * Real.sqrt (S.card * T.card))
    (L : ℕ) (v : ι → ℝ) :
    |∑ i, ∑ j, v i * M i j * v j| ≤
      4 * (8 * α * (2 * L + 1) + B / 2 ^ L) * ∑ i, v i ^ 2 := by
  classical
  set K := 8 * α * (2 * L + 1) + B / 2 ^ L
  have hσ : ∀ σ : ι → Bool,
      |∑ i, ∑ j, (if σ i then v i else 0) * M i j * (if σ j then 0 else v j)| ≤
        K * ∑ i, v i ^ 2 := by
    intro σ
    have := core M hsymm hα hB hdisc L (fun i ↦ if σ i then v i else 0)
      (fun j ↦ if σ j then 0 else v j) (fun i ↦ by by_cases h : σ i <;> simp [h])
    refine this.trans (le_of_eq ?_)
    rw [← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun i _ ↦ by by_cases h : σ i <;> simp [h]
  have hpos : (0:ℝ) < 2 ^ Fintype.card ι := by positivity
  have h1 : 2 ^ Fintype.card ι / 4 * |∑ i, ∑ j, v i * M i j * v j| ≤
      2 ^ Fintype.card ι * (K * ∑ i, v i ^ 2) := by
    rw [← abs_of_pos (by positivity : (0:ℝ) < 2 ^ Fintype.card ι / 4), ← abs_mul,
      ← sum_partition M hdiag v]
    calc _ ≤ ∑ σ : ι → Bool,
          |∑ i, ∑ j, (if σ i then v i else 0) * M i j * (if σ j then 0 else v j)| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ σ : ι → Bool, K * ∑ i, v i ^ 2 := sum_le_sum fun σ _ ↦ hσ σ
      _ = 2 ^ Fintype.card ι * (K * ∑ i, v i ^ 2) := by simp
  have h2 : 2 ^ Fintype.card ι * |∑ i, ∑ j, v i * M i j * v j| ≤
      2 ^ Fintype.card ι * (4 * K * ∑ i, v i ^ 2) := by
    linarith
  exact le_of_mul_le_mul_left (by linarith) hpos

/-- The constant in the converse expander mixing lemma. -/
noncomputable def C : ℝ := 64 / Real.log 2 + 100

theorem one_le_C : 1 ≤ C := by
  have : 0 < 64 / Real.log 2 := div_pos (by norm_num) (Real.log_pos one_lt_two)
  unfold C
  linarith

omit [DecidableEq ι] in
/-- **The converse expander mixing lemma** with the explicit constant `BL.C`. -/
theorem bilu_linial_C (M : ι → ι → ℝ) (hsymm : ∀ i j, M i j = M j i)
    (hdiag : ∀ i, M i i = 0) {B α : ℝ} (hα : 0 < α) (hαB : α ≤ B) (hB : ∀ i, ∑ j, |M i j| ≤ B)
    (hdisc : ∀ S T : Finset ι, Disjoint S T →
      |∑ i ∈ S, ∑ j ∈ T, M i j| ≤ α * Real.sqrt (S.card * T.card))
    (v : ι → ℝ) :
    |∑ i, ∑ j, v i * M i j * v j| ≤ C * α * (1 + Real.log (B / α)) * ∑ i, v i ^ 2 := by
  set ℓ := Real.log (B / α) with hℓdef
  have hBα : 1 ≤ B / α := (one_le_div hα).2 hαB
  have hℓ : 0 ≤ ℓ := Real.log_nonneg hBα
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set L := ⌈Real.logb 2 (B / α)⌉₊ with hLdef
  have hL1 : B / α ≤ (2:ℝ) ^ L := by
    calc B / α = (2:ℝ) ^ Real.logb 2 (B / α) :=
          (Real.rpow_logb two_pos (by norm_num) (by positivity)).symm
      _ ≤ (2:ℝ) ^ (L:ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil _)
      _ = 2 ^ L := Real.rpow_natCast 2 L
  have hL2 : (L:ℝ) ≤ ℓ / Real.log 2 + 1 := by
    have hlb : 0 ≤ Real.logb 2 (B / α) := Real.logb_nonneg one_lt_two hBα
    have := Nat.ceil_lt_add_one hlb
    have e : Real.logb 2 (B / α) = ℓ / Real.log 2 := rfl
    linarith
  have hBL : B / 2 ^ L ≤ α := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hα] at hL1
    linarith
  have key := le_of_level M hsymm hdiag hα hB hdisc L v
  have hv : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg _
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hv)
  have h3 : 0 ≤ α / Real.log 2 := by positivity
  have h4 : 0 ≤ α * ℓ := by positivity
  have h5 : (L:ℝ) * α ≤ α * ℓ / Real.log 2 + α := by
    have := mul_le_mul_of_nonneg_left hL2 hα.le
    calc (L:ℝ) * α = α * L := by ring
      _ ≤ α * (ℓ / Real.log 2 + 1) := this
      _ = α * ℓ / Real.log 2 + α := by ring
  have expand : C * α * (1 + ℓ) =
      64 * (α / Real.log 2) + 64 * (α * ℓ / Real.log 2) + 100 * α + 100 * (α * ℓ) := by
    unfold C; ring
  rw [expand]
  nlinarith

/-! ### The centred adjacency matrix of a weighted hypercube -/

section Cube

variable {m : ℕ}

theorem mem_badSet {w : Fin m → Cube m → ℝ} {p γ : ℝ} {x : Cube m} :
    x ∈ badSet w p γ ↔ γ * p * m < |deg w x - p * m| := by
  simp [badSet]

/-- The centred adjacency matrix: `w(e) - p` on the hypercube edges `e = {x, y}`. -/
noncomputable def cmat (w : Fin m → Cube m → ℝ) (p : ℝ) (x y : Cube m) : ℝ :=
  ∑ i, if y = flip x i then w i (lowPt x i) - p else 0

/-- The centred adjacency matrix restricted to the good vertices. -/
noncomputable def gmat (w : Fin m → Cube m → ℝ) (p γ : ℝ) (x y : Cube m) : ℝ :=
  if x ∉ badSet w p γ ∧ y ∉ badSet w p γ then cmat w p x y else 0

theorem cmat_symm (w : Fin m → Cube m → ℝ) (p : ℝ) (x y : Cube m) :
    cmat w p x y = cmat w p y x := by
  unfold cmat
  refine sum_congr rfl fun i _ ↦ ?_
  by_cases h : y = flip x i
  · subst h
    rw [ite_eq_left rfl, ite_eq_left (flip_flip x i).symm, lowPt_flip]
  · have h' : ¬ x = flip y i := fun h' ↦ h (by rw [h', flip_flip])
    rw [ite_eq_right h, ite_eq_right h']

theorem cmat_self (w : Fin m → Cube m → ℝ) (p : ℝ) (x : Cube m) : cmat w p x x = 0 := by
  unfold cmat
  exact sum_eq_zero fun i _ ↦ ite_eq_right (fun h ↦ flip_ne_self x i h.symm)

theorem sum_cmat_mul (w : Fin m → Cube m → ℝ) (p : ℝ) (x : Cube m) (h : Cube m → ℝ) :
    ∑ y, cmat w p x y * h y = ∑ i, (w i (lowPt x i) - p) * h (flip x i) := by
  unfold cmat
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ ↦ ?_
  simp_rw [ite_mul, zero_mul]
  simp

/-- `energy w h - p energy 1 h = ∑ₓ (deg w x - p m) h(x)² - hᵀ N h` for the centred adjacency
matrix `N`. -/
theorem energy_sub_eq (w : Fin m → Cube m → ℝ) (p : ℝ) (h : Cube m → ℝ) :
    energy w h - p * energy 1 h =
      ∑ x, (deg w x - p * m) * h x ^ 2 - ∑ x, ∑ y, h x * cmat w p x y * h y := by
  rw [← energy_sub_const, ← sum_mul_lap, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  have e1 : ∑ y, h x * cmat w p x y * h y =
      h x * ∑ i, (w i (lowPt x i) - p) * h (flip x i) := by
    rw [← sum_cmat_mul, mul_sum]
    exact sum_congr rfl fun y _ ↦ by ring
  have e2 : ∑ i, (w i (lowPt x i) - p) * h x = (deg w x - p * m) * h x := by
    rw [← sum_mul, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, deg]
    ring
  have e3 : ∑ i, (w i (lowPt x i) - p) * (h x - h (flip x i)) =
      ∑ i, (w i (lowPt x i) - p) * h x - ∑ i, (w i (lowPt x i) - p) * h (flip x i) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [e1]
  simp only [lap]
  rw [e3, e2]
  ring

/-- Summing over the edges in direction `i` by their lower endpoints. -/
theorem sum_eq_sum_low (i : Fin m) (G : Cube m → ℝ) :
    ∑ x, G x = ∑ x ∈ univ.filter (fun x : Cube m ↦ x i = false), (G x + G (flip x i)) := by
  have hb : Function.Bijective fun x : Cube m ↦ flip x i :=
    (flip_injective i).bijective_of_finite
  have e1 : ∑ x, G x = ∑ x, (if x i = false then G x else 0) +
      ∑ x, (if x i = false then 0 else G x) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun x _ ↦ by split_ifs <;> ring
  have e2 : ∑ x, (if x i = false then 0 else G x) =
      ∑ x, (if x i = false then G (flip x i) else 0) := by
    rw [← hb.sum_comp]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [flip_apply_self]
    cases x i <;> simp
  rw [e1, e2, ← sum_add_distrib, sum_filter]
  exact sum_congr rfl fun x _ ↦ by split_ifs <;> ring

/-- The centred adjacency matrix summed over disjoint `S × T` is the centred cut. -/
theorem sum_cmat_eq_cutW (w : Fin m → Cube m → ℝ) (p : ℝ) (S T : Finset (Cube m))
    (hST : Disjoint S T) :
    ∑ x ∈ S, ∑ y ∈ T, cmat w p x y = cutW w S T - p * cutW 1 S T := by
  have e1 : ∑ x ∈ S, ∑ y ∈ T, cmat w p x y =
      ∑ i, ∑ x, (if x ∈ S ∧ flip x i ∈ T then w i (lowPt x i) - p else 0) := by
    unfold cmat
    calc ∑ x ∈ S, ∑ y ∈ T, ∑ i, (if y = flip x i then w i (lowPt x i) - p else 0)
        = ∑ x ∈ S, ∑ i, (if flip x i ∈ T then w i (lowPt x i) - p else 0) := by
          refine sum_congr rfl fun x _ ↦ ?_
          rw [sum_comm]
          exact sum_congr rfl fun i _ ↦ sum_ite_eq' _ _ _
      _ = ∑ i, ∑ x ∈ S, (if flip x i ∈ T then w i (lowPt x i) - p else 0) := sum_comm
      _ = _ := by
          refine sum_congr rfl fun i _ ↦ ?_
          rw [← sum_subset (subset_univ S) (fun x _ hx ↦ by simp [hx])]
          refine sum_congr rfl fun x hx ↦ ?_
          simp [hx]
  have hd : ∀ z, z ∈ S → z ∉ T := fun z hz hz' ↦ disjoint_left.1 hST hz hz'
  rw [e1, cutW, cutW, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [sum_eq_sum_low i, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun x hx ↦ ?_
  have hxi : x i = false := (mem_filter.1 hx).2
  rw [lowPt_flip, lowPt_of_false hxi, flip_flip]
  simp only [Pi.one_apply, one_mul]
  by_cases h1 : x ∈ S <;> by_cases h2 : flip x i ∈ T <;> by_cases h3 : flip x i ∈ S <;>
    by_cases h4 : x ∈ T <;> first
    | exact absurd h4 (hd _ h1)
    | simp [h1, h2, h3, h4]

end Cube


/-- The choice of `η`: `C η (1 + log (3 / η)) ≤ γ` for `η = t²`, `t = γ / (5 C)`. -/
theorem eta_bound {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    C * (γ / (5 * C)) ^ 2 * (1 + Real.log (3 / (γ / (5 * C)) ^ 2)) ≤ γ := by
  have hC := one_le_C
  set t := γ / (5 * C) with ht
  have ht0 : 0 < t := by positivity
  have hCt : C * t = γ / 5 := by rw [ht]; field_simp
  have hlog : Real.log (3 / t ^ 2) ≤ 2 / t := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]
    have h3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have h4 := Real.log_le_sub_one_of_pos (inv_pos.2 ht0)
    rw [Real.log_inv] at h4
    have : 2 / t = 2 * t⁻¹ := by ring
    push_cast
    linarith
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    linarith
  have h1 : C * t ^ 2 * (1 + Real.log (3 / t ^ 2)) ≤ C * t ^ 2 * (1 + 2 / t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h2 : C * t ^ 2 * (1 + 2 / t) = C * t * (t + 2) := by
    field_simp
  rw [h2, hCt] at h1
  nlinarith

end BL

/-- **The converse expander mixing lemma** of Bilu and Linial. -/
theorem bilu_linial : ∃ c : ℝ, 0 < c ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (M : ι → ι → ℝ), (∀ i j, M i j = M j i) →
      (∀ i, M i i = 0) → ∀ {B α : ℝ}, 0 < α → α ≤ B → (∀ i, ∑ j, |M i j| ≤ B) →
      (∀ S T : Finset ι, Disjoint S T →
        |∑ i ∈ S, ∑ j ∈ T, M i j| ≤ α * Real.sqrt (S.card * T.card)) →
      ∀ v : ι → ℝ, |∑ i, ∑ j, v i * M i j * v j| ≤
        c * α * (1 + Real.log (B / α)) * ∑ i, v i ^ 2 :=
  ⟨BL.C, by linarith [BL.one_le_C], fun M hsymm hdiag _ _ hα hαB hB hdisc v ↦
    BL.bilu_linial_C M hsymm hdiag hα hαB hB hdisc v⟩

/-- **Spectral closeness on the good vertices** from the discrepancy, for a small enough `η`
depending on `γ`. -/
theorem goodNorm_of_disc {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∀ {m : ℕ} {p : ℝ} {w : Fin m → Cube m → ℝ}, (∀ i x, w i x = 0 ∨ w i x = 1) → 0 < p →
        p ≤ 1 → Disc w p γ η → GoodNorm w p γ := by
  have hC := BL.one_le_C
  have heta := BL.eta_bound hγ hγ1
  set t := γ / (5 * BL.C) with ht
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]
    linarith
  refine ⟨t ^ 2, by positivity, pow_le_one₀ ht0.le ht1, ?_⟩
  intro m p w hw hp hp1 hdisc h hbad
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [energy]
  have hm' : (0:ℝ) < m := Nat.cast_pos.2 hm
  have hw0 : ∀ i z, 0 ≤ w i z := fun i z ↦ by rcases hw i z with h | h <;> norm_num [h]
  -- the centred adjacency matrix on the good vertices
  have hsymm : ∀ x y, BL.gmat w p γ x y = BL.gmat w p γ y x := by
    intro x y
    unfold BL.gmat
    rw [BL.cmat_symm w p x y]
    by_cases hx : x ∈ badSet w p γ <;> by_cases hy : y ∈ badSet w p γ <;> simp [hx, hy]
  have hdiag : ∀ x, BL.gmat w p γ x x = 0 := fun x ↦ by
    unfold BL.gmat
    simp [BL.cmat_self]
  have hrow : ∀ x, ∑ y, |BL.gmat w p γ x y| ≤ 3 * p * m := by
    intro x
    by_cases hx : x ∈ badSet w p γ
    · have : ∀ y, BL.gmat w p γ x y = 0 := fun y ↦ by simp [BL.gmat, hx]
      simp only [this, abs_zero, sum_const_zero]
      positivity
    have hdeg : deg w x ≤ p * m + γ * p * m := by
      have := not_lt.1 (fun h' ↦ hx (BL.mem_badSet.2 h'))
      linarith [le_abs_self (deg w x - p * m)]
    have hγpm : γ * (p * m) ≤ 1 * (p * m) := mul_le_mul_of_nonneg_right hγ1 (by positivity)
    calc ∑ y, |BL.gmat w p γ x y|
        ≤ ∑ y, ∑ i, (if y = flip x i then |w i (lowPt x i) - p| else 0) := by
          refine sum_le_sum fun y _ ↦ ?_
          unfold BL.gmat BL.cmat
          split_ifs
          · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ ?_)
            split_ifs <;> simp
          · simp only [abs_zero]
            exact sum_nonneg fun i _ ↦ by split_ifs <;> simp
      _ = ∑ i, |w i (lowPt x i) - p| := by
          rw [sum_comm]
          simp
      _ ≤ ∑ i, (w i (lowPt x i) + p) := sum_le_sum fun i _ ↦
          abs_sub_le_iff.2 ⟨by linarith [hw0 i (lowPt x i)], by linarith [hw0 i (lowPt x i)]⟩
      _ = deg w x + p * m := by
          rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, deg]
          ring
      _ ≤ 3 * p * m := by linarith
  have hα : 0 < t ^ 2 * p * m := by positivity
  have hαB : t ^ 2 * p * m ≤ 3 * p * m := by
    have : t ^ 2 ≤ 3 := by nlinarith
    have hpm : 0 ≤ p * m := by positivity
    nlinarith
  have hdisc' : ∀ S T : Finset (Cube m), Disjoint S T →
      |∑ x ∈ S, ∑ y ∈ T, BL.gmat w p γ x y| ≤
        t ^ 2 * p * m * Real.sqrt (S.card * T.card) := by
    intro S T hST
    set S' := S.filter (fun x ↦ x ∉ badSet w p γ) with hS'
    set T' := T.filter (fun x ↦ x ∉ badSet w p γ) with hT'
    have e : ∑ x ∈ S, ∑ y ∈ T, BL.gmat w p γ x y = ∑ x ∈ S', ∑ y ∈ T', BL.cmat w p x y := by
      rw [hS', sum_filter]
      refine sum_congr rfl fun x _ ↦ ?_
      rw [hT', sum_filter]
      by_cases hx : x ∈ badSet w p γ
      · rw [ite_eq_right (not_not.2 hx)]
        exact sum_eq_zero fun y _ ↦ by simp [BL.gmat, hx]
      · rw [ite_eq_left hx]
        exact sum_congr rfl fun y _ ↦ by
          by_cases hy : y ∈ badSet w p γ <;> simp [BL.gmat, hx, hy]
    have hS'T' : Disjoint S' T' := hST.mono (filter_subset _ _) (filter_subset _ _)
    rw [e, BL.sum_cmat_eq_cutW w p S' T' hS'T']
    refine (hdisc S' T' hS'T' ?_ ?_).trans ?_
    · exact disjoint_left.2 fun x hx hx' ↦ (mem_filter.1 hx).2 hx'
    · exact disjoint_left.2 fun x hx hx' ↦ (mem_filter.1 hx).2 hx'
    · have h1 : S' ⊆ S := filter_subset _ _
      have h2 : T' ⊆ T := filter_subset _ _
      gcongr
  have key := BL.bilu_linial_C (BL.gmat w p γ) hsymm hdiag hα hαB hrow hdisc' h
  have hBα : 3 * p * m / (t ^ 2 * p * m) = 3 / t ^ 2 := by
    field_simp
  rw [hBα] at key
  have hM : ∑ x, ∑ y, h x * BL.cmat w p x y * h y =
      ∑ x, ∑ y, h x * BL.gmat w p γ x y * h y := by
    refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
    by_cases hx : x ∈ badSet w p γ
    · simp [hbad x hx]
    by_cases hy : y ∈ badSet w p γ
    · simp [hbad y hy]
    simp [BL.gmat, hx, hy]
  have hD : |∑ x, (deg w x - p * m) * h x ^ 2| ≤ γ * p * m * ∑ x, h x ^ 2 := by
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ ↦ ?_)
    by_cases hx : x ∈ badSet w p γ
    · simp [hbad x hx]
    rw [abs_mul, abs_of_nonneg (sq_nonneg (h x))]
    exact mul_le_mul_of_nonneg_right (not_lt.1 fun h' ↦ hx (BL.mem_badSet.2 h')) (sq_nonneg _)
  have hh : 0 ≤ ∑ x, h x ^ 2 := sum_nonneg fun x _ ↦ sq_nonneg _
  have key2 : BL.C * (t ^ 2 * p * m) * (1 + Real.log (3 / t ^ 2)) * ∑ x, h x ^ 2 ≤
      γ * p * m * ∑ x, h x ^ 2 := by
    have e : BL.C * (t ^ 2 * p * m) * (1 + Real.log (3 / t ^ 2)) =
        (BL.C * t ^ 2 * (1 + Real.log (3 / t ^ 2))) * (p * m) := by ring
    have hpm : 0 ≤ p * m := by positivity
    rw [e]
    calc _ ≤ γ * (p * m) * ∑ x, h x ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heta hpm) hh
      _ = _ := by ring
  rw [BL.energy_sub_eq, hM]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ γ * p * m * ∑ x, h x ^ 2 + γ * p * m * ∑ x, h x ^ 2 := add_le_add hD (key.trans key2)
    _ = 2 * γ * p * m * ∑ x, h x ^ 2 := by ring

end BMW26
