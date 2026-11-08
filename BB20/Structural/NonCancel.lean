module

public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise

/-!
# Non-cancellation of sums of products

[BB20, Lemmas 16 and 8], as statements about real numbers. Fix rows `i` (a finite set of at most
`m` of them), coefficients `aᵢ`, and entries `x_{ij} ∈ [-1, 1]`. For a finite set `K` of columns,
let `F(K) = ∑ᵢ aᵢ ∏_{j ∈ K} x_{ij}` (`BB20.Structural.prodSum`).

* `BB20.Structural.exists_subset_of_card_eq_succ` (Lemma 16): if `|K| = k + 1` and there are at
  most `k` rows, then `|F(K)| ≤ (2^k - 1) |F(S)|` for some `S ⊆ K` with `|S| ≤ k`. By induction
  on `k`: with a row `i₀` and a column `j₀`, `F(K)` is the sum of `x_{i₀j₀} F(K ∖ j₀)` and a sum
  of the same kind over the other rows with coefficients `aᵢ (x_{ij₀} - x_{i₀j₀})` and columns
  `K ∖ j₀`. The induction hypothesis bounds the latter through a set `S*` with `|S*| ≤ k - 1`,
  where that sum equals `F(S* ∪ j₀) - x_{i₀j₀} F(S*)`, and the largest of `|F(S* ∪ j₀)|`,
  `|F(S*)|`, `|F(K ∖ j₀)|` gives the bound.
* `BB20.Structural.exists_subset_noncancel` (Lemma 8): for any nonempty `K`,
  `|F(K)| ≤ 4^m |K|^{m(m+1)} |F(S)|` for some `S ⊆ K` with `|S| ≤ m`. While `|K| > m`, split `K`
  into `m + 1` parts of nearly equal sizes (`BB20.Structural.exists_subset_step`), treat the
  product over each part as one column, and keep the union `K₁` of the parts that Lemma 16
  selects. This drops a whole part, so `(m + 1)(|K₁| - m) ≤ m (|K| - m)`, at a cost `2^m - 1`.
  Since `2^m (m / (m + 1))^{m(m+1)} ≤ 1`, induction on `|K|` gives the bound
  `2^m (|K| - m)^{m(m+1)}` (`BB20.Structural.exists_subset_noncancel_aux`).
-/

@[expose] public section

namespace BB20.Structural

open Finset

variable {ι κ : Type*}

/-- The sum `F(K) = ∑_{i ∈ rows} aᵢ ∏_{j ∈ K} x_{ij}`. -/
def prodSum (rows : Finset ι) (a : ι → ℝ) (x : ι → κ → ℝ) (K : Finset κ) : ℝ :=
  ∑ i ∈ rows, a i * ∏ j ∈ K, x i j

theorem prodSum_empty_rows (a : ι → ℝ) (x : ι → κ → ℝ) (K : Finset κ) :
    prodSum ∅ a x K = 0 := by
  simp [prodSum]

/-- **[BB20, Lemma 16]**: with at most `k` rows and `k + 1` columns, some set of at most `k`
columns keeps a `1 / (2^k - 1)` fraction of `|F|`. -/
theorem exists_subset_of_card_eq_succ (x : ι → κ → ℝ) (hx : ∀ i j, |x i j| ≤ 1) (k : ℕ) :
    ∀ (rows : Finset ι) (a : ι → ℝ) (K : Finset κ), rows.card ≤ k → K.card = k + 1 →
      ∃ S ⊆ K, S.card ≤ k ∧ |prodSum rows a x K| ≤ (2 ^ k - 1) * |prodSum rows a x S| := by
  classical
  induction k with
  | zero =>
    intro rows a K hr _
    obtain rfl : rows = ∅ := card_eq_zero.mp (Nat.le_zero.mp hr)
    exact ⟨∅, empty_subset _, by simp, by simp [prodSum_empty_rows]⟩
  | succ k ih =>
    intro rows a K hr hK
    rcases rows.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
    · exact ⟨∅, empty_subset _, by simp, by simp [prodSum_empty_rows]⟩
    obtain ⟨j₀, hj₀⟩ : K.Nonempty := card_pos.mp (by omega)
    set b : ι → ℝ := fun i ↦ a i * (x i j₀ - x i₀ j₀) with hb
    have key : ∀ T : Finset κ, j₀ ∉ T → prodSum (rows.erase i₀) b x T =
        prodSum rows a x (insert j₀ T) - x i₀ j₀ * prodSum rows a x T := by
      intro T hT
      unfold prodSum
      rw [sum_erase _ (by simp [hb]), mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun i _ ↦ ?_
      rw [prod_insert hT, hb]
      ring
    obtain ⟨S, hSK, hSc, hS⟩ := ih (rows.erase i₀) b (K.erase j₀)
      (by rw [card_erase_of_mem hi₀]; omega) (by rw [card_erase_of_mem hj₀]; omega)
    have hj₀S : j₀ ∉ S := fun h ↦ by simpa using hSK h
    have hK' : prodSum rows a x K =
        prodSum (rows.erase i₀) b x (K.erase j₀) + x i₀ j₀ * prodSum rows a x (K.erase j₀) := by
      rw [key _ (notMem_erase j₀ K), insert_erase hj₀]
      ring
    have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hx₀ : |x i₀ j₀| ≤ 1 := hx _ _
    set A := |prodSum rows a x (insert j₀ S)|
    set B := |prodSum rows a x S|
    set C := |prodSum rows a x (K.erase j₀)|
    have hmain : |prodSum rows a x K| ≤ (2 ^ k - 1) * (A + B) + C := by
      have hbS : |prodSum (rows.erase i₀) b x S| ≤ A + B := by
        rw [key S hj₀S]
        calc _ ≤ A + |x i₀ j₀ * prodSum rows a x S| := abs_sub _ _
          _ ≤ A + B := by
            rw [abs_mul]
            gcongr
            exact mul_le_of_le_one_left (abs_nonneg _) hx₀
      rw [hK']
      calc _ ≤ |prodSum (rows.erase i₀) b x (K.erase j₀)| +
            |x i₀ j₀ * prodSum rows a x (K.erase j₀)| := abs_add_le _ _
        _ ≤ (2 ^ k - 1) * (A + B) + C := by
          gcongr
          · exact hS.trans (mul_le_mul_of_nonneg_left hbS (by linarith))
          · rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) hx₀
    have hle : |prodSum rows a x K| ≤ (2 ^ (k + 1) - 1) * max A (max B C) := by
      have hA := le_max_left A (max B C)
      have hB := (le_max_left B C).trans (le_max_right A _)
      have hC := (le_max_right B C).trans (le_max_right A _)
      have h0 : (0 : ℝ) ≤ 2 ^ k - 1 := by linarith
      calc _ ≤ (2 ^ k - 1) * (A + B) + C := hmain
        _ ≤ (2 ^ k - 1) * (max A (max B C) + max A (max B C)) + max A (max B C) := by
          gcongr
        _ = _ := by ring
    have hSK' : S ⊆ K := hSK.trans (erase_subset _ _)
    rcases max_choice A (max B C) with h | h
    · rw [h] at hle
      exact ⟨insert j₀ S, insert_subset hj₀ hSK', (card_insert_le _ _).trans (by omega), hle⟩
    · rcases max_choice B C with h' | h'
      · rw [h, h'] at hle
        exact ⟨S, hSK', by omega, hle⟩
      · rw [h, h'] at hle
        exact ⟨K.erase j₀, erase_subset _ _, by rw [card_erase_of_mem hj₀]; omega, hle⟩

/-- One round of the proof of Lemma 8: if `|K| > m ≥ |rows|`, some `K₁ ⊆ K` with
`(m + 1) |K₁| ≤ m |K| + m` has `|F(K)| ≤ (2^m - 1) |F(K₁)|`. -/
theorem exists_subset_step (x : ι → κ → ℝ) (hx : ∀ i j, |x i j| ≤ 1) (m : ℕ)
    (rows : Finset ι) (hr : rows.card ≤ m) (a : ι → ℝ) (K : Finset κ) (hK : m < K.card) :
    ∃ K₁ ⊆ K, (m + 1) * K₁.card ≤ m * K.card + m ∧
      |prodSum rows a x K| ≤ (2 ^ m - 1) * |prodSum rows a x K₁| := by
  classical
  obtain ⟨P, hP, hPc⟩ :=
    Finpartition.exists_equipartition_card_eq K (n := m + 1) (by omega) (by omega)
  have hy : ∀ i (B : Finset κ), |∏ j ∈ B, x i j| ≤ 1 := fun i B ↦ by
    rw [abs_prod]
    exact prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun j _ ↦ hx i j)
  obtain ⟨T, hTP, hTc, hT⟩ :=
    exists_subset_of_card_eq_succ (fun i B ↦ ∏ j ∈ B, x i j) hy m rows a P.parts hr hPc
  have hdisjT : (T : Set (Finset κ)).PairwiseDisjoint id :=
    P.disjoint.subset (by exact_mod_cast hTP)
  have hprodT : ∀ i, ∏ B ∈ T, ∏ j ∈ B, x i j = ∏ j ∈ T.biUnion id, x i j := fun i ↦
    (prod_biUnion hdisjT).symm
  have hprodK : ∀ i, ∏ B ∈ P.parts, ∏ j ∈ B, x i j = ∏ j ∈ K, x i j := fun i ↦ by
    have := prod_biUnion (f := fun j ↦ x i j) P.disjoint
    rw [P.biUnion_parts] at this
    exact this.symm
  have hsub : T.biUnion id ⊆ K := by
    rw [← P.biUnion_parts]
    exact biUnion_subset_biUnion_of_subset_left _ hTP
  refine ⟨T.biUnion id, hsub, ?_, ?_⟩
  · obtain ⟨B₀, hB₀P, hB₀T⟩ : ∃ B₀ ∈ P.parts, B₀ ∉ T := by
      by_contra h
      push Not at h
      have := card_le_card h
      omega
    have hdisj : Disjoint (T.biUnion id) B₀ := by
      rw [disjoint_biUnion_left]
      intro B hB
      exact P.disjoint (hTP hB) hB₀P (ne_of_mem_of_not_mem hB hB₀T)
    have hB₀K : B₀ ⊆ K := P.le hB₀P
    have h1 : (T.biUnion id).card + B₀.card ≤ K.card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card (union_subset hsub hB₀K)
    have h2 : K.card / (m + 1) ≤ B₀.card := hPc ▸ hP.average_le_card_part hB₀P
    have h3 := Nat.div_add_mod K.card (m + 1)
    have h4 := Nat.mod_lt K.card (show 0 < m + 1 by omega)
    have h5 := Nat.mul_le_mul_left (m + 1) h1
    have h6 := Nat.mul_le_mul_left (m + 1) h2
    nlinarith
  · simpa only [prodSum, hprodK, hprodT] using hT

/-- `2 m^{m+1} ≤ (m + 1)^{m+1}` for `m ≥ 1` (Bernoulli). -/
theorem two_mul_pow_le_succ_pow {m : ℕ} (hm : 1 ≤ m) :
    2 * (m : ℝ) ^ (m + 1) ≤ ((m : ℝ) + 1) ^ (m + 1) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hb := one_add_mul_le_pow (a := 1 / (m : ℝ))
    (by have : 0 ≤ 1 / (m : ℝ) := by positivity
        linarith) (m + 1)
  have heq : ((m : ℝ) + 1) ^ (m + 1) = (1 + 1 / (m : ℝ)) ^ (m + 1) * (m : ℝ) ^ (m + 1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  have h2 : (2 : ℝ) ≤ 1 + ((m + 1 : ℕ) : ℝ) * (1 / m) := by
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * (1 / m) := by
      rw [mul_one_div, one_le_div hm']
      push_cast
      linarith
    linarith
  rw [heq]
  calc 2 * (m : ℝ) ^ (m + 1) ≤ (1 + ((m + 1 : ℕ) : ℝ) * (1 / m)) * (m : ℝ) ^ (m + 1) := by
        gcongr
    _ ≤ _ := by gcongr

/-- If `(m + 1) a ≤ m b` with `a ≥ 0` and `m ≥ 1`, then `2^m a^{m(m+1)} ≤ b^{m(m+1)}`. -/
theorem two_pow_mul_pow_le {m : ℕ} (hm : 1 ≤ m) {a b : ℝ} (ha : 0 ≤ a)
    (hab : ((m : ℝ) + 1) * a ≤ m * b) :
    2 ^ m * a ^ (m * (m + 1)) ≤ b ^ (m * (m + 1)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : (2 : ℝ) ^ m * (m : ℝ) ^ (m * (m + 1)) ≤ ((m : ℝ) + 1) ^ (m * (m + 1)) := by
    have := pow_le_pow_left₀ (by positivity) (two_mul_pow_le_succ_pow hm) m
    rw [mul_pow, ← pow_mul, ← pow_mul] at this
    rwa [mul_comm (m + 1) m] at this
  have h2 : (((m : ℝ) + 1) * a) ^ (m * (m + 1)) ≤ ((m : ℝ) * b) ^ (m * (m + 1)) :=
    pow_le_pow_left₀ (by positivity) hab _
  rw [mul_pow, mul_pow] at h2
  have hpos : (0 : ℝ) < (m : ℝ) ^ (m * (m + 1)) := by positivity
  have h3 : 2 ^ m * a ^ (m * (m + 1)) * (m : ℝ) ^ (m * (m + 1)) ≤
      b ^ (m * (m + 1)) * (m : ℝ) ^ (m * (m + 1)) := by
    calc _ = (2 ^ m * (m : ℝ) ^ (m * (m + 1))) * a ^ (m * (m + 1)) := by ring
      _ ≤ ((m : ℝ) + 1) ^ (m * (m + 1)) * a ^ (m * (m + 1)) := by gcongr
      _ ≤ (m : ℝ) ^ (m * (m + 1)) * b ^ (m * (m + 1)) := h2
      _ = _ := by ring
  exact le_of_mul_le_mul_right h3 hpos

/-- The induction behind Lemma 8: for `|K| = N > m ≥ 1`, some `S ⊆ K` with `|S| ≤ m` has
`|F(K)| ≤ 2^m (N - m)^{m(m+1)} |F(S)|`. -/
theorem exists_subset_noncancel_aux (x : ι → κ → ℝ) (hx : ∀ i j, |x i j| ≤ 1) {m : ℕ}
    (hm : 1 ≤ m) (rows : Finset ι) (hr : rows.card ≤ m) (a : ι → ℝ) (N : ℕ) :
    ∀ K : Finset κ, K.card = N → m < N → ∃ S ⊆ K, S.card ≤ m ∧
      |prodSum rows a x K| ≤ 2 ^ m * ((N - m : ℕ) : ℝ) ^ (m * (m + 1)) * |prodSum rows a x S| := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro K hKN hmN
    obtain ⟨K₁, hK₁K, hc, hF⟩ := exists_subset_step x hx m rows hr a K (hKN ▸ hmN)
    rw [hKN] at hc
    have hNm : (1 : ℝ) ≤ ((N - m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N - m)
    have h2m : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    by_cases h₁ : K₁.card ≤ m
    · refine ⟨K₁, hK₁K, h₁, hF.trans ?_⟩
      gcongr
      calc (2 : ℝ) ^ m - 1 ≤ 2 ^ m * 1 := by linarith
        _ ≤ 2 ^ m * ((N - m : ℕ) : ℝ) ^ (m * (m + 1)) := by
          gcongr
          exact one_le_pow₀ hNm
    · push Not at h₁
      have hlt : K₁.card < N := by nlinarith
      obtain ⟨S, hSK, hSc, hS⟩ := ih K₁.card hlt K₁ rfl h₁
      refine ⟨S, hSK.trans hK₁K, hSc, ?_⟩
      have hnum : (2 : ℝ) ^ m * ((K₁.card - m : ℕ) : ℝ) ^ (m * (m + 1)) ≤
          ((N - m : ℕ) : ℝ) ^ (m * (m + 1)) := by
        apply two_pow_mul_pow_le hm (Nat.cast_nonneg _)
        have : (m + 1) * (K₁.card - m) ≤ m * (N - m) := by
          have e1 : (m + 1) * (K₁.card - m) = (m + 1) * K₁.card - (m + 1) * m :=
            Nat.mul_sub _ _ _
          have e2 : m * (N - m) = m * N - m * m := Nat.mul_sub _ _ _
          rw [e1, e2]
          have : (m + 1) * m ≤ (m + 1) * K₁.card := Nat.mul_le_mul_left _ h₁.le
          have : m * m ≤ m * N := Nat.mul_le_mul_left _ hmN.le
          have : (m + 1) * m = m * m + m := by ring
          omega
        exact_mod_cast this
      have h0 : (0 : ℝ) ≤ 2 ^ m - 1 := by linarith
      calc |prodSum rows a x K| ≤ (2 ^ m - 1) * |prodSum rows a x K₁| := hF
        _ ≤ (2 ^ m - 1) * (2 ^ m * ((K₁.card - m : ℕ) : ℝ) ^ (m * (m + 1)) *
            |prodSum rows a x S|) := by gcongr
        _ ≤ 2 ^ m * (2 ^ m * ((K₁.card - m : ℕ) : ℝ) ^ (m * (m + 1)) *
            |prodSum rows a x S|) := by gcongr; linarith
        _ = 2 ^ m * ((2 ^ m * ((K₁.card - m : ℕ) : ℝ) ^ (m * (m + 1))) *
            |prodSum rows a x S|) := by ring
        _ ≤ 2 ^ m * (((N - m : ℕ) : ℝ) ^ (m * (m + 1)) * |prodSum rows a x S|) := by gcongr
        _ = _ := by ring

/-- **[BB20, Lemma 8]**: with at most `m` rows and a nonempty set `K` of columns, some set of at
most `m` columns keeps a `4^{-m} |K|^{-m(m+1)}` fraction of `|F|`. -/
theorem exists_subset_noncancel (x : ι → κ → ℝ) (hx : ∀ i j, |x i j| ≤ 1) (m : ℕ)
    (rows : Finset ι) (hr : rows.card ≤ m) (a : ι → ℝ) (K : Finset κ) (hK : K.Nonempty) :
    ∃ S ⊆ K, S.card ≤ m ∧
      |prodSum rows a x K| ≤ 4 ^ m * (K.card : ℝ) ^ (m * (m + 1)) * |prodSum rows a x S| := by
  have hK1 : (1 : ℝ) ≤ K.card := by exact_mod_cast card_pos.mpr hK
  by_cases hKm : K.card ≤ m
  · refine ⟨K, subset_refl _, hKm, le_mul_of_one_le_left (abs_nonneg _) ?_⟩
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hK1)
  push Not at hKm
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain rfl : rows = ∅ := card_eq_zero.mp (Nat.le_zero.mp hr)
    exact ⟨∅, empty_subset _, by simp, by simp [prodSum_empty_rows]⟩
  obtain ⟨S, hSK, hSc, hS⟩ :=
    exists_subset_noncancel_aux x hx hm rows hr a K.card K rfl hKm
  refine ⟨S, hSK, hSc, hS.trans ?_⟩
  gcongr
  · norm_num
  · exact_mod_cast Nat.sub_le _ _

end BB20.Structural
