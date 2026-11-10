module

public import BHSV25.Net.Greedy
public import Mathlib.Algebra.Order.Round

/-!
# Gram–Schmidt coordinates and a grid of constant precision

For a list `S` of columns whose leading Gram determinants `Δ_l` (of the first `l` columns) are
positive, the residuals `r_l` of the columns against the columns before them
(`BHSV25.Net.gsR`) are the Gram–Schmidt vectors: they are orthogonal (`BHSV25.Net.gsR_orth`),
`‖r_l‖² = Δ_(l+1) / Δ_l` (`BHSV25.Net.gsR_dot_self`), and the projection of every vector onto the
span of the columns is `∑_l (r_l ⬝ y / ‖r_l‖²) r_l` (`BHSV25.Net.sub_resid_eq_sum`).

**The grid** (`BHSV25.Net.exists_grid_near`): for orthogonal vectors `q_l` of squared lengths in
`[1, 4]`, every vector `∑_l a_l q_l` of length at most `1` is within `2 √k / N` of a combination
`∑_l (m_l / N) q_l` with integers `m_l` in the ball `∑ m_l² ≤ N²`. The greedy net
(`BHSV25/Net/GSMachine.lean`) takes `q_l = (Δ_l / σ_l) r_l` with `σ_l = ⌊√(Δ_(l+1) Δ_l)⌋`, so
that its candidates, the points of the ball (`BHSV25/Net/Ball.lean`), do not depend on the number
of vertices.
-/

@[expose] public section

namespace BHSV25

namespace Net

open Matrix

variable {n : ℕ}

/-! ### Orthogonal families -/

theorem dotProduct_sum_orth {k : ℕ} (q : Fin k → Fin n → ℝ)
    (horth : ∀ i j, i ≠ j → q i ⬝ᵥ q j = 0) (a b : Fin k → ℝ) :
    (∑ i, a i • q i) ⬝ᵥ (∑ i, b i • q i) = ∑ i, a i * b i * (q i ⬝ᵥ q i) := by
  rw [sum_dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dotProduct_sum, Finset.sum_eq_single i]
  · simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  · intro j _ hji
    rw [smul_dotProduct, dotProduct_smul, horth i j (Ne.symm hji), smul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The grid.** For orthogonal `q_l` with `1 ≤ ‖q_l‖² ≤ 4` and `‖∑ a_l q_l‖ ≤ 1`, rounding
`N a_l` toward `0` gives integers `m_l` with `∑ m_l² ≤ N²` (so `|m_l| ≤ N`) and
`‖∑ (m_l / N) q_l - ∑ a_l q_l‖² ≤ 4 k / N²`. -/
theorem exists_grid_near {k : ℕ} (q : Fin k → Fin n → ℝ) (horth : ∀ i j, i ≠ j → q i ⬝ᵥ q j = 0)
    (hq : ∀ i, 1 ≤ q i ⬝ᵥ q i ∧ q i ⬝ᵥ q i ≤ 4) (a : Fin k → ℝ)
    (hz : (∑ i, a i • q i) ⬝ᵥ (∑ i, a i • q i) ≤ 1) {N : ℕ} (hN : 0 < N) :
    ∃ m : Fin k → ℤ, (∀ i, |m i| ≤ N) ∧ ∑ i, ((m i : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 ∧
      (∑ i, ((m i : ℝ) / N) • q i - ∑ i, a i • q i) ⬝ᵥ
          (∑ i, ((m i : ℝ) / N) • q i - ∑ i, a i • q i) ≤ 4 * k / N ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsa : ∑ i, a i ^ 2 ≤ 1 := by
    rw [dotProduct_sum_orth q horth] at hz
    refine le_trans (Finset.sum_le_sum fun i _ ↦ ?_) hz
    nlinarith [(hq i).1, mul_self_nonneg (a i)]
  have ha : ∀ i, |a i| ≤ 1 := by
    intro i
    have h1 : a i ^ 2 ≤ 1 := le_trans
      (Finset.single_le_sum (f := fun i ↦ a i ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)) hsa
    exact (sq_le_one_iff_abs_le_one _).1 h1
  set m : Fin k → ℤ := fun i ↦ if 0 ≤ a i then ⌊(N : ℝ) * a i⌋ else ⌈(N : ℝ) * a i⌉ with hm
  have hm1 : ∀ i, |(m i : ℝ)| ≤ N * |a i| ∧ |(m i : ℝ) - N * a i| ≤ 1 := by
    intro i
    by_cases h : 0 ≤ a i
    · simp only [hm, h, ↓reduceIte]
      have h0 : 0 ≤ (N : ℝ) * a i := mul_nonneg (Nat.cast_nonneg _) h
      have f1 := Int.floor_le ((N : ℝ) * a i)
      have f2 := Int.lt_floor_add_one ((N : ℝ) * a i)
      have f0 : (0 : ℝ) ≤ ⌊(N : ℝ) * a i⌋ := by exact_mod_cast Int.floor_nonneg.2 h0
      rw [abs_of_nonneg f0, abs_of_nonneg h]
      exact ⟨f1, abs_le.2 ⟨by linarith, by linarith⟩⟩
    · simp only [hm, h, ↓reduceIte]
      replace h := not_le.1 h
      have h0 : (N : ℝ) * a i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) h.le
      have c1 := Int.le_ceil ((N : ℝ) * a i)
      have c2 := Int.ceil_lt_add_one ((N : ℝ) * a i)
      have c0' : ⌈(N : ℝ) * a i⌉ ≤ 0 := Int.ceil_le.2 (by simpa using h0)
      have c0 : (⌈(N : ℝ) * a i⌉ : ℝ) ≤ 0 := by exact_mod_cast c0'
      rw [abs_of_nonpos c0, abs_of_neg h]
      exact ⟨by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩
  have hmsq : ∀ i, ((m i : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 * a i ^ 2 := by
    intro i
    rw [← sq_abs, ← sq_abs (a i), ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hm1 i).1 2
  refine ⟨m, fun i ↦ ?_, ?_, ?_⟩
  · have h1 : |(m i : ℝ)| ≤ N := (hm1 i).1.trans (by
      have := mul_le_mul_of_nonneg_left (ha i) hN'.le
      linarith)
    have h2 : ((|m i| : ℤ) : ℝ) ≤ N := by rw [Int.cast_abs]; exact h1
    exact_mod_cast h2
  · calc ∑ i, ((m i : ℝ)) ^ 2 ≤ ∑ i, (N : ℝ) ^ 2 * a i ^ 2 := Finset.sum_le_sum fun i _ ↦ hmsq i
      _ = (N : ℝ) ^ 2 * ∑ i, a i ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (N : ℝ) ^ 2 * 1 := mul_le_mul_of_nonneg_left hsa (by positivity)
      _ = (N : ℝ) ^ 2 := mul_one _
  · rw [← Finset.sum_sub_distrib]
    have hsub : ∑ i, (((m i : ℝ) / N) • q i - a i • q i) = ∑ i, ((m i : ℝ) / N - a i) • q i :=
      Finset.sum_congr rfl fun i _ ↦ (sub_smul _ _ _).symm
    rw [hsub, dotProduct_sum_orth q horth]
    calc ∑ i, ((m i : ℝ) / N - a i) * ((m i : ℝ) / N - a i) * (q i ⬝ᵥ q i)
        ≤ ∑ _i : Fin k, (4 / N ^ 2 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have h1 : (m i : ℝ) / N - a i = ((m i : ℝ) - N * a i) / N := by field_simp
          have h2 : ((m i : ℝ) / N - a i) * ((m i : ℝ) / N - a i) ≤ 1 / N ^ 2 := by
            rw [h1, div_mul_div_comm, ← sq, ← sq_abs, div_le_div_iff₀ (by positivity)
              (by positivity)]
            have h3 := (hm1 i).2
            have h4 : |(m i : ℝ) - N * a i| ^ 2 ≤ 1 ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) h3 2
            nlinarith
          have h5 := (hq i).2
          calc ((m i : ℝ) / N - a i) * ((m i : ℝ) / N - a i) * (q i ⬝ᵥ q i)
              ≤ 1 / N ^ 2 * 4 := mul_le_mul h2 h5 (dot_self_nonneg _) (by positivity)
            _ = 4 / N ^ 2 := by ring
      _ = 4 * k / N ^ 2 := by simp [div_eq_mul_inv]; ring

/-! ### Gram–Schmidt residuals of a list of columns -/

/-- The Gram determinant `Δ_l` of the first `l` columns of `S`. -/
noncomputable def deltaR (col : ℕ → Fin n → ℝ) (S : List ℕ) (l : ℕ) : ℝ :=
  (gramF (colsL col (S.take l))).det

/-- The Gram–Schmidt vector `r_l`: the residual of the `l`-th column of `S` against the columns
before it. -/
noncomputable def gsR (col : ℕ → Fin n → ℝ) (S : List ℕ) (l : ℕ) : Fin n → ℝ :=
  resid (colsL col (S.take l)) (col (S.getD l 0))

variable (col : ℕ → Fin n → ℝ) (S : List ℕ)

theorem take_succ_eq (l : ℕ) (hl : l < S.length) :
    S.take (l + 1) = S.take l ++ [S.getD l 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hl, List.getD_eq_getElem _ _ hl]
  rfl

theorem deltaR_succ {l : ℕ} (hl : l < S.length) (hpos : 0 < deltaR col S l) :
    deltaR col S (l + 1) = deltaR col S l * (gsR col S l ⬝ᵥ gsR col S l) := by
  rw [deltaR, take_succ_eq S l hl, det_gramF_colsL_append, det_gramF_snocF _ hpos.ne']
  rfl

/-- `‖r_l‖² = Δ_(l+1) / Δ_l`. -/
theorem gsR_dot_self {l : ℕ} (hl : l < S.length) (hpos : 0 < deltaR col S l) :
    gsR col S l ⬝ᵥ gsR col S l = deltaR col S (l + 1) / deltaR col S l := by
  rw [deltaR_succ col S hl hpos]
  field_simp

theorem gsR_ne_zero {l : ℕ} (hl : l < S.length) (hpos : 0 < deltaR col S l)
    (hpos' : 0 < deltaR col S (l + 1)) : gsR col S l ≠ 0 := by
  intro h
  rw [deltaR_succ col S hl hpos, h, dotProduct_zero, mul_zero] at hpos'
  exact lt_irrefl _ hpos'

/-- Columns of a list are orthogonal to the residuals against it. -/
theorem dot_resid_of_mem {L : List ℕ} (hL : (gramF (colsL col L)).det ≠ 0) {s : ℕ} (hs : s ∈ L)
    (y : Fin n → ℝ) : col s ⬝ᵥ resid (colsL col L) y = 0 := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  exact col_dotProduct_resid (colsL col L) hL y ⟨j, hj⟩

/-- **The Gram–Schmidt vectors are orthogonal.** -/
theorem gsR_orth (hpos : ∀ l ≤ S.length, 0 < deltaR col S l) {l m : ℕ} (hlm : l < m)
    (hm : m < S.length) : gsR col S l ⬝ᵥ gsR col S m = 0 := by
  have hdet : (gramF (colsL col (S.take m))).det ≠ 0 := (hpos m hm.le).ne'
  have hmem : ∀ s ∈ S.take l, s ∈ S.take m := fun s hs ↦
    (List.take_prefix_take_left (l := S) hlm.le).subset hs
  have hl : l < S.length := hlm.trans hm
  have hSl : S.getD l 0 ∈ S.take m := by
    rw [List.getD_eq_getElem _ _ hl]
    exact List.mem_take_iff_getElem.2 ⟨l, by simp [hlm, hl], rfl⟩
  rw [gsR, gsR, resid, sub_dotProduct, dot_resid_of_mem col hdet hSl, combF_dotProduct]
  simp only [zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  have hj : (S.take l)[j] ∈ S.take m := hmem _ (List.getElem_mem _)
  rw [colsL, dot_resid_of_mem col hdet hj, mul_zero]

/-- **The projection in Gram–Schmidt coordinates**: `y - resid_S y = ∑_l (r_l ⬝ y / ‖r_l‖²) r_l`. -/
theorem sub_resid_eq_sum (hpos : ∀ l ≤ S.length, 0 < deltaR col S l) (y : Fin n → ℝ) :
    y - resid (colsL col S) y = ∑ l ∈ Finset.range S.length,
      ((gsR col S l ⬝ᵥ y) / (gsR col S l ⬝ᵥ gsR col S l)) • gsR col S l := by
  have key : ∀ m ≤ S.length, y - resid (colsL col (S.take m)) y = ∑ l ∈ Finset.range m,
      ((gsR col S l ⬝ᵥ y) / (gsR col S l ⬝ᵥ gsR col S l)) • gsR col S l := by
    intro m
    induction m with
    | zero => intro _; rw [List.take_zero, resid_nil, sub_self, Finset.sum_range_zero]
    | succ m ih =>
      intro hm
      have hml : m < S.length := hm
      have hdet : (gramF (colsL col (S.take m))).det ≠ 0 := (hpos m hml.le).ne'
      have hdet' : (gramF (colsL col (S.take m ++ [S.getD m 0]))).det ≠ 0 := by
        rw [← take_succ_eq S m hml]; exact (hpos (m + 1) hm).ne'
      have hne := gsR_ne_zero col S hml (hpos m hml.le) (hpos (m + 1) hm)
      rw [Finset.sum_range_succ, ← ih hml.le, take_succ_eq S m hml,
        resid_colsL_append col _ _ hdet', resid_snocF _ hdet hne]
      simp only [gsR]
      abel
  have := key S.length le_rfl
  rwa [List.take_length] at this

/-- The projection is no longer than the vector. -/
theorem sub_resid_dot_self_le {L : List ℕ} (hL : (gramF (colsL col L)).det ≠ 0)
    (y : Fin n → ℝ) :
    (y - resid (colsL col L) y) ⬝ᵥ (y - resid (colsL col L) y) ≤ y ⬝ᵥ y := by
  have h : y - resid (colsL col L) y = combF (colsL col L) (coefF (colsL col L) y) := by
    rw [resid, sub_sub_cancel]
  have hy : y = (y - resid (colsL col L) y) + resid (colsL col L) y := by abel
  conv_rhs => rw [hy]
  rw [add_dotProduct, dotProduct_add, dotProduct_add, h, combF_dotProduct_resid _ hL,
    resid_dotProduct_combF _ hL]
  have := dot_self_nonneg (resid (colsL col L) y)
  linarith

end Net

end BHSV25
