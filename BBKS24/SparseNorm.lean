module

public import BBKS24.SparseNorm.Core
public import BBKS24.SparseNorm.Params
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Sparse operator norms, and few large correlations

The one heavy ingredient of [BBKS24]: a random matrix whose rows are independent samples of a
bounded orthonormal system has small operator norm on all sparse vectors at once, and then no
vector correlates with many of its columns.

In the paper (§3, and §4 for general `p`), the rows are indexed by the vertices `i ∉ S*` and the
columns by the triples `α ⊆ S*`, with entries `∏_{a ∈ α} G(a, i)`: products of the `p`-biased
characters of the random edges between `S*` and the rest. The rows are independent, and within a
row the entries are orthonormal and bounded. Every vertex `j ∉ S*` gives a vector `u`, the row of
`j` outside `S*`, which the adversary chooses after seeing the random edges, so the bound must
hold for every `u` at once.

## Main results

* `BBKS24.SparseNorm.card_lt_of_sparseNormLE` [BBKS24, Lemma 3.3]: if `‖A v‖² ≤ c ‖v‖²` for every
  `s`-sparse `v`, then a vector `u` with entries at most `B` in absolute value has correlation at
  least `τ` with fewer than `s` columns of `A`, provided `c B² |R| < s τ²`, where `|R|` is the
  number of rows. Deterministic, proved here.
* `BBKS24.SparseNorm.sparse_norm_bound` [BBKS24, Theorem 2.6, Lemma 3.4]: for `m` independent
  rows of a bounded orthonormal system with `N` functions bounded by `K`, if
  `m ≥ C K² s log⁴(N + 2) log(2/δ)`, then with probability at least `1 - δ` every `s`-sparse
  vector `v` has `‖A v‖² ≤ 2 m ‖v‖²`, with `C = 10⁹`. Proved, following Haviv–Regev (below).
* `BBKS24.SparseNorm.few_large_correlations`: the two together. With probability at least
  `1 - δ`, every vector with entries at most `B` has correlation at least `τ` with fewer than `s`
  columns, when `2 m² B² < s τ²`.

## The form of `sparse_norm_bound`

It is the upper half of the restricted isometry property, with constant `2`, which is all that
Lemma 3.3 needs. Its hypotheses are chosen so that it follows from either of two known proofs:

* Rudelson–Vershynin, as in [FR13, Theorems 12.31, 12.32], which [BBKS24] cites (its Theorem 2.6
  states `m ≥ O(r K² log³ r log N)`, with failure probability `N^(-log³ r)`, which follows from
  Theorem 12.32 when `log(K² r log N) = O(log r)`, as in its application). Theorem 12.32 has
  `m ≥ C K² s max(log² s · log(K² s log N) · log N, log(1/δ))`. It uses symmetrization,
  Rudelson's lemma, Dudley's entropy integral and Maurey's empirical method.
* Haviv–Regev [HR17, Section 3, Theorem 3.7], proved for subsampled unitary matrices with bounded
  entries, with `m ≥ C K² s log²(K² s) log N`. The proof is elementary (multiplicative Chernoff
  bounds, Markov's inequality, Maurey-style sampling of columns, and union bounds over nets at
  several scales) and carries over to independent rows from any distribution and to rectangular
  matrices: the nets are counted by columns, and rows only enter through averages. This is the
  proof formalized here.

The factor `log⁴(N + 2) log(2/δ)` is at least both bounds, up to constants, once `K² ≤ N + 2`
(and `s ≤ N`, which loses nothing). The hypothesis `K² ≤ N + 2` is needed only for the
Haviv–Regev route, whose bound grows with `log K`. In [BBKS24], `N` is the number of triples in
`S*`, and `K² = max(1, (p/(1 - p))³)` is at most `k^(3/4)` under the size condition, so the
hypothesis costs nothing there. The logarithm `log⁴ N` matches the paper's threshold: with
`s ≈ n²/k²` and `m ≈ n`, it asks for `k ≳ √n log² n`.

## The proof

Following [HR17, Section 3], one-sided, in `BBKS24/SparseNorm/`:

* `Tail.lean`: means on finite types; Chernoff's multiplicative upper tail for independent rows
  (`BBKS24.SparseNorm.chernoff`); Hoeffding for independent samples.
* `Maurey.lean`: Maurey's empirical method [HR17, Lemma 3.5]
  (`BBKS24.SparseNorm.exists_approx`).
* `Levels.lean`: the levels `2^(-i/2)` and the pieces of `f²` [HR17, Lemma 3.6], deterministic.
* `Core.lean`: the Chernoff event over all nets of pieces, its probability
  (`BBKS24.SparseNorm.prob_not_chernoffEvent`), and on it the bound for every `f_w` with
  `‖w‖₁ = 1` (`BBKS24.SparseNorm.sum_sq_le_of_chernoffEvent`) [HR17, Theorem 3.1, upper half].
* `Params.lean`: `t = ⌈10 log(N + 2)⌉` levels, `⌈8800 · 2^j log(N + 2)⌉` samples at level `j`,
  and the arithmetic.
* Here: `w = v / ‖v‖₁` for an `s`-sparse `v`, with `‖v‖₁² ≤ s ‖v‖₂²`
  (`BBKS24.SparseNorm.sparseNormLE_of_forall`) [HR17, Theorem 3.7].

## References

* [BBKS24] J. Błasiok, R.-D. Buhai, P. K. Kothari, D. Steurer, *Semirandom planted clique and the
  restricted isometry property*, FOCS 2024, arXiv:2404.14159 (v2).
* [FR13] S. Foucart, H. Rauhut, *A Mathematical Introduction to Compressive Sensing*, Birkhäuser
  2013, Chapter 12.
* [HR17] I. Haviv, O. Regev, *The restricted isometry property of subsampled Fourier matrices*,
  GAFA Seminar 2014–2016 (2017), arXiv:1507.01768.
-/

@[expose] public section

namespace BBKS24.SparseNorm

open Finset MeasureTheory

variable {R ι : Type*} [Fintype R] [Fintype ι]

/-- `‖A v‖² ≤ c ‖v‖²` for every `s`-sparse vector `v`: the `s`-sparse operator norm of the
matrix `A` (rows `R`, columns `ι`) is at most `√c`. -/
def SparseNormLE (A : R → ι → ℝ) (s : ℕ) (c : ℝ) : Prop :=
  ∀ v : ι → ℝ, (univ.filter fun α ↦ v α ≠ 0).card ≤ s →
    ∑ i, (∑ α, A i α * v α) ^ 2 ≤ c * ∑ α, v α ^ 2

/-- **Few large correlations** [BBKS24, Lemma 3.3]. If the `s`-sparse operator norm of `A` is at
most `√c`, then a vector `u` with entries at most `B` in absolute value has correlation
`⟨A_α, u⟩ ≥ τ` with fewer than `s` columns `α` of `A`, provided `c B² |R| < s τ²`.

Proof: if `s` columns `T` had correlation at least `τ`, then for the indicator `v` of `T`,
`s τ ≤ ⟨A v, u⟩ ≤ ‖A v‖ ‖u‖ ≤ √(c s) · B √|R|` by Cauchy–Schwarz. -/
theorem card_lt_of_sparseNormLE {A : R → ι → ℝ} {s : ℕ} {c : ℝ} (hA : SparseNormLE A s c)
    (hc : 0 ≤ c) {u : R → ℝ} {B τ : ℝ} (hu : ∀ i, |u i| ≤ B) (hτ : 0 < τ)
    (hs : c * B ^ 2 * Fintype.card R < s * τ ^ 2) :
    (univ.filter fun α ↦ τ ≤ ∑ i, A i α * u i).card < s := by
  classical
  by_contra! h
  obtain ⟨T, hT, hTs⟩ := exists_subset_card_eq h
  set v : ι → ℝ := fun α ↦ if α ∈ T then 1 else 0
  have hsupp : (univ.filter fun α ↦ v α ≠ 0) = T := by
    ext α
    simp [v]
  have hv2 : ∑ α, v α ^ 2 = s := by
    simp [v, ← hTs]
  have hnorm : ∑ i, (∑ α, A i α * v α) ^ 2 ≤ c * s := by
    rw [← hv2]
    exact hA v (hsupp ▸ hTs.le)
  -- The correlation of `A v` with `u` is at least `s τ`.
  have hcorr : s * τ ≤ ∑ i, u i * ∑ α, A i α * v α := by
    calc (s : ℝ) * τ = ∑ _α ∈ T, τ := by rw [sum_const, hTs, nsmul_eq_mul]
      _ ≤ ∑ α ∈ T, ∑ i, A i α * u i := sum_le_sum fun α hα ↦ (mem_filter.1 (hT hα)).2
      _ = ∑ α, v α * ∑ i, A i α * u i := by
          simp only [v, ite_mul, one_mul, zero_mul]
          rw [sum_ite_mem, univ_inter]
      _ = ∑ i, u i * ∑ α, A i α * v α := by
          simp_rw [mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun i _ ↦ sum_congr rfl fun α _ ↦ by ring
  have hu2 : ∑ i, u i ^ 2 ≤ B ^ 2 * Fintype.card R := by
    calc ∑ i, u i ^ 2 ≤ ∑ _i : R, B ^ 2 := sum_le_sum fun i _ ↦ by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hu i) 2
      _ = B ^ 2 * Fintype.card R := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]
  -- Cauchy–Schwarz.
  have hCS : ((s : ℝ) * τ) ^ 2 ≤ B ^ 2 * Fintype.card R * (c * s) :=
    calc ((s : ℝ) * τ) ^ 2 ≤ (∑ i, u i * ∑ α, A i α * v α) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hcorr 2
      _ ≤ (∑ i, u i ^ 2) * ∑ i, (∑ α, A i α * v α) ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ B ^ 2 * Fintype.card R * (c * s) :=
          mul_le_mul hu2 hnorm (sum_nonneg fun _ _ ↦ sq_nonneg _) (by positivity)
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · rw [hs0, Nat.cast_zero, zero_mul] at hs
    have : 0 ≤ c * B ^ 2 * Fintype.card R := by positivity
    linarith
  · have hs0' : (0 : ℝ) < s := Nat.cast_pos.2 hs0
    have := mul_lt_mul_of_pos_left hs hs0'
    nlinarith

/-! ### Proof of the sparse norm bound -/

section Proof

theorem SparseNormLE.of_min {A : R → ι → ℝ} {s : ℕ} {c : ℝ}
    (h : SparseNormLE A (min s (Fintype.card ι)) c) : SparseNormLE A s c := fun v hv ↦
  h v (le_min hv ((card_filter_le _ _).trans_eq card_univ))

theorem sparseNormLE_zero (A : R → ι → ℝ) (c : ℝ) : SparseNormLE A 0 c := by
  intro v hv
  have hv0 : ∀ α, v α = 0 := by
    intro α
    by_contra h
    have : 0 < (univ.filter fun α ↦ v α ≠ 0).card := card_pos.2 ⟨α, by simp [h]⟩
    omega
  simp [hv0]

theorem sparseNormLE_of_isEmpty [IsEmpty ι] (A : R → ι → ℝ) (s : ℕ) (c : ℝ) :
    SparseNormLE A s c := by
  intro v _
  simp

omit [Fintype R] in
/-- Cauchy–Schwarz on the support: `‖v‖₁² ≤ s ‖v‖₂²` for an `s`-sparse vector `v`. -/
theorem sq_sum_abs_le {v : ι → ℝ} {s : ℕ} (hv : (univ.filter fun a ↦ v a ≠ 0).card ≤ s) :
    (∑ a, |v a|) ^ 2 ≤ s * ∑ a, v a ^ 2 := by
  classical
  set T := univ.filter fun a ↦ v a ≠ 0
  have h1 : ∑ a, |v a| = ∑ a ∈ T, |v a| * 1 := by
    rw [← sum_filter_of_ne fun a _ h ↦ abs_ne_zero.1 h]
    simp [T]
  calc (∑ a, |v a|) ^ 2 = (∑ a ∈ T, |v a| * 1) ^ 2 := by rw [h1]
    _ ≤ (∑ a ∈ T, |v a| ^ 2) * ∑ a ∈ T, (1 : ℝ) ^ 2 := sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ a, v a ^ 2) * s := by
        gcongr
        · simp only [sq_abs]
          exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ sq_nonneg _
        · simp only [one_pow, sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast hv
    _ = s * ∑ a, v a ^ 2 := mul_comm _ _

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

omit [Fintype R] [MeasurableSingletonClass X] in
/-- For orthonormal `φ`, `E (∑ₐ v a φ a)² = ∑ₐ v a²`. -/
theorem mean_sq_sum (μ : Measure X) [DecidableEq ι] {φ : ι → X → ℝ}
    (hφ : ∀ α β, mean μ (fun x ↦ φ α x * φ β x) = if α = β then 1 else 0) (v : ι → ℝ) :
    mean μ (fun x ↦ (∑ a, φ a x * v a) ^ 2) = ∑ a, v a ^ 2 := by
  have : ∀ x, (∑ a, φ a x * v a) ^ 2 = ∑ a, ∑ b, (v a * v b) * (φ a x * φ b x) := by
    intro x
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun a _ ↦ sum_congr rfl fun b _ ↦ by ring
  simp_rw [this]
  rw [mean_finsetSum]
  simp_rw [mean_finsetSum, mean_const_mul, hφ]
  simp [mul_ite, sq]

omit [MeasurableSingletonClass X] in
/-- **From all `w` to sparse vectors.** The bound of `BBKS24.SparseNorm.sum_sq_le_of_chernoffEvent`
for every `w` with `∑ |w| = 1`, for the normalized columns `φ / K`, gives the `s`-sparse norm
bound `2 |R|` once its additive error `E` is at most `0.35 / (s K²)`: apply it to `w = v / ‖v‖₁`,
for which `E f_w² = ‖v‖₂² / (K ‖v‖₁)² ≥ 1 / (s K²)` by Cauchy–Schwarz. -/
theorem sparseNormLE_of_forall (μ : Measure X) [IsProbabilityMeasure μ] [DecidableEq ι]
    {φ : ι → X → ℝ} {K : ℝ} (hK : 0 < K)
    (hφ : ∀ α β, mean μ (fun x ↦ φ α x * φ β x) = if α = β then 1 else 0)
    {s : ℕ} (hs : 1 ≤ s) {g : R → X} {E : ℝ} (hE : E ≤ 35 / 100 / (s * K ^ 2))
    (h : ∀ w : ι → ℝ, ∑ a, |w a| = 1 → ∑ r, comb (fun a x ↦ φ a x / K) w (g r) ^ 2 ≤
      Fintype.card R * (1331 / 810 * mean μ (fun x ↦ comb (fun a x ↦ φ a x / K) w x ^ 2) + E)) :
    SparseNormLE (fun r α ↦ φ α (g r)) s (2 * Fintype.card R) := by
  intro v hv
  change ∑ r, (∑ α, φ α (g r) * v α) ^ 2 ≤ 2 * (Fintype.card R : ℝ) * ∑ α, v α ^ 2
  set n1 := ∑ a, |v a| with hn1
  have hn10 : 0 ≤ n1 := sum_nonneg fun a _ ↦ abs_nonneg (v a)
  rcases hn10.eq_or_lt with h0 | hpos
  · have hv0 : ∀ a, v a = 0 := fun a ↦ abs_eq_zero.1
      ((sum_eq_zero_iff_of_nonneg fun a _ ↦ abs_nonneg (v a)).1 h0.symm a (mem_univ a))
    simp [hv0]
  set w : ι → ℝ := fun a ↦ v a / n1 with hwdef
  have hw : ∑ a, |w a| = 1 := by
    simp only [hwdef, abs_div, abs_of_pos hpos, ← sum_div]
    exact div_self hpos.ne'
  have hcomb : ∀ x, comb (fun a x ↦ φ a x / K) w x = (K * n1)⁻¹ * ∑ a, φ a x * v a := by
    intro x
    simp only [comb, hwdef, mul_sum]
    exact sum_congr rfl fun a _ ↦ by field_simp
  set V := ∑ a, v a ^ 2 with hV
  have hM : mean μ (fun x ↦ comb (fun a x ↦ φ a x / K) w x ^ 2) = ((K * n1) ^ 2)⁻¹ * V := by
    simp_rw [hcomb, mul_pow, inv_pow]
    rw [mean_const_mul, mean_sq_sum μ hφ v]
    ring
  have hCS : n1 ^ 2 ≤ s * V := sq_sum_abs_le hv
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  set c := ((K * n1) ^ 2)⁻¹ * V with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ V := sum_nonneg fun a _ ↦ sq_nonneg (v a)
    positivity
  have hE' : E ≤ 35 / 100 * c := by
    refine hE.trans ?_
    have key : c = V / (K ^ 2 * n1 ^ 2) := by rw [hc, mul_pow, inv_mul_eq_div]
    rw [key, div_eq_mul_one_div (35 / 100 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hK2 : 0 < K ^ 2 := by positivity
    nlinarith
  have hmain := h w hw
  rw [hM] at hmain
  have hsum : ∑ r, (∑ α, φ α (g r) * v α) ^ 2 =
      (K * n1) ^ 2 * ∑ r, comb (fun a x ↦ φ a x / K) w (g r) ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun r _ ↦ ?_
    have := hK.ne'
    have := hpos.ne'
    rw [hcomb]
    field_simp
  rw [hsum]
  have hq0 : (0 : ℝ) ≤ Fintype.card R := Nat.cast_nonneg _
  calc (K * n1) ^ 2 * ∑ r, comb (fun a x ↦ φ a x / K) w (g r) ^ 2
      ≤ (K * n1) ^ 2 * (Fintype.card R * (1331 / 810 * c + E)) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ ≤ (K * n1) ^ 2 * (Fintype.card R * (2 * c)) := by
        gcongr
        linarith
    _ = 2 * Fintype.card R * V := by
        rw [hc]
        field_simp

end Proof

/-- **Sparse operator norms of random matrices with orthonormal columns** [BBKS24, Theorem 2.6,
Lemma 3.4], from [FR13, Theorem 12.32] or [HR17, Theorem 3.7] (see the module docstring).

Let `φ α`, for `α` in a set of `N` indices, be orthonormal functions in `L²(μ)` bounded by `K`,
with `K² ≤ N + 2`, and let `g i`, `i ∈ R`, be independent samples of `μ`. If
`|R| ≥ C K² s log⁴(N + 2) log(2/δ)`, then with probability at least `1 - δ` the matrix
`A i α = φ α (g i)` has `‖A v‖² ≤ 2 |R| ‖v‖²` for every `s`-sparse vector `v`. -/
theorem sparse_norm_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X ι R : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
        [Fintype ι] [DecidableEq ι] [Fintype R] (μ : Measure X) [IsProbabilityMeasure μ]
        (φ : ι → X → ℝ) (K δ : ℝ) (s : ℕ),
        (∀ α β, ∫ x, φ α x * φ β x ∂μ = if α = β then 1 else 0) →
        (∀ α x, |φ α x| ≤ K) → K ^ 2 ≤ Fintype.card ι + 2 →
        0 < δ → δ ≤ 1 →
        C * K ^ 2 * s * Real.log (Fintype.card ι + 2) ^ 4 * Real.log (2 / δ) ≤
          Fintype.card R →
        1 - δ ≤ (Measure.infinitePi fun _ : R ↦ μ).real
          {g | SparseNormLE (fun i α ↦ φ α (g i)) s (2 * Fintype.card R)} := by
  refine ⟨10 ^ 9, by norm_num, ?_⟩
  intro X ι R _ _ _ _ _ _ μ _ φ K δ s hφ hK hKN hδ hδ1 hm
  classical
  set P := Measure.infinitePi fun _ : R ↦ μ with hP
  have huniv : (∀ g : R → X, SparseNormLE (fun i α ↦ φ α (g i)) s (2 * Fintype.card R)) →
      1 - δ ≤ P.real {g | SparseNormLE (fun i α ↦ φ α (g i)) s (2 * Fintype.card R)} := by
    intro hall
    have hset : {g : R → X | SparseNormLE (fun i α ↦ φ α (g i)) s (2 * Fintype.card R)} =
        Set.univ := Set.eq_univ_of_forall hall
    rw [hset, probReal_univ]
    linarith
  -- The trivial cases.
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hι | hι
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hι
    exact huniv fun g ↦ sparseNormLE_of_isEmpty _ _ _
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · subst hs0
    exact huniv fun g ↦ sparseNormLE_zero _ _
  -- Reduce to the sparsity `s' = min s N ≤ N`.
  set N := Fintype.card ι with hNdef
  set s' := min s N with hs'
  have hs'1 : 1 ≤ s' := le_min hs0 hι
  have hs'N : s' ≤ N := min_le_right _ _
  have hs's : s' ≤ s := min_le_left _ _
  have hN1 : 1 ≤ N := hι
  -- `K ≥ 1`.
  have : Nonempty X := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact IsProbabilityMeasure.ne_zero μ (Measure.eq_zero_of_isEmpty μ)
  have hφm : ∀ α β, mean μ (fun x ↦ φ α x * φ β x) = if α = β then 1 else 0 := fun α β ↦ by
    rw [← integral_eq_mean]
    exact hφ α β
  obtain ⟨α₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 hι
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK α₀ x₀)
  have hK1 : 1 ≤ K ^ 2 := by
    have h1 := hφm α₀ α₀
    rw [ite_eq_left rfl] at h1
    rw [← h1]
    refine mean_le_of_le μ fun x ↦ ?_
    rw [← sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hK α₀ x) 2
  have hKpos : 0 < K := by nlinarith
  -- The normalized columns and the parameters.
  set ψ : ι → X → ℝ := fun a x ↦ φ a x / K with hψdef
  have hψ : ∀ a x, |ψ a x| ≤ 1 := fun a x ↦ by
    rw [hψdef, abs_div, abs_of_pos hKpos, div_le_one hKpos]
    exact hK a x
  set Q : ℝ := s' * K ^ 2 with hQdef
  have hs'R : (1 : ℝ) ≤ s' := by exact_mod_cast hs'1
  have hQ0 : 0 < Q := by positivity
  have hQN : Q ≤ ((N : ℝ) + 2) ^ 2 := by
    have h1 : (s' : ℝ) ≤ N := by exact_mod_cast hs'N
    have h2 : K ^ 2 ≤ (N : ℝ) + 2 := hKN
    calc Q = s' * K ^ 2 := rfl
      _ ≤ N * ((N : ℝ) + 2) := mul_le_mul h1 h2 (by positivity) (by positivity)
      _ ≤ ((N : ℝ) + 2) ^ 2 := by nlinarith
  set t := nLevels N with htdef
  set L := nSamples N with hLdef
  set α : ℝ := 1 / Q / 20 / t with hαdef
  set β : ℝ := 1 / Q / 40 with hβdef
  have ht1 : 1 ≤ t := one_le_nLevels hN1
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  have hβ : ∀ j < t, 4 * Real.exp (-(L j * (lvl j / 10) ^ 2) / 8) ≤ β / t :=
    fun j _ ↦ maurey_le hN1 hQ0 hQN j
  have hq : 10 ^ 9 * Q * Real.log (N + 2) ^ 4 * Real.log (2 / δ) ≤ Fintype.card R := by
    have hD : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    have : (s' : ℝ) ≤ s := by exact_mod_cast hs's
    calc 10 ^ 9 * Q * Real.log (N + 2) ^ 4 * Real.log (2 / δ) =
          10 ^ 9 * K ^ 2 * s' * Real.log (N + 2) ^ 4 * Real.log (2 / δ) := by
          rw [hQdef]
          ring
      _ ≤ 10 ^ 9 * K ^ 2 * s * Real.log (N + 2) ^ 4 * Real.log (2 / δ) := by gcongr
      _ ≤ Fintype.card R := hm
  -- The Chernoff event is likely.
  have hprob : P.real {g | ¬ ChernoffEvent μ (signed ψ) L t α g} ≤ δ := by
    refine (prob_not_chernoffEvent μ (signed ψ) L t α).trans ?_
    have hcard : (Fintype.card (Fin N × Bool) : ℝ) = ((2 * N : ℕ) : ℝ) := by
      simp [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
    rw [hcard]
    exact sum_chernoff_le hN1 hQ0 hδ hδ1 hq
  -- On the Chernoff event, the sparse norm bound holds.
  have hsub : {g : R → X | ChernoffEvent μ (signed ψ) L t α g} ⊆
      {g | SparseNormLE (fun i α ↦ φ α (g i)) s' (2 * Fintype.card R)} := by
    intro g hg
    have hE : 5324 / 1000 * β + 121 / 100 * t * α + 242 / 100 * (1 / 2) ^ t ≤
        35 / 100 / (s' * K ^ 2) := by
      have h2t := le_two_pow_nLevels hN1
      have hpow : ((1 : ℝ) / 2) ^ t ≤ 1 / (20 * Q) := by
        rw [one_div_pow, one_div_le_one_div (by positivity) (by positivity)]
        nlinarith
      have htα : (t : ℝ) * α = 1 / (20 * Q) := by
        rw [hαdef]
        field_simp
      rw [← hQdef, mul_assoc (121 / 100 : ℝ), htα, hβdef]
      have : 0 < 1 / Q := by positivity
      calc 5324 / 1000 * (1 / Q / 40) + 121 / 100 * (1 / (20 * Q)) + 242 / 100 * (1 / 2) ^ t
          ≤ 5324 / 1000 * (1 / Q / 40) + 121 / 100 * (1 / (20 * Q)) +
            242 / 100 * (1 / (20 * Q)) := by gcongr
        _ ≤ 35 / 100 / Q := by
            field_simp
            norm_num
    exact sparseNormLE_of_forall μ hKpos hφm hs'1 hE fun w hw ↦
      (sum_sq_le_of_chernoffEvent μ hψ (nSamples_pos hN1) ht1 hβ hg w hw).trans_eq (by ring)
  -- Conclude.
  have hcompl := probReal_compl_eq_one_sub (μ := P)
    (s := {g : R → X | ChernoffEvent μ (signed ψ) L t α g}) MeasurableSet.of_discrete
  rw [Set.compl_ofPred] at hcompl
  calc 1 - δ ≤ P.real {g : R → X | ChernoffEvent μ (signed ψ) L t α g} := by linarith
    _ ≤ P.real {g | SparseNormLE (fun i α ↦ φ α (g i)) s' (2 * Fintype.card R)} :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real {g | SparseNormLE (fun i α ↦ φ α (g i)) s (2 * Fintype.card R)} :=
        measureReal_mono (fun g hg ↦ SparseNormLE.of_min hg) (measure_ne_top _ _)

/-- **Few large correlations, with high probability**: `sparse_norm_bound` and
`card_lt_of_sparseNormLE` together. With probability at least `1 - δ` over the rows, every
vector `u` with entries at most `B` in absolute value (possibly chosen after seeing the rows) has
correlation `⟨A_α, u⟩ ≥ τ` with fewer than `s` columns `α`, when `2 |R|² B² < s τ²`. -/
theorem few_large_correlations :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X ι R : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
        [Fintype ι] [DecidableEq ι] [Fintype R] (μ : Measure X) [IsProbabilityMeasure μ]
        (φ : ι → X → ℝ) (K δ B τ : ℝ) (s : ℕ),
        (∀ α β, ∫ x, φ α x * φ β x ∂μ = if α = β then 1 else 0) →
        (∀ α x, |φ α x| ≤ K) → K ^ 2 ≤ Fintype.card ι + 2 →
        0 < δ → δ ≤ 1 →
        C * K ^ 2 * s * Real.log (Fintype.card ι + 2) ^ 4 * Real.log (2 / δ) ≤
          Fintype.card R →
        0 < τ → 2 * Fintype.card R * B ^ 2 * Fintype.card R < s * τ ^ 2 →
        1 - δ ≤ (Measure.infinitePi fun _ : R ↦ μ).real
          {g | ∀ u : R → ℝ, (∀ i, |u i| ≤ B) →
            (univ.filter fun α ↦ τ ≤ ∑ i, φ α (g i) * u i).card < s} := by
  obtain ⟨C, hC, h⟩ := sparse_norm_bound
  refine ⟨C, hC, fun μ _ φ K δ B τ s hφ hK hKN hδ hδ1 hm hτ hs ↦ ?_⟩
  refine (h μ φ K δ s hφ hK hKN hδ hδ1 hm).trans (measureReal_mono fun g hg u hu ↦ ?_)
  exact card_lt_of_sparseNormLE hg (by positivity) hu hτ hs

end BBKS24.SparseNorm
