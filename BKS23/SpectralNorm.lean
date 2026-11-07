module

public import BKS23.SpectralDefs
public import BKS23.RandomCut
public import BKS23.SpectralWalks

/-!
# The spectral norm of the cut of a random graph

[BKS23, Fact 3.14] for the matrix of the cut: the `p`-biased characters
`H_uv = χ_q(u ∼ v)` (`u ∈ U`, `v ∉ U`) of `G(n, q)` are independent, with mean `0`, variance `1`
and `|H_uv|² ≤ charMax q`, and if `charMax q` is small compared to `n` the matrix has norm
`O(√n)` with high probability. In terms of the centred matrix `M = √(q(1-q)) H`:
`BKS23.Spectral.prob_not_normLE`.

The proof is the moment method: `‖H y‖^(2r) ≤ ‖y‖^(2r) tr(X^(2r))` for the symmetric matrix `X`
of the cut (`BKS23.Spectral.cutMatrix`) and `r` a power of two
(`BKS23.Spectral.pow_dotProduct_le`), so the norm is small unless `tr(X^(2r)) > (18 n)^r`
(`BKS23.Spectral.normLE_of_trace_le`); and `E tr(X^(2r)) ≤ n (9n)^r` when
`charMax q (2r + 1)^4 ≤ n` (`BKS23.Spectral.integral_trace_le` with
`BKS23.Spectral.Walk.bound_le`), by counting closed walks in which every edge is traversed at least
twice (`BKS23/SpectralWalks.lean`). Markov's inequality concludes.

* **The matrix inequality.** For symmetric `N`, `⟨y, N y⟩² ≤ ‖y‖² ⟨y, N² y⟩` by Cauchy–Schwarz;
  iterating from `N = X²` gives `‖X y‖^(2r) ≤ ‖y‖^(2(r-1)) ‖X^r y‖²`, and
  `‖X^r y‖² ≤ ‖X^r‖_F² ‖y‖² = tr(X^(2r)) ‖y‖²`.
* **Walks.** `(X^t)_ac` times the product of `X` along a walk is the sum over its extensions by
  one step of the same with `t - 1` (`BKS23.Spectral.walkProd_mul_pow_succ`). The product along
  a walk of the coins of `G(n, q)` is `∏_e χ(ω_e)^(m_e)` over the pairs `e`, with `m_e` the number
  of traversals, and its mean is `∏_e E χ^(m_e)` (`BKS23.Spectral.integral_walkProd`), which is
  `0` if some `m_e = 1` and at most `∏_e K^(m_e - 2)` otherwise.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory unitInterval SimpleGraph Finset Matrix

namespace BKS23.Spectral

variable {n : ℕ}

/-! ### Powers of symmetric matrices -/

section Powers

variable {X : Matrix (Fin n) (Fin n) ℝ}

theorem dotProduct_self_nonneg (u : Fin n → ℝ) : 0 ≤ u ⬝ᵥ u :=
  sum_nonneg fun i _ ↦ mul_self_nonneg (u i)

theorem dotProduct_mulVec_of_isSymm (hX : X.IsSymm) (u v : Fin n → ℝ) :
    u ⬝ᵥ (X *ᵥ v) = (X *ᵥ u) ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hX.eq]

/-- **Cauchy–Schwarz** for the dot product. -/
theorem sq_dotProduct_le (u v : Fin n → ℝ) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  have h := sum_mul_sq_le_sq_mul_sq univ u v
  simp only [dotProduct, ← sq]
  exact h

/-- `‖N y‖² ≤ ‖N‖_F² ‖y‖²`. -/
theorem dotProduct_mulVec_self_le (N : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    (N *ᵥ y) ⬝ᵥ (N *ᵥ y) ≤ (∑ i, ∑ j, N i j ^ 2) * (y ⬝ᵥ y) := by
  rw [sum_mul]
  refine sum_le_sum fun i _ ↦ ?_
  have h := sq_dotProduct_le (N i) y
  simp only [mulVec, ← sq]
  calc (N i ⬝ᵥ y) ^ 2 ≤ (N i ⬝ᵥ N i) * (y ⬝ᵥ y) := h
    _ = (∑ j, N i j ^ 2) * (y ⬝ᵥ y) := by simp only [dotProduct, ← sq]

/-- For symmetric `N`, `tr(N²) = ‖N‖_F²`. -/
theorem trace_mul_self_of_isSymm {N : Matrix (Fin n) (Fin n) ℝ} (hN : N.IsSymm) :
    (N * N).trace = ∑ i, ∑ j, N i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [hN.apply j i, sq]

theorem trace_pow_two_mul_nonneg (hX : X.IsSymm) (k : ℕ) : 0 ≤ (X ^ (2 * k)).trace := by
  rw [two_mul, pow_add, trace_mul_self_of_isSymm (hX.pow k)]
  positivity

/-- One step of the iteration: `‖X^(2^i) y‖⁴ ≤ ‖y‖² ‖X^(2^(i+1)) y‖²`. -/
theorem sq_dotProduct_pow_le (hX : X.IsSymm) (y : Fin n → ℝ) (i : ℕ) :
    ((X ^ 2 ^ i *ᵥ y) ⬝ᵥ (X ^ 2 ^ i *ᵥ y)) ^ 2 ≤
      (y ⬝ᵥ y) * ((X ^ 2 ^ (i + 1) *ᵥ y) ⬝ᵥ (X ^ 2 ^ (i + 1) *ᵥ y)) := by
  have hsq : X ^ 2 ^ (i + 1) = X ^ 2 ^ i * X ^ 2 ^ i := by rw [← pow_add, pow_succ, mul_two]
  rw [← dotProduct_mulVec_of_isSymm (hX.pow _), mulVec_mulVec, ← hsq]
  exact sq_dotProduct_le _ _

/-- **The matrix inequality**: `‖X y‖^(2r) ≤ ‖y‖^(2r) tr(X^(2r))` for symmetric `X` and
`r = 2^ℓ`. -/
theorem pow_dotProduct_le (hX : X.IsSymm) (y : Fin n → ℝ) (ℓ : ℕ) :
    ((X *ᵥ y) ⬝ᵥ (X *ᵥ y)) ^ 2 ^ ℓ ≤ (y ⬝ᵥ y) ^ 2 ^ ℓ * (X ^ (2 * 2 ^ ℓ)).trace := by
  set m : ℕ → ℝ := fun i ↦ (X ^ 2 ^ i *ᵥ y) ⬝ᵥ (X ^ 2 ^ i *ᵥ y) with hm
  have hy := dotProduct_self_nonneg y
  have hiter : ∀ i, m 0 ^ 2 ^ i ≤ (y ⬝ᵥ y) ^ (2 ^ i - 1) * m i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have h0 : 0 ≤ m 0 ^ 2 ^ i := pow_nonneg (dotProduct_self_nonneg _) _
      have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      calc m 0 ^ 2 ^ (i + 1) = (m 0 ^ 2 ^ i) ^ 2 := by rw [← pow_mul, pow_succ]
        _ ≤ ((y ⬝ᵥ y) ^ (2 ^ i - 1) * m i) ^ 2 := pow_le_pow_left₀ h0 ih 2
        _ = (y ⬝ᵥ y) ^ (2 * (2 ^ i - 1)) * m i ^ 2 := by
            rw [mul_pow, ← pow_mul, mul_comm (2 ^ i - 1) 2]
        _ ≤ (y ⬝ᵥ y) ^ (2 * (2 ^ i - 1)) * ((y ⬝ᵥ y) * m (i + 1)) :=
            mul_le_mul_of_nonneg_left (sq_dotProduct_pow_le hX y i) (pow_nonneg hy _)
        _ = (y ⬝ᵥ y) ^ (2 ^ (i + 1) - 1) * m (i + 1) := by
            rw [← mul_assoc, ← pow_succ]
            congr 2
            rw [pow_succ]
            omega
  have hlast : m ℓ ≤ (X ^ (2 * 2 ^ ℓ)).trace * (y ⬝ᵥ y) := by
    rw [two_mul, pow_add, trace_mul_self_of_isSymm (hX.pow _)]
    exact dotProduct_mulVec_self_le _ y
  have h1 : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  calc ((X *ᵥ y) ⬝ᵥ (X *ᵥ y)) ^ 2 ^ ℓ = m 0 ^ 2 ^ ℓ := by simp [hm]
    _ ≤ (y ⬝ᵥ y) ^ (2 ^ ℓ - 1) * m ℓ := hiter ℓ
    _ ≤ (y ⬝ᵥ y) ^ (2 ^ ℓ - 1) * ((X ^ (2 * 2 ^ ℓ)).trace * (y ⬝ᵥ y)) :=
        mul_le_mul_of_nonneg_left hlast (pow_nonneg hy _)
    _ = (y ⬝ᵥ y) ^ 2 ^ ℓ * (X ^ (2 * 2 ^ ℓ)).trace := by
        rw [mul_comm (X ^ (2 * 2 ^ ℓ)).trace, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel h1]

end Powers

/-! ### The matrix of the cut -/

/-- The symmetric matrix of the cut of `R` at `U`: the character `χ_q(a ∼ b)` if exactly one of
`a, b` is in `U`, and `0` otherwise. -/
noncomputable def cutMatrix (q : ℝ) (U : Finset (Fin n)) (R : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b ↦ if (a ∈ U ↔ b ∉ U) then RandomGraph.chi q (R.Adj a b) else 0

theorem cutMatrix_isSymm (q : ℝ) (U : Finset (Fin n)) (R : SimpleGraph (Fin n)) :
    (cutMatrix q U R).IsSymm := by
  ext a b
  simp only [cutMatrix, transpose_apply, of_apply]
  rw [R.adj_comm]
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [ha, hb]

/-- The centred adjacency is `√(q(1-q))` times the character. -/
theorem cent_eq {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (R : SimpleGraph (Fin n)) (u v : Fin n) :
    cent q R u v = √(q * (1 - q)) * RandomGraph.chi q (R.Adj u v) := by
  have h1 : 0 < 1 - q := by linarith
  unfold cent RandomGraph.chi
  split_ifs
  · rw [← Real.sqrt_mul (by positivity), show q * (1 - q) * ((1 - q) / q) = (1 - q) ^ 2 by
      field_simp, Real.sqrt_sq h1.le]
  · rw [mul_neg, ← Real.sqrt_mul (by positivity), show q * (1 - q) * (q / (1 - q)) = q ^ 2 by
      field_simp, Real.sqrt_sq hq.le]

/-- **The deterministic step**: if `tr(X^(2r)) ≤ (18 n)^r` for the matrix of the cut, then the
centred cut matrix has norm at most `√(18 n q (1 - q))`. -/
theorem normLE_of_trace_le {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (U : Finset (Fin n))
    (R : SimpleGraph (Fin n)) (ℓ : ℕ)
    (htr : (cutMatrix q U R ^ (2 * 2 ^ ℓ)).trace ≤ (18 * n) ^ 2 ^ ℓ) :
    NormLE q U (18 * n * (q * (1 - q))) R := by
  intro y
  set X := cutMatrix q U R
  set z : Fin n → ℝ := fun v ↦ if v ∈ U then 0 else y v
  have hrow : ∀ u ∈ U, ∑ v ∈ Uᶜ, cent q R u v * y v = √(q * (1 - q)) * (X *ᵥ z) u := by
    intro u hu
    simp only [mulVec, dotProduct, X, z, cutMatrix, of_apply, mul_sum]
    rw [← univ_inter Uᶜ, ← sum_ite_mem]
    refine sum_congr rfl fun v _ ↦ ?_
    by_cases hv : v ∈ U
    · simp [hu, hv]
    · simp [hu, hv, cent_eq hq hq1, mul_assoc]
  have hzz : z ⬝ᵥ z = ∑ v ∈ Uᶜ, y v ^ 2 := by
    simp only [dotProduct, z]
    rw [← univ_inter Uᶜ, ← sum_ite_mem]
    refine sum_congr rfl fun v _ ↦ ?_
    by_cases hv : v ∈ U <;> simp [hv, sq]
  have hXz : (X *ᵥ z) ⬝ᵥ (X *ᵥ z) ≤ 18 * n * (z ⬝ᵥ z) := by
    have h := pow_dotProduct_le (cutMatrix_isSymm q U R) z ℓ
    have hz := dotProduct_self_nonneg z
    have h' : ((X *ᵥ z) ⬝ᵥ (X *ᵥ z)) ^ 2 ^ ℓ ≤ (18 * n * (z ⬝ᵥ z)) ^ 2 ^ ℓ := by
      refine h.trans ?_
      rw [mul_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right htr (pow_nonneg hz _)
    exact (pow_le_pow_iff_left₀ (dotProduct_self_nonneg _) (by positivity)
      (pow_ne_zero _ two_ne_zero)).1 h'
  have hq0 : 0 ≤ q * (1 - q) := mul_nonneg hq.le (by linarith)
  calc ∑ u ∈ U, (∑ v ∈ Uᶜ, cent q R u v * y v) ^ 2
      = q * (1 - q) * ∑ u ∈ U, (X *ᵥ z) u ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun u hu ↦ ?_
        rw [hrow u hu, mul_pow, Real.sq_sqrt hq0]
    _ ≤ q * (1 - q) * ((X *ᵥ z) ⬝ᵥ (X *ᵥ z)) := by
        refine mul_le_mul_of_nonneg_left ?_ hq0
        simp only [dotProduct, ← sq]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ U) fun _ _ _ ↦ sq_nonneg _
    _ ≤ q * (1 - q) * (18 * n * (z ⬝ᵥ z)) := mul_le_mul_of_nonneg_left hXz hq0
    _ = 18 * n * (q * (1 - q)) * ∑ v ∈ Uᶜ, y v ^ 2 := by rw [hzz]; ring

/-! ### Walks in the matrix of the cut -/

/-- The product of the entries of `X` along the walk `a :: p`, written backwards. -/
def walkProd (X : Matrix (Fin n) (Fin n) ℝ) : Fin n → List (Fin n) → ℝ
  | _, [] => 1
  | a, a' :: p => X a' a * walkProd X a' p

/-- The entries of the powers of `X` expand into sums over walks. -/
theorem walkProd_mul_pow_succ (X : Matrix (Fin n) (Fin n) ℝ) (a c : Fin n) (p : List (Fin n))
    (t : ℕ) : walkProd X a p * (X ^ (t + 1)) a c = ∑ b, walkProd X b (a :: p) * (X ^ t) b c := by
  rw [pow_succ', Matrix.mul_apply, mul_sum]
  refine sum_congr rfl fun b _ ↦ ?_
  simp only [walkProd]
  ring

/-- Every step of the walk `a :: p` crosses the cut at `U`. -/
def Crossing (U : Finset (Fin n)) : Fin n → List (Fin n) → Prop
  | _, [] => True
  | a, a' :: p => (a' ∈ U ↔ a ∉ U) ∧ Crossing U a' p

/-- Along a walk crossing the cut, the product of the matrix of the cut of the graph of the coins
`ω` is `∏_e χ(ω_e)^(m_e)`. -/
theorem walkProd_graphOf (q : ℝ) {U : Finset (Fin n)} (ω : RandomGraph.Pair (Fin n) → Prop) :
    ∀ (a : Fin n) (p : List (Fin n)), Crossing U a p →
      walkProd (cutMatrix q U (RandomGraph.graphOf ω)) a p =
        ∏ e : RandomGraph.Pair (Fin n), RandomGraph.chi q (ω e) ^ Walk.cnt a p e.1
  | a, [], _ => by simp [walkProd]
  | a, a' :: p, h => by
    have hne : a' ≠ a := fun h' ↦ by
      have := h.1
      rw [h'] at this
      tauto
    set e₀ : RandomGraph.Pair (Fin n) := ⟨s(a', a), by simpa using hne⟩
    have hadj : RandomGraph.chi q ((RandomGraph.graphOf ω).Adj a' a) =
        RandomGraph.chi q (ω e₀) := by
      congr 1
      rw [RandomGraph.graphOf_adj]
      exact propext ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hne, h⟩⟩
    have hpow : ∀ e : RandomGraph.Pair (Fin n), RandomGraph.chi q (ω e) ^ Walk.cnt a (a' :: p) e.1 =
        RandomGraph.chi q (ω e) ^ Walk.cnt a' p e.1 *
          if e₀ = e then RandomGraph.chi q (ω e) else 1 := by
      intro e
      rw [Walk.cnt_cons, pow_add]
      congr 1
      by_cases he : e₀ = e
      · rw [ite_eq_left he, ite_eq_left (by rw [← he]), pow_one]
      · rw [ite_eq_right he, ite_eq_right (fun h ↦ he (Subtype.ext h)), pow_zero]
    rw [walkProd, walkProd_graphOf q ω a' p h.2, prod_congr rfl fun e _ ↦ hpow e,
      prod_mul_distrib, prod_ite_eq, ite_eq_left (mem_univ _)]
    simp only [cutMatrix, of_apply, h.1, ite_true, hadj]
    ring

/-- **The mean of the product along a walk**: `E ∏_e χ^(m_e) = ∏_e E χ^(m_e)`, the coins on the
pairs being independent. -/
theorem integral_walkProd {q : I} {U : Finset (Fin n)} {a : Fin n} {p : List (Fin n)}
    (h : Crossing U a p) :
    ∫ R, walkProd (cutMatrix q U R) a p ∂G(Fin n, q) =
      ∏ e : RandomGraph.Pair (Fin n), ∫ x, RandomGraph.chi q x ^ Walk.cnt a p e.1
        ∂Ber(True, False, q) := by
  rw [RandomGraph.binomialRandom_eq_map_graphOf, integral_map
    RandomGraph.measurable_graphOf.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  simp_rw [walkProd_graphOf q _ a p h]
  rw [RandomGraph.coins, Measure.infinitePi_eq_pi]
  exact integral_fintype_prod_eq_prod (f := fun (e : RandomGraph.Pair (Fin n)) (x : Prop) ↦
    RandomGraph.chi q x ^ Walk.cnt a p e.1)

/-- The moments of a character: `E χ = 0`, and `|E χ^m| ≤ K^(m - 2)` for `K = √(charMax q)`. -/
theorem abs_integral_chi_pow_le {q : I} (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (m : ℕ) :
    |∫ x, RandomGraph.chi q x ^ m ∂Ber(True, False, q)| ≤
      if m = 1 then 0 else √(Biclique.charMax q) ^ (m - 2) := by
  split_ifs with hm
  · rw [hm]
    simp only [pow_one]
    rw [RandomGraph.integral_chi hq hq1, abs_zero]
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · have hm0 : m = 0 := by omega
    simp [hm0]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  set K := √(Biclique.charMax q)
  have hpt : ∀ x : Prop, |RandomGraph.chi q x ^ (k + 2)| ≤
      K ^ k * (RandomGraph.chi q x * RandomGraph.chi q x) := by
    intro x
    rw [abs_pow, pow_add, sq_abs, sq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _)
      (Random.abs_chi_le hq hq1 x) k) (mul_self_nonneg _)
  calc |∫ x, RandomGraph.chi q x ^ (k + 2) ∂Ber(True, False, q)|
      ≤ ∫ x, |RandomGraph.chi q x ^ (k + 2)| ∂Ber(True, False, q) := abs_integral_le_integral_abs
    _ ≤ ∫ x, K ^ k * (RandomGraph.chi q x * RandomGraph.chi q x) ∂Ber(True, False, q) :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = K ^ k := by rw [integral_const_mul, RandomGraph.integral_chi_mul_chi hq hq1, mul_one]

/-- The bound `∏_e K^(m_e - 2)` on the mean of the product along a walk. -/
noncomputable def kappa (K : ℝ) (a : Fin n) (p : List (Fin n)) : ℝ :=
  ∏ e : RandomGraph.Pair (Fin n), K ^ (Walk.cnt a p e.1 - 2)

@[simp] theorem kappa_nil (K : ℝ) (a : Fin n) : kappa K a [] = 1 := by simp [kappa]

theorem kappa_nonneg {K : ℝ} (hK : 0 ≤ K) (a : Fin n) (p : List (Fin n)) : 0 ≤ kappa K a p :=
  prod_nonneg fun _ _ ↦ pow_nonneg hK _

theorem kappa_cons (K : ℝ) {a b : Fin n} (hab : a ≠ b) (p : List (Fin n)) :
    kappa K b (a :: p) = kappa K a p * Walk.fac K a p b := by
  set e₀ : RandomGraph.Pair (Fin n) := ⟨s(a, b), by simpa using hab⟩
  have hpt : ∀ e : RandomGraph.Pair (Fin n), K ^ (Walk.cnt b (a :: p) e.1 - 2) =
      K ^ (Walk.cnt a p e.1 - 2) * if e₀ = e then Walk.fac K a p b else 1 := by
    intro e
    rw [Walk.cnt_cons]
    by_cases he : e₀ = e
    · rw [ite_eq_left he, ite_eq_left (by rw [← he]), ← he]
      unfold Walk.fac
      split_ifs with h2
      · rw [← pow_succ]
        congr 1
        change Walk.cnt a p s(a, b) + 1 - 2 = Walk.cnt a p s(a, b) - 2 + 1
        omega
      · rw [mul_one]
        congr 1
        change Walk.cnt a p s(a, b) + 1 - 2 = Walk.cnt a p s(a, b) - 2
        omega
    · rw [ite_eq_right he, ite_eq_right (fun h ↦ he (Subtype.ext h)), add_zero, mul_one]
  rw [kappa, prod_congr rfl fun e _ ↦ hpt e, prod_mul_distrib, prod_ite_eq,
    ite_eq_left (mem_univ _), kappa]

/-- The mean of the product along a walk crossing the cut is at most `∏_e K^(m_e - 2)`, and `0`
unless every edge is traversed `0` or at least `2` times. -/
theorem abs_integral_walkProd_le {q : I} (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    {U : Finset (Fin n)} {a : Fin n} {p : List (Fin n)} (h : Crossing U a p) :
    |∫ R, walkProd (cutMatrix q U R) a p ∂G(Fin n, q)| ≤
      kappa √(Biclique.charMax q) a p * if Walk.opens a p = 0 then 1 else 0 := by
  rw [integral_walkProd h, abs_prod]
  split_ifs with hO
  · rw [mul_one, kappa]
    refine prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun e _ ↦ ?_
    have he : Walk.cnt a p e.1 ≠ 1 := by
      intro he
      unfold Walk.opens at hO
      rw [card_eq_zero, filter_eq_empty_iff] at hO
      exact hO (mem_univ e) he
    refine (abs_integral_chi_pow_le hq hq1 _).trans (le_of_eq ?_)
    rw [ite_eq_right he]
  · rw [mul_zero]
    obtain ⟨e, he⟩ : ∃ e : RandomGraph.Pair (Fin n), Walk.cnt a p e.1 = 1 := by
      unfold Walk.opens at hO
      obtain ⟨e, he⟩ := card_ne_zero.1 hO
      exact ⟨e, (mem_filter.1 he).2⟩
    refine le_of_eq (prod_eq_zero (mem_univ e) ?_)
    rw [he]
    simp only [pow_one]
    rw [RandomGraph.integral_chi hq hq1, abs_zero]

/-- **The walk expansion of the moments**: the mean of `(X^t)_ac` times the product along a walk
crossing the cut is at most `∏_e K^(m_e - 2)` times the walk bound `Walk.bound`. -/
theorem integral_walkProd_mul_pow_le {q : I} (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1)
    (U : Finset (Fin n)) (c : Fin n) :
    ∀ (t : ℕ) (a : Fin n) (p : List (Fin n)), Crossing U a p →
      ∫ R, walkProd (cutMatrix q U R) a p * (cutMatrix q U R ^ t) a c ∂G(Fin n, q) ≤
        kappa √(Biclique.charMax q) a p * Walk.bound √(Biclique.charMax q) t a p
  | 0, a, p, h => by
    set K := √(Biclique.charMax q)
    simp only [pow_zero, Matrix.one_apply]
    rw [Walk.bound]
    by_cases hac : a = c
    · simp only [hac, ite_true, mul_one]
      rw [← hac]
      exact (le_abs_self _).trans (abs_integral_walkProd_le hq hq1 h)
    · simp only [hac, ite_false, mul_zero, integral_zero]
      exact mul_nonneg (kappa_nonneg (Real.sqrt_nonneg _) a p) (by split_ifs <;> norm_num)
  | t + 1, a, p, h => by
    set K := √(Biclique.charMax q)
    have hK : 0 ≤ K := Real.sqrt_nonneg _
    simp_rw [walkProd_mul_pow_succ]
    rw [integral_finsetSum _ fun b _ ↦ Integrable.of_finite, Walk.bound, mul_sum]
    refine sum_le_sum fun b _ ↦ ?_
    by_cases hcross : a ∈ U ↔ b ∉ U
    · have hab : a ≠ b := fun h' ↦ by rw [h'] at hcross; tauto
      rw [ite_eq_left hab, ← mul_assoc, ← kappa_cons K hab]
      exact integral_walkProd_mul_pow_le hq hq1 U c t b (a :: p) ⟨hcross, h⟩
    · have h0 : ∀ R : SimpleGraph (Fin n),
          walkProd (cutMatrix q U R) b (a :: p) * (cutMatrix q U R ^ t) b c = 0 := by
        intro R
        simp [walkProd, cutMatrix, hcross]
      simp only [h0, integral_zero]
      refine mul_nonneg (kappa_nonneg hK a p) ?_
      split_ifs
      · exact mul_nonneg (Walk.fac_nonneg hK a p b) (Walk.bound_nonneg hK t b (a :: p))
      · exact le_rfl

/-- **The trace moment**: `E tr(X^L) ≤ ∑_c Walk.bound K L c []`. -/
theorem integral_trace_le {q : I} (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (U : Finset (Fin n))
    (L : ℕ) :
    ∫ R, (cutMatrix q U R ^ L).trace ∂G(Fin n, q) ≤
      ∑ c : Fin n, Walk.bound √(Biclique.charMax q) L c [] := by
  have h : ∀ R : SimpleGraph (Fin n), (cutMatrix q U R ^ L).trace =
      ∑ c, walkProd (cutMatrix q U R) c [] * (cutMatrix q U R ^ L) c c := by
    intro R
    simp [trace, walkProd]
  simp_rw [h]
  rw [integral_finsetSum _ fun c _ ↦ Integrable.of_finite]
  refine sum_le_sum fun c _ ↦ ?_
  have := integral_walkProd_mul_pow_le hq hq1 U c L c [] trivial
  rwa [kappa_nil, one_mul] at this

/-! ### The theorem -/

/-- **The norm of the cut** [BKS23, Fact 3.14]: if `charMax q (2r + 1)^4 ≤ n` for `r = 2^ℓ`, the
centred cut matrix of `G(n, q)` at `U` has `‖M‖² > 18 n q (1 - q)` with probability at most
`n / 2^r`. -/
theorem prob_not_normLE {q : I} (hq : 0 < (q : ℝ)) (hq1 : (q : ℝ) < 1) (U : Finset (Fin n))
    (ℓ : ℕ) (hK : Biclique.charMax q * (2 * 2 ^ ℓ + 1 : ℝ) ^ 4 ≤ n) :
    (G(Fin n, q)).real {R | ¬ NormLE q U (18 * n * (q * (1 - q))) R} ≤ n / 2 ^ (2 ^ ℓ) := by
  set B : ℝ := 2 * 2 ^ ℓ + 1
  set K := √(Biclique.charMax q)
  set s := √(n : ℝ)
  have hM := Biclique.one_le_charMax hq hq1
  have hB1 : 1 ≤ B := by
    have : (0 : ℝ) < 2 ^ ℓ := by positivity
    linarith
  have hB4 : B ^ 4 ≤ n := le_trans (le_mul_of_one_le_left (by positivity) hM) hK
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hB4
  have hn : (n : ℝ) = s ^ 2 := (Real.sq_sqrt hn0.le).symm
  have hs : 0 < s := Real.sqrt_pos.2 hn0
  have hB3 : B ^ 3 ≤ s ^ 2 := by
    rw [← hn]
    exact (pow_le_pow_right₀ hB1 (by norm_num)).trans hB4
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hKB : K * B ^ 2 ≤ s := by
    have : K * B ^ 2 = √(Biclique.charMax q * B ^ 4) := by
      rw [Real.sqrt_mul' _ (by positivity), show B ^ 4 = (B ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [this]
    exact Real.sqrt_le_sqrt hK
  have hL : (((2 * 2 ^ ℓ : ℕ) : ℝ) + 1) ≤ B := by
    push_cast
    exact le_refl _
  -- The moment: `E tr(X^(2r)) ≤ n (9n)^r`.
  have hmom : ∫ R, (cutMatrix q U R ^ (2 * 2 ^ ℓ)).trace ∂G(Fin n, q) ≤
      (n : ℝ) * (9 * n) ^ 2 ^ ℓ := by
    refine (integral_trace_le hq hq1 U _).trans ?_
    calc ∑ c : Fin n, Walk.bound K (2 * 2 ^ ℓ) c []
        ≤ ∑ _c : Fin n, (3 * s) ^ (2 * 2 ^ ℓ) :=
          sum_le_sum fun c _ ↦ Walk.bound_le hn hs hB1 hB3 hK0 hKB hL c
      _ = (n : ℝ) * (9 * n) ^ 2 ^ ℓ := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, pow_mul, mul_pow, ← hn]
          norm_num
  -- Markov's inequality.
  have hsub : ∀ R ∈ {R | ¬ NormLE q U (18 * n * (q * (1 - q))) R},
      (18 * n : ℝ) ^ 2 ^ ℓ ≤ (cutMatrix q U R ^ (2 * 2 ^ ℓ)).trace := by
    intro R hR
    by_contra h
    exact hR (normLE_of_trace_le hq hq1 U R ℓ (not_le.1 h).le)
  have hmarkov := RandomGraph.mul_measureReal_le_integral (μ := G(Fin n, q))
    Integrable.of_finite (fun R ↦ trace_pow_two_mul_nonneg (cutMatrix_isSymm q U R) _)
    MeasurableSet.of_discrete hsub
  have h9 : 0 < (9 * n : ℝ) ^ 2 ^ ℓ := by positivity
  have h18 : (18 * n : ℝ) ^ 2 ^ ℓ = (9 * n) ^ 2 ^ ℓ * 2 ^ 2 ^ ℓ := by
    rw [← mul_pow]
    ring
  rw [le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ h9
  calc (9 * n : ℝ) ^ 2 ^ ℓ * ((G(Fin n, q)).real
        {R | ¬ NormLE q U (18 * n * (q * (1 - q))) R} * 2 ^ 2 ^ ℓ)
      = (18 * n : ℝ) ^ 2 ^ ℓ *
          (G(Fin n, q)).real {R | ¬ NormLE q U (18 * n * (q * (1 - q))) R} := by
        rw [h18]
        ring
    _ ≤ (n : ℝ) * (9 * n) ^ 2 ^ ℓ := hmarkov.trans hmom
    _ = (9 * n : ℝ) ^ 2 ^ ℓ * n := mul_comm _ _

end BKS23.Spectral
