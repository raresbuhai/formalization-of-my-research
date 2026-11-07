module

public import Background.GaussianCalculus
public import Background.ArcsinSeries
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Votes and their energy

[BGHKLMM26, Section 3.2]. A vertex `i` sees its neighbours `k` through unit vectors `u_k`
(orthogonal to `v_i`), with weights `p_k ≥ 0` summing to `1`. Its vote is
`ψ(g) = ∑ p_k sgn⟨u_k, g⟩`, and the smoothed vote is `f_η = U_η ψ = ∑ p_k s_η(⟨u_k, g⟩)`
(`BGHKLMM26.vote p u η`, with `vote p u 1 = ψ`).

By the smoothed correlations (`Gaussian.integral_smoothSign_mul_smoothSign`),
`E f_a f_b = (2/π) ∑ p_j p_k arcsin (a b Q_jk)` with `Q_jk = ⟨u_j, u_k⟩`. Expanding `arcsin` in
its power series with nonnegative coefficients, and using that every `∑ p_j p_k Q_jk^m` is
nonnegative (the Schur product theorem), gives

* `E f_η² ≤ E f_η ψ =: a` [BGHKLMM26, Lemma 3.12] (`BGHKLMM26.integral_vote_sq_le`), without
  Hermite expansions, and
* `a ≥ c / (d √L)` when the off-diagonal `Q_jk` are at least `-β` and `β^(2L+1) ≤ 1/(2d)`
  [BGHKLMM26, Lemma 3.10] (`BGHKLMM26.energy_ge`).
-/

@[expose] public section

namespace BGHKLMM26

open MeasureTheory ProbabilityTheory Real Gaussian Finset
open scoped RealInnerProductSpace

section Schur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

/-- **The Schur product theorem**, as used in [BGHKLMM26, Lemma 3.10]: for any vectors `u_k`
and weights `p_k`, `∑ p_j p_k ⟨u_j, u_k⟩^m ≥ 0`. -/
theorem schur_nonneg (p : ι → ℝ) (u : ι → E) (m : ℕ) :
    0 ≤ ∑ j, ∑ k, p j * p k * ⟪u j, u k⟫ ^ m := by
  have hpsd : (Matrix.of fun j k : ι ↦ ⟪u j, u k⟫ ^ m).PosSemidef := by
    induction m with
    | zero =>
      have := Matrix.posSemidef_gram ℝ (fun _ : ι ↦ (1 : ℝ))
      convert this using 1
      ext j k
      simp
    | succ m ih =>
      have := ih.hadamard (Matrix.posSemidef_gram ℝ u)
      convert this using 1
      ext j k
      simp [pow_succ]
  have := hpsd.dotProduct_mulVec_nonneg p
  convert this using 1
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

end Schur

section Vote

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

/-- The smoothed vote `f_a(g) = ∑ₖ pₖ s_a(⟨uₖ, g⟩)`; for `a = 1` it is the vote
`ψ(g) = ∑ₖ pₖ sgn⟨uₖ, g⟩`. -/
noncomputable def vote (p : ι → ℝ) (u : ι → E) (a : ℝ) (g : E) : ℝ :=
  ∑ k, p k * smoothSign a ⟪u k, g⟫

omit [FiniteDimensional ℝ E] in
@[fun_prop]
theorem measurable_vote (p : ι → ℝ) (u : ι → E) (a : ℝ) : Measurable (vote p u a) := by
  unfold vote
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem vote_one (p : ι → ℝ) (u : ι → E) (g : E) :
    vote p u 1 g = ∑ k, p k * sgn ⟪u k, g⟫ := by
  simp [vote, smoothSign_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A vote with weights `p ≥ 0` summing to at most `1` is in `[-1, 1]`. -/
theorem abs_vote_le {p : ι → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k ≤ 1) (u : ι → E) (a : ℝ)
    (g : E) : |vote p u a g| ≤ 1 := by
  unfold vote
  calc |∑ k, p k * smoothSign a ⟪u k, g⟫| ≤ ∑ k, |p k * smoothSign a ⟪u k, g⟫| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, p k := by
        refine Finset.sum_le_sum fun k _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hp0 k)]
        exact mul_le_of_le_one_right (hp0 k) (abs_smoothSign_le _ _)
    _ ≤ 1 := hp1

/-- **Correlations of smoothed votes**: `E f_a f_b = (2/π) ∑ p_j p_k arcsin (a b ⟨u_j, u_k⟩)` for
unit vectors `u_k` and `a, b ∈ [0, 1]`. -/
theorem integral_vote_mul_vote (p : ι → ℝ) {u : ι → E} (hu : ∀ k, ‖u k‖ = 1) {a b : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∫ g, vote p u a g * vote p u b g ∂stdGaussian E =
      2 / π * ∑ j, ∑ k, p j * p k * arcsin (a * b * ⟪u j, u k⟫) := by
  have hint : ∀ j k, Integrable (fun g ↦ p j * p k *
      (smoothSign a ⟪u j, g⟫ * smoothSign b ⟪u k, g⟫)) (stdGaussian E) := by
    intro j k
    refine (integrable_of_abs_le (C := 1) (by fun_prop) fun g ↦ ?_).const_mul _
    rw [abs_mul]
    calc |smoothSign a ⟪u j, g⟫| * |smoothSign b ⟪u k, g⟫| ≤ 1 * 1 :=
          mul_le_mul (abs_smoothSign_le _ _) (abs_smoothSign_le _ _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h : ∀ g, vote p u a g * vote p u b g = ∑ j, ∑ k, p j * p k *
      (smoothSign a ⟪u j, g⟫ * smoothSign b ⟪u k, g⟫) := by
    intro g
    rw [vote, vote, Fintype.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  simp_rw [h]
  rw [integral_finsetSum _ fun j _ ↦ integrable_finsetSum _ fun k _ ↦ hint j k,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_finsetSum _ fun k _ ↦ hint j k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_const_mul, integral_smoothSign_mul_smoothSign (hu j) (hu k) ha0 ha1 hb0 hb1]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `|⟨u, v⟩| ≤ 1` for unit vectors. -/
theorem abs_inner_le_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) : |⟪u, v⟫| ≤ 1 := by
  have := abs_real_inner_le_norm u v
  rwa [hu, hv, one_mul] at this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The arcsin quadratic form as a series**: for `|x| < 1`,
`∑ p_j p_k arcsin (x Q_jk) = ∑ₙ cₙ x^(2n+1) q_(2n+1)` with `q_m = ∑ p_j p_k Q_jk^m`. -/
theorem hasSum_arcsin_form (p : ι → ℝ) {u : ι → E} (hu : ∀ k, ‖u k‖ = 1) {x : ℝ}
    (hx : |x| < 1) :
    HasSum (fun n ↦ ArcsinSeries.c n * x ^ (2 * n + 1) *
        ∑ j, ∑ k, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1))
      (∑ j, ∑ k, p j * p k * arcsin (x * ⟪u j, u k⟫)) := by
  have hterm : ∀ j k, HasSum (fun n ↦ p j * p k *
      (ArcsinSeries.c n * (x * ⟪u j, u k⟫) ^ (2 * n + 1)))
      (p j * p k * arcsin (x * ⟪u j, u k⟫)) := by
    intro j k
    refine (ArcsinSeries.hasSum_arcsin ?_).mul_left _
    rw [abs_mul]
    calc |x| * |⟪u j, u k⟫| ≤ |x| * 1 :=
          mul_le_mul_of_nonneg_left (abs_inner_le_one (hu j) (hu k)) (abs_nonneg x)
      _ < 1 := by rwa [mul_one]
  have := hasSum_sum (s := Finset.univ) fun j _ ↦
    hasSum_sum (s := Finset.univ) fun k _ ↦ hterm j k
  convert this using 1
  funext n
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [mul_pow]
  ring

/-- **The smoothed vote has energy at most its correlation with the vote** [BGHKLMM26,
Lemma 3.12]: `E f_η² ≤ E f_η ψ` for `η ∈ [0, 1)`. -/
theorem integral_vote_sq_le (p : ι → ℝ) {u : ι → E} (hu : ∀ k, ‖u k‖ = 1) {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∫ g, vote p u η g * vote p u η g ∂stdGaussian E ≤
      ∫ g, vote p u η g * vote p u 1 g ∂stdGaussian E := by
  rw [integral_vote_mul_vote p hu hη0 hη1.le hη0 hη1.le,
    integral_vote_mul_vote p hu hη0 hη1.le zero_le_one le_rfl, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hηη : |η * η| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hη' : |η| < 1 := by rwa [abs_of_nonneg hη0]
  refine hasSum_le (fun n ↦ ?_) (hasSum_arcsin_form p hu hηη) (hasSum_arcsin_form p hu hη')
  refine mul_le_mul_of_nonneg_right ?_ (schur_nonneg p u _)
  refine mul_le_mul_of_nonneg_left ?_ (ArcsinSeries.c_nonneg n)
  rw [mul_pow]
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hη0 hη1.le)

/-- `cₙ ≥ 1 / (10 √2 L √L)` for `1 ≤ n ≤ 2L`. -/
theorem c_ge {L n : ℕ} (hn : 1 ≤ n) (hnL : n ≤ 2 * L) :
    1 / (10 * √2 * L * √L) ≤ ArcsinSeries.c n := by
  have hL : (1 : ℝ) ≤ L := by
    have : 1 ≤ 2 * L := hn.trans hnL
    exact_mod_cast (show 1 ≤ L by omega)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnL' : (n : ℝ) ≤ 2 * L := by exact_mod_cast hnL
  have hsn : √(n : ℝ) ≤ √2 * √L := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hnL'
  have hb := ArcsinSeries.b_ge hn
  rw [ArcsinSeries.c]
  have hsn0 : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hsL : 0 < √(L : ℝ) := Real.sqrt_pos.2 (by linarith)
  calc 1 / (10 * √2 * L * √L) ≤ 1 / (2 * √n) / (2 * n + 1) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
        have h1 : 2 * (n : ℝ) + 1 ≤ 5 * L := by linarith
        calc 2 * √(n : ℝ) * (2 * n + 1) ≤ 2 * (√2 * √L) * (5 * L) := by gcongr
          _ = 10 * √2 * L * √L := by ring
    _ ≤ ArcsinSeries.b n / (2 * n + 1) := by gcongr

/-- **The energy lower bound** [BGHKLMM26, Lemma 3.10]: if the weights `p ≥ 0` sum to `1` over at
most `d` neighbours, the off-diagonal correlations are at least `-β`, `β^(2L+1) ≤ 1/(2d)` and
`η^(4L+1) ≥ 1/2`, then `a = E f_η ψ ≥ 1 / (100 d √L)`. -/
theorem energy_ge {p : ι → ℝ} (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1) {u : ι → E}
    (hu : ∀ k, ‖u k‖ = 1) {d : ℕ} (hd : Fintype.card ι ≤ d) {β : ℝ} (hβ0 : 0 ≤ β)
    (hQ : ∀ j k, j ≠ k → -β ≤ ⟪u j, u k⟫) {L : ℕ} (hL : 1 ≤ L)
    (hβL : β ^ (2 * L + 1) ≤ 1 / (2 * d)) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hηL : 1 / 2 ≤ η ^ (4 * L + 1)) :
    1 / (100 * d * √L) ≤ ∫ g, vote p u η g * vote p u 1 g ∂stdGaussian E := by
  classical
  have hd1 : (1 : ℝ) ≤ d := by
    have : 0 < Fintype.card ι := by
      by_contra h
      have h0 : Fintype.card ι = 0 := by omega
      rw [Fintype.card_eq_zero_iff] at h0
      simp at hp1
    exact_mod_cast this.trans_le hd
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  -- `q_(2n+1) ≥ 1/(2d)` once `β^(2n+1) ≤ 1/(2d)`.
  have hq : ∀ n, L ≤ n → 1 / (2 * d) ≤ ∑ j, ∑ k, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) := by
    intro n hn
    have hβn : β ^ (2 * n + 1) ≤ 1 / (2 * d) :=
      (pow_le_pow_of_le_one hβ0 (by
        by_contra h
        have : 1 < β ^ (2 * L + 1) := one_lt_pow₀ (not_le.1 h) (by omega)
        have : 1 / (2 * (d : ℝ)) < 1 := by
          rw [div_lt_one (by positivity)]
          linarith
        linarith) (by omega)).trans hβL
    -- Diagonal and off-diagonal parts.
    have hsplit : ∀ j, ∑ k, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) =
        p j ^ 2 + ∑ k ∈ Finset.univ.erase j, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) := by
      intro j
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), real_inner_self_eq_norm_sq, hu j]
      ring
    have hoff : ∀ j, -(β ^ (2 * n + 1)) * (p j * ∑ k ∈ Finset.univ.erase j, p k) ≤
        ∑ k ∈ Finset.univ.erase j, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
      have hm : Odd (2 * n + 1) := odd_two_mul_add_one n
      have hodd : -(β ^ (2 * n + 1)) ≤ ⟪u j, u k⟫ ^ (2 * n + 1) := by
        rw [← hm.neg_pow]
        exact hm.strictMono_pow.monotone (hQ j k hjk)
      have := mul_le_mul_of_nonneg_left hodd (mul_nonneg (hp0 j) (hp0 k))
      linarith
    have hrest : ∀ j, ∑ k ∈ Finset.univ.erase j, p k ≤ 1 := by
      intro j
      rw [← hp1]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        fun k _ _ ↦ hp0 k
    have hdiag : 1 / (d : ℝ) ≤ ∑ j, p j ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := p)
      rw [hp1, one_pow, Finset.card_univ] at h
      rw [div_le_iff₀ (by positivity)]
      have : (Fintype.card ι : ℝ) ≤ d := by exact_mod_cast hd
      nlinarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ sq_nonneg (p j)]
    have hoff' : -(β ^ (2 * n + 1)) ≤ ∑ j, ∑ k ∈ Finset.univ.erase j,
        p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) := by
      calc -(β ^ (2 * n + 1)) = -(β ^ (2 * n + 1)) * ∑ j, p j := by rw [hp1, mul_one]
        _ ≤ ∑ j, -(β ^ (2 * n + 1)) * (p j * ∑ k ∈ Finset.univ.erase j, p k) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun j _ ↦ ?_
            have := mul_le_of_le_one_right (hp0 j) (hrest j)
            have hb : 0 ≤ β ^ (2 * n + 1) := by positivity
            nlinarith
        _ ≤ _ := Finset.sum_le_sum fun j _ ↦ hoff j
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    have : 1 / (2 * (d : ℝ)) = 1 / d - 1 / (2 * d) := by field_simp; ring
    linarith
  -- The series, from `n = L` to `2L - 1`.
  have hη' : |η| < 1 := by rwa [abs_of_nonneg hη0]
  have hform := hasSum_arcsin_form p hu hη'
  rw [integral_vote_mul_vote p hu hη0 hη1.le zero_le_one le_rfl]
  simp_rw [mul_one]
  have hnonneg : ∀ n, 0 ≤ ArcsinSeries.c n * η ^ (2 * n + 1) *
      ∑ j, ∑ k, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) := fun n ↦
    mul_nonneg (mul_nonneg (ArcsinSeries.c_nonneg n) (by positivity)) (schur_nonneg p u _)
  have hpart := sum_le_hasSum (Finset.Ico L (2 * L)) (fun n _ ↦ hnonneg n) hform
  have hterm : ∀ n ∈ Finset.Ico L (2 * L), 1 / (40 * √2 * d * L * √L) ≤
      ArcsinSeries.c n * η ^ (2 * n + 1) * ∑ j, ∑ k, p j * p k * ⟪u j, u k⟫ ^ (2 * n + 1) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hc := c_ge (L := L) (by omega) hn.2.le
    have hη : 1 / 2 ≤ η ^ (2 * n + 1) :=
      hηL.trans (pow_le_pow_of_le_one hη0 hη1.le (by omega))
    have hqn := hq n hn.1
    calc 1 / (40 * √2 * d * L * √L)
        = 1 / (10 * √2 * L * √L) * (1 / 2) * (1 / (2 * d)) := by field_simp; ring
      _ ≤ _ := mul_le_mul (mul_le_mul hc hη (by norm_num) (ArcsinSeries.c_nonneg n)) hqn
          (by positivity) (mul_nonneg (ArcsinSeries.c_nonneg n) (by positivity))
  have hsum := Finset.card_nsmul_le_sum _ _ _ hterm
  rw [Nat.card_Ico, show 2 * L - L = L by omega, nsmul_eq_mul] at hsum
  have hsL : 0 < √(L : ℝ) := Real.sqrt_pos.2 (by linarith)
  have h1 : (L : ℝ) * (1 / (40 * √2 * d * L * √L)) = 1 / (40 * √2 * d * √L) := by
    field_simp
  rw [h1] at hsum
  have hs2 : √2 < 1.415 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hπ := pi_lt_d2
  calc 1 / (100 * d * √L) ≤ 2 / π * (1 / (40 * √2 * d * √L)) := by
        rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
        have h5 : π * √2 ≤ 5 := by nlinarith [pi_pos, Real.sqrt_nonneg 2]
        have hpos : 0 ≤ (d : ℝ) * √L := by positivity
        have : π * (40 * √2 * d * √L) ≤ 2 * (100 * d * √L) :=
          calc π * (40 * √2 * d * √L) = 40 * (π * √2) * (d * √L) := by ring
            _ ≤ 40 * 5 * (d * √L) := by gcongr
            _ = 2 * (100 * d * √L) := by ring
        linarith
    _ ≤ 2 / π * ∑ j, ∑ k, p j * p k * arcsin (η * ⟪u j, u k⟫) := by
        gcongr
        exact hsum.trans hpart

end Vote

end BGHKLMM26
