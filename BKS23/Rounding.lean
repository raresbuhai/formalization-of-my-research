module

public import BKS23.CliqueProgram
public import Background.SumOfSquares.Mixture
public import Background.SumOfSquares.Algorithm.Correct
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Rounding

[BKS23, Lemmas 5.3–5.5, Theorem 5.1], with the output of the solver: a pseudo-expectation `Ẽ`
that satisfies the clique program up to `η + γ` and whose objective `∑ᵢ Ẽ[wᵢ]²` is within `γ`
of every pseudo-expectation satisfying it up to `η`. For a `T`-tuple `Q` of vertices let
`w_Q = ∏ⱼ w_{Qⱼ}` and

  `S_Q = {i | Ẽ[w_Q wᵢ] ≥ Ẽ[w_Q] / 2}`.

**Main result** (`BKS23.Rounding.exists_round_eq`): if the cut of the planted clique `S` has the
biclique certificate `|x|^T |y| ≤ ω` and the parameters are such that `ω (n/k²)^T` and the
approximation errors are small, then `S_Q = S` for some `Q`.

**Deviation from the paper.** The paper samples `O((n/k)^T)` tuples `Q` with probability
proportional to `Ẽ[w_Q]` and shows that a good one appears with probability `0.99`. We show that
a good one exists; the algorithm (`BKS23.Algorithm`) then tries all `n^T` tuples, which is
polynomial for fixed `T`. This needs no coins and no sampling from rational weights. The pruning
of the cleanup (`BKS23/Cleanup.lean`) bounds the list either way.

The steps:

* **Maximal coverage** (Lemma 5.3, `BKS23.Rounding.coverage`): `Ẽ[∑_{i ∈ S} wᵢ] ≳ k²/n`, by
  comparing `Ẽ` with its mixture with the planted point (`SoS.PseudoExpectation.mix`), which
  satisfies the program up to `η` once the weight of the point is `γ / (η + γ)`.
* **Hölder** (Lemma 5.4, `BKS23.Rounding.holder`): `Ẽ[s^T] ≥ Ẽ[s]^T - errH` for
  `s = ∑_{i ∈ S} wᵢ` and every `T`, by the tangent line of `x^T` at `Ẽ[s]`
  (`BKS23.Rounding.apply_pow_eq`): `s^T - Ẽ[s]^T - T Ẽ[s]^(T-1) (s - Ẽ[s])` is a sum of terms
  `(s - Ẽ[s])² w_Q` with nonnegative coefficients, each with a small proof from the Boolean
  constraints, so `Ẽ` of it is at least `-errH`, which is of order `(η + γ) T² (30k + 20)^T` times
  the constraint norms.
* **Averaging** (`BKS23.Rounding.exists_round`): from `∑_{Q ∈ S^T} Ẽ[w_Q] = Ẽ[s^T] ≥ L` and
  `∑_{Q ∈ S^T} Ẽ[w_Q |y|] = Ẽ[s^T |y|] ≤ U` (the certificate), some `Q` has `Ẽ[w_Q]` at least
  `L / (2 k^T)` and `Ẽ[w_Q |y|] ≤ c Ẽ[w_Q]` with `c ≈ 2U / L`. With the approximate constraints
  (`0 ≤ Ẽ[w_Q wᵢ] ≤ Ẽ[w_Q]`, `∑ᵢ Ẽ[w_Q wᵢ] = k Ẽ[w_Q]`) and `c < 1/2`, this `Q` has
  `S_Q = S`: the threshold is `1/2`, not the paper's `1 - 2δ` (`BKS23/README.md`, item 1), and
  no factor `2` is lost to Markov (item 2), since only existence is needed.
-/

@[expose] public section

namespace BKS23.Rounding

open SoS MvPolynomial Finset

/-! ### Averaging -/

/-- **Averaging.** Reals `a Q` (for `Ẽ[w_Q]`) and `d Q i` (for `Ẽ[w_Q wᵢ]`), `Q ∈ 𝒬`, with
`∑_Q a Q ≥ L > 0`, `∑_Q ∑_{i ∉ S} d Q i ≤ U`, and, up to `ε`, `0 ≤ d Q i ≤ a Q` and
`∑ᵢ d Q i ≥ |S| a Q`. If the errors are small, some `Q` has `a Q > 0` and
`{i | a Q ≤ 2 d Q i} = S`. -/
theorem exists_round {ι : Type*} {n : ℕ} (𝒬 : Finset ι) (S : Finset (Fin n)) (a : ι → ℝ)
    (d : ι → Fin n → ℝ) {L U ε : ℝ} (hL0 : 0 < L) (hε : 0 ≤ ε) (hL : L ≤ ∑ Q ∈ 𝒬, a Q)
    (hU : ∑ Q ∈ 𝒬, ∑ i ∈ Sᶜ, d Q i ≤ U) (hd0 : ∀ Q i, -ε ≤ d Q i)
    (hd1 : ∀ Q i, d Q i ≤ a Q + ε) (hsum : ∀ Q, S.card * a Q - ε ≤ ∑ i, d Q i)
    (hsmall : 2 * (U + 𝒬.card * n * ε) / L + n * (2 * 𝒬.card * ε / L) < 1 / 2) :
    ∃ Q ∈ 𝒬, 0 < a Q ∧ univ.filter (fun i ↦ a Q ≤ 2 * d Q i) = S := by
  classical
  set c := 2 * (U + 𝒬.card * n * ε) / L with hc
  set τ := L / (2 * 𝒬.card) with hτ
  have hn : (Sᶜ.card : ℝ) ≤ n := by
    have := card_le_univ Sᶜ
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hinner : ∀ Q, -(n * ε) ≤ ∑ i ∈ Sᶜ, d Q i := fun Q ↦ by
    calc -(n * ε) ≤ -(Sᶜ.card * ε) := by nlinarith
      _ = ∑ _i ∈ Sᶜ, -ε := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum fun i _ ↦ hd0 Q i
  have hne : 𝒬.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hL
    linarith
  have hQ0 : (0 : ℝ) < 𝒬.card := by exact_mod_cast hne.card_pos
  have hτ0 : 0 < τ := by positivity
  have hcU : 0 ≤ U + 𝒬.card * n * ε := by
    have : -(𝒬.card * (n * ε)) ≤ ∑ Q ∈ 𝒬, ∑ i ∈ Sᶜ, d Q i := by
      calc -(𝒬.card * (n * ε)) = ∑ _Q ∈ 𝒬, -(n * ε) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := sum_le_sum fun Q _ ↦ hinner Q
    nlinarith
  have hc0 : 0 ≤ c := by positivity
  -- (i) Some `Q` has `a Q ≥ τ` and `∑_{i ∉ S} d Q i ≤ c a Q`.
  have hgood : ∃ Q ∈ 𝒬, τ ≤ a Q ∧ ∑ i ∈ Sᶜ, d Q i ≤ c * a Q := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    set 𝒬₁ := 𝒬.filter (fun Q ↦ τ ≤ a Q)
    set 𝒬₀ := 𝒬.filter (fun Q ↦ ¬ τ ≤ a Q)
    have hsplit : ∀ f : ι → ℝ, ∑ Q ∈ 𝒬, f Q = ∑ Q ∈ 𝒬₁, f Q + ∑ Q ∈ 𝒬₀, f Q :=
      fun f ↦ (sum_filter_add_sum_filter_not 𝒬 _ f).symm
    have h0 : ∑ Q ∈ 𝒬₀, a Q ≤ L / 2 := by
      calc ∑ Q ∈ 𝒬₀, a Q ≤ ∑ _Q ∈ 𝒬₀, τ :=
            sum_le_sum fun Q hQ ↦ (not_le.1 (mem_filter.1 hQ).2).le
        _ = 𝒬₀.card * τ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ 𝒬.card * τ := by
            gcongr
            exact filter_subset _ _
        _ = L / 2 := by rw [hτ]; field_simp
    have h1 : L / 2 ≤ ∑ Q ∈ 𝒬₁, a Q := by
      have := hsplit a
      linarith
    have hne₁ : 𝒬₁.Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at h1
      linarith
    have hlt : c * ∑ Q ∈ 𝒬₁, a Q < ∑ Q ∈ 𝒬₁, ∑ i ∈ Sᶜ, d Q i := by
      rw [mul_sum]
      exact sum_lt_sum_of_nonempty hne₁ fun Q hQ ↦
        hcon Q (mem_filter.1 hQ).1 (mem_filter.1 hQ).2
    have hge0 : -(𝒬.card * (n * ε)) ≤ ∑ Q ∈ 𝒬₀, ∑ i ∈ Sᶜ, d Q i := by
      calc -(𝒬.card * (n * ε)) ≤ -(𝒬₀.card * (n * ε)) := by
            have : (𝒬₀.card : ℝ) ≤ 𝒬.card := by exact_mod_cast card_le_card (filter_subset _ _)
            exact neg_le_neg (mul_le_mul_of_nonneg_right this (by positivity))
        _ = ∑ _Q ∈ 𝒬₀, -(n * ε) := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := sum_le_sum fun Q _ ↦ hinner Q
    have hcL : c * (L / 2) = U + 𝒬.card * n * ε := by rw [hc]; field_simp
    have hs := hsplit fun Q ↦ ∑ i ∈ Sᶜ, d Q i
    have hm := mul_le_mul_of_nonneg_left h1 hc0
    have hassoc : (𝒬.card : ℝ) * (n * ε) = 𝒬.card * n * ε := by ring
    linarith
  obtain ⟨Q, hQ, hτQ, hbQ⟩ := hgood
  have ha : 0 < a Q := hτ0.trans_le hτQ
  have herr : n * (ε / a Q) ≤ n * (2 * 𝒬.card * ε / L) := by
    have : ε / a Q ≤ ε / τ := div_le_div_of_nonneg_left hε hτ0 hτQ
    have h2 : ε / τ = 2 * 𝒬.card * ε / L := by rw [hτ]; field_simp
    rw [h2] at this
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
  have hsmall' : c + n * (ε / a Q) < 1 / 2 := by linarith
  have hkn : (S.card : ℝ) ≤ n := by
    have := card_le_univ S
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  refine ⟨Q, hQ, ha, ?_⟩
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · -- A vertex outside `S` has `d Q i ≤ c a Q + n ε < a Q / 2`.
    intro hi
    by_contra hiS
    have hiSc : i ∈ Sᶜ := mem_compl.2 hiS
    have hrest : -((n : ℝ) * ε) ≤ ∑ j ∈ Sᶜ.erase i, d Q j := by
      calc -((n : ℝ) * ε) ≤ -((Sᶜ.erase i).card * ε) := by
            have h1 : ((Sᶜ.erase i).card : ℝ) ≤ Sᶜ.card := by
              exact_mod_cast card_le_card (erase_subset i Sᶜ)
            exact neg_le_neg (mul_le_mul_of_nonneg_right (h1.trans hn) hε)
        _ = ∑ _j ∈ Sᶜ.erase i, -ε := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ _ := sum_le_sum fun j _ ↦ hd0 Q j
    have := add_sum_erase Sᶜ (d Q) hiSc
    have hdi : d Q i ≤ c * a Q + n * ε := by linarith
    have hne' : (n : ℝ) * ε = n * (ε / a Q) * a Q := by field_simp
    have h2 : 2 * d Q i ≤ 2 * (c + n * (ε / a Q)) * a Q := by nlinarith
    have h3 : 2 * (c + n * (ε / a Q)) * a Q < a Q := by nlinarith
    linarith
  · -- A vertex of `S` with `d Q i < a Q / 2` would leave too little for `∑ᵢ d Q i`.
    intro hiS
    by_contra hlt
    rw [not_le] at hlt
    have hS : ∑ j ∈ S, d Q j < a Q / 2 + (S.card - 1) * (a Q + ε) := by
      have := add_sum_erase S (d Q) hiS
      have hrest : ∑ j ∈ S.erase i, d Q j ≤ (S.card - 1) * (a Q + ε) := by
        calc ∑ j ∈ S.erase i, d Q j ≤ ∑ _j ∈ S.erase i, (a Q + ε) :=
              sum_le_sum fun j _ ↦ hd1 Q j
          _ = (S.card - 1) * (a Q + ε) := by
              rw [sum_const, card_erase_of_mem hiS, nsmul_eq_mul, Nat.cast_sub
                (card_pos.2 ⟨i, hiS⟩)]
              simp
      linarith
    have hall := sum_add_sum_compl S (d Q)
    have := hsum Q
    have hkε : (S.card : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right hkn hε
    have hne' : (n : ℝ) * ε = n * (ε / a Q) * a Q := by field_simp
    -- `a/2 < c a + k ε ≤ (c + n ε / a) a < a / 2`.
    have h2 : a Q / 2 < c * a Q + S.card * ε := by nlinarith
    have h3 : (c + n * (ε / a Q)) * a Q < a Q / 2 := by nlinarith
    nlinarith

/-! ### Maximal coverage, algebraically -/

/-- If `‖m‖² ≤ ‖(1 - λ) m + λ u‖² + γ'` for the indicator `u` of a `k`-set, then
`⟨m, u⟩ ≥ ‖m‖² - λ (‖m‖² + k) - γ'/λ`, for `0 < λ ≤ 1/2`. -/
theorem coverage_bound {n : ℕ} (m u : Fin n → ℝ) {k t γ' : ℝ} (hu : ∀ i, u i = 0 ∨ u i = 1)
    (hk : ∑ i, u i = k) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (hγ : 0 ≤ γ')
    (h : ∑ i, m i ^ 2 ≤ ∑ i, ((1 - t) * m i + t * u i) ^ 2 + γ') :
    ∑ i, m i ^ 2 - t * (∑ i, m i ^ 2 + k) - γ' / t ≤ ∑ i, m i * u i := by
  set a := ∑ i, m i ^ 2
  set b := ∑ i, m i * u i
  have hu2 : ∑ i, u i ^ 2 = k := by
    rw [← hk]
    exact sum_congr rfl fun i _ ↦ by rcases hu i with h | h <;> rw [h] <;> norm_num
  have hexp : ∑ i, ((1 - t) * m i + t * u i) ^ 2 = (1 - t) ^ 2 * a + 2 * t * (1 - t) * b +
      t ^ 2 * k := by
    rw [← hu2]
    simp only [a, b, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hexp] at h
  have ha : 0 ≤ a := sum_nonneg fun i _ ↦ sq_nonneg _
  have hk0 : 0 ≤ k := by
    rw [← hk]
    exact sum_nonneg fun i _ ↦ by rcases hu i with h | h <;> simp [h]
  have hγt : 0 ≤ γ' / t := div_nonneg hγ ht0.le
  -- `2 t (1 - t) b ≥ (2t - t²) a - t² k - γ'`, so `b ≥ N / (2 (1 - t))` with `N` below.
  set N := (2 - t) * a - t * k - γ' / t
  have hN : N ≤ 2 * (1 - t) * b := by
    have : t * N ≤ t * (2 * (1 - t) * b) := by
      simp only [N]
      rw [mul_sub, mul_sub, mul_div_cancel₀ _ ht0.ne']
      nlinarith
    exact le_of_mul_le_mul_left this ht0
  have hR : a - t * (a + k) - γ' / t ≤ N := by simp only [N]; nlinarith
  have hR2 : 2 * (a - t * (a + k) - γ' / t) ≤ N := by simp only [N]; nlinarith
  have ht1' : 0 < 1 - t := by linarith
  rcases le_total 0 b with hb | hb
  · -- `2 b ≥ 2 (1 - t) b ≥ N ≥ 2 R`.
    have : 2 * (1 - t) * b ≤ 2 * b := by nlinarith
    linarith
  · -- `b ≥ 2 (1 - t) b ≥ N ≥ R`, and `R ≤ 0` here.
    have : 2 * (1 - t) * b ≤ b := by nlinarith
    linarith

/-! ### Hölder for every exponent -/

/-- **The tangent line** of `x^(m+2)` at `c`:
`x^(m+2) - c^(m+2) - (m+2) c^(m+1) (x - c) = (x - c)² ∑_{j ≤ m} (j + 1) c^j x^(m-j)`. -/
theorem tangent_identity {R : Type*} [CommRing R] (x c : R) (m : ℕ) :
    x ^ (m + 2) - c ^ (m + 2) - ((m : R) + 2) * c ^ (m + 1) * (x - c) =
      (x - c) ^ 2 * ∑ j ∈ range (m + 1), ((j : R) + 1) * c ^ j * x ^ (m - j) := by
  induction m with
  | zero => simp; ring
  | succ m ih =>
    rw [sum_range_succ]
    have hsum : ∑ j ∈ range (m + 1), ((j : R) + 1) * c ^ j * x ^ (m + 1 - j) =
        x * ∑ j ∈ range (m + 1), ((j : R) + 1) * c ^ j * x ^ (m - j) := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj ↦ ?_
      rw [show m + 1 - j = m - j + 1 by have := mem_range.1 hj; omega, pow_succ]
      ring
    rw [hsum, Nat.sub_self, pow_zero, mul_one]
    push_cast
    linear_combination x * ih

/-- `Ẽ[s^(m+2)] = Ẽ[s]^(m+2) + ∑_{j ≤ m} (j + 1) Ẽ[s]^j Ẽ[(s - Ẽ[s])² s^(m-j)]`, from the
tangent line at `Ẽ[s]`. -/
theorem apply_pow_eq {σ : Type*} {ℓ : ℕ} (E : PseudoExpectation σ ℓ) (s : MvPolynomial σ ℝ)
    (m : ℕ) : E (s ^ (m + 2)) = E s ^ (m + 2) +
      ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * E s ^ j * E ((s - C (E s)) ^ 2 * s ^ (m - j)) := by
  set c := E s
  have hid := tangent_identity s (C c) m
  have hsum : (s - C c) ^ 2 * ∑ j ∈ range (m + 1), ((j : MvPolynomial σ ℝ) + 1) * C c ^ j *
      s ^ (m - j) = ∑ j ∈ range (m + 1), C (((j : ℝ) + 1) * c ^ j) * ((s - C c) ^ 2 *
        s ^ (m - j)) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ ↦ ?_
    simp only [map_mul, map_add, map_natCast, map_one, map_pow]
    ring
  have hpoly : s ^ (m + 2) = C (c ^ (m + 2)) + C (((m : ℝ) + 2) * c ^ (m + 1)) * (s - C c) +
      ∑ j ∈ range (m + 1), C (((j : ℝ) + 1) * c ^ j) * ((s - C c) ^ 2 * s ^ (m - j)) := by
    rw [← hsum]
    simp only [map_mul, map_add, map_natCast, map_ofNat, map_pow]
    linear_combination hid
  rw [hpoly, PseudoExpectation.map_add, PseudoExpectation.map_add, PseudoExpectation.map_C,
    PseudoExpectation.map_C_mul, PseudoExpectation.map_sub, PseudoExpectation.map_C,
    PseudoExpectation.map_sum]
  simp only [PseudoExpectation.map_C_mul]
  rw [show E s - c = 0 from sub_self c, mul_zero, add_zero]

/-! ### The rounding of the solver's output -/

/-- The product `∏ᵢ (1 + ‖fᵢ‖₂)` over the constraints of the clique program: the price, per unit
of `‖·‖₁` of the multipliers, of using a proof against an approximate pseudo-expectation
(`SoS.DerivesN.approx_ge`). -/
noncomputable def constraintNorm (n k ℓ : ℕ) (L : List (ℕ × ℕ)) : ℝ :=
  ∏ i : Fin (Clique.realSystem n k ℓ L).length,
    (1 + coeffNorm ((Clique.realSystem n k ℓ L).get i))

theorem constraintNorm_nonneg (n k ℓ : ℕ) (L : List (ℕ × ℕ)) : 0 ≤ constraintNorm n k ℓ L :=
  prod_nonneg fun i _ ↦ by
    have := coeffNorm_nonneg ((Clique.realSystem n k ℓ L).get i)
    linarith

/-- The error `(η + γ) 2 · 10^(T+1) ∏ᵢ (1 + ‖fᵢ‖₂)` of the approximate Boolean and size
constraints used by the rounding. -/
noncomputable def err (n k ℓ : ℕ) (L : List (ℕ × ℕ)) (η γ : ℝ) (T : ℕ) : ℝ :=
  (η + γ) * (2 * 10 ^ (T + 1)) * constraintNorm n k ℓ L

/-- The lower bound `(k - ε)²/n - λ (4n + k) - (η + γ)` on `Ẽ[∑_{i ∈ S} wᵢ]` from maximal
coverage, with `λ = γ / (η + γ)`. -/
noncomputable def coverage (n k : ℕ) (η γ ε : ℝ) : ℝ :=
  (k - ε) ^ 2 / n - γ / (η + γ) * (4 * n + k) - (η + γ)

/-- `w_Q = ∏ⱼ w_{Qⱼ}`. -/
noncomputable def wQ {n T : ℕ} (Q : Fin T → Fin n) : MvPolynomial (Fin n) ℝ := ∏ j, X (Q j)

theorem litProd_ofFn {n T : ℕ} (Q : Fin T → Fin n) :
    litProd (List.ofFn fun j ↦ (true, Q j)) = wQ Q := by
  simp [litProd, lit, wQ, List.prod_ofFn]

/-- `(∑_{u ∈ S} xᵤ)^i = ∑_{Q ∈ S^i} w_Q`. -/
theorem pow_sum_X_eq {n : ℕ} (S : Finset (Fin n)) (i : ℕ) :
    (∑ u ∈ S, (X u : MvPolynomial (Fin n) ℝ)) ^ i =
      ∑ Q ∈ Fintype.piFinset fun _ : Fin i ↦ S, wQ Q := by
  rw [← Fin.prod_const, prod_univ_sum]
  rfl

/-- The error `(η + γ) ∏ᵢ (1 + ‖fᵢ‖₂) · 2 T² (30k + 20)^T` of Hölder for `T`
(`BKS23.Rounding.apply_pow_eq`, with the Boolean constraints). -/
noncomputable def errH (n k ℓ : ℕ) (L : List (ℕ × ℕ)) (η γ : ℝ) (T : ℕ) : ℝ :=
  (η + γ) * constraintNorm n k ℓ L * (2 * (T : ℝ) ^ 2 * (30 * k + 20) ^ T)

theorem errH_nonneg (n k ℓ : ℕ) (L : List (ℕ × ℕ)) {η γ : ℝ} (hηγ : 0 ≤ η + γ) (T : ℕ) :
    0 ≤ errH n k ℓ L η γ T := by
  unfold errH
  have := constraintNorm_nonneg n k ℓ L
  positivity

/-- **Hölder for every exponent** [BKS23, Lemma 5.4]: if `Ẽ` satisfies Boolean constraints up to
`η` and `0 ≤ Ẽ[s] ≤ 2k` for `s = ∑_{u ∈ S} xᵤ`, `|S| = k`, then
`Ẽ[s^T] ≥ Ẽ[s]^T - η ∏ᵢ (1 + ‖fᵢ‖₂) · 2 T² (30k + 20)^T`. By the tangent line at `Ẽ[s]`
(`BKS23.Rounding.apply_pow_eq`): each `(s - Ẽ[s])² s^i` is a sum of squares times a product of
literals, so it has a small proof from the Boolean constraints. -/
theorem holder {n k ℓ T : ℕ} {A : System (Fin n) ℝ} (hB : Boolean A) {S : Finset (Fin n)}
    (hS : S.card = k) {E : PseudoExpectation (Fin n) ℓ} {η : ℝ} (hη : 0 ≤ η)
    (hA : E.ApproxSatisfies A η 0) (hℓ : 2 * T ≤ ℓ) (hc0 : 0 ≤ E (∑ u ∈ S, X u))
    (hck : E (∑ u ∈ S, X u) ≤ 2 * k) :
    E (∑ u ∈ S, X u) ^ T - η * (∏ i : Fin A.length, (1 + coeffNorm (A.get i))) *
      (2 * (T : ℝ) ^ 2 * (30 * k + 20) ^ T) ≤ E ((∑ u ∈ S, X u) ^ T) := by
  set s : MvPolynomial (Fin n) ℝ := ∑ u ∈ S, X u
  set PN := ∏ i : Fin A.length, (1 + coeffNorm (A.get i)) with hPN
  have hPN0 : 0 ≤ PN := prod_nonneg fun i _ ↦ by
    have := coeffNorm_nonneg (A.get i)
    linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hsdeg : s.totalDegree ≤ 1 := totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X]
  obtain _ | _ | m := T
  · have : 0 ≤ η * PN * (2 * ((0 : ℕ) : ℝ) ^ 2 * (30 * (k : ℝ) + 20) ^ 0) := by
      push_cast; positivity
    simp only [pow_zero, PseudoExpectation.map_one] at this ⊢
    linarith
  · have : 0 ≤ η * PN * (2 * ((0 + 1 : ℕ) : ℝ) ^ 2 * (30 * (k : ℝ) + 20) ^ (0 + 1)) := by
      push_cast; positivity
    simp only [zero_add, pow_one] at this ⊢
    linarith
  rw [apply_pow_eq]
  set c := E s with hcdef
  -- `Ẽ[(s - c)² s^i] ≥ -η k^i (k + c)² 2·10^i ∏ (1 + ‖fᵢ‖₂)`.
  have hs1 : coeffNorm1 s ≤ k :=
    (coeffNorm1_sum_le _ _).trans (by simp [coeffNorm1_X, hS])
  have hs2 : coeffNorm1 ((s - C c) ^ 2) ≤ (k + c) ^ 2 := by
    refine (coeffNorm1_pow_le _ 2).trans (pow_le_pow_left₀ (coeffNorm1_nonneg _) ?_ 2)
    refine (coeffNorm1_sub_le _ _).trans ?_
    rw [coeffNorm1_C, abs_of_nonneg hc0]
    linarith
  have hs2d : ((s - C c) ^ 2).totalDegree ≤ 2 := (totalDegree_pow _ 2).trans (by
    have := (totalDegree_sub s (C c)).trans (max_le hsdeg (by rw [totalDegree_C]; omega))
    omega)
  have hDN : ∀ i : ℕ, DerivesN A (2 + 2 * i) ((k : ℝ) ^ i * ((k + c) ^ 2 * (2 * 10 ^ i)))
      ((s - C c) ^ 2 * s ^ i) := by
    intro i
    have h := DerivesN.sum (Fintype.piFinset fun _ : Fin i ↦ S) fun f _ ↦
      ((hB.litProd_nonneg (List.ofFn fun j ↦ (true, f j))).mulSOS (IsSOS.sq (s - C c))).mono
        (k' := 2 + 2 * i) (by rw [List.length_ofFn]; omega)
        (M' := (k + c) ^ 2 * (2 * 10 ^ i)) (by
          rw [List.length_ofFn]
          exact mul_le_mul_of_nonneg_right hs2 (by positivity))
    refine (h.mono le_rfl (le_of_eq ?_)).congr ?_
    · rw [sum_const, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hS,
        nsmul_eq_mul]
      push_cast
      ring
    · rw [pow_sum_X_eq S i, mul_sum]
      exact sum_congr rfl fun f _ ↦ by rw [litProd_ofFn]
  have hterm : ∀ j ∈ range (m + 1), -(η * ((k : ℝ) ^ (m - j) *
      ((k + c) ^ 2 * (2 * 10 ^ (m - j)))) * PN) ≤ E ((s - C c) ^ 2 * s ^ (m - j)) :=
    fun j _ ↦ (hDN (m - j)).approx_ge hη hA (by omega)
  -- Each term of the sum is at most `(m + 2) η Π 2 (3k + 2)^(m+2) 10^(m+2)` in absolute value.
  set K : ℝ := 3 * k + 2 with hK
  have hB0 : 0 ≤ η * PN * 2 := by positivity
  have hbound : ∀ j ∈ range (m + 1), ((j : ℝ) + 1) * c ^ j * (η * ((k : ℝ) ^ (m - j) *
      ((k + c) ^ 2 * (2 * 10 ^ (m - j)))) * PN) ≤
        ((m : ℝ) + 2) * (η * PN * 2) * (K ^ (m + 2) * 10 ^ (m + 2)) := by
    intro j hj
    have hjm := mem_range.1 hj
    have hcK : c ≤ K := by linarith
    have hkK : (k : ℝ) ≤ K := by linarith
    have hkcK : (k : ℝ) + c ≤ K := by linarith
    have hX0 : 0 ≤ c ^ j * (k : ℝ) ^ (m - j) * (k + c) ^ 2 :=
      mul_nonneg (mul_nonneg (pow_nonneg hc0 j) (pow_nonneg hk0 _)) (sq_nonneg _)
    have h1 : c ^ j * (k : ℝ) ^ (m - j) * (k + c) ^ 2 ≤ K ^ (m + 2) := by
      calc c ^ j * (k : ℝ) ^ (m - j) * (k + c) ^ 2 ≤ K ^ j * K ^ (m - j) * K ^ 2 :=
            mul_le_mul (mul_le_mul (pow_le_pow_left₀ hc0 hcK j)
              (pow_le_pow_left₀ hk0 hkK _) (pow_nonneg hk0 _) (by positivity))
              (pow_le_pow_left₀ (by linarith) hkcK 2) (sq_nonneg _) (by positivity)
        _ = K ^ (m + 2) := by rw [← pow_add, ← pow_add]; congr 1; omega
    have h2 : (10 : ℝ) ^ (m - j) ≤ 10 ^ (m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (j : ℝ) + 1 ≤ m + 2 := by
      have : (j : ℝ) ≤ m := by exact_mod_cast (by omega : j ≤ m)
      linarith
    have heq : ((j : ℝ) + 1) * c ^ j * (η * ((k : ℝ) ^ (m - j) * ((k + c) ^ 2 *
        (2 * 10 ^ (m - j)))) * PN) = ((j : ℝ) + 1) * (η * PN * 2) *
          ((c ^ j * (k : ℝ) ^ (m - j) * (k + c) ^ 2) * 10 ^ (m - j)) := by ring
    rw [heq]
    exact mul_le_mul (mul_le_mul_of_nonneg_right h3 hB0)
      (mul_le_mul h1 h2 (by positivity) (by positivity)) (mul_nonneg hX0 (by positivity))
      (by positivity)
  have hsum : -(((m : ℝ) + 1) * (((m : ℝ) + 2) * (η * PN * 2) *
      (K ^ (m + 2) * 10 ^ (m + 2)))) ≤ ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * c ^ j *
        E ((s - C c) ^ 2 * s ^ (m - j)) := by
    calc -(((m : ℝ) + 1) * (((m : ℝ) + 2) * (η * PN * 2) * (K ^ (m + 2) * 10 ^ (m + 2))))
        = ∑ _j ∈ range (m + 1), -(((m : ℝ) + 2) * (η * PN * 2) *
            (K ^ (m + 2) * 10 ^ (m + 2))) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
      _ ≤ ∑ j ∈ range (m + 1), ((j : ℝ) + 1) * c ^ j * E ((s - C c) ^ 2 * s ^ (m - j)) :=
          sum_le_sum fun j hj ↦ by
            have hcj : 0 ≤ ((j : ℝ) + 1) * c ^ j := by positivity
            have h1 := mul_le_mul_of_nonneg_left (hterm j hj) hcj
            have h2 := hbound j hj
            have e : ((j : ℝ) + 1) * c ^ j * -(η * ((k : ℝ) ^ (m - j) *
                ((k + c) ^ 2 * (2 * 10 ^ (m - j)))) * PN) = -(((j : ℝ) + 1) * c ^ j *
                  (η * ((k : ℝ) ^ (m - j) * ((k + c) ^ 2 * (2 * 10 ^ (m - j)))) * PN)) := by
              ring
            linarith
  have h10K : K ^ (m + 2) * 10 ^ (m + 2) = (30 * (k : ℝ) + 20) ^ (m + 2) := by
    rw [← mul_pow, hK]; ring_nf
  have herr : ((m : ℝ) + 1) * (((m : ℝ) + 2) * (η * PN * 2) * (K ^ (m + 2) * 10 ^ (m + 2))) ≤
      η * PN * (2 * (((m + 2 : ℕ)) : ℝ) ^ 2 * (30 * k + 20) ^ (m + 2)) := by
    rw [h10K]
    push_cast
    have : 0 ≤ η * PN * (30 * (k : ℝ) + 20) ^ (m + 2) := by positivity
    nlinarith
  linarith

/-- **The rounding** [BKS23, Theorem 5.1, Lemmas 5.3–5.5]. Let `Ẽ` satisfy the clique program
of `G` up to `η + γ`, with objective within `γ` of every pseudo-expectation satisfying it up to
`η`, and let `S` be a `k`-clique of `G` whose cut has the certificate
`|x|^T |y| ≤ ω` (multipliers of `‖·‖₁ ≤ M`, degree `D ≤ ℓ`), with `2T + 2 ≤ ℓ`. If the
approximation errors are small and the ratio `ω / L` with `L = coverage^T - errH` (about
`ω (n/k²)^T`) is below `1/4` (`hsmall`), then `S_Q = {i | Ẽ[w_Q] ≤ 2 Ẽ[w_Q wᵢ]}` is `S` for some
`T`-tuple `Q`. -/
theorem exists_round_eq {n k ℓ T D : ℕ} {L : List (ℕ × ℕ)} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} (hS : G.IsNClique k S) (hLc : Clique.ListsNonEdges G L)
    (hLs : Clique.OnlyNonEdges G L) {E : PseudoExpectation (Fin n) ℓ} {η γ : ℝ} (hη : 0 < η)
    (hγ : 0 < γ) (hγη : γ ≤ η)
    (hE : E.ApproxSatisfies (Clique.problem n k ℓ L).system (η + γ) 0)
    (hopt : ∀ E' : PseudoExpectation (Fin n) ℓ,
      E'.ApproxSatisfies (Clique.problem n k ℓ L).system η 0 →
        (Clique.problem n k ℓ L).objective E ≤ (Clique.problem n k ℓ L).objective E' + γ)
    (hℓ : 2 * T + 2 ≤ ℓ) {ω M : ℝ} (hD : D ≤ ℓ)
    (hcert : DerivesN (Clique.realSystem n k ℓ L) D M
      (C ω - (∑ u ∈ S, X u) ^ T * ∑ v ∈ Sᶜ, X v))
    (hε1 : err n k ℓ L η γ T ≤ 1) (hεk : err n k ℓ L η γ T ≤ k)
    (hcov : 0 < coverage n k η γ (err n k ℓ L η γ T))
    (hLpos : 0 < coverage n k η γ (err n k ℓ L η γ T) ^ T - errH n k ℓ L η γ T)
    (hsmall : 2 * (ω + (η + γ) * M * constraintNorm n k ℓ L +
        (k : ℝ) ^ T * n * err n k ℓ L η γ T) /
          (coverage n k η γ (err n k ℓ L η γ T) ^ T - errH n k ℓ L η γ T) +
      n * (2 * (k : ℝ) ^ T * err n k ℓ L η γ T /
        (coverage n k η γ (err n k ℓ L η γ T) ^ T - errH n k ℓ L η γ T)) < 1 / 2) :
    ∃ Q : Fin T → Fin n, univ.filter (fun i ↦ E (wQ Q) ≤ 2 * E (wQ Q * X i)) = S := by
  classical
  set A := Clique.realSystem n k ℓ L
  set PN := constraintNorm n k ℓ L with hPN
  set ε := err n k ℓ L η γ T with hεdef
  have hPN0 : 0 ≤ PN := constraintNorm_nonneg n k ℓ L
  have hηγ : 0 ≤ η + γ := by linarith
  have hε0 : 0 ≤ ε := by rw [hεdef, err]; positivity
  have hA : E.ApproxSatisfies A (η + γ) 0 := hE.map_toReal
  have hAx : Biclique.Axioms A S G.Adj k := Clique.axioms hLc fun _ _ _ _ h ↦ h
  have hB := hAx.bool
  have hcardEq : DerivesEq A 1 1 (∑ i, X i - C (k : ℝ)) :=
    hAx.card.derivesEq ((totalDegree_sub _ _).trans
      (max_le (totalDegree_finsetSum_le fun i _ ↦ by rw [totalDegree_X])
        (by rw [totalDegree_C]; omega))) le_rfl
  -- Approximate soundness, with the error `ε`.
  have hsound : ∀ {d : ℕ} {M' : ℝ} {g : MvPolynomial (Fin n) ℝ}, d ≤ ℓ →
      M' ≤ 2 * 10 ^ (T + 1) → DerivesN A d M' g → -ε ≤ E g := by
    intro d M' g hd hM' h
    refine le_trans ?_ (h.approx_ge hηγ hA hd)
    rw [neg_le_neg_iff, hεdef, err, ← hPN]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM' hηγ) hPN0
  have hlit : ∀ l : List (Bool × Fin n), l.length ≤ T + 1 → -ε ≤ E (litProd l) := by
    intro l hl
    refine hsound (by omega) ?_ (hB.litProd_nonneg l)
    have : (10 : ℝ) ^ l.length ≤ 10 ^ (T + 1) := pow_le_pow_right₀ (by norm_num) hl
    linarith
  -- The approximate constraints on `Ẽ[w_Q wᵢ]`.
  have hd0 : ∀ (Q : Fin T → Fin n) i, -ε ≤ E (wQ Q * X i) := by
    intro Q i
    have := hlit ((true, i) :: List.ofFn fun j ↦ (true, Q j)) (by simp)
    simp only [litProd_cons, litProd_ofFn, lit, ↓reduceIte] at this
    rwa [mul_comm] at this
  have hd1 : ∀ (Q : Fin T → Fin n) i, E (wQ Q * X i) ≤ E (wQ Q) + ε := by
    intro Q i
    have := hlit ((false, i) :: List.ofFn fun j ↦ (true, Q j)) (by simp)
    simp only [litProd_cons, litProd_ofFn, lit, Bool.false_eq_true, ↓reduceIte, sub_mul,
      one_mul, PseudoExpectation.map_sub] at this
    rw [mul_comm] at this
    linarith
  have hsum : ∀ Q : Fin T → Fin n, S.card * E (wQ Q) - ε ≤ ∑ i, E (wQ Q * X i) := by
    intro Q
    have hw : (wQ Q).totalDegree ≤ T := (totalDegree_finsetProd _ _).trans (by simp)
    have hwn : coeffNorm1 (wQ Q) ≤ 1 := coeffNorm1_prod_X_le' Q
    have := hsound (by omega) (by
      have : (coeffNorm1 (wQ Q) + 1) ^ 2 * 1 ≤ 4 := by
        nlinarith [coeffNorm1_nonneg (wQ Q)]
      have : (4 : ℝ) ≤ 2 * 10 ^ (T + 1) := by
        have : (10 : ℝ) ≤ 10 ^ (T + 1) := le_self_pow₀ (by norm_num) (by omega)
        linarith
      linarith) ((hcardEq.mul (wQ Q)).1)
    rw [hS.card_eq]
    rw [mul_sub, mul_sum, PseudoExpectation.map_sub, PseudoExpectation.map_sum,
      mul_comm (wQ Q) (C _), PseudoExpectation.map_C_mul] at this
    linarith
  -- Maximal coverage: `Ẽ[s] ≥ coverage`.
  have hm0 : ∀ i, -ε ≤ E (X i) := fun i ↦ by
    have := hlit [(true, i)] (by simp)
    simpa [litProd, lit] using this
  have hm1 : ∀ i, E (X i) ≤ 1 + ε := fun i ↦ by
    have := hlit [(false, i)] (by simp)
    simp [litProd, lit] at this
    linarith
  have hsumm : (k : ℝ) - ε ≤ ∑ i, E (X i) := by
    have := hsound (by omega) (by
      have : (10 : ℝ) ≤ 10 ^ (T + 1) := le_self_pow₀ (by norm_num) (by omega)
      linarith) hcardEq.1
    rw [PseudoExpectation.map_sub, PseudoExpectation.map_sum, PseudoExpectation.map_C] at this
    linarith
  set t := γ / (η + γ) with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 / 2 := by rw [htdef, div_le_iff₀ (by linarith)]; linarith
  have hmixη : (1 - t) * (η + γ) + t * 0 = η := by rw [htdef]; field_simp; ring
  set y := Clique.planted S
  have hy : ∀ f ∈ (Clique.problem n k ℓ L).system, 0 ≤ eval y (toReal f) := by
    intro f hf
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hf
    exact (Clique.eval_planted hS hLs hr).ge
  set E' := PseudoExpectation.mix E (SoS.Correct.ofPoint ℓ y) t ht0.le (by linarith)
  have hE' : E'.ApproxSatisfies (Clique.problem n k ℓ L).system η 0 := by
    have := hE.mix (SoS.Correct.ofPoint_approxSatisfies (ℓ := ℓ) hy le_rfl) ht0.le
      (by linarith : t ≤ 1)
    rwa [hmixη] at this
  have hobj := hopt E' hE'
  rw [Clique.objective_eq, Clique.objective_eq] at hobj
  have hE'X : ∀ i, E' (X i) = (1 - t) * E (X i) + t * y i := fun i ↦ by
    rw [PseudoExpectation.mix_apply, SoS.Correct.ofPoint_apply, eval_X]
  simp_rw [hE'X] at hobj
  have hu : ∀ i, y i = 0 ∨ y i = 1 := fun i ↦ by
    simp only [y, Clique.planted]
    split_ifs <;> simp
  have hcov' := coverage_bound (fun i ↦ E (X i)) y hu
    (by rw [Clique.sum_planted, hS.card_eq]) ht0 ht1 hγ.le hobj
  have hsS : E (∑ u ∈ S, X u) = ∑ i, E (X i) * y i := by
    rw [PseudoExpectation.map_sum]
    simp only [y, Clique.planted, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, univ_inter]
  have ha4 : ∑ i, E (X i) ^ 2 ≤ 4 * n := by
    calc ∑ i, E (X i) ^ 2 ≤ ∑ _i : Fin n, (4 : ℝ) := sum_le_sum fun i _ ↦ by
          nlinarith [hm0 i, hm1 i]
      _ = 4 * n := by simp; ring
  have haLow : ((k : ℝ) - ε) ^ 2 / n ≤ ∑ i, E (X i) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    have hcs := sq_sum_le_card_mul_sum_sq (s := univ) (f := fun i : Fin n ↦ E (X i))
    simp only [card_univ, Fintype.card_fin] at hcs
    have hk0 : 0 ≤ (k : ℝ) - ε := by linarith
    nlinarith [pow_le_pow_left₀ hk0 hsumm 2]
  have hcovE : coverage n k η γ ε ≤ E (∑ u ∈ S, X u) := by
    rw [hsS]
    have hγt : γ / t = η + γ := by rw [htdef]; field_simp
    rw [hγt] at hcov'
    simp only [coverage]
    have : t * (∑ i, E (X i) ^ 2 + k) ≤ t * (4 * n + k) := by gcongr
    linarith
  -- Hölder: `Ẽ[s^T] ≥ Ẽ[s]^T - errH ≥ coverage^T - errH`.
  set s : MvPolynomial (Fin n) ℝ := ∑ u ∈ S, X u
  have hc0 : 0 ≤ E s := hcov.le.trans hcovE
  have hck : E s ≤ 2 * k := by
    simp only [s, PseudoExpectation.map_sum]
    calc ∑ u ∈ S, E (X u) ≤ ∑ _u ∈ S, (2 : ℝ) := sum_le_sum fun u _ ↦ by linarith [hm1 u]
      _ = 2 * k := by rw [sum_const, hS.card_eq, nsmul_eq_mul]; ring
  have hL : coverage n k η γ ε ^ T - errH n k ℓ L η γ T ≤ E (s ^ T) := by
    have hH : E s ^ T - errH n k ℓ L η γ T ≤ E (s ^ T) :=
      holder hB hS.card_eq hηγ hA (by omega) hc0 hck
    have hcovT : coverage n k η γ ε ^ T ≤ E s ^ T := pow_le_pow_left₀ hcov.le hcovE T
    linarith
  -- The certificate: `Ẽ[s^T |y|] ≤ ω + (η + γ) M Π`.
  have hU : E (s ^ T * ∑ v ∈ Sᶜ, X v) ≤ ω + (η + γ) * M * PN := by
    have := hcert.approx_ge hηγ hA hD
    rw [PseudoExpectation.map_sub, PseudoExpectation.map_C] at this
    have hPN' : ∏ i, (1 + coeffNorm (A.get i)) = PN := rfl
    rw [hPN'] at this
    linarith
  -- The sums over `Q ∈ S^T`.
  have hexp : s ^ T = ∑ Q ∈ Fintype.piFinset fun _ : Fin T ↦ S, wQ Q := pow_sum_X_eq S T
  have hsumA : E (s ^ T) = ∑ Q ∈ Fintype.piFinset fun _ : Fin T ↦ S, E (wQ Q) := by
    rw [hexp, PseudoExpectation.map_sum]
  have hsumU : E (s ^ T * ∑ v ∈ Sᶜ, X v) =
      ∑ Q ∈ Fintype.piFinset fun _ : Fin T ↦ S, ∑ i ∈ Sᶜ, E (wQ Q * X i) := by
    rw [hexp, sum_mul, PseudoExpectation.map_sum]
    exact sum_congr rfl fun Q _ ↦ by rw [mul_sum, PseudoExpectation.map_sum]
  have hcardQ : ((Fintype.piFinset fun _ : Fin T ↦ S).card : ℝ) = (k : ℝ) ^ T := by
    rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, hS.card_eq]
    push_cast
    rfl
  obtain ⟨Q, -, -, hQ⟩ := exists_round (Fintype.piFinset fun _ : Fin T ↦ S) S
    (fun Q ↦ E (wQ Q)) (fun Q i ↦ E (wQ Q * X i)) hLpos hε0 (hsumA ▸ hL)
    (hsumU ▸ hU) hd0 hd1 hsum (by rw [hcardQ]; exact hsmall)
  exact ⟨Q, hQ⟩

end BKS23.Rounding
