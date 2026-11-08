module

public import BS23.SmallRadius.IdentCore
public import Background.SumOfSquares.Holder

/-!
# From the identifiability inequality to the cross moments, abstractly

The pseudo-expectation half of identifiability in the small-radius analysis
(`BS23/SmallRadius/Ident.lean`), for abstract polynomials. Let `Ẽ` be a pseudo-expectation of
degree `ℓ ≥ 22 t` that satisfies a system `A` up to `η`, where the soundness error of every
certificate of norm at most `W^(50 t)` is at most `1/4` (`sosErr A η (W^(50 t)) ≤ 1/4`). Let `P`
and `Q` be sums of Boolean variables (`0 ≤ P ≤ |T_P| ≤ W` in degree `2`, the same for `Q`), and
`D₁`, `D₂` polynomials of degree at most `2` with the identifiability inequality (H1) of
`BS23.SmallRadius.Core.H1Data.Good.H1`,

  `P^(2t) D₁^(2t) ≤ c P^(2t-m) D₁^t`,  `Q^(2t) D₂^(2t) ≤ c Q^(2t-m) D₂^t`,  `c = W^m (2^16 s)^t`,

in degree `9t` with norm `W^(48t)`, and with `D₁ + D₂ ≥ Δ²/2` (a sum of squares), `Δ² > 0`.
Then (`BS23.SmallRadius.Core.cross_abstract`)

  `Ẽ[P Q] ≤ 2 W² ρ^s + 1`,  `ρ = 2^18 s / Δ²`.

With `a_r = Ẽ[(PQ)^(2r)]`:
1. (H1) times the square `Q^(2t)` and approximate soundness:
   `Ẽ[(PQ)^(2t) D₁^(2t)] ≤ c Ẽ[P^(2t-m) Q^(2t) D₁^t] + 1/4`.
2. Cauchy–Schwarz on `(P^(t-m) Q^t)(P^t Q^t D₁^t)`, and `Q^(2m) ≤ W^(2m)` (approximately sound):
   `Ẽ[(PQ)^(2t) D₁^(2t)] ≤ c² W^(2m) a_(t-m) + (c² + 2)/4` (`BS23.SmallRadius.Core.side_bound`).
3. `D₁^(2t) + D₂^(2t) ≥ 2^(1-2t) (Δ²/2)^(2t)` (power mean and powers of `D₁ + D₂ ≥ Δ²/2`), times
   `(PQ)^(2t)`: `(Δ²/2)^(2t) a_t ≤ 2^(2t-1) (2 c² W^(2m) a_(t-m) + (c² + 2)/2)`.
4. Log-convexity `a_(t-m)^t ≤ a_t^(t-m)` and `Ẽ[PQ]^(2t) ≤ a_t`
   (`Background/SumOfSquares/Holder.lean`):
   if `Ẽ[PQ] > 1`, then `Ẽ[PQ]^(2m) ≤ 2 (W² ρ^s)^(2m)` (`BS23.SmallRadius.Core.final_real`).
-/

@[expose] public section

namespace BS23.SmallRadius.Core

open MvPolynomial Finset SoS

variable {σ : Type*}

/-! ### Soundness errors -/

/-- The soundness error `η (M + |A| (M + 1)²) ∏ᵢ (1 + ‖fᵢ‖₂)` of `SoS.SosPlusIdeal.approx_ge` for
a certificate of norm `M`. -/
noncomputable def sosErr (A : System σ ℝ) (η M : ℝ) : ℝ :=
  η * (M + A.length * (M + 1) ^ 2) * ∏ i : Fin A.length, (1 + coeffNorm (A.get i))

theorem sosErr_mono {A : System σ ℝ} {η M M' : ℝ} (hη : 0 ≤ η) (hM : 0 ≤ M) (h : M ≤ M') :
    sosErr A η M ≤ sosErr A η M' := by
  unfold sosErr
  have hp : 0 ≤ ∏ i : Fin A.length, (1 + coeffNorm (A.get i)) :=
    prod_nonneg fun i _ ↦ by have := coeffNorm_nonneg (A.get i); linarith
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hη) hp
  have : (M + 1) ^ 2 ≤ (M' + 1) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hA : (0 : ℝ) ≤ A.length := Nat.cast_nonneg _
  nlinarith

/-- **Approximate soundness with a norm budget**: a certificate of norm `M ≤ Λ` in degree `k`,
`2k ≤ ℓ`, has `Ẽ g ≥ -ε` when `sosErr A η Λ ≤ ε`. -/
theorem ge_of_sosPlusIdeal {ℓ : ℕ} {E : PseudoExpectation σ ℓ} {A : System σ ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hE : E.ApproxSatisfies A η 0) {k : ℕ} {M Λ ε : ℝ} {g : MvPolynomial σ ℝ}
    (hk : 2 * k ≤ ℓ) (h : SosPlusIdeal A k M g) (hM : M ≤ Λ) (hacc : sosErr A η Λ ≤ ε) :
    -ε ≤ E g := by
  have h1 := h.approx_ge hη hE hk
  have h2 := sosErr_mono (A := A) hη h.nonneg hM
  unfold sosErr at h2 hacc
  linarith

/-! ### Two real lemmas -/

/-- From `U ≤ c y + ε` and `y² ≤ V U`: `U ≤ c² V + 2 ε`. -/
theorem cs_real {U V y c ε : ℝ} (hU : 0 ≤ U) (hV : 0 ≤ V) (h1 : U ≤ c * y + ε)
    (h2 : y ^ 2 ≤ V * U) : U ≤ c ^ 2 * V + 2 * ε := by
  have hB : 0 ≤ (c ^ 2 * V + U) / 2 := by positivity
  have h3 : (c * y) ^ 2 ≤ ((c ^ 2 * V + U) / 2) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg c)
    nlinarith [sq_nonneg (c ^ 2 * V - U)]
  have h4 : c * y ≤ (c ^ 2 * V + U) / 2 := by
    by_contra h
    rw [not_le] at h
    have := mul_self_lt_mul_self hB h
    nlinarith
  linarith

/-- **The final real argument.** If `x > 1`, `x^(2t) ≤ a`, `b^t ≤ a^(t-m)` (`t = s m`),
`A' a ≤ C₁ b + ε` with `ε ≤ C₁`, `C₁ ≥ 0` and `A' > 0`, then `A' x^(2m) ≤ 2 C₁`. -/
theorem final_real {x a b A' C₁ ε : ℝ} {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hA : 0 < A')
    (hC : 0 ≤ C₁) (hε : ε ≤ C₁) (hx1 : 1 < x) (hx : x ^ (2 * (s * m)) ≤ a)
    (hba : b ^ (s * m) ≤ a ^ (s * m - m)) (hmain : A' * a ≤ C₁ * b + ε) :
    A' * x ^ (2 * m) ≤ 2 * C₁ := by
  set t := s * m with ht
  have hmt : m ≤ t := by rw [ht]; nlinarith
  have ha1 : 1 < a := lt_of_lt_of_le (one_lt_pow₀ hx1 (by omega)) hx
  have ha0 : 0 < a := by linarith
  set b' := max b 1 with hb'
  have hb'1 : 1 ≤ b' := le_max_right _ _
  have hb't : b' ^ t ≤ a ^ (t - m) := by
    rcases le_total b 1 with h | h
    · rw [hb', max_eq_right h, one_pow]; exact one_le_pow₀ ha1.le
    · rw [hb', max_eq_left h]; exact hba
  have h1 : A' * a ≤ 2 * C₁ * b' := by
    have : C₁ * b ≤ C₁ * b' := mul_le_mul_of_nonneg_left (le_max_left _ _) hC
    have : ε ≤ C₁ * b' := hε.trans (le_mul_of_one_le_right hC hb'1)
    linarith
  have h2 : (A' * a) ^ t ≤ (2 * C₁) ^ t * a ^ (t - m) := by
    calc (A' * a) ^ t ≤ (2 * C₁ * b') ^ t := pow_le_pow_left₀ (by positivity) h1 t
      _ = (2 * C₁) ^ t * b' ^ t := mul_pow _ _ _
      _ ≤ (2 * C₁) ^ t * a ^ (t - m) :=
          mul_le_mul_of_nonneg_left hb't (pow_nonneg (by linarith) _)
  -- Cancel `a^(t-m)`.
  have h3 : A' ^ t * a ^ m ≤ (2 * C₁) ^ t := by
    have e : (A' * a) ^ t = A' ^ t * a ^ m * a ^ (t - m) := by
      rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hmt]
    rw [e] at h2
    exact le_of_mul_le_mul_right h2 (pow_pos ha0 _)
  -- Take the `m`-th root.
  have h4 : A' ^ s * a ≤ (2 * C₁) ^ s := by
    have e1 : A' ^ t * a ^ m = (A' ^ s * a) ^ m := by rw [mul_pow, ← pow_mul, ht]
    have e2 : (2 * C₁) ^ t = ((2 * C₁) ^ s) ^ m := by rw [← pow_mul, ht]
    rw [e1, e2] at h3
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h3
  -- Take the `s`-th root.
  have h5 : (A' * x ^ (2 * m)) ^ s ≤ (2 * C₁) ^ s := by
    calc (A' * x ^ (2 * m)) ^ s = A' ^ s * x ^ (2 * t) := by
          rw [mul_pow, ← pow_mul, ht]; ring_nf
      _ ≤ A' ^ s * a := mul_le_mul_of_nonneg_left hx (pow_nonneg hA.le _)
      _ ≤ (2 * C₁) ^ s := h4
  have hx0 : 0 < x := by linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega)).1 h5

/-! ### One side -/

section Side

variable {ℓ : ℕ} {E : PseudoExpectation σ ℓ} {A : System σ ℝ} {η W : ℝ}

/-- **One side of the argument**: from (H1) for `(P, D)` and `0 ≤ Q ≤ T_Q ≤ W`,
`Ẽ[(PQ)^(2t) D^(2t)] ≤ c² W^(2m) Ẽ[(PQ)^(2(t-m))] + (c² + 2)/4`. -/
theorem side_bound (hη : 0 ≤ η) (hE : E.ApproxSatisfies A η 0) (hW : 2 ≤ W) {s m t : ℕ}
    (hsm : s * m = t) (hs : 1 ≤ s) (hm : 1 ≤ m) (hℓ : 22 * t ≤ ℓ)
    (hacc : sosErr A η (W ^ (50 * t)) ≤ 1 / 4) {P Q D : MvPolynomial σ ℝ}
    (hPd : P.totalDegree ≤ 1) (hQd : Q.totalDegree ≤ 1) (hDd : D.totalDegree ≤ 2)
    (hPn : coeffNorm1 P ≤ W ^ 1) (hQn : coeffNorm1 Q ≤ W ^ 1) {c : ℝ}
    (hH : SosPlusIdeal A (9 * t) (W ^ (48 * t))
      (C c * P ^ ((2 * s - 1) * m) * D ^ t - P ^ (2 * t) * D ^ (2 * t)))
    {TQ : ℝ} (hQ : SosPlusIdeal A 2 (W ^ 1) Q) (hQc : SosPlusIdeal A 2 (W ^ 3) (C TQ - Q))
    (hTQ0 : 0 ≤ TQ) (hTQ : TQ ≤ W) :
    E ((P * Q) ^ (2 * t) * D ^ (2 * t)) ≤
      c ^ 2 * W ^ (2 * m) * E ((P * Q) ^ (2 * (t - m))) + (c ^ 2 + 2) / 4 := by
  have hmt : m ≤ t := by rw [← hsm]; nlinarith
  have hexp : (2 * s - 1) * m = (t - m) + t := by
    have : (2 * s - 1) * m + m = 2 * (s * m) := by
      rw [← Nat.succ_mul, ← mul_assoc]; congr 1; omega
    omega
  rw [hexp] at hH
  obtain ⟨v, rfl⟩ : ∃ v, t = v + m := ⟨t - m, by omega⟩
  rw [Nat.add_sub_cancel] at hH ⊢
  have hPQd : (P * Q).totalDegree ≤ 2 := (totalDegree_mul _ _).trans (by omega)
  have hPQn : coeffNorm1 (P * Q) ≤ W ^ 2 := by have := cn_mul hPn hQn; simpa using this
  -- Step 1: (H1) times `Q^(2t)`.
  have hQ2 : IsSumSq (Q ^ (2 * (v + m))) := isSumSq_pow_two_mul Q _
  have hQ2d : (Q ^ (2 * (v + m))).totalDegree ≤ 2 * (v + m) :=
    (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * (v + m)) hQd; omega)
  have hQ2n : coeffNorm1 (Q ^ (2 * (v + m))) ≤ W ^ (2 * (v + m)) := by
    have := cn_pow hQn (2 * (v + m)); rwa [one_mul] at this
  have h1 := SosPlusIdeal.mulSOSW hW (k₁ := 2 * (v + m)) hQ2 hQ2d hQ2n hH
  have h1E := ge_of_sosPlusIdeal hη hE (by omega) h1
    (pow_le_pow_of_two_le hW (by omega)) hacc
  set f := P ^ v * Q ^ (v + m) with hf
  set g := P ^ (v + m) * Q ^ (v + m) * D ^ (v + m) with hg
  have e1 : Q ^ (2 * (v + m)) * (C c * P ^ (v + (v + m)) * D ^ (v + m) -
      P ^ (2 * (v + m)) * D ^ (2 * (v + m))) = C c * (f * g) - g * g := by
    rw [hf, hg]; ring
  rw [e1, E.map_sub, E.map_C_mul] at h1E
  have eU : (P * Q) ^ (2 * (v + m)) * D ^ (2 * (v + m)) = g * g := by rw [hg]; ring
  rw [eU]
  -- Step 2: Cauchy–Schwarz.
  have hfd : f.totalDegree ≤ 4 * (v + m) := by
    refine (totalDegree_mul _ _).trans ?_
    have := (totalDegree_pow P v).trans (Nat.mul_le_mul_left v hPd)
    have := (totalDegree_pow Q (v + m)).trans (Nat.mul_le_mul_left (v + m) hQd)
    omega
  have hgd : g.totalDegree ≤ 4 * (v + m) := by
    refine (totalDegree_mul _ _).trans ?_
    have := (totalDegree_mul (P ^ (v + m)) (Q ^ (v + m))).trans (add_le_add
      ((totalDegree_pow P (v + m)).trans (Nat.mul_le_mul_left (v + m) hPd))
      ((totalDegree_pow Q (v + m)).trans (Nat.mul_le_mul_left (v + m) hQd)))
    have := (totalDegree_pow D (v + m)).trans (Nat.mul_le_mul_left (v + m) hDd)
    omega
  have hcs := E.sq_apply_mul_le hfd hgd (by omega)
  have hU0 : 0 ≤ E (g * g) := E.map_mul_self_nonneg (by omega)
  have hV0 : 0 ≤ E (f ^ 2) := by rw [sq]; exact E.map_mul_self_nonneg (by omega)
  rw [← sq] at hU0 h1E ⊢
  have hU := cs_real (c := c) (ε := 1 / 4) hU0 hV0 (by linarith) hcs
  -- Step 3: `Ẽ[f²] ≤ W^(2m) Ẽ[(PQ)^(2v)] + 1/4`.
  have hCn : coeffNorm1 (C TQ : MvPolynomial σ ℝ) ≤ W ^ 1 :=
    cn_C (by rw [abs_of_nonneg hTQ0, pow_one]; exact hTQ)
  have hQm := SosPlusIdeal.pow_sub_powW hW hQ hQc hQn hCn (2 * m)
  simp only [show max 1 (max 3 1) + 4 = 7 by norm_num] at hQm
  have hTm : TQ ^ (2 * m) ≤ W ^ (2 * m) := pow_le_pow_left₀ hTQ0 hTQ _
  have hcst := SosPlusIdeal.of_isSumSqW A (k := 2 * m * 2) (a := 2 * m)
    (isSumSq_C (show 0 ≤ W ^ (2 * m) - TQ ^ (2 * m) by linarith)) (by rw [totalDegree_C]; omega)
    (cn_C (by rw [abs_of_nonneg (by linarith)]; have := pow_nonneg hTQ0 (2 * m); linarith))
  have hQW := SosPlusIdeal.addW hW (e := 2 * m * 7) hQm hcst le_rfl (by omega)
  have eQ : C TQ ^ (2 * m) - Q ^ (2 * m) + C (W ^ (2 * m) - TQ ^ (2 * m)) =
      C (W ^ (2 * m)) - Q ^ (2 * m) := by
    simp only [map_sub, map_pow]; ring
  rw [eQ] at hQW
  have hPQ2 : IsSumSq ((P * Q) ^ (2 * v)) := isSumSq_pow_two_mul _ _
  have hPQ2d : ((P * Q) ^ (2 * v)).totalDegree ≤ 4 * v :=
    (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * v) hPQd; omega)
  have hPQ2n : coeffNorm1 ((P * Q) ^ (2 * v)) ≤ W ^ (2 * (2 * v)) := cn_pow hPQn _
  have h3 := SosPlusIdeal.mulSOSW hW (k₁ := 4 * v) hPQ2 hPQ2d hPQ2n hQW
  have h3E := ge_of_sosPlusIdeal hη hE (by omega) h3
    (pow_le_pow_of_two_le hW (by omega)) hacc
  have e3 : (P * Q) ^ (2 * v) * (C (W ^ (2 * m)) - Q ^ (2 * m)) =
      C (W ^ (2 * m)) * (P * Q) ^ (2 * v) - f ^ 2 := by
    rw [hf]; ring
  rw [e3, E.map_sub, E.map_C_mul] at h3E
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith

/-- **The triangle bound**: `2^(2t-1) (D₁^(2t) + D₂^(2t)) ≥ (Δ²/2)^(2t)` from `D₁ + D₂ ≥ Δ²/2`,
for `t` a power of `2` (power mean, and powers of a lower bound). -/
theorem isSumSq_triangle_pow {D₁ D₂ : MvPolynomial σ ℝ} {Δ2 : ℝ} (hΔ : 0 ≤ Δ2)
    (htri : IsSumSq (D₁ + D₂ - C (Δ2 / 2))) {t : ℕ} (ht : ∃ a, t = 2 ^ a) :
    IsSumSq (C ((2 : ℝ) ^ (2 * t - 1)) * (D₁ ^ (2 * t) + D₂ ^ (2 * t)) -
      C ((Δ2 / 2) ^ (2 * t))) := by
  obtain ⟨a, rfl⟩ := ht
  have h2t : 2 * 2 ^ a = 2 ^ (a + 1) := by rw [pow_succ]; ring
  have h6 := isSumSq_pow_ge_const (by positivity : 0 ≤ Δ2 / 2) htri (2 * 2 ^ a)
  have h2 := isSumSq_add_pow_le D₁ D₂ (a + 1)
  rw [← h2t] at h2
  exact isSumSq_sub_trans h6 h2

/-- **The cross moment** of two clusters: from (H1) for `(P, D₁)` and `(Q, D₂)` with
`c = W^m (2^16 s)^t`, `0 ≤ P ≤ T_P ≤ W`, `0 ≤ Q ≤ T_Q ≤ W`, and `D₁ + D₂ ≥ Δ²/2 > 0`:
`Ẽ[P Q] ≤ 2 W² (2^18 s / Δ²)^s + 1`. -/
theorem cross_abstract (hη : 0 ≤ η) (hE : E.ApproxSatisfies A η 0) (hW : 2 ≤ W) {s m t : ℕ}
    (hsm : s * m = t) (hs : 1 ≤ s) (hm : 1 ≤ m) (ht : ∃ a, t = 2 ^ a) (hℓ : 22 * t ≤ ℓ)
    (hacc : sosErr A η (W ^ (50 * t)) ≤ 1 / 4) {P Q D₁ D₂ : MvPolynomial σ ℝ}
    (hPd : P.totalDegree ≤ 1) (hQd : Q.totalDegree ≤ 1) (hD₁d : D₁.totalDegree ≤ 2)
    (hD₂d : D₂.totalDegree ≤ 2) (hPn : coeffNorm1 P ≤ W ^ 1) (hQn : coeffNorm1 Q ≤ W ^ 1)
    {TP TQ : ℝ} (hP : SosPlusIdeal A 2 (W ^ 1) P) (hPc : SosPlusIdeal A 2 (W ^ 3) (C TP - P))
    (hTP0 : 0 ≤ TP) (hTP : TP ≤ W) (hQ : SosPlusIdeal A 2 (W ^ 1) Q)
    (hQc : SosPlusIdeal A 2 (W ^ 3) (C TQ - Q)) (hTQ0 : 0 ≤ TQ) (hTQ : TQ ≤ W)
    (hH₁ : SosPlusIdeal A (9 * t) (W ^ (48 * t))
      (C (W ^ m * (2 ^ 16 * s) ^ t) * P ^ ((2 * s - 1) * m) * D₁ ^ t -
        P ^ (2 * t) * D₁ ^ (2 * t)))
    (hH₂ : SosPlusIdeal A (9 * t) (W ^ (48 * t))
      (C (W ^ m * (2 ^ 16 * s) ^ t) * Q ^ ((2 * s - 1) * m) * D₂ ^ t -
        Q ^ (2 * t) * D₂ ^ (2 * t)))
    {Δ2 : ℝ} (hΔ : 0 < Δ2) (htri : IsSumSq (D₁ + D₂ - C (Δ2 / 2))) :
    E (P * Q) ≤ 2 * W ^ 2 * (2 ^ 18 * s / Δ2) ^ s + 1 := by
  have hmt : m ≤ t := by rw [← hsm]; nlinarith
  have ht1 : 1 ≤ t := le_trans hm hmt
  set c : ℝ := W ^ m * (2 ^ 16 * s) ^ t with hc
  have hW1 : (1 : ℝ) ≤ W := by linarith
  have hc1 : 1 ≤ c := by
    have h1 : (1 : ℝ) ≤ W ^ m := one_le_pow₀ hW1
    have h2 : (1 : ℝ) ≤ (2 ^ 16 * s) ^ t := one_le_pow₀ (by
      have : (1 : ℝ) ≤ s := by exact_mod_cast hs
      nlinarith)
    nlinarith
  set ρ : ℝ := 2 ^ 18 * s / Δ2 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set x := E (P * Q) with hx
  by_cases hx1 : x ≤ 1
  · have : 0 ≤ 2 * W ^ 2 * ρ ^ s := by positivity
    linarith
  rw [not_le] at hx1
  have hPQd : (P * Q).totalDegree ≤ 2 := (totalDegree_mul _ _).trans (by omega)
  set a := E ((P * Q) ^ (2 * t)) with ha
  set b := E ((P * Q) ^ (2 * (t - m))) with hb
  -- The two sides.
  have h₁ := side_bound hη hE hW hsm hs hm hℓ hacc hPd hQd hD₁d hPn hQn hH₁ hQ hQc hTQ0 hTQ
  have h₂ := side_bound hη hE hW hsm hs hm hℓ hacc hQd hPd hD₂d hQn hPn hH₂ hP hPc hTP0 hTP
  rw [mul_comm Q P] at h₂
  -- The triangle bound.
  have htp := isSumSq_triangle_pow hΔ.le htri ht
  have hsq := (isSumSq_pow_two_mul (P * Q) t).mul htp
  have hdeg : ((P * Q) ^ (2 * t) * (C ((2 : ℝ) ^ (2 * t - 1)) * (D₁ ^ (2 * t) + D₂ ^ (2 * t)) -
      C ((Δ2 / 2) ^ (2 * t)))).totalDegree ≤ ℓ := by
    refine (totalDegree_mul _ _).trans ?_
    have h1 := (totalDegree_pow (P * Q) (2 * t)).trans (Nat.mul_le_mul_left (2 * t) hPQd)
    have h2 : (C ((2 : ℝ) ^ (2 * t - 1)) * (D₁ ^ (2 * t) + D₂ ^ (2 * t)) -
        C ((Δ2 / 2) ^ (2 * t))).totalDegree ≤ 4 * t := by
      refine (totalDegree_sub_C_le _ _).trans ((totalDegree_mul _ _).trans ?_)
      rw [totalDegree_C, zero_add]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · exact (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * t) hD₁d; omega)
      · exact (totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left (2 * t) hD₂d; omega)
    omega
  have hnn := E.nonneg_of_isSumSq hsq hdeg
  have e : (P * Q) ^ (2 * t) * (C ((2 : ℝ) ^ (2 * t - 1)) * (D₁ ^ (2 * t) + D₂ ^ (2 * t)) -
      C ((Δ2 / 2) ^ (2 * t))) =
      C ((2 : ℝ) ^ (2 * t - 1)) * ((P * Q) ^ (2 * t) * D₁ ^ (2 * t)) +
        C ((2 : ℝ) ^ (2 * t - 1)) * ((P * Q) ^ (2 * t) * D₂ ^ (2 * t)) -
        C ((Δ2 / 2) ^ (2 * t)) * (P * Q) ^ (2 * t) := by ring
  rw [e, E.map_sub, E.map_add, E.map_C_mul, E.map_C_mul, E.map_C_mul] at hnn
  -- The main inequality `A' a ≤ C₁ b + ε`.
  set k : ℝ := 2 ^ (2 * t - 1) with hk
  have hk2 : k * 2 = 2 ^ (2 * t) := by
    rw [hk, ← pow_succ]; congr 1; omega
  have hk0 : 0 < k := by positivity
  set A' : ℝ := (Δ2 / 2) ^ (2 * t) with hA'
  set C₁ : ℝ := 2 ^ (2 * t) * c ^ 2 * W ^ (2 * m) with hC₁
  set ε : ℝ := k * ((c ^ 2 + 2) / 2) with hε
  have hmain : A' * a ≤ C₁ * b + ε := by
    have hsum := add_le_add h₁ h₂
    have : A' * a ≤ k * (E ((P * Q) ^ (2 * t) * D₁ ^ (2 * t)) +
        E ((P * Q) ^ (2 * t) * D₂ ^ (2 * t))) := by linarith
    calc A' * a ≤ k * (E ((P * Q) ^ (2 * t) * D₁ ^ (2 * t)) +
          E ((P * Q) ^ (2 * t) * D₂ ^ (2 * t))) := this
      _ ≤ k * (2 * (c ^ 2 * W ^ (2 * m) * b) + 2 * ((c ^ 2 + 2) / 4)) :=
          mul_le_mul_of_nonneg_left (by linarith) hk0.le
      _ = C₁ * b + ε := by rw [hC₁, hε, ← hk2]; ring
  have hW2m : (1 : ℝ) ≤ W ^ (2 * m) := one_le_pow₀ hW1
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hεC : ε ≤ C₁ := by
    rw [hε, hC₁, ← hk2]
    have : (c ^ 2 + 2) / 2 ≤ 2 * c ^ 2 * W ^ (2 * m) := by nlinarith
    nlinarith
  -- Hölder.
  have hxa : x ^ (2 * (s * m)) ≤ a := by
    rw [hsm, hx, ha]; exact E.pow_apply_le hPQd (by omega)
  have hba : b ^ (s * m) ≤ a ^ (s * m - m) := by
    rw [hsm, hb, ha]; exact E.pow_le_pow hPQd (by omega) (by omega)
  have hA0 : 0 < A' := by positivity
  have hfin := final_real hs hm hA0 hC₁0 hεC hx1 hxa hba hmain
  -- The bound `2 C₁ ≤ A' (2 W² ρ^s)^(2m)`.
  have hkey : 2 * C₁ ≤ A' * (2 * W ^ 2 * ρ ^ s) ^ (2 * m) := by
    have e1 : (2 * W ^ 2 * ρ ^ s) ^ (2 * m) = 2 ^ (2 * m) * W ^ (4 * m) * ρ ^ (2 * t) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← hsm]; ring
    have e2 : A' * ρ ^ (2 * t) = (2 ^ 17 * s) ^ (2 * t) := by
      rw [hA', ← mul_pow, hρ]
      congr 1
      field_simp
    have e3 : C₁ = W ^ (4 * m) * (2 ^ 17 * s) ^ (2 * t) := by
      rw [hC₁, hc, mul_pow, ← pow_mul, ← pow_mul]
      rw [show (2 : ℝ) ^ 17 * s = 2 * (2 ^ 16 * s) by ring, mul_pow (2 : ℝ), mul_comm t 2]
      ring
    have h2m : (2 : ℝ) ≤ 2 ^ (2 * m) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 * m) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [e1, show A' * (2 ^ (2 * m) * W ^ (4 * m) * ρ ^ (2 * t)) =
      2 ^ (2 * m) * W ^ (4 * m) * (A' * ρ ^ (2 * t)) by ring, e2, e3]
    have h0 : (0 : ℝ) ≤ W ^ (4 * m) * (2 ^ 17 * s) ^ (2 * t) := by positivity
    calc 2 * (W ^ (4 * m) * (2 ^ 17 * s) ^ (2 * t))
        ≤ 2 ^ (2 * m) * (W ^ (4 * m) * (2 ^ 17 * s) ^ (2 * t)) :=
          mul_le_mul_of_nonneg_right h2m h0
      _ = 2 ^ (2 * m) * W ^ (4 * m) * (2 ^ 17 * s) ^ (2 * t) := by ring
  have hpow : x ^ (2 * m) ≤ (2 * W ^ 2 * ρ ^ s) ^ (2 * m) :=
    le_of_mul_le_mul_left (hfin.trans hkey) hA0
  have hx0 : 0 ≤ x := by linarith
  have := (pow_le_pow_iff_left₀ hx0 (by positivity) (by omega)).1 hpow
  linarith

end Side

end BS23.SmallRadius.Core
