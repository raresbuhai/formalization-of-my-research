module

public import BS23.Separating.Alg
public import BS23.Separating.Setup
public import BS23.Common.Input

/-!
# Feasibility of the program

The program solved by the algorithm for [BS23, Theorem 1.1] (`BS23.Separating.progOf`) is valid:
some point `v` satisfies its three constraints `‖v‖² ≤ 256`, `F_{2s}(v) ≥ 1` and
`F_{2t}(v) ≤ 1024^t`, where `F_p = n⁻² ∑_{i,j} ⟨xᵢ - xⱼ, v⟩^p` for the whitened points `x`
(`BS23.Separating.progOf_valid_of_sample`; in the coordinates of the sample,
`BS23.Separating.exists_feasible_point`).

**The point.** Let `(a, b)` be a pair of components at maximal distance
`D² = sqNormIn Σ (μ_a - μ_b)`, and `λ* = (4 / D²) Σ⁻¹ (μ_a - μ_b)`
(`BS23.Separating.lamStar`). The point is `v* = (Wᵀ)⁻¹ λ*` for the whitening matrix `W`, so that
`⟨xᵢ - xⱼ, v*⟩ = ⟨μ_{ℓᵢ} - μ_{ℓⱼ}, λ*⟩ + ⟨ĝᵢ - ĝⱼ, Bᵀv*⟩`
(`BS23.Separating.whiten_sub_dotProduct`). By Cauchy–Schwarz in the geometry of `Σ` and the
maximality of `(a, b)`, `|⟨μᵢ - μⱼ, λ*⟩| ≤ 4`, with equality `⟨μ_a - μ_b, λ*⟩ = 4`
(`BS23.Separating.abs_dotProduct_lamStar_le`, `BS23.Separating.dotProduct_lamStar_self`), and the
noise form is `‖Bᵀv*‖² = λ*ᵀΣλ* = 16 / D²` (`BS23.Separating.quad_lamStar`).

**The estimates** (pointwise, on the empirical pair distribution). With `zⱼ = ⟨ĝⱼ, Bᵀv*⟩`, the
per-cluster moment closeness `|avg_{S_c} zⱼ^(2p) - (2p-1)‼ ν^p| ≤ δ ν^p` (`ν = 16 / D²`, `δ ≤ 1`)
gives `∑_{j ∈ S_c} zⱼ^(2p) ≤ |S_c| K_p` with `K_p = ((2p-1)‼ + δ) ν^p`
(`BS23.Separating.sum_cluster_pow_le`), and `4^p K_p ≤ 2 (128 p / D²)^p`
(`BS23.Separating.four_pow_mul_le`, using `(2p-1)‼ ≤ (2p)^p`).
* *Upper* (`BS23.Separating.pair_le_of_bounded`): from `(α + β)^(2p) ≤ 2^(2p-1) (α^(2p) + β^(2p))`
  twice, `F_{2p}(v*) ≤ 2^(2p-1) (4^(2p) + 4^p K_p) ≤ 64^p` when `16 p ≤ D²`; at `p = t` this is
  `≤ 1024^t`.
* *Lower* (`BS23.Separating.one_le_pair_of_far`): keeping only the pairs of `S_a × S_b`, where the
  mean term is `4`, and `4^(2s) ≤ 2^(2s-1) ((4 + β)^(2s) + β^(2s))`,
  `F_{2s}(v*) ≥ n⁻² |S_a| |S_b| 4^s ≥ (wmin 2^(s-1))² ≥ 1` when `128 s ≤ D²`,
  `|S_c| ≥ wmin n / 2` and `wmin ≥ 2^-(s-1)` (`BS23.Separating.one_le_wmin_mul_two_pow_logInv` for
  `s = logInv wmin + 1`).
* *Ball* (`BS23.Separating.pair_sq_le_of_pow_le`): by Jensen, `F_2(v*)^s ≤ F_{2s}(v*) ≤ 64^s`,
  so `‖v*‖² ≤ F_2(v*) ≤ 64` (`BS23.Separating.sum_sq_lt_pairSum_whiten`).

The moment closeness is the pointwise form of `BS23.Separating.abs_eval_empMom_sub_le_even`
(with `ĝ = g + ε`, `BS23.Separating.ghat_eq`; on the good event,
`BS23.Separating.ghat_momClose_of_goodNoise`), the cluster sizes the form of
`BS23.Separating.wmin_mul_le_card_cluster`, and `Ĉ ≻ 0` follows from CV1
(`BS23.Separating.empCov_yt_posDef`). The input of the algorithm is the rounded sample, indexed
by `Fin (length)` and `Fin (dim)`; the transport to `Fin n` and `Fin d` is
`BS23.Separating.exists_feasible_transport`.
-/

@[expose] public section

namespace BS23.Separating

open Matrix MvPolynomial Finset Colinear

variable {k d n : ℕ}

/-! ### Scalar estimates -/

/-- `(2p - 1)‼ ≤ (2p)^p`. -/
theorem gaussMom_two_mul_le_pow (p : ℕ) : gaussMom (2 * p) ≤ (2 * p) ^ p := by
  rw [gaussMom, ite_eq_left (even_two_mul p)]
  induction p with
  | zero => simp
  | succ p ih =>
    rw [show 2 * (p + 1) - 1 = 2 * p + 1 by omega, Nat.doubleFactorial_add_one]
    calc (2 * p + 1) * (2 * p - 1).doubleFactorial ≤ (2 * (p + 1)) * (2 * (p + 1)) ^ p :=
          Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) p))
      _ = (2 * (p + 1)) ^ (p + 1) := by ring

/-- `(2p - 1)‼ + δ ≤ 2 (2p)^p` for `δ ≤ 1`. -/
theorem gaussMom_add_le {δ : ℝ} (hδ : δ ≤ 1) (p : ℕ) :
    (gaussMom (2 * p) : ℝ) + δ ≤ 2 * (2 * p : ℝ) ^ p := by
  have h1 : (gaussMom (2 * p) : ℝ) ≤ (2 * p : ℝ) ^ p := by
    exact_mod_cast gaussMom_two_mul_le_pow p
  have h2 : (1 : ℝ) ≤ (2 * p : ℝ) ^ p := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · exact one_le_pow₀ (by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hp
        linarith)
  linarith

/-- `4^p ((2p-1)‼ + δ) (16 / D²)^p ≤ 2 (128 p / D²)^p` for `δ ≤ 1`. -/
theorem four_pow_mul_le {δ D2 : ℝ} (hδ : δ ≤ 1) (hD : 0 < D2) (p : ℕ) :
    4 ^ p * (((gaussMom (2 * p) : ℝ) + δ) * (16 / D2) ^ p) ≤ 2 * (128 * p / D2) ^ p := by
  have h := gaussMom_add_le hδ p
  calc 4 ^ p * (((gaussMom (2 * p) : ℝ) + δ) * (16 / D2) ^ p)
      = ((gaussMom (2 * p) : ℝ) + δ) * (64 / D2) ^ p := by
        rw [mul_left_comm, ← mul_pow]
        congr 2
        ring
    _ ≤ 2 * (2 * p : ℝ) ^ p * (64 / D2) ^ p :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = 2 * (128 * p / D2) ^ p := by
        rw [mul_assoc, ← mul_pow]
        congr 2
        ring

/-- `2 · 2^(2s-1) = 4^s` for `s ≥ 1`. -/
theorem two_mul_two_pow_two_mul_sub_one {s : ℕ} (hs : 1 ≤ s) :
    (2 : ℝ) * 2 ^ (2 * s - 1) = 4 ^ s := by
  have h : 2 * s = 2 * s - 1 + 1 := by omega
  calc (2 : ℝ) * 2 ^ (2 * s - 1) = 2 ^ (2 * s - 1 + 1) := by rw [pow_succ]; ring
    _ = 2 ^ (2 * s) := by rw [← h]
    _ = 4 ^ s := by rw [pow_mul]; norm_num

/-- `∑_{i ∈ A} ∑_{j ∈ B} (fᵢ + gⱼ) = |B| ∑_A f + |A| ∑_B g`. -/
theorem sum_sum_add_eq {ι : Type*} (A B : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ A, ∑ j ∈ B, (f i + g j) = B.card * ∑ i ∈ A, f i + A.card * ∑ j ∈ B, g j := by
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]

/-- Summing a bound over the clusters: if `∑_{j ∈ S_c} fⱼ ≤ |S_c| K` for every cluster `c`, then
`∑ⱼ fⱼ ≤ n K`. -/
theorem sum_le_card_mul_of_cluster {ℓ : Fin n → Fin k} {f : Fin n → ℝ} {K : ℝ}
    (h : ∀ c, ∑ j ∈ cluster ℓ c, f j ≤ (cluster ℓ c).card * K) : ∑ j, f j ≤ n * K := by
  calc ∑ j, f j = ∑ c, ∑ j ∈ cluster ℓ c, f j := (sum_fiberwise univ ℓ f).symm
    _ ≤ ∑ c, ∑ _j ∈ cluster ℓ c, K := by
        refine sum_le_sum fun c _ ↦ ?_
        rw [sum_const, nsmul_eq_mul]
        exact h c
    _ = ∑ _j : Fin n, K := sum_fiberwise univ ℓ fun _ ↦ K
    _ = n * K := by simp

/-- **Upper bound, summed.** If `|αᵢⱼ| ≤ ρ` and `∑ⱼ zⱼ^(2p) ≤ n K`, then
`∑_{i,j} (αᵢⱼ + zᵢ - zⱼ)^(2p) ≤ n² 2^(2p-1) (ρ^(2p) + 4^p K)`. -/
theorem sum_sum_add_pow_le {α : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {ρ K : ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hα : ∀ i j, |α i j| ≤ ρ) (hz : ∑ j, z j ^ (2 * p) ≤ n * K) :
    ∑ i, ∑ j, (α i j + (z i - z j)) ^ (2 * p) ≤
      (n : ℝ) ^ 2 * (2 ^ (2 * p - 1) * (ρ ^ (2 * p) + 4 ^ p * K)) := by
  have hev : Even (2 * p) := even_two_mul p
  set c : ℝ := 2 ^ (2 * p - 1) with hc_def
  have hc : 0 ≤ c := by positivity
  have h2c : 2 * c = 4 ^ p := two_mul_two_pow_two_mul_sub_one hp
  have hterm : ∀ i j, (α i j + (z i - z j)) ^ (2 * p) ≤
      c * ρ ^ (2 * p) + c * c * (z i ^ (2 * p) + z j ^ (2 * p)) := by
    intro i j
    have h1 := hev.add_pow_le (a := α i j) (b := z i - z j)
    have h2 : α i j ^ (2 * p) ≤ ρ ^ (2 * p) := by
      rw [← hev.pow_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hα i j) _
    have h3 := hev.add_pow_le (a := z i) (b := -z j)
    rw [hev.neg_pow, ← sub_eq_add_neg] at h3
    calc (α i j + (z i - z j)) ^ (2 * p) ≤ c * (α i j ^ (2 * p) + (z i - z j) ^ (2 * p)) := h1
      _ ≤ c * (ρ ^ (2 * p) + c * (z i ^ (2 * p) + z j ^ (2 * p))) :=
          mul_le_mul_of_nonneg_left (add_le_add h2 h3) hc
      _ = _ := by ring
  have hsum : ∑ i : Fin n, ∑ j : Fin n, (c * ρ ^ (2 * p) + c * c * (z i ^ (2 * p) + z j ^ (2 * p)))
      = (n : ℝ) ^ 2 * (c * ρ ^ (2 * p)) + c * c * (2 * n * ∑ j, z j ^ (2 * p)) := by
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
    ring
  calc ∑ i, ∑ j, (α i j + (z i - z j)) ^ (2 * p)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
          (c * ρ ^ (2 * p) + c * c * (z i ^ (2 * p) + z j ^ (2 * p))) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hterm i j
    _ = (n : ℝ) ^ 2 * (c * ρ ^ (2 * p)) + c * c * (2 * n * ∑ j, z j ^ (2 * p)) := hsum
    _ ≤ (n : ℝ) ^ 2 * (c * ρ ^ (2 * p)) + c * c * (2 * n * (n * K)) := by
        gcongr
    _ = (n : ℝ) ^ 2 * (c * (ρ ^ (2 * p) + (2 * c) * K)) := by ring
    _ = _ := by rw [h2c]

/-- **Upper bound.** If `|αᵢⱼ| ≤ 4`, `∑_{j ∈ S_c} zⱼ^(2p) ≤ |S_c| K` for every cluster and
`4^p K ≤ 16^p`, then `n⁻² ∑_{i,j} (αᵢⱼ + zᵢ - zⱼ)^(2p) ≤ 64^p`. -/
theorem pair_le_of_bounded {ℓ : Fin n → Fin k} {α : Fin n → Fin n → ℝ} {z : Fin n → ℝ} {K : ℝ}
    {p : ℕ} (hn : 0 < n) (hp : 1 ≤ p) (hα : ∀ i j, |α i j| ≤ 4)
    (hz : ∀ c, ∑ j ∈ cluster ℓ c, z j ^ (2 * p) ≤ (cluster ℓ c).card * K)
    (hK : 4 ^ p * K ≤ 16 ^ p) :
    ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (α i j + (z i - z j)) ^ (2 * p) ≤ 64 ^ p := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have h := sum_sum_add_pow_le hp hα (sum_le_card_mul_of_cluster hz)
  have h2c := two_mul_two_pow_two_mul_sub_one hp
  have h16 : (4 : ℝ) ^ (2 * p) = 16 ^ p := by rw [pow_mul]; norm_num
  have h64 : (64 : ℝ) ^ p = 4 ^ p * 16 ^ p := by rw [← mul_pow]; norm_num
  rw [inv_mul_le_iff₀ (by positivity)]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hc : (0 : ℝ) ≤ 2 ^ (2 * p - 1) := by positivity
  calc (2 : ℝ) ^ (2 * p - 1) * (4 ^ (2 * p) + 4 ^ p * K)
      ≤ 2 ^ (2 * p - 1) * (16 ^ p + 16 ^ p) := by
        rw [h16]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hK) hc
    _ = (2 * 2 ^ (2 * p - 1)) * 16 ^ p := by ring
    _ = 64 ^ p := by rw [h2c, h64]

/-- **Lower bound, summed over two clusters.** If `∑_{i ∈ A} zᵢ^(2s) ≤ |A| K`,
`∑_{j ∈ B} zⱼ^(2s) ≤ |B| K` and `4^s K ≤ 2`, then
`|A| |B| 4^s ≤ ∑_{i ∈ A} ∑_{j ∈ B} (4 + zᵢ - zⱼ)^(2s)`. -/
theorem le_sum_sum_four_add_pow {A B : Finset (Fin n)} {z : Fin n → ℝ} {K : ℝ} {s : ℕ}
    (hs : 1 ≤ s) (hzA : ∑ i ∈ A, z i ^ (2 * s) ≤ A.card * K)
    (hzB : ∑ j ∈ B, z j ^ (2 * s) ≤ B.card * K) (hK : 4 ^ s * K ≤ 2) :
    (A.card : ℝ) * B.card * 4 ^ s ≤ ∑ i ∈ A, ∑ j ∈ B, (4 + (z i - z j)) ^ (2 * s) := by
  have hev : Even (2 * s) := even_two_mul s
  set c : ℝ := 2 ^ (2 * s - 1) with hc_def
  have hc : 0 < c := by positivity
  have h2c : 2 * c = 4 ^ s := two_mul_two_pow_two_mul_sub_one hs
  have hc1 : 1 ≤ c := one_le_pow₀ (by norm_num)
  set T := ∑ i ∈ A, ∑ j ∈ B, (4 + (z i - z j)) ^ (2 * s) with hT_def
  have hT : 0 ≤ T := sum_nonneg fun i _ ↦ sum_nonneg fun j _ ↦ hev.pow_nonneg _
  have h16 : (4 : ℝ) ^ (2 * s) = (2 * c) ^ 2 := by rw [h2c, ← pow_mul, mul_comm]
  have hterm : ∀ i j, (2 * c) ^ 2 ≤
      c * (4 + (z i - z j)) ^ (2 * s) + c * c * (z i ^ (2 * s) + z j ^ (2 * s)) := by
    intro i j
    have h1 := hev.add_pow_le (a := 4 + (z i - z j)) (b := -(z i - z j))
    rw [add_neg_cancel_right, hev.neg_pow, h16] at h1
    have h3 := hev.add_pow_le (a := z i) (b := -z j)
    rw [hev.neg_pow, ← sub_eq_add_neg] at h3
    calc (2 * c) ^ 2 ≤ c * ((4 + (z i - z j)) ^ (2 * s) + (z i - z j) ^ (2 * s)) := h1
      _ ≤ c * ((4 + (z i - z j)) ^ (2 * s) + c * (z i ^ (2 * s) + z j ^ (2 * s))) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) hc.le
      _ = _ := by ring
  have hsum : (A.card : ℝ) * B.card * (2 * c) ^ 2 ≤
      c * T + c * c * (B.card * ∑ i ∈ A, z i ^ (2 * s) + A.card * ∑ j ∈ B, z j ^ (2 * s)) := by
    calc (A.card : ℝ) * B.card * (2 * c) ^ 2 = ∑ _i ∈ A, ∑ _j ∈ B, (2 * c) ^ 2 := by
          simp only [sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ i ∈ A, ∑ j ∈ B,
            (c * (4 + (z i - z j)) ^ (2 * s) + c * c * (z i ^ (2 * s) + z j ^ (2 * s))) :=
          sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hterm i j
      _ = c * T + c * c * ∑ i ∈ A, ∑ j ∈ B, (z i ^ (2 * s) + z j ^ (2 * s)) := by
          rw [hT_def, mul_sum, mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun i _ ↦ ?_
          rw [mul_sum, mul_sum, ← sum_add_distrib]
      _ = _ := by rw [sum_sum_add_eq]
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B.card := Nat.cast_nonneg _
  have hnoise : c * c * (B.card * ∑ i ∈ A, z i ^ (2 * s) + A.card * ∑ j ∈ B, z j ^ (2 * s)) ≤
      2 * c * (A.card * B.card) := by
    have h1 : B.card * ∑ i ∈ A, z i ^ (2 * s) + A.card * ∑ j ∈ B, z j ^ (2 * s) ≤
        2 * (A.card * B.card) * K := by
      nlinarith [mul_le_mul_of_nonneg_left hzA hB0, mul_le_mul_of_nonneg_left hzB hA0]
    have hK' : c * (2 * c * K) ≤ c * 2 := by
      rw [h2c]
      exact mul_le_mul_of_nonneg_left hK hc.le
    have hAB : (0 : ℝ) ≤ A.card * B.card := mul_nonneg hA0 hB0
    calc c * c * (B.card * ∑ i ∈ A, z i ^ (2 * s) + A.card * ∑ j ∈ B, z j ^ (2 * s))
        ≤ c * c * (2 * (A.card * B.card) * K) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (A.card * B.card) * (c * (2 * c * K)) := by ring
      _ ≤ (A.card * B.card) * (c * 2) := mul_le_mul_of_nonneg_left hK' hAB
      _ = 2 * c * (A.card * B.card) := by ring
  rw [← h2c]
  have hAB : (0 : ℝ) ≤ A.card * B.card := mul_nonneg hA0 hB0
  have key : c * ((A.card : ℝ) * B.card * (2 * c)) ≤ c * T := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (mul_nonneg hc.le hAB)]
  exact le_of_mul_le_mul_left key hc

/-- **Lower bound.** If `αᵢⱼ = 4` for `ℓᵢ = a`, `ℓⱼ = b`, every cluster has at least `wmin n / 2`
points, `∑_{j ∈ S_c} zⱼ^(2s) ≤ |S_c| K`, `4^s K ≤ 2` and `wmin 2^(s-1) ≥ 1`, then
`1 ≤ n⁻² ∑_{i,j} (αᵢⱼ + zᵢ - zⱼ)^(2s)`. -/
theorem one_le_pair_of_far {ℓ : Fin n → Fin k} {α : Fin n → Fin n → ℝ} {z : Fin n → ℝ}
    {a b : Fin k} {K wmin : ℝ} {s : ℕ} (hn : 0 < n) (hs : 1 ≤ s)
    (hws : 1 ≤ wmin * 2 ^ (s - 1)) (hsize : ∀ c, wmin * n / 2 ≤ ((cluster ℓ c).card : ℝ))
    (hα : ∀ i j, ℓ i = a → ℓ j = b → α i j = 4)
    (hz : ∀ c, ∑ j ∈ cluster ℓ c, z j ^ (2 * s) ≤ (cluster ℓ c).card * K)
    (hK : 4 ^ s * K ≤ 2) :
    1 ≤ ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (α i j + (z i - z j)) ^ (2 * s) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hev : Even (2 * s) := even_two_mul s
  have hw0 : 0 < wmin := by
    by_contra h
    replace h := not_lt.mp h
    have : wmin * 2 ^ (s - 1) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  set A := cluster ℓ a
  set B := cluster ℓ b
  have hsub : ∑ i ∈ A, ∑ j ∈ B, (4 + (z i - z j)) ^ (2 * s) ≤
      ∑ i, ∑ j, (α i j + (z i - z j)) ^ (2 * s) := by
    calc ∑ i ∈ A, ∑ j ∈ B, (4 + (z i - z j)) ^ (2 * s)
        = ∑ i ∈ A, ∑ j ∈ B, (α i j + (z i - z j)) ^ (2 * s) := by
          refine sum_congr rfl fun i hi ↦ sum_congr rfl fun j hj ↦ ?_
          rw [hα i j (mem_filter.1 hi).2 (mem_filter.1 hj).2]
      _ ≤ ∑ i ∈ A, ∑ j, (α i j + (z i - z j)) ^ (2 * s) :=
          sum_le_sum fun i _ ↦ sum_le_sum_of_subset_of_nonneg (subset_univ _)
            fun j _ _ ↦ hev.pow_nonneg _
      _ ≤ ∑ i, ∑ j, (α i j + (z i - z j)) ^ (2 * s) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _)
            fun i _ _ ↦ sum_nonneg fun j _ ↦ hev.pow_nonneg _
  have hlow := le_sum_sum_four_add_pow hs (hz a) (hz b) hK
  have hsizes : (wmin * n / 2) * (wmin * n / 2) ≤ (A.card : ℝ) * B.card :=
    mul_le_mul (hsize a) (hsize b) (by positivity) (Nat.cast_nonneg _)
  have h4 : (4 : ℝ) ^ s = 4 * (2 ^ (s - 1)) ^ 2 := by
    rw [← pow_mul, show (s - 1) * 2 = 2 * (s - 1) by ring, pow_mul,
      show ((2 : ℝ) ^ 2) = 4 by norm_num, ← pow_succ']
    congr 1
    omega
  have hone : 1 ≤ (wmin * 2 ^ (s - 1)) ^ 2 := one_le_pow₀ hws
  rw [le_inv_mul_iff₀ (by positivity), mul_one]
  calc (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 * (wmin * 2 ^ (s - 1)) ^ 2 := le_mul_of_one_le_right
        (by positivity) hone
    _ = (wmin * n / 2) * (wmin * n / 2) * 4 ^ s := by rw [h4]; ring
    _ ≤ (A.card : ℝ) * B.card * 4 ^ s := mul_le_mul_of_nonneg_right hsizes (by positivity)
    _ ≤ _ := hlow.trans hsub

/-- **Ball, by Jensen.** If `n⁻² ∑_{i,j} Aᵢⱼ^(2s) ≤ B^s` then `n⁻² ∑_{i,j} Aᵢⱼ² ≤ B`. -/
theorem pair_sq_le_of_pow_le {A : Fin n → Fin n → ℝ} {s : ℕ} (hn : 0 < n) (hs : 1 ≤ s) {B : ℝ}
    (hB : 0 ≤ B) (h : ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, A i j ^ (2 * s) ≤ B ^ s) :
    ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, A i j ^ 2 ≤ B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hw : ∑ _x : Fin n × Fin n, ((n : ℝ) ^ 2)⁻¹ = 1 := by
    rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hJ := Real.pow_arith_mean_le_arith_mean_pow (univ : Finset (Fin n × Fin n))
    (fun _ ↦ ((n : ℝ) ^ 2)⁻¹) (fun x ↦ A x.1 x.2 ^ 2) (fun _ _ ↦ by positivity) hw
    (fun _ _ ↦ sq_nonneg _) s
  simp only [← mul_sum, ← pow_mul] at hJ
  rw [Fintype.sum_prod_type' (fun i j ↦ A i j ^ 2),
    Fintype.sum_prod_type' (fun i j ↦ A i j ^ (2 * s))] at hJ
  have h0 : 0 ≤ ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, A i j ^ 2 := by positivity
  exact (pow_le_pow_iff_left₀ h0 hB (by omega)).1 (hJ.trans h)

/-! ### The direction `λ*` -/

/-- Cauchy–Schwarz: `⟨u, Σ⁻¹ w⟩² ≤ (uᵀΣ⁻¹u)(wᵀΣ⁻¹w)`. -/
theorem sq_dotProduct_inv_mulVec_le {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    (u w : Fin d → ℝ) : (u ⬝ᵥ (S⁻¹ *ᵥ w)) ^ 2 ≤ sqNormIn S u * sqNormIn S w := by
  have h := sq_dotProduct_le hS u (S⁻¹ *ᵥ w)
  have hSw : S *ᵥ (S⁻¹ *ᵥ w) = w := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det S).mp hS.isUnit), one_mulVec]
  rw [hSw, dotProduct_comm (S⁻¹ *ᵥ w) w] at h
  exact h

/-- The direction `λ* = (4 / D²) Σ⁻¹ (μ_a - μ_b)`, `D² = sqNormIn Σ (μ_a - μ_b)`. -/
noncomputable def lamStar (M : Mixture k d) (a b : Fin k) : Fin d → ℝ :=
  (4 / sqNormIn M.S (M.μ a - M.μ b)) • (M.S⁻¹ *ᵥ (M.μ a - M.μ b))

/-- `|⟨μᵢ - μⱼ, λ*⟩| ≤ 4` when `(a, b)` is a pair at maximal distance. -/
theorem abs_dotProduct_lamStar_le {M : Mixture k d} (hS : M.S.PosDef) {a b : Fin k}
    (hmax : ∀ i j, sqNormIn M.S (M.μ i - M.μ j) ≤ sqNormIn M.S (M.μ a - M.μ b))
    (hD : 0 < sqNormIn M.S (M.μ a - M.μ b)) (i j : Fin k) :
    |(M.μ i - M.μ j) ⬝ᵥ lamStar M a b| ≤ 4 := by
  set D2 := sqNormIn M.S (M.μ a - M.μ b)
  have h := sq_dotProduct_inv_mulVec_le hS (M.μ i - M.μ j) (M.μ a - M.μ b)
  have h2 : ((M.μ i - M.μ j) ⬝ᵥ (M.S⁻¹ *ᵥ (M.μ a - M.μ b))) ^ 2 ≤ D2 ^ 2 := by
    calc _ ≤ _ := h
      _ ≤ D2 * D2 := mul_le_mul_of_nonneg_right (hmax i j) hD.le
      _ = D2 ^ 2 := (sq D2).symm
  have h3 := abs_le_of_sq_le_sq h2 hD.le
  rw [lamStar, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos (by positivity)]
  calc 4 / D2 * |(M.μ i - M.μ j) ⬝ᵥ (M.S⁻¹ *ᵥ (M.μ a - M.μ b))| ≤ 4 / D2 * D2 :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 4 := div_mul_cancel₀ 4 hD.ne'

/-- `⟨μ_a - μ_b, λ*⟩ = 4`. -/
theorem dotProduct_lamStar_self (M : Mixture k d) {a b : Fin k}
    (hD : 0 < sqNormIn M.S (M.μ a - M.μ b)) : (M.μ a - M.μ b) ⬝ᵥ lamStar M a b = 4 := by
  rw [lamStar, dotProduct_smul, smul_eq_mul]
  change 4 / sqNormIn M.S (M.μ a - M.μ b) * sqNormIn M.S (M.μ a - M.μ b) = 4
  exact div_mul_cancel₀ 4 hD.ne'

/-- `λ*ᵀ Σ λ* = 16 / D²`. -/
theorem quad_lamStar {M : Mixture k d} (hS : M.S.PosDef) {a b : Fin k}
    (hD : 0 < sqNormIn M.S (M.μ a - M.μ b)) : quad M.S (lamStar M a b) = 16 /
      sqNormIn M.S (M.μ a - M.μ b) := by
  have hSw : M.S *ᵥ (M.S⁻¹ *ᵥ (M.μ a - M.μ b)) = M.μ a - M.μ b := by
    rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det M.S).mp hS.isUnit),
      one_mulVec]
  have hw : (M.S⁻¹ *ᵥ (M.μ a - M.μ b)) ⬝ᵥ (M.μ a - M.μ b) = sqNormIn M.S (M.μ a - M.μ b) := by
    rw [dotProduct_comm]
    rfl
  rw [quad, lamStar, mulVec_smul, hSw, smul_dotProduct, dotProduct_smul, hw, smul_eq_mul,
    smul_eq_mul]
  generalize sqNormIn M.S (M.μ a - M.μ b) = D at hD ⊢
  field_simp
  ring

/-! ### The point `v*` -/

/-- `Aᵀ (Aᵀ)⁻¹ u = u` for an invertible `A`. -/
theorem transpose_mulVec_inv_mulVec {A : Matrix (Fin d) (Fin d) ℝ} (hA : IsUnit A)
    (u : Fin d → ℝ) : Aᵀ *ᵥ ((Aᵀ)⁻¹ *ᵥ u) = u := by
  have h : IsUnit Aᵀ.det := by
    rw [det_transpose]
    exact (isUnit_iff_isUnit_det A).mp hA
  rw [mulVec_mulVec, mul_nonsing_inv _ h, one_mulVec]

/-- `⟨W u, v⟩ = ⟨u, Wᵀ v⟩`. -/
theorem mulVec_dotProduct_eq (A : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) :
    (A *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (Aᵀ *ᵥ v) := by
  rw [dotProduct_comm (A *ᵥ u) v, dotProduct_mulVec v A u, ← mulVec_transpose]
  exact dotProduct_comm _ _

/-- **The whitened pairs**: `⟨xᵢ - xⱼ, v⟩ = ⟨μ_{ℓᵢ} - μ_{ℓⱼ}, Wᵀv⟩ + ⟨ĝᵢ, Bᵀv⟩ - ⟨ĝⱼ, Bᵀv⟩`. -/
theorem whiten_sub_dotProduct (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (i j : Fin n) (v : Fin d → ℝ) :
    (whiten (yt r ω) i - whiten (yt r ω) j) ⬝ᵥ v =
      (M.μ (labels ω i) - M.μ (labels ω j)) ⬝ᵥ ((Wr r ω)ᵀ *ᵥ v) +
        (ghat M r ω i ⬝ᵥ ((Bm M r ω)ᵀ *ᵥ v) - ghat M r ω j ⬝ᵥ ((Bm M r ω)ᵀ *ᵥ v)) := by
  rw [whiten_yt M hS, whiten_yt M hS]
  have h : mc M r ω (labels ω i) + zeta M r ω i - (mc M r ω (labels ω j) + zeta M r ω j) =
      (mc M r ω (labels ω i) - mc M r ω (labels ω j)) + (zeta M r ω i - zeta M r ω j) := by
    abel
  rw [h, add_dotProduct, sub_dotProduct (zeta M r ω i), zeta_dotProduct, zeta_dotProduct,
    mc_sub, mulVec_dotProduct_eq]

/-- The value of `F_p` at `v`: `n⁻² ∑_{i,j} ⟨xᵢ - xⱼ, v⟩^p`. -/
theorem eval_pairLin (x : Fin n → Fin d → ℝ) (p : ℕ) (v : Fin d → ℝ) :
    eval v (pairLin x p) = ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, ((x i - x j) ⬝ᵥ v) ^ p := by
  simp only [pairLin, smul_eval, map_sum, map_pow, eval_lin]
  rfl

/-- **Moment closeness, summed**: from the pointwise moment closeness of cluster `c` at degree
`2p`, `∑_{j ∈ S_c} ⟨ĝⱼ, b⟩^(2p) ≤ |S_c| ((2p-1)‼ + δ) ‖b‖^(2p)`. -/
theorem sum_cluster_pow_le {M : Mixture k d} {r : Rounding k d}
    {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)} {δ : ℝ} {p : ℕ}
    (hmc : ∀ c b, |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * p)) -
      gaussMom (2 * p) * (∑ i, b i ^ 2) ^ p| ≤ δ * (∑ i, b i ^ 2) ^ p) (c : Fin k)
    (b : Fin d → ℝ) :
    ∑ j ∈ cluster (labels ω) c, (ghat M r ω j ⬝ᵥ b) ^ (2 * p) ≤
      ((cluster (labels ω) c).card : ℝ) * ((gaussMom (2 * p) + δ) * (∑ i, b i ^ 2) ^ p) := by
  have h := (abs_le.mp (hmc c b)).2
  rw [eval_empMom] at h
  set S := cluster (labels ω) c
  rcases Nat.eq_zero_or_pos S.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]
    simp
  · have hS : (0 : ℝ) < S.card := by exact_mod_cast hpos
    have h' : (S.card : ℝ)⁻¹ * ∑ j ∈ S, (ghat M r ω j ⬝ᵥ b) ^ (2 * p) ≤
        (gaussMom (2 * p) + δ) * (∑ i, b i ^ 2) ^ p := by
      change (S.card : ℝ)⁻¹ * ∑ j ∈ S, (∑ i, ghat M r ω j i * b i) ^ (2 * p) ≤ _
      linarith
    rwa [inv_mul_le_iff₀ hS] at h'

/-- **The moment hypothesis on the good event**: `BS23.GoodNoise` up to degree `D ≥ 2p`, with
`2η ≤ 1`, `2η ≤ wmin ≤ w_c`, `d ≤ n` and a rounding within `1/n`, gives the pointwise moment
closeness of `ĝ` at degree `2p` in every cluster with any
`δ ≥ (2η/wmin + 1/n) (4 (d + 1) (2p + 1))^(2p + 1)`
(from `BS23.Separating.abs_eval_empMom_sub_le_even`). -/
theorem ghat_momClose_of_goodNoise (M : Mixture k d) (hS : M.S.PosDef) {r : Rounding k d}
    (hr : IsRounding M.S (1 / n) r) {ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)}
    {wmin η δ : ℝ} {D p : ℕ} (hG : GoodNoise M.w η D (labels ω) (stdNoise M ω))
    (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) (hη1 : 2 * η ≤ 1) (hη : 2 * η ≤ wmin)
    (hd : d ≤ n) (hp : 2 * p ≤ D)
    (hδ : (2 * η / wmin + 1 / n) * (4 * (d + 1) * (2 * p + 1)) ^ (2 * p + 1) ≤ δ)
    (c : Fin k) (b : Fin d → ℝ) :
    |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * p)) -
      gaussMom (2 * p) * (∑ i, b i ^ 2) ^ p| ≤ δ * (∑ i, b i ^ 2) ^ p := by
  have hfun : ghat M r ω = stdNoise M ω + roundErr M r ω := funext (ghat_eq M r ω)
  have hwc : 0 < M.w c := hwmin.trans_le (hw c)
  have hη0 := eta_nonneg_of_goodNoise hG c
  have h := abs_eval_empMom_sub_le_even hG c hwc hη1 (hη.trans (hw c)) hd
    (sum_sq_roundErr_le M hS hr ω) hp b
  rw [hfun]
  refine h.trans (mul_le_mul_of_nonneg_right (le_trans ?_ hδ) (by positivity))
  have h1 : 2 * η / M.w c ≤ 2 * η / wmin :=
    div_le_div_of_nonneg_left (by linarith) hwmin (hw c)
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-! ### Feasibility -/

/-- **A feasible point**, in the coordinates of the sample. Let `Σ = M.S ≻ 0`, the empirical
covariance of the rounded points be positive definite, every cluster have at least `wmin n / 2`
points, the empirical moments of `⟨ĝⱼ, b⟩` of degrees `2s` and `2t` in every cluster be within
`δ ‖b‖^(2p)` of the Gaussian ones (`δ ≤ 1`), `wmin 2^(s-1) ≥ 1`, and some pair of components be at
distance `D₀² ≥ max(128 s, 16 t)`. Then some `v` has `‖v‖² ≤ 256`, `F_{2s}(v) ≥ 1` and
`F_{2t}(v) ≤ 1024^t` for the whitened points. -/
theorem exists_feasible_point (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (hn : 0 < n)
    (hC : (empCov (yt r ω)).PosDef) {wmin δ : ℝ} (hδ : δ ≤ 1) {s t : ℕ} (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hws : 1 ≤ wmin * 2 ^ (s - 1))
    (hsize : ∀ c, wmin * n / 2 ≤ ((cluster (labels ω) c).card : ℝ))
    (hmcs : ∀ c b, |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * s)) -
      gaussMom (2 * s) * (∑ i, b i ^ 2) ^ s| ≤ δ * (∑ i, b i ^ 2) ^ s)
    (hmct : ∀ c b, |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * t)) -
      gaussMom (2 * t) * (∑ i, b i ^ 2) ^ t| ≤ δ * (∑ i, b i ^ 2) ^ t)
    {a₀ b₀ : Fin k} (hsep_s : 128 * (s : ℝ) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀))
    (hsep_t : 16 * (t : ℝ) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀)) :
    ∃ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 ∧ 1 ≤ eval v (pairLin (whiten (yt r ω)) (2 * s)) ∧
      eval v (pairLin (whiten (yt r ω)) (2 * t)) ≤ 1024 ^ t := by
  -- the pair at maximal distance
  have : Nonempty (Fin k × Fin k) := ⟨(a₀, b₀)⟩
  obtain ⟨⟨a, b⟩, hmax⟩ :=
    Finite.exists_max fun q : Fin k × Fin k ↦ sqNormIn M.S (M.μ q.1 - M.μ q.2)
  have hmax' : ∀ i j, sqNormIn M.S (M.μ i - M.μ j) ≤ sqNormIn M.S (M.μ a - M.μ b) :=
    fun i j ↦ hmax (i, j)
  set D2 := sqNormIn M.S (M.μ a - M.μ b) with hD2_def
  have hD0 : sqNormIn M.S (M.μ a₀ - M.μ b₀) ≤ D2 := hmax' a₀ b₀
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hD : 0 < D2 := by linarith
  -- the point
  set lam := lamStar M a b
  set v := ((Wr r ω)ᵀ)⁻¹ *ᵥ lam
  have hWv : (Wr r ω)ᵀ *ᵥ v = lam := transpose_mulVec_inv_mulVec (isUnit_W hC) lam
  set bv := (Bm M r ω)ᵀ *ᵥ v
  have hν : ∑ i, bv i ^ 2 = 16 / D2 := by
    rw [← Nform_eq_sum_sq M hS.posSemidef, Nform, hWv]
    exact quad_lamStar hS hD
  set z : Fin n → ℝ := fun j ↦ ghat M r ω j ⬝ᵥ bv
  set α : Fin n → Fin n → ℝ := fun i j ↦ (M.μ (labels ω i) - M.μ (labels ω j)) ⬝ᵥ lam
  have hF : ∀ p, eval v (pairLin (whiten (yt r ω)) p) =
      ((n : ℝ) ^ 2)⁻¹ * ∑ i, ∑ j, (α i j + (z i - z j)) ^ p := by
    intro p
    rw [eval_pairLin]
    simp only [whiten_sub_dotProduct M hS, hWv]
    rfl
  have hα : ∀ i j, |α i j| ≤ 4 := fun i j ↦ abs_dotProduct_lamStar_le hS hmax' hD _ _
  -- the upper bound at any degree `2p` with `16 p ≤ D²`
  have hup : ∀ p : ℕ, 1 ≤ p → 16 * (p : ℝ) ≤ D2 →
      (∀ c b, |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * p)) -
        gaussMom (2 * p) * (∑ i, b i ^ 2) ^ p| ≤ δ * (∑ i, b i ^ 2) ^ p) →
      eval v (pairLin (whiten (yt r ω)) (2 * p)) ≤ 64 ^ p := by
    intro p hp hDp hmc
    have hz : ∀ c, ∑ j ∈ cluster (labels ω) c, z j ^ (2 * p) ≤
        (cluster (labels ω) c).card * ((gaussMom (2 * p) + δ) * (16 / D2) ^ p) := by
      intro c
      have h := sum_cluster_pow_le hmc c bv
      rwa [hν] at h
    have hK : 4 ^ p * ((gaussMom (2 * p) + δ) * (16 / D2) ^ p) ≤ 16 ^ p := by
      refine (four_pow_mul_le hδ hD p).trans ?_
      have h8 : 128 * (p : ℝ) / D2 ≤ 8 := by
        rw [div_le_iff₀ hD]
        linarith
      have h1 : (128 * (p : ℝ) / D2) ^ p ≤ 8 ^ p := pow_le_pow_left₀ (by positivity) h8 p
      have h2 : (2 : ℝ) ≤ 2 ^ p := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
      have h16 : (16 : ℝ) ^ p = 2 ^ p * 8 ^ p := by rw [← mul_pow]; norm_num
      rw [h16]
      have h8p : (0 : ℝ) ≤ 8 ^ p := by positivity
      nlinarith
    rw [hF]
    exact pair_le_of_bounded hn hp hα hz hK
  refine ⟨v, ?_, ?_, ?_⟩
  · -- the ball
    have hFs := hup s hs (by linarith) hmcs
    rw [hF] at hFs
    have hF2 := pair_sq_le_of_pow_le hn hs (by norm_num) hFs
    by_cases hv : v = 0
    · rw [hv]
      simp
    · have hlt := sum_sq_lt_pairSum_whiten hC hv
      have h2 := hF 2
      rw [eval_pairLin, div_eq_inv_mul] at *
      linarith
  · -- the lower bound
    rw [hF]
    have hz : ∀ c, ∑ j ∈ cluster (labels ω) c, z j ^ (2 * s) ≤
        (cluster (labels ω) c).card * ((gaussMom (2 * s) + δ) * (16 / D2) ^ s) := by
      intro c
      have h := sum_cluster_pow_le hmcs c bv
      rwa [hν] at h
    have hK : 4 ^ s * ((gaussMom (2 * s) + δ) * (16 / D2) ^ s) ≤ 2 := by
      refine (four_pow_mul_le hδ hD s).trans ?_
      have h1 : 128 * (s : ℝ) / D2 ≤ 1 := by
        rw [div_le_iff₀ hD]
        linarith
      have h2 : (128 * (s : ℝ) / D2) ^ s ≤ 1 := pow_le_one₀ (by positivity) h1
      linarith
    have hαab : ∀ i j, labels ω i = a → labels ω j = b → α i j = 4 := by
      intro i j hi hj
      simp only [α, hi, hj]
      exact dotProduct_lamStar_self M hD
    exact one_le_pair_of_far hn hs hws hsize hαab hz hK
  · -- the upper bound
    calc eval v (pairLin (whiten (yt r ω)) (2 * t)) ≤ 64 ^ t := hup t ht (by linarith) hmct
      _ ≤ 1024 ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t

/-- **Transport** of a feasible point from the coordinates `Fin n`, `Fin d` of the sample to the
coordinates `Fin (length)`, `Fin (dim)` of the input list. -/
theorem exists_feasible_transport {s t : ℕ} (L : Points) (hn : L.length = n) (hd : dim L = d)
    {Y : Fin n → Fin d → ℝ}
    (hY : ∀ j a, Y j a = (pointsFun L (Fin.cast hn.symm j) (Fin.cast hd.symm a) : ℝ))
    (h : ∃ v : Fin d → ℝ, ∑ i, v i ^ 2 ≤ 256 ∧ 1 ≤ eval v (pairLin (whiten Y) (2 * s)) ∧
      eval v (pairLin (whiten Y) (2 * t)) ≤ 1024 ^ t) :
    ∃ v : Fin (dim L) → ℝ, ∑ i, v i ^ 2 ≤ 256 ∧
      1 ≤ eval v (pairLin (whiten fun j a ↦ (pointsFun L j a : ℝ)) (2 * s)) ∧
      eval v (pairLin (whiten fun j a ↦ (pointsFun L j a : ℝ)) (2 * t)) ≤ 1024 ^ t := by
  subst hn hd
  have hY' : Y = fun j a ↦ (pointsFun L j a : ℝ) := by
    funext j a
    exact hY j a
  rw [← hY']
  exact h

/-- `wmin 2^L ≥ 1` for `L = logInv wmin`. -/
theorem one_le_wmin_mul_two_pow_logInv {wmin : ℚ} (hw : 0 < wmin) :
    1 ≤ (wmin : ℝ) * 2 ^ logInv wmin := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have h1 : wmin⁻¹ ≤ (⌈wmin⁻¹⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : (⌈wmin⁻¹⌉₊ : ℚ) ≤ 2 ^ logInv wmin := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) ⌈wmin⁻¹⌉₊
    exact_mod_cast this
  have h3 : (wmin : ℝ)⁻¹ ≤ 2 ^ logInv wmin := by exact_mod_cast h1.trans h2
  calc (1 : ℝ) = wmin * (wmin : ℝ)⁻¹ := (mul_inv_cancel₀ hw'.ne').symm
    _ ≤ wmin * 2 ^ logInv wmin := mul_le_mul_of_nonneg_left h3 hw'.le

/-- **The program is valid** (feasibility, [BS23, §4]). For an input `x = ⟨q, wmin, ỹ⟩` (any
failure probability `q`) of a rounded sample `ỹ` of `n > 0` points of a mixture with
`Σ = M.S ≻ 0`, with `s = sDeg x`, `t = tDeg ratio x`: if the empirical covariance of the rounded
points is positive definite, every cluster has at least `wmin n / 2` points, the empirical moments
of `⟨ĝⱼ, b⟩` of degrees `2s` and `2t` in every cluster are within `δ ‖b‖^(2p)` of the Gaussian
ones with `δ ≤ 1`, and some pair of components is at distance
`sqNormIn Σ (μ_a - μ_b) ≥ max(128 s, 16 t)`, then the program `progOf ratio x Lb` is valid for
every budget `Lb ≥ (dim + 1)^(2t)`. -/
theorem progOf_valid_of_sample (M : Mixture k d) (hS : M.S.PosDef) (r : Rounding k d)
    (ω : Fin n → Fin k × EuclideanSpace ℝ (Fin d)) (hn : 0 < n)
    (hC : (empCov (yt r ω)).PosDef) {q wmin : ℚ} (hwmin : 0 < wmin) {x : BipartitionInput}
    (hx : x = ⟨q, wmin, roundedSample r ω⟩) {ratio : ℕ} (hratio : 1 ≤ ratio) {δ : ℝ} (hδ : δ ≤ 1)
    (hsize : ∀ c, (wmin : ℝ) * n / 2 ≤ ((cluster (labels ω) c).card : ℝ))
    (hmcs : ∀ c b, |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * sDeg x)) -
      gaussMom (2 * sDeg x) * (∑ i, b i ^ 2) ^ sDeg x| ≤ δ * (∑ i, b i ^ 2) ^ sDeg x)
    (hmct : ∀ c b, |eval b (empMom (cluster (labels ω) c) (ghat M r ω) (2 * tDeg ratio x)) -
      gaussMom (2 * tDeg ratio x) * (∑ i, b i ^ 2) ^ tDeg ratio x| ≤
        δ * (∑ i, b i ^ 2) ^ tDeg ratio x)
    {a₀ b₀ : Fin k} (hsep_s : 128 * (sDeg x : ℝ) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀))
    (hsep_t : 16 * (tDeg ratio x : ℝ) ≤ sqNormIn M.S (M.μ a₀ - M.μ b₀))
    {Lb : ℕ} (hLb : (dim x.points + 1) ^ (2 * tDeg ratio x) ≤ Lb) :
    (progOf ratio x Lb).Valid := by
  subst hx
  have hws : 1 ≤ (wmin : ℝ) * 2 ^ (sDeg ⟨q, wmin, roundedSample r ω⟩ - 1) := by
    rw [sDeg, Nat.add_sub_cancel]
    exact one_le_wmin_mul_two_pow_logInv hwmin
  have hfeas := exists_feasible_point M hS r ω hn hC hδ (one_le_sDeg _) (one_le_tDeg hratio _)
    hws hsize hmcs hmct hsep_s hsep_t
  have hY : ∀ j a, yt r ω j a = (pointsFun (roundedSample r ω)
      (Fin.cast (length_roundedSample r ω).symm j)
      (Fin.cast (dim_roundedSample r ω hn).symm a) : ℝ) := by
    intro j a
    rw [pointsFun_roundedSample]
    rfl
  obtain ⟨v, h1, h2, h3⟩ := exists_feasible_transport (roundedSample r ω)
    (length_roundedSample r ω) (dim_roundedSample r ω hn) hY hfeas
  refine progOf_valid hratio hLb h1 ?_ ?_
  · rw [xR_eq_whiten]
    exact h2
  · rw [xR_eq_whiten]
    exact h3

end BS23.Separating
