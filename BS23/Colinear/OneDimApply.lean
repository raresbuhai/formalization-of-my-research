module

public import BS23.Colinear.Cast
public import BS23.Colinear.Moments
public import BS23.Colinear.OneDimCorrect
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The line clustering on the projections of the rounded sample

The last step of the analysis of the colinear algorithm [BS23, Theorem 1.2]: once the direction
`a` separates the means, the clustering on the line (`BS23.OneDim.cluster`) of the projections
`z_j = ⟨a, ỹ_j⟩` of the rounded points, run with the parameters of `BS23.Colinear.params`, errs
on at most a `(wmin / k)^c` fraction of the points (`BS23.Colinear.oneDim_clustersWithin`, and
`BS23.Colinear.oneDim_clustersWithin_params` with the parameters as the algorithm casts them).

Write `s = √(aᵀ Σ a)` and `L = logInv wmin`. The hypotheses:

* the centers `⟨a, μ_c⟩` are pairwise at least `Γ s` apart, with
  `Γ² ≥ 10⁸ · 4^c · log (1 / wmin)`;
* the noise is Gaussian-like up to degree `D ≥ 2 L + 8` (`BS23.UniformNoise` with error
  `η' ≤ wmin / 2`), the rounding moves each point by at most `1/n` in the geometry of `Σ`, and
  every cluster holds at least `wmin n / 2` points;
* the scale `V` the algorithm uses (`aᵀ Ĉ a`) is comparable to `s²`: `s² ≤ 2 V ≤ 2 s² n²`.

The proof feeds `BS23.OneDim.cluster_clustersWithin_of_tails`:

* **Tails** (`BS23.Colinear.OneDimApply.tail_le`): Markov's inequality on the empirical moment of
  order `2q`, `q = L + 4`, of the noise of a cluster along `a` bounds the fraction of the points of
  the cluster at distance at least `ρ s` from its center by `τ ρ = 2 (2q / (ρ - 1/n)²)^q` (the
  rounding moves the projection by at most `s / n`).
* **Numerics**: `2^L ≥ 1/wmin` and `L + 4 ≤ 11 log (1/wmin)`, so `τ A ≤ wmin / 8` for the range
  factor `A = ⌊√(64 (L + 1))⌋ + 1`, and `τ ρ ≤ 2^{-19} wmin^{2c + 2}` for `ρ ≥ Γ / 10`.
* **Grid** (`BS23.Colinear.OneDimApply.exists_grid_scale`): the top scale `H = 2^e` has
  `2 A² V ≤ H² < 8 A² V`, so some scale `H / 2^ℓ`, `ℓ ≤ log₂ n + 8`, lies in `[A s, Γ s / 20]`.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix Finset
open scoped Nat

namespace OneDimApply

variable {k d n : ℕ}

/-! ### Gaussian moments -/

/-- `(2r+1)‼ ≤ (2r+2)^(r+1)`. -/
theorem doubleFactorial_odd_le (r : ℕ) : (2 * r + 1)‼ ≤ (2 * r + 2) ^ (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by ring
    rw [h, Nat.doubleFactorial_add_two]
    calc (2 * r + 1 + 2) * (2 * r + 1)‼ ≤ (2 * (r + 1) + 2) * (2 * (r + 1) + 2) ^ (r + 1) := by
          apply Nat.mul_le_mul (by omega)
          exact ih.trans (Nat.pow_le_pow_left (by omega) _)
      _ = (2 * (r + 1) + 2) ^ (r + 1 + 1) := by ring

/-- `E Z^(2q) = (2q-1)‼ ≤ (2q)^q`. -/
theorem gaussMom_two_mul_le (q : ℕ) : (gaussMom (2 * q) : ℝ) ≤ (2 * q : ℝ) ^ q := by
  rcases q with _ | r
  · simp [gaussMom]
  · have h : gaussMom (2 * (r + 1)) = (2 * r + 1)‼ := by
      have h2 : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
      simp only [gaussMom, even_two_mul, ↓reduceIte, h2]
    rw [h]
    calc ((2 * r + 1)‼ : ℝ) ≤ ((2 * r + 2) ^ (r + 1) : ℕ) := by
          exact_mod_cast doubleFactorial_odd_le r
      _ = (2 * ((r + 1 : ℕ) : ℝ)) ^ (r + 1) := by push_cast; ring

/-! ### Tails of the projections -/

/-- The tail bound `2 (2q / (ρ - 1/n)²)^q`. -/
noncomputable def tailFn (n q : ℕ) (ρ : ℝ) : ℝ := 2 * (2 * q / (ρ - 1 / n) ^ 2) ^ q

theorem tailFn_nonneg (n q : ℕ) (ρ : ℝ) : 0 ≤ tailFn n q ρ := by
  unfold tailFn
  positivity

/-- **Tails of the projections.** On the cluster `c`, the number of points `j` whose projection
`⟨a, ỹ_j⟩` is at distance at least `ρ s` from `⟨a, μ_c⟩` (with `s = √(aᵀ Σ a)` and `ρ > 1/n`) is
at most a `2 (2q / (ρ - 1/n)²)^q` fraction of the cluster, by Markov's inequality on the empirical
`2q`-th moment of the noise along `a`, if `η' n ≤ |S_c|`. -/
theorem tail_le {M : Mixture k d} (hS : M.S.PosDef) {ℓ : Fin n → Fin k}
    {ν yt : Fin n → Fin d → ℝ} (hn : 0 < n)
    (hround : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2)
    {η' : ℝ} {D q : ℕ} (hU : UniformNoise M.S η' D ℓ ν) (hqD : 2 * q ≤ D) (hq : 1 ≤ q)
    {a : Fin d → ℝ} (ha : 0 < quad M.S a) (c : Fin k)
    (hη' : η' * n ≤ (cluster ℓ c).card) {ρ : ℝ} (hρ : 1 / n < ρ) :
    (((cluster ℓ c).filter fun j ↦
        ρ * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ yt j - a ⬝ᵥ M.μ c|).card : ℝ) ≤
      tailFn n q ρ * (cluster ℓ c).card := by
  unfold tailFn
  have hqa : a ⬝ᵥ (M.S *ᵥ a) = quad M.S a := rfl
  set s := Real.sqrt (quad M.S a) with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 ha
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ' : 0 < ρ - 1 / n := by linarith
  set F := (cluster ℓ c).filter fun j ↦ ρ * s ≤ |a ⬝ᵥ yt j - a ⬝ᵥ M.μ c| with hF
  -- a far point has a large noise projection
  have hfar : ∀ j ∈ F, ((ρ - 1 / n) * s) ^ (2 * q) ≤ (ν j ⬝ᵥ a) ^ (2 * q) := by
    intro j hj
    obtain ⟨hjc, hjfar⟩ := Finset.mem_filter.1 hj
    have hℓ : ℓ j = c := (Finset.mem_filter.1 hjc).2
    have he := abs_dotProduct_le_of_sqNormIn hS (v := a) hn (hround j)
    rw [hℓ, hqa, ← hs_def] at he
    have hsplit : a ⬝ᵥ yt j - a ⬝ᵥ M.μ c = ν j ⬝ᵥ a + (yt j - (M.μ c + ν j)) ⬝ᵥ a := by
      rw [dotProduct_comm (ν j) a, dotProduct_comm _ a, dotProduct_sub, dotProduct_add]
      ring
    rw [hsplit] at hjfar
    have h1 : (ρ - 1 / n) * s ≤ |ν j ⬝ᵥ a| := by
      have h2 := abs_add_le (ν j ⬝ᵥ a) ((yt j - (M.μ c + ν j)) ⬝ᵥ a)
      have h3 : (ρ - 1 / n) * s = ρ * s - s / n := by ring
      rw [h3]
      linarith
    calc ((ρ - 1 / n) * s) ^ (2 * q) ≤ |ν j ⬝ᵥ a| ^ (2 * q) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = (ν j ⬝ᵥ a) ^ (2 * q) := (even_two_mul q).pow_abs _
  have hsum : (F.card : ℝ) * ((ρ - 1 / n) * s) ^ (2 * q) ≤
      ∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ a) ^ (2 * q) := by
    calc (F.card : ℝ) * ((ρ - 1 / n) * s) ^ (2 * q) = ∑ j ∈ F, ((ρ - 1 / n) * s) ^ (2 * q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ F, (ν j ⬝ᵥ a) ^ (2 * q) := Finset.sum_le_sum hfar
      _ ≤ ∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ a) ^ (2 * q) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun j _ _ ↦ (even_two_mul q).pow_nonneg _
  -- the empirical moment of the noise
  have hmom := (abs_le.1 (hU c (2 * q) hqD a)).2
  rw [hqa, ← hs_def] at hmom
  have hT : 0 < s ^ (2 * q) := by positivity
  have hg : (gaussMom (2 * q) : ℝ) ≤ (2 * q : ℝ) ^ q := gaussMom_two_mul_le q
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hg1 : 1 ≤ (2 * q : ℝ) ^ q := one_le_pow₀ (by linarith)
  have hN : (0 : ℝ) ≤ (cluster ℓ c).card := Nat.cast_nonneg _
  have hmom' : ∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ a) ^ (2 * q) ≤
      (((cluster ℓ c).card : ℝ) * (gaussMom (2 * q) : ℝ) + η' * n) * s ^ (2 * q) := by
    have h : (∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ a) ^ (2 * q)) / n ≤
        ((cluster ℓ c).card : ℝ) / n * (gaussMom (2 * q) : ℝ) * s ^ (2 * q) +
          η' * s ^ (2 * q) := by linarith
    rw [div_le_iff₀ hn'] at h
    calc _ ≤ _ := h
      _ = (((cluster ℓ c).card : ℝ) * (gaussMom (2 * q) : ℝ) + η' * n) * s ^ (2 * q) := by
          field_simp
  have hP : 0 < (ρ - 1 / n) ^ (2 * q) := by positivity
  have hkey : (F.card : ℝ) * (ρ - 1 / n) ^ (2 * q) ≤
      2 * (2 * q : ℝ) ^ q * (cluster ℓ c).card := by
    have hcoef : ((cluster ℓ c).card : ℝ) * (gaussMom (2 * q) : ℝ) + η' * n ≤
        2 * (2 * q : ℝ) ^ q * (cluster ℓ c).card := by
      nlinarith [mul_le_mul_of_nonneg_left hg hN, mul_le_mul_of_nonneg_left hg1 hN]
    have h1 : (F.card : ℝ) * (ρ - 1 / n) ^ (2 * q) * s ^ (2 * q) ≤
        (2 * (2 * q : ℝ) ^ q * (cluster ℓ c).card) * s ^ (2 * q) := by
      calc (F.card : ℝ) * (ρ - 1 / n) ^ (2 * q) * s ^ (2 * q) =
            (F.card : ℝ) * ((ρ - 1 / n) * s) ^ (2 * q) := by rw [mul_pow]; ring
        _ ≤ _ := hsum.trans hmom'
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hT.le
    exact le_of_mul_le_mul_right h1 hT
  rw [div_pow, ← pow_mul, show 2 * ((2 * (q : ℝ)) ^ q / (ρ - 1 / n) ^ (2 * q)) *
      ((cluster ℓ c).card : ℝ) = (2 * (2 * q : ℝ) ^ q * (cluster ℓ c).card) /
        (ρ - 1 / n) ^ (2 * q) by ring, le_div_iff₀ hP]
  exact hkey


/-- The tail bound is small once `(ρ - 1/n)² ≥ 2 q B`: `τ ρ · B^q ≤ 2`. -/
theorem tail_mul_pow_le {q : ℕ} {ρ B : ℝ} (hB : 0 < B) (h : 2 * q * B ≤ (ρ - 1 / n) ^ 2) :
    tailFn n q ρ * B ^ q ≤ 2 := by
  unfold tailFn
  rcases q.eq_zero_or_pos with rfl | hq
  · simp
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (ρ - 1 / n) ^ 2 := lt_of_lt_of_le (by positivity) h
  have hx : 2 * q / (ρ - 1 / n) ^ 2 * B ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one hpos]
    exact h
  have h1 : (2 * q / (ρ - 1 / n) ^ 2 * B) ^ q ≤ 1 :=
    pow_le_one₀ (mul_nonneg (div_nonneg (by positivity) hpos.le) hB.le) hx
  calc 2 * (2 * q / (ρ - 1 / n) ^ 2) ^ q * B ^ q = 2 * (2 * q / (ρ - 1 / n) ^ 2 * B) ^ q := by
        rw [mul_pow]; ring
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ = 2 := mul_one _

/-- `2^20 W² (W²)^c ≤ (32 · 4^c)^(L + 4)` for `W = 2^L`. -/
theorem pow_bound (L c : ℕ) :
    2 ^ 20 * ((2 : ℝ) ^ L) ^ 2 * (((2 : ℝ) ^ L) ^ 2) ^ c ≤ (32 * 4 ^ c : ℝ) ^ (L + 4) := by
  have h1 : ((2 : ℝ) ^ L) ^ 2 = 4 ^ L := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have h2 : ((4 : ℝ) ^ L) ^ c = ((4 : ℝ) ^ c) ^ L := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h1, h2, mul_pow, pow_add, pow_add]
  have h3 : (4 : ℝ) ^ L ≤ 32 ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L
  have h4 : (1 : ℝ) ≤ (4 ^ c) ^ 4 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  calc (2 : ℝ) ^ 20 * 4 ^ L * (4 ^ c) ^ L = 32 ^ 4 * 4 ^ L * (4 ^ c) ^ L * 1 := by norm_num
    _ ≤ 32 ^ 4 * 32 ^ L * (4 ^ c) ^ L * (4 ^ c) ^ 4 := by gcongr
    _ = _ := by ring

/-- The tail at the range factor `A = r + 1` with `r² ≥ 4 (L + 4)`: `τ A · 16 · 2^L ≤ 2`. -/
theorem tailFn_range_le {L r : ℕ} (hn : 0 < n) (hr : 4 * ((L : ℝ) + 4) ≤ (r : ℝ) ^ 2) :
    tailFn n (L + 4) ((r : ℝ) + 1) * (16 * 2 ^ L) ≤ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hn1
  have hAn : (r : ℝ) ≤ (r : ℝ) + 1 - 1 / n := by linarith
  have h := tail_mul_pow_le (n := n) (q := L + 4) (ρ := (r : ℝ) + 1) (B := 2) (by norm_num) (by
    have : (r : ℝ) ^ 2 ≤ ((r : ℝ) + 1 - 1 / n) ^ 2 := pow_le_pow_left₀ (by positivity) hAn 2
    push_cast
    linarith)
  have h2 : (2 : ℝ) ^ (L + 4) = 16 * 2 ^ L := by rw [pow_add]; norm_num; ring
  rwa [h2] at h

/-- The tails beyond `Γ / 10`, for `Γ ≥ 40` and `Γ² ≥ 9 · 10⁶ · 4^c (L + 4)`:
`τ ρ · 2^20 W² (W²)^c ≤ 2` for `W = 2^L`. -/
theorem tailFn_far_le {L c : ℕ} (hn : 0 < n) {Γ ρ : ℝ} (hΓ40 : 40 ≤ Γ)
    (hΓ : 9 * 10 ^ 6 * (4 ^ c * ((L : ℝ) + 4)) ≤ Γ ^ 2) (hρ : Γ / 10 ≤ ρ) :
    tailFn n (L + 4) ρ * (2 ^ 20 * ((2 : ℝ) ^ L) ^ 2 * (((2 : ℝ) ^ L) ^ 2) ^ c) ≤ 2 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hn1
  have h1 : Γ / 10 - 1 ≤ ρ - 1 / n := by linarith
  have h2 : (Γ / 10 - 1) ^ 2 ≤ (ρ - 1 / n) ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
  have h3 : Γ ^ 2 / 200 ≤ (Γ / 10 - 1) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Γ) (by linarith : (0 : ℝ) ≤ Γ - 40)]
  have h4 : (0 : ℝ) ≤ 4 ^ c * ((L : ℝ) + 4) := by positivity
  have hB := tail_mul_pow_le (n := n) (q := L + 4) (ρ := ρ) (B := 32 * 4 ^ c) (by positivity) (by
    have h5 : 2 * ((L + 4 : ℕ) : ℝ) * (32 * 4 ^ c) = 64 * (4 ^ c * ((L : ℝ) + 4)) := by
      push_cast; ring
    rw [h5]
    linarith)
  exact (mul_le_mul_of_nonneg_left (pow_bound L c) (tailFn_nonneg _ _ _)).trans hB

/-! ### The weight bound -/

/-- `k wmin ≤ 1`. -/
theorem k_mul_wmin_le {M : Mixture k d} (hM : M.Valid) {wmin : ℝ} (hw : ∀ i, wmin ≤ M.w i) :
    (k : ℝ) * wmin ≤ 1 := by
  have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) ↦ hw i
  rwa [hM.sum_w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h

/-- `wmin ≤ 1/2` when `k ≥ 2`. -/
theorem wmin_le_half {wmin : ℚ} (hk : 2 ≤ k) (hkw : (k : ℝ) * wmin ≤ 1) (hw : 0 < wmin) :
    wmin ≤ 1 / 2 := by
  have hkwQ : (k : ℚ) * wmin ≤ 1 := by exact_mod_cast hkw
  have hkQ : (2 : ℚ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- `2^L ≥ 1 / wmin` for `L = logInv wmin`. -/
theorem one_le_mul_two_pow_logInv {wmin : ℚ} (hw : 0 < wmin) :
    1 ≤ (wmin : ℝ) * 2 ^ logInv wmin := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have h1 : wmin⁻¹ ≤ (⌈wmin⁻¹⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : (⌈wmin⁻¹⌉₊ : ℚ) ≤ 2 ^ logInv wmin := by
    have := Nat.le_pow_clog (b := 2) (by norm_num) ⌈wmin⁻¹⌉₊
    exact_mod_cast this
  have h3 : (wmin : ℝ)⁻¹ ≤ 2 ^ logInv wmin := by exact_mod_cast h1.trans h2
  calc (1 : ℝ) = wmin * (wmin : ℝ)⁻¹ := (mul_inv_cancel₀ hw'.ne').symm
    _ ≤ wmin * 2 ^ logInv wmin := mul_le_mul_of_nonneg_left h3 hw'.le

/-- `2^(L + 4) ≤ (1 / wmin)^7` for `L = logInv wmin` and `wmin ≤ 1/2`. -/
theorem two_pow_logInv_add_four_le {wmin : ℚ} (hw : 0 < wmin) (hw2 : wmin ≤ 1 / 2) :
    (2 : ℝ) ^ (logInv wmin + 4) ≤ ((wmin : ℝ)⁻¹) ^ 7 := by
  have hx : (2 : ℚ) ≤ wmin⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hw]
    linarith
  have hN1 : 1 < ⌈wmin⁻¹⌉₊ := by
    have := Nat.le_ceil (wmin⁻¹)
    exact_mod_cast (by linarith : (1 : ℚ) < ⌈wmin⁻¹⌉₊)
  have hpos : 0 < logInv wmin := Nat.clog_pos (by norm_num) hN1
  have hlt : 2 ^ (logInv wmin - 1) < ⌈wmin⁻¹⌉₊ := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN1
    rwa [Nat.pred_eq_sub_one] at this
  have hceil : (⌈wmin⁻¹⌉₊ : ℚ) < wmin⁻¹ + 1 := Nat.ceil_lt_add_one (by linarith)
  have h1 : 2 ^ (logInv wmin + 4) < 32 * ⌈wmin⁻¹⌉₊ := by
    have : logInv wmin + 4 = (logInv wmin - 1) + 5 := by omega
    rw [this, pow_add]
    norm_num
    omega
  have h3 : ((2 ^ (logInv wmin + 4) : ℕ) : ℝ) < 32 * (⌈wmin⁻¹⌉₊ : ℝ) := by exact_mod_cast h1
  have h4 : (⌈wmin⁻¹⌉₊ : ℝ) < (wmin : ℝ)⁻¹ + 1 := by exact_mod_cast hceil
  have hx' : (2 : ℝ) ≤ (wmin : ℝ)⁻¹ := by exact_mod_cast hx
  have h6 : (2 : ℝ) ^ 6 ≤ ((wmin : ℝ)⁻¹) ^ 6 := pow_le_pow_left₀ (by norm_num) hx' 6
  have h7 : ((wmin : ℝ)⁻¹) ^ 7 = (wmin : ℝ)⁻¹ * ((wmin : ℝ)⁻¹) ^ 6 := by ring
  push_cast at h3
  rw [h7]
  nlinarith [mul_le_mul_of_nonneg_left h6 (by linarith : (0 : ℝ) ≤ (wmin : ℝ)⁻¹)]

/-- `L + 4 ≤ 11 log (1 / wmin)` for `L = logInv wmin` and `wmin ≤ 1/2`. -/
theorem logInv_add_four_le {wmin : ℚ} (hw : 0 < wmin) (hw2 : wmin ≤ 1 / 2) :
    (logInv wmin : ℝ) + 4 ≤ 11 * Real.log (1 / (wmin : ℝ)) := by
  have hw' : (0 : ℝ) < wmin := by exact_mod_cast hw
  have h := two_pow_logInv_add_four_le hw hw2
  have hlog := Real.log_le_log (by positivity) h
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  rw [one_div]
  have h2 := Real.log_two_gt_d9
  have hL : (0 : ℝ) ≤ (logInv wmin : ℝ) + 4 := by positivity
  have h3 : ((logInv wmin : ℝ) + 4) * 0.6931471803 ≤ ((logInv wmin : ℝ) + 4) * Real.log 2 :=
    mul_le_mul_of_nonneg_left h2.le hL
  nlinarith

/-! ### The range factor and the separation -/

theorem eight_le_sqrt (L : ℕ) : 8 ≤ Nat.sqrt (64 * (L + 1)) :=
  Nat.le_sqrt.2 (by omega)

theorem four_mul_le_sqrt_sq (L : ℕ) :
    4 * ((L : ℝ) + 4) ≤ (Nat.sqrt (64 * (L + 1)) : ℝ) ^ 2 := by
  have h8 : (8 : ℝ) ≤ Nat.sqrt (64 * (L + 1)) := by exact_mod_cast eight_le_sqrt L
  have hlt : 64 * ((L : ℝ) + 1) <
      ((Nat.sqrt (64 * (L + 1)) : ℝ) + 1) * ((Nat.sqrt (64 * (L + 1)) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_succ_sqrt (64 * (L + 1))
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right h8 (by positivity : (0 : ℝ) ≤ Nat.sqrt (64 * (L + 1)))]

theorem sqrt_add_one_sq_le (L : ℕ) :
    ((Nat.sqrt (64 * (L + 1)) : ℝ) + 1) ^ 2 ≤ 256 * ((L : ℝ) + 1) := by
  have h8 : (8 : ℝ) ≤ Nat.sqrt (64 * (L + 1)) := by exact_mod_cast eight_le_sqrt L
  have hle : (Nat.sqrt (64 * (L + 1)) : ℝ) * (Nat.sqrt (64 * (L + 1)) : ℝ) ≤
      64 * ((L : ℝ) + 1) := by
    exact_mod_cast Nat.sqrt_le (64 * (L + 1))
  nlinarith

/-- From `Γ² ≥ 10⁸ · 4^c · lg` and `L + 4 ≤ 11 lg`: `Γ² ≥ 9 · 10⁶ · 4^c (L + 4)` and
`Γ ≥ 40 A` for `A = r + 1 ≤ 16 √(L + 1)`. -/
theorem gamma_bounds {L c r : ℕ} {Γ lg : ℝ} (hΓ : 0 < Γ) (hlog : (L : ℝ) + 4 ≤ 11 * lg)
    (hΓc : 10 ^ 8 * 4 ^ c * lg ≤ Γ ^ 2) (hA2 : ((r : ℝ) + 1) ^ 2 ≤ 256 * ((L : ℝ) + 1)) :
    9 * 10 ^ 6 * (4 ^ c * ((L : ℝ) + 4)) ≤ Γ ^ 2 ∧ 40 * ((r : ℝ) + 1) ≤ Γ := by
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have h4c : (1 : ℝ) ≤ 4 ^ c := one_le_pow₀ (by norm_num)
  have hlg : 0 ≤ lg := by linarith
  have h1 : 4 ^ c * ((L : ℝ) + 4) ≤ 4 ^ c * (11 * lg) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : 0 ≤ 4 ^ c * lg := mul_nonneg (by positivity) hlg
  have hΓ' : 9 * 10 ^ 6 * (4 ^ c * ((L : ℝ) + 4)) ≤ Γ ^ 2 := by
    have e1 : 10 ^ 8 * 4 ^ c * lg = 10 ^ 8 * (4 ^ c * lg) := by ring
    have e2 : (4 : ℝ) ^ c * (11 * lg) = 11 * (4 ^ c * lg) := by ring
    rw [e1] at hΓc
    rw [e2] at h1
    linarith
  refine ⟨hΓ', ?_⟩
  have h3 : (L : ℝ) + 4 ≤ 4 ^ c * ((L : ℝ) + 4) := le_mul_of_one_le_left (by positivity) h4c
  have h5 : (40 * ((r : ℝ) + 1)) ^ 2 ≤ Γ ^ 2 := by nlinarith
  exact (sq_le_sq₀ (by positivity) hΓ.le).1 h5

/-! ### The conditions on the tails -/

theorem tail_sq_le {W t : ℝ} {c : ℕ} (hW1 : 1 ≤ W) (ht0 : 0 ≤ t)
    (ht : t * (2 ^ 20 * W ^ 2 * (W ^ 2) ^ c) ≤ 2) : t * W ^ 2 * 2 ^ 20 ≤ 2 := by
  have hWc : 1 ≤ (W ^ 2) ^ c := one_le_pow₀ (one_le_pow₀ hW1)
  calc t * W ^ 2 * 2 ^ 20 = t * (2 ^ 20 * W ^ 2 * 1) := by ring
    _ ≤ t * (2 ^ 20 * W ^ 2 * (W ^ 2) ^ c) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWc (by positivity)) ht0
    _ ≤ 2 := ht

/-- Coverage: `τ A + 3 k θ ≤ ε` for `θ = wmin² / 100` and `ε = wmin / 4`. -/
theorem tail_range {wmin W t : ℝ} (hw0 : 0 < wmin) (hW : 1 ≤ wmin * W) (hW0 : 0 < W)
    (hkw : (k : ℝ) * wmin ≤ 1) (ht : t * (16 * W) ≤ 2) :
    t + 3 * k * (wmin ^ 2 / 100) ≤ wmin / 4 := by
  have h1 : t * W ≤ wmin / 8 * W := by linarith
  have h2 : t ≤ wmin / 8 := le_of_mul_le_mul_right h1 hW0
  have h3 : 3 * (k : ℝ) * (wmin ^ 2 / 100) ≤ 3 * wmin / 100 := by
    nlinarith [mul_le_mul_of_nonneg_right hkw hw0.le]
  linarith

/-- Light cells: `τ (Γ/10) < θ = wmin² / 100`. -/
theorem tail_light {wmin W t : ℝ} {c : ℕ} (hW : 1 ≤ wmin * W) (hW1 : 1 ≤ W) (ht0 : 0 ≤ t)
    (ht : t * (2 ^ 20 * W ^ 2 * (W ^ 2) ^ c) ≤ 2) : t < wmin ^ 2 / 100 := by
  have h1 := tail_sq_le hW1 ht0 ht
  have hwW : 1 ≤ wmin ^ 2 * W ^ 2 := by
    have := one_le_pow₀ (n := 2) hW
    rwa [mul_pow] at this
  have h2 : 100 * t * W ^ 2 < wmin ^ 2 * W ^ 2 := by linarith
  have h3 : 100 * t < wmin ^ 2 := lt_of_mul_lt_mul_right h2 (by positivity)
  linarith

/-- Heavy cells near the centers: `ε + τ (3Γ/20) < wmin / 2` for `ε = wmin / 4`. -/
theorem tail_heavy {wmin W t : ℝ} {c : ℕ} (hW : 1 ≤ wmin * W) (hW1 : 1 ≤ W) (ht0 : 0 ≤ t)
    (ht : t * (2 ^ 20 * W ^ 2 * (W ^ 2) ^ c) ≤ 2) : wmin / 4 + t < wmin / 2 := by
  have h1 := tail_sq_le hW1 ht0 ht
  have h2 : t * W ≤ t * W ^ 2 := by
    have := mul_le_mul_of_nonneg_left hW1 (mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ W))
    linarith
  have h3 : 4 * t * W < wmin * W := by linarith
  have h4 : 4 * t < wmin := lt_of_mul_lt_mul_right h3 (by linarith)
  linarith

/-- The error: `τ (3Γ/10) ≤ (wmin / k)^c`. -/
theorem tail_error {wmin W t : ℝ} {c : ℕ} (hk : 0 < k) (hw0 : 0 < wmin)
    (hkw : (k : ℝ) * wmin ≤ 1) (hW : 1 ≤ wmin * W) (hW1 : 1 ≤ W) (ht0 : 0 ≤ t)
    (ht : t * (2 ^ 20 * W ^ 2 * (W ^ 2) ^ c) ≤ 2) : t ≤ (wmin / k) ^ c := by
  have h2 : t * (W ^ 2) ^ c ≤ 1 := by
    have h5 : 0 ≤ t * (W ^ 2) ^ c := by positivity
    have h6 : (1 : ℝ) ≤ W ^ 2 := one_le_pow₀ hW1
    have h7 := mul_le_mul_of_nonneg_left h6 h5
    linarith
  have h3 : 1 ≤ (wmin ^ 2 * W ^ 2) ^ c := by
    refine one_le_pow₀ ?_
    have := one_le_pow₀ (n := 2) hW
    rwa [mul_pow] at this
  have h4 : wmin ^ 2 ≤ wmin / k := by
    rw [le_div_iff₀ (by exact_mod_cast hk)]
    nlinarith [mul_le_mul_of_nonneg_right hkw hw0.le]
  calc t ≤ t * (wmin ^ 2 * W ^ 2) ^ c := le_mul_of_one_le_right ht0 h3
    _ = (t * (W ^ 2) ^ c) * (wmin ^ 2) ^ c := by rw [mul_pow]; ring
    _ ≤ 1 * (wmin ^ 2) ^ c := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ (wmin / k) ^ c := by rw [one_mul]; exact pow_le_pow_left₀ (by positivity) h4 c

/-! ### The grid of scales -/

/-- **A good grid scale.** If `s² ≤ 2 V ≤ 2 s² n²` and `Γ ≥ 40 A`, then some scale
`topScale A V / 2^ℓ` with `ℓ ≤ log₂ n + 8` lies in `[A s, Γ s / 20]`. -/
theorem exists_grid_scale {A V s Γ : ℝ} (hn : 0 < n) (hA : 0 < A) (hs : 0 < s)
    (hV1 : s ^ 2 ≤ 2 * V) (hV2 : V ≤ s ^ 2 * n ^ 2) (hΓA : 40 * A ≤ Γ) :
    ∃ L ≤ Nat.clog 2 n + 8, A * s ≤ OneDim.scale (topScale A V) L ∧
      OneDim.scale (topScale A V) L ≤ Γ * s / 20 := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hV : 0 < V := by nlinarith [pow_pos hs 2]
  have hr : 0 < 2 * A ^ 2 * V := by positivity
  set H := topScale A V with hH_def
  have hH : H = (2 : ℝ) ^ Int.clog 4 (2 * A ^ 2 * V) := rfl
  have hHpos : 0 < H := zpow_pos (by norm_num) _
  have hsq : H ^ 2 = (4 : ℝ) ^ Int.clog 4 (2 * A ^ 2 * V) := by
    rw [hH, sq, ← mul_zpow]
    norm_num
  have hlo : 2 * A ^ 2 * V ≤ H ^ 2 := by
    rw [hsq]
    exact_mod_cast Int.self_le_zpow_clog (R := ℝ) (b := 4) (by norm_num) (2 * A ^ (2 : ℕ) * V)
  have hhi : H ^ 2 < 8 * A ^ 2 * V := by
    have h := Int.zpow_pred_clog_lt_self (R := ℝ) (b := 4) (by norm_num) hr
    push_cast at h
    rw [zpow_sub_one₀ (by norm_num : (4 : ℝ) ≠ 0)] at h
    rw [hsq]
    linarith
  have hHge : A * s ≤ H := by
    have h1 : (A * s) ^ 2 ≤ H ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hV1 (sq_nonneg A)]
    exact (sq_le_sq₀ (by positivity) hHpos.le).1 h1
  have hpow : (n : ℝ) * 256 ≤ 2 ^ (Nat.clog 2 n + 8) := by
    have h := Nat.le_pow_clog (b := 2) (by norm_num) n
    have h' : (n : ℝ) ≤ 2 ^ Nat.clog 2 n := by exact_mod_cast h
    rw [pow_add]
    norm_num
    linarith
  have hHle : H ≤ 512 * n * A * s := by
    have h1 : H ^ 2 ≤ (512 * n * A * s) ^ 2 := by
      have : 8 * A ^ 2 * V ≤ 8 * A ^ 2 * (s ^ 2 * n ^ 2) :=
        mul_le_mul_of_nonneg_left hV2 (by positivity)
      nlinarith
    exact (sq_le_sq₀ hHpos.le (by positivity)).1 h1
  have hlast : OneDim.scale H (Nat.clog 2 n + 8) ≤ 2 * A * s := by
    unfold OneDim.scale
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 2 * A * s)]
  have hT : 2 * A * s ≤ Γ * s / 20 := by
    nlinarith [mul_le_mul_of_nonneg_right hΓA hs.le]
  have hex : ∃ L, OneDim.scale H L ≤ Γ * s / 20 := ⟨_, hlast.trans hT⟩
  obtain ⟨L, hL, hmin⟩ : ∃ L, OneDim.scale H L ≤ Γ * s / 20 ∧
      ∀ L' < L, ¬ OneDim.scale H L' ≤ Γ * s / 20 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun L' h ↦ Nat.find_min hex h⟩
  refine ⟨L, ?_, ?_, hL⟩
  · by_contra h
    exact hmin _ (by omega) (hlast.trans hT)
  · rcases L with _ | L
    · simpa [OneDim.scale] using hHge
    · have h1 := not_le.1 (hmin L (by omega))
      have h2 : OneDim.scale H (L + 1) = OneDim.scale H L / 2 := by
        unfold OneDim.scale
        rw [pow_succ, div_div]
      rw [h2]
      linarith

/-! ### Errors -/

theorem clustersWithin_mono {ε ε' : ℝ} {ℓ : Fin n → Fin k} {out : Output}
    (h : ClustersWithin ε ℓ out) (hε : ε ≤ ε') : ClustersWithin ε' ℓ out :=
  ⟨h.1, h.2.1, h.2.2.imp fun _ hπ ↦ hπ.trans hε⟩

end OneDimApply

open OneDimApply

/-- **The line clustering of the projections is correct.** For a direction `a` along which the
centers `⟨a, μ_c⟩` are at least `Γ √(aᵀ Σ a)` apart, with `Γ² ≥ 10⁸ · 4^c · log (1/wmin)`, the
clustering on the line of the projections `⟨a, ỹ_j⟩` of the rounded points, with the parameters of
`BS23.Colinear.params wmin` and a scale `V` with `aᵀ Σ a ≤ 2 V ≤ 2 (aᵀ Σ a) n²`, errs on at most a
`(wmin / k)^c` fraction of the points. The sample: true points `μ_{ℓ_j} + ν_j` rounded within `1/n`
in the geometry of `Σ`, clusters of at least `wmin n / 2` points, and noise with the Gaussian
directional moments up to degree `2 logInv wmin + 8` within `η' ≤ wmin / 2`. -/
theorem oneDim_clustersWithin {k d n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) {M : Mixture k d}
    (hM : M.Valid) {wmin : ℚ} (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i)
    {ℓ : Fin n → Fin k} {ν yt : Fin n → Fin d → ℝ}
    (hround : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2)
    (hsize : ∀ i, (wmin : ℝ) / 2 * n ≤ (cluster ℓ i).card)
    {η' : ℝ} {D : ℕ} (hU : UniformNoise M.S η' D ℓ ν) (hη' : η' ≤ (wmin : ℝ) / 2)
    (hD : 2 * logInv wmin + 8 ≤ D)
    {a : Fin d → ℝ} (ha : 0 < quad M.S a) {Γ : ℝ} (hΓ : 0 < Γ)
    (hsep : ∀ i₁ i₂, i₁ ≠ i₂ → Γ * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ (M.μ i₁ - M.μ i₂)|)
    {c : ℕ} (hΓc : 10 ^ 8 * 4 ^ c * Real.log (1 / (wmin : ℝ)) ≤ Γ ^ 2)
    {V : ℝ} (hV1 : quad M.S a ≤ 2 * V) (hV2 : V ≤ quad M.S a * n ^ 2) :
    ClustersWithin (((wmin : ℝ) / k) ^ c) ℓ
      (List.ofFn (OneDim.cluster k ((wmin ^ 2 / 100 : ℚ) : ℝ) ((wmin / 4 : ℚ) : ℝ)
        (topScale (((Nat.sqrt (64 * (logInv wmin + 1)) + 1 : ℕ) : ℚ) : ℝ) V)
        (Nat.clog 2 n + 8) (fun j ↦ a ⬝ᵥ yt j))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hn
  have hw0 : (0 : ℝ) < wmin := by exact_mod_cast hwmin
  have hkw : (k : ℝ) * wmin ≤ 1 := k_mul_wmin_le hM hw
  have hwhalf : wmin ≤ 1 / 2 := wmin_le_half hk hkw hwmin
  have hs : 0 < Real.sqrt (quad M.S a) := Real.sqrt_pos.2 ha
  have hs2 : Real.sqrt (quad M.S a) ^ 2 = quad M.S a := Real.sq_sqrt ha.le
  have hW : 1 ≤ (wmin : ℝ) * 2 ^ logInv wmin := one_le_mul_two_pow_logInv hwmin
  have hW1 : (1 : ℝ) ≤ 2 ^ logInv wmin := one_le_pow₀ (by norm_num)
  obtain ⟨hΓ', hΓA⟩ := gamma_bounds hΓ (logInv_add_four_le hwmin hwhalf) hΓc
    (sqrt_add_one_sq_le (logInv wmin))
  have hr0 : (8 : ℝ) ≤ Nat.sqrt (64 * (logInv wmin + 1)) := by
    exact_mod_cast eight_le_sqrt (logInv wmin)
  have hΓ40 : 40 ≤ Γ := by linarith
  -- the parameters over the reals
  have hθeq : ((wmin ^ 2 / 100 : ℚ) : ℝ) = (wmin : ℝ) ^ 2 / 100 := by push_cast; ring
  have hεeq : ((wmin / 4 : ℚ) : ℝ) = (wmin : ℝ) / 4 := by push_cast; ring
  have hA : (((Nat.sqrt (64 * (logInv wmin + 1)) + 1 : ℕ) : ℚ) : ℝ) =
      (Nat.sqrt (64 * (logInv wmin + 1)) : ℝ) + 1 := by push_cast; ring
  rw [hθeq, hεeq, hA]
  -- the tails
  have htail : ∀ ρ : ℝ, 1 / (n : ℝ) < ρ → ∀ i, (((cluster ℓ i).filter fun j ↦
      ρ * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ yt j - a ⬝ᵥ M.μ i|).card : ℝ) ≤
        tailFn n (logInv wmin + 4) ρ * (cluster ℓ i).card :=
    fun ρ hρ i ↦ tail_le hM.posDef hn hround hU (by omega) (by omega) ha i
      ((mul_le_mul_of_nonneg_right hη' hn'.le).trans (hsize i)) hρ
  have hfar : ∀ ρ, Γ / 10 ≤ ρ → tailFn n (logInv wmin + 4) ρ *
      (2 ^ 20 * ((2 : ℝ) ^ logInv wmin) ^ 2 * (((2 : ℝ) ^ logInv wmin) ^ 2) ^ c) ≤ 2 :=
    fun ρ hρ ↦ tailFn_far_le hn hΓ40 hΓ' hρ
  have hsep' : ∀ i₁ i₂, i₁ ≠ i₂ →
      Γ * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ M.μ i₁ - a ⬝ᵥ M.μ i₂| := fun i₁ i₂ h ↦ by
    rw [← dotProduct_sub]
    exact hsep i₁ i₂ h
  have hgrid := exists_grid_scale (V := V) hn (by positivity) hs (by rw [hs2]; exact hV1)
    (by rw [hs2]; exact hV2) hΓA
  have key := OneDim.cluster_clustersWithin_of_tails hk hn (fun j ↦ a ⬝ᵥ yt j) ℓ
    (fun i ↦ a ⬝ᵥ M.μ i) (s := Real.sqrt (quad M.S a)) (Γ := Γ) (w := (wmin : ℝ) / 2)
    (θ := (wmin : ℝ) ^ 2 / 100) (ε := (wmin : ℝ) / 4)
    (A := (Nat.sqrt (64 * (logInv wmin + 1)) : ℝ) + 1)
    (H := topScale ((Nat.sqrt (64 * (logInv wmin + 1)) : ℝ) + 1) V)
    (tailFn n (logInv wmin + 4)) (ℓmax := Nat.clog 2 n + 8) hsep' (by positivity) hsize
    (htail _ (by linarith)) (htail _ (by linarith)) (htail _ (by linarith))
    (htail _ (by linarith)) (by positivity)
    (tail_light hW hW1 (tailFn_nonneg _ _ _) (hfar _ le_rfl))
    (tail_range hw0 hW (by positivity) hkw
      (tailFn_range_le hn (four_mul_le_sqrt_sq (logInv wmin))))
    (tail_heavy hW hW1 (tailFn_nonneg _ _ _) (hfar _ (by linarith)))
    (zpow_pos (by norm_num) _) hgrid
  exact clustersWithin_mono key
    (tail_error (by omega) hw0 hkw hW hW1 (tailFn_nonneg _ _ _) (hfar _ (by linarith)))

/-- `BS23.Colinear.oneDim_clustersWithin` with the parameters as the algorithm uses them over the
reals (`BS23.Colinear.Params.cast` of `BS23.Colinear.params wmin`). -/
theorem oneDim_clustersWithin_params {k d n : ℕ} (hk : 2 ≤ k) (hn : 0 < n) {M : Mixture k d}
    (hM : M.Valid) {wmin : ℚ} (hwmin : 0 < wmin) (hw : ∀ i, (wmin : ℝ) ≤ M.w i)
    {ℓ : Fin n → Fin k} {ν yt : Fin n → Fin d → ℝ}
    (hround : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2)
    (hsize : ∀ i, (wmin : ℝ) / 2 * n ≤ (cluster ℓ i).card)
    {η' : ℝ} {D : ℕ} (hU : UniformNoise M.S η' D ℓ ν) (hη' : η' ≤ (wmin : ℝ) / 2)
    (hD : 2 * logInv wmin + 8 ≤ D)
    {a : Fin d → ℝ} (ha : 0 < quad M.S a) {Γ : ℝ} (hΓ : 0 < Γ)
    (hsep : ∀ i₁ i₂, i₁ ≠ i₂ → Γ * Real.sqrt (quad M.S a) ≤ |a ⬝ᵥ (M.μ i₁ - M.μ i₂)|)
    {c : ℕ} (hΓc : 10 ^ 8 * 4 ^ c * Real.log (1 / (wmin : ℝ)) ≤ Γ ^ 2)
    {V : ℝ} (hV1 : quad M.S a ≤ 2 * V) (hV2 : V ≤ quad M.S a * n ^ 2) :
    ClustersWithin (((wmin : ℝ) / k) ^ c) ℓ
      (List.ofFn (OneDim.cluster k (params wmin).cast.θ (params wmin).cast.ε
        (topScale (params wmin).cast.A V) (Nat.clog 2 n + 8) (fun j ↦ a ⬝ᵥ yt j))) :=
  oneDim_clustersWithin hk hn hM hwmin hw hround hsize hU hη' hD ha hΓ hsep hΓc hV1 hV2

end BS23.Colinear
