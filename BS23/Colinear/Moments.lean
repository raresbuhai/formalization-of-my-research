module

public import BS23.Common.Hermite
public import BS23.Common.Uniform
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Empirical moments of the rounded sample along a direction

The first step (MOM) of the analysis of the colinear algorithm [BS23, Theorem 1.2], and the only
place where it looks at the sample directly. It is deterministic: on the good event (cluster sizes
`| |S_c|/n - w_c | ≤ η w_c` and the noise in uniform form, `BS23.UniformNoise` with error `η'` up
to degree `D`), for every rounding within `1/n` and every direction `v` with `vᵀ cov v ≤ 1`,
the empirical moments of the rounded points `ỹ_j` along `v` are close to those of the mixture:

`|(1/n) ∑_j ⟨ỹ_j - μ̄, v⟩^r - ∑_c w_c · hmom r ⟨μ_c - μ̄, v⟩ (vᵀΣv)| ≤ (η + η' + 1/n) K_r`

for `2 r ≤ D`, with `K_r = (4 (r + 1))^(2 (r + 1)) / wmin^(r + 1)` (`BS23.Colinear.momConst`); see
`BS23.Colinear.moment_close`, and `BS23.Colinear.moment_close_homog` for every `v`, with the
error multiplied by `(vᵀ cov v)^(r/2)`. Here `hmom r a q` is the `r`-th moment of `N(a, q)`.

The proof splits the sum over the clusters. On cluster `c`, `⟨ỹ_j - μ̄, v⟩ = a_c + X_j + e_j`
with `a_c = ⟨μ_c - μ̄, v⟩`, `X_j = ⟨ν_j, v⟩` and the rounding error `|e_j| ≤ √(vᵀΣv) / n`
(Cauchy–Schwarz in the geometry of `Σ`). Expanding `(a_c + X_j)^r` binomially, the empirical
moments of `X_j` are replaced by the Gaussian ones, which gives `(|S_c|/n) hmom r a_c (vᵀΣv)`;
then `|S_c|/n` is replaced by `w_c`. The rounding errors cost
`|(Z + e)^r - Z^r| ≤ r |e| max(|Z + e|, |Z|)^(r-1)`, which is controlled by the empirical
`2r`-th moment of the noise. Everything uses `|a_c| ≤ w_c^{-1/2} ≤ 1/wmin` (from
`vᵀ cov v = vᵀΣv + ∑_c w_c a_c²`), `vᵀΣv ≤ 1` and `k ≤ 1/wmin`.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix Finset
open scoped Nat

variable {k d : ℕ}

/-! ### Linear algebra -/

/-- `vᵀ cov v = vᵀ Σ v + ∑_c w_c ⟨μ_c - μ̄, v⟩²`. -/
theorem quad_cov (M : Mixture k d) (v : Fin d → ℝ) :
    v ⬝ᵥ (M.cov *ᵥ v) = v ⬝ᵥ (M.S *ᵥ v) + ∑ c, M.w c * ((M.μ c - M.mean) ⬝ᵥ v) ^ 2 := by
  rw [Mixture.cov, add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [smul_mulVec, vecMulVec_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    op_smul_eq_smul, smul_eq_mul, dotProduct_comm v]
  ring

/-- `∑_c w_c ⟨μ_c - μ̄, v⟩² = vᵀ cov v - vᵀ Σ v`. -/
theorem sum_w_sq_center (M : Mixture k d) (v : Fin d → ℝ) :
    ∑ c, M.w c * ((M.μ c - M.mean) ⬝ᵥ v) ^ 2 = v ⬝ᵥ (M.cov *ᵥ v) - v ⬝ᵥ (M.S *ᵥ v) := by
  rw [quad_cov]
  ring

/-- `vᵀ Σ v ≥ 0` for a valid mixture. -/
theorem quad_S_nonneg {M : Mixture k d} (hM : M.Valid) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (M.S *ᵥ v) := by
  simpa using hM.posDef.posSemidef.dotProduct_mulVec_nonneg v

/-- `vᵀ Σ v ≤ vᵀ cov v` when the weights are nonnegative. -/
theorem quad_S_le_quad_cov (M : Mixture k d) (hw : ∀ c, 0 ≤ M.w c) (v : Fin d → ℝ) :
    v ⬝ᵥ (M.S *ᵥ v) ≤ v ⬝ᵥ (M.cov *ᵥ v) := by
  rw [quad_cov]
  linarith [sum_nonneg fun c (_ : c ∈ univ) ↦ mul_nonneg (hw c) (sq_nonneg ((M.μ c - M.mean) ⬝ᵥ v))]

/-- `w_c ⟨μ_c - μ̄, v⟩² ≤ vᵀ cov v` when the weights are nonnegative. -/
theorem w_mul_sq_center_le {M : Mixture k d} (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c)
    (v : Fin d → ℝ) (c : Fin k) :
    M.w c * ((M.μ c - M.mean) ⬝ᵥ v) ^ 2 ≤ v ⬝ᵥ (M.cov *ᵥ v) := by
  have := single_le_sum (fun c (_ : c ∈ univ) ↦ mul_nonneg (hw c)
    (sq_nonneg ((M.μ c - M.mean) ⬝ᵥ v))) (mem_univ c)
  rw [quad_cov]
  linarith [quad_S_nonneg hM v]

/-- `|⟨μ_c - μ̄, v⟩| ≤ wmin^{-1/2}` when `vᵀ cov v ≤ 1` and all weights are at least
`wmin > 0`. -/
theorem abs_center_le {M : Mixture k d} (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c) {v : Fin d → ℝ} (hv : v ⬝ᵥ (M.cov *ᵥ v) ≤ 1) (c : Fin k) :
    |(M.μ c - M.mean) ⬝ᵥ v| ≤ Real.sqrt (1 / wmin) := by
  refine Real.abs_le_sqrt ?_
  rw [le_div_iff₀ hwmin]
  have h := w_mul_sq_center_le hM (fun c ↦ hwmin.le.trans (hw c)) v c
  nlinarith [hw c, sq_nonneg ((M.μ c - M.mean) ⬝ᵥ v)]

/-- **Cauchy–Schwarz in the geometry of `S`**: `⟨u, v⟩² ≤ (uᵀ S⁻¹ u) (vᵀ S v)`. -/
theorem sq_dotProduct_le {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) (u v : Fin d → ℝ) :
    (u ⬝ᵥ v) ^ 2 ≤ sqNormIn S u * (v ⬝ᵥ (S *ᵥ v)) := by
  have h := hS.inv.star_dotProduct_mulVec_mul_le u (S *ᵥ v)
  have hSv : S⁻¹ *ᵥ (S *ᵥ v) = v := by
    rw [mulVec_mulVec, nonsing_inv_mul _ ((isUnit_iff_isUnit_det S).mp hS.isUnit), one_mulVec]
  simp only [star_trivial, hSv] at h
  rw [sqNormIn, dotProduct_comm (S *ᵥ v) v] at *
  nlinarith [h]

/-! ### Gaussian moments -/

/-- `E Z^p ≤ p!`. -/
theorem gaussMom_le_factorial (p : ℕ) : gaussMom p ≤ p ! := by
  unfold gaussMom
  split_ifs
  · exact (Nat.doubleFactorial_le_factorial _).trans (Nat.factorial_le (Nat.sub_le _ _))
  · exact Nat.zero_le _

/-- `E (a + s Z)^r`, expanded binomially, is `hmom r a (s²)`. -/
theorem sum_choose_gaussMom (r : ℕ) (a s : ℝ) :
    ∑ p ∈ range (r + 1), (r.choose p : ℝ) * a ^ (r - p) * (gaussMom p : ℝ) * s ^ p =
      hmom r a (s ^ 2) := by
  have himg : (range (r / 2 + 1)).image (fun i ↦ 2 * i) ⊆ range (r + 1) := by
    intro p hp
    simp only [mem_image, mem_range] at hp ⊢
    obtain ⟨i, hi, rfl⟩ := hp
    omega
  rw [hmom, ← sum_subset himg, sum_image (fun x _ y _ h ↦ by simpa using h)]
  · refine sum_congr rfl fun i _ ↦ ?_
    simp only [gaussMom, even_two_mul, ite_true, hermCoeff]
    push_cast
    ring
  · intro p hp hpi
    have hodd : ¬ Even p := by
      rintro ⟨i, rfl⟩
      apply hpi
      simp only [mem_image, mem_range] at hp ⊢
      exact ⟨i, by omega, by ring⟩
    simp [gaussMom, hodd]

/-- `∑_p C(r, p) A^(r-p) = (A + 1)^r`. -/
theorem sum_choose_pow (r : ℕ) (A : ℝ) :
    ∑ p ∈ range (r + 1), (r.choose p : ℝ) * A ^ (r - p) = (A + 1) ^ r := by
  rw [add_comm A 1, add_pow]
  exact sum_congr rfl fun p _ ↦ by ring

/-- `|hmom r a (s²)| ≤ (2r)! (W + 1)^r` for `|a| ≤ W` and `0 ≤ s ≤ 1`. -/
theorem abs_hmom_le {r : ℕ} {a s W : ℝ} (ha : |a| ≤ W) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |hmom r a (s ^ 2)| ≤ (2 * r)! * (W + 1) ^ r := by
  have hW : 0 ≤ W := (abs_nonneg a).trans ha
  rw [← sum_choose_gaussMom, ← sum_choose_pow, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp ↦ ?_)
  have hp : p ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hp)
  have hg : (gaussMom p : ℝ) ≤ (2 * r)! := by
    exact_mod_cast (gaussMom_le_factorial p).trans (Nat.factorial_le (by omega))
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hs0, Nat.abs_cast, Nat.abs_cast]
  calc (r.choose p : ℝ) * |a| ^ (r - p) * (gaussMom p : ℝ) * s ^ p
      ≤ (r.choose p : ℝ) * W ^ (r - p) * (2 * r)! * 1 := by
        gcongr
        exact pow_le_one₀ hs0 hs1
    _ = _ := by ring

/-- Homogeneity: `hmom r (s a) (s² q) = s^r hmom r a q`. -/
theorem hmom_mul (r : ℕ) (s a q : ℝ) : hmom r (s * a) (s ^ 2 * q) = s ^ r * hmom r a q := by
  rw [hmom, hmom, mul_sum]
  refine sum_congr rfl fun i hi ↦ ?_
  have hi : 2 * i ≤ r := by have := mem_range.mp hi; omega
  have : s ^ r = s ^ (r - 2 * i) * s ^ (2 * i) := by rw [← pow_add, Nat.sub_add_cancel hi]
  rw [this, mul_pow, mul_pow, ← pow_mul]
  ring

/-- The moments of `N(0, 0)` of positive order vanish. -/
theorem hmom_zero_zero {r : ℕ} (hr : 0 < r) : hmom r (0 : ℝ) 0 = 0 := by
  rw [hmom]
  refine sum_eq_zero fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [zero_pow hr.ne']
  · simp [zero_pow hi0.ne']

/-! ### One cluster -/

variable {n : ℕ}

/-- The binomial expansion of `(1/n) ∑_{j ∈ s} (a + X_j)^r`. -/
theorem sum_add_pow_div (s : Finset (Fin n)) (a : ℝ) (X : Fin n → ℝ) (r : ℕ) :
    (∑ j ∈ s, (a + X j) ^ r) / n =
      ∑ p ∈ range (r + 1), (r.choose p : ℝ) * a ^ (r - p) * ((∑ j ∈ s, X j ^ p) / n) := by
  have h : ∀ j, (a + X j) ^ r = ∑ p ∈ range (r + 1), (r.choose p : ℝ) * a ^ (r - p) * X j ^ p :=
    fun j ↦ by
      rw [add_comm, add_pow]
      exact sum_congr rfl fun p _ ↦ by ring
  simp_rw [h]
  rw [sum_comm, sum_div]
  refine sum_congr rfl fun p _ ↦ ?_
  rw [← mul_sum, mul_div_assoc]

/-- The binomial expansion of `(a + ⟨ν_j, v⟩)^r` over one cluster, with the empirical moments of
the noise replaced by the Gaussian ones. -/
theorem cluster_moment_close {S : Matrix (Fin d) (Fin d) ℝ} {η' : ℝ} {D : ℕ}
    {ℓ : Fin n → Fin k} {ν : Fin n → Fin d → ℝ} (hU : UniformNoise S η' D ℓ ν) (hη' : 0 ≤ η')
    (c : Fin k) {r : ℕ} (hr : r ≤ D) {v : Fin d → ℝ} (hq0 : 0 ≤ v ⬝ᵥ (S *ᵥ v))
    (hq1 : v ⬝ᵥ (S *ᵥ v) ≤ 1) {a W : ℝ} (ha : |a| ≤ W) :
    |(∑ j ∈ cluster ℓ c, (a + ν j ⬝ᵥ v) ^ r) / n -
        ((cluster ℓ c).card : ℝ) / n * hmom r a (v ⬝ᵥ (S *ᵥ v))| ≤ η' * (W + 1) ^ r := by
  have hW : 0 ≤ W := (abs_nonneg a).trans ha
  set q := v ⬝ᵥ (S *ᵥ v)
  have hs0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs1 : Real.sqrt q ≤ 1 := Real.sqrt_le_one.mpr hq1
  rw [← Real.sq_sqrt hq0, ← sum_choose_gaussMom, sum_add_pow_div, mul_sum, ← sum_sub_distrib,
    ← sum_choose_pow, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp ↦ ?_)
  have hp : p ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hp)
  have hU' := hU c p (hp.trans hr) v
  have hrw : (r.choose p : ℝ) * a ^ (r - p) * ((∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ v) ^ p) / n) -
      ((cluster ℓ c).card : ℝ) / n *
        ((r.choose p : ℝ) * a ^ (r - p) * (gaussMom p : ℝ) * Real.sqrt q ^ p) =
      (r.choose p : ℝ) * a ^ (r - p) * ((∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ v) ^ p) / n -
        ((cluster ℓ c).card : ℝ) / n * (gaussMom p : ℝ) * Real.sqrt q ^ p) := by ring
  rw [hrw, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
  calc (r.choose p : ℝ) * |a| ^ (r - p) *
        |(∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ v) ^ p) / n -
          ((cluster ℓ c).card : ℝ) / n * (gaussMom p : ℝ) * Real.sqrt q ^ p|
      ≤ (r.choose p : ℝ) * W ^ (r - p) * (η' * 1) := by
        gcongr
        exact hU'.trans (mul_le_mul_of_nonneg_left (pow_le_one₀ hs0 hs1) hη')
    _ = _ := by ring

/-- The `2r`-th empirical moment of the noise of one cluster along `v` is bounded. -/
theorem cluster_even_moment_le {S : Matrix (Fin d) (Fin d) ℝ} {η' : ℝ} {D : ℕ}
    {ℓ : Fin n → Fin k} {ν : Fin n → Fin d → ℝ} (hU : UniformNoise S η' D ℓ ν) (hη' : 0 ≤ η')
    (c : Fin k) {r : ℕ} (hr : 2 * r ≤ D) {v : Fin d → ℝ} (hq1 : v ⬝ᵥ (S *ᵥ v) ≤ 1) :
    (∑ j ∈ cluster ℓ c, (ν j ⬝ᵥ v) ^ (2 * r)) / n ≤ (2 * r)! + η' := by
  have hs0 : 0 ≤ Real.sqrt (v ⬝ᵥ (S *ᵥ v)) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (v ⬝ᵥ (S *ᵥ v)) ^ (2 * r) ≤ 1 :=
    pow_le_one₀ hs0 (Real.sqrt_le_one.mpr hq1)
  have hcard : ((cluster ℓ c).card : ℝ) / n ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
    exact_mod_cast (card_filter_le _ _).trans (card_fin n).le
  have hg : (gaussMom (2 * r) : ℝ) ≤ (2 * r)! := by exact_mod_cast gaussMom_le_factorial _
  have h := (abs_le.mp (hU c (2 * r) hr v)).2
  have h1 : ((cluster ℓ c).card : ℝ) / n * (gaussMom (2 * r) : ℝ) *
      Real.sqrt (v ⬝ᵥ (S *ᵥ v)) ^ (2 * r) ≤ (2 * r)! := by
    calc _ ≤ 1 * ((2 * r)! : ℝ) * 1 := by gcongr
      _ = _ := by ring
  have h2 : η' * Real.sqrt (v ⬝ᵥ (S *ᵥ v)) ^ (2 * r) ≤ η' :=
    (mul_le_mul_of_nonneg_left hs1 hη').trans_eq (mul_one _)
  linarith

/-! ### Rounding and the perturbation -/

/-- `|⟨u, v⟩| ≤ √(vᵀSv) / n` when `uᵀS⁻¹u ≤ 1/n²`. -/
theorem abs_dotProduct_le_of_sqNormIn {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef)
    {u v : Fin d → ℝ} (hn : 0 < n) (hu : sqNormIn S u ≤ 1 / n ^ 2) :
    |u ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ (S *ᵥ v)) / n := by
  have hq0 : 0 ≤ v ⬝ᵥ (S *ᵥ v) := by simpa using hS.posSemidef.dotProduct_mulVec_nonneg v
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp ?_
  rw [sq_abs, div_pow, Real.sq_sqrt hq0]
  calc (u ⬝ᵥ v) ^ 2 ≤ sqNormIn S u * (v ⬝ᵥ (S *ᵥ v)) := sq_dotProduct_le hS u v
    _ ≤ 1 / n ^ 2 * (v ⬝ᵥ (S *ᵥ v)) := mul_le_mul_of_nonneg_right hu hq0
    _ = _ := by ring

/-- `|x|^r ≤ 1 + x^(2r)`. -/
theorem abs_pow_le_one_add (x : ℝ) (r : ℕ) : |x| ^ r ≤ 1 + x ^ (2 * r) := by
  have : x ^ (2 * r) = (|x| ^ r) ^ 2 := by rw [← abs_pow, sq_abs, ← pow_mul, mul_comm]
  rw [this]
  nlinarith [sq_nonneg (|x| ^ r - 1)]

/-- The effect of the rounding on one point: `|(Z + e)^r - Z^r|` for `|e| ≤ 1/n` and
`|Z| ≤ W + |X|`. -/
theorem abs_add_pow_sub_pow_le {Z e X W : ℝ} {r : ℕ} (hn : 0 < n) (he : |e| ≤ 1 / n)
    (hZ : |Z| ≤ W + |X|) (hW : 1 ≤ W) :
    |(Z + e) ^ r - Z ^ r| ≤ 1 / n * (r * 2 ^ r * ((W + 1) ^ r + 1 + X ^ (2 * r))) := by
  have hn1 : (1 : ℝ) / n ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hn) (Nat.cast_nonneg _)
  have hmax : max |Z + e| |Z| ≤ (W + 1) + |X| := by
    refine max_le ((abs_add_le _ _).trans ?_) ?_ <;> linarith
  have hT : 1 ≤ (W + 1) + |X| := by linarith [abs_nonneg X]
  have h1 : max |Z + e| |Z| ^ (r - 1) ≤ ((W + 1) + |X|) ^ r :=
    (pow_le_pow_left₀ (le_max_of_le_right (abs_nonneg _)) hmax _).trans
      (pow_le_pow_right₀ hT (Nat.sub_le _ _))
  have h2 : ((W + 1) + |X|) ^ r ≤ 2 ^ r * ((W + 1) ^ r + |X| ^ r) :=
    (add_pow_le (by linarith) (abs_nonneg X) r).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (Nat.sub_le _ _))
        (by positivity))
  have h3 := abs_pow_le_one_add X r
  have h := abs_pow_sub_pow_le (a := Z + e) (b := Z) (n := r)
  rw [add_sub_cancel_left] at h
  refine h.trans ?_
  calc |e| * r * max |Z + e| |Z| ^ (r - 1)
      ≤ 1 / n * r * (2 ^ r * ((W + 1) ^ r + (1 + X ^ (2 * r)))) := by
        gcongr
        exact h1.trans (h2.trans (by gcongr))
    _ = _ := by ring

/-! ### Numerics -/

/-- The constant `(4 (r + 1))^(2 (r + 1)) / wmin^(r + 1)` of the moment bound. -/
noncomputable def momConst (r : ℕ) (wmin : ℝ) : ℝ :=
  (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) / wmin ^ (r + 1)

/-- `(r + 1) 2^r (2^r + 1 + (2r)!) ≤ (4 (r + 1))^(2 (r + 1))`. -/
theorem momNum_le (r : ℕ) :
    ((r : ℝ) + 1) * 2 ^ r * (2 ^ r + 1 + (2 * r)!) ≤ (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) := by
  have key : (r + 1) * 2 ^ r * (2 ^ r + 1 + (2 * r)!) ≤ (4 * (r + 1)) ^ (2 * (r + 1)) := by
    have hR : 0 < 2 * (r + 1) := by omega
    have hmono : ∀ m ≤ 2 * (r + 1), m ^ m ≤ (2 * (r + 1)) ^ (2 * (r + 1)) := fun m hm ↦
      (Nat.pow_le_pow_left hm _).trans (Nat.pow_le_pow_right hR hm)
    have h1 : (2 * r)! ≤ (2 * (r + 1)) ^ (2 * (r + 1)) :=
      (Nat.factorial_le_pow _).trans (hmono _ (by omega))
    have h2 : 2 ^ r + 1 ≤ (2 * (r + 1)) ^ (2 * (r + 1)) := by
      have h21 : 2 ^ r + 1 ≤ 2 ^ (r + 1) := by
        rw [pow_succ]
        have := Nat.one_le_two_pow (n := r)
        omega
      exact h21.trans
        ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hR (by omega)))
    have h3 : (r + 1) * 2 ^ r * 2 ≤ 4 ^ (r + 1) := by
      have : r + 1 ≤ 2 ^ (r + 1) := Nat.lt_two_pow_self.le
      calc (r + 1) * 2 ^ r * 2 = (r + 1) * 2 ^ (r + 1) := by ring
        _ ≤ 2 ^ (r + 1) * 2 ^ (r + 1) := Nat.mul_le_mul_right _ this
        _ = 4 ^ (r + 1) := by rw [← mul_pow]; norm_num
    calc (r + 1) * 2 ^ r * (2 ^ r + 1 + (2 * r)!)
        ≤ (r + 1) * 2 ^ r * (2 * (2 * (r + 1)) ^ (2 * (r + 1))) := by gcongr; omega
      _ = (r + 1) * 2 ^ r * 2 * (2 * (r + 1)) ^ (2 * (r + 1)) := by ring
      _ ≤ 4 ^ (r + 1) * (2 * (r + 1)) ^ (2 * (r + 1)) := Nat.mul_le_mul_right _ h3
      _ = (4 * (r + 1)) ^ (2 * (r + 1)) := by
        have e1 : (2 * (r + 1)) ^ (2 * (r + 1)) = 4 ^ (r + 1) * (r + 1) ^ (2 * (r + 1)) := by
          rw [mul_pow, pow_mul]; norm_num
        have e2 : (4 * (r + 1)) ^ (2 * (r + 1)) = 16 ^ (r + 1) * (r + 1) ^ (2 * (r + 1)) := by
          rw [mul_pow, pow_mul]; norm_num
        rw [e1, e2, ← mul_assoc, ← mul_pow]
        norm_num
  exact_mod_cast key

/-- The final bookkeeping of the moment bound. -/
theorem moment_numerics {η η' t W : ℝ} {r : ℕ} (hη : 0 ≤ η) (hη' : 0 ≤ η') (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hW : 1 ≤ W) :
    t * (r * 2 ^ r * ((W + 1) ^ r + 1 + W * ((2 * r)! + η'))) + W * η' * (W + 1) ^ r +
        η * ((2 * r)! * (W + 1) ^ r) ≤
      (η + η' + t) * ((4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) * W ^ (r + 1)) := by
  have hG : (1 : ℝ) ≤ ((2 * r)! : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  set G : ℝ := ((2 * r)! : ℝ)
  set N : ℝ := (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1))
  set V : ℝ := W ^ (r + 1)
  set P : ℝ := (W + 1) ^ r
  set T : ℝ := (2 : ℝ) ^ r
  have hW0 : 0 ≤ W := by linarith
  have hT : 1 ≤ T := one_le_pow₀ one_le_two
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hWr : 1 ≤ W ^ r := one_le_pow₀ hW
  have hV : V = W ^ r * W := pow_succ W r
  have hVr : W ^ r ≤ V := by rw [hV]; nlinarith
  have hV1 : 1 ≤ V := hWr.trans hVr
  have hWV : W ≤ V := by rw [hV]; nlinarith
  have hP : P ≤ T * W ^ r := by
    calc P ≤ (2 * W) ^ r := pow_le_pow_left₀ (by linarith) (by linarith) r
      _ = T * W ^ r := mul_pow _ _ _
  have hN : ((r : ℝ) + 1) * T * (T + 1 + G) ≤ N := momNum_le r
  have hNV : ((r : ℝ) + 1) * T * (T + 1 + G) * V ≤ N * V :=
    mul_le_mul_of_nonneg_right hN (by linarith)
  -- the three coefficients
  have hi : G * P ≤ N * V := by
    calc G * P ≤ G * (T * V) := by gcongr; exact hP.trans (by gcongr)
      _ = (1 * T * G) * V := by ring
      _ ≤ (((r : ℝ) + 1) * T * (T + 1 + G)) * V := by gcongr <;> linarith
      _ ≤ N * V := hNV
  have hii : W * P + r * T * W ≤ N * V := by
    have hWP : W * P ≤ T * V := by
      calc W * P ≤ W * (T * W ^ r) := by gcongr
        _ = T * V := by rw [hV]; ring
    calc W * P + r * T * W ≤ T * V + r * T * V := by gcongr
      _ = (((r : ℝ) + 1) * T * 1) * V := by ring
      _ ≤ (((r : ℝ) + 1) * T * (T + 1 + G)) * V := by gcongr; linarith
      _ ≤ N * V := hNV
  have hiii : r * T * (P + 1 + W * G) ≤ N * V := by
    calc r * T * (P + 1 + W * G) ≤ r * T * (T * V + V + V * G) := by
          gcongr
          exact hP.trans (by gcongr)
      _ = (r * T * (T + 1 + G)) * V := by ring
      _ ≤ (((r : ℝ) + 1) * T * (T + 1 + G)) * V := by gcongr; linarith
      _ ≤ N * V := hNV
  have e1 : t * (r * T * (P + 1 + W * G)) ≤ t * (N * V) := mul_le_mul_of_nonneg_left hiii ht0
  have e2 : η' * (t * (r * T * W)) ≤ η' * (r * T * W) :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (by positivity) ht1) hη'
  have e3 : η' * (W * P + r * T * W) ≤ η' * (N * V) := mul_le_mul_of_nonneg_left hii hη'
  have e4 : η * (G * P) ≤ η * (N * V) := mul_le_mul_of_nonneg_left hi hη
  have hlhs : t * (r * T * (P + 1 + W * (G + η'))) + W * η' * P + η * (G * P) =
      t * (r * T * (P + 1 + W * G)) + η' * (t * (r * T * W)) + η' * (W * P) + η * (G * P) := by
    ring
  rw [hlhs]
  nlinarith [e1, e2, e3, e4]

/-! ### The moment bound -/

/-- **(MOM)** The empirical moments of the rounded sample along a direction `v` with
`vᵀ cov v ≤ 1` are close to those of the mixture: for labels `ℓ`, noise `ν` (true points
`y_j = μ_{ℓ_j} + ν_j`) and rounded points `ỹ_j` with `(ỹ_j - y_j)ᵀ Σ⁻¹ (ỹ_j - y_j) ≤ 1/n²`, if
the cluster fractions are within `1 ± η` of the weights and the noise has the Gaussian moments up
to `η'` in uniform form up to degree `D ≥ 2r`, then
`|(1/n) ∑_j ⟨ỹ_j - μ̄, v⟩^r - ∑_c w_c hmom r ⟨μ_c - μ̄, v⟩ (vᵀΣv)| ≤ (η + η' + 1/n) K_r`
with `K_r = (4 (r + 1))^(2 (r + 1)) / wmin^(r + 1)`. -/
theorem moment_close (M : Mixture k d) (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c) (hn : 0 < n) (ℓ : Fin n → Fin k) (ν yt : Fin n → Fin d → ℝ)
    (hyt : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2) {η η' : ℝ}
    (hsize : ∀ c, |((cluster ℓ c).card : ℝ) / n - M.w c| ≤ η * M.w c) {D : ℕ}
    (hU : UniformNoise M.S η' D ℓ ν) {v : Fin d → ℝ} (hv : v ⬝ᵥ (M.cov *ᵥ v) ≤ 1) {r : ℕ}
    (hr : 2 * r ≤ D) :
    |(∑ j, ((yt j - M.mean) ⬝ᵥ v) ^ r) / n -
        ∑ c, M.w c * hmom r ((M.μ c - M.mean) ⬝ᵥ v) (v ⬝ᵥ (M.S *ᵥ v))| ≤
      (η + η' + 1 / n) * momConst r wmin := by
  obtain ⟨a, ha_def⟩ : ∃ a : Fin k → ℝ, ∀ c, a c = (M.μ c - M.mean) ⬝ᵥ v := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨X, hX_def⟩ : ∃ X : Fin n → ℝ, ∀ j, X j = ν j ⬝ᵥ v := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨e, he_def⟩ : ∃ e : Fin n → ℝ, ∀ j, e j = (yt j - (M.μ (ℓ j) + ν j)) ⬝ᵥ v :=
    ⟨_, fun _ ↦ rfl⟩
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = v ⬝ᵥ (M.S *ᵥ v) := ⟨_, rfl⟩
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = 1 / wmin := ⟨_, rfl⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hwpos : ∀ c, 0 < M.w c := fun c ↦ hwmin.trans_le (hw c)
  have hk0 : 0 < k := Nat.pos_of_ne_zero <| by
    rintro rfl
    have := hM.sum_w
    simp at this
  have hη : 0 ≤ η := by
    have h := (abs_nonneg _).trans (hsize ⟨0, hk0⟩)
    by_contra hneg
    linarith [mul_neg_of_neg_of_pos (not_le.mp hneg) (hwpos ⟨0, hk0⟩)]
  have hη' : 0 ≤ η' := by
    have h := (abs_nonneg _).trans (hU ⟨0, hk0⟩ 0 (Nat.zero_le _) v)
    rwa [pow_zero, mul_one] at h
  -- the scales
  have hq0 : 0 ≤ q := hq_def ▸ quad_S_nonneg hM v
  have hcov : v ⬝ᵥ (M.cov *ᵥ v) = q + ∑ c, M.w c * a c ^ 2 := by
    rw [quad_cov, hq_def]
    simp only [ha_def]
  have hsq : ∀ c, 0 ≤ M.w c * a c ^ 2 := fun c ↦ mul_nonneg (hwpos c).le (sq_nonneg _)
  have hq1 : q ≤ 1 := by linarith [sum_nonneg fun c (_ : c ∈ univ) ↦ hsq c]
  have hk : (k : ℝ) * wmin ≤ 1 := by
    have := sum_le_sum fun c (_ : c ∈ univ) ↦ hw c
    simpa [hM.sum_w] using this
  have hwmin1 : wmin ≤ 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  have hW1 : 1 ≤ W := by rw [hW_def, le_div_iff₀ hwmin]; linarith
  have hkW : (k : ℝ) ≤ W := by rw [hW_def, le_div_iff₀ hwmin]; exact hk
  have ha : ∀ c, |a c| ≤ W := by
    intro c
    have h1 : M.w c * a c ^ 2 ≤ 1 := by
      have := single_le_sum (fun c (_ : c ∈ univ) ↦ hsq c) (mem_univ c)
      linarith
    have h2 : wmin * a c ^ 2 ≤ 1 := (mul_le_mul_of_nonneg_right (hw c) (sq_nonneg _)).trans h1
    have h3 : a c ^ 2 ≤ W := by
      rw [hW_def, le_div_iff₀ hwmin]
      linarith
    by_contra h
    nlinarith [sq_abs (a c), abs_nonneg (a c), not_le.mp h]
  have he : ∀ j, |e j| ≤ 1 / n := by
    intro j
    rw [he_def]
    refine (abs_dotProduct_le_of_sqNormIn hM.posDef hn (hyt j)).trans ?_
    rw [← hq_def]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_one.mpr hq1) hn'.le
  -- rewrite the goal in terms of `a`, `X`, `e`, `q`
  have hdec : ∀ j, (yt j - M.mean) ⬝ᵥ v = (a (ℓ j) + X j) + e j := by
    intro j
    rw [ha_def, hX_def, he_def,
      show yt j - M.mean = (yt j - (M.μ (ℓ j) + ν j)) + (M.μ (ℓ j) - M.mean) + ν j by abel]
    simp only [add_dotProduct]
    ring
  simp_rw [hdec, ← ha_def, ← hq_def]
  -- the hmom bound
  have hh : ∀ c, |hmom r (a c) q| ≤ (2 * r)! * (W + 1) ^ r := by
    intro c
    have := abs_hmom_le (r := r) (ha c) (Real.sqrt_nonneg q) (Real.sqrt_le_one.mpr hq1)
    rwa [Real.sq_sqrt hq0] at this
  -- the decomposition
  have hsplit : (∑ j, (a (ℓ j) + X j) ^ r) / n =
      ∑ c, (∑ j ∈ cluster ℓ c, (a c + X j) ^ r) / n := by
    rw [← sum_fiberwise univ ℓ (fun j ↦ (a (ℓ j) + X j) ^ r), sum_div]
    refine sum_congr rfl fun c _ ↦ ?_
    congr 1
    refine sum_congr rfl fun j hj ↦ ?_
    rw [(mem_filter.mp hj).2]
  have hid : (∑ j, (a (ℓ j) + X j + e j) ^ r) / n - ∑ c, M.w c * hmom r (a c) q =
      (∑ j, ((a (ℓ j) + X j + e j) ^ r - (a (ℓ j) + X j) ^ r)) / n +
        ∑ c, ((∑ j ∈ cluster ℓ c, (a c + X j) ^ r) / n -
          ((cluster ℓ c).card : ℝ) / n * hmom r (a c) q) +
        ∑ c, (((cluster ℓ c).card : ℝ) / n - M.w c) * hmom r (a c) q := by
    rw [sum_sub_distrib, sub_div, hsplit, sum_sub_distrib]
    simp only [sub_mul, sum_sub_distrib]
    ring
  rw [hid]
  refine (abs_add_three _ _ _).trans ?_
  -- the perturbation
  have hA : |(∑ j, ((a (ℓ j) + X j + e j) ^ r - (a (ℓ j) + X j) ^ r)) / n| ≤
      1 / n * (r * 2 ^ r * ((W + 1) ^ r + 1 + W * ((2 * r)! + η'))) := by
    have hpt : ∀ j, |(a (ℓ j) + X j + e j) ^ r - (a (ℓ j) + X j) ^ r| ≤
        1 / n * (r * 2 ^ r * ((W + 1) ^ r + 1 + X j ^ (2 * r))) := fun j ↦
      abs_add_pow_sub_pow_le hn (he j) ((abs_add_le _ _).trans (by linarith [ha (ℓ j)])) hW1
    have hX2 : (∑ j, X j ^ (2 * r)) / n ≤ W * ((2 * r)! + η') := by
      rw [← sum_fiberwise univ ℓ (fun j ↦ X j ^ (2 * r)), sum_div]
      calc ∑ c, (∑ j ∈ univ with ℓ j = c, X j ^ (2 * r)) / n
          ≤ ∑ _c : Fin k, (((2 * r)! : ℝ) + η') := by
            refine sum_le_sum fun c _ ↦ ?_
            simp only [hX_def]
            exact cluster_even_moment_le hU hη' c hr (hq_def ▸ hq1)
        _ = k * ((2 * r)! + η') := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ W * ((2 * r)! + η') := by gcongr
    rw [abs_div, abs_of_pos hn']
    refine div_le_of_le_mul₀ hn'.le (by positivity) ?_
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ ↦ hpt j).trans ?_)
    have hsum : ∑ j, 1 / (n : ℝ) * (r * 2 ^ r * ((W + 1) ^ r + 1 + X j ^ (2 * r))) =
        1 / n * (r * 2 ^ r * (n * ((W + 1) ^ r + 1) + n * ((∑ j, X j ^ (2 * r)) / n))) := by
      rw [← mul_sum, ← mul_sum, sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_div_cancel₀ _ hn'.ne']
    rw [hsum]
    have : 0 ≤ (r : ℝ) * 2 ^ r := by positivity
    calc 1 / (n : ℝ) * (r * 2 ^ r * (n * ((W + 1) ^ r + 1) + n * ((∑ j, X j ^ (2 * r)) / n)))
        ≤ 1 / n * (r * 2 ^ r * (n * ((W + 1) ^ r + 1) + n * (W * ((2 * r)! + η')))) := by
          gcongr
      _ = _ := by field_simp
  -- the noise moments
  have hB : |∑ c, ((∑ j ∈ cluster ℓ c, (a c + X j) ^ r) / n -
      ((cluster ℓ c).card : ℝ) / n * hmom r (a c) q)| ≤ W * η' * (W + 1) ^ r := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c, |(∑ j ∈ cluster ℓ c, (a c + X j) ^ r) / n -
          ((cluster ℓ c).card : ℝ) / n * hmom r (a c) q|
        ≤ ∑ _c : Fin k, η' * (W + 1) ^ r := by
          refine sum_le_sum fun c _ ↦ ?_
          simp only [hX_def, hq_def]
          exact cluster_moment_close hU hη' c (by omega) (hq_def ▸ hq0) (hq_def ▸ hq1) (ha c)
      _ = k * (η' * (W + 1) ^ r) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ W * (η' * (W + 1) ^ r) := by gcongr
      _ = _ := by ring
  -- the cluster sizes
  have hC : |∑ c, (((cluster ℓ c).card : ℝ) / n - M.w c) * hmom r (a c) q| ≤
      η * ((2 * r)! * (W + 1) ^ r) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c, |(((cluster ℓ c).card : ℝ) / n - M.w c) * hmom r (a c) q|
        ≤ ∑ c, η * M.w c * ((2 * r)! * (W + 1) ^ r) := by
          refine sum_le_sum fun c _ ↦ ?_
          rw [abs_mul]
          exact mul_le_mul (hsize c) (hh c) (abs_nonneg _) (mul_nonneg hη (hwpos c).le)
      _ = η * ((2 * r)! * (W + 1) ^ r) := by
          rw [← sum_mul, ← mul_sum, hM.sum_w, mul_one]
  have hnum := moment_numerics (r := r) hη hη' (by positivity : (0 : ℝ) ≤ 1 / n)
    (div_le_one_of_le₀ (by exact_mod_cast hn) hn'.le) hW1
  have hK : momConst r wmin = (4 * ((r : ℝ) + 1)) ^ (2 * (r + 1)) * W ^ (r + 1) := by
    rw [momConst, hW_def, _root_.one_div_pow, mul_one_div]
  rw [hK]
  linarith

/-- **(MOM)**, homogeneous form: for every direction `v`, the error of `BS23.Colinear.moment_close`
is multiplied by `(vᵀ cov v)^(r/2)`. -/
theorem moment_close_homog (M : Mixture k d) (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c) (hn : 0 < n) (ℓ : Fin n → Fin k) (ν yt : Fin n → Fin d → ℝ)
    (hyt : ∀ j, sqNormIn M.S (yt j - (M.μ (ℓ j) + ν j)) ≤ 1 / n ^ 2) {η η' : ℝ}
    (hsize : ∀ c, |((cluster ℓ c).card : ℝ) / n - M.w c| ≤ η * M.w c) {D : ℕ}
    (hU : UniformNoise M.S η' D ℓ ν) (v : Fin d → ℝ) {r : ℕ} (hr : 2 * r ≤ D) :
    |(∑ j, ((yt j - M.mean) ⬝ᵥ v) ^ r) / n -
        ∑ c, M.w c * hmom r ((M.μ c - M.mean) ⬝ᵥ v) (v ⬝ᵥ (M.S *ᵥ v))| ≤
      (η + η' + 1 / n) * momConst r wmin * Real.sqrt (v ⬝ᵥ (M.cov *ᵥ v)) ^ r := by
  have hSC := quad_S_le_quad_cov M (fun c ↦ hwmin.le.trans (hw c)) v
  have hS0 := quad_S_nonneg hM v
  have hC0 : 0 ≤ v ⬝ᵥ (M.cov *ᵥ v) := hS0.trans hSC
  rcases (Real.sqrt_nonneg (v ⬝ᵥ (M.cov *ᵥ v))).eq_or_lt with ht | ht
  · -- `vᵀ cov v = 0`, so `v = 0`
    have hC : v ⬝ᵥ (M.cov *ᵥ v) ≤ 0 := Real.sqrt_eq_zero'.mp ht.symm
    have hv0 : v = 0 := by
      by_contra hv
      have := hM.posDef.dotProduct_mulVec_pos hv
      simp only [star_trivial] at this
      linarith
    subst hv0
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · rw [pow_zero, mul_one]
      exact moment_close M hM hwmin hw hn ℓ ν yt hyt hsize hU (by simp) hr
    · simp [zero_pow hr0.ne', hmom_zero_zero hr0]
  · set t := Real.sqrt (v ⬝ᵥ (M.cov *ᵥ v)) with ht_def
    have ht2 : t ^ 2 = v ⬝ᵥ (M.cov *ᵥ v) := Real.sq_sqrt hC0
    have hv' : (t⁻¹ • v) ⬝ᵥ (M.cov *ᵥ (t⁻¹ • v)) ≤ 1 := by
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← ht2]
      field_simp
      rfl
    have h := moment_close M hM hwmin hw hn ℓ ν yt hyt hsize hU hv' hr
    have e2 : (t⁻¹ • v) ⬝ᵥ (M.S *ᵥ (t⁻¹ • v)) = t⁻¹ ^ 2 * (v ⬝ᵥ (M.S *ᵥ v)) := by
      rw [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
      ring
    rw [e2] at h
    simp only [dotProduct_smul, smul_eq_mul, mul_pow, hmom_mul] at h
    simp_rw [mul_left_comm (M.w _) (t⁻¹ ^ r)] at h
    rw [← mul_sum, ← mul_sum, mul_div_assoc, ← mul_sub, abs_mul,
      abs_of_pos (pow_pos (inv_pos.mpr ht) r), inv_pow, ← div_eq_inv_mul,
      div_le_iff₀ (pow_pos ht r)] at h
    exact h

end BS23.Colinear
