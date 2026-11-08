module

public import BS23.Colinear.HermiteScore
public import BS23.Common.Mismatch

/-!
# The population Hermite score of a mixture with colinear means

The population side of the analysis of the colinear-means algorithm [BS23, Theorem 1.2].

* **Population moments** (any mixture). `BS23.Colinear.popMom M r v = ∑_c w_c hmom r ⟨μ_c - μ̄, v⟩
  (vᵀΣv)` is the `r`-th moment of `⟨y - μ̄, v⟩` for `y` drawn from the mixture (the quantity that
  `BS23.Colinear.moment_close` compares the empirical moments with). It has `popMom 0 = 1`,
  `popMom 1 = 0` and `popMom 2 = vᵀ cov v` (`BS23.Colinear.popMom_zero`, `popMom_one`,
  `popMom_two`), so the Hermite score `F_m` evaluated at it is
  `∑_c w_c He_m(⟨μ_c - μ̄, v⟩; vᵀ(cov - Σ)v)` (`BS23.Colinear.Fm_popMom`, by the heat identity), and
  it is bounded: `|popMom r v| ≤ (2 (m + 1) / wmin)^r` for `r ≤ m` when `vᵀ cov v ≤ 1`
  (`BS23.Colinear.abs_popMom_le`).
* **Colinear means** `μ_c = base + t_c u₀`. With `t̄ = ∑_c w_c t_c` (`BS23.Colinear.tbar`) and
  `τ² = ∑_c w_c (t_c - t̄)²` (`BS23.Colinear.tau2`): `μ̄ = base + t̄ u₀`, `μ_c - μ̄ = (t_c - t̄) u₀`
  and `cov = Σ + τ² u₀u₀ᵀ` (`BS23.Colinear.cov_eq`). With `q₀ = u₀ᵀΣ⁻¹u₀` and `κ = u₀ᵀ cov⁻¹ u₀`,
  Sherman–Morrison gives `cov⁻¹u₀ = (1 + τ² q₀)⁻¹ Σ⁻¹u₀`, so `κ = q₀ / (1 + τ² q₀)` and
  `σ² = κ / q₀ = 1 / (1 + τ² q₀) = 1 - τ² κ` (`BS23.Colinear.sigmaSq_eq_inv`,
  `BS23.Colinear.sigmaSq_eq_one_sub`).
* **The population score.** `F_m(popMom · v) = h̃_m ⟨u₀, v⟩^m` with
  `h̃_m = ∑_c w_c He_m(t_c - t̄; τ²)` (`BS23.Colinear.hpop`, `BS23.Colinear.Fm_popMom_eq_hpop`);
  `h̃_1 = h̃_2 = 0`.
* **Mismatch.** Under the separation `C log (1/wmin) ≤ (μ_a - μ_b)ᵀΣ⁻¹(μ_a - μ_b)` (`C ≥ 3`,
  `k ≥ 2`), `s² = τ² κ` lies in `[wmin/2, 1)` (`BS23.Colinear.wmin_half_le_s2`,
  `BS23.Colinear.s2_lt_one`), and for `T ≥ 10`, `T ≥ 10 log (1/wmin)` some degree `3 ≤ m ≤ 4T` has
  `|h̃_m| κ^{m/2} ≥ s^{4T} / (4 · 16^T)` (`BS23.Colinear.exists_hpop_mismatch`), by the
  one-dimensional mismatch lemma applied to `V_c = (t_c - t̄) √κ` (mean `0`, variance `s²`), since
  `κ^{m/2} h̃_m = ∑_c w_c He_m(V_c; s²)`.
-/

@[expose] public section

namespace BS23.Colinear

open Matrix Finset

variable {k d : ℕ}

/-! ### Generalities -/

private theorem quad_cov_eq (M : Mixture k d) (v : Fin d → ℝ) :
    v ⬝ᵥ (M.cov *ᵥ v) = v ⬝ᵥ (M.S *ᵥ v) + ∑ c, M.w c * ((M.μ c - M.mean) ⬝ᵥ v) ^ 2 := by
  rw [Mixture.cov, add_mulVec, dotProduct_add, sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [smul_mulVec, vecMulVec_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul,
    op_smul_eq_smul, smul_eq_mul, dotProduct_comm v]
  ring

private theorem quad_S_nonneg' {M : Mixture k d} (hM : M.Valid) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (M.S *ᵥ v) := by
  simpa using hM.posDef.posSemidef.dotProduct_mulVec_nonneg v

private theorem inv_quad_nonneg' {M : Mixture k d} (hM : M.Valid) (u : Fin d → ℝ) :
    0 ≤ u ⬝ᵥ (M.S⁻¹ *ᵥ u) := by
  simpa using hM.posDef.inv.posSemidef.dotProduct_mulVec_nonneg u

/-- The weights of a valid mixture with weights at least `wmin` are at most `1`, so `wmin ≤ 1`. -/
theorem wmin_le_one {M : Mixture k d} (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c) : wmin ≤ 1 := by
  have hk : (univ : Finset (Fin k)).Nonempty := by
    rw [univ_nonempty_iff]
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := hM.sum_w
    simp at this
  obtain ⟨c, -⟩ := hk
  calc wmin ≤ M.w c := hw c
    _ ≤ ∑ c, M.w c := single_le_sum (fun c _ ↦ hwmin.le.trans (hw c)) (mem_univ c)
    _ = 1 := hM.sum_w

/-- With at least two components, `2 wmin ≤ 1`. -/
theorem two_mul_wmin_le_one {M : Mixture k d} (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c) (hk : 2 ≤ k) : 2 * wmin ≤ 1 := by
  set a : Fin k := ⟨0, by omega⟩
  set b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hsub : ({a, b} : Finset (Fin k)) ⊆ univ := subset_univ _
  have h := sum_le_sum_of_subset_of_nonneg hsub (f := M.w)
    (fun c _ _ ↦ hwmin.le.trans (hw c))
  rw [sum_pair hab, hM.sum_w] at h
  linarith [hw a, hw b]

/-! ### Population moments of any mixture -/

/-- The **population moments** along `v`: `∑_c w_c hmom r ⟨μ_c - μ̄, v⟩ (vᵀΣv)`, the `r`-th moment
of `⟨y - μ̄, v⟩` for `y` drawn from the mixture. -/
noncomputable def popMom (M : Mixture k d) (r : ℕ) (v : Fin d → ℝ) : ℝ :=
  ∑ c, M.w c * hmom r ((M.μ c - M.mean) ⬝ᵥ v) (v ⬝ᵥ (M.S *ᵥ v))

/-- The centered means average to `0`: `∑_c w_c (μ_c - μ̄) = 0`. -/
theorem sum_w_smul_center (M : Mixture k d) (hM : M.Valid) :
    ∑ c, M.w c • (M.μ c - M.mean) = 0 := by
  simp only [smul_sub, sum_sub_distrib, ← sum_smul, hM.sum_w, one_smul]
  rw [Mixture.mean, sub_self]

theorem sum_w_mul_center_dotProduct (M : Mixture k d) (hM : M.Valid) (v : Fin d → ℝ) :
    ∑ c, M.w c * ((M.μ c - M.mean) ⬝ᵥ v) = 0 := by
  have h := congrArg (· ⬝ᵥ v) (sum_w_smul_center M hM)
  simpa [sum_dotProduct, smul_dotProduct] using h

theorem popMom_zero (M : Mixture k d) (hM : M.Valid) (v : Fin d → ℝ) : popMom M 0 v = 1 := by
  simp [popMom, hM.sum_w]

theorem popMom_one (M : Mixture k d) (hM : M.Valid) (v : Fin d → ℝ) : popMom M 1 v = 0 := by
  simpa [popMom] using sum_w_mul_center_dotProduct M hM v

theorem popMom_two (M : Mixture k d) (hM : M.Valid) (v : Fin d → ℝ) :
    popMom M 2 v = v ⬝ᵥ (M.cov *ᵥ v) := by
  simp only [popMom, hmom_two, mul_add, sum_add_distrib, ← sum_mul, hM.sum_w, one_mul]
  rw [quad_cov_eq]
  ring

/-- The Hermite score at the population moments: by the heat identity,
`F_m(popMom · v) = ∑_c w_c He_m(⟨μ_c - μ̄, v⟩; vᵀ cov v - vᵀΣv)`. -/
theorem Fm_popMom (M : Mixture k d) (hM : M.Valid) (m : ℕ) (v : Fin d → ℝ) :
    Fm m (fun r ↦ popMom M r v) = ∑ c, M.w c *
      hermite m ((M.μ c - M.mean) ⬝ᵥ v) (v ⬝ᵥ (M.cov *ᵥ v) - v ⬝ᵥ (M.S *ᵥ v)) := by
  rw [Fm_of_center m _ (v ⬝ᵥ (M.cov *ᵥ v)) (popMom_one M hM v) (popMom_two M hM v)]
  simp only [popMom, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [← sum_hmom_eq_hermite, mul_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  ring

/-- `|hmom r a s| ≤ (2 (r + 1) W)^r` for `|a| ≤ W`, `W ≥ 1` and `0 ≤ s ≤ 1`. -/
theorem abs_hmom_le_pow (r : ℕ) {a s W : ℝ} (ha : |a| ≤ W) (hW : 1 ≤ W) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : |hmom r a s| ≤ (2 * (r + 1) * W) ^ r := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hterm : ∀ i ∈ range (r / 2 + 1),
      |(hermCoeff r i : ℝ) * a ^ (r - 2 * i) * s ^ i| ≤ ((r : ℝ) + 1) ^ r * W ^ r := by
    intro i hi
    have hi' : 2 * i ≤ r := by have := mem_range.mp hi; omega
    rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow, abs_pow, abs_of_nonneg hs0]
    have h1 : (hermCoeff r i : ℝ) ≤ ((r : ℝ) + 1) ^ r := by
      exact_mod_cast hermCoeff_le_pow hi'
    have h2 : |a| ^ (r - 2 * i) ≤ W ^ r :=
      (pow_le_pow_left₀ (abs_nonneg a) ha _).trans (pow_le_pow_right₀ hW (Nat.sub_le _ _))
    have h3 : s ^ i ≤ 1 := pow_le_one₀ hs0 hs1
    calc (hermCoeff r i : ℝ) * |a| ^ (r - 2 * i) * s ^ i
        ≤ ((r : ℝ) + 1) ^ r * W ^ r * 1 := by gcongr
      _ = _ := mul_one _
  have hcard : ((r / 2 + 1 : ℕ) : ℝ) ≤ 2 ^ r := by
    have : r / 2 + 1 ≤ 2 ^ r := by
      have := Nat.lt_two_pow_self (n := r)
      omega
    exact_mod_cast this
  calc |hmom r a s| ≤ ∑ i ∈ range (r / 2 + 1), |(hermCoeff r i : ℝ) * a ^ (r - 2 * i) * s ^ i| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (r / 2 + 1), ((r : ℝ) + 1) ^ r * W ^ r := sum_le_sum hterm
    _ = ((r / 2 + 1 : ℕ) : ℝ) * (((r : ℝ) + 1) ^ r * W ^ r) := by
        rw [sum_const, card_range, nsmul_eq_mul]
    _ ≤ 2 ^ r * (((r : ℝ) + 1) ^ r * W ^ r) := by gcongr
    _ = (2 * (r + 1) * W) ^ r := by rw [mul_pow, mul_pow]; ring

/-- `1 ≤ 2 (m + 1) / wmin` for `0 < wmin ≤ 1`. -/
theorem one_le_popK {wmin : ℝ} (hwmin : 0 < wmin) (hw1 : wmin ≤ 1) (m : ℕ) :
    1 ≤ 2 * ((m : ℝ) + 1) / wmin := by
  rw [le_div_iff₀ hwmin]
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- **Bounded population moments**: if `vᵀ cov v ≤ 1` and all weights are at least `wmin > 0`,
then `|popMom r v| ≤ (2 (m + 1) / wmin)^r` for `r ≤ m`. -/
theorem abs_popMom_le (M : Mixture k d) (hM : M.Valid) {wmin : ℝ} (hwmin : 0 < wmin)
    (hw : ∀ c, wmin ≤ M.w c) {v : Fin d → ℝ} (hv : v ⬝ᵥ (M.cov *ᵥ v) ≤ 1) {m r : ℕ}
    (hr : r ≤ m) : |popMom M r v| ≤ (2 * ((m : ℝ) + 1) / wmin) ^ r := by
  have hw0 : ∀ c, 0 ≤ M.w c := fun c ↦ hwmin.le.trans (hw c)
  have hw1 := wmin_le_one hM hwmin hw
  set W : ℝ := 1 / wmin with hW_def
  have hW1 : 1 ≤ W := by rw [hW_def, le_div_iff₀ hwmin]; linarith
  have hS0 := quad_S_nonneg' hM v
  have hsum0 : 0 ≤ ∑ c, M.w c * ((M.μ c - M.mean) ⬝ᵥ v) ^ 2 :=
    sum_nonneg fun c _ ↦ mul_nonneg (hw0 c) (sq_nonneg _)
  have hcov := quad_cov_eq M v
  have hS1 : v ⬝ᵥ (M.S *ᵥ v) ≤ 1 := by linarith
  have ha : ∀ c, |(M.μ c - M.mean) ⬝ᵥ v| ≤ W := by
    intro c
    set a := (M.μ c - M.mean) ⬝ᵥ v
    have h1 : M.w c * a ^ 2 ≤ 1 := by
      have := single_le_sum (fun c (_ : c ∈ univ) ↦ mul_nonneg (hw0 c)
        (sq_nonneg ((M.μ c - M.mean) ⬝ᵥ v))) (mem_univ c)
      linarith
    have h2 : a ^ 2 ≤ W ^ 2 := by
      rw [hW_def, div_pow, one_pow, le_div_iff₀ (by positivity)]
      have : wmin * a ^ 2 ≤ 1 := (mul_le_mul_of_nonneg_right (hw c) (sq_nonneg a)).trans h1
      nlinarith [sq_nonneg a]
    exact abs_le_of_sq_le_sq' h2 (zero_le_one.trans hW1) |> abs_le.mpr
  have hK : 2 * ((r : ℝ) + 1) * W ≤ 2 * ((m : ℝ) + 1) / wmin := by
    rw [hW_def, mul_one_div]
    gcongr
  calc |popMom M r v| ≤ ∑ c, |M.w c * hmom r ((M.μ c - M.mean) ⬝ᵥ v) (v ⬝ᵥ (M.S *ᵥ v))| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, M.w c * (2 * ((r : ℝ) + 1) * W) ^ r := by
        refine sum_le_sum fun c _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (hw0 c)]
        exact mul_le_mul_of_nonneg_left (abs_hmom_le_pow r (ha c) hW1 hS0 hS1) (hw0 c)
    _ = (2 * ((r : ℝ) + 1) * W) ^ r := by rw [← sum_mul, hM.sum_w, one_mul]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) hK r

/-! ### Colinear means -/

/-- The mean `t̄ = ∑_c w_c t_c` of the positions of the means on the line. -/
noncomputable def tbar (M : Mixture k d) (t : Fin k → ℝ) : ℝ := ∑ c, M.w c * t c

/-- The variance `τ² = ∑_c w_c (t_c - t̄)²` of the positions of the means on the line. -/
noncomputable def tau2 (M : Mixture k d) (t : Fin k → ℝ) : ℝ := ∑ c, M.w c * (t c - tbar M t) ^ 2

/-- The **population Hermite moment** `h̃_m = ∑_c w_c He_m(t_c - t̄; τ²)` on the line. -/
noncomputable def hpop (M : Mixture k d) (t : Fin k → ℝ) (m : ℕ) : ℝ :=
  ∑ c, M.w c * hermite m (t c - tbar M t) (tau2 M t)

variable {M : Mixture k d} {base u0 : Fin d → ℝ} {t : Fin k → ℝ} {wmin : ℝ}

theorem tau2_nonneg (hw : ∀ c, 0 ≤ M.w c) : 0 ≤ tau2 M t :=
  sum_nonneg fun c _ ↦ mul_nonneg (hw c) (sq_nonneg _)

/-- The mean of a mixture with colinear means: `μ̄ = base + t̄ u₀`. -/
theorem mixture_mean_eq (hM : M.Valid) (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.mean = base + tbar M t • u0 := by
  simp only [Mixture.mean, hμ, smul_add, sum_add_distrib, smul_smul, ← sum_smul, hM.sum_w,
    one_smul, tbar]

/-- The centered means: `μ_c - μ̄ = (t_c - t̄) u₀`. -/
theorem center_eq (hM : M.Valid) (hμ : ∀ c, M.μ c = base + t c • u0) (c : Fin k) :
    M.μ c - M.mean = (t c - tbar M t) • u0 := by
  rw [hμ c, mixture_mean_eq hM hμ, sub_smul]
  abel

/-- The covariance of a mixture with colinear means: `cov = Σ + τ² u₀u₀ᵀ`. -/
theorem cov_eq (hM : M.Valid) (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.cov = M.S + tau2 M t • vecMulVec u0 u0 := by
  rw [Mixture.cov, tau2, sum_smul]
  congr 1
  refine sum_congr rfl fun c _ ↦ ?_
  rw [center_eq hM hμ, smul_vecMulVec, vecMulVec_smul, smul_smul, smul_smul, sq, mul_assoc]

/-- The covariance of a mixture with nonnegative weights is positive definite. -/
theorem cov_posDef (M : Mixture k d) (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c) : M.cov.PosDef := by
  refine hM.posDef.add_posSemidef (posSemidef_sum _ fun c _ ↦ ?_)
  have h := posSemidef_vecMulVec_self_star (M.μ c - M.mean)
  rw [star_trivial] at h
  exact h.smul (hw c)

/-- `cov Σ⁻¹u₀ = (1 + τ² q₀) u₀` with `q₀ = u₀ᵀΣ⁻¹u₀`. -/
theorem cov_mulVec_S_inv (hM : M.Valid) (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.cov *ᵥ (M.S⁻¹ *ᵥ u0) = (1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0))) • u0 := by
  rw [cov_eq hM hμ, add_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul,
    mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hM.posDef.isUnit),
    one_mulVec, add_smul, one_smul]

/-- **Sherman–Morrison**: `cov⁻¹u₀ = (1 + τ² q₀)⁻¹ Σ⁻¹u₀` with `q₀ = u₀ᵀΣ⁻¹u₀`. -/
theorem cov_inv_mulVec (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c)
    (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.cov⁻¹ *ᵥ u0 = (1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)))⁻¹ • (M.S⁻¹ *ᵥ u0) := by
  have hc := cov_posDef M hM hw
  have h1 := cov_mulVec_S_inv hM hμ
  set c := 1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) with hc_def
  have hpos : 0 < c := by
    have := mul_nonneg (tau2_nonneg (t := t) hw) (inv_quad_nonneg' hM u0)
    linarith
  have h2 : M.S⁻¹ *ᵥ u0 = c • (M.cov⁻¹ *ᵥ u0) := by
    rw [← mulVec_smul, ← h1, mulVec_mulVec,
      nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hc.isUnit), one_mulVec]
  rw [h2, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]

/-- `κ = u₀ᵀ cov⁻¹ u₀ = q₀ / (1 + τ² q₀)` with `q₀ = u₀ᵀΣ⁻¹u₀`. -/
theorem kappa_eq (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c) (hμ : ∀ c, M.μ c = base + t c • u0) :
    u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0) =
      (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) / (1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0))) := by
  rw [cov_inv_mulVec hM hw hμ, dotProduct_smul, smul_eq_mul, div_eq_inv_mul]

/-- `σ² = κ / q₀ = 1 / (1 + τ² q₀)`. -/
theorem sigmaSq_eq_inv (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c) (hu0 : u0 ≠ 0)
    (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.sigmaSq u0 = 1 / (1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0))) := by
  have hq : 0 < u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0) := by
    simpa using hM.posDef.inv.dotProduct_mulVec_pos hu0
  have hpos : 0 < 1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) := by
    have := mul_nonneg (tau2_nonneg (t := t) hw) hq.le
    linarith
  rw [Mixture.sigmaSq, sqNormIn, sqNormIn, kappa_eq hM hw hμ]
  field_simp

/-- `σ² = 1 - τ² κ`. -/
theorem sigmaSq_eq_one_sub (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c) (hu0 : u0 ≠ 0)
    (hμ : ∀ c, M.μ c = base + t c • u0) :
    M.sigmaSq u0 = 1 - tau2 M t * (u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0)) := by
  have hpos : 0 < 1 + tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) := by
    have := mul_nonneg (tau2_nonneg (t := t) hw) (inv_quad_nonneg' hM u0)
    linarith
  rw [sigmaSq_eq_inv hM hw hu0 hμ, kappa_eq hM hw hμ]
  field_simp
  ring

/-! ### The population score -/

/-- **The population score** on the line: `F_m(popMom · v) = h̃_m ⟨u₀, v⟩^m`. -/
theorem Fm_popMom_eq_hpop (hM : M.Valid) (hμ : ∀ c, M.μ c = base + t c • u0) (m : ℕ)
    (v : Fin d → ℝ) : Fm m (fun r ↦ popMom M r v) = hpop M t m * (u0 ⬝ᵥ v) ^ m := by
  have hq : v ⬝ᵥ (M.cov *ᵥ v) - v ⬝ᵥ (M.S *ᵥ v) = (u0 ⬝ᵥ v) ^ 2 * tau2 M t := by
    rw [cov_eq hM hμ, add_mulVec, dotProduct_add, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
      dotProduct_smul, smul_eq_mul, dotProduct_smul, smul_eq_mul, dotProduct_comm v u0]
    ring
  rw [Fm_popMom M hM, hpop, sum_mul, hq]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [center_eq hM hμ, smul_dotProduct, smul_eq_mul, mul_comm (t c - tbar M t), hermite_mul]
  ring

theorem hpop_one (hM : M.Valid) : hpop M t 1 = 0 := by
  simp only [hpop, hermite_one, mul_sub, sum_sub_distrib, ← sum_mul, hM.sum_w, one_mul, tbar,
    sub_self]

theorem hpop_two (hM : M.Valid) : hpop M t 2 = 0 := by
  simp only [hpop, hermite_two, mul_sub, sum_sub_distrib, ← sum_mul, hM.sum_w, one_mul, tau2,
    sub_self]

/-! ### The mismatch -/

/-- The separation along the line: `(μ_a - μ_b)ᵀΣ⁻¹(μ_a - μ_b) = (t_a - t_b)² q₀`. -/
theorem sqNormIn_sub_eq (hμ : ∀ c, M.μ c = base + t c • u0) (a b : Fin k) :
    sqNormIn M.S (M.μ a - M.μ b) = (t a - t b) ^ 2 * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) := by
  have h : M.μ a - M.μ b = (t a - t b) • u0 := by
    rw [hμ a, hμ b, sub_smul]
    abel
  rw [sqNormIn, h, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-- Two atoms of weight at least `wmin` force `τ² ≥ (wmin/2) (t_a - t_b)²`. -/
theorem tau2_ge (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c) {a b : Fin k} (hab : a ≠ b) :
    wmin / 2 * (t a - t b) ^ 2 ≤ tau2 M t := by
  have hw0 : ∀ c, 0 ≤ M.w c := fun c ↦ hwmin.le.trans (hw c)
  have h := sum_le_sum_of_subset_of_nonneg (subset_univ ({a, b} : Finset (Fin k)))
    (f := fun c ↦ M.w c * (t c - tbar M t) ^ 2) (fun c _ _ ↦ mul_nonneg (hw0 c) (sq_nonneg _))
  rw [sum_pair hab] at h
  have ha := mul_le_mul_of_nonneg_right (hw a) (sq_nonneg (t a - tbar M t))
  have hb := mul_le_mul_of_nonneg_right (hw b) (sq_nonneg (t b - tbar M t))
  have hsq : (t a - t b) ^ 2 ≤ 2 * ((t a - tbar M t) ^ 2 + (t b - tbar M t) ^ 2) := by
    nlinarith [sq_nonneg (t a + t b - 2 * tbar M t)]
  rw [tau2]
  nlinarith

/-- `τ² q₀ ≥ wmin` under the separation `C log (1/wmin)` with `C ≥ 3` and `k ≥ 2`. -/
theorem wmin_le_tau2_mul (hM : M.Valid) (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c)
    (hμ : ∀ c, M.μ c = base + t c • u0) (hk : 2 ≤ k) {Csep : ℝ} (hC : 3 ≤ Csep)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) :
    wmin ≤ tau2 M t * (u0 ⬝ᵥ (M.S⁻¹ *ᵥ u0)) := by
  set a : Fin k := ⟨0, by omega⟩
  set b : Fin k := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hw2 := two_mul_wmin_le_one hM hwmin hw hk
  have hq0 := inv_quad_nonneg' hM u0
  have hlog : Real.log 2 ≤ Real.log (1 / wmin) :=
    Real.log_le_log two_pos (by rw [le_div_iff₀ hwmin]; linarith)
  have hl2 := Real.log_two_gt_d9
  have hCl : 2 ≤ Csep * Real.log (1 / wmin) := by nlinarith
  have hs := hsep a b hab
  rw [sqNormIn_sub_eq hμ] at hs
  have ht := mul_le_mul_of_nonneg_right (tau2_ge (t := t) hwmin hw hab) hq0
  nlinarith

/-- **`s² = τ² κ ≥ wmin / 2`** under the separation `C log (1/wmin)` with `C ≥ 3` and `k ≥ 2`. -/
theorem wmin_half_le_s2 (hM : M.Valid) (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c)
    (hμ : ∀ c, M.μ c = base + t c • u0) (hk : 2 ≤ k) {Csep : ℝ} (hC : 3 ≤ Csep)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b)) :
    wmin / 2 ≤ tau2 M t * (u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0)) := by
  have hw0 : ∀ c, 0 ≤ M.w c := fun c ↦ hwmin.le.trans (hw c)
  have hX := wmin_le_tau2_mul (t := t) hM hwmin hw hμ hk hC hsep
  have hw2 := two_mul_wmin_le_one hM hwmin hw hk
  rw [kappa_eq hM hw0 hμ, ← mul_div_assoc, le_div_iff₀ (by linarith)]
  nlinarith

/-- **`s² = τ² κ < 1`**. -/
theorem s2_lt_one (hM : M.Valid) (hw : ∀ c, 0 ≤ M.w c) (hμ : ∀ c, M.μ c = base + t c • u0) :
    tau2 M t * (u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0)) < 1 := by
  have hX := mul_nonneg (tau2_nonneg (t := t) hw) (inv_quad_nonneg' hM u0)
  rw [kappa_eq hM hw hμ, ← mul_div_assoc, div_lt_one (by linarith)]
  linarith

/-- **The population mismatch.** Under the separation `C log (1/wmin)` (`C ≥ 3`, `k ≥ 2`), for
`T ≥ 10` with `T ≥ 10 log (1/wmin)` there is a degree `3 ≤ m ≤ 4T` with
`(τ² κ)^{2T} / (4 · 16^T) ≤ |h̃_m| κ^{m/2}`. -/
theorem exists_hpop_mismatch (hM : M.Valid) (hwmin : 0 < wmin) (hw : ∀ c, wmin ≤ M.w c)
    (hμ : ∀ c, M.μ c = base + t c • u0) (hk : 2 ≤ k) {Csep : ℝ} (hC : 3 ≤ Csep)
    (hsep : ∀ a b, a ≠ b → Csep * Real.log (1 / wmin) ≤ sqNormIn M.S (M.μ a - M.μ b))
    {T : ℕ} (hT : 10 ≤ T) (hTw : 10 * Real.log (1 / wmin) ≤ T) :
    ∃ m, 3 ≤ m ∧ m ≤ 4 * T ∧
      (tau2 M t * (u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0))) ^ (2 * T) / (4 * 16 ^ T) ≤
        |hpop M t m| * Real.sqrt (u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0)) ^ m := by
  have hw0 : ∀ c, 0 ≤ M.w c := fun c ↦ hwmin.le.trans (hw c)
  set κ := u0 ⬝ᵥ (M.cov⁻¹ *ᵥ u0) with hκ
  set β := Real.sqrt κ with hβ
  have hκ0 : 0 ≤ κ := by
    simpa using (cov_posDef M hM hw0).inv.posSemidef.dotProduct_mulVec_nonneg u0
  have hβ2 : β ^ 2 = κ := Real.sq_sqrt hκ0
  set V : Fin k → ℝ := fun c ↦ β * (t c - tbar M t) with hV
  have hVs : ∑ c, M.w c * V c ^ 2 = tau2 M t * κ := by
    simp only [hV, mul_pow, hβ2, tau2, sum_mul]
    exact sum_congr rfl fun c _ ↦ by ring
  have hs0 := wmin_half_le_s2 (t := t) hM hwmin hw hμ hk hC hsep
  have hs1 := s2_lt_one (t := t) hM hw0 hμ
  obtain ⟨m, hm1, hm2, hbound⟩ := exists_hermite_mismatch M.w V hwmin hw hM.sum_w
    (by rw [hVs]; linarith) (by rw [hVs]; exact hs1.le) hT hTw
  rw [hVs] at hbound
  have hsum : ∑ c, M.w c * hermite m (V c) (tau2 M t * κ) = β ^ m * hpop M t m := by
    rw [hpop, mul_sum]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [hV, show tau2 M t * κ = β ^ 2 * tau2 M t by rw [hβ2, mul_comm], hermite_mul]
    ring
  rw [hsum, abs_mul, abs_pow, abs_of_nonneg (Real.sqrt_nonneg κ),
    mul_comm (Real.sqrt κ ^ m)] at hbound
  have hpos : 0 < (tau2 M t * κ) ^ (2 * T) / (4 * 16 ^ T) := by
    have : 0 < tau2 M t * κ := by linarith
    positivity
  refine ⟨m, ?_, hm2, hbound⟩
  by_contra hm3
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl
  · rw [hpop_one hM, abs_zero, zero_mul] at hbound
    linarith
  · rw [hpop_two hM, abs_zero, zero_mul] at hbound
    linarith

end BS23.Colinear
