module

public import BS23.Colinear.Direction
public import BS23.Colinear.Line
public import BS23.Common.HermiteFacts

/-!
# Selection and gradient: the selected pair gives a gradient along `u₀`

The steps (SEL) and (GRAD) of the analysis of the colinear-means algorithm [BS23, Section 6].
Suppose the empirical covariance `Ĉ` is within `1 ± ε_C` of `cov` (as quadratic forms), the
empirical Hermite moments are close to a rank-one form along `u₀`,
`|P̂_m(v) - h_m ⟨u₀, v⟩^m| ≤ ε_P ‖v‖_cov^m` for `3 ≤ m ≤ M`, and some degree `m₀` has a large
normalized coefficient `|h_{m₀}| κ^{m₀/2} ≥ η₀` (`κ = u₀ᵀ cov⁻¹ u₀`). Then the pair `(m, i)`
selected by the algorithm (`BS23.Colinear.selectBest`) has a gradient `∇P̂_m(λᵢ) = c u₀ + E`
with `c ≠ 0` and a small error `‖E‖_{cov⁻¹} ≤ |c| √κ σ / 16`
(`BS23.Colinear.exists_selectBest_gradPhat`), as needed by `BS23.Colinear.fisher_ratio`.

* **Homogeneity.** `P̂_m(c v) = c^m P̂_m(v)` (`BS23.Colinear.phat_smul`), so the score
  `P̂_m(v)² / (vᵀĈv)^m` is scale invariant (`BS23.Colinear.phat_sq_div_quad_smul`).
* **Gradient.** If `|P̂_m(v) - a ⟨u₀, v⟩^m| ≤ ε_P ‖v‖_cov^m` for all `v`, then
  `E = ∇P̂_m(v) - m a ⟨u₀, v⟩^(m-1) u₀` has
  `‖E‖_{cov⁻¹} ≤ (m+1)^(m+1) 2^m ε_P ‖v‖_cov^(m-1)` (`BS23.Colinear.inv_quad_gradPhat_sub_le`):
  along a line `t ↦ v + t θ` both functions are polynomials of degree at most `m`, so their
  derivatives at `0` are close (`BS23.Colinear.abs_gradPhat_sub_le`).
* **Selection.** Some basis vector `λ` of `Ĉ` has `⟨u₀, λ⟩² / λᵀĈλ ≥ κ / (d (1 + ε_C))`, so its
  score at the degree `m₀` is at least `(η₀ / (4 d^M))²`; the selected pair has at least this
  score, hence `|h_m| |⟨u₀, λ⟩|^m ≥ η₀ / (16 d^M) · ‖λ‖_cov^m`, which makes the main part `c u₀`
  of the gradient large compared to `E` (Cauchy–Schwarz: `|⟨u₀, λ⟩| ≤ √κ ‖λ‖_cov`).
-/

@[expose] public section

namespace BS23.Colinear

open Matrix

variable {n d : ℕ}

/-! ### Homogeneity -/

section Homogeneity

variable {K : Type*} [Field K]

/-- **Homogeneity** of the empirical Hermite moment: `P̂_m(c v) = c^m P̂_m(v)`. -/
theorem phat_smul (m : ℕ) (Y : Fin n → Fin d → K) (c : K) (v : Fin d → K) :
    phat m Y (c • v) = c ^ m * phat m Y v := by
  simp only [phat, dotProduct_smul, smul_eq_mul, quad_smul, hermite_mul, ← Finset.mul_sum,
    mul_div_assoc]

/-- The score `P̂_m(v)² / (vᵀĈv)^m` is scale invariant. -/
theorem phat_sq_div_quad_smul (m : ℕ) (Y : Fin n → Fin d → K) {c : K} (hc : c ≠ 0)
    (v : Fin d → K) :
    phat m Y (c • v) ^ 2 / quad (empCov Y) (c • v) ^ m =
      phat m Y v ^ 2 / quad (empCov Y) v ^ m := by
  rw [phat_smul, quad_smul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2,
    mul_div_mul_left _ _ (pow_ne_zero _ hc)]

/-- The score of a pair is the scale-free ratio at its basis vector. -/
theorem score_eq (Y : Fin n → Fin d → K) (m : ℕ) (i : Fin d) :
    score Y (m, i) =
      phat m Y (basisVec (empCov Y) i) ^ 2 / quad (empCov Y) (basisVec (empCov Y) i) ^ m :=
  rfl

end Homogeneity

/-! ### Elementary estimates -/

/-- For `0 ≤ ε ≤ 1/4` and `m ε ≤ 1/4`: `(1 + ε)^m ≤ 4` and `(1 - ε)⁻¹^m ≤ 4`. -/
theorem pow_one_add_le_four {ε : ℝ} {m : ℕ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (hmε : (m : ℝ) * ε ≤ 1 / 4) :
    (1 + ε) ^ m ≤ 4 ∧ (1 - ε)⁻¹ ^ m ≤ 4 := by
  have hb : 1 + m * (-ε) ≤ (1 + -ε) ^ m := one_add_mul_le_pow (by linarith) m
  rw [← sub_eq_add_neg] at hb
  have h34 : 3 / 4 ≤ (1 - ε) ^ m := by linarith
  have hpos : 0 < (1 - ε) ^ m := by linarith
  have hinv : ((1 - ε) ^ m)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith
  refine ⟨?_, by rwa [inv_pow]⟩
  have hprod : (1 + ε) ^ m * (1 - ε) ^ m ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  calc (1 + ε) ^ m ≤ ((1 - ε) ^ m)⁻¹ := by rw [← one_div, le_div_iff₀ hpos]; exact hprod
    _ ≤ 4 := hinv

/-- If `x ≤ c y` and `c^m ≤ 4` then `√x^m ≤ 2 √y^m`. -/
theorem sqrt_pow_le_two_mul {x y c : ℝ} {m : ℕ} (hy : 0 ≤ y)
    (hxy : x ≤ c * y) (hcm : c ^ m ≤ 4) :
    Real.sqrt x ^ m ≤ 2 * Real.sqrt y ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · norm_num
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [mul_pow, pow_right_comm (Real.sqrt x), pow_right_comm (Real.sqrt y), Real.sq_sqrt hy]
  rcases le_or_gt x 0 with hx | hx
  · rw [Real.sqrt_eq_zero'.mpr hx, zero_pow two_ne_zero, zero_pow (by omega)]
    positivity
  rw [Real.sq_sqrt hx.le]
  calc x ^ m ≤ (c * y) ^ m := pow_le_pow_left₀ hx.le hxy m
    _ = c ^ m * y ^ m := mul_pow c y m
    _ ≤ 4 * y ^ m := by gcongr
    _ = 2 ^ 2 * y ^ m := by norm_num

/-! ### The gradient from the values -/

/-- Along directions `θ` no longer than `v`: if `|P̂_m(w) - a ⟨u₀, w⟩^m| ≤ ε_P ‖w‖_cov^m` for all
`w`, then `|⟨∇P̂_m(v) - m a ⟨u₀, v⟩^(m-1) u₀, θ⟩| ≤ (m+1)^(m+1) 2^m ε_P ‖v‖_cov^m`. -/
theorem abs_gradPhat_sub_dotProduct_le {m : ℕ} (Y : Fin n → Fin d → ℝ)
    {cov : Matrix (Fin d) (Fin d) ℝ} (hcov : cov.PosDef) (u0 : Fin d → ℝ) (a : ℝ) {εP : ℝ}
    (hεP : 0 ≤ εP)
    (HP : ∀ w, |phat m Y w - a * (u0 ⬝ᵥ w) ^ m| ≤ εP * Real.sqrt (quad cov w) ^ m)
    (v θ : Fin d → ℝ) (hθ : qnorm cov θ ≤ qnorm cov v) :
    |(gradPhat m Y v - ((m : ℝ) * a * (u0 ⬝ᵥ v) ^ (m - 1)) • u0) ⬝ᵥ θ| ≤
      (m + 1) ^ (m + 1) * 2 ^ m * εP * qnorm cov v ^ m := by
  set N := qnorm cov v with hN
  have hF : ∃ P : Polynomial ℝ, P.natDegree ≤ m ∧
      ∀ t, P.eval t = (fun t : ℝ ↦ a * (u0 ⬝ᵥ (v + t • θ)) ^ m) t := by
    refine ⟨Polynomial.C a *
      (Polynomial.C (u0 ⬝ᵥ θ) * Polynomial.X + Polynomial.C (u0 ⬝ᵥ v)) ^ m, ?_, fun t ↦ ?_⟩
    · refine (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_pow_le_of_le m Polynomial.natDegree_linear_le).trans ?_)
      simp
    · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, dotProduct_line]
  have hD : HasDerivAt (fun t : ℝ ↦ a * (u0 ⬝ᵥ (v + t • θ)) ^ m)
      (a * ((m : ℝ) * (u0 ⬝ᵥ v) ^ (m - 1) * (u0 ⬝ᵥ θ))) 0 := by
    have hx : HasDerivAt (fun t : ℝ ↦ u0 ⬝ᵥ (v + t • θ)) (u0 ⬝ᵥ θ) 0 := by
      simp only [dotProduct_line]
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (u0 ⬝ᵥ θ)).add_const (u0 ⬝ᵥ v)
    simpa using (hx.fun_pow m).const_mul a
  have hB : ∀ j : ℕ, j ≤ m → |phat m Y (v + (j : ℝ) • θ) -
      (fun t : ℝ ↦ a * (u0 ⬝ᵥ (v + t • θ)) ^ m) j| ≤ εP * ((m + 1) * N) ^ m := by
    intro j hj
    have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
    have hlen : qnorm cov (v + (j : ℝ) • θ) ≤ (m + 1) * N := by
      calc qnorm cov (v + (j : ℝ) • θ) ≤ N + |(j : ℝ)| * qnorm cov θ := by
            rw [← qnorm_smul]; exact qnorm_add_le hcov _ _
        _ ≤ N + m * N := by
            rw [Nat.abs_cast]
            gcongr
            exact qnorm_nonneg cov θ
        _ = (m + 1) * N := by ring
    exact (HP _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (qnorm_nonneg _ _) hlen m) hεP)
  have key := abs_gradPhat_sub_le Y v θ hF hD hB
  rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  calc |gradPhat m Y v ⬝ᵥ θ - (m : ℝ) * a * (u0 ⬝ᵥ v) ^ (m - 1) * (u0 ⬝ᵥ θ)|
      = |gradPhat m Y v ⬝ᵥ θ - a * ((m : ℝ) * (u0 ⬝ᵥ v) ^ (m - 1) * (u0 ⬝ᵥ θ))| := by ring_nf
    _ ≤ (m + 1) * 2 ^ m * (εP * ((m + 1) * N) ^ m) := key
    _ = (m + 1) ^ (m + 1) * 2 ^ m * εP * N ^ m := by rw [mul_pow, pow_succ]; ring

/-- **The gradient is along `u₀`**: if `|P̂_m(w) - a ⟨u₀, w⟩^m| ≤ ε_P ‖w‖_cov^m` for all `w`, then
for `v ≠ 0` the error `E = ∇P̂_m(v) - m a ⟨u₀, v⟩^(m-1) u₀` has
`Eᵀ cov⁻¹ E ≤ ((m+1)^(m+1) 2^m ε_P ‖v‖_cov^(m-1))²`. -/
theorem inv_quad_gradPhat_sub_le {m : ℕ} (hm : 1 ≤ m) (Y : Fin n → Fin d → ℝ)
    {cov : Matrix (Fin d) (Fin d) ℝ} (hcov : cov.PosDef) (u0 : Fin d → ℝ) (a : ℝ) {εP : ℝ}
    (hεP : 0 ≤ εP)
    (HP : ∀ w, |phat m Y w - a * (u0 ⬝ᵥ w) ^ m| ≤ εP * Real.sqrt (quad cov w) ^ m)
    {v : Fin d → ℝ} (hv : v ≠ 0) :
    (gradPhat m Y v - ((m : ℝ) * a * (u0 ⬝ᵥ v) ^ (m - 1)) • u0) ⬝ᵥ
        (cov⁻¹ *ᵥ (gradPhat m Y v - ((m : ℝ) * a * (u0 ⬝ᵥ v) ^ (m - 1)) • u0)) ≤
      ((m + 1) ^ (m + 1) * 2 ^ m * εP * qnorm cov v ^ (m - 1)) ^ 2 := by
  set E := gradPhat m Y v - ((m : ℝ) * a * (u0 ⬝ᵥ v) ^ (m - 1)) • u0 with hE
  set N := qnorm cov v with hN
  set B₀ : ℝ := (m + 1) ^ (m + 1) * 2 ^ m * εP with hB₀
  have hB₀0 : 0 ≤ B₀ := by positivity
  have hNpos : 0 < N := Real.sqrt_pos.mpr (quad_pos hcov hv)
  have hNm : N ^ m = N ^ (m - 1) * N := by rw [← pow_succ, Nat.sub_add_cancel hm]
  refine inv_quad_le_sq_of_abs_le hcov fun θ ↦ ?_
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp only [dotProduct_zero, abs_zero]
    positivity
  set Nθ := qnorm cov θ with hNθ
  have hNθpos : 0 < Nθ := Real.sqrt_pos.mpr (quad_pos hcov hθ)
  set s := N / Nθ with hs
  have hspos : 0 < s := div_pos hNpos hNθpos
  have h1 := abs_gradPhat_sub_dotProduct_le Y hcov u0 a hεP HP v (s • θ) (by
    rw [qnorm_smul, abs_of_pos hspos, hs, div_mul_cancel₀ _ hNθpos.ne'])
  rw [← hE, dotProduct_smul, smul_eq_mul, abs_mul, abs_of_pos hspos, ← hB₀] at h1
  change |E ⬝ᵥ θ| ≤ B₀ * N ^ (m - 1) * Nθ
  calc |E ⬝ᵥ θ| = s * |E ⬝ᵥ θ| * (Nθ / N) := by
        rw [hs]; field_simp
    _ ≤ B₀ * N ^ m * (Nθ / N) := by gcongr
    _ = B₀ * N ^ (m - 1) * Nθ := by rw [hNm]; field_simp

/-! ### Selection -/

/-- The score bound at a basis vector aligned with `u₀`, in scalar form: if
`κ q ≤ L X²`, `L^m ≤ (2D)²`, `η₀ ≤ |a| √κ^m`, `|a| X^m - ε_P N^m ≤ |P|`, `N^m ≤ 2 √q^m` and
`8 ε_P D ≤ η₀`, then `η₀ √q^m ≤ 4 D |P|`. -/
theorem score_aux {m : ℕ} {κ q X L D a N P η₀ εP : ℝ} (hκ : 0 ≤ κ) (hq : 0 ≤ q) (hX : 0 ≤ X)
    (hD : 0 < D) (hεP : 0 ≤ εP) (halign : κ * q ≤ L * X ^ 2)
    (hLm : L ^ m ≤ (2 * D) ^ 2) (hη : η₀ ≤ |a| * Real.sqrt κ ^ m)
    (hP : |a| * X ^ m - εP * N ^ m ≤ |P|) (hN : N ^ m ≤ 2 * Real.sqrt q ^ m)
    (hsmall : 8 * εP * D ≤ η₀) :
    η₀ * Real.sqrt q ^ m ≤ 4 * D * |P| := by
  set S := Real.sqrt κ ^ m * Real.sqrt q ^ m with hS
  have hS0 : 0 ≤ S := by positivity
  have hSsq : S ^ 2 = (κ * q) ^ m := by
    rw [hS, mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2, pow_mul, pow_mul, Real.sq_sqrt hκ,
      Real.sq_sqrt hq, mul_pow]
  have h1 : S ≤ 2 * D * X ^ m := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [hSsq]
    calc (κ * q) ^ m ≤ (L * X ^ 2) ^ m := pow_le_pow_left₀ (by positivity) halign m
      _ = L ^ m * (X ^ m) ^ 2 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 m]
      _ ≤ (2 * D) ^ 2 * (X ^ m) ^ 2 := by gcongr
      _ = (2 * D * X ^ m) ^ 2 := by ring
  have hQ0 : 0 ≤ Real.sqrt q ^ m := by positivity
  have h2 : η₀ * Real.sqrt q ^ m ≤ |a| * S := by
    rw [hS, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hη hQ0
  have h3 : |a| * S ≤ 2 * D * (|a| * X ^ m) := by
    have := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
    linarith
  have h4 : 2 * D * (|a| * X ^ m) ≤ 2 * D * |P| + 2 * D * (εP * N ^ m) := by
    have := mul_le_mul_of_nonneg_left (show |a| * X ^ m ≤ |P| + εP * N ^ m by linarith)
      (by positivity : (0 : ℝ) ≤ 2 * D)
    linarith
  have h5 : 2 * D * (εP * N ^ m) ≤ η₀ / 2 * Real.sqrt q ^ m := by
    have := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ 2 * D * εP)
    have h6 : 4 * D * εP * Real.sqrt q ^ m ≤ η₀ / 2 * Real.sqrt q ^ m :=
      mul_le_mul_of_nonneg_right (by linarith) hQ0
    nlinarith
  nlinarith

/-- `Ĉ` is positive definite if `(1 - ε_C) cov ≼ Ĉ` with `ε_C < 1`. -/
theorem empCov_posDef_of_le (Y : Fin n → Fin d → ℝ) {cov : Matrix (Fin d) (Fin d) ℝ}
    (hcov : cov.PosDef) {εC : ℝ} (hεC : εC < 1)
    (hlow : ∀ v, (1 - εC) * quad cov v ≤ quad (empCov Y) v) : (empCov Y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx ↦ ?_
  · change (empCov Y)ᴴ = empCov Y
    rw [conjTranspose_eq_transpose_of_trivial]
    exact empCov_transpose Y
  · rw [star_trivial]
    have h1 := hlow x
    have h2 := quad_pos hcov hx
    have h3 : 0 < (1 - εC) * quad cov x := mul_pos (by linarith) h2
    exact lt_of_lt_of_le h3 h1

/-- **A basis vector with a large score** (step (SEL)): if `Ĉ ≼ (1 + ε_C) cov`,
`(1 + ε_C)^m ≤ 4`, `‖v‖_cov^m ≤ 2 (vᵀĈv)^(m/2)` and `|P̂_m(v) - a ⟨u₀, v⟩^m| ≤ ε_P ‖v‖_cov^m` for
all `v`, `|a| √κ^m ≥ η₀` and `8 ε_P d^M ≤ η₀` with `m ≤ M`, then some basis vector of `Ĉ` has
score at least `(η₀ / (4 d^M))²` at the degree `m`. -/
theorem exists_le_score {M m : ℕ} (hd : 1 ≤ d) (hmM : m ≤ M) (Y : Fin n → Fin d → ℝ)
    (hC : (empCov Y).PosDef) {cov : Matrix (Fin d) (Fin d) ℝ} (hcov : cov.PosDef)
    (u0 : Fin d → ℝ) (a : ℝ) {εC εP η₀ : ℝ} (hεC0 : 0 ≤ εC) (hεP0 : 0 ≤ εP)
    (hup : ∀ v, quad (empCov Y) v ≤ (1 + εC) * quad cov v) (hpow : (1 + εC) ^ m ≤ 4)
    (hcmp : ∀ v, Real.sqrt (quad cov v) ^ m ≤ 2 * Real.sqrt (quad (empCov Y) v) ^ m)
    (HP : ∀ v, |phat m Y v - a * (u0 ⬝ᵥ v) ^ m| ≤ εP * Real.sqrt (quad cov v) ^ m)
    (hη : η₀ ≤ |a| * Real.sqrt (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) ^ m)
    (hsmall : 8 * εP * (d : ℝ) ^ M ≤ η₀) :
    ∃ i, (η₀ / (4 * (d : ℝ) ^ M)) ^ 2 ≤ score Y (m, i) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD1 : (1 : ℝ) ≤ (d : ℝ) ^ M := one_le_pow₀ hd1
  have hD0 : (0 : ℝ) < (d : ℝ) ^ M := by linarith
  have hκ := inv_quad_nonneg hcov u0
  obtain ⟨i₀, hi₀⟩ := exists_le_sq_div_quad_basisVec hC hd u0
  have hinv := inv_quad_le_of_quad_le_one_add hC hcov hεC0 hup u0
  refine ⟨i₀, ?_⟩
  set w₀ := basisVec (empCov Y) i₀ with hw₀
  set q₀ := quad (empCov Y) w₀ with hq₀def
  have hq₀ : 0 < q₀ := quad_basisVec_pos hC i₀
  have halign : (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) * q₀ ≤ (d * (1 + εC)) * |u0 ⬝ᵥ w₀| ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hq₀] at hi₀
    rw [sq_abs, dotProduct_comm u0 w₀]
    have e1 := mul_le_mul_of_nonneg_right hinv hq₀.le
    have e2 := mul_le_mul_of_nonneg_left hi₀ (by linarith : (0 : ℝ) ≤ 1 + εC)
    linarith
  have hLm : ((d : ℝ) * (1 + εC)) ^ m ≤ (2 * (d : ℝ) ^ M) ^ 2 := by
    rw [mul_pow]
    have e1 : (d : ℝ) ^ m ≤ (d : ℝ) ^ M := pow_le_pow_right₀ hd1 hmM
    calc (d : ℝ) ^ m * (1 + εC) ^ m ≤ (d : ℝ) ^ M * 4 :=
          mul_le_mul e1 hpow (by positivity) (by positivity)
      _ ≤ (2 * (d : ℝ) ^ M) ^ 2 := by nlinarith
  have hP₀ : |a| * |u0 ⬝ᵥ w₀| ^ m - εP * Real.sqrt (quad cov w₀) ^ m ≤ |phat m Y w₀| := by
    have h1 := HP w₀
    have h2 := abs_sub_abs_le_abs_sub (a * (u0 ⬝ᵥ w₀) ^ m) (phat m Y w₀)
    rw [abs_sub_comm, abs_mul, abs_pow] at h2
    linarith
  have hscore := score_aux hκ hq₀.le (abs_nonneg _) hD0 hεP0 halign hLm hη hP₀ (hcmp w₀)
    hsmall
  have hA₀ : η₀ / (4 * (d : ℝ) ^ M) * Real.sqrt q₀ ^ m ≤ |phat m Y w₀| := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have hη₀ : 0 ≤ η₀ := le_trans (by positivity) hsmall
  rw [score_eq, le_div_iff₀ (pow_pos hq₀ _)]
  have := pow_le_pow_left₀ (by positivity) hA₀ 2
  rwa [mul_pow, pow_right_comm, Real.sq_sqrt hq₀.le, sq_abs] at this

/-- A pair with score at least `A²` has a large main coefficient: if
`4 ε_P ≤ A`, `‖v‖_cov^m ≤ 2 (vᵀĈv)^(m/2)` and `|P̂_m(v) - a ⟨u₀, v⟩^m| ≤ ε_P ‖v‖_cov^m` for
all `v`, then the basis vector `w = λᵢ` has `|a| |⟨u₀, w⟩|^m ≥ A/4 · ‖w‖_cov^m`. -/
theorem le_abs_mul_pow_of_le_score {m : ℕ} (Y : Fin n → Fin d → ℝ) (hC : (empCov Y).PosDef)
    {cov : Matrix (Fin d) (Fin d) ℝ} (u0 : Fin d → ℝ) (a : ℝ) {εP A : ℝ} (hεP0 : 0 ≤ εP)
    (hA : 0 ≤ A) (hAε : 4 * εP ≤ A)
    (hcmp : ∀ v, Real.sqrt (quad cov v) ^ m ≤ 2 * Real.sqrt (quad (empCov Y) v) ^ m)
    (HP : ∀ v, |phat m Y v - a * (u0 ⬝ᵥ v) ^ m| ≤ εP * Real.sqrt (quad cov v) ^ m)
    (i : Fin d) (hsc : A ^ 2 ≤ score Y (m, i)) :
    A / 4 * Real.sqrt (quad cov (basisVec (empCov Y) i)) ^ m ≤
      |a| * |u0 ⬝ᵥ basisVec (empCov Y) i| ^ m := by
  set w := basisVec (empCov Y) i with hw
  have hq : 0 < quad (empCov Y) w := quad_basisVec_pos hC i
  have hph : A * Real.sqrt (quad (empCov Y) w) ^ m ≤ |phat m Y w| := by
    rw [score_eq, le_div_iff₀ (pow_pos hq _)] at hsc
    refine le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg _) ?_
    rwa [mul_pow, pow_right_comm, Real.sq_sqrt hq.le, sq_abs]
  have h1 := HP w
  have h2 := abs_sub_abs_le_abs_sub (phat m Y w) (a * (u0 ⬝ᵥ w) ^ m)
  rw [abs_mul a, abs_pow] at h2
  have h3 := hcmp w
  set Q := Real.sqrt (quad (empCov Y) w) ^ m with hQ
  set Nm := Real.sqrt (quad cov w) ^ m with hNm
  have hQ0 : 0 ≤ Q := by positivity
  have e1 : εP * Nm ≤ εP * (2 * Q) := mul_le_mul_of_nonneg_left h3 hεP0
  have e2 : 2 * εP * Q ≤ A / 2 * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0
  have e3 : A / 4 * Nm ≤ A / 4 * (2 * Q) := mul_le_mul_of_nonneg_left h3 (by positivity)
  linarith

/-- The step (GRAD) at one vector: if the main coefficient is large,
`|a| |⟨u₀, w⟩|^m ≥ A/4 · ‖w‖_cov^m` with `A > 0`, and `(m+1)^(m+1) 2^m ε_P ≤ σ A / 64`, then
`∇P̂_m(w) = c u₀ + E` with `c ≠ 0` and `Eᵀ cov⁻¹ E ≤ (|c| √κ σ / 16)²`. -/
theorem exists_gradPhat_eq_smul_add {m : ℕ} (hm : 1 ≤ m) (Y : Fin n → Fin d → ℝ)
    {cov : Matrix (Fin d) (Fin d) ℝ} (hcov : cov.PosDef) (u0 : Fin d → ℝ) (a : ℝ)
    {εP A σ : ℝ} (hεP0 : 0 ≤ εP) (hA : 0 < A) (hσ : 0 ≤ σ)
    (HP : ∀ v, |phat m Y v - a * (u0 ⬝ᵥ v) ^ m| ≤ εP * Real.sqrt (quad cov v) ^ m)
    {w : Fin d → ℝ} (hw : w ≠ 0)
    (hmain : A / 4 * Real.sqrt (quad cov w) ^ m ≤ |a| * |u0 ⬝ᵥ w| ^ m)
    (hsmall : (m + 1 : ℝ) ^ (m + 1) * 2 ^ m * εP ≤ σ * A / 64) :
    ∃ c E, c ≠ 0 ∧ gradPhat m Y w = c • u0 + E ∧
      E ⬝ᵥ (cov⁻¹ *ᵥ E) ≤ (|c| * Real.sqrt (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) * σ / 16) ^ 2 := by
  have hgrad := inv_quad_gradPhat_sub_le hm Y hcov u0 a hεP0 HP hw
  have hNq : qnorm cov w = Real.sqrt (quad cov w) := rfl
  rw [hNq] at hgrad
  set κ := u0 ⬝ᵥ (cov⁻¹ *ᵥ u0) with hκdef
  set N := Real.sqrt (quad cov w) with hN
  have hNpos : 0 < N := Real.sqrt_pos.mpr (quad_pos hcov hw)
  set c : ℝ := (m : ℝ) * a * (u0 ⬝ᵥ w) ^ (m - 1) with hc
  set E := gradPhat m Y w - c • u0 with hE
  have hCS : |u0 ⬝ᵥ w| ≤ N * Real.sqrt κ := by
    rw [dotProduct_comm]
    exact abs_dotProduct_le hcov w u0
  have hcκ : A / 4 * N ^ m ≤ |c| * Real.sqrt κ * N := by
    have e1 : |u0 ⬝ᵥ w| ^ m = |u0 ⬝ᵥ w| ^ (m - 1) * |u0 ⬝ᵥ w| := by
      rw [← pow_succ, Nat.sub_add_cancel hm]
    have e3 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have e5 : 0 ≤ |a| * |u0 ⬝ᵥ w| ^ (m - 1) * (N * Real.sqrt κ) := by positivity
    calc A / 4 * N ^ m ≤ |a| * |u0 ⬝ᵥ w| ^ m := hmain
      _ = |a| * |u0 ⬝ᵥ w| ^ (m - 1) * |u0 ⬝ᵥ w| := by rw [e1]; ring
      _ ≤ |a| * |u0 ⬝ᵥ w| ^ (m - 1) * (N * Real.sqrt κ) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ ≤ m * (|a| * |u0 ⬝ᵥ w| ^ (m - 1) * (N * Real.sqrt κ)) := le_mul_of_one_le_left e5 e3
      _ = |c| * Real.sqrt κ * N := by rw [hc, abs_mul, abs_mul, abs_pow, Nat.abs_cast]; ring
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, abs_zero, zero_mul, zero_mul] at hcκ
    have : 0 < A / 4 * N ^ m := by positivity
    linarith
  refine ⟨c, E, hc0, by rw [hE]; abel, ?_⟩
  have hNm : N ^ m = N ^ (m - 1) * N := by rw [← pow_succ, Nat.sub_add_cancel hm]
  have hB : (m + 1 : ℝ) ^ (m + 1) * 2 ^ m * εP * N ^ (m - 1) ≤ |c| * Real.sqrt κ * σ / 16 := by
    refine le_of_mul_le_mul_right ?_ hNpos
    calc (m + 1 : ℝ) ^ (m + 1) * 2 ^ m * εP * N ^ (m - 1) * N =
          (m + 1 : ℝ) ^ (m + 1) * 2 ^ m * εP * N ^ m := by rw [hNm]; ring
      _ ≤ σ * A / 64 * N ^ m := by gcongr
      _ = σ / 16 * (A / 4 * N ^ m) := by ring
      _ ≤ σ / 16 * (|c| * Real.sqrt κ * N) := by gcongr
      _ = |c| * Real.sqrt κ * σ / 16 * N := by ring
  exact hgrad.trans (pow_le_pow_left₀ (by positivity) hB 2)

/-- **Selection and gradient** (steps (SEL) and (GRAD)). Let `Ĉ = empCov Y` be within `1 ± ε_C`
of a positive definite `cov`, with `0 ≤ ε_C ≤ 1/(4M)`; let the empirical Hermite moments satisfy
`|P̂_m(v) - h_m ⟨u₀, v⟩^m| ≤ ε_P ‖v‖_cov^m` for `3 ≤ m ≤ M`, with
`|h_{m₀}| √κ^{m₀} ≥ η₀ > 0` for some `3 ≤ m₀ ≤ M` (`κ = u₀ᵀ cov⁻¹ u₀`), and
`ε_P ≤ η₀ σ / (2^(M+8) (M+1)^(M+1) d^M)` with `0 < σ ≤ 1`. Then the algorithm selects a pair
`(m, i)`, and the gradient at `λᵢ` is `c u₀ + E` with `c ≠ 0` and
`Eᵀ cov⁻¹ E ≤ (|c| √κ σ / 16)²`. -/
theorem exists_selectBest_gradPhat {M : ℕ} (hd : 1 ≤ d) (hM : 3 ≤ M) (Y : Fin n → Fin d → ℝ)
    {cov : Matrix (Fin d) (Fin d) ℝ} (hcov : cov.PosDef) {u0 : Fin d → ℝ} (hu0 : u0 ≠ 0)
    (h : ℕ → ℝ) {εC εP η₀ σ : ℝ} (hεC0 : 0 ≤ εC) (hεC : εC ≤ 1 / (4 * M)) (hσ0 : 0 < σ)
    (hσ1 : σ ≤ 1) (hη₀ : 0 < η₀)
    (HC : ∀ v, (1 - εC) * quad cov v ≤ quad (empCov Y) v ∧
      quad (empCov Y) v ≤ (1 + εC) * quad cov v)
    (HP : ∀ m, 3 ≤ m → m ≤ M → ∀ v,
      |phat m Y v - h m * (u0 ⬝ᵥ v) ^ m| ≤ εP * Real.sqrt (quad cov v) ^ m)
    (HM : ∃ m₀, 3 ≤ m₀ ∧ m₀ ≤ M ∧ η₀ ≤ |h m₀| * Real.sqrt (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) ^ m₀)
    (Hsmall : εP ≤ η₀ * σ / (2 ^ (M + 8) * (M + 1) ^ (M + 1) * d ^ M)) :
    ∃ p, selectBest M Y = some p ∧ ∃ c E, c ≠ 0 ∧
      gradPhat p.1 Y (basisVec (empCov Y) p.2) = c • u0 + E ∧
      E ⬝ᵥ (cov⁻¹ *ᵥ E) ≤ (|c| * Real.sqrt (u0 ⬝ᵥ (cov⁻¹ *ᵥ u0)) * σ / 16) ^ 2 := by
  -- the comparison `Ĉ ≈ cov`
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hMε : (M : ℝ) * εC ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hεC
    linarith
  have hε4 : εC ≤ 1 / 4 := by nlinarith
  have hε1 : 0 < 1 - εC := by linarith
  have hpow : ∀ m, m ≤ M → (1 + εC) ^ m ≤ 4 ∧ (1 - εC)⁻¹ ^ m ≤ 4 := by
    intro m hm
    have : (m : ℝ) ≤ M := by exact_mod_cast hm
    exact pow_one_add_le_four hεC0 hε4 (by nlinarith)
  have hC : (empCov Y).PosDef := empCov_posDef_of_le Y hcov (by linarith) fun v ↦ (HC v).1
  have hcmp : ∀ m, m ≤ M → ∀ v,
      Real.sqrt (quad cov v) ^ m ≤ 2 * Real.sqrt (quad (empCov Y) v) ^ m := by
    intro m hm v
    refine sqrt_pow_le_two_mul (quad_nonneg hC.posSemidef v) ?_ (hpow m hm).2
    rw [inv_mul_eq_div, le_div_iff₀ hε1, mul_comm]
    exact (HC v).1
  -- `ε_P ≥ 0`
  have hεP0 : 0 ≤ εP := by
    have h1 := HP 3 le_rfl hM u0
    have h2 : 0 < Real.sqrt (quad cov u0) ^ 3 :=
      pow_pos (Real.sqrt_pos.mpr (quad_pos hcov hu0)) 3
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h2
    linarith [abs_nonneg (phat 3 Y u0 - h 3 * (u0 ⬝ᵥ u0) ^ 3)]
  -- the constants
  set D : ℝ := (d : ℝ) ^ M with hDdef
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD1 : 1 ≤ D := one_le_pow₀ hd1
  have hD0 : 0 < D := by linarith
  set K : ℝ := (M + 1 : ℝ) ^ (M + 1) * 2 ^ M with hKdef
  have hK1 : 1 ≤ K :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by norm_num))
  have hsmall : 256 * K * D * εP ≤ η₀ * σ := by
    rw [le_div_iff₀ (by positivity)] at Hsmall
    calc 256 * K * D * εP = εP * (2 ^ (M + 8) * (M + 1) ^ (M + 1) * d ^ M) := by
          rw [hKdef, hDdef, pow_add]; ring
      _ ≤ η₀ * σ := Hsmall
  have hsmall' : 256 * D * εP ≤ η₀ := by
    have h0 : 0 ≤ 256 * D * εP := by positivity
    have h1 : 256 * D * εP ≤ 256 * K * D * εP := by
      have := mul_le_mul_of_nonneg_left hK1 h0
      linarith
    have h2 : η₀ * σ ≤ η₀ := mul_le_of_le_one_right hη₀.le hσ1
    linarith
  set A : ℝ := η₀ / (4 * D) with hAdef
  have hA0 : 0 < A := by positivity
  have hAε : 64 * εP ≤ A := by
    rw [hAdef, le_div_iff₀ (by positivity)]
    linarith
  -- (SEL) some pair has a large score, hence so does the selected one
  obtain ⟨m₀, hm₀3, hm₀M, hm₀⟩ := HM
  obtain ⟨i₀, hsc₀⟩ := exists_le_score hd hm₀M Y hC hcov u0 (h m₀) hεC0 hεP0
    (fun v ↦ (HC v).2) (hpow m₀ hm₀M).1 (hcmp m₀ hm₀M) (HP m₀ hm₀3 hm₀M) hm₀ (by linarith)
  obtain ⟨p, hp⟩ := selectBest_isSome (M := M) Y (candidates_ne_nil hM hd)
  obtain ⟨hpmem, hpmax⟩ := selectBest_spec hp
  obtain ⟨m, i⟩ := p
  obtain ⟨hm3, hmM⟩ := mem_candidates.mp hpmem
  have hsc : A ^ 2 ≤ score Y (m, i) :=
    hsc₀.trans (hpmax _ (mem_candidates.mpr ⟨hm₀3, hm₀M⟩))
  have hmain := le_abs_mul_pow_of_le_score Y hC u0 (h m) hεP0 hA0.le (by linarith)
    (hcmp m hmM) (HP m hm3 hmM) i hsc
  have hw0 : basisVec (empCov Y) i ≠ 0 := fun h0 ↦
    (quad_basisVec_pos hC i).ne' (by rw [h0]; simp [quad])
  -- (GRAD) the gradient at the selected basis vector
  have hK' : (m + 1 : ℝ) ^ (m + 1) * 2 ^ m ≤ K := by
    have e1 : (m : ℝ) + 1 ≤ M + 1 := by
      have : (m : ℝ) ≤ M := by exact_mod_cast hmM
      linarith
    rw [hKdef]
    gcongr ?_ * ?_
    · calc (m + 1 : ℝ) ^ (m + 1) ≤ (M + 1) ^ (m + 1) := by gcongr
        _ ≤ (M + 1) ^ (M + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    · exact pow_le_pow_right₀ (by norm_num) hmM
  have hKε : K * εP ≤ σ * A / 64 := by
    rw [hAdef, show σ * (η₀ / (4 * D)) / 64 = η₀ * σ / (256 * D) by field_simp; ring,
      le_div_iff₀ (by positivity)]
    linarith
  exact ⟨(m, i), hp, exists_gradPhat_eq_smul_add (by omega) Y hcov u0 (h m) hεP0 hA0 hσ0.le
    (HP m hm3 hmM) hw0 hmain ((mul_le_mul_of_nonneg_right hK' hεP0).trans hKε)⟩

end BS23.Colinear
